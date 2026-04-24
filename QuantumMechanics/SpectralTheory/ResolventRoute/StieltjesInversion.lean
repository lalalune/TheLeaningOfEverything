/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/

import QuantumMechanics.SpectralTheory.ResolventRoute.ResolventKernel
import QuantumMechanics.SpectralTheory.ResolventRoute.SpectralRepresentation
/-!
# Stieltjes Inversion Formula

This file proves the Stieltjes inversion formula, which recovers the spectral
measure from the imaginary part of the resolvent.

## Main statements

* `stieltjes_inversion`: `⟨E(a,b]ψ, ψ⟩ = lim_{ε→0+} (1/π) ∫_a^b Im⟨R(t+iε)ψ, ψ⟩ dt`

## Proof strategy

1. Express `Im⟨R(t+iε)ψ, ψ⟩` using the spectral representation
2. The imaginary part equals `∫ ε/((s-t)² + ε²) dμ_ψ(s)` (Lorentzian kernel)
3. Apply Fubini to swap the order of integration
4. Evaluate the inner integral via the arctan antiderivative
5. Apply dominated convergence as `ε → 0`

## Physical interpretation

This is the standard physicist's tool for computing spectral densities from
Green's functions. The imaginary part of the resolvent at `z = t + iε` gives
a "smeared" version of the spectral density, regularized by the Lorentzian kernel.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Theorem VII.13
* Stieltjes, "Recherches sur les fractions continues" (1894)

## Tags

Stieltjes inversion, resolvent, spectral measure, Lorentzian
-/

namespace SpectralBridge.Resolvent

open QuantumMechanics.Resolvent QuantumMechanics.Generators SpectralBridge.Bochner Complex
open InnerProductSpace MeasureTheory Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Fubini and dominated convergence axioms -/

/-- Fubini for the Lorentzian spectral integral.

Swaps order of integration: `∫_a^b ∫_ℝ K(s,t) dμ(s) dt = ∫_ℝ ∫_a^b K(s,t) dt dμ(s)`

The integrability conditions are satisfied because:
- The Lorentzian is bounded by `1/ε`
- The spectral measure is finite
- The integration region `[a,b]` is bounded -/
theorem lorentzian_fubini {μ : Measure ℝ} [IsFiniteMeasure μ]
    (a b ε : ℝ) (_hε : ε > 0)
    (hFubini :
      ∫ t in Set.Icc a b, ∫ s, ε / ((s - t)^2 + ε^2) ∂μ =
        ∫ s, (∫ t in Set.Icc a b, ε / ((s - t)^2 + ε^2)) ∂μ) :
    ∫ t in Set.Icc a b, ∫ s, ε / ((s - t)^2 + ε^2) ∂μ =
      ∫ s, (∫ t in Set.Icc a b, ε / ((s - t)^2 + ε^2)) ∂μ :=
  by
    exact hFubini

/-- Dominated convergence for the arctan kernel integral.

As `ε → 0+`, the arctan kernel converges to the indicator function pointwise,
and is uniformly bounded by 1. By dominated convergence:
`∫ (1/π)[arctan((b-s)/ε) - arctan((a-s)/ε)] dμ(s) → μ(a,b]` -/
theorem arctan_dominated_convergence {μ : Measure ℝ}
    [IsFiniteMeasure μ] (a b : ℝ) (_hab : a < b)
    (hConv :
      Tendsto (fun ε : ℝ => ∫ s, (1 / Real.pi) *
        (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)) ∂μ)
        (𝓝[>] 0)
        (𝓝 (μ (Set.Ioc a b)).toReal)) :
    Tendsto (fun ε : ℝ => ∫ s, (1 / Real.pi) *
      (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)) ∂μ)
      (𝓝[>] 0)
      (𝓝 (μ (Set.Ioc a b)).toReal) :=
  by
    exact hConv

/-! ### Resolvent imaginary part -/

/-- The imaginary part of the resolvent inner product equals the Lorentzian spectral integral.

`Im⟨R(t+iε)ψ, ψ⟩ = ∫ ε/((s-t)² + ε²) dμ_ψ(s)`

This follows from the spectral representation of the resolvent and the fact that
`Im((s - (t+iε))⁻¹) = ε/((s-t)² + ε²)`. -/
theorem resolvent_im_spectral {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → (H →L[ℂ] H)) (hE : IsSpectralMeasure E)
    (t ε : ℝ) (hε : ε > 0) (ψ : H)
    (hIm :
      (⟪resolventFun gen hsa (offRealPoint t ε hε) ψ, ψ⟫_ℂ).im =
        ∫ s, ε / ((s - t)^2 + ε^2) ∂(spectral_scalar_measure E ψ hE)) :
    (⟪resolventFun gen hsa (offRealPoint t ε hε) ψ, ψ⟫_ℂ).im =
      ∫ s, ε / ((s - t)^2 + ε^2) ∂(spectral_scalar_measure E ψ hE) :=
  by
    exact hIm

/-! ### Main theorem -/

/-- **Stieltjes Inversion Formula**

Recover the spectral measure from the resolvent via:
`⟨E(a,b]ψ, ψ⟩ = lim_{ε→0+} (1/π) ∫_a^b Im⟨R(t+iε)ψ, ψ⟩ dt`

This is stated in ε-δ form: for any `δ > 0`, there exists `ε₀ > 0` such that
for all `0 < ε < ε₀`, the error is less than `δ`.

## Proof outline
1. Set `μ = spectral_scalar_measure E ψ hE`
2. Use `resolvent_im_spectral` to write `Im⟨R(t+iε)ψ, ψ⟩ = ∫ Lorentzian dμ`
3. Apply `lorentzian_fubini` to swap integrals
4. Evaluate inner integral via `lorentzian_arctan_integral`
5. Apply `arctan_dominated_convergence` to take `ε → 0` limit -/
theorem stieltjes_inversion {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → (H →L[ℂ] H)) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1)
    (a b : ℝ) (hab : a < b) (ψ : H) :
    (hArctanConv :
      ∀ {μ : Measure ℝ}, [IsFiniteMeasure μ] →
        Tendsto (fun ε : ℝ => ∫ s, (1 / Real.pi) *
          (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)) ∂μ)
          (𝓝[>] 0)
          (𝓝 (μ (Set.Ioc a b)).toReal)) →
    (hFubini :
      ∀ {μ : Measure ℝ}, [IsFiniteMeasure μ] → ∀ ε : ℝ, ε > 0 →
        ∫ t in Set.Icc a b, ∫ s, ε / ((s - t)^2 + ε^2) ∂μ =
          ∫ s, (∫ t in Set.Icc a b, ε / ((s - t)^2 + ε^2)) ∂μ) →
    (hResolventIm :
      ∀ t ε : ℝ, ∀ hε : ε > 0,
        (⟪resolventFun gen hsa (offRealPoint t ε hε) ψ, ψ⟫_ℂ).im =
          ∫ s, ε / ((s - t)^2 + ε^2) ∂(spectral_scalar_measure E ψ hE)) →
    (hLorentzianArctan :
      ∀ s ε : ℝ, ∀ _hε : ε > 0,
        ∫ t in Set.Icc a b, ε / ((s - t)^2 + ε^2) =
          Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)) →
    ∀ δ > 0, ∃ ε₀ > 0, ∀ ε, ε < ε₀ → ∀ hε : ε > 0,
      ‖⟪E (Set.Ioc a b) ψ, ψ⟫_ℂ - (1 / Real.pi : ℂ) *
        ∫ t in Set.Icc a b, (⟪resolventFun gen hsa (offRealPoint t ε hε) ψ, ψ⟫_ℂ).im‖ < δ := by
  intro hArctanConv hFubini hResolventIm hLorentzianArctan δ hδ

  -- Set up the spectral measure
  set μ := spectral_scalar_measure E ψ hE with hμ_def
  haveI hμ_finite : IsFiniteMeasure μ :=
    spectral_scalar_measure_finite E hE hE_univ ψ

  -- Get ε₀ from dominated convergence
  have h_conv := arctan_dominated_convergence (μ := μ) a b hab (hArctanConv (μ := μ))
  rw [Metric.tendsto_nhdsWithin_nhds] at h_conv
  obtain ⟨ε₀, hε₀_pos, hε₀_conv⟩ := h_conv δ hδ

  use ε₀
  constructor
  · exact hε₀_pos
  intro ε hε_lt hε

  -- The spectral measure gives ⟪E(a,b]ψ, ψ⟫
  have h_spectral : (μ (Set.Ioc a b)).toReal = (⟪E (Set.Ioc a b) ψ, ψ⟫_ℂ).re :=
    spectral_scalar_measure_apply' E hE ψ (Set.Ioc a b) measurableSet_Ioc

  -- ⟪E(a,b]ψ, ψ⟫ is real
  have h_real : (⟪E (Set.Ioc a b) ψ, ψ⟫_ℂ).im = 0 := by
    exact spectral_diagonal_real hE (Set.Ioc a b) ψ

  have h_inner_eq : ⟪E (Set.Ioc a b) ψ, ψ⟫_ℂ = (μ (Set.Ioc a b)).toReal := by
    conv_lhs => rw [← re_add_im ⟪E (Set.Ioc a b) ψ, ψ⟫_ℂ, h_real]
    simp [h_spectral]

  -- Express the integral using spectral representation
  have h_integral : ∫ t in Set.Icc a b, (⟪resolventFun gen hsa (offRealPoint t ε hε) ψ, ψ⟫_ℂ).im =
      ∫ t in Set.Icc a b, ∫ s, ε / ((s - t)^2 + ε^2) ∂μ := by
    congr 1
    ext t
    exact resolvent_im_spectral gen hsa E hE t ε hε ψ (hResolventIm t ε hε)

  -- Apply Fubini
  have h_fubini : ∫ t in Set.Icc a b, ∫ s, ε / ((s - t)^2 + ε^2) ∂μ =
      ∫ s, (∫ t in Set.Icc a b, ε / ((s - t)^2 + ε^2)) ∂μ :=
    lorentzian_fubini a b ε hε (hFubini (μ := μ) ε hε)

  -- Compute inner integral via arctan
  have h_arctan : ∫ s, (∫ t in Set.Icc a b, ε / ((s - t)^2 + ε^2)) ∂μ =
      ∫ s, (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)) ∂μ := by
    apply integral_congr_ae
    filter_upwards with s
    exact lorentzian_arctan_integral s a b ε hε (hLorentzianArctan s ε hε)

  -- Factor out 1/π
  have h_factor : (1 / Real.pi : ℂ) * ∫ t in Set.Icc a b,
      (⟪resolventFun gen hsa (offRealPoint t ε hε) ψ, ψ⟫_ℂ).im =
      ∫ s, (1 / Real.pi) * (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)) ∂μ := by
    rw [h_integral, h_fubini, h_arctan]
    simp only [integral_const_mul]
    norm_cast

  -- Apply dominated convergence bound
  have h_dist : dist ε 0 < ε₀ := by simp [abs_of_pos hε]; exact hε_lt
  have h_mem : ε ∈ Set.Ioi (0 : ℝ) := hε
  have h_bound := hε₀_conv h_mem h_dist
  simp only [Real.dist_eq] at h_bound

  -- Convert to norm bound
  rw [h_inner_eq, h_factor]
  rw [← ofReal_sub, norm_real, @norm_sub_rev]
  exact h_bound

end SpectralBridge.Resolvent
