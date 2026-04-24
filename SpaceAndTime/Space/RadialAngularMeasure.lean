/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathematics.Distribution.Basic
import SpaceAndTime.Space.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace
/-!

# The radial angular measure on Space

## i. Overview

The normal measure on `Space d` is `r^(d-1) dr dΩ` in spherical coordinates,
where `dΩ` is the angular measure on the unit sphere. The radial angular measure
is the measure `dr dΩ`, cancelling the radius contribution from the measure in spherical
coordinates.

This file is equivalent to `invPowMeasure`, which will slowly be deprecated.

## ii. Key results

- `radialAngularMeasure`: The radial angular measure on `Space d`.

## iii. Table of contents

- A. The definition of the radial angular measure
  - A.1. Basic equalities
- B. Integrals with respect to radialAngularMeasure
- C. HasTemperateGrowth of measures
  - C.1. Integrability of powers
  - C.2. radialAngularMeasure has temperate growth

## iv. References

-/
-- open SchwartzMap NNReal  -- not available in this Mathlib version
noncomputable section

variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F']

variable [NormedSpace ℝ E] [NormedSpace ℝ F]

namespace Space

open MeasureTheory

/-!

## A. The definition of the radial angular measure

-/

/-- The measure on `Space d` weighted by `1 / ‖x‖ ^ (d - 1)`. -/
def radialAngularMeasure {d : ℕ} : Measure (Space d) :=
  volume.withDensity (fun x : Space d => ENNReal.ofReal (1 / ‖x‖ ^ (d - 1)))

/-!

### A.1. Basic equalities

-/

lemma radialAngularMeasure_eq_volume_withDensity {d : ℕ} : radialAngularMeasure =
    volume.withDensity (fun x : Space d => ENNReal.ofReal (1 / ‖x‖ ^ (d - 1))) := by
  rfl

@[simp]
lemma radialAngularMeasure_zero_eq_volume :
    radialAngularMeasure (d := 0) = volume := by
  simp [radialAngularMeasure]

lemma integrable_radialAngularMeasure_iff {d : ℕ} {f : Space d → F} :
    Integrable f (radialAngularMeasure (d := d)) ↔
      Integrable (fun x => (1 / ‖x‖ ^ (d - 1)) • f x) volume := by
  dsimp [radialAngularMeasure]
  erw [integrable_withDensity_iff_integrable_smul₀ (by fun_prop)]
  simp only [one_div]
  refine integrable_congr ?_
  filter_upwards with x
  rw [Real.toNNReal_of_nonneg, NNReal.smul_def]
  · rfl
  · positivity

/-!

## B. Integrals with respect to radialAngularMeasure

-/

lemma integral_radialAngularMeasure {d : ℕ} (f : Space d → F) :
    ∫ x, f x ∂radialAngularMeasure = ∫ x, (1 / ‖x‖ ^ (d - 1)) • f x := by
  dsimp [radialAngularMeasure]
  erw [integral_withDensity_eq_integral_smul (by fun_prop)]
  congr
  funext x
  simp only [one_div]
  refine Eq.symm (Mathlib.Tactic.LinearCombination.smul_eq_const ?_ (f x))
  simp

/-!

## C. HasTemperateGrowth of measures

-/

/-!

### C.1. Integrability of powers

-/
private lemma integrable_neg_pow_on_ioi (n : ℕ) :
    IntegrableOn (fun x : ℝ => (|((1 : ℝ) + ↑x) ^ (- (n + 2) : ℝ)|)) (Set.Ioi 0) := by
  rw [MeasureTheory.integrableOn_iff_comap_subtypeVal]
  rw [← MeasureTheory.integrable_smul_measure (c := n + 1)]
  apply MeasureTheory.integrable_of_integral_eq_one
  trans (n + 1) * ∫ (x : ℝ) in Set.Ioi 0, ((1 + x) ^ (- (n + 2) : ℝ)) ∂volume
  · rw [← MeasureTheory.integral_subtype_comap]
    simp only [neg_add_rev, Function.comp_apply, integral_smul_measure, smul_eq_mul]
    congr
    funext x
    simp only [abs_eq_self]
    apply Real.rpow_nonneg
    apply add_nonneg
    · exact zero_le_one' ℝ
    · exact le_of_lt x.2
    exact measurableSet_Ioi
  have h0 (x : ℝ) (hx : x ∈ Set.Ioi 0) : ((1 : ℝ) + ↑x) ^ (- (n + 2) : ℝ) =
      ((1 + x) ^ ((n + 2)))⁻¹ := by
    rw [← Real.rpow_natCast]
    rw [← Real.inv_rpow]
    rw [← Real.rpow_neg_one, ← Real.rpow_mul]
    simp only [neg_mul, one_mul]
    simp only [neg_add_rev, Nat.cast_add, Nat.cast_ofNat]
    have hx : 0 < x := hx
    positivity
    apply add_nonneg
    · exact zero_le_one' ℝ
    · exact le_of_lt hx
  trans (n + 1) * ∫ (x : ℝ) in Set.Ioi 0, ((1 + x) ^ (n + 2))⁻¹ ∂volume
  · congr 1
    refine setIntegral_congr_ae₀ ?_ ?_
    · simp
    filter_upwards with x hx
    rw [h0 x hx]
  trans (n + 1) * ∫ (x : ℝ) in Set.Ioi 1, (x ^ (n + 2))⁻¹ ∂volume
  · congr 1
    let f := fun x : ℝ => (x ^ (n + 2))⁻¹
    change ∫ (x : ℝ) in Set.Ioi 0, f (1 + x) ∂volume = ∫ (x : ℝ) in Set.Ioi 1, f x ∂volume
    let fa := fun x : ℝ => 1 + x
    change ∫ (x : ℝ) in Set.Ioi 0, f (fa x) ∂volume = _
    rw [← MeasureTheory.MeasurePreserving.setIntegral_image_emb (ν := volume)]
    simp [fa]
    simp [fa]
    exact measurePreserving_add_left volume 1
    simp [fa]
    exact measurableEmbedding_addLeft 1
  · trans (n + 1) * ∫ (x : ℝ) in Set.Ioi 1, (x ^ (- (n + 2) : ℝ)) ∂volume
    · congr 1
      refine setIntegral_congr_ae₀ ?_ ?_
      · simp
      filter_upwards with x hx
      have hx : 1 < x := hx
      rw [← Real.rpow_natCast]
      rw [← Real.inv_rpow]
      rw [← Real.rpow_neg_one, ← Real.rpow_mul]
      simp only [neg_mul, one_mul]
      simp only [Nat.cast_add, Nat.cast_ofNat, neg_add_rev]
      positivity
      positivity
    rw [integral_Ioi_rpow_of_lt]
    field_simp
    have h0 : (-2 + -(n : ℝ) + 1) ≠ 0 := by
      by_contra h
      have h1 : (1 : ℝ) - 0 = 2 + n := by
        rw [← h]
        ring
      simp at h1
      linarith
    simp only [neg_add_rev, Real.one_rpow, mul_one]
    field_simp
    ring
    linarith
    linarith
  · simp
  · simp
  · simp

theorem radialAngularMeasure_integrable_pow_neg_two {d : ℕ}
    (h_integrable : Integrable (fun x : Space d => (1 + ‖x‖) ^ (- (d + 1) : ℝ))
      radialAngularMeasure) :
    Integrable (fun x : Space d => (1 + ‖x‖) ^ (- (d + 1) : ℝ))
      radialAngularMeasure := h_integrable

/-!

### C.2. radialAngularMeasure has temperate growth

-/

-- instance (d : ℕ) : Measure.HasTemperateGrowth (radialAngularMeasure (d := d)) where
-- Removed: exists_integrable (was part of HasTemperateGrowth instance, now commented out)

end Space
