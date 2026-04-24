import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Star.CHSH
import Mathlib.Data.Complex.Basic
import QEC.Foundations.Basic
import QEC.Foundations.Gates

namespace Quantum

open Matrix
open scoped BigOperators ComplexOrder

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A quantum code projector is an idempotent Hermitian matrix. -/
def IsCodeProjection (P : Matrix α α ℂ) : Prop :=
  P * P = P ∧ Pᴴ = P

/-- Knill-Laflamme exact-correctability conditions for a finite error set. -/
def IsCorrectableCode
    (P : Matrix α α ℂ)
    (errors : Finset (Matrix α α ℂ)) : Prop :=
  IsCodeProjection P ∧
  ∃ c : Matrix errors errors ℂ,
    cᴴ = c ∧
    ∀ Ei Ej : errors, P * (Ei.valᴴ * Ej.val) * P = c Ei Ej • P

private theorem projection_posSemidef {P : Matrix α α ℂ}
    (hP : IsCodeProjection P) : P.PosSemidef := by
  rcases hP with ⟨h_idem, h_herm⟩
  have h_psd : (Pᴴ * P).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self P
  have h_eq : Pᴴ * P = P := by simpa [h_herm] using h_idem
  simpa [h_eq] using h_psd

private theorem trace_projection_re_pos {P : Matrix α α ℂ}
    (hP : IsCodeProjection P) (hP_nonzero : P ≠ 0) :
    0 < P.trace.re := by
  have h_psd : P.PosSemidef := projection_posSemidef hP
  have h_trace_nonneg : 0 ≤ P.trace := h_psd.trace_nonneg
  have h_re_nonneg : 0 ≤ P.trace.re := (Complex.nonneg_iff.mp h_trace_nonneg).1
  have h_im_zero : P.trace.im = 0 := (Complex.nonneg_iff.mp h_trace_nonneg).2.symm
  have h_trace_ne_zero : P.trace ≠ 0 := by
    intro h0
    exact hP_nonzero ((h_psd.trace_eq_zero_iff).1 h0)
  have h_re_ne_zero : P.trace.re ≠ 0 := by
    intro h0
    apply h_trace_ne_zero
    exact Complex.ext h0 h_im_zero
  exact lt_of_le_of_ne h_re_nonneg (Ne.symm h_re_ne_zero)

private theorem trace_PEdagEP_re_nonneg {P E : Matrix α α ℂ}
    (hP : IsCodeProjection P) :
    0 ≤ (Matrix.trace (P * (Eᴴ * E) * P)).re := by
  rcases hP with ⟨_, h_herm⟩
  have h_rewrite : P * (Eᴴ * E) * P = (E * P)ᴴ * (E * P) := by
    calc
      P * (Eᴴ * E) * P = (P * Eᴴ) * (E * P) := by
        simp [Matrix.mul_assoc]
      _ = (Pᴴ * Eᴴ) * (E * P) := by simpa [h_herm]
      _ = (E * P)ᴴ * (E * P) := by
        simp [Matrix.conjTranspose_mul]
  have h_nonneg :
      0 ≤ Matrix.trace ((E * P)ᴴ * (E * P)) :=
    (Matrix.posSemidef_conjTranspose_mul_self (E * P)).trace_nonneg
  have h_re_nonneg : 0 ≤ (Matrix.trace ((E * P)ᴴ * (E * P))).re :=
    (Complex.nonneg_iff.mp h_nonneg).1
  simpa [h_rewrite] using h_re_nonneg

/-- Diagonal Knill-Laflamme coefficients are nonnegative reals. -/
theorem IsCorrectableCode_diag_nonneg
    {P : Matrix α α ℂ} {errors : Finset (Matrix α α ℂ)}
    (h : IsCorrectableCode P errors)
    (hP_nonzero : P ≠ 0)
    (Ei : errors) :
    ∃ r : ℝ, 0 ≤ r ∧
      P * (Ei.valᴴ * Ei.val) * P = (r : ℂ) • P := by
  rcases h with ⟨hP, c, hc_herm, hc_eq⟩
  have h_diag : P * (Ei.valᴴ * Ei.val) * P = c Ei Ei • P := hc_eq Ei Ei

  have h_diag_real : (c Ei Ei).im = 0 := by
    have hconj : star (c Ei Ei) = c Ei Ei := by
      simpa [Matrix.conjTranspose_apply] using congrArg (fun M => M Ei Ei) hc_herm
    exact Complex.conj_eq_iff_im.mp hconj

  have h_trace_lhs_nonneg : 0 ≤ (Matrix.trace (P * (Ei.valᴴ * Ei.val) * P)).re :=
    trace_PEdagEP_re_nonneg hP

  have h_trace_eq : Matrix.trace (P * (Ei.valᴴ * Ei.val) * P) = c Ei Ei * Matrix.trace P := by
    simpa [h_diag, Matrix.trace_smul, smul_eq_mul] using congrArg Matrix.trace h_diag

  have hP_trace_nonneg : 0 ≤ P.trace := (projection_posSemidef hP).trace_nonneg
  have hP_trace_im_zero : P.trace.im = 0 := (Complex.nonneg_iff.mp hP_trace_nonneg).2.symm
  have hP_trace_re_pos : 0 < P.trace.re := trace_projection_re_pos hP hP_nonzero

  have h_mul_re :
      (c Ei Ei * P.trace).re = (c Ei Ei).re * P.trace.re := by
    rw [Complex.mul_re, h_diag_real, hP_trace_im_zero]
    ring

  have h_prod_nonneg : 0 ≤ (c Ei Ei).re * P.trace.re := by
    have h_rhs_nonneg : 0 ≤ (c Ei Ei * P.trace).re := by
      simpa [h_trace_eq] using h_trace_lhs_nonneg
    simpa [h_mul_re] using h_rhs_nonneg

  have h_r_nonneg : 0 ≤ (c Ei Ei).re := by
    nlinarith [h_prod_nonneg, hP_trace_re_pos]

  refine ⟨(c Ei Ei).re, h_r_nonneg, ?_⟩
  have h_rewrite_coeff : c Ei Ei = ((c Ei Ei).re : ℂ) := Complex.ext rfl h_diag_real
  calc
    P * (Ei.valᴴ * Ei.val) * P = c Ei Ei • P := h_diag
    _ = ((c Ei Ei).re : ℂ) • P := by
      rw [h_rewrite_coeff]
      simp

end Quantum
