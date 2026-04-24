/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.ForMathlib.Matrix

open BigOperators
open Classical

namespace Matrix
noncomputable section traceNorm

open scoped ComplexOrder

variable {m n R : Type*}
variable [Fintype m] [Fintype n]
variable [RCLike R]

/-- The trace norm of a matrix: Tr[√(A† A)]. -/
def traceNorm (A : Matrix m n R) : ℝ :=
  open MatrixOrder in
  RCLike.re (CFC.sqrt (Aᴴ * A)).trace

@[simp]
theorem traceNorm_zero : traceNorm (0 : Matrix m n R) = 0 := by
  simp [traceNorm]

/-- The trace norm of the negative is equal to the trace norm. -/
@[simp]
theorem traceNorm_eq_neg_self (A : Matrix m n R) : traceNorm (-A) = traceNorm A := by
  unfold traceNorm
  congr! 3
  rw [Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg]
  exact neg_neg _

--More generally sum of abs of singular values.
--Proposition 9.1.1 in Wilde
theorem traceNorm_Hermitian_eq_sum_abs_eigenvalues {A : Matrix n n R} (hA : A.IsHermitian) :
    A.traceNorm = ∑ i, abs (hA.eigenvalues i) :=
  by
    open MatrixOrder in
    have hAA_nonneg : 0 ≤ (Aᴴ * A : Matrix n n R) :=
      Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_conjTranspose_mul_self A)
    have hright_nonneg : 0 ≤ hA.cfc abs := by
      rw [← hA.cfc_eq abs]
      exact cfc_nonneg (fun x _ => abs_nonneg x)
    have hsqrt_eq : CFC.sqrt (Aᴴ * A) = hA.cfc abs := by
      have hleft : 0 ≤ CFC.sqrt (Aᴴ * A) := CFC.sqrt_nonneg _
      refine (CFC.sq_eq_sq_iff _ _ hleft hright_nonneg).mp ?_
      have hleft_sq : (CFC.sqrt (Aᴴ * A)) ^ 2 = A ^ 2 := by
        rw [pow_two, CFC.sqrt_mul_sqrt_self (a := (Aᴴ * A : Matrix n n R)) hAA_nonneg, hA, pow_two]
      have hright_sq : (hA.cfc abs) ^ 2 = A ^ 2 := by
        rw [← hA.cfc_eq abs, ← cfc_pow (R := ℝ) (fun x => abs x) 2 A]
        have habs_sq : (fun x : ℝ => abs x ^ 2) = fun x => x ^ 2 := by
          funext x
          exact sq_abs x
        rw [habs_sq, cfc_pow_id (R := ℝ) (a := A) 2]
      exact hleft_sq.trans hright_sq.symm
    have htrace_abs : (hA.cfc abs).trace = ∑ i, ((abs (hA.eigenvalues i) : ℝ) : R) := by
      rw [Matrix.IsHermitian.cfc, Matrix.trace_mul_cycle, hA.eigenvectorUnitary.2.1]
      simp [Matrix.trace_diagonal]
    rw [traceNorm, hsqrt_eq, htrace_abs]
    simp

/-- The trace norm is nonnegative. Property 9.1.1 in Wilde -/
theorem traceNorm_nonneg (A : Matrix m n R) : 0 ≤ A.traceNorm :=
  open MatrixOrder in
  And.left $ RCLike.nonneg_iff.1
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Aᴴ * A))).trace_nonneg

/-- The trace norm is zero only if the matrix is zero. -/
theorem traceNorm_zero_iff (A : Matrix m n R) : A.traceNorm = 0 ↔ A = 0 := by
  open MatrixOrder in
  constructor
  · intro h
    let S : Matrix n n R := CFC.sqrt (Aᴴ * A)
    have hpsd : S.PosSemidef := by
      refine Matrix.nonneg_iff_posSemidef.mp ?_
      simpa [S] using (CFC.sqrt_nonneg (Aᴴ * A))
    have htrace : S.trace = 0 := by
      refine RCLike.ext ?_ ?_
      · simpa [traceNorm, S] using h
      · simpa using (RCLike.nonneg_iff.mp hpsd.trace_nonneg).2
    have hsqrt : S = 0 := (hpsd.trace_eq_zero_iff).1 htrace
    have hmul_nonneg : 0 ≤ Aᴴ * A :=
      Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_conjTranspose_mul_self A)
    have hmul : Aᴴ * A = 0 := by
      simpa [S] using (CFC.sqrt_eq_zero_iff (Aᴴ * A) (ha := hmul_nonneg)).1 hsqrt
    exact Matrix.conjTranspose_mul_self_eq_zero.1 hmul
  · rintro rfl
    simp

/-- Trace norm is linear under scalar multiplication. Property 9.1.2 in Wilde -/
theorem traceNorm_smul (A : Matrix m n R) (c : R) : (c • A).traceNorm = ‖c‖ * A.traceNorm := by
  have h : (c • A)ᴴ * (c • A) = (‖c‖^2:R) • (Aᴴ * A) := by
    rw [conjTranspose_smul, RCLike.star_def, mul_smul, smul_mul, smul_smul]
    rw [RCLike.mul_conj c]
  rw [traceNorm, h]
  open MatrixOrder in
  have : RCLike.re (trace (‖c‖ • CFC.sqrt (Aᴴ * A))) = ‖c‖ * traceNorm A := by
    simp [RCLike.smul_re]
    apply Or.inl
    rfl
  convert this using 3
  rw [RCLike.real_smul_eq_coe_smul (K := R) ‖c‖]
  by_cases h : c = 0
  · subst c
    simp
  · have hM_pd : (Aᴴ * A).PosSemidef := by apply posSemidef_conjTranspose_mul_self
    set M := (Aᴴ * A)
    rw [sq]
    simp [SemigroupAction.mul_smul]
    apply CFC.sqrt_unique;
    · simp; rw [CFC.sqrt_mul_sqrt_self M hM_pd.nonneg]
    · exact le_trans ( by norm_num ) (
        smul_le_smul_of_nonneg_left ( show 0 ≤ CFC.sqrt M from by exact (CFC.sqrt_nonneg M) ) ( norm_nonneg c ) );

/-- For square matrices, the trace norm is max Tr[U * A] over unitaries U.-/
lemma unitary_diagEntry_norm_le_one (W : unitaryGroup n ℂ) (i : n) :
    ‖(W : Matrix n n ℂ) i i‖ ≤ 1 := by
  have hsum : ∑ x, ‖(W : Matrix n n ℂ) x i‖ ^ 2 = 1 := Matrix.unitaryGroup_row_norm W i
  have hterm : ‖(W : Matrix n n ℂ) i i‖ ^ 2 ≤ 1 := by
    calc
      ‖(W : Matrix n n ℂ) i i‖ ^ 2 ≤ ∑ x, ‖(W : Matrix n n ℂ) x i‖ ^ 2 := by
        have hterm' : ‖(W : Matrix n n ℂ) i i‖ * ‖(W : Matrix n n ℂ) i i‖ ≤
            ∑ x, ‖(W : Matrix n n ℂ) x i‖ * ‖(W : Matrix n n ℂ) x i‖ := by
          simpa [pow_two] using (Finset.single_le_sum
            (f := fun x : n => ‖(W : Matrix n n ℂ) x i‖ * ‖(W : Matrix n n ℂ) x i‖)
            (fun x hx => by positivity)
            (Finset.mem_univ i))
        simpa [pow_two] using hterm'
      _ = 1 := hsum
  exact (sq_le_sq₀ (show 0 ≤ ‖(W : Matrix n n ℂ) i i‖ by positivity) zero_le_one).mp
    (by simpa [pow_two] using hterm)

/-- For Hermitian matrices over `ℂ`, the trace norm is the maximum real trace pairing against a
unitary. -/
theorem traceNorm_eq_max_tr_U {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    IsGreatest {x : ℝ | ∃ U : unitaryGroup n ℂ, Complex.re ((U.1 * A).trace) = x} A.traceNorm := by
  let sr : n → ℝ := fun i => if hA.eigenvalues i < 0 then -1 else 1
  let s : n → ℂ := Complex.ofReal ∘ sr
  have hsr_val : ∀ i, sr i = -1 ∨ sr i = 1 := by
    intro i
    by_cases hi : hA.eigenvalues i < 0 <;> simp [sr, hi]
  have hsr_mul : ∀ i, sr i * hA.eigenvalues i = abs (hA.eigenvalues i) := by
    intro i
    by_cases hi : hA.eigenvalues i < 0
    · simp [sr, hi, abs_of_neg hi]
    · simp [sr, hi, abs_of_nonneg (le_of_not_gt hi)]
  have hs_unitary : diagonal s ∈ unitaryGroup n ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    have hstar : star (diagonal s : Matrix n n ℂ) = diagonal s := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [s, Matrix.diagonal_apply_eq]
      · simp [Matrix.diagonal_apply_ne' _ hij, Matrix.diagonal_apply_ne _ hij]
    rw [hstar, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      rcases hsr_val i with hsi | hsi <;> simp [s, hsi]
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  let S : unitaryGroup n ℂ := ⟨diagonal s, hs_unitary⟩
  let V : unitaryGroup n ℂ := hA.eigenvectorUnitary
  let D : Matrix n n ℂ := diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  have hspec : A = (V : Matrix n n ℂ) * D * star (V : Matrix n n ℂ) := by
    simpa [V, D] using hA.spectral_theorem
  have hV : star (V : Matrix n n ℂ) * (V : Matrix n n ℂ) = 1 := by
    simpa using unitary.coe_star_mul_self V
  refine ⟨?_, ?_⟩
  · refine ⟨V * S * star V, ?_⟩
    calc
      Complex.re ((((V * S * star V : unitaryGroup n ℂ) : Matrix n n ℂ) * A).trace)
        = Complex.re ((((V : Matrix n n ℂ) * diagonal s * star (V : Matrix n n ℂ)) * A).trace) := by
            rfl
      _ = Complex.re ((((V : Matrix n n ℂ) * diagonal s * star (V : Matrix n n ℂ)) *
          ((V : Matrix n n ℂ) * D * star (V : Matrix n n ℂ))).trace) := by rw [hspec]
      _ = Complex.re (((V : Matrix n n ℂ) * diagonal s * (star (V : Matrix n n ℂ) *
          ((V : Matrix n n ℂ) * D * star (V : Matrix n n ℂ)))).trace) := by
            simp [Matrix.mul_assoc]
      _ = Complex.re (((V : Matrix n n ℂ) * diagonal s * (D * star (V : Matrix n n ℂ))).trace) := by
            have h_inner :
                star (V : Matrix n n ℂ) * ((V : Matrix n n ℂ) * D * star (V : Matrix n n ℂ)) =
                  D * star (V : Matrix n n ℂ) := by
              calc
                star (V : Matrix n n ℂ) * ((V : Matrix n n ℂ) * D * star (V : Matrix n n ℂ))
                    = (star (V : Matrix n n ℂ) * (V : Matrix n n ℂ)) * D *
                        star (V : Matrix n n ℂ) := by
                          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
                _ = 1 * D * star (V : Matrix n n ℂ) := by rw [hV]
                _ = D * star (V : Matrix n n ℂ) := by simp
            rw [h_inner]
      _ = Complex.re (((V : Matrix n n ℂ) * diagonal s * D * star (V : Matrix n n ℂ)).trace) := by
            simp [Matrix.mul_assoc]
      _ = Complex.re (((diagonal s * D) * star (V : Matrix n n ℂ) * V).trace) := by
            rw [show (V : Matrix n n ℂ) * diagonal s * D * star (V : Matrix n n ℂ) =
                (V : Matrix n n ℂ) * (diagonal s * D * star (V : Matrix n n ℂ)) by
                  simp [Matrix.mul_assoc]]
            rw [Matrix.trace_mul_cycle]
            simp [Matrix.mul_assoc]
      _ = Complex.re ((diagonal s * D).trace) := by
            simp [Matrix.mul_assoc, hV]
      _ = ∑ i, abs (hA.eigenvalues i) := by
            simp [D, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, s, hsr_mul]
      _ = A.traceNorm := by
            symm
            exact Matrix.traceNorm_Hermitian_eq_sum_abs_eigenvalues hA
  · intro x hx
    rcases hx with ⟨U, rfl⟩
    let W : unitaryGroup n ℂ := star V * U * V
    have htrace : Complex.re (((U : Matrix n n ℂ) * A).trace) =
        Complex.re (((W : Matrix n n ℂ) * D).trace) := by
      calc
        Complex.re (((U : Matrix n n ℂ) * A).trace)
          = Complex.re (((U : Matrix n n ℂ) * ((V : Matrix n n ℂ) * D *
              star (V : Matrix n n ℂ))).trace) := by rw [hspec]
        _ = Complex.re ((((U : Matrix n n ℂ) * (V : Matrix n n ℂ) * D *
            star (V : Matrix n n ℂ))).trace) := by
              simp [Matrix.mul_assoc]
        _ = Complex.re (((star (V : Matrix n n ℂ) * ((U : Matrix n n ℂ) *
            (V : Matrix n n ℂ)) * D).trace)) := by
              rw [show (U : Matrix n n ℂ) * (V : Matrix n n ℂ) * D * star (V : Matrix n n ℂ) =
                  ((U : Matrix n n ℂ) * (V : Matrix n n ℂ) * D) * star (V : Matrix n n ℂ) by
                    simp [Matrix.mul_assoc]]
              rw [Matrix.trace_mul_cycle]
        _ = Complex.re (((W : Matrix n n ℂ) * D).trace) := by
              have hm :
                  star (V : Matrix n n ℂ) * ((U : Matrix n n ℂ) * (V : Matrix n n ℂ)) * D =
                    ((((star V * U * V : unitaryGroup n ℂ) : Matrix n n ℂ)) * D) := by
                simp [Matrix.mul_assoc]
              rw [hm]
    have hdiag_formula : Complex.re (((W : Matrix n n ℂ) * D).trace) =
        ∑ i, hA.eigenvalues i * Complex.re ((W : Matrix n n ℂ) i i) := by
      simp [D, Matrix.trace, Matrix.mul_diagonal, Complex.mul_re, mul_comm]
    have hdiag_bound : ∀ i, |Complex.re ((W : Matrix n n ℂ) i i)| ≤ 1 := by
      intro i
      exact (Complex.abs_re_le_norm _).trans (unitary_diagEntry_norm_le_one W i)
    have hsum_le :
        ∑ i, hA.eigenvalues i * Complex.re ((W : Matrix n n ℂ) i i) ≤ ∑ i, abs (hA.eigenvalues i) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      have habs_mul : |hA.eigenvalues i * Complex.re ((W : Matrix n n ℂ) i i)| ≤ abs (hA.eigenvalues i) := by
        calc
          |hA.eigenvalues i * Complex.re ((W : Matrix n n ℂ) i i)|
              = abs (hA.eigenvalues i) * |Complex.re ((W : Matrix n n ℂ) i i)| := by rw [abs_mul]
          _ ≤ abs (hA.eigenvalues i) * 1 := by
              exact mul_le_mul_of_nonneg_left (hdiag_bound i) (abs_nonneg _)
          _ = abs (hA.eigenvalues i) := by ring
      exact (le_abs_self _).trans habs_mul
    calc
      Complex.re (((U : Matrix n n ℂ) * A).trace)
        = Complex.re (((W : Matrix n n ℂ) * D).trace) := htrace
      _ = ∑ i, hA.eigenvalues i * Complex.re ((W : Matrix n n ℂ) i i) := hdiag_formula
      _ ≤ ∑ i, abs (hA.eigenvalues i) := hsum_le
      _ = A.traceNorm := by
            symm
            exact Matrix.traceNorm_Hermitian_eq_sum_abs_eigenvalues hA

/-- The trace norm satisfies the triangle inequality on Hermitian matrices. -/
theorem traceNorm_triangleIneq {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A + B).traceNorm ≤ A.traceNorm + B.traceNorm := by
  obtain ⟨Uab, h₁⟩ := (traceNorm_eq_max_tr_U (hA.add hB)).left
  rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re] at h₁
  obtain h₂ := (traceNorm_eq_max_tr_U hA).right
  obtain h₃ := (traceNorm_eq_max_tr_U hB).right
  simp only [upperBounds, Subtype.exists, exists_prop, Set.mem_setOf_eq, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂] at h₂ h₃
  replace h₂ := h₂ Uab.1 Uab.2
  replace h₃ := h₃ Uab.1 Uab.2
  calc
    (A + B).traceNorm = Complex.re ((Uab.1 * A).trace) + Complex.re ((Uab.1 * B).trace) := h₁.symm
    _ ≤ A.traceNorm + Complex.re ((Uab.1 * B).trace) := by
          exact add_le_add_right h₂ _
    _ ≤ A.traceNorm + B.traceNorm := by
          exact add_le_add_left h₃ _

theorem traceNorm_triangleIneq' {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A - B).traceNorm ≤ A.traceNorm + B.traceNorm := by
  rw [sub_eq_add_neg A B, ← traceNorm_eq_neg_self B]
  exact traceNorm_triangleIneq hA hB.neg

theorem PosSemidef.traceNorm_PSD_eq_trace {A : Matrix m m R} (hA : A.PosSemidef) : A.traceNorm = A.trace := by
  have : Aᴴ * A = A^2 := by rw [hA.1, pow_two]
  open MatrixOrder in
  rw [traceNorm, this, CFC.sqrt_sq A, hA.1.re_trace_eq_trace]

end traceNorm

end Matrix
