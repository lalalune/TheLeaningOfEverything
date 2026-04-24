import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import QuantumInfo.ForMathlib.HermitianMat.CFC
import QuantumInfo.ForMathlib.HermitianMat.Inner
import QuantumInfo.ForMathlib.Matrix
import QuantumInfo.ForMathlib.Misc
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.RCLike.Basic

variable {d : Type*} [Fintype d] [DecidableEq d]

open FiniteDimensional
open Matrix
open InnerProductSpace
open ComplexConjugate
open RCLike
open HermitianMat

open scoped InnerProductSpace Matrix HermitianMat ComplexOrder RealInnerProductSpace

namespace HermitianMat

theorem transition_matrix_nonneg (A B : HermitianMat d ℂ) (i j : d) :
    0 ≤ _root_.HermitianMat.transition_matrix A B i j := RCLike.normSq_nonneg _

theorem transition_matrix_eq_inner_mul_inner (A B : HermitianMat d ℂ) (i j : d) :
    (_root_.HermitianMat.transition_matrix A B i j : ℂ) =
      inner ℂ (A.H.eigenvectorBasis i) (B.H.eigenvectorBasis j) *
        inner ℂ (B.H.eigenvectorBasis j) (A.H.eigenvectorBasis i) := by
  unfold _root_.HermitianMat.transition_matrix
  rw [Complex.normSq_eq_conj_mul_self]
  have h_inner :
      (∑ k, star (A.H.eigenvectorBasis i k) * B.H.eigenvectorBasis j k) =
        inner ℂ (A.H.eigenvectorBasis i) (B.H.eigenvectorBasis j) := by
    calc
      (∑ k, star (A.H.eigenvectorBasis i k) * B.H.eigenvectorBasis j k)
        = ∑ k, B.H.eigenvectorBasis j k * star (A.H.eigenvectorBasis i k) := by
            apply Finset.sum_congr rfl
            intro k _
            rw [mul_comm]
      _ = inner ℂ (A.H.eigenvectorBasis i) (B.H.eigenvectorBasis j) := by
            simpa [dotProduct] using
              (EuclideanSpace.inner_eq_star_dotProduct (A.H.eigenvectorBasis i)
                (B.H.eigenvectorBasis j)).symm
  have h_conj :
      (starRingEnd ℂ) (∑ k, star (A.H.eigenvectorBasis i k) * B.H.eigenvectorBasis j k) =
        inner ℂ (B.H.eigenvectorBasis j) (A.H.eigenvectorBasis i) := by
    rw [h_inner]
    simpa using inner_conj_symm (A.H.eigenvectorBasis i) (B.H.eigenvectorBasis j)
  rw [h_conj, h_inner]
  simpa [mul_comm]

theorem transition_row_sum (A B : HermitianMat d ℂ) (i : d) :
    ∑ j : d, _root_.HermitianMat.transition_matrix A B i j = 1 := by
  apply Complex.ofReal_injective
  calc
    ((∑ j : d, _root_.HermitianMat.transition_matrix A B i j : ℝ) : ℂ)
      = ∑ j : d, (_root_.HermitianMat.transition_matrix A B i j : ℂ) := by
              simp
    _ = ∑ j : d,
          inner ℂ (A.H.eigenvectorBasis i) (B.H.eigenvectorBasis j) *
            inner ℂ (B.H.eigenvectorBasis j) (A.H.eigenvectorBasis i) := by
              apply Finset.sum_congr rfl
              intro j _
              exact transition_matrix_eq_inner_mul_inner A B i j
    _ = inner ℂ (A.H.eigenvectorBasis i) (A.H.eigenvectorBasis i) := by
          rw [B.H.eigenvectorBasis.sum_inner_mul_inner]
    _ = 1 := by
          simpa using A.H.eigenvectorBasis.orthonormal.1 i

theorem transition_col_sum (A B : HermitianMat d ℂ) (j : d) :
    ∑ i : d, _root_.HermitianMat.transition_matrix A B i j = 1 := by
  apply Complex.ofReal_injective
  calc
    ((∑ i : d, _root_.HermitianMat.transition_matrix A B i j : ℝ) : ℂ)
      = ∑ i : d, (_root_.HermitianMat.transition_matrix A B i j : ℂ) := by
              simp
    _ = ∑ i : d,
          inner ℂ (A.H.eigenvectorBasis i) (B.H.eigenvectorBasis j) *
            inner ℂ (B.H.eigenvectorBasis j) (A.H.eigenvectorBasis i) := by
              apply Finset.sum_congr rfl
              intro i _
              exact transition_matrix_eq_inner_mul_inner A B i j
    _ = inner ℂ (B.H.eigenvectorBasis j) (B.H.eigenvectorBasis j) := by
          simpa [mul_comm] using
            (A.H.eigenvectorBasis.sum_inner_mul_inner (B.H.eigenvectorBasis j)
              (B.H.eigenvectorBasis j))
    _ = 1 := by
          simpa using B.H.eigenvectorBasis.orthonormal.1 j

set_option maxHeartbeats 3000000

theorem inner_cfc_cross (A B : HermitianMat d ℂ) (f : ℝ → ℝ) :
    ⟪A, B.cfc f⟫ = ∑ i : d, ∑ j : d, A.H.eigenvalues i * f (B.H.eigenvalues j) * _root_.HermitianMat.transition_matrix A B i j := by
  have hA :
      A.mat =
        ∑ i, (A.H.eigenvalues i) •
          Matrix.vecMulVec (A.H.eigenvectorBasis i) (star (A.H.eigenvectorBasis i)) := by
    nth_rw 1 [A.H.spectral_theorem]
    ext x y
    simp only [Matrix.sum_apply]
    simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.vecMulVec, Algebra.smul_def,
      mul_assoc, mul_comm]
  have hB :
      (B.cfc f).mat =
        ∑ j, f (B.H.eigenvalues j) •
          Matrix.vecMulVec (B.H.eigenvectorBasis j) (star (B.H.eigenvectorBasis j)) := by
    rw [B.cfc_toMat_eq_sum_smul_proj]
    refine Finset.sum_congr rfl ?_
    intro j _
    congr 1
    ext x y
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single, Matrix.vecMulVec,
      Matrix.IsHermitian.eigenvectorUnitary_apply, Finset.sum_mul]
    rw [Finset.sum_eq_single j]
    · simp [mul_comm]
    · intro j' _ hj'
      have hjj' : j ≠ j' := by simpa [eq_comm] using hj'
      simp [hjj']
    · intro hj
      simp [hj]
  apply Complex.ofReal_injective
  calc
    ((⟪A, B.cfc f⟫ : ℝ) : ℂ) = (A.mat * (B.cfc f).mat).trace := by
      simpa using (HermitianMat.inner_eq_trace_rc A (B.cfc f))
    _ = ((∑ i, (A.H.eigenvalues i) •
          Matrix.vecMulVec (A.H.eigenvectorBasis i) (star (A.H.eigenvectorBasis i)) :
            Matrix d d ℂ) * (B.cfc f).mat).trace := by
      exact congrArg (fun M : Matrix d d ℂ => (M * (B.cfc f).mat).trace) hA
    _ = ((∑ i, (A.H.eigenvalues i) •
          Matrix.vecMulVec (A.H.eigenvectorBasis i) (star (A.H.eigenvectorBasis i)) :
            Matrix d d ℂ) *
          (∑ j, f (B.H.eigenvalues j) •
            Matrix.vecMulVec (B.H.eigenvectorBasis j) (star (B.H.eigenvectorBasis j)) :
              Matrix d d ℂ)).trace := by
      exact congrArg
        (fun M : Matrix d d ℂ =>
          ((∑ i, (A.H.eigenvalues i) •
            Matrix.vecMulVec (A.H.eigenvectorBasis i) (star (A.H.eigenvectorBasis i)) :
              Matrix d d ℂ) * M).trace) hB
    _ = ↑(∑ i : d, ∑ j : d,
          A.H.eigenvalues i * f (B.H.eigenvalues j) *
            _root_.HermitianMat.transition_matrix A B i j) := by
      simp [Matrix.trace_sum, Matrix.trace_smul, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      have htrace :
          Matrix.trace
              (Matrix.vecMulVec (A.H.eigenvectorBasis i) (star (A.H.eigenvectorBasis i)) *
                Matrix.vecMulVec (B.H.eigenvectorBasis j) (star (B.H.eigenvectorBasis j))) =
            (_root_.HermitianMat.transition_matrix A B i j : ℂ) := by
        calc
          Matrix.trace
              (Matrix.vecMulVec (A.H.eigenvectorBasis i) (star (A.H.eigenvectorBasis i)) *
                Matrix.vecMulVec (B.H.eigenvectorBasis j) (star (B.H.eigenvectorBasis j))) =
            inner ℂ (B.H.eigenvectorBasis j) (A.H.eigenvectorBasis i) *
              inner ℂ (A.H.eigenvectorBasis i) (B.H.eigenvectorBasis j) := by
                simpa [Matrix.rankOne, Matrix.vecMulVec] using
                  (Matrix.trace_rankOne_mul_rankOne (u := A.H.eigenvectorBasis i)
                    (v := B.H.eigenvectorBasis j))
          _ = (_root_.HermitianMat.transition_matrix A B i j : ℂ) := by
            rw [mul_comm, ← transition_matrix_eq_inner_mul_inner]
      rw [htrace]
      ring_nf

theorem transition_matrix_self (A : HermitianMat d ℂ) (i j : d) :
    _root_.HermitianMat.transition_matrix A A i j = if i = j then 1 else 0 := by
  apply Complex.ofReal_injective
  rw [transition_matrix_eq_inner_mul_inner]
  by_cases hij : i = j
  · subst hij
    simpa using (A.H.eigenvectorBasis.orthonormal.1 j : inner ℂ (A.H.eigenvectorBasis j)
      (A.H.eigenvectorBasis j) = 1)
  · have horth : inner ℂ (A.H.eigenvectorBasis i) (A.H.eigenvectorBasis j) = 0 := by
      simpa using A.H.eigenvectorBasis.orthonormal.2 hij
    simp [hij, horth]

private lemma mulVec_eq_zero_iff_inner_eigenvector_zero_aux
    (A : HermitianMat d ℂ) (x : EuclideanSpace ℂ d) :
    A.mat.mulVec x = 0 ↔ ∀ i, A.H.eigenvalues i ≠ 0 → inner ℂ (A.H.eigenvectorBasis i) x = 0 := by
  exact HermitianMat.mulVec_eq_zero_iff_inner_eigenvector_zero A x

private theorem transition_matrix_eq_zero_of_right_eigenvalue_zero
    (A B : HermitianMat d ℂ) (h_ker : B.ker ≤ A.ker) {i j : d}
    (hi : A.H.eigenvalues i ≠ 0) (hj : B.H.eigenvalues j = 0) :
    _root_.HermitianMat.transition_matrix A B i j = 0 := by
  have hB_mul : B.mat.mulVec (B.H.eigenvectorBasis j) = 0 := by
    simpa [hj] using B.H.mulVec_eigenvectorBasis j
  have hB_ker : B.H.eigenvectorBasis j ∈ B.ker := by
    exact (HermitianMat.mem_ker_iff_mulVec_zero B (B.H.eigenvectorBasis j)).mpr hB_mul
  have hA_ker : B.H.eigenvectorBasis j ∈ A.ker := h_ker hB_ker
  have hA_mul : A.mat.mulVec (B.H.eigenvectorBasis j) = 0 := by
    exact (HermitianMat.mem_ker_iff_mulVec_zero A (B.H.eigenvectorBasis j)).mp hA_ker
  have hinner :
      inner ℂ (A.H.eigenvectorBasis i) (B.H.eigenvectorBasis j) = 0 :=
    (mulVec_eq_zero_iff_inner_eigenvector_zero_aux A (B.H.eigenvectorBasis j)).1 hA_mul i hi
  apply Complex.ofReal_injective
  rw [transition_matrix_eq_inner_mul_inner]
  simp [hinner]

theorem inner_cfc_self (A : HermitianMat d ℂ) (f : ℝ → ℝ) :
    ⟪A, A.cfc f⟫ = ∑ i : d, A.H.eigenvalues i * f (A.H.eigenvalues i) := by
  rw [inner_cfc_cross]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.sum_eq_single i]
  · simp [transition_matrix_self]
  · intro j _ hij
    have hij' : i ≠ j := by simpa [eq_comm] using hij
    simp [transition_matrix_self, hij']
  · intro hi
    exfalso
    exact hi (Finset.mem_univ i)

theorem klein_algebraic_bound (A B : HermitianMat d ℂ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hA_tr : A.trace = 1) (hB_tr : B.trace = 1) (h_ker : B.ker ≤ A.ker) :
    trace (A - B) ≤ ⟪A, A.log - B.log⟫ := by
  let μ : d → ℝ := fun i => ∑ j : d, B.H.eigenvalues j * _root_.HermitianMat.transition_matrix A B i j
  have hA_psd := HermitianMat.zero_le_iff.mp hA
  have hB_psd := HermitianMat.zero_le_iff.mp hB
  have hμ_nonneg : ∀ i, 0 ≤ μ i := by
    intro i
    unfold μ
    refine Finset.sum_nonneg ?_
    intro j _
    exact mul_nonneg (hB_psd.eigenvalues_nonneg j) (transition_matrix_nonneg A B i j)
  have hpointwise :
      ∀ i,
        A.H.eigenvalues i - μ i ≤
          A.H.eigenvalues i * Real.log (A.H.eigenvalues i) -
            A.H.eigenvalues i *
              ∑ j : d, _root_.HermitianMat.transition_matrix A B i j * Real.log (B.H.eigenvalues j) := by
    intro i
    by_cases hi0 : A.H.eigenvalues i = 0
    · simpa [μ, hi0, mul_comm, mul_left_comm, mul_assoc] using (neg_nonpos.mpr (hμ_nonneg i))
    · have hi_pos : 0 < A.H.eigenvalues i := by
        exact lt_of_le_of_ne (hA_psd.eigenvalues_nonneg i) (by simpa [eq_comm] using hi0)
      set s : Finset d :=
        Finset.univ.filter fun j => _root_.HermitianMat.transition_matrix A B i j ≠ 0 with hs
      have hweights :
          Finset.sum s (fun j => _root_.HermitianMat.transition_matrix A B i j) = 1 := by
        rw [hs, Finset.sum_filter_ne_zero]
        exact transition_row_sum A B i
      have hmem :
          ∀ j ∈ s, B.H.eigenvalues j ∈ Set.Ioi (0 : ℝ) := by
        intro j hj
        have hjnz : _root_.HermitianMat.transition_matrix A B i j ≠ 0 := by
          simpa [s] using hj
        have hjpos : 0 < B.H.eigenvalues j := by
          refine lt_of_le_of_ne (hB_psd.eigenvalues_nonneg j) ?_
          intro hj0
          exact hjnz (transition_matrix_eq_zero_of_right_eigenvalue_zero A B h_ker hi0 (by simpa [eq_comm] using hj0))
        exact hjpos
      have hlog_filter :
          Finset.sum s (fun j => _root_.HermitianMat.transition_matrix A B i j * Real.log (B.H.eigenvalues j)) ≤
            Real.log
              (Finset.sum s (fun j => _root_.HermitianMat.transition_matrix A B i j * B.H.eigenvalues j)) := by
        simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
          (strictConcaveOn_log_Ioi.concaveOn.le_map_sum
            (t := s)
            (w := fun j => _root_.HermitianMat.transition_matrix A B i j)
            (p := fun j => B.H.eigenvalues j)
            (h₀ := fun j hj => transition_matrix_nonneg A B i j)
            (h₁ := hweights)
            hmem)
      have hlog_left :
          Finset.sum s (fun j => _root_.HermitianMat.transition_matrix A B i j * Real.log (B.H.eigenvalues j)) =
            ∑ j : d, _root_.HermitianMat.transition_matrix A B i j * Real.log (B.H.eigenvalues j) := by
        rw [hs, Finset.sum_filter]
        refine Finset.sum_congr rfl ?_
        intro j _
        by_cases hj0 : _root_.HermitianMat.transition_matrix A B i j = 0
        · simp [hj0]
        · rw [if_pos hj0]
      have hμ_filter :
          Finset.sum s (fun j => _root_.HermitianMat.transition_matrix A B i j * B.H.eigenvalues j) = μ i := by
        rw [hs, Finset.sum_filter]
        unfold μ
        refine Finset.sum_congr rfl ?_
        intro j _
        by_cases hj0 : _root_.HermitianMat.transition_matrix A B i j = 0
        · simp [hj0]
        · rw [if_pos hj0, mul_comm]
      have hlog :
          ∑ j : d, _root_.HermitianMat.transition_matrix A B i j * Real.log (B.H.eigenvalues j) ≤
            Real.log (μ i) := by
        rw [← hlog_left, ← hμ_filter]
        exact hlog_filter
      have hs_nonempty : s.Nonempty := by
        by_contra hs
        simpa [Finset.not_nonempty_iff_eq_empty.mp hs] using hweights
      obtain ⟨j, hj⟩ := hs_nonempty
      have hjw_pos : 0 < _root_.HermitianMat.transition_matrix A B i j := by
        refine lt_of_le_of_ne (transition_matrix_nonneg A B i j) ?_
        simpa [eq_comm, s] using hj
      have hjb_pos : 0 < B.H.eigenvalues j := hmem j hj
      have hμ_pos : 0 < μ i := by
        have :
            0 < Finset.sum s (fun j => _root_.HermitianMat.transition_matrix A B i j * B.H.eigenvalues j) := by
          refine Finset.sum_pos' ?_ ⟨j, hj, mul_pos hjw_pos hjb_pos⟩
          intro k hk
          exact mul_nonneg (transition_matrix_nonneg A B i k) (hB_psd.eigenvalues_nonneg k)
        rwa [hμ_filter] at this
      have hscalar_raw :
          A.H.eigenvalues i * Real.log (μ i / A.H.eigenvalues i) ≤ μ i - A.H.eigenvalues i := by
        have hlog_raw :
            Real.log (μ i / A.H.eigenvalues i) ≤ μ i / A.H.eigenvalues i - 1 :=
          Real.log_le_sub_one_of_pos (div_pos hμ_pos hi_pos)
        have hmul := mul_le_mul_of_nonneg_left hlog_raw hi_pos.le
        calc
          A.H.eigenvalues i * Real.log (μ i / A.H.eigenvalues i)
              ≤ A.H.eigenvalues i * (μ i / A.H.eigenvalues i - 1) := hmul
          _ = μ i - A.H.eigenvalues i := by
              field_simp [hi_pos.ne']
      have hscalar :
          A.H.eigenvalues i - μ i ≤
            A.H.eigenvalues i * Real.log (A.H.eigenvalues i) -
              A.H.eigenvalues i * Real.log (μ i) := by
        rw [Real.log_div hμ_pos.ne' hi_pos.ne'] at hscalar_raw
        linarith
      have hscaled_log :
          A.H.eigenvalues i *
              ∑ j : d, _root_.HermitianMat.transition_matrix A B i j * Real.log (B.H.eigenvalues j) ≤
            A.H.eigenvalues i * Real.log (μ i) := by
        exact mul_le_mul_of_nonneg_left hlog hi_pos.le
      linarith
  have hsum :
      ∑ i : d,
        (A.H.eigenvalues i - μ i) ≤
          ∑ i : d,
            (A.H.eigenvalues i * Real.log (A.H.eigenvalues i) -
              A.H.eigenvalues i *
                ∑ j : d, _root_.HermitianMat.transition_matrix A B i j * Real.log (B.H.eigenvalues j)) :=
    Finset.sum_le_sum (fun i _ => hpointwise i)
  have hμ_sum : ∑ i : d, μ i = 1 := by
    unfold μ
    rw [Finset.sum_comm]
    calc
      ∑ j : d, ∑ i : d, B.H.eigenvalues j * _root_.HermitianMat.transition_matrix A B i j
        = ∑ j : d, B.H.eigenvalues j * ∑ i : d, _root_.HermitianMat.transition_matrix A B i j := by
            refine Finset.sum_congr rfl ?_
            intro j _
            rw [Finset.mul_sum]
      _ = ∑ j : d, B.H.eigenvalues j := by
            refine Finset.sum_congr rfl ?_
            intro j _
            rw [transition_col_sum A B j, mul_one]
      _ = 1 := by simpa [hB_tr] using B.sum_eigenvalues_eq_trace
  have hA_sum : ∑ i : d, A.H.eigenvalues i = 1 := by
    simpa [hA_tr] using A.sum_eigenvalues_eq_trace
  have hleft : ∑ i : d, (A.H.eigenvalues i - μ i) = trace (A - B) := by
    calc
      ∑ i : d, (A.H.eigenvalues i - μ i)
          = (∑ i : d, A.H.eigenvalues i) - ∑ i : d, μ i := by
              rw [Finset.sum_sub_distrib]
      _ = 1 - 1 := by rw [hA_sum, hμ_sum]
      _ = trace (A - B) := by
              rw [HermitianMat.trace_sub, hA_tr, hB_tr]
  have hright :
      ∑ i : d,
        (A.H.eigenvalues i * Real.log (A.H.eigenvalues i) -
          A.H.eigenvalues i *
            ∑ j : d, _root_.HermitianMat.transition_matrix A B i j * Real.log (B.H.eigenvalues j)) =
      ⟪A, A.log - B.log⟫ := by
    have hdouble :
        ∑ i : d, A.H.eigenvalues i *
          ∑ j : d, _root_.HermitianMat.transition_matrix A B i j * Real.log (B.H.eigenvalues j) =
        ∑ i : d, ∑ j : d,
          A.H.eigenvalues i * Real.log (B.H.eigenvalues j) *
            _root_.HermitianMat.transition_matrix A B i j := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring
    calc
      ∑ i : d,
          (A.H.eigenvalues i * Real.log (A.H.eigenvalues i) -
            A.H.eigenvalues i *
              ∑ j : d, _root_.HermitianMat.transition_matrix A B i j * Real.log (B.H.eigenvalues j))
          = (∑ i : d, A.H.eigenvalues i * Real.log (A.H.eigenvalues i)) -
              ∑ i : d, A.H.eigenvalues i *
                ∑ j : d, _root_.HermitianMat.transition_matrix A B i j * Real.log (B.H.eigenvalues j) := by
                  rw [Finset.sum_sub_distrib]
      _ = (∑ i : d, A.H.eigenvalues i * Real.log (A.H.eigenvalues i)) -
            ∑ i : d, ∑ j : d,
              A.H.eigenvalues i * Real.log (B.H.eigenvalues j) *
                _root_.HermitianMat.transition_matrix A B i j := by
                  rw [hdouble]
      _ = ⟪A, A.log - B.log⟫ := by
            rw [inner_sub_right, HermitianMat.log, HermitianMat.log, inner_cfc_self, inner_cfc_cross]
  rw [hleft, hright] at hsum
  exact hsum

theorem klein_inequality (A B : HermitianMat d ℂ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hA_tr : A.trace = 1) (hB_tr : B.trace = 1) (h_ker : B.ker ≤ A.ker) :
    0 ≤ ⟪A, A.cfc Real.log - B.cfc Real.log⟫ := by
  simpa [hA_tr, hB_tr] using klein_algebraic_bound A B hA hB hA_tr hB_tr h_ker

end HermitianMat
