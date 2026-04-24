/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef

import QuantumInfo.ForMathlib.Matrix

open BigOperators
open Classical

namespace LinearMap
section unitary

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]

open Module.End

@[simp]
theorem unitary_star_apply_eq (U : unitary (E →ₗ[𝕜] E)) (v : E) :
    (star U.val) (U.val v) = v := by
  rw [← mul_apply, (unitary.mem_iff.mp U.prop).left, one_apply]

@[simp]
theorem unitary_apply_star_eq (U : unitary (E →ₗ[𝕜] E)) (v : E) :
    U.val ((star U.val) v) = v := by
  rw [← mul_apply, (unitary.mem_iff.mp U.prop).right, one_apply]

noncomputable def unitaryToLinearEquiv (U : unitary (E →ₗ[𝕜] E)) : E ≃ₗ[𝕜] E where
  toFun := U.1
  invFun := fun x => (star (U : E →ₗ[𝕜] E)) x
  left_inv := unitary_star_apply_eq U
  right_inv := unitary_apply_star_eq U
  map_add' := U.1.map_add
  map_smul' := U.1.map_smul

noncomputable def unitaryToLinearIsometryEquiv (U : unitary (E →ₗ[𝕜] E)) : E ≃ₗᵢ[𝕜] E := by
  refine (unitaryToLinearEquiv U).isometryOfInner ?_
  intro x y
  change inner 𝕜 (U.1 x) (U.1 y) = inner 𝕜 x y
  rw [← LinearMap.adjoint_inner_right U.1]
  rw [show (LinearMap.adjoint U.1) = star U.1 by rfl]
  rw [← mul_apply]
  rw [(unitary.mem_iff.mp U.prop).left]
  simp

/-- Conjugating a linear map by a unitary operator gives a map whose μ-eigenspace is
  isomorphic (same dimension) as those of the original linear map. -/
noncomputable def conj_unitary_eigenspace_equiv (T : E →ₗ[𝕜] E) (U : unitary (E →ₗ[𝕜] E)) (μ : 𝕜) :
    eigenspace T μ ≃ₗ[𝕜] eigenspace (U.val * T * star (U.val)) μ where
  toFun v := ⟨U.val v.val, by
    have hv := v.2
    rw [mem_eigenspace_iff] at hv ⊢
    simp [hv]⟩
  invFun v := ⟨(star U.val) v, by
    have hv := v.2
    rw [mem_eigenspace_iff] at hv ⊢
    simpa using congrArg ((star U.val) ·) hv⟩
  map_add' := by simp
  map_smul' := by simp
  left_inv _ := by simp
  right_inv _ := by simp

end unitary
namespace IsSymmetric

open Module.End

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {T : E →ₗ[𝕜] E}

/-- A symmetric operator conjugated by a unitary is symmetric. -/
theorem conj_unitary_IsSymmetric (U : unitary (E →ₗ[𝕜] E)) (hT : T.IsSymmetric) :
    (U.val * T * star U.val).IsSymmetric := by
  intro i j
  rw [mul_assoc, mul_apply, ← LinearMap.adjoint_inner_right]
  rw [mul_apply, mul_apply, mul_apply, ← LinearMap.adjoint_inner_left U.val]
  exact hT (star U.val <| i) (star U.val j)

variable {n : ℕ} (hn : Module.finrank 𝕜 E = n)

/-- There is an equivalence between the eigenvalues of a finite dimensional symmetric operator,
and the eigenvalues of that operator conjugated by a unitary. -/
noncomputable def conj_unitary_eigenvalue_equiv (U : unitary (E →ₗ[𝕜] E)) (hT : T.IsSymmetric) :
    { σ : Equiv.Perm (Fin n) // (hT.conj_unitary_IsSymmetric U).eigenvalues hn = hT.eigenvalues hn ∘ σ } := by
  let hT' : (U.1 * T * star U.1).IsSymmetric := hT.conj_unitary_IsSymmetric U
  let b0 : OrthonormalBasis (Fin n) 𝕜 E := hT'.eigenvectorBasis hn
  let b1 : OrthonormalBasis (Fin n) 𝕜 E := (hT.eigenvectorBasis hn).map (unitaryToLinearIsometryEquiv U)
  let W : Matrix (Fin n) (Fin n) 𝕜 := b0.toBasis.toMatrix b1.toBasis
  let D0 : Matrix (Fin n) (Fin n) 𝕜 := Matrix.diagonal (fun i => ((hT'.eigenvalues hn i : ℝ) : 𝕜))
  let D1 : Matrix (Fin n) (Fin n) 𝕜 := Matrix.diagonal (fun i => ((hT.eigenvalues hn i : ℝ) : 𝕜))
  have hb1 : LinearMap.toMatrix b1.toBasis b1.toBasis (U.1 * T * star U.1) = D1 := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    have h : (U.1 * T * star U.1) (b1 j) = (hT.eigenvalues hn j : 𝕜) • b1 j := by
      change U.1 (T ((star U.1) (U.1 ((hT.eigenvectorBasis hn) j)))) =
          (hT.eigenvalues hn j : 𝕜) • U.1 ((hT.eigenvectorBasis hn) j)
      rw [unitary_star_apply_eq U ((hT.eigenvectorBasis hn) j)]
      simpa using congrArg U.1 (hT.apply_eigenvectorBasis hn j)
    have h' := congrArg (fun x => b1.repr x i) h
    by_cases hij : i = j
    · subst hij
      simpa [D1, Matrix.diagonal, OrthonormalBasis.repr_self, EuclideanSpace.single_apply,
        RCLike.real_smul_eq_coe_mul] using h'
    · simpa [D1, Matrix.diagonal, OrthonormalBasis.repr_self, EuclideanSpace.single_apply, hij,
        RCLike.real_smul_eq_coe_mul] using h'
  have hb0 : LinearMap.toMatrix b0.toBasis b0.toBasis (U.1 * T * star U.1) = D0 := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    have h'' : b0.repr ((U.1 * T * star U.1) (b0 j)) i = (hT'.eigenvalues hn i : 𝕜) * b0.repr (b0 j) i := by
      simpa [b0] using hT'.eigenvectorBasis_apply_self_apply hn (b0 j) i
    by_cases hij : i = j
    · subst hij
      simpa [D0, Matrix.diagonal, OrthonormalBasis.repr_self, EuclideanSpace.single_apply] using h''
    · simpa [D0, Matrix.diagonal, OrthonormalBasis.repr_self, EuclideanSpace.single_apply, hij] using h''
  have hW : W ∈ Matrix.unitaryGroup (Fin n) 𝕜 := by
    simpa [W, b0, b1] using b0.toMatrix_orthonormalBasis_mem_unitary b1
  have hWstar : b1.toBasis.toMatrix b0.toBasis = Matrix.conjTranspose W := by
    calc
      b1.toBasis.toMatrix b0.toBasis = (star W * W) * b1.toBasis.toMatrix b0.toBasis := by
        rw [(Matrix.mem_unitaryGroup_iff').mp hW]
        simp
      _ = star W * (W * b1.toBasis.toMatrix b0.toBasis) := by rw [Matrix.mul_assoc]
      _ = star W * 1 := by rw [Module.Basis.toMatrix_mul_toMatrix_flip]
      _ = Matrix.conjTranspose W := by simp [Matrix.star_eq_conjTranspose]
  have hsim : D0 = W * D1 * Matrix.conjTranspose W := by
    have hchange := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
      (b := b0.toBasis) (b' := b1.toBasis) (c := b0.toBasis) (c' := b1.toBasis)
      (f := U.1 * T * star U.1)
    rw [hb0, hb1, hWstar] at hchange
    simpa [W, D0, D1, Matrix.mul_assoc] using hchange.symm
  have hD0 : D0.IsHermitian := by
    change Matrix.IsHermitian (Matrix.diagonal (fun i => ((hT'.eigenvalues hn i : ℝ) : 𝕜)))
    rw [Matrix.isHermitian_diagonal_iff]
    intro i
    simp [isSelfAdjoint_iff]
  have h1U : (1 : Matrix (Fin n) (Fin n) 𝕜) ∈ Matrix.unitaryGroup (Fin n) 𝕜 := by
    rw [Matrix.mem_unitaryGroup_iff]
    simp
  let hexists0 := Matrix.IsHermitian.eigenvalues_eq_of_unitary_similarity_diagonal
    (hA := hD0) (hU := h1U) (f := hT'.eigenvalues hn) (by simp [D0])
  let hexists1 := Matrix.IsHermitian.eigenvalues_eq_of_unitary_similarity_diagonal
    (hA := hD0) (hU := hW) (f := hT.eigenvalues hn) hsim
  let σ0 : Equiv.Perm (Fin n) := Classical.choose hexists0
  let σ1 : Equiv.Perm (Fin n) := Classical.choose hexists1
  have hσ0 : hD0.eigenvalues ∘ σ0 = hT'.eigenvalues hn := Classical.choose_spec hexists0
  have hσ1 : hD0.eigenvalues ∘ σ1 = hT.eigenvalues hn := Classical.choose_spec hexists1
  refine ⟨σ0.trans σ1.symm, ?_⟩
  ext i
  have h0' : hT'.eigenvalues hn i = hD0.eigenvalues (σ0 i) := by
    simpa [Function.comp] using (congrFun hσ0 i).symm
  have h1' : hD0.eigenvalues (σ0 i) = hT.eigenvalues hn (σ1.symm (σ0 i)) := by
    simpa [Function.comp] using congrFun hσ1 (σ1.symm (σ0 i))
  simpa [Function.comp, σ0, σ1] using h0'.trans h1'

end IsSymmetric
end LinearMap
