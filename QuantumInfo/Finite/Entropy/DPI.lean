/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.Finite.Entropy.Relative
import QuantumInfo.ForMathlib.HermitianMat.CfcOrder

noncomputable section

open scoped InnerProductSpace RealInnerProductSpace HermitianMat
open scoped Matrix ComplexOrder
open BigOperators

variable {d d₂ : Type*}
variable [Fintype d] [Fintype d₂]
variable [DecidableEq d] [DecidableEq d₂]
variable {σ : MState d}

/-!
# DPI

This file records the algebraic `Γ_σ` and `T = Γ_{Φ(σ)}⁻¹ ∘ Φ ∘ Γ_σ` infrastructure used in the
standard proof of data processing for sandwiched Rényi quantities.

The weighted Schatten norm interpolation argument itself is not yet formalized here, so this file
keeps only the part of the development that is currently proved and used.
-/

/-- The map `Γ_σ(X) = σ^{1/2} X σ^{1/2}`. -/
noncomputable def Gamma (σ : MState d) (X : Matrix d d ℂ) : Matrix d d ℂ :=
  (σ.M ^ (1 / 2 : ℝ)).mat * X * (σ.M ^ (1 / 2 : ℝ)).mat

/-- The inverse map `Γ_σ⁻¹(X) = σ^{-1/2} X σ^{-1/2}` on the support of a positive definite state. -/
noncomputable def Gamma_inv (σ : MState d) (X : Matrix d d ℂ) : Matrix d d ℂ :=
  (σ.M ^ (-1 / 2 : ℝ)).mat * X * (σ.M ^ (-1 / 2 : ℝ)).mat

/-- The operator `T = Γ_{Φ(σ)}⁻¹ ∘ Φ ∘ Γ_σ`. -/
noncomputable def T_op (Φ : CPTPMap d d₂) (σ : MState d) (X : Matrix d d ℂ) : Matrix d₂ d₂ ℂ :=
  Gamma_inv (Φ σ) (Φ.map (Gamma σ X))

/-- `Γ_σ` as a linear map. -/
noncomputable def Gamma_map (σ : MState d) : MatrixMap d d ℂ :=
  MatrixMap.conj (σ.M ^ (1 / 2 : ℝ)).mat

lemma Gamma_map_eq (σ : MState d) (X : Matrix d d ℂ) :
    Gamma_map σ X = Gamma σ X := by
  dsimp [Gamma_map, Gamma, MatrixMap.conj]
  rw [(σ.M ^ (1 / 2 : ℝ)).H.eq]

lemma Gamma_map_CP (σ : MState d) : (Gamma_map σ).IsCompletelyPositive := by
  simpa [Gamma_map] using MatrixMap.conj_isCompletelyPositive ((σ.M ^ (1 / 2 : ℝ)).mat)

/-- `Γ_σ⁻¹` as a linear map. -/
noncomputable def Gamma_inv_map (σ : MState d) : MatrixMap d d ℂ :=
  MatrixMap.conj (σ.M ^ (-1 / 2 : ℝ)).mat

lemma Gamma_inv_map_eq (σ : MState d) (X : Matrix d d ℂ) :
    Gamma_inv_map σ X = Gamma_inv σ X := by
  dsimp [Gamma_inv_map, Gamma_inv, MatrixMap.conj]
  rw [(σ.M ^ (-1 / 2 : ℝ)).H.eq]

lemma Gamma_inv_map_CP (σ : MState d) : (Gamma_inv_map σ).IsCompletelyPositive := by
  simpa [Gamma_inv_map] using MatrixMap.conj_isCompletelyPositive ((σ.M ^ (-1 / 2 : ℝ)).mat)

/-- `T` as a linear map. -/
noncomputable def T_map (σ : MState d) (Φ : CPTPMap d d₂) : MatrixMap d d₂ ℂ :=
  { toFun := fun X => T_op Φ σ X
    map_add' := fun X Y => by
      unfold T_op Gamma_inv Gamma
      simp [Matrix.mul_add, Matrix.add_mul]
    map_smul' := fun c X => by
      unfold T_op Gamma_inv Gamma
      simp [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc] }

lemma T_map_eq_comp (σ : MState d) (Φ : CPTPMap d d₂) :
    T_map σ Φ = (Gamma_inv_map (Φ σ)).comp (Φ.map.comp (Gamma_map σ)) := by
  ext X
  simp [T_map, T_op, Gamma_map_eq, Gamma_inv_map_eq]

lemma T_is_CP (σ : MState d) (Φ : CPTPMap d d₂) :
    (T_map σ Φ).IsCompletelyPositive := by
  rw [T_map_eq_comp]
  apply MatrixMap.IsCompletelyPositive.comp
  · apply MatrixMap.IsCompletelyPositive.comp
    · exact Gamma_map_CP σ
    · exact Φ.cp
  · exact Gamma_inv_map_CP (Φ σ)

lemma T_is_positive (σ : MState d) (Φ : CPTPMap d d₂) :
    (T_map σ Φ).IsPositive := by
  exact (T_is_CP σ Φ).IsPositive

/-- `Γ_σ(1) = σ`. -/
lemma Gamma_one (σ : MState d) : Gamma σ 1 = σ.M.mat := by
  unfold Gamma
  simpa [Matrix.mul_assoc] using HermitianMat.pow_half_mul (A := σ.M) σ.zero_le

/-- `Γ_σ⁻¹(σ) = 1` for positive definite `σ`. -/
lemma Gamma_inv_self (σ : MState d) (hσ : σ.m.PosDef) :
    Gamma_inv σ σ.M.mat = 1 := by
  -- We use `HermitianMat.cfc_mul` and the fact that $x^{-1/2} * x * x^{-1/2} = 1$ for $x > 0$.
  have h_gamma_inv_sigma : (σ.M.cfc (fun x => x ^ (-1/2 : ℝ))).mat * (σ.M.mat) * (σ.M.cfc (fun x => x ^ (-1/2 : ℝ))).mat = (σ.M.cfc (fun x => x ^ (-1/2 : ℝ) * x * x ^ (-1/2 : ℝ))).mat := by
    have h_gamma_inv_sigma : (σ.M.cfc (fun x => x ^ (-1/2 : ℝ))).mat * (σ.M.cfc id).mat * (σ.M.cfc (fun x => x ^ (-1/2 : ℝ))).mat = (σ.M.cfc (fun x => x ^ (-1/2 : ℝ) * x * x ^ (-1/2 : ℝ))).mat := by
      have h_gamma_inv_sigma : ∀ (f g h : ℝ → ℝ), ContinuousOn f (spectrum ℝ σ.M.mat) → ContinuousOn g (spectrum ℝ σ.M.mat) → ContinuousOn h (spectrum ℝ σ.M.mat) → (σ.M.cfc f).mat * (σ.M.cfc g).mat * (σ.M.cfc h).mat = (σ.M.cfc (fun x => f x * g x * h x)).mat := by
        intro f g h hf hg hh
        have h_gamma_inv_sigma : (σ.M.cfc f).mat * (σ.M.cfc g).mat = (σ.M.cfc (fun x => f x * g x)).mat := by
          symm
          convert HermitianMat.mat_cfc_mul σ.M f g using 1;
        rw [ h_gamma_inv_sigma, ← HermitianMat.mat_cfc_mul ];
        congr! 2
      have h : ∀ x ∈ spectrum ℝ σ.M.mat, x ≠ 0 := by
        norm_num
        intro x hx h_zero
        have h_eigenvalue : ∃ v : d → ℂ, v ≠ 0 ∧ σ.m.mulVec v = x • v := by
          simp_all [ spectrum.mem_iff]
          contrapose! hx;
          exact Matrix.PosDef.isUnit hσ;
        obtain ⟨ v, hv_ne_zero, hv_eigenvalue ⟩ := h_eigenvalue
        rw [Matrix.posDef_iff_dotProduct_mulVec] at hσ
        have := hσ.2 hv_ne_zero
        simp [hv_eigenvalue, h_zero] at this
      apply h_gamma_inv_sigma
      · fun_prop
      · fun_prop
      · fun_prop
    convert h_gamma_inv_sigma using 1;
    ext i j ; simp [ Matrix.mul_apply]
  -- Since $x^{-1/2} * x * x^{-1/2} = 1$ for $x > 0$, we have $(σ.M.cfc (fun x => x ^ (-1/2 : ℝ))).mat * (σ.M.mat) * (σ.M.cfc (fun x => x ^ (-1/2 : ℝ))).mat = (σ.M.cfc (fun x => 1)).mat$.
  have h_gamma_inv_sigma_simplified : (σ.M.cfc (fun x => x ^ (-1/2 : ℝ))).mat * (σ.M.mat) * (σ.M.cfc (fun x => x ^ (-1/2 : ℝ))).mat = (σ.M.cfc (fun x => 1)).mat := by
    convert h_gamma_inv_sigma using 1;
    congr! 1;
    -- Since $x^{-1/2} * x * x^{-1/2} = 1$ for all $x > 0$, the functions are equal.
    have h_eq : ∀ x : ℝ, 0 < x → x ^ (-1 / 2 : ℝ) * x * x ^ (-1 / 2 : ℝ) = 1 := by
      intro x hx
      ring_nf
      norm_num [ hx.ne' ];
      rw [ ← Real.rpow_natCast, ← Real.rpow_mul hx.le ] ; norm_num [ hx.ne' ];
      rw [ Real.rpow_neg_one, inv_mul_cancel₀ hx.ne' ];
    exact Eq.symm (HermitianMat.cfc_congr_of_posDef hσ h_eq);
  convert h_gamma_inv_sigma_simplified using 1;
  ext i j
  simp

/-- The matrix of the output state is the map applied to the input matrix. -/
lemma CPTPMap_apply_MState_M (Φ : CPTPMap d d₂) (σ : MState d) :
    (Φ σ).M.mat = Φ.map σ.M.mat := by
  rfl

/-- The operator `T` is unital whenever `Φ(σ)` is positive definite. -/
theorem T_map_unital (σ : MState d) (Φ : CPTPMap d d₂) (hΦσ : (Φ σ).m.PosDef) :
    (T_map σ Φ) 1 = 1 := by
  dsimp [T_map, T_op]
  rw [Gamma_one σ, ← CPTPMap_apply_MState_M, Gamma_inv_self (Φ σ) hΦσ]

/-
The map T is completely positive.
-/
theorem T_map_is_CP_proof (σ : MState d) (Φ : CPTPMap d d₂) :
    (T_map σ Φ).IsCompletelyPositive := by
  apply T_is_CP

/-
Gamma composed with Gamma inverse is identity.
-/
lemma Gamma_Gamma_inv (σ : MState d) (hσ : σ.m.PosDef) (X : Matrix d d ℂ) :
    Gamma σ (Gamma_inv σ X) = X := by
  -- By definition of Gamma and Gamma_inv, we can simplify the expression.
  have h_simp : (σ.M.cfc (fun x => x ^ (1 / 2 : ℝ))).mat * (σ.M.cfc (fun x => x ^ (-1 / 2 : ℝ))).mat = 1 := by
    symm
    convert HermitianMat.mat_cfc_mul _ _ _ using 1;
    · have h_gamma_gamma_inv : ∀ x ∈ spectrum ℝ σ.M.mat, x ^ (1 / 2 : ℝ) * x ^ (-1 / 2 : ℝ) = 1 := by
        intro x hx
        have hx_pos : 0 < x := by
          have := (Matrix.posDef_iff_dotProduct_mulVec.mp hσ).2;
          obtain ⟨v, hv⟩ : ∃ v : d → ℂ, v ≠ 0 ∧ σ.m.mulVec v = x • v := by
            rw [ spectrum.mem_iff ] at hx;
            simp_all [ Matrix.isUnit_iff_isUnit_det ];
            obtain ⟨ v, hv ⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hx;
            simp_all [ sub_eq_iff_eq_add, Matrix.sub_mulVec ];
            exact ⟨ v, hv.1, hv.2.symm.trans ( by ext i; erw [ Matrix.mulVec_diagonal ] ; aesop ) ⟩;
          specialize this hv.1;
          simp_all [ dotProduct];
          simp_all [ mul_assoc, mul_comm];
          simp_all [ mul_left_comm ( v _ ), Complex.mul_conj, Complex.normSq_eq_norm_sq ];
          norm_cast at this;
          exact lt_of_not_ge fun hx' => this.not_ge <| Finset.sum_nonpos fun i _ => mul_nonpos_of_nonpos_of_nonneg hx' <| sq_nonneg _;
        rw [ ← Real.rpow_add hx_pos ] ; norm_num;
      rw [HermitianMat.cfc_congr (g := fun x ↦ 1)]
      · rw [ HermitianMat.cfc_const ]
        norm_num
      · exact fun x hx => h_gamma_gamma_inv x hx;
  unfold Gamma Gamma_inv; simp_all [ ← mul_assoc ] ;
  simp_all [ mul_assoc, mul_eq_one_comm.mp h_simp ]

/-
If a Hermitian matrix is bounded by M*I, then all its eigenvalues are at most M.
-/
theorem HermitianMat.le_smul_one_imp_eigenvalues_le (A : HermitianMat d ℂ) (M : ℝ)
    (h : A ≤ M • (1 : HermitianMat d ℂ)) (i : d) :
    A.H.eigenvalues i ≤ M := by
  -- By definition of eigenvalues, for any unit vector $v$, we have $\langle v, A v \rangle \leq M$.
  have h_eigenvalue_le_M_step : ∀ (v : EuclideanSpace ℂ d), ‖v‖ = 1 → ⟪v, .toLp 2 <| A.mat.mulVec v⟫_ℂ ≤ M := by
    intro v hv
    have h_inner : ⟪v, .toLp 2 <| A.mat.mulVec v⟫_ℂ ≤ ⟪v, .toLp 2 <| (M • 1 : Matrix d d ℂ).mulVec v⟫_ℂ := by
      have h_inner : ⟪v, .toLp 2 <| ((M • 1 : Matrix d d ℂ) - A.mat).mulVec v⟫_ℂ ≥ 0 := by
        have h_inner_le_M : ∀ (X : HermitianMat d ℂ), X ≥ 0 → ∀ (v : EuclideanSpace ℂ d), ⟪v, .toLp 2 <| X.mat.mulVec v⟫_ℂ ≥ 0 := by
          intro X hX v
          rw [ge_iff_le, HermitianMat.zero_le_iff, Matrix.posSemidef_iff_dotProduct_mulVec] at hX
          have := hX.2 v
          simp [ Matrix.mulVec, dotProduct ] at *
          convert this using 1;
          refine Finset.sum_congr rfl fun _ _ => ?_
          sorry
        convert h_inner_le_M ⟨ _, _ ⟩ _ v;
        all_goals norm_num [ HermitianMat.le_iff ] at *;
        · convert h.1;
        · exact h;
      simp_all [ Matrix.sub_mulVec]
    simp_all [ EuclideanSpace.norm_eq ];
    convert h_inner using 1;
    simp [ Matrix.mulVec, dotProduct, inner ];
    simp [ Matrix.one_apply,mul_assoc];
    simp [ ← Finset.mul_sum];
    simp [ Complex.mul_conj, Complex.normSq_eq_norm_sq ];
    norm_cast ; aesop;
  have := A.H.eigenvectorBasis.orthonormal;
  have := this.1 i;
  have := h_eigenvalue_le_M_step ( A.H.eigenvectorBasis i ) this;
  rw [ show A.mat.mulVec _ = ( Matrix.IsHermitian.eigenvalues A.H i : ℂ ) • ( Matrix.IsHermitian.eigenvectorBasis A.H i ) from ?_ ] at this;
  · simp_all
  · convert A.H.mulVec_eigenvectorBasis i using 1

set_option maxHeartbeats 400000 in
open MatrixOrder in
/-
If all eigenvalues of a Hermitian matrix are at most M, then the matrix is bounded by M*I.
-/
theorem HermitianMat.eigenvalues_le_imp_le_smul_one (A : HermitianMat d ℂ) (M : ℝ)
    (h : ∀ i, A.H.eigenvalues i ≤ M) :
    A ≤ M • (1 : HermitianMat d ℂ) := by
  have := A.H.spectral_theorem.symm;
  -- Since $A$ is Hermitian, we can write it as $A = UDU^*$ where $U$ is unitary and $D$ is diagonal with eigenvalues $\lambda_i$.
  have h_decomp : ∃ U : Matrix d d ℂ, U * star U = 1 ∧ ∃ D : HermitianMat d ℂ, A = U * D * star U ∧ ∀ i, D i i ≤ M := by
    use A.H.eigenvectorUnitary
    constructor; · simp
    use HermitianMat.diagonal ℂ A.H.eigenvalues
    constructor
    · exact this.symm
    · simpa [HermitianMat.diagonal, ← HermitianMat.mat_apply] using h
  obtain ⟨U, hU_unitary, D, hA_eq, hD_le⟩ := h_decomp;
  have hA_le : U * D * star U ≤ U * (M • 1) * star U := by
    have hD_le : D ≤ M • (1 : HermitianMat d ℂ) := by
      sorry
    have := HermitianMat.conj_mono (M := U) hD_le
    simp only [conj, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
    replace this := Subtype.coe_le_coe.mpr this
    simp only [mat_smul, mat_one] at this
    exact this
  rw [ ← hA_eq ] at hA_le
  simp only [Algebra.mul_smul_comm, mul_one, Algebra.smul_mul_assoc, hU_unitary] at hA_le
  exact hA_le

/-- The block matrix [[1, X], [X†, X†X]] is positive semidefinite. -/
theorem block_matrix_posSemidef {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    (X : Matrix k n ℂ) (Y : Matrix k m ℂ) :
    (Matrix.fromBlocks (Yᴴ * Y) (Yᴴ * X) (Xᴴ * Y) (Xᴴ * X)).PosSemidef := by
  set Z : Matrix (m ⊕ n) (m ⊕ n) ℂ :=
    Matrix.fromBlocks (Yᴴ * Y) (Yᴴ * X) (Xᴴ * Y) (Xᴴ * X)
  have hZ : Z = (Matrix.fromBlocks (o := k) Y X 0 0)ᴴ * Matrix.fromBlocks Y X 0 0 := by
    ext i j
    cases i <;> cases j <;> simp [Z, Matrix.fromBlocks_multiply, Matrix.mul_apply]
  rw [hZ]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem block_matrix_one_posSemidef {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (X : Matrix m n ℂ) :
    (Matrix.fromBlocks 1 X Xᴴ (Xᴴ * X)).PosSemidef := by
  simpa using block_matrix_posSemidef X (1 : Matrix m m ℂ)

/-- The Data Processing Inequality for the Sandwiched Renyi relative entropy.
Proved in `https://arxiv.org/pdf/1306.5920`. Seems kind of involved. -/
theorem sandwichedRenyiEntropy_DPI (hα : 1 ≤ α) (ρ σ : MState d) (Φ : CPTPMap d d₂) :
    D̃_ α(Φ ρ‖Φ σ) ≤ D̃_ α(ρ‖σ) := by
  --If we want, we can prove this just for 1 < α, and then use continuity (above) to take the limit as
  -- α → 1.
  sorry

--Helps us track this one sorry for the GQSL
axiom sandwichedRenyiEntropy_DPI_ax : type_of% @sandwichedRenyiEntropy_DPI

/--
info: 'sandwichedRenyiEntropy_DPI_ax' depends on axioms: [propext,
 sandwichedRenyiEntropy_DPI_ax,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms sandwichedRenyiEntropy_DPI_ax
