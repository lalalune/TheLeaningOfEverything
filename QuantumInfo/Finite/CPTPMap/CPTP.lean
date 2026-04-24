/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.Finite.CPTPMap.Bundled
import QuantumInfo.Finite.Unitary
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Completely Positive Trace Preserving maps

A `CPTPMap` is a `ℂ`-linear map between matrices (`MatrixMap` is an alias), bundled with the facts that it
`IsCompletelyPositive` and `IsTracePreserving`. CPTP maps are typically regarded as the "most general quantum
operation", as they map density matrices (`MState`s) to density matrices. The type `PTPMap`, for maps that are
positive (but not necessarily completely positive) is also declared.

A large portion of the theory is in terms of the Choi matrix (`MatrixMap.choi_matrix`), as the positive-definiteness
of this matrix corresponds to being a CP map. This is [Choi's theorem on CP maps](https://en.wikipedia.org/wiki/Choi%27s_theorem_on_completely_positive_maps).

This file also defines several important examples of, classes of, and operations on, CPTPMaps:
 * `compose`: Composition of maps
 * `id`: The identity map
 * `replacement`: The replacement channel that always outputs the same state
 * `prod`: Tensor product of two CPTP maps, with notation M₁ ⊗ M₂
 * `piProd`: Tensor product of finitely many CPTP maps (Pi-type product)
 * `of_unitary`: The CPTP map corresponding to a unitary opeation `U`
 * `IsUnitary`: Predicate whether the map corresponds to any unitary
 * `purify`: Purifying a channel into a unitary on a larger Hilbert space
 * `complementary`: The complementary channel to its purification
 * `IsEntanglementBreaking`, `IsDegradable`, `IsAntidegradable`: Entanglement breaking, degradable and antidegradable channels.
 * `SWAP`, `assoc`, `assoc'`, `traceLeft`, `traceRight`: The CPTP maps corresponding to important operations on states. These correspond directly to `MState.SWAP`, `MState.assoc`, `MState.assoc'`, `MState.traceLeft`, and `MState.traceRight`.
-/

variable {dIn dOut dOut₂ : Type*} [Fintype dIn] [Fintype dOut] [Fintype dOut₂]

namespace CPTPMap
noncomputable section
open scoped Matrix ComplexOrder

variable [DecidableEq dIn]

variable {dM : Type*} [Fintype dM] [DecidableEq dM]
variable {dM₂ : Type*} [Fintype dM₂] [DecidableEq dM₂]
variable (Λ : CPTPMap dIn dOut)

/-- The Choi matrix of a CPTPMap. -/
@[reducible]
def choi := Λ.map.choi_matrix

/-- Two CPTPMaps are equal if their Choi matrices are equal. -/
theorem choi_ext {Λ₁ Λ₂ : CPTPMap dIn dOut} (h : Λ₁.choi = Λ₂.choi) : Λ₁ = Λ₂ := by
  ext1
  exact MatrixMap.choi_equiv.injective h

/-- The Choi matrix of a channel is PSD. -/
theorem choi_PSD_of_CPTP : Λ.map.choi_matrix.PosSemidef :=
  Λ.map.choi_PSD_iff_CP_map.1 Λ.cp

/-- The trace of a Choi matrix of a CPTP map is the cardinality of the input space. -/
@[simp]
theorem Tr_of_choi_of_CPTP : Λ.choi.trace =
    (Finset.univ (α := dIn)).card :=
  Λ.TP.trace_choi

/-- Construct a CPTP map from a PSD Choi matrix with correct partial trace. -/
def CPTP_of_choi_PSD_Tr {M : Matrix (dOut × dIn) (dOut × dIn) ℂ} (h₁ : M.PosSemidef)
    (h₂ : M.traceLeft = 1) : CPTPMap dIn dOut where
  toLinearMap := MatrixMap.of_choi_matrix M
  cp := (MatrixMap.choi_PSD_iff_CP_map (MatrixMap.of_choi_matrix M)).2
      ((MatrixMap.map_choi_inv M).symm ▸ h₁)
  TP := (MatrixMap.of_choi_matrix M).IsTracePreserving_iff_trace_choi.2
    ((MatrixMap.map_choi_inv M).symm ▸ h₂)

@[simp]
theorem choi_of_CPTP_of_choi (M : Matrix (dOut × dIn) (dOut × dIn) ℂ) {h₁} {h₂} :
    (CPTP_of_choi_PSD_Tr (M := M) h₁ h₂).choi = M := by
  simp only [choi, CPTP_of_choi_PSD_Tr]
  rw [MatrixMap.map_choi_inv]

theorem mat_coe_eq_apply_mat [DecidableEq dOut] (ρ : MState dIn) : (Λ ρ).m = Λ.map ρ.m :=
  rfl

@[ext]
theorem funext [DecidableEq dOut] {Λ₁ Λ₂ : CPTPMap dIn dOut} (h : ∀ ρ, Λ₁ ρ = Λ₂ ρ) : Λ₁ = Λ₂ :=
  DFunLike.ext _ _ h

/-- The composition of CPTPMaps, as a CPTPMap. -/
def compose (Λ₂ : CPTPMap dM dOut) (Λ₁ : CPTPMap dIn dM) : CPTPMap dIn dOut where
  toLinearMap := Λ₂.map ∘ₗ Λ₁.map
  cp := Λ₁.cp.comp Λ₂.cp
  TP := Λ₁.TP.comp Λ₂.TP

infixl:75 "∘ₘ" => CPTPMap.compose

/-- Composition of CPTPMaps by `CPTPMap.compose` is compatible with the `instFunLike` action. -/
@[simp]
theorem compose_eq [DecidableEq dOut] {Λ₁ : CPTPMap dIn dM} {Λ₂ : CPTPMap dM dOut} : ∀ρ, (Λ₂ ∘ₘ Λ₁) ρ = Λ₂ (Λ₁ ρ) :=
  fun _ ↦ rfl

/-- Composition of CPTPMaps is associative. -/
theorem compose_assoc [DecidableEq dOut] (Λ₃ : CPTPMap dM₂ dOut) (Λ₂ : CPTPMap dM dM₂)
    (Λ₁ : CPTPMap dIn dM) : (Λ₃ ∘ₘ Λ₂) ∘ₘ Λ₁ = Λ₃ ∘ₘ (Λ₂ ∘ₘ Λ₁) := by
  ext1 ρ
  simp

/-- CPTPMaps have a convex structure from their Choi matrices. -/
instance instMixable : Mixable (Matrix (dOut × dIn) (dOut × dIn) ℂ) (CPTPMap dIn dOut) where
  to_U := CPTPMap.choi
  to_U_inj := choi_ext
  mkT {u} h := ⟨CPTP_of_choi_PSD_Tr (M := u)
    (Exists.recOn h fun t ht => ht ▸ t.choi_PSD_of_CPTP)
    (Exists.recOn h fun t ht => (by
      rw [← ht, ← MatrixMap.IsTracePreserving_iff_trace_choi]
      exact t.TP)),
    by apply choi_of_CPTP_of_choi⟩
  convex := by
    have h_convex : ∀ (M₁ M₂ : Matrix (dOut × dIn) (dOut × dIn) ℂ), M₁.PosSemidef → M₂.PosSemidef → ∀ (t : ℝ), 0 ≤ t → t ≤ 1 → (t • M₁ + (1 - t) • M₂).PosSemidef := by
      intro M₁ M₂ h₁ h₂ t ht₁ ht₂;
      convert Matrix.PosSemidef.add ( h₁.smul ht₁ ) ( h₂.smul ( sub_nonneg.mpr ht₂ ) ) using 1;
    intro M hM N hN a b ha hb hab;
    obtain ⟨Λ₁, hΛ₁⟩ := hM
    obtain ⟨Λ₂, hΛ₂⟩ := hN;
    obtain ⟨Λ, hΛ⟩ : ∃ Λ : MatrixMap dIn dOut ℂ, (a • M + b • N).traceLeft = 1 ∧ (a • M + b • N).PosSemidef ∧ Λ = MatrixMap.of_choi_matrix (a • M + b • N) := by
      refine ⟨_, ?_, ?_, rfl⟩
      · have h_trace_M : M.traceLeft = 1 := by
          convert Λ₁.TP using 1;
          rw [ ← hΛ₁, MatrixMap.IsTracePreserving_iff_trace_choi ]
        have h_trace_N : N.traceLeft = 1 := by
          convert Λ₂.map.IsTracePreserving_iff_trace_choi.1 Λ₂.TP;
          exact hΛ₂.symm;
        convert congr_arg₂ ( fun x y : Matrix dIn dIn ℂ => a • x + b • y ) h_trace_M h_trace_N using 1;
        · ext i j
          simp [ Matrix.traceLeft ]
          simp only [Finset.sum_add_distrib, Finset.mul_sum _ _ _];
        · rw [ ← add_smul, hab, one_smul ];
      · convert h_convex M N ( by simpa [ ← hΛ₁ ] using Λ₁.choi_PSD_of_CPTP ) ( by simpa [ ← hΛ₂ ] using Λ₂.choi_PSD_of_CPTP ) a ha ( by linarith ) using 1 ; rw [ ← hab ]
        ring_nf
    use CPTP_of_choi_PSD_Tr hΛ.2.1 hΛ.1;
    exact MatrixMap.map_choi_inv (a • M + b • N)

/-- The identity channel, which leaves the input unchanged. -/
def id : CPTPMap dIn dIn where
  toLinearMap := .id
  cp := .id
  TP := .id

/-- The map `CPTPMap.id` leaves any matrix unchanged. -/
@[simp]
theorem id_map : (id (dIn := dIn)).map = LinearMap.id := by
  rfl

/-- The map `CPTPMap.id` leaves the input state unchanged. -/
@[simp]
theorem id_MState (ρ : MState dIn) : CPTPMap.id (dIn := dIn) ρ = ρ := by
  apply MState.ext_m
  rw [mat_coe_eq_apply_mat]
  simp

/-- The map `CPTPMap.id` composed with any map is the same map. -/
@[simp]
theorem id_compose [DecidableEq dOut] (Λ : CPTPMap dIn dOut) : id ∘ₘ Λ = Λ := by
  apply funext
  simp

/-- Any map composed with `CPTPMap.id` is the same map. -/
@[simp]
theorem compose_id (Λ : CPTPMap dIn dOut) : Λ ∘ₘ id = Λ := by
  classical ext1
  simp

section equiv
variable [DecidableEq dOut]

/-- Given a equivalence (a bijection) between the types d₁ and d₂, that is, if they're
 the same dimension, then there's a CPTP channel for this. This is what we need for
 defining e.g. the SWAP channel, which is 'unitary' but takes heterogeneous input
 and outputs types (d₁ × d₂) and (d₂ × d₁). -/
def ofEquiv (σ : dIn ≃ dOut) : CPTPMap dIn dOut where
  toLinearMap := MatrixMap.submatrix ℂ σ.symm
  cp := .submatrix σ.symm
  TP x := by rw [MatrixMap.IsTracePreserving.submatrix]

@[simp]
theorem ofEquiv_apply (σ : dIn ≃ dOut) (ρ : MState dIn) :
    ofEquiv σ ρ = ρ.relabel σ.symm := by
  rfl

@[simp]
theorem ofEquiv_refl : ofEquiv (Equiv.refl dIn) = id (dIn := dIn) := by
  ext1 ρ
  simp

@[simp]
theorem ofEquiv_comp (σ : dIn ≃ dM) (τ : dM ≃ dOut) :
    (ofEquiv τ) ∘ₘ (ofEquiv σ) = ofEquiv (σ.trans τ) := by
  ext1 ρ
  rfl

@[simp]
theorem equiv_inverse (σ : dIn ≃ dOut) :
    (ofEquiv σ) ∘ₘ (ofEquiv σ.symm) = id (dIn := dOut) := by
  simp [ofEquiv_comp]

variable {d₁ d₂ d₃ : Type*} [Fintype d₁] [Fintype d₂] [Fintype d₃]
variable [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃]

/-- The SWAP operation, as a channel. -/
def SWAP : CPTPMap (d₁ × d₂) (d₂ × d₁) :=
  ofEquiv (Equiv.prodComm d₁ d₂)

/-- The associator, as a channel. -/
def assoc : CPTPMap ((d₁ × d₂) × d₃) (d₁ × d₂ × d₃) :=
  ofEquiv (Equiv.prodAssoc d₁ d₂ d₃)

/-- The inverse associator, as a channel. -/
def assoc' : CPTPMap (d₁ × d₂ × d₃) ((d₁ × d₂) × d₃) :=
  ofEquiv (Equiv.prodAssoc d₁ d₂ d₃).symm

@[simp]
theorem SWAP_eq_MState_SWAP (ρ : MState (d₁ × d₂)) : SWAP (d₁ := d₁) (d₂ := d₂) ρ = ρ.SWAP :=
  rfl

@[simp]
theorem assoc_eq_MState_assoc (ρ : MState ((d₁ × d₂) × d₃)) : assoc (d₁ := d₁) (d₂ := d₂) (d₃ := d₃) ρ = ρ.assoc :=
  rfl

@[simp]
theorem assoc'_eq_MState_assoc' (ρ : MState (d₁ × d₂ × d₃)) : assoc' (d₁ := d₁) (d₂ := d₂) (d₃ := d₃) ρ = ρ.assoc' :=
  rfl

@[simp]
theorem SWAP_SWAP : (SWAP (d₁ := d₁) (d₂ := d₂)) ∘ₘ SWAP = id := by
  simpa [SWAP] using (equiv_inverse (σ := Equiv.prodComm d₁ d₂))

@[simp]
theorem assoc_assoc' : (assoc (d₁ := d₁) (d₂ := d₂) (d₃ := d₃)) ∘ₘ assoc' = id := by
  simp [assoc, assoc']

@[simp]
theorem assoc'_assoc : (assoc' (d₁ := d₁) (d₂ := d₂) (d₃ := d₃)) ∘ₘ assoc = id := by
  simp [assoc, assoc', ofEquiv_comp]

end equiv

section trace
variable {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂]

/-- Partial tracing out the left, as a CPTP map. -/
@[simps!]
def traceLeft : CPTPMap (d₁ × d₂) d₂ :=
  {
    toLinearMap := MatrixMap.traceLeft (A := d₁) (B := d₂) ℂ
    TP := by intro; simp
    cp := by
      --(traceLeft ⊗ₖₘ I) = traceLeft ∘ₘ (ofEquiv prod_assoc)
      --Both go (A × B) × C → B × C
      --So then it suffices to show both are positive, and we have PosSemidef.traceLeft already.
      intro n
      classical
      suffices MatrixMap.IsPositive
          (MatrixMap.traceLeft (A := d₁) (B := d₂ × Fin n) ℂ ∘ₗ
            MatrixMap.submatrix ℂ (Equiv.prodAssoc d₁ d₂ (Fin n)).symm) by
        convert this
        ext
        rw [MatrixMap.kron_def]
        simp [Matrix.submatrix, Matrix.single, ite_and, Matrix.traceLeft, Fintype.sum_prod_type]
      apply MatrixMap.IsPositive.comp
      · exact (MatrixMap.IsCompletelyPositive.submatrix _).IsPositive
      · intro x h
        exact h.traceLeft
  }

/-- Partial tracing out the right, as a CPTP map. -/
def traceRight : CPTPMap (d₁ × d₂) d₁ :=
  traceLeft ∘ₘ SWAP

@[simp]
theorem traceLeft_eq_MState_traceLeft (ρ : MState (d₁ × d₂)) :
    traceLeft (d₁ := d₁) (d₂ := d₂) ρ = ρ.traceLeft := by
  rfl

@[simp]
theorem traceRight_eq_MState_traceRight (ρ : MState (d₁ × d₂)) :
    traceRight (d₁ := d₁) (d₂ := d₂) ρ = ρ.traceRight := by
  rfl --It's actually pretty crazy that this is a definitional equality, cool

end trace

/--The replacement channel that maps all inputs to a given state. -/
def replacement [Nonempty dIn] [DecidableEq dOut] (ρ : MState dOut) : CPTPMap dIn dOut :=
  traceLeft ∘ₘ {
      toFun := fun M => Matrix.kroneckerMap (fun x1 x2 => x1 * x2) M ρ.m
      map_add' := by simp [Matrix.add_kronecker]
      map_smul' := by simp [Matrix.smul_kronecker]
      cp := MatrixMap.kron_kronecker_const ρ.pos
      TP := by intro; simp [Matrix.trace_kronecker]
      }

/-- The output of `replacement ρ` is always that `ρ`. -/
@[simp]
theorem replacement_apply [Nonempty dIn] [DecidableEq dOut] (ρ : MState dOut) (ρ₀ : MState dIn) :
    replacement ρ ρ₀ = ρ := by
  simp [replacement, instMFunLike, PTPMap.instMFunLike, HPMap.instFunLike, HPMap.map,
    MState.traceLeft]
  --This should be simp...
  ext i j
  simp
  rw [HermitianMat.instFun]
  simp [-HermitianMat.mat_apply, Matrix.traceLeft, ← Finset.sum_mul]
  convert one_mul _
  exact ρ₀.tr'

--In principle we can relax the `Nonempty dIn`: for the case where `IsEmpty dIn`, we just take the
-- 0 map, and it's CPTP.
instance [Nonempty dIn] [Nonempty dOut] [DecidableEq dOut] : Inhabited (CPTPMap dIn dOut) :=
  ⟨replacement default⟩

instance [Nonempty dIn] [Nonempty dOut] : Nonempty (CPTPMap dIn dOut) := by
  classical infer_instance

/-- There is a CPTP map that takes a system of any (nonzero) dimension and outputs the
trivial Hilbert space, 1-dimensional, indexed by any `Unique` type. We can think of this
as "destroying" the whole system; tracing out everything. -/
def destroy [Nonempty dIn] [Unique dOut] : CPTPMap dIn dOut :=
  replacement default

/-- Two CPTP maps into the same one-dimensional output space must be equal -/
theorem eq_if_output_unique [Unique dOut] (Λ₁ Λ₂ : CPTPMap dIn dOut) : Λ₁ = Λ₂ :=
  funext fun _ ↦ (Unique.eq_default _).trans (Unique.eq_default _).symm

/-- There is exactly one CPTPMap to a 1-dimensional space. -/
instance instUnique [Nonempty dIn] [Unique dOut] : Unique (CPTPMap dIn dOut) where
  default := destroy
  uniq := fun _ ↦ eq_if_output_unique _ _

@[simp]
theorem destroy_comp {dOut₂ : Type*} [Unique dOut₂] [DecidableEq dOut] [Nonempty dIn] [Nonempty dOut]
  (Λ : CPTPMap dIn dOut) :
    destroy (dOut := dOut₂) ∘ₘ Λ = destroy :=
  Unique.eq_default _

section prod
open Kronecker

variable {dI₁ dI₂ dO₁ dO₂ : Type*} [Fintype dI₁] [Fintype dI₂] [Fintype dO₁] [Fintype dO₂]
variable [DecidableEq dI₁] [DecidableEq dI₂] [DecidableEq dO₁] [DecidableEq dO₂]

set_option maxRecDepth 1000 in -- ??? what the heck is recursing
/-- The tensor product of two CPTPMaps. -/
def prod (Λ₁ : CPTPMap dI₁ dO₁) (Λ₂ : CPTPMap dI₂ dO₂) : CPTPMap (dI₁ × dI₂) (dO₁ × dO₂) where
  toLinearMap := Λ₁.map.kron Λ₂.map
  cp := Λ₁.cp.kron Λ₂.cp
  TP := Λ₁.TP.kron Λ₂.TP

infixl:70 "⊗ᶜᵖ" => CPTPMap.prod

/-- Tensor-product channels act componentwise on product states. -/
theorem prod_apply_prod (Λ₁ : CPTPMap dI₁ dO₁) (Λ₂ : CPTPMap dI₂ dO₂)
    (ρ₁ : MState dI₁) (ρ₂ : MState dI₂) :
    (Λ₁ ⊗ᶜᵖ Λ₂) (ρ₁ ⊗ᴹ ρ₂) = (Λ₁ ρ₁) ⊗ᴹ (Λ₂ ρ₂) := by
  apply MState.ext_m
  rw [CPTPMap.mat_coe_eq_apply_mat]
  simpa [CPTPMap.prod, MState.prod] using
    MatrixMap.kron_map_of_kron_state Λ₁.map Λ₂.map ρ₁.m ρ₂.m

end prod

section ancilla

variable {dAnc : Type*} [Fintype dAnc] [DecidableEq dAnc]

private theorem ofEquiv_prodPUnit_eq_prod_pureUnit (ρ : MState dIn) :
    CPTPMap.ofEquiv (dIn := dIn) (dOut := dIn × Unit) (Equiv.prodPUnit dIn).symm ρ =
      ρ ⊗ᴹ MState.pure (Ket.basis ()) := by
  rw [CPTPMap.ofEquiv_apply]
  apply MState.ext_m
  ext i j
  rcases i with ⟨i, _⟩
  rcases j with ⟨j, _⟩
  change ρ.m.submatrix (Equiv.prodPUnit dIn) (Equiv.prodPUnit dIn) (i, ()) (j, ()) =
    Matrix.kroneckerMap (fun x y : ℂ => x * y) ρ.m ((MState.pure (Ket.basis ())).m) (i, ()) (j, ())
  have hu : (MState.pure (Ket.basis ())).m () () = (1 : ℂ) := by
    change Ket.basis () () * (starRingEnd ℂ) (Ket.basis () ()) = (1 : ℂ)
    have hbasis : Ket.basis () () = (1 : ℂ) := by
      simp [Ket.basis, Ket.apply]
    rw [hbasis]
    simp
  simp [Matrix.kroneckerMap, hu]

/-- Append a fixed ancilla state to the input system. -/
def appendState (ρ : MState dAnc) : CPTPMap dIn (dIn × dAnc) :=
  let append : CPTPMap dIn (dIn × Unit) := ofEquiv (Equiv.prodPUnit dIn).symm
  ((id (dIn := dIn)) ⊗ᶜᵖ replacement (dIn := Unit) ρ) ∘ₘ append

/-- Appending an ancilla is exactly tensoring with that ancilla state. -/
theorem appendState_eq_prod (ρAnc : MState dAnc) (ρ : MState dIn) :
    CPTPMap.appendState (dIn := dIn) ρAnc ρ = ρ ⊗ᴹ ρAnc := by
  rw [CPTPMap.appendState, CPTPMap.compose_eq, ofEquiv_prodPUnit_eq_prod_pureUnit]
  rw [prod_apply_prod]
  simp

end ancilla

section finprod

variable {ι : Type u} [DecidableEq ι] [fι : Fintype ι]
variable {dI : ι → Type v} [∀(i :ι), Fintype (dI i)] [∀(i :ι), DecidableEq (dI i)]
variable {dO : ι → Type w} [∀(i :ι), Fintype (dO i)] [∀(i :ι), DecidableEq (dO i)]

/-- Finitely-indexed tensor products of CPTPMaps.  -/
def piProd (Λi : (i:ι) → CPTPMap (dI i) (dO i)) : CPTPMap ((i:ι) → dI i) ((i:ι) → dO i) where
  toLinearMap := MatrixMap.piProd (fun i ↦ (Λi i).map)
  cp := MatrixMap.IsCompletelyPositive.piProd (fun i ↦ (Λi i).cp)
  TP := MatrixMap.IsTracePreserving.piProd (fun i ↦ (Λi i).TP)

theorem fin_1_piProd
  {dI : Fin 1 → Type v} [Fintype (dI 0)] [DecidableEq (dI 0)]
  {dO : Fin 1 → Type w} [Fintype (dO 0)] [DecidableEq (dO 0)]
  (Λi : (i : Fin 1) → CPTPMap (dI 0) (dO 0)) :
    piProd Λi =
      (ofEquiv (Equiv.funUnique (Fin 1) (dO 0)).symm) ∘ₘ
        ((Λi 0) ∘ₘ ofEquiv (Equiv.funUnique (Fin 1) (dI 0)) ) := by
  apply choi_ext
  ext x y
  rcases x with ⟨xO, xI⟩
  rcases y with ⟨yO, yI⟩
  change MatrixMap.piProd (fun i => (Λi i).map) (Matrix.single xI yI 1) xO yO = _
  rw [MatrixMap.IsCompletelyPositive.piProd_apply_single]
  have hright :
      (((ofEquiv (Equiv.funUnique (Fin 1) (dO 0)).symm) ∘ₘ
          ((Λi 0) ∘ₘ ofEquiv (Equiv.funUnique (Fin 1) (dI 0)))).map
          (Matrix.single xI yI 1)) xO yO =
        ((Λi 0).map (Matrix.single (xI 0) (yI 0) 1)) (xO 0) (yO 0) := by
    change ((Λi 0).map ((Matrix.single xI yI 1).submatrix
        (Equiv.funUnique (Fin 1) (dI 0)).symm (Equiv.funUnique (Fin 1) (dI 0)).symm))
      (xO 0) (yO 0) = _
    have hsub : ((Matrix.single xI yI (1 : ℂ)).submatrix
        (Equiv.funUnique (Fin 1) (dI 0)).symm (Equiv.funUnique (Fin 1) (dI 0)).symm) =
        Matrix.single (xI 0) (yI 0) 1 := by
      ext i j
      by_cases hx : xI 0 = i <;> by_cases hy : yI 0 = j
      · simp [Matrix.submatrix, Matrix.single, funext_iff, hx, hy]
      · simp [Matrix.submatrix, Matrix.single, funext_iff, hx, hy]
      · simp [Matrix.submatrix, Matrix.single, funext_iff, hx, hy]
      · simp [Matrix.submatrix, Matrix.single, funext_iff, hx, hy]
    rw [hsub]
  simpa using hright.symm

/--
The tensor product of composed maps is the composition of the tensor products.
-/
theorem piProd_comp
  {d₁ d₂ d₃ : ι → Type*}
  [∀ i, Fintype (d₁ i)] [∀ i, DecidableEq (d₁ i)]
  [∀ i, Fintype (d₂ i)] [∀ i, DecidableEq (d₂ i)]
  [∀ i, Fintype (d₃ i)] [∀ i, DecidableEq (d₃ i)]
  (Λ₁ : ∀ i, CPTPMap (d₁ i) (d₂ i)) (Λ₂ : ∀ i, CPTPMap (d₂ i) (d₃ i)) :
  piProd (fun i => (Λ₂ i) ∘ₘ (Λ₁ i)) = (piProd Λ₂) ∘ₘ (piProd Λ₁) := by
  apply CPTPMap.ext
  convert MatrixMap.piProd_comp _ _

end finprod

section unitary

/-- Conjugating density matrices by a unitary as a channel. This is standard unitary evolution. -/
def ofUnitary (U : 𝐔[dIn]) : CPTPMap dIn dIn where
  toLinearMap := MatrixMap.conj U
  cp := MatrixMap.conj_isCompletelyPositive U.val
  TP := by intro; simp [Matrix.trace_mul_cycle U.val, ← Matrix.star_eq_conjTranspose]

/-- The unitary channel U conjugated by U. -/
theorem ofUnitary_eq_conj (U : 𝐔[dIn]) (ρ : MState dIn) :
    (ofUnitary U) ρ = ρ.U_conj U :=
  rfl

/-- A channel is unitary iff it is `ofUnitary U`. -/
def IsUnitary (Λ : CPTPMap dIn dIn) : Prop :=
  ∃ U, Λ = ofUnitary U

/-- A channel is unitary iff it can be written as conjugation by a unitary. -/
theorem IsUnitary_iff_U_conj (Λ : CPTPMap dIn dIn) : IsUnitary Λ ↔ ∃ U, ∀ ρ, Λ ρ = ρ.U_conj U := by
  simp_rw [IsUnitary, ← ofUnitary_eq_conj, CPTPMap.funext_iff]

theorem IsUnitary_equiv (σ : dIn ≃ dIn) : IsUnitary (ofEquiv σ) := by
  have h_unitary : ∃ U : Matrix dIn dIn ℂ, U * U.conjTranspose = 1 ∧ U.conjTranspose * U = 1 ∧ ∀ x : dIn, (∀ y : dIn, (U y x = 1) ↔ (y = σ x)) ∧ ∀ y : dIn, (U y x = 0) ↔ (y ≠ σ x) := by
    simp only [Matrix.conjTranspose, RCLike.star_def];
    refine' ⟨ fun y x => if y = σ x then 1 else 0, ?_, ?_, by simp⟩
    · ext y x
      simp [Matrix.mul_apply, Matrix.transpose_apply];
      rw [Finset.sum_eq_single ( σ.symm x )] <;> aesop
    · ext y x
      simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply];
      simp [Matrix.one_apply, eq_comm]
  obtain ⟨U, hU_unitary, hU_eq⟩ := h_unitary;
  use ⟨U, Matrix.mem_unitaryGroup_iff.mpr hU_unitary⟩
  have h_mul : ∀ ρ : Matrix dIn dIn ℂ, U * ρ * Uᴴ = Matrix.submatrix ρ σ.symm σ.symm := by
    intro ρ
    ext i j
    have hU_i_x : ∀ x : dIn, U i x = if x = σ.symm i then 1 else 0 := by grind
    have hU_j_x : ∀ x : dIn, U j x = if x = σ.symm j then 1 else 0 := by grind
    simp [Matrix.mul_apply, Matrix.submatrix, hU_i_x, hU_j_x]
  ext ρ : 3
  exact (h_mul ρ).symm

end unitary

-- /-- A channel is *entanglement breaking* iff its product with the identity channel
--   only outputs separable states. -/
-- def IsEntanglementBreaking (Λ : CPTPMap dIn dOut) : Prop :=
--   ∀ (dR : Type u_1) [Fintype dR] [DecidableEq dR],
--   ∀ (ρ : MState (dR × dIn)), ((CPTPMap.id (dIn := dR) ⊗ₖ Λ) ρ).IsSeparable

--TODO:
--Theorem: entanglement breaking iff it holds for all channels, not just id.
--Theorem: entanglement break iff it breaks a Bell pair (Wilde Exercise 4.6.2)
--Theorem: entanglement break if c-q or q-c, e.g. measurements
--Theorem: eb iff Kraus operators can be written as all unit rank (Wilde Theorem 4.6.1)

section purify
variable [DecidableEq dOut] [Inhabited dOut]

private lemma isometry_orthonormal_columns
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (V : Matrix m n ℂ) (hV : V.Isometry) :
    Orthonormal ℂ (V.toEuclideanLin ∘ EuclideanSpace.basisFun n ℂ) := by
  let f : EuclideanSpace ℂ n →ₗᵢ[ℂ] EuclideanSpace ℂ m :=
    V.toEuclideanLin.isometryOfInner (fun x y => by
      rw [← LinearMap.adjoint_inner_right]
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
      simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]
      rw [hV, Matrix.one_mulVec]
      simp)
  exact ((EuclideanSpace.basisFun n ℂ).orthonormal).comp_linearIsometry f

private theorem exists_unitary_extension_of_isometry
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (V : Matrix m n ℂ) (hV : V.Isometry) (e : n → m) (he : Function.Injective e) :
    ∃ U : Matrix.unitaryGroup m ℂ, U.1.submatrix _root_.id e = V := by
  let colsOrtho := isometry_orthonormal_columns V hV
  let s : Set m := Set.range e
  let eRange : n ≃ s := Equiv.ofInjective e he
  let v : m → EuclideanSpace ℂ m := fun i =>
    if hi : i ∈ s then
      V.toEuclideanLin (EuclideanSpace.basisFun n ℂ (eRange.symm ⟨i, hi⟩))
    else
      EuclideanSpace.basisFun m ℂ i
  have hv_eq :
      s.restrict v = fun x : s =>
        V.toEuclideanLin (EuclideanSpace.basisFun n ℂ (eRange.symm x)) := by
    funext x
    rcases x with ⟨i, hi⟩
    obtain ⟨j, rfl⟩ := hi
    simp [Set.restrict, v, s]
  have hv : Orthonormal ℂ (s.restrict v) := by
    rw [hv_eq]
    simpa [Function.comp_def] using colsOrtho.comp eRange.symm eRange.symm.injective
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (ι := m) (E := EuclideanSpace ℂ m) (s := s) (v := v) (by simp) hv
  refine ⟨⟨(EuclideanSpace.basisFun m ℂ).toBasis.toMatrix b.toBasis,
    (EuclideanSpace.basisFun m ℂ).toMatrix_orthonormalBasis_mem_unitary b⟩, ?_⟩
  ext i a
  have ha : e a ∈ s := ⟨a, rfl⟩
  have hpre : eRange.symm ⟨e a, ha⟩ = a := by
    apply he
    change ((eRange) (eRange.symm ⟨e a, ha⟩) : m) = e a
    simp
  simp [Matrix.submatrix_apply, Module.Basis.toMatrix_apply, EuclideanSpace.basisFun_repr,
    hb (e a) ha, v, s, hpre, Matrix.toEuclideanLin_apply]

private lemma of_kraus_tp_sum_eq_one
    {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (K : (B × A) → Matrix B A ℂ)
    (hTP : (MatrixMap.of_kraus K K).IsTracePreserving) :
    (∑ k, (K k).conjTranspose * K k) = (1 : Matrix A A ℂ) := by
  ext a a'
  have h := hTP (Matrix.single a' a (1 : ℂ))
  simp only [MatrixMap.of_kraus, LinearMap.coeFn_sum, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.sum_apply, Matrix.trace_sum] at h
  have hsum :
      ∑ i, (K i * Matrix.single a' a (1 : ℂ) * (K i)ᴴ).trace =
        ∑ i, (((K i)ᴴ * K i) * Matrix.single a' a (1 : ℂ)).trace := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    simpa [Matrix.mul_assoc] using
      (Matrix.trace_mul_cycle (K i) (Matrix.single a' a (1 : ℂ)) (K i).conjTranspose)
  rw [hsum] at h
  simp [Matrix.trace_mul_single, Matrix.mul_apply] at h
  have h' : (∑ k, (K k)ᴴ * K k) a a' = (Matrix.single a' a (1 : ℂ)).trace := by
    calc
      (∑ k, (K k)ᴴ * K k) a a' = ∑ k, (((K k)ᴴ * K k) a a') := by
        simp [Matrix.sum_apply]
      _ = ∑ x, ∑ x_1, (starRingEnd ℂ) (K x x_1 a) * K x x_1 a' := by
        simp [Matrix.mul_apply]
      _ = (Matrix.single a' a (1 : ℂ)).trace := h
  by_cases haa' : a = a'
  · subst haa'
    simpa using h'
  · simp [Matrix.trace_single_eq_of_ne, haa', eq_comm] at h'
    simpa [Matrix.one_apply, haa'] using h'.symm

private theorem embed_mul_mul_embed_conjTranspose_eq_kron_pure
    (X : Matrix dIn dIn ℂ) :
    let e : dIn → (dIn × dOut × dOut) := fun a => (a, default)
    let J : Matrix (dIn × dOut × dOut) dIn ℂ :=
      Matrix.submatrix (α := ℂ)
        (1 : Matrix (dIn × dOut × dOut) (dIn × dOut × dOut) ℂ) _root_.id e
    J * X * Jᴴ =
      Matrix.kroneckerMap (fun x y : ℂ => x * y) X
        (MState.pure (Ket.basis (default : dOut × dOut))).m := by
  ext i j
  rcases i with ⟨i, ⟨i₁, i₂⟩⟩
  rcases j with ⟨j, ⟨j₁, j₂⟩⟩
  have hpure : ∀ a b : dOut × dOut,
      (MState.pure (Ket.basis (default : dOut × dOut))).m a b =
        if a = default ∧ b = default then 1 else 0 := by
    intro a b
    change Ket.basis (default : dOut × dOut) a *
        (starRingEnd ℂ) (Ket.basis (default : dOut × dOut) b) =
      if a = default ∧ b = default then 1 else 0
    by_cases ha : a = default
    · by_cases hb : b = default
      · subst ha
        subst hb
        have hbasis : Ket.basis (default : dOut × dOut) default = (1 : ℂ) := by
          simp [Ket.basis, Ket.apply]
        rw [hbasis]
        simp
      · have hb' : ¬ default = b := by simpa [eq_comm] using hb
        simp [Ket.basis, Ket.apply, ha, hb, hb']
    · simp [Ket.basis, Ket.apply, ha, eq_comm]
  by_cases hi : (i₁, i₂) = (default : dOut × dOut)
  · by_cases hj : (j₁, j₂) = (default : dOut × dOut)
    · cases hi
      cases hj
      have hdef : ((default, default) : dOut × dOut) = default := rfl
      simp [Matrix.mul_apply, Matrix.submatrix, Matrix.one_apply, Matrix.kroneckerMap,
        hpure, hdef]
    · simp [Matrix.mul_apply, Matrix.submatrix, Matrix.one_apply, Matrix.kroneckerMap,
        hpure, hi, hj]
  · simp [Matrix.mul_apply, Matrix.submatrix, Matrix.one_apply, Matrix.kroneckerMap,
      hpure, hi]

Concretely, define the column vectors of V as an orthonormal family in EuclideanSpace ℂ m,
indexed by the range of emb. Then use `Orthonormal.exists_orthonormalBasis_extension_of_card_eq`
to extend this to a full OrthonormalBasis. The matrix of this basis is unitary.

Alternatively, use V to define a linear isometry on the subspace spanned by the image
of emb, then use `LinearIsometry.extend` to extend to the full space. Since in finite
dimensions a linear isometry from a space to itself is surjective, this gives a
LinearIsometryEquiv, hence a unitary matrix.
-/
set_option maxHeartbeats 1600000 in
private lemma exists_unitary_extending_isometry
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (V : Matrix m n ℂ) (hV : V.conjTranspose * V = 1)
    (emb : n ↪ m) :
    ∃ U : 𝐔[m], ∀ i j, U.val i (emb j) = V i j := by
  -- Let $u_i$ be the $i$-th column of $V$.
  set u : n → EuclideanSpace ℂ m := fun j => WithLp.toLp 2 (fun i => V i j)
  -- Since $u$ is an orthonormal set, we can extend it to an orthonormal basis of $\mathbb{C}^m$.
  obtain ⟨b, hb⟩ : ∃ b : OrthonormalBasis m ℂ (EuclideanSpace ℂ m), ∀ j, b (emb j) = u j := by
    have h_orthonormal : Orthonormal ℂ (fun j => u j) := by
      rw [ orthonormal_iff_ite ];
      intro i j
      replace hV := congr_fun (congr_fun hV i) j
      simpa only [ mul_comm, Matrix.mul_apply ] using hV
    have := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℂ) (E := EuclideanSpace ℂ m) (ι := m)
    simp only [finrank_euclideanSpace, forall_const] at this
    contrapose! this
    · refine ⟨fun i => if hi : i ∈ Set.range emb then u (Classical.choose hi) else 0, Set.range emb, ?_, ?_ ⟩
      · simp +contextual only [Orthonormal, h_orthonormal.1, implies_true, true_and,
          Set.mem_range, Set.restrict_apply, Subtype.forall, ↓reduceDIte]
        intro i j hij
        split_ifs with h₁ h₂
        · apply h_orthonormal.2
          have := Classical.choose_spec ‹∃ y, emb y = ↑i›
          have := Classical.choose_spec ‹∃ y, emb y = ↑j›
          grind
        · simp
        · simp
        · simp
      · simp_all only [Orthonormal, ne_eq, Set.mem_range, exists_exists_eq_and,
          EmbeddingLike.apply_eq_iff_eq, exists_eq, ↓reduceDIte, Classical.choose_eq, implies_true];
  refine ⟨⟨Matrix.of (fun i j ↦ b j i), ?_⟩, ?_⟩
  · simp only [Matrix.mem_unitaryGroup_iff]
    ext1 i j
    simpa [inner] using b.sum_inner_mul_inner (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  · simp [hb, u]

omit [DecidableEq dOut] [Inhabited dOut] in
/--
Given Kraus operators K indexed by (dOut × dIn), define the isometry matrix
V : Matrix (dIn × dOut × dOut) dIn ℂ by V_{(a, b, d), a'} = (K (b, a))_{d, a'}.
Then V†V = 1.
-/
private lemma purify_isometry_condition
    {K : (dOut × dIn) → Matrix dOut dIn ℂ}
    (hTP : ∑ k, (K k).conjTranspose * (K k) = 1) :
    let V : Matrix (dIn × dOut × dOut) dIn ℂ :=
      fun (aEnv, bEnv, bOut) aIn => K (bEnv, aEnv) bOut aIn
    (Matrix.traceLeft (d := dOut)) ((Matrix.traceLeft (d := dIn)) (V * X * Vᴴ)) =
      MatrixMap.of_kraus K K X := by
  ext b₁ b₂
  change
    ∑ x, ∑ x_1, ∑ x_2,
      (∑ x_3, K (x, x_1) b₁ x_3 * X x_3 x_2) * (starRingEnd ℂ) (K (x, x_1) b₂ x_2) =
      (MatrixMap.of_kraus K K X) b₁ b₂
  simp [MatrixMap.of_kraus, Matrix.sum_apply, Matrix.mul_apply, Fintype.sum_prod_type]

theorem exists_purify (Λ : CPTPMap dIn dOut) :
    ∃ (Λ' : CPTPMap (dIn × dOut × dOut) (dIn × dOut × dOut)),
      Λ'.IsUnitary ∧
      Λ = CPTPMap.traceLeft ∘ₘ CPTPMap.traceLeft ∘ₘ Λ' ∘ₘ
        CPTPMap.appendState (MState.pure (Ket.basis default)) := by
  obtain ⟨K, hK⟩ := MatrixMap.IsCompletelyPositive.exists_kraus Λ.map Λ.cp
  let V : Matrix (dIn × dOut × dOut) dIn ℂ :=
    fun (aEnv, bEnv, bOut) aIn => K (bEnv, aEnv) bOut aIn
  have hTPK : (MatrixMap.of_kraus K K).IsTracePreserving := by
    simpa [hK] using Λ.TP
  have hNorm : (∑ k, (K k).conjTranspose * K k) = (1 : Matrix dIn dIn ℂ) :=
    of_kraus_tp_sum_eq_one K hTPK
  have hV : V.Isometry := by
    ext a a'
    change ∑ i : dIn × dOut × dOut, (starRingEnd ℂ) (V i a) * V i a' =
      (1 : Matrix dIn dIn ℂ) a a'
    simp only [V, Fintype.sum_prod_type]
    calc
      ∑ x, ∑ x_1, ∑ x_2, (starRingEnd ℂ) (K (x_1, x) x_2 a) * K (x_1, x) x_2 a'
        = ∑ x_1, ∑ x, ∑ x_2, (starRingEnd ℂ) (K (x_1, x) x_2 a) * K (x_1, x) x_2 a' := by
            rw [Finset.sum_comm]
      _ = (1 : Matrix dIn dIn ℂ) a a' := by
        simpa [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
          using congrFun₂ hNorm a a'
  let e : dIn → (dIn × dOut × dOut) := fun a => (a, default)
  have he : Function.Injective e := by
    intro a a' h
    exact congrArg Prod.fst h
  obtain ⟨U, hU⟩ := exists_unitary_extension_of_isometry V hV e he
  refine ⟨ofUnitary U, ⟨⟨U, rfl⟩, ?_⟩⟩
  apply CPTPMap.funext
  intro ρ
  let ρ0 : MState (dOut × dOut) := MState.pure (Ket.basis (default : dOut × dOut))
  have hAppend : CPTPMap.appendState (dIn := dIn) ρ0 ρ = ρ ⊗ᴹ ρ0 := appendState_eq_prod ρ0 ρ
  let J : Matrix (dIn × dOut × dOut) dIn ℂ :=
    Matrix.submatrix (α := ℂ)
      (1 : Matrix (dIn × dOut × dOut) (dIn × dOut × dOut) ℂ) _root_.id e
  have hEmbed : J * ρ.m * Jᴴ = (ρ ⊗ᴹ ρ0).m := by
    simpa [J, e, ρ0, MState.prod] using
      (embed_mul_mul_embed_conjTranspose_eq_kron_pure (dIn := dIn) (dOut := dOut) ρ.m)
  have hUJ : U.1 * J = V := by
    calc
      U.1 * J = U.1.submatrix _root_.id e := by
        ext i a
        simp [J, e, Matrix.mul_apply, Matrix.submatrix, Matrix.one_apply]
      _ = V := hU
  apply MState.ext_m
  rw [CPTPMap.compose_eq, CPTPMap.compose_eq, CPTPMap.compose_eq, hAppend]
  rw [CPTPMap.mat_coe_eq_apply_mat]
  rw [CPTPMap.traceLeft_eq_MState_traceLeft, CPTPMap.traceLeft_eq_MState_traceLeft]
  change Λ.map ρ.m =
    (Matrix.traceLeft (d := dOut))
      ((Matrix.traceLeft (d := dIn)) (((ofUnitary U) (ρ ⊗ᴹ ρ0)).m))
  rw [CPTPMap.mat_coe_eq_apply_mat (Λ := ofUnitary U) (ρ := ρ ⊗ᴹ ρ0)]
  rw [← hEmbed]
  calc
    Λ.map ρ.m = MatrixMap.of_kraus K K ρ.m := by rw [hK]
    _ = (Matrix.traceLeft (d := dOut)) ((Matrix.traceLeft (d := dIn)) (V * ρ.m * Vᴴ)) := by
      symm
      simpa [V] using traceLeft_traceLeft_stinespring_eq_of_kraus (dIn := dIn) (dOut := dOut) K ρ.m
    _ = (Matrix.traceLeft (d := dOut))
          ((Matrix.traceLeft (d := dIn)) (U.1 * (J * ρ.m * Jᴴ) * U.1ᴴ)) := by
        congr 1
        congr 1
        calc
          V * ρ.m * Vᴴ = (U.1 * J) * ρ.m * (U.1 * J)ᴴ := by rw [hUJ]
          _ = U.1 * (J * ρ.m * Jᴴ) * U.1ᴴ := by
            simp [Matrix.mul_assoc, Matrix.conjTranspose_mul]

/-- Every channel can be written as a unitary channel on a larger system. In general, if
 the original channel was A→B, we may need to go as big as dilating the output system (the
 environment) by a factor of A*B. One way of stating this would be that it forms an
 isometry from A to (B×A×B). So that we can instead talk about the cleaner unitaries, we
 say that this is a unitary on (A×B×B). The defining properties that this is a valid
 purification comes are `purify_IsUnitary` and `purify_trace`. This means the environment
 always has type `dIn × dOut`.

 Furthermore, since we need a canonical "0" state on B in order to add with the input,
 we require a typeclass instance [Inhabited dOut]. -/
def purify (Λ : CPTPMap dIn dOut) : CPTPMap (dIn × dOut × dOut) (dIn × dOut × dOut) :=
  exists_purify Λ |>.choose
-- where
  -- toLinearMap := by
  --   proof omitted
  -- cp := proof omitted
  -- TP := proof omitted

--TODO: Constructing this will probably need Kraus operators first.

theorem purify_IsUnitary (Λ : CPTPMap dIn dOut) : Λ.purify.IsUnitary :=
  exists_purify Λ |>.choose_spec.1

/-- With a channel Λ : A → B, a valid purification (A×B×B)→(A×B×B) is such that:
 * Preparing the default ∣0⟩ state on two copies of B
 * Appending these to the input
 * Applying the purified unitary channel
 * Tracing out the two left parts of the output
is equivalent to the original channel. This theorem states that the channel output by `purify`
has this property. -/
theorem purify_trace (Λ : CPTPMap dIn dOut) : Λ = (
    CPTPMap.traceLeft ∘ₘ CPTPMap.traceLeft ∘ₘ Λ.purify ∘ₘ
      CPTPMap.appendState (MState.pure (Ket.basis default))
  ) :=
  exists_purify Λ |>.choose_spec.2

--TODO Theorem: `purify` is unique up to unitary equivalence.

/-- The complementary channel comes from tracing out the other half (the right half) of the purified channel `purify`. -/
def complementary (Λ : CPTPMap dIn dOut) : CPTPMap dIn (dIn × dOut) :=
  CPTPMap.traceRight ∘ₘ CPTPMap.assoc' ∘ₘ Λ.purify ∘ₘ
    CPTPMap.appendState (MState.pure (Ket.basis default))

end purify

section degradable
variable [DecidableEq dOut] [Inhabited dOut] [DecidableEq dOut₂] [Inhabited dOut₂]

/-- A channel is *degradable to* another, if the other can be written as a composition of
  a _degrading_ channel D with the original channel. -/
def IsDegradableTo (Λ : CPTPMap dIn dOut) (Λ₂ : CPTPMap dIn dOut₂) : Prop :=
  ∃ (D : CPTPMap dOut (dOut₂)), D ∘ₘ Λ = Λ₂

/-- A channel is *antidegradable to* another, if the other `IsDegradableTo` this one. -/
@[reducible]
def IsAntidegradableTo (Λ : CPTPMap dIn dOut) (Λ₂ : CPTPMap dIn dOut₂) : Prop :=
  IsDegradableTo Λ₂ Λ

/-- A channel is *degradable* if it `IsDegradableTo` its complementary channel. -/
def IsDegradable (Λ : CPTPMap dIn dOut) : Prop :=
  IsDegradableTo Λ Λ.complementary

/-- A channel is *antidegradable* if it `IsAntidegradableTo` its complementary channel. -/
@[reducible]
def IsAntidegradable (Λ : CPTPMap dIn dOut) : Prop :=
  IsAntidegradableTo Λ Λ.complementary

--Theorem (Wilde Exercise 13.5.7): Entanglement breaking channels are antidegradable.
end degradable

/-- `CPTPMap`s inherit a topology from their choi matrices. -/
instance instTop : TopologicalSpace (CPTPMap dIn dOut) :=
  TopologicalSpace.induced (CPTPMap.choi) instTopologicalSpaceMatrix

/-- The projection from `CPTPMap` to the Choi matrix is an embedding -/
theorem choi_IsEmbedding : Topology.IsEmbedding (CPTPMap.choi (dIn := dIn) (dOut := dOut)) where
  eq_induced := rfl
  injective _ _ := choi_ext

instance instT3Space : T3Space (CPTPMap dIn dOut) :=
  Topology.IsEmbedding.t3Space choi_IsEmbedding

end
end CPTPMap
