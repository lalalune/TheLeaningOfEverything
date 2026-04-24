/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Relativity.Tensors.RealTensor.Vector.MinkowskiProduct
import Relativity.LorentzGroup.Rotations
import Relativity.SpeedOfLight
import SpaceAndTime.Time.Basic
/-!
# Spacetime

## i. Overview

In this file we define the type `SpaceTime d` which corresponds to `d+1` dimensional
spacetime. This is equipped with an instance of the action of a Lorentz group,
corresponding to Minkowski-spacetime.

It is defined through `Lorentz.Vector d`, and carries the tensorial instance,
allowing it to be used in tensorial expressions.

## ii. Key results

- `SpaceTime d` : The type corresponding to `d+1` dimensional spacetime.
- `toTimeAndSpace` : A continuous linear equivalence between `SpaceTime d`
  and `Time × Space d`.

## iii. Table of contents

- A. The definition of `SpaceTime d`
- C. Continuous linear map to coordinates
- D. Measures on `SpaceTime d`
  - D.1. Instance of a measurable space
  - D.2. Instance of a borel space
  - D.4. Instance of a measure space
  - D.5. Volume measure is positive on non-empty open sets
  - D.6. Volume measure is a finite measure on compact sets
  - D.7. Volume measure is an additive Haar measure
- B. Maps to and from `Space` and `Time`
  - B.1. Linear map to `Space d`
    - B.1.1. Explicit expansion of map to space
    - B.1.2. Equivariance of the to space under rotations
  - B.2. Linear map to `Time`
    - B.2.1. Explicit expansion of map to time in terms of coordinates
  - B.3. `toTimeAndSpace`: Continuous linear equivalence to `Time × Space d`
    - B.3.1. Derivative of `toTimeAndSpace`
    - B.3.2. Derivative of the inverse of `toTimeAndSpace`
    - B.3.3. `toTimeAndSpace` acting on spatial basis vectors
    - B.3.4. `toTimeAndSpace` acting on the temporal basis vectors
  - B.4. Time space basis
    - B.4.1. Elements of the basis
    - B.4.2. Equivalence adjusting time basis vector
    - B.4.3. Determinant of the equivalence
    - B.4.4. Time space basis expressed in terms of the Lorentz basis
    - B.4.5. The additive Haar measure associated to the time space basis
  - B.5. Integrals over `SpaceTime d`
    - B.5.1. Measure preserving property of `toTimeAndSpace.symm`
    - B.5.2. Integrals over `SpaceTime d` expressed as integrals over `Time` and `Space d`

## iv. References

-/

noncomputable section

/-!

## A. The definition of `SpaceTime d`

-/

-- NOTE (`6V2DR`): `SpaceTime` should be refactored into a structure (or similar) to reduce casts.

/-- `SpaceTime d` corresponds to `d+1` dimensional space-time.
  This is equipped with an instance of the action of a Lorentz group,
  corresponding to Minkowski-spacetime. -/
abbrev SpaceTime (d : ℕ := 3) := Lorentz.Vector d

namespace SpaceTime

open Manifold
open Matrix
open Complex
open ComplexConjugate
open TensorSpecies

/-!

## C. Continuous linear map to coordinates

-/

/-- For a given `μ : Fin (1 + d)` `coord μ p` is the coordinate of
  `p` in the direction `μ`.

  This is denoted `𝔁 μ p`, where `𝔁` is typed with `\MCx`. -/
def coord {d : ℕ} (μ : Fin (1 + d)) : SpaceTime d →ₗ[ℝ] ℝ where
  toFun x := x (finSumFinEquiv.symm μ)
  map_add' x1 x2 := by
    simp
  map_smul' c x := by
    simp

@[inherit_doc coord]
scoped notation "𝔁" => coord

lemma coord_apply {d : ℕ} (μ : Fin (1 + d)) (y : SpaceTime d) :
    𝔁 μ y = y (finSumFinEquiv.symm μ) := by
  rfl

/-- The continuous linear map from a point in space time to one of its coordinates. -/
def coordCLM (μ : Fin 1 ⊕ Fin d) : SpaceTime d →L[ℝ] ℝ where
  toFun x := x μ
  map_add' x1 x2 := by
    simp
  map_smul' c x := by
    simp
  cont := by
    fun_prop

/-!

## D. Measures on `SpaceTime d`

-/
open MeasureTheory

/-!

### D.1. Instance of a measurable space

-/

instance {d : ℕ} : MeasurableSpace (SpaceTime d) := borel (SpaceTime d)

/-!

### D.2. Instance of a borel space

-/

instance {d : ℕ} : BorelSpace (SpaceTime d) where
  measurable_eq := by rfl

/-!

### D.4. Instance of a measure space

-/

instance {d : ℕ} : MeasureSpace (SpaceTime d) where
  volume := Lorentz.Vector.basis.addHaar

/-!

### D.5. Volume measure is positive on non-empty open sets

-/

instance {d : ℕ} : (volume (α := SpaceTime d)).IsOpenPosMeasure :=
  inferInstanceAs ((Lorentz.Vector.basis.addHaar).IsOpenPosMeasure)

/-!

### D.6. Volume measure is a finite measure on compact sets

-/

instance {d : ℕ} : IsFiniteMeasureOnCompacts (volume (α := SpaceTime d)) :=
  inferInstanceAs (IsFiniteMeasureOnCompacts (Lorentz.Vector.basis.addHaar))

/-!

### D.7. Volume measure is an additive Haar measure

-/

instance {d : ℕ} : Measure.IsAddHaarMeasure (volume (α := SpaceTime d)) :=
  inferInstanceAs (Measure.IsAddHaarMeasure (Lorentz.Vector.basis.addHaar))

/-!

## B. Maps to and from `Space` and `Time`

-/

/-!

### B.1. Linear map to `Space d`

-/

/-- The space part of spacetime. -/
def space {d : ℕ} : SpaceTime d →L[ℝ] Space d := LinearMap.toContinuousLinearMap {
  toFun := fun x => ⟨Lorentz.Vector.spatialPart x⟩
  map_add' := by
    intro x1 x2
    ext i
    simp
  map_smul' := by
    intro c x
    ext i
    simp
}

/-!

#### B.1.1. Explicit expansion of map to space

-/

lemma space_toCoord_symm {d : ℕ} (f : Fin 1 ⊕ Fin d → ℝ) :
    space f = fun i => f (Sum.inr i) := by
  funext i
  simp [space]

/-!

#### B.1.2. Equivariance of the to space under rotations

-/

open realLorentzTensor
open Tensor

/-- The function `space` is equivariant with respect to rotations. -/
lemma space_equivariant {d : ℕ} (Λ : LorentzGroup.Rotations d) (x : SpaceTime d) :
    space (Λ.1 • x) =
      ⟨fun i => ∑ j, (LorentzGroup.ofSpecialOrthogonal.symm Λ).1 i j * space x j⟩ := by
  ext i
  change (Λ.1 • x) (Sum.inr i) = _
  rw [Lorentz.Vector.smul_eq_mulVec]
  have hΛ : Matrix.fromBlocks 1 0 0 (LorentzGroup.ofSpecialOrthogonal.symm Λ).1 = Λ.1.1 := by
    exact congrArg (fun M : LorentzGroup d => M.1)
      (congrArg Subtype.val (LorentzGroup.ofSpecialOrthogonal.apply_symm_apply Λ))
  rw [← hΛ]
  simp [Matrix.mulVec_eq_sum, space, mul_comm]

/-!

### B.2. Linear map to `Time`

-/

/-- The time part of spacetime. -/
def time {d : ℕ} (c : SpeedOfLight := 1) : SpaceTime d →ₗ[ℝ] Time where
  toFun x := ⟨Lorentz.Vector.timeComponent x / c⟩
  map_add' x1 x2 := by
    ext
    simp [Lorentz.Vector.timeComponent]
    grind
  map_smul' c x := by
    ext
    simp [Lorentz.Vector.timeComponent]
    grind

/-!

#### B.2.1. Explicit expansion of map to time in terms of coordinates

-/

@[simp]
lemma time_val_toCoord_symm {d : ℕ} (c : SpeedOfLight) (f : Fin 1 ⊕ Fin d → ℝ) :
    (time c f).val = f (Sum.inl 0) / c := by
  simp [time, Lorentz.Vector.timeComponent]

/-!

### B.3. `toTimeAndSpace`: Continuous linear equivalence to `Time × Space d`

-/

/-- A continuous linear equivalence between `SpaceTime d` and
  `Time × Space d`. -/
def toTimeAndSpace {d : ℕ} (c : SpeedOfLight := 1) : SpaceTime d ≃L[ℝ] Time × Space d :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun x := (x.time c, x.space)
    invFun tx := (fun i =>
      match i with
      | Sum.inl _ => c * tx.1.val
      | Sum.inr i => tx.2 i)
    left_inv x := by
      simp only [time, LinearMap.coe_mk, AddHom.coe_mk, space]
      funext i
      match i with
      | Sum.inl 0 =>
        simp [Lorentz.Vector.timeComponent]
        field_simp
      | Sum.inr i => simp
    right_inv tx := by
      ext <;> simp [time, Lorentz.Vector.timeComponent, space, SpeedOfLight.val_ne_zero]
    map_add' x y := by
      simp only [Prod.mk_add_mk, Prod.mk.injEq]
      constructor
      · ext
        simp
      ext i
      simp
    map_smul' r x := by
      simp only [Prod.smul_mk, Prod.mk.injEq, RingHom.id_apply]
      exact ⟨map_smul (time c) r x, map_smul space r x⟩
  }

@[simp]
lemma toTimeAndSpace_symm_apply_time_space {d : ℕ} {c : SpeedOfLight} (x : SpaceTime d) :
    (toTimeAndSpace c).symm (x.time c, x.space) = x := by
  apply (toTimeAndSpace c).left_inv

@[simp]
lemma space_toTimeAndSpace_symm {d : ℕ} {c : SpeedOfLight} (t : Time) (s : Space d) :
    ((toTimeAndSpace c).symm (t, s)).space = s := by
  simp only [space, toTimeAndSpace]
  ext i
  simp

@[simp]
lemma time_toTimeAndSpace_symm {d : ℕ} {c : SpeedOfLight} (t : Time) (s : Space d) :
    ((toTimeAndSpace c).symm (t, s)).time c = t := by
  simp only [time, toTimeAndSpace]
  ext
  simp

@[simp]
lemma toTimeAndSpace_symm_apply_inl {d : ℕ} {c : SpeedOfLight} (t : Time) (s : Space d) :
    (toTimeAndSpace c).symm (t, s) (Sum.inl 0) = c * t := by rfl

@[simp]
lemma toTimeAndSpace_symm_apply_inr {d : ℕ} {c : SpeedOfLight} (t : Time) (x : Space d)
    (i : Fin d) :
    (toTimeAndSpace c).symm (t, x) (Sum.inr i) = x i := by rfl
/-!

#### B.3.1. Derivative of `toTimeAndSpace`

-/

@[simp]
lemma toTimeAndSpace_fderiv {d : ℕ} {c : SpeedOfLight} (x : SpaceTime d) :
    fderiv ℝ (toTimeAndSpace c) x = (toTimeAndSpace c).toContinuousLinearMap := by
  rw [ContinuousLinearEquiv.fderiv]

/-!

#### B.3.2. Derivative of the inverse of `toTimeAndSpace`

-/

@[simp]
lemma toTimeAndSpace_symm_fderiv {d : ℕ} {c : SpeedOfLight} (x : Time × Space d) :
    fderiv ℝ (toTimeAndSpace c).symm x = (toTimeAndSpace c).symm.toContinuousLinearMap := by
  rw [ContinuousLinearEquiv.fderiv]

/-!

#### B.3.3. `toTimeAndSpace` acting on spatial basis vectors

-/
lemma toTimeAndSpace_basis_inr {d : ℕ} {c : SpeedOfLight} (i : Fin d) :
    toTimeAndSpace c (Lorentz.Vector.basis (Sum.inr i))
    = (0, Space.basis i) := by
  simp only [toTimeAndSpace, time, LinearMap.coe_mk,
    AddHom.coe_mk, LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.coe_mk, Prod.mk.injEq]
  rw [Lorentz.Vector.timeComponent_basis_sum_inr]
  constructor
  · simp
  ext j
  simp [Space.basis_apply, space]

/-!

#### B.3.4. `toTimeAndSpace` acting on the temporal basis vectors

-/

lemma toTimeAndSpace_basis_inl {d : ℕ} {c : SpeedOfLight} :
    toTimeAndSpace (d := d) c (Lorentz.Vector.basis (Sum.inl 0)) = (⟨1/c.val⟩, 0) := by
  simp only [toTimeAndSpace, time, LinearMap.coe_mk,
    AddHom.coe_mk, LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.coe_mk, Prod.mk.injEq]
  rw [Lorentz.Vector.timeComponent_basis_sum_inl]
  constructor
  · simp
  ext j
  simp [space]

lemma toTimeAndSpace_basis_inl' {d : ℕ} {c : SpeedOfLight} :
    toTimeAndSpace (d := d) c (Lorentz.Vector.basis (Sum.inl 0)) = (1/c.val) • (1, 0) := by
  rw [toTimeAndSpace_basis_inl]
  simp only [one_div, Prod.smul_mk, smul_zero, Prod.mk.injEq, and_true]
  congr
  simp

/-!

### B.4. Time space basis

-/

/-- The basis of `SpaceTime` where the first component is `(c, 0, 0, ...)` instead
of `(1, 0, 0, ....).`-/
def timeSpaceBasis {d : ℕ} (c : SpeedOfLight := 1) :
    Module.Basis (Fin 1 ⊕ Fin d) ℝ (SpaceTime d) where
  repr := (toTimeAndSpace (d := d) c).toLinearEquiv.trans <|
      (Time.basis.toBasis.prod (Space.basis (d := d)).toBasis).repr

/-!

#### B.4.1. Elements of the basis

-/

@[simp]
lemma timeSpaceBasis_apply_inl {d : ℕ} (c : SpeedOfLight) :
    timeSpaceBasis (d := d) c (Sum.inl 0) = c.val • Lorentz.Vector.basis (Sum.inl 0) := by
  simp [timeSpaceBasis]
  apply (toTimeAndSpace (d := d) c).injective
  simp only [ContinuousLinearEquiv.apply_symm_apply, Fin.isValue, map_smul]
  rw [@toTimeAndSpace_basis_inl]
  simp only [one_div, Prod.smul_mk, smul_zero, Prod.mk.injEq, and_true]
  ext
  simp

@[simp]
lemma timeSpaceBasis_apply_inr {d : ℕ} (c : SpeedOfLight) (i : Fin d) :
    timeSpaceBasis (d := d) c (Sum.inr i) = Lorentz.Vector.basis (Sum.inr i) := by
  simp [timeSpaceBasis]
  apply (toTimeAndSpace (d := d) c).injective
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  rw [toTimeAndSpace_basis_inr]

/-!

#### B.4.2. Equivalence adjusting time basis vector

-/

/-- The equivalence on of `SpaceTime` taking `(1, 0, 0, ...)` to
of `(c, 0, 0, ....)` and keeping all other components the same. -/
def timeSpaceBasisEquiv {d : ℕ} (c : SpeedOfLight) :
    SpaceTime d ≃L[ℝ] SpaceTime d where
  toFun x := fun μ =>
    match μ with
    | Sum.inl 0 => c.val * x (Sum.inl 0)
    | Sum.inr i => x (Sum.inr i)
  invFun x := fun μ =>
    match μ with
    | Sum.inl 0 => (1 / c.val) * x (Sum.inl 0)
    | Sum.inr i => x (Sum.inr i)
  left_inv x := by
    funext μ
    match μ with
    | Sum.inl 0 =>
      field_simp
    | Sum.inr i =>
      rfl
  right_inv x := by
    funext μ
    match μ with
    | Sum.inl 0 =>
      field_simp
    | Sum.inr i =>
      rfl
  map_add' x y := by
    funext μ
    match μ with
    | Sum.inl 0 =>
      simp only [Fin.isValue, Lorentz.Vector.apply_add]
      ring
    | Sum.inr i =>
      simp
  map_smul' c x := by
    funext μ
    match μ with
    | Sum.inl 0 =>
      simp only [Fin.isValue, Lorentz.Vector.apply_smul, RingHom.id_apply]
      ring
    | Sum.inr i =>
      simp
  continuous_invFun := by
    simp only [one_div, Fin.isValue]
    apply Lorentz.Vector.continuous_of_apply
    intro μ
    match μ with
    | Sum.inl 0 =>
      simp only [Fin.isValue]
      fun_prop
    | Sum.inr i =>
      simp only
      fun_prop
  continuous_toFun := by
    apply Lorentz.Vector.continuous_of_apply
    intro μ
    match μ with
    | Sum.inl 0 =>
      simp only [Fin.isValue]
      fun_prop
    | Sum.inr i =>
      simp only
      fun_prop

/-!

#### B.4.3. Determinant of the equivalence

-/

lemma det_timeSpaceBasisEquiv {d : ℕ} (c : SpeedOfLight) :
    (timeSpaceBasisEquiv (d := d) c).det = c.val := by
  rw [@LinearEquiv.coe_det]
  let e := toTimeAndSpace (d := d) c
  trans LinearMap.det (e.toLinearMap ∘ₗ (timeSpaceBasisEquiv (d := d) c).toLinearMap ∘ₗ
    e.symm.toLinearMap)
  · simp only [ContinuousLinearEquiv.toLinearEquiv_symm, LinearMap.det_conj]
  have h1 : e.toLinearMap ∘ₗ (timeSpaceBasisEquiv (d := d) c).toLinearMap ∘ₗ
    e.symm.toLinearMap = (c.val • LinearMap.id).prodMap LinearMap.id := by
    apply LinearMap.ext
    intro tx
    simp [e, timeSpaceBasisEquiv, toTimeAndSpace]
    apply And.intro
    · ext
      simp
    · ext i
      simp [space]
  rw [h1]
  rw [LinearMap.det_prodMap]
  simp

/-!

#### B.4.4. Time space basis expressed in terms of the Lorentz basis

-/

lemma timeSpaceBasis_eq_map_basis {d : ℕ} (c : SpeedOfLight) :
    timeSpaceBasis (d := d) c =
    Module.Basis.map (Lorentz.Vector.basis (d := d)) (timeSpaceBasisEquiv c).toLinearEquiv := by
  ext μ
  match μ with
  | Sum.inl 0 =>
    simp [timeSpaceBasisEquiv]
    funext ν
    match ν with
    | Sum.inl 0 => simp
    | Sum.inr i => simp
  | Sum.inr i =>
    simp [timeSpaceBasisEquiv]
    funext ν
    match ν with
    | Sum.inl 0 => simp
    | Sum.inr j => simp

/-!

#### B.4.5. The additive Haar measure associated to the time space basis

-/

lemma timeSpaceBasis_addHaar {d : ℕ} (c : SpeedOfLight := 1) :
    (timeSpaceBasis (d := d) c).addHaar = (ENNReal.ofReal (c⁻¹)) • volume := by
  rw [timeSpaceBasis_eq_map_basis c, ← Module.Basis.map_addHaar]
  have h1 := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
    (f := (timeSpaceBasisEquiv (d := d) c).toLinearMap) (μ := Lorentz.Vector.basis.addHaar)
    (by simp [← LinearEquiv.coe_det, det_timeSpaceBasisEquiv])
  simp at h1
  rw [h1]
  simp [← LinearEquiv.coe_det, det_timeSpaceBasisEquiv]
  congr
  simp

/-!
### B.5. Integrals over `SpaceTime d`

-/

/-!

#### B.5.1. Measure preserving property of `toTimeAndSpace.symm`

-/

open MeasureTheory
lemma toTimeAndSpace_symm_measurePreserving {d : ℕ} (c : SpeedOfLight) :
    MeasurePreserving (toTimeAndSpace c).symm (volume.prod (volume (α := Space d)))
    (ENNReal.ofReal c⁻¹ • volume) := by
  refine ⟨(toTimeAndSpace c).symm.continuous.measurable, ?_⟩
  rw [Time.volume_eq_basis_addHaar, Space.volume_eq_addHaar]
  rw [← Module.Basis.prod_addHaar (v := Time.basis.toBasis) (w := Space.basis (d := d).toBasis)]
  rw [Module.Basis.map_addHaar
    (b := (Time.basis.toBasis).prod (Space.basis (d := d).toBasis))
    (f := (toTimeAndSpace c).symm)]
  change (timeSpaceBasis (d := d) c).addHaar = (ENNReal.ofReal c⁻¹) • volume
  simpa using (timeSpaceBasis_addHaar (d := d) c)

/-!

#### B.5.2. Integrals over `SpaceTime d` expressed as integrals over `Time` and `Space d`

-/

lemma spaceTime_integral_eq_time_space_integral {M} [NormedAddCommGroup M]
    [NormedSpace ℝ M] {d : ℕ} (c : SpeedOfLight)
    (f : SpaceTime d → M) :
    ∫ x : SpaceTime d, f x ∂(volume) =
    c.val • ∫ tx : Time × Space d, f ((toTimeAndSpace c).symm tx) ∂(volume.prod volume) := by
  let e : Time × Space d ≃ᵐ SpaceTime d :=
    (toTimeAndSpace c).symm.toHomeomorph.toMeasurableEquiv
  have hmp : MeasurePreserving (toTimeAndSpace c).symm (volume.prod (volume (α := Space d)))
      (ENNReal.ofReal ((c : ℝ)⁻¹) • volume) := toTimeAndSpace_symm_measurePreserving (d := d) c
  have hcomp :
      ∫ tx : Time × Space d, f ((toTimeAndSpace c).symm tx) ∂(volume.prod volume) =
      ∫ x : SpaceTime d, f x ∂((ENNReal.ofReal ((c : ℝ)⁻¹)) • volume) := by
    simpa [e] using
      (MeasureTheory.MeasurePreserving.integral_comp' (h := hmp) (f := e) (g := f))
  calc
    ∫ x : SpaceTime d, f x ∂(volume) =
        c.val • (((c : ℝ)⁻¹) • ∫ x : SpaceTime d, f x ∂(volume)) := by
      simp [smul_smul, SpeedOfLight.val_ne_zero c]
    _ = c.val • ∫ x : SpaceTime d, f x ∂((ENNReal.ofReal ((c : ℝ)⁻¹)) • volume) := by
      congr 1
      symm
      simpa [ENNReal.toReal_ofReal, inv_nonneg, SpeedOfLight.val_nonneg c] using
        (MeasureTheory.integral_smul_measure (μ := volume) (f := f)
          (c := ENNReal.ofReal ((c : ℝ)⁻¹)))
    _ = c.val • ∫ tx : Time × Space d, f ((toTimeAndSpace c).symm tx) ∂(volume.prod volume) := by
      congr 1
      simpa using hcomp.symm

lemma spaceTime_integrable_iff_space_time_integrable {M} [NormedAddCommGroup M]
    {d : ℕ} (c : SpeedOfLight)
    (f : SpaceTime d → M) :
    Integrable f volume ↔ Integrable (f ∘ ((toTimeAndSpace c).symm)) (volume.prod volume) := by
  let e : Time × Space d ≃ᵐ SpaceTime d :=
    (toTimeAndSpace c).symm.toHomeomorph.toMeasurableEquiv
  have hmp : MeasurePreserving (toTimeAndSpace c).symm (volume.prod (volume (α := Space d)))
      (ENNReal.ofReal ((c : ℝ)⁻¹) • volume) := toTimeAndSpace_symm_measurePreserving (d := d) c
  have hcomp :
      Integrable (f ∘ ((toTimeAndSpace c).symm)) (volume.prod volume) ↔
      Integrable f ((ENNReal.ofReal ((c : ℝ)⁻¹)) • volume) := by
    simpa [e] using
      (MeasureTheory.MeasurePreserving.integrable_comp_emb
        (h₁ := hmp) (h₂ := e.measurableEmbedding) (g := f))
  have hc0 : (c : ℝ) ≠ 0 := SpeedOfLight.val_ne_zero c
  have hscale0 : (ENNReal.ofReal ((c : ℝ)⁻¹)) ≠ 0 := by
    simp [hc0]
  have hsmul : Integrable f ((ENNReal.ofReal ((c : ℝ)⁻¹)) • volume) ↔ Integrable f volume :=
    MeasureTheory.integrable_smul_measure
      (f := f) (μ := volume)
      hscale0
      ENNReal.ofReal_ne_top
  exact (hcomp.trans hsmul).symm

lemma spaceTime_integral_eq_time_integral_space_integral {M} [NormedAddCommGroup M]
    [NormedSpace ℝ M] {d : ℕ} (c : SpeedOfLight)
    (f : SpaceTime d → M)
    (h : Integrable f volume) :
    ∫ x : SpaceTime d, f x =
    c.val • ∫ t : Time, ∫ x : Space d, f ((toTimeAndSpace c).symm (t, x)) := by
  rw [spaceTime_integral_eq_time_space_integral, MeasureTheory.integral_prod]
  rw [spaceTime_integrable_iff_space_time_integrable] at h
  exact h

lemma spaceTime_integral_eq_space_integral_time_integral {M} [NormedAddCommGroup M]
    [NormedSpace ℝ M] {d : ℕ} (c : SpeedOfLight)
    (f : SpaceTime d → M)
    (h : Integrable f volume) :
    ∫ x : SpaceTime d, f x =
    c.val • ∫ x : Space d, ∫ t : Time, f ((toTimeAndSpace c).symm (t, x)) := by
  rw [spaceTime_integral_eq_time_space_integral, MeasureTheory.integral_prod_symm]
  rw [spaceTime_integrable_iff_space_time_integrable] at h
  exact h

end SpaceTime

end
