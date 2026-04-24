/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Particles.StandardModel.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
/-!

# The Pati-Salam Model

The Pati-Salam model is a petite unified theory that unifies the Standard Model gauge group into
`SU(4) x SU(2) x SU(2)`.

This file currently contains informal-results about the Pati-Salam group.

-/

namespace PatiSalam
/-!

## The Pati-Salam gauge group.

-/

/-- The gauge group of the Pati-Salam model (unquotiented by ℤ₂), i.e., `SU(4) × SU(2) × SU(2)`. -/
abbrev GaugeGroupI : Type :=
  Matrix.specialUnitaryGroup (Fin 4) ℂ ×
    Matrix.specialUnitaryGroup (Fin 2) ℂ ×
    Matrix.specialUnitaryGroup (Fin 2) ℂ

namespace GaugeGroupI

/-- The underlying `SU(4)` component of a Pati-Salam gauge transformation. -/
def toSU4 : GaugeGroupI →* Matrix.specialUnitaryGroup (Fin 4) ℂ where
  toFun g := g.1
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The left `SU(2)` component of a Pati-Salam gauge transformation. -/
def toSU2L : GaugeGroupI →* Matrix.specialUnitaryGroup (Fin 2) ℂ where
  toFun g := g.2.1
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The right `SU(2)` component of a Pati-Salam gauge transformation. -/
def toSU2R : GaugeGroupI →* Matrix.specialUnitaryGroup (Fin 2) ℂ where
  toFun g := g.2.2
  map_one' := rfl
  map_mul' _ _ := rfl

@[ext]
lemma ext {g g' : GaugeGroupI} (h4 : toSU4 g = toSU4 g') (hL : toSU2L g = toSU2L g')
    (hR : toSU2R g = toSU2R g') : g = g' := by
  rcases g with ⟨g4, gL, gR⟩
  rcases g' with ⟨g4', gL', gR'⟩
  simp [toSU4, toSU2L, toSU2R] at h4 hL hR
  simp_all

end GaugeGroupI

/-- A temporary matrix-model stand-in for the Standard Model inclusion.

The full Pati-Salam embedding mixes the `SU(3)` and `U(1)` factors into the
`SU(4)` and right-handed `SU(2)` factors. Until that block-matrix construction
is formalized, we retain the visible `SU(2)` component and use identity elements
for the unavailable factors. -/
def inclSM : StandardModel.GaugeGroupI →* GaugeGroupI where
  toFun g := (1, StandardModel.GaugeGroupI.toSU2 g, 1)
  map_one' := by simp [StandardModel.GaugeGroupI.toSU2]
  map_mul' g h := by
    apply GaugeGroupI.ext
    · simp [GaugeGroupI.toSU4]
    · simp [GaugeGroupI.toSU2L, StandardModel.GaugeGroupI.toSU2]
    · simp [GaugeGroupI.toSU2R]

/-- The actual kernel of the current stand-in inclusion `inclSM`.

Because the present matrix-level model only retains the visible `SU(2)` factor,
this is larger than the physical `ℤ₃` kernel of the full Pati-Salam embedding. -/
def inclSM_ker : Subgroup StandardModel.GaugeGroupI :=
  inclSM.ker

@[simp]
lemma mem_inclSM_ker_iff (g : StandardModel.GaugeGroupI) :
    g ∈ inclSM_ker ↔ StandardModel.GaugeGroupI.toSU2 g = 1 := by
  change inclSM g = 1 ↔ StandardModel.GaugeGroupI.toSU2 g = 1
  constructor
  · intro h
    simpa [inclSM, GaugeGroupI.toSU2L, StandardModel.GaugeGroupI.toSU2] using
      congrArg GaugeGroupI.toSU2L h
  · intro h
    apply GaugeGroupI.ext
    · simp [inclSM, GaugeGroupI.toSU4]
    · simpa [inclSM, GaugeGroupI.toSU2L, StandardModel.GaugeGroupI.toSU2] using h
    · simp [inclSM, GaugeGroupI.toSU2R]

/-- The current stand-in embedding from the `ℤ₃`-quotiented Standard Model gauge group. -/
def embedSMℤ₃ : StandardModel.GaugeGroupℤ₃ →* GaugeGroupI :=
  inclSM

/-- A temporary stand-in for the unavailable `Spin(6) × Spin(4)` model.

At the current matrix-group level, we retain the underlying
`SU(4) × SU(2) × SU(2)` realization and expose the identity equivalence.
Replacing this with the actual spin-group equivalence requires a dedicated
formalization of spin groups and their low-rank accidental isomorphisms. -/
@[simps!]
def gaugeGroupISpinEquiv : GaugeGroupI ≃* GaugeGroupI :=
  MulEquiv.refl _

/-- The central element `-1` in `SU(4)`. -/
noncomputable def minusOneSU4 : Matrix.specialUnitaryGroup (Fin 4) ℂ := by
  refine ⟨(-1 : Matrix (Fin 4) (Fin 4) ℂ), ?_, ?_⟩
  · change (-1 : Matrix (Fin 4) (Fin 4) ℂ) ∈ Matrix.unitaryGroup (Fin 4) ℂ
    rw [Matrix.mem_unitaryGroup_iff]
    simp
  · norm_num [Matrix.det_neg]

/-- The central element `-1` in `SU(2)`. -/
noncomputable def minusOneSU2 : Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  refine ⟨(-1 : Matrix (Fin 2) (Fin 2) ℂ), ?_, ?_⟩
  · change (-1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ
    rw [Matrix.mem_unitaryGroup_iff]
    simp
  · norm_num [Matrix.det_neg]

/-- The nontrivial central element `(-1,-1,-1)` of the unquotiented Pati-Salam gauge group. -/
noncomputable def gaugeGroupℤ₂Elem : GaugeGroupI :=
  (minusOneSU4, minusOneSU2, minusOneSU2)

/-- The central order-two element `(-1,-1,-1)` in the unquotiented Pati-Salam gauge group. -/
lemma minusOneSU4_sq : minusOneSU4 ^ 2 = 1 := by
  ext i j
  simp [minusOneSU4]

lemma minusOneSU2_sq : minusOneSU2 ^ 2 = 1 := by
  ext i j
  simp [minusOneSU2]

/-- The scalar matrix `-1` commutes with every element of `SU(4)`. -/
lemma minusOneSU4_commute (g : Matrix.specialUnitaryGroup (Fin 4) ℂ) :
    g * minusOneSU4 = minusOneSU4 * g := by
  ext i j
  change ((↑g : Matrix (Fin 4) (Fin 4) ℂ) * (-(1 : Matrix (Fin 4) (Fin 4) ℂ))) i j =
    ((-(1 : Matrix (Fin 4) (Fin 4) ℂ)) * (↑g : Matrix (Fin 4) (Fin 4) ℂ)) i j
  rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one, Matrix.one_mul]

/-- The scalar matrix `-1` commutes with every element of `SU(2)`. -/
lemma minusOneSU2_commute (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    g * minusOneSU2 = minusOneSU2 * g := by
  ext i j
  change ((↑g : Matrix (Fin 2) (Fin 2) ℂ) * (-(1 : Matrix (Fin 2) (Fin 2) ℂ))) i j =
    ((-(1 : Matrix (Fin 2) (Fin 2) ℂ)) * (↑g : Matrix (Fin 2) (Fin 2) ℂ)) i j
  rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one, Matrix.one_mul]

lemma gaugeGroupℤ₂Elem_sq : gaugeGroupℤ₂Elem ^ 2 = 1 := by
  apply GaugeGroupI.ext
  · simpa [gaugeGroupℤ₂Elem, GaugeGroupI.toSU4] using minusOneSU4_sq
  · simpa [gaugeGroupℤ₂Elem, GaugeGroupI.toSU2L] using minusOneSU2_sq
  · simpa [gaugeGroupℤ₂Elem, GaugeGroupI.toSU2R] using minusOneSU2_sq

/-- The distinguished `(-1,-1,-1)` element is central in `GaugeGroupI`. -/
lemma gaugeGroupℤ₂Elem_commute (g : GaugeGroupI) :
    g * gaugeGroupℤ₂Elem = gaugeGroupℤ₂Elem * g := by
  apply GaugeGroupI.ext
  · simpa [GaugeGroupI.toSU4, gaugeGroupℤ₂Elem] using minusOneSU4_commute (GaugeGroupI.toSU4 g)
  · simpa [GaugeGroupI.toSU2L, gaugeGroupℤ₂Elem] using minusOneSU2_commute (GaugeGroupI.toSU2L g)
  · simpa [GaugeGroupI.toSU2R, gaugeGroupℤ₂Elem] using minusOneSU2_commute (GaugeGroupI.toSU2R g)

/-- The ℤ₂-subgroup of the unquotiented gauge group generated by the nontrivial element
`(-1, -1, -1)`.

See https://math.ucr.edu/home/baez/guts.pdf
-/
noncomputable def gaugeGroupℤ₂SubGroup : Subgroup GaugeGroupI := Subgroup.zpowers gaugeGroupℤ₂Elem

instance gaugeGroupℤ₂SubGroup_normal : gaugeGroupℤ₂SubGroup.Normal := by
  refine ⟨fun a ha g => ?_⟩
  rcases Subgroup.mem_zpowers_iff.mp ha with ⟨k, rfl⟩
  have hcomm : Commute g gaugeGroupℤ₂Elem := gaugeGroupℤ₂Elem_commute g
  have h_eq : g * gaugeGroupℤ₂Elem ^ k * g⁻¹ = gaugeGroupℤ₂Elem ^ k := by
    calc
      g * gaugeGroupℤ₂Elem ^ k * g⁻¹ = gaugeGroupℤ₂Elem ^ k * g * g⁻¹ := by
        rw [(hcomm.zpow_right k).eq]
      _ = gaugeGroupℤ₂Elem ^ k := by simp [mul_assoc]
  exact h_eq.symm ▸ Subgroup.zpow_mem_zpowers gaugeGroupℤ₂Elem k

/-- The Pati-Salam gauge group with its distinguished central `ℤ₂` quotient.

This is the quotient of `GaugeGroupI` by the subgroup generated by `(-1,-1,-1)`.

See https://math.ucr.edu/home/baez/guts.pdf
-/
abbrev GaugeGroupℤ₂ : Type := GaugeGroupI ⧸ gaugeGroupℤ₂SubGroup

/-- The canonical projection from the unquotiented gauge group to the `ℤ₂` quotient. -/
noncomputable def toGaugeGroupℤ₂ : GaugeGroupI →* GaugeGroupℤ₂ :=
  QuotientGroup.mk' gaugeGroupℤ₂SubGroup

@[simp]
lemma toGaugeGroupℤ₂_gaugeGroupℤ₂Elem : toGaugeGroupℤ₂ gaugeGroupℤ₂Elem = 1 := by
  exact (QuotientGroup.eq_one_iff gaugeGroupℤ₂Elem).mpr <| Subgroup.mem_zpowers gaugeGroupℤ₂Elem

/-- The current stand-in `ℤ₆` subgroup maps trivially into the `ℤ₂` quotient.

At present `StandardModel.gaugeGroupℤ₆SubGroup` is implemented as `⊥`, so the
factorization condition is the corresponding kernel inclusion. -/
lemma sm_ℤ₆_factor_through_gaugeGroupℤ₂SubGroup :
    StandardModel.gaugeGroupℤ₆SubGroup ≤ (toGaugeGroupℤ₂.comp inclSM).ker := by
  intro g hg
  have hg' : g = 1 := by
    simpa [StandardModel.gaugeGroupℤ₆SubGroup, Subgroup.mem_bot] using hg
  change (toGaugeGroupℤ₂.comp inclSM) g = 1
  simpa [hg']

/-- The current stand-in hom from `StandardModel.GaugeGroupℤ₆` to `GaugeGroupℤ₂`.

Since `StandardModel.GaugeGroupℤ₆` is presently definitionally equal to
`StandardModel.GaugeGroupI`, this is the direct composite of `inclSM` with the
canonical quotient map. -/
noncomputable def embedSMℤ₆Toℤ₂ : StandardModel.GaugeGroupℤ₆ →* GaugeGroupℤ₂ :=
  toGaugeGroupℤ₂.comp inclSM

@[simp]
lemma embedSMℤ₆Toℤ₂_apply (g : StandardModel.GaugeGroupℤ₆) :
    embedSMℤ₆Toℤ₂ g = toGaugeGroupℤ₂ (inclSM g) := rfl

end PatiSalam
