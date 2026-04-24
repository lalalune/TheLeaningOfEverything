/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Particles.BeyondTheStandardModel.PatiSalam.Basic
import Particles.BeyondTheStandardModel.GeorgiGlashow.Basic
/-!

# The Spin(10) Model

Note: By physicists this is usually called SO(10). However, the true gauge group involved
is Spin(10).

-/

namespace Spin10Model

/-- A concrete matrix model for the Spin(10) gauge group.

At the level of classical matrix groups, this uses `SO(10)` as the available
realization in the current library. Replacing this with the universal cover
`Spin(10)` requires a dedicated formalization of spin groups. -/
abbrev GaugeGroupI : Type := Matrix.specialOrthogonalGroup (Fin 10) ℝ

/-- A temporary stand-in for the unavailable Pati-Salam inclusion into `Spin(10)`.

The current library has a concrete `SO(10)` stand-in for `Spin(10)` but does not yet
formalize the low-rank accidental isomorphisms and universal-cover map needed for the
actual embedding. We therefore expose the trivial homomorphism as an explicit placeholder. -/
def inclPatiSalam : PatiSalam.GaugeGroupI →* GaugeGroupI where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := by simp

/-- The current stand-in Standard Model inclusion into `Spin(10)` through Pati-Salam. -/
def inclSM : StandardModel.GaugeGroupI →* GaugeGroupI :=
  inclPatiSalam.comp PatiSalam.inclSM

/-- A temporary stand-in for the unavailable Georgi-Glashow inclusion into `Spin(10)`. -/
def inclGeorgiGlashow : GeorgiGlashow.GaugeGroupI →* GaugeGroupI where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := by simp

/-- The current stand-in Standard Model inclusion into `Spin(10)` through Georgi-Glashow. -/
def inclSMThruGeorgiGlashow : StandardModel.GaugeGroupI →* GaugeGroupI :=
  inclGeorgiGlashow.comp GeorgiGlashow.inclSM

/-- The inclusion `inclSM` is equal to the inclusion `inclSMThruGeorgiGlashow`. -/
lemma inclSM_eq_inclSMThruGeorgiGlashow : inclSM = inclSMThruGeorgiGlashow := by
  ext g
  simp [inclSM, inclSMThruGeorgiGlashow, inclPatiSalam, inclGeorgiGlashow]

end Spin10Model
