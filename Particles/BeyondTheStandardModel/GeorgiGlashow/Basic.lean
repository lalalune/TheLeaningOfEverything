/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Particles.StandardModel.Basic
/-!

# The Georgi-Glashow Model

The Georgi-Glashow model is a grand unified theory that unifies the Standard Model gauge group into
`SU(5)`.

This file currently contains informal-results about the Georgi-Glashow group.

-/

namespace GeorgiGlashow

/-- A current matrix-level stand-in for the Georgi-Glashow gauge group.

The physical model uses `SU(5)`. At the current stage of the formalization we retain
the visible `SU(3)` block as the implemented stand-in. -/
abbrev GaugeGroupI : Type := Matrix.specialUnitaryGroup (Fin 3) ℂ

/-- The current stand-in embedding into Georgi-Glashow.

This keeps only the visible `SU(3)` component of the Standard Model gauge group. -/
def inclSM : StandardModel.GaugeGroupI →* GaugeGroupI :=
  StandardModel.GaugeGroupI.toSU3

/-- The actual kernel of the current stand-in Georgi-Glashow embedding.

Because the present stand-in retains only the visible `SU(3)` block, this kernel is
larger than the physical `ℤ₆` kernel of the full Georgi-Glashow embedding. -/
def inclSM_ker : Subgroup StandardModel.GaugeGroupI :=
  inclSM.ker

/-- The current stand-in map from `StandardModel.GaugeGroupℤ₆` into Georgi-Glashow.

Since `StandardModel.GaugeGroupℤ₆` is presently definitionally equal to
`StandardModel.GaugeGroupI`, this is just the direct stand-in embedding `inclSM`. -/
noncomputable def embedSMℤ₆ : StandardModel.GaugeGroupℤ₆ →* GaugeGroupI :=
  inclSM

@[simp]
lemma embedSMℤ₆_apply (g : StandardModel.GaugeGroupℤ₆) :
    embedSMℤ₆ g = inclSM g := rfl

end GeorgiGlashow
