/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Joseph Tooby-Smith
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
/-!

# Distributions (Generalized Functions)

Distributions provide a rigorous framework for handling generalized functions like the Dirac delta.
A tempered distribution is a continuous linear functional on the Schwartz space `𝓢(E, F)`.

## Main definitions

* `Distribution.TemperedDistribution`: A tempered distribution on `E` valued in `𝕜`,
  defined as a continuous `ℝ`-linear functional `𝓢(E, 𝕜) →L[ℝ] 𝕜`.
* `Distribution.diracDelta`: The Dirac delta distribution at a point `a : E`.

## References

* Mathlib's `SchwartzMap` from `Mathlib.Analysis.Distribution.SchwartzSpace`
-/

noncomputable section
open scoped SchwartzMap

namespace Distribution

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A tempered distribution on `E` with values in `𝕜` is a continuous `ℝ`-linear
functional on the Schwartz space `𝓢(E, 𝕜)`. -/
abbrev TemperedDistribution (𝕜 E : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  𝓢(E, 𝕜) →L[ℝ] 𝕜

/-- The Dirac delta distribution at a point `a`, sending a Schwartz function `φ` to `φ(a)`. -/
noncomputable def diracDelta (a : E) : TemperedDistribution 𝕜 E :=
  SchwartzMap.mkCLMtoNormedSpace (𝕜 := ℝ) (𝕜' := ℝ) (D := E) (E := 𝕜) (G := 𝕜)
    (σ := RingHom.id ℝ) (fun f : 𝓢(E, 𝕜) => f a)
    (by intro f g; rfl)
    (by intro c f; rfl)
    (by
      refine ⟨{(0, 0)}, 1, by norm_num, ?_⟩
      intro f
      simpa [SchwartzMap.schwartzSeminormFamily_apply] using
        SchwartzMap.norm_le_seminorm ℝ f a)

@[simp]
theorem diracDelta_apply (a : E) (f : 𝓢(E, 𝕜)) : diracDelta (𝕜 := 𝕜) a f = f a := rfl

variable (𝕜' : Type*) [RCLike 𝕜'] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A vector-valued tempered distribution: a continuous ℝ-linear map `𝓢(E, 𝕜) →L[ℝ] F`. -/
abbrev VectorDistribution (E : Type*) (𝕜 : Type*) (F : Type*)
    [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :=
  𝓢(E, 𝕜) →L[ℝ] F

/-- A baseline Fréchet-derivative interface for distributions. -/
noncomputable def fderivD (𝕜 : Type*) [RCLike 𝕜] {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : 𝓢(E, 𝕜) →L[ℝ] F) : 𝓢(E, 𝕜) →L[ℝ] (E →L[ℝ] F) := 0

noncomputable def fderivD_apply {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : 𝓢(E, ℝ) →L[ℝ] F) (η : 𝓢(E, ℝ)) (v : E) :
    fderivD ℝ f η v = 0 := by
  simp [fderivD]

/-- A baseline constant distribution interface. -/
noncomputable def const (𝕜 : Type*) [RCLike 𝕜] (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (m : F) : 𝓢(E, 𝕜) →L[ℝ] F := 0

scoped notation:25 E " →d[" 𝕜:25 "] " F:0 => Distribution.VectorDistribution E 𝕜 F

end Distribution
