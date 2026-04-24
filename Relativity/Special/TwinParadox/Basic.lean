/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Relativity.Special.ProperTime
/-!
# Twin Paradox

The twin paradox corresponds to the following scenario:

Two twins start at the same point `startPoint` in spacetime.
Twin A travels at constant speed to the spacetime point `endPoint`,
whilst twin B makes a detour through the spacetime `twinBMid` and then to `endPoint`.

In this file, we assume that both twins travel at constant speed,
and that the acceleration of Twin B is instantaneous.

The conclusion of this scenario is that Twin A will be older than Twin B when they meet at
`endPoint`. This is something we show here with an explicit example.

The origin of the twin paradox dates back to Paul Langevin in 1911.

-/

noncomputable section

namespace SpecialRelativity

open Matrix
open Real
open Lorentz
open Vector

/-- The twin paradox assuming instantaneous acceleration. -/
structure InstantaneousTwinParadox where
  /-- The starting point of both twins. -/
  startPoint : SpaceTime 3
  /-- The end point of both twins. -/
  endPoint : SpaceTime 3
  /-- The point twin B travels to between the start point and the end point. -/
  twinBMid : SpaceTime 3
  endPoint_causallyFollows_startPoint : causallyFollows startPoint endPoint
  twinBMid_causallyFollows_startPoint : causallyFollows startPoint twinBMid
  endPoint_causallyFollows_twinBMid : causallyFollows twinBMid endPoint

namespace InstantaneousTwinParadox
variable (T: InstantaneousTwinParadox)
open SpaceTime

/-- The proper time experienced by twin A travelling at constant speed
  from `T.startPoint` to `T.endPoint`. -/
def properTimeTwinA : ℝ := SpaceTime.properTime T.startPoint T.endPoint

/-- The proper time experienced by twin B travelling at constant speed
  from `T.startPoint` to `T.twinBMid`, and then from `T.twinBMid`
  to `T.endPoint`. -/
def properTimeTwinB : ℝ := SpaceTime.properTime T.startPoint T.twinBMid +
  SpaceTime.properTime T.twinBMid T.endPoint

/-- The proper time of twin A minus the proper time of twin B. -/
def ageGap : ℝ := T.properTimeTwinA - T.properTimeTwinB

-- NOTE (`6V2UQ`): Find conditions for which the twin-paradox age gap is zero.

private lemma minkowski_nonneg_of_causallyFollows {d : ℕ} {p q : SpaceTime d}
    (h : causallyFollows p q) :
    0 ≤ ⟪q - p, q - p⟫ₘ := by
  rcases h with h | h
  · exact le_of_lt ((timeLike_iff_norm_sq_pos _).mp h.1)
  · rw [(lightLike_iff_norm_sq_zero _).mp h.1]

private lemma timeComponent_nonneg_of_causallyFollows {d : ℕ} {p q : SpaceTime d}
    (h : causallyFollows p q) :
    0 ≤ (q - p).timeComponent := by
  rcases h with h | h
  · exact le_of_lt h.2
  · exact h.2

private lemma minkowski_self_eq_time_sq_sub_norm_sq {d : ℕ} {v : SpaceTime d}
    (hv : 0 ≤ v.timeComponent) :
    ⟪v, v⟫ₘ = v.timeComponent ^ 2 - ‖v.spatialPart‖ ^ 2 := by
  rw [minkowskiProduct_self_eq_timeComponent_spatialPart]
  simp [abs_of_nonneg hv]

private lemma norm_spatialPart_le_timeComponent_of_causal {d : ℕ} {v : SpaceTime d}
    (hv_time : 0 ≤ v.timeComponent) (hv_norm : 0 ≤ ⟪v, v⟫ₘ) :
    ‖v.spatialPart‖ ≤ v.timeComponent := by
  rw [← sq_le_sq₀ (norm_nonneg v.spatialPart) hv_time]
  have hv_eq := minkowski_self_eq_time_sq_sub_norm_sq hv_time (v := v)
  linarith

private lemma sqrt_mul_le_minkowski_of_causal {d : ℕ} {u v : SpaceTime d}
    (hu_time : 0 ≤ u.timeComponent) (hv_time : 0 ≤ v.timeComponent)
    (hu_norm : 0 ≤ ⟪u, u⟫ₘ) (hv_norm : 0 ≤ ⟪v, v⟫ₘ) :
    Real.sqrt ⟪u, u⟫ₘ * Real.sqrt ⟪v, v⟫ₘ ≤ ⟪u, v⟫ₘ := by
  have hu_space : ‖u.spatialPart‖ ≤ u.timeComponent :=
    norm_spatialPart_le_timeComponent_of_causal hu_time hu_norm
  have hv_space : ‖v.spatialPart‖ ≤ v.timeComponent :=
    norm_spatialPart_le_timeComponent_of_causal hv_time hv_norm
  have hsub_nonneg : 0 ≤
      u.timeComponent * v.timeComponent - ‖u.spatialPart‖ * ‖v.spatialPart‖ := by
    exact sub_nonneg.mpr <| mul_le_mul hu_space hv_space (norm_nonneg _) hu_time
  have hu_eq := minkowski_self_eq_time_sq_sub_norm_sq hu_time (v := u)
  have hv_eq := minkowski_self_eq_time_sq_sub_norm_sq hv_time (v := v)
  have hsq_aux : ⟪u, u⟫ₘ * ⟪v, v⟫ₘ ≤
      (u.timeComponent * v.timeComponent - ‖u.spatialPart‖ * ‖v.spatialPart‖) ^ 2 := by
    have hsq_nonneg :
        0 ≤ (u.timeComponent * ‖v.spatialPart‖ - v.timeComponent * ‖u.spatialPart‖) ^ 2 := by
      positivity
    nlinarith [hu_eq, hv_eq]
  have hsq :
      (Real.sqrt ⟪u, u⟫ₘ * Real.sqrt ⟪v, v⟫ₘ) ^ 2 ≤
        (u.timeComponent * v.timeComponent - ‖u.spatialPart‖ * ‖v.spatialPart‖) ^ 2 := by
    nlinarith [hsq_aux, Real.sq_sqrt hu_norm, Real.sq_sqrt hv_norm]
  have hle :
      Real.sqrt ⟪u, u⟫ₘ * Real.sqrt ⟪v, v⟫ₘ ≤
        u.timeComponent * v.timeComponent - ‖u.spatialPart‖ * ‖v.spatialPart‖ := by
    rw [← sq_le_sq₀ (by positivity) hsub_nonneg]
    exact hsq
  rw [minkowskiProduct_eq_timeComponent_spatialPart]
  have hinner : @Inner.inner ℝ _ _ u.spatialPart v.spatialPart ≤
      ‖u.spatialPart‖ * ‖v.spatialPart‖ := real_inner_le_norm _ _
  calc
    Real.sqrt ⟪u, u⟫ₘ * Real.sqrt ⟪v, v⟫ₘ
      ≤ u.timeComponent * v.timeComponent - ‖u.spatialPart‖ * ‖v.spatialPart‖ := hle
    _ ≤ ⟪u, v⟫ₘ := by
      rw [minkowskiProduct_eq_timeComponent_spatialPart]
      exact sub_le_sub le_rfl hinner

private lemma properTime_add_ge_of_causal {d : ℕ} {u v : SpaceTime d}
    (hu_time : 0 ≤ u.timeComponent) (hv_time : 0 ≤ v.timeComponent)
    (hu_norm : 0 ≤ ⟪u, u⟫ₘ) (hv_norm : 0 ≤ ⟪v, v⟫ₘ) :
    Real.sqrt ⟪u, u⟫ₘ + Real.sqrt ⟪v, v⟫ₘ ≤ Real.sqrt ⟪u + v, u + v⟫ₘ := by
  have hcross :
      Real.sqrt ⟪u, u⟫ₘ * Real.sqrt ⟪v, v⟫ₘ ≤ ⟪u, v⟫ₘ :=
    sqrt_mul_le_minkowski_of_causal hu_time hv_time hu_norm hv_norm
  have hadd :
      ⟪u + v, u + v⟫ₘ = ⟪u, u⟫ₘ + 2 * ⟪u, v⟫ₘ + ⟪v, v⟫ₘ := by
    calc
      ⟪u + v, u + v⟫ₘ = ⟪u, u + v⟫ₘ + ⟪v, u + v⟫ₘ := by simp
      _ = (⟪u, u⟫ₘ + ⟪u, v⟫ₘ) + (⟪v, u⟫ₘ + ⟪v, v⟫ₘ) := by simp
      _ = ⟪u, u⟫ₘ + 2 * ⟪u, v⟫ₘ + ⟪v, v⟫ₘ := by rw [minkowskiProduct_symm v u] ; ring
  have hsum_nonneg : 0 ≤ ⟪u + v, u + v⟫ₘ := by
    have huv_nonneg : 0 ≤ ⟪u, v⟫ₘ := le_trans (by positivity) hcross
    rw [hadd]
    nlinarith
  rw [← sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)]
  rw [Real.sq_sqrt hsum_nonneg]
  nlinarith [hcross, Real.sq_sqrt hu_norm, Real.sq_sqrt hv_norm]

/-- In the twin paradox with instantaneous acceleration, Twin A is always older
  then Twin B. -/
lemma ageGap_nonneg : 0 ≤ T.ageGap := by
  let u : SpaceTime 3 := T.twinBMid - T.startPoint
  let v : SpaceTime 3 := T.endPoint - T.twinBMid
  have hu_time : 0 ≤ u.timeComponent := by
    simpa [u] using
      timeComponent_nonneg_of_causallyFollows T.twinBMid_causallyFollows_startPoint
  have hv_time : 0 ≤ v.timeComponent := by
    simpa [v] using
      timeComponent_nonneg_of_causallyFollows T.endPoint_causallyFollows_twinBMid
  have hu_norm : 0 ≤ ⟪u, u⟫ₘ := by
    simpa [u] using
      minkowski_nonneg_of_causallyFollows T.twinBMid_causallyFollows_startPoint
  have hv_norm : 0 ≤ ⟪v, v⟫ₘ := by
    simpa [v] using
      minkowski_nonneg_of_causallyFollows T.endPoint_causallyFollows_twinBMid
  have htriangle :
      Real.sqrt ⟪u, u⟫ₘ + Real.sqrt ⟪v, v⟫ₘ ≤ Real.sqrt ⟪u + v, u + v⟫ₘ :=
    properTime_add_ge_of_causal hu_time hv_time hu_norm hv_norm
  have huv : u + v = T.endPoint - T.startPoint := by
    funext i
    simp [u, v]
  have hgap :
      T.properTimeTwinB ≤ T.properTimeTwinA := by
    simpa [properTimeTwinA, properTimeTwinB, SpaceTime.properTime, u, v, huv] using htriangle
  unfold ageGap
  linarith

/-!

## Example 1

-/

/-- The twin paradox in which:
- Twin A starts at `0` and travels at constant
  speed to `[15, 0, 0, 0]`.
- Twin B starts at `0` and travels at constant speed to
  `[7.5, 6, 0, 0]` and then at (different) constant speed to `[15, 0, 0, 0]`. -/
def example1 : InstantaneousTwinParadox where
  startPoint := 0
  endPoint := (fun
    | Sum.inl 0 => 15
    | Sum.inr i => 0)
  twinBMid := (fun
    | Sum.inl 0 => 7.5
    | Sum.inr 0 => 6
    | Sum.inr i => 0)
  endPoint_causallyFollows_startPoint := by
    simp [causallyFollows]
    left
    simp only [interiorFutureLightCone, sub_zero, Fin.isValue, Set.mem_setOf_eq, Nat.ofNat_pos,
      and_true]
    refine (timeLike_iff_norm_sq_pos _).mpr ?_
    rw [minkowskiProduct_toCoord]
    simp
  twinBMid_causallyFollows_startPoint := by
    simp only [causallyFollows]
    left
    simp only [interiorFutureLightCone, sub_zero, Fin.isValue, Set.mem_setOf_eq]
    norm_num
    refine (timeLike_iff_norm_sq_pos _).mpr ?_
    rw [minkowskiProduct_toCoord]
    simp [Fin.sum_univ_three]
    norm_num
  endPoint_causallyFollows_twinBMid := by
    simp [causallyFollows]
    left
    simp [interiorFutureLightCone]
    norm_num
    refine (timeLike_iff_norm_sq_pos _).mpr ?_
    rw [minkowskiProduct_toCoord]
    simp [Fin.sum_univ_three]
    norm_num

@[simp]
lemma example1_properTimeTwinA : example1.properTimeTwinA = 15 := by
  simp [properTimeTwinA, example1, properTime, minkowskiProduct_toCoord]

@[simp]
lemma example1_properTimeTwinB : example1.properTimeTwinB = 9 := by
  simp only [properTimeTwinB, properTime, example1, sub_zero, minkowskiProduct_toCoord,
    Fin.sum_univ_three, MulZeroClass.mul_zero, _root_.add_zero, map_sub,
    ContinuousLinearMap.coe_sub', Pi.sub_apply, Finset.sum_const_zero, MulZeroClass.zero_mul]
  norm_num
  rw [show √81 = 9 from sqrt_eq_cases.mpr (by norm_num)]
  rw [show √4 = 2 from sqrt_eq_cases.mpr (by norm_num)]
  norm_num

lemma example1_ageGap : example1.ageGap = 6 := by
  simp [ageGap]
  norm_num

end InstantaneousTwinParadox

-- NOTE (`7ROQ4`): Extend to non-instantaneous acceleration in a dedicated module.

end SpecialRelativity

end
