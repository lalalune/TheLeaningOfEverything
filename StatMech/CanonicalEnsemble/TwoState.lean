/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
import StatMech.CanonicalEnsemble.Finite
import Meta.Informal.Basic
/-!

# Two-state canonical ensemble

This module contains the definitions and properties related to the two-state
canonical ensemble.

-/

namespace CanonicalEnsemble

open Temperature
open Real MeasureTheory
open Constants

/-- The canonical ensemble corresponding to state system, with one state of energy
  `E₀` and the other state of energy `E₁`. -/
noncomputable def twoState (E₀ E₁ : ℝ) : CanonicalEnsemble (Fin 2) where
  energy := fun | 0 => E₀ | 1 => E₁
  dof := 0
  μ := Measure.count
  energy_measurable := by fun_prop

instance {E₀ E₁} : IsFinite (twoState E₀ E₁) where
  μ_eq_count := rfl
  dof_eq_zero := rfl
  phase_space_unit_eq_one := rfl

lemma twoState_partitionFunction_apply (E₀ E₁ : ℝ) (T : Temperature) :
    (twoState E₀ E₁).partitionFunction T = exp (- β T * E₀) + exp (- β T * E₁) := by
  rw [partitionFunction_of_fintype, twoState]
  simp [Fin.sum_univ_two]

lemma twoState_partitionFunction_apply_eq_cosh (E₀ E₁ : ℝ) (T : Temperature) :
    (twoState E₀ E₁).partitionFunction T =
    2 * exp (- β T * (E₀ + E₁) / 2) * cosh (β T * (E₁ - E₀) / 2) := by
  rw [twoState_partitionFunction_apply, Real.cosh_eq]
  field_simp
  simp only [mul_add, ← exp_add]
  ring_nf

@[simp]
lemma twoState_energy_fst (E₀ E₁ : ℝ) : (twoState E₀ E₁).energy 0 = E₀ := by
  rfl

@[simp]
lemma twoState_energy_snd (E₀ E₁ : ℝ) : (twoState E₀ E₁).energy 1 = E₁ := by
  rfl

/-- Probability of the first state (energy `E₀`) in closed form. -/
lemma twoState_probability_fst (E₀ E₁ : ℝ) (T : Temperature) :
    (twoState E₀ E₁).probability T 0 = 1 / 2 * (1 + Real.tanh (β T * (E₁ - E₀) / 2)) := by
  set x := β T * (E₁ - E₀) / 2
  set C := β T * (E₀ + E₁) / 2
  have hE0 : - β T * E₀ = x - C := by
    simp [x, C]; ring
  have hE1 : - β T * E₁ = -x - C := by
    simp [x, C]; ring
  rw [probability, mathematicalPartitionFunction_of_fintype]
  simp only [twoState, Fin.sum_univ_two, Fin.isValue]
  rw [hE0, hE1]
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  simp only [Real.exp_sub, Real.exp_neg]
  field_simp
  ring

/-- Probability of the second state (energy `E₁`) in closed form. -/
lemma twoState_probability_snd (E₀ E₁ : ℝ) (T : Temperature) :
    (twoState E₀ E₁).probability T 1 = 1 / 2 * (1 - Real.tanh (β T * (E₁ - E₀) / 2)) := by
  set x := β T * (E₁ - E₀) / 2
  set C := β T * (E₀ + E₁) / 2
  have hE0 : - β T * E₀ = x - C := by
    simp [x, C]; ring
  have hE1 : - β T * E₁ = -x - C := by
    simp [x, C]; ring
  rw [probability, mathematicalPartitionFunction_of_fintype]
  simp only [twoState, Fin.sum_univ_two, Fin.isValue]
  rw [hE0, hE1]
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  simp only [Real.exp_sub, Real.exp_neg]
  field_simp
  ring

lemma twoState_meanEnergy_eq (E₀ E₁ : ℝ) (T : Temperature) :
    (twoState E₀ E₁).meanEnergy T =
    (E₀ + E₁) / 2 - (E₁ - E₀) / 2 * Real.tanh (β T * (E₁ - E₀) / 2) := by
  rw [meanEnergy_of_fintype]
  simp [Fin.sum_univ_two, twoState_probability_fst, twoState_probability_snd]
  ring

/-- Closed form of the Helmholtz free energy for the two-state ensemble at positive temperature. -/
lemma twoState_helmholtzFreeEnergy_eq (E₀ E₁ : ℝ) (T : Temperature) (hT : 0 < T.val) :
    (twoState E₀ E₁).helmholtzFreeEnergy T =
      (E₀ + E₁) / 2 - kB * T.val * Real.log (2 * Real.cosh (β T * (E₁ - E₀) / 2)) := by
  rw [helmholtzFreeEnergy_dof_zero (𝓒 := twoState E₀ E₁) T rfl]
  have hZ : (twoState E₀ E₁).mathematicalPartitionFunction T =
      2 * exp (- β T * (E₀ + E₁) / 2) * cosh (β T * (E₁ - E₀) / 2) := by
    simpa [partitionFunction, twoState] using twoState_partitionFunction_apply_eq_cosh E₀ E₁ T
  rw [hZ]
  have hmul₁ : (2 : ℝ) * Real.exp (-β T * (E₀ + E₁) / 2) ≠ 0 := by
    exact mul_ne_zero two_ne_zero (Real.exp_ne_zero _)
  have hcosh : Real.cosh (β T * (E₁ - E₀) / 2) ≠ 0 := by
    exact (Real.cosh_pos _).ne'
  rw [Real.log_mul hmul₁ hcosh]
  rw [Real.log_mul two_ne_zero (Real.exp_ne_zero _)]
  rw [Real.log_exp]
  have hkβ : (kB : ℝ) * (T.β : ℝ) = 1 / T.val := kB_mul_beta T hT
  have hT0 : (T.val : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hT)
  have hkβT : (kB : ℝ) * (T.β : ℝ) * T.val = 1 := by
    rw [hkβ]
    field_simp [hT0]
  have hmid : -kB * T.val * (-↑(β T) * (E₀ + E₁) / 2) = (E₀ + E₁) / 2 := by
    have hkβT' : (kB : ℝ) * T.val * (T.β : ℝ) = 1 := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hkβT
    calc
      -kB * T.val * (-↑(β T) * (E₀ + E₁) / 2)
          = ((kB : ℝ) * T.val * (T.β : ℝ)) * ((E₀ + E₁) / 2) := by
              ring
      _ = (E₀ + E₁) / 2 := by
            simp [hkβT']
  calc
    -kB * T.val * (Real.log 2 + (-↑(β T) * (E₀ + E₁) / 2) +
        Real.log (Real.cosh (↑(β T) * (E₁ - E₀) / 2)))
        = -kB * T.val * Real.log 2 + (E₀ + E₁) / 2
            - kB * T.val * Real.log (Real.cosh (β T * (E₁ - E₀) / 2)) := by
              rw [mul_add, mul_add, hmid]
              ring
    _ = (E₀ + E₁) / 2
          - kB * T.val * (Real.log 2 + Real.log (Real.cosh (β T * (E₁ - E₀) / 2))) := by
            ring
    _ = (E₀ + E₁) / 2 - kB * T.val * Real.log (2 * Real.cosh (β T * (E₁ - E₀) / 2)) := by
          congr 2
          rw [Real.log_mul two_ne_zero (Real.cosh_pos _).ne']

/-- Closed form of the thermodynamic entropy for the two-state ensemble at positive temperature. -/
lemma twoState_entropy_eq (E₀ E₁ : ℝ) (T : Temperature) (hT : 0 < T.val) :
    (twoState E₀ E₁).thermodynamicEntropy T =
      kB * (Real.log (2 * Real.cosh (β T * (E₁ - E₀) / 2))
        - (β T * (E₁ - E₀) / 2) * Real.tanh (β T * (E₁ - E₀) / 2)) := by
  have hEint : Integrable (twoState E₀ E₁).energy ((twoState E₀ E₁).μProd T) := Integrable.of_finite
  have hFid := helmholtzFreeEnergy_eq_meanEnergy_sub_temp_mul_thermodynamicEntropy
    (𝓒 := twoState E₀ E₁) (T := T) hT (hE := hEint)
  have hT0 : (T.val : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hT)
  have hS : (twoState E₀ E₁).thermodynamicEntropy T =
      ((twoState E₀ E₁).meanEnergy T - (twoState E₀ E₁).helmholtzFreeEnergy T) / T.val := by
    apply (eq_div_iff hT0).2
    calc
      (twoState E₀ E₁).thermodynamicEntropy T * T.val
          = T.val * (twoState E₀ E₁).thermodynamicEntropy T := by
              ring
      _ = (twoState E₀ E₁).meanEnergy T - (twoState E₀ E₁).helmholtzFreeEnergy T := by
            linarith [hFid]
  set x : ℝ := β T * (E₁ - E₀) / 2
  have hx : β T * (E₁ - E₀) / 2 = x := by
    rfl
  have htanhx : Real.tanh (β T * (E₁ - E₀) / 2) = Real.tanh x := by
    rw [hx]
  have hlogx : Real.log (2 * Real.cosh (β T * (E₁ - E₀) / 2)) = Real.log (2 * Real.cosh x) := by
    rw [hx]
  rw [hS, twoState_meanEnergy_eq, twoState_helmholtzFreeEnergy_eq E₀ E₁ T hT, htanhx, hlogx]
  have hkβ : (kB : ℝ) * (T.β : ℝ) = 1 / T.val := kB_mul_beta T hT
  have hdelta : ((E₁ - E₀) / 2) / T.val = kB * x := by
    calc
      ((E₁ - E₀) / 2) / T.val = ((E₁ - E₀) / 2) * (1 / T.val) := by
        ring
      _ = ((E₁ - E₀) / 2) * (kB * (β T : ℝ)) := by
        rw [← hkβ]
      _ = kB * x := by
        simp [x]
        ring
  have hmain :
      (((E₀ + E₁) / 2 - (E₁ - E₀) / 2 * Real.tanh x) -
          ((E₀ + E₁) / 2 - kB * T.val * Real.log (2 * Real.cosh x))) / T.val
        = kB * Real.log (2 * Real.cosh x) - (((E₁ - E₀) / 2) / T.val) * Real.tanh x := by
    field_simp [hT0]
    ring
  rw [hmain, hdelta]
  ring

end CanonicalEnsemble
