/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from ATOMSLab/LeanLJ (arXiv:2505.09095).
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.List.Range

/-!
# Pair Counting for Molecular Simulations

Proves that the number of unique pairs among `n` particles is `n(n-1)/2`.
This is fundamental for molecular dynamics and Monte Carlo simulations where
we need to iterate over all unique (i,j) pairs with i < j.

## Main results

* `pairs_length_eq` : the length of the pairs list equals `n(n-1)/2`
* `pairs_ordered` : all pairs `(i,j)` in the list satisfy `i < j`
* `pairs_bounded` : all indices in the pairs list are bounded by `n`

## References

* ATOMSLab/LeanLJ (GitHub), arXiv:2505.09095
-/

open List Finset
open scoped BigOperators

namespace MolecularDynamics

/-- Generate all unique pairs (i, j) with i < j from `{0, ..., n-1}`. -/
def pairs (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap fun i =>
    (List.range' (i + 1) (n - (i + 1))).map fun j => (i, j)

/-- Helper: the sum of a mapped list equals the corresponding finset sum. -/
private lemma list_sum_map_range (n : ℕ) (f : ℕ → ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [List.range_succ, Finset.sum_range_succ, ih]

/-- The sum of `0 + 1 + ... + (n-1)` via list equals the finset sum. -/
private lemma list_sum_range_eq_finset (n : ℕ) :
    (List.range n).sum = ∑ i ∈ Finset.range n, i := by
  have h := list_sum_map_range n id
  simp at h
  exact h

/-- The number of unique pairs among `n` objects is exactly `n(n-1)/2`.
    This is proven by showing that the pairs list has the correct length. -/
theorem pairs_length_eq (n : ℕ) :
    (pairs n).length = n * (n - 1) / 2 := by
  have h₀ :
      (pairs n).length =
      ((List.range n).map (fun i =>
        (List.range' (i + 1) (n - (i + 1))).length)).sum := by
    simp [pairs, List.length_flatMap, List.length_map]
  have h₁ :
      ((List.range n).map (fun i =>
        (List.range' (i + 1) (n - (i + 1))).length)).sum =
      ((List.range n).map (fun i => n - 1 - i)).sum := by
    have h_list :
        (List.range n).map
          (fun i =>
            (List.map (fun j => (i, j))
              (List.range' (i + 1) (n - (i + 1)))).length) =
          (List.range n).map (fun i => n - 1 - i) := by
      apply List.map_congr_left
      intro i _
      simp [List.length_map, List.length_range',
            Nat.sub_sub, add_comm, add_left_comm, add_assoc]
    simpa using congrArg List.sum h_list
  have h₂ :
      ((List.range n).map (fun i => n - 1 - i)).sum = (List.range n).sum := by
    have h_left :
        ((List.range n).map (fun i => n - 1 - i)).sum =
        ∑ i ∈ Finset.range n, (n - 1 - i) :=
      list_sum_map_range n (fun i => n - 1 - i)
    have h_right :
        (List.range n).sum = ∑ i ∈ Finset.range n, i :=
      list_sum_range_eq_finset n
    have h_reflect :
        (∑ i ∈ Finset.range n, (n - 1 - i)) = ∑ i ∈ Finset.range n, i :=
      Finset.sum_range_reflect (fun i : ℕ => i) n
    rw [h_left, h_reflect, ← h_right]
  have h_chain : (pairs n).length = (List.range n).sum := by
    rw [h₀, h₁, h₂]
  have h_sum : (List.range n).sum = n * (n - 1) / 2 := by
    rw [list_sum_range_eq_finset n, Finset.sum_range_id]
  rw [h_chain, h_sum]

/-- All pairs in the list are ordered: first component < second component. -/
theorem pairs_ordered {n : ℕ} :
    ∀ p ∈ pairs n, p.1 < p.2 := by
  intro ⟨i, j⟩ hp
  simp only [pairs, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_range'] at hp
  obtain ⟨i', _, j', ⟨hj_lo, _⟩, hij⟩ := hp
  simp only [Prod.mk.injEq] at hij
  obtain ⟨rfl, rfl⟩ := hij
  omega

/-- All pairs have both indices within bounds. -/
theorem pairs_bounded {n : ℕ} :
    ∀ p ∈ pairs n, p.1 < n ∧ p.2 < n := by
  intro ⟨i, j⟩ hp
  simp only [pairs, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_range'] at hp
  obtain ⟨i', hi', j', ⟨hj_lo, hj_hi⟩, hij⟩ := hp
  simp only [Prod.mk.injEq] at hij
  obtain ⟨rfl, rfl⟩ := hij
  exact ⟨hi', by omega⟩

/-- Number of pairs for small values: zero particles have zero pairs. -/
@[simp]
theorem pairs_zero : pairs 0 = [] := by
  simp [pairs]

/-- One particle has zero pairs. -/
@[simp]
theorem pairs_one : pairs 1 = [] := by
  simp [pairs]

/-- Two particles have exactly one pair. -/
@[simp]
theorem pairs_two : pairs 2 = [(0, 1)] := by
  decide +kernel

/-- Three particles have exactly three pairs. -/
@[simp]
theorem pairs_three : pairs 3 = [(0, 1), (0, 2), (1, 2)] := by
  decide +kernel

/-- The number of pairs grows quadratically. -/
theorem pairs_length_quadratic (n : ℕ) (hn : 2 ≤ n) :
    n ≤ (pairs n).length * 2 + 2 := by
  rw [pairs_length_eq]
  have h_ge : n ≤ n * (n - 1) := by
    calc n = n * 1 := (Nat.mul_one n).symm
      _ ≤ n * (n - 1) := Nat.mul_le_mul_left n (by omega)
  have h_div := Nat.div_add_mod (n * (n - 1)) 2
  have h_mod : n * (n - 1) % 2 < 2 := Nat.mod_lt _ (by omega)
  omega

/-! ## Verification Tests -/

section Tests

/-- Four particles have exactly six pairs. -/
@[simp]
theorem pairs_four : pairs 4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)] := by
  decide +kernel

/-- Verify length formula at n = 4: 4 * 3 / 2 = 6. -/
example : (pairs 4).length = 6 := by rw [pairs_length_eq]

/-- Verify length formula at n = 5: 5 * 4 / 2 = 10. -/
example : (pairs 5).length = 10 := by rw [pairs_length_eq]

/-- Verify length formula at n = 10: 10 * 9 / 2 = 45. -/
example : (pairs 10).length = 45 := by rw [pairs_length_eq]

/-- Verify length formula at n = 100: 100 * 99 / 2 = 4950. -/
example : (pairs 100).length = 4950 := by rw [pairs_length_eq]

/-- All pairs in `pairs 4` are ordered. -/
example : ∀ p ∈ pairs 4, p.1 < p.2 := pairs_ordered

/-- All pairs in `pairs 4` are bounded. -/
example : ∀ p ∈ pairs 4, p.1 < 4 ∧ p.2 < 4 := pairs_bounded

end Tests

end MolecularDynamics
