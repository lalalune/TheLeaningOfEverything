/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.ZMod.Defs
import Particles.SuperSymmetry.SU5.ChargeSpectrum.Yukawa
import Particles.SuperSymmetry.SU5.ChargeSpectrum.Completions
import Meta.Linters.Sorry
/-!

# Charge spectra with values in `ZMod n`

## i. Overview

The way that we have defined `ChargeSpectrum` means we can consider values
of charges which are not only elements of `ℤ`, but also elements of other types.

In this file we will consider `ChargeSpectrum` which have values in `ZMod n` for various
natural numbers `n`, as well as charge spectra with values in `ZMod n × ZMod m`.

In this file we focus on 4-insertions of singlets to be phenomenologically viable.
In other files we usually just consider one.

## ii. Key results

- `ZModCharges n` : The finite set of `ZMod n` valued charges which are complete,
  not pheno-constrained and don't regenerate dangerous couplings
  with the Yukawa term up-to 4-inserstions of singlets.
- `ZModZModCharges m n` : The finite set of `ZMod n × ZMod m` valued charges which are complete,
  not pheno-constrained and don't regenerate dangerous couplings
  with the Yukawa term up-to 4-inserstions of singlets.

## iii. Table of contents

- A. The finite set of viable `ZMod n` charge spectra
  - A.1. General construction
  - A.2. Finite set of viable `ZMod 1` charge spectra is empty
  - A.3. Finite set of viable `ZMod 2` charge spectra is empty
  - A.4. Finite set of viable `ZMod 3` charge spectra is empty
  - A.5. Finite set of viable `ZMod 4` has four elements
  - A.6. Finite set of viable `ZMod 5` charge spectra is empty
  - A.7. Finite set of viable `ZMod 6` charge spectra is non-empty
- B. The finite set of viable `ZMod n × ZMod m` charge spectra
  - B.1. General construction

## iv. References

There are no known references for the material in this module.

-/

namespace SuperSymmetry

namespace SU5
namespace ChargeSpectrum

/-!

## A. The finite set of viable `ZMod n` charge spectra

-/

/-!

### A.1. General construction

-/

/-- The finite set of `ZMod n` valued charges which are complete,
  not pheno-constrained and don't regenerate dangerous couplings
  with the Yukawa term up-to 4-inserstions of singlets. -/
def ZModCharges (n : ℕ) [NeZero n] : Finset (ChargeSpectrum (ZMod n)) :=
  let S : Finset (ChargeSpectrum (ZMod n)) := ofFinset Finset.univ Finset.univ
  S.filter (fun x => IsComplete x ∧ ¬ x.IsPhenoConstrained ∧ ¬ x.YukawaGeneratesDangerousAtLevel 4)

/-!

### A.2. Finite set of viable `ZMod 1` charge spectra is empty

-/

/-- This lemma corresponds to the statement that there are no choices of `ℤ₁` representations
  which give a phenomenologically viable theory. -/
lemma ZModCharges_one_eq : ZModCharges 1 = ∅:= by decide

/-!

### A.3. Finite set of viable `ZMod 2` charge spectra is empty

-/

set_option maxRecDepth 2000 in
/-- This lemma corresponds to the statement that there are no choices of `ℤ₂` representations
  which give a phenomenologically viable theory. -/
lemma ZModCharges_two_eq : ZModCharges 2 = ∅ := by decide

/-!

### A.4. Finite set of viable `ZMod 3` charge spectra is empty

-/

/-- This lemma corresponds to the statement that there are no choices of `ℤ₃` representations
  which give a phenomenologically viable theory. -/
lemma ZModCharges_three_eq : ZModCharges 3 = ∅ := by decide +kernel

/-!

### A.5. Finite set of viable `ZMod 4` has four elements

-/

lemma ZModCharges_four_eq : ZModCharges 4 = {⟨some 0, some 2, {1}, {3}⟩,
    ⟨some 0, some 2, {3}, {1}⟩, ⟨some 1, some 2, {0}, {3}⟩, ⟨some 3, some 2, {0}, {1}⟩} := by
  decide +kernel

/-!

### A.6. Finite set of viable `ZMod 5` charge spectra is empty

-/

/-- This lemma corresponds to the statement that there are no choices of `ℤ₅` representations
  which give a phenomenologically viable theory. -/
lemma ZModCharges_five_eq : ZModCharges 5 = ∅ := by decide +kernel

/-!

### A.7. Finite set of viable `ZMod 6` charge spectra is non-empty

-/

private def withQHdQHuEmbedding {𝓩 : Type} (qHd qHu : Option 𝓩) :
    Finset 𝓩 × Finset 𝓩 ↪ ChargeSpectrum 𝓩 where
  toFun x := ⟨qHd, qHu, x.1, x.2⟩
  inj' := by
    rintro ⟨Q5, Q10⟩ ⟨Q5', Q10'⟩ h
    simp [ChargeSpectrum.eq_iff] at h
    simp [h]

private def ofFinsetUnivWithQHdQHu (n : ℕ) [NeZero n]
    (qHd qHu : Option (ZMod n)) :
    Finset (ChargeSpectrum (ZMod n)) :=
  let SQ : Finset (Finset (ZMod n)) := (Finset.univ : Finset (ZMod n)).powerset
  (SQ.product SQ).map (withQHdQHuEmbedding qHd qHu)

private lemma mem_ofFinsetUnivWithQHdQHu_iff {n : ℕ} [NeZero n]
    {qHd qHu : Option (ZMod n)}
    {x : ChargeSpectrum (ZMod n)} :
    x ∈ ofFinsetUnivWithQHdQHu n qHd qHu ↔ x.qHd = qHd ∧ x.qHu = qHu := by
  cases x
  simp [ofFinsetUnivWithQHdQHu, withQHdQHuEmbedding]

private def ZModChargesWithQHdQHu (n : ℕ) [NeZero n]
    (qHd qHu : Option (ZMod n)) :
    Finset (ChargeSpectrum (ZMod n)) :=
  (ofFinsetUnivWithQHdQHu n qHd qHu).filter
    fun x => IsComplete x ∧ ¬ x.IsPhenoConstrained ∧ ¬ x.YukawaGeneratesDangerousAtLevel 4

private lemma mem_ZModChargesWithQHdQHu_iff {n : ℕ} [NeZero n]
    {qHd qHu : Option (ZMod n)}
    {x : ChargeSpectrum (ZMod n)} :
    x ∈ ZModChargesWithQHdQHu n qHd qHu ↔
      x ∈ ZModCharges n ∧ x.qHd = qHd ∧ x.qHu = qHu := by
  simp [ZModChargesWithQHdQHu, ZModCharges, mem_ofFinsetUnivWithQHdQHu_iff, ofFinset_univ]

private lemma ZModChargesWithQHdQHu_subset {n : ℕ} [NeZero n]
    (qHd qHu : Option (ZMod n)) :
    ZModChargesWithQHdQHu n qHd qHu ⊆ ZModCharges n := by
  intro x hx
  exact (mem_ZModChargesWithQHdQHu_iff.mp hx).1

private lemma ZModChargesWithQHdQHu_mem_of_eq {n : ℕ} [NeZero n]
    {qHd qHu : Option (ZMod n)} {x : ChargeSpectrum (ZMod n)}
    (hx : x ∈ ZModCharges n) (hHd : x.qHd = qHd) (hHu : x.qHu = qHu) :
    x ∈ ZModChargesWithQHdQHu n qHd qHu := by
  exact mem_ZModChargesWithQHdQHu_iff.mpr ⟨hx, hHd, hHu⟩

private lemma ZModCharges_six_zero_zero_eq :
    ZModChargesWithQHdQHu 6 (some 0) (some 0) = ∅ := by
  decide +kernel

private lemma ZModCharges_six_zero_one_eq :
    ZModChargesWithQHdQHu 6 (some 0) (some 1) = ∅ := by
  decide +kernel

private lemma ZModCharges_six_zero_two_eq :
    ZModChargesWithQHdQHu 6 (some 0) (some 2) = {⟨some 0, some 2, {5}, {1}⟩} := by
  decide +kernel

private lemma ZModCharges_six_zero_three_eq :
    ZModChargesWithQHdQHu 6 (some 0) (some 3) = ∅ := by
  decide +kernel

private lemma ZModCharges_six_zero_four_eq :
    ZModChargesWithQHdQHu 6 (some 0) (some 4) = {⟨some 0, some 4, {1}, {5}⟩} := by
  decide +kernel

private lemma ZModCharges_six_zero_five_eq :
    ZModChargesWithQHdQHu 6 (some 0) (some 5) = ∅ := by
  decide +kernel

private lemma ZModCharges_six_one_zero_eq :
    ZModChargesWithQHdQHu 6 (some 1) (some 0) = {⟨some 1, some 0, {2}, {3}⟩} := by
  decide +kernel

private lemma ZModCharges_six_one_one_eq :
    ZModChargesWithQHdQHu 6 (some 1) (some 1) = ∅ := by
  decide +kernel

private lemma ZModCharges_six_one_two_eq :
    ZModChargesWithQHdQHu 6 (some 1) (some 2) = {⟨some 1, some 2, {4}, {1}⟩} := by
  decide +kernel

private lemma ZModCharges_six_one_three_eq :
    ZModChargesWithQHdQHu 6 (some 1) (some 3) = ∅ := by
  decide +kernel

private lemma ZModCharges_six_one_four_eq :
    ZModChargesWithQHdQHu 6 (some 1) (some 4) = {⟨some 1, some 4, {0}, {5}⟩,
      ⟨some 1, some 4, {3}, {2}⟩} := by
  decide +kernel

private lemma ZModCharges_six_one_five_eq :
    ZModChargesWithQHdQHu 6 (some 1) (some 5) = ∅ := by
  decide +kernel

private lemma ZModCharges_six_two_zero_eq :
    ZModChargesWithQHdQHu 6 (some 2) (some 0) = {⟨some 2, some 0, {1}, {3}⟩} := by
  decide +kernel

private lemma ZModCharges_six_two_one_eq :
    ZModChargesWithQHdQHu 6 (some 2) (some 1) = ∅ := by
  decide +kernel

private lemma ZModCharges_six_two_two_eq :
    ZModChargesWithQHdQHu 6 (some 2) (some 2) = ∅ := by
  decide +kernel

private lemma ZModCharges_six_two_three_eq :
    ZModChargesWithQHdQHu 6 (some 2) (some 3) = ∅ := by
  decide +kernel

private lemma ZModCharges_six_two_four_eq :
    ZModChargesWithQHdQHu 6 (some 2) (some 4) = {⟨some 2, some 4, {5}, {5}⟩} := by
  decide +kernel

private lemma ZModCharges_six_two_five_eq :
    ZModChargesWithQHdQHu 6 (some 2) (some 5) = ∅ := by
  decide +kernel

private lemma ZModCharges_six_three_zero_eq :
    ZModChargesWithQHdQHu 6 (some 3) (some 0) = ∅ := by
  decide +kernel

private lemma ZModCharges_six_three_one_eq :
    ZModChargesWithQHdQHu 6 (some 3) (some 1) = ∅ := by
  decide +kernel

private lemma ZModCharges_six_three_two_eq :
    ZModChargesWithQHdQHu 6 (some 3) (some 2) = {⟨some 3, some 2, {5}, {4}⟩} := by
  decide +kernel

private lemma ZModCharges_six_three_three_eq :
    ZModChargesWithQHdQHu 6 (some 3) (some 3) = ∅ := by
  decide +kernel

private lemma ZModCharges_six_three_four_eq :
    ZModChargesWithQHdQHu 6 (some 3) (some 4) = {⟨some 3, some 4, {1}, {2}⟩} := by
  decide +kernel

private lemma ZModCharges_six_three_five_eq :
    ZModChargesWithQHdQHu 6 (some 3) (some 5) = ∅ := by
  decide +kernel

private lemma ZModCharges_six_four_zero_eq :
    ZModChargesWithQHdQHu 6 (some 4) (some 0) = {⟨some 4, some 0, {5}, {3}⟩} := by
  decide +kernel

private lemma ZModCharges_six_four_one_eq :
    ZModChargesWithQHdQHu 6 (some 4) (some 1) = ∅ := by
  decide +kernel

private lemma ZModCharges_six_four_two_eq :
    ZModChargesWithQHdQHu 6 (some 4) (some 2) = {⟨some 4, some 2, {1}, {1}⟩} := by
  decide +kernel

private lemma ZModCharges_six_four_three_eq :
    ZModChargesWithQHdQHu 6 (some 4) (some 3) = ∅ := by
  decide +kernel

private lemma ZModCharges_six_four_four_eq :
    ZModChargesWithQHdQHu 6 (some 4) (some 4) = ∅ := by
  decide +kernel

private lemma ZModCharges_six_four_five_eq :
    ZModChargesWithQHdQHu 6 (some 4) (some 5) = ∅ := by
  decide +kernel

private lemma ZModCharges_six_five_zero_eq :
    ZModChargesWithQHdQHu 6 (some 5) (some 0) = {⟨some 5, some 0, {4}, {3}⟩} := by
  decide +kernel

private lemma ZModCharges_six_five_one_eq :
    ZModChargesWithQHdQHu 6 (some 5) (some 1) = ∅ := by
  decide +kernel

private lemma ZModCharges_six_five_two_eq :
    ZModChargesWithQHdQHu 6 (some 5) (some 2) = {⟨some 5, some 2, {0}, {1}⟩,
      ⟨some 5, some 2, {3}, {4}⟩} := by
  decide +kernel

private lemma ZModCharges_six_five_three_eq :
    ZModChargesWithQHdQHu 6 (some 5) (some 3) = ∅ := by
  decide +kernel

private lemma ZModCharges_six_five_four_eq :
    ZModChargesWithQHdQHu 6 (some 5) (some 4) = {⟨some 5, some 4, {2}, {5}⟩} := by
  decide +kernel

private lemma ZModCharges_six_five_five_eq :
    ZModChargesWithQHdQHu 6 (some 5) (some 5) = ∅ := by
  decide +kernel

lemma ZModCharges_six_eq : ZModCharges 6 = {⟨some 0, some 2, {5}, {1}⟩,
    ⟨some 0, some 4, {1}, {5}⟩, ⟨some 1, some 0, {2}, {3}⟩, ⟨some 1, some 2, {4}, {1}⟩,
    ⟨some 1, some 4, {0}, {5}⟩, ⟨some 1, some 4, {3}, {2}⟩, ⟨some 2, some 0, {1}, {3}⟩,
    ⟨some 2, some 4, {5}, {5}⟩, ⟨some 3, some 2, {5}, {4}⟩, ⟨some 3, some 4, {1}, {2}⟩,
    ⟨some 4, some 0, {5}, {3}⟩, ⟨some 4, some 2, {1}, {1}⟩, ⟨some 5, some 0, {4}, {3}⟩,
    ⟨some 5, some 2, {0}, {1}⟩, ⟨some 5, some 2, {3}, {4}⟩, ⟨some 5, some 4, {2}, {5}⟩} := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hx
    have hxComplete : IsComplete x := by
      simpa [ZModCharges] using hx
    let qHd := x.qHd
    have hqHd : x.qHd = qHd := rfl
    let qHu := x.qHu
    have hqHu : x.qHu = qHu := rfl
    fin_cases qHd
    · simp [hqHd] at hxComplete
    fin_cases qHu
    · simp [hqHu] at hxComplete
    all_goals
      have hx' := ZModChargesWithQHdQHu_mem_of_eq hx hqHd hqHu
      first
      | rw [ZModCharges_six_zero_zero_eq] at hx'; simp at hx'
      | rw [ZModCharges_six_zero_one_eq] at hx'; simp at hx'
      | rw [ZModCharges_six_zero_two_eq] at hx'; simpa [ChargeSpectrum.eq_iff] using hx'
      | rw [ZModCharges_six_zero_three_eq] at hx'; simp at hx'
      | rw [ZModCharges_six_zero_four_eq] at hx'; simpa [ChargeSpectrum.eq_iff] using hx'
      | rw [ZModCharges_six_zero_five_eq] at hx'; simp at hx'
      | rw [ZModCharges_six_one_zero_eq] at hx'; simpa [ChargeSpectrum.eq_iff] using hx'
      | rw [ZModCharges_six_one_one_eq] at hx'; simp at hx'
      | rw [ZModCharges_six_one_two_eq] at hx'; simpa [ChargeSpectrum.eq_iff] using hx'
      | rw [ZModCharges_six_one_three_eq] at hx'; simp at hx'
      | rw [ZModCharges_six_one_four_eq] at hx'; simpa [ChargeSpectrum.eq_iff] using hx'
      | rw [ZModCharges_six_one_five_eq] at hx'; simp at hx'
      | rw [ZModCharges_six_two_zero_eq] at hx'; simpa [ChargeSpectrum.eq_iff] using hx'
      | rw [ZModCharges_six_two_one_eq] at hx'; simp at hx'
      | rw [ZModCharges_six_two_two_eq] at hx'; simp at hx'
      | rw [ZModCharges_six_two_three_eq] at hx'; simp at hx'
      | rw [ZModCharges_six_two_four_eq] at hx'; simpa [ChargeSpectrum.eq_iff] using hx'
      | rw [ZModCharges_six_two_five_eq] at hx'; simp at hx'
      | rw [ZModCharges_six_three_zero_eq] at hx'; simp at hx'
      | rw [ZModCharges_six_three_one_eq] at hx'; simp at hx'
      | rw [ZModCharges_six_three_two_eq] at hx'; simpa [ChargeSpectrum.eq_iff] using hx'
      | rw [ZModCharges_six_three_three_eq] at hx'; simp at hx'
      | rw [ZModCharges_six_three_four_eq] at hx'; simpa [ChargeSpectrum.eq_iff] using hx'
      | rw [ZModCharges_six_three_five_eq] at hx'; simp at hx'
      | rw [ZModCharges_six_four_zero_eq] at hx'; simpa [ChargeSpectrum.eq_iff] using hx'
      | rw [ZModCharges_six_four_one_eq] at hx'; simp at hx'
      | rw [ZModCharges_six_four_two_eq] at hx'; simpa [ChargeSpectrum.eq_iff] using hx'
      | rw [ZModCharges_six_four_three_eq] at hx'; simp at hx'
      | rw [ZModCharges_six_four_four_eq] at hx'; simp at hx'
      | rw [ZModCharges_six_four_five_eq] at hx'; simp at hx'
      | rw [ZModCharges_six_five_zero_eq] at hx'; simpa [ChargeSpectrum.eq_iff] using hx'
      | rw [ZModCharges_six_five_one_eq] at hx'; simp at hx'
      | rw [ZModCharges_six_five_two_eq] at hx'; simpa [ChargeSpectrum.eq_iff] using hx'
      | rw [ZModCharges_six_five_three_eq] at hx'; simp at hx'
      | rw [ZModCharges_six_five_four_eq] at hx'; simpa [ChargeSpectrum.eq_iff] using hx'
      | rw [ZModCharges_six_five_five_eq] at hx'; simp at hx'
  · intro hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    all_goals
      first
      | exact ZModChargesWithQHdQHu_subset (n := 6) (some 0) (some 2) (by
          rw [ZModCharges_six_zero_two_eq]
          simp)
      | exact ZModChargesWithQHdQHu_subset (n := 6) (some 0) (some 4) (by
          rw [ZModCharges_six_zero_four_eq]
          simp)
      | exact ZModChargesWithQHdQHu_subset (n := 6) (some 1) (some 0) (by
          rw [ZModCharges_six_one_zero_eq]
          simp)
      | exact ZModChargesWithQHdQHu_subset (n := 6) (some 1) (some 2) (by
          rw [ZModCharges_six_one_two_eq]
          simp)
      | exact ZModChargesWithQHdQHu_subset (n := 6) (some 1) (some 4) (by
          rw [ZModCharges_six_one_four_eq]
          simp)
      | exact ZModChargesWithQHdQHu_subset (n := 6) (some 2) (some 0) (by
          rw [ZModCharges_six_two_zero_eq]
          simp)
      | exact ZModChargesWithQHdQHu_subset (n := 6) (some 2) (some 4) (by
          rw [ZModCharges_six_two_four_eq]
          simp)
      | exact ZModChargesWithQHdQHu_subset (n := 6) (some 3) (some 2) (by
          rw [ZModCharges_six_three_two_eq]
          simp)
      | exact ZModChargesWithQHdQHu_subset (n := 6) (some 3) (some 4) (by
          rw [ZModCharges_six_three_four_eq]
          simp)
      | exact ZModChargesWithQHdQHu_subset (n := 6) (some 4) (some 0) (by
          rw [ZModCharges_six_four_zero_eq]
          simp)
      | exact ZModChargesWithQHdQHu_subset (n := 6) (some 4) (some 2) (by
          rw [ZModCharges_six_four_two_eq]
          simp)
      | exact ZModChargesWithQHdQHu_subset (n := 6) (some 5) (some 0) (by
          rw [ZModCharges_six_five_zero_eq]
          simp)
      | exact ZModChargesWithQHdQHu_subset (n := 6) (some 5) (some 2) (by
          rw [ZModCharges_six_five_two_eq]
          simp)
      | exact ZModChargesWithQHdQHu_subset (n := 6) (some 5) (some 4) (by
          rw [ZModCharges_six_five_four_eq]
          simp)

/-!

## B. The finite set of viable `ZMod n × ZMod m` charge spectra

-/

/-!

### B.1. General construction

-/

/-- The finite set of `ZMod n × ZMod m` valued charges which are complete,
  not pheno-constrained and don't regenerate dangerous couplings
  with the Yukawa term up-to 4-inserstions of singlets. -/
def ZModZModCharges (n m : ℕ) [NeZero n] [NeZero m] : Finset (ChargeSpectrum (ZMod n × ZMod m)) :=
  let S : Finset (ChargeSpectrum (ZMod n × ZMod m)) := ofFinset (Finset.univ) Finset.univ
  S.filter (fun x => IsComplete x ∧
  ¬ x.IsPhenoConstrained ∧ ¬ x.YukawaGeneratesDangerousAtLevel 4)

end ChargeSpectrum
end SU5

end SuperSymmetry
