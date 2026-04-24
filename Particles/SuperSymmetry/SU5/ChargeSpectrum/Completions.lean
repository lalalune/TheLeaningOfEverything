/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Particles.SuperSymmetry.SU5.ChargeSpectrum.MinimallyAllowsTerm.OfFinset

/-!

# Completions of charges

## i. Overview

Recall that a charge spectrum has optional `Hu` and `Hd` charges, and
can have an empty set of `5`-bar or `10` charges.

We say a charge spectrum is complete if it has all types of fields present, i.e.
the `Hd` and `Hu` charges are present, and the sets of `5`-bar and `10` charges are non-empty.

Given a non-complete charge spectrum `x` we can find all the completions of `x`,
which charges in given subsets. That is, all charge spectra `y` which are a super set of `x`,
are complete, and have their charges in the given subsets.

## ii. Key results

- `IsComplete` : A predicate saying a charge spectrum is complete.
- `completions` : Given a charge spectrum `x` and finite sets of charges `S5` and `S10`,
  the multiset of completions of `x` with charges in `S5` and `S10`.
- `completionsTopYukawa` : A fast version of `completions` for an `x` which is in
  `minimallyAllowsTermsOfFinset S5 S10 .topYukawa`, or in other words has a `qHu` charge,
  a non-empty set of `10` charges, but does not have a `qHd` charge or any `5`-bar charges.

## iii. Table of contents

- A. The IsComplete predicate
  - A.1. The empty spectrum is not complete
  - A.2. The predicate `IsCompelete` is monotonic
- B. Multiset of completions
  - B.1. A membership condition
  - B.2. No duplicate condition
  - B.3. Completions of a complete charge spectrum
  - B.4. Membership of own completions
  - B.5. Completeness of members of completions
  - B.6. Subset of members of completions
- C. Completions for top Yukawa
  - C.1. No duplicates in completionsTopYukawa
  - C.2. Equivalence of completions and completionsTopYukawa

## iv. References

There are no known references for the material in this module.

-/

namespace SuperSymmetry

namespace SU5

namespace ChargeSpectrum

variable {𝓩 : Type}
/-!

## A. The IsComplete predicate

We say a charge spectrum is complete if it has all types of fields present, i.e.
the `Hd` and `Hu` charges are present, and the sets of `5`-bar and `10` charges are non-empty.

-/

/-- A charge spectrum is complete if it has all types of fields. -/
def IsComplete (x : ChargeSpectrum 𝓩) : Prop :=
  x.qHd.isSome ∧ x.qHu.isSome ∧ x.Q5 ≠ ∅ ∧ x.Q10 ≠ ∅

instance [DecidableEq 𝓩] (x : ChargeSpectrum 𝓩) : Decidable (IsComplete x) :=
  inferInstanceAs (Decidable (x.qHd.isSome ∧ x.qHu.isSome ∧ x.Q5 ≠ ∅ ∧ x.Q10 ≠ ∅))

/-!

### A.1. The empty spectrum is not complete

The empty charge spectrum is not complete, since it has no charges present.

-/

@[simp]
lemma not_isComplete_empty : ¬ IsComplete (∅ : ChargeSpectrum 𝓩) := by
  simp [IsComplete]

/-!

### A.2. The predicate `IsCompelete` is monotonic

The predicate `IsComplete` is monotonic with respect to the subset relation. That is, if `x` is a
subset of `y` and `x` is complete, then `y` is also complete.

-/

lemma isComplete_mono {x y : ChargeSpectrum 𝓩} (h : x ⊆ y) (hx : IsComplete x) :
    IsComplete y := by
  simp [IsComplete] at *
  rw [subset_def] at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra hn
    simp only [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hn
    have h1 := h.1
    have hx1 := hx.1
    rw [Option.isSome_iff_exists] at hx1
    obtain ⟨a, ha⟩ := hx1
    rw [hn, ha] at h1
    simp at h1
  · by_contra hn
    simp only [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hn
    have h1 := h.2.1
    have hx1 := hx.2.1
    rw [Option.isSome_iff_exists] at hx1
    obtain ⟨a, ha⟩ := hx1
    rw [hn, ha] at h1
    simp at h1
  · by_contra hn
    simp_all
  · by_contra hn
    simp_all

/-!

## B. Multiset of completions

The completions of a charge spectrum `x` with charges in given finite sets `S5` and `S10`
are all the charge spectra `y` which are a super set of `x`, are complete, and have
their charges in `S5` and `S10`.

-/

variable [DecidableEq 𝓩]

/-- Given a collection of charges `x` in `ofFinset S5 S10`,
  the minimal charges `y` in `ofFinset S5 S10` which are a super sets of `x` and are
  complete. -/
def completions (S5 S10 : Finset 𝓩) (x : ChargeSpectrum 𝓩) : Multiset (ChargeSpectrum 𝓩) :=
  let SqHd := if x.qHd.isSome then {x.qHd} else S5.val.map fun y => some y
  let SqHu := if x.qHu.isSome then {x.qHu} else S5.val.map fun y => some y
  let SQ5 := if x.Q5 ≠ ∅ then {x.Q5} else S5.val.map fun y => {y}
  let SQ10 := if x.Q10 ≠ ∅ then {x.Q10} else S10.val.map fun y => {y}
  (SqHd ×ˢ SqHu ×ˢ SQ5 ×ˢ SQ10).map (toProd).symm

/-!

### B.1. A membership condition

A simple relation for membership of a charge spectrum in the completions of another.

-/

lemma mem_completions_iff {S5 S10 : Finset 𝓩} {x y : ChargeSpectrum 𝓩} :
    y ∈ completions S5 S10 x ↔
    y.qHd ∈ (if x.qHd.isSome then {x.qHd} else S5.val.map fun y => some y) ∧
    y.qHu ∈ (if x.qHu.isSome then {x.qHu} else S5.val.map fun y => some y) ∧
    y.Q5 ∈ (if x.Q5 ≠ ∅ then {x.Q5} else S5.val.map fun y => {y}) ∧
    y.Q10 ∈ (if x.Q10 ≠ ∅ then {x.Q10} else S10.val.map fun y => {y}) := by
  constructor
  · intro hy
    simp only [completions, Multiset.mem_map] at hy
    obtain ⟨⟨a, b, c, d⟩, hmem, heq⟩ := hy
    have ⟨hmem1, hmem234⟩ := Multiset.mem_product.mp hmem
    have ⟨hmem2, hmem34⟩ := Multiset.mem_product.mp hmem234
    have ⟨hmem3, hmem4⟩ := Multiset.mem_product.mp hmem34
    have : y = ⟨a, b, c, d⟩ := by
      have : (toProd).symm (a, b, c, d) = (⟨a, b, c, d⟩ : ChargeSpectrum 𝓩) := rfl
      rw [this] at heq; exact heq.symm
    subst this
    exact ⟨hmem1, hmem2, hmem3, hmem4⟩
  · intro ⟨h1, h2, h3, h4⟩
    simp only [completions, Multiset.mem_map]
    exact ⟨(y.qHd, y.qHu, y.Q5, y.Q10),
      Multiset.mem_product.mpr ⟨h1, Multiset.mem_product.mpr ⟨h2,
        Multiset.mem_product.mpr ⟨h3, h4⟩⟩⟩,
      show (toProd).symm (y.qHd, y.qHu, y.Q5, y.Q10) = y by cases y; rfl⟩
/-!

### B.2. No duplicate condition

-/

/-- For speed we define `completions` to be a multiset, but in fact it has no duplicates,
so it could be defined as a finite set. -/
lemma completions_nodup (S5 S10 : Finset 𝓩) (x : ChargeSpectrum 𝓩) :
    (completions S5 S10 x).Nodup := by
  simp [completions]
  split_ifs
  all_goals
    refine Multiset.Nodup.map toProd.symm.injective ?_
    refine Multiset.Nodup.product ?_ (Multiset.Nodup.product ?_ (Multiset.Nodup.product ?_ ?_))
  any_goals exact Multiset.nodup_singleton _
  any_goals exact Finset.nodup_map_iff_injOn.mpr (by simp)

/-!

### B.3. Completions of a complete charge spectrum

-/

/-- The completions of a complete charge spectrum is just the singleton containing itself. -/
lemma completions_eq_singleton_of_complete {S5 S10 : Finset 𝓩} (x : ChargeSpectrum 𝓩)
    (hcomplete : IsComplete x) :
    completions S5 S10 x = {x} := by
  simp [completions]
  simp [IsComplete] at hcomplete
  by_cases h1 : x.qHd.isSome
  case' neg => simp_all
  by_cases h2 : x.qHu.isSome
  case' neg => simp_all
  by_cases h3 : x.Q5 ≠ ∅
  case' neg => simp_all
  by_cases h4 : x.Q10 ≠ ∅
  case' neg => simp_all
  simp_all
  rfl

/-!

### B.4. Membership of own completions

-/

/-- If a charge spectrum `x` is a member of its own completion then it is complete,
  and vice versa. -/
@[simp]
lemma self_mem_completions_iff_isComplete {S5 S10 : Finset 𝓩} (x : ChargeSpectrum 𝓩) :
    x ∈ completions S5 S10 x ↔ IsComplete x := by
  simp [mem_completions_iff, IsComplete]
  by_cases h1 : x.qHd.isSome
  case neg => simp_all
  by_cases h2 : x.qHu.isSome
  case' neg => simp_all
  by_cases h3 : x.Q5 ≠ ∅
  case' neg => simp_all
  by_cases h4 : x.Q10 ≠ ∅
  case' neg => simp_all
  simp_all

/-!

### B.5. Completeness of members of completions

We now show that any member of the completions of a charge spectrum is complete.

-/

/-- A charge spectrum which is a member of the completions of another charge
  spectrum is complete. -/
lemma mem_completions_isComplete {S5 S10 : Finset 𝓩} {x y : ChargeSpectrum 𝓩}
    (hx : y ∈ completions S5 S10 x) : IsComplete y := by
  match y with
  | ⟨qHd, qHu, Q5, Q10⟩ =>
  simp [mem_completions_iff] at hx
  match x with
  | ⟨x1, x2, x3, x4⟩ =>
  simp_all
  rw [IsComplete]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp
    by_cases hs : x1.isSome
    · simp_all
    · simp_all
      obtain ⟨a, h, rfl⟩ := hx.1
      simp
  · simp
    by_cases hs : x2.isSome
    · simp_all
    · simp_all
      obtain ⟨a, h, rfl⟩ := hx.2.1
      simp
  · simp
    by_cases hs : x3 ≠ ∅
    · simp_all
    · simp_all
      obtain ⟨a, h, rfl⟩ := hx.2.2.1
      simp
  · simp
    by_cases hs : x4 ≠ ∅
    · simp_all
    · simp_all
      obtain ⟨a, h, rfl⟩ := hx.2.2.2
      simp

/-!

### B.6. Subset of members of completions

We show that any member of the completions of a charge spectrum is a super set of that
charge spectrum.

-/

/-- If `y` is in the completions of `x` then `x ⊆ y`. -/
lemma self_subset_mem_completions (S5 S10 : Finset 𝓩) (x y : ChargeSpectrum 𝓩)
    (hy : y ∈ completions S5 S10 x) : x ⊆ y := by
  simp [mem_completions_iff] at hy
  rw [Subset]
  dsimp [hasSubset]
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_cases h : x.qHd.isSome
    · simp_all
    · simp_all
  · by_cases h : x.qHu.isSome
    · simp_all
    · simp_all
  · by_cases h : x.Q5 ≠ ∅
    · simp_all
    · simp_all
  · by_cases h : x.Q10 ≠ ∅
    · simp_all
    · simp_all

/-- If `x` is a subset of `y` and `y` is complete, then there is a completion of `x` which is also
  a subset of `y`. -/
lemma exist_completions_subset_of_complete (S5 S10 : Finset 𝓩) (x y : ChargeSpectrum 𝓩)
    (hsubset : x ⊆ y) (hy : y ∈ ofFinset S5 S10) (hycomplete : IsComplete y) :
    ∃ z ∈ completions S5 S10 x, z ⊆ y := by
  by_cases hx : IsComplete x
  · use x
    simp_all
  rw [Subset] at hsubset
  dsimp [hasSubset] at hsubset
  match x, y with
  | ⟨x1, x2, x3, x4⟩, ⟨y1, y2, y3, y4⟩ =>
  simp [IsComplete] at hycomplete
  rw [Option.isSome_iff_exists, Option.isSome_iff_exists] at hycomplete
  obtain ⟨y1, rfl⟩ := hycomplete.1
  obtain ⟨y2, rfl⟩ := hycomplete.2.1
  rw [Finset.eq_empty_iff_forall_notMem, Finset.eq_empty_iff_forall_notMem] at hycomplete
  simp at hycomplete
  obtain ⟨z3, hz3⟩ := hycomplete.1
  obtain ⟨z4, hz4⟩ := hycomplete.2
  simp [mem_ofFinset_iff] at hy
  have hz3Mem : z3 ∈ S5 := by
    apply hy.2.2.1
    simp_all
  have hz4Mem : z4 ∈ S10 := by
    apply hy.2.2.2
    simp_all
  have hy1' : some y1 ∈ if x1.isSome = true then {x1} else
      Multiset.map (fun y => some y) S5.val := by
    by_cases h1 : x1.isSome
    · simp_all
      rw [Option.isSome_iff_exists] at h1
      obtain ⟨a, rfl⟩ := h1
      simp_all
    · simp_all
  have hy2' : some y2 ∈ if x2.isSome = true then {x2} else
      Multiset.map (fun y => some y) S5.val := by
    by_cases h2 : x2.isSome
    · simp_all
      rw [Option.isSome_iff_exists] at h2
      obtain ⟨a, rfl⟩ := h2
      simp_all
    · simp_all
  simp_all
  by_cases h3 : x3 ≠ ∅
  · by_cases h4 : x4 ≠ ∅
    · use ⟨y1, y2, x3, x4⟩
      constructor
      · simp_all [mem_completions_iff]
      · rw [Subset]
        dsimp [hasSubset]
        simp_all
    · simp at h4
      subst h4
      use ⟨y1, y2, x3, {z4}⟩
      constructor
      · simp_all [mem_completions_iff]
      · rw [Subset]
        dsimp [hasSubset]
        simp_all
  · simp at h3
    subst h3
    by_cases h4 : x4 ≠ ∅
    · use ⟨y1, y2, {z3}, x4⟩
      constructor
      · simp_all [mem_completions_iff]
      · rw [Subset]
        dsimp [hasSubset]
        simp_all
    · simp at h4
      subst h4
      use ⟨y1, y2, {z3}, {z4}⟩
      constructor
      · simp_all [mem_completions_iff]
      · rw [Subset]
        dsimp [hasSubset]
        simp_all

/-!

## C. Completions for top Yukawa

We give a fast version of `completions` in the case when `x` has a `qHu` charge,
and a non-empty set of `10` charges, but does not have a `qHd` charge or any `5`-bar charges.
Here we only need to specify the allowed `5`-bar charges, not the allowed `10` charges.

This is the case for charges which minimally allow the top Yukawa coupling.

These definitions are primarily for speed, as this is the most common case we will
look at.

-/

/-- A fast version of `completions` for an `x` which is in
  `minimallyAllowsTermsOfFinset S5 S10 .topYukawa`. -/
def completionsTopYukawa (S5 : Finset 𝓩) (x : ChargeSpectrum 𝓩) :
    Multiset (ChargeSpectrum 𝓩) :=
  (S5.val ×ˢ S5.val).map fun (qHd, q5) => ⟨qHd, x.qHu, {q5}, x.Q10⟩

/-!

### C.1. No duplicates in completionsTopYukawa

Like for `completions`, we define `completionsTopYukawa` as a multiset for speed,
however, we can show it has no duplicates.

-/

omit [DecidableEq 𝓩] in
/-- The multiset `completionsTopYukawa S5 x` has no duplicates. -/
lemma completionsTopYukawa_nodup {S5 : Finset 𝓩} (x : ChargeSpectrum 𝓩) :
    (completionsTopYukawa S5 x).Nodup := by
  simp [completionsTopYukawa]
  refine Multiset.Nodup.map_on ?_ ?_
  intro (z1, z2) hz (y1, y2) hy h
  simp [eq_iff] at h
  simp_all
  exact (S5.product S5).nodup

/-!

### C.2. Equivalence of completions and completionsTopYukawa

For charges `x` which are in `minimallyAllowsTermsOfFinset S5 S10 .topYukawa`,
we show that `completions S5 S10 x` and `completionsTopYukawa S5 x` are equal multisets.

-/

/-- The multisets `completions S5 S10 x` and `completionsTopYukawa S5 x` are equivalent if
  `x` minimally allows the top Yukawa. -/
lemma completions_eq_completionsTopYukawa_of_mem_minimallyAllowsTermsOfFinset [AddCommGroup 𝓩]
    {S5 S10 : Finset 𝓩} (x : ChargeSpectrum 𝓩)
    (hx : x ∈ minimallyAllowsTermsOfFinset S5 S10 .topYukawa) :
    completions S5 S10 x = completionsTopYukawa S5 x := by
  dsimp [minimallyAllowsTermsOfFinset] at hx
  rcases Multiset.mem_map.mp hx with ⟨y, hy, rfl⟩
  rcases Multiset.mem_filter.mp hy with ⟨hyProd, hyZero⟩
  obtain ⟨hqHu, hQ10⟩ := Multiset.mem_product.mp hyProd
  obtain ⟨qHu, Q10⟩ := y
  dsimp at hqHu hQ10 ⊢
  have hQ10card : Q10.card = 2 := (mem_toMultisetsTwo_iff Q10).1 hQ10 |>.2
  have hQ10ne : Q10.toFinset ≠ ∅ := by
    intro hEmpty
    have hQ10zero : Q10 = 0 := by
      simpa [Multiset.toFinset_eq_empty] using hEmpty
    simpa [hQ10zero] using hQ10card
  apply (Multiset.Nodup.ext (completions_nodup S5 S10 _) (completionsTopYukawa_nodup _)).2
  intro z
  cases z
  simp [mem_completions_iff, completionsTopYukawa, hQ10ne]
  constructor
  · rintro ⟨⟨qHd, hqHdS5, hqHd⟩, hqHu, ⟨q5, hq5S5, hQ5⟩, hQ10'⟩
    exact ⟨qHd, q5, ⟨hqHdS5, hq5S5⟩, hqHd, hqHu.symm, hQ5, hQ10'.symm⟩
  · rintro ⟨qHd, q5, ⟨hqHdS5, hq5S5⟩, hqHd, hqHu, hQ5, hQ10'⟩
    exact ⟨⟨qHd, hqHdS5, hqHd⟩, hqHu.symm, ⟨q5, hq5S5, hQ5⟩, hQ10'.symm⟩
end ChargeSpectrum

end SU5

end SuperSymmetry
