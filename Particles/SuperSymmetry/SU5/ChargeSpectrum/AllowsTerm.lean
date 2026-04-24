/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Particles.SuperSymmetry.SU5.ChargeSpectrum.OfPotentialTerm
import Mathlib.Tactic.FinCases

/-!

# Charges allowing terms

## i. Overview

To each charge spectrum `x : ChargeSpectrum 𝓩` we say it
allows the potential term `T : PotentialTerm`, if one of the charges associated with that
potential term is zero.

What this means, is that there is a choice of charges from the charge spectrum `x` that
can be assigned to the fields in the potential term `T` such that the total charge is zero,
and therefore that the term is present in the potential. The presence of
absence of certain terms is of phenomenological importance.

This concept is captured by the proposition `AllowsTerm`.

In addition to this, for each potential term `T`, we define a function `allowsTermForm`
which takes three elements of `𝓩`, `a`, `b`, and `c` and returns a charge spectrum
which allows the term `T`. We will show in `allowsTerm_iff_subset_allowsTermForm`
that any charge spectrum that allows a term `T` has a subset which can be expressed as
`allowsTermForm a b c T` for some `a`, `b`, and `c`.

We also define the propositions `AllowsTermQ5 x q5 T` and `AllowsTermQ10 x q10 T`
which correspond to the condition that adding a charge `q5` to the `Q5` charges of
the charge spectrum `x`, or adding a charge `q10` to the `Q10` charges of the
charge spectrum `x`, leads to a zero charge in the charges of potential term `T`.

## ii. Key results

- `AllowsTerm` : The proposition that a charge spectrum allows a potential term.
- `allowsTermForm` : A function which for each potential term `T` and three charges
  `a`, `b`, and `c` returns a charge spectrum which allows the term `T`,
  and such that any charge spectrum allowing `T` has a subset of this form.
- `AllowsTermQ5` : The proposition that adding a charge `q5` to the `Q5` charges
  of a charge spectrum `x` allows the potential term `T` due to the addition of that charge.
- `AllowsTermQ10` : The proposition that adding a charge `q10` to the `Q10` charges
  of a charge spectrum `x` allows the potential term `T` due to the addition of that charge.

## iii. Table of contents

- A. Charge spectrums allowing potential terms
  - A.1. Decidability of `AllowsTerm`
  - A.2. Monotonicity of `AllowsTerm`
- B. Forms of charges which allow potential terms
  - B.1. `allowsTermForm` allows the potential term
  - B.2. Subset relations for `allowsTermForm`
  - B.3. Card of `allowsTermForm`
  - B.4. If `AllowsTerm` then subset equal to `allowsTermForm a b c T`
  - B.5. `AllowsTerm` if and only if subset equal to `allowsTermForm a b c T`
  - B.6. Cardinality of subset allowing potential term
- C. Allowing a potential term by insertion of a `Q5` charge
  - C.1. Decidability of `AllowsTermQ5`
  - C.2. AllowsTermQ5 or AllowsTerm from AllowsTerm with inserted of `Q5` charge
  - C.3. AllowsTerm with inserted of `Q5` charge from AllowsTermQ5
  - C.4. AllowsTerm with inserted of `Q5` charge iff AllowsTermQ5 or AllowsTerm
- D. Allowing a potential term by insertion of a `Q10` charge
  - D.1. Decidability of `AllowsTermQ5`
  - D.2. AllowsTermQ10 or AllowsTerm from AllowsTerm with inserted of `Q10` charge
  - D.3. AllowsTerm with inserted of `Q10` charge from AllowsTermQ5
  - D.4. AllowsTerm with inserted of `Q10` charge iff AllowsTermQ10 or AllowsTerm

## iv. References

There are no known references for the results in this file.

-/

namespace SuperSymmetry
namespace SU5

namespace ChargeSpectrum

variable {𝓩 : Type} [AddCommGroup 𝓩]

private theorem multiset_mem_sprod {α β : Type*} {s : Multiset α} {t : Multiset β}
    {p : α × β} : p ∈ s ×ˢ t ↔ p.1 ∈ s ∧ p.2 ∈ t :=
  Multiset.mem_product

private theorem multiset_mem_finset_product {α β : Type*} {s : Finset α} {t : Finset β}
    {p : α × β} : p ∈ (s.product t).val ↔ p.1 ∈ s ∧ p.2 ∈ t := by
  constructor
  · intro hp
    exact Finset.mem_product.mp (Finset.mem_val.mp hp)
  · intro hp
    exact Finset.mem_val.mpr (Finset.mem_product.mpr hp)

/-!

## A. Charge spectrums allowing potential terms

We first define the proposition `AllowsTerm`, which for a charge spectrum `x : ChargeSpectrum 𝓩`
and a potential term `T : PotentialTerm`, is true if the zero charge is in the set of
charges associated with that potential term.

That is, if there is some choice of representations present in the theory which will allow that
potential term via symmetry.

-/

/-- The charges of representations `x : Charges` allow a potential term `T : PotentialTerm`
if the zero charge is in the set of charges associated with that potential term. -/
def AllowsTerm (x : ChargeSpectrum 𝓩) (T : PotentialTerm) : Prop := 0 ∈ ofPotentialTerm x T

/-!

### A.1. Decidability of `AllowsTerm`

We define the decidability of `AllowsTerm` through `ofPotentialTerm'` rather than
`ofPotentialTerm` due to the speed of the former compared to the latter.

-/

lemma allowsTerm_iff_zero_mem_ofPotentialTerm' [DecidableEq 𝓩]
    {x : ChargeSpectrum 𝓩} {T : PotentialTerm} :
    x.AllowsTerm T ↔ 0 ∈ x.ofPotentialTerm' T := by
  rw [AllowsTerm]
  exact mem_ofPotentialTerm_iff_mem_ofPotentialTerm

instance [DecidableEq 𝓩] (x : ChargeSpectrum 𝓩) (T : PotentialTerm) : Decidable (x.AllowsTerm T) :=
  decidable_of_iff (0 ∈ x.ofPotentialTerm' T) allowsTerm_iff_zero_mem_ofPotentialTerm'.symm

/-!

### A.2. Monotonicity of `AllowsTerm`

The proposition `AllowsTerm` is monotone in its charge spectrum argument.
That is if a charge spectrum `y` is a subset of a charge spectrum `x`,
and `y` allows a potential term `T`, then `x` also allows that potential term `T`.

-/

lemma allowsTerm_mono {T : PotentialTerm} {y x : ChargeSpectrum 𝓩}
    (h : y ⊆ x) (hy : y.AllowsTerm T) : x.AllowsTerm T := ofPotentialTerm_mono h T hy

/-!

## B. Forms of charges which allow potential terms

We now define the function `allowsTermForm` which for each potential term `T`
and three charges `a`, `b`, and `c` returns a charge spectrum which allows the term `T`.

These charges are in a minimal form, in the sense that any charge spectrum allowing `T`
has a subset of this form.

-/

variable [DecidableEq 𝓩]

/-- A element of `Charges` from three integers `a b c : ℤ` for a given potential term `T`.
  Defined such that `allowsTermForm a b c T` always allows the potential term `T`,
  and if any over charge `x` allows `T` then it is due to a subset of the form
  `allowsTermForm a b c T`. -/
def allowsTermForm (a b c : 𝓩) : (T : PotentialTerm) → ChargeSpectrum 𝓩
  | .μ => ⟨some a, some a, ∅, ∅⟩
  | .β => ⟨none, some a, {a}, ∅⟩
  | .Λ => ⟨none, none, {a, b}, {- a - b}⟩
  | .W1 => ⟨none, none, {- a - b - c}, {a, b, c}⟩
  | .W2 => ⟨some (- a - b - c), none, ∅, {a, b, c}⟩
  | .W3 => ⟨none, some (- a), {b, - b - 2 • a}, ∅⟩
  | .W4 => ⟨some (- c - 2 • b), some (- b), {c}, ∅⟩
  | .K1 => ⟨none, none, {-a}, {b, - a - b}⟩
  | .K2 => ⟨some a, some b, ∅, {- a - b}⟩
  | .topYukawa => ⟨none, some (-a), ∅, {b, - a - b}⟩
  | .bottomYukawa => ⟨some a, none, {b}, {- a - b}⟩

/-!

### B.1. `allowsTermForm` allows the potential term

Any charge spectrum of the form `allowsTermForm a b c T` allows the potential term `T`.

-/

lemma allowsTermForm_allowsTerm {a b c : 𝓩} {T : PotentialTerm} :
    (allowsTermForm a b c T).AllowsTerm T := by
  rw [allowsTerm_iff_zero_mem_ofPotentialTerm']
  cases T <;> simp only [allowsTermForm, ofPotentialTerm']
  case μ => exact Multiset.mem_singleton.mpr (by abel)
  case β =>
    apply Multiset.mem_map.mpr
    exact ⟨a, by simp [Multiset.mem_ndinsert, Multiset.mem_singleton], by abel⟩
  case W4 =>
    apply Multiset.mem_map.mpr
    exact ⟨c, by simp [Multiset.mem_ndinsert, Multiset.mem_singleton], by abel⟩
  case K2 =>
    apply Multiset.mem_map.mpr
    exact ⟨-a - b, by simp [Multiset.mem_ndinsert, Multiset.mem_singleton], by abel⟩
  all_goals (apply Multiset.mem_map.mpr)
  case Λ =>
    refine ⟨(a, (b, -a - b)), Finset.mem_val.mpr ?_, ?_⟩
    · simp [Finset.mem_product, Finset.mem_insert, Finset.mem_singleton]
    · simp only [neg_one_zsmul]; abel
  case W1 =>
    refine ⟨(-a - b - c, (a, (b, c))), Finset.mem_val.mpr ?_, ?_⟩
    · simp [Finset.mem_product, Finset.mem_insert, Finset.mem_singleton]
    · simp only [neg_one_zsmul]; abel
  case W2 =>
    refine ⟨(a, (b, c)), Finset.mem_val.mpr ?_, ?_⟩
    · simp [Finset.mem_product, Finset.mem_insert, Finset.mem_singleton]
    · simp only [neg_one_zsmul]; abel
  case W3 =>
    refine ⟨(b, -b - 2 • a), Finset.mem_val.mpr ?_, ?_⟩
    · simp [Finset.mem_product, Finset.mem_insert, Finset.mem_singleton]
    · simp only [neg_one_zsmul]; abel
  case K1 =>
    refine ⟨(-a, (b, -a - b)), Finset.mem_val.mpr ?_, ?_⟩
    · simp [Finset.mem_product, Finset.mem_insert, Finset.mem_singleton]
    · simp only [neg_one_zsmul]; abel
  case topYukawa =>
    refine ⟨(b, -a - b), Finset.mem_val.mpr ?_, ?_⟩
    · simp [Finset.mem_product, Finset.mem_insert, Finset.mem_singleton]
    · simp only [neg_one_zsmul]; abel
  case bottomYukawa =>
    refine ⟨(b, -a - b), Finset.mem_val.mpr ?_, ?_⟩
    · simp [Finset.mem_product, Finset.mem_insert, Finset.mem_singleton]
    · simp only [neg_one_zsmul]; abel

lemma allowsTerm_of_eq_allowsTermForm {T : PotentialTerm}
    (x : ChargeSpectrum 𝓩) (h : ∃ a b c, x = allowsTermForm a b c T) :
    x.AllowsTerm T := by
  obtain ⟨a, b, c, rfl⟩ := h
  exact allowsTermForm_allowsTerm

/-!

### B.2. Subset relations for `allowsTermForm`

For any potential term `T` except for `W¹ᵢⱼₖₗ 10ⁱ 10ʲ 10ᵏ 5̄Mˡ` or `W²ᵢⱼₖ 10ⁱ 10ʲ 10ᵏ 5̄Hd`,
a charge spectrum `allowsTermForm a b c T` is a subset of another charge spectrum
`allowsTermForm a' b' c' T` if they are equal.

The reason this does not work for `W1` an `W2` is due to the presence of three
charges in the 10d representation.

-/

open PotentialTerm in
lemma allowsTermForm_eq_of_subset {a b c a' b' c' : 𝓩} {T : PotentialTerm}
    (h : allowsTermForm a b c T ⊆ allowsTermForm a' b' c' T) (hT : T ≠ W1 ∧ T ≠ W2) :
    allowsTermForm a b c T = allowsTermForm a' b' c' T := by
  cases T
  case' W1 | W2 => simp at hT
  all_goals
    rw [subset_def] at h
    simp [allowsTermForm] at h ⊢
  case' μ =>
    subst h
    rfl
  case' β =>
    subst h
    rfl
  case' K2 =>
    obtain ⟨rfl, rfl, h2⟩ := h
    simp
  case' W4 =>
    obtain ⟨h2, rfl, rfl⟩ := h
    simp
  case' bottomYukawa =>
    obtain ⟨rfl, rfl, h2⟩ := h
    simp
  case' Λ => obtain ⟨h2, h1⟩ := h
  case' K1 => obtain ⟨rfl, h2⟩ := h
  case' topYukawa => obtain ⟨rfl, h2⟩ := h
  case' W3 => obtain ⟨rfl, h2⟩ := h
  case' topYukawa | W3 | K1 | Λ =>
    rw [Finset.insert_subset_iff] at h2
    simp at h2
    obtain ⟨rfl | rfl, h1 | h2⟩ := h2
    all_goals simp_all [Finset.pair_comm]

/-!

### B.3. Card of `allowsTermForm`

The cardinality of the charge spectrum `allowsTermForm a b c T` is always
less than or equal to the degree of the potential term `T`.

-/

lemma allowsTermForm_card_le_degree {a b c : 𝓩} {T : PotentialTerm} :
    (allowsTermForm a b c T).card ≤ T.degree := by
  cases T
  all_goals
    simp [allowsTermForm, PotentialTerm.toFieldLabel, card, PotentialTerm.degree]
  case' Λ =>
    have h1 : Finset.card {a, b} ≤ 2 := Finset.card_le_two
    omega
  case' W3 =>
    have h1 : Finset.card {b, -b - 2 • a} ≤ 2 := Finset.card_le_two
    omega
  case' K1 =>
    have h1 : Finset.card {b, -a - b} ≤ 2 := Finset.card_le_two
    omega
  case' topYukawa =>
    have h1 : Finset.card {b, -a - b} ≤ 2 := Finset.card_le_two
    omega
  all_goals
    have h1 : Finset.card {a, b, c} ≤ 3 := Finset.card_le_three
    omega

/-!

### B.4. If `AllowsTerm` then subset equal to `allowsTermForm a b c T`

We now show one of the more important properties of `allowsTermForm`.
Namely that if a charge spectrum `x`
allows a potential term `T`, then there exists charges `a`, `b`, and `c` such that
`allowsTermForm a b c T ⊆ x`.

The proof of this result is rather long, relying on case-by-case analysis of each
of the potential terms of interest.

-/

set_option maxHeartbeats 6400000 in
lemma allowsTermForm_subset_allowsTerm_of_allowsTerm {T : PotentialTerm} {x : ChargeSpectrum 𝓩}
    (h : x.AllowsTerm T) :
    ∃ a b c, allowsTermForm a b c T ⊆ x ∧ (allowsTermForm a b c T).AllowsTerm T := by
  rw [allowsTerm_iff_zero_mem_ofPotentialTerm'] at h
  obtain ⟨qHd, qHu, Q5, Q10⟩ := x
  cases T
  case μ =>
    cases qHd <;> cases qHu
    · simp [ofPotentialTerm'] at h
    · simp [ofPotentialTerm'] at h
    · simp [ofPotentialTerm'] at h
    · rename_i qHd qHu
      simp only [ofPotentialTerm', Multiset.mem_singleton] at h
      have heq : qHd = qHu := sub_eq_zero.mp h.symm
      subst heq
      exact ⟨qHd, qHd, qHd, by simp [allowsTermForm, subset_def], allowsTermForm_allowsTerm⟩
  case β =>
    cases qHu
    · simp [ofPotentialTerm'] at h
    · rename_i qHu
      simp only [ofPotentialTerm', Multiset.mem_map] at h
      obtain ⟨a, ha, h0⟩ := h
      have ha_eq : a = qHu := ((neg_add_eq_zero (a := qHu)).mp h0).symm
      subst ha_eq
      exact ⟨a, a, a, by simp [allowsTermForm, subset_def, Finset.singleton_subset_iff,
        Finset.mem_val.mp ha], allowsTermForm_allowsTerm⟩
  case Λ =>
    simp only [ofPotentialTerm', Multiset.mem_map, multiset_mem_finset_product] at h
    obtain ⟨⟨a, ⟨b, c⟩⟩, ⟨ha, hbc⟩, h0⟩ := h
    have hb : b ∈ Q5 := (Finset.mem_product.mp hbc).1
    have hc : c ∈ Q10 := (Finset.mem_product.mp hbc).2
    use a, b, c
    constructor
    · simp [allowsTermForm, subset_def]
      have hc' : -a - b = c := by
        rw [← sub_eq_zero]
        abel_nf at h0 ⊢
        simpa [add_comm, add_left_comm, add_assoc] using congrArg Neg.neg h0
      have hc_mem : -a - b ∈ Q10 := hc'.symm ▸ hc
      simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, ha, hb, hc_mem]
    · exact allowsTermForm_allowsTerm
  case W1 =>
    simp only [ofPotentialTerm', Multiset.mem_map, multiset_mem_finset_product] at h
    obtain ⟨⟨q5, ⟨a, ⟨b, c⟩⟩⟩, ⟨hq5, habc⟩, h0⟩ := h
    have ha : a ∈ Q10 := (Finset.mem_product.mp habc).1
    have hbc : (b, c) ∈ Q10.product Q10 := (Finset.mem_product.mp habc).2
    have hb : b ∈ Q10 := (Finset.mem_product.mp hbc).1
    have hc : c ∈ Q10 := (Finset.mem_product.mp hbc).2
    use a, b, c
    constructor
    · simp [allowsTermForm, subset_def]
      have hq5' : -a - b - c = q5 := by
        rw [← sub_eq_zero]
        abel_nf at h0 ⊢
        simpa [add_comm, add_left_comm, add_assoc] using congrArg Neg.neg h0
      have hq5_mem : -a - b - c ∈ Q5 := hq5'.symm ▸ hq5
      simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, hq5_mem, ha, hb, hc]
    · exact allowsTermForm_allowsTerm
  case W2 =>
    cases qHd
    · simp [ofPotentialTerm'] at h
    · rename_i qHd
      simp only [ofPotentialTerm', Multiset.mem_map, multiset_mem_finset_product] at h
      obtain ⟨⟨a, ⟨b, c⟩⟩, ⟨ha, hbc⟩, h0⟩ := h
      have hb : b ∈ Q10 := (Finset.mem_product.mp hbc).1
      have hc : c ∈ Q10 := (Finset.mem_product.mp hbc).2
      use a, b, c
      constructor
      · simp [allowsTermForm, subset_def]
        have hqHd : -a - b - c = qHd := by
          rw [← sub_eq_zero]
          abel_nf at h0 ⊢
          simpa [add_comm, add_left_comm, add_assoc] using congrArg Neg.neg h0
        simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, hqHd, ha, hb, hc]
      · exact allowsTermForm_allowsTerm
  case W3 =>
    cases qHu
    · simp [ofPotentialTerm'] at h
    · rename_i qHu
      simp only [ofPotentialTerm', Multiset.mem_map, multiset_mem_finset_product] at h
      obtain ⟨⟨u, v⟩, ⟨hu, hv⟩, h0⟩ := h
      use -qHu, u, u
      constructor
      · simp [allowsTermForm, subset_def]
        have hv' : -u + 2 • qHu = v := by
          rw [← sub_eq_zero]
          abel_nf at h0 ⊢
          simpa [add_comm, add_left_comm, add_assoc] using congrArg Neg.neg h0
        have hv_mem : -u + 2 • qHu ∈ Q5 := hv'.symm ▸ hv
        simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, hu, hv_mem]
      · exact allowsTermForm_allowsTerm
  case W4 =>
    cases qHd <;> cases qHu
    · simp [ofPotentialTerm'] at h
    · simp [ofPotentialTerm'] at h
    · simp [ofPotentialTerm'] at h
    · rename_i qHd qHu
      simp only [ofPotentialTerm', Multiset.mem_map] at h
      obtain ⟨a, ha, h0⟩ := h
      use a, -qHu, a
      constructor
      · simp [allowsTermForm, subset_def]
        have hqHd : -a + 2 • qHu = qHd := by
          rw [← sub_eq_zero]
          abel_nf at h0 ⊢
          simpa [add_comm, add_left_comm, add_assoc] using congrArg Neg.neg h0
        exact ⟨hqHd, by simpa using ha⟩
      · exact allowsTermForm_allowsTerm
  case K1 =>
    simp only [ofPotentialTerm', Multiset.mem_map, multiset_mem_finset_product] at h
    obtain ⟨⟨q5, ⟨a, b⟩⟩, ⟨hq5, hab⟩, h0⟩ := h
    have ha : a ∈ Q10 := (Finset.mem_product.mp hab).1
    have hb : b ∈ Q10 := (Finset.mem_product.mp hab).2
    use -q5, a, b
    constructor
    · simp [allowsTermForm, subset_def]
      have hb' : q5 - a = b := by
        rw [← sub_eq_zero]
        abel_nf at h0 ⊢
        simpa [add_comm, add_left_comm, add_assoc] using congrArg Neg.neg h0
      have hb_mem : q5 - a ∈ Q10 := hb'.symm ▸ hb
      simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, hq5, ha, hb_mem]
    · exact allowsTermForm_allowsTerm
  case K2 =>
    cases qHd <;> cases qHu
    · simp [ofPotentialTerm'] at h
    · simp [ofPotentialTerm'] at h
    · simp [ofPotentialTerm'] at h
    · rename_i qHd qHu
      simp only [ofPotentialTerm', Multiset.mem_map] at h
      obtain ⟨a, ha, h0⟩ := h
      use qHd, qHu, a
      constructor
      · simp [allowsTermForm, subset_def]
        have ha' : -qHd - qHu = a := by
          rw [← sub_eq_zero]
          abel_nf at h0 ⊢
          simpa [add_comm, add_left_comm, add_assoc] using congrArg Neg.neg h0
        have ha_mem : -qHd - qHu ∈ Q10 := ha'.symm ▸ Finset.mem_val.mp ha
        simpa [allowsTermForm, subset_def, ha_mem]
      · exact allowsTermForm_allowsTerm
  case topYukawa =>
    cases qHu
    · simp [ofPotentialTerm'] at h
    · rename_i qHu
      simp only [ofPotentialTerm', Multiset.mem_map, multiset_mem_finset_product] at h
      obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, h0⟩ := h
      use -qHu, a, b
      constructor
      · simp [allowsTermForm, subset_def]
        have hb' : qHu - a = b := by
          rw [← sub_eq_zero]
          abel_nf at h0 ⊢
          simpa [add_comm, add_left_comm, add_assoc] using congrArg Neg.neg h0
        have hb_mem : qHu - a ∈ Q10 := hb'.symm ▸ hb
        simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, ha, hb_mem]
      · exact allowsTermForm_allowsTerm
  case bottomYukawa =>
    cases qHd
    · simp [ofPotentialTerm'] at h
    · rename_i qHd
      simp only [ofPotentialTerm', Multiset.mem_map, multiset_mem_finset_product] at h
      obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, h0⟩ := h
      use qHd, a, a
      constructor
      · simp [allowsTermForm, subset_def]
        have hb' : -qHd - a = b := by
          rw [← sub_eq_zero]
          abel_nf at h0 ⊢
          simpa [add_comm, add_left_comm, add_assoc] using congrArg Neg.neg h0
        exact ⟨ha, hb'.symm ▸ hb⟩
      · exact allowsTermForm_allowsTerm

/-!

### B.5. `AllowsTerm` if and only if subset equal to `allowsTermForm a b c T`

We now lift the previous result to show that a charge spectrum `x`
allows a potential term `T` if and only if there exists charges `a`, `b`, and `c` such that
`allowsTermForm a b c T ⊆ x`.

Given what has already been shown, this result is now trivial.

-/
lemma allowsTerm_iff_subset_allowsTermForm {T : PotentialTerm} {x : ChargeSpectrum 𝓩} :
    x.AllowsTerm T ↔ ∃ a b c, allowsTermForm a b c T ⊆ x := by
  constructor
  · intro h
    obtain ⟨a, b, c, h1, h2⟩ := allowsTermForm_subset_allowsTerm_of_allowsTerm h
    use a, b, c
  · intro h
    obtain ⟨a, b, c, h1⟩ := h
    apply allowsTerm_mono h1 allowsTermForm_allowsTerm

/-!

### B.6. Cardinality of subset allowing potential term

We show that if a charge spectrum `x` allows a potential term `T`,
then there exists a subset of `x` which allows `T` and whose cardinality is less than or equal
to the degree of `T`.

This follows from the fact that `allowsTermForm a b c T` always has cardinality
less than or equal to the degree of `T`.

-/

lemma subset_card_le_degree_allowsTerm_of_allowsTerm {T : PotentialTerm} {x : ChargeSpectrum 𝓩}
    (h : x.AllowsTerm T) : ∃ y ∈ x.powerset, y.card ≤ T.degree ∧ y.AllowsTerm T := by
  obtain ⟨a, b, c, h1, h2⟩ := allowsTermForm_subset_allowsTerm_of_allowsTerm h
  use allowsTermForm a b c T
  simp_all
  exact allowsTermForm_card_le_degree

/-!

## C. Allowing a potential term by insertion of a `Q5` charge

We now study what happens when we add a charge `q5` to the `Q5` charges of a charge spectrum `x`.
We define the proposition `AllowsTermQ5 x q5 T` which is true if adding the charge `q5`
to the `Q5` charges of `x` allows the potential term `T` due to the addition of that charge.

We prove a number of properties of this proposition, including its relation
to `AllowsTerm` and its decidability.

-/

/-- The proposition for which says, given a charge `x` adding a charge `q5` permits the
  existence of a potential term `T` due to the addition of that charge. -/
def AllowsTermQ5 [DecidableEq 𝓩] (x : ChargeSpectrum 𝓩) (q5 : 𝓩) (T : PotentialTerm) : Prop :=
  match T with
  | .μ => false
  | .β =>
    match x with
    | ⟨_, some qHu, _, _⟩ => q5 = qHu
    | _ => false
  | .Λ => (0 : 𝓩) ∈ ((insert q5 x.Q5).product x.Q10).val.map (fun (q1, q2) => (q1 + q5 + q2))
  | .W4 =>
    match x with
    | ⟨some qHd, some qHu, _, _⟩ => q5 + qHd - qHu - qHu = 0
    | _ => false
  | .K1 => (0 : 𝓩) ∈ (x.Q10.product x.Q10).val.map (fun (y, z) => -q5 + y + z)
  | .W1 => (0 : 𝓩) ∈ (x.Q10.product (x.Q10.product x.Q10)).val.map
    (fun (q1, q2, q3) => q5 + q1 + q2 + q3)
  | .W2 => false
  | .bottomYukawa =>
    match x with
    | ⟨none, _, _, _⟩ => false
    | ⟨some qHd, _, _, _⟩ => (0 : 𝓩) ∈ x.Q10.val.map (fun y => y + q5 + qHd)
  | .topYukawa => false
  | .K2 => false
  | .W3 =>
    match x with
    | ⟨_, some qHu, _, _⟩ =>
      (0 : 𝓩) ∈ (insert q5 x.Q5).val.map (fun y => y + q5 - qHu - qHu)
    | _ => false

/-!

### C.1. Decidability of `AllowsTermQ5`

We show that if the type `𝓩` has decidable equality, then the proposition
`AllowsTermQ5 x q5 T` is decidable for any charge spectrum `x`, charge `q5`, and
potential term `T`.

-/
instance [DecidableEq 𝓩] (x : ChargeSpectrum 𝓩) (q5 : 𝓩) (T : PotentialTerm) :
    Decidable (AllowsTermQ5 x q5 T) :=
  match T with
  | .μ => isFalse fun h => by simp [AllowsTermQ5] at h
  | .β =>
    match x with
    | ⟨_, some qHu, _, _⟩ => decidable_of_iff (q5 = qHu) (by simp [AllowsTermQ5])
    | ⟨_, none, _, _⟩ => isFalse fun h => by simp [AllowsTermQ5] at h
  | .Λ =>
    decidable_of_iff ((0 : 𝓩) ∈ ((insert q5 x.Q5).product x.Q10).val.map
      (fun (q1, q2) => (q1 + q5 + q2))) (by simp [AllowsTermQ5])
  | .W4 =>
    match x with
    | ⟨some qHd, some qHu, _, _⟩ => decidable_of_iff (q5 + qHd - qHu - qHu = 0)
      (by simp [AllowsTermQ5])
    | ⟨some qHd, none, _, _⟩ => isFalse fun h => by simp [AllowsTermQ5] at h
    | ⟨none, _, _, _⟩ => isFalse fun h => by simp [AllowsTermQ5] at h
  | .K1 =>
    decidable_of_iff ((0 : 𝓩) ∈ (x.Q10.product x.Q10).val.map (fun (y, z) => -q5 + y + z))
      (by simp [AllowsTermQ5])
  | .W1 =>
    decidable_of_iff ((0 : 𝓩) ∈ (x.Q10.product (x.Q10.product x.Q10)).val.map
    (fun (q1, q2, q3) => q5 + q1 + q2 + q3)) (by rfl)
  | .W2 => isFalse fun h => by simp [AllowsTermQ5] at h
  | .bottomYukawa =>
    match x with
    | ⟨none, _, _, _⟩ => isFalse fun h => by simp [AllowsTermQ5] at h
    | ⟨some qHd, _, _, Q10⟩ => decidable_of_iff ((0 : 𝓩) ∈ Q10.val.map (fun y => y + q5 + qHd))
      (by simp [AllowsTermQ5])
  | .topYukawa => isFalse fun h => by simp [AllowsTermQ5] at h
  | .K2 => isFalse fun h => by simp [AllowsTermQ5] at h
  | .W3 =>
    match x with
    | ⟨_, some qHu, Q5, _⟩ => decidable_of_iff
      ((0 : 𝓩) ∈ (insert q5 Q5).val.map (fun y => y + q5 - qHu - qHu))
      (by simp [AllowsTermQ5])
    | ⟨_, none, _, _⟩ => isFalse fun h => by simp [AllowsTermQ5] at h

/-!

### C.2. AllowsTermQ5 or AllowsTerm from AllowsTerm with inserted of `Q5` charge

We show that if a charge spectrum `x` with an inserted charge `q5`
allows a potential term `T`, then either the charge spectrum `x`
allows that potential term `T` *due to* the addition of that charge,
or the charge spectrum `x` already allows that potential term `T`.

-/

set_option maxHeartbeats 6400000 in
lemma allowsTermQ5_or_allowsTerm_of_allowsTerm_insertQ5 {qHd qHu : Option 𝓩}
    {Q5 Q10: Finset 𝓩} {q5 : 𝓩} (T : PotentialTerm)
    (h : AllowsTerm ⟨qHd, qHu, insert q5 Q5, Q10⟩ T) :
    AllowsTermQ5 ⟨qHd, qHu, Q5, Q10⟩ q5 T ∨
    AllowsTerm ⟨qHd, qHu, Q5, Q10⟩ T := by
  rw [allowsTerm_iff_zero_mem_ofPotentialTerm'] at h ⊢
  cases T <;> cases qHd <;> cases qHu <;>
    simp_all [AllowsTermQ5, ofPotentialTerm', Finset.mem_insert, Multiset.mem_map,
      multiset_mem_finset_product, Multiset.mem_ndinsert,
      neg_add_eq_zero, add_neg_eq_zero, eq_comm] <;>
    aesop (config := { maxRuleApplications := 600 })
      (add norm simp [add_comm, add_left_comm, add_assoc, sub_eq_add_neg,
        neg_add_eq_zero, add_neg_eq_zero, eq_comm])

/-!

### C.3. AllowsTerm with inserted of `Q5` charge from AllowsTermQ5

We show that if a charge spectrum `x` allows a potential term `T`
*due to* the addition of a charge `q5`, then the charge spectrum `x` with that charge inserted
allows that potential term `T`.

-/
set_option maxHeartbeats 25600000 in
lemma allowsTerm_insertQ5_of_allowsTermQ5 {qHd qHu : Option 𝓩}
    {Q5 Q10: Finset 𝓩} {q5 : 𝓩} (T : PotentialTerm)
    (h : AllowsTermQ5 ⟨qHd, qHu, Q5, Q10⟩ q5 T) :
    AllowsTerm ⟨qHd, qHu, insert q5 Q5, Q10⟩ T := by
  rw [allowsTerm_iff_zero_mem_ofPotentialTerm']
  cases T
  case μ =>
    simp [AllowsTermQ5] at h
  case β =>
    cases qHu with
    | none =>
      simp [AllowsTermQ5] at h
    | some qHu =>
      simp only [AllowsTermQ5] at h
      simp only [ofPotentialTerm', Multiset.mem_map]
      refine ⟨q5, Finset.mem_val.mpr (Finset.mem_insert_self q5 Q5), ?_⟩
      rw [h]
      abel
  case Λ =>
    simp only [AllowsTermQ5, ofPotentialTerm', Multiset.mem_map,
      multiset_mem_finset_product] at h ⊢
    obtain ⟨⟨q1, q2⟩, ⟨hq1, hq2⟩, h0⟩ := h
    refine ⟨(q1, (q5, q2)), ?_, ?_⟩
    · exact ⟨hq1, Finset.mem_product.mpr ⟨Finset.mem_insert_self q5 Q5, hq2⟩⟩
    · abel_nf at h0 ⊢
      exact h0
  case W4 =>
    cases qHd with
    | none =>
      simp [AllowsTermQ5] at h
    | some qHd =>
      cases qHu with
      | none =>
        simp [AllowsTermQ5] at h
      | some qHu =>
        simp only [AllowsTermQ5] at h
        simp only [ofPotentialTerm', Multiset.mem_map]
        refine ⟨q5, Finset.mem_val.mpr (Finset.mem_insert_self q5 Q5), ?_⟩
        abel_nf at h ⊢
        exact h
  case K1 =>
    simp only [AllowsTermQ5, ofPotentialTerm', Multiset.mem_map,
      multiset_mem_finset_product] at h ⊢
    obtain ⟨⟨q1, q2⟩, ⟨hq1, hq2⟩, h0⟩ := h
    refine ⟨(q5, (q1, q2)), ?_, ?_⟩
    · exact ⟨Finset.mem_insert_self q5 Q5, Finset.mem_product.mpr ⟨hq1, hq2⟩⟩
    · abel_nf at h0 ⊢
      exact h0
  case W1 =>
    simp only [AllowsTermQ5, ofPotentialTerm', Multiset.mem_map,
      multiset_mem_finset_product] at h ⊢
    obtain ⟨⟨q1, ⟨q2, q3⟩⟩, ⟨hq1, h23⟩, h0⟩ := h
    have hq2 : q2 ∈ Q10 := (Finset.mem_product.mp h23).1
    have hq3 : q3 ∈ Q10 := (Finset.mem_product.mp h23).2
    refine ⟨(q5, (q1, (q2, q3))), ?_, ?_⟩
    · exact ⟨Finset.mem_insert_self q5 Q5, Finset.mem_product.mpr
        ⟨hq1, Finset.mem_product.mpr ⟨hq2, hq3⟩⟩⟩
    · abel_nf at h0 ⊢
      exact h0
  case W2 =>
    simp [AllowsTermQ5] at h
  case bottomYukawa =>
    cases qHd with
    | none =>
      simp [AllowsTermQ5] at h
    | some qHd =>
      simp only [AllowsTermQ5, ofPotentialTerm', Multiset.mem_map,
        multiset_mem_finset_product] at h ⊢
      obtain ⟨q, hq, h0⟩ := h
      refine ⟨(q5, q), ?_, ?_⟩
      · exact ⟨Finset.mem_insert_self q5 Q5, Finset.mem_val.mp hq⟩
      · abel_nf at h0 ⊢
        exact h0
  case topYukawa =>
    simp [AllowsTermQ5] at h
  case K2 =>
    simp [AllowsTermQ5] at h
  case W3 =>
    cases qHu with
    | none =>
      simp [AllowsTermQ5] at h
    | some qHu =>
      simp only [AllowsTermQ5, ofPotentialTerm', Multiset.mem_map,
        multiset_mem_finset_product] at h ⊢
      obtain ⟨q, hq, h0⟩ := h
      refine ⟨(q, q5), ?_, ?_⟩
      · exact ⟨Finset.mem_val.mp hq, Finset.mem_insert_self q5 Q5⟩
      · abel_nf at h0 ⊢
        exact h0

/-!

### C.4. AllowsTerm with inserted of `Q5` charge iff AllowsTermQ5 or AllowsTerm

We show that the charge spectrum `x` with that charge inserted
allows that potential term `T` if and only if either the charge spectrum `x`
allows that potential term `T` *due to* the addition of that charge,
or the charge spectrum `x` already allows that potential term `T`.

-/

lemma allowsTerm_insertQ5_iff_allowsTermQ5 {qHd qHu : Option 𝓩}
    {Q5 Q10: Finset 𝓩} {q5 : 𝓩} (T : PotentialTerm) :
    AllowsTerm ⟨qHd, qHu, insert q5 Q5, Q10⟩ T ↔
    AllowsTermQ5 ⟨qHd, qHu, Q5, Q10⟩ q5 T ∨
    AllowsTerm ⟨qHd, qHu, Q5, Q10⟩ T := by
  constructor
  · exact allowsTermQ5_or_allowsTerm_of_allowsTerm_insertQ5 T
  · intro h
    rcases h with h | h
    · exact allowsTerm_insertQ5_of_allowsTermQ5 T h
    · apply allowsTerm_mono _ h
      simp [subset_def]

/-!

## D. Allowing a potential term by insertion of a `Q10` charge

We now replicate the previous section, but for the insertion of a `Q10` charge, rather
than a `Q5` charge.

We study what happens when we add a charge `q10` to the `Q10` charges of a charge spectrum `x`.
We define the proposition `AllowsTermQ10 x q10 T` which is true if adding the charge `q10`
to the `Q10` charges of `x` allows the potential term `T` due to the addition of that charge.

We prove a number of properties of this proposition, including its relation
to `AllowsTerm` and its decidability.

-/

/-- The proposition for which says, given a charge `x` adding a charge `q5` permits the
  existence of a potential term `T` due to the addition of that charge. -/
def AllowsTermQ10 [DecidableEq 𝓩] (x : ChargeSpectrum 𝓩) (q10 : 𝓩) (T : PotentialTerm) : Prop :=
  match T with
  | .μ => false
  | .β => false
  | .Λ => (0 : 𝓩) ∈ (x.Q5.product x.Q5).val.map (fun (y, z) => y + z + q10)
  | .W4 => false
  | .K1 => (0 : 𝓩) ∈ (x.Q5.product (insert q10 x.Q10)).val.map (fun (q5, q2) => -q5 + q2+ q10)
  | .W1 => (0 : 𝓩) ∈ (x.Q5.product ((insert q10 x.Q10).product (insert q10 x.Q10))).val.map
    (fun (q5, q2, q3) => q5 + q2 + q3 + q10)
  | .W2 =>
    match x with
    | ⟨some qHd, _, _, _⟩ => (0 : 𝓩) ∈
      (((insert q10 x.Q10).product (insert q10 x.Q10))).val.map
      (fun (q2, q3) => qHd + q2 + q3 + q10)
    | _ => false
  | .bottomYukawa =>
    match x with
    | ⟨none, _, _, _⟩ => false
    | ⟨some qHd, _, _, _⟩ => (0 : 𝓩) ∈ x.Q5.val.map (fun y => q10 + y + qHd)
  | .topYukawa =>
    match x with
    | ⟨_, some qHu, _, _⟩ => (0 : 𝓩) ∈ (insert q10 x.Q10).val.map (fun y => q10 + y - qHu)
    | _ => false
  | .K2 =>
    match x with
    | ⟨some qHd, some qHu, _, _⟩ => qHd + qHu + q10 = 0
    | _ => false
  | .W3 => false

/-!

### D.1. Decidability of `AllowsTermQ5`

We show that if the type `𝓩` has decidable equality, then the proposition
`AllowsTermQ10 x q10 T` is decidable for any charge spectrum `x`, charge `q10`, and
potential term `T`.

-/

instance [DecidableEq 𝓩] (x : ChargeSpectrum 𝓩) (q10 : 𝓩) (T : PotentialTerm) :
    Decidable (AllowsTermQ10 x q10 T) :=
  match T with
  | .μ => isFalse fun h => by simp [AllowsTermQ10] at h
  | .β => isFalse fun h => by simp [AllowsTermQ10] at h
  | .Λ =>
    decidable_of_iff ((0 : 𝓩) ∈ (x.Q5.product x.Q5).val.map (fun (y, z) => y + z + q10))
      (by simp [AllowsTermQ10])
  | .W4 => isFalse fun h => by simp [AllowsTermQ10] at h
  | .K1 =>
    decidable_of_iff ((0 : 𝓩) ∈
      (x.Q5.product (insert q10 x.Q10)).val.map (fun (q5, q2) => -q5 + q2 + q10))
      (by simp [AllowsTermQ10])
  | .W1 =>
    decidable_of_iff ((0 : 𝓩) ∈
    (x.Q5.product ((insert q10 x.Q10).product (insert q10 x.Q10))).val.map
    (fun (q5, q2, q3) => q5 + q2 + q3 + q10)) (by rfl)
  | .W2 =>
    match x with
    | ⟨some qHd, _, _, Q10⟩ => decidable_of_iff ((0 : 𝓩) ∈
      (((insert q10 Q10).product (insert q10 Q10))).val.map
      (fun (q2, q3) => qHd + q2 + q3 + q10)) (by simp [AllowsTermQ10])
    | ⟨none, _, _, _⟩ => isFalse fun h => by simp [AllowsTermQ10] at h
  | .bottomYukawa =>
    match x with
    | ⟨none, _, _, _⟩ => isFalse fun h => by simp [AllowsTermQ10] at h
    | ⟨some qHd, _, Q5, _⟩ => decidable_of_iff ((0 : 𝓩) ∈ Q5.val.map (fun y => q10 + y + qHd))
      (by simp [AllowsTermQ10])
  | .topYukawa =>
    match x with
    | ⟨_, some qHu, _, Q10⟩ => decidable_of_iff
      ((0 : 𝓩) ∈ (insert q10 Q10).val.map (fun y => q10 + y - qHu))
      (by simp [AllowsTermQ10])
    | ⟨_, none, _, _⟩ => isFalse fun h => by simp [AllowsTermQ10] at h
  | .K2 =>
    match x with
    | ⟨some qHd, some qHu, _, _⟩ => decidable_of_iff (qHd + qHu + q10 = 0) (by simp [AllowsTermQ10])
    | ⟨some qHd, none, _, _⟩ => isFalse fun h => by simp [AllowsTermQ10] at h
    | ⟨none, _, _, _⟩ => isFalse fun h => by simp [AllowsTermQ10] at h
  | .W3 => isFalse fun h => by simp [AllowsTermQ10] at h

/-!

### D.2. AllowsTermQ10 or AllowsTerm from AllowsTerm with inserted of `Q10` charge

We show that if a charge spectrum `x` with an inserted charge `q10`
allows a potential term `T`, then either the charge spectrum `x`
allows that potential term `T` *due to* the addition of that charge,
or the charge spectrum `x` already allows that potential term `T`.

-/

set_option maxHeartbeats 25600000 in
lemma allowsTermQ10_or_allowsTerm_of_allowsTerm_insertQ10 {qHd qHu : Option 𝓩}
    {Q5 Q10: Finset 𝓩} {q10 : 𝓩} (T : PotentialTerm)
    (h : AllowsTerm ⟨qHd, qHu, Q5, insert q10 Q10⟩ T) :
    AllowsTermQ10 ⟨qHd, qHu, Q5, Q10⟩ q10 T ∨
    AllowsTerm ⟨qHd, qHu, Q5, Q10⟩ T := by
  rw [allowsTerm_iff_zero_mem_ofPotentialTerm'] at h ⊢
  cases T
  case μ =>
    right
    simpa [ofPotentialTerm'] using h
  case β =>
    right
    simpa [ofPotentialTerm'] using h
  case Λ =>
    simp only [AllowsTermQ10, ofPotentialTerm', Multiset.mem_map,
      multiset_mem_finset_product] at h ⊢
    obtain ⟨⟨q5a, ⟨q5b, q⟩⟩, ⟨hq5a, hbq⟩, h0⟩ := h
    have hq5b : q5b ∈ Q5 := (Finset.mem_product.mp hbq).1
    have hq : q ∈ insert q10 Q10 := (Finset.mem_product.mp hbq).2
    rcases Finset.mem_insert.mp hq with rfl | hq
    · left
      refine ⟨(q5a, q5b), ⟨hq5a, hq5b⟩, ?_⟩
      abel_nf at h0 ⊢
      exact h0
    · right
      refine ⟨(q5a, (q5b, q)), ?_, h0⟩
      exact ⟨hq5a, Finset.mem_product.mpr ⟨hq5b, hq⟩⟩
  case W4 =>
    right
    simpa [ofPotentialTerm'] using h
  case K1 =>
    simp only [AllowsTermQ10, ofPotentialTerm', Multiset.mem_map,
      multiset_mem_finset_product] at h ⊢
    obtain ⟨⟨q5, ⟨q2, q3⟩⟩, ⟨hq5, h23⟩, h0⟩ := h
    have hq2i : q2 ∈ insert q10 Q10 := (Finset.mem_product.mp h23).1
    have hq3i : q3 ∈ insert q10 Q10 := (Finset.mem_product.mp h23).2
    rcases Finset.mem_insert.mp hq2i with rfl | hq2
    · left
      refine ⟨(q5, q3), ⟨hq5, hq3i⟩, ?_⟩
      abel_nf at h0 ⊢
      exact h0
    · rcases Finset.mem_insert.mp hq3i with rfl | hq3
      · left
        refine ⟨(q5, q2), ?_, ?_⟩
        · exact ⟨hq5, Finset.mem_insert.mpr (Or.inr hq2)⟩
        · abel_nf at h0 ⊢
          exact h0
      · right
        refine ⟨(q5, (q2, q3)), ?_, h0⟩
        exact ⟨hq5, Finset.mem_product.mpr ⟨hq2, hq3⟩⟩
  case W1 =>
    simp only [AllowsTermQ10, ofPotentialTerm', Multiset.mem_map,
      multiset_mem_finset_product] at h ⊢
    obtain ⟨⟨q5, ⟨q2, ⟨q3, q4⟩⟩⟩, ⟨hq5, h234⟩, h0⟩ := h
    have hq2i : q2 ∈ insert q10 Q10 := (Finset.mem_product.mp h234).1
    have hq34 : (q3, q4) ∈ (insert q10 Q10).product (insert q10 Q10) :=
      (Finset.mem_product.mp h234).2
    have hq3i : q3 ∈ insert q10 Q10 := (Finset.mem_product.mp hq34).1
    have hq4i : q4 ∈ insert q10 Q10 := (Finset.mem_product.mp hq34).2
    rcases Finset.mem_insert.mp hq2i with rfl | hq2
    · left
      refine ⟨(q5, (q3, q4)), ?_, ?_⟩
      · exact ⟨hq5, Finset.mem_product.mpr ⟨hq3i, hq4i⟩⟩
      · abel_nf at h0 ⊢
        exact h0
    · rcases Finset.mem_insert.mp hq3i with rfl | hq3
      · left
        refine ⟨(q5, (q2, q4)), ?_, ?_⟩
        · exact ⟨hq5, Finset.mem_product.mpr ⟨Finset.mem_insert.mpr (Or.inr hq2), hq4i⟩⟩
        · abel_nf at h0 ⊢
          exact h0
      · rcases Finset.mem_insert.mp hq4i with rfl | hq4
        · left
          refine ⟨(q5, (q2, q3)), ?_, ?_⟩
          · exact ⟨hq5, Finset.mem_product.mpr
              ⟨Finset.mem_insert.mpr (Or.inr hq2), Finset.mem_insert.mpr (Or.inr hq3)⟩⟩
          · abel_nf at h0 ⊢
            exact h0
        · right
          refine ⟨(q5, (q2, (q3, q4))), ?_, h0⟩
          exact ⟨hq5, Finset.mem_product.mpr
            ⟨hq2, Finset.mem_product.mpr ⟨hq3, hq4⟩⟩⟩
  case W2 =>
    cases qHd
    · simp [ofPotentialTerm'] at h
    · rename_i qHd
      simp only [AllowsTermQ10, ofPotentialTerm', Multiset.mem_map,
        multiset_mem_finset_product] at h ⊢
      obtain ⟨⟨q2, ⟨q3, q4⟩⟩, ⟨hq2i, h34⟩, h0⟩ := h
      have hq3i : q3 ∈ insert q10 Q10 := (Finset.mem_product.mp h34).1
      have hq4i : q4 ∈ insert q10 Q10 := (Finset.mem_product.mp h34).2
      rcases Finset.mem_insert.mp hq2i with rfl | hq2
      · left
        refine ⟨(q3, q4), ⟨hq3i, hq4i⟩, ?_⟩
        abel_nf at h0 ⊢
        exact h0
      · rcases Finset.mem_insert.mp hq3i with rfl | hq3
        · left
          refine ⟨(q2, q4), ?_, ?_⟩
          · exact ⟨Finset.mem_insert.mpr (Or.inr hq2), hq4i⟩
          · abel_nf at h0 ⊢
            exact h0
        · rcases Finset.mem_insert.mp hq4i with rfl | hq4
          · left
            refine ⟨(q2, q3), ?_, ?_⟩
            · exact ⟨Finset.mem_insert.mpr (Or.inr hq2),
                Finset.mem_insert.mpr (Or.inr hq3)⟩
            · abel_nf at h0 ⊢
              exact h0
          · right
            refine ⟨(q2, (q3, q4)), ?_, h0⟩
            exact ⟨hq2, Finset.mem_product.mpr ⟨hq3, hq4⟩⟩
  case bottomYukawa =>
    cases qHd
    · simp [ofPotentialTerm'] at h
    · rename_i qHd
      simp only [AllowsTermQ10, ofPotentialTerm', Multiset.mem_map,
        multiset_mem_finset_product] at h ⊢
      obtain ⟨⟨q5, q⟩, ⟨hq5, hq⟩, h0⟩ := h
      rcases Finset.mem_insert.mp hq with rfl | hq
      · left
        refine ⟨q5, hq5, ?_⟩
        abel_nf at h0 ⊢
        exact h0
      · right
        exact ⟨(q5, q), ⟨hq5, hq⟩, h0⟩
  case topYukawa =>
    cases qHu
    · simp [ofPotentialTerm'] at h
    · rename_i qHu
      simp only [AllowsTermQ10, ofPotentialTerm', Multiset.mem_map,
        multiset_mem_finset_product] at h ⊢
      obtain ⟨⟨q2, q3⟩, ⟨hq2i, hq3i⟩, h0⟩ := h
      rcases Finset.mem_insert.mp hq2i with rfl | hq2
      · left
        refine ⟨q3, hq3i, ?_⟩
        abel_nf at h0 ⊢
        exact h0
      · rcases Finset.mem_insert.mp hq3i with rfl | hq3
        · left
          refine ⟨q2, Finset.mem_insert.mpr (Or.inr hq2), ?_⟩
          abel_nf at h0 ⊢
          exact h0
        · right
          exact ⟨(q2, q3), ⟨hq2, hq3⟩, h0⟩
  case K2 =>
    cases qHd
    · simp [ofPotentialTerm'] at h
    · cases qHu
      · simp [ofPotentialTerm'] at h
      · rename_i qHu qHd
        simp only [AllowsTermQ10, ofPotentialTerm', Multiset.mem_map] at h ⊢
        obtain ⟨q, hq, h0⟩ := h
        rcases Finset.mem_insert.mp (Finset.mem_val.mp hq) with rfl | hq
        · left
          exact h0
        · right
          exact ⟨q, Finset.mem_val.mpr hq, h0⟩
  case W3 =>
    right
    simpa [ofPotentialTerm'] using h

/-!

### D.3. AllowsTerm with inserted of `Q10` charge from AllowsTermQ5

We show that if a charge spectrum `x` allows a potential term `T`
*due to* the addition of a charge `q10`, then the charge spectrum `x` with that charge inserted
allows that potential term `T`.

-/

set_option maxHeartbeats 25600000 in
lemma allowsTerm_insertQ10_of_allowsTermQ10 {qHd qHu : Option 𝓩}
    {Q5 Q10: Finset 𝓩} {q10 : 𝓩} (T : PotentialTerm)
    (h : AllowsTermQ10 ⟨qHd, qHu, Q5, Q10⟩ q10 T) :
    AllowsTerm ⟨qHd, qHu, Q5, insert q10 Q10⟩ T := by
  rw [allowsTerm_iff_zero_mem_ofPotentialTerm']
  cases T
  case μ => simp [AllowsTermQ10] at h
  case β => simp [AllowsTermQ10] at h
  case Λ =>
    simp only [AllowsTermQ10, ofPotentialTerm', Multiset.mem_map,
      multiset_mem_finset_product] at h ⊢
    obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, h0⟩ := h
    refine ⟨(a, (b, q10)), ?_, ?_⟩
    · exact ⟨ha, Finset.mem_product.mpr ⟨hb, Finset.mem_insert_self q10 Q10⟩⟩
    · convert h0 using 1 <;> abel
  case W4 => simp [AllowsTermQ10] at h
  case K1 =>
    simp only [AllowsTermQ10, ofPotentialTerm', Multiset.mem_map,
      multiset_mem_finset_product] at h ⊢
    obtain ⟨⟨q5, q2⟩, ⟨hq5, hq2⟩, h0⟩ := h
    refine ⟨(q5, (q2, q10)), ?_, ?_⟩
    · exact ⟨hq5, Finset.mem_product.mpr ⟨hq2, Finset.mem_insert_self q10 Q10⟩⟩
    · convert h0 using 1 <;> abel
  case W1 =>
    simp only [AllowsTermQ10, ofPotentialTerm', Multiset.mem_map,
      multiset_mem_finset_product] at h ⊢
    obtain ⟨⟨q5, ⟨q2, q3⟩⟩, ⟨hq5, h23⟩, h0⟩ := h
    have hq2 : q2 ∈ insert q10 Q10 := (Finset.mem_product.mp h23).1
    have hq3 : q3 ∈ insert q10 Q10 := (Finset.mem_product.mp h23).2
    refine ⟨(q5, (q2, (q3, q10))), ?_, ?_⟩
    · exact ⟨hq5, Finset.mem_product.mpr ⟨hq2,
        Finset.mem_product.mpr ⟨hq3, Finset.mem_insert_self q10 Q10⟩⟩⟩
    · convert h0 using 1 <;> abel
  case W2 =>
    cases qHd
    · simp [AllowsTermQ10] at h
    · rename_i qHd
      simp only [AllowsTermQ10, ofPotentialTerm', Multiset.mem_map,
        multiset_mem_finset_product] at h ⊢
      obtain ⟨⟨q2, q3⟩, ⟨hq2, hq3⟩, h0⟩ := h
      refine ⟨(q2, (q3, q10)), ?_, ?_⟩
      · exact ⟨hq2, Finset.mem_product.mpr ⟨hq3, Finset.mem_insert_self q10 Q10⟩⟩
      · convert h0 using 1 <;> abel
  case bottomYukawa =>
    cases qHd
    · simp [AllowsTermQ10] at h
    · rename_i qHd
      simp only [AllowsTermQ10, ofPotentialTerm', Multiset.mem_map,
        multiset_mem_finset_product] at h ⊢
      obtain ⟨q5, hq5, h0⟩ := h
      refine ⟨(q5, q10), ?_, ?_⟩
      · exact ⟨hq5, Finset.mem_insert_self q10 Q10⟩
      · convert h0 using 1 <;> abel
  case topYukawa =>
    cases qHu
    · simp [AllowsTermQ10] at h
    · rename_i qHu
      simp only [AllowsTermQ10, ofPotentialTerm', Multiset.mem_map,
        multiset_mem_finset_product] at h ⊢
      obtain ⟨q2, hq2, h0⟩ := h
      refine ⟨(q10, q2), ?_, ?_⟩
      · exact ⟨Finset.mem_insert_self q10 Q10, hq2⟩
      · convert h0 using 1 <;> abel
  case K2 =>
    cases qHd <;> cases qHu
    · simp [AllowsTermQ10] at h
    · simp [AllowsTermQ10] at h
    · simp [AllowsTermQ10] at h
    · simp only [AllowsTermQ10, ofPotentialTerm', Multiset.mem_map] at h ⊢
      refine ⟨q10, ?_, ?_⟩
      · exact Finset.mem_val.mpr (Finset.mem_insert_self q10 Q10)
      · exact h
  case W3 => simp [AllowsTermQ10] at h

/-!

### D.4. AllowsTerm with inserted of `Q10` charge iff AllowsTermQ10 or AllowsTerm

We show that the charge spectrum `x` with that charge inserted
allows that potential term `T` if and only if either the charge spectrum `x`
allows that potential term `T` *due to* the addition of that charge,
or the charge spectrum `x` already allows that potential term `T`.

-/

lemma allowsTerm_insertQ10_iff_allowsTermQ10 {qHd qHu : Option 𝓩}
    {Q5 Q10: Finset 𝓩} {q10 : 𝓩} (T : PotentialTerm) :
    AllowsTerm ⟨qHd, qHu, Q5, insert q10 Q10⟩ T ↔
    AllowsTermQ10 ⟨qHd, qHu, Q5, Q10⟩ q10 T ∨
    AllowsTerm ⟨qHd, qHu, Q5, Q10⟩ T := by
  constructor
  · exact allowsTermQ10_or_allowsTerm_of_allowsTerm_insertQ10 T
  · intro h
    rcases h with h | h
    · exact allowsTerm_insertQ10_of_allowsTermQ10 T h
    · apply allowsTerm_mono _ h
      simp [subset_def]

end ChargeSpectrum

end SU5
end SuperSymmetry
