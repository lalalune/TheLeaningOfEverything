/-
Copyright (c) 2025 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Data.Real.CompleteField
import Mathlib.Data.Real.StarOrdered

set_option synthInstance.maxHeartbeats 200000
/-!

# Inner product space

In this module we define the type class `InnerProductSpace' 𝕜 E` which is a
generalization of `InnerProductSpace 𝕜 E`, as it does not require the condition `‖x‖^2 = ⟪x,x⟫`
but instead the condition `∃ (c > 0) (d > 0), c • ‖x‖^2 ≤ ⟪x,x⟫ ≤ d • ‖x‖^2`.
Instead `E` is equipped with a L₂ norm `‖x‖₂` which satisfies `‖x‖₂ = √⟪x,x⟫`.

This allows us to define the inner product space structure on product types `E × F` and
pi types `ι → E`, which would otherwise not be possible due to the use of max norm on these types.

We define the following maps:

- `InnerProductSpace 𝕜 E → InnerProductSpace' 𝕜 E` which sets `‖x‖₂ = ‖x‖`.
- `InnerProductSpace' 𝕜 E → InnerProductSpace 𝕜 (WithLp 2 E)` which uses the fact that the norm
  defined on `WithLp 2 E` is L₂ norm.

-/

/-- L₂ norm on `E`.

In particular, on product types `X×Y` and pi types `ι → X` this class provides L₂ norm unlike `‖·‖`.
-/
class Norm₂ (E : Type*) where
  norm₂ : E → ℝ

export Norm₂ (norm₂)

attribute [inherit_doc Norm₂] norm₂

@[inherit_doc Norm₂]
notation:max "‖" x "‖₂" => norm₂ x

open RCLike ComplexConjugate

/-- Effectively as `InnerProductSpace 𝕜 E` but it does not requires that `‖x‖^2 = ⟪x,x⟫`. It is
only required that they are equivalent `∃ (c > 0) (d > 0), c • ‖x‖^2 ≤ ⟪x,x⟫ ≤ d • ‖x‖^2`. The main
purpose of this class is to provide inner product space structure on product types `ExF` and
pi types `ι → E` without using `WithLp` gadget.

If you want to access L₂ norm use `‖x‖₂ := √⟪x,x⟫`.

This class induces `InnerProductSpace 𝕜 (WithLp 2 E)` which equips `‖·‖` on `X` with L₂ norm.
This is very useful when translating results from `InnerProductSpace` to `InnerProductSpace'`
together with `toL2 : E →L[𝕜] (WithLp 2 E)` and `fromL2 : (WithL2 2 E) →L[𝕜] E`.

In short we have these implications:
```
  InnerProductSpace 𝕜 E → InnerProductSpace' 𝕜 E
  InnerProductSpace' 𝕜 E → InnerProductSpace 𝕜 (WithLp 2 E)
```

The reason behind this type class is that with current mathlib design the requirement
`‖x‖^2 = ⟪x,x⟫` prevents us to give inner product space structure on product type `E×F` and pi
type `ι → E` as they are equipped with max norm. One has to work with `WithLp 2 (E×F)` and
`WithLp 2 (ι → E)`. This places quite a bit inconvenience on users in certain scenarios.
In particular, the main motivation behind this class is to make computations of `adjFDeriv` and
`gradient` easy.
-/
class InnerProductSpace' (𝕜 : Type*) (E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    extends Norm₂ E where
  /-- Core inner product properties. -/
  core : InnerProductSpace.Core 𝕜 E
  /-- The inner product induces the L₂ norm. -/
  norm₂_sq_eq_re_inner : ∀ x : E, ‖x‖₂ ^ 2 = re (core.inner x x)
  /-- Norm induced by inner product is topologically equivalent to the given norm on E. -/
  inner_top_equiv_norm : ∃ c d : ℝ,
    0 < c ∧ 0 < d ∧
    ∀ x : E, (c • ‖x‖^2 ≤ re (core.inner x x)) ∧ (re (core.inner x x) ≤ d • ‖x‖^2)

section BasicInstances

variable {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

instance [inst : InnerProductSpace' 𝕜 E] : InnerProductSpace.Core 𝕜 E := inst.core

instance [inst : InnerProductSpace' 𝕜 E] : Inner 𝕜 E := inst.core.toInner

instance {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [inst : InnerProductSpace 𝕜 E] :
    InnerProductSpace' 𝕜 E where
  norm₂ x := ‖x‖
  core := inst.toCore
  norm₂_sq_eq_re_inner := norm_sq_eq_re_inner
  inner_top_equiv_norm := ⟨1, 1, one_pos, one_pos, fun x => by
    constructor <;> simp only [one_smul] <;> linarith [norm_sq_eq_re_inner (𝕜 := 𝕜) x]⟩

end BasicInstances

section InnerProductSpace'

variable
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [hE : InnerProductSpace' 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [InnerProductSpace' 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [InnerProductSpace' 𝕜 G]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

local postfix:90 "†" => starRingEnd _

namespace InnerProductSpace'
/-!

## B. Deriving the inner product structure on `WithLp 2 E` from `InnerProductSpace' 𝕜 E`

-/

/-- Attach L₂ norm to `WithLp 2 E` -/
noncomputable
scoped instance toNormWithL2 : Norm (WithLp 2 E) where
  norm x := √ (RCLike.re ⟪WithLp.equiv 2 E x, WithLp.equiv 2 E x⟫)

/-- Attach inner product to `WithLp 2 E` -/
noncomputable
scoped instance toInnerWithL2 : Inner 𝕜 (WithLp 2 E) where
  inner x y := ⟪WithLp.equiv 2 E x, WithLp.equiv 2 E y⟫

/-- Attach normed group structure to `WithLp 2 E` with L₂ norm. -/
noncomputable
scoped instance toNormedAddCommGroupWitL2 : NormedAddCommGroup (WithLp 2 E) :=
  let core : InnerProductSpace.Core (𝕜:=𝕜) (F:=E) := by infer_instance
  {
  dist_self x := core.toNormedAddCommGroup.dist_self (WithLp.equiv 2 E x)
  dist_comm x y := core.toNormedAddCommGroup.dist_comm (WithLp.equiv 2 E x) (WithLp.equiv 2 E y)
  dist_triangle x y z := core.toNormedAddCommGroup.dist_triangle (WithLp.equiv 2 E x)
    (WithLp.equiv 2 E y) (WithLp.ofLp z)
  eq_of_dist_eq_zero {x y} := by
    intro h
    simpa [-WithLp.equiv_apply] using core.toNormedAddCommGroup.eq_of_dist_eq_zero
      (x:= WithLp.equiv 2 E x) (y:= WithLp.equiv 2 E y) h
  }

lemma norm_withLp2_eq_norm2 (x : WithLp 2 E) :
    ‖x‖ = |norm₂ (WithLp.equiv 2 E x)| := by
  trans √ (RCLike.re ⟪WithLp.equiv 2 E x, WithLp.equiv 2 E x⟫)
  · rfl
  have h1 := norm₂_sq_eq_re_inner (𝕜 := 𝕜) ((WithLp.equiv 2 E) x)
  rw [← h1]
  exact Real.sqrt_sq_eq_abs ‖(WithLp.equiv 2 E) x‖₂

/-- Attach normed space structure to `WithLp 2 E` with L₂ norm. -/
noncomputable
scoped instance toNormedSpaceWithL2 : NormedSpace 𝕜 (WithLp 2 E) where
  norm_smul_le := by
    let core : PreInnerProductSpace.Core (𝕜:=𝕜) (F:=E) := by infer_instance
    intro a x
    apply (InnerProductSpace.Core.toNormedSpace (c := core)).norm_smul_le

/-- Attach inner product space structure to `WithLp 2 E`. -/
noncomputable
instance toInnerProductSpaceWithL2 : InnerProductSpace 𝕜 (WithLp 2 E) where
  norm_sq_eq_re_inner := by intros; simp [norm, Real.sq_sqrt,hE.core.re_inner_nonneg]; rfl
  conj_inner_symm x y := hE.core.conj_inner_symm (WithLp.equiv 2 E x) (WithLp.equiv 2 E y)
  add_left x y z := hE.core.add_left _ _ _
  smul_left x y := hE.core.smul_left _ _

variable (𝕜) in
/-- Continuous linear map from `E` to `WithLp 2 E`.

This map is continuous because we require topological equivalence between `‖·‖` and `‖·‖₂`. -/
noncomputable
def toL2 : E →L[𝕜] WithLp 2 E where
  toFun := (WithLp.equiv 2 _).symm
  map_add' := by simp
  map_smul' := by simp
  cont := by
    apply IsBoundedLinearMap.continuous (𝕜:=𝕜)
    constructor
    · constructor <;> simp
    · obtain ⟨c,d,hc,hd,h⟩ := InnerProductSpace'.inner_top_equiv_norm (𝕜:=𝕜) (E:=E)
      use √d
      constructor
      · apply Real.sqrt_pos.2 hd
      · intro x
        have h := Real.sqrt_le_sqrt (h x).2
        simp [smul_eq_mul] at h
        exact h

variable (𝕜) in
/-- Continuous linear map from `WithLp 2 E` to `E`.

This map is continuous because we require topological equivalence between `‖·‖` and `‖·‖₂`.
-/
noncomputable
def fromL2 : WithLp 2 E →L[𝕜] E where
  toFun := (WithLp.equiv 2 _)
  map_add' := by simp
  map_smul' := by simp
  cont := by
    apply IsBoundedLinearMap.continuous (𝕜:=𝕜)
    constructor
    · constructor <;> simp
    · obtain ⟨c,d,hc,hd,h⟩ := InnerProductSpace'.inner_top_equiv_norm (𝕜:=𝕜) (E:=E)
      use (√c)⁻¹
      have hc : 0 < √c := Real.sqrt_pos.2 hc
      constructor
      · apply inv_pos.2 hc
      · intro x
        have h := Real.sqrt_le_sqrt (h ((WithLp.equiv 2 E) x)).1
        simp [smul_eq_mul] at h
        exact (le_inv_mul_iff₀' hc).2 (by simpa [mul_comm] using h)

lemma fromL2_inner_left (x : WithLp 2 E) (y : E) : ⟪fromL2 𝕜 x, y⟫ = ⟪x, toL2 𝕜 y⟫ := rfl

lemma ofLp_inner_left (x : E) (y : WithLp 2 E) : ⟪WithLp.ofLp y, x⟫ = ⟪y, WithLp.toLp 2 x⟫ := by
  exact fromL2_inner_left y x

lemma toL2_inner_left (x : E) (y : WithLp 2 E) : ⟪toL2 𝕜 x, y⟫ = ⟪x, fromL2 𝕜 y⟫ := rfl

lemma toLp_inner_left (x : WithLp 2 E) (y : E) : ⟪WithLp.toLp 2 y, x⟫ = ⟪y, WithLp.ofLp x⟫ := by
  exact toL2_inner_left y x

@[simp]
lemma toL2_fromL2 (x : WithLp 2 E) : toL2 𝕜 (fromL2 𝕜 x) = x := rfl
@[simp]
lemma fromL2_toL2 (x : E) : fromL2 𝕜 (toL2 𝕜 x) = x := rfl

variable (𝕜 E) in
/-- Continuous linear equivalence between `WithLp 2 E` and `E` under `InnerProductSpace' 𝕜 E`. -/
noncomputable
def equivL2 : (WithLp 2 E) ≃L[𝕜] E where
  toFun := fromL2 𝕜
  invFun := toL2 𝕜
  map_add' := (fromL2 𝕜).1.1.2
  map_smul' := (fromL2 𝕜).1.2
  left_inv := by intro _; rfl
  right_inv := by intro _; rfl
  continuous_toFun := (fromL2 𝕜).2
  continuous_invFun := (toL2 𝕜).2

instance [CompleteSpace E] : CompleteSpace (WithLp 2 E) := by
  have e := (equivL2 𝕜 E)
  have he := ContinuousLinearEquiv.isUniformEmbedding e
  apply (completeSpace_congr (α:=WithLp 2 E) (β:=E) (e:=e) he).2
  infer_instance

end InnerProductSpace'

open InnerProductSpace'

variable (𝕜) in

/-!

## C. Basic properties of the inner product

-/

lemma ext_inner_left' {x y : E} (h : ∀ v, ⟪v, x⟫ = ⟪v, y⟫) : x = y :=
  (WithLp.equiv 2 E).symm.injective <| ext_inner_left (E := WithLp 2 E) 𝕜 <| by
  simpa [← ofLp_inner_left] using fun v => h (WithLp.ofLp v)

variable (𝕜) in
lemma ext_inner_right' {x y : E} (h : ∀ v, ⟪x, v⟫ = ⟪y, v⟫) : x = y :=
  (WithLp.equiv 2 E).symm.injective <| ext_inner_right (E := WithLp 2 E) 𝕜 <| by
  simpa [← ofLp_inner_left] using fun v => h (WithLp.ofLp v)

@[simp]
lemma inner_conj_symm' (x y : E) : ⟪y, x⟫† = ⟪x, y⟫ :=
  inner_conj_symm (E:=WithLp 2 E) _ _

lemma inner_smul_left' (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪x, y⟫ :=
  inner_smul_left (E:=WithLp 2 E) _ _ r

lemma inner_smul_right' (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * ⟪x, y⟫ :=
  inner_smul_right (E:=WithLp 2 E) _ _ r

@[simp]
lemma inner_zero_left' (x : E) : ⟪0, x⟫ = 0 :=
  inner_zero_left (E:=WithLp 2 E) _

@[simp]
lemma inner_zero_right' (x : E) : ⟪x, 0⟫ = 0 :=
  inner_zero_right (E:=WithLp 2 E) _

lemma inner_add_left' (x y z : E) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ :=
  inner_add_left (E:=WithLp 2 E) _ _ _

lemma inner_add_right' (x y z : E) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫ :=
  inner_add_right (E:=WithLp 2 E) _ _ _

lemma inner_sub_left' (x y z : E) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ :=
  inner_sub_left (E:=WithLp 2 E) _ _ _

lemma inner_sub_right' (x y z : E) : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ :=
  inner_sub_right (E:=WithLp 2 E) _ _ _

@[simp]
lemma inner_neg_left' (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫ :=
  inner_neg_left (E:=WithLp 2 E) _ _

@[simp]
lemma inner_neg_right' (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫ :=
  inner_neg_right (E:=WithLp 2 E) _ _

@[simp]
lemma inner_self_eq_zero' {x : E} : ⟪x, x⟫ = 0 ↔ x = 0 := by
  constructor
  · intro h
    exact hE.core.definite x h
  · intro hx
    simp [hx]

@[simp]
lemma inner_sum'{ι : Type*} [Fintype ι] (x : E) (g : ι → E) :
    ⟪x, ∑ i, g i⟫ = ∑ i, ⟪x, g i⟫ := by
  have h1 := inner_sum (𝕜 := 𝕜) (E:=WithLp 2 E) (x := WithLp.toLp 2 x)
    (f := fun i => WithLp.toLp 2 (g i))
  change ⟪WithLp.toLp 2 x, WithLp.toLp 2 (∑ i, g i)⟫ =
    ∑ i, ⟪WithLp.toLp 2 x, WithLp.toLp 2 (g i)⟫
  rw [WithLp.toLp_sum]
  exact h1 Finset.univ

@[fun_prop]
lemma Continuous.inner' {α} [TopologicalSpace α] (f g : α → E)
    (hf : Continuous f) (hg : Continuous g) : Continuous (fun a => ⟪f a, g a⟫) :=
  have hf : Continuous (fun x => toL2 𝕜 (f x)) := by fun_prop
  have hg : Continuous (fun x => toL2 𝕜 (g x)) := by fun_prop
  Continuous.inner (𝕜:=𝕜) (E:=WithLp 2 E) hf hg

section Real

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [InnerProductSpace' ℝ F]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

lemma real_inner_self_nonneg' {x : F} : 0 ≤ re (⟪x, x⟫) :=
  real_inner_self_nonneg (F:=WithLp 2 F)

lemma real_inner_comm' (x y : F) : ⟪y, x⟫ = ⟪x, y⟫ :=
  real_inner_comm (F:=WithLp 2 F) _ _

@[fun_prop]
lemma ContDiffAt.inner' {f g : E → F} {x : E}
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) :
    ContDiffAt ℝ n (fun x => ⟪f x, g x⟫) x :=
  have hf : ContDiffAt ℝ n (fun x => toL2 ℝ (f x)) x := by fun_prop
  have hg : ContDiffAt ℝ n (fun x => toL2 ℝ (g x)) x := by fun_prop
  hf.inner ℝ hg

@[fun_prop]
lemma ContDiff.inner' {f g : E → F}
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (fun x => ⟪f x, g x⟫) :=
  have hf : ContDiff ℝ n (fun x => toL2 ℝ (f x)) := by fun_prop
  have hg : ContDiff ℝ n (fun x => toL2 ℝ (g x)) := by fun_prop
  hf.inner ℝ hg

end Real

end InnerProductSpace'

section Constructions

variable
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [InnerProductSpace' 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [InnerProductSpace' 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [InnerProductSpace' 𝕜 G]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- Inner product on product types `E×F` defined as `⟪x,y⟫ = ⟪x.fst,y.fst⟫ + ⟪x.snd,y.snd⟫`.

This is just local instance as it is superseded by the following instance for
`InnerProductSpace'`. -/
local instance : Inner 𝕜 (E×F) := ⟨fun (x,y) (x',y') => ⟪x,x'⟫ + ⟪y,y'⟫⟩

@[simp]
lemma prod_inner_apply' (x y : (E × F)) : ⟪x, y⟫ = ⟪x.fst, y.fst⟫ + ⟪x.snd, y.snd⟫ := rfl

open InnerProductSpace' in
noncomputable
instance : InnerProductSpace' 𝕜 (E × F) where
  norm₂ x := (WithLp.instProdNormedAddCommGroup 2 (WithLp 2 E) (WithLp 2 F)).toNorm.norm
    (WithLp.toLp 2 (WithLp.toLp 2 x.1, WithLp.toLp 2 x.2))
  core :=
    let _ := WithLp.instProdNormedAddCommGroup 2 (WithLp 2 E) (WithLp 2 F)
    let inst := (WithLp.instProdInnerProductSpace (𝕜:=𝕜) (E := WithLp 2 E) (F := WithLp 2 F)).toCore
  {
    inner x y := inst.inner (WithLp.toLp 2 (WithLp.toLp 2 x.1, WithLp.toLp 2 x.2))
        (WithLp.toLp 2 (WithLp.toLp 2 y.1, WithLp.toLp 2 y.2))
    conj_inner_symm x y := inst.conj_inner_symm _ _
    re_inner_nonneg x := inst.re_inner_nonneg _
    add_left x y z := inst.add_left (WithLp.toLp 2 (WithLp.toLp 2 x.1, WithLp.toLp 2 x.2))
        (WithLp.toLp 2 (WithLp.toLp 2 y.1, WithLp.toLp 2 y.2))
        (WithLp.toLp 2 (WithLp.toLp 2 z.1, WithLp.toLp 2 z.2))
    smul_left x y r := inst.smul_left (WithLp.toLp 2 (WithLp.toLp 2 x.1, WithLp.toLp 2 x.2))
        (WithLp.toLp 2 (WithLp.toLp 2 y.1, WithLp.toLp 2 y.2)) r
    definite x := by
      intro h
      have h1 := inst.definite (WithLp.toLp 2 (WithLp.toLp 2 x.1, WithLp.toLp 2 x.2)) h
      simp at h1
      exact Prod.ext_iff.mpr h1
  }

  norm₂_sq_eq_re_inner := by
    intro (x,y)
    have : 0 ≤ re ⟪x,x⟫ := PreInnerProductSpace.Core.re_inner_nonneg (𝕜:=𝕜) (F:=E) _ x
    have : 0 ≤ re ⟪y,y⟫ := PreInnerProductSpace.Core.re_inner_nonneg (𝕜:=𝕜) (F:=F) _ y
    simp only [norm, OfNat.ofNat_ne_zero, ↓reduceDIte, ENNReal.ofNat_ne_top, ↓reduceIte,
      WithLp.toLp_fst, WithLp.equiv_apply, ENNReal.toReal_ofNat, Real.rpow_ofNat, WithLp.toLp_snd,
      one_div, WithLp.prod_inner_apply, prod_inner_apply', map_add]
    repeat rw [Real.sq_sqrt (by assumption)]
    norm_num
    rw[← Real.rpow_mul_natCast (by linarith)]
    simp
  inner_top_equiv_norm := by
    obtain ⟨c₁,d₁,hc₁,hd₁,h₁⟩ := inner_top_equiv_norm (𝕜:=𝕜) (E:=E)
    have h₁₁ := fun x => (h₁ x).1
    have h₁₂ := fun x => (h₁ x).2
    obtain ⟨c₂,d₂,hc2,hd₂,h₂⟩ := inner_top_equiv_norm (𝕜:=𝕜) (E:=F)
    have h₂₁ := fun x => (h₂ x).1
    have h₂₂ := fun x => (h₂ x).2
    use min c₁ c₂; use 2 * max d₁ d₂
    constructor
    · positivity
    constructor
    · positivity
    · intro (x,y)
      have : 0 ≤ re ⟪y, y⟫ := by apply PreInnerProductSpace.Core.re_inner_nonneg
      have : 0 ≤ re ⟪x, x⟫ := by apply PreInnerProductSpace.Core.re_inner_nonneg
      simp only [Prod.norm_mk, smul_eq_mul, prod_inner_apply', map_add]
      constructor
      · by_cases h : ‖x‖ ≤ ‖y‖
        · have : max ‖x‖ ‖y‖ ≤ ‖y‖ := by simp[h]
          calc _ ≤ c₂ * ‖y‖ ^ 2 := by gcongr; simp
              _ ≤ re ⟪y,y⟫ := h₂₁ y
              _ ≤ _ := by simpa
        · have : max ‖x‖ ‖y‖ ≤ ‖x‖ := by simp at h; simp; linarith
          calc _ ≤ c₁ * ‖x‖ ^ 2 := by gcongr; simp
              _ ≤ re ⟪x,x⟫ := h₁₁ x
              _ ≤ _ := by simpa
      · by_cases h : re ⟪x,x⟫ ≤ re ⟪y,y⟫
        · calc _ ≤ re ⟪y,y⟫ + re ⟪y,y⟫ := by simp [h]
              _ ≤ d₂ * ‖y‖ ^ 2 + d₂ * ‖y‖ ^ 2 := by gcongr <;> exact h₂₂ y
              _ ≤ _ := by ring_nf; gcongr <;> simp
        · have h : re ⟪y,y⟫ ≤ re ⟪x,x⟫ := by linarith
          calc _ ≤ re ⟪x,x⟫ + re ⟪x,x⟫ := by simp [h]
              _ ≤ d₁ * ‖x‖ ^ 2 + d₁ * ‖x‖ ^ 2 := by gcongr <;> exact h₁₂ x
              _ ≤ _ := by ring_nf; gcongr <;> simp

open InnerProductSpace' in
noncomputable
instance {ι : Type*} [Fintype ι] : InnerProductSpace' 𝕜 (ι → E) where
  norm₂ x := (PiLp.seminormedAddCommGroup 2 (fun _ : ι => (WithLp 2 E))).toNorm.norm
    (WithLp.toLp 2 (fun i => WithLp.toLp 2 (x i)))
  core :=
    let _ := PiLp.normedAddCommGroup 2 (fun _ : ι => (WithLp 2 E))
    let inst := (PiLp.innerProductSpace (𝕜:=𝕜) (fun _ : ι => (WithLp 2 E)))
    {
    inner x y := inst.inner (WithLp.toLp 2 (fun i => WithLp.toLp 2 (x i)))
        (WithLp.toLp 2 (fun i => WithLp.toLp 2 (y i)))
    conj_inner_symm x y := inst.conj_inner_symm _ _
    re_inner_nonneg x := inst.toCore.re_inner_nonneg (WithLp.toLp 2 (fun i => WithLp.toLp 2 (x i)))
    add_left x y z := inst.add_left
      (WithLp.toLp 2 (fun i => WithLp.toLp 2 (x i)))
      (WithLp.toLp 2 (fun i => WithLp.toLp 2 (y i)))
      (WithLp.toLp 2 (fun i => WithLp.toLp 2 (z i)))
    smul_left x y r := inst.smul_left
      (WithLp.toLp 2 (fun i => WithLp.toLp 2 (x i)))
      (WithLp.toLp 2 (fun i => WithLp.toLp 2 (y i))) r
    definite x := by
      intro h
      have h1 := inst.toCore.definite (WithLp.toLp 2 (fun i => WithLp.toLp 2 (x i))) h
      simp at h1
      funext i
      simpa using congrFun h1 i
  }
  norm₂_sq_eq_re_inner := by
    intro x
    simp only [norm, OfNat.ofNat_ne_zero, ↓reduceIte, ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat,
      Real.rpow_two, one_div]
    conv_rhs => rw [inner]
    simp [InnerProductSpace.toInner, PiLp.innerProductSpace]
    rw [← Real.rpow_two, ← Real.rpow_mul]
    swap
    · apply Finset.sum_nonneg
      intro i hi
      exact sq_nonneg √(re ⟪ (x i),(x i)⟫)
    simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      IsUnit.inv_mul_cancel, Real.rpow_one]
    congr 1

  inner_top_equiv_norm := by
    obtain ⟨c, d, hc, hd, hcd⟩ := inner_top_equiv_norm (𝕜 := 𝕜) (E := E)
    refine ⟨c, (Fintype.card ι : ℝ) * d + d, hc, ?_, ?_⟩
    · positivity
    · intro x
      letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
      letI := PiLp.seminormedAddCommGroup 2 (fun _ : ι => WithLp 2 E)
      letI : Norm (PiLp 2 (fun _ : ι => WithLp 2 E)) :=
        (PiLp.seminormedAddCommGroup 2 (fun _ : ι => WithLp 2 E)).toNorm
      letI := PiLp.normedAddCommGroup 2 (fun _ : ι => WithLp 2 E)
      let xL2 : ι → WithLp 2 E := fun i => WithLp.toLp 2 (x i)
      let z : PiLp 2 (fun _ : ι => WithLp 2 E) := WithLp.toLp 2 xL2
      have h_toL2_bound (y : E) : ‖WithLp.toLp 2 y‖ ≤ Real.sqrt d * ‖y‖ := by
        have hy := Real.sqrt_le_sqrt (hcd y).2
        have hleft : ‖WithLp.toLp 2 y‖ = Real.sqrt (re ⟪y, y⟫) := by
          calc
            ‖WithLp.toLp 2 y‖ = |‖y‖₂| := by
              simpa using (norm_withLp2_eq_norm2 (𝕜 := 𝕜) (E := E) (WithLp.toLp 2 y))
            _ = Real.sqrt (‖y‖₂ ^ 2) := by
              symm
              exact Real.sqrt_sq_eq_abs ‖y‖₂
            _ = Real.sqrt (re ⟪y, y⟫) := by rw [norm₂_sq_eq_re_inner (𝕜 := 𝕜) y]
        have hright : Real.sqrt (d * ‖y‖ ^ 2) = Real.sqrt d * ‖y‖ := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg y)]
        simpa [hleft, hright] using hy
      have h_fromL2_bound (y : E) : ‖y‖ ≤ (Real.sqrt c)⁻¹ * ‖WithLp.toLp 2 y‖ := by
        have hy := Real.sqrt_le_sqrt (hcd y).1
        have hleft : Real.sqrt (c * ‖y‖ ^ 2) = Real.sqrt c * ‖y‖ := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg y)]
        have hright : Real.sqrt (re ⟪y, y⟫) = ‖WithLp.toLp 2 y‖ := by
          calc
            Real.sqrt (re ⟪y, y⟫) = Real.sqrt (‖y‖₂ ^ 2) := by rw [norm₂_sq_eq_re_inner (𝕜 := 𝕜) y]
            _ = |‖y‖₂| := Real.sqrt_sq_eq_abs ‖y‖₂
            _ = ‖WithLp.toLp 2 y‖ := by
              simpa using (norm_withLp2_eq_norm2 (𝕜 := 𝕜) (E := E) (WithLp.toLp 2 y)).symm
        have hy' : Real.sqrt c * ‖y‖ ≤ ‖WithLp.toLp 2 y‖ := by
          simpa [hleft, hright] using hy
        have hcsqrt : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
        exact (le_inv_mul_iff₀' hcsqrt).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hy')
      have hxL2_upper : ‖xL2‖ ≤ Real.sqrt d * ‖x‖ := by
        refine (pi_norm_le_iff_of_nonneg (by positivity)).2 ?_
        intro i
        calc
          ‖xL2 i‖ = ‖WithLp.toLp 2 (x i)‖ := rfl
          _ ≤ Real.sqrt d * ‖x i‖ := h_toL2_bound (x i)
          _ ≤ Real.sqrt d * ‖x‖ := by
            gcongr
            exact norm_le_pi_norm x i
      have hxL2_lower : ‖x‖ ≤ (Real.sqrt c)⁻¹ * ‖xL2‖ := by
        refine (pi_norm_le_iff_of_nonneg (by positivity)).2 ?_
        intro i
        calc
          ‖x i‖ ≤ (Real.sqrt c)⁻¹ * ‖WithLp.toLp 2 (x i)‖ := h_fromL2_bound (x i)
          _ ≤ (Real.sqrt c)⁻¹ * ‖xL2‖ := by
            gcongr
            exact norm_le_pi_norm xL2 i
      have hz_lower : ‖xL2‖ ≤ ‖z‖ := by
        refine (pi_norm_le_iff_of_nonneg (norm_nonneg z)).2 ?_
        intro i
        calc
          ‖xL2 i‖ = ‖z i‖ := by simp [xL2, z]
          _ = dist (z i) 0 := by simp [dist_eq_norm]
          _ ≤ dist z 0 := PiLp.dist_apply_le z 0 i
          _ = ‖z‖ := by simp [dist_eq_norm]
      have hz_upper_sq : ‖z‖ ^ 2 ≤ (Fintype.card ι : ℝ) * ‖xL2‖ ^ 2 := by
        rw [PiLp.norm_sq_eq_of_L2 (β := fun _ : ι => WithLp 2 E) z]
        calc
          ∑ i, ‖xL2 i‖ ^ 2 ≤ ∑ i, ‖xL2‖ ^ 2 := by
            refine Finset.sum_le_sum ?_
            intro i hi
            gcongr
            exact norm_le_pi_norm xL2 i
          _ = (Fintype.card ι : ℝ) * ‖xL2‖ ^ 2 := by
            simp [nsmul_eq_mul]
      have hz_re : re ((PiLp.innerProductSpace (𝕜 := 𝕜) (fun _ : ι => WithLp 2 E)).inner z z) = ‖z‖ ^ 2 := by
        simpa [InnerProductSpace.toInner] using (norm_sq_eq_re_inner (𝕜 := 𝕜) z).symm
      constructor
      · have hsqrt_l2 : Real.sqrt c * ‖x‖ ≤ ‖xL2‖ := by
          have hcsqrt : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
          have hmul := mul_le_mul_of_nonneg_left hxL2_lower (Real.sqrt_nonneg c)
          have hsimp : Real.sqrt c * ((Real.sqrt c)⁻¹ * ‖xL2‖) = ‖xL2‖ := by
            field_simp [hcsqrt.ne']
          exact hmul.trans_eq hsimp
        have hsqrt : Real.sqrt c * ‖x‖ ≤ ‖z‖ := hsqrt_l2.trans hz_lower
        have hsq : (Real.sqrt c * ‖x‖) ^ 2 ≤ ‖z‖ ^ 2 := by
          exact pow_le_pow_left₀ (by positivity) hsqrt 2
        have hrewrite : c * ‖x‖ ^ 2 = (Real.sqrt c * ‖x‖) ^ 2 := by
          calc
            c * ‖x‖ ^ 2 = (Real.sqrt c) ^ 2 * ‖x‖ ^ 2 := by rw [Real.sq_sqrt (le_of_lt hc)]
            _ = (Real.sqrt c * ‖x‖) ^ 2 := by ring
        have hmain : c * ‖x‖ ^ 2 ≤ ‖z‖ ^ 2 := by
          simpa [hrewrite] using hsq
        simpa [smul_eq_mul, xL2, z, hz_re] using hmain
      · have hxL2_upper_sq : ‖xL2‖ ^ 2 ≤ d * ‖x‖ ^ 2 := by
          have hsq : ‖xL2‖ ^ 2 ≤ (Real.sqrt d * ‖x‖) ^ 2 := by
            exact pow_le_pow_left₀ (by positivity) hxL2_upper 2
          have hrewrite : (Real.sqrt d * ‖x‖) ^ 2 = d * ‖x‖ ^ 2 := by
            calc
              (Real.sqrt d * ‖x‖) ^ 2 = (Real.sqrt d) ^ 2 * ‖x‖ ^ 2 := by ring
              _ = d * ‖x‖ ^ 2 := by rw [Real.sq_sqrt (le_of_lt hd)]
          simpa [hrewrite] using hsq
        have hmain : ‖z‖ ^ 2 ≤ (Fintype.card ι : ℝ) * d * ‖x‖ ^ 2 := by
          refine hz_upper_sq.trans ?_
          nlinarith [hxL2_upper_sq, hd, sq_nonneg ‖x‖]
        have hmain' : ‖z‖ ^ 2 ≤ ((Fintype.card ι : ℝ) * d + d) * ‖x‖ ^ 2 := by
          refine hmain.trans ?_
          nlinarith [hd, sq_nonneg ‖x‖]
        simpa [smul_eq_mul, xL2, z, hz_re, mul_assoc, mul_left_comm, mul_comm] using hmain'

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [hE : InnerProductSpace' ℝ E]
local notation "⟪" x ", " y "⟫" => inner ℝ x y
open InnerProductSpace'
lemma _root_.isBoundedBilinearMap_inner' :
    IsBoundedBilinearMap ℝ fun p : E × E => ⟪p.1, p.2⟫ where
  add_left := inner_add_left'
  smul_left := fun r x y => by
    simpa using inner_smul_left' x y r
  add_right := inner_add_right'
  smul_right := fun r x y => by
    simpa using inner_smul_right' x y r
  bound := by
    obtain ⟨c, d, hc, hd, h⟩ := hE.inner_top_equiv_norm
    use d
    simp_all
    intro x y
    trans |‖x‖₂| * |‖y‖₂|
    change |@inner ℝ (WithLp 2 E) _ _ _| ≤ _
    have h1 := norm_inner_le_norm (𝕜 := ℝ) (E := WithLp 2 E) (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simp at h1
    apply h1.trans
    apply le_of_eq
    congr
    rw [norm_withLp2_eq_norm2]
    rfl
    rw [norm_withLp2_eq_norm2]
    rfl
    have h1 : |‖x‖₂| ≤ √ d * ‖x‖ := by
      apply le_of_sq_le_sq
      simp [@mul_pow]
      rw [norm₂_sq_eq_re_inner (𝕜 := ℝ)]
      simp only [re_to_real]
      apply (h x).2.trans
      apply le_of_eq
      simp only [mul_eq_mul_right_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        pow_eq_zero_iff, norm_eq_zero]
      left
      refine Eq.symm (Real.sq_sqrt ?_)
      linarith
      apply mul_nonneg
      exact Real.sqrt_nonneg d
      exact norm_nonneg x
    have h2 : |‖y‖₂| ≤ √ d * ‖y‖ := by
      apply le_of_sq_le_sq
      simp [@mul_pow]
      rw [norm₂_sq_eq_re_inner (𝕜 := ℝ)]
      simp only [re_to_real]
      apply (h y).2.trans
      apply le_of_eq
      simp only [mul_eq_mul_right_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        pow_eq_zero_iff, norm_eq_zero]
      left
      refine Eq.symm (Real.sq_sqrt ?_)
      linarith
      apply mul_nonneg
      exact Real.sqrt_nonneg d
      exact norm_nonneg y
    trans (√ d * ‖x‖) * (√ d * ‖y‖)
    refine mul_le_mul_of_nonneg h1 h2 ?_ ?_
    exact abs_nonneg ‖x‖₂
    apply mul_nonneg
    exact Real.sqrt_nonneg d
    exact norm_nonneg y
    apply le_of_eq
    ring_nf
    rw [Real.sq_sqrt]
    ring
    linarith

end Constructions
