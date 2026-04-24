/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.QuadraticForm.Real
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Pseudo-Riemannian Metrics on Smooth Manifolds

This file formalizes pseudo-Riemannian metrics on smooth manifolds and establishes their basic
properties.

A pseudo-Riemannian metric equips a manifold with a smoothly varying, non-degenerate, symmetric
bilinear form of *constant index* on each tangent space, generalizing the concept of an inner
product space to curved spaces. The index here refers to `QuadraticForm.negDim`, the dimension
of a maximal negative definite subspace.

## Main Definitions

* `PseudoRiemannianMetric E H M n I`: A structure representing a `C^n` pseudo-Riemannian metric
  on a manifold `M` modelled on `(E, H)` with model with corners `I`. It consists of a family
  of non-degenerate, symmetric, continuous bilinear forms `gₓ` on each tangent space `TₓM`,
  varying `C^n`-smoothly with `x` and having a locally constant negative dimension (`negDim`).
  The model space `E` must be finite-dimensional, and the manifold `M` must be `C^{n+1}` smooth.

* `PseudoRiemannianMetric.flatEquiv g x`: The "musical isomorphism" from the tangent space at `x`
  to its dual space, representing the canonical isomorphism induced by the metric.

* `PseudoRiemannianMetric.sharpEquiv g x`: The inverse of the flat isomorphism, mapping from
  the dual space back to the tangent space.

* `PseudoRiemannianMetric.toQuadraticForm g x`: The quadratic form `v ↦ gₓ(v, v)` associated
  with the metric at point `x`.

This formalization adopts a direct approach, defining the metric as a family of bilinear forms
on tangent spaces, varying smoothly over the manifold. This pragmatic choice allows for foundational
development while acknowledging that a more abstract ideal would involve defining metrics as
sections of a tensor bundle (e.g., `Hom(TM ⊗ TM, ℝ)` or `TM →L[ℝ] TM →L[ℝ] ℝ`.

## Reference

* Barrett O'Neill, "Semi-Riemannian Geometry With Applications to Relativity" (Academic Press, 1983)
* [Discussion on Zulip about (Pseudo) Riemannian metrics] https.
leanprover.zulipchat.com/#narrow/channel/113488-general/topic/.28Pseudo.29.20Riemannian.20metric
-/

section PseudoRiemannianMetric

noncomputable section

open Bundle Set Finset Function Filter Module Topology ContinuousLinearMap
open scoped Manifold Bundle LinearMap Dual

namespace QuadraticForm

variable {K : Type*} [Field K]

/-! ## Negative Index -/

/-- The negative dimension (often called the index or negative index of inertia) of a
quadratic form `q` on a finite-dimensional real vector space.

This value is defined by diagonalizing the quadratic form into an equivalent
`QuadraticMap.weightedSumSquares ℝ s`, where `s : Fin (finrank ℝ E) → SignType`
assigns `1`, `0`, or `-1` to each component. The `negDim` is the count of
components `i` for which `s i = SignType.neg`.

By Sylvester's Law of Inertia, this count is an invariant of the quadratic form.
Geometrically, `negDim q` represents the dimension of any maximal vector subspace
on which `q` is negative definite. This corresponds to O'Neill's Definition 18 (p. 47)
of the index `ν` of a symmetric bilinear form `b` on `V`, which is "the largest integer
that is the dimension of a subspace `W ⊂ V` on which `b|W` is negative
definite." -/
noncomputable def negDim {E : Type*} [AddCommGroup E]
    [Module ℝ E] [FiniteDimensional ℝ E]
    (q : QuadraticForm ℝ E) : ℕ := by classical
  let P : (Fin (finrank ℝ E) → SignType) → Prop := fun w =>
      QuadraticMap.Equivalent q (QuadraticMap.weightedSumSquares ℝ fun i => (w i : ℝ))
  let h_exists : ∃ w, P w := QuadraticForm.equivalent_signType_weighted_sum_squared q
  let w := Classical.choose h_exists
  exact Finset.card (Finset.filter (fun i => w i = SignType.neg) Finset.univ)

/-- For a standard basis vector in a weighted sum of squares, only one term in the sum
    is nonzero. -/
lemma QuadraticMap.weightedSumSquares_basis_vector {E : Type*} [AddCommGroup E]
    [Module ℝ E] {weights : Fin (finrank ℝ E) → ℝ}
    {i : Fin (finrank ℝ E)} (v : Fin (finrank ℝ E) → ℝ)
    (hv : ∀ j, v j = if j = i then 1 else 0) :
    QuadraticMap.weightedSumSquares ℝ weights v = weights i := by
  simp only [QuadraticMap.weightedSumSquares_apply]
  rw [Finset.sum_eq_single i]
  · simp only [hv i, ↓reduceIte, mul_one, smul_eq_mul]
  · intro j _ hj
    simp only [hv j, if_neg hj, mul_zero, smul_eq_mul]
  · simp only [Finset.mem_univ, not_true_eq_false, smul_eq_mul, mul_eq_zero, or_self,
    IsEmpty.forall_iff]

/-- When a quadratic form is equivalent to a weighted sum of squares,
    negative weights correspond to vectors where the form takes negative values.
    This is a concrete realization of a 1-dimensional negative definite subspace,
    contributing to O'Neill's index `ν` (Definition 18, p. 47). -/
lemma neg_weight_implies_neg_value {E : Type*} [AddCommGroup E] [Module ℝ E]
    {q : QuadraticForm ℝ E} {w : Fin (finrank ℝ E) → SignType}
    (h_equiv : QuadraticMap.Equivalent q (QuadraticMap.weightedSumSquares ℝ fun i => (w i : ℝ)))
    {i : Fin (finrank ℝ E)} (hi : w i = SignType.neg) :
    ∃ v : E, v ≠ 0 ∧ q v < 0 := by
  let f := Classical.choice h_equiv
  let v_std : Fin (finrank ℝ E) → ℝ := fun j => if j = i then 1 else 0
  let v := f.symm v_std
  have hv_ne_zero : v ≠ 0 := by
    intro h
    have : f v = f 0 := by rw [h]
    have : f (f.symm v_std) = f 0 := by rw [← this]
    have : v_std = 0 := by
      rw [← f.apply_symm_apply v_std]
      exact Eq.trans this (map_zero f)
    have : v_std i = 0 := by rw [this]; rfl
    simp only [↓reduceIte, one_ne_zero, v_std] at this
  have hq_neg : q v < 0 := by
    have heq : q v = QuadraticMap.weightedSumSquares ℝ (fun j => (w j : ℝ)) v_std :=
      QuadraticMap.IsometryEquiv.map_app f.symm v_std
    have hw : QuadraticMap.weightedSumSquares ℝ (fun j => (w j : ℝ)) v_std = (w i : ℝ) := by
      apply QuadraticMap.weightedSumSquares_basis_vector v_std
      intro j; simp only [v_std]
    rw [heq, hw]
    have : (w i : ℝ) = -1 := by simp only [hi, SignType.neg_eq_neg_one, SignType.coe_neg,
      SignType.coe_one]
    rw [this]
    exact neg_one_lt_zero
  exact ⟨v, hv_ne_zero, hq_neg⟩

/-- A positive definite quadratic form cannot have any negative weights
    in its diagonal representation. A quadratic form `q` derived from a bilinear form `b`
    is positive definite if `b(v,v) > 0` for `v ≠ 0` (O'Neill, Definition 17 (1), p. 46).
    The existence of a negative weight would imply `q(v) < 0` for some `v ≠ 0`, a contradiction. -/
lemma posDef_no_neg_weights {E : Type*} [AddCommGroup E] [Module ℝ E]
    {q : QuadraticForm ℝ E} (hq : q.PosDef)
    {w : Fin (finrank ℝ E) → SignType}
    (h_equiv : QuadraticMap.Equivalent q (QuadraticMap.weightedSumSquares ℝ fun i => (w i : ℝ))) :
    ∀ i, w i ≠ SignType.neg := by
  intro i hi
  obtain ⟨v, hv_ne_zero, hq_neg⟩ := QuadraticForm.neg_weight_implies_neg_value h_equiv hi
  have hq_pos : 0 < q v := hq v hv_ne_zero
  exact lt_asymm hq_neg hq_pos

/-- For a positive definite quadratic form, the negative dimension (index) is zero.
    O'Neill states (p. 47) that "ν = 0 if and only if b is positive semidefinite."
    Since positive definite implies positive semidefinite (Definitions 17 (1) and (2), p. 46),
    a positive definite form must have index `ν = 0`. -/
theorem rankNeg_eq_zero {E : Type*} [AddCommGroup E]
    [Module ℝ E] [FiniteDimensional ℝ E] {q : QuadraticForm ℝ E} (hq : q.PosDef) :
    q.negDim = 0 := by
  haveI : Invertible (2 : ℝ) := inferInstance
  unfold QuadraticForm.negDim
  have h_exists := equivalent_signType_weighted_sum_squared q
  let w := Classical.choose h_exists
  have h_equiv : QuadraticMap.Equivalent q
      (QuadraticMap.weightedSumSquares ℝ fun i => (w i : ℝ)) :=
    Classical.choose_spec h_exists
  have h_no_neg : ∀ i, w i ≠ SignType.neg :=
    QuadraticForm.posDef_no_neg_weights hq h_equiv
  simp [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun ⦃x⦄ => h_no_neg x

end QuadraticForm

/-! ## Pseudo-Riemannian Metric -/

/--
Constructs a `QuadraticForm` on the tangent space `TₓM` at a point `x` from the
value of a pseudo-Riemannian metric at that point.
(O'Neill, p. 47, "The function q: V → R given by q(v) = b(v,v) is the associated quadratic
form of b.")
The pseudo-Riemannian metric is given by `val`, a family of continuous bilinear forms
`gₓ: TₓM × TₓM → ℝ` for each `x : M`.
The quadratic form `Qₓ` at `x` is defined as `Qₓ(v) = gₓ(v,v)`.
The associated symmetric bilinear form required by `QuadraticForm.exists_companion'`
is `Bₓ(v,w) = gₓ(v,w) + gₓ(w,v)`. Given the symmetry `symm`, this is `2 * gₓ(v,w)`.
-/
private def pseudoRiemannianMetricValToQuadraticForm
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type w} [TopologicalSpace H]
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H}
    (val : ∀ (x : M), TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ))
    (symm : ∀ (x : M) (v w : TangentSpace I x), (val x v) w = (val x w) v)
    (x : M) : QuadraticForm ℝ (TangentSpace I x) where
  toFun v := val x v v
  toFun_smul a v := by
    simp only [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, smul_smul]
  exists_companion' :=
      ⟨LinearMap.mk₂ ℝ (fun v y => val x v y + val x y v)
        (fun v₁ v₂ y => by simp only [map_add, add_apply]; ring)
        (fun a v y => by simp only [map_smul, smul_apply]; ring_nf; exact Eq.symm (smul_add ..))
        (fun v y₁ y₂ => by simp only [map_add, add_apply]; ring)
        (fun a v y => by simp only [map_smul, smul_apply]; ring_nf; exact Eq.symm (smul_add ..)),
            by
              intro v y
              simp only [LinearMap.mk₂_apply, ContinuousLinearMap.map_add,
                ContinuousLinearMap.add_apply, symm x]
              ring⟩

/-- A pseudo-Riemannian metric of smoothness class `C^n` on a manifold `M` modelled on `(E, H)`
with model `I`. This structure defines a smoothly varying, non-degenerate, symmetric,
continuous bilinear form `gₓ` of constant negative dimension on the tangent space `TₓM`
at each point `x`. Requires `M` to be `C^{n+1}` smooth.
This structure formalizes O'Neill's Definition 3.1 (p. 54) of a metric tensor `g` on `M`
as a "symmetric non-degenerate (0,2) tensor field on M of constant index."
Each `gₓ` is a scalar product (O'Neill, Definition 20, p. 47) on `TₓM`. -/
@[ext]
structure PseudoRiemannianMetric
    (E : Type v) (H : Type w) (M : Type w) (n : WithTop ℕ∞)
    [inst_norm_grp_E : NormedAddCommGroup E]
    [inst_norm_sp_E : NormedSpace ℝ E]
    [inst_top_H : TopologicalSpace H]
    [inst_top_M : TopologicalSpace M]
    [inst_chart_M : ChartedSpace H M]
    [inst_chart_E : ChartedSpace H E]
    (I : ModelWithCorners ℝ E H)
    [inst_mani : IsManifold I (n + 1) M]
    [inst_tangent_findim : ∀ (x : M), FiniteDimensional ℝ (TangentSpace I x)] :
      Type (max u v w) where
  /-- The metric tensor at each point `x : M`, represented as a continuous linear map
      `TₓM →L[ℝ] (TₓM →L[ℝ] ℝ)`. Applying it twice, `(val x v) w`, yields `gₓ(v, w)`. -/
  val : ∀ (x : M), TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)
  /-- The metric is symmetric: `gₓ(v, w) = gₓ(w, v)`. -/
  symm : ∀ (x : M) (v w : TangentSpace I x), (val x v) w = (val x w) v
  /-- The metric is non-degenerate: if `gₓ(v, w) = 0` for all `w`, then `v = 0`. -/
  nondegenerate : ∀ (x : M) (v : TangentSpace I x), (∀ w : TangentSpace I x,
    (val x v) w = 0) → v = 0
  /-- The metric varies smoothly: Expressed in local coordinates via the chart
      `e := extChartAt I x₀`, the function
      `y ↦ g_{e.symm y}(mfderiv I I e.symm y v, mfderiv I I e.symm y w)` is `C^n` smooth on the
      chart's target `e.target` for any constant vectors `v, w` in the model space `E`. -/
  smooth_in_charts' : ∀ (x₀ : M) (v w : E),
    let e := extChartAt I x₀
    ContDiffWithinAt ℝ n
      (fun y => val (e.symm y) (mfderiv I I e.symm y v) (mfderiv I I e.symm y w))
      (e.target) (e x₀)
  /-- The negative dimension (`QuadraticForm.negDim`) of the metric's quadratic form is
      locally constant. On a connected manifold, this implies it is constant globally. -/
  negDim_isLocallyConstant :
    IsLocallyConstant (fun x : M =>
      have : FiniteDimensional ℝ (TangentSpace I x) := inferInstance
      (pseudoRiemannianMetricValToQuadraticForm val symm x).negDim)

namespace PseudoRiemannianMetric

variable {E : Type v} {H : Type w} {M : Type w} {n : WithTop ℕ∞}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [ChartedSpace H E]
variable {I : ModelWithCorners ℝ E H}
variable [IsManifold I (n + 1) M]
variable [inst_tangent_findim : ∀ (x : M), FiniteDimensional ℝ (TangentSpace I x)]
variable {g : PseudoRiemannianMetric E H M n I}

/-- Given a pseudo-Riemannian metric `g` on manifold `M` and a point `x : M`,
this function constructs a bilinear form on the tangent space at `x`.
For tangent vectors `u v : T_x M`, the bilinear form is given by:
`g_x(u, v) = g(x)(u, v)` -/
def toBilinForm (g : PseudoRiemannianMetric E H M n I) (x : M) :
    LinearMap.BilinForm ℝ (TangentSpace I x) where
  toFun := λ v => { toFun := λ w => g.val x v w,
                    map_add' := λ w₁ w₂ => by
                      simp only [ContinuousLinearMap.map_add],
                    map_smul' := λ c w => by
                      simp only [map_smul, smul_eq_mul, RingHom.id_apply] }
  map_add' := λ v₁ v₂ => by
    ext w
    simp only [map_add, add_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
  map_smul' := λ c v => by
    ext w
    simp only [map_smul, coe_smul', Pi.smul_apply, smul_eq_mul, LinearMap.coe_mk, AddHom.coe_mk,
      RingHom.id_apply, LinearMap.smul_apply]

/-- Convert a pseudo-Riemannian metric at a point `x` to a quadratic form `v ↦ gₓ(v, v)`. -/
abbrev toQuadraticForm (g : PseudoRiemannianMetric E H M n I) (x : M) :
    QuadraticForm ℝ (TangentSpace I x) :=
  pseudoRiemannianMetricValToQuadraticForm g.val g.symm x

/-- Coercion from PseudoRiemannianMetric to its function representation. -/
instance coeFunInst : CoeFun (PseudoRiemannianMetric E H M n I)
        (fun _ => ∀ x : M, TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)) where
  coe g := g.val

@[simp]
lemma toBilinForm_apply (g : PseudoRiemannianMetric E H M n I) (x : M)
    (v w : TangentSpace I x) :
  toBilinForm g x v w = g.val x v w := rfl

@[simp]
lemma toQuadraticForm_apply (g : PseudoRiemannianMetric E H M n I) (x : M)
    (v : TangentSpace I x) :
  toQuadraticForm g x v = g.val x v v := rfl

@[simp]
lemma toBilinForm_isSymm (g : PseudoRiemannianMetric E H M n I) (x : M) :
    (toBilinForm g x).IsSymm := by
  refine { eq := ?_ }
  intro v w; simp only [toBilinForm_apply]; exact g.symm x v w

@[simp]
lemma toBilinForm_nondegenerate (g : PseudoRiemannianMetric E H M n I) (x : M) :
    (toBilinForm g x).Nondegenerate := by
  constructor
  · intro v hv
    simp_rw [toBilinForm_apply] at hv
    exact g.nondegenerate x v hv
  · intro v hv
    apply g.nondegenerate x v
    intro w
    rw [g.symm x v w]
    exact hv w

/-- The inner product (or scalar product) on the tangent space at point `x`
  induced by the pseudo-Riemannian metric `g`. This is `gₓ(v, w)`. -/
def inner (g : PseudoRiemannianMetric E H M n I) (x : M) (v w : TangentSpace I x) : ℝ :=
  g.val x v w

@[simp]
lemma inner_apply (g : PseudoRiemannianMetric E H M n I) (x : M) (v w : TangentSpace I x) :
    inner g x v w = g.val x v w := rfl

/-! ## Flat -/

section Flat

/-- The "musical" isomorphism (index lowering) `v ↦ gₓ(v, -)`.
The non-degeneracy of `gₓ` (O'Neill, Def 17 (3), p. 46) means its matrix representation
is invertible (O'Neill, Lemma 19, p. 47), and that this map is an isomorphism from `TₓM`
to its dual. -/
def flat (g : PseudoRiemannianMetric E H M n I) (x : M) :
    TangentSpace I x →ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  { toFun := λ v => g.val x v,
    map_add' := λ v w => by simp only [ContinuousLinearMap.map_add],
    map_smul' := λ a v => by simp only [ContinuousLinearMap.map_smul]; rfl }

@[simp]
lemma flat_apply (g : PseudoRiemannianMetric E H M n I) (x : M) (v w : TangentSpace I x) :
    (flat g x v) w = g.val x v w := by rfl

/-- The musical isomorphism as a continuous linear map. -/
def flatL (g : PseudoRiemannianMetric E H M n I) (x : M) :
    TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ) where
  toFun := λ v => g.val x v
  map_add' := λ v w => by simp only [ContinuousLinearMap.map_add]
  map_smul' := λ a v => by simp only [ContinuousLinearMap.map_smul]; rfl
  cont := ContinuousLinearMap.continuous (g.val x)

@[simp]
lemma flatL_apply (g : PseudoRiemannianMetric E H M n I) (x : M) (v w : TangentSpace I x) :
    (flatL g x v) w = g.val x v w := rfl

@[simp]
lemma flat_inj (g : PseudoRiemannianMetric E H M n I) (x : M) :
    Function.Injective (flat g x) := by
  rw [← LinearMap.ker_eq_bot]; apply LinearMap.ker_eq_bot'.mpr
  intro v hv; apply g.nondegenerate x v; intro w; exact DFunLike.congr_fun hv w

@[simp]
lemma flatL_inj (g : PseudoRiemannianMetric E H M n I) (x : M) :
    Function.Injective (flatL g x) :=
  flat_inj g x

@[simp]
lemma flatL_surj
    (g : PseudoRiemannianMetric E H M n I) (x : M) :
    Function.Surjective (g.flatL x) := by
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inst_tangent_findim x
  have h_finrank_eq : finrank ℝ (TangentSpace I x) = finrank ℝ (TangentSpace I x →L[ℝ] ℝ) := by
    have h_dual_eq : finrank ℝ (TangentSpace I x →L[ℝ] ℝ) = finrank ℝ (Module.Dual ℝ
    (TangentSpace I x)) := by
      let to_dual : (TangentSpace I x →L[ℝ] ℝ) → Module.Dual ℝ (TangentSpace I x) :=
        fun f => f.toLinearMap
      let from_dual : Module.Dual ℝ (TangentSpace I x) → (TangentSpace I x →L[ℝ] ℝ) := fun f =>
        ContinuousLinearMap.mk f (by
          apply LinearMap.continuous_of_finiteDimensional)
      let equiv : (TangentSpace I x →L[ℝ] ℝ) ≃ₗ[ℝ] Module.Dual ℝ (TangentSpace I x) :=
      { toFun := to_dual,
        invFun := from_dual,
        map_add' := fun f g => by
          ext v; unfold to_dual; simp only [LinearMap.add_apply]; rfl,
        map_smul' := fun c f => by
          ext v; unfold to_dual; simp only [LinearMap.smul_apply]; rfl,
        left_inv := fun f => by
          ext v; unfold to_dual from_dual; simp,
        right_inv := fun f => by
          ext v; unfold to_dual from_dual; simp }
      exact LinearEquiv.finrank_eq equiv
    rw [h_dual_eq, ← Subspace.dual_finrank_eq]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_finrank_eq).mp (flatL_inj g x)

/-- The "musical" isomorphism (index lowering) from `TₓM` to its dual,
as a continuous linear equivalence. This equivalence is a direct result of `gₓ` being
a non-degenerate bilinear form (O'Neill, Def 17(3), p. 46; Lemma 19, p. 47). -/
def flatEquiv
    (g : PseudoRiemannianMetric E H M n I)
    (x : M) :
    TangentSpace I x ≃L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    (LinearEquiv.ofBijective
      ((g.flatL x).toLinearMap)
      ⟨g.flatL_inj x, g.flatL_surj x⟩)

lemma coe_flatEquiv
    (g : PseudoRiemannianMetric E H M n I) (x : M) :
    (g.flatEquiv x : TangentSpace I x →ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ)) = g.flatL x := rfl

@[simp]
lemma flatEquiv_apply
    (g : PseudoRiemannianMetric E H M n I) (x : M) (v w : TangentSpace I x) :
    (g.flatEquiv x v) w = g.val x v w := rfl

end Flat

/-! ## Sharp -/

section Sharp

/-- The "musical" isomorphism (index raising) from the dual of `TₓM` to `TₓM`.
This is the inverse of `flatEquiv g x`, and its existence as an isomorphism is
guaranteed by the non-degeneracy of `gₓ` (O'Neill, Lemma 19, p. 47). -/
def sharpEquiv
    (g : PseudoRiemannianMetric E H M n I) (x : M) :
    (TangentSpace I x →L[ℝ] ℝ) ≃L[ℝ] TangentSpace I x :=
  (g.flatEquiv x).symm

/-- The index raising map `sharp` as a continuous linear map. -/
def sharpL
    (g : PseudoRiemannianMetric E H M n I) (x : M) :
    (TangentSpace I x →L[ℝ] ℝ) →L[ℝ] TangentSpace I x := (g.sharpEquiv x).toContinuousLinearMap

lemma sharpL_eq_toContinuousLinearMap
    (g : PseudoRiemannianMetric E H M n I) (x : M) :
  g.sharpL x = (g.sharpEquiv x).toContinuousLinearMap := rfl

lemma coe_sharpEquiv
    (g : PseudoRiemannianMetric E H M n I) (x : M) :
    (g.sharpEquiv x : (TangentSpace I x →L[ℝ] ℝ) →L[ℝ] TangentSpace I x) = g.sharpL x := rfl

/-- The index raising map `sharp` as a linear map. -/
noncomputable def sharp
    (g : PseudoRiemannianMetric E H M n I) (x : M) :
    (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] TangentSpace I x := (g.sharpEquiv x).toLinearEquiv.toLinearMap

@[simp]
lemma sharpL_apply_flatL
    (g : PseudoRiemannianMetric E H M n I) (x : M) (v : TangentSpace I x) :
    g.sharpL x (g.flatL x v) = v :=
  (g.flatEquiv x).left_inv v

@[simp]
lemma flatL_apply_sharpL
    (g : PseudoRiemannianMetric E H M n I) (x : M) (ω : TangentSpace I x →L[ℝ] ℝ) :
    g.flatL x (g.sharpL x ω) = ω := (g.flatEquiv x).right_inv ω

/-- Applying `sharp` then `flat` recovers the original covector. -/
@[simp]
lemma flat_sharp_apply
    (g : PseudoRiemannianMetric E H M n I) (x : M) (ω : TangentSpace I x →L[ℝ] ℝ) :
    g.flat x (g.sharp x ω) = ω := by
  have := flatL_apply_sharpL g x ω
  simp only [flat, sharp]; simp only [LinearEquiv.coe_coe] at this ⊢
  exact this

@[simp]
lemma sharp_flat_apply
    (g : PseudoRiemannianMetric E H M n I) (x : M) (v : TangentSpace I x) :
    g.sharp x (g.flat x v) = v := by
  have := sharpL_apply_flatL g x v
  simp only [sharp, flat]; simp only [LinearEquiv.coe_coe] at this ⊢
  exact this

/-- The metric evaluated at `sharp ω₁` and `sharp ω₂`. -/
@[simp]
lemma apply_sharp_sharp
    (g : PseudoRiemannianMetric E H M n I) (x : M) (ω₁ ω₂ : TangentSpace I x →L[ℝ] ℝ) :
    g.val x (g.sharpL x ω₁) (g.sharpL x ω₂) = ω₁ (g.sharpL x ω₂) := by
  rw [← flatL_apply g x (g.sharpL x ω₁)]
  rw [flatL_apply_sharpL g x ω₁]

/-- The metric evaluated at `v` and `sharp ω`. -/
lemma apply_vec_sharp
    (g : PseudoRiemannianMetric E H M n I) (x : M) (v : TangentSpace I x)
    (ω : TangentSpace I x →L[ℝ] ℝ) :
    g.val x v (g.sharpL x ω) = ω v := by
  rw [g.symm x v (g.sharpL x ω)]
  rw [← flatL_apply g x (g.sharpL x ω)]
  rw [flatL_apply_sharpL g x ω]

end Sharp

/-! ## Cotangent -/
section Cotangent

variable {E : Type v} {H : Type w} {M : Type w} {n : WithTop ℕ∞}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [ChartedSpace H E]
variable {I : ModelWithCorners ℝ E H}
variable [IsManifold I (n + 1) M]
variable [inst_tangent_findim : ∀ (x : M), FiniteDimensional ℝ (TangentSpace I x)]

/-- The value of the induced metric on the cotangent space at point `x`. -/
noncomputable def cotangentMetricVal (g : PseudoRiemannianMetric E H M n I) (x : M)
    (ω₁ ω₂ : TangentSpace I x →L[ℝ] ℝ) : ℝ :=
  g.val x (g.sharpL x ω₁) (g.sharpL x ω₂)

@[simp]
lemma cotangentMetricVal_eq_apply_sharp (g : PseudoRiemannianMetric E H M n I) (x : M)
    (ω₁ ω₂ : TangentSpace I x →L[ℝ] ℝ) :
  cotangentMetricVal g x ω₁ ω₂ = ω₁ (g.sharpL x ω₂) := by
  rw [cotangentMetricVal, apply_sharp_sharp]

lemma cotangentMetricVal_symm (g : PseudoRiemannianMetric E H M n I) (x : M)
    (ω₁ ω₂ : TangentSpace I x →L[ℝ] ℝ) :
  cotangentMetricVal g x ω₁ ω₂ = cotangentMetricVal g x ω₂ ω₁ := by
  unfold cotangentMetricVal
  rw [g.symm x (g.sharpL x ω₁) (g.sharpL x ω₂)]

/-- The induced metric on the cotangent space at point `x` as a bilinear form.
For covectors `ω₁` and `ω₂`, this gives `g(ω₁^#, ω₂^#)`, where `ω^#` is
the "sharp" musical isomorphism raising indices. -/
noncomputable def cotangentToBilinForm (g : PseudoRiemannianMetric E H M n I) (x : M) :
    LinearMap.BilinForm ℝ (TangentSpace I x →L[ℝ] ℝ) where
  toFun ω₁ := { toFun := λ ω₂ => cotangentMetricVal g x ω₁ ω₂,
                map_add' := λ ω₂ ω₃ => by
                  simp only [cotangentMetricVal,
                    ContinuousLinearMap.map_add],
                map_smul' := λ c ω₂ => by
                  simp only [cotangentMetricVal,
                    map_smul, smul_eq_mul, RingHom.id_apply] }
  map_add' := λ ω₁ ω₂ => by
    ext ω₃
    simp only [cotangentMetricVal,
      ContinuousLinearMap.map_add,
      ContinuousLinearMap.add_apply,
      LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
  map_smul' := λ c ω₁ => by
    ext ω₂
    simp only [cotangentMetricVal,
      ContinuousLinearMap.map_smul,
      ContinuousLinearMap.smul_apply,
      LinearMap.coe_mk, AddHom.coe_mk,
      RingHom.id_apply, LinearMap.smul_apply]

/-- The cometric on the cotangent space T_x*M at `x`, expressed as a quadratic form.
It is induced by the pseudo-Riemannian metric on the tangent space T_xM. -/
noncomputable def cotangentToQuadraticForm (g : PseudoRiemannianMetric E H M n I) (x : M) :
    QuadraticForm ℝ (TangentSpace I x →L[ℝ] ℝ) where
  toFun ω := cotangentMetricVal g x ω ω
  toFun_smul a ω := by
    simp only [cotangentMetricVal,
      ContinuousLinearMap.map_smul,
      ContinuousLinearMap.smul_apply,
      smul_smul]
  exists_companion' :=
      ⟨LinearMap.mk₂ ℝ (fun ω₁ ω₂ =>
          cotangentMetricVal g x ω₁ ω₂ + cotangentMetricVal g x ω₂ ω₁)
        (fun ω₁ ω₂ ω₃ => by simp only [cotangentMetricVal, map_add, add_apply]; ring)
        (fun a ω₁ ω₂ => by
          simp only [cotangentMetricVal, map_smul, smul_apply];
          ring_nf; exact Eq.symm (smul_add ..))
        (fun ω₁ ω₂ ω₃ => by
          simp only [cotangentMetricVal, map_add, add_apply]; ring)
        (fun a ω₁ ω₂ => by
          simp only [cotangentMetricVal, map_smul, smul_apply]; ring_nf;
          exact Eq.symm (smul_add ..)),
          by
            intro ω₁ ω₂
            simp only [LinearMap.mk₂_apply, cotangentMetricVal]
            simp only [ContinuousLinearMap.map_add, ContinuousLinearMap.add_apply]
            ring⟩

@[simp]
lemma cotangentToBilinForm_apply (g : PseudoRiemannianMetric E H M n I) (x : M)
    (ω₁ ω₂ : TangentSpace I x →L[ℝ] ℝ) :
  cotangentToBilinForm g x ω₁ ω₂ = cotangentMetricVal g x ω₁ ω₂ := rfl

@[simp]
lemma cotangentToQuadraticForm_apply (g : PseudoRiemannianMetric E H M n I) (x : M)
    (ω : TangentSpace I x →L[ℝ] ℝ) :
  cotangentToQuadraticForm g x ω = cotangentMetricVal g x ω ω := rfl

@[simp]
lemma cotangentToBilinForm_isSymm (g : PseudoRiemannianMetric E H M n I) (x : M) :
    (cotangentToBilinForm g x).IsSymm := by
  refine { eq := ?_ }
  intro ω₁ ω₂; simp only [cotangentToBilinForm_apply]; exact cotangentMetricVal_symm g x ω₁ ω₂

/-- The cotangent metric is non-degenerate: if `cotangentMetricVal g x ω v = 0` for all `v`,
    then `ω = 0`. -/
lemma cotangentMetricVal_nondegenerate (g : PseudoRiemannianMetric E H M n I) (x : M)
    (ω : TangentSpace I x →L[ℝ] ℝ) (h : ∀ v : TangentSpace I x →L[ℝ] ℝ,
      cotangentMetricVal g x ω v = 0) :
    ω = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  have h_forall : ∀ w : TangentSpace I x, ω w = 0 := by
    intro w
    let ω' : TangentSpace I x →L[ℝ] ℝ := g.flatL x w
    have this : g.sharpL x ω' = w := by
      simp only [ω', sharpL_apply_flatL]
    have h_apply : cotangentMetricVal g x ω ω' = 0 := h ω'
    simp only [cotangentMetricVal_eq_apply_sharp] at h_apply
    rw [this] at h_apply
    exact h_apply
  exact h_forall v

@[simp]
lemma cotangentToBilinForm_nondegenerate (g : PseudoRiemannianMetric E H M n I) (x : M) :
    (cotangentToBilinForm g x).Nondegenerate := by
  constructor
  · intro ω hω
    apply cotangentMetricVal_nondegenerate g x ω
    intro v
    exact hω v
  · intro ω hω
    apply cotangentMetricVal_nondegenerate g x ω
    intro v
    rw [cotangentMetricVal_symm g x ω v]
    exact hω v

end Cotangent

end PseudoRiemannianMetric
end
end PseudoRiemannianMetric
