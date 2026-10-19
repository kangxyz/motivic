/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Motivic.Aglib.AlgebraicGeometry.Graph.CommonStalkTransport
public import Motivic.Aglib.AlgebraicGeometry.Cycles.ResidueDegree

/-!
# Whole affine inverse-image charts for a finite morphism

An affine target open gives the entire affine inverse image, a finite coordinate
ring map and a bijection with every original source point in the fiber. The
literal chart square gives the actual stalk scalar and remaining-list squares
and preserves scheme residue degrees. No coefficient sheaf is presumed.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.FiniteAffineChart

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
  {U : Y.Opens} (hU : IsAffineOpen U)

/-- The coordinate morphism of the whole finite affine inverse image. -/
abbrev coordinateMap := Spec.map (f.app U)

/-- The actual open chart includes the entire inverse image of the target open. -/
abbrev sourceChart := (hU.preimage f).fromSpec

include hU in
/-- The coordinate ring map of this whole inverse image is finite. -/
theorem coordinateRingMap_finite : (f.app U).hom.Finite := f.finite_app U hU

/-- The Spec coordinate map and the original finite map form the actual chart square. -/
@[reassoc] theorem chart_square :
    coordinateMap f (U := U) ≫ hU.fromSpec = sourceChart f hU ≫ f := by
  simpa only [coordinateMap, sourceChart, Scheme.Hom.app_eq_appLE] using
    IsAffineOpen.SpecMap_appLE_fromSpec f hU (hU.preimage f) le_rfl

/-- Pointwise equality in the actual whole-inverse-image chart square. -/
theorem chart_point (q : Spec Γ(X, f ⁻¹ᵁ U)) :
    hU.fromSpec (coordinateMap f q) = f (sourceChart f hU q) :=
  congrArg (fun m => m q) (chart_square f hU)

/-- The coordinate chart never discards a branch of an original target fiber. -/
def fiberMap (p : Spec Γ(Y, U)) :
    {q : Spec Γ(X, f ⁻¹ᵁ U) // coordinateMap f q = p} →
      {x : X // f x = hU.fromSpec p} := fun q =>
  ⟨sourceChart f hU q.1, (chart_point f hU q.1).symm.trans (congrArg hU.fromSpec q.2)⟩

/-- All source points over the target chart point arise uniquely in the whole chart. -/
theorem fiberMap_bijective (p : Spec Γ(Y, U)) : Function.Bijective (fiberMap f hU p) := by
  constructor
  · intro q r h
    apply Subtype.ext
    have he : sourceChart f hU q.1 = sourceChart f hU r.1 :=
      congrArg (fun z : {x : X // f x = hU.fromSpec p} => z.1) h
    have hi : Function.Injective (sourceChart f hU) :=
      (sourceChart f hU).isOpenEmbedding.injective
    exact hi he
  · intro x
    have hp : hU.fromSpec p ∈ U := by
      change hU.fromSpec p ∈ (U : Set Y)
      rw [← hU.range_fromSpec]
      exact ⟨p, rfl⟩
    have hx : x.1 ∈ f ⁻¹ᵁ U := by
      change f x.1 ∈ U
      rw [x.2]
      exact hp
    have hx' : x.1 ∈ Set.range (sourceChart f hU) :=
      (hU.preimage f).range_fromSpec.symm ▸ hx
    obtain ⟨q, hq⟩ := hx'
    have he : coordinateMap f q = p := by
      apply hU.fromSpec.isOpenEmbedding.injective
      rw [chart_point f hU, hq, x.2]
    exact ⟨⟨q, he⟩, Subtype.ext hq⟩

/-- The full coordinate fiber is equivalent to the original geometric fiber. -/
def fiberEquiv (p : Spec Γ(Y, U)) :
    {q : Spec Γ(X, f ⁻¹ᵁ U) // coordinateMap f q = p} ≃
      {x : X // f x = hU.fromSpec p} :=
  Equiv.ofBijective (fiberMap f hU p) (fiberMap_bijective f hU p)

/-- The fiber equivalence is the actual source open-chart map on points. -/
@[simp] theorem fiberEquiv_apply_val (p : Spec Γ(Y, U))
    (q : {q : Spec Γ(X, f ⁻¹ᵁ U) // coordinateMap f q = p}) :
    (fiberEquiv f hU p q).1 = sourceChart f hU q.1 := rfl

/-- Canonical scalar map from the target chart's original stalk to the source stalk. -/
def originalStalkMap (q : Spec Γ(X, f ⁻¹ᵁ U)) :
    Y.presheaf.stalk (hU.fromSpec (coordinateMap f q)) ⟶
      X.presheaf.stalk (sourceChart f hU q) :=
  Graph.alignedStalkMap f (sourceChart f hU q) (hU.fromSpec (coordinateMap f q))
    (chart_point f hU q)

/-- The actual open chart identifies source structure stalks by a ring isomorphism. -/
def sourceStalkIso (q : Spec Γ(X, f ⁻¹ᵁ U)) :
    X.presheaf.stalk (sourceChart f hU q) ≅ (Spec Γ(X, f ⁻¹ᵁ U)).presheaf.stalk q :=
  asIso ((sourceChart f hU).stalkMap q)

/-- The actual open chart identifies target structure stalks by a ring isomorphism. -/
def targetStalkIso (p : Spec Γ(Y, U)) :
    Y.presheaf.stalk (hU.fromSpec p) ≅ (Spec Γ(Y, U)).presheaf.stalk p :=
  asIso (hU.fromSpec.stalkMap p)

/-- The whole affine presentation preserves the actual finite-map scalar action. -/
@[reassoc] theorem stalk_square (q : Spec Γ(X, f ⁻¹ᵁ U)) :
    originalStalkMap f hU q ≫ (sourceStalkIso f hU q).hom =
      (targetStalkIso hU (coordinateMap f q)).hom ≫ (coordinateMap f).stalkMap q :=
  by
    simpa only [originalStalkMap, sourceStalkIso, targetStalkIso, asIso_hom,
      Graph.alignedStalkMap_rfl] using
      Graph.alignedStalkMap_naturality f (coordinateMap f) (sourceChart f hU) hU.fromSpec
        (chart_square f hU) q (coordinateMap f q) rfl (chart_point f hU q)

/-- Target chart stalk transport with the target point literally written as f(x). -/
def targetStalkIsoAtSource (q : Spec Γ(X, f ⁻¹ᵁ U)) :
    Y.presheaf.stalk (f (sourceChart f hU q)) ≅
      (Spec Γ(Y, U)).presheaf.stalk (coordinateMap f q) :=
  Y.presheaf.stalkCongr (.of_eq (chart_point f hU q).symm) ≪≫
    targetStalkIso hU (coordinateMap f q)

/-- The scalar square starts with the literal original finite-map stalk map. -/
@[reassoc] theorem stalk_square_at_source (q : Spec Γ(X, f ⁻¹ᵁ U)) :
    f.stalkMap (sourceChart f hU q) ≫ (sourceStalkIso f hU q).hom =
      (targetStalkIsoAtSource f hU q).hom ≫ (coordinateMap f).stalkMap q := by
  have he := congrArg (fun k =>
    (Y.presheaf.stalkCongr (.of_eq (chart_point f hU q))).inv ≫ k) (stalk_square f hU q)
  simpa [originalStalkMap, Graph.alignedStalkMap, targetStalkIsoAtSource,
    Category.assoc] using he


/-- The same literal target-stalk list is transported through both scalar paths. -/
theorem list_square (q : Spec Γ(X, f ⁻¹ᵁ U))
    (s : List (Y.presheaf.stalk (hU.fromSpec (coordinateMap f q)))) :
    (s.map (originalStalkMap f hU q).hom).map (sourceStalkIso f hU q).hom.hom =
      (s.map (targetStalkIso hU (coordinateMap f q)).hom.hom).map
        ((coordinateMap f).stalkMap q).hom := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro a _
  exact ConcreteCategory.congr_hom (stalk_square f hU q) a

/-- Literal scheme residue degrees are unchanged by the whole open-chart presentation. -/
theorem residueDegree_eq (q : Spec Γ(X, f ⁻¹ᵁ U)) :
    (coordinateMap f).residueDegree q = f.residueDegree (sourceChart f hU q) := by
  have he := congrArg (fun m => m.residueDegree q) (chart_square f hU)
  simpa only [residueDegree_comp, residueDegree_of_surjectiveOnStalks,
    one_mul, mul_one] using he

/-- Every original target point admits an affine target chart point. The whole
inverse image is then supplied by the finite-map construction above. -/
theorem exists_targetChart (y : Y) :
    ∃ (U : Y.Opens) (hU : IsAffineOpen U) (p : Spec Γ(Y, U)), hU.fromSpec p = y := by
  obtain ⟨U, hU, hy, _⟩ := exists_isAffineOpen_mem_and_subset
    (U := (⊤ : Y.Opens)) (x := y) (by trivial)
  have hy' : y ∈ Set.range hU.fromSpec := hU.range_fromSpec.symm ▸ hy
  obtain ⟨p, hp⟩ := hy'
  exact ⟨U, hU, p, hp⟩

end AlgebraicGeometry.Scheme.Hom.FiniteAffineChart
