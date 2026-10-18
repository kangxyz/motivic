/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleSplitClosedImageExact
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleOrdinaryEdgeMap
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleSplitClosedSupportUnit

/-! # Original ordinary cohomology under split-closed direct image

The actual edge map is the inverse exact-adjunction Ext equivalence, followed
by the original free-source comparison. No replacement cohomology theory or
supplied higher-direct-image vanishing family is used.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite
variable {Z U Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i] [IsNoetherian Y]
  (p : Y ⟶ Z) (hip : i ≫ p = 𝟙 Z)
  (j : U ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
  (hcomp : Set.range i = (Set.range j)ᶜ)
  [HasExt.{u + 1} (Sheaf (nisnevichTopology Y) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (nisnevichTopology Z) AddCommGrpCat.{u + 1})]

omit [IsClosedImmersion i] [AlgebraicGeometry.IsNoetherian Y] in
/-- The support comparison is the genuine inverse-image map on original Ext,
with the original source isomorphism. This equation is valid before imposing
split closed support hypotheses and pins subsequent naturality calculations. -/
theorem ordinarySupportComparison_eq_inverseImage (V : FiniteEtaleSite Y)
    (G : Sheaf (nisnevichTopology Y) AddCommGrpCat.{u + 1}) (n : ℕ)
    (x : SheafCohomology.H.{u + 1, u + 1, u, u + 1} (nisnevichTopology Y) G n V) :
    ordinaryEdgeMap i V ((inverseImage i).obj G) n
        (x.comp (Ext.mk₀ ((imageAdjunction i).unit.app G)) (add_zero n)) =
      (Ext.mk₀ (inverseImageSourceIso i V).inv).comp
        (x.mapExactFunctor (inverseImage i)) (zero_add n) := by
  change (Ext.mk₀ (inverseImageSourceIso i V).inv).comp
    ((imageAdjunction i).extEdge n
      (x.comp (Ext.mk₀ ((imageAdjunction i).unit.app G)) (add_zero n))) (zero_add n) = _
  erw [Adjunction.extEdge_unit]

include p hip j hcomp

/-- All-degree comparison for the original ordinary edge and the original
free-abelian representing objects on every actual test neighborhood. -/
theorem splitClosedOrdinaryEdgeMap_bijective (V : FiniteEtaleSite Y)
    (F : Sheaf (nisnevichTopology Z) AddCommGrpCat.{u + 1}) (n : ℕ) :
    Function.Bijective (ordinaryEdgeMap i V F n) := by
  let := splitClosedDirectImage_preservesFiniteColimits i p hip j hcomp
  let e := (((extFunctor n).mapIso (inverseImageSourceIso i V).symm.op).app F)
  have he : Function.Bijective e.hom := ConcreteCategory.bijective_of_isIso e.hom
  exact he.comp (imageAdjunction i).extEquiv.symm.bijective

/-- Actual ordinary support comparison: coefficient change by the original
unit, followed by the original edge map, is bijective on every test object. -/
theorem splitClosedSupportCohomology_bijective (V : FiniteEtaleSite Y)
    (G : Sheaf (nisnevichTopology Y) AddCommGrpCat.{u + 1})
    (hG : IsZero ((inverseImage j).obj G)) (n : ℕ) :
    Function.Bijective (fun x : SheafCohomology.H.{u + 1, u + 1, u, u + 1}
        (nisnevichTopology Y) G n V =>
      ordinaryEdgeMap i V ((inverseImage i).obj G) n
        (x.comp (Ext.mk₀ ((imageAdjunction i).unit.app G)) (add_zero n))) := by
  let := splitClosed_support_unit_isIso i p hip j hcomp G hG
  let e := ((extFunctor n).obj (op
      (Hypercohomology.freeAbelianSheaf.{u + 1, u, u + 1} (nisnevichTopology Y) V))).mapIso
        (asIso ((imageAdjunction i).unit.app G))
  exact (splitClosedOrdinaryEdgeMap_bijective i p hip j hcomp V ((inverseImage i).obj G) n).comp
    (ConcreteCategory.bijective_of_isIso e.hom)

end Motivic.FiniteEtaleSite
