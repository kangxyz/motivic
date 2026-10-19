/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Closed.Split.Cohomology
public import Motivic.Aglib.CategoryTheory.Sites.RestrictionSourceNaturality

/-! # Test-object naturality of the original ordinary support comparison

The immersion and coefficient sheaf remain fixed. The original adjunction unit
and ordinary edge map commute with restriction along an actual small-site arrow.
Split closed support supplies bijectivity in the imported comparison theorem;
the naturality equation itself needs no split or support hypotheses.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open _root_.CategoryTheory.Sheaf
variable {Z Y : Scheme.{u}} (i : Z ⟶ Y)

/-- Inverse original free-source comparison is natural in the actual test object. -/
theorem inverseImageSourceIso_inv_naturality {V W : EtaleSeparatedFiniteType Y} (a : V ⟶ W) :
    (inverseImageSourceIso i V).inv ≫
        (inverseImage i).map ((Hypercohomology.freeAbelianSheafFunctor
          (nisnevichTopology Y)).map a) =
      (Hypercohomology.freeAbelianSheafFunctor (nisnevichTopology Z)).map
          ((baseChange i).map a) ≫ (inverseImageSourceIso i W).inv := by
  have hs := Hypercohomology.restrictionSourceIso_naturality.{u + 1, u, u + 1, u + 1}
    (nisnevichTopology Y) (nisnevichTopology Z) (baseChange i) a
  change (inverseImage i).map ((Hypercohomology.freeAbelianSheafFunctor
      (nisnevichTopology Y)).map a) ≫ (inverseImageSourceIso i W).hom =
    (inverseImageSourceIso i V).hom ≫
      (Hypercohomology.freeAbelianSheafFunctor (nisnevichTopology Z)).map
        ((baseChange i).map a) at hs
  apply (Iso.inv_comp_eq _).2
  rw [← Category.assoc, ← hs, Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable [HasExt.{u + 1} (Sheaf (nisnevichTopology Y) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (nisnevichTopology Z) AddCommGrpCat.{u + 1})]

/-- The literal unit followed by the ordinary edge commutes with actual restriction.
The fixed split-closed instance can therefore be used with its proved bijectivity
without replacing the original support comparison by an abstract family. -/
theorem ordinarySupportComparison_naturality {V W : EtaleSeparatedFiniteType Y} (a : V ⟶ W)
    (G : Sheaf (nisnevichTopology Y) AddCommGrpCat.{u + 1}) (n : ℕ)
    (x : LargeCohomology.H.{u + 1, u + 1, u, u + 1} (nisnevichTopology Y) G n W) :
    ordinaryEdgeMap i V ((inverseImage i).obj G) n
        (((LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
          (nisnevichTopology Y) G n).map a.op x).comp
          (Ext.mk₀ ((imageAdjunction i).unit.app G)) (add_zero n)) =
      (LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (nisnevichTopology Z) ((inverseImage i).obj G) n).map
        ((baseChange i).map a).op
        (ordinaryEdgeMap i W ((inverseImage i).obj G) n
          (x.comp (Ext.mk₀ ((imageAdjunction i).unit.app G)) (add_zero n))) := by
  rw [ordinarySupportComparison_eq_inverseImage, ordinarySupportComparison_eq_inverseImage,
    LargeCohomology.restriction_apply, LargeCohomology.restriction_apply,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  rw [← Ext.comp_assoc _ _ _ (zero_add 0) (zero_add n) (by omega), Ext.mk₀_comp_mk₀,
    ← Ext.comp_assoc _ _ _ (zero_add 0) (zero_add n) (by omega), Ext.mk₀_comp_mk₀]
  rw [inverseImageSourceIso_inv_naturality]

/-- The original support comparison as a natural map of ordinary cohomology presheaves. -/
def ordinarySupportComparison
    (G : Sheaf (nisnevichTopology Y) AddCommGrpCat.{u + 1}) (n : ℕ) :
    LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1} (nisnevichTopology Y) G n ⟶
      (baseChange i).op ⋙
        LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
          (nisnevichTopology Z) ((inverseImage i).obj G) n where
  app V := AddCommGrpCat.ofHom
    { toFun := fun x => ordinaryEdgeMap i V.unop ((inverseImage i).obj G) n
        (x.comp (Ext.mk₀ ((imageAdjunction i).unit.app G)) (add_zero n))
      map_zero' := by simp
      map_add' := by intros; simp }
  naturality V W a := by
    ext x
    exact ordinarySupportComparison_naturality i a.unop G n x

/-- The natural support comparison has exactly the original unit-then-edge components. -/
theorem ordinarySupportComparison_app_apply
    (G : Sheaf (nisnevichTopology Y) AddCommGrpCat.{u + 1}) (n : ℕ)
    (V : EtaleSeparatedFiniteType Y)
    (x : LargeCohomology.H.{u + 1, u + 1, u, u + 1} (nisnevichTopology Y) G n V) :
    (ordinarySupportComparison i G n).app (Opposite.op V) x =
      ordinaryEdgeMap i V ((inverseImage i).obj G) n
        (x.comp (Ext.mk₀ ((imageAdjunction i).unit.app G)) (add_zero n)) := rfl

variable [IsClosedImmersion i] [IsNoetherian Y]
  (p : Y ⟶ Z) (hip : i ≫ p = 𝟙 Z)
  {U : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
  (hcomp : Set.range i = (Set.range j)ᶜ)
  (G : Sheaf (nisnevichTopology Y) AddCommGrpCat.{u + 1})
  (hG : IsZero ((inverseImage j).obj G)) (n : ℕ)

include p hip j hcomp hG in
/-- Bijectivity applies to the literal components of the original natural map. -/
theorem ordinarySupportComparison_app_bijective (V : (EtaleSeparatedFiniteType Y)ᵒᵖ) :
    Function.Bijective ((ordinarySupportComparison i G n).app V) := by
  exact splitClosedSupportCohomology_bijective i p hip j hcomp V.unop G hG n

include p hip j hcomp hG in
/-- Each original support comparison component is an isomorphism under split support. -/
theorem ordinarySupportComparison_app_isIso (V : (EtaleSeparatedFiniteType Y)ᵒᵖ) :
    IsIso ((ordinarySupportComparison i G n).app V) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    (ordinarySupportComparison_app_bijective i p hip j hcomp G hG n V)

include p hip j hcomp hG in
/-- The original support comparison is naturally invertible under split support. -/
theorem ordinarySupportComparison_isIso : IsIso (ordinarySupportComparison i G n) := by
  let := fun V => ordinarySupportComparison_app_isIso i p hip j hcomp G hG n V
  exact NatIso.isIso_of_isIso_app (ordinarySupportComparison i G n)

/-- Split closed support makes the original natural comparison an isomorphism. -/
def splitClosedSupportCohomologyIso :
    LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1} (nisnevichTopology Y) G n ≅
      (baseChange i).op ⋙
        LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
          (nisnevichTopology Z) ((inverseImage i).obj G) n := by
  letI := ordinarySupportComparison_isIso i p hip j hcomp G hG n
  exact asIso (ordinarySupportComparison i G n)

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
