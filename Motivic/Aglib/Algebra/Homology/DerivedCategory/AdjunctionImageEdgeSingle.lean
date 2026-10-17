/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.DerivedCategory.AdjunctionImageEdge

/-! # Identification of the actual image edge on single complexes -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe w₁ w₂ v₁ v₂ u₁ u₂
namespace CategoryTheory.Adjunction
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ R) (Y : D)

/-- The actual counit on degree-zero single complexes. -/
def imageEdgeCounit :
    L.mapDerivedCategory.obj ((DerivedCategory.singleFunctor C 0).obj (R.obj Y)) ⟶
      (DerivedCategory.singleFunctor D 0).obj Y :=
  (L.mapDerivedCategorySingleFunctor 0).hom.app (R.obj Y) ≫
    (DerivedCategory.singleFunctor D 0).map (adj.counit.app Y)

omit [HasDerivedCategory C] [HasDerivedCategory D]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] in
/-- The chain-level single comparison intertwines the actual degreewise counit. -/
theorem single_counit :
    (L.mapHomologicalComplex (.up ℤ)).map
      ((singleMapHomologicalComplex R (.up ℤ) 0).inv.app Y) ≫
        (NatTrans.mapHomologicalComplex adj.counit (.up ℤ)).app
          ((CochainComplex.singleFunctor D 0).obj Y) =
      (singleMapHomologicalComplex L (.up ℤ) 0).hom.app (R.obj Y) ≫
        (CochainComplex.singleFunctor D 0).map (adj.counit.app Y) := by
  apply to_single_hom_ext
  simp only [comp_f, Functor.mapHomologicalComplex_map_f,
    singleMapHomologicalComplex_inv_app_self, singleMapHomologicalComplex_hom_app_self,
    CochainComplex.singleFunctor, single_map_f_self, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_assoc]
  exact congrArg (L.map (singleObjXSelf (.up ℤ) 0 (R.obj Y)).hom ≫ ·)
    (adj.counit.naturality (singleObjXSelf (.up ℤ) 0 Y).inv)

/-- The genuine cone edge equals the exact-functor map followed by the original single counit. -/
theorem derivedImageEdge_eq (K : CochainComplex C ℤ)
    (x : DerivedCategory.Q.obj K ⟶
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj (R.obj Y))) :
    adj.derivedImageEdge K x =
      L.mapDerivedCategoryFactors.inv.app K ≫
        L.mapDerivedCategory.map x ≫ adj.imageEdgeCounit Y := by
  dsimp only [derivedImageEdge, imageEdgeCounit]
  rw [adj.single_counit]
  simp [Functor.mapDerivedCategorySingleFunctor,
    DerivedCategory.singleFunctorIsoCompQ, CochainComplex.singleFunctor]

end CategoryTheory.Adjunction
