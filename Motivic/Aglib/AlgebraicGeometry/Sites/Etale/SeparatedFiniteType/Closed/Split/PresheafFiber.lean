/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Closed.Split.Neighborhood

/-! # Original marked BASE colimits along a split closed immersion

The proved initiality applies to an arbitrary original presheaf, including the
positive cohomology of a whole cylinder. No sheafification, derived continuity,
or retraction on a later test neighborhood is required.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i] [IsNoetherian Y]
  (p : Y ⟶ Z) (hip : i ≫ p = 𝟙 Z)
  (K : Type u) [Field K] (c : Spec (.of K) ⟶ Z)
  (P : (EtaleSeparatedFiniteType Z)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})

/-- Initiality of literal closed BASE change on the full field-valued marks,
applied before any cohomology or homotopy cylinder is evaluated. -/
def splitClosedPresheafNeighborhoodColimitIso :
    colimit ((Functor.Elements.π
      (MorphismProperty.Over.forget etaleSeparatedFiniteType ⊤ Y ⋙
        coyoneda.obj (op (Over.mk (𝟙 _ ≫ (c ≫ i)))))).op ⋙
          (baseChange i).op ⋙ P) ≅
    colimit ((Functor.Elements.π
      (MorphismProperty.Over.forget etaleSeparatedFiniteType ⊤ Z ⋙
        coyoneda.obj (op (Over.mk (𝟙 _ ≫ c))))).op ⋙ P) := by
  let := closedNeighborhoodBaseChange_initial i K c p hip
  exact Functor.Final.colimitIso (closedNeighborhoodBaseChange i K c).op
    ((Functor.Elements.π
      (MorphismProperty.Over.forget etaleSeparatedFiniteType ⊤ Z ⋙
        coyoneda.obj (op (Over.mk (𝟙 _ ≫ c))))).op ⋙ P)

/-- The same comparison on the unchanged native Nisnevich point fibers. -/
def splitClosedPresheafPointFiberIso :
    (relativeFieldPoint (c ≫ i) K (𝟙 _)).presheafFiber.obj
        ((baseChange i).op ⋙ P) ≅
      (relativeFieldPoint c K (𝟙 _)).presheafFiber.obj P :=
  (fieldNeighborhoodFiberIso (c ≫ i) K (𝟙 _) ((baseChange i).op ⋙ P)).symm ≪≫
    splitClosedPresheafNeighborhoodColimitIso i p hip K c P ≪≫
      fieldNeighborhoodFiberIso c K (𝟙 _) P

/-- An original representative is sent to its actual full closed base change. -/
@[reassoc]
theorem splitClosedPresheafNeighborhoodColimitIso_ι
    (N : FieldValuedNeighborhood (c ≫ i) K (𝟙 _)) :
    colimit.ι _ (op N) ≫
        (splitClosedPresheafNeighborhoodColimitIso i p hip K c P).hom =
      colimit.ι ((Functor.Elements.π
        (MorphismProperty.Over.forget etaleSeparatedFiniteType ⊤ Z ⋙
          coyoneda.obj (op (Over.mk (𝟙 _ ≫ c))))).op ⋙ P)
        (op ((closedNeighborhoodBaseChange i K c).obj N)) := by
  let := closedNeighborhoodBaseChange_initial i K c p hip
  exact Functor.Final.ι_colimitIso_hom (closedNeighborhoodBaseChange i K c).op
    ((Functor.Elements.π
      (MorphismProperty.Over.forget etaleSeparatedFiniteType ⊤ Z ⋙
        coyoneda.obj (op (Over.mk (𝟙 _ ≫ c))))).op ⋙ P) (op N)

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
