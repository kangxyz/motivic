/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleSplitClosedNeighborhood
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleImageExact

/-! # The actual direct-image point fiber for a split closed immersion

This comparison uses literal closed base change on the original marked
neighborhood index. In particular, it compares the original direct image,
not a replacement support functor or a new cohomology theory.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite

variable {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i] [IsNoetherian Y]
  (p : Y ⟶ Z) (hip : i ≫ p = 𝟙 Z)
  (K : Type u) [Field K] (c : Spec (.of K) ⟶ Z)

/-- The cofinality comparison on the actual underlying neighborhood colimits. -/
def splitClosedNeighborhoodColimitIso
    (F : Sheaf (nisnevichTopology Z) AddCommGrpCat.{u + 1}) :
    colimit ((Functor.Elements.π
      (MorphismProperty.Over.forget etaleSeparatedFiniteType ⊤ Y ⋙
        coyoneda.obj (op (Over.mk (𝟙 _ ≫ (c ≫ i)))))).op ⋙
          ((directImage i).obj F).obj) ≅
    colimit ((Functor.Elements.π
      (MorphismProperty.Over.forget etaleSeparatedFiniteType ⊤ Z ⋙
        coyoneda.obj (op (Over.mk (𝟙 _ ≫ c))))).op ⋙ F.obj) := by
  letI := closedNeighborhoodBaseChange_initial i K c p hip
  exact Functor.Final.colimitIso (closedNeighborhoodBaseChange i K c).op
    ((Functor.Elements.π
      (MorphismProperty.Over.forget etaleSeparatedFiniteType ⊤ Z ⋙
        coyoneda.obj (op (Over.mk (𝟙 _ ≫ c))))).op ⋙ F.obj)

/-- The closed-supported direct-image fiber is the actual source point fiber,
with the same entire coefficient-field-valued marking. -/
def splitClosedDirectImagePointFiberIso
    (F : Sheaf (nisnevichTopology Z) AddCommGrpCat.{u + 1}) :
    (relativeFieldPoint (c ≫ i) K (𝟙 _)).sheafFiber.obj ((directImage i).obj F) ≅
      (relativeFieldPoint c K (𝟙 _)).sheafFiber.obj F :=
  (fieldNeighborhoodFiberIso (c ≫ i) K (𝟙 _) ((directImage i).obj F).obj).symm ≪≫
    splitClosedNeighborhoodColimitIso i p hip K c F ≪≫
      fieldNeighborhoodFiberIso c K (𝟙 _) F.obj

/-- Every original representative is sent by the actual closed base-change
object and its unchanged full mark. This pins the comparison map. -/
@[reassoc]
theorem splitClosedNeighborhoodColimitIso_ι
    (F : Sheaf (nisnevichTopology Z) AddCommGrpCat.{u + 1})
    (N : FieldValuedNeighborhood (c ≫ i) K (𝟙 _)) :
    colimit.ι _ (op N) ≫ (splitClosedNeighborhoodColimitIso i p hip K c F).hom =
      colimit.ι ((Functor.Elements.π
        (MorphismProperty.Over.forget etaleSeparatedFiniteType ⊤ Z ⋙
          coyoneda.obj (op (Over.mk (𝟙 _ ≫ c))))).op ⋙ F.obj)
        (op ((closedNeighborhoodBaseChange i K c).obj N)) := by
  let := closedNeighborhoodBaseChange_initial i K c p hip
  exact Functor.Final.ι_colimitIso_hom (closedNeighborhoodBaseChange i K c).op
    ((Functor.Elements.π
      (MorphismProperty.Over.forget etaleSeparatedFiniteType ⊤ Z ⋙
        coyoneda.obj (op (Over.mk (𝟙 _ ≫ c))))).op ⋙ F.obj) (op N)

end Motivic.FiniteEtaleSite
