/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtalePersistentMarkedSection
public import Mathlib.CategoryTheory.Filtered.Final

/-! # Actual marked neighborhoods over an étale test object

The comparison factors through the slice over the original marked test object.
Forgetting that slice is initial. In particular, no fullness assertion is made
about the direct composition functor between the two neighborhood categories.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite
variable {S : Scheme.{u}}

/-- Composition of actual small étale objects does not change their underlying schemes or arrows. -/
def composeObjectFunctor (V : FiniteEtaleSite S) :
    FiniteEtaleSite V.left ⥤ FiniteEtaleSite S where
  obj := composeObject V
  map := composeObjectMap V

variable (V : FiniteEtaleSite S) (K : Type u) [Field K] (b : Spec (.of K) ⟶ V.left)

/-- The original test object with its given field-valued marking. -/
def fieldNeighborhoodMark : FieldValuedNeighborhood (b ≫ V.hom) K (𝟙 _) :=
  Functor.elementsMk _ V (Over.homMk b (by simp))

/-- Compose structural maps while retaining the original field-valued marking. -/
def fieldNeighborhoodCompose :
    FieldValuedNeighborhood b K (𝟙 _) ⥤
      FieldValuedNeighborhood (b ≫ V.hom) K (𝟙 _) where
  obj N := Functor.elementsMk _ (composeObject V N.obj)
    (Over.homMk N.val.left (by
      change N.val.left ≫ (N.obj.hom ≫ V.hom) = 𝟙 _ ≫ (b ≫ V.hom)
      have hn : N.val.left ≫ N.obj.hom = 𝟙 _ ≫ b := Over.w N.val
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun t => t ≫ V.hom) hn).trans (Category.assoc _ _ _))))
  map {N M} f := Functor.Elements.homMk (composeObjectMap V f.hom) (by
    apply Over.OverMorphism.ext
    exact congrArg (fun a => a.left) f.map_val)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The marking provides the actual arrow to the distinguished marked test object. -/
def fieldNeighborhoodProjection (N : FieldValuedNeighborhood b K (𝟙 _)) :
    (fieldNeighborhoodCompose V K b).obj N ⟶ fieldNeighborhoodMark V K b :=
  Functor.Elements.homMk (composeObjectProjection V N.obj) (by
    apply Over.OverMorphism.ext
    exact (Over.w N.val).trans (Category.id_comp b))

/-- Neighborhoods over the test object factor through its marked slice. -/
def fieldNeighborhoodToOver :
    FieldValuedNeighborhood b K (𝟙 _) ⥤ Over (fieldNeighborhoodMark V K b) where
  obj N := Over.mk (fieldNeighborhoodProjection V K b N)
  map f := Over.homMk ((fieldNeighborhoodCompose V K b).map f) (by
    apply Functor.Elements.hom_ext
    apply MorphismProperty.Over.Hom.ext
    exact MorphismProperty.Over.w f.hom)

instance fieldNeighborhoodToOver_faithful : (fieldNeighborhoodToOver V K b).Faithful where
  map_injective h := Functor.Elements.hom_ext (MorphismProperty.Over.Hom.ext
    (congrArg (fun a => a.left.hom.left) h))

instance fieldNeighborhoodToOver_full : (fieldNeighborhoodToOver V K b).Full where
  map_surjective {N M} a := by
    have ha : a.left.hom.left ≫ M.obj.hom = N.obj.hom :=
      congrArg (fun f => f.hom.left) (Over.w a)
    let f : N.obj ⟶ M.obj := MorphismProperty.Over.homMk a.left.hom.left ha
    have hf : N.val ≫ (MorphismProperty.Over.forget _ _ V.left).map f = M.val := by
      apply Over.OverMorphism.ext
      exact congrArg (fun f => f.left) a.left.map_val
    refine ⟨Functor.Elements.homMk f hf, ?_⟩
    apply Over.OverMorphism.ext
    apply Functor.Elements.hom_ext
    apply MorphismProperty.Over.Hom.ext
    rfl

/-- Every marked arrow into the original test object comes from an actual small
étale neighborhood over that test object. -/
instance fieldNeighborhoodToOver_initial : (fieldNeighborhoodToOver V K b).Initial := by
  apply Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful
  intro A
  let W := arrowObject A.hom.hom
  have ha : A.left.val.left ≫ W.hom = b :=
    congrArg (fun a => a.left) A.hom.map_val
  let N : FieldValuedNeighborhood b K (𝟙 _) :=
    Functor.elementsMk _ W (Over.homMk A.left.val.left (by simpa using ha))
  let f : composeObject V W ⟶ A.left.obj := MorphismProperty.Over.homMk (𝟙 _)
    (by
      change 𝟙 _ ≫ A.left.obj.hom = A.hom.hom.left ≫ V.hom
      exact (Category.id_comp _).trans (MorphismProperty.Over.w A.hom.hom).symm)
  let g : (fieldNeighborhoodCompose V K b).obj N ⟶ A.left :=
    Functor.Elements.homMk f (by
      apply Over.OverMorphism.ext
      exact Category.comp_id _)
  refine ⟨N, ⟨Over.homMk g ?_⟩⟩
  apply Functor.Elements.hom_ext
  apply MorphismProperty.Over.Hom.ext
  exact Category.id_comp _

/-- Actual neighborhoods of the marked test object are initial among neighborhoods
of the same field-valued point on the original base. -/
instance fieldNeighborhoodCompose_initial : (fieldNeighborhoodCompose V K b).Initial :=
  inferInstanceAs ((fieldNeighborhoodToOver V K b ⋙
    Over.forget (fieldNeighborhoodMark V K b)).Initial)

/-- Restriction to the actual marked test object computes exactly the original
field-valued point fiber, for any presheaf. -/
def fieldPointComposeFiberIso (P : (FiniteEtaleSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (relativeFieldPoint b K (𝟙 _)).presheafFiber.obj ((composeObjectFunctor V).op ⋙ P) ≅
      (relativeFieldPoint (b ≫ V.hom) K (𝟙 _)).presheafFiber.obj P :=
  (fieldNeighborhoodFiberIso b K (𝟙 _) ((composeObjectFunctor V).op ⋙ P)).symm ≪≫
    Functor.Final.colimitIso (fieldNeighborhoodCompose V K b).op
      ((Functor.Elements.π _).op ⋙ P) ≪≫
        fieldNeighborhoodFiberIso (b ≫ V.hom) K (𝟙 _) P

/-- The same comparison for a residue point of every actual small test object.
The residue field is that of the test point, not just its image in the base. -/
def markedResidueFiberIso (z : V.left)
    (P : (FiniteEtaleSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (residuePoint V.left z).presheafFiber.obj ((composeObjectFunctor V).op ⋙ P) ≅
      (markedResiduePoint V z).presheafFiber.obj P :=
  fieldPointComposeFiberIso V (V.left.residueField z) (V.left.fromSpecResidueField z) P

/-- The literal field-neighborhood comparison sends an original native
representative to the unchanged literal marked neighborhood. -/
@[reassoc]
theorem toPresheafFiber_fieldNeighborhoodFiberIso_inv
    (P : (FiniteEtaleSite V.left)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (W : FiniteEtaleSite V.left) (a : (relativeFieldPoint b K (𝟙 _)).fiber.obj W) :
    (relativeFieldPoint b K (𝟙 _)).toPresheafFiber W a P ≫
        (fieldNeighborhoodFiberIso b K (𝟙 _) P).inv =
      colimit.ι ((Functor.Elements.π _).op ⋙ P)
        (op ((pointElementsToNeighborhood b K (𝟙 _)).obj (Functor.elementsMk _ W a))) :=
  Functor.Final.ι_colimitIso_hom (pointElementsToNeighborhood b K (𝟙 _)).op
    ((Functor.Elements.π _).op ⋙ P) (op (Functor.elementsMk _ W a))

/-- An original literal marking, composed to the base, determines the target
native point-fiber element without changing its field-valued map. -/
def fieldPointComposeElement (W : FiniteEtaleSite V.left)
    (a : (relativeFieldPoint b K (𝟙 _)).fiber.obj W) :
    (relativeFieldPoint (b ≫ V.hom) K (𝟙 _)).fiber.obj (composeObject V W) :=
  (relativeFieldPointFiberEquiv (b ≫ V.hom) K (𝟙 _) (composeObject V W)).symm
    (((fieldNeighborhoodCompose V K b).obj
      ((pointElementsToNeighborhood b K (𝟙 _)).obj (Functor.elementsMk _ W a))).val)

/-- Representative-level compatibility with the original point-fiber maps. -/
@[reassoc]
theorem toPresheafFiber_fieldPointComposeFiberIso_hom
    (P : (FiniteEtaleSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (W : FiniteEtaleSite V.left) (a : (relativeFieldPoint b K (𝟙 _)).fiber.obj W) :
    (relativeFieldPoint b K (𝟙 _)).toPresheafFiber W a
        ((composeObjectFunctor V).op ⋙ P) ≫ (fieldPointComposeFiberIso V K b P).hom =
      (relativeFieldPoint (b ≫ V.hom) K (𝟙 _)).toPresheafFiber
        (composeObject V W) (fieldPointComposeElement V K b W a) P := by
  let N₀ := (pointElementsToNeighborhood b K (𝟙 _)).obj (Functor.elementsMk _ W a)
  let N := (fieldNeighborhoodCompose V K b).obj N₀
  let D := (Functor.Elements.π
    (MorphismProperty.Over.forget etaleSeparatedFiniteType ⊤ S ⋙
      coyoneda.obj (op (Over.mk (𝟙 _ ≫ (b ≫ V.hom)))))).op ⋙ P
  dsimp only [fieldPointComposeFiberIso, Iso.trans_hom, Iso.symm_hom]
  rw [toPresheafFiber_fieldNeighborhoodFiberIso_inv_assoc]
  have h₁ := Functor.Final.ι_colimitIso_hom (fieldNeighborhoodCompose V K b).op D (op N₀)
  have h₂ := Functor.Final.ι_colimitIso_inv
    (pointElementsToNeighborhood (b ≫ V.hom) K (𝟙 _)).op D
      (op (Functor.elementsMk _ (composeObject V W) (fieldPointComposeElement V K b W a)))
  have hι : colimit.ι D
      ((pointElementsToNeighborhood (b ≫ V.hom) K (𝟙 _)).op.obj
        (op (Functor.elementsMk _ (composeObject V W) (fieldPointComposeElement V K b W a)))) =
        colimit.ι D (op N) :=
    congrArg (fun t : Over.mk (𝟙 _ ≫ (b ≫ V.hom)) ⟶
        (MorphismProperty.Over.forget etaleSeparatedFiniteType ⊤ S).obj (composeObject V W) =>
      (show P.obj (op (composeObject V W)) ⟶ colimit D from
        colimit.ι D (op (Functor.elementsMk
          (MorphismProperty.Over.forget etaleSeparatedFiniteType ⊤ S ⋙
            coyoneda.obj (op (Over.mk (𝟙 _ ≫ (b ≫ V.hom))))) (composeObject V W) t))))
      ((relativeFieldPointFiberEquiv (b ≫ V.hom) K (𝟙 _)
        (composeObject V W)).apply_symm_apply N.val)
  have h₂' : colimit.ι D (op N) ≫
      (fieldNeighborhoodFiberIso (b ≫ V.hom) K (𝟙 _) P).hom =
        (relativeFieldPoint (b ≫ V.hom) K (𝟙 _)).toPresheafFiber
          (composeObject V W) (fieldPointComposeElement V K b W a) P :=
    (congrArg (fun t => t ≫
      (fieldNeighborhoodFiberIso (b ≫ V.hom) K (𝟙 _) P).hom) hι.symm).trans h₂
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ (fieldNeighborhoodFiberIso (b ≫ V.hom) K (𝟙 _) P).hom) h₁).trans h₂')

end Motivic.FiniteEtaleSite
