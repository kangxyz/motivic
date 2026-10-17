/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.OriginalGermRelativeNeighborhood
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleFieldPointInverseImage

/-! # The actual finite-type small-site neighborhood diagram of an original germ -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
namespace Motivic.SmoothSite
variable {S : Scheme.{u}} {U X : SmoothSite S} (f : U ⟶ X) (u : U.left)

/-- Finite-type small étale neighborhoods of the literal field-valued point. -/
abbrev SmallRelativeNeighborhood :=
  (MorphismProperty.Over.forget etaleSeparatedFiniteType ⊤ X.left ⋙ coyoneda.obj
    (op (Over.mk (U.left.fromSpecResidueField u ≫ f.left)))).Elements

instance : IsCofiltered (SmallRelativeNeighborhood f u) :=
  Functor.isCofiltered_elements _

namespace RelativeNisnevichNeighborhood

/-- A neighborhood in the original smooth site is separated and quasi-compact over `X`. -/
def smallObject (N : RelativeNisnevichNeighborhood f u) : FiniteEtaleSite X.left := by
  have : IsSeparated (N.obj.obj.hom ≫ X.hom) := N.property.1.2
  have : QuasiCompact (N.obj.obj.hom ≫ X.hom) := N.property.2
  exact MorphismProperty.Over.mk ⊤ N.obj.obj.hom
    ⟨⟨inferInstance, IsSeparated.of_comp N.obj.obj.hom X.hom⟩,
      QuasiCompact.of_comp N.obj.obj.hom X.hom⟩

/-- The identity on underlying schemes and residue-field points gives the small-site diagram. -/
def toSmall : RelativeNisnevichNeighborhood f u ⥤ SmallRelativeNeighborhood f u where
  obj N := Functor.elementsMk _ (smallObject f u N)
    (Over.homMk N.obj.val.left (Over.w N.obj.val))
  map {N M} a := Functor.Elements.homMk
    (MorphismProperty.Over.homMk a.hom.hom.left (MorphismProperty.Over.w a.hom.hom)) (by
      apply Over.OverMorphism.ext
      exact congrArg (fun t => t.left) a.hom.map_val)
  map_id _ := rfl
  map_comp _ _ := rfl

instance toSmall_full : (toSmall f u).Full where
  map_surjective {N M} a := by
    refine ⟨ObjectProperty.homMk (Functor.Elements.homMk
      (MorphismProperty.Over.homMk a.hom.left (MorphismProperty.Over.w a.hom)) ?_), ?_⟩
    · apply Over.OverMorphism.ext
      exact congrArg (fun t => t.left) a.map_val
    · rfl

instance toSmall_faithful : (toSmall f u).Faithful where
  map_injective h := by
    apply ObjectProperty.hom_ext
    apply Functor.Elements.hom_ext
    apply MorphismProperty.Over.Hom.ext
    exact congrArg (fun a => a.hom.left) h

/-- Every small étale neighborhood is already smooth finite type over the original base. -/
def fromSmall (N : SmallRelativeNeighborhood f u) : RelativeNisnevichNeighborhood f u :=
  ⟨Functor.elementsMk _ (Scheme.Etale.mk N.obj.hom)
    (Over.homMk N.val.left (Over.w N.val)), by
      exact (FiniteEtaleSite.toSmoothSite X).obj N.obj |>.prop⟩

/-- The two versions of each small neighborhood have the actual identity refinement. -/
def fromSmallToSmall (N : SmallRelativeNeighborhood f u) :
    (toSmall f u).obj (fromSmall f u N) ⟶ N :=
  Functor.Elements.homMk (MorphismProperty.Over.homMk (𝟙 _) (Category.id_comp _)) (by
    apply Over.OverMorphism.ext
    exact Category.comp_id _)

instance toSmall_initial : (toSmall f u).Initial :=
  Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful _
    (fun N => ⟨fromSmall f u N, ⟨fromSmallToSmall f u N⟩⟩)


/-- Forget a small pointed neighborhood to the original smooth-site object. -/
def smallForget : SmallRelativeNeighborhood f u ⥤ SmoothSite S :=
  Functor.Elements.π _ ⋙ FiniteEtaleSite.toSmoothSite X

/-- Both diagrams retain the same underlying smooth schemes and restriction maps. -/
def toSmallForgetIso : toSmall f u ⋙ smallForget f u ≅ forget f u :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

variable [IsAffine S] [Etale f.left]
  (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})

instance smallDiagramHasColimit : HasColimit ((smallForget f u).op ⋙ F) := by
  let : HasColimit ((toSmall f u).op ⋙ (smallForget f u).op ⋙ F) :=
    hasColimit_of_iso (Functor.isoWhiskerRight (NatIso.op (toSmallForgetIso f u).symm) F)
  exact Functor.Final.hasColimit_of_comp (toSmall f u).op

/-- The actual small-site field-valued neighborhood colimit is the original germ. -/
def smallOriginalFiberIso : colimit ((smallForget f u).op ⋙ F) ≅
    (nisnevichPointFiberCocone U u F).pt :=
  (Functor.Final.colimitIso (toSmall f u).op ((smallForget f u).op ⋙ F)).symm ≪≫
    HasColimit.isoOfNatIso
      (Functor.isoWhiskerRight (NatIso.op (toSmallForgetIso f u).symm) F) ≪≫
    originalFiberIso f u F

end RelativeNisnevichNeighborhood
end Motivic.SmoothSite
