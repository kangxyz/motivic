module

public import Motivic.Cohomology.A1.ContractionBoundaryGeometry

/-! # The canonical original-contraction map to the actual boundary sheaf -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Motivic.FiniteEtaleSite

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  (F : SheafWithTransfers.{u + 1} k)

/-- The actual boundary sheaf of the zero section in the literal affine-line cylinder. -/
abbrev zeroSectionBoundary := boundaryCokernel ((SheafWithTransfers.toSheaf k).obj F)
  (SmoothSite.contractionOpen (.of k) X) (SmoothSite.a1Section (.of k) X 0)

/-- The Laurent projection is a natural map of the actual smooth neighborhood functors. -/
def puncturedProjectionNat :
    puncturedNeighborhood X ⋙ toSmoothSite (SmoothSite.torusCylinder (.of k) X) ⟶
      toSmoothSite X ⋙ SmoothSite.parameterProduct (SmoothSite.torus (.of k)) where
  app := puncturedProjection X
  naturality _ _ f := puncturedProjection_naturality X f

/-- Laurent sections map to the actual ambient sheaf cokernel on cylinder neighborhoods. -/
def laurentToAmbientCokernel :
    (toSmoothSite X).op ⋙ (PresheafWithTransfers.toPresheaf k).obj
      (PresheafWithTransfers.torusSections F.obj) ⟶
    (cylinderNeighborhood X).op ⋙
      (boundaryAmbientCokernel ((SheafWithTransfers.toSheaf k).obj F)
        (SmoothSite.contractionOpen (.of k) X)).obj :=
  Functor.whiskerLeft (toSmoothSite X).op
      (PresheafWithTransfers.withParameterUnderlyingIso F.obj (SmoothSite.torus (.of k))).hom ≫
    Functor.whiskerRight (NatTrans.op (puncturedProjectionNat X))
      ((SheafWithTransfers.toSheaf k).obj F).obj ≫
    Functor.whiskerLeft (cylinderNeighborhood X).op
      (cokernel.π (restrictionToDirectImage ((SheafWithTransfers.toSheaf k).obj F)
        (SmoothSite.contractionOpen (.of k) X))).hom

/-- From the ambient cokernel on cylinder neighborhoods to its true closed inverse image. -/
def ambientCokernelToBoundary :
    (cylinderNeighborhood X).op ⋙
      (boundaryAmbientCokernel ((SheafWithTransfers.toSheaf k).obj F)
        (SmoothSite.contractionOpen (.of k) X)).obj ⟶ (zeroSectionBoundary X F).obj :=
  Functor.whiskerLeft (cylinderNeighborhood X).op
      ((imageAdjunction (SmoothSite.a1Section (.of k) X 0).left).unit.app
        (boundaryAmbientCokernel ((SheafWithTransfers.toSheaf k).obj F)
          (SmoothSite.contractionOpen (.of k) X))).hom ≫
    Functor.whiskerRight (NatTrans.op (zeroNeighborhoodLiftNat X))
      (zeroSectionBoundary X F).obj

/-- The original affine-line-to-Laurent restriction, restricted to the small site. -/
abbrev contractionRestrictionSmall :=
  Functor.whiskerLeft (toSmoothSite X).op
    ((PresheafWithTransfers.toPresheaf k).map
      (PresheafWithTransfers.contractionRestriction F.obj))

/-- The ambient boundary kills exactly the original affine-line restriction. -/
theorem restriction_laurentToAmbientCokernel :
    contractionRestrictionSmall X F ≫ laurentToAmbientCokernel X F = 0 := by
  apply NatTrans.ext
  funext V
  let G := ((SheafWithTransfers.toSheaf k).obj F).obj
  let r := restrictionToDirectImage ((SheafWithTransfers.toSheaf k).obj F)
    (SmoothSite.contractionOpen (.of k) X)
  change G.map (SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj V.unop)).op ≫
    (𝟙 _ ≫ G.map (puncturedProjection X V.unop).op ≫
      (cokernel.π r).hom.app (op ((cylinderNeighborhood X).obj V.unop))) = 0
  rw [Category.id_comp, ← Category.assoc, ← G.map_comp, ← op_comp,
    puncturedProjection_open, op_comp, G.map_comp, Category.assoc]
  have h := congrArg (fun f ↦ f.hom.app (op ((cylinderNeighborhood X).obj V.unop)))
    (cokernel.condition r)
  change G.map ((restrictionProjection (SmoothSite.contractionOpen (.of k) X)).app
      ((cylinderNeighborhood X).obj V.unop)).op ≫
      (cokernel.π r).hom.app (op ((cylinderNeighborhood X).obj V.unop)) = 0 at h
  rw [h, comp_zero]

/-- Restriction preserves the original presheaf contraction cokernel literally. -/
def contractionRestrictedCokernelIso :
    (toSmoothSite X).op ⋙ (PresheafWithTransfers.toPresheaf k).obj
      (PresheafWithTransfers.contraction F.obj) ≅
      cokernel (contractionRestrictionSmall X F) :=
  PreservesCokernel.iso
    ((Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
      (toSmoothSite X ⋙ Cor.graphFunctor k).op)
    (PresheafWithTransfers.contractionRestriction F.obj).hom

/-- The canonical map from the unchanged original contraction to the boundary sheaf. -/
def contractionToBoundaryPresheaf :
    (toSmoothSite X).op ⋙ (PresheafWithTransfers.toPresheaf k).obj
      (PresheafWithTransfers.contraction F.obj) ⟶ (zeroSectionBoundary X F).obj :=
  (contractionRestrictedCokernelIso X F).hom ≫
    cokernel.desc _ (laurentToAmbientCokernel X F)
      (restriction_laurentToAmbientCokernel X F) ≫
    ambientCokernelToBoundary X F

/-- The actual sheaf map `(F₋₁)|S → B(A¹_S,0_S)`. Only ordinary HI is used
for sheafness of the original contraction; no purity or strict HI is assumed. -/
def contractionToBoundary (hF : F.obj.IsA1Invariant) :
    (restrict X AddCommGrpCat).obj
        ((SheafWithTransfers.toSheaf k).obj (SheafWithTransfers.contraction F hF)) ⟶
      zeroSectionBoundary X F where
  hom := contractionToBoundaryPresheaf X F

/-- The comparison on the original Laurent representative is the actual sheaf
cokernel projection followed by the closed inverse-image unit and zero lift. -/
@[reassoc (attr := simp)]
theorem toContraction_contractionToBoundaryPresheaf :
    Functor.whiskerLeft (toSmoothSite X).op
        ((PresheafWithTransfers.toPresheaf k).map (PresheafWithTransfers.toContraction F.obj)) ≫
      contractionToBoundaryPresheaf X F =
      laurentToAmbientCokernel X F ≫ ambientCokernelToBoundary X F := by
  have h := PreservesCokernel.π_iso_hom
    ((Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
      (toSmoothSite X ⋙ Cor.graphFunctor k).op)
    (PresheafWithTransfers.contractionRestriction F.obj).hom
  change Functor.whiskerLeft (toSmoothSite X).op
      ((PresheafWithTransfers.toPresheaf k).map (PresheafWithTransfers.toContraction F.obj)) ≫
      (contractionRestrictedCokernelIso X F).hom =
      cokernel.π (contractionRestrictionSmall X F) at h
  simp only [contractionToBoundaryPresheaf, ← Category.assoc, h, cokernel.π_desc]

end Motivic.FiniteEtaleSite
