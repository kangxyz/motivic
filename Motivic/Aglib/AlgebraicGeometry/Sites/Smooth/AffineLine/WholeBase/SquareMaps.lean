/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.WholeBase.Square
/-! # Exact maps from the base-restricted square to the original square -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ProjectiveSpace
open Scheme.Hom
universe u
namespace AlgebraicGeometry.Scheme.Hom
/-- The smoothness instance used in this module. -/
local instance squareMapsSmooth {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
    Smooth f := SmoothOfRelativeDimension.smooth 1 f
variable (k : Type u) [Field k] (R : Type u) [CommRing R] (ι : Type u)
  {X Y A C : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine A]
  (t : Spec (.of R) ⟶ Spec (.of k)) [Smooth t]
  (q : X ⟶ Spec (.of R)) [SmoothOfRelativeDimension 1 q]
  (p : Y ⟶ X) [Etale p] (a : A ⟶ X) [IsOpenImmersion a]
  (f : C ⟶ ProjectiveSpace R ι) (j : Y ⟶ C)
  (hj : j ≫ (f ≫ toSpec R ι) = p ≫ q)
  (U : X.Opens) (V : (Spec (.of R)).Opens)
  [IsAffine V.toScheme] [IsAffine (boundaryBaseSourceOpen q U V).toScheme]

/-- The original ambient scheme as a smooth-site object over the ground field. -/
abbrev originalAmbientSite : SmoothSite (Spec (.of k)) := SmoothSite.mk (q ≫ t)
/-- The original étale source as a smooth-site object over the ground field. -/
abbrev originalEtaleSite : SmoothSite (Spec (.of k)) := SmoothSite.mk (p ≫ q ≫ t)
/-- The original open source as a smooth-site object over the ground field. -/
abbrev originalOpenSite : SmoothSite (Spec (.of k)) := SmoothSite.mk (a ≫ q ≫ t)
/-- The original étale-open overlap as a smooth-site object over the ground field. -/
abbrev originalOverlapSite : SmoothSite (Spec (.of k)) :=
  SmoothSite.mk (pullback.fst p a ≫ p ≫ q ≫ t)

/-- The original étale map as an arrow of smooth-site objects. -/
def originalEtaleArrow : originalEtaleSite k R t q p ⟶ originalAmbientSite k R t q :=
  SmoothSite.homMk p rfl

/-- The original open immersion as an arrow of smooth-site objects. -/
def originalOpenArrow : originalOpenSite k R t q a ⟶ originalAmbientSite k R t q :=
  SmoothSite.homMk a rfl

/-- The first overlap projection as an arrow to the original étale smooth-site object. -/
def originalOverlapToEtale : originalOverlapSite k R t q p a ⟶ originalEtaleSite k R t q p :=
  SmoothSite.homMk (pullback.fst p a) rfl

/-- The second overlap projection as an arrow to the original open smooth-site object. -/
def originalOverlapToOpen : originalOverlapSite k R t q p a ⟶ originalOpenSite k R t q a :=
  SmoothSite.homMk (pullback.snd p a) (by
    change pullback.snd p a ≫ a ≫ q ≫ t = pullback.fst p a ≫ p ≫ q ≫ t
    rw [← Category.assoc, ← pullback.condition, Category.assoc])

/-- The square of original étale and open maps with their overlap in the smooth site. -/
abbrev originalBoundarySquare : Square (SmoothSite (Spec (.of k))) where
  f₁₂ := originalOverlapToOpen k R t q p a
  f₁₃ := originalOverlapToEtale k R t q p a
  f₂₄ := originalOpenArrow k R t q a
  f₃₄ := originalEtaleArrow k R t q p
  fac := by ext; exact pullback.condition.symm

lemma boundaryBaseAmbientSite_hom :
    (boundaryBaseAmbientSite k R t q U V).hom =
      (boundaryBaseSourceOpen q U V).ι ≫ q ≫ t := by
  change (boundaryBaseSourceProjection q U V ≫ V.toScheme.isoSpec.hom) ≫
    (V.toScheme.isoSpec.inv ≫ V.ι ≫ t) = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, boundaryBaseSourceProjection_ι, Category.assoc]

/-- The restriction arrow from the boundary-base ambient object to the original ambient object. -/
def boundaryBaseAmbientRestriction : boundaryBaseAmbientSite k R t q U V ⟶
    originalAmbientSite k R t q :=
  SmoothSite.homMk (boundaryBaseSourceOpen q U V).ι
    (boundaryBaseAmbientSite_hom k R t q U V).symm

/-- The restriction arrow from the boundary-base étale object to the original étale object. -/
def boundaryBaseEtaleRestriction : boundaryBaseEtaleSite k R ι t q p f j hj U V ⟶
    originalEtaleSite k R t q p :=
  SmoothSite.homMk (boundaryBaseCoverOpen q p U V).ι (by
    rw [← MorphismProperty.Over.w (boundaryBaseEtaleArrow k R ι t q p f j hj U V),
      boundaryBaseAmbientSite_hom]
    change _ = (boundaryBaseCoverMap q p U V) ≫ (boundaryBaseSourceOpen q U V).ι ≫ q ≫ t
    rw [← Category.assoc, morphismRestrict_ι]
    rfl)

/-- The restriction arrow from the boundary-base open object to the original open object. -/
def boundaryBaseOpenRestriction : boundaryBaseOpenSite k R t q a U V ⟶
    originalOpenSite k R t q a :=
  SmoothSite.homMk (boundaryBaseCoverOpen q a U V).ι (by
    rw [← MorphismProperty.Over.w (boundaryBaseOpenArrow k R t q a U V),
      boundaryBaseAmbientSite_hom]
    change _ = (boundaryBaseCoverMap q a U V) ≫ (boundaryBaseSourceOpen q U V).ι ≫ q ≫ t
    rw [← Category.assoc, morphismRestrict_ι]
    rfl)

/-- The restriction arrow from the boundary-base overlap to the original overlap object. -/
def boundaryBaseOverlapRestriction :
    (boundaryBasePencilSquare k R ι t q p a f j hj U V).X₁ ⟶
      originalOverlapSite k R t q p a :=
  SmoothSite.homMk (boundaryBaseOverlapMap q p a U V) (by
    change boundaryBaseOverlapMap q p a U V ≫ (pullback.fst p a ≫ p ≫ q ≫ t) = _
    rw [← Category.assoc, boundaryBaseOverlapMap_fst, Category.assoc]
    change pullback.fst _ _ ≫
      ((boundaryBaseCoverOpen q p U V).ι ≫ (originalEtaleSite k R t q p).hom) = _
    have h := MorphismProperty.Over.w
      (boundaryBaseEtaleRestriction k R ι t q p f j hj U V)
    change (boundaryBaseCoverOpen q p U V).ι ≫ (originalEtaleSite k R t q p).hom =
      (boundaryBaseEtaleSite k R ι t q p f j hj U V).hom at h
    rw [h]
    exact MorphismProperty.Over.w (boundaryBasePencilAlpha k R ι t q p a f j hj U V))

@[reassoc] theorem boundaryBaseOverlapRestriction_open :
    boundaryBaseOverlapRestriction k R ι t q p a f j hj U V ≫
      originalOverlapToOpen k R t q p a =
    boundaryBasePencilBeta k R ι t q p a f j hj U V ≫
      boundaryBaseOpenRestriction k R t q a U V := by
  ext
  exact boundaryBaseOverlapMap_snd q p a U V

@[reassoc] theorem boundaryBaseOverlapRestriction_etale :
    boundaryBaseOverlapRestriction k R ι t q p a f j hj U V ≫
      originalOverlapToEtale k R t q p a =
    boundaryBasePencilAlpha k R ι t q p a f j hj U V ≫
      boundaryBaseEtaleRestriction k R ι t q p f j hj U V := by
  ext
  exact boundaryBaseOverlapMap_fst q p a U V

@[reassoc] theorem boundaryBaseOpenRestriction_ambient :
    boundaryBaseOpenRestriction k R t q a U V ≫ originalOpenArrow k R t q a =
      boundaryBaseOpenArrow k R t q a U V ≫ boundaryBaseAmbientRestriction k R t q U V := by
  ext
  exact (morphismRestrict_ι a (boundaryBaseSourceOpen q U V)).symm

@[reassoc] theorem boundaryBaseEtaleRestriction_ambient :
    boundaryBaseEtaleRestriction k R ι t q p f j hj U V ≫ originalEtaleArrow k R t q p =
      boundaryBaseEtaleArrow k R ι t q p f j hj U V ≫
        boundaryBaseAmbientRestriction k R t q U V := by
  ext
  exact (morphismRestrict_ι p (boundaryBaseSourceOpen q U V)).symm

end AlgebraicGeometry.Scheme.Hom
