/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.WholeAffineLineH1Correction
public import Motivic.Cohomology.A1.WholeAffineLineNisnevichLifting

/-! # Literal smooth-site squares of the base-only affine-line restriction -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic ProjectiveSpace
open Scheme.Hom
universe u
namespace Motivic.SmoothSite

/-- The native scheme pullback universal property restricts to Sm/S. -/
theorem isPullback_of_left {S : Scheme.{u}} (sq : Square (SmoothSite S))
    (H : IsPullback sq.f₁₂.left sq.f₁₃.left sq.f₂₄.left sq.f₃₄.left) : sq.IsPullback where
  w := sq.fac
  isLimit' := ⟨PullbackCone.IsLimit.mk _ (fun c => homMk
    (H.lift c.fst.left c.snd.left (congrArg (fun f => f.left) c.condition)) (by
      rw [← MorphismProperty.Over.w sq.f₁₂, ← Category.assoc,
        H.lift_fst, MorphismProperty.Over.w]))
    (fun c => by ext; exact H.lift_fst _ _ _)
    (fun c => by ext; exact H.lift_snd _ _ _)
    (fun c m h₁ h₂ => by
      apply MorphismProperty.Over.Hom.ext
      apply H.hom_ext
      · exact (congrArg (fun f => f.left) h₁).trans (H.lift_fst _ _ _).symm
      · exact (congrArg (fun f => f.left) h₂).trans (H.lift_snd _ _ _).symm)⟩

end Motivic.SmoothSite
namespace AlgebraicGeometry.Scheme.Hom
local instance {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
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

abbrev boundaryBaseAmbientSite : SmoothSite (Spec (.of k)) :=
  SmoothSite.mk (boundaryBaseSpecProjection q U V ≫ boundaryBaseFieldMap V t)

abbrev boundaryBaseEtaleSite :=
  RelativeCurvePencil.lambdaSourceSite k (boundaryBaseFieldMap V t)
    (boundaryBaseProjectiveMap R ι f V ≫ toSpec Γ(V.toScheme, ⊤) ι)
    (boundaryBaseCoverInclusion q p (f ≫ toSpec R ι) j hj U V)

abbrev boundaryBaseOpenSite :=
  RelativeCurvePencil.psiSourceSite k (boundaryBaseFieldMap V t)
    (boundaryBaseSpecProjection q U V) (boundaryBaseCoverMap q a U V)

def boundaryBaseEtaleArrow : boundaryBaseEtaleSite k R ι t q p f j hj U V ⟶
    boundaryBaseAmbientSite k R t q U V :=
  SmoothSite.homMk (boundaryBaseCoverMap q p U V) (by
    change boundaryBaseCoverMap q p U V ≫
      (boundaryBaseSpecProjection q U V ≫ boundaryBaseFieldMap V t) =
      (boundaryBaseCoverInclusion q p (f ≫ toSpec R ι) j hj U V ≫
        (boundaryBaseProjectiveMap R ι f V ≫ toSpec Γ(V.toScheme, ⊤) ι)) ≫
          boundaryBaseFieldMap V t
    rw [boundaryBaseCoverInclusion_spec_projection, Category.assoc])

def boundaryBaseOpenArrow : boundaryBaseOpenSite k R t q a U V ⟶
    boundaryBaseAmbientSite k R t q U V :=
  SmoothSite.homMk (boundaryBaseCoverMap q a U V) (Category.assoc _ _ _).symm

abbrev boundaryBasePencilSquare : Square (SmoothSite (Spec (.of k))) where
  f₁₂ := boundaryBasePencilBeta k R ι t q p a f j hj U V
  f₁₃ := boundaryBasePencilAlpha k R ι t q p a f j hj U V
  f₂₄ := boundaryBaseOpenArrow k R t q a U V
  f₃₄ := boundaryBaseEtaleArrow k R ι t q p f j hj U V
  fac := by
    apply MorphismProperty.Over.Hom.ext
    exact pullback.condition.symm

theorem boundaryBasePencilSquare_isPullback :
    (boundaryBasePencilSquare k R ι t q p a f j hj U V).IsPullback :=
  SmoothSite.isPullback_of_left _ (IsPullback.of_hasPullback _ _).flip

end AlgebraicGeometry.Scheme.Hom
