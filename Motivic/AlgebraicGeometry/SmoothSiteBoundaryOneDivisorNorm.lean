module

public import Motivic.AlgebraicGeometry.SmoothSiteBoundaryOneSheafDivisor
public import Motivic.AlgebraicGeometry.SmoothSiteReducedTorusNorm
public import Motivic.AlgebraicGeometry.SmoothSiteIntegralAffineSheafification

/-! # The actual boundary divisor has zero reduced norm -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Motivic.SmoothSiteTorusDivisor

universe u
namespace Motivic.SmoothSiteBoundaryOneDivisor
variable (k : Type u) [Field k]

/-- Cancelling the original torus coordinate isomorphism preserves the zero norm. -/
theorem affinePowerOneNorm_affinePowerOneDivisor (X : SmoothSite (Spec (.of k)))
    [IsAffine X.left] [IsIntegral X.left]
    (m : Additive (Polynomial.BoundaryOneRationalFunctions.group Γ(X.left, ⊤))) :
    affinePowerOneNorm X (affinePowerOneDivisor X m) = 0 := by
  let e := (Cor.graphFunctor k).mapIso (SmoothSite.torusPowerOneIso (.of k))
  have h : (affineDivisor X m ≫ e.inv) ≫ e.hom = affineDivisor X m := by
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun t => affineDivisor X m ≫ t) e.inv_hom_id).trans (Category.comp_id _))
  exact (congrArg (affineNorm X) h).trans (affineNorm_affineDivisor X m)

/-- The ordinary norm kills the genuine local reduced boundary divisor. -/
theorem largeAffineReducedDivisor_norm (X : SmoothSite (Spec (.of k)))
    [IsAffine X.left] [IsIntegral X.left] :
    largeAffineReducedDivisor k X ≫ reducedNorm.app (op X) = 0 := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro m
  change reducedNorm.app (op X)
    ((PresheafWithTransfers.toReducedTorus k 1).hom.app (op (Cor.mk X))
      (ULift.up (affinePowerOneDivisor X m.down))) = ULift.up 0
  rw [reducedNorm_affine_apply]
  apply congrArg ULift.up
  exact affinePowerOneNorm_affinePowerOneDivisor k X m.down

/-- The raw source map has zero composite with the genuine sheafified norm. -/
theorem singularDivisorToSheaf_norm (n : ℕ) :
    singularDivisorToSheaf k n ≫ ((reducedNormSheafMap (k := k)).f n).hom = 0 := by
  apply (Functor.IsCoverDense.restrictHomEquivHom
    (G := SmoothSite.integralAffineInclusion k)
    (ℱ' := (SingularComplex.sheafObj (SmoothSite.nisnevichTopology (Spec (.of k)))
      (AlgebraicSimplex.cosimplicialSmoothSite k)
      (SmoothSite.largeUnitsPresheaf (Spec (.of k)))).X n)).symm.injective
  apply NatTrans.ext
  funext X
  let : IsAffine X.unop.obj.left := X.unop.property.1
  let : IsIntegral X.unop.obj.left := X.unop.property.2
  change (singularDivisorToSheaf k n).app (op X.unop.obj) ≫
    ((reducedNormSheafMap (k := k)).f n).hom.app (op X.unop.obj) = 0
  rw [singularDivisorToSheaf_app, Category.assoc]
  have hn := congrArg (fun η => η.app (op X.unop.obj))
    (toSheafify_naturality (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SingularComplex.presheafMap (AlgebraicSimplex.cosimplicialSmoothSite k)
        (reducedNorm (k := k))).f n))
  simp only [NatTrans.comp_app] at hn
  change _ ≫ (toSheafify (SmoothSite.nisnevichTopology (Spec (.of k)))
    ((rawReducedSingular k).X n)).app (op X.unop.obj) ≫
      (sheafifyMap (SmoothSite.nisnevichTopology (Spec (.of k)))
        ((SingularComplex.presheafMap (AlgebraicSimplex.cosimplicialSmoothSite k)
          (reducedNorm (k := k))).f n)).app (op X.unop.obj) = 0
  rw [← hn, ← Category.assoc]
  change (largeAffineReducedDivisor k
    (X.unop.obj ⨯ AlgebraicSimplex.smoothSiteObj k n) ≫
      reducedNorm.app (op (X.unop.obj ⨯ AlgebraicSimplex.smoothSiteObj k n))) ≫ _ = 0
  rw [largeAffineReducedDivisor_norm, zero_comp]

/-- The original sheaf divisor and reduced norm form a genuine complex. -/
theorem sheafDivisorChainMap_norm :
    sheafDivisorChainMap k ≫ reducedNormSheafMap = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _
    (((SingularComplex.sheafObj (SmoothSite.nisnevichTopology (Spec (.of k)))
      (AlgebraicSimplex.cosimplicialSmoothSite k)
      (SmoothSite.largeUnitsPresheaf (Spec (.of k)))).X n).property)
  change toSheafify _ _ ≫ (sheafifyLift _ _ _ ≫ _) = toSheafify _ _ ≫ 0
  rw [← Category.assoc, toSheafify_sheafifyLift, comp_zero]
  exact singularDivisorToSheaf_norm k n

end Motivic.SmoothSiteBoundaryOneDivisor
