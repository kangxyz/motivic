/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightOne.Geometry.TorusDivisor
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Units.BoundaryOneComplex

/-! # Actual boundary-one divisors on arbitrary integral affine smooth sources -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent
open _root_.AlgebraicGeometry.PolynomialOpenQuotient.Laurent
open _root_.AlgebraicGeometry.Scheme.PolynomialLaurent
open _root_.AlgebraicGeometry.Scheme.SmoothSite
open _root_.Motivic.AffineTorusPolynomialPresentation
open _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
open Motivic.SmoothSiteTorusDivisor Polynomial.BoundaryOneRationalFunctions

universe u

namespace Motivic.SmoothSiteBoundaryOneDivisor
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]
attribute [local instance] sectionsAlgebra

/-- The actual affine-coordinate precomposition is an additive equivalence. -/
def affineCycleEquiv (X : SmoothSite (Spec (.of k))) [IsAffine X.left] :
    (Cor.mk X ⟶ Cor.mk (torus (.of k))) ≃+
      FiniteCorrespondence (baseMap k Γ(X.left, ⊤)) (laurentProjection (.of k)) where
  toFun := affineCycleCoordinates X
  invFun z := (Cor.graphFunctor k).map (affineIso X).inv ≫ z
  left_inv z := by
    let e := (Cor.graphFunctor k).mapIso (affineIso X)
    change e.inv ≫ (e.hom ≫ z) = z
    exact e.inv_hom_id_assoc z
  right_inv z := by
    let e := (Cor.graphFunctor k).mapIso (affineIso X)
    let z' : (Cor.graphFunctor k).obj (affineSite k Γ(X.left, ⊤)) ⟶
        Cor.mk (torus (.of k)) := z
    change e.hom ≫ (e.inv ≫ z') = z'
    exact e.hom_inv_id_assoc z'
  map_add' := map_add (affineCycleCoordinates X)

/-- The original divisor, transported back from actual affine coordinates. -/
def affineDivisor (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left] :
    Additive (group Γ(X.left, ⊤)) →+
      (Cor.mk X ⟶ Cor.mk (torus (.of k))) :=
  (affineCycleEquiv X).symm.toAddMonoidHom.comp boundaryDivisor

@[simp] theorem affineCycleCoordinates_affineDivisor
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left]
    (m : Additive (group Γ(X.left, ⊤))) :
    affineCycleCoordinates X (affineDivisor X m) = boundaryDivisor m :=
  (affineCycleEquiv X).apply_symm_apply _

/-- The actual divisor retains all ordinary restrictions on integral affines. -/
theorem affineDivisor_natural
    {X Y : SmoothSite (Spec (.of k))} [IsAffine X.left] [IsAffine Y.left]
    [IsIntegral X.left] [IsIntegral Y.left] (f : X ⟶ Y)
    (m : Additive (group Γ(Y.left, ⊤))) :
    (Cor.graphFunctor k).map f ≫ affineDivisor Y m =
      affineDivisor X ((Polynomial.BoundaryOneRationalFunctions.map
        f.left.appTop.hom).toAdditive m) := by
  apply (affineCycleEquiv X).injective
  change affineCycleCoordinates X _ = affineCycleCoordinates X _
  have hc := affineCycleCoordinates_natural f (affineDivisor Y m)
  have hr := congrArg (affineRestriction (sectionsMap f))
    (affineCycleCoordinates_affineDivisor Y m)
  have hn := boundaryDivisor_natural (sectionsMap f) m
  exact hc.symm.trans (hr.trans (hn.trans (affineCycleCoordinates_affineDivisor X _).symm))

/-- The boundary divisor takes values in the project's original first torus power. -/
def affinePowerOneDivisor (X : SmoothSite (Spec (.of k)))
    [IsAffine X.left] [IsIntegral X.left] :
    Additive (group Γ(X.left, ⊤)) →+
      (Cor.mk X ⟶ Cor.mk (torusPower (.of k) 1)) :=
  (Preadditive.rightComp (Cor.mk X)
    ((Cor.graphFunctor k).map (torusPowerOneIso (.of k)).inv)).comp (affineDivisor X)

/-- Original first-torus boundary divisors are ordinary-natural. -/
theorem affinePowerOneDivisor_natural
    {X Y : SmoothSite (Spec (.of k))} [IsAffine X.left] [IsAffine Y.left]
    [IsIntegral X.left] [IsIntegral Y.left] (f : X ⟶ Y)
    (m : Additive (group Γ(Y.left, ⊤))) :
    (Cor.graphFunctor k).map f ≫ affinePowerOneDivisor Y m =
      affinePowerOneDivisor X ((Polynomial.BoundaryOneRationalFunctions.map
        f.left.appTop.hom).toAdditive m) := by
  let t := (Cor.graphFunctor k).map (torusPowerOneIso (.of k)).inv
  exact (Category.assoc ((Cor.graphFunctor k).map f) (affineDivisor Y m) t).symm.trans
    (congrArg (fun z => z ≫ t) (affineDivisor_natural f m))

/-- Boundary-one functions have zero signed-unit image on the original torus. -/
theorem affineNorm_affineDivisor
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left]
    (m : Additive (group Γ(X.left, ⊤))) : affineNorm X (affineDivisor X m) = 0 := by
  have hc := affineCycleCoordinates_affineDivisor X m
  have he := congrArg (cycleRationalFunction (k := k)) hc
  change cycleRationalFunction (affineCycleCoordinates X (affineDivisor X m)) =
    cycleRationalFunction (rationalDivisorHom (boundaryInclusion.toAdditive m)) at he
  rw [cycleRationalFunction_rationalDivisorHom] at he
  have hs := congrArg (signedValueHom (R := Γ(X.left, ⊤))).toAdditive he
  have hb := (boundaryInvariant_eq_one_iff (boundaryInclusion m.toMul)).mpr m.toMul.property
  have hz := congrArg Prod.snd hb
  exact hs.trans (congrArg Additive.ofMul hz)

/-- The original boundary-one divisor has no nonzero kernel on integral affine sources. -/
theorem affineDivisor_injective
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left] :
    Function.Injective (affineDivisor X) :=
  (affineCycleEquiv X).symm.injective.comp (boundaryDivisor_injective (k := k))

/-- The universe-raised local divisor lands in the project's actual first-torus presheaf. -/
def largeAffineDivisor (X : SmoothSite (Spec (.of k)))
    [IsAffine X.left] [IsIntegral X.left] :
    (largeBoundaryOnePresheaf k).obj (op X) ⟶
      ((PresheafWithTransfers.toPresheaf k).obj
        (PresheafWithTransfers.torusRepresentable k 1)).obj (op X) :=
  AddCommGrpCat.ofHom {
    toFun m := ULift.up (affinePowerOneDivisor X m.down)
    map_zero' := by change ULift.up (affinePowerOneDivisor X 0) = ULift.up 0; rw [map_zero]
    map_add' m n := by
      change ULift.up (affinePowerOneDivisor X (m.down + n.down)) =
        ULift.up (affinePowerOneDivisor X m.down + affinePowerOneDivisor X n.down)
      rw [map_add] }

/-- Naturality of the local divisor in exactly the original coefficient universe. -/
theorem largeAffineDivisor_natural
    {X Y : SmoothSite (Spec (.of k))} [IsAffine X.left] [IsAffine Y.left]
    [IsIntegral X.left] [IsIntegral Y.left] (f : X ⟶ Y) :
    (largeBoundaryOnePresheaf k).map f.op ≫ largeAffineDivisor X =
      largeAffineDivisor Y ≫
        ((PresheafWithTransfers.toPresheaf k).obj
          (PresheafWithTransfers.torusRepresentable k 1)).map f.op := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro m
  exact congrArg ULift.up (affinePowerOneDivisor_natural f m.down).symm

end Motivic.SmoothSiteBoundaryOneDivisor
