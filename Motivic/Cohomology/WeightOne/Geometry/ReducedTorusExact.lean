/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightOne.Geometry.ReducedTorusNorm
public import Motivic.Cohomology.WeightOne.Geometry.BoundaryOneSheafDivisor
public import Mathlib.Algebra.Homology.ShortComplex.Ab

/-! # Exactness on the original reduced torus over integral affine sources -/

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
open Motivic.SmoothSiteTorusDivisor Motivic.SmoothSiteBoundaryOneDivisor
open _root_.AlgebraicSimplex
open _root_.Motivic.PresheafWithTransfers
open Polynomial.BoundaryOneRationalFunctions

universe u

namespace Motivic.SmoothSiteReducedTorusExact
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]
attribute [local instance] sectionsAlgebra

/-- The literal first torus-power target comparison on actual correspondence groups. -/
def powerOneTargetEquiv (X : SmoothSite (Spec (.of k))) :
    (Cor.mk X ⟶ Cor.mk (torusPower (.of k) 1)) ≃+
      (Cor.mk X ⟶ Cor.mk (torus (.of k))) where
  toFun z := z ≫ (Cor.graphFunctor k).map (torusPowerOneIso (.of k)).hom
  invFun z := z ≫ (Cor.graphFunctor k).map (torusPowerOneIso (.of k)).inv
  left_inv z := by
    let e := (Cor.graphFunctor k).mapIso (torusPowerOneIso (.of k))
    change (z ≫ e.hom) ≫ e.inv = z
    rw [Category.assoc, e.hom_inv_id]
    exact Category.comp_id z
  right_inv z := by
    let e := (Cor.graphFunctor k).mapIso (torusPowerOneIso (.of k))
    change (z ≫ e.inv) ≫ e.hom = z
    rw [Category.assoc, e.inv_hom_id]
    exact Category.comp_id _
  map_add' := map_add (Preadditive.rightComp (Cor.mk X)
    ((Cor.graphFunctor k).map (torusPowerOneIso (.of k)).hom))

/-- Actual cycle-to-rational-function coordinates, including both genuine geometric isomorphisms. -/
def affinePowerOneRationalEquiv (X : SmoothSite (Spec (.of k)))
    [IsAffine X.left] [IsIntegral X.left] :
    (Cor.mk X ⟶ Cor.mk (torusPower (.of k) 1)) ≃+
      Additive (admissibleGroup Γ(X.left, ⊤)) :=
  ((powerOneTargetEquiv X).trans (affineCycleEquiv X)).trans
    (rationalDivisorEquiv (k := k)).symm

/-- The original constant-one section, as an actual graph cycle into the first torus power. -/
def identityGraph (X : SmoothSite (Spec (.of k))) :
    Cor.mk X ⟶ Cor.mk (torusPower (.of k) 1) :=
  (Cor.graphFunctor k).map
    (structureMorphism X ≫ torusInsertOne (.of k) 0 0)

/-- The original identity graph becomes the literal fraction X - 1 in actual coordinates. -/
theorem affinePowerOneRationalEquiv_identityGraph
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left] :
    affinePowerOneRationalEquiv X (identityGraph X) =
      Additive.ofMul (identityPointFraction (R := Γ(X.left, ⊤))) := by
  have hc : affineCycleCoordinates X (powerOneTargetEquiv X (identityGraph X)) =
      (Cor.graphFunctor k).map (unitMorphism (k := k) (1 : (Γ(X.left, ⊤))ˣ)) := by
    change (Cor.graphFunctor k).map (affineIso X).hom ≫
      ((Cor.graphFunctor k).map (structureMorphism X ≫
        torusInsertOne (.of k) 0 0) ≫
        (Cor.graphFunctor k).map (torusPowerOneIso (.of k)).hom) = _
    rw [← Functor.map_comp, Category.assoc, torusInsertOne_zero_powerOneIso,
      ← Functor.map_comp, ← Category.assoc, affineIso_structureMorphism, ← unitMorphism_one]
  exact (congrArg (cycleRationalFunction (k := k)) hc).trans
    (cycleRationalFunction_identityGraph (k := k) (R := Γ(X.left, ⊤)))

/-- The actual boundary divisor has its original boundary-one function as coordinates. -/
theorem affinePowerOneRationalEquiv_affinePowerOneDivisor
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left]
    (m : Additive (group Γ(X.left, ⊤))) :
    affinePowerOneRationalEquiv X (affinePowerOneDivisor X m) =
      boundaryInclusion.toAdditive m := by
  have ht : powerOneTargetEquiv X (affinePowerOneDivisor X m) = affineDivisor X m :=
    (powerOneTargetEquiv X).apply_symm_apply (affineDivisor X m)
  have hc := (congrArg (affineCycleCoordinates X) ht).trans
    (affineCycleCoordinates_affineDivisor X m)
  exact (congrArg (cycleRationalFunction (k := k)) hc).trans
    (cycleRationalFunction_rationalDivisorHom (boundaryInclusion.toAdditive m))

/-- On an integral affine source the norm kernel is M* plus the actual identity graph. -/
theorem affinePowerOneNorm_kernel_decomposition
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left]
    (z : Cor.mk X ⟶ Cor.mk (torusPower (.of k) 1))
    (hz : affinePowerOneNorm X z = 0) :
    ∃ m : Additive (group Γ(X.left, ⊤)), ∃ n : ℤ,
      z = affinePowerOneDivisor X m + n • identityGraph X := by
  let f := affinePowerOneRationalEquiv X z
  have hf : signedValueHom f.toMul = 1 := hz
  obtain ⟨m, hm⟩ := signedValue_kernel_decomposition f.toMul hf
  refine ⟨Additive.ofMul m, fractionDegree f.toMul, ?_⟩
  let n := fractionDegree f.toMul
  let e := affinePowerOneRationalEquiv X
  have hi : e (n • identityGraph X) =
      n • Additive.ofMul (identityPointFraction (R := Γ(X.left, ⊤))) :=
    (map_zsmul e n (identityGraph X)).trans
      (congrArg (n • ·) (affinePowerOneRationalEquiv_identityGraph X))
  have he := (map_add e (affinePowerOneDivisor X (Additive.ofMul m))
    (n • identityGraph X)).trans
      (congrArg₂ (· + ·) (affinePowerOneRationalEquiv_affinePowerOneDivisor X
        (Additive.ofMul m)) hi)
  exact e.injective ((congrArg Additive.ofMul hm).trans he.symm)

/-- The actual norm is surjective on all integral affine smooth sources. -/
theorem affinePowerOneNorm_surjective
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left] :
    Function.Surjective (affinePowerOneNorm X) := by
  intro u
  obtain ⟨f, hf⟩ := boundaryInvariant_surjective (R := Γ(X.left, ⊤))
    (1, u.toMul)
  refine ⟨(affinePowerOneRationalEquiv X).symm (Additive.ofMul f), ?_⟩
  have he := (affinePowerOneRationalEquiv X).apply_symm_apply (Additive.ofMul f)
  have hs := congrArg (signedValueHom (R := Γ(X.left, ⊤))).toAdditive he
  exact hs.trans (congrArg Additive.ofMul (congrArg Prod.snd hf))

/-- No nontrivial actual boundary-one divisor is an identity-axis multiple. -/
theorem affinePowerOneDivisor_identityGraph_intersection
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left]
    (m : Additive (group Γ(X.left, ⊤))) (n : ℤ)
    (h : affinePowerOneDivisor X m = n • identityGraph X) : m = 0 ∧ n = 0 := by
  have he := congrArg (affinePowerOneRationalEquiv X) h
  have ht := (map_zsmul (affinePowerOneRationalEquiv X) n (identityGraph X)).trans
    (congrArg (n • ·) (affinePowerOneRationalEquiv_identityGraph X))
  have hb := (affinePowerOneRationalEquiv_affinePowerOneDivisor X m).symm.trans (he.trans ht)
  have hi := boundary_identityPoint_intersection m.toMul n (congrArg Additive.toMul hb)
  exact ⟨congrArg Additive.ofMul hi.1, hi.2⟩

/-- The original quotient kills the original identity graph, on any smooth source. -/
theorem toReduced_identityGraph (X : SmoothSite (Spec (.of k))) :
    (toReducedTorus k 1).hom.app (op (Cor.mk X)) (ULift.up (identityGraph X)) = 0 := by
  have h := congrArg (fun η => η.hom.app (op (Cor.mk X))
    (ULift.up ((Cor.graphFunctor k).map (structureMorphism X))))
      (torusIdentityAxis_toReducedTorus k 1 0)
  change (toReducedTorus k 1).hom.app (op (Cor.mk X))
    (ULift.up ((Cor.graphFunctor k).map (structureMorphism X) ≫
      (Cor.graphFunctor k).map (torusInsertOne (.of k) 0 0))) = 0 at h
  simpa only [identityGraph, Functor.map_comp] using h

/-- Adding an actual identity graph multiple does not change the original quotient section. -/
theorem toReduced_add_identityGraph (X : SmoothSite (Spec (.of k)))
    (z : Cor.mk X ⟶ Cor.mk (torusPower (.of k) 1)) (n : ℤ) :
    (toReducedTorus k 1).hom.app (op (Cor.mk X)) (ULift.up (z + n • identityGraph X)) =
      (toReducedTorus k 1).hom.app (op (Cor.mk X)) (ULift.up z) := by
  change (toReducedTorus k 1).hom.app (op (Cor.mk X))
    (ULift.up z + n • ULift.up (identityGraph X)) = _
  rw [map_add, map_zsmul, toReduced_identityGraph, smul_zero, add_zero]

/-- The kernel of the actual original quotient is the original identity cyclic subgroup. -/
theorem toReduced_eq_zero_iff (X : SmoothSite (Spec (.of k))) [IsIntegral X.left]
    (z : Cor.mk X ⟶ Cor.mk (torusPower (.of k) 1)) :
    (toReducedTorus k 1).hom.app (op (Cor.mk X)) (ULift.up z) = 0 ↔
      ∃ n : ℤ, z = n • identityGraph X := by
  constructor
  · intro hz
    let E := (evaluation (Cor k)ᵒᵖ AddCommGrpCat.{u + 1}).obj (op (Cor.mk X))
    have hex := (ShortComplex.cokernelSequence_exact (torusRelation k 1)).map E
    obtain ⟨s, hs⟩ := (ShortComplex.ab_exact_iff _).mp hex (ULift.up z) hz
    change (torusRelation k 1).app (op (Cor.mk X)) s = ULift.up z at hs
    rw [torusRelation_app_apply, Fin.sum_univ_one] at hs
    let a := (biproduct.π (fun _ : Fin 1 => (torusRepresentable k 0).obj) 0).app
      (op (Cor.mk X)) s
    have he : a.down ≫ (Cor.graphFunctor k).map
        (torusInsertOne (.of k) 0 0) = z := congrArg ULift.down hs
    obtain ⟨n, hn⟩ := baseCorrespondence_eq_zsmul X a.down
    refine ⟨n, he.symm.trans ?_⟩
    rw [hn, Preadditive.zsmul_comp, ← Functor.map_comp]
    rfl
  · rintro ⟨n, rfl⟩
    change (toReducedTorus k 1).hom.app (op (Cor.mk X))
      (n • ULift.up (identityGraph X)) = 0
    rw [map_zsmul, toReduced_identityGraph, smul_zero]

/-- Boundary-one divisors still have zero norm before and after the original quotient. -/
theorem affinePowerOneNorm_affinePowerOneDivisor
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left]
    (m : Additive (group Γ(X.left, ⊤))) :
    affinePowerOneNorm X (affinePowerOneDivisor X m) = 0 := by
  have ht : powerOneTargetEquiv X (affinePowerOneDivisor X m) = affineDivisor X m :=
    (powerOneTargetEquiv X).apply_symm_apply (affineDivisor X m)
  exact (congrArg (affineNorm X) ht).trans (affineNorm_affineDivisor X m)

/-- The original reduced boundary divisor has zero composite with the descended norm. -/
theorem largeAffineReducedDivisor_reducedNorm
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left] :
    largeAffineReducedDivisor k X ≫ reducedNorm.app (op X) = 0 := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro m
  exact (reducedNorm_affine_apply X (affinePowerOneDivisor X m.down)).trans
    (congrArg ULift.up (affinePowerOneNorm_affinePowerOneDivisor X m.down))

/-- The genuine boundary divisor remains injective after the original identity-axis quotient. -/
theorem largeAffineReducedDivisor_injective
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left] :
    Function.Injective (largeAffineReducedDivisor k X) := by
  apply (injective_iff_map_eq_zero (largeAffineReducedDivisor k X).hom).mpr
  intro m hm
  obtain ⟨n, hn⟩ := (toReduced_eq_zero_iff X (affinePowerOneDivisor X m.down)).mp hm
  have h := (affinePowerOneDivisor_identityGraph_intersection X m.down n hn).1
  exact ULift.ext _ _ h

/-- The descended norm is surjective on the actual reduced sections over integral affines. -/
theorem reducedNorm_app_surjective
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left] :
    Function.Surjective (reducedNorm.app (op X)) := by
  intro u
  obtain ⟨z, hz⟩ := affinePowerOneNorm_surjective X u.down
  refine ⟨(toReducedTorus k 1).hom.app (op (Cor.mk X)) (ULift.up z), ?_⟩
  exact (reducedNorm_affine_apply X z).trans (congrArg ULift.up hz)

/-- Exactness at the project's original reduced sections, before any sheafification. -/
theorem reducedNorm_app_eq_zero_iff
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left]
    (z : (rawReducedTorus k).obj (op X)) :
    reducedNorm.app (op X) z = 0 ↔
      ∃ m : (largeBoundaryOnePresheaf k).obj (op X),
        largeAffineReducedDivisor k X m = z := by
  constructor
  · intro hz
    obtain ⟨a, rfl⟩ := toReducedTorus_surjective k 1 (Cor.mk X) z
    have hn : affinePowerOneNorm X a.down = 0 := by
      have he := (reducedNorm_affine_apply X a.down).symm.trans hz
      exact congrArg ULift.down he
    obtain ⟨m, n, hm⟩ := affinePowerOneNorm_kernel_decomposition X a.down hn
    refine ⟨ULift.up m, ?_⟩
    change (toReducedTorus k 1).hom.app (op (Cor.mk X))
      (ULift.up (affinePowerOneDivisor X m)) =
        (toReducedTorus k 1).hom.app (op (Cor.mk X)) (ULift.up a.down)
    have he := congrArg (fun a => (toReducedTorus k 1).hom.app (op (Cor.mk X))
      (ULift.up a)) hm
    exact (he.trans (toReduced_add_identityGraph X (affinePowerOneDivisor X m) n)).symm
  · rintro ⟨m, rfl⟩
    exact congrArg (fun f => f m) (largeAffineReducedDivisor_reducedNorm X)

end Motivic.SmoothSiteReducedTorusExact
