/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Diagonal.BoundarySupport

/-! # Literal endpoint fibers of arbitrary-weight integral support generators -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Polynomial
universe u
namespace Motivic.DiagonalBoundarySupport
variable {k : Type u} [Field k] {q : ℕ} (Z : Generator k q)

/-- The literal scheme-theoretic fiber over an arbitrary polynomial point. -/
abbrev fiber (a : k) : Scheme.{u} :=
  Z.graphPullback (WeightOneBoundaryNorm.evaluationPoint k a).left

/-- Its finite structural map to the original field point. -/
abbrev fiberProjection (a : k) : fiber Z a ⟶ Spec (.of k) :=
  pullback.fst (WeightOneBoundaryNorm.evaluationPoint k a).left Z.projection

/-- The original map from the whole fiber to the torus product. -/
abbrev fiberInclusion (a : k) :=
  Z.graphPullbackMap (WeightOneBoundaryNorm.evaluationPoint k a).left
    (MorphismProperty.Over.w (WeightOneBoundaryNorm.evaluationPoint k a))

/-- The whole fiber remains a closed subscheme of the actual point-torus product. -/
instance fiberInclusionClosed (a : k) : IsClosedImmersion (fiberInclusion Z a) := by
  apply (IsClosedImmersion.iff_isFinite_and_mono _).mpr
  refine ⟨inferInstance, ⟨?_⟩⟩
  intro W f g h
  have hfst : f ≫ fiberProjection Z a = g ≫ fiberProjection Z a := by
    simpa only [Category.assoc, FiniteCorrespondenceGenerator.graphPullbackMap_fst]
      using congrArg (fun t => t ≫ pullback.fst _ _) h
  have hsnd : f ≫ pullback.snd (WeightOneBoundaryNorm.evaluationPoint k a).left Z.projection ≫
        Z.targetProjection =
      g ≫ pullback.snd (WeightOneBoundaryNorm.evaluationPoint k a).left Z.projection ≫
        Z.targetProjection := by
    simpa only [Category.assoc, FiniteCorrespondenceGenerator.graphPullbackMap_snd]
      using congrArg (fun t => t ≫ pullback.snd _ _) h
  apply pullback.hom_ext hfst
  apply (cancel_mono Z.inclusion).mp
  apply pullback.hom_ext
  · change (f ≫ pullback.snd (WeightOneBoundaryNorm.evaluationPoint k a).left Z.projection ≫
        Z.inclusion) ≫
      pullback.fst _ _ =
        (g ≫ pullback.snd (WeightOneBoundaryNorm.evaluationPoint k a).left Z.projection ≫
        Z.inclusion) ≫
          pullback.fst _ _
    change (f ≫ pullback.snd (WeightOneBoundaryNorm.evaluationPoint k a).left
      Z.projection) ≫ Z.projection =
      (g ≫ pullback.snd (WeightOneBoundaryNorm.evaluationPoint k a).left
        Z.projection) ≫ Z.projection
    rw [Category.assoc, Category.assoc, ← pullback.condition]
    simpa only [Category.assoc] using
      congrArg (fun t => t ≫ (WeightOneBoundaryNorm.evaluationPoint k a).left) hfst
  · simpa only [Category.assoc] using hsnd

/-- The actual affine pullback chart, with the polynomial action given by evaluation. -/
def fiberSchemeIso (a : k) : fiber Z a ≅
    Spec (.of (Algebra.PolynomialFiber.Fiber (coordinateRing Z) a)) := by
  letI : Algebra k[X] k := Algebra.PolynomialFiber.evaluationAlgebra a
  have H : IsPullback (fiberProjection Z a)
      (pullback.snd (WeightOneBoundaryNorm.evaluationPoint k a).left Z.projection ≫
        Z.scheme.isoSpec.hom)
      (Spec.map (CommRingCat.ofHom (algebraMap k[X] k)))
      (Spec.map (CommRingCat.ofHom (algebraMap k[X] (coordinateRing Z)))) :=
    (IsPullback.of_hasPullback (WeightOneBoundaryNorm.evaluationPoint k a).left Z.projection).of_iso
      (Iso.refl _) (Iso.refl _) Z.scheme.isoSpec (WeightOneBoundaryNorm.oneSchemeIso k)
      (by simp [fiberProjection]) (by simp)
      (by
        change (WeightOneBoundaryNorm.evaluationPoint k a).left ≫
          (WeightOneBoundaryNorm.oneSchemeIso k).hom =
          𝟙 _ ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))
        rw [Category.id_comp]
        exact WeightOneBoundaryNorm.evaluationPoint_oneSchemeIso k a)
      (supportIsoSpec_projection Z).symm
  exact H.isoPullback ≪≫ pullbackSpecIso k[X] k (coordinateRing Z)

/-- The inverse fiber chart preserves the actual map to the base point. -/
theorem fiberSchemeIso_inv_fst (a : k) :
    (fiberSchemeIso Z a).inv ≫ fiberProjection Z a =
      Spec.map (CommRingCat.ofHom
        (algebraMap k (Algebra.PolynomialFiber.Fiber (coordinateRing Z) a))) := by
  let : Algebra k[X] k := Algebra.PolynomialFiber.evaluationAlgebra a
  simp only [fiberSchemeIso, Iso.trans_inv, Category.assoc, IsPullback.isoPullback_inv_fst]
  exact pullbackSpecIso_inv_fst' k[X] k (coordinateRing Z)

/-- The inverse fiber chart preserves the original support projection. -/
theorem fiberSchemeIso_inv_snd (a : k) :
    (fiberSchemeIso Z a).inv ≫
      pullback.snd (WeightOneBoundaryNorm.evaluationPoint k a).left Z.projection ≫
      Z.scheme.isoSpec.hom =
      Spec.map (CommRingCat.ofHom
        (Algebra.PolynomialFiber.specialize (coordinateRing Z) a)) := by
  let : Algebra k[X] k := Algebra.PolynomialFiber.evaluationAlgebra a
  simp only [fiberSchemeIso, Iso.trans_inv, Category.assoc, IsPullback.isoPullback_inv_snd]
  exact pullbackSpecIso_inv_snd k[X] k (coordinateRing Z)


/-- The same whole fiber in the original affine polynomial chart. -/
def affineFiberIso (a : k) : fiber Z a ≅
    AlgebraicGeometry.FiniteFlatCurve.fiber
      (Spec.map (CommRingCat.ofHom (scalarMap Z))) a := by
  let : Algebra k[X] k := Algebra.PolynomialFiber.evaluationAlgebra a
  exact fiberSchemeIso Z a ≪≫ (pullbackSpecIso k[X] k (coordinateRing Z)).symm

/-- The affine fiber chart retains the original map to the field point. -/
theorem affineFiberIso_inv_fst (a : k) :
    (affineFiberIso Z a).inv ≫ fiberProjection Z a =
      pullback.fst (AlgebraicGeometry.FiniteFlatCurve.endpoint a)
        (Spec.map (CommRingCat.ofHom (scalarMap Z))) := by
  let : Algebra k[X] k := Algebra.PolynomialFiber.evaluationAlgebra a
  change (pullbackSpecIso k[X] k (coordinateRing Z)).hom ≫
    (fiberSchemeIso Z a).inv ≫ fiberProjection Z a = _
  rw [fiberSchemeIso_inv_fst]
  exact pullbackSpecIso_hom_fst k[X] k (coordinateRing Z)

/-- The affine chart retains the original map to the whole support. -/
theorem affineFiberIso_inv_snd (a : k) :
    (affineFiberIso Z a).inv ≫
      pullback.snd (WeightOneBoundaryNorm.evaluationPoint k a).left Z.projection ≫
        Z.scheme.isoSpec.hom =
      AlgebraicGeometry.FiniteFlatCurve.fiberInclusion
        (Spec.map (CommRingCat.ofHom (scalarMap Z))) a := by
  let : Algebra k[X] k := Algebra.PolynomialFiber.evaluationAlgebra a
  simp only [affineFiberIso, Iso.trans_inv, Iso.symm_inv, Category.assoc]
  rw [fiberSchemeIso_inv_snd]
  exact pullbackSpecIso_hom_snd k[X] k (coordinateRing Z)

end Motivic.DiagonalBoundarySupport
