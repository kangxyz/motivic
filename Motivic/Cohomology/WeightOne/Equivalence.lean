/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightOne.HomologyNorm
public import Motivic.Cohomology.WeightOne.SplitPolynomialCycle
public import Motivic.Cohomology.WeightOne.PointPolynomial

/-!
# The actual weight-one equivalence

Actual finite-flat polynomial interpolation identifies the genuine homology
classes of closed points with their norm graphs. The original identity-axis
quotient removes the identity graph.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Polynomial

universe w u

namespace Motivic.WeightOneEquivalence
open _root_.AlgebraicGeometry.Scheme

open _root_.AlgebraicSimplex
open _root_.Motivic.PresheafWithTransfers
open WeightOneHomologyNorm
open WeightOneBoundaryNorm
open WeightOnePointNorm WeightOneInterpolationCycle WeightOneSplitPolynomialCycle

variable (k : Type u) [Field k]

/-- Every genuine homology class comes from the actual top raw term. -/
theorem rawClass_surjective : Function.Surjective (rawClass k) := by
  apply (AddCommGrpCat.epi_iff_surjective _).mp
  unfold rawClass
  infer_instance

/-- The actual raw class map kills the actual preceding differential. -/
theorem differential_rawClass :
    (motivicRawBaseComplex k 1).d 0 1 ≫ rawClass k = 0 := by
  rw [rawClass, ← (motivicRawBaseComplex k 1).toCycles_i 0 1]
  simp only [Category.assoc, HomologicalComplex.iCyclesIso_hom_inv_id_assoc,
    HomologicalComplex.toCycles_comp_homologyπ]

/-- The class of every actual boundary vanishes. -/
theorem rawClass_boundary (x : (motivicRawBaseComplex k 1).X 0) :
    rawClass k ((motivicRawBaseComplex k 1).d 0 1 x) = 0 :=
  ConcreteCategory.congr_hom (differential_rawClass k) x

/-- The actual singular degree-zero class map. -/
def singularClass : sections (reducedTorus k 1)
    (Cor.simplexProduct (point k) 0) →+
      (motivicRawBaseComplex k 1).homology 1 :=
  (rawClass k).hom.comp (motivicRawBaseComplexXIso k 1 0).inv.hom

/-- Singular boundaries vanish in the actual shifted homology. -/
theorem singularClass_boundary
    (s : sections (reducedTorus k 1) (Cor.simplexProduct (point k) 1)) :
    singularClass k ((singularObj (reducedTorus k 1) (point k)).d 1 0 s) = 0 := by
  have h := rawClass_boundary k ((motivicRawBaseComplexXIso k 1 1).inv s)
  rw [raw_d_zero_one] at h
  change rawClass k (-((motivicRawBaseComplexXIso k 1 0).inv
    ((singularObj (reducedTorus k 1) (point k)).d 1 0
      ((motivicRawBaseComplexXIso k 1 1).hom
        ((motivicRawBaseComplexXIso k 1 1).inv s))))) = 0 at h
  rw [Iso.inv_hom_id_apply, map_neg, neg_eq_zero] at h
  exact h

/-- The actual homology class map on signed finite point correspondences. -/
def cycleClass : (point k ⟶ WeightOnePointNorm.target k) →+
    (motivicRawBaseComplex k 1).homology 1 :=
  (singularClass k).comp
    (((toReducedTorus k 1).hom.app (op (Cor.simplexProduct (point k) 0))).hom.comp
      ((AddEquiv.ulift : ULift.{u + 1}
        (Cor.simplexProduct (point k) 0 ⟶ WeightOnePointNorm.target k) ≃+
          (Cor.simplexProduct (point k) 0 ⟶ WeightOnePointNorm.target k)).symm.toAddMonoidHom.comp
        (Preadditive.leftComp (WeightOnePointNorm.target k) (zeroProductIso k).hom)))

/-- Graph notation agrees literally with the original norm section. -/
theorem cycleClass_graph (a : kˣ) :
    cycleClass k ((Cor.graphFunctor k).map (rationalPoint k a)) = graphUnitClass k a := rfl

/-- Every homology class has a signed point-cycle representative. -/
theorem cycleClass_surjective : Function.Surjective (cycleClass k) := by
  intro y
  obtain ⟨x, rfl⟩ := rawClass_surjective k y
  obtain ⟨⟨α⟩, hα⟩ := toReducedTorus_surjective k 1
    (Cor.simplexProduct (point k) 0) ((motivicRawBaseComplexXIso k 1 0).hom x)
  refine ⟨(zeroProductIso k).inv ≫ α, ?_⟩
  change rawClass k ((motivicRawBaseComplexXIso k 1 0).inv
    ((toReducedTorus k 1).hom.app (op (Cor.simplexProduct (point k) 0))
      (ULift.up ((zeroProductIso k).hom ≫ (zeroProductIso k).inv ≫ α)))) = _
  rw [Iso.hom_inv_id_assoc, hα, Iso.hom_inv_id_apply]

/-- The norm of an actual represented cycle is the original closed-point norm. -/
theorem homologyNorm_cycleClass (α : point k ⟶ WeightOnePointNorm.target k) :
    homologyNorm k (cycleClass k α) = cycleNorm k α := by
  change homologyNorm k (rawClass k ((motivicRawBaseComplexXIso k 1 0).inv
    ((toReducedTorus k 1).hom.app (op (Cor.simplexProduct (point k) 0))
      (ULift.up ((zeroProductIso k).hom ≫ α))))) = _
  rw [homologyNorm_rawClass]
  change degreeZeroNorm k ((motivicRawBaseComplexXIso k 1 0).hom
    ((motivicRawBaseComplexXIso k 1 0).inv
      ((toReducedTorus k 1).hom.app (op (Cor.simplexProduct (point k) 0))
        (ULift.up ((zeroProductIso k).hom ≫ α))))) = _
  rw [Iso.inv_hom_id_apply, degreeZeroNorm_quotient, Iso.inv_hom_id_assoc]

/-- The unit-one section is precisely the original inserted identity axis. -/
theorem rationalPoint_one : rationalPoint k 1 = SmoothSite.torusInsertOne (.of k) 0 0 := by
  apply SmoothSite.torusPower_hom_ext
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rw [rationalPoint, SmoothSite.torusPowerLift_coordinate,
    SmoothSite.torusInsertOne_coordinate_self]
  apply MorphismProperty.Over.Hom.ext
  change _ = 𝟙 (Spec (.of k)) ≫ _
  rw [Category.id_comp]
  rfl

/-- The identity graph is killed by the actual reduced-torus quotient. -/
theorem graphUnitClass_one : graphUnitClass k 1 = 0 := by
  rw [← cycleClass_graph, rationalPoint_one]
  have h := congrArg (fun η => η.hom.app
      (op (Cor.simplexProduct (point k) 0)))
    (torusIdentityAxis_toReducedTorus k 1 0)
  have he := ConcreteCategory.congr_hom h (ULift.up (zeroProductIso k).hom)
  change (toReducedTorus k 1).hom.app (op (Cor.simplexProduct (point k) 0))
    (ULift.up ((zeroProductIso k).hom ≫
      (Cor.graphFunctor k).map (SmoothSite.torusInsertOne (.of k) 0 0))) = 0 at he
  change singularClass k ((toReducedTorus k 1).hom.app
    (op (Cor.simplexProduct (point k) 0))
      (ULift.up ((zeroProductIso k).hom ≫
        (Cor.graphFunctor k).map (SmoothSite.torusInsertOne (.of k) 0 0)))) = 0
  rw [he, map_zero]

/-- A represented singular zero-simplex has the class of its actual base point cycle. -/
theorem singularClass_quotient
    (α : Cor.simplexProduct (point k) 0 ⟶ WeightOnePointNorm.target k) :
    singularClass k ((toReducedTorus k 1).hom.app
      (op (Cor.simplexProduct (point k) 0)) (ULift.up α)) =
        cycleClass k ((zeroProductIso k).inv ≫ α) := by
  change _ = singularClass k ((toReducedTorus k 1).hom.app
    (op (Cor.simplexProduct (point k) 0))
      (ULift.up ((zeroProductIso k).hom ≫ (zeroProductIso k).inv ≫ α)))
  rw [Iso.hom_inv_id_assoc]

/-- A coface of a represented section has exactly its endpoint cycle class. -/
theorem singularClass_face_quotient (i : Fin 2)
    (α : Cor.simplexProduct (point k) 1 ⟶ WeightOnePointNorm.target k) :
    singularClass k (transfer (reducedTorus k 1)
      ((Cor.simplexProductCosimplicial (point k)).δ i)
        ((toReducedTorus k 1).hom.app (op (Cor.simplexProduct (point k) 1)) (ULift.up α))) =
      cycleClass k ((zeroProductIso k).inv ≫
        (Cor.simplexProductCosimplicial (point k)).δ i ≫ α) := by
  exact (congrArg (singularClass k) (reducedTorus_transfer_apply k 1
    ((Cor.simplexProductCosimplicial (point k)).δ i) α)).trans
      (singularClass_quotient k _)

/-- The two literal endpoint cycles of every singular correspondence have equal classes. -/
theorem cycleClass_endpoints
    (α : Cor.simplexProduct (point k) 1 ⟶ WeightOnePointNorm.target k) :
    cycleClass k ((zeroProductIso k).inv ≫
      (Cor.simplexProductCosimplicial (point k)).δ 0 ≫ α) =
    cycleClass k ((zeroProductIso k).inv ≫
      (Cor.simplexProductCosimplicial (point k)).δ 1 ≫ α) := by
  have h := singularClass_boundary k ((toReducedTorus k 1).hom.app
    (op (Cor.simplexProduct (point k) 1)) (ULift.up α))
  rw [singular_d_one_zero] at h
  change singularClass k
    (transfer (reducedTorus k 1) ((Cor.simplexProductCosimplicial (point k)).δ 0)
      ((toReducedTorus k 1).hom.app (op (Cor.simplexProduct (point k) 1)) (ULift.up α)) -
    transfer (reducedTorus k 1) ((Cor.simplexProductCosimplicial (point k)).δ 1)
      ((toReducedTorus k 1).hom.app (op (Cor.simplexProduct (point k) 1)) (ULift.up α))) = 0 at h
  rw [map_sub, singularClass_face_quotient, singularClass_face_quotient, sub_eq_zero] at h
  exact h

/-- Actual finite-flat interpolation identifies the complete endpoint cycles in homology. -/
theorem cycleClass_polynomial_target (p : k[X]) (hp : p.Monic)
    (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0) :
    cycleClass k (polynomialCycle p hp h0) =
      cycleClass k (polynomialCycle (Polynomial.MonicUnitInterpolation.target p)
        (Polynomial.MonicUnitInterpolation.target_monic p)
        ((Polynomial.MonicUnitInterpolation.target_coeff_zero p hd).trans_ne h0)) := by
  have h := cycleClass_endpoints k (singularCorrespondence hp hd h0)
  rw [singularCorrespondence_face_zero, singularCorrespondence_face_one] at h
  exact h

/-- Every actual polynomial cycle has the graph class of its signed constant coefficient. -/
theorem cycleClass_polynomial (p : k[X]) (hp : p.Monic)
    (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0) :
    cycleClass k (polynomialCycle p hp h0) =
      graphUnitClass k (Units.mk0 (Polynomial.MonicUnitInterpolation.normValue p)
        (Polynomial.MonicUnitInterpolation.normValue_ne_zero p h0)) := by
  rw [cycleClass_polynomial_target k p hp hd h0, polynomialCycle_target p hd h0,
    map_add, map_zsmul, cycleClass_graph, cycleClass_graph, graphUnitClass_one,
    zsmul_zero, add_zero]

/-- Quadratic interpolation gives the multiplicative law of actual graph classes. -/
theorem graphUnitClass_mul (a b : kˣ) :
    graphUnitClass k (a * b) = graphUnitClass k a + graphUnitClass k b := by
  let p : k[X] := (X - C (a : k)) * (X - C (b : k))
  have hd : 1 ≤ p.natDegree := by rw [twoLinear_natDegree]; decide
  have h := cycleClass_polynomial k p (twoLinear_monic a b) hd
    (twoLinear_coeff_zero_ne_zero a b)
  rw [polynomialCycle_twoLinear, map_add, cycleClass_graph, cycleClass_graph] at h
  have hu : Units.mk0 (Polynomial.MonicUnitInterpolation.normValue p)
      (Polynomial.MonicUnitInterpolation.normValue_ne_zero p
        (twoLinear_coeff_zero_ne_zero a b)) = a * b := by
    apply Units.ext
    exact twoLinear_normValue a b
  rw [hu] at h
  exact h.symm

/-- The genuine graph section is an additive homomorphism from the original unit group. -/
def graphUnitHom : Additive kˣ →+ (motivicRawBaseComplex k 1).homology 1 where
  toFun a := graphUnitClass k a.toMul
  map_zero' := graphUnitClass_one k
  map_add' a b := graphUnitClass_mul k a.toMul b.toMul

/-- Every actual point generator has precisely the graph class of its field norm. -/
theorem cycleClass_generator (Z : WeightOnePointNorm.Generator k) :
    cycleClass k Z.cycle = graphUnitClass k (generatorNorm Z) := by
  obtain ⟨p, hp, h0, hd, hZ⟩ := WeightOnePointPolynomial.exists_polynomialCycle Z
  have h : cycleClass k Z.cycle =
      graphUnitClass k (Units.mk0 (Polynomial.MonicUnitInterpolation.normValue p)
        (Polynomial.MonicUnitInterpolation.normValue_ne_zero p h0)) := by
    rw [hZ]
    exact cycleClass_polynomial k p hp hd h0
  have hn := congrArg (homologyNorm k) h
  rw [homologyNorm_cycleClass, cycleNorm_cycle, homologyNorm_graphUnitClass] at hn
  have hu := congrArg Additive.toMul hn
  change generatorNorm Z = Units.mk0 (Polynomial.MonicUnitInterpolation.normValue p)
    (Polynomial.MonicUnitInterpolation.normValue_ne_zero p h0) at hu
  exact h.trans (congrArg (graphUnitClass k) hu.symm)

/-- Signed sums of actual point generators retain the inverse norm formula. -/
theorem graphUnitHom_comp_cycleNorm :
    (graphUnitHom k).comp (cycleNorm k) = cycleClass k := by
  apply Finsupp.addHom_ext'
  intro Z
  apply AddMonoidHom.ext_int
  change graphUnitHom k (cycleNorm k Z.cycle) = cycleClass k Z.cycle
  rw [cycleNorm_cycle]
  exact (cycleClass_generator k Z).symm

/-- The graph homomorphism is a left inverse to the genuine homology norm. -/
theorem graphUnitHom_homologyNorm (x : (motivicRawBaseComplex k 1).homology 1) :
    graphUnitHom k (homologyNorm k x) = x := by
  obtain ⟨α, rfl⟩ := cycleClass_surjective k x
  rw [homologyNorm_cycleClass]
  exact DFunLike.congr_fun (graphUnitHom_comp_cycleNorm k) α

/-- The norm on actual homology is injective over every field. -/
theorem homologyNorm_injective : Function.Injective (homologyNorm k) :=
  Function.LeftInverse.injective (graphUnitHom_homologyNorm k)

/-- The actual raw weight-one homology is the original field's unit group. -/
def homologyEquiv : (motivicRawBaseComplex k 1).homology 1 ≃+ Additive kˣ :=
  AddEquiv.ofBijective (homologyNorm k)
    ⟨homologyNorm_injective k, homologyNorm_surjective k⟩

/-- The homology equivalence is exactly the descended geometric norm. -/
theorem homologyEquiv_apply (x : (motivicRawBaseComplex k 1).homology 1) :
    homologyEquiv k x = homologyNorm k x := rfl

/-- Its inverse sends each unit to its literal rational graph class. -/
theorem homologyEquiv_symm_apply (a : Additive kˣ) :
    (homologyEquiv k).symm a = graphUnitClass k a.toMul := by
  apply (homologyEquiv k).injective
  rw [AddEquiv.apply_symm_apply, homologyEquiv_apply, homologyNorm_graphUnitClass]
  rfl

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The genuinely defined derived motivic norm is injective. -/
theorem motivicNorm_injective : Function.Injective (motivicNorm k) :=
  (homologyNorm_injective k).comp (motivicRawBaseEvaluationComparison k 1 1).injective

/-- Weight-one motivic cohomology of the actual base field is its group of units. -/
def weightOneEquiv :
    motivicCohomology k 1 1 (SmoothSite.base (Spec (.of k))) ≃+ Additive kˣ :=
  (motivicRawBaseEvaluationComparison k 1 1).trans (homologyEquiv k)

/-- The equivalence acts by the actual derived geometric norm. -/
theorem weightOneEquiv_apply
    (x : motivicCohomology k 1 1 (SmoothSite.base (Spec (.of k)))) :
    weightOneEquiv k x = motivicNorm k x := rfl

/-- The inverse is the literal graph class transported by the existing derived comparison. -/
theorem weightOneEquiv_symm_apply (a : Additive kˣ) :
    (weightOneEquiv k).symm a =
      (motivicRawBaseEvaluationComparison k 1 1).symm (graphUnitClass k a.toMul) := by
  change (motivicRawBaseEvaluationComparison k 1 1).symm ((homologyEquiv k).symm a) = _
  rw [homologyEquiv_symm_apply]

end Motivic.WeightOneEquivalence
