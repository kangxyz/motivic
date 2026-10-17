/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.WeightOneBoundaryNorm
public import Motivic.Cohomology.Motivic.WeightOneFundamentalNorm
public import Motivic.Aglib.RingTheory.MonicUnitInterpolation
public import Motivic.Aglib.AlgebraicGeometry.FiniteFlatCurveSpecialization

/-!
# The whole finite-flat monic interpolation scheme

The original quotient algebra is used without reduction. Its actual finite-flat
map to the one-simplex and invertible coordinate determine a finite morphism
into the canonical simplex-torus product. All generic local lengths are kept
when assembling its fundamental correspondence.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Polynomial Polynomial.MonicUnitInterpolation
open AlgebraicGeometry.Scheme.PolynomialLaurent
open scoped BigOperators

universe u

namespace Motivic.WeightOneInterpolationCycle

variable {k : Type u} [Field k]

/-- The entire monic quotient, including all nilpotents and components. -/
abbrev familyScheme (p : k[X]) : Scheme.{u} := Spec (.of (FamilyAlgebra p))

/-- The literal structure map to the affine parameter line. -/
def affineProjection (p : k[X]) : familyScheme p ⟶ Spec (.of k[X]) :=
  Spec.map (CommRingCat.ofHom (AdjoinRoot.of (family p)))

/-- The literal finite-flat projection, in the actual simplex chart. -/
def projection (p : k[X]) : familyScheme p ⟶ (AlgebraicSimplex.smoothSiteObj k 1).left :=
  affineProjection p ≫ (WeightOneBoundaryNorm.oneSchemeIso k).inv

/-- Polynomial and simplex parameters are identified by the specified chart. -/
@[reassoc (attr := simp)] theorem projection_oneSchemeIso (p : k[X]) :
    projection p ≫ (WeightOneBoundaryNorm.oneSchemeIso k).hom = affineProjection p := by
  simp [projection]

/-- The whole family is finite over the actual one-simplex. -/
theorem projection_finite {p : k[X]} (hp : p.Monic) (hd : 1 ≤ p.natDegree) :
    IsFinite (projection p) := by
  let : Module.Finite k[X] (FamilyAlgebra p) := family_finite hp hd
  have : IsFinite (affineProjection p) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  unfold projection
  infer_instance

/-- The whole family is flat; this does not assert it is integral or reduced. -/
theorem projection_flat {p : k[X]} (hp : p.Monic) (hd : 1 ≤ p.natDegree) :
    Flat (projection p) := by
  let : Module.Free k[X] (FamilyAlgebra p) := family_free hp hd
  have : Flat (affineProjection p) := by
    apply Flat.SpecMap_iff.mpr
    change (AdjoinRoot.of (family p)).Flat
    rw [← AdjoinRoot.algebraMap_eq]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  unfold projection
  infer_instance

/-- The constant field action on the original quotient. -/
def constantMap (p : k[X]) : k →+* FamilyAlgebra p :=
  (AdjoinRoot.of (family p)).comp Polynomial.C

/-- The unit coordinate gives the genuine Laurent-torus morphism. -/
def torusMap (p : k[X]) (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0) :
    familyScheme p ⟶ (SmoothSite.torus (.of k)).left :=
  Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ (constantMap p)
    (coordinateUnit p hd h0)))

/-- The same coordinate in the canonical recursive one-fold torus power. -/
def targetMap (p : k[X]) (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0) :
    familyScheme p ⟶ (SmoothSite.torusPower (.of k) 1).left :=
  torusMap p hd h0 ≫ (SmoothSite.torusPowerOneIso (.of k)).inv.left

@[reassoc (attr := simp)] theorem targetMap_coordinate (p : k[X])
    (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0) :
    targetMap p hd h0 ≫ (SmoothSite.torusCoordinate (.of k) 1 0).left =
      torusMap p hd h0 := by
  change torusMap p hd h0 ≫ (SmoothSite.torusPowerOneIso (.of k)).inv.left ≫
    (SmoothSite.torusPowerOneIso (.of k)).hom.left = _
  have h := congrArg (fun f => f.left) (SmoothSite.torusPowerOneIso (.of k)).inv_hom_id
  change (SmoothSite.torusPowerOneIso (.of k)).inv.left ≫
    (SmoothSite.torusPowerOneIso (.of k)).hom.left = 𝟙 _ at h
  rw [h, Category.comp_id]

/-- The parameter chart retains the original field map. -/
theorem projection_structure (p : k[X]) :
    projection p ≫ (AlgebraicSimplex.smoothSiteObj k 1).hom =
      Spec.map (CommRingCat.ofHom (constantMap p)) := by
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = Spec.map _
  simp only [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  change AdjoinRoot.of (family p)
    (WeightOneBoundaryNorm.oneCoordinateEquiv k
      (algebraMap k (AlgebraicSimplex.CoordinateRing k 1) r)) = constantMap p r
  rw [(WeightOneBoundaryNorm.oneCoordinateEquiv k).commutes]
  rfl

/-- Both actual maps have the same original field structure. -/
theorem projection_base (p : k[X]) (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0) :
    projection p ≫ (AlgebraicSimplex.smoothSiteObj k 1).hom =
      targetMap p hd h0 ≫ (SmoothSite.torusPower (.of k) 1).hom := by
  rw [projection_structure]
  have ht : (SmoothSite.torusPowerOneIso (.of k)).inv.left ≫
      (SmoothSite.torusPower (.of k) 1).hom = (SmoothSite.torus (.of k)).hom :=
    MorphismProperty.Over.w (SmoothSite.torusPowerOneIso (.of k)).inv
  rw [targetMap, Category.assoc, ht]
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  change constantMap p r =
    LaurentPolynomial.eval₂ (constantMap p) (coordinateUnit p hd h0) (LaurentPolynomial.C r)
  exact (LaurentPolynomial.eval₂_C _ _ _).symm

/-- The actual simplex-torus ambient scheme. -/
abbrev ambient (k : Type u) [Field k] : Scheme.{u} :=
  pullback (AlgebraicSimplex.smoothSiteObj k 1).hom (SmoothSite.torusPower (.of k) 1).hom

/-- The whole scheme maps by its parameter and its invertible coordinate. -/
def inclusion (p : k[X]) (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0) :
    familyScheme p ⟶ ambient k :=
  pullback.lift (projection p) (targetMap p hd h0) (projection_base p hd h0)

@[reassoc (attr := simp)] theorem inclusion_fst (p : k[X])
    (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0) :
    inclusion p hd h0 ≫ pullback.fst _ _ = projection p := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem inclusion_snd (p : k[X])
    (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0) :
    inclusion p hd h0 ≫ pullback.snd _ _ = targetMap p hd h0 := pullback.lift_snd _ _ _

/-- Finiteness holds for the whole map into the separated torus product. -/
theorem inclusion_finite {p : k[X]} (hp : p.Monic) (hd : 1 ≤ p.natDegree)
    (h0 : p.coeff 0 ≠ 0) : IsFinite (inclusion p hd h0) := by
  have : IsFinite (inclusion p hd h0 ≫ pullback.fst _ _) := by
    rw [inclusion_fst]
    exact projection_finite hp hd
  exact IsFinite.of_comp (inclusion p hd h0) (pullback.fst _ _)

/-- An affine target map expressed as the actual pullback of global functions. -/
def affinePullback {R : Type u} [CommRing R] {W : Scheme.{u}}
    (f : W ⟶ Spec (.of R)) : R →+* Γ(W, ⊤) :=
  f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom

/-- The affine pullback chart respects an actual spectrum morphism. -/
theorem affinePullback_comp {R S : Type u} [CommRing R] [CommRing S]
    {W : Scheme.{u}} (f : W ⟶ Spec (.of S)) (g : R →+* S) :
    affinePullback (f ≫ Spec.map (CommRingCat.ofHom g)) =
      (affinePullback f).comp g := by
  apply RingHom.ext
  intro r
  change f.appTop ((Spec.map (CommRingCat.ofHom g)).appTop
      ((Scheme.ΓSpecIso (.of R)).inv r)) =
    f.appTop ((Scheme.ΓSpecIso (.of S)).inv (g r))
  congr 1
  exact ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g)).symm r

/-- The original affine coordinates determine every map into the whole family. -/
theorem family_hom_ext (p : k[X]) (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0)
    {W : Scheme.{u}} {f g : W ⟶ familyScheme p}
    (hp : f ≫ projection p = g ≫ projection p)
    (ht : f ≫ torusMap p hd h0 = g ≫ torusMap p hd h0) : f = g := by
  have hp' : f ≫ affineProjection p = g ≫ affineProjection p := by
    simpa only [Category.assoc, projection_oneSchemeIso] using
      congrArg (fun q => q ≫ (WeightOneBoundaryNorm.oneSchemeIso k).hom) hp
  have ha : (affinePullback f).comp (AdjoinRoot.of (family p)) =
      (affinePullback g).comp (AdjoinRoot.of (family p)) := by
    simpa only [affineProjection, affinePullback_comp] using congrArg affinePullback hp'
  have hb := congrArg affinePullback ht
  simp only [torusMap, affinePullback_comp] at hb
  have hc := RingHom.congr_fun hb (LaurentPolynomial.T 1)
  simp only [RingHom.comp_apply, LaurentPolynomial.eval₂_T, zpow_one,
    coordinateUnit_val] at hc
  have he := AdjoinRoot.ringHom_ext ha hc
  apply ext_of_isAffine
  apply (cancel_epi (Scheme.ΓSpecIso (.of (FamilyAlgebra p))).inv).mp
  exact CommRingCat.hom_ext he

/-- The parameter and unit coordinate embed the entire quotient scheme. -/
theorem inclusion_closed {p : k[X]} (hp : p.Monic) (hd : 1 ≤ p.natDegree)
    (h0 : p.coeff 0 ≠ 0) : IsClosedImmersion (inclusion p hd h0) := by
  have : IsFinite (inclusion p hd h0) := inclusion_finite hp hd h0
  apply (IsClosedImmersion.iff_isFinite_and_mono _).mpr
  refine ⟨inferInstance, ⟨?_⟩⟩
  intro W f g h
  apply family_hom_ext p hd h0
  · simpa only [Category.assoc, inclusion_fst] using
      congrArg (fun t => t ≫ pullback.fst _ _) h
  · simpa only [Category.assoc, inclusion_snd_assoc, targetMap_coordinate] using
      congrArg (fun t => t ≫ pullback.snd _ _ ≫
        (SmoothSite.torusCoordinate (.of k) 1 0).left) h

private instance baseIntegralLiteral :
    IsIntegral (SmoothSite.base (Spec (.of k))).left :=
  inferInstanceAs (IsIntegral (Spec (.of k)))

private instance baseIntegral :
    IsIntegral ((𝟭 Scheme).obj (SmoothSite.base (Spec (.of k))).left) :=
  inferInstanceAs (IsIntegral (Spec (.of k)))

private instance simplexIntegralLiteral :
    IsIntegral (AlgebraicSimplex.smoothSiteObj k 1).left :=
  inferInstanceAs (IsIntegral (Spec (.of (AlgebraicSimplex.CoordinateRing k 1))))

private instance simplexIntegral :
    IsIntegral ((𝟭 Scheme).obj (AlgebraicSimplex.smoothSiteObj k 1).left) :=
  inferInstanceAs (IsIntegral (Spec (.of (AlgebraicSimplex.CoordinateRing k 1))))

/-- Each actual component of the whole family, with its original reduced support. -/
abbrev componentSupport (p : k[X]) (z : genericPoints (familyScheme p)) :=
  IntegralClosedSubscheme.pointClosure z.val

/-- Every component dominates the simplex because the WHOLE projection is flat and finite. -/
theorem component_projection_surjective {p : k[X]} (hp : p.Monic)
    (hd : 1 ≤ p.natDegree) (z : genericPoints (familyScheme p)) :
    Function.Surjective ((componentSupport p z).val.subschemeι ≫ projection p) := by
  have : IsFinite (projection p) := projection_finite hp hd
  have : Flat (projection p) := projection_flat hp hd
  exact surjective_pointClosure_of_finite_generalizing (projection p)
    (Flat.generalizingMap (projection p)) z.val z.property

/-- Every actual component image is an admissible finite-correspondence generator. -/
def componentGenerator {p : k[X]} (hp : p.Monic) (hd : 1 ≤ p.natDegree)
    (h0 : p.coeff 0 ≠ 0) (z : genericPoints (familyScheme p)) :
    WeightOneBoundaryNorm.Generator k := by
  let : IrreducibleSpace (AlgebraicSimplex.smoothSiteObj k 1).left :=
    inferInstanceAs (IrreducibleSpace (Spec (.of (AlgebraicSimplex.CoordinateRing k 1))))
  have : IsFinite (projection p) := projection_finite hp hd
  have : IsFinite (inclusion p hd h0) := inclusion_finite hp hd h0
  let C := componentSupport p z
  let j := C.val.subschemeι ≫ inclusion p hd h0
  have hj : IsFinite (j ≫ pullback.fst
      (AlgebraicSimplex.smoothSiteObj k 1).hom (SmoothSite.torusPower (.of k) 1).hom) := by
    dsimp only [j]
    rw [Category.assoc, inclusion_fst]
    infer_instance
  refine ⟨(C.finiteImage (inclusion p hd h0)).val,
    (C.finiteImage (inclusion p hd h0)).property,
    isFinite_image_projection j (pullback.fst _ _), ?_⟩
  change Set.range (j.imageι ≫ pullback.fst _ _) ∈ irreducibleComponents _
  rw [range_image_projection]
  change Set.range ((C.val.subschemeι ≫ inclusion p hd h0) ≫ pullback.fst _ _) ∈ _
  rw [Category.assoc, inclusion_fst]
  change Set.range ((componentSupport p z).val.subschemeι ≫ projection p) ∈ _
  rw [Set.range_eq_univ.mpr (component_projection_surjective hp hd z)]
  exact (irreducibleComponents_eq_singleton
    (X := (AlgebraicSimplex.smoothSiteObj k 1).left)) ▸ Set.mem_singleton _

/-- The admissible generator retains the literal image ideal of the original component. -/
@[simp] theorem componentGenerator_toIntegralClosedSubscheme {p : k[X]} (hp : p.Monic)
    (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0) (z : genericPoints (familyScheme p)) :
    letI := inclusion_finite hp hd h0
    (componentGenerator hp hd h0 z).toIntegralClosedSubscheme =
      (componentSupport p z).finiteImage (inclusion p hd h0) := rfl

/-- The signed finite correspondence of the WHOLE family: every generic component
is weighted by the length of its original local ring. -/
def fundamentalCorrespondence {p : k[X]} (hp : p.Monic) (hd : 1 ≤ p.natDegree)
    (h0 : p.coeff 0 ≠ 0) :
    Cor.mk (AlgebraicSimplex.smoothSiteObj k 1) ⟶ WeightOnePointNorm.target k := by
  classical
  let := IntegralCycle.genericPointFintype (familyScheme p)
  exact ∑ z, (genericMultiplicity z : ℤ) • (componentGenerator hp hd h0 z).cycle

/-- Forgetting admissibility gives exactly the pushed original fundamental cycle. -/
theorem toIntegralCycle_fundamentalCorrespondence {p : k[X]} (hp : p.Monic)
    (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0) :
    letI := inclusion_closed hp hd h0
    FiniteCorrespondence.toIntegralCycle (fundamentalCorrespondence hp hd h0) =
      IntegralCycle.finitePushforward (inclusion p hd h0) (fundamentalCycle (familyScheme p)) := by
  classical
  let := IntegralCycle.genericPointFintype (familyScheme p)
  let := inclusion_closed hp hd h0
  rw [← IntegralCycle.ofGenericCoefficients_genericMultiplicity,
    IntegralCycle.ofGenericCoefficients_eq_sum, map_sum]
  unfold fundamentalCorrespondence
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [map_zsmul, FiniteCorrespondenceGenerator.cycle,
    FiniteCorrespondence.toIntegralCycle_single, componentGenerator_toIntegralClosedSubscheme,
    IntegralCycle.finitePushforward_single, residueDegree_of_surjectiveOnStalks]
  simp only [Nat.cast_one, mul_one, Finsupp.smul_single, smul_eq_mul, mul_one]

/-- The actual root unit in an arbitrary endpoint quotient. -/
def polynomialUnit (p : k[X]) (h0 : p.coeff 0 ≠ 0) : (AdjoinRoot p)ˣ :=
  (adjoinRoot_root_isUnit p (isUnit_iff_ne_zero.mpr h0)).unit

@[simp] theorem polynomialUnit_val (p : k[X]) (h0 : p.coeff 0 ≠ 0) :
    (polynomialUnit p h0 : AdjoinRoot p) = AdjoinRoot.root p := IsUnit.unit_spec _

/-- The entire endpoint quotient maps to the Laurent torus through its root unit. -/
def polynomialTorusMap (p : k[X]) (h0 : p.coeff 0 ≠ 0) :
    Spec (.of (AdjoinRoot p)) ⟶ (SmoothSite.torus (.of k)).left :=
  Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ (AdjoinRoot.of p) (polynomialUnit p h0)))

/-- The quotient is a closed subscheme of the torus because its root generates it. -/
instance polynomialTorusMap_closed (p : k[X]) (h0 : p.coeff 0 ≠ 0) :
    IsClosedImmersion (polynomialTorusMap p h0) := by
  apply IsClosedImmersion.spec_of_surjective
  intro r
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective r
  refine ⟨Polynomial.toLaurent f, ?_⟩
  change LaurentPolynomial.eval₂ (AdjoinRoot.of p) (polynomialUnit p h0)
    (Polynomial.toLaurent f) = AdjoinRoot.mk p f
  rw [LaurentPolynomial.eval₂_toLaurent, polynomialUnit_val, ← AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.aeval_eq f

/-- Endpoint map to the same canonical one-fold torus used throughout. -/
def polynomialTargetMap (p : k[X]) (h0 : p.coeff 0 ≠ 0) :
    Spec (.of (AdjoinRoot p)) ⟶ (SmoothSite.torusPower (.of k) 1).left :=
  polynomialTorusMap p h0 ≫ (SmoothSite.torusPowerOneIso (.of k)).inv.left

@[reassoc (attr := simp)] theorem polynomialTargetMap_coordinate (p : k[X])
    (h0 : p.coeff 0 ≠ 0) :
    polynomialTargetMap p h0 ≫ (SmoothSite.torusCoordinate (.of k) 1 0).left =
      polynomialTorusMap p h0 := by
  change polynomialTorusMap p h0 ≫ (SmoothSite.torusPowerOneIso (.of k)).inv.left ≫
    (SmoothSite.torusPowerOneIso (.of k)).hom.left = _
  have h := congrArg (fun f => f.left) (SmoothSite.torusPowerOneIso (.of k)).inv_hom_id
  change (SmoothSite.torusPowerOneIso (.of k)).inv.left ≫
    (SmoothSite.torusPowerOneIso (.of k)).hom.left = 𝟙 _ at h
  rw [h, Category.comp_id]

/-- The endpoint map is over the original field with its actual quotient scalar map. -/
theorem polynomialTargetMap_structure (p : k[X]) (h0 : p.coeff 0 ≠ 0) :
    polynomialTargetMap p h0 ≫ (SmoothSite.torusPower (.of k) 1).hom =
      Spec.map (CommRingCat.ofHom (AdjoinRoot.of p)) := by
  have ht : (SmoothSite.torusPowerOneIso (.of k)).inv.left ≫
      (SmoothSite.torusPower (.of k) 1).hom = (SmoothSite.torus (.of k)).hom :=
    MorphismProperty.Over.w (SmoothSite.torusPowerOneIso (.of k)).inv
  rw [polynomialTargetMap, Category.assoc, ht]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact LaurentPolynomial.eval₂_C _ _ r

/-- The whole endpoint polynomial scheme in the actual point-torus ambient product. -/
def polynomialInclusion (p : k[X]) (h0 : p.coeff 0 ≠ 0) :
    Spec (.of (AdjoinRoot p)) ⟶ WeightOneFundamentalNorm.ambient k :=
  pullback.lift (Spec.map (CommRingCat.ofHom (AdjoinRoot.of p)))
    (polynomialTargetMap p h0) (by
      change Spec.map _ ≫ 𝟙 _ = _
      rw [Category.comp_id, polynomialTargetMap_structure])

@[reassoc (attr := simp)] theorem polynomialInclusion_fst (p : k[X])
    (h0 : p.coeff 0 ≠ 0) :
    polynomialInclusion p h0 ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (AdjoinRoot.of p)) := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem polynomialInclusion_snd (p : k[X])
    (h0 : p.coeff 0 ≠ 0) :
    polynomialInclusion p h0 ≫ pullback.snd _ _ =
      polynomialTargetMap p h0 := pullback.lift_snd _ _ _

/-- The endpoint polynomial is its actual closed subscheme, not its reduction. -/
instance polynomialInclusion_closed (p : k[X]) (h0 : p.coeff 0 ≠ 0) :
    IsClosedImmersion (polynomialInclusion p h0) := by
  let q := pullback.snd (SmoothSite.base (Spec (.of k))).hom
      (SmoothSite.torusPower (.of k) 1).hom ≫
    (SmoothSite.torusCoordinate (.of k) 1 0).left
  have : IsSeparated (SmoothSite.torusCoordinate (.of k) 1 0).left := by
    change IsSeparated (SmoothSite.torusPowerOneIso (.of k)).hom.left
    infer_instance
  have : IsSeparated q := by
    dsimp only [q]
    infer_instance
  have : IsClosedImmersion (polynomialInclusion p h0 ≫ q) := by
    dsimp only [q]
    rw [polynomialInclusion_snd_assoc, polynomialTargetMap_coordinate]
    infer_instance
  exact IsClosedImmersion.of_comp (polynomialInclusion p h0) q

/-- The actual full endpoint polynomial correspondence has every local multiplicity. -/
def polynomialCycle (p : k[X]) (hp : p.Monic) (h0 : p.coeff 0 ≠ 0) :
    WeightOnePointNorm.point k ⟶ WeightOnePointNorm.target k :=
  letI : Module.Finite k (AdjoinRoot p) := hp.finite_adjoinRoot
  WeightOneFundamentalNorm.affineFundamentalCorrespondence (polynomialInclusion p h0)
    (polynomialInclusion_fst p h0)

/-- The polynomial cycle is precisely the pushed whole quotient fundamental cycle. -/
theorem toIntegralCycle_polynomialCycle (p : k[X]) (hp : p.Monic) (h0 : p.coeff 0 ≠ 0) :
    FiniteCorrespondence.toIntegralCycle (polynomialCycle p hp h0) =
      IntegralCycle.finitePushforward (polynomialInclusion p h0)
        (fundamentalCycle (Spec (.of (AdjoinRoot p)))) := by
  let : Module.Finite k (AdjoinRoot p) := hp.finite_adjoinRoot
  exact WeightOneFundamentalNorm.toIntegralCycle_affineFundamentalCorrespondence _ _

/-- The entire scheme-theoretic family fiber at the actual affine evaluation point. -/
abbrev fiber (p : k[X]) (a : k) : Scheme.{u} :=
  pullback (WeightOneBoundaryNorm.evaluationPoint k a).left (projection p)

/-- The whole fiber projects to the original base field point. -/
abbrev fiberProjection (p : k[X]) (a : k) : fiber p a ⟶ Spec (.of k) :=
  pullback.fst (WeightOneBoundaryNorm.evaluationPoint k a).left (projection p)

/-- The other original pullback projection goes to the whole family. -/
abbrev fiberToFamily (p : k[X]) (a : k) : fiber p a ⟶ familyScheme p :=
  pullback.snd (WeightOneBoundaryNorm.evaluationPoint k a).left (projection p)

/-- The whole geometric fiber has its literal tensor-product coordinate algebra. -/
def fiberSchemeIso (p : k[X]) (a : k) : fiber p a ≅
    Spec (.of (Algebra.PolynomialFiber.Fiber (FamilyAlgebra p) a)) := by
  letI : Algebra k[X] k := Algebra.PolynomialFiber.evaluationAlgebra a
  have H : IsPullback (fiberProjection p a) (fiberToFamily p a)
      (Spec.map (CommRingCat.ofHom (algebraMap k[X] k)))
      (Spec.map (CommRingCat.ofHom (algebraMap k[X] (FamilyAlgebra p)))) :=
    (IsPullback.of_hasPullback (WeightOneBoundaryNorm.evaluationPoint k a).left
      (projection p)).of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (WeightOneBoundaryNorm.oneSchemeIso k)
      (by simp) (by simp)
      (by
        change (WeightOneBoundaryNorm.evaluationPoint k a).left ≫
          (WeightOneBoundaryNorm.oneSchemeIso k).hom =
          𝟙 _ ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))
        rw [Category.id_comp]
        exact WeightOneBoundaryNorm.evaluationPoint_oneSchemeIso k a)
      (by simpa only [Iso.refl_hom, Category.id_comp, AdjoinRoot.algebraMap_eq, affineProjection]
        using projection_oneSchemeIso p)
  exact H.isoPullback ≪≫ pullbackSpecIso k[X] k (FamilyAlgebra p)

/-- The tensor chart preserves the original field structure. -/
theorem fiberSchemeIso_inv_fst (p : k[X]) (a : k) :
    (fiberSchemeIso p a).inv ≫ fiberProjection p a =
      Spec.map (CommRingCat.ofHom
        (algebraMap k (Algebra.PolynomialFiber.Fiber (FamilyAlgebra p) a))) := by
  let : Algebra k[X] k := Algebra.PolynomialFiber.evaluationAlgebra a
  simp only [fiberSchemeIso, Iso.trans_inv, Category.assoc, IsPullback.isoPullback_inv_fst]
  exact pullbackSpecIso_inv_fst' k[X] k (FamilyAlgebra p)

/-- The tensor chart preserves the original unreduced family map. -/
theorem fiberSchemeIso_inv_snd (p : k[X]) (a : k) :
    (fiberSchemeIso p a).inv ≫ fiberToFamily p a =
      Spec.map (CommRingCat.ofHom (Algebra.PolynomialFiber.specialize (FamilyAlgebra p) a)) := by
  let : Algebra k[X] k := Algebra.PolynomialFiber.evaluationAlgebra a
  simp only [fiberSchemeIso, Iso.trans_inv, Category.assoc, IsPullback.isoPullback_inv_snd]
  exact pullbackSpecIso_inv_snd k[X] k (FamilyAlgebra p)

/-- The whole fiber maps into the same degree-zero product as a polynomial cycle. -/
def fiberInclusion (p : k[X]) (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0) (a : k) :
    fiber p a ⟶ WeightOneFundamentalNorm.ambient k :=
  pullback.lift (fiberProjection p a) (fiberToFamily p a ≫ targetMap p hd h0) (by
    rw [Category.assoc, ← projection_base, ← Category.assoc]
    change _ = (pullback.snd _ _ ≫ projection p) ≫ (AlgebraicSimplex.smoothSiteObj k 1).hom
    rw [← pullback.condition, Category.assoc, MorphismProperty.Over.w])

@[reassoc (attr := simp)] theorem fiberInclusion_fst (p : k[X])
    (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0) (a : k) :
    fiberInclusion p hd h0 a ≫ pullback.fst _ _ = fiberProjection p a :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem fiberInclusion_snd (p : k[X])
    (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0) (a : k) :
    fiberInclusion p hd h0 a ≫ pullback.snd _ _ = fiberToFamily p a ≫ targetMap p hd h0 :=
  pullback.lift_snd _ _ _

/-- Base change keeps the entire fiber finite over the field. -/
theorem fiberProjection_finite {p : k[X]} (hp : p.Monic)
    (hd : 1 ≤ p.natDegree) (a : k) : IsFinite (fiberProjection p a) := by
  have : IsFinite (projection p) := projection_finite hp hd
  infer_instance

/-- The whole fiber remains Noetherian, as its original finite scheme. -/
theorem fiber_noetherian {p : k[X]} (hp : p.Monic)
    (hd : 1 ≤ p.natDegree) (a : k) : IsNoetherian (fiber p a) := by
  have : IsFinite (fiberProjection p a) := fiberProjection_finite hp hd a
  exact isNoetherian_of_finiteType (fiberProjection p a)

/-- The whole finite fiber inclusion retains its nilpotent scheme structure. -/
theorem fiberInclusion_closed {p : k[X]} (hp : p.Monic)
    (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0) (a : k) :
    IsClosedImmersion (fiberInclusion p hd h0 a) := by
  have : IsClosedImmersion (inclusion p hd h0) := inclusion_closed hp hd h0
  have : IsFinite (fiberInclusion p hd h0 a ≫ pullback.fst _ _) := by
    rw [fiberInclusion_fst]
    exact fiberProjection_finite hp hd a
  have : IsFinite (fiberInclusion p hd h0 a) :=
    IsFinite.of_comp (fiberInclusion p hd h0 a) (pullback.fst _ _)
  apply (IsClosedImmersion.iff_isFinite_and_mono _).mpr
  refine ⟨inferInstance, ⟨?_⟩⟩
  intro W f g h
  have hfst : f ≫ fiberProjection p a = g ≫ fiberProjection p a := by
    simpa only [Category.assoc, fiberInclusion_fst] using
      congrArg (fun t => t ≫ pullback.fst _ _) h
  have hsnd : f ≫ fiberToFamily p a ≫ targetMap p hd h0 =
      g ≫ fiberToFamily p a ≫ targetMap p hd h0 := by
    simpa only [Category.assoc, fiberInclusion_snd] using
      congrArg (fun t => t ≫ pullback.snd _ _) h
  apply pullback.hom_ext hfst
  apply (cancel_mono (inclusion p hd h0)).mp
  apply pullback.hom_ext
  · simp only [Category.assoc, inclusion_fst]
    change (f ≫ pullback.snd _ _) ≫ projection p = (g ≫ pullback.snd _ _) ≫ projection p
    rw [Category.assoc, Category.assoc, ← pullback.condition]
    simpa only [Category.assoc] using
      congrArg (fun t => t ≫ (WeightOneBoundaryNorm.evaluationPoint k a).left) hfst
  · simpa only [Category.assoc, inclusion_snd] using hsnd

/-- Laurent homomorphisms are determined by their constants and their invertible coordinate. -/
theorem laurentRingHom_ext {R : Type u} [CommRing R]
    {f g : LaurentPolynomial k →+* R}
    (hC : f.comp LaurentPolynomial.C = g.comp LaurentPolynomial.C)
    (hT : f (LaurentPolynomial.T 1) = g (LaurentPolynomial.T 1)) : f = g := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (X : k[X]))
  apply Polynomial.ringHom_ext
  · intro r
    simpa only [RingHom.comp_apply, LaurentPolynomial.algebraMap_eq_toLaurent,
      Polynomial.toLaurent_C] using RingHom.congr_fun hC r
  · simpa only [RingHom.comp_apply, LaurentPolynomial.algebraMap_eq_toLaurent,
      Polynomial.toLaurent_X] using hT

/-- The tensor specialization retains the original constant field action. -/
theorem specialize_constant (p : k[X]) (a r : k) :
    Algebra.PolynomialFiber.specialize (FamilyAlgebra p) a (constantMap p r) =
      algebraMap k (Algebra.PolynomialFiber.Fiber (FamilyAlgebra p) a) r := by
  let : Algebra k[X] k := Algebra.PolynomialFiber.evaluationAlgebra a
  change Algebra.TensorProduct.includeRight
    (algebraMap k[X] (FamilyAlgebra p) (C r)) = _
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply k[X] k
    (Algebra.PolynomialFiber.Fiber (FamilyAlgebra p) a)]
  congr 1
  exact Polynomial.eval_C

/-- A whole tensor-fiber algebra equivalence gives an actual whole scheme isomorphism. -/
def fiberPolynomialSchemeIso (p : k[X]) (a : k) (q : k[X])
    (e : Algebra.PolynomialFiber.Fiber (FamilyAlgebra p) a ≃ₐ[k] AdjoinRoot q) :
    fiber p a ≅ Spec (.of (AdjoinRoot q)) :=
  fiberSchemeIso p a ≪≫ Scheme.Spec.mapIso e.symm.toRingEquiv.toCommRingCatIso.op

/-- The whole endpoint scheme isomorphism preserves the actual field projection. -/
theorem fiberPolynomialSchemeIso_inv_fst (p : k[X]) (a : k) (q : k[X])
    (e : Algebra.PolynomialFiber.Fiber (FamilyAlgebra p) a ≃ₐ[k] AdjoinRoot q) :
    (fiberPolynomialSchemeIso p a q e).inv ≫ fiberProjection p a =
      Spec.map (CommRingCat.ofHom (AdjoinRoot.of q)) := by
  rw [fiberPolynomialSchemeIso, Iso.trans_inv, Category.assoc, fiberSchemeIso_inv_fst]
  change Spec.map (CommRingCat.ofHom e.toRingHom) ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext e.commutes

/-- A root-preserving tensor-fiber equivalence preserves the actual Laurent map. -/
theorem fiberPolynomialSchemeIso_inv_torus (p : k[X]) (hd : 1 ≤ p.natDegree)
    (h0 : p.coeff 0 ≠ 0) (a : k) (q : k[X]) (hq0 : q.coeff 0 ≠ 0)
    (e : Algebra.PolynomialFiber.Fiber (FamilyAlgebra p) a ≃ₐ[k] AdjoinRoot q)
    (he : e (Algebra.PolynomialFiber.specialize (FamilyAlgebra p) a
      (AdjoinRoot.root (family p))) = AdjoinRoot.root q) :
    (fiberPolynomialSchemeIso p a q e).inv ≫ fiberToFamily p a ≫ torusMap p hd h0 =
      polynomialTorusMap q hq0 := by
  rw [fiberPolynomialSchemeIso, Iso.trans_inv, Category.assoc,
    ← Category.assoc (fiberSchemeIso p a).inv, fiberSchemeIso_inv_snd]
  change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (Algebra.PolynomialFiber.specialize (FamilyAlgebra p) a)) ≫
      Spec.map (CommRingCat.ofHom
        (LaurentPolynomial.eval₂ (constantMap p) (coordinateUnit p hd h0))) = _
  simp only [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply laurentRingHom_ext
  · apply RingHom.ext
    intro r
    change e (Algebra.PolynomialFiber.specialize (FamilyAlgebra p) a
      (LaurentPolynomial.eval₂ (constantMap p) (coordinateUnit p hd h0)
        (LaurentPolynomial.C r))) =
      LaurentPolynomial.eval₂ (AdjoinRoot.of q) (polynomialUnit q hq0) (LaurentPolynomial.C r)
    rw [LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_C, specialize_constant]
    exact e.commutes r
  · change e (Algebra.PolynomialFiber.specialize (FamilyAlgebra p) a
      (LaurentPolynomial.eval₂ (constantMap p) (coordinateUnit p hd h0) (LaurentPolynomial.T 1))) =
      LaurentPolynomial.eval₂ (AdjoinRoot.of q) (polynomialUnit q hq0) (LaurentPolynomial.T 1)
    simpa only [LaurentPolynomial.eval₂_T, zpow_one, coordinateUnit_val, polynomialUnit_val]
      using he

/-- The entire geometric endpoint map is exactly its quotient-polynomial embedding. -/
theorem fiberPolynomialSchemeIso_inv_inclusion (p : k[X]) (hd : 1 ≤ p.natDegree)
    (h0 : p.coeff 0 ≠ 0) (a : k) (q : k[X]) (hq0 : q.coeff 0 ≠ 0)
    (e : Algebra.PolynomialFiber.Fiber (FamilyAlgebra p) a ≃ₐ[k] AdjoinRoot q)
    (he : e (Algebra.PolynomialFiber.specialize (FamilyAlgebra p) a
      (AdjoinRoot.root (family p))) = AdjoinRoot.root q) :
    (fiberPolynomialSchemeIso p a q e).inv ≫ fiberInclusion p hd h0 a =
      polynomialInclusion q hq0 := by
  apply pullback.hom_ext
  · rw [Category.assoc, fiberInclusion_fst, polynomialInclusion_fst,
      fiberPolynomialSchemeIso_inv_fst]
  · rw [Category.assoc, fiberInclusion_snd, polynomialInclusion_snd]
    have : IsIso (SmoothSite.torusCoordinate (.of k) 1 0).left := by
      change IsIso (SmoothSite.torusPowerOneIso (.of k)).hom.left
      infer_instance
    apply (cancel_mono (SmoothSite.torusCoordinate (.of k) 1 0).left).mp
    simp only [Category.assoc, targetMap_coordinate, polynomialTargetMap_coordinate]
    exact fiberPolynomialSchemeIso_inv_torus p hd h0 a q hq0 e he

private theorem finitePushforward_congr {P Q : Scheme.{u}} (f g : P ⟶ Q)
    [hf : IsFinite f] [hg : IsFinite g] (h : f = g) (c : IntegralCycle P) :
    IntegralCycle.finitePushforward f c = IntegralCycle.finitePushforward g c := by
  cases h
  rfl

/-- The whole fiber fundamental cycle equals the full endpoint polynomial cycle,
including every original local length and every nilpotent branch. -/
theorem fiber_fundamental_eq_polynomialCycle {p : k[X]} (hp : p.Monic)
    (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0) (a : k) (q : k[X])
    (hq : q.Monic) (hq0 : q.coeff 0 ≠ 0)
    (e : Algebra.PolynomialFiber.Fiber (FamilyAlgebra p) a ≃ₐ[k] AdjoinRoot q)
    (he : e (Algebra.PolynomialFiber.specialize (FamilyAlgebra p) a
      (AdjoinRoot.root (family p))) = AdjoinRoot.root q) :
    letI := fiber_noetherian hp hd a
    letI := fiberInclusion_closed hp hd h0 a
    IntegralCycle.finitePushforward (fiberInclusion p hd h0 a) (fundamentalCycle (fiber p a)) =
      FiniteCorrespondence.toIntegralCycle (polynomialCycle q hq hq0) := by
  let := fiber_noetherian hp hd a
  let := fiberInclusion_closed hp hd h0 a
  rw [toIntegralCycle_polynomialCycle,
    ← finitePushforward_fundamentalCycle (fiberPolynomialSchemeIso p a q e).inv,
    ← AddMonoidHom.comp_apply, ← IntegralCycle.finitePushforward_comp]
  exact finitePushforward_congr _ _
    (fiberPolynomialSchemeIso_inv_inclusion p hd h0 a q hq0 e he) _

/-- The literal zero fiber is the whole original polynomial cycle. -/
theorem zero_fiber_fundamental {p : k[X]} (hp : p.Monic)
    (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0) :
    letI := fiber_noetherian hp hd 0
    letI := fiberInclusion_closed hp hd h0 0
    IntegralCycle.finitePushforward (fiberInclusion p hd h0 0) (fundamentalCycle (fiber p 0)) =
      FiniteCorrespondence.toIntegralCycle (polynomialCycle p hp h0) :=
  fiber_fundamental_eq_polynomialCycle hp hd h0 0 p hp h0
    (fiberZeroEquiv p) (fiberZeroEquiv_root p)

/-- The literal one fiber is the full split polynomial cycle, including repeated identities. -/
theorem one_fiber_fundamental {p : k[X]} (hp : p.Monic)
    (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0) :
    letI := fiber_noetherian hp hd 1
    letI := fiberInclusion_closed hp hd h0 1
    IntegralCycle.finitePushforward (fiberInclusion p hd h0 1) (fundamentalCycle (fiber p 1)) =
      FiniteCorrespondence.toIntegralCycle (polynomialCycle (target p) (target_monic p)
        ((target_coeff_zero p hd).trans_ne h0)) :=
  fiber_fundamental_eq_polynomialCycle hp hd h0 1 (target p) (target_monic p)
    ((target_coeff_zero p hd).trans_ne h0) (fiberOneEquiv p) (fiberOneEquiv_root p)

/-- Each component image is isomorphic to its original reduced support. -/
def componentSchemeIso {p : k[X]} (hp : p.Monic) (hd : 1 ≤ p.natDegree)
    (h0 : p.coeff 0 ≠ 0) (z : genericPoints (familyScheme p)) :
    (componentSupport p z).val.subscheme ≅ (componentGenerator hp hd h0 z).scheme := by
  have : IsClosedImmersion (inclusion p hd h0) := inclusion_closed hp hd h0
  exact asIso ((componentSupport p z).val.subschemeι ≫ inclusion p hd h0).toImage

@[reassoc (attr := simp)] theorem componentSchemeIso_hom_projection {p : k[X]}
    (hp : p.Monic) (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0)
    (z : genericPoints (familyScheme p)) :
    (componentSchemeIso hp hd h0 z).hom ≫ (componentGenerator hp hd h0 z).projection =
      (componentSupport p z).val.subschemeι ≫ projection p := by
  change ((componentSupport p z).val.subschemeι ≫ inclusion p hd h0).toImage ≫
    ((componentSupport p z).val.subschemeι ≫ inclusion p hd h0).imageι ≫ pullback.fst _ _ = _
  rw [← Category.assoc, Scheme.Hom.toImage_imageι, Category.assoc, inclusion_fst]

@[reassoc (attr := simp)] theorem componentSchemeIso_hom_target {p : k[X]}
    (hp : p.Monic) (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0)
    (z : genericPoints (familyScheme p)) :
    (componentSchemeIso hp hd h0 z).hom ≫ (componentGenerator hp hd h0 z).targetProjection =
      (componentSupport p z).val.subschemeι ≫ targetMap p hd h0 := by
  change ((componentSupport p z).val.subschemeι ≫ inclusion p hd h0).toImage ≫
    ((componentSupport p z).val.subschemeι ≫ inclusion p hd h0).imageι ≫ pullback.snd _ _ = _
  rw [← Category.assoc, Scheme.Hom.toImage_imageι, Category.assoc, inclusion_snd]

/-- The original reduced component's fiber is left wholly unreduced. -/
abbrev componentFiber (p : k[X]) (z : genericPoints (familyScheme p)) (a : k) : Scheme.{u} :=
  pullback (WeightOneBoundaryNorm.evaluationPoint k a).left
    ((componentSupport p z).val.subschemeι ≫ projection p)

/-- The original component fiber inclusion into the entire family fiber. -/
def componentFiberInclusion (p : k[X]) (z : genericPoints (familyScheme p)) (a : k) :
    componentFiber p z a ⟶ fiber p a :=
  pullback.map _ _ _ _ (𝟙 _) (componentSupport p z).val.subschemeι (𝟙 _)
    (by simp) (by simp)

instance componentFiberInclusion_closed (p : k[X]) (z : genericPoints (familyScheme p))
    (a : k) : IsClosedImmersion (componentFiberInclusion p z a) := by
  unfold componentFiberInclusion
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    (inferInstanceAs (IsClosedImmersion (𝟙 (Spec (.of k)))))
    (inferInstanceAs (IsClosedImmersion (componentSupport p z).val.subschemeι))
    (by simp) (by simp)

/-- The fiber comparison is induced by the original component-image isomorphism. -/
def componentFiberIso {p : k[X]} (hp : p.Monic) (hd : 1 ≤ p.natDegree)
    (h0 : p.coeff 0 ≠ 0) (z : genericPoints (familyScheme p)) (a : k) :
    componentFiber p z a ≅
      (componentGenerator hp hd h0 z).graphPullback
        (WeightOneBoundaryNorm.evaluationPoint k a).left :=
  asIso (pullback.map _ _ _ _ (𝟙 _) (componentSchemeIso hp hd h0 z).hom (𝟙 _)
    (by simp) (by simpa using (componentSchemeIso_hom_projection hp hd h0 z).symm))

/-- The component fiber map to the point-torus product uses the same two original coordinates. -/
theorem componentFiberIso_hom_inclusion {p : k[X]} (hp : p.Monic)
    (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0)
    (z : genericPoints (familyScheme p)) (a : k) :
    (componentFiberIso hp hd h0 z a).hom ≫
        (componentGenerator hp hd h0 z).graphPullbackMap
          (WeightOneBoundaryNorm.evaluationPoint k a).left
          (MorphismProperty.Over.w (WeightOneBoundaryNorm.evaluationPoint k a)) =
      componentFiberInclusion p z a ≫ fiberInclusion p hd h0 a := by
  apply pullback.hom_ext
  · simp only [Category.assoc, FiniteCorrespondenceGenerator.graphPullbackMap_fst,
      fiberInclusion_fst, componentFiberIso, asIso_hom, componentFiberInclusion,
      pullback.map, pullback.lift_fst, Category.comp_id]
  · simp only [Category.assoc, FiniteCorrespondenceGenerator.graphPullbackMap_snd,
      fiberInclusion_snd, componentFiberIso, asIso_hom, componentFiberInclusion,
      pullback.map, pullback.lift_snd_assoc, componentSchemeIso_hom_target]

/-- A component's actual graph restriction is its whole original fiber pushforward. -/
theorem component_graph_restriction {p : k[X]} (hp : p.Monic)
    (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0)
    (z : genericPoints (familyScheme p)) (a : k) :
    letI := fiber_noetherian hp hd a
    letI := fiberInclusion_closed hp hd h0 a
    letI : IsNoetherian (componentFiber p z a) :=
      isNoetherian_of_finiteType (componentFiberInclusion p z a)
    FiniteCorrespondence.toIntegralCycle
      (f := (SmoothSite.base (Spec (.of k))).hom)
      (g := (SmoothSite.torusPower (.of k) 1).hom)
      ((Cor.graphFunctor k).map (WeightOneBoundaryNorm.evaluationPoint k a) ≫
        (show Cor.mk (AlgebraicSimplex.smoothSiteObj k 1) ⟶ WeightOnePointNorm.target k from
          (componentGenerator hp hd h0 z).cycle)) =
      IntegralCycle.finitePushforward (componentFiberInclusion p z a ≫ fiberInclusion p hd h0 a)
        (fundamentalCycle (componentFiber p z a)) := by
  let := fiber_noetherian hp hd a
  let := fiberInclusion_closed hp hd h0 a
  let : IsNoetherian (componentFiber p z a) :=
    isNoetherian_of_finiteType (componentFiberInclusion p z a)
  rw [FiniteCorrespondenceGenerator.toIntegralCycle_graphFunctor_comp]
  rw [← finitePushforward_fundamentalCycle (componentFiberIso hp hd h0 z a).hom,
    ← AddMonoidHom.comp_apply, ← IntegralCycle.finitePushforward_comp]
  exact finitePushforward_congr _ _ (componentFiberIso_hom_inclusion hp hd h0 z a) _

/-- Every generic component contributes its original length to the actual endpoint restriction. -/
theorem fundamentalCorrespondence_graph_restriction_sum {p : k[X]} (hp : p.Monic)
    (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0) (a : k) :
    letI := fiber_noetherian hp hd a
    letI := fiberInclusion_closed hp hd h0 a
    letI := IntegralCycle.genericPointFintype (familyScheme p)
    letI : ∀ z, IsNoetherian (componentFiber p z a) :=
      fun z => isNoetherian_of_finiteType (componentFiberInclusion p z a)
    FiniteCorrespondence.toIntegralCycle
      (f := (SmoothSite.base (Spec (.of k))).hom)
      (g := (SmoothSite.torusPower (.of k) 1).hom)
      ((Cor.graphFunctor k).map (WeightOneBoundaryNorm.evaluationPoint k a) ≫
        fundamentalCorrespondence hp hd h0) =
      ∑ z, (genericMultiplicity z : ℤ) •
        IntegralCycle.finitePushforward (componentFiberInclusion p z a ≫ fiberInclusion p hd h0 a)
          (fundamentalCycle (componentFiber p z a)) := by
  classical
  let := fiber_noetherian hp hd a
  let := fiberInclusion_closed hp hd h0 a
  let := IntegralCycle.genericPointFintype (familyScheme p)
  let : ∀ z, IsNoetherian (componentFiber p z a) :=
    fun z => isNoetherian_of_finiteType (componentFiberInclusion p z a)
  simp only [fundamentalCorrespondence, Preadditive.comp_sum, map_sum]
  apply Finset.sum_congr rfl
  intro z _
  change FiniteCorrespondence.toIntegralCycle
    (f := (SmoothSite.base (Spec (.of k))).hom)
    (g := (SmoothSite.torusPower (.of k) 1).hom)
    ((Cor.graphFunctor k).map (WeightOneBoundaryNorm.evaluationPoint k a) ≫
      ((genericMultiplicity z : ℤ) •
        (show Cor.mk (AlgebraicSimplex.smoothSiteObj k 1) ⟶ WeightOnePointNorm.target k from
          (componentGenerator hp hd h0 z).cycle))) = _
  rw [Preadditive.comp_zsmul, map_zsmul, component_graph_restriction hp hd h0]

/-- The whole actual fiber is identified with the literal polynomial-parameter pullback. -/
def fiberAffineIso (p : k[X]) (a : k) : fiber p a ≅
    pullback (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))) (affineProjection p) :=
  asIso (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (WeightOneBoundaryNorm.oneSchemeIso k).hom
    (by simpa using WeightOneBoundaryNorm.evaluationPoint_oneSchemeIso k a)
    (by simp))

/-- The same chart identifies every whole component fiber. -/
def componentFiberAffineIso (p : k[X]) (z : genericPoints (familyScheme p)) (a : k) :
    componentFiber p z a ≅
      pullback (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)))
        ((componentSupport p z).val.subschemeι ≫ affineProjection p) :=
  asIso (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (WeightOneBoundaryNorm.oneSchemeIso k).hom
    (by simpa using WeightOneBoundaryNorm.evaluationPoint_oneSchemeIso k a)
    (by simp only [Category.assoc, projection_oneSchemeIso, Category.id_comp]))

/-- The original component fiber map in polynomial coordinates. -/
def affineComponentFiberInclusion (p : k[X]) (z : genericPoints (familyScheme p)) (a : k) :
    pullback (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)))
        ((componentSupport p z).val.subschemeι ≫ affineProjection p) ⟶
      pullback (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))) (affineProjection p) :=
  pullback.map _ _ _ _ (𝟙 _) (componentSupport p z).val.subschemeι (𝟙 _)
    (by simp) (by simp)

instance affineComponentFiberInclusion_closed (p : k[X]) (z : genericPoints (familyScheme p))
    (a : k) : IsClosedImmersion (affineComponentFiberInclusion p z a) := by
  unfold affineComponentFiberInclusion
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    (inferInstanceAs (IsClosedImmersion (𝟙 (Spec (.of k)))))
    (inferInstanceAs (IsClosedImmersion (componentSupport p z).val.subschemeι))
    (by simp) (by simp)

/-- Changing the parameter chart commutes with every original component inclusion. -/
theorem componentFiberAffineIso_hom_inclusion (p : k[X])
    (z : genericPoints (familyScheme p)) (a : k) :
    (componentFiberAffineIso p z a).hom ≫ affineComponentFiberInclusion p z a =
      componentFiberInclusion p z a ≫ (fiberAffineIso p a).hom := by
  apply pullback.hom_ext <;>
    simp only [componentFiberAffineIso, fiberAffineIso, affineComponentFiberInclusion,
      componentFiberInclusion, asIso_hom, pullback.map, Category.assoc,
      pullback.lift_fst, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]

/-- The full family fiber is the sum of the unreduced component fibers,
weighted by the ORIGINAL generic lengths of the whole family. -/
theorem fiber_fundamental_eq_component_sum {p : k[X]} (hp : p.Monic)
    (hd : 1 ≤ p.natDegree) (a : k) :
    letI := fiber_noetherian hp hd a
    letI := IntegralCycle.genericPointFintype (familyScheme p)
    letI : ∀ z, IsNoetherian (componentFiber p z a) :=
      fun z => isNoetherian_of_finiteType (componentFiberInclusion p z a)
    fundamentalCycle (fiber p a) =
      ∑ z, (genericMultiplicity z : ℤ) •
        IntegralCycle.finitePushforward (componentFiberInclusion p z a)
          (fundamentalCycle (componentFiber p z a)) := by
  classical
  let := fiber_noetherian hp hd a
  let := IntegralCycle.genericPointFintype (familyScheme p)
  let : ∀ z, IsNoetherian (componentFiber p z a) :=
    fun z => isNoetherian_of_finiteType (componentFiberInclusion p z a)
  let : IsNoetherian
      (pullback (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)))
        (affineProjection p)) := isNoetherian_of_finiteType (fiberAffineIso p a).inv
  let : ∀ z, IsNoetherian
      (pullback (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)))
        ((componentSupport p z).val.subschemeι ≫ affineProjection p)) :=
    fun z => isNoetherian_of_finiteType (componentFiberAffineIso p z a).inv
  have : IsFinite (projection p) := projection_finite hp hd
  have : Flat (projection p) := projection_flat hp hd
  have : IsFinite (affineProjection p) := by
    rw [← projection_oneSchemeIso p]
    infer_instance
  have : Flat (affineProjection p) := by
    rw [← projection_oneSchemeIso p]
    infer_instance
  have hbase := AlgebraicGeometry.finiteFlatCurve_fundamentalCycle_specialization
    (affineProjection p) a
  apply IntegralCycle.finitePushforward_injective_of_isClosedImmersion (fiberAffineIso p a).hom
  rw [finitePushforward_fundamentalCycle, map_sum]
  simp only [map_zsmul]
  change fundamentalCycle _ = ∑ z, (genericMultiplicity z : ℤ) • _
  rw [hbase]
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  symm
  rw [← AddMonoidHom.comp_apply, ← IntegralCycle.finitePushforward_comp]
  refine (finitePushforward_congr _ _ (componentFiberAffineIso_hom_inclusion p z a).symm _).trans ?_
  rw [IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply,
    finitePushforward_fundamentalCycle]
  rfl

/-- Actual graph restriction of the signed whole family is its WHOLE
scheme-theoretic fiber fundamental cycle, with all nonreduced multiplicities. -/
theorem toIntegralCycle_graph_restriction {p : k[X]} (hp : p.Monic)
    (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0) (a : k) :
    letI := fiber_noetherian hp hd a
    letI := fiberInclusion_closed hp hd h0 a
    FiniteCorrespondence.toIntegralCycle
      (f := (SmoothSite.base (Spec (.of k))).hom)
      (g := (SmoothSite.torusPower (.of k) 1).hom)
      ((Cor.graphFunctor k).map (WeightOneBoundaryNorm.evaluationPoint k a) ≫
        fundamentalCorrespondence hp hd h0) =
      IntegralCycle.finitePushforward (fiberInclusion p hd h0 a)
        (fundamentalCycle (fiber p a)) := by
  classical
  let := fiber_noetherian hp hd a
  let := fiberInclusion_closed hp hd h0 a
  let := IntegralCycle.genericPointFintype (familyScheme p)
  let : ∀ z, IsNoetherian (componentFiber p z a) :=
    fun z => isNoetherian_of_finiteType (componentFiberInclusion p z a)
  rw [fundamentalCorrespondence_graph_restriction_sum,
    fiber_fundamental_eq_component_sum hp hd a, map_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [map_zsmul, IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply]

/-- The actual graph restriction at zero is exactly the original full polynomial correspondence. -/
theorem graph_zero_fundamentalCorrespondence {p : k[X]} (hp : p.Monic)
    (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0) :
    (Cor.graphFunctor k).map (WeightOneBoundaryNorm.evaluationPoint k 0) ≫
        fundamentalCorrespondence hp hd h0 = polynomialCycle p hp h0 := by
  apply FiniteCorrespondence.toIntegralCycle_injective
  exact (toIntegralCycle_graph_restriction hp hd h0 0).trans
    (zero_fiber_fundamental hp hd h0)

/-- The actual graph restriction at one is exactly the full split polynomial correspondence. -/
theorem graph_one_fundamentalCorrespondence {p : k[X]} (hp : p.Monic)
    (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0) :
    (Cor.graphFunctor k).map (WeightOneBoundaryNorm.evaluationPoint k 1) ≫
        fundamentalCorrespondence hp hd h0 =
      polynomialCycle (target p) (target_monic p) ((target_coeff_zero p hd).trans_ne h0) := by
  apply FiniteCorrespondence.toIntegralCycle_injective
  exact (toIntegralCycle_graph_restriction hp hd h0 1).trans
    (one_fiber_fundamental hp hd h0)

/-- The literal first face is the whole original polynomial correspondence. -/
theorem face_zero_fundamentalCorrespondence {p : k[X]} (hp : p.Monic)
    (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0) :
    (Cor.graphFunctor k).map (WeightOneBoundaryNorm.facePoint k 0) ≫
        fundamentalCorrespondence hp hd h0 = polynomialCycle p hp h0 := by
  rw [WeightOneBoundaryNorm.facePoint_zero, graph_zero_fundamentalCorrespondence]

/-- The literal second face is the complete split polynomial correspondence. -/
theorem face_one_fundamentalCorrespondence {p : k[X]} (hp : p.Monic)
    (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0) :
    (Cor.graphFunctor k).map (WeightOneBoundaryNorm.facePoint k 1) ≫
        fundamentalCorrespondence hp hd h0 =
      polynomialCycle (target p) (target_monic p) ((target_coeff_zero p hd).trans_ne h0) := by
  rw [WeightOneBoundaryNorm.facePoint_one, graph_one_fundamentalCorrespondence]

/-- The actual one-simplex correspondence in the literal singular product convention. -/
def singularCorrespondence {p : k[X]} (hp : p.Monic) (hd : 1 ≤ p.natDegree)
    (h0 : p.coeff 0 ≠ 0) :
    Cor.simplexProduct (WeightOnePointNorm.point k) 1 ⟶ WeightOnePointNorm.target k :=
  (WeightOneBoundaryNorm.simplexProductIso k 1).hom ≫ fundamentalCorrespondence hp hd h0

/-- The literal singular product coface is exactly the corresponding geometric endpoint. -/
theorem singularCorrespondence_face {p : k[X]} (hp : p.Monic)
    (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0) (i : Fin 2) :
    (WeightOneBoundaryNorm.zeroProductIso k).inv ≫
        (Cor.simplexProductCosimplicial (WeightOnePointNorm.point k)).δ i ≫
          singularCorrespondence hp hd h0 =
      (Cor.graphFunctor k).map (WeightOneBoundaryNorm.facePoint k i) ≫
        fundamentalCorrespondence hp hd h0 := by
  rw [← Category.assoc, WeightOneBoundaryNorm.zeroProductIso_inv_face]
  simp only [singularCorrespondence, Category.assoc, Iso.inv_hom_id_assoc]

/-- The first literal singular coface is the original full polynomial cycle. -/
theorem singularCorrespondence_face_zero {p : k[X]} (hp : p.Monic)
    (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0) :
    (WeightOneBoundaryNorm.zeroProductIso k).inv ≫
        (Cor.simplexProductCosimplicial (WeightOnePointNorm.point k)).δ 0 ≫
          singularCorrespondence hp hd h0 = polynomialCycle p hp h0 := by
  rw [singularCorrespondence_face, face_zero_fundamentalCorrespondence]

/-- The second literal singular coface is the complete split polynomial cycle. -/
theorem singularCorrespondence_face_one {p : k[X]} (hp : p.Monic)
    (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0) :
    (WeightOneBoundaryNorm.zeroProductIso k).inv ≫
        (Cor.simplexProductCosimplicial (WeightOnePointNorm.point k)).δ 1 ≫
          singularCorrespondence hp hd h0 =
      polynomialCycle (target p) (target_monic p) ((target_coeff_zero p hd).trans_ne h0) := by
  rw [singularCorrespondence_face, face_one_fundamentalCorrespondence]

end Motivic.WeightOneInterpolationCycle
