/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.WeightTwoSymbols
public import Motivic.Aglib.RingTheory.TwoUnitPolynomialFamily
public import Motivic.AlgebraicGeometry.Correspondences.FiniteFlatCurveFamily

/-!
# The full two-unit cubic endpoint boundary

The original monic quotient maps by its literal two units `x` and `1-x`.
No reduction, selection of components, or separability assumption is made.
The eventual endpoint relation is a relation in actual weight-two raw homology;
it does not assert the Steinberg relation or a Milnor K-theory comparison.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open Polynomial.TwoUnitPolynomialFamily
open scoped BigOperators

universe u

namespace Motivic.WeightTwoCubicBoundary

variable {k : Type u} [Field k]

/-- The actual Laurent morphism associated to a unit in an arbitrary affine algebra. -/
def unitMap {R : Type u} [CommRing R] (c : k →+* R) (v : Rˣ) :
    Spec (.of R) ⟶ (SmoothSite.torus (.of k)).left :=
  Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ c v))

@[reassoc (attr := simp)] theorem unitMap_structure {R : Type u} [CommRing R]
    (c : k →+* R) (v : Rˣ) :
    unitMap c v ≫ (SmoothSite.torus (.of k)).hom = Spec.map (CommRingCat.ofHom c) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact LaurentPolynomial.eval₂_C c v

/-- A pair of units gives an actual map to the canonical two-fold torus,
without requiring its source to be smooth. -/
def pairMap {R : Type u} [CommRing R] (c : k →+* R) (v w : Rˣ) :
    Spec (.of R) ⟶ (SmoothSite.torusPower (.of k) 2).left :=
  pullback.lift (unitMap c v)
    (unitMap c w ≫ (SmoothSite.torusPowerOneIso (.of k)).inv.left) (by
      rw [Category.assoc, MorphismProperty.Over.w]
      simp only [unitMap_structure])

@[reassoc (attr := simp)] theorem pairMap_first {R : Type u} [CommRing R]
    (c : k →+* R) (v w : Rˣ) :
    pairMap c v w ≫ (SmoothSite.torusCoordinate (.of k) 2 0).left = unitMap c v :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem pairMap_second {R : Type u} [CommRing R]
    (c : k →+* R) (v w : Rˣ) :
    pairMap c v w ≫ (SmoothSite.torusCoordinate (.of k) 2 1).left = unitMap c w := by
  change pairMap c v w ≫ pullback.snd _ _ ≫
    (SmoothSite.torusPowerOneIso (.of k)).hom.left = _
  rw [← Category.assoc, pairMap, pullback.lift_snd]
  have h := congrArg (fun f => f.left) (SmoothSite.torusPowerOneIso (.of k)).inv_hom_id
  change (SmoothSite.torusPowerOneIso (.of k)).inv.left ≫
    (SmoothSite.torusPowerOneIso (.of k)).hom.left = 𝟙 _ at h
  rw [Category.assoc, h, Category.comp_id]

@[reassoc (attr := simp)] theorem pairMap_structure {R : Type u} [CommRing R]
    (c : k →+* R) (v w : Rˣ) :
    pairMap c v w ≫ (SmoothSite.torusPower (.of k) 2).hom =
      Spec.map (CommRingCat.ofHom c) := by
  change pairMap c v w ≫ pullback.fst _ _ ≫ (SmoothSite.torus (.of k)).hom = _
  rw [← Category.assoc, pairMap, pullback.lift_fst, unitMap_structure]

/-- Arbitrary scheme maps to the two-fold torus are determined by both coordinates. -/
theorem pair_hom_ext {W : Scheme.{u}}
    {f g : W ⟶ (SmoothSite.torusPower (.of k) 2).left}
    (h0 : f ≫ (SmoothSite.torusCoordinate (.of k) 2 0).left =
      g ≫ (SmoothSite.torusCoordinate (.of k) 2 0).left)
    (h1 : f ≫ (SmoothSite.torusCoordinate (.of k) 2 1).left =
      g ≫ (SmoothSite.torusCoordinate (.of k) 2 1).left) : f = g := by
  apply pullback.hom_ext h0
  apply (cancel_mono (SmoothSite.torusPowerOneIso (.of k)).hom.left).mp
  exact h1

/-- Unit maps retain the exact scalar and unit images under an affine morphism. -/
theorem unitMap_comp {R S : Type u} [CommRing R] [CommRing S]
    (c : k →+* R) (d : k →+* S) (φ : R →+* S) (v : Rˣ) (w : Sˣ)
    (hc : φ.comp c = d) (hv : φ v = w) :
    Spec.map (CommRingCat.ofHom φ) ≫ unitMap c v = unitMap d w := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply WeightOneInterpolationCycle.laurentRingHom_ext
  · apply RingHom.ext
    intro r
    change φ (LaurentPolynomial.eval₂ c v (LaurentPolynomial.C r)) =
      LaurentPolynomial.eval₂ d w (LaurentPolynomial.C r)
    simpa only [LaurentPolynomial.eval₂_C, RingHom.comp_apply] using RingHom.congr_fun hc r
  · change φ (LaurentPolynomial.eval₂ c v (LaurentPolynomial.T 1)) =
      LaurentPolynomial.eval₂ d w (LaurentPolynomial.T 1)
    simpa only [LaurentPolynomial.eval₂_T, zpow_one] using hv

/-- Both literal coordinates are preserved by the specified affine scalar map. -/
theorem pairMap_comp {R S : Type u} [CommRing R] [CommRing S]
    (c : k →+* R) (d : k →+* S) (φ : R →+* S)
    (v w : Rˣ) (v' w' : Sˣ) (hc : φ.comp c = d)
    (hv : φ v = v') (hw : φ w = w') :
    Spec.map (CommRingCat.ofHom φ) ≫ pairMap c v w = pairMap d v' w' := by
  apply pair_hom_ext
  · simp only [Category.assoc, pairMap_first]
    exact unitMap_comp c d φ v v' hc hv
  · simp only [Category.assoc, pairMap_second]
    exact unitMap_comp c d φ w w' hc hw

/-- The whole polynomial quotient, including its nilpotents. -/
abbrev familyScheme (f : k[X][X]) : Scheme.{u} := Spec (.of (AdjoinRoot f))

/-- The literal parameter projection. -/
def projection (f : k[X][X]) : familyScheme f ⟶ Spec (.of k[X]) :=
  Spec.map (CommRingCat.ofHom (AdjoinRoot.of f))

/-- The original constant field action. -/
def constantMap (f : k[X][X]) : k →+* AdjoinRoot f :=
  (AdjoinRoot.of f).comp C

/-- The family has the actual two-coordinate map `(x, 1-x)`. -/
def targetMap (f : k[X][X]) (h0 : IsUnit (f.eval 0)) (h1 : IsUnit (f.eval 1)) :
    familyScheme f ⟶ (SmoothSite.torusPower (.of k) 2).left :=
  pairMap (constantMap f) (rootUnit f h0) (oneSubRootUnit f h1)

/-- The ambient product uses the original affine parameter and two-fold torus. -/
abbrev ambient (k : Type u) [Field k] : Scheme.{u} :=
  pullback (Spec.map (CommRingCat.ofHom (C : k →+* k[X])))
    (SmoothSite.torusPower (.of k) 2).hom

/-- The literal closed image to be used as the entire finite correspondence. -/
def inclusion (f : k[X][X]) (h0 : IsUnit (f.eval 0)) (h1 : IsUnit (f.eval 1)) :
    familyScheme f ⟶ ambient k :=
  pullback.lift (projection f) (targetMap f h0 h1) (by
    rw [targetMap, pairMap_structure]
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl)

@[reassoc (attr := simp)] theorem inclusion_fst (f : k[X][X])
    (h0 : IsUnit (f.eval 0)) (h1 : IsUnit (f.eval 1)) :
    inclusion f h0 h1 ≫ pullback.fst _ _ = projection f := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem inclusion_snd (f : k[X][X])
    (h0 : IsUnit (f.eval 0)) (h1 : IsUnit (f.eval 1)) :
    inclusion f h0 h1 ≫ pullback.snd _ _ = targetMap f h0 h1 := pullback.lift_snd _ _ _

/-- Monicity gives finiteness of the whole projection. -/
theorem projection_finite {f : k[X][X]} (hf : f.Monic) : IsFinite (projection f) := by
  let : Module.Finite k[X] (AdjoinRoot f) := hf.finite_adjoinRoot
  exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

/-- Monicity gives flatness of the whole projection. -/
theorem projection_flat {f : k[X][X]} (hf : f.Monic) : Flat (projection f) := by
  let : Module.Free k[X] (AdjoinRoot f) := hf.free_adjoinRoot
  apply Flat.SpecMap_iff.mpr
  change (AdjoinRoot.of f).Flat
  rw [← AdjoinRoot.algebraMap_eq]
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- The parameter and first coordinate determine all maps into the quotient. -/
theorem family_hom_ext (f : k[X][X]) (h0 : IsUnit (f.eval 0))
    {W : Scheme.{u}} {r s : W ⟶ familyScheme f}
    (ht : r ≫ projection f = s ≫ projection f)
    (hx : r ≫ unitMap (constantMap f) (rootUnit f h0) =
      s ≫ unitMap (constantMap f) (rootUnit f h0)) : r = s := by
  have ht' : (WeightOneInterpolationCycle.affinePullback r).comp (AdjoinRoot.of f) =
      (WeightOneInterpolationCycle.affinePullback s).comp (AdjoinRoot.of f) := by
    simpa only [projection, WeightOneInterpolationCycle.affinePullback_comp] using
      congrArg WeightOneInterpolationCycle.affinePullback ht
  have hx' := congrArg WeightOneInterpolationCycle.affinePullback hx
  simp only [unitMap, WeightOneInterpolationCycle.affinePullback_comp] at hx'
  have hc := RingHom.congr_fun hx' (LaurentPolynomial.T 1)
  simp only [RingHom.comp_apply, LaurentPolynomial.eval₂_T, zpow_one, rootUnit_val] at hc
  have he := AdjoinRoot.ringHom_ext ht' hc
  apply ext_of_isAffine
  apply (cancel_epi (Scheme.ΓSpecIso (.of (AdjoinRoot f))).inv).mp
  exact CommRingCat.hom_ext he

/-- The actual `(t,x,1-x)` morphism is closed, even for a nonreduced quotient. -/
theorem inclusion_closed {f : k[X][X]} (hf : f.Monic)
    (h0 : IsUnit (f.eval 0)) (h1 : IsUnit (f.eval 1)) :
    IsClosedImmersion (inclusion f h0 h1) := by
  have : IsFinite (projection f) := projection_finite hf
  have : IsFinite (inclusion f h0 h1 ≫ pullback.fst _ _) := by
    rw [inclusion_fst]
    infer_instance
  have : IsFinite (inclusion f h0 h1) := IsFinite.of_comp _ (pullback.fst _ _)
  apply (IsClosedImmersion.iff_isFinite_and_mono _).mpr
  refine ⟨inferInstance, ⟨?_⟩⟩
  intro W r s h
  apply family_hom_ext f h0
  · simpa only [Category.assoc, inclusion_fst] using
      congrArg (fun t => t ≫ pullback.fst _ _) h
  · simpa only [Category.assoc, inclusion_snd_assoc, targetMap, pairMap_first] using
      congrArg (fun t => t ≫ pullback.snd _ _ ≫
        (SmoothSite.torusCoordinate (.of k) 2 0).left) h

/-- Positive degree makes the entire finite-free family surjective onto its parameter line. -/
theorem projection_surjective {f : k[X][X]} (hf : f.Monic) (hd : 0 < f.natDegree) :
    Function.Surjective (projection f) := by
  let : Module.FaithfullyFlat k[X] (AdjoinRoot f) := faithfullyFlat hf hd
  exact PrimeSpectrum.comap_surjective_of_faithfullyFlat

/-- The whole endpoint quotient maps through its literal root and complement. -/
def polynomialTargetMap (p : k[X]) (h0 : IsUnit (p.eval 0)) (h1 : IsUnit (p.eval 1)) :
    Spec (.of (AdjoinRoot p)) ⟶ (SmoothSite.torusPower (.of k) 2).left :=
  pairMap (AdjoinRoot.of p) (rootUnit p h0) (oneSubRootUnit p h1)

/-- Its first Laurent coordinate already embeds the entire polynomial quotient. -/
instance polynomialFirst_closed (p : k[X]) (h0 : IsUnit (p.eval 0)) :
    IsClosedImmersion (unitMap (AdjoinRoot.of p) (rootUnit p h0)) := by
  apply IsClosedImmersion.spec_of_surjective
  intro r
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective r
  refine ⟨Polynomial.toLaurent q, ?_⟩
  change LaurentPolynomial.eval₂ (AdjoinRoot.of p) (rootUnit p h0)
    (Polynomial.toLaurent q) = AdjoinRoot.mk p q
  rw [LaurentPolynomial.eval₂_toLaurent, rootUnit_val, ← AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.aeval_eq q

/-- The exact point-two-torus product. -/
abbrev pointAmbient (k : Type u) [Field k] : Scheme.{u} :=
  pullback (SmoothSite.base (Spec (.of k))).hom (SmoothSite.torusPower (.of k) 2).hom

/-- The whole literal endpoint polynomial scheme, in the actual correspondence ambient. -/
def polynomialInclusion (p : k[X]) (h0 : IsUnit (p.eval 0)) (h1 : IsUnit (p.eval 1)) :
    Spec (.of (AdjoinRoot p)) ⟶ pointAmbient k :=
  pullback.lift (Spec.map (CommRingCat.ofHom (AdjoinRoot.of p)))
    (polynomialTargetMap p h0 h1) (by
      change Spec.map _ ≫ 𝟙 _ = _
      rw [Category.comp_id, polynomialTargetMap, pairMap_structure])

@[reassoc (attr := simp)] theorem polynomialInclusion_fst (p : k[X])
    (h0 : IsUnit (p.eval 0)) (h1 : IsUnit (p.eval 1)) :
    polynomialInclusion p h0 h1 ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (AdjoinRoot.of p)) := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem polynomialInclusion_snd (p : k[X])
    (h0 : IsUnit (p.eval 0)) (h1 : IsUnit (p.eval 1)) :
    polynomialInclusion p h0 h1 ≫ pullback.snd _ _ = polynomialTargetMap p h0 h1 :=
  pullback.lift_snd _ _ _

/-- Endpoint schemes retain their entire original closed structure. -/
instance polynomialInclusion_closed (p : k[X])
    (h0 : IsUnit (p.eval 0)) (h1 : IsUnit (p.eval 1)) :
    IsClosedImmersion (polynomialInclusion p h0 h1) := by
  let q := pullback.snd (SmoothSite.base (Spec (.of k))).hom
      (SmoothSite.torusPower (.of k) 2).hom ≫
    (SmoothSite.torusCoordinate (.of k) 2 0).left
  have : IsSeparated (SmoothSite.torusCoordinate (.of k) 2 0).left := by
    change IsSeparated (pullback.fst (SmoothSite.torus (.of k)).hom
      (SmoothSite.torusPower (.of k) 1).hom)
    infer_instance
  have : IsSeparated q := by dsimp only [q]; infer_instance
  have : IsClosedImmersion (polynomialInclusion p h0 h1 ≫ q) := by
    dsimp only [q]
    rw [polynomialInclusion_snd_assoc, polynomialTargetMap, pairMap_first]
    infer_instance
  exact IsClosedImmersion.of_comp (polynomialInclusion p h0 h1) q

/-- Monic endpoint quotients are finite over the original field. -/
theorem polynomialProjection_finite {p : k[X]} (hp : p.Monic) :
    IsFinite (Spec.map (CommRingCat.ofHom (AdjoinRoot.of p))) := by
  let : Module.Finite k (AdjoinRoot p) := hp.finite_adjoinRoot
  exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

/-- The literal whole endpoint cycle includes every generic local length. -/
def polynomialCycle (p : k[X]) (hp : p.Monic)
    (h0 : IsUnit (p.eval 0)) (h1 : IsUnit (p.eval 1)) :
    WeightOnePointNorm.point k ⟶ WeightTwoSymbols.target k :=
  letI := polynomialProjection_finite hp
  FiniteFlatCurveFamily.pointFundamentalCorrespondence
    (Spec.map (CommRingCat.ofHom (AdjoinRoot.of p))) (polynomialInclusion p h0 h1)
    (polynomialInclusion_fst p h0 h1)

/-- Forgetting admissibility recovers the pushed whole endpoint quotient. -/
theorem toIntegralCycle_polynomialCycle (p : k[X]) (hp : p.Monic)
    (h0 : IsUnit (p.eval 0)) (h1 : IsUnit (p.eval 1)) :
    FiniteCorrespondence.toIntegralCycle (polynomialCycle p hp h0 h1) =
      IntegralCycle.finitePushforward (polynomialInclusion p h0 h1)
        (fundamentalCycle (Spec (.of (AdjoinRoot p)))) := by
  let := polynomialProjection_finite hp
  exact FiniteFlatCurveFamily.toIntegralCycle_pointFundamentalCorrespondence _ _ _

/-- The actual full finite-flat family correspondence. -/
def fundamentalCorrespondence (f : k[X][X]) (hf : f.Monic)
    (h0 : IsUnit (f.eval 0)) (h1 : IsUnit (f.eval 1)) :
    Cor.mk (FiniteFlatCurveFamily.line k) ⟶ WeightTwoSymbols.target k :=
  letI := projection_finite hf
  letI := projection_flat hf
  letI := inclusion_closed hf h0 h1
  FiniteFlatCurveFamily.fundamentalCorrespondence (projection f) (inclusion f h0 h1)
    (inclusion_fst f h0 h1)

/-- Its cycle retains all original generic local lengths. -/
theorem toIntegralCycle_fundamentalCorrespondence (f : k[X][X]) (hf : f.Monic)
    (h0 : IsUnit (f.eval 0)) (h1 : IsUnit (f.eval 1)) :
    letI := inclusion_closed hf h0 h1
    FiniteCorrespondence.toIntegralCycle (fundamentalCorrespondence f hf h0 h1) =
      IntegralCycle.finitePushforward (inclusion f h0 h1) (fundamentalCycle (familyScheme f)) := by
  let := projection_finite hf
  let := projection_flat hf
  let := inclusion_closed hf h0 h1
  exact FiniteFlatCurveFamily.toIntegralCycle_fundamentalCorrespondence _ _ _

/-- The original scheme-theoretic parameter fiber. -/
abbrev fiber (f : k[X][X]) (s : k) : Scheme.{u} :=
  FiniteFlatCurveFamily.fiber (projection f) s

/-- The whole tensor-fiber chart, retaining the specified evaluation scalar action. -/
def fiberSchemeIso (f : k[X][X]) (s : k) :
    fiber f s ≅ Spec (.of (Algebra.PolynomialFiber.Fiber (AdjoinRoot f) s)) := by
  letI : Algebra k[X] k := Algebra.PolynomialFiber.evaluationAlgebra s
  exact pullbackSpecIso k[X] k (AdjoinRoot f)

@[reassoc (attr := simp)] theorem fiberSchemeIso_inv_fst (f : k[X][X]) (s : k) :
    (fiberSchemeIso f s).inv ≫ pullback.fst (FiniteFlatCurve.endpoint s) (projection f) =
      Spec.map (CommRingCat.ofHom
        (algebraMap k (Algebra.PolynomialFiber.Fiber (AdjoinRoot f) s))) := by
  let : Algebra k[X] k := Algebra.PolynomialFiber.evaluationAlgebra s
  exact pullbackSpecIso_inv_fst' k[X] k (AdjoinRoot f)

@[reassoc (attr := simp)] theorem fiberSchemeIso_inv_snd (f : k[X][X]) (s : k) :
    (fiberSchemeIso f s).inv ≫ pullback.snd (FiniteFlatCurve.endpoint s) (projection f) =
      Spec.map (CommRingCat.ofHom (Algebra.PolynomialFiber.specialize (AdjoinRoot f) s)) := by
  let : Algebra k[X] k := Algebra.PolynomialFiber.evaluationAlgebra s
  exact pullbackSpecIso_inv_snd k[X] k (AdjoinRoot f)

/-- The entire geometric fiber is identified with its literal endpoint polynomial quotient. -/
def fiberPolynomialSchemeIso (f : k[X][X]) (s : k) (p : k[X])
    (hp : f.map (evalRingHom s) = p) : fiber f s ≅ Spec (.of (AdjoinRoot p)) :=
  fiberSchemeIso f s ≪≫
    Scheme.Spec.mapIso (endpointFiberEquiv f s p hp).symm.toRingEquiv.toCommRingCatIso.op

@[reassoc (attr := simp)] theorem fiberPolynomialSchemeIso_inv_fst
    (f : k[X][X]) (s : k) (p : k[X]) (hp : f.map (evalRingHom s) = p) :
    (fiberPolynomialSchemeIso f s p hp).inv ≫
        pullback.fst (FiniteFlatCurve.endpoint s) (projection f) =
      Spec.map (CommRingCat.ofHom (AdjoinRoot.of p)) := by
  rw [fiberPolynomialSchemeIso, Iso.trans_inv, Category.assoc, fiberSchemeIso_inv_fst]
  change Spec.map (CommRingCat.ofHom (endpointFiberEquiv f s p hp).toRingHom) ≫
    Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (endpointFiberEquiv f s p hp).commutes

@[reassoc (attr := simp)] theorem fiberPolynomialSchemeIso_inv_snd
    (f : k[X][X]) (s : k) (p : k[X]) (hp : f.map (evalRingHom s) = p) :
    (fiberPolynomialSchemeIso f s p hp).inv ≫
        pullback.snd (FiniteFlatCurve.endpoint s) (projection f) =
      Spec.map (CommRingCat.ofHom (endpoint f s p hp)) := by
  rw [fiberPolynomialSchemeIso, Iso.trans_inv, Category.assoc, fiberSchemeIso_inv_snd]
  change Spec.map (CommRingCat.ofHom (endpointFiberEquiv f s p hp).toRingHom) ≫
    Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro r
    exact (endpointFiberEquiv_of f s p hp r).trans (endpoint_of f s p hp r).symm
  · exact (endpointFiberEquiv_root f s p hp).trans (endpoint_root f s p hp).symm

/-- The endpoint scalar map preserves the original constants and both units. -/
theorem endpoint_targetMap (f : k[X][X]) (h0 : IsUnit (f.eval 0))
    (h1 : IsUnit (f.eval 1)) (s : k) (p : k[X]) (hp : f.map (evalRingHom s) = p)
    (hp0 : IsUnit (p.eval 0)) (hp1 : IsUnit (p.eval 1)) :
    Spec.map (CommRingCat.ofHom (endpoint f s p hp)) ≫ targetMap f h0 h1 =
      polynomialTargetMap p hp0 hp1 := by
  apply pairMap_comp
  · ext r
    change endpoint f s p hp (AdjoinRoot.of f (C r)) = AdjoinRoot.of p r
    rw [endpoint_of, eval_C]
  · simp only [rootUnit_val, endpoint_root]
  · simp only [oneSubRootUnit_val, endpoint_one_sub_root]

/-- Unit evaluations survive the actual scalar specialization. -/
theorem specialize_eval_zero_isUnit (f : k[X][X]) (h0 : IsUnit (f.eval 0))
    (s : k) (p : k[X]) (hp : f.map (evalRingHom s) = p) : IsUnit (p.eval 0) := by
  rw [← hp, ← (evalRingHom s).map_zero, eval_map_apply]
  exact h0.map (evalRingHom s)

/-- The complementary unit condition survives the same specialization. -/
theorem specialize_eval_one_isUnit (f : k[X][X]) (h1 : IsUnit (f.eval 1))
    (s : k) (p : k[X]) (hp : f.map (evalRingHom s) = p) : IsUnit (p.eval 1) := by
  rw [← hp, ← (evalRingHom s).map_one, eval_map_apply]
  exact h1.map (evalRingHom s)

/-- The full scheme-theoretic fiber retains its original two target coordinates. -/
def fiberInclusion (f : k[X][X]) (h0 : IsUnit (f.eval 0))
    (h1 : IsUnit (f.eval 1)) (s : k) : fiber f s ⟶ pointAmbient k :=
  FiniteFlatCurveFamily.fiberInclusion (projection f) (inclusion f h0 h1)
    (inclusion_fst f h0 h1) s

@[reassoc (attr := simp)] theorem fiberInclusion_fst (f : k[X][X])
    (h0 : IsUnit (f.eval 0)) (h1 : IsUnit (f.eval 1)) (s : k) :
    fiberInclusion f h0 h1 s ≫ pullback.fst _ _ =
      pullback.fst (FiniteFlatCurve.endpoint s) (projection f) :=
  FiniteFlatCurveFamily.fiberInclusion_fst _ _ _ _

@[reassoc (attr := simp)] theorem fiberInclusion_snd (f : k[X][X])
    (h0 : IsUnit (f.eval 0)) (h1 : IsUnit (f.eval 1)) (s : k) :
    fiberInclusion f h0 h1 s ≫ pullback.snd _ _ =
      pullback.snd (FiniteFlatCurve.endpoint s) (projection f) ≫ targetMap f h0 h1 := by
  rw [fiberInclusion, FiniteFlatCurveFamily.fiberInclusion_snd]
  exact congrArg (fun t => pullback.snd (FiniteFlatCurve.endpoint s) (projection f) ≫ t)
    (inclusion_snd f h0 h1)

/-- Every whole fiber remains a closed subscheme of the point-target product. -/
theorem fiberInclusion_closed {f : k[X][X]} (hf : f.Monic)
    (h0 : IsUnit (f.eval 0)) (h1 : IsUnit (f.eval 1)) (s : k) :
    IsClosedImmersion (fiberInclusion f h0 h1 s) := by
  let := projection_finite hf
  let := projection_flat hf
  let := inclusion_closed hf h0 h1
  exact FiniteFlatCurveFamily.fiberInclusion_closed _ _ _ _

/-- The endpoint comparison preserves the actual closed image, not only its support. -/
theorem fiberPolynomialSchemeIso_inv_inclusion
    (f : k[X][X]) (h0 : IsUnit (f.eval 0)) (h1 : IsUnit (f.eval 1))
    (s : k) (p : k[X]) (hp : f.map (evalRingHom s) = p)
    (hp0 : IsUnit (p.eval 0)) (hp1 : IsUnit (p.eval 1)) :
    (fiberPolynomialSchemeIso f s p hp).inv ≫ fiberInclusion f h0 h1 s =
      polynomialInclusion p hp0 hp1 := by
  apply pullback.hom_ext
  · rw [Category.assoc, fiberInclusion_fst, polynomialInclusion_fst,
      fiberPolynomialSchemeIso_inv_fst]
  · rw [Category.assoc, fiberInclusion_snd, polynomialInclusion_snd,
      ← Category.assoc, fiberPolynomialSchemeIso_inv_snd,
      endpoint_targetMap]

private theorem finitePushforward_congr {P Q : Scheme.{u}} (f g : P ⟶ Q)
    [IsFinite f] [IsFinite g] (h : f = g) (c : IntegralCycle P) :
    IntegralCycle.finitePushforward f c = IntegralCycle.finitePushforward g c := by
  cases h
  rfl

/-- The full fiber fundamental cycle is the literal endpoint polynomial cycle,
with every generic and nonreduced local multiplicity retained. -/
theorem fiber_fundamental_eq_polynomialCycle (f : k[X][X]) (hf : f.Monic)
    (h0 : IsUnit (f.eval 0)) (h1 : IsUnit (f.eval 1))
    (s : k) (p : k[X]) (hp : f.map (evalRingHom s) = p) (hpm : p.Monic)
    (hp0 : IsUnit (p.eval 0)) (hp1 : IsUnit (p.eval 1)) :
    letI := fiberInclusion_closed hf h0 h1 s
    IntegralCycle.finitePushforward (fiberInclusion f h0 h1 s) (fundamentalCycle (fiber f s)) =
      FiniteCorrespondence.toIntegralCycle (polynomialCycle p hpm hp0 hp1) := by
  let := fiberInclusion_closed hf h0 h1 s
  rw [toIntegralCycle_polynomialCycle,
    ← finitePushforward_fundamentalCycle (fiberPolynomialSchemeIso f s p hp).inv,
    ← AddMonoidHom.comp_apply, ← IntegralCycle.finitePushforward_comp]
  exact finitePushforward_congr _ _
    (fiberPolynomialSchemeIso_inv_inclusion f h0 h1 s p hp hp0 hp1) _

/-- Literal graph restriction at any scalar is its whole endpoint polynomial cycle. -/
theorem graph_restriction (f : k[X][X]) (hf : f.Monic)
    (h0 : IsUnit (f.eval 0)) (h1 : IsUnit (f.eval 1))
    (s : k) (p : k[X]) (hp : f.map (evalRingHom s) = p) (hpm : p.Monic)
    (hp0 : IsUnit (p.eval 0)) (hp1 : IsUnit (p.eval 1)) :
    (Cor.graphFunctor k).map (FiniteFlatCurveFamily.evaluationPoint k s) ≫
        fundamentalCorrespondence f hf h0 h1 = polynomialCycle p hpm hp0 hp1 := by
  let := projection_finite hf
  let := projection_flat hf
  let := inclusion_closed hf h0 h1
  apply FiniteCorrespondence.toIntegralCycle_injective
  exact (FiniteFlatCurveFamily.toIntegralCycle_graph_restriction (projection f)
    (inclusion f h0 h1) (inclusion_fst f h0 h1) s).trans
      (fiber_fundamental_eq_polynomialCycle f hf h0 h1 s p hp hpm hp0 hp1)

/-- The simplex chart uses exactly the original polynomial scalar map. -/
def simplexLineMap (k : Type u) [Field k] :
    AlgebraicSimplex.smoothSiteObj k 1 ⟶ FiniteFlatCurveFamily.line k :=
  SmoothSite.homMk (WeightOneBoundaryNorm.oneSchemeIso k).hom (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact RingHom.ext (WeightOneBoundaryNorm.oneCoordinateEquiv k).symm.commutes)

/-- The specified chart takes each actual simplex evaluation to the same affine evaluation. -/
@[reassoc (attr := simp)] theorem evaluationPoint_simplexLineMap (s : k) :
    WeightOneBoundaryNorm.evaluationPoint k s ≫ simplexLineMap k =
      FiniteFlatCurveFamily.evaluationPoint k s := by
  apply MorphismProperty.Over.Hom.ext
  exact WeightOneBoundaryNorm.evaluationPoint_oneSchemeIso k s

/-- The genuine one-simplex correspondence associated to the whole two-unit family. -/
def singularCorrespondence (f : k[X][X]) (hf : f.Monic)
    (h0 : IsUnit (f.eval 0)) (h1 : IsUnit (f.eval 1)) :
    Cor.simplexProduct (WeightOnePointNorm.point k) 1 ⟶ WeightTwoSymbols.target k :=
  (WeightOneBoundaryNorm.simplexProductIso k 1).hom ≫
    (Cor.graphFunctor k).map (simplexLineMap k) ≫ fundamentalCorrespondence f hf h0 h1

/-- The first literal singular face is the entire zero-endpoint polynomial. -/
theorem singularCorrespondence_face_zero (f : k[X][X]) (hf : f.Monic)
    (h0 : IsUnit (f.eval 0)) (h1 : IsUnit (f.eval 1))
    (p : k[X]) (hp : f.map (evalRingHom 0) = p) (hpm : p.Monic)
    (hp0 : IsUnit (p.eval 0)) (hp1 : IsUnit (p.eval 1)) :
    (WeightOneBoundaryNorm.zeroProductIso k).inv ≫
        (Cor.simplexProductCosimplicial (WeightOnePointNorm.point k)).δ 0 ≫
          singularCorrespondence f hf h0 h1 = polynomialCycle p hpm hp0 hp1 := by
  rw [← Category.assoc, WeightOneBoundaryNorm.zeroProductIso_inv_face]
  simp only [singularCorrespondence, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, ← Functor.map_comp, WeightOneBoundaryNorm.facePoint_zero,
    evaluationPoint_simplexLineMap]
  exact graph_restriction f hf h0 h1 0 p hp hpm hp0 hp1

/-- The second literal singular face is the entire one-endpoint polynomial. -/
theorem singularCorrespondence_face_one (f : k[X][X]) (hf : f.Monic)
    (h0 : IsUnit (f.eval 0)) (h1 : IsUnit (f.eval 1))
    (p : k[X]) (hp : f.map (evalRingHom 1) = p) (hpm : p.Monic)
    (hp0 : IsUnit (p.eval 0)) (hp1 : IsUnit (p.eval 1)) :
    (WeightOneBoundaryNorm.zeroProductIso k).inv ≫
        (Cor.simplexProductCosimplicial (WeightOnePointNorm.point k)).δ 1 ≫
          singularCorrespondence f hf h0 h1 = polynomialCycle p hpm hp0 hp1 := by
  rw [← Category.assoc, WeightOneBoundaryNorm.zeroProductIso_inv_face]
  simp only [singularCorrespondence, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, ← Functor.map_comp, WeightOneBoundaryNorm.facePoint_one,
    evaluationPoint_simplexLineMap]
  exact graph_restriction f hf h0 h1 1 p hp hpm hp0 hp1

/-- Whole endpoint cycles of an actual two-unit monic family have equal weight-two classes. -/
theorem cycleClass_endpoints (f : k[X][X]) (hf : f.Monic)
    (h0 : IsUnit (f.eval 0)) (h1 : IsUnit (f.eval 1))
    (p q : k[X]) (hp : f.map (evalRingHom 0) = p) (hq : f.map (evalRingHom 1) = q)
    (hpm : p.Monic) (hqm : q.Monic)
    (hp0 : IsUnit (p.eval 0)) (hp1 : IsUnit (p.eval 1))
    (hq0 : IsUnit (q.eval 0)) (hq1 : IsUnit (q.eval 1)) :
    WeightTwoSymbols.cycleClass k (polynomialCycle p hpm hp0 hp1) =
      WeightTwoSymbols.cycleClass k (polynomialCycle q hqm hq0 hq1) := by
  have h := WeightTwoSymbols.cycleClass_endpoints k (singularCorrespondence f hf h0 h1)
  rw [singularCorrespondence_face_zero f hf h0 h1 p hp hpm hp0 hp1,
    singularCorrespondence_face_one f hf h0 h1 q hq hqm hq0 hq1] at h
  exact h

/-- The literal zero polynomial remains monic in every characteristic. -/
theorem cubicZero_monic (a : k) : (cubicZero a).Monic := by
  rw [← cubic_specialize_zero a]
  exact (cubic_monic a).map _

/-- The literal factored one polynomial is monic, also with repeated roots. -/
theorem cubicOne_monic (a : k) : (cubicOne a).Monic := by
  rw [← cubic_specialize_one a]
  exact (cubic_monic a).map _

/-- The full cycle of `k[X]/(X³-a³)`, mapped by `(x,1-x)`. -/
def zeroCycle (a : k) (ha : a ≠ 0) (ha3 : a ^ 3 ≠ 1) :
    WeightOnePointNorm.point k ⟶ WeightTwoSymbols.target k :=
  polynomialCycle (cubicZero a) (cubicZero_monic a)
    (specialize_eval_zero_isUnit _ (cubic_eval_zero_isUnit a ha) 0 _ (cubic_specialize_zero a))
    (specialize_eval_one_isUnit _ (cubic_eval_one_isUnit a ha3) 0 _ (cubic_specialize_zero a))

/-- The full cycle of `k[X]/((X-a³)(X²-X+1))`, mapped by `(x,1-x)`. -/
def oneCycle (a : k) (ha : a ≠ 0) (ha3 : a ^ 3 ≠ 1) :
    WeightOnePointNorm.point k ⟶ WeightTwoSymbols.target k :=
  polynomialCycle (cubicOne a) (cubicOne_monic a)
    (specialize_eval_zero_isUnit _ (cubic_eval_zero_isUnit a ha) 1 _ (cubic_specialize_one a))
    (specialize_eval_one_isUnit _ (cubic_eval_one_isUnit a ha3) 1 _ (cubic_specialize_one a))

/-- The entire admissible cubic as a genuine singular one-simplex. -/
def cubicCorrespondence (a : k) (ha : a ≠ 0) (ha3 : a ^ 3 ≠ 1) :
    Cor.simplexProduct (WeightOnePointNorm.point k) 1 ⟶ WeightTwoSymbols.target k :=
  singularCorrespondence (cubic a) (cubic_monic a)
    (cubic_eval_zero_isUnit a ha) (cubic_eval_one_isUnit a ha3)

/-- The actual first cubic face is its full original zero-endpoint cycle. -/
theorem cubicCorrespondence_face_zero (a : k) (ha : a ≠ 0) (ha3 : a ^ 3 ≠ 1) :
    (WeightOneBoundaryNorm.zeroProductIso k).inv ≫
        (Cor.simplexProductCosimplicial (WeightOnePointNorm.point k)).δ 0 ≫
          cubicCorrespondence a ha ha3 = zeroCycle a ha ha3 :=
  singularCorrespondence_face_zero _ _ _ _ _ (cubic_specialize_zero a) _ _ _

/-- The actual second cubic face includes both factors with their whole local lengths. -/
theorem cubicCorrespondence_face_one (a : k) (ha : a ≠ 0) (ha3 : a ^ 3 ≠ 1) :
    (WeightOneBoundaryNorm.zeroProductIso k).inv ≫
        (Cor.simplexProductCosimplicial (WeightOnePointNorm.point k)).δ 1 ≫
          cubicCorrespondence a ha ha3 = oneCycle a ha ha3 :=
  singularCorrespondence_face_one _ _ _ _ _ (cubic_specialize_one a) _ _ _

/-- The actual two full cubic endpoint cycles have equal classes in weight-two raw homology.
The only hypotheses are `a ≠ 0` and `a³ ≠ 1`; this does not assert Steinberg. -/
theorem cubic_cycleClass_endpoints (a : k) (ha : a ≠ 0) (ha3 : a ^ 3 ≠ 1) :
    WeightTwoSymbols.cycleClass k (zeroCycle a ha ha3) =
      WeightTwoSymbols.cycleClass k (oneCycle a ha ha3) := by
  have h := WeightTwoSymbols.cycleClass_endpoints k (cubicCorrespondence a ha ha3)
  rw [cubicCorrespondence_face_zero, cubicCorrespondence_face_one] at h
  exact h

end Motivic.WeightTwoCubicBoundary
