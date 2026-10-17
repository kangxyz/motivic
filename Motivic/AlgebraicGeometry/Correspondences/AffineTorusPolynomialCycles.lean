/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.AffineTorusPolynomialPresentation
public import Motivic.AlgebraicGeometry.Correspondences.FiniteFlat
public import Motivic.Aglib.RingTheory.MonicUnitInterpolation
public import Motivic.Aglib.AlgebraicGeometry.LaurentTorus

/-!
# Original affine torus generators as whole polynomial cycles

The polynomial quotient is identified with the original support over its actual
ambient product. Its fundamental correspondence retains the whole quotient and
all original generic local lengths. This does not yet assert divisor exactness.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace Motivic.AffineTorusPolynomialPresentation

variable {k R : Type u} [Field k] [CommRing R] [Algebra k R]

/-- The actual unit represented by the quotient root. -/
def polynomialUnit (p : R[X]) (h0 : IsUnit (p.coeff 0)) : (AdjoinRoot p)ˣ :=
  (MonicUnitInterpolation.adjoinRoot_root_isUnit p h0).unit

@[simp] theorem polynomialUnit_val (p : R[X]) (h0 : IsUnit (p.coeff 0)) :
    (polynomialUnit p h0 : AdjoinRoot p) = AdjoinRoot.root p := IsUnit.unit_spec _

/-- The whole polynomial quotient in the original relative Laurent spectrum. -/
def polynomialLaurentMap (p : R[X]) (h0 : IsUnit (p.coeff 0)) :
    Spec (.of (AdjoinRoot p)) ⟶ Spec (.of (LaurentPolynomial R)) :=
  Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ (AdjoinRoot.of p)
    (polynomialUnit p h0)))

instance polynomialLaurentMap_closed (p : R[X]) (h0 : IsUnit (p.coeff 0)) :
    IsClosedImmersion (polynomialLaurentMap p h0) := by
  apply IsClosedImmersion.spec_of_surjective
  intro r
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective r
  refine ⟨Polynomial.toLaurent f, ?_⟩
  change LaurentPolynomial.eval₂ (AdjoinRoot.of p) (polynomialUnit p h0)
    (Polynomial.toLaurent f) = AdjoinRoot.mk p f
  rw [LaurentPolynomial.eval₂_toLaurent, polynomialUnit_val, ← AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.aeval_eq f

/-- The source map of the whole quotient. -/
def polynomialProjection (p : R[X]) : Spec (.of (AdjoinRoot p)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (AdjoinRoot.of p))

@[reassoc (attr := simp)] theorem polynomialLaurentMap_projection
    (p : R[X]) (h0 : IsUnit (p.coeff 0)) :
    polynomialLaurentMap p h0 ≫ laurentProjection (.of R) = polynomialProjection p := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact LaurentPolynomial.eval₂_C _ _

/-- Monicity supplies finiteness of the exact quotient source. -/
theorem polynomialProjection_finite {p : R[X]} (hp : p.Monic) :
    IsFinite (polynomialProjection p) := by
  let : Module.Finite R (AdjoinRoot p) := hp.finite_adjoinRoot
  exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

/-- Monicity supplies flatness without reducing the quotient. -/
theorem polynomialProjection_flat {p : R[X]} (hp : p.Monic) :
    Flat (polynomialProjection p) := by
  let : Module.Free R (AdjoinRoot p) := hp.free_adjoinRoot
  apply Flat.SpecMap_iff.mpr
  change (AdjoinRoot.of p).Flat
  rw [← AdjoinRoot.algebraMap_eq]
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- The quotient's literal closed immersion in the original source-target product. -/
def polynomialInclusion (p : R[X]) (h0 : IsUnit (p.coeff 0)) :
    Spec (.of (AdjoinRoot p)) ⟶ pullback (baseMap k R) (laurentProjection (.of k)) :=
  polynomialLaurentMap p h0 ≫ (ambientIso k R).hom

instance polynomialInclusion_closed (p : R[X]) (h0 : IsUnit (p.coeff 0)) :
    IsClosedImmersion (polynomialInclusion (k := k) p h0) := by
  unfold polynomialInclusion
  infer_instance

@[reassoc (attr := simp)] theorem polynomialInclusion_fst
    (p : R[X]) (h0 : IsUnit (p.coeff 0)) :
    polynomialInclusion (k := k) p h0 ≫ pullback.fst _ _ = polynomialProjection p := by
  simp [polynomialInclusion]

section Cycles
variable [IsNoetherianRing R]

/-- The whole polynomial quotient defines an original finite correspondence. -/
def polynomialCycle (p : R[X]) (hp : p.Monic) (h0 : IsUnit (p.coeff 0)) :
    FiniteCorrespondence (baseMap k R) (laurentProjection (.of k)) := by
  let : IsFinite (polynomialProjection p) := polynomialProjection_finite hp
  let : Flat (polynomialProjection p) := polynomialProjection_flat hp
  let : IsNoetherian (Spec (.of (AdjoinRoot p))) :=
    isNoetherian_of_finiteType (polynomialProjection p)
  exact FiniteFlatCorrespondence.fundamentalCorrespondence (polynomialProjection p)
    (polynomialInclusion p h0) (polynomialInclusion_fst p h0)

theorem toIntegralCycle_polynomialCycle (p : R[X]) (hp : p.Monic)
    (h0 : IsUnit (p.coeff 0)) :
    FiniteCorrespondence.toIntegralCycle (polynomialCycle (k := k) p hp h0) =
      letI : IsFinite (polynomialProjection p) := polynomialProjection_finite hp
      letI : IsNoetherian (Spec (.of (AdjoinRoot p))) :=
        isNoetherian_of_finiteType (polynomialProjection p)
      IntegralCycle.finitePushforward (polynomialInclusion (k := k) p h0)
        (fundamentalCycle (Spec (.of (AdjoinRoot p)))) := by
  let : IsFinite (polynomialProjection p) := polynomialProjection_finite hp
  let : Flat (polynomialProjection p) := polynomialProjection_flat hp
  let : IsNoetherian (Spec (.of (AdjoinRoot p))) :=
    isNoetherian_of_finiteType (polynomialProjection p)
  exact FiniteFlatCorrespondence.toIntegralCycle_fundamentalCorrespondence
    (polynomialProjection p) (polynomialInclusion (k := k) p h0)
    (polynomialInclusion_fst (k := k) p h0)

end Cycles

variable [IsDomain R] [Algebra.Smooth k R] (Z : Generator k R)

/-- The literal monic coordinate polynomial of the original support. -/
def coordinatePolynomial : R[X] := minpoly R (coordinateUnit Z : coordinateRing Z)

omit [IsDomain R] [Algebra.Smooth k R] in
theorem coordinatePolynomial_monic : (coordinatePolynomial Z).Monic :=
  minpoly.monic (Algebra.IsIntegral.isIntegral _)

omit [IsDomain R] [Algebra.Smooth k R] in
theorem coordinatePolynomial_natDegree_pos : 1 ≤ (coordinatePolynomial Z).natDegree :=
  minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral _)

@[simp] theorem polynomialEquiv_symm_coordinate :
    (polynomialEquiv Z).symm (coordinateUnit Z : coordinateRing Z) =
      AdjoinRoot.root (coordinatePolynomial Z) := by
  apply (polynomialEquiv Z).injective
  rw [AlgEquiv.apply_symm_apply]
  exact (polynomialEquiv_root Z).symm

/-- The actual full quotient scheme is the original integral support. -/
def polynomialSupportIso : Spec (.of (AdjoinRoot (coordinatePolynomial Z))) ≅ Z.scheme :=
  Scheme.Spec.mapIso (polynomialEquiv Z).symm.toRingEquiv.toCommRingCatIso.op ≪≫
    Z.scheme.isoSpec.symm

omit [IsDomain R] [Algebra.Smooth k R] in
theorem supportIsoSpec_inv_map {A : Type u} [CommRing A]
    (f : Z.scheme ⟶ Spec (.of A)) :
    Z.scheme.isoSpec.inv ≫ f = Spec.map (CommRingCat.ofHom
      (f.appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom)) := by
  rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

@[reassoc] theorem polynomialSupportIso_projection :
    (polynomialSupportIso Z).hom ≫ Z.projection =
      polynomialProjection (coordinatePolynomial Z) := by
  change Spec.map (CommRingCat.ofHom (polynomialEquiv Z).symm.toRingHom) ≫
    Z.scheme.isoSpec.inv ≫ Z.projection = _
  rw [supportIsoSpec_inv_map, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (polynomialEquiv Z).symm.commutes r

@[reassoc] theorem polynomialSupportIso_laurentEmbedding :
    (polynomialSupportIso Z).hom ≫ laurentEmbedding Z =
      polynomialLaurentMap (coordinatePolynomial Z)
        (coordinatePolynomial_constant_isUnit Z) := by
  change Spec.map (CommRingCat.ofHom (polynomialEquiv Z).symm.toRingHom) ≫
    Z.scheme.isoSpec.inv ≫ laurentEmbedding Z = _
  rw [supportIsoSpec_inv_map, ← Spec.map_comp]
  unfold polynomialLaurentMap
  congr 1
  apply CommRingCat.hom_ext
  apply CommRingCat.PolynomialLaurent.laurent_hom_ext
  · intro r
    change (polynomialEquiv Z).symm (laurentPullback Z (LaurentPolynomial.C r)) = _
    rw [laurentPullback_C]
    exact ((polynomialEquiv Z).symm.commutes r).trans
      (LaurentPolynomial.eval₂_C _ _ r).symm
  · change (polynomialEquiv Z).symm (coordinateUnit Z : coordinateRing Z) =
      LaurentPolynomial.eval₂ (AdjoinRoot.of (coordinatePolynomial Z))
        (polynomialUnit _ (coordinatePolynomial_constant_isUnit Z)) (LaurentPolynomial.T 1)
    simp only [LaurentPolynomial.eval₂_T, zpow_one, polynomialEquiv_symm_coordinate,
      polynomialUnit_val]

@[reassoc] theorem polynomialSupportIso_inclusion :
    (polynomialSupportIso Z).hom ≫ Z.inclusion =
      polynomialInclusion (k := k) (coordinatePolynomial Z)
        (coordinatePolynomial_constant_isUnit Z) := by
  apply (cancel_mono (ambientIso k R).inv).mp
  simpa only [Category.assoc, polynomialInclusion, Iso.hom_inv_id,
    Category.comp_id, laurentEmbedding] using polynomialSupportIso_laurentEmbedding Z

/-- Every original integral generator is the full cycle of its literal monic quotient. -/
theorem generator_cycle_eq_polynomialCycle [IsNoetherianRing R] :
    Z.cycle = polynomialCycle (coordinatePolynomial Z) (coordinatePolynomial_monic Z)
      (coordinatePolynomial_constant_isUnit Z) := by
  let : IsNoetherian Z.scheme := isNoetherian_of_finiteType Z.projection
  let : IsFinite (polynomialProjection (coordinatePolynomial Z)) :=
    polynomialProjection_finite (coordinatePolynomial_monic Z)
  let : IsNoetherian (Spec (.of (AdjoinRoot (coordinatePolynomial Z)))) :=
    isNoetherian_of_finiteType (polynomialProjection (coordinatePolynomial Z))
  let : IsNoetherian (pullback (baseMap k R) (laurentProjection (.of k))) :=
    isNoetherian_of_finiteType (pullback.fst (baseMap k R) (laurentProjection (.of k)))
  apply FiniteCorrespondence.toIntegralCycle_injective
  rw [toIntegralCycle_polynomialCycle]
  simp only [← polynomialSupportIso_inclusion Z,
    IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply,
    finitePushforward_fundamentalCycle, FiniteCorrespondenceGenerator.cycle,
    FiniteCorrespondence.toIntegralCycle_single]
  exact (closedFundamentalCycle_of_isIntegral Z.val).symm

end Motivic.AffineTorusPolynomialPresentation
