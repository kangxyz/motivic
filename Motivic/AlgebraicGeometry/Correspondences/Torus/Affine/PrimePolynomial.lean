/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Torus.Affine.RationalDivisor

/-! # Actual geometric basis generators of prime monic polynomials -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace Motivic.AffineTorusPolynomialPresentation
open _root_.Algebra.Smooth
open _root_.AlgebraicGeometry.PolynomialOpenQuotient.Laurent
open _root_.AlgebraicGeometry.Scheme

variable {k R : Type u} [Field k] [CommRing R] [Algebra k R]

/-- The actual closed support of a monic prime polynomial is an original generator. -/
def primePolynomialGenerator (p : R[X]) (hp : p.Monic)
    (h0 : IsUnit (p.coeff 0)) (hprime : Prime p) : Generator k R := by
  let : IsDomain (AdjoinRoot p) := AdjoinRoot.isDomain_of_prime hprime
  let : IsFinite (polynomialProjection p) := polynomialProjection_finite hp
  let : Flat (polynomialProjection p) := polynomialProjection_flat hp
  let j := polynomialInclusion (k := k) p h0
  have he : correspondenceProjection (baseMap k R) (laurentProjection (.of k)) j.ker =
      inv j.toImage ≫ polynomialProjection p := by
    apply (cancel_epi j.toImage).mp
    simp only [correspondenceProjection, ← Category.assoc, Scheme.Hom.toImage_imageι,
      ]
    simpa only [Category.assoc, IsIso.hom_inv_id_assoc] using
      polynomialInclusion_fst (k := k) p h0
  refine ⟨j.ker, ?_, ?_, ?_⟩
  · exact IsIntegral.of_isIso j.toImage
  · rw [he]
    infer_instance
  · rw [he]
    have h := (polynomialProjection p).image_closure_mem_irreducibleComponents_of_finite_flat
      (genericPoint (Spec (.of (AdjoinRoot p)))) (by simp [genericPoints_eq_singleton])
    rw [(genericPoint_spec (Spec (.of (AdjoinRoot p)))).def, Set.image_univ] at h
    change Set.range (polynomialProjection p ∘ inv j.toImage) ∈ _
    have hsur : Function.Surjective (inv j.toImage) :=
      (Scheme.homeoOfIso (asIso j.toImage).symm).surjective
    rw [Set.range_comp, Set.range_eq_univ.mpr hsur, Set.image_univ]
    exact h

@[simp] theorem primePolynomialGenerator_ideal (p : R[X]) (hp : p.Monic)
    (h0 : IsUnit (p.coeff 0)) (hprime : Prime p) :
    (primePolynomialGenerator (k := k) p hp h0 hprime).val =
      (polynomialInclusion (k := k) p h0).ker := rfl

/-- The prime quotient identifies with the original generator's scheme-theoretic image. -/
def primePolynomialSupportIso (p : R[X]) (hp : p.Monic)
    (h0 : IsUnit (p.coeff 0)) (hprime : Prime p) :
    Spec (.of (AdjoinRoot p)) ≅ (primePolynomialGenerator (k := k) p hp h0 hprime).scheme :=
  asIso (polynomialInclusion (k := k) p h0).toImage

@[reassoc (attr := simp)] theorem primePolynomialSupportIso_inclusion
    (p : R[X]) (hp : p.Monic) (h0 : IsUnit (p.coeff 0)) (hprime : Prime p) :
    (primePolynomialSupportIso (k := k) p hp h0 hprime).hom ≫
      (primePolynomialGenerator (k := k) p hp h0 hprime).inclusion =
        polynomialInclusion (k := k) p h0 := Scheme.Hom.toImage_imageι _

/-- The whole prime-polynomial quotient contributes exactly its original basis generator. -/
theorem polynomialCycle_eq_primeGenerator [IsNoetherianRing R]
    (p : R[X]) (hp : p.Monic) (h0 : IsUnit (p.coeff 0)) (hprime : Prime p) :
    polynomialCycle (k := k) p hp h0 =
      (primePolynomialGenerator (k := k) p hp h0 hprime).cycle := by
  let Z := primePolynomialGenerator (k := k) p hp h0 hprime
  let : IsFinite (polynomialProjection p) := polynomialProjection_finite hp
  let : IsNoetherian (Spec (.of (AdjoinRoot p))) :=
    isNoetherian_of_finiteType (polynomialProjection p)
  let : IsNoetherian Z.scheme := isNoetherian_of_finiteType Z.projection
  let : IsNoetherian (pullback (baseMap k R) (laurentProjection (.of k))) :=
    isNoetherian_of_finiteType (pullback.fst (baseMap k R) (laurentProjection (.of k)))
  apply FiniteCorrespondence.toIntegralCycle_injective
  rw [toIntegralCycle_polynomialCycle]
  simp only [← primePolynomialSupportIso_inclusion p hp h0 hprime,
    IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply,
    finitePushforward_fundamentalCycle, FiniteCorrespondenceGenerator.cycle,
    FiniteCorrespondence.toIntegralCycle_single]
  exact closedFundamentalCycle_of_isIntegral Z.val

@[reassoc] theorem primePolynomialSupportIso_laurentEmbedding
    (p : R[X]) (hp : p.Monic) (h0 : IsUnit (p.coeff 0)) (hprime : Prime p) :
    (primePolynomialSupportIso (k := k) p hp h0 hprime).hom ≫
      (primePolynomialGenerator (k := k) p hp h0 hprime).inclusion ≫ (ambientIso k R).inv =
        polynomialLaurentMap p h0 := by
  rw [← Category.assoc, primePolynomialSupportIso_inclusion]
  simp only [polynomialInclusion, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Equal original supports have equal actual Laurent kernel ideals. -/
theorem primePolynomialGenerator_eq_kernel (p q : R[X])
    (hp : p.Monic) (hq : q.Monic) (hp0 : IsUnit (p.coeff 0)) (hq0 : IsUnit (q.coeff 0))
    (hpprime : Prime p) (hqprime : Prime q)
    (h : primePolynomialGenerator (k := k) p hp hp0 hpprime =
      primePolynomialGenerator (k := k) q hq hq0 hqprime) :
    (polynomialLaurentMap p hp0).ker = (polynomialLaurentMap q hq0).ker := by
  calc
    (polynomialLaurentMap p hp0).ker =
        ((primePolynomialGenerator (k := k) p hp hp0 hpprime).inclusion ≫
          (ambientIso k R).inv).ker := by
      rw [← primePolynomialSupportIso_laurentEmbedding (k := k) p hp hp0 hpprime]
      exact Scheme.Hom.ker_comp_of_isIso _ _
    _ = ((primePolynomialGenerator (k := k) q hq hq0 hqprime).inclusion ≫
          (ambientIso k R).inv).ker := by rw [h]
    _ = (polynomialLaurentMap q hq0).ker := by
      rw [← primePolynomialSupportIso_laurentEmbedding (k := k) q hq hq0 hqprime]
      exact (Scheme.Hom.ker_comp_of_isIso _ _).symm

/-- The actual Laurent kernel records ordinary polynomial divisibility. -/
theorem dvd_of_polynomialLaurentMap_kernel_le (p q : R[X])
    (hp0 : IsUnit (p.coeff 0)) (hq0 : IsUnit (q.coeff 0))
    (h : (polynomialLaurentMap q hq0).ker ≤ (polynomialLaurentMap p hp0).ker) : p ∣ q := by
  have hmem : (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv (toLaurent q) ∈
      (polynomialLaurentMap p hp0).ker.ideal
        ⟨⊤, isAffineOpen_top (Spec (.of (LaurentPolynomial R)))⟩ := by
    apply h ⟨⊤, isAffineOpen_top (Spec (.of (LaurentPolynomial R)))⟩
    rw [polynomialLaurentMap_kernel_top]
    exact Ideal.subset_span (Set.mem_singleton _)
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker] at hmem
  have hn := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
      (LaurentPolynomial.eval₂ (AdjoinRoot.of p) (polynomialUnit p hp0)))) (toLaurent q)
  change (Scheme.ΓSpecIso (.of (AdjoinRoot p))).inv
      (LaurentPolynomial.eval₂ (AdjoinRoot.of p) (polynomialUnit p hp0) (toLaurent q)) =
    (polynomialLaurentMap p hp0).appTop
      ((Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv (toLaurent q)) at hn
  change (polynomialLaurentMap p hp0).appTop
    ((Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv (toLaurent q)) = 0 at hmem
  rw [hmem, polynomialLaurent_eval_toLaurent] at hn
  apply AdjoinRoot.mk_eq_zero.mp
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (AdjoinRoot p))).inv).1
  simpa only [map_zero] using hn

/-- Monic prime polynomials give distinct original geometric basis generators. -/
theorem primePolynomialGenerator_injective (p q : R[X])
    (hp : p.Monic) (hq : q.Monic) (hp0 : IsUnit (p.coeff 0)) (hq0 : IsUnit (q.coeff 0))
    (hpprime : Prime p) (hqprime : Prime q)
    (h : primePolynomialGenerator (k := k) p hp hp0 hpprime =
      primePolynomialGenerator (k := k) q hq hq0 hqprime) : p = q := by
  have he := primePolynomialGenerator_eq_kernel p q hp hq hp0 hq0 hpprime hqprime h
  have hpq := dvd_of_polynomialLaurentMap_kernel_le p q hp0 hq0 he.ge
  have hqp := dvd_of_polynomialLaurentMap_kernel_le q p hq0 hp0 he.le
  exact (eq_of_monic_of_dvd_of_natDegree_le hp hq hpq
    (hq.natDegree_le_of_dvd hpprime.ne_zero hqp)).symm

variable [IsDomain R] [Algebra.Smooth k R]

/-- The original support's coordinate polynomial is prime, since its whole
quotient is the original domain. No unique-factorization hypothesis is used. -/
theorem coordinatePolynomial_prime (Z : Generator k R) : Prime (coordinatePolynomial Z) := by
  let : IsIntegrallyClosed R := isIntegrallyClosed_of_smooth_field k R
  apply (Ideal.span_singleton_prime (coordinatePolynomial_monic Z).ne_zero).mp
  change (Ideal.span {minpoly R (coordinateUnit Z : coordinateRing Z)}).IsPrime
  rw [← Algebra.NormalLaurentPresentation.evaluation_kernel (coordinateUnit Z)
    (Algebra.IsIntegral.isIntegral _)]
  exact RingHom.ker_isPrime _

variable [IsNoetherianRing R]

/-- Every original geometric generator is precisely its prime-polynomial support. -/
theorem generator_eq_primePolynomialGenerator (Z : Generator k R) :
    Z = primePolynomialGenerator (coordinatePolynomial Z) (coordinatePolynomial_monic Z)
      (coordinatePolynomial_constant_isUnit Z) (coordinatePolynomial_prime Z) := by
  apply FiniteCorrespondenceGenerator.cycle_injective
  exact (generator_cycle_eq_polynomialCycle Z).trans
    (polynomialCycle_eq_primeGenerator _ _ _ _)

/-- The coordinate polynomial of a prime-polynomial support is the original
monic polynomial itself, not merely an associated polynomial. -/
@[simp] theorem coordinatePolynomial_primePolynomialGenerator
    (p : R[X]) (hp : p.Monic) (h0 : IsUnit (p.coeff 0)) (hprime : Prime p) :
    coordinatePolynomial (primePolynomialGenerator (k := k) p hp h0 hprime) = p := by
  let Z := primePolynomialGenerator (k := k) p hp h0 hprime
  exact (primePolynomialGenerator_injective p (coordinatePolynomial Z) hp
    (coordinatePolynomial_monic Z) h0 (coordinatePolynomial_constant_isUnit Z)
    hprime (coordinatePolynomial_prime Z) (generator_eq_primePolynomialGenerator Z)).symm

end Motivic.AffineTorusPolynomialPresentation
