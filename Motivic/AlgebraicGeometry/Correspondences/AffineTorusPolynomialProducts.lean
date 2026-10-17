/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.AffineTorusPolynomialCycles
public import Motivic.AlgebraicGeometry.Correspondences.ProductZeroCycles
public import Mathlib.AlgebraicGeometry.FunctionField

/-! # Product additivity for original affine polynomial correspondences -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace Motivic.AffineTorusPolynomialPresentation

variable {k R : Type u} [Field k] [CommRing R] [Algebra k R]

theorem polynomialLaurent_eval_toLaurent (p : R[X]) (h0 : IsUnit (p.coeff 0))
    (q : R[X]) :
    LaurentPolynomial.eval₂ (AdjoinRoot.of p) (polynomialUnit p h0) (toLaurent q) =
      AdjoinRoot.mk p q := by
  rw [LaurentPolynomial.eval₂_toLaurent, polynomialUnit_val, ← AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.aeval_eq q

/-- The Laurent presentation retains exactly the principal ideal, not its radical. -/
theorem polynomialLaurent_eval_kernel (p : R[X]) (h0 : IsUnit (p.coeff 0)) :
    RingHom.ker (LaurentPolynomial.eval₂ (AdjoinRoot.of p) (polynomialUnit p h0)) =
      Ideal.span {toLaurent p} := by
  apply le_antisymm
  · intro f hf
    obtain ⟨n, q, hq⟩ := LaurentPolynomial.exists_T_pow f
    have hq0 : AdjoinRoot.mk p q = 0 := by
      rw [← polynomialLaurent_eval_toLaurent p h0, hq, map_mul,
        RingHom.mem_ker.mp hf, zero_mul]
    obtain ⟨r, hr⟩ := AdjoinRoot.mk_eq_zero.mp hq0
    apply (Ideal.unit_mul_mem_iff_mem (Ideal.span {toLaurent p})
      (LaurentPolynomial.isUnit_T n)).mp
    rw [mul_comm, ← hq, hr, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
  · apply Ideal.span_le.mpr
    rintro x (rfl : x = toLaurent p)
    change LaurentPolynomial.eval₂ (AdjoinRoot.of p) (polynomialUnit p h0) (toLaurent p) = 0
    rw [polynomialLaurent_eval_toLaurent, AdjoinRoot.mk_self]

/-- The original scheme kernel on the affine torus is the actual principal ideal. -/
theorem polynomialLaurentMap_kernel_top (p : R[X]) (h0 : IsUnit (p.coeff 0)) :
    (polynomialLaurentMap p h0).ker.ideal
        ⟨⊤, isAffineOpen_top (Spec (.of (LaurentPolynomial R)))⟩ =
      Ideal.span {(Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv (toLaurent p)} := by
  rw [Scheme.Hom.ker_apply]
  apply Ideal.comap_injective_of_surjective
    (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv.hom
    (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).symm.commRingCatIsoToRingEquiv.surjective
  rw [RingHom.comap_ker]
  have hn := congrArg CommRingCat.Hom.hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
      (LaurentPolynomial.eval₂ (AdjoinRoot.of p) (polynomialUnit p h0))))
  change (Scheme.ΓSpecIso (.of (AdjoinRoot p))).inv.hom.comp
      (LaurentPolynomial.eval₂ (AdjoinRoot.of p) (polynomialUnit p h0)) =
    (polynomialLaurentMap p h0).appTop.hom.comp
      (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv.hom at hn
  rw [← hn]
  have hi : Function.Injective (Scheme.ΓSpecIso (.of (AdjoinRoot p))).inv.hom :=
    (Scheme.ΓSpecIso (.of (AdjoinRoot p))).symm.commRingCatIsoToRingEquiv.injective
  rw [RingHom.ker_comp_of_injective _ hi, polynomialLaurent_eval_kernel]
  have hm : Ideal.span {(Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv (toLaurent p)} =
      (Ideal.span {toLaurent p}).map
        (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv.hom := by
    rw [Ideal.map_span, Set.image_singleton]
  have hb : Function.Bijective (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv.hom :=
    (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).symm.commRingCatIsoToRingEquiv.bijective
  rw [hm, Ideal.comap_map_of_bijective _ hb]

/-- The literal polynomial as an element of the actual torus stalk. -/
def polynomialGerm (p : R[X]) (x : Spec (.of (LaurentPolynomial R))) :
    (Spec (.of (LaurentPolynomial R))).presheaf.stalk x :=
  (Spec (.of (LaurentPolynomial R))).presheaf.germ ⊤ x (by trivial)
    ((Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv (toLaurent p))

theorem polynomialLaurentMap_kernel_stalk (p : R[X]) (h0 : IsUnit (p.coeff 0))
    (x : Spec (.of (LaurentPolynomial R))) :
    (polynomialLaurentMap p h0).ker.stalk x = Ideal.span {polynomialGerm p x} := by
  rw [Scheme.IdealSheafData.stalk_eq_map _
    ⟨⊤, isAffineOpen_top (Spec (.of (LaurentPolynomial R)))⟩ (by trivial),
    polynomialLaurentMap_kernel_top, Ideal.map_span, Set.image_singleton]
  rfl

@[simp] theorem polynomialGerm_mul (p q : R[X])
    (x : Spec (.of (LaurentPolynomial R))) :
    polynomialGerm (p * q) x = polynomialGerm p x * polynomialGerm q x := by
  simp only [polynomialGerm, map_mul]

theorem polynomialGerm_regular [IsDomain R] (p : R[X]) (hp : p.Monic)
    (x : Spec (.of (LaurentPolynomial R))) :
    polynomialGerm p x ∈ nonZeroDivisors ((Spec (.of (LaurentPolynomial R))).presheaf.stalk x) := by
  apply mem_nonZeroDivisors_iff_ne_zero.mpr
  intro h
  have h₁ : (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv (toLaurent p) = 0 :=
    germ_injective_of_isIntegral (Spec (.of (LaurentPolynomial R))) x (by trivial)
      (by simpa only [polynomialGerm, map_zero] using h)
  have h₂ : toLaurent p = 0 :=
    (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv).1
      (by simpa only [map_zero] using h₁)
  exact hp.ne_zero (Polynomial.toLaurent_eq_zero.mp h₂)

/-- Product additivity uses the actual generic local lengths of all three
whole quotient schemes. Neither radicalization nor a cycle identity is assumed. -/
theorem polynomialCycle_mul [IsDomain R] [IsNoetherianRing R]
    (p q : R[X]) (hp : p.Monic) (hq : q.Monic)
    (hp0 : IsUnit (p.coeff 0)) (hq0 : IsUnit (q.coeff 0)) :
    polynomialCycle (k := k) (p * q) (hp.mul hq) (by simpa using hp0.mul hq0) =
      polynomialCycle (k := k) p hp hp0 + polynomialCycle (k := k) q hq hq0 := by
  let hpq0 : IsUnit ((p * q).coeff 0) := by simpa using hp0.mul hq0
  let : IsFinite (polynomialProjection p) := polynomialProjection_finite hp
  let : IsFinite (polynomialProjection q) := polynomialProjection_finite hq
  let : IsFinite (polynomialProjection (p * q)) := polynomialProjection_finite (hp.mul hq)
  let : Flat (polynomialProjection p) := polynomialProjection_flat hp
  let : Flat (polynomialProjection q) := polynomialProjection_flat hq
  let : Flat (polynomialProjection (p * q)) := polynomialProjection_flat (hp.mul hq)
  let : IsNoetherian (Spec (.of (AdjoinRoot p))) :=
    isNoetherian_of_finiteType (polynomialProjection p)
  let : IsNoetherian (Spec (.of (AdjoinRoot q))) :=
    isNoetherian_of_finiteType (polynomialProjection q)
  let : IsNoetherian (Spec (.of (AdjoinRoot (p * q)))) :=
    isNoetherian_of_finiteType (polynomialProjection (p * q))
  let : IsFinite (polynomialLaurentMap p hp0 ≫ laurentProjection (.of R)) := by
    rw [polynomialLaurentMap_projection]
    infer_instance
  let : IsFinite (polynomialLaurentMap q hq0 ≫ laurentProjection (.of R)) := by
    rw [polynomialLaurentMap_projection]
    infer_instance
  let : IsFinite (polynomialLaurentMap (p * q) hpq0 ≫ laurentProjection (.of R)) := by
    rw [polynomialLaurentMap_projection]
    infer_instance
  let : Flat (polynomialLaurentMap p hp0 ≫ laurentProjection (.of R)) := by
    rw [polynomialLaurentMap_projection]
    infer_instance
  let : Flat (polynomialLaurentMap q hq0 ≫ laurentProjection (.of R)) := by
    rw [polynomialLaurentMap_projection]
    infer_instance
  let : Flat (polynomialLaurentMap (p * q) hpq0 ≫ laurentProjection (.of R)) := by
    rw [polynomialLaurentMap_projection]
    infer_instance
  have h := ProductZeroCycles.fundamentalCycle_product
    (polynomialLaurentMap p hp0) (polynomialLaurentMap q hq0)
    (polynomialLaurentMap (p * q) hpq0) (laurentProjection (.of R))
    (fun x _ => ⟨polynomialGerm p x, polynomialGerm q x, polynomialGerm_regular q hq x,
      polynomialLaurentMap_kernel_stalk p hp0 x, polynomialLaurentMap_kernel_stalk q hq0 x,
      by rw [polynomialLaurentMap_kernel_stalk, polynomialGerm_mul]⟩)
  apply FiniteCorrespondence.toIntegralCycle_injective
  rw [map_add, toIntegralCycle_polynomialCycle, toIntegralCycle_polynomialCycle,
    toIntegralCycle_polynomialCycle]
  simpa only [polynomialInclusion, IntegralCycle.finitePushforward_comp,
    AddMonoidHom.comp_apply, map_add] using
    congrArg (IntegralCycle.finitePushforward (ambientIso k R).hom) h

@[simp] theorem polynomialCycle_one [IsDomain R] [IsNoetherianRing R] :
    polynomialCycle (k := k) (1 : R[X]) monic_one (by simp) = 0 := by
  have h := polynomialCycle_mul (k := k) (1 : R[X]) 1 monic_one monic_one
    (by simp) (by simp)
  simp only [one_mul] at h
  apply add_left_cancel (a := polynomialCycle (k := k) (1 : R[X]) monic_one (by simp))
  simpa only [add_zero] using h.symm

end Motivic.AffineTorusPolynomialPresentation
