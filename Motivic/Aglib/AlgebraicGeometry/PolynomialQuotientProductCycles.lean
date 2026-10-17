/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.PolynomialOpenQuotient
public import Motivic.AlgebraicGeometry.Correspondences.ProductZeroCycles
public import Mathlib.AlgebraicGeometry.FunctionField
public import Motivic.AlgebraicGeometry.Scheme.FiniteTypeNoetherian

/-! # Product additivity of whole monic polynomial quotient cycles

The equality is in the original integral-cycle group of `Spec R[T]`, with
actual finite pushforwards and generic local lengths. No quotient is reduced,
and neither coprimality nor a unit constant coefficient is required.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace AlgebraicGeometry.PolynomialOpenQuotient
variable {R : Type u} [CommRing R]

/-- The closed immersion retains the exact principal ideal at the affine global chart. -/
theorem inclusion_kernel_top (p : R[X]) :
    (inclusion p).ker.ideal ⟨⊤, isAffineOpen_top (Spec (.of R[X]))⟩ =
      Ideal.span {(Scheme.ΓSpecIso (.of R[X])).inv p} := by
  rw [Scheme.Hom.ker_apply]
  apply Ideal.comap_injective_of_surjective (Scheme.ΓSpecIso (.of R[X])).inv.hom
    (Scheme.ΓSpecIso (.of R[X])).symm.commRingCatIsoToRingEquiv.surjective
  rw [RingHom.comap_ker]
  have hn := congrArg CommRingCat.Hom.hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (AdjoinRoot.mk p)))
  change (Scheme.ΓSpecIso (.of (AdjoinRoot p))).inv.hom.comp (AdjoinRoot.mk p) =
    (inclusion p).appTop.hom.comp (Scheme.ΓSpecIso (.of R[X])).inv.hom at hn
  rw [← hn]
  have hi : Function.Injective (Scheme.ΓSpecIso (.of (AdjoinRoot p))).inv.hom :=
    (Scheme.ΓSpecIso (.of (AdjoinRoot p))).symm.commRingCatIsoToRingEquiv.injective
  rw [RingHom.ker_comp_of_injective _ hi]
  have hk : RingHom.ker (AdjoinRoot.mk p) = Ideal.span {p} := Ideal.mk_ker
  rw [hk]
  have hm : Ideal.span {(Scheme.ΓSpecIso (.of R[X])).inv p} =
      (Ideal.span {p}).map (Scheme.ΓSpecIso (.of R[X])).inv.hom := by
    rw [Ideal.map_span, Set.image_singleton]
  have hb : Function.Bijective (Scheme.ΓSpecIso (.of R[X])).inv.hom :=
    (Scheme.ΓSpecIso (.of R[X])).symm.commRingCatIsoToRingEquiv.bijective
  rw [hm, Ideal.comap_map_of_bijective _ hb]

/-- The original polynomial in the actual local ring of the polynomial spectrum. -/
def polynomialGerm (p : R[X]) (x : Spec (.of R[X])) :
    (Spec (.of R[X])).presheaf.stalk x :=
  (Spec (.of R[X])).presheaf.germ ⊤ x (by trivial) ((Scheme.ΓSpecIso (.of R[X])).inv p)

/-- The actual closed-source stalk ideal, not its radical. -/
theorem inclusion_kernel_stalk (p : R[X]) (x : Spec (.of R[X])) :
    (inclusion p).ker.stalk x = Ideal.span {polynomialGerm p x} := by
  rw [Scheme.IdealSheafData.stalk_eq_map _
    ⟨⊤, isAffineOpen_top (Spec (.of R[X]))⟩ (by trivial), inclusion_kernel_top,
    Ideal.map_span, Set.image_singleton]
  rfl

@[simp] theorem polynomialGerm_mul (p q : R[X]) (x : Spec (.of R[X])) :
    polynomialGerm (p * q) x = polynomialGerm p x * polynomialGerm q x := by
  simp only [polynomialGerm, map_mul]

/-- Monic polynomials remain regular in every original ambient stalk over a domain. -/
theorem polynomialGerm_regular [IsDomain R] (p : R[X]) (hp : p.Monic)
    (x : Spec (.of R[X])) :
    polynomialGerm p x ∈ nonZeroDivisors ((Spec (.of R[X])).presheaf.stalk x) := by
  apply mem_nonZeroDivisors_iff_ne_zero.mpr
  intro h
  have h₁ : (Scheme.ΓSpecIso (.of R[X])).inv p = 0 :=
    germ_injective_of_isIntegral (Spec (.of R[X])) x (by trivial)
      (by simpa only [polynomialGerm, map_zero] using h)
  apply hp.ne_zero
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R[X])).inv).1
    (by simpa only [map_zero] using h₁)

/-- Actual finite pushforward of the whole monic quotient's fundamental cycle. -/
def quotientCycle [IsNoetherianRing R] (p : R[X]) (hp : p.Monic) :
    Motivic.IntegralCycle (Spec (.of R[X])) := by
  let : IsFinite (source p) := source_finite p hp
  let : IsNoetherian (Spec (.of (AdjoinRoot p))) := Motivic.isNoetherian_of_finiteType (source p)
  exact Motivic.IntegralCycle.finitePushforward (inclusion p)
    (Motivic.fundamentalCycle (Spec (.of (AdjoinRoot p))))

/-- Product additivity retains all original generic multiplicities, including
repeated factors. This is an equality of actual ambient cycles. -/
theorem quotientCycle_mul [IsDomain R] [IsNoetherianRing R]
    (p q : R[X]) (hp : p.Monic) (hq : q.Monic) :
    quotientCycle (p * q) (hp.mul hq) = quotientCycle p hp + quotientCycle q hq := by
  let : IsFinite (source p) := source_finite p hp
  let : IsFinite (source q) := source_finite q hq
  let : IsFinite (source (p * q)) := source_finite (p * q) (hp.mul hq)
  let : Flat (source p) := source_flat p hp
  let : Flat (source q) := source_flat q hq
  let : Flat (source (p * q)) := source_flat (p * q) (hp.mul hq)
  let : IsNoetherian (Spec (.of (AdjoinRoot p))) := Motivic.isNoetherian_of_finiteType (source p)
  let : IsNoetherian (Spec (.of (AdjoinRoot q))) := Motivic.isNoetherian_of_finiteType (source q)
  let : IsNoetherian (Spec (.of (AdjoinRoot (p * q)))) :=
    Motivic.isNoetherian_of_finiteType (source (p * q))
  let : IsFinite (inclusion p ≫ polynomialProjection (.of R)) := by
    rw [inclusion_projection]; infer_instance
  let : IsFinite (inclusion q ≫ polynomialProjection (.of R)) := by
    rw [inclusion_projection]; infer_instance
  let : IsFinite (inclusion (p * q) ≫ polynomialProjection (.of R)) := by
    rw [inclusion_projection]; infer_instance
  let : Flat (inclusion p ≫ polynomialProjection (.of R)) := by
    rw [inclusion_projection]; infer_instance
  let : Flat (inclusion q ≫ polynomialProjection (.of R)) := by
    rw [inclusion_projection]; infer_instance
  let : Flat (inclusion (p * q) ≫ polynomialProjection (.of R)) := by
    rw [inclusion_projection]; infer_instance
  exact Motivic.ProductZeroCycles.fundamentalCycle_product
    (inclusion p) (inclusion q) (inclusion (p * q)) (polynomialProjection (.of R))
    (fun x _ => ⟨polynomialGerm p x, polynomialGerm q x, polynomialGerm_regular q hq x,
      inclusion_kernel_stalk p x, inclusion_kernel_stalk q x,
      by rw [inclusion_kernel_stalk, polynomialGerm_mul]⟩)

end AlgebraicGeometry.PolynomialOpenQuotient
