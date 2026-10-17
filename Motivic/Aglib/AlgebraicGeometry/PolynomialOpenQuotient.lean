/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.PolynomialOpenMovingPair
public import Motivic.Aglib.AlgebraicGeometry.LaurentTorus
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
/-! # Whole monic quotient schemes with their actual open target -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace AlgebraicGeometry.PolynomialOpenQuotient
variable {k R : Type u} [CommRing k] [CommRing R] (σ : k →+* R) (p : R[X])

/-- The literal principal open in the polynomial spectrum. -/
abbrev principalOpen (f : k[X]) : (Spec (.of k[X])).Opens := PrimeSpectrum.basicOpen f

/-- The literal whole polynomial quotient, without radicalization. -/
def inclusion : Spec (.of (AdjoinRoot p)) ⟶ Spec (.of R[X]) :=
  Spec.map (CommRingCat.ofHom (AdjoinRoot.mk p))

instance inclusion_closed : IsClosedImmersion (inclusion p) :=
  IsClosedImmersion.spec_of_surjective _ (AdjoinRoot.mk_surjective)

/-- Original source projection. -/
def source : Spec (.of (AdjoinRoot p)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (AdjoinRoot.of p))

@[reassoc (attr := simp)] theorem inclusion_projection :
    inclusion p ≫ polynomialProjection (.of R) = source p := by
  rw [inclusion, source, polynomialProjection, ← Spec.map_comp]
  rfl

/-- Literal polynomial-coordinate target over the original coefficient ring. -/
def target : Spec (.of (AdjoinRoot p)) ⟶ Spec (.of k[X]) :=
  inclusion p ≫ Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom σ))

@[reassoc] theorem target_base :
    target σ p ≫ polynomialProjection (.of k) =
      source p ≫ Spec.map (CommRingCat.ofHom σ) := by
  simp only [target, inclusion, source, polynomialProjection, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext x
  change AdjoinRoot.mk p ((C x).map σ) = AdjoinRoot.of p (σ x)
  rw [Polynomial.map_C]
  rfl

/-- Boundary invertibility is proved on the entire quotient, so every point lands in the open. -/
theorem target_range (f : k[X]) (hf : IsUnit (AdjoinRoot.mk p (f.map σ))) :
    Set.range (target σ p) ⊆ ((principalOpen f) : Set _) := by
  rintro _ ⟨x, rfl⟩
  change AdjoinRoot.mk p (f.map σ) ∉ x.asIdeal
  exact fun h ↦ x.isPrime.ne_top (x.asIdeal.eq_top_of_isUnit_mem h hf)

/-- The actual target lift, with the principal open unchanged. -/
def openTarget (f : k[X]) (hf : IsUnit (AdjoinRoot.mk p (f.map σ))) :
    Spec (.of (AdjoinRoot p)) ⟶ (principalOpen f).toScheme :=
  IsOpenImmersion.lift (principalOpen f).ι (target σ p) (by
    rw [Scheme.Opens.range_ι]
    exact target_range σ p f hf)

@[reassoc (attr := simp)] theorem openTarget_inclusion
    (f : k[X]) (hf : IsUnit (AdjoinRoot.mk p (f.map σ))) :
    openTarget σ p f hf ≫ (principalOpen f).ι = target σ p :=
  IsOpenImmersion.lift_fac _ _ _

/-- Monicity gives finiteness of the original source map. -/
theorem source_finite (hp : p.Monic) : IsFinite (source p) := by
  let : Module.Finite R (AdjoinRoot p) := hp.finite_adjoinRoot
  exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

/-- Monicity gives flatness even if the quotient has nilpotents. -/
theorem source_flat (hp : p.Monic) : Flat (source p) := by
  let : Module.Free R (AdjoinRoot p) := hp.free_adjoinRoot
  apply Flat.SpecMap_iff.mpr
  change (AdjoinRoot.of p).Flat
  rw [← AdjoinRoot.algebraMap_eq]
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

end AlgebraicGeometry.PolynomialOpenQuotient
