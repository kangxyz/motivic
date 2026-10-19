/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.AffineProduct
public import Motivic.Aglib.RingTheory.Polynomial.Interpolation.MonicUnit
public import Motivic.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.Torus
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Polynomial quotient maps to Laurent spectra
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace AlgebraicGeometry.PolynomialOpenQuotient.Laurent

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


end AlgebraicGeometry.PolynomialOpenQuotient.Laurent
