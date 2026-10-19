/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.AffineProduct
public import Motivic.Aglib.AlgebraicGeometry.Spec.PolynomialQuotient.LaurentMap
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Torus.Basic
public import Motivic.Aglib.AlgebraicGeometry.BaseChange.Affine.AdjoinRootBaseChange

/-!
# Scalar maps on polynomial quotient schemes
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

section
open _root_.AlgebraicGeometry.PolynomialOpenQuotient.Laurent
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.SmoothSite

section Quotients
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (p : R[X])

/-- The literal coefficient map of whole polynomial quotient schemes. -/
def _root_.AlgebraicGeometry.PolynomialOpenQuotient.Laurent.polynomialBaseChangeMap :
    Spec (.of (AdjoinRoot (p.map φ))) ⟶ Spec (.of (AdjoinRoot p)) :=
  Spec.map (CommRingCat.ofHom (AdjoinRoot.map φ p (p.map φ) dvd_rfl))

/-- The original quotient square is Cartesian for every scalar map. -/
theorem _root_.AlgebraicGeometry.PolynomialOpenQuotient.Laurent.polynomial_isPullback :
    IsPullback (polynomialProjection (p.map φ)) (polynomialBaseChangeMap φ p)
      (Spec.map (CommRingCat.ofHom φ)) (polynomialProjection p) :=
  AdjoinRootBaseChange.isPullback φ p

/-- Mapped admissibility is retained under an arbitrary coefficient map. -/
theorem _root_.AlgebraicGeometry.PolynomialOpenQuotient.Laurent.polynomialConstant_map_unit (h0 :
    IsUnit (p.coeff 0)) :
    IsUnit ((p.map φ).coeff 0) := by
  simpa only [coeff_map] using h0.map φ

@[reassoc] theorem
    _root_.AlgebraicGeometry.PolynomialOpenQuotient.Laurent.polynomialBaseChangeMap_laurent (h0 :
    IsUnit (p.coeff 0)) :
    polynomialBaseChangeMap φ p ≫ polynomialLaurentMap p h0 =
      polynomialLaurentMap (p.map φ) (polynomialConstant_map_unit φ p h0) ≫
        Spec.map (CommRingCat.PolynomialLaurent.laurentMap (CommRingCat.ofHom φ)) := by
  unfold polynomialBaseChangeMap polynomialLaurentMap
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply CommRingCat.PolynomialLaurent.laurent_hom_ext
  · intro r
    change AdjoinRoot.map φ p (p.map φ) dvd_rfl
      (LaurentPolynomial.eval₂ (AdjoinRoot.of p) (PolynomialOpenQuotient.Laurent.polynomialUnit p
          h0)
        (LaurentPolynomial.C r)) =
      LaurentPolynomial.eval₂ (AdjoinRoot.of (p.map φ))
        (PolynomialOpenQuotient.Laurent.polynomialUnit (p.map φ) (polynomialConstant_map_unit φ p
            h0))
        ((CommRingCat.PolynomialLaurent.laurentMap (CommRingCat.ofHom φ)) (LaurentPolynomial.C r))
    rw [CommRingCat.PolynomialLaurent.laurentMap_C]
    simp
  · change AdjoinRoot.map φ p (p.map φ) dvd_rfl
      (LaurentPolynomial.eval₂ (AdjoinRoot.of p) (PolynomialOpenQuotient.Laurent.polynomialUnit p
          h0)
        (LaurentPolynomial.T 1)) =
      LaurentPolynomial.eval₂ (AdjoinRoot.of (p.map φ))
        (PolynomialOpenQuotient.Laurent.polynomialUnit (p.map φ) (polynomialConstant_map_unit φ p
            h0))
        ((CommRingCat.PolynomialLaurent.laurentMap (CommRingCat.ofHom φ)) (LaurentPolynomial.T 1))
    rw [CommRingCat.PolynomialLaurent.laurentMap_T]
    simp

end Quotients

variable {k R S : Type u} [Field k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S]

@[reassoc (attr := simp)] theorem
    _root_.AlgebraicGeometry.Scheme.PolynomialLaurent.ambientIso_hom_snd :
    (ambientIso k R).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.PolynomialLaurent.laurentMap
        (CommRingCat.ofHom (algebraMap k R))) :=
  (ambient_isPullback k R).isoPullback_hom_snd

/-- The coefficient quotient map retains the original torus coordinate over the field. -/
@[reassoc] theorem
    _root_.AlgebraicGeometry.PolynomialOpenQuotient.Laurent.polynomialBaseChangeMap_target (φ : R
    →ₐ[k] S)
    (p : R[X]) (h0 : IsUnit (p.coeff 0)) :
    polynomialBaseChangeMap φ.toRingHom p ≫
        polynomialInclusion (k := k) p h0 ≫ pullback.snd _ _ =
      polynomialInclusion (k := k) (p.map φ.toRingHom)
        (polynomialConstant_map_unit φ.toRingHom p h0) ≫ pullback.snd _ _ := by
  simp only [polynomialInclusion, Category.assoc, ambientIso_hom_snd]
  rw [← Category.assoc, polynomialBaseChangeMap_laurent, Category.assoc,
    ← Spec.map_comp, ← CommRingCat.PolynomialLaurent.laurentMap_comp]
  congr 3
  ext r
  exact φ.commutes r

section Smooth
variable [Algebra.Smooth k R]

instance _root_.AlgebraicGeometry.Scheme.PolynomialLaurent.baseMap_smooth : Smooth (baseMap k R) :=
    by
  rw [baseMap, HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.mpr inferInstance

instance _root_.AlgebraicGeometry.Scheme.PolynomialLaurent.baseMap_separated : IsSeparated (baseMap
    k R) :=
  inferInstanceAs (IsSeparated (Spec.map (CommRingCat.ofHom (algebraMap k R))))

instance _root_.AlgebraicGeometry.Scheme.PolynomialLaurent.baseMap_quasiCompact : QuasiCompact
    (baseMap k R) :=
  inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k R))))

/-- The affine smooth source with its original structural map. -/
def _root_.AlgebraicGeometry.Scheme.SmoothSite.affineSite (k R : Type u) [Field k] [CommRing R]
    [Algebra k R] [Algebra.Smooth k R] :
    SmoothSite (Spec (.of k)) := SmoothSite.mk (baseMap k R)

/-- Every algebra map induces its original smooth-site morphism, with no flatness requirement. -/
def _root_.AlgebraicGeometry.Scheme.SmoothSite.affineMorphism [Algebra.Smooth k S] (φ : R →ₐ[k] S) :
    affineSite k S ⟶ affineSite k R :=
  SmoothSite.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact φ.commutes r)


end Smooth
end
