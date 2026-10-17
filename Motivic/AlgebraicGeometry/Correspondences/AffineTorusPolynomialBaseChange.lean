/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.AffineTorusDivisorEquivalence
public import Motivic.AlgebraicGeometry.Correspondences.FlatLeftGraphComposition
public import Motivic.AlgebraicGeometry.SmoothSiteTorus
public import Motivic.Aglib.AlgebraicGeometry.AdjoinRootBaseChange

/-! # Ordinary coefficient base change of the original affine torus cycles -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent
open Polynomial.BoundaryOneRationalFunctions

universe u

namespace Motivic.AffineTorusPolynomialPresentation

section Quotients
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (p : R[X])

/-- The literal coefficient map of whole polynomial quotient schemes. -/
def polynomialBaseChangeMap :
    Spec (.of (AdjoinRoot (p.map φ))) ⟶ Spec (.of (AdjoinRoot p)) :=
  Spec.map (CommRingCat.ofHom (AdjoinRoot.map φ p (p.map φ) dvd_rfl))

/-- The original quotient square is Cartesian for every scalar map. -/
theorem polynomial_isPullback :
    IsPullback (polynomialProjection (p.map φ)) (polynomialBaseChangeMap φ p)
      (Spec.map (CommRingCat.ofHom φ)) (polynomialProjection p) :=
  AdjoinRootBaseChange.isPullback φ p

/-- Mapped admissibility is retained under an arbitrary coefficient map. -/
theorem polynomialConstant_map_unit (h0 : IsUnit (p.coeff 0)) :
    IsUnit ((p.map φ).coeff 0) := by
  simpa only [coeff_map] using h0.map φ

@[reassoc] theorem polynomialBaseChangeMap_laurent (h0 : IsUnit (p.coeff 0)) :
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
      (LaurentPolynomial.eval₂ (AdjoinRoot.of p) (polynomialUnit p h0)
        (LaurentPolynomial.C r)) =
      LaurentPolynomial.eval₂ (AdjoinRoot.of (p.map φ))
        (polynomialUnit (p.map φ) (polynomialConstant_map_unit φ p h0))
        ((CommRingCat.PolynomialLaurent.laurentMap (CommRingCat.ofHom φ)) (LaurentPolynomial.C r))
    rw [CommRingCat.PolynomialLaurent.laurentMap_C]
    simp
  · change AdjoinRoot.map φ p (p.map φ) dvd_rfl
      (LaurentPolynomial.eval₂ (AdjoinRoot.of p) (polynomialUnit p h0)
        (LaurentPolynomial.T 1)) =
      LaurentPolynomial.eval₂ (AdjoinRoot.of (p.map φ))
        (polynomialUnit (p.map φ) (polynomialConstant_map_unit φ p h0))
        ((CommRingCat.PolynomialLaurent.laurentMap (CommRingCat.ofHom φ)) (LaurentPolynomial.T 1))
    rw [CommRingCat.PolynomialLaurent.laurentMap_T]
    simp

end Quotients

variable {k R S : Type u} [Field k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S]

@[reassoc (attr := simp)] theorem ambientIso_hom_snd :
    (ambientIso k R).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.PolynomialLaurent.laurentMap
        (CommRingCat.ofHom (algebraMap k R))) :=
  (ambient_isPullback k R).isoPullback_hom_snd

/-- The coefficient quotient map retains the original torus coordinate over the field. -/
@[reassoc] theorem polynomialBaseChangeMap_target (φ : R →ₐ[k] S)
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

instance baseMap_smooth : Smooth (baseMap k R) := by
  rw [baseMap, HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.mpr inferInstance

instance baseMap_separated : IsSeparated (baseMap k R) :=
  inferInstanceAs (IsSeparated (Spec.map (CommRingCat.ofHom (algebraMap k R))))

instance baseMap_quasiCompact : QuasiCompact (baseMap k R) :=
  inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k R))))

/-- The affine smooth source with its original structural map. -/
def affineSite (k R : Type u) [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R] :
    SmoothSite (Spec (.of k)) := SmoothSite.mk (baseMap k R)

/-- Every algebra map induces its original smooth-site morphism, with no flatness requirement. -/
def affineMorphism [Algebra.Smooth k S] (φ : R →ₐ[k] S) : affineSite k S ⟶ affineSite k R :=
  SmoothSite.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact φ.commutes r)

variable [IsDomain R] (Z : Generator k R)

/-- Every original integral finite support in the torus is flat over the smooth affine source. -/
instance generator_projection_flat : Flat Z.projection := by
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @Flat) (polynomialSupportIso Z).hom,
    polynomialSupportIso_projection]
  exact polynomialProjection_flat (coordinatePolynomial_monic Z)

omit [Algebra k S] in
/-- The original support's actual whole coefficient fiber is the mapped polynomial quotient. -/
theorem supportBaseChange_isPullback (φ : R →+* S) :
    IsPullback (polynomialProjection ((coordinatePolynomial Z).map φ))
      (polynomialBaseChangeMap φ (coordinatePolynomial Z) ≫ (polynomialSupportIso Z).hom)
      (Spec.map (CommRingCat.ofHom φ)) Z.projection := by
  apply (polynomial_isPullback φ (coordinatePolynomial Z)).of_iso
    (Iso.refl _) (Iso.refl _) (polynomialSupportIso Z) (Iso.refl _)
  · simp
  · simp
  · simp
  · simpa only [Iso.refl_hom, Category.comp_id] using
      (polynomialSupportIso_projection Z).symm

/-- No reduced fiber is substituted in this actual support comparison. -/
def supportBaseChangeIso (φ : R →+* S) :
    Spec (.of (AdjoinRoot ((coordinatePolynomial Z).map φ))) ≅
      Z.graphPullback (Spec.map (CommRingCat.ofHom φ)) :=
  (supportBaseChange_isPullback Z φ).isoPullback

omit [Algebra k S] in
@[reassoc (attr := simp)] theorem supportBaseChangeIso_fst (φ : R →+* S) :
    (supportBaseChangeIso Z φ).hom ≫
      pullback.fst (Spec.map (CommRingCat.ofHom φ)) Z.projection =
        polynomialProjection ((coordinatePolynomial Z).map φ) :=
  (supportBaseChange_isPullback Z φ).isoPullback_hom_fst

omit [Algebra k S] in
@[reassoc (attr := simp)] theorem supportBaseChangeIso_snd (φ : R →+* S) :
    (supportBaseChangeIso Z φ).hom ≫
      pullback.snd (Spec.map (CommRingCat.ofHom φ)) Z.projection =
        polynomialBaseChangeMap φ (coordinatePolynomial Z) ≫ (polynomialSupportIso Z).hom :=
  (supportBaseChange_isPullback Z φ).isoPullback_hom_snd

/-- The whole fiber isomorphism preserves its literal ambient source and torus coordinates. -/
@[reassoc] theorem supportBaseChangeIso_inclusion [Algebra.Smooth k S] (φ : R →ₐ[k] S) :
    (supportBaseChangeIso Z φ.toRingHom).hom ≫
      Z.graphPullbackMap (affineMorphism φ).left (MorphismProperty.Over.w (affineMorphism φ)) =
        polynomialInclusion (k := k) ((coordinatePolynomial Z).map φ.toRingHom)
          (polynomialConstant_map_unit φ.toRingHom _ (coordinatePolynomial_constant_isUnit Z)) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, FiniteCorrespondenceGenerator.graphPullbackMap_fst,
      affineMorphism, SmoothSite.homMk_left, supportBaseChangeIso_fst]
    exact (polynomialInclusion_fst (k := k) _ _).symm
  · simp only [Category.assoc, FiniteCorrespondenceGenerator.graphPullbackMap_snd,
      affineMorphism, SmoothSite.homMk_left, supportBaseChangeIso_snd_assoc]
    rw [← Category.assoc (polynomialSupportIso Z).hom, polynomialSupportIso_inclusion,
      polynomialBaseChangeMap_target]
    rfl

variable [IsDomain S] [Algebra.Smooth k S] [IsNoetherianRing S]

/-- Arbitrary ordinary pullback of an original generator is the entire mapped
polynomial cycle, with every original scheme-theoretic fiber multiplicity. -/
theorem graph_generator_eq_polynomialCycle (φ : R →ₐ[k] S) :
    (Cor.graphFunctor k).map (affineMorphism φ) ≫
        (show Cor.mk (affineSite k R) ⟶ Cor.mk (SmoothSite.torus (.of k)) from Z.cycle) =
      polynomialCycle (k := k) ((coordinatePolynomial Z).map φ.toRingHom)
        ((coordinatePolynomial_monic Z).map φ.toRingHom)
        (polynomialConstant_map_unit φ.toRingHom _ (coordinatePolynomial_constant_isUnit Z)) := by
  let : IsIntegral (affineSite k S).left := inferInstanceAs (IsIntegral (Spec (.of S)))
  let : IsNoetherian (Z.graphPullback (affineMorphism φ).left) :=
    isNoetherian_of_finiteType (pullback.fst (affineMorphism φ).left Z.projection)
  let : IsFinite (polynomialProjection ((coordinatePolynomial Z).map φ.toRingHom)) :=
    polynomialProjection_finite ((coordinatePolynomial_monic Z).map φ.toRingHom)
  let : IsNoetherian (Spec (.of (AdjoinRoot ((coordinatePolynomial Z).map φ.toRingHom)))) :=
    isNoetherian_of_finiteType (polynomialProjection ((coordinatePolynomial Z).map φ.toRingHom))
  have hw : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ baseMap k R = baseMap k S :=
    MorphismProperty.Over.w (affineMorphism φ)
  have hi : (supportBaseChangeIso Z φ.toRingHom).hom ≫
      Z.graphPullbackMap (Spec.map (CommRingCat.ofHom φ.toRingHom)) hw =
    polynomialInclusion (k := k) ((coordinatePolynomial Z).map φ.toRingHom)
      (polynomialConstant_map_unit φ.toRingHom _ (coordinatePolynomial_constant_isUnit Z)) :=
    supportBaseChangeIso_inclusion Z φ
  have hc : IntegralCycle.finitePushforward
      (Z.graphPullbackMap (Spec.map (CommRingCat.ofHom φ.toRingHom)) hw)
      (fundamentalCycle (Z.graphPullback (Spec.map (CommRingCat.ofHom φ.toRingHom)))) =
    FiniteCorrespondence.toIntegralCycle (f := baseMap k S) (g := laurentProjection (.of k))
      (polynomialCycle (k := k) ((coordinatePolynomial Z).map φ.toRingHom)
        ((coordinatePolynomial_monic Z).map φ.toRingHom)
        (polynomialConstant_map_unit φ.toRingHom _ (coordinatePolynomial_constant_isUnit Z))) := by
    rw [toIntegralCycle_polynomialCycle]
    simp only [← hi, IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply,
      finitePushforward_fundamentalCycle]
  apply FiniteCorrespondence.toIntegralCycle_injective
  exact (@FiniteCorrespondenceGenerator.toIntegralCycle_graphFunctor_comp k _
    (affineSite k S) (affineSite k R) (SmoothSite.torus (.of k))
    Z inferInstance (generator_projection_flat (k := k) Z) (affineMorphism φ)).trans hc

end Smooth

end Motivic.AffineTorusPolynomialPresentation
