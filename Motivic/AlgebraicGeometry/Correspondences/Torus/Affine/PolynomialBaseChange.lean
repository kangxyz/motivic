/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Spec.PolynomialQuotient.ScalarMap

public import Motivic.AlgebraicGeometry.Correspondences.Torus.Affine.DivisorEquivalence
public import Motivic.AlgebraicGeometry.Correspondences.Graph.Flat.LeftComposition
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Torus.Basic
public import Motivic.Aglib.AlgebraicGeometry.BaseChange.Affine.AdjoinRootBaseChange

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
open _root_.AlgebraicGeometry.PolynomialOpenQuotient.Laurent
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.SmoothSite


variable {k R S : Type u} [Field k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S]

section Smooth
variable [Algebra.Smooth k R]
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
