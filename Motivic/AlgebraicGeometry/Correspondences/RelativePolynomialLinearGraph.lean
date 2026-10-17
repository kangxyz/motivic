/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.RelativePolynomialSpanIdentities

/-! # Whole linear quotient cycles are the original coordinate graphs -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.PolynomialOpenQuotient
universe u
namespace Motivic.RelativePolynomialOpenSpans
variable {k R A : Type u} [Field k] [CommRing R] [CommRing A]
    [Algebra k R] [Algebra.Smooth k R] [Algebra R A] [Algebra k A]
    [IsScalarTower k R A] [Algebra.Smooth k A]

/-- The original affine-line coordinate map, with its actual structural equation. -/
def coordinateMorphism (a : A) :
    sourceSite (k := k) (A := A) ⟶ lineSite (k := k) (R := R) :=
  SmoothSite.homMk (Spec.map (CommRingCat.ofHom (eval₂RingHom (algebraMap R A) a))) (by
    change Spec.map _ ≫ (Spec.map _ ≫ Spec.map _) = _
    rw [← coefficient_base (k := k) (R := R) (A := A), ← Category.assoc]
    congr 1
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact eval₂_C _ _)

/-- The whole linear quotient gives the literal coordinate graph, without a unit condition. -/
theorem affineCycle_linear_graph (a : A) :
    affineCycle (k := k) (R := R) (X - C a) (monic_X_sub_C a) =
      (Cor.graphFunctor k).map (coordinateMorphism (k := k) (R := R) a) := by
  have hs := GlobalBoundaryPencil.ofFiniteFlatSpan_precompIso
    (X := sourceSite (k := k) (A := A)) (Y := lineSite (k := k) (R := R))
    (asIso (source (X - C a))) (𝟙 _) (coordinateMorphism (k := k) (R := R) a).left
    ((Category.id_comp _).trans (MorphismProperty.Over.w
      (coordinateMorphism (k := k) (R := R) a)).symm)
  have ht := hs.trans (DiagonalZeroCycle.ofFiniteFlatSpan_id
    (coordinateMorphism (k := k) (R := R) a))
  simpa only [asIso_hom, Category.comp_id, affineCycle, target_linear,
    coordinateMorphism, SmoothSite.homMk_left] using ht

/-- Retaining the original open target gives the original lifted graph itself. -/
theorem cycle_linear_graph (a : A) (f : R[X])
    (hf : IsUnit (AdjoinRoot.mk (X - C a) (f.map (algebraMap R A))))
    (j : sourceSite (k := k) (A := A) ⟶ openSite (k := k) f)
    (hj : j ≫ openInclusion (k := k) f = coordinateMorphism a) :
    cycle (X - C a) (monic_X_sub_C a) f hf = (Cor.graphFunctor k).map j := by
  let : IsOpenImmersion (openInclusion (k := k) f).left := inferInstanceAs
    (IsOpenImmersion (principalOpen f).ι)
  apply Cor.comp_open_graph_injective (openInclusion (k := k) f)
  dsimp only
  rw [← Functor.map_comp, hj, cycle_comp_inclusion]
  exact affineCycle_linear_graph a

end Motivic.RelativePolynomialOpenSpans
