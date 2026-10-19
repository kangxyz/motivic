/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Moving.Polynomial.Open.SpanIdentities

/-! # Whole linear quotient cycles are the original coordinate graphs -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.PolynomialOpenQuotient
universe u
namespace Motivic.PolynomialOpenSpans
open _root_.AlgebraicGeometry.Scheme
variable {k R : Type u} [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]

/-- The original affine-line coordinate map, with its actual structural equation. -/
def coordinateMorphism (a : R) :
    affineSite (k := k) (R := R) ⟶ SmoothSite.affineLine (.of k) :=
  SmoothSite.homMk (Spec.map (CommRingCat.ofHom (eval₂RingHom (algebraMap k R) a))) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact eval₂_C _ _)

/-- The whole linear quotient gives the literal coordinate graph, without a unit condition. -/
theorem affineCycle_linear_graph (a : R) :
    affineCycle (k := k) (X - C a) (monic_X_sub_C a) =
      (Cor.graphFunctor k).map (coordinateMorphism (k := k) a) := by
  have hs := GlobalBoundaryPencil.ofFiniteFlatSpan_precompIso
    (X := affineSite (k := k) (R := R)) (Y := SmoothSite.affineLine (.of k))
    (asIso (source (X - C a))) (𝟙 _) (coordinateMorphism (k := k) a).left
    ((Category.id_comp _).trans (MorphismProperty.Over.w
      (coordinateMorphism (k := k) a)).symm)
  have ht := hs.trans (DiagonalZeroCycle.ofFiniteFlatSpan_id
    (coordinateMorphism (k := k) a))
  simpa only [asIso_hom, Category.comp_id, affineCycle, target_linear,
    coordinateMorphism, SmoothSite.homMk_left] using ht

/-- Retaining the original open target gives the original lifted graph itself. -/
theorem cycle_linear_graph (a : R) (f : k[X])
    (hf : IsUnit (AdjoinRoot.mk (X - C a) (f.map (algebraMap k R))))
    (j : affineSite (k := k) (R := R) ⟶ openSite f)
    (hj : j ≫ openInclusion f = coordinateMorphism a) :
    cycle (X - C a) (monic_X_sub_C a) f hf = (Cor.graphFunctor k).map j := by
  let : IsOpenImmersion (openInclusion f).left := inferInstanceAs
    (IsOpenImmersion (principalOpen f).ι)
  apply Cor.comp_open_graph_injective (openInclusion f)
  dsimp only
  rw [← Functor.map_comp, hj, cycle_comp_inclusion]
  exact affineCycle_linear_graph a

end Motivic.PolynomialOpenSpans
