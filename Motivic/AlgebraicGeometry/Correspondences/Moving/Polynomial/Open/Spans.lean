/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Spec.PolynomialQuotient.PolynomialOpenQuotient
public import Motivic.AlgebraicGeometry.Correspondences.Torus.Affine.PolynomialBaseChange
public import Motivic.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.Graph
public import Motivic.Aglib.AlgebraicGeometry.AffineLine.Open.AffineLineReducedComplement
/-! # Actual whole monic-polynomial correspondences into principal opens -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.PolynomialOpenQuotient
universe u
namespace Motivic.PolynomialOpenSpans
open _root_.AlgebraicGeometry.Scheme
variable {k R : Type u} [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]

abbrev affineSite := SmoothSite.affineSite k R

/-- The target is the original open subscheme, not a replacement localization model. -/
abbrev openSite (f : k[X]) : SmoothSite (Spec (.of k)) :=
  AffineLineReducedComplement.openObject (principalOpen f)

/-- Original principal-open inclusion. -/
def openInclusion (f : k[X]) : openSite f ⟶ SmoothSite.affineLine (.of k) :=
  AffineLineReducedComplement.openInclusion (principalOpen f)

/-- The actual quotient span has compatible original coefficient maps. -/
theorem span_base (p : R[X]) (f : k[X])
    (hf : IsUnit (AdjoinRoot.mk p (f.map (algebraMap k R)))) :
    source p ≫ (affineSite (k := k) (R := R)).hom =
      openTarget (algebraMap k R) p f hf ≫ (openSite f).hom := by
  change source p ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) =
    openTarget (algebraMap k R) p f hf ≫ ((principalOpen f).ι ≫ polynomialProjection (.of k))
  rw [← Category.assoc, openTarget_inclusion, target_base]

/-- Every multiplicity of the original monic quotient contributes to the actual correspondence. -/
def cycle (p : R[X]) (hp : p.Monic) (f : k[X])
    (hf : IsUnit (AdjoinRoot.mk p (f.map (algebraMap k R)))) :
    Cor.mk (affineSite (k := k) (R := R)) ⟶ Cor.mk (openSite f) := by
  let : IsFinite (source p) := source_finite p hp
  let : Flat (source p) := source_flat p hp
  exact Cor.ofFiniteFlatSpan (source p) (openTarget (algebraMap k R) p f hf) (span_base p f hf)

/-- Forgetting the open target retains the literal quotient coordinate and the whole cycle. -/
theorem cycle_comp_inclusion (p : R[X]) (hp : p.Monic) (f : k[X])
    (hf : IsUnit (AdjoinRoot.mk p (f.map (algebraMap k R)))) :
    cycle p hp f hf ≫ (Cor.graphFunctor k).map (openInclusion f) =
      letI : IsFinite (source p) := source_finite p hp
      letI : Flat (source p) := source_flat p hp
      Cor.ofFiniteFlatSpan (X := affineSite (k := k) (R := R))
        (Y := SmoothSite.affineLine (.of k)) (source p) (target (algebraMap k R) p)
        (target_base (algebraMap k R) p).symm := by
  let : IsFinite (source p) := source_finite p hp
  let : Flat (source p) := source_flat p hp
  rw [cycle, Cor.ofFiniteFlatSpan_comp_graph]
  congr 1
  exact openTarget_inclusion _ _ _ _

end Motivic.PolynomialOpenSpans
