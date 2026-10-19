/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Spec.PolynomialQuotient.SmoothSite
public import Motivic.Aglib.AlgebraicGeometry.Spec.PolynomialQuotient.PolynomialQuotientChangeBase
public import Motivic.AlgebraicGeometry.Correspondences.Moving.Polynomial.Open.Spans
/-! # Relative polynomial open spans as actual finite correspondences over the original field -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.PolynomialOpenQuotient
universe u
namespace AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
variable {k R A : Type u} [Field k] [CommRing R] [CommRing A]
    [Algebra k R] [Algebra.Smooth k R] [Algebra R A] [Algebra k A]
    [IsScalarTower k R A] [Algebra.Smooth k A]

/-- Whole finite-flat quotients, with the relative target and original k-correspondence group. -/
def cycle (p : A[X]) (hp : p.Monic) (f : R[X])
    (hf : IsUnit (AdjoinRoot.mk p (f.map (algebraMap R A)))) :
    _root_.Motivic.Cor.mk (sourceSite (k := k) (A := A)) ⟶ _root_.Motivic.Cor.mk (openSite (k :=
        k) f) := by
  let : IsFinite (source p) := source_finite p hp
  let : Flat (source p) := source_flat p hp
  exact _root_.Motivic.Cor.ofFiniteFlatSpan (source p) (openTarget (algebraMap R A) p f hf)
    (span_base p f hf)

/-- The whole polynomial span into the unchanged relative affine line. -/
def affineCycle (p : A[X]) (hp : p.Monic) :
    _root_.Motivic.Cor.mk (sourceSite (k := k) (A := A)) ⟶ _root_.Motivic.Cor.mk (lineSite (k :=
        k) (R := R)) := by
  let : IsFinite (source p) := source_finite p hp
  let : Flat (source p) := source_flat p hp
  exact _root_.Motivic.Cor.ofFiniteFlatSpan (source p) (target (algebraMap R A) p) (affine_base p)

theorem cycle_comp_inclusion (p : A[X]) (hp : p.Monic) (f : R[X])
    (hf : IsUnit (AdjoinRoot.mk p (f.map (algebraMap R A)))) :
    cycle (k := k) p hp f hf ≫ (_root_.Motivic.Cor.graphFunctor k).map (openInclusion f) =
      affineCycle (k := k) (R := R) p hp := by
  let : IsFinite (source p) := source_finite p hp
  let : Flat (source p) := source_flat p hp
  rw [cycle, _root_.Motivic.Cor.ofFiniteFlatSpan_comp_graph]
  congr 1
  exact openTarget_inclusion _ _ _ _

end AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
