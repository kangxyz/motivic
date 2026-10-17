/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.PolynomialQuotientChangeBase
public import Motivic.AlgebraicGeometry.Correspondences.PolynomialOpenSpans
/-! # Relative polynomial open spans as actual finite correspondences over the original field -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.PolynomialOpenQuotient
universe u
namespace Motivic.RelativePolynomialOpenSpans
variable {k R A : Type u} [Field k] [CommRing R] [CommRing A]
    [Algebra k R] [Algebra.Smooth k R] [Algebra R A] [Algebra k A]
    [IsScalarTower k R A] [Algebra.Smooth k A]

abbrev sourceSite := AffineTorusPolynomialPresentation.affineSite k A

/-- The target is the actual relative affine line, still regarded over k. -/
abbrev lineSite : SmoothSite (Spec (.of k)) := by
  let : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k R))) :=
    AffineTorusPolynomialPresentation.baseMap_smooth (k := k) (R := R)
  exact SmoothSite.mk (polynomialProjection (.of R) ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)))

/-- The unchanged principal open of the relative line. -/
abbrev openSite (f : R[X]) : SmoothSite (Spec (.of k)) := by
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  exact SmoothSite.mk ((principalOpen f).ι ≫ (lineSite (k := k) (R := R)).hom)

def openInclusion (f : R[X]) : openSite (k := k) f ⟶ lineSite (k := k) (R := R) :=
  SmoothSite.homMk (principalOpen f).ι rfl

omit [Algebra.Smooth k R] in
/-- The original coefficient tower agrees with the literal structure map. -/
theorem coefficient_base :
    Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k R)) =
        (sourceSite (k := k) (A := A)).hom := by
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact congrArg (fun φ : k →+* A => φ r) (IsScalarTower.algebraMap_eq k R A).symm

/-- Relative target coordinates preserve the original k-structure. -/
theorem span_base (p : A[X]) (f : R[X])
    (hf : IsUnit (AdjoinRoot.mk p (f.map (algebraMap R A)))) :
    source p ≫ (sourceSite (k := k) (A := A)).hom =
      openTarget (algebraMap R A) p f hf ≫ (openSite (k := k) f).hom := by
  rw [← coefficient_base (k := k) (R := R) (A := A)]
  change source p ≫ (_ ≫ _) = openTarget _ _ _ _ ≫ ((principalOpen f).ι ≫ (_ ≫ _))
  rw [← Category.assoc, ← Category.assoc, openTarget_inclusion,
    ← Category.assoc, target_base]

/-- Whole finite-flat quotients, with the relative target and original k-correspondence group. -/
def cycle (p : A[X]) (hp : p.Monic) (f : R[X])
    (hf : IsUnit (AdjoinRoot.mk p (f.map (algebraMap R A)))) :
    Cor.mk (sourceSite (k := k) (A := A)) ⟶ Cor.mk (openSite (k := k) f) := by
  let : IsFinite (source p) := source_finite p hp
  let : Flat (source p) := source_flat p hp
  exact Cor.ofFiniteFlatSpan (source p) (openTarget (algebraMap R A) p f hf)
    (span_base p f hf)

/-- The actual relative target relation before restricting to an open. -/
theorem affine_base (p : A[X]) :
    source p ≫ (sourceSite (k := k) (A := A)).hom =
      target (algebraMap R A) p ≫ (lineSite (k := k) (R := R)).hom := by
  rw [← coefficient_base (k := k) (R := R) (A := A)]
  exact target_changeBase (algebraMap R A)
    (Spec.map (CommRingCat.ofHom (algebraMap k R))) p

/-- The whole polynomial span into the unchanged relative affine line. -/
def affineCycle (p : A[X]) (hp : p.Monic) :
    Cor.mk (sourceSite (k := k) (A := A)) ⟶ Cor.mk (lineSite (k := k) (R := R)) := by
  let : IsFinite (source p) := source_finite p hp
  let : Flat (source p) := source_flat p hp
  exact Cor.ofFiniteFlatSpan (source p) (target (algebraMap R A) p) (affine_base p)

theorem cycle_comp_inclusion (p : A[X]) (hp : p.Monic) (f : R[X])
    (hf : IsUnit (AdjoinRoot.mk p (f.map (algebraMap R A)))) :
    cycle (k := k) p hp f hf ≫ (Cor.graphFunctor k).map (openInclusion f) =
      affineCycle (k := k) (R := R) p hp := by
  let : IsFinite (source p) := source_finite p hp
  let : Flat (source p) := source_flat p hp
  rw [cycle, Cor.ofFiniteFlatSpan_comp_graph]
  congr 1
  exact openTarget_inclusion _ _ _ _

end Motivic.RelativePolynomialOpenSpans
