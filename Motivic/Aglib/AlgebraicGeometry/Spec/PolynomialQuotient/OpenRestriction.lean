/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Spec.PolynomialQuotient.SmoothSite

/-!
# Restriction of polynomial quotient opens
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.PolynomialOpenQuotient
universe u
namespace AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
open _root_.AlgebraicGeometry.Scheme
variable {k R A : Type u} [Field k] [CommRing R] [CommRing A]
    [Algebra k R] [Algebra.Smooth k R] [Algebra R A] [Algebra k A]
    [IsScalarTower k R A] [Algebra.Smooth k A]

/-- The actual inclusion D(fg) into D(f). -/
def narrowInclusion (f g : R[X]) : openSite (k := k) (f * g) ⟶ openSite (k := k) f :=
  SmoothSite.homMk (Scheme.homOfLE (Spec (.of R[X])) (PrimeSpectrum.basicOpen_mul_le_left f g)) (by
    change Scheme.homOfLE _ _ ≫ ((principalOpen f).ι ≫ _) = _
    rw [← Category.assoc, Scheme.homOfLE_ι]
    rfl)

@[reassoc (attr := simp)] theorem narrowInclusion_comp (f g : R[X]) :
    narrowInclusion (k := k) f g ≫ openInclusion (k := k) f = openInclusion (k := k) (f * g) := by
  apply MorphismProperty.Over.Hom.ext
  exact Scheme.homOfLE_ι _ (PrimeSpectrum.basicOpen_mul_le_left f g)

omit [Algebra.Smooth k R] [Algebra.Smooth k A] [IsScalarTower k R A] in
/-- The larger boundary remains a unit on the same entire quotient. -/
theorem old_boundary_unit (p : A[X]) (f g : R[X])
    (h : IsUnit (AdjoinRoot.mk p ((f * g).map (algebraMap R A)))) :
    IsUnit (AdjoinRoot.mk p (f.map (algebraMap R A))) := by
  rw [Polynomial.map_mul, map_mul] at h
  exact (IsUnit.mul_iff.mp h).1


end AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
