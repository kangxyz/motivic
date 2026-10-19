/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.Moving.PolynomialRelative
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.LaurentChart
/-! # Actual relative Laurent restriction before any function-field extension of presheaves -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.PolynomialOpenQuotient
universe v u
namespace AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
variable {k R : Type u} [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]

attribute [local instance] laurent_smooth


variable [IsDomain R]

/-- Relative Laurent restriction is injective after the genuine monic/coprime presentation.
The coefficient presheaf is still an arbitrary HI presheaf with transfers over k. -/
theorem laurent_principal_restriction_injective
    (P : _root_.Motivic.PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant)
    (g : R[X]) (hg : g.Monic) (hXg : IsCoprime X g) :
    Function.Injective (P.transfer ((_root_.Motivic.Cor.graphFunctor k).map
      (narrowInclusion (k := k) X g))) := by
  let : IsNoetherianRing (LaurentPolynomial R) :=
    Algebra.FiniteType.isNoetherianRing k (LaurentPolynomial R)
  have hu : IsUnit (((X : R[X]).map (algebraMap R (LaurentPolynomial R))).eval
      (LaurentPolynomial.T 1)) := by
    simpa using (LaurentPolynomial.isUnit_T (R := R) 1)
  obtain ⟨β, hβ⟩ := exists_moving_action (k := k) X g monic_X hg hXg
    (LaurentPolynomial.T 1) hu (laurentSiteIso (k := k) (R := R)).hom
    (laurentSiteIso_coordinate (k := k) (R := R))
  have he : Function.Injective
      (P.transfer ((_root_.Motivic.Cor.graphFunctor k).map (laurentSiteIso (k := k) (R :=
          R)).hom)) :=
    (ConcreteCategory.bijective_of_isIso _).injective
  intro x y hxy
  apply he
  exact (ConcreteCategory.congr_hom (hβ P hP) x).trans
    ((congrArg (fun z => (P.transfer β) z) hxy).trans
      (ConcreteCategory.congr_hom (hβ P hP) y).symm)

end AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
