/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Generalizing.GenericPoints
public import Motivic.Aglib.RingTheory.Ideal.GoingDown.BaseChange

/-!
# Components of an actual finite algebra base change

For a finite faithful algebra inclusion from an integrally closed base into
a domain, base change by an integral finite-type algebra has every reduced
integral component surjecting onto the base-changed target. The actual tensor
product is not assumed reduced or a domain. This is an affine componentwise
dominance theorem; normality of arbitrary smooth schemes remains separate.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Every reduced integral component of the actual base-change tensor product
surjects onto the integral finite-type test scheme. No flatness of the original
finite algebra or reducedness of its base change is assumed. -/
theorem finite_baseChange_component_surjective
    (R A B : Type u) [CommRing R] [CommRing A] [IsDomain A] [CommRing B]
    [Algebra R A] [Algebra.FiniteType R A] [Algebra R B]
    [IsDomain B] [FaithfulSMul R B] [Module.Finite R B] [IsIntegrallyClosed R]
    (x : genericPoints (Spec (.of (A ⊗[R] B)))) :
    Function.Surjective
      ((IntegralClosedSubscheme.pointClosure x.val).val.subschemeι ≫
        Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[R] B)))) := by
  have : Algebra.HasGoingDown A (A ⊗[R] B) :=
    Algebra.HasGoingDown.finiteType_baseChange (R := R) (S := B) (A := A)
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[R] B)))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  apply surjective_pointClosure_of_finite_generalizing _ _ x.val x.property
  change GeneralizingMap (PrimeSpectrum.comap (algebraMap A (A ⊗[R] B)))
  exact Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap.mp inferInstance

end AlgebraicGeometry.Scheme.Hom
