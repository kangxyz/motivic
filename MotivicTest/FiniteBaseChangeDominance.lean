/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.BaseChange.Dominance

/-!
# Actual finite base-change component consumers

The prime quotient test does not assume the finite extension flat. The field
polynomial test instantiates the actual affine morphism and reduced component
closed immersion. Neither test treats the whole tensor product as integral.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u

namespace MotivicTest.FiniteBaseChangeDominance

example (R B : Type u) [CommRing R] [CommRing B] [IsDomain B] [Algebra R B]
    [FaithfulSMul R B] [Module.Finite R B] [IsIntegrallyClosed R]
    (p : Ideal R) [p.IsPrime]
    (x : genericPoints (Spec (.of ((R ⧸ p) ⊗[R] B)))) :
    Function.Surjective
      ((_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure x.val).val.subschemeι ≫
        Spec.map (CommRingCat.ofHom (algebraMap (R ⧸ p) ((R ⧸ p) ⊗[R] B)))) :=
  _root_.AlgebraicGeometry.Scheme.Hom.finite_baseChange_component_surjective R (R ⧸ p) B x

example (K L : Type u) [Field K] [Field L] [Algebra K L] [Module.Finite K L]
    (x : genericPoints (Spec (.of (Polynomial K ⊗[K] L)))) :
    Function.Surjective
      ((_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure x.val).val.subschemeι ≫
        Spec.map (CommRingCat.ofHom (algebraMap (Polynomial K) (Polynomial K ⊗[K] L)))) :=
  _root_.AlgebraicGeometry.Scheme.Hom.finite_baseChange_component_surjective K (Polynomial K) L x

end MotivicTest.FiniteBaseChangeDominance
