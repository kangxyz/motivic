/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.ActualConstantCurveMap

/-! The actual source map and the original target twist are both retained. -/
@[expose] public noncomputable section
set_option linter.hashCommand false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.ConstantCurve
universe u
example {k R : Type u} [CommRing k] [CommRing R]
    (b : Spec (.of R) ⟶ Spec (.of k)) (ι : Type u)
    {C : Scheme.{u}} (q : C ⟶ ProjectiveSpace k ι) [IsFinite q] :
    IsFinite (actualToProjectiveSpace b ι q) ∧
      actualToProjectiveSpace b ι q ≫ ProjectiveSpace.toSpec R ι = pullback.fst _ _ :=
  ⟨inferInstance, actualToProjectiveSpace_toSpec b ι q⟩
example {k R : Type u} [CommRing k] [CommRing R]
    (b : Spec (.of R) ⟶ Spec (.of k)) (ι : Type u)
    {C : Scheme.{u}} (q : C ⟶ ProjectiveSpace k ι) (d : ℤ) :=
  actualOriginalTwistIso b ι q d
#print axioms AlgebraicGeometry.Scheme.ConstantCurve.actualOriginalTwistIso
#print axioms AlgebraicGeometry.Scheme.ConstantCurve.actualToProjectiveSpace_isPullback
