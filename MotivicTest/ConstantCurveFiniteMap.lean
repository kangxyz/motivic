/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.ConstantCurveFiniteMap

/-! The actual relative finite map and its structural equation. -/
@[expose] public noncomputable section
set_option linter.hashCommand false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.ConstantCurve
universe u
example {k R : Type u} [CommRing k] [CommRing R] (f : k →+* R) (ι : Type u)
    {C : Scheme.{u}} (q : C ⟶ ProjectiveSpace k ι) [IsFinite q] :
    IsFinite (toProjectiveSpace f ι q) ∧
      IsPullback (pullback.snd _ _) (toProjectiveSpace f ι q) q
        (ProjectiveSpace.map f ι) ∧
      toProjectiveSpace f ι q ≫ ProjectiveSpace.toSpec R ι = pullback.fst _ _ :=
  ⟨inferInstance, isPullback_toProjectiveSpace f ι q, toProjectiveSpace_toSpec f ι q⟩
#print axioms AlgebraicGeometry.Scheme.ConstantCurve.isPullback_toProjectiveSpace
