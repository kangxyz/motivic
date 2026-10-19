/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Etale.Fibers.FieldCoproduct

/-! # Direct tests for the canonical finite étale field decomposition -/

public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

variable (X : Scheme.{u}) [IsReduced X] [DiscreteTopology X]

example : IsColimit (Cofan.mk X X.fromSpecResidueField) := X.residueFieldCofanIsColimit

example : (∐ fun x : X ↦ Spec (X.residueField x)) ≅ X := X.residueFieldCoproductIso

example (x : X) :
    Sigma.ι (fun x : X ↦ Spec (X.residueField x)) x ≫
      X.residueFieldCoproductIso.hom = X.fromSpecResidueField x := by simp

section Field

variable {K : Type u} [Field K] {Y : Scheme.{u}}
  (f : Y ⟶ Spec (.of K)) [Etale f] [QuasiCompact f]

example : Finite Y := Scheme.finite_of_etale_over_field f

example : DiscreteTopology Y := Scheme.discreteTopology_of_etale_over_field f

example : IsReduced Y := Scheme.isReduced_of_etale_over_field f

example : (∐ fun y : Y ↦ Spec (Y.residueField y)) ≅ Y := Scheme.etaleFieldCoproductIso f

example (y : Y) :
    Sigma.ι (fun y : Y ↦ Spec (Y.residueField y)) y ≫
      (Scheme.etaleFieldCoproductIso f).hom ≫ f = Y.fromSpecResidueField y ≫ f := by simp

end Field
