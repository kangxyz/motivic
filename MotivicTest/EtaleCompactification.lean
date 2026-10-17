/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.EtaleCompactification

/-! Actual finite compactification of the original quasi-compact separated étale source. -/
@[expose] public noncomputable section
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry
universe u

example (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
    {Y : Scheme.{u}} (f : Y ⟶ X) [Etale f] [QuasiCompact f] [IsSeparated f] :
    ∃ (C : Scheme.{u}) (j : Y ⟶ C) (q : C ⟶ X),
      IsOpenImmersion j ∧ IsFinite q ∧ j ≫ q = f :=
  ⟨(Scheme.EtaleCompactification.genericMap X f).normalization,
    Scheme.EtaleCompactification.inclusion X f,
    (Scheme.EtaleCompactification.genericMap X f).fromNormalization,
    inferInstance, inferInstance, Scheme.EtaleCompactification.inclusion_over X f⟩

#print axioms AlgebraicGeometry.Scheme.EtaleCompactification.normalizationIso
#print axioms AlgebraicGeometry.Scheme.EtaleCompactification.inclusion_isOpenImmersion
#print axioms AlgebraicGeometry.Scheme.EtaleCompactification.finite_normalization
#print axioms AlgebraicGeometry.Scheme.EtaleCompactification.proper_compactification
