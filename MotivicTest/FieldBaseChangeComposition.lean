/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.FieldBaseChangeComposition

/-!
# Arbitrary-field actual signed composition consumers

No separability, finite-type field extension, connectedness, effectiveness, or
geometric integrality hypotheses occur. The full cycle comparison and additive
functor are checked against a rejecting standard-foundations axiom allowlist.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open scoped BigOperators

universe u

namespace MotivicTest.FieldBaseChangeComposition

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)
  {X Y Z : SmoothSite.overField k}

/-- The actual signed operation commutes with the actual incidence Tor composition. -/
theorem allSignedComposition
    (α : FiniteCorrespondence X.hom Y.hom) (β : FiniteCorrespondence Y.hom Z.hom) :
    FiniteCorrespondence.fieldBaseChange (X := X) (Y := Z) φ
      (FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := Z) α β) =
    FiniteCorrespondence.incidenceTorPairing L
      (X := (SmoothSite.fieldBaseChange φ).obj X)
      (Y := (SmoothSite.fieldBaseChange φ).obj Y)
      (Z := (SmoothSite.fieldBaseChange φ).obj Z)
      (FiniteCorrespondence.fieldBaseChange (X := X) (Y := Y) φ α)
      (FiniteCorrespondence.fieldBaseChange (X := Y) (Y := Z) φ β) :=
  FiniteCorrespondence.fieldBaseChange_incidenceTorPairing φ α β

/-- Both potentially negative generator coefficients are included in the same theorem. -/
theorem signedGeneratorComposition
    (A : FiniteCorrespondenceGenerator X.hom Y.hom)
    (B : FiniteCorrespondenceGenerator Y.hom Z.hom) (m n : ℤ) :
    FiniteCorrespondence.fieldBaseChange (X := X) (Y := Z) φ
      (FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := Z)
        (Finsupp.single A m) (Finsupp.single B n)) =
    FiniteCorrespondence.incidenceTorPairing L
      (X := (SmoothSite.fieldBaseChange φ).obj X)
      (Y := (SmoothSite.fieldBaseChange φ).obj Y)
      (Z := (SmoothSite.fieldBaseChange φ).obj Z)
      (m • A.fieldBaseChangeCycle φ) (n • B.fieldBaseChangeCycle φ) := by
  simpa only [FiniteCorrespondence.fieldBaseChange_single] using
    allSignedComposition φ (Finsupp.single A m) (Finsupp.single B n)

/-- The bundled category law is the same actual signed operation. -/
theorem actualFunctorComposition {X Y Z : Cor k} (α : X ⟶ Y) (β : Y ⟶ Z) :
    (Cor.fieldBaseChange φ).map (α ≫ β) =
      (Cor.fieldBaseChange φ).map α ≫ (Cor.fieldBaseChange φ).map β :=
  (Cor.fieldBaseChange φ).map_comp α β

/-- The graph-proved full identity is preserved. -/
theorem actualFunctorIdentity (X : Cor k) :
    (Cor.fieldBaseChange φ).map (𝟙 X) = 𝟙 ((Cor.fieldBaseChange φ).obj X) :=
  (Cor.fieldBaseChange φ).map_id X

example : (Cor.fieldBaseChange φ).Additive := inferInstance

open Lean in
run_cmd do
  for name in #[``allSignedComposition, ``signedGeneratorComposition,
      ``actualFunctorComposition, ``actualFunctorIdentity,
      ``FiniteCorrespondenceGenerator.fieldBaseChangeIncidenceTorCycle_eq_pair_sum,
      ``FiniteCorrespondenceGenerator.fieldBaseChangePairTorCycle_coefficient_of_not_generic,
      ``FiniteCorrespondenceGenerator.finitePushforward_fieldBaseChangePairTorCycle,
      ``FiniteCorrespondenceGenerator.fieldBaseChange_incidenceTorCorrespondence,
      ``Cor.fieldBaseChange, ``Cor.fieldBaseChange_additive,
      ``Cor.fieldBaseChangeAdditiveFunctor] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual arbitrary-field signed correspondence composition uses only standard foundations."

end MotivicTest.FieldBaseChangeComposition
