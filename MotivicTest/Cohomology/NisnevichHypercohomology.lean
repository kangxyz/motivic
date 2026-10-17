/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.HypercohomologyNisnevich

/-! # Consumer of unbounded Nisnevich hypercohomology at a field -/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Motivic.Hypercohomology

attribute [local instance] HasDerivedCategory.standard in
example (K : Type u) [Field K]
    (M : CochainComplex (Sheaf Motivic.Nisnevich.topology AddCommGrpCat.{u + 1}) ℤ)
    (p : ℤ) :
    H.{_, u + 1, u, u + 1} Motivic.Nisnevich.topology M p (Spec (.of K)) ≃+
      (((Motivic.Nisnevich.evaluation K).mapHomologicalComplex (.up ℤ)).obj M).homology p :=
  nisnevichFieldEvaluationComparison K M p
