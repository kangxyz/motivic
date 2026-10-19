/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Nisnevich.Hypercohomology

/-! # Consumer of unbounded Nisnevich hypercohomology at a field -/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry _root_.CategoryTheory.Sheaf.Hypercohomology

attribute [local instance] HasDerivedCategory.standard in
example (K : Type u) [Field K]
    (M : CochainComplex (Sheaf Nisnevich.topology AddCommGrpCat.{u + 1}) ℤ)
    (p : ℤ) :
    H.{_, u + 1, u, u + 1} Nisnevich.topology M p (Spec (.of K)) ≃+
      (((Nisnevich.evaluation K).mapHomologicalComplex (.up ℤ)).obj M).homology p :=
  nisnevichFieldEvaluationComparison K M p
