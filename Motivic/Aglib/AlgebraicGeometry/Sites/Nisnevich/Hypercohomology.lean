/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Hypercohomology.FieldEvaluation
public import Motivic.Aglib.AlgebraicGeometry.Sites.Nisnevich.Evaluation

/-!
# Unbounded Nisnevich hypercohomology at a field

This specializes the unbounded exact-evaluation comparison to the actual
etale field-lifting topology constructed in `Motivic.Aglib.AlgebraicGeometry.Sites.Nisnevich.Basic`.
Coefficients
are ordinary abelian sheaves on the big scheme site. The coefficient complex
is arbitrary and integer-indexed; no bounded-below assumption is introduced.

The canonical motivic coefficient complex, transfer-compatible sheafification,
the smooth-site comparison and the Zariski/Nisnevich comparison remain separate.
-/

@[expose] public noncomputable section

universe w u

open CategoryTheory AlgebraicGeometry

namespace CategoryTheory.Sheaf.Hypercohomology

variable [HasDerivedCategory.{w} (Sheaf Nisnevich.topology AddCommGrpCat.{u + 1})]

/-- Every unbounded ordinary Nisnevich sheaf complex has hypercohomology at Spec K
canonically identified with cohomology of its actual evaluated complex. -/
def nisnevichFieldEvaluationComparison (K : Type u) [Field K]
    (M : CochainComplex (Sheaf Nisnevich.topology AddCommGrpCat.{u + 1}) ℤ) (p : ℤ) :
    H.{w, u + 1, u, u + 1} Nisnevich.topology M p (Spec (.of K)) ≃+
      (((Nisnevich.evaluation K).mapHomologicalComplex (.up ℤ)).obj M).homology p :=
  fieldEvaluationComparison Nisnevich.topology Nisnevich.topology_le_fieldLiftingTopology K M p

end CategoryTheory.Sheaf.Hypercohomology
