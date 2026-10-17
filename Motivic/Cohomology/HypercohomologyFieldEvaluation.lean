/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.HypercohomologyEvaluation
public import Motivic.AlgebraicGeometry.Sites.NisnevichFieldEvaluation

/-!
# Unbounded hypercohomology on field-lifting sites at a field

For a topology coarser than the actual field-lifting topology on schemes,
the section-representing free abelian sheaf at `Spec K` is projective. The
unbounded derived-Hom definition therefore agrees with cohomology of the
actual evaluated cochain complex, in every integer degree.

This does not apply to the etale topology: the comparison requires the
displayed order relation to the field-lifting topology. It constructs no
motivic coefficient complex and no Zariski/Nisnevich comparison.
-/

@[expose] public noncomputable section

universe w u

open CategoryTheory Opposite AlgebraicGeometry

namespace Motivic.Hypercohomology

variable (J : GrothendieckTopology Scheme.{u}) (hJ : J ≤ Nisnevich.fieldLiftingTopology)
  (K : Type u) [Field K]

include hJ

/-- The actual free abelian sheaf representing sections at Spec K is projective. -/
theorem projective_freeAbelianSheaf_spec :
    Projective (freeAbelianSheaf.{u + 1, u, u + 1} J (Spec (.of K))) :=
  projective_freeAbelianSheaf.{u + 1, u, u + 1} J _ fun φ ↦
    Nisnevich.surjective_app_of_epi_of_le J hJ K φ

variable [HasDerivedCategory.{w} (Sheaf J AddCommGrpCat.{u + 1})]

/-- Unbounded hypercohomology at Spec K is cohomology of the literal evaluated complex.
No boundedness assumption on the coefficient complex is used. -/
def fieldEvaluationComparison (M : CochainComplex (Sheaf J AddCommGrpCat.{u + 1}) ℤ)
    (p : ℤ) :
    H.{w, u + 1, u, u + 1} J M p (Spec (.of K)) ≃+
      (((Nisnevich.fieldEvaluation J K).mapHomologicalComplex (.up ℤ)).obj M).homology p := by
  letI := projective_freeAbelianSheaf_spec J hJ K
  exact evaluationComparison J (Spec (.of K)) M p

end Motivic.Hypercohomology
