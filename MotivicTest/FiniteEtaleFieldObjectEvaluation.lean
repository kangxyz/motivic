/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleFieldObjectEvaluation
public import Lean.Util.CollectAxioms

/-! Ordinary sheaf evaluation is exact on every actual finite étale field object. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Motivic Motivic.FiniteEtaleSite
universe u
namespace MotivicTest.FiniteEtaleFieldObjectEvaluation

variable {K : Type u} [Field K] (V : FiniteEtaleSite (Spec (.of K)))

/-- The comparison uses the original canonical residue-field restrictions. -/
theorem literal_component_restriction
    (F : Sheaf (nisnevichTopology (Spec (.of K))) AddCommGrpCat.{u + 1})
    (s : F.obj.obj (op V)) (v : V.left) :
    residueComponentSectionsEquiv V F s v = F.obj.map (residueComponentHom V v).op s := rfl

/-- No connectedness assumption is imposed on the original finite étale object. -/
theorem arbitrary_object_epi_surjective
    {F G : Sheaf (nisnevichTopology (Spec (.of K))) AddCommGrpCat.{u + 1}}
    (a : F ⟶ G) [Epi a] : Function.Surjective (a.hom.app (op V)) :=
  objectEvaluation_surjective_of_epi V a

/-- Exactness holds for the original ordinary sheaf sequence evaluated at the original object. -/
theorem ordinary_short_exact_evaluation
    (C : ShortComplex (Sheaf (nisnevichTopology (Spec (.of K))) AddCommGrpCat.{u + 1}))
    (hC : C.ShortExact) : (C.map (objectEvaluation V)).ShortExact :=
  objectEvaluation_shortExact V C hC

open Lean in
run_cmd do
  for name in #[``literal_component_restriction, ``arbitrary_object_epi_surjective,
      ``ordinary_short_exact_evaluation, ``residueComponents_mem_precoverage,
      ``finite_residueComponents, ``residueComponent_restriction_bijective,
      ``residueComponentSectionsEquiv, ``objectEvaluation_surjective_of_epi] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Arbitrary finite étale object evaluation: standard foundations only."

end MotivicTest.FiniteEtaleFieldObjectEvaluation
