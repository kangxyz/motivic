/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleFieldPointNaturality
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleFieldEvaluation
public import Lean.Util.CollectAxioms

/-! Direct consumers of the actual field restriction and ordinary evaluation. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Motivic Motivic.FiniteEtaleSite
universe u
namespace MotivicTest.FiniteEtaleFieldPointNaturality
variable {S T : Scheme.{u}} (b : S ⟶ T)
  (K L : Type u) [Field K] [Field L]
  (q : Spec (.of K) ⟶ S) (r : Spec (.of L) ⟶ S)
  [Etale q] [IsSeparated q] [QuasiCompact q]
  [Etale r] [IsSeparated r] [QuasiCompact r]

/-- The bottom arrow is the original inverse-image sheaf restriction. -/
theorem actual_field_restriction
    (c : fieldObject K q ⟶ fieldObject L r)
    (G : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}) :
    (relativeFieldPointHom b K L q r c).sheafFiber.app G ≫
      (relativeFieldPointInverseImageIso b K q).hom.app G =
    (relativeFieldPointInverseImageIso b L r).hom.app G ≫
      ((inverseImage b).obj G).obj.map c.op :=
  relativeFieldPointInverseImageIso_field_naturality b K L q r c G

/-- These are ordinary sheaf epimorphisms, not transfer-category epimorphisms. -/
theorem actual_field_epi
    {F G : Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}} (a : F ⟶ G) [Epi a] :
    Function.Surjective (a.hom.app (op (fieldObject K q))) :=
  fieldEvaluation_surjective_of_epi K q a

open Lean in
run_cmd do
  for name in #[``actual_field_restriction, ``actual_field_epi,
      ``relativeFieldPointHom_ι, ``relativeFieldPointInverseImageIso_field_naturality,
      ``fieldEvaluation_shortExact] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual field restriction and ordinary evaluation: standard foundations only."

end MotivicTest.FiniteEtaleFieldPointNaturality
