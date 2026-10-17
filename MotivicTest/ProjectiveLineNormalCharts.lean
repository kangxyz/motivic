/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Coheight

/-! # Consumers of the actual projective-line charts and normality -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Motivic.MotivicTest.ProjectiveLineNormalCharts
universe u
variable (k : Type u) [Field k]

example : IsIntegral (ProjectiveSpace k (ULift.{u} (Fin 2))) := inferInstance
example : IsLocallyNoetherian (ProjectiveSpace k (ULift.{u} (Fin 2))) := inferInstance
example (x : ProjectiveSpace k (ULift.{u} (Fin 2))) :
    IsIntegrallyClosed ((ProjectiveSpace k (ULift.{u} (Fin 2))).presheaf.stalk x) :=
  inferInstance
example (i : ULift.{u} (Fin 2)) : IsOpenImmersion (ProjectiveLine.chart k i) := inferInstance
example (i : ULift.{u} (Fin 2)) :
    ProjectiveLine.chart k i ≫ ProjectiveSpace.toSpec k (ULift.{u} (Fin 2)) =
      Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)) :=
  ProjectiveLine.chart_toSpec k i

attribute [local instance] specializationOrder

example (x : ProjectiveSpace k (ULift.{u} (Fin 2)))
    (hx : x ≠ genericPoint (ProjectiveSpace k (ULift.{u} (Fin 2)))) :
    Order.coheight x = 1 :=
  ProjectiveLine.coheight_eq_one_of_ne_genericPoint k x hx

open Lean in
run_cmd do
  for name in #[``ProjectiveLine.chart_toSpec, ``ProjectiveLine.chart_isOpenImmersion,
      ``ProjectiveLine.iSup_chart_opensRange, ``ProjectiveLine.stalk_normal_domain,
      ``ProjectiveLine.instIsIntegral, ``ProjectiveLine.coheight_eq_one_of_ne_genericPoint] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual projective-line chart and normality consumers use only standard foundations."

end Motivic.MotivicTest.ProjectiveLineNormalCharts
