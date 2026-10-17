/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.SmoothSiteNisnevichRepresentativeCechGerms
public import Lean.Util.CollectAxioms

/-! Original arbitrary-point colimit equality gives the literal Čech germ equality. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Motivic
open SmoothSite
universe u v
namespace MotivicTest.SmoothSiteNisnevichRepresentativeCechGerms
variable {S : Scheme.{u}} [IsAffine S] {X : SmoothSite S} {x : X.left}
  (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v})

/-- Actual original germs, not a surrogate group, admit actual section representatives. -/
theorem actual_original_germ_representative
    (a : (nisnevichPointFiberCocone X x F).pt) :
    ∃ (N : NisnevichNeighborhood X x)
      (s : F.obj (op ((nisnevichNeighborhoodFunctor X x).obj N))),
      (nisnevichPointFiberCocone X x F).ι.app (op N) s = a :=
  exists_original_germ_representative F x a

open Lean in
run_cmd do
  for name in #[``actual_original_germ_representative,
      ``representative_pair_cech_germs_eq, ``germs_eq_of_restricted_germs_eq] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original germ representatives and pair matching: standard foundations only."

end MotivicTest.SmoothSiteNisnevichRepresentativeCechGerms
