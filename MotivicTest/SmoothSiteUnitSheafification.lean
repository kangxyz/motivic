/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSiteUnitSheafification
public import Lean.Util.CollectAxioms

/-! # Direct audit of the actual native sheafified unit singular complex -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Motivic.SmoothSite

universe u

namespace MotivicTest.SmoothSiteUnitSheafification

variable (k : Type u) [Field k]

/-- This consumer uses the original native singular sheaf complex in every degree. -/
def actual_native_unit_homotopy_equiv :
    HomotopyEquiv
      (SingularComplex.sheafObj (nisnevichTopology (Spec (.of k)))
        (AlgebraicSimplex.cosimplicialSmoothSite k) (largeUnitsPresheaf (Spec (.of k))))
      ((ChainComplex.single₀ _).obj (largeUnitsSheaf (Spec (.of k)))) :=
  (HomotopyEquiv.ofIso (unitSheafifiedSingularIso k)).trans
    (unitSingularSheafHomotopyEquiv k)

open Lean in
run_cmd do
  for name in #[``unitRawTermIso, ``unitRawTermIso_simplex, ``unitUnderlying_d_app,
      ``unitRawComplexIso,
      ``unitSheafifiedSingularIso, ``actual_native_unit_homotopy_equiv] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Native unit singular comparison uses only standard Lean foundations."

end MotivicTest.SmoothSiteUnitSheafification
