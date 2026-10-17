/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.SmoothSiteNisnevichCommonGerms
public import Lean.Util.CollectAxioms

/-! Original arbitrary-point colimit equality gives the literal Čech germ equality. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Motivic
open SmoothSite
universe u v
namespace MotivicTest.SmoothSiteNisnevichCommonGerms
variable {S : Scheme.{u}} [IsAffine S] {X : SmoothSite S} {x : X.left}
  (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v})

/-- Both sides use the original point fiber, literal pullback and original restriction maps. -/
theorem actual_arbitrary_point_cech_germs
    (N M : NisnevichNeighborhood X x)
    (s : F.obj (op ((nisnevichNeighborhoodFunctor X x).obj N)))
    (t : F.obj (op ((nisnevichNeighborhoodFunctor X x).obj M)))
    (hst : (nisnevichPointFiberCocone X x F).ι.app (op N) s =
      (nisnevichPointFiberCocone X x F).ι.app (op M) t) :
    sectionToNisnevichPoint F (etalePullback N.toBase M.toBase)
        (NisnevichNeighborhood.commonPoint N M default)
        (F.map (etalePullbackFst N.toBase M.toBase).op s) =
      sectionToNisnevichPoint F (etalePullback N.toBase M.toBase)
        (NisnevichNeighborhood.commonPoint N M default)
        (F.map (etalePullbackSnd N.toBase M.toBase).op t) :=
  literal_cech_germs_eq F N M s t hst

/-- No closedness hypothesis is required even when testing equality at a chosen center. -/
theorem actual_center_germ_detection (N : NisnevichNeighborhood X x)
    (s t : F.obj (op ((nisnevichNeighborhoodFunctor X x).obj N))) :
    (nisnevichPointFiberCocone X x F).ι.app (op N) s =
        (nisnevichPointFiberCocone X x F).ι.app (op N) t ↔
      sectionToNisnevichPoint F ((nisnevichNeighborhoodFunctor X x).obj N) N.center s =
        sectionToNisnevichPoint F ((nisnevichNeighborhoodFunctor X x).obj N) N.center t :=
  nisnevichPointFiberCocone_eq_iff_center_germ_eq F N s t

open Lean in
run_cmd do
  for name in #[``actual_arbitrary_point_cech_germs, ``actual_center_germ_detection,
      ``common_refinement_center_germs_eq, ``common_cech_center_germs_eq,
      ``germ_eq_zero_of_pointed_restriction] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original arbitrary-point common Čech germs: standard foundations only."

end MotivicTest.SmoothSiteNisnevichCommonGerms
