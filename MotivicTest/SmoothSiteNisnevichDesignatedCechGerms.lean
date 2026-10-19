/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.DesignatedCechGerms
public import Lean.Util.CollectAxioms

/-! Original arbitrary-point colimit equality gives the literal Čech germ equality. -/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.SmoothSite
universe u v
namespace MotivicTest.SmoothSiteNisnevichDesignatedCechGerms
variable {S : Scheme.{u}} [IsAffine S] {X : SmoothSite S} {x : X.left}
  (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v})

/-- The input point is arbitrary subject only to its two literal designated projections. -/
theorem actual_designated_cech_germs
    (N M : NisnevichNeighborhood X x)
    (s : F.obj (op ((nisnevichNeighborhoodFunctor X x).obj N)))
    (t : F.obj (op ((nisnevichNeighborhoodFunctor X x).obj M)))
    (hst : (nisnevichPointFiberCocone X x F).ι.app (op N) s =
      (nisnevichPointFiberCocone X x F).ι.app (op M) t)
    (w : (etalePullback N.toBase M.toBase).left)
    (hfst : (etalePullbackFst N.toBase M.toBase).left w = N.center)
    (hsnd : (etalePullbackSnd N.toBase M.toBase).left w = M.center) :
    sectionToNisnevichPoint F (etalePullback N.toBase M.toBase) w
        (F.map (etalePullbackFst N.toBase M.toBase).op s) =
      sectionToNisnevichPoint F (etalePullback N.toBase M.toBase) w
        (F.map (etalePullbackSnd N.toBase M.toBase).op t) :=
  literal_cech_germs_eq_at_designated_point F N M s t hst w hfst hsnd

open Lean in
run_cmd do
  for name in #[``actual_designated_cech_germs,
      ``NisnevichNeighborhood.eq_commonPoint_of_projections] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual designated Čech point germs: standard foundations only."

end MotivicTest.SmoothSiteNisnevichDesignatedCechGerms
