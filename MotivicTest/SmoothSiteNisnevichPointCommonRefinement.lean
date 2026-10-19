/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Point.CommonRefinement
public import Lean.Util.CollectAxioms

/-! # Arbitrary-point literal common-neighborhood consumers -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.SmoothSite

universe u

variable {S : Scheme.{u}} {X : Scheme.SmoothSite S} {x : X.left}
  (N M : NisnevichNeighborhood X x)

example (q : M ⟶ N) : Etale ((nisnevichNeighborhoodFunctor X x).map q).left :=
  inferInstance

example (q : M ⟶ N) :
    IsIso (((nisnevichNeighborhoodFunctor X x).map q).left.residueFieldMap M.center) :=
  inferInstance

example (q : M ⟶ N) :
    ((nisnevichNeighborhoodFunctor X x).map q).left M.center = N.center :=
  NisnevichNeighborhood.map_center q

example : (nisnevichNeighborhoodFunctor X x).obj (N.common M) ≅
    etalePullback N.toBase M.toBase :=
  N.commonIso M

example : (N.common M).obj.val.left =
    pullback.lift N.obj.val.left M.obj.val.left
      ((Over.w N.obj.val).trans (Over.w M.obj.val).symm) := rfl

example : ((nisnevichNeighborhoodFunctor X x).map (N.commonFst M)).left
    (N.common M).center = N.center :=
  NisnevichNeighborhood.map_center _

example : ((nisnevichNeighborhoodFunctor X x).map (N.commonSnd M)).left
    (N.common M).center = M.center :=
  NisnevichNeighborhood.map_center _

example : (nisnevichNeighborhoodFunctor X x).map (N.commonFst M) =
    (N.commonIso M).hom ≫ etalePullbackFst N.toBase M.toBase :=
  N.map_commonFst M

example : (nisnevichNeighborhoodFunctor X x).map (N.commonSnd M) =
    (N.commonIso M).hom ≫ etalePullbackSnd N.toBase M.toBase :=
  N.map_commonSnd M

open Lean in
open _root_.AlgebraicGeometry.Scheme.SmoothSite.NisnevichNeighborhood in
run_cmd do
  for name in #[``_root_.AlgebraicGeometry.Scheme.SmoothSite.NisnevichNeighborhood.etale_map,
      ``isIso_residueFieldMap_map_center,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.NisnevichNeighborhood.map_center,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.NisnevichNeighborhood.common,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.NisnevichNeighborhood.commonFst,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.NisnevichNeighborhood.commonSnd,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.NisnevichNeighborhood.commonIso,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.NisnevichNeighborhood.common_point,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.NisnevichNeighborhood.common_center,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.NisnevichNeighborhood.map_commonFst,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.NisnevichNeighborhood.map_commonSnd] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual common pointed pullbacks preserve arbitrary centers and their residue fields."
