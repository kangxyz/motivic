/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.DistinguishedSquare
public import Mathlib.Algebra.Category.Grp.Basic
public import Lean.Util.CollectAxioms

/-! # Actual smooth Nisnevich distinguished-square gluing -/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open  _root_.AlgebraicGeometry.Scheme.SmoothSite

universe u

namespace MotivicTest.SmoothSiteNisnevichDistinguishedSquare
open _root_.AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} (sq : Square (SmoothSite S)) (hpb : sq.IsPullback)
  [IsOpenImmersion sq.f₂₄.left] [Etale sq.f₃₄.left]
  {Z : Scheme.{u}} (z : Z ⟶ sq.X₄.left) [IsClosedImmersion z]
  (hcomp : Set.range z = (Set.range sq.f₂₄.left)ᶜ)
  [IsIso (pullback.snd sq.f₃₄.left z)]

/-- In particular the gluing result applies at the universe of ordinary
abelian sheaves used by the H¹ descent construction. -/
example (F : Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}) :
    (sq.op.map F.obj).IsPullback :=
  isPullback_op_map_of_iso_complement sq hpb z hcomp F

example : Sieve.ofTwoArrows sq.f₂₄ sq.f₃₄ ∈ nisnevichTopology S sq.X₄ :=
  ofTwoArrows_mem_nisnevichTopology_of_iso_complement sq.f₂₄ sq.f₃₄ z hcomp

open Lean in
run_cmd do
  for name in #[``ofTwoArrows_mem_nisnevichTopology_of_field_lifting,
      ``ofTwoArrows_mem_nisnevichTopology_of_iso_complement,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.isPullback_op_map_of_iso_complement] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Smooth Nisnevich distinguished-square gluing uses only standard Lean foundations."

end MotivicTest.SmoothSiteNisnevichDistinguishedSquare
