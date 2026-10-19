/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.PersistentSectionVanishing
public import Lean.Util.CollectAxioms

/-! Actual degree-zero section detection on an actual open puncture. -/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace MotivicTest.SmoothSitePersistentSectionVanishing
open _root_.AlgebraicGeometry.Scheme.SmoothSite

/-- No higher cohomological vanishing is assumed or concluded. -/
theorem actual_open_puncture_section_vanishes
    {S : Scheme.{u}} [IsAffine S] [IsNoetherian S] (X : Scheme.SmoothSite S)
    (V : X.left.Opens) (x : X.left)
    (F : Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1})
    (s : F.obj.obj (op ((opensFunctor X).obj V)))
    (hs : ∀ z : ((opensFunctor X).obj V).left,
      (openInclusion X V).left z ⤳ x →
        sectionToNisnevichPoint.{u, 0} F.obj ((opensFunctor X).obj V) z s = 0) :
    ∃ W : X.left.Opens, x ∈ W ∧
      F.obj.map (openInclusion ((opensFunctor X).obj V)
        ((openInclusion X V).left ⁻¹ᵁ W)).op s = 0 :=
  exists_open_restriction_eq_zero_of_persistent_germs
    (openInclusion X V) x F.obj F.property s hs

open Lean in
run_cmd do
  for dependency in ← collectAxioms ``actual_open_puncture_section_vanishes do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
      throwError "Unsupported assumption {dependency}"
  logInfo "Actual persistent-germ section detection: standard axioms only."

end MotivicTest.SmoothSitePersistentSectionVanishing
