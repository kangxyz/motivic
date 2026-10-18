/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.GraphIdealMovedCycle
public import Motivic.AlgebraicGeometry.Correspondences.IdealFrameMoved
import all Motivic.AlgebraicGeometry.Cycles.IdealFrameMovedDominance
import all Motivic.AlgebraicGeometry.Correspondences.FinitePointCycle
import all Motivic.AlgebraicGeometry.Correspondences.IdealFrameMoved
public import Lean.Util.CollectAxioms
public import Batteries.Tactic.Lint
public import Mathlib.Tactic.Linter.TextBased

/-!
# Original compactification graph with prescribed moved support

The actual graph ideal, canonical infinity frame, marked split frame and exact
affine extension feed the literal moved sum. Integral and nonempty-boundary
hypotheses remain explicit; this does not assert a principal A1 relation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Scheme.Modules Scheme.Modules.Invertible Scheme.Hom

open scoped BigOperators

universe u

namespace MotivicTest.GraphMovedCorrespondence


variable {k : Type u} [Field k] (T Y : SmoothSite (Spec (.of k)))
  {S C D Z : Scheme.{u}} (q : C ⟶ S) [IsProper q]
  (j : T.left ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
  (d : D ⟶ C) (z : Z ⟶ C)
  (hd : Disjoint (Set.range j) (Set.range d))
  (eZ : (Scheme.Modules.pullback (infinityProductMap q j z)).obj
      (idealModule (compactificationGraph q j)) ≅
    SheafOfModules.unit (pullback (pullback.snd (j ≫ q) q) z).ringCatSheaf)

variable (A : (pullback (j ≫ q) q).affineOpens)
  (b : (pullback (pullback.snd (j ≫ q) q) d ⨿
    pullback (pullback.snd (j ≫ q) q) z) ⟶ A.val.toScheme)
  (hb : b ≫ A.val.ι =
    coprod.desc (infinityProductMap q j d) (infinityProductMap q j z))

open Classical in
/-- The exact prescribed original graph extension yields an actual finite
correspondence, with original moved weights and residue-degree collision sums. -/
theorem exists_original_graph_correspondence
    [IsAffine T.left] [IsIntegral (pullback (j ≫ q) q)]
    [IsNoetherian (pullback (j ≫ q) q)] [IsClosedImmersion b]
    [Nonempty ((pullback (pullback.snd (j ≫ q) q) d ⨿
      pullback (pullback.snd (j ≫ q) q) z) : Scheme.{u})]
    {V : Scheme.{u}} [V.IsQuasiAffine]
    (v : V ⟶ pullback (j ≫ q) q) [IsOpenImmersion v]
    [SmoothOfRelativeDimension 1 (v ≫ pullback.fst (j ≫ q) q)]
    (hboundary : (Set.range v)ᶜ ⊆ Set.range
      (coprod.desc (infinityProductMap q j d) (infinityProductMap q j z)))
    (g : V ⟶ Y.left)
    (hbase : v ≫ pullback.fst (j ≫ q) q ≫ T.hom = g ≫ Y.hom) :
    ∃ E : PrescribedAffineFrameExtension A b (relativeCompactificationGraphLine q j)
        (GraphIdealMovedCycle.affineBoundaryFrame q j d z hd eZ A b hb),
      ∃ hW : (Set.range v)ᶜ ⊆ (E.affineOpen.val : Set ↥(pullback (j ≫ q) q : Scheme.{u})),
      ∃ α : Cor.mk T ⟶ Cor.mk Y,
        ∀ H : FiniteCorrespondenceGenerator T.hom Y.hom,
          (show FiniteCorrespondence T.hom Y.hom from α) H =
            ∑ x : (idealFrameMovedCycle (compactificationGraph q j)
                E.affineOpen E.overFrame 1 isUnit_one).support,
              if IdealFrameMovedCorrespondence.generator (compactificationGraph q j)
                  (relativeCompactificationGraphLine q j).property E.affineOpen E.overFrame
                  1 isUnit_one (pullback.fst (j ≫ q) q) v hW g hbase x = H then
                idealFrameMovedCycle (compactificationGraph q j) E.affineOpen E.overFrame
                  1 isUnit_one x.val *
                  ((IdealFrameMovedCorrespondence.productMap (compactificationGraph q j)
                    (relativeCompactificationGraphLine q j).property E.affineOpen E.overFrame
                    1 isUnit_one (pullback.fst (j ≫ q) q) v hW g hbase x).residueDegree
                      (genericPoint (IntegralClosedSubscheme.pointClosure x.val).val.subscheme) : ℤ)
              else 0 := by
  obtain ⟨E, _, _⟩ := GraphIdealMovedCycle.exists_original_graph_moved_sum
    q j d z hd eZ A b hb v hboundary
  have hW : (Set.range v)ᶜ ⊆ (E.affineOpen.val : Set ↥(pullback (j ≫ q) q : Scheme.{u})) := by
    rw [← hb] at hboundary
    exact hboundary.trans E.boundary_range_subset
  refine ⟨E, hW, IdealFrameMovedCorrespondence.correspondence (compactificationGraph q j)
    (relativeCompactificationGraphLine q j).property E.affineOpen E.overFrame
    1 isUnit_one (pullback.fst (j ≫ q) q) v hW g hbase, ?_⟩
  exact IdealFrameMovedCorrespondence.correspondence_coefficient (compactificationGraph q j)
    (relativeCompactificationGraphLine q j).property E.affineOpen E.overFrame
    1 isUnit_one (pullback.fst (j ≫ q) q) v hW g hbase

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[
    `Motivic.AlgebraicGeometry.Cycles.IdealFrameMovedDominance,
    `Motivic.AlgebraicGeometry.Correspondences.FinitePointCycle,
    `Motivic.AlgebraicGeometry.Correspondences.IdealFrameMoved]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ 12 do
    throwError "Exact-origin original graph moved-support declarations are missing."
  for name in declarations do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  let linters ← Lean.Elab.Command.liftCoreM (getChecks true none none)
  unless !linters.isEmpty do
    throwError "No declaration linters selected."
  let results ← Lean.Elab.Command.liftCoreM <|
    Lean.withExporting (isExporting := false) (lintCore declarations linters)
  for (linter, findings) in results do
    for (name, message) in findings.toArray do
      throwError "{linter.name}: {name}: {message}"
  logInfo m!"All {declarations.size} exact-origin declarations: lint and standard axioms passed."

open Lean Mathlib.Linter.TextBased in
run_cmd do
  let options : Lean.Linter.LinterOptions := {
    toOptions := ← getOptions
    linterSets := (Lean.Linter.linterSetsExt.getState (← getEnv)).merged }
  let modules := #[
    `Motivic.AlgebraicGeometry.Cycles.IdealFrameMovedDominance,
    `Motivic.AlgebraicGeometry.Correspondences.FinitePointCycle,
    `Motivic.AlgebraicGeometry.Correspondences.IdealFrameMoved,
    `MotivicTest.GraphMovedCorrespondence]
  let errors ← lintModules options #[] modules .humanReadable false
  let casingErrors ← modulesNotUpperCamelCase options modules
  let filenameErrors ← modulesOSForbidden options modules
  unless errors == 0 && casingErrors == 0 && filenameErrors == 0 do
    throwError "Exact-file source text/style checks failed."
  logInfo "Pinned text/style checks passed for all four selected modules."

end MotivicTest.GraphMovedCorrespondence
