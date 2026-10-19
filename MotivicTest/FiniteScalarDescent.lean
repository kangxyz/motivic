/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.FiniteScalarDescent
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Open.FiniteMarkedOpenDescent
import all Motivic.AlgebraicGeometry.Correspondences.BaseChange.ScalarTrace
import all Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.ScalarExtension.Finite.Basic
import all Motivic.Transfers.Presheaf.FiniteScalarTrace
import all Motivic.Transfers.Presheaf.FiniteScalarDescent
import all Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Open.FiniteMarkedOpenDescent
import Mathlib.Tactic.Linter.TextBased
import Lean.Util.CollectAxioms
import Batteries.Tactic.Lint

/-!
# Original two-extension descent on a constructed common marked open

The actual finite scalar projections construct the unchanged common base open.
The extended factorization maps on that chosen open remain explicit inputs.
This does not assert existence of those geometric maps, an affine refinement,
or finite-field strict homotopy invariance.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open  _root_.Motivic.PresheafWithTransfers

universe v u

namespace MotivicTest.FiniteScalarDescent

variable {k E L : Type u} [Field k] [Field E] [Field L]
  [Algebra k E] [Module.Finite k E] [Algebra.IsSeparable k E]
  [Algebra k L] [Module.Finite k L] [Algebra.IsSeparable k L]

/-- Both entire marked scalar fibers survive on one constructed original open.
Any two extended local factorizations on that precise open descend to a single
factorization of the original restriction, in the original coefficient group. -/
theorem commonMarkedOpenFactorization (P : PresheafWithTransfers.{v} k)
    {V X : SmoothSite (Spec (.of k))} (j : V ⟶ X)
    (O : (SmoothSite.finiteScalarExtension (E := E) X).left.Opens)
    (W : (SmoothSite.finiteScalarExtension (E := L) X).left.Opens)
    (S : Set X.left)
    (hO : (SmoothSite.finiteScalarProjection (E := E) X).left ⁻¹' S ⊆ O)
    (hW : (SmoothSite.finiteScalarProjection (E := L) X).left ⁻¹' S ⊆ W)
    (hdegree : (Module.finrank k E).Coprime (Module.finrank k L)) :
    ∃ B : X.left.Opens, S ⊆ B ∧
      (SmoothSite.finiteScalarProjection (E := E) X).left ⁻¹ᵁ B ≤ O ∧
      (SmoothSite.finiteScalarProjection (E := L) X).left ⁻¹ᵁ B ≤ W ∧
      let U := SmoothSite.mk (B.ι ≫ X.hom)
      let a : U ⟶ X := SmoothSite.homMk B.ι rfl
      ∀ (φ : P.sections (Cor.mk (SmoothSite.finiteScalarExtension (E := E) V)) ⟶
          P.sections (Cor.mk (SmoothSite.finiteScalarExtension (E := E) U)))
        (ψ : P.sections (Cor.mk (SmoothSite.finiteScalarExtension (E := L) V)) ⟶
          P.sections (Cor.mk (SmoothSite.finiteScalarExtension (E := L) U))),
        P.transfer ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := E) j)) ≫ φ =
            P.transfer ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := E) a)) →
        P.transfer ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := L) j)) ≫ ψ =
            P.transfer ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := L) a)) →
        ∃ θ : P.sections (Cor.mk V) ⟶ P.sections (Cor.mk U),
          P.transfer ((Cor.graphFunctor k).map j) ≫ θ =
            P.transfer ((Cor.graphFunctor k).map a) := by
  obtain ⟨B, hS, hE, hL⟩ :=
    (SmoothSite.finiteScalarProjection (E := E) X).left.exists_common_marked_open
      (SmoothSite.finiteScalarProjection (E := L) X).left O W S hO hW
  refine ⟨B, hS, hE, hL, ?_⟩
  dsimp only
  intro φ ψ hφ hψ
  have : Flat (SmoothSite.homMk (X := SmoothSite.mk (B.ι ≫ X.hom))
      (Y := X) B.ι rfl).left := inferInstanceAs (Flat B.ι)
  exact exists_factorization_of_coprime_finiteScalar P j
    (SmoothSite.homMk (X := SmoothSite.mk (B.ι ≫ X.hom)) (Y := X) B.ι rfl)
    φ ψ hφ hψ hdegree

/-- The descended original factorization implies original local vanishing,
without a sheaf or homotopy-invariance hypothesis. -/
theorem originalLocalZero (P : PresheafWithTransfers.{v} k)
    {U V X : SmoothSite (Spec (.of k))} (j : V ⟶ X) (a : U ⟶ X)
    (θ : P.sections (Cor.mk V) ⟶ P.sections (Cor.mk U))
    (hθ : P.transfer ((Cor.graphFunctor k).map j) ≫ θ =
      P.transfer ((Cor.graphFunctor k).map a))
    (s : P.sections (Cor.mk X)) (hs : P.transfer ((Cor.graphFunctor k).map j) s = 0) :
    P.transfer ((Cor.graphFunctor k).map a) s = 0 := by
  have h := congrArg (fun f => f s) hθ
  change θ (P.transfer ((Cor.graphFunctor k).map j) s) =
    P.transfer ((Cor.graphFunctor k).map a) s at h
  simpa only [hs, map_zero] using h.symm

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[`Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.ScalarExtension.Finite.Basic,
      `Motivic.AlgebraicGeometry.Correspondences.BaseChange.ScalarTrace,
    `Motivic.Transfers.Presheaf.FiniteScalarTrace,
    `Motivic.Transfers.Presheaf.FiniteScalarDescent,
    `Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Open.FiniteMarkedOpenDescent]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ 10 do
    throwError "The exact original scalar descent declarations are missing."
  for name in declarations do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  let linters ← Lean.Elab.Command.liftCoreM (getChecks true none none)
  unless !linters.isEmpty do
    throwError "No declaration linters were selected."
  let results ← Lean.Elab.Command.liftCoreM <|
    Lean.withExporting (isExporting := false) (lintCore declarations linters)
  let mut failed := false
  for (linter, findings) in results do
    for (name, message) in findings.toArray do
      logError m!"{linter.name}: {name}: {message}"
      failed := true
  if failed then
    throwError "The exact-origin declaration lint found errors."
  logInfo m!"Original finite scalar descent: {declarations.size} declarations passed."

open Lean Mathlib.Linter.TextBased in
run_cmd do
  let options : Lean.Linter.LinterOptions := {
    toOptions := ← getOptions
    linterSets := (Lean.Linter.linterSetsExt.getState (← getEnv)).merged }
  let modules := #[`Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.ScalarExtension.Finite.Basic,
      `Motivic.AlgebraicGeometry.Correspondences.BaseChange.ScalarTrace,
    `Motivic.Transfers.Presheaf.FiniteScalarTrace,
    `Motivic.Transfers.Presheaf.FiniteScalarDescent,
    `Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Open.FiniteMarkedOpenDescent,
        `MotivicTest.FiniteScalarDescent]
  let errors ← lintModules options #[] modules .humanReadable false
  let casingErrors ← modulesNotUpperCamelCase options modules
  let filenameErrors ← modulesOSForbidden options modules
  unless errors == 0 && casingErrors == 0 && filenameErrors == 0 do
    throwError "Finite scalar descent text/style checks failed."
  logInfo "Pinned Lean text/style passed for five exact finite scalar descent sources."

end MotivicTest.FiniteScalarDescent
