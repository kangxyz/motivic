/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.Boundary.Presheaf.AffineWeilDescent
import all Motivic.Aglib.AlgebraicGeometry.BaseChange.Affine.ScalarPullback
import all Motivic.Aglib.AlgebraicGeometry.WeilRestriction.Affine.FiniteFree.Scalar
import all Motivic.Aglib.AlgebraicGeometry.WeilRestriction.Affine.Witness
import all Motivic.Aglib.AlgebraicGeometry.WeilRestriction.Affine.ActualPair
import all Motivic.Aglib.AlgebraicGeometry.BaseChange.Affine.ScalarChart
import all Motivic.Aglib.AlgebraicGeometry.WeilRestriction.Affine.NativePair
import all Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.AffineWeilRefinement
import all Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Affine.WeilRefinement
import all Motivic.Transfers.Presheaf.RestrictionDifferenceRefinement
import all Motivic.Transfers.Presheaf.FiniteScalarRefinementDifference
import all Motivic.Transfers.Presheaf.FiniteScalarEtaleCorrection
import all Motivic.Cohomology.A1.Boundary.Presheaf.FiniteSeparableDescent
import all Motivic.Cohomology.A1.Boundary.Presheaf.AffineWeilDescent
public import Lean.Util.CollectAxioms
public import Batteries.Tactic.Lint
public import Mathlib.Tactic.Linter.TextBased

/-! # Actual original boundary witness from affine scalar corrections

This consumer applies the constructed-refinement endpoint to the literal
canonical image sieve and the prescribed original base arrow. Every correction
section and its actual punctured equation remains visible in the hypotheses.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Motivic
open _root_.AlgebraicSimplex
open _root_.Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open _root_.Motivic.FiniteEtaleSite
open OriginalPresheaf

universe u

namespace MotivicTest.AffineWeilBoundaryDescent
open _root_.AlgebraicGeometry.Scheme (EtaleSeparatedFiniteType SmoothSite)

variable {k L₁ L₂ A T : Type u} [Field k] [Field L₁] [Field L₂]
variable [Algebra k L₁] [Algebra k L₂]
variable [Module.Finite k L₁] [Module.Finite k L₂]
variable [Algebra.IsSeparable k L₁] [Algebra.IsSeparable k L₂]
variable [CommRing A] [CommRing T] [Algebra k A] [Algebra A T]
variable (X : SmoothSite (Spec (.of k))) (P : PresheafWithTransfers.{u + 1} k)
variable (V : EtaleSeparatedFiniteType X.left)
variable {W : EtaleSeparatedFiniteType (SmoothSite.a1Cylinder (.of k) X).left}
variable (W₀ : SmoothSite (Spec (.of k)))


variable (q₀ : W₀ ⟶ SmoothSite.a1Cylinder (.of k) ((toSmoothSite X).obj V)) [Etale q₀.left]
variable (z₀ : ((toSmoothSite X).obj V) ⟶ W₀) (hz₀ : z₀ ≫ q₀ = SmoothSite.a1Section (.of k)
  ((toSmoothSite X).obj V) 0)
variable (e₀ : W₀ ⟶ (toSmoothSite (SmoothSite.a1Cylinder (.of k) X)).obj W)
variable (he₀ : e₀.left ≫ W.hom = q₀.left ≫ ((cylinderNeighborhood X).obj V).hom)
variable (v : V ⟶ (baseChange (SmoothSite.a1Section (.of k) X 0).left).obj W)
variable (hv : z₀.left ≫ e₀.left =
  v.left ≫ pullback.fst W.hom (SmoothSite.a1Section (.of k) X 0).left)
variable (e : Spec (.of A) ≅ W₀.left) (he : e.hom ≫ W₀.hom = Spec.algebraMap k A)
variable (d : Spec (.of T) ≅ V.left)
variable (hmark : d.hom ≫ z₀.left = Spec.algebraMap A T ≫ e.hom)


variable (φ₀ : (SmoothSite.etalePullback q₀ (SmoothSite.contractionOpen (.of k) ((toSmoothSite
  X).obj V))) ⟶ ((toSmoothSite (SmoothSite.torusCylinder (.of k) X)).obj ((baseChange
  (SmoothSite.contractionOpen (.of k) X).left).obj W)))
variable (hφ₁ : φ₀.left ≫ pullback.fst W.hom
  (SmoothSite.contractionOpen (.of k) X).left = (SmoothSite.etalePullbackFst q₀
    (SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj V))).left ≫ e₀.left)
variable (hφ₂ : φ₀.left ≫ pullback.snd W.hom
  (SmoothSite.contractionOpen (.of k) X).left = (SmoothSite.etalePullbackSnd q₀
    (SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj V))).left ≫
    (SmoothSite.productMap (toBase X V) (𝟙 (SmoothSite.torus (.of k)))).left)
variable (s : sections P (Cor.mk ((toSmoothSite (SmoothSite.torusCylinder (.of k) X)).obj
  ((baseChange (SmoothSite.contractionOpen (.of k) X).left).obj W))))

variable {E₁ : SmoothSite (Spec (.of L₁))} [IsAffine E₁.left]
variable (f₁ : E₁ ⟶ (SmoothSite.fieldBaseChange (algebraMap k L₁)).obj W₀) [Etale f₁.left]
variable (t₁ : (SmoothSite.fieldBaseChange (algebraMap k L₁)).obj ((toSmoothSite X).obj V) ⟶ E₁)
  (ht₁ : t₁ ≫ f₁ = (SmoothSite.fieldBaseChange (algebraMap k L₁)).map z₀)
variable (u₁ : sections (finiteSeparableExtension L₁ P)
  (Cor.mk ((SmoothSite.fieldBaseChange (algebraMap k L₁)).obj (SmoothSite.torusCylinder (.of k)
    ((toSmoothSite X).obj V)))))
variable (c₁ : sections (finiteSeparableExtension L₁ P) (Cor.mk E₁))
variable (h₁ : transfer (finiteSeparableExtension L₁ P) ((Cor.graphFunctor L₁).map
      (SmoothSite.etalePullbackSnd f₁ ((SmoothSite.fieldBaseChange (algebraMap k L₁)).map
        (SmoothSite.etalePullbackFst q₀ (SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj
        V)))) ≫ (SmoothSite.fieldBaseChange (algebraMap k L₁)).map (SmoothSite.etalePullbackSnd q₀
        (SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj V))))) u₁ -
    transfer (finiteSeparableExtension L₁ P) ((Cor.graphFunctor L₁).map
      (SmoothSite.etalePullbackFst f₁ ((SmoothSite.fieldBaseChange (algebraMap k L₁)).map
        (SmoothSite.etalePullbackFst q₀ (SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj
        V)))))) c₁ =
    transfer (finiteSeparableExtension L₁ P) ((Cor.graphFunctor L₁).map
      (SmoothSite.etalePullbackSnd f₁ ((SmoothSite.fieldBaseChange (algebraMap k L₁)).map
        (SmoothSite.etalePullbackFst q₀ (SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj
        V)))) ≫ (SmoothSite.fieldBaseChange (algebraMap k L₁)).map φ₀))
      (transfer P ((Cor.graphFunctor k).map
        (SmoothSite.fieldBaseChangeForgetProjection (L := L₁) ((toSmoothSite
          (SmoothSite.torusCylinder (.of k) X)).obj ((baseChange (SmoothSite.contractionOpen (.of
          k) X).left).obj W)))) s))

variable {E₂ : SmoothSite (Spec (.of L₂))} [IsAffine E₂.left]
variable (f₂ : E₂ ⟶ (SmoothSite.fieldBaseChange (algebraMap k L₂)).obj W₀) [Etale f₂.left]
variable (t₂ : (SmoothSite.fieldBaseChange (algebraMap k L₂)).obj ((toSmoothSite X).obj V) ⟶ E₂)
  (ht₂ : t₂ ≫ f₂ = (SmoothSite.fieldBaseChange (algebraMap k L₂)).map z₀)
variable (u₂ : sections (finiteSeparableExtension L₂ P)
  (Cor.mk ((SmoothSite.fieldBaseChange (algebraMap k L₂)).obj (SmoothSite.torusCylinder (.of k)
    ((toSmoothSite X).obj V)))))
variable (c₂ : sections (finiteSeparableExtension L₂ P) (Cor.mk E₂))
variable (h₂ : transfer (finiteSeparableExtension L₂ P) ((Cor.graphFunctor L₂).map
      (SmoothSite.etalePullbackSnd f₂ ((SmoothSite.fieldBaseChange (algebraMap k L₂)).map
        (SmoothSite.etalePullbackFst q₀ (SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj
        V)))) ≫ (SmoothSite.fieldBaseChange (algebraMap k L₂)).map (SmoothSite.etalePullbackSnd q₀
        (SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj V))))) u₂ -
    transfer (finiteSeparableExtension L₂ P) ((Cor.graphFunctor L₂).map
      (SmoothSite.etalePullbackFst f₂ ((SmoothSite.fieldBaseChange (algebraMap k L₂)).map
        (SmoothSite.etalePullbackFst q₀ (SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj
        V)))))) c₂ =
    transfer (finiteSeparableExtension L₂ P) ((Cor.graphFunctor L₂).map
      (SmoothSite.etalePullbackSnd f₂ ((SmoothSite.fieldBaseChange (algebraMap k L₂)).map
        (SmoothSite.etalePullbackFst q₀ (SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj
        V)))) ≫ (SmoothSite.fieldBaseChange (algebraMap k L₂)).map φ₀))
      (transfer P ((Cor.graphFunctor k).map
        (SmoothSite.fieldBaseChangeForgetProjection (L := L₂) ((toSmoothSite
          (SmoothSite.torusCylinder (.of k) X)).obj ((baseChange (SmoothSite.contractionOpen (.of
          k) X).left).obj W)))) s))

include hz₀ he₀ hv e he d hmark hφ₁ hφ₂ ht₁ ht₂ h₁ h₂ in
/-- The public consumer produces membership in the original canonical image
sieve at the literal supplied zero-base arrow, with no common-refinement input. -/
theorem original_canonical_image_of_actual_affine_corrections
    (hdegree : (Module.finrank k L₁).Coprime (Module.finrank k L₂)) :
    Presheaf.imageSieve (contractionToBoundary X P).hom
      ((presheafBoundaryGenerator ((PresheafWithTransfers.toPresheaf k).obj P)
        (SmoothSite.contractionOpen (.of k) X)
        (SmoothSite.a1Section (.of k) X 0)).app (op W) s) v := by
  exact imageSieve_of_affine_weil_corrections
    (X := X) (P := P) (V := V) (W₀ := W₀) (q₀ := q₀) (z₀ := z₀)
    (hz₀ := hz₀) (e₀ := e₀) (he₀ := he₀) (v := v) (hv := hv)
    (e := e) (he := he) (d := d) (hmark := hmark)
    (φ₀ := φ₀) (hφ₁ := hφ₁) (hφ₂ := hφ₂) (s := s)
    (f₁ := f₁) (t₁ := t₁) (ht₁ := ht₁) (u₁ := u₁) (c₁ := c₁) (h₁ := h₁)
    (f₂ := f₂) (t₂ := t₂) (ht₂ := ht₂) (u₂ := u₂) (c₂ := c₂) (h₂ := h₂) hdegree

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[
    `Motivic.Aglib.AlgebraicGeometry.BaseChange.Affine.ScalarPullback,
    `Motivic.Aglib.AlgebraicGeometry.WeilRestriction.Affine.FiniteFree.Scalar,
    `Motivic.Aglib.AlgebraicGeometry.WeilRestriction.Affine.Witness,
    `Motivic.Aglib.AlgebraicGeometry.WeilRestriction.Affine.ActualPair,
    `Motivic.Aglib.AlgebraicGeometry.BaseChange.Affine.ScalarChart,
    `Motivic.Aglib.AlgebraicGeometry.WeilRestriction.Affine.NativePair,
    `Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.AffineWeilRefinement,
    `Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Affine.WeilRefinement,
    `Motivic.Transfers.Presheaf.RestrictionDifferenceRefinement,
    `Motivic.Transfers.Presheaf.FiniteScalarRefinementDifference,
    `Motivic.Transfers.Presheaf.FiniteScalarEtaleCorrection,
    `Motivic.Cohomology.A1.Boundary.Presheaf.FiniteSeparableDescent,
    `Motivic.Cohomology.A1.Boundary.Presheaf.AffineWeilDescent]
  for source in sourceModules do
    unless env.header.moduleNames.contains source do
      throwError "Missing exact production origin {source}."
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ sourceModules.size do
    throwError "Exact-origin affine boundary declarations are missing."
  for name in declarations do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  let linters ← Lean.Elab.Command.liftCoreM (getChecks true none none)
  unless !linters.isEmpty do
    throwError "No declaration linters selected."
  let results ← Lean.Elab.Command.liftCoreM <|
    Lean.withExporting (isExporting := false) (lintCore declarations linters)
  let mut failed := false
  for (linter, findings) in results do
    for (name, message) in findings.toArray do
      logError m!"{linter.name}: {name}: {message}"
      failed := true
  if failed then
    throwError "Exact-origin declaration lint failed."
  logInfo m!"All {declarations.size} exact-origin declarations: lint and standard axioms passed."

open Lean Mathlib.Linter.TextBased in
run_cmd do
  let options : Lean.Linter.LinterOptions := {
    toOptions := ← getOptions
    linterSets := (Lean.Linter.linterSetsExt.getState (← getEnv)).merged }
  let modules := #[
    `Motivic.Aglib.AlgebraicGeometry.BaseChange.Affine.ScalarPullback,
    `Motivic.Aglib.AlgebraicGeometry.WeilRestriction.Affine.FiniteFree.Scalar,
    `Motivic.Aglib.AlgebraicGeometry.WeilRestriction.Affine.Witness,
    `Motivic.Aglib.AlgebraicGeometry.WeilRestriction.Affine.ActualPair,
    `Motivic.Aglib.AlgebraicGeometry.BaseChange.Affine.ScalarChart,
    `Motivic.Aglib.AlgebraicGeometry.WeilRestriction.Affine.NativePair,
    `Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.AffineWeilRefinement,
    `Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Affine.WeilRefinement,
    `Motivic.Transfers.Presheaf.RestrictionDifferenceRefinement,
    `Motivic.Transfers.Presheaf.FiniteScalarRefinementDifference,
    `Motivic.Transfers.Presheaf.FiniteScalarEtaleCorrection,
    `Motivic.Cohomology.A1.Boundary.Presheaf.FiniteSeparableDescent,
    `Motivic.Cohomology.A1.Boundary.Presheaf.AffineWeilDescent,
    `MotivicTest.AffineWeilBoundaryDescent]
  let errors ← lintModules options #[] modules .humanReadable false
  let casingErrors ← modulesNotUpperCamelCase options modules
  let filenameErrors ← modulesOSForbidden options modules
  unless errors == 0 && casingErrors == 0 && filenameErrors == 0 do
    throwError "Exact-file source text/style checks failed."
  logInfo "Pinned text/style checks passed for all fourteen selected modules."

end MotivicTest.AffineWeilBoundaryDescent
