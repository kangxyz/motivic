/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.SignedPrincipalFaceCoefficient
public import Motivic.AlgebraicGeometry.Correspondences.Endpoints.FinitePoint.Equality

import all Motivic.Aglib.RingTheory.Multiplicity.PrincipalEuler.FaceDifference
import all Motivic.AlgebraicGeometry.Correspondences.Endpoints.FinitePoint.Equality
import all Motivic.Aglib.RingTheory.Multiplicity.PrincipalEuler.Koszul
import all Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.PrincipalFaceCoefficient
import all Motivic.Aglib.RingTheory.Multiplicity.PrincipalEuler.Surjective
import all Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.PrincipalDivisorFaceCoefficient
import all Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.PrincipalDivisorFaceSupport
import all Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.SignedPrincipalFaceCoefficient
public import Lean.Util.CollectAxioms
public import Batteries.Tactic.Lint
public import Mathlib.Tactic.Linter.TextBased

/-!
# Original signed principal face and correspondence endpoint consumers

The geometric consumer retains actual numerator and denominator zero fibers,
nonreduced generic weights, complete reduced-component fibers, and the common
ambient face point. Cancellation uses a literal scalar congruence, not an
assumed cycle equality. The correspondence consumer retains the actual graph
endpoint and original residue-degree collision weights. The global rational
family and principal A1 relation are not asserted here.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry.Scheme (fundamentalCycle)
open _root_.AlgebraicGeometry.Scheme (FiniteSupportCycle IntegralClosedSubscheme IntegralCycle
  SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open AlgebraicGeometry.FiniteFlatCurve
open _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram
open scoped BigOperators Polynomial

universe u

namespace MotivicTest.PrincipalFaceConsumers

section SignedFace

variable {k : Type u} [Field k] {P : Scheme.{u}} [IsNoetherian P]
  (n d f : P ⟶ Spec (.of k[X])) (a : k) (x : fiber f a)

/-- Actual original signed divisor coefficients vanish under the literal face
congruence, including mixed and empty support without chosen fake preimages. -/
theorem original_signed_face_zero
    (hn : PrincipalFaceConditions n f a x) (hd : PrincipalFaceConditions d f a x)
    (hc : IsSMulRegular (P.presheaf.stalk (fiberInclusion f a x))
      (scalar f a (fiberInclusion f a x)))
    (hnr : IsSMulRegular (P.presheaf.stalk (fiberInclusion f a x))
      (scalar n 0 (fiberInclusion f a x)))
    (hdr : IsSMulRegular (P.presheaf.stalk (fiberInclusion f a x))
      (scalar d 0 (fiberInclusion f a x)))
    (r : P.presheaf.stalk (fiberInclusion f a x))
    (hrelation : scalar n 0 (fiberInclusion f a x) =
      scalar d 0 (fiberInclusion f a x) + scalar f a (fiberInclusion f a x) * r) :
    IntegralCycle.toPoints
        (principalDivisorFaceCycle n f a - principalDivisorFaceCycle d f a)
        (fiberInclusion f a x) = 0 := by
  exact signed_principal_face_coefficient_eq_zero n d f a x hn hd hc hnr hdr r hrelation

end SignedFace

section Correspondence

open FinitePointCycleCorrespondence

variable {k : Type u} [Field k] (X Y : SmoothSite (Spec (.of k)))
  {C V : Scheme.{u}} (q : C ⟶ relativeLine X.hom) (j : V ⟶ C) [IsOpenImmersion j]
  (c : FiniteSupportCycle C)
  (hretained : ∀ x : c.support,
    Set.range (IntegralClosedSubscheme.pointClosure x.val).val.subschemeι ⊆ Set.range j)
  (hfinite : ∀ x : c.support,
    IsFinite ((IntegralClosedSubscheme.pointClosure x.val).val.subschemeι ≫ q))
  (hdominant : ∀ x : c.support,
    Set.range ((IntegralClosedSubscheme.pointClosure x.val).val.subschemeι ≫ q) ∈
      irreducibleComponents (relativeLine X.hom))
  (g : V ⟶ Y.left) (hbase : j ≫ q ≫ relativeLineHom X.hom = g ≫ Y.hom)

local instance : IsNoetherian ((𝟭 Scheme).obj X.left) :=
  inferInstanceAs (IsNoetherian X.left)

/-- The actual original graph endpoint retains full generator fibers and
all signed residue-degree collision contributions, without family flatness. -/
theorem original_graph_endpoint_cycle (a : k) :
    FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Y.hom)
      ((Cor.graphFunctor k).map (endpointMorphism X a) ≫
        correspondence (X := relativeLineSite X) q j c hretained hfinite hdominant g hbase) =
      ∑ x : c.support,
        (c x.val * ((productMap (X := relativeLineSite X) q j c hretained g hbase x).residueDegree
          (genericPoint (supportScheme c x)) : ℤ)) •
        IntegralCycle.finitePushforward
          ((generator (X := relativeLineSite X) q j c hretained hfinite hdominant
            g hbase x).graphPullbackMap (endpoint X.hom a) (endpoint_base X.hom a))
          (fundamentalCycle
            ((generator (X := relativeLineSite X) q j c hretained hfinite hdominant
              g hbase x).graphPullback (endpoint X.hom a))) := by
  exact FinitePointCycleCorrespondence.toIntegralCycle_graph_endpoint
    X Y q j c hretained hfinite hdominant g hbase a

end Correspondence

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[
    `Motivic.Aglib.RingTheory.Multiplicity.PrincipalEuler.FaceDifference,
    `Motivic.AlgebraicGeometry.Correspondences.Endpoints.FinitePoint.Equality,
    `Motivic.Aglib.RingTheory.Multiplicity.PrincipalEuler.Koszul,
    `Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.PrincipalFaceCoefficient,
    `Motivic.Aglib.RingTheory.Multiplicity.PrincipalEuler.Surjective,
    `Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.PrincipalDivisorFaceCoefficient,
    `Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.PrincipalDivisorFaceSupport,
    `Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.SignedPrincipalFaceCoefficient]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ 25 do
    throwError "Exact-origin original signed face declarations are missing."
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
    `Motivic.Aglib.RingTheory.Multiplicity.PrincipalEuler.FaceDifference,
    `Motivic.AlgebraicGeometry.Correspondences.Endpoints.FinitePoint.Equality,
    `Motivic.Aglib.RingTheory.Multiplicity.PrincipalEuler.Koszul,
    `Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.PrincipalFaceCoefficient,
    `Motivic.Aglib.RingTheory.Multiplicity.PrincipalEuler.Surjective,
    `Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.PrincipalDivisorFaceCoefficient,
    `Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.PrincipalDivisorFaceSupport,
    `Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.SignedPrincipalFaceCoefficient,
    `MotivicTest.PrincipalFaceConsumers]
  let errors ← lintModules options #[] modules .humanReadable false
  let casingErrors ← modulesNotUpperCamelCase options modules
  let filenameErrors ← modulesOSForbidden options modules
  unless errors == 0 && casingErrors == 0 && filenameErrors == 0 do
    throwError "Exact-file source text/style checks failed."
  logInfo "Pinned text/style checks passed for all nine selected modules."


end MotivicTest.PrincipalFaceConsumers
