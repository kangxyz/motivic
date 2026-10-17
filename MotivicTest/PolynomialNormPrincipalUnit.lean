/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK3.PolynomialNormPrincipalUnit
import Lean.Util.CollectAxioms

/-!
# Principal-unit polynomial norm consumers and standard-foundation audit

The complete-DVR consumer supplies only an actual complete DVR, residue
characteristic zero, the original monic irreducible polynomial, an arbitrary
source-field unit, and a principal unit in the actual integral closure. No
norm/tame compatibility or upstairs vanishing is among its inputs.
-/

noncomputable section

namespace MotivicTest.PolynomialNormPrincipalUnit

open Polynomial Polynomial.LocalResidue IsLocalRing
open Motivic.KTheory.MilnorK2 Motivic.KTheory.MilnorK2.DVR
open Motivic.KTheory.MilnorK3.PolynomialResidue
open Motivic.KTheory.MilnorK3.PolynomialNorm
open Motivic

/-- The original polynomial norm target is the original integer tensor quotient. -/
theorem original_K2_target (K : Type*) [Field K] :
    K2 K = (TensorProduct ℤ (Additive Kˣ) (Additive Kˣ) ⧸ steinbergSpan K) := rfl

section PrincipalNorm

variable {R B S K L : Type*}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [HenselianLocalRing B]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra S L] [IsFractionRing S L]
  [CharZero (ResidueField B)]
  (j : R →+* S) [IsLocalHom j] (F : K →+* L)
  (hF : ∀ r : R, F (algebraMap R K r) = algebraMap S L (j r))
  (p : MonicIrreducible K) (hp : (p.val.map F).Splits)
  [Algebra B (AdjoinRoot p.val)] [IsFractionRing B (AdjoinRoot p.val)]
  (β : ∀ _q : {q // q ∈ placesAbove F p}, B →+* S)
  [∀ _q, IsLocalHom (β _q)]
  (hβ : ∀ (q : {q // q ∈ placesAbove F p}) (r : B),
    splitBranchMap F p hp q (algebraMap B (AdjoinRoot p.val) r) =
      algebraMap S L (β q r))
  {πR : R} {πS : S} (hπR : Irreducible πR) (hπS : Irreducible πS)
  (u : Sˣ) (e : ℕ) (hπ : j πR = (u : S) * πS ^ e)
  [Algebra (ResidueField R) (ResidueField S)]
  [FiniteDimensional (ResidueField R) (ResidueField S)]
  [Algebra.IsSeparable (ResidueField R) (ResidueField S)]
  (hκ : algebraMap (ResidueField R) (ResidueField S) = ResidueField.map j)

include hF hβ hπ hκ hπS

omit [IsFractionRing B (AdjoinRoot p.val)] in
/-- The consumer keeps every concrete local map and literal compatibility equation. -/
theorem actual_concrete_DVR_vanishing
    (b : (AdjoinRoot p.val)ˣ) (h : Bˣ) (hh : residue B (h : B) = 1) :
    tame (data (K := K) hπR)
        (polynomialNorm p (symbol b (fieldUnits B (AdjoinRoot p.val) h))) = 0 ∧
      specialize (data (K := K) hπR) (unitReductionCompatible hπR)
        (polynomialNorm p (symbol b (fieldUnits B (AdjoinRoot p.val) h))) = 0 :=
  polynomialNorm_principal_unit_joint_vanish j F hF p hp β hβ hπR hπS u e hπ hκ b h hh

end PrincipalNorm

section CompleteDVR

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [CharZero (ResidueField R)]

/-- Principal-unit polynomial norms over a complete DVR. The source DVR is the
actual integral closure of `R` in the original `AdjoinRoot p`. The splitting
field, its integral-closure DVR, all local branch maps, finite residue degree,
and positive ramification are constructed in the proof. Both field algebras
are the canonical scalar extensions, so no compatibility input is supplied. -/
theorem actual_complete_DVR_vanishing
    (p : MonicIrreducible K)
    {πR : R} (hπR : Irreducible πR)
    (b : (AdjoinRoot p.val)ˣ) (h : (integralClosure R (AdjoinRoot p.val))ˣ) :
    let _ : CharZero R := RingHom.charZero (residue R)
    let _ : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective R K)
    let _ := (AdjoinRoot.powerBasis p.property.2.ne_zero).finite
    let _ := CompleteDVRExtension.integralClosure_isDiscreteValuationRing R K (AdjoinRoot p.val)
    residue (integralClosure R (AdjoinRoot p.val)) (h : integralClosure R (AdjoinRoot p.val)) = 1 →
      tame (data (K := K) hπR)
          (polynomialNorm p (symbol b (fieldUnits (integralClosure R (AdjoinRoot p.val))
            (AdjoinRoot p.val) h))) = 0 ∧
        specialize (data (K := K) hπR) (unitReductionCompatible hπR)
          (polynomialNorm p (symbol b (fieldUnits (integralClosure R (AdjoinRoot p.val))
            (AdjoinRoot p.val) h))) = 0 :=
  polynomialNorm_principal_unit_completeDVR p hπR b h

end CompleteDVR

end MotivicTest.PolynomialNormPrincipalUnit

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "The principal-unit norm audit requires legacy imports for private helpers"
  let prefixes := #[`Motivic.KTheory.MilnorK2, `Motivic.KTheory.MilnorK3,
    `Motivic.HenselianPrincipalRoots, `Motivic.CompleteDVRExtension,
    `MotivicTest.PolynomialNormPrincipalUnit]
  let isLibrary (name : Name) : Bool := prefixes.any (·.isPrefixOf name)
  let selected (name : Name) : Bool :=
    let origin := match env.getModuleIdxFor? name with
      | some index => isLibrary env.header.moduleNames[index.toNat]!
      | none => false
    origin || isLibrary name
  let mut names : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    let origin := isLibrary env.header.moduleNames[i]!
    for name in env.header.moduleData[i]!.constNames do
      if origin || selected name then names := names.insert name
  names := env.constants.foldStage2 (fun names name _ =>
    if selected name then names.insert name else names) names
  let mut count : Nat := 0
  for name in names.toArray do
    unless (env.checked.get.find? name).isSome do
      throwError "Principal-unit norm declaration {name} is absent from the kernel environment"
    count := count + 1
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Audited {count} original Milnor K₂/K₃, principal-unit Hensel lifting, complete \
    integral-closure, and principal-unit norm declarations: only standard Lean logical foundations."
