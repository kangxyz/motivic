/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK.FiniteExtensionNormRationalResidue
import Lean.Util.CollectAxioms

/-! Direct consumers of the general finite-place norm square on the actual
fields, with the entire original residue-field branch sum displayed. -/

open Polynomial Polynomial.LocalResidue AdjoinRoot
open Motivic.KTheory MilnorK PolynomialResidue
open scoped RatFunc

attribute [local instance] Polynomial.algebra AdjoinRoot.scalarBranchAlgebra
  MilnorK.residueRootFinite MilnorK.residueRootCharZero MilnorK.primeRationalFinite

namespace MotivicTest.GeneralMilnorFiniteExtensionNormRationalResidue

universe u

/-- Every finite coefficient field, finite place, Milnor degree, and original
quotient class is admitted, without normality or a supplied residue square. -/
theorem actual_arbitrary_finite_square
    {k : Type u} [Field k] [CharZero k] (E : Type u) [Field E]
    [Algebra k E] [FiniteDimensional k E] (h : MonicIrreducible k)
    (n : ℕ) (x : K (RatFunc E) (n + 1)) :
    residueAt h.val n (finiteExtensionNorm (RatFunc k) (RatFunc E) (n + 1) x) =
      rationalResidueNormSum k E h n x :=
  residueAt_finiteExtensionNorm_rational E h n x

open scoped Classical in
/-- Expanded complete branch formula: each summand is the actual finite norm
of the original residue-field extension, with its literal coefficient action. -/
theorem original_full_residue_norm_sum
    {k : Type u} [Field k] [CharZero k] (E : Type u) [Field E]
    [Algebra k E] [FiniteDimensional k E] (h : MonicIrreducible k)
    (n : ℕ) (x : K (RatFunc E) (n + 1)) :
    letI : Finite (IrreducibleBranch (h.val.map (algebraMap k E))) :=
      finite_irreducibleBranch _ (h.property.1.map _)
    letI : Fintype (IrreducibleBranch (h.val.map (algebraMap k E))) := Fintype.ofFinite _
    residueAt h.val n (finiteExtensionNorm (RatFunc k) (RatFunc E) (n + 1) x) =
      ∑ r : IrreducibleBranch (h.val.map (algebraMap k E)),
        letI : FiniteDimensional (AdjoinRoot h.val) (AdjoinRoot r.val.val) :=
          finiteDimensional_scalarBranch_residue h r
        finiteExtensionNorm (AdjoinRoot h.val) (AdjoinRoot r.val.val) n
          (residueAt r.val.val n x) :=
  residueAt_finiteExtensionNorm_rational E h n x

/-- The complete actual residue sum is independent of the coefficient-field
presentation by the explicitly proved literal coefficient transport. -/
theorem original_sum_coefficient_equivalence
    {k A B : Type u} [Field k] [CharZero k] [Field A] [Field B]
    [Algebra k A] [Algebra k B] [FiniteDimensional k A] [FiniteDimensional k B]
    (φ : A ≃ₐ[k] B) (h : MonicIrreducible k) (n : ℕ)
    (x : K (RatFunc A) (n + 1)) :
    rationalResidueNormSum k B h n (map (n + 1) (fractionMap φ.toRingHom) x) =
      rationalResidueNormSum k A h n x :=
  rationalResidueNormSum_map_algEquiv φ h n x

end MotivicTest.GeneralMilnorFiniteExtensionNormRationalResidue

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`AdjoinRoot, `Polynomial.LocalResidue, `Motivic.KTheory.MilnorK,
    `MotivicTest.GeneralMilnorFiniteExtensionNormRationalResidue]
  let selected (name : Name) := prefixes.any (·.isPrefixOf name)
  let mut names : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    if selected env.header.moduleNames[i]! then
      for name in env.header.moduleData[i]!.constNames do
        names := names.insert name
  names := env.constants.foldStage2 (fun names name _ =>
    if selected name then names.insert name else names) names
  for name in names.toArray do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Checked {names.size} actual finite rational residue norm declarations: \
    standard axioms only."
