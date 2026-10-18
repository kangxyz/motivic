/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors, kangxyz
-/

import Motivic
import MotivicTest
import Lean.Util.CollectAxioms
/-! Adapted from the public Quillen 0.5.0 audit at commit
4444574cd12bdaab888bd65c79ffba79ce0640ce.

Audit every project-origin kernel declaration, including private helpers, and
every Motivic-namespaced declaration. Imported module name inventories avoid
forcing unrelated ConstantInfo values. The exact defining-origin predicate is
rechecked after deduplication, and local stage-2 declarations are included.
Transitive axiom collection and the allowed foundations are unchanged. -/

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "Exhaustive axiom audit requires legacy (.private) transitive imports"
  let migratedHelpers := #[
    `Aglib.AlgebraicGeometry.DedekindPointStalk,
    `Aglib.FieldTheory.AdjoinRootMinpolyDegree,
    `Aglib.FieldTheory.AdjoinRootNormalScalarBranch,
    `Aglib.FieldTheory.AdjoinRootSplitBranchEmbedding,
    `Aglib.FieldTheory.CoprimeIrreducibility,
    `Aglib.FieldTheory.FieldCharpolyPower,
    `Aglib.FieldTheory.FiniteCoprimeSplitting,
    `Aglib.FieldTheory.PGroupNormalSubfield,
    `Aglib.FieldTheory.PGroupNormalSubfieldEmbedding,
    `Aglib.FieldTheory.PrimeNormalScalarDichotomy,
    `Aglib.FieldTheory.RatFuncCoefficientEquiv,
    `Aglib.FieldTheory.RatFuncCoefficientMap,
    `Aglib.FieldTheory.RatFuncInversion,
    `Aglib.FieldTheory.RatFuncReverse,
    `Aglib.FieldTheory.RatFuncTranslation,
    `Aglib.FieldTheory.RationalCoefficientRoot,
    `Aglib.FieldTheory.ResidueMinpolyBranch,
    `Aglib.FieldTheory.SylowFixedField,
    `Aglib.FieldTheory.TensorCharpolyProduct,
    `Aglib.RingTheory.AdicCompletion.BranchBaseLocal,
    `Aglib.RingTheory.AdicCompletion.BranchFractionAlgebra,
    `Aglib.RingTheory.AdicCompletion.BranchFractionFinite,
    `Aglib.RingTheory.AdicCompletion.BranchUniformizer,
    `Aglib.RingTheory.AdicCompletion.ChineseRemainder,
    `Aglib.RingTheory.AdicCompletion.DedekindBranches,
    `Aglib.RingTheory.AdicCompletion.FiniteAlgebra,
    `Aglib.RingTheory.AdicCompletion.FiniteDedekindBranches,
    `Aglib.RingTheory.AdicCompletion.FractionBaseChange,
    `Aglib.RingTheory.AdicCompletion.FractionBranches,
    `Aglib.RingTheory.AdicCompletion.FractionTensorBranches,
    `Aglib.RingTheory.AdicCompletion.LocalCompletionsBase,
    `Aglib.RingTheory.AdicCompletion.Localization,
    `Aglib.RingTheory.AdicCompletion.OriginalBranchFractions,
    `Aglib.RingTheory.AdicCompletion.OriginalBranchResidues,
    `Aglib.RingTheory.AdicCompletion.Powers,
    `Aglib.RingTheory.AdicCompletion.ScalarExtension,
    `Aglib.RingTheory.AdicCompletion.SemilocalBranches,
    `Aglib.RingTheory.AdjoinRootBalancedFractions,
    `Aglib.RingTheory.AdjoinRootBranchProduct,
    `Aglib.RingTheory.AdjoinRootCoefficientEquiv,
    `Aglib.RingTheory.AdjoinRootCoefficientTowerBranches,
    `Aglib.RingTheory.AdjoinRootFieldProductBranches,
    `Aglib.RingTheory.AdjoinRootNestedBaseChange,
    `Aglib.RingTheory.AdjoinRootNestedBranches,
    `Aglib.RingTheory.AdjoinRootNormEvaluation,
    `Aglib.RingTheory.AdjoinRootNormResultant,
    `Aglib.RingTheory.AdjoinRootNormRoot,
    `Aglib.RingTheory.AdjoinRootPiBranches,
    `Aglib.RingTheory.AdjoinRootScalarBranchCoefficientEquiv,
    `Aglib.RingTheory.AdjoinRootScalarBranches,
    `Aglib.RingTheory.AdjoinRootTensorBranchProduct,
    `Aglib.RingTheory.AdjoinRootTensorBranches,
    `Aglib.RingTheory.AdjoinRootTowerBranch,
    `Aglib.RingTheory.AdjoinRootTowerBranchChange,
    `Aglib.RingTheory.CompleteDVRExtension,
    `Aglib.RingTheory.CompleteDVRIntegralClosureTower,
    `Aglib.RingTheory.DVRCartierLength,
    `Aglib.RingTheory.DVRCharpolyBranchCount,
    `Aglib.RingTheory.DVRCharpolyResidue,
    `Aglib.RingTheory.DVRNormResidueUnit,
    `Aglib.RingTheory.DVRNormValuation,
    `Aglib.RingTheory.DVRPrimeUniformizerNorm,
    `Aglib.RingTheory.DVRRamificationDegree,
    `Aglib.RingTheory.DVRUniformizerBinomial,
    `Aglib.RingTheory.DVRUniformizerNorm,
    `Aglib.RingTheory.DiscreteValuationRing.FractionAway,
    `Aglib.RingTheory.DiscreteValuationRing.FractionBaseChange,
    `Aglib.RingTheory.DiscreteValuationRing.FractionPi,
    `Aglib.RingTheory.DiscreteValuationRing.IntegralFractionAway,
    `Aglib.RingTheory.FiniteAlgebraNormLength,
    `Aglib.RingTheory.FiniteLength.FiniteAlgebraFiber,
    `Aglib.RingTheory.FiniteLength.FiniteAlgebraLength,
    `Aglib.RingTheory.FiniteLocalResidue,
    `Aglib.RingTheory.FiniteTypeLocalResidue,
    `Aglib.RingTheory.HenselianPrincipalRoots,
    `Aglib.RingTheory.HenselianUniformizerNormalization,
    `Aglib.RingTheory.IntegralTensorCharpolyProduct,
    `Aglib.RingTheory.IntermediateIntegralClosureTower,
    `Aglib.RingTheory.LocalizedDedekindBranches,
    `Aglib.RingTheory.LocalizedDedekindFractions,
    `Aglib.RingTheory.LocalizedPrimeBranches,
    `Aglib.RingTheory.Multiplicity.PrincipalEuler.Additivity,
    `Aglib.RingTheory.Multiplicity.PrincipalEuler.Basic,
    `Aglib.RingTheory.Multiplicity.PrincipalEuler.Filtration,
    `Aglib.RingTheory.Multiplicity.PrincipalEuler.Support,
    `Aglib.RingTheory.PolynomialFiberNorm,
    `Aglib.RingTheory.PolynomialLocalResidue,
    `Aglib.RingTheory.PolynomialPlaceContraction,
    `Aglib.RingTheory.PolynomialPowerFactorCount,
    `Aglib.RingTheory.PolynomialResidueBaseChange,
    `Aglib.RingTheory.PowerSeriesConstantClosure,
    `Aglib.RingTheory.PrimeFiltration.Basic,
    `Aglib.RingTheory.PrimeFiltration.Multiplicity]
  let projectModuleName (moduleName : Name) : Bool :=
    (`Motivic).isPrefixOf moduleName || (`MotivicTest).isPrefixOf moduleName ||
      (`Aglib.KTheory.MilnorK).isPrefixOf moduleName || migratedHelpers.contains moduleName
  let selected (name : Name) : Bool :=
    let projectModule := match env.getModuleIdxFor? name with
      | some index => projectModuleName env.header.moduleNames[index.toNat]!
      | none => false
    projectModule || (`Motivic).isPrefixOf name || (`MilnorK).isPrefixOf name
  let mut names : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    let projectModule := projectModuleName env.header.moduleNames[i]!
    for name in env.header.moduleData[i]!.constNames do
      if projectModule || (`Motivic).isPrefixOf name || (`MilnorK).isPrefixOf name then
        names := names.insert name
  names := env.constants.foldStage2 (fun names name _ =>
    if selected name then names.insert name else names) names
  let mut count : Nat := 0
  for name in names.toArray do
    if selected name then
      unless (env.checked.get.find? name).isSome do
        throwError
          "Selected audit declaration {name} is missing from the checked kernel environment"
      count := count + 1
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{name} depends on unsupported assumption {dependency}"
  logInfo
    m!"Audited {count} project declarations (including private helpers): \
      only standard Lean logical foundations."
