/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic
public import MotivicTest.Cohomology.SheafCohomologyH1SquareDescent
public import MotivicTest.NisnevichPointControlledCechKernel
public import MotivicTest.Cohomology.SheafCohomologyH1Descent
public import MotivicTest.ArbitraryPointGermLocality
public import MotivicTest.RelativeFiniteFlatSpanEndpoints
public import MotivicTest.RelativeCartierBaseEndpoints
public import MotivicTest.NisnevichCechPointPairing
public import MotivicTest.NisnevichCechIncidencePointPairing
public import MotivicTest.NisnevichCechLocalPointControl
public import MotivicTest.NisnevichPointChosenGeneratorLift
public import MotivicTest.RelativeFiniteFlatSpecialization
public import MotivicTest.Cohomology.SheafCohomologyLocalTriviality
public import MotivicTest.FixedLiftGermIndependence
public import MotivicTest.RelativeEndpointIncidenceCycle
public import MotivicTest.RelativeEndpointIncidenceTor
public import MotivicTest.RelativeEndpointComponentTor
public import MotivicTest.RelativeEndpointStalkTor
public import MotivicTest.GlobalIncidenceAmbientTorComparison
public import MotivicTest.SupportLiftImageSumControl
public import MotivicTest.SupportLiftImageControl
public import MotivicTest.SmoothSiteNisnevichPointRefinement
public import MotivicTest.NisnevichPointNormalizedLift
public import MotivicTest.NisnevichFamilySupportLift
public import MotivicTest.Cohomology.CurveEndpointActions
public import MotivicTest.Cohomology.SheafCohomologyHenselianEvaluation
public import MotivicTest.SmoothSiteNisnevichPointNormalization
public import MotivicTest.SmoothSiteNisnevichPointSections
public import MotivicTest.FiniteSupportGermLocality
public import MotivicTest.Cohomology.RelativeSheafCohomologyNaturality
public import MotivicTest.Cohomology.ContractionRelativeNaturality
public import MotivicTest.Cohomology.SheafCohomologyFieldEvaluation
public import MotivicTest.FlatPolynomialComponentRegularity
public import MotivicTest.GraphPolynomialTor
public import MotivicTest.Cohomology.ContractionRelative
public import MotivicTest.NisnevichPointCechKernel
public import MotivicTest.FiniteFlatSpanForgottenEndpoints
public import MotivicTest.NisnevichPointGeneratorLift
public import MotivicTest.SmoothSiteNisnevichPointLifting
public import MotivicTest.Cohomology.RelativeSheafCohomology
public import MotivicTest.Cohomology.FreeSheafMonomorphisms
public import MotivicTest.SmoothSiteNisnevichPoint
public import MotivicTest.FiniteFlatSpanEndpoints
public import MotivicTest.AlgebraicGeometry.SmoothSiteParameterProducts
public import MotivicTest.Transfers.ContractionSheaf
public import MotivicTest.SkyscraperCohomology
public import MotivicTest.AlgebraicGeometry.FiniteNeighborhoodLineBundle
public import MotivicTest.Cohomology.A1DegreeZero
public import MotivicTest.TransferContractionInvariance
public import MotivicTest.Transfers.EnoughInjectives
public import MotivicTest.AlgebraicGeometry.SemilocalLineBundle
public import MotivicTest.TransferContraction
public import MotivicTest.Transfers.DegreeZeroNaturality
public import MotivicTest.DiagonalPolynomialNormComparison
public import MotivicTest.Transfers.DegreeZeroTransfers
public import MotivicTest.Cohomology.A1
public import MotivicTest.Transfers.SheafExactness
public import MotivicTest.FiniteFlatCorrespondence
public import MotivicTest.RelativeCartierDivisor
public import MotivicTest.GenericDominance
public import MotivicTest.DiagonalWeightZero
public import MotivicTest.DiagonalCorestrictionTower
public import MotivicTest.DiagonalCorestriction
public import MotivicTest.DiagonalTopDegree
public import MotivicTest.DiagonalCycleSymbols
public import MotivicTest.DiagonalCoordinateInsertion
public import MotivicTest.DiagonalMilnorSymbol
public import MotivicTest.DiagonalFieldChange
public import MotivicTest.FiniteCurveBranchOrders
public import MotivicTest.FiniteCurveNormalization
public import MotivicTest.WeightTwoCoordinateCycleEvaluation
public import MotivicTest.WeightTwoCoordinateEvaluation
public import MotivicTest.WeightTwoMilnorSurjective
public import MotivicTest.WeightTwoMilnorNormComparison
public import MotivicTest.WeightTwoPointPresentation
public import MotivicTest.WeightTwoMonicDeformationNormSum
public import MotivicTest.WeightTwoMonicDeformationFactors
public import MotivicTest.WeightTwoMonicDeformationTransfer
public import MotivicTest.AdjoinRootFactorLength
public import MotivicTest.WeightTwoMonicDeformation
public import MotivicTest.TwoUnitMonicDeformation
public import MotivicTest.WeightTwoCorestrictionBaseChange
public import MotivicTest.WeightTwoScalarPairChange
public import MotivicTest.FinitePointBaseChange
public import MotivicTest.AdjoinRootScalarBranchesGeometry
public import MotivicTest.WeightTwoMilnorMixedNorm
public import MotivicTest.WeightTwoMilnorRootNorm
public import MotivicTest.CorIntegration
public import MotivicTest.LaurentTorus
public import MotivicTest.SmoothSiteTorus
public import MotivicTest.SimplexExteriorGraph
public import MotivicTest.ReducedTransferTorus
public import MotivicTest.TransferSingularComplex
public import MotivicTest.TransferSheafifiedSingularComplex
public import MotivicTest.MotivicComplex
public import MotivicTest.SmoothSiteNisnevichEvaluation
public import MotivicTest.MotivicHypercohomology
public import MotivicTest.MotivicFieldCycleEvaluation
public import MotivicTest.MotivicFiniteCoefficients
public import MotivicTest.MotivicFiniteHypercohomology
public import MotivicTest.TransferSingularNormalization
public import MotivicTest.FlatTorsionFreeMinimalPrimes
public import MotivicTest.FlatBaseChangeGeneric
public import MotivicTest.FieldBaseChangeSupport
public import MotivicTest.FieldBaseChangeCycle
public import MotivicTest.FieldBaseChangeGraph
public import MotivicTest.ClosedImmersionKoszulEuler
public import MotivicTest.FlatFundamentalCycle
public import MotivicTest.SmoothSiteBaseChangeProducts
public import MotivicTest.SmoothSiteSimplexBaseChange
public import MotivicTest.SmoothSiteTorusBaseChange

public import MotivicTest.BaseFieldGenerators

public import MotivicTest.WeightOnePointNorm


public import MotivicTest.FieldBaseChangePushforward

public import MotivicTest.FieldBaseChangeIncidence

public import MotivicTest.SmoothSiteDiagonalBaseChange
public import MotivicTest.FlatLeftGraphComposition

public import MotivicTest.FieldBaseChangeIncidenceCycle
public import MotivicTest.FieldBaseChangeIncidenceTor
public import MotivicTest.FieldBaseChangeCompositionPushforward
public import MotivicTest.FieldBaseChangeComposition
public import MotivicTest.WeightOneFundamentalNorm
public import MotivicTest.MonicUnitInterpolation
public import MotivicTest.WeightOneBoundaryNorm
public import MotivicTest.WeightOneHomologyNorm
public import MotivicTest.FiniteFlatCurveComponents
public import MotivicTest.CartierCutLength
public import MotivicTest.RawFieldChangeCoherence

public import MotivicTest.CorrespondenceIsoTransport
public import MotivicTest.ScalarExtensionEndpointFiber
public import MotivicTest.ScalarExtensionSimplexEndpoint
public import MotivicTest.WeightTwoCorestriction
public import MotivicTest.WeightTwoCorestrictionSupport
public import MotivicTest.WeightTwoCorestrictionBoundary
public import MotivicTest.WeightTwoCorestrictionHomology
public import MotivicTest.WeightTwoCorestrictionMixed
public import MotivicTest.WeightTwoCorestrictionDegree

public import MotivicTest.WeightTwoCorestrictionFinite

public import MotivicTest.AdjoinRootSimpleFactorLocalization
public import MotivicTest.AdjoinRootBranchDimension
public import MotivicTest.WeightTwoPolynomialTransfer
public import MotivicTest.WeightTwoSplitPolynomialCycle
public import MotivicTest.WeightTwoSteinbergTorsion
public import MotivicTest.WeightTwoSteinbergBound
public import MotivicTest.WeightTwoSteinberg

public import MotivicTest.WeightTwoMilnorSymbol
public import MotivicTest.WeightTwoCorestrictionTower


/-! # Public integration of actual motivic complexes and derived cohomology -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Motivic

universe u

namespace MotivicTest.MotivicIntegration

variable (k : Type u) [Field k]

/-- The public root exposes the actual all-degree complex over an arbitrary field. -/
def canonical (q : ℕ) : CochainComplex (SheafWithTransfers.{u + 1} k) ℤ :=
  motivicComplex k q

/-- The public definition is literally the signed shift of the actual reduced-torus complex. -/
example (q : ℕ) : canonical k q =
    (PresheafWithTransfers.singularSheafCochainComplex k
      (PresheafWithTransfers.reducedTorus k q) 0)⟦-(q : ℤ)⟧ := rfl

/-- Cohomology uses the available standard large derived category, not a smallness premise. -/
def derivedGroups (p : ℤ) (q : ℕ) (X : SmoothSite (Spec (.of k))) :=
  letI := HasDerivedCategory.standard
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
  AddCommGrpCat.of (motivicCohomology k p q X)

/-- Evaluation at the field is proved from the actual derived definition. -/
def fieldComparison (p : ℤ) (q : ℕ) :=
  letI := HasDerivedCategory.standard
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
  motivicBaseEvaluationComparison k p q

/-- The derived field group is computed by the literal shifted reduced-cycle complex. -/
def cycleComparison (p : ℤ) (q : ℕ) :=
  letI := HasDerivedCategory.standard
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
  motivicRawBaseEvaluationComparison k p q

/-- Negative cochain degrees are retained in the full complex. -/
example : (canonical k 2).X (-4) ≅
    (PresheafWithTransfers.nisnevichSheafify k).obj
      ((PresheafWithTransfers.singularComplex
        (PresheafWithTransfers.reducedTorus k 2)).X 6) :=
  motivicComplexXIso k 2 6

/-- Finite coefficients retain actual transfers and use the canonical integral complex. -/
def finiteCoefficients (q n : ℕ) : CochainComplex (SheafWithTransfers.{u + 1} k) ℤ :=
  motivicFiniteComplex k q n

/-- Finite derived motivic groups use the same actual standard large derived category. -/
def finiteDerivedGroups (p : ℤ) (q n : ℕ) (X : SmoothSite (Spec (.of k))) :=
  letI := HasDerivedCategory.standard
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
  AddCommGrpCat.of (motivicFiniteCohomology k p q n X)

/-- The public positive field Bockstein retains the proved cone comparison. -/
def fieldBockstein (p : ℤ) (q n : ℕ) :=
  letI := HasDerivedCategory.standard
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
  motivicBaseBockstein k p q n

/-- Moore normalization is an actual homotopy equivalence to the signed motivic complex. -/
def normalizedCanonical (q : ℕ) :
    HomotopyEquiv
      ((PresheafWithTransfers.normalizedSingularSheafCochainComplex
        (PresheafWithTransfers.reducedTorus k q) 0)⟦-(q : ℤ)⟧)
      (motivicComplex k q) :=
  PresheafWithTransfers.singularSheafShiftedNormalizationHomotopyEquiv
    (PresheafWithTransfers.reducedTorus k q) q

/-- Arbitrary field maps act on all signed correspondences with whole-support lengths. -/
def signedFieldChange {L : Type u} [Field L] (φ : k →+* L)
    (X Y : SmoothSite.overField k) :
    FiniteCorrespondence X.hom Y.hom →+
      FiniteCorrespondence ((SmoothSite.fieldBaseChange φ).obj X).hom
        ((SmoothSite.fieldBaseChange φ).obj Y).hom :=
  FiniteCorrespondence.fieldBaseChange φ

/-- The actual graph morphisms agree, including all components of the new source. -/
theorem signedFieldChange_graph {L : Type u} [Field L] (φ : k →+* L)
    {X Y : SmoothSite.overField k} (f : X ⟶ Y) :
    signedFieldChange k φ X Y ((Cor.graphFunctor k).map f) =
      (Cor.graphFunctor L).map ((SmoothSite.fieldBaseChange φ).map f) :=
  FiniteCorrespondence.fieldBaseChange_componentGraphCycleOver φ f

/-- Arbitrary field maps give an actual additive correspondence functor. -/
def correspondenceFieldFunctor {L : Type u} [Field L] (φ : k →+* L) : Cor k ⥤+ Cor L :=
  Cor.fieldBaseChangeAdditiveFunctor φ

/-- The public functor preserves the actual signed composition operation. -/
theorem correspondenceFieldFunctor_comp {L : Type u} [Field L] (φ : k →+* L)
    {X Y Z : Cor k} (α : X ⟶ Y) (β : Y ⟶ Z) :
    (Cor.fieldBaseChange φ).map (α ≫ β) =
      (Cor.fieldBaseChange φ).map α ≫ (Cor.fieldBaseChange φ).map β :=
  (Cor.fieldBaseChange φ).map_comp α β

/-- Every simplex operator commutes with the actual arbitrary-field parameter comparison. -/
def simplexFieldComparison {L : Type u} [Field L] (φ : k →+* L) :
    AlgebraicSimplex.cosimplicialSmoothSite k ⋙ SmoothSite.fieldBaseChange φ ≅
      AlgebraicSimplex.cosimplicialSmoothSite L :=
  AlgebraicSimplex.cosimplicialFieldBaseChangeIso φ

/-- All torus powers use the literal new-field scheme, without a finite-type extension premise. -/
def torusFieldComparison {L : Type u} [Field L] (φ : k →+* L) (q : ℕ) :
    (SmoothSite.fieldBaseChange φ).obj (SmoothSite.torusPower (CommRingCat.of k) q) ≅
      SmoothSite.torusPower (CommRingCat.of L) q :=
  SmoothSite.torusPowerFieldBaseChangeIso φ q

/-- The public reduced weight-one point norm uses the actual cokernel sections. -/
def reducedPointNorm :
    PresheafWithTransfers.sections (PresheafWithTransfers.reducedTorus k 1)
      (WeightOnePointNorm.point k) →+ Additive kˣ :=
  WeightOnePointNorm.reducedNorm k

/-- Actual graph classes reach every unit; boundary injectivity is a separate theorem. -/
theorem reducedPointNorm_surjective : Function.Surjective (reducedPointNorm k) :=
  WeightOnePointNorm.reducedNorm_surjective

/-- The actual derived weight-one group has its boundary-compatible unit norm. -/
def derivedWeightOneNorm :=
  letI := HasDerivedCategory.standard
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
  WeightOneHomologyNorm.motivicNorm k

/-- Actual graph classes prove surjectivity; the interpolation kernel is separate. -/
theorem derivedWeightOneNorm_surjective : Function.Surjective (derivedWeightOneNorm k) := by
  let := HasDerivedCategory.standard
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
  exact WeightOneHomologyNorm.motivicNorm_surjective k

/-- The original derived weight-one group is canonically its field's unit group. -/
def derivedWeightOneEquiv :=
  letI := HasDerivedCategory.standard
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
  WeightOneEquivalence.weightOneEquiv k

/-- The computed equivalence retains exactly the geometric norm map. -/
theorem derivedWeightOneEquiv_apply (x : _) :
    derivedWeightOneEquiv k x = derivedWeightOneNorm k x := rfl

/-- Actual finite weight-one groups use the literal quotient by unit powers. -/
def derivedFiniteWeightOneEquiv (n : ℕ) :=
  letI := HasDerivedCategory.standard
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
  WeightOneFiniteCoefficients.weightOneFiniteEquiv k n

/-- Every field has the actual integral vanishing bound above its weight. -/
theorem derivedAboveWeightZero (p : ℤ) (q : ℕ) (h : (q : ℤ) < p) :
    letI := HasDerivedCategory.standard
      (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
    Subsingleton (motivicCohomology k p q (SmoothSite.base (Spec (.of k)))) := by
  let := HasDerivedCategory.standard
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
  exact FieldTopDegree.subsingleton_integral_above k p q h

/-- All top-degree finite groups use the original integral quotient by multiples. -/
def derivedTopFiniteEquiv (q n : ℕ) :=
  letI := HasDerivedCategory.standard
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
  FieldTopDegree.topDegreeFiniteEquiv k q n

/-- Arbitrary field maps act on the original derived integral groups. -/
def derivedFieldChange {L : Type u} [Field L] (φ : k →+* L) (p : ℤ) (q : ℕ) :=
  letI := HasDerivedCategory.standard
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
  letI := HasDerivedCategory.standard
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of L))) AddCommGrpCat.{u + 1})
  motivicCohomologyFieldChange φ p q

/-- Every coefficient level uses the actual field-change cone map. -/
def derivedFiniteFieldChange {L : Type u} [Field L] (φ : k →+* L)
    (p : ℤ) (q n : ℕ) :=
  letI := HasDerivedCategory.standard
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
  letI := HasDerivedCategory.standard
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of L))) AddCommGrpCat.{u + 1})
  motivicFiniteCohomologyFieldChange φ p q n

/-- The public weight-two tensor symbol lands in the genuinely defined derived group. -/
def derivedWeightTwoSymbol :=
  letI := HasDerivedCategory.standard
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
  WeightTwoSymbols.motivicTensorSymbol k

/-- Finite weight-two symbols use the original integral coefficient reduction. -/
def derivedFiniteWeightTwoSymbol (n : ℕ) :=
  letI := HasDerivedCategory.standard
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
  WeightTwoFiniteSymbols.finiteTensorSymbol k n

open Lean in
run_cmd do
  for name in #[``MilnorK.K3.PolynomialNorm.polynomialNorm_principal_unit_completeDVR,
      ``MilnorK.K3.PolynomialNorm.polynomialNorm_restrict_of_splits,
      ``motivicComplex, ``motivicComplexPlacementIso,
      ``motivicComplexUnderlyingXIso, ``motivicComplex_d_faces,
      ``motivicComplex_two_d_one_two, ``motivicComplex_one_d_zero_one,
      ``motivicCohomology, ``motivicCohomologyRestriction,
      ``motivicBaseEvaluationComparison, ``motivicRawBaseEvaluationComparison,
      ``canonical, ``derivedGroups, ``fieldComparison, ``cycleComparison,
      ``finiteCoefficients, ``normalizedCanonical, ``finiteDerivedGroups, ``fieldBockstein,
      ``motivicBase_exact_mul_reduction, ``motivicBase_exact_reduction_bockstein,
      ``motivicBase_exact_bockstein_mul, ``signedFieldChange,
      ``simplexFieldComparison, ``torusFieldComparison, ``signedFieldChange_graph,
      ``correspondenceFieldFunctor, ``correspondenceFieldFunctor_comp,
      ``reducedPointNorm, ``reducedPointNorm_surjective,
      ``derivedWeightOneNorm, ``derivedWeightOneNorm_surjective,
      ``derivedWeightOneEquiv, ``derivedWeightOneEquiv_apply,
      ``derivedFiniteWeightOneEquiv, ``derivedAboveWeightZero, ``derivedTopFiniteEquiv,
      ``derivedFieldChange, ``derivedFiniteFieldChange,
      ``derivedWeightTwoSymbol, ``derivedFiniteWeightTwoSymbol,
      ``WeightOneCohomologyFieldChange.weightOneEquiv_fieldChange,
      ``WeightOneCohomologyFieldChange.weightOneFiniteEquiv_fieldChange,
      ``WeightOneCohomologyFieldChange.integral_fieldChange_id,
      ``WeightOneCohomologyFieldChange.finite_fieldChange_id,
      ``WeightOneCohomologyFieldChange.integral_fieldChange_comp,
      ``WeightOneCohomologyFieldChange.finite_fieldChange_comp,
      ``WeightTwoFiniteSymbols.finiteTensorSymbol_topDegree_comparison,
      ``WeightTwoFieldChange.motivicTensorSymbol_fieldChange_square,
      ``WeightTwoFieldChange.finiteTensorSymbol_fieldChange_square,
      ``WeightTwoSkewSymmetry.graphSymbol_add_swap,
      ``WeightTwoSkewSymmetry.two_nsmul_graphSymbol_diagonal,
      ``WeightTwoSkewSymmetry.motivicTensorSymbol_add_swap,
      ``WeightTwoSkewSymmetry.finiteTensorSymbol_add_swap,
      ``motivicRawBaseComplexMap_id, ``motivicRawBaseComplexMap_comp,
      ``motivicBaseComplexMap_id, ``motivicBaseComplexMap_comp,
      ``motivicBaseFiniteConeMap_id, ``motivicBaseFiniteConeMap_comp,
      ``motivicCohomologyFieldChange_id, ``motivicCohomologyFieldChange_comp,
      ``motivicFiniteCohomologyFieldChange_id, ``motivicFiniteCohomologyFieldChange_comp,
      ``AdjoinRoot.norm_algebraMap_sub_root, ``AdjoinRoot.norm_one_sub_root,
      ``WeightTwoPolynomialTransfer.cycleClass_polynomialCycle_eq_sum_corestriction,
      ``WeightTwoSplitPolynomialCycle.polynomialCycle_threeLinear,
      ``WeightTwoSteinbergBound.twelve_nsmul_graphSymbol,
      ``WeightTwoSteinbergBound.graphSymbol_steinberg,
      ``WeightTwoSteinberg.motivicTensorSymbol_steinberg,
      ``WeightTwoSteinberg.finiteTensorSymbol_steinberg,
      ``MilnorK.K3.DegreeFiltration.stageResidue_comp_stageLift,
      ``MilnorK.K3.PolynomialResidue.totalResidue_surjective,
      ``MilnorK.K3.PolynomialResidue.ker_totalResidue_eq_constant_range,
      ``MilnorK.K3.PolynomialResidue.quotientConstantEquivResidues,
      ``Polynomial.LocalResidue.primeIdeal_eq_comap,
      ``Polynomial.LocalResidue.residueEquiv_residueMap,
      ``Polynomial.LocalResidue.fractionMap_algebraMap_localRing,
      ``Polynomial.LocalResidue.irreducible_localRingMap_polynomial,
      ``MilnorK.K3.DVR.residue_restrict,
      ``MilnorK.K3.PolynomialResidue.residueAt_restrict,
      ``MilnorK.K3.InfinityResidue.residue_restrict,
      ``Polynomial.LocalResidue.finite_place_or_no_polynomial_divisor,
      ``MilnorK.K3.PolynomialResidue.residueAt_restrict_zero_of_no_polynomial_divisor,
      ``MilnorK.K3.PolynomialResidue.totalResidue_restrict_single_of_dvd,
      ``MilnorK.K3.PolynomialResidue.totalResidue_restrict_single_of_not_dvd,
      ``MilnorK.K3.PolynomialResidue.totalResidue_restrict_single_support_subset,
      ``MilnorK.K3.PolynomialNorm.polynomialNorm_restrict,
      ``MilnorK.K3.PolynomialNorm.polynomialNorm_comp_restrict,
      ``AdjoinRoot.norm_mk_eq_resultant,
      ``AdjoinRoot.norm_mk_reciprocity,
      ``MilnorK.K3.PolynomialNorm.polynomialNorm_symbol_constant,
      ``MilnorK.K3.PolynomialNorm.polynomialNorm_constant_symbol,
      ``WeightTwoMilnorMixedNorm.raw_mixed,
      ``WeightTwoMilnorMixedNorm.derived_mixed,
      ``WeightTwoMilnorMixedNorm.finite_mixed,
      ``FinitePointBaseChange.finitePushforward_fundamentalCycle,
      ``FinitePointCorrespondenceBaseChange.toIntegralCycle_fieldBaseChange_of_finitePoint,
      ``FinitePointCorrespondenceBaseChange.supportMap_original,
      ``FinitePointCorrespondenceBaseChange.supportMap_base,
      ``AdjoinRoot.branchEquivMaximal,
      ``AdjoinRoot.scalar_local_length_eq_one,
      ``AdjoinRoot.scalarExtensionEquiv,
      ``AdjoinRootScalarBranches.scalar_isPullback,
      ``AdjoinRootScalarBranches.scalar_fundamentalCycle_eq_sum_branches,
      ``AdjoinRootScalarBranches.branchMap_scalarMap,
      ``MilnorK.K3.PolynomialNorm.totalNorm_totalResidue,
      ``MilnorK.K3.PolynomialNorm.totalNorm_unique,
      ``MilnorK.K3.PolynomialNorm.finite_rational_reciprocity,
      ``MilnorK.K3.PolynomialNorm.polynomialNorm_map_constants,
      ``MilnorK.K3.PolynomialNorm.polynomialNorm_root_constant,
      ``AdjoinRoot.norm_root,
      ``WeightTwoMilnorRootNorm.raw_root_constant,
      ``WeightTwoMilnorRootNorm.derived_root_constant,
      ``WeightTwoMilnorRootNorm.finite_root_constant,
      ``MilnorK.K3.DegreeFiltration.lower_succ_eq,
      ``MilnorK.K3.DegreeFiltration.exists_mem_lower,
      ``MilnorK.K3.DegreeFiltration.lower_one_eq_constant_range,
      ``MilnorK.K3.DegreeFiltration.actualStageEquiv,
      ``MilnorK.K3.DegreeFiltration.degreeResidues_eq_zero_iff_mem_lower,
      ``MilnorK.K3.InfinityResidue.residue_polynomial_constants,
      ``MilnorK.K3.PolynomialResidue.totalResidue,
      ``MilnorK.K3.PolynomialResidue.finite_residueAt_support,
      ``MilnorK.K3.DegreeFiltration.reduced_mul_middle_mem_lower,
      ``MilnorK.K3.DegreeFiltration.reduced_mul_right_mem_lower,
      ``MilnorK.K3.DegreeFiltration.reduced_steinberg,
      ``MilnorK.K3.map_comp,
      ``RatFunc.inversion_inversion,
      ``MilnorK.K3.InfinityResidue.residue,
      ``MilnorK.K3.InfinityResidue.residue_inv_variable,
      ``MilnorK.K3.InfinityResidue.residue_comp_constants,
      ``MilnorK.K3.PolynomialResidue.residueAt,
      ``MilnorK.K3.PolynomialResidue.residueAt_reduced,
      ``MilnorK.K3.PolynomialResidue.residueAt_coprime,
      ``MilnorK.K3.symbol3FixedLast,
      ``MilnorK.K3.symbol3_euclidean,
      ``MilnorK.K3.residue3,
      ``MilnorK.K3.residue3_uniformizer_units,
      ``MilnorK.K3.residue3_eq_of_unitPart_change,
      ``MilnorK.K3.DVR.residue,
      ``MilnorK.K3.DVR.residue_uniformizer_ring_units,
      ``Polynomial.LocalResidue.residueEquiv_residue_eq_aeval,
      ``Polynomial.LocalResidue.irreducible_polynomial,
      ``WeightTwoMilnorSymbol.rawMilnorSymbol,
      ``WeightTwoMilnorSymbol.motivicMilnorSymbol,
      ``WeightTwoMilnorSymbol.finiteMilnorSymbolModulo,
      ``WeightTwoMilnorSymbol.motivicMilnorSymbol_fieldChange_square,
      ``WeightTwoMilnorSymbol.finiteMilnorSymbolModulo_fieldChange_square,
      ``WeightTwoCorestriction.cyclePushforward_face,
      ``WeightTwoCorestriction.corestriction, ``WeightTwoCorestriction.corestriction_cycleClass,
      ``WeightTwoCorestriction.motivicCorestriction,
      ``WeightTwoCorestriction.motivicCorestriction_comparison,
      ``WeightTwoCorestriction.corestriction_graphSymbol_prepend,
      ``WeightTwoCorestriction.corestriction_graphSymbol_append,
      ``WeightTwoCorestriction.cyclePushforward_fieldBaseChange,
      ``WeightTwoCorestriction.corestriction_fieldChange,
      ``WeightTwoCorestriction.motivicCorestriction_fieldChange,
      ``WeightTwoCorestriction.corestriction_comp,
      ``WeightTwoCorestriction.motivicCorestriction_comp,
      ``WeightTwoCorestriction.finiteCorestriction_comp,
      ``WeightTwoCorestriction.finiteCorestriction_id,
      ``WeightTwoCorestriction.finiteCorestriction,
      ``WeightTwoCorestriction.finiteCorestriction_integralReduction,
      ``WeightTwoCorestriction.finiteCorestriction_cycleReduction,
      ``WeightTwoMixedNorm.cycle_prepend, ``WeightTwoMixedNorm.cycle_append,
      ``WeightTwoMixedNorm.finite_point_prepend, ``WeightTwoMixedNorm.finite_point_append,
      ``FiniteCorrespondence.toIntegralCycle_fieldBaseChange_comp,
      ``FiniteCorrespondence.toIntegralCycle_fieldBaseChange_id,
      ``GenericFinitePushforwardMultiplicity.scheme_genericLength,
      ``AlgebraicGeometry.finiteCurve_finitePushforward_fiber,
      ``Koszul.domainCartier_chainEuler, ``Koszul.domainCartier_quotient_length,
      ``WeightOneFinitePointNorm.cycleNorm_unitPointCorrespondence,
      ``WeightOneFinitePointNorm.cycleNorm_eq_norm_of_finite_fundamental,
      ``WeightTwoCubicBoundary.cubic_cycleClass_endpoints,
      ``WeightTwoCubicBoundary.cubicCorrespondence_face_zero,
      ``WeightTwoCubicBoundary.cubicCorrespondence_face_one,
      ``AlgebraicGeometry.Scheme.Hom.residueDegree_SpecMap_algebraMap,
      ``Polynomial.TwoUnitPolynomialFamily.cubic_admissible,
      ``Polynomial.TwoUnitPolynomialFamily.cubicFiberZeroEquiv_root,
      ``motivicCohomologyFieldChange_integralReduction, ``motivicCohomologyFieldChange_bockstein,
      ``WeightOneNormFieldChange.reducedNorm_baseReducedTorusFieldChange,
      ``Algebra.norm_eq_prod_quotient_norm_pow_local_length_of_finite,
      ``MilnorK.lift, ``MilnorK.map_comp,
      ``MilnorK.zeroEquiv, ``MilnorK.oneEquiv,
      ``MilnorK.twoEquiv, ``MilnorK.threeEquiv,
      ``MilnorK.twoEquiv_map, ``MilnorK.threeEquiv_map,
      ``IsDiscreteValuationRing.length_quotient_span_eq_addVal,
      ``FiniteCurveNormalization.fiber_fundamentalCoefficient_eq_sum_branchOrders,
      ``DiagonalTopDegree.raw_d_top, ``DiagonalTopDegree.quotientToRawEquiv,
      ``DiagonalTopDegree.quotientToMotivicEquiv,
      ``MilnorK.product, ``MilnorK.product_assoc,
      ``MilnorK.map_product, ``MilnorK.symbol_adjacent_skew,
      ``MilnorK.symbol_adjacent_self,
      ``DiagonalCycleSymbols.graphSymbol_mul,
      ``DiagonalCoordinateInsertion.graphSymbol_steinberg,
      ``DiagonalMilnorSymbol.motivicSymbol,
      ``DiagonalMilnorSymbol.motivicSymbol_two_comparison,
      ``DiagonalFieldChange.motivicSymbol_fieldChange,
      ``DiagonalWeightZero.motivicEquiv, ``DiagonalWeightZero.milnorEquiv,
      ``DiagonalWeightZero.motivicSymbol_zero,
      ``DiagonalCorestriction.corestriction_comp,
      ``DiagonalCorestriction.motivicCorestriction_comp,
      ``MilnorK.specializeTwist, ``MilnorK.twoEquiv_specialize,
      ``MilnorK.DVR.specializeWithUniformizer_ring_units,
      ``MilnorK.productUnit_pair_zero,
      ``MilnorK.residue, ``MilnorK.residueSymbol_steinberg,
      ``MilnorK.zeroEquiv_residue, ``MilnorK.residue_symbol_principal,
      ``MilnorK.residue_symbol_uniformizers,
      ``MilnorK.oneEquiv_residue_one, ``MilnorK.twoEquiv_residue_two,
      ``MilnorK.specialize_change,
      ``MilnorK.residue_eq_of_unitPart_change,
      ``MilnorK.DVR.residueWithUniformizer_independent,
      ``MilnorK.DVR.residue_ring_units_uniformizer,
      ``MilnorK.DVR.residue_principal_ring_unit,
      ``MilnorK.symbol_skew, ``MilnorK.pairMap,
      ``MilnorK.PolynomialResidue.residueAt_eq_dvr,
      ``MilnorK.PolynomialResidue.residueAt_reduced,
      ``MilnorK.PolynomialResidue.finite_residueAt_support,
      ``MilnorK.PolynomialResidue.totalResidue,
      ``MilnorK.InfinityResidue.residue_polynomial_constants,
      ``MilnorK.DegreeFiltration.exists_mem_lower,
      ``MilnorK.DegreeFiltration.lower_succ_eq,
      ``MilnorK.DegreeFiltration.reduced_mul_coordinate_mem_lower,
      ``MilnorK.DegreeFiltration.stageResidue_comp_stageLift,
      ``MilnorK.DegreeFiltration.actualStageEquiv,
      ``MilnorK.PolynomialResidue.totalResidue_surjective,
      ``MilnorK.PolynomialResidue.ker_totalResidue_eq_constant_range,
      ``MilnorK.PolynomialResidue.quotientConstantEquivResidues,
      ``MilnorK.PolynomialResidue.rational_short_exact,
      ``MilnorK.ConstantRestriction.constants_injective,
      ``MilnorK.specialize_product,
      ``MilnorK.DVR.residue_product_base_field_left,
      ``MilnorK.PolynomialNorm.polynomialNorm,
      ``MilnorK.PolynomialNorm.totalNorm_unique,
      ``MilnorK.PolynomialNorm.infinity_residue_eq_of_totalResidue_eq,
      ``MilnorK.PolynomialNorm.finite_rational_reciprocity,
      ``MilnorK.PolynomialNorm.polynomialNorm_map_constants,
      ``MilnorK.PolynomialNorm.polynomialNorm_product_constants_left,
      ``SmoothSite.a1Section_projection,
      ``A1.projectionPullback_naturality,
      ``A1.projectionPullback_coefficient_naturality,
      ``A1.sectionPullback_eq,
      ``PresheafWithTransfers.transfer_homotopy_endpoints,
      ``SheafWithTransfers.isStrictA1Invariant_iff,
      ``SheafCohomology.ordinaryComparison,
      ``SheafCohomology.singleComparison_restriction,
      ``SheafCohomology.singleComparison_coefficient,
      ``SheafWithTransfers.exact_toSheaf_iff,
      ``SheafWithTransfers.underlyingCokernelIso_π_hom,
      ``Cor.ofFiniteFlatSpan,
      ``Cor.toIntegralCycle_ofFiniteFlatSpan,
      ``FiniteFlatCorrespondence.cycleAssembly_coefficient,
      ``Scheme.Hom.isFinite_and_locallyOfFinitePresentation_of_proper_flat_cartier,
      ``Scheme.Hom.pushforwardStructureSheaf_isFiniteLocallyFree_of_proper_flat_cartier,
      ``RelativeCartierDivisor.toIntegralCycle_correspondence,
      ``SheafCohomology.zeroSections_restriction,
      ``SheafCohomology.zeroSections_naturality,
      ``SheafWithTransfers.degreeZeroTransfer_graph,
      ``SheafWithTransfers.degreeZeroTransfer_comp,
      ``SheafWithTransfers.degreeZeroUnderlyingIso,
      ``SheafWithTransfers.degreeZeroTransfer_naturality,
      ``PresheafWithTransfers.contraction_transfer_apply,
      ``PresheafWithTransfers.contractionSectionsIsoQuotient,
      ``PresheafWithTransfers.contractionSectionsIsoUnitKernel,
      ``PresheafWithTransfers.contractionIsoKernel_inv_quotient,
      ``PresheafWithTransfers.contraction_split_identity,
      ``PresheafWithTransfers.contractionFunctor,
      ``PresheafWithTransfers.contractionIsoKernel_hom_naturality,
      ``MilnorK.PolynomialNorm.twoEquiv_polynomialNorm,
      ``DiagonalPolynomialNormComparison.raw_norm,
      ``DiagonalPolynomialNormComparison.derived_norm,
      ``DiagonalPolynomialNormComparison.finite_norm,
      ``PresheafWithTransfers.withParameter_isA1Invariant,
      ``PresheafWithTransfers.contraction_isA1Invariant,
      ``CategoryTheory.AdditiveFunctor.liftedYonedaAddEquiv,
      ``CategoryTheory.AdditiveFunctor.isGrothendieckAbelian,
      ``SheafWithTransfers.isGrothendieckAbelian,
      ``SheafWithTransfers.enoughInjectives,
      ``AlgebraicGeometry.Scheme.Modules.Invertible.semilocalLineBundle_trivial,
      ``AlgebraicGeometry.Scheme.Modules.Invertible.finiteFiberLineBundle_trivial,
      ``MilnorK.specialize_restrict,
      ``MilnorK.DVR.residue_restrict,
      ``MilnorK.PolynomialResidue.residueAt_restrict,
      ``MilnorK.InfinityResidue.residue_restrict,
      ``MilnorK.PolynomialResidue.residueAt_restrict_zero_of_no_polynomial_divisor,
      ``MilnorK.PolynomialResidue.totalResidue_restrict_single_support_subset,
      ``MilnorK.PolynomialNorm.polynomialNorm_restrict,
      ``MilnorK.PolynomialNorm.polynomialNorm_comp_restrict,
      ``AlgebraicGeometry.Scheme.Modules.Invertible.exists_base_open_support_unitIso,
      ``AlgebraicGeometry.Scheme.Modules.Invertible.exists_base_open_unitIso_of_isFinite,
      ``SheafCohomology.zero_isIso_restriction_iff,
      ``SheafWithTransfers.degreeZero_isInvariant,
      ``SheafWithTransfers.IsStrictA1Invariant.isA1Invariant,
      ``SheafWithTransfers.degreeZeroProjectionIso_inv,
      ``SmoothSite.parameterProduct_op_comp_isSheaf,
      ``PresheafWithTransfers.withParameter_isNisnevichSheaf,
      ``PresheafWithTransfers.contraction_isNisnevichSheaf,
      ``SheafWithTransfers.contraction_isA1Invariant,
      ``CategoryTheory.GrothendieckTopology.Point.skyscraperCohomologyComparison,
      ``CategoryTheory.GrothendieckTopology.Point.skyscraper_cohomology_eq_zero,
      ``MilnorK.PolynomialNorm.polynomialNorm_eq_map_rootEvaluation,
      ``MilnorK.PolynomialNorm.polynomialNorm_restrict_of_splits,
      ``MilnorK.PolynomialNorm.oneEquiv_polynomialNorm,
      ``MilnorK.PolynomialNorm.polynomialNorm_one_map_algEquiv,
      ``MilnorK.PolynomialNorm.polynomialNorm_productUnit_constants,
      ``MilnorK.exists_degree_retraction,
      ``MilnorK.finrank_smul_eq_zero_of_map_eq_zero,
      ``MilnorK.eq_zero_of_map_eq_zero_of_coprime_pow,
      ``MilnorK.eq_zero_of_two_maps_eq_zero_of_coprime,
      ``Cor.graph_evaluation_ofFiniteFlatSpan,
      ``RelativeCartierDivisor.productMap_closed_of_target_closed,
      ``RelativeCartierDivisor.graph_evaluation_correspondence,
      ``SmoothSite.nisnevichNeighborhood_cover_lifting,
      ``SmoothSite.nisnevichPoint,
      ``SmoothSite.isColimitNisnevichPointFiberCocone,
      ``SmoothSite.nisnevichPointFiberCocone_naturality,
      ``MilnorK.mixedSpan_eq_top_of_degree_gap,
      ``MilnorK.mixedSpan_eq_top_of_natDegree_le_two,
      ``MilnorK.exists_mixed_expansion_of_degree_gap,
      ``CategoryTheory.uliftYoneda_map_app_injective,
      ``Hypercohomology.freeAbelianSheafFunctor_map_mono,
      ``SheafCohomology.relativePresentation_shortExact,
      ``SheafCohomology.relativeSequence_eq,
      ``SheafCohomology.relativeSequence_exact,
      ``SheafCohomology.relativeBoundary_apply,
      ``SheafCohomology.relative_lift_of_restriction_zero,
      ``SheafCohomology.restriction_lift_of_relativeBoundary_zero,
      ``SheafCohomology.relativeBoundary_lift_of_forget_zero,
      ``AlgebraicGeometry.Scheme.Hom.residueFieldPointLift_comp,
      ``SmoothSite.NisnevichNeighborhood.exists_lift_of_isFinite,
      ``SmoothSite.NisnevichNeighborhood.exists_family_lift_of_isFinite,
      ``FiniteCorrespondenceGenerator.exists_pointed_graph_family_factorization,
      ``MilnorK.FiniteDescent.exists_finite_relation,
      ``MilnorK.FiniteDescent.exists_finite_intermediate_map_eq_zero,
      ``MilnorK.FiniteDescent.eq_zero_of_map_eq_zero_of_finite_degrees_coprime_pow,
      ``Cor.toPoints_comp_graph,
      ``Cor.ofFiniteFlatSpan_comp_graph,
      ``Cor.graph_evaluation_ofFiniteFlatSpan_postcompose,
      ``RelativeCartierDivisor.graph_evaluation_correspondence_of_separated_quasiCompact,
      ``IntermediateField.exists_coprime_splitting_intermediateField,
      ``AlgebraicGeometry.Scheme.Hom.isClosed_target_of_locallyQuasiFinite_source,
      ``FiniteCorrespondence.exists_pointed_cech_boundary_of_common_support_fiber,
      ``FiniteCorrespondence.exists_pointed_cech_boundary_of_common_support_closed_centers,
      ``SheafWithTransfers.contractionSectionBoundary_apply,
      ``SheafWithTransfers.contractionToRelative_injective,
      ``SheafWithTransfers.contractionToRelative_toContraction,
      ``SheafWithTransfers.contractionToRelative_range,
      ``MilnorK.DegreeFiltration.polynomial_symbol_mem_lower_two_of_splits,
      ``MilnorK.restricted_symbol_mem_mixed_of_reduced_splits,
      ``MilnorK.exists_finite_reduced_mixed_expansion,
      ``MilnorK.exists_finite_coprime_mixed_expansion,
      ``AdjoinRoot.coefficientEquiv_coefficientMap,
      ``MilnorK.PolynomialNorm.exists_coprime_restriction_eq_of_algEquiv,
      ``SmoothSite.NisnevichNeighborhood.exists_normalized_refinement,
      ``SmoothSite.sectionToNisnevichPoint_eq_zero_iff,
      ``PresheafWithTransfers.transfer_germ_eq_of_eq_on_support,
      ``SheafCohomology.relativeBoundary_restriction,
      ``SheafWithTransfers.contractionToRelative_restriction_naturality,
      ``SheafCohomology.H_succ_base_eq_zero,
      ``Graph.polynomialTor_length,
      ``Graph.polynomialTor_component_isZero_succ,
      ``MilnorK.PolynomialNorm.polynomialNorm_map_algEquiv_of_prime_normal,
      ``SmoothSite.exists_section_of_mem_nisnevichPrecoverage_of_henselian,
      ``SheafCohomology.H_succ_eq_zero_of_henselian,
      ``MilnorK.DVR.residue_ramified_restrict_apply,
      ``MilnorK.PolynomialNorm.residue_polynomialNorm_ring_units_eq,
      ``MilnorK.PolynomialNorm.residue_polynomialNorm_one_eq,
      ``FiniteCorrespondenceGenerator.exists_graph_family_factorization_with_support_lift,
      ``FiniteCorrespondenceGenerator.exists_pointed_graph_family_factorization_with_support,
      ``FiniteCorrespondenceGenerator.exists_normalized_pointed_graph_family_factorization,
      ``SmoothSite.nisnevichPointFiberCocone_eq_of_center_germ_eq,
      ``GlobalIncidenceAmbientTorComparison.incidenceTor_length_eq_pulled,
      ``RelativeEndpointDiagram.component_incidenceTor_koszul_length,
      ``RelativeEndpointDiagram.rightSupport_endpointScalar_regular,
      ``RelativeEndpointDiagram.component_incidenceTor_isZero_succ,
      ``RelativeEndpointDiagram.component_incidenceTorCorrespondence_eq_fundamental,
      ``RelativeEndpointDiagram.component_toIntegralCycle_incidenceTorCorrespondence,
      ``Algebra.residue_intNorm_eq_norm_residue_pow,
      ``SheafCohomology.zeroSieve_mem_succ,
      ``PresheafWithTransfers.transfer_germ_eq_of_single_center,
      ``PresheafWithTransfers.fixed_lift_germ_evaluation_eq,
      ``MilnorK.PolynomialNorm.residue_polynomialNorm_final_ring_unit,
      ``IsLocalRing.exists_principal_adjusted_uniformizer,
      ``AlgebraicGeometry.relativeFiniteFlat_fundamentalCycle_specialization,
      ``FiniteCorrespondenceGenerator.exists_pointed_germ_family_factorization,
      ``IsDiscreteValuationRing.exists_uniformizer_norm_coefficient_of_prime_degree,
      ``SheafCohomology.h_one_eq_zero_of_nisnevich_coboundary,
      ``PresheafWithTransfers.transfer_germ_eq_at_point_of_eq_on_support,
      ``Cor.graph_relative_endpoint_ofFiniteFlatSpan_postcompose,
      ``RelativeCartierDivisor.graph_relative_endpoint_correspondence,
      ``FiniteCorrespondence.exists_cech_boundary_of_common_support_lift_with_point_lift,
      ``MilnorK.PolynomialNorm.residue_polynomialNorm_mixed_prime,
      ``SheafCohomology.h_one_eq_zero_of_square_difference_surjective,
      ``FiniteCorrespondence.exists_pointed_cech_boundary_with_point_property] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Integrated actual motivic complexes and derived groups use only standard Lean axioms."

end MotivicTest.MotivicIntegration
