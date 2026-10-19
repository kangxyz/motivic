/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import MotivicTest.CorrespondenceCategory
public import MotivicTest.IncidenceTorAssociativity
public import MotivicTest.RightExteriorPairStalks
public import MotivicTest.CorrespondenceGraphFunctor
public import MotivicTest.PresheavesWithTransfers
public import MotivicTest.PresheafGraphRestriction
public import MotivicTest.SmoothSiteProducts
public import MotivicTest.SimplexExterior
public import MotivicTest.ProductGraphTransversality
public import MotivicTest.SmoothSiteNisnevich
public import MotivicTest.FiniteSupportShrinking
public import MotivicTest.ExteriorPointClosurePushforward
public import MotivicTest.KoszulRegularBlockElimination
public import MotivicTest.ExteriorIdentityIncidence
public import MotivicTest.SimplexExteriorGraphInterchange
public import MotivicTest.SimplexSingularTransferMaps
public import MotivicTest.HenselianEtaleSections
public import MotivicTest.ArtinianEtaleSections
public import MotivicTest.HenselianSchemeSections
public import MotivicTest.NisnevichHenselian
public import MotivicTest.CorPublicImports
public import MotivicTest.NisnevichHenselianEvaluation
public import MotivicTest.ArtinianSchemeSections
public import MotivicTest.NisnevichQuasiFinite
public import MotivicTest.NisnevichFiberSections
public import MotivicTest.NisnevichFiniteSplitting
public import MotivicTest.FiniteEtaleNeighborhoodIso
public import MotivicTest.NisnevichFiniteBranchLift
public import MotivicTest.NisnevichFiniteLifting
public import MotivicTest.NisnevichFiniteFamilyLifting
public import MotivicTest.SmoothSiteNisnevichFiniteLifting
public import MotivicTest.NisnevichGeneratorLift
public import MotivicTest.NisnevichLocalGeneratorLift
public import MotivicTest.NisnevichSignedLocalLift
public import MotivicTest.SmoothSiteNisnevichFiniteFamilyLifting
public import MotivicTest.NisnevichFamilyGeneratorLift
public import MotivicTest.NisnevichFamilyLocalLift
public import MotivicTest.NisnevichCechSupportPairing
public import MotivicTest.FinitePushforwardInjective
public import MotivicTest.ClosedImageBaseChange
public import MotivicTest.SmoothSiteCoproducts
public import MotivicTest.SmoothSiteFiniteCovers
public import MotivicTest.CorBinaryCoproducts
public import MotivicTest.CorFiniteCoproducts
public import MotivicTest.CorNisnevichTopology
public import MotivicTest.SheafifyAdditive
public import MotivicTest.SmoothSiteNisnevichFiniteDescent
public import MotivicTest.NisnevichComparison
public import MotivicTest.TransferNisnevichSheafification
public import MotivicTest.SheafifyLocallyBijective
public import MotivicTest.NisnevichCechGraphPushforward
public import MotivicTest.NisnevichCechLocalExactness
public import MotivicTest.NisnevichFiniteSubfamily
public import MotivicTest.FiniteCommonImage
public import MotivicTest.NisnevichCechFiniteSupport
public import MotivicTest.NisnevichCechIncidencePairing
public import MotivicTest.ProductDiagonal
public import MotivicTest.ProductDiagonalBaseChange
public import MotivicTest.ExteriorIdentityRemainingPair
public import MotivicTest.ExteriorIdentityRemainingIncidence
public import MotivicTest.ExteriorIdentityIncidenceProjection
public import MotivicTest.ExteriorIdentityTorLengthComparison
public import MotivicTest.ExteriorIdentityComponentPushforward
public import MotivicTest.ExteriorIdentityTorCycle
public import MotivicTest.ExteriorIdentityComposition
public import MotivicTest.ExteriorIdentityUnit
public import MotivicTest.SimplexExteriorFunctor
public import MotivicTest.SimplexSingularTransferFunctor
public import MotivicTest.KoszulTorRegularBlockReduction

/-!
# Integrated correspondence and transfer interfaces

The actual correspondence category, graph functor, additive presheaves with
transfers, simplex exterior cycles, mixed graph law and smooth Nisnevich site
coexist with the general henselian and Artinian lifting results in one
environment. The consumers above retain their concrete cycle formulas.
Actual exterior identity and composition yield the additive simplex functor
and the all-degree singular transfer functor. Actual Nisnevich sheafification
preserves transfers and has the original ordinary sheafification as its
underlying sheaf, with canonical unit compatibility.
The final check rejects any nonstandard axiom reachable from these interfaces.
-/

@[expose] public section

open Lean Motivic.FiniteCorrespondenceGenerator in
open _root_.AlgebraicGeometry.Scheme.Cycles.Pushforward.ExteriorPointClosure in
open _root_.AlgebraicGeometry.Scheme.Hom.ArtinianEtale in
open _root_.AlgebraicGeometry.Scheme.Hom.HenselianEtale in
open _root_.AlgebraicGeometry.Scheme.IntegralCycle in
run_cmd do
  let interfaces := #[
    ``Motivic.FiniteCorrespondence.incidenceTorPairing_assoc,
    ``Motivic.Cor.category,
    ``Motivic.Cor.coproductIsColimit,
    ``Motivic.Cor.empty_isZero,
    ``Motivic.Cor.nisnevichTopology,
    ``Motivic.Cor.principal_covering_basis,
    ``Motivic.Cor.coproduct_restriction_bijective,
    ``Motivic.FiniteCorrespondence.exists_nisnevich_cech_boundary,
    ``_root_.AlgebraicGeometry.Scheme.SmoothSite.exists_finiteNisnevichCoverNormalization,
    ``CategoryTheory.sheafify_additive_of_principal_covering_basis,
    ``_root_.AlgebraicGeometry.Scheme.SmoothSite.isSheaf_iff_singleton_of_finiteCoproduct,
    ``Motivic.PresheafWithTransfers.isSheaf_correspondenceTopology_iff_restriction,
    ``Motivic.PresheafWithTransfers.isNisnevichSheaf_iff_correspondenceTopology,
    ``Motivic.PresheafWithTransfers.nisnevichSheafificationAdjunction,
    ``Motivic.PresheafWithTransfers.nisnevichSheafificationUnderlyingIso,
    ``Motivic.PresheafWithTransfers.toSheafify_nisnevichSheafificationUnderlyingIso,
    ``Motivic.Cor.preadditive,
    ``Motivic.incidenceTorPairing_componentGraph_comp,
    ``Motivic.Cor.graphFunctor,
    ``Motivic.PresheafWithTransfers.transfer_comp,
    ``Motivic.PresheafWithTransfers.representable,
    ``Motivic.PresheafWithTransfers.yonedaAddEquiv,
    ``Motivic.PresheafWithTransfers.toPresheaf,
    ``_root_.AlgebraicGeometry.Scheme.SmoothSite.categoricalProductIso,
    ``_root_.AlgebraicSimplex.structureMap_geometricallyIntegral,
    ``Motivic.FiniteCorrespondenceGenerator.toIntegralCycle_exteriorIdentityGenerator_cycle,
    ``Motivic.Cor.simplexExterior,
    ``_root_.AlgebraicGeometry.Scheme.Graph.Product.mixed_isPullback,
    ``_root_.AlgebraicGeometry.Scheme.Graph.Product.exists_common_regular_list,
    ``_root_.AlgebraicGeometry.Scheme.SmoothSite.nisnevichTopology_eq_restrictedTopology,
    ``_root_.AlgebraicGeometry.Scheme.SmoothSite.restrictNisnevichSheafificationIso,
    ``Motivic.SheafWithTransfers.toSheaf,
    ``Motivic.FiniteCorrespondence.exists_open_nhds_preimage_subset,
    ``finitePushforward_fundamentalCycle,
    ``_root_.ChainComplex.Koszul.regularBlockHomologyIso,
    ``_root_.ChainComplex.Koszul.regularBlockHomology_length,
    ``Motivic.FiniteCorrespondenceGenerator.exteriorIdentityIncidenceIso,
    ``Motivic.Cor.simplexExterior_graph_interchange,
    ``Motivic.Cor.simplexExteriorNatTrans,
    ``Motivic.PresheafWithTransfers.singularTransfer,
    ``Motivic.PresheafWithTransfers.singularTransfer_comm,
    ``_root_.Algebra.Etale.Henselian.exists_lift_of_etale,
    ``_root_.Algebra.Etale.Artinian.exists_lift_of_formallySmooth,
    ``_root_.AlgebraicGeometry.Scheme.Hom.HenselianEtale.exists_section_of_etale,
    ``_root_.AlgebraicGeometry.Scheme.Hom.HenselianEtale.exists_section_of_etale_of_artinian,
    ``_root_.AlgebraicGeometry.Nisnevich.covering_sieve_eq_top_of_henselian,
    ``_root_.AlgebraicGeometry.Nisnevich.covering_sieve_eq_top_of_artinian,
    ``_root_.AlgebraicGeometry.Nisnevich.isIso_toSheafify_app_of_henselian,
    ``_root_.AlgebraicGeometry.Nisnevich.exact_map_ringEvaluation_of_henselian,
    ``exists_section_of_etale_of_isLocallyArtinian,
    ``AlgebraicGeometry.exists_nisnevich_isCompl_of_quasiFiniteAt,
    ``AlgebraicGeometry.Scheme.Hom.exists_lift_from_quasiFiniteFiber_of_residueFieldIso,
    ``AlgebraicGeometry.exists_nisnevich_finiteSplitting,
    ``AlgebraicGeometry.Scheme.Hom.exists_isIso_morphismRestrict_of_singleton,
    ``AlgebraicGeometry.exists_nisnevich_lift_of_isFinite_singleton,
    ``AlgebraicGeometry.exists_nisnevich_lift_of_isFinite,
    ``AlgebraicGeometry.exists_nisnevich_family_lift_of_isFinite,
    ``_root_.AlgebraicGeometry.Scheme.SmoothSite.exists_nisnevich_lift_of_isFinite,
    ``_root_.AlgebraicGeometry.Scheme.SmoothSite.exists_common_nisnevich_refinement,
    ``Motivic.FiniteCorrespondence.exists_nisnevich_graph_factorization,
    ``Motivic.FiniteCorrespondence.exists_nisnevich_graph_family_factorization,
    ``Motivic.FiniteCorrespondenceGenerator.exists_cech_pairing_of_common_support,
    ``finitePushforward_injective_of_isClosedImmersion,
    ``AlgebraicGeometry.ClosedImageBaseChange.inclusion_isClosedImmersion,
    ``_root_.AlgebraicGeometry.Nisnevich.exists_finset_residueFieldLifting,
    ``Motivic.FiniteCorrespondenceGenerator.exists_cech_pairing_of_incidenceTor,
    ``_root_.ChainComplex.Koszul.regularLeadingBlockTor_length,
    ``Motivic.FiniteCorrespondenceGenerator.exteriorIncidenceProjection_isPullback,
    ``Motivic.FiniteCorrespondenceGenerator.exteriorIncidenceTor_length,
    ``Motivic.FiniteCorrespondenceGenerator.exteriorIncidenceTorCoefficient_eq,
    ``exteriorIncidence_finitePushforward_componentFundamentalCycle,
    ``Motivic.FiniteCorrespondenceGenerator.exteriorIncidenceTorCycle_eq_component_sum,
    ``Motivic.FiniteCorrespondence.exteriorIdentity_incidenceTorPairing,
    ``Motivic.Cor.simplexExterior_comp,
    ``Motivic.Cor.simplexExterior_id,
    ``Motivic.Cor.simplexExteriorAdditiveFunctor,
    ``Motivic.Cor.simplexProductCosimplicialFunctor,
    ``Motivic.PresheafWithTransfers.singularTransfer_comp,
    ``Motivic.PresheafWithTransfers.singularAdditiveFunctor]
  for interface in interfaces do
    for dependency in ← collectAxioms interface do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "Interface {interface} depends on unsupported assumption {dependency}"
  logInfo "Integrated correspondence and Nisnevich interfaces use only standard Lean axioms."
