/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.WeightTwoMonicDeformationTransfer
public import Motivic.Cohomology.Motivic.WeightTwoScalarPairChange
public import Motivic.Aglib.RingTheory.AdjoinRootFactorLength

/-!
# Literal factor-field transfers of whole polynomial endpoints

The complete maximal-quotient decomposition is transported through the actual
scalar-compatible quotient-field equivalence. The resulting factors retain
all original local lengths and the actual images of both original units.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open scoped BigOperators
open UniqueFactorizationMonoid

universe u

namespace Motivic.WeightTwoMonicDeformationFactors

open WeightTwoCorestriction WeightTwoMonicDeformation WeightTwoMonicDeformationTransfer

variable {k : Type u} [Field k]

local instance quotientField {R : Type u} [CommRing R] (q : MaximalSpectrum R) :
    Field (R ⧸ q.asIdeal) := Ideal.Quotient.field q.asIdeal

/-- An actual scalar-compatible field isomorphism preserves the finite point transfer. -/
theorem pointPushforward_graph_algEquiv {E F : Type u} [Field E] [Field F]
    [Algebra k E] [Algebra k F] [Module.Finite k E] [Module.Finite k F]
    (e : E ≃ₐ[k] F) (a b : Eˣ) :
    pointPushforward (k := k) ((Cor.graphFunctor E).map
      (WeightTwoSymbols.rationalPair E a b)) =
    pointPushforward (k := k) ((Cor.graphFunctor F).map
      (WeightTwoSymbols.rationalPair F (Units.map e.toRingHom.toMonoidHom a)
        (Units.map e.toRingHom.toMonoidHom b))) := by
  let t := Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op
  have ht : IsIso (Spec.map (CommRingCat.ofHom e.toRingHom)) := by
    change IsIso t.hom
    infer_instance
  apply FiniteCorrespondence.toIntegralCycle_injective
  rw [toIntegralCycle_pointPushforward_graph, toIntegralCycle_pointPushforward_graph,
    ← finitePushforward_fundamentalCycle (Spec.map (CommRingCat.ofHom e.toRingHom)),
    ← AddMonoidHom.comp_apply, ← IntegralCycle.finitePushforward_comp]
  exact DFunLike.congr_fun (IntegralCycle.finitePushforward_congr
    (WeightTwoScalarPairChange.scalarPoint_rationalPair_comp e.toRingHom
      (RingHom.ext e.commutes) a b)) _

/-- The same literal isomorphism preserves the original raw-H22 corestriction. -/
theorem corestriction_graphSymbol_algEquiv {E F : Type u} [Field E] [Field F]
    [Algebra k E] [Algebra k F] [Module.Finite k E] [Module.Finite k F]
    (e : E ≃ₐ[k] F) (a b : Eˣ) :
    corestriction (k := k) (WeightTwoSymbols.graphSymbol E a b) =
      corestriction (k := k) (WeightTwoSymbols.graphSymbol F
        (Units.map e.toRingHom.toMonoidHom a) (Units.map e.toRingHom.toMonoidHom b)) := by
  have h := congrArg (WeightTwoSymbols.cycleClass k) (pointPushforward_graph_algEquiv e a b)
  rw [← corestriction_cycleClass, ← corestriction_cycleClass] at h
  exact h

/-- An original unit in the literal quotient by a monic irreducible factor. -/
def branchUnit (p : k[X]) (a : (AdjoinRoot p)ˣ) (q : AdjoinRoot.IrreducibleBranch p) :
    (AdjoinRoot q.val.val)ˣ :=
  Units.map (AdjoinRoot.divisorMap p q.val.val q.property).toMonoidHom a

/-- The actual quotient-field equivalence carries precisely the original unit images. -/
theorem branchQuotientAlgEquiv_residueUnit (p : k[X]) (a : (AdjoinRoot p)ˣ)
    (q : AdjoinRoot.IrreducibleBranch p) :
    Units.map (AdjoinRoot.branchQuotientAlgEquiv p q).toRingHom.toMonoidHom
      (residueUnit p a (AdjoinRoot.branchMaximal p q)) = branchUnit p a q := by
  apply Units.ext
  exact AdjoinRoot.branchQuotientEquiv_mk p q a

/-- A maximal quotient transfer equals the literal factor-field transfer. -/
theorem corestriction_residueUnit_branch (p : k[X]) (hp : p.Monic)
    (a b : (AdjoinRoot p)ˣ) (q : AdjoinRoot.IrreducibleBranch p) :
    letI := hp.finite_adjoinRoot
    letI := q.val.property.1.finite_adjoinRoot
    corestriction (k := k) (WeightTwoSymbols.graphSymbol
      (AdjoinRoot p ⧸ (AdjoinRoot.branchMaximal p q).asIdeal)
      (residueUnit p a (AdjoinRoot.branchMaximal p q))
      (residueUnit p b (AdjoinRoot.branchMaximal p q))) =
      corestriction (k := k) (WeightTwoSymbols.graphSymbol (AdjoinRoot q.val.val)
        (branchUnit p a q) (branchUnit p b q)) := by
  let := hp.finite_adjoinRoot
  let := q.val.property.1.finite_adjoinRoot
  rw [corestriction_graphSymbol_algEquiv (AdjoinRoot.branchQuotientAlgEquiv p q),
    branchQuotientAlgEquiv_residueUnit, branchQuotientAlgEquiv_residueUnit]

/-- Every literal factor occurs with its original local length, including repeated factors. -/
theorem cycleClass_polynomialCycle_eq_sum_branches (p : k[X]) (hp : p.Monic)
    (a b : (AdjoinRoot p)ˣ) :
    letI := hp.finite_adjoinRoot
    letI : IsArtinianRing (AdjoinRoot p) := .of_finite k _
    letI : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
    letI : Fintype (AdjoinRoot.IrreducibleBranch p) :=
      Fintype.ofEquiv (MaximalSpectrum (AdjoinRoot p))
        (AdjoinRoot.branchEquivMaximal p hp.ne_zero).symm
    WeightTwoSymbols.cycleClass k (polynomialCycle p hp a b) =
      ∑ q : AdjoinRoot.IrreducibleBranch p,
        letI := q.val.property.1.finite_adjoinRoot
        ((Module.length (Localization.AtPrime (AdjoinRoot.branchMaximal p q).asIdeal)
          (Localization.AtPrime (AdjoinRoot.branchMaximal p q).asIdeal)).toNat : ℤ) •
          corestriction (k := k) (WeightTwoSymbols.graphSymbol (AdjoinRoot q.val.val)
            (branchUnit p a q) (branchUnit p b q)) := by
  classical
  let := hp.finite_adjoinRoot
  let : IsArtinianRing (AdjoinRoot p) := .of_finite k _
  let : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
  let : Fintype (AdjoinRoot.IrreducibleBranch p) :=
    Fintype.ofEquiv (MaximalSpectrum (AdjoinRoot p))
      (AdjoinRoot.branchEquivMaximal p hp.ne_zero).symm
  rw [cycleClass_polynomialCycle_eq_sum_corestriction]
  symm
  apply Fintype.sum_equiv (AdjoinRoot.branchEquivMaximal p hp.ne_zero)
  intro q
  dsimp only [AdjoinRoot.branchEquivMaximal, Equiv.ofBijective_apply]
  rw [corestriction_residueUnit_branch p hp]


open scoped Classical in
/-- The exact number of occurrences of each factor replaces its original local length. -/
theorem cycleClass_polynomialCycle_eq_sum_factor_counts (p : k[X]) (hp : p.Monic)
    (a b : (AdjoinRoot p)ˣ) :
    letI := hp.finite_adjoinRoot
    letI : IsArtinianRing (AdjoinRoot p) := .of_finite k _
    letI : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
    letI : Fintype (AdjoinRoot.IrreducibleBranch p) :=
      Fintype.ofEquiv (MaximalSpectrum (AdjoinRoot p))
        (AdjoinRoot.branchEquivMaximal p hp.ne_zero).symm
    WeightTwoSymbols.cycleClass k (polynomialCycle p hp a b) =
      ∑ q : AdjoinRoot.IrreducibleBranch p,
        letI := q.val.property.1.finite_adjoinRoot
        ((normalizedFactors p).count q.val.val : ℤ) •
          corestriction (k := k) (WeightTwoSymbols.graphSymbol (AdjoinRoot q.val.val)
            (branchUnit p a q) (branchUnit p b q)) := by
  classical
  let := hp.finite_adjoinRoot
  let : IsArtinianRing (AdjoinRoot p) := .of_finite k _
  let : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
  let : Fintype (AdjoinRoot.IrreducibleBranch p) :=
    Fintype.ofEquiv (MaximalSpectrum (AdjoinRoot p))
      (AdjoinRoot.branchEquivMaximal p hp.ne_zero).symm
  rw [cycleClass_polynomialCycle_eq_sum_branches]
  apply Finset.sum_congr rfl
  intro q _
  rw [AdjoinRoot.branch_local_length_eq_count_normalizedFactors p hp q, ENat.toNat_natCast]


/-- For an irreducible polynomial, the full endpoint is its original finite corestriction. -/
theorem cycleClass_polynomialCycle_irreducible (p : k[X]) (hp : p.Monic)
    [Fact (Irreducible p)] (a b : (AdjoinRoot p)ˣ) :
    letI := hp.finite_adjoinRoot
    WeightTwoSymbols.cycleClass k (polynomialCycle p hp a b) =
      corestriction (k := k) (WeightTwoSymbols.graphSymbol (AdjoinRoot p) a b) := by
  classical
  let := hp.finite_adjoinRoot
  let : IsArtinianRing (AdjoinRoot p) := .of_finite k _
  let : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
  let : Fintype (AdjoinRoot.IrreducibleBranch p) :=
    Fintype.ofEquiv (MaximalSpectrum (AdjoinRoot p))
      (AdjoinRoot.branchEquivMaximal p hp.ne_zero).symm
  let q : AdjoinRoot.IrreducibleBranch p := ⟨⟨p, hp, Fact.out⟩, dvd_rfl⟩
  have hall (r : AdjoinRoot.IrreducibleBranch p) : r = q := by
    apply Subtype.ext
    apply Subtype.ext
    exact Polynomial.eq_of_monic_of_associated r.val.property.1 hp
      (r.val.property.2.associated_of_dvd Fact.out r.property)
  let : Subsingleton (AdjoinRoot.IrreducibleBranch p) :=
    ⟨fun r s => (hall r).trans (hall s).symm⟩
  rw [cycleClass_polynomialCycle_eq_sum_factor_counts, Fintype.sum_subsingleton _ q]
  have hunit (c : (AdjoinRoot p)ˣ) : branchUnit p c q = c := by
    apply Units.ext
    obtain ⟨f, hf⟩ := AdjoinRoot.mk_surjective (c : AdjoinRoot p)
    change AdjoinRoot.divisorMap p p dvd_rfl c = c
    rw [← hf, AdjoinRoot.divisorMap_mk]
  change ((normalizedFactors p).count p : ℤ) • _ = _
  rw [normalizedFactors_irreducible (Fact.out : Irreducible p), hp.normalize_eq_self,
    Multiset.count_singleton_self, Nat.cast_one, one_smul, hunit, hunit]

end Motivic.WeightTwoMonicDeformationFactors
