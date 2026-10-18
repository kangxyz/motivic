/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K2.BalancedRepresentatives
public import Motivic.Cohomology.Motivic.WeightTwoMilnorMixedNorm
public import Motivic.Cohomology.Motivic.WeightTwoMonicDeformationNormSum
public import Aglib.KTheory.MilnorK.K3.PolynomialNormDeformation

/-!
# The actual polynomial Milnor norm and motivic corestriction

The comparison uses small-total-degree generators of the actual Milnor group
and a finite monic two-unit deformation. Its whole special fiber retains every
irreducible factor and multiplicity. Strong induction applies only after all
factors have strictly smaller polynomial degree.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial

universe w u

namespace Motivic.WeightTwoMilnorNormComparison

open MilnorK.K2 MilnorK.K3.PolynomialResidue
open MilnorK.K3.PolynomialNorm WeightTwoMilnorSymbol WeightTwoCorestriction
open Polynomial.TwoUnitMonicDeformation WeightTwoMonicDeformation
open WeightTwoMonicDeformationFactors

variable {k : Type u} [Field k] [CharZero k]

local instance finite_root (p : MonicIrreducible k) :
    Module.Finite k (AdjoinRoot p.val) := p.property.1.finite_adjoinRoot

local instance charZero_root (p : MonicIrreducible k) : CharZero (AdjoinRoot p.val) :=
  charZero_of_injective_algebraMap (algebraMap k (AdjoinRoot p.val)).injective

omit [CharZero k] in
/-- A degree-zero polynomial coordinate is literally a base-field unit. -/
theorem unit_eq_map_constant (p : MonicIrreducible k) (B : k[X])
    (hB : B ≠ 0) (hdeg : B.natDegree = 0) (b : (AdjoinRoot p.val)ˣ)
    (hb : (b : AdjoinRoot p.val) = AdjoinRoot.mk p.val B) :
    ∃ b₀ : kˣ, b = Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom b₀ := by
  have hC : B = C (B.coeff 0) := eq_C_of_natDegree_eq_zero hdeg
  have hc : B.coeff 0 ≠ 0 := by
    intro h
    apply hB
    rw [hC, h, C_0]
  refine ⟨Units.mk0 (B.coeff 0) hc, ?_⟩
  apply Units.ext
  change (b : AdjoinRoot p.val) = algebraMap k (AdjoinRoot p.val) (B.coeff 0)
  rw [hb, hC, AdjoinRoot.mk_C, coeff_C_zero]
  rfl

/-- The genuine degree-one base case uses actual mixed-symbol compatibility. -/
theorem raw_norm_degree_one (p : MonicIrreducible k) (hp : p.val.natDegree = 1)
    (x : MilnorK.K2.Group (AdjoinRoot p.val)) :
    rawMilnorSymbol k (polynomialNorm p x) =
      corestriction (k := k) (E := AdjoinRoot p.val) (rawMilnorSymbol (AdjoinRoot p.val) x) := by
  have hmaps : (rawMilnorSymbol k).comp (polynomialNorm p).toAddMonoidHom =
      (corestriction (k := k) (E := AdjoinRoot p.val)).comp
        (rawMilnorSymbol (AdjoinRoot p.val)) := by
    apply lowDegree_symbolHom_ext p.property.1
    intro A B _ hB hdeg a b _ hb
    have hBd : B.natDegree = 0 := by omega
    obtain ⟨b₀, rfl⟩ := unit_eq_map_constant p B hB hBd b hb
    exact WeightTwoMilnorMixedNorm.raw_mixed p a b₀
  exact DFunLike.congr_fun hmaps x

omit [CharZero k] in
/-- The entire deformed endpoint stays coprime to both polynomial coordinates. -/
theorem endpoint_isCoprime (p A B : k[X]) (γ s : k)
    (hcop : IsCoprime p (A * B)) :
    IsCoprime (endpointPolynomial p A B γ s) (A * B) := by
  simpa only [endpointPolynomial, IsCoprime.sub_mul_right_left_iff] using hcop

omit [CharZero k] in
/-- The original product divides the exact difference between whole endpoints. -/
theorem endpoint_difference (p A B : k[X]) (γ s : k) :
    A * B ∣ p - endpointPolynomial p A B γ s := by
  rw [endpointPolynomial, sub_sub_cancel]
  exact dvd_mul_left _ _

/-- The whole initial fiber is the original finite transfer of the chosen symbol. -/
theorem zeroCycle_eq_corestriction (p : MonicIrreducible k) (A B : k[X])
    (γ : k) (hcop : IsCoprime p.val (A * B)) (a b : (AdjoinRoot p.val)ˣ)
    (ha : (a : AdjoinRoot p.val) = AdjoinRoot.mk p.val A)
    (hb : (b : AdjoinRoot p.val) = AdjoinRoot.mk p.val B) :
    WeightTwoSymbols.cycleClass k (zeroCycle p.val A B γ p.property.1 hcop) =
      corestriction (k := k) (E := AdjoinRoot p.val)
        (rawMilnorSymbol (AdjoinRoot p.val) (symbol a b)) := by
  have ha₀ : zeroFirstUnit p.val A B γ hcop = a := by
    apply Units.ext
    exact (zeroFirstUnit_val p.val A B γ hcop).trans ha.symm
  have hb₀ : zeroSecondUnit p.val A B γ hcop = b := by
    apply Units.ext
    exact (zeroSecondUnit_val p.val A B γ hcop).trans hb.symm
  rw [zeroCycle, cycleClass_polynomialCycle_irreducible, ha₀, hb₀,
    rawMilnorSymbol_symbol]

/-- A termwise comparison on all literal factors compares the whole endpoint.
The multiset retains every repeated factor. -/
theorem factor_sum_comparison (p A B : k[X]) (hp : p.Monic)
    (hcop : IsCoprime p (A * B)) (a b : (AdjoinRoot p)ˣ)
    (ha : (a : AdjoinRoot p) = AdjoinRoot.mk p A)
    (hb : (b : AdjoinRoot p) = AdjoinRoot.mk p B)
    (h : ∀ r : MonicIrreducible k, r ∈ factorPlaces p hp.ne_zero →
      ∀ x : MilnorK.K2.Group (AdjoinRoot r.val),
        rawMilnorSymbol k (polynomialNorm r x) =
          corestriction (k := k) (E := AdjoinRoot r.val) (rawMilnorSymbol (AdjoinRoot r.val) x)) :
    rawMilnorSymbol k (factorNormSum p A B hp hcop) =
      WeightTwoSymbols.cycleClass k (polynomialCycle p hp a b) := by
  classical
  rw [cycleClass_polynomialCycle_eq_factorPlaces p A B hp hcop a b ha hb,
    factorNormSum, map_multiset_sum, Multiset.map_map]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro r _
  exact h r.val r.property (factorSymbol p A B hp.ne_zero hcop r)

/-- The higher-degree comparison follows from comparisons at strictly smaller
actual quotient fields, using the whole finite monic deformation. -/
theorem raw_norm_degree_step (p : MonicIrreducible k) (hn : 1 < p.val.natDegree)
    (ih : ∀ r : MonicIrreducible k, r.val.natDegree < p.val.natDegree →
      ∀ x : MilnorK.K2.Group (AdjoinRoot r.val),
        rawMilnorSymbol k (polynomialNorm r x) =
          corestriction (k := k) (E := AdjoinRoot r.val) (rawMilnorSymbol (AdjoinRoot r.val) x))
    (x : MilnorK.K2.Group (AdjoinRoot p.val)) :
    rawMilnorSymbol k (polynomialNorm p x) =
      corestriction (k := k) (E := AdjoinRoot p.val) (rawMilnorSymbol (AdjoinRoot p.val) x) := by
  classical
  have hmaps : (rawMilnorSymbol k).comp (polynomialNorm p).toAddMonoidHom =
      (corestriction (k := k) (E := AdjoinRoot p.val)).comp
        (rawMilnorSymbol (AdjoinRoot p.val)) := by
    apply lowDegree_symbolHom_ext p.property.1
    intro A B hA hB hdeg a b ha hb
    let : Infinite k := Infinite.of_injective Nat.cast Nat.cast_injective
    obtain ⟨c, hcA, hcB⟩ := exists_good_point A B hA hB
    let γ := gamma p.val A B c
    let q := endpointPolynomial p.val A B γ 1
    have hcop : IsCoprime p.val (A * B) := isCoprime_product p.property.2 hA hB hdeg
    have hq : q.Monic := endpointPolynomial_monic p.val A B γ 1 p.property.1 hdeg
    have hqc : IsCoprime q (A * B) := endpoint_isCoprime p.val A B γ 1 hcop
    have hqd : p.val.natDegree = q.natDegree :=
      (endpointPolynomial_natDegree p.val A B γ 1 hdeg).symm
    have hrA : ¬ p.val ∣ A := not_dvd_of_natDegree_lt hA (by omega)
    have hrB : ¬ p.val ∣ B := not_dvd_of_natDegree_lt hB (by omega)
    have hsingle : polynomialNorm p (symbol a b) =
        factorNormSum p.val A B p.property.1 hcop := by
      rw [factorNormSum_irreducible p A B hcop hrA hrB]
      congr 1
      apply congrArg₂ symbol
      · exact Units.ext ha
      · exact Units.ext hb
    have hrec := factorNormSum_eq_of_monic_deformation p.val q A B
      p.property.1 hq hqd hA hB hcop hqc (endpoint_difference p.val A B γ 1)
    have hfactor : ∀ r : MonicIrreducible k, r ∈ factorPlaces q hq.ne_zero →
        ∀ y : MilnorK.K2.Group (AdjoinRoot r.val),
          rawMilnorSymbol k (polynomialNorm r y) =
            corestriction (k := k) (E := AdjoinRoot r.val)
            (rawMilnorSymbol (AdjoinRoot r.val) y) := by
      intro r hr y
      apply ih r _ y
      exact irreducible_factor_natDegree_lt p.val A B c p.property.1 hdeg hn hcA hcB
        r.val r.property.2 ((mem_factorPlaces_iff q hq.ne_zero r).mp hr)
    have hone := factor_sum_comparison q A B hq hqc
      (oneFirstUnit p.val A B γ hcop) (oneSecondUnit p.val A B γ hcop)
      (oneFirstUnit_val p.val A B γ hcop) (oneSecondUnit_val p.val A B γ hcop) hfactor
    calc
      rawMilnorSymbol k (polynomialNorm p (symbol a b)) =
          rawMilnorSymbol k (factorNormSum p.val A B p.property.1 hcop) :=
        congrArg (rawMilnorSymbol k) hsingle
      _ = rawMilnorSymbol k (factorNormSum q A B hq hqc) :=
        congrArg (rawMilnorSymbol k) hrec
      _ = WeightTwoSymbols.cycleClass k
          (oneCycle p.val A B γ p.property.1 hdeg hcop) := hone
      _ = WeightTwoSymbols.cycleClass k
          (zeroCycle p.val A B γ p.property.1 hcop) :=
        (monicDeformation_cycleClass_endpoints p.val A B γ p.property.1 hdeg hcop).symm
      _ = corestriction (k := k) (E := AdjoinRoot p.val)
          (rawMilnorSymbol (AdjoinRoot p.val) (symbol a b)) :=
        zeroCycle_eq_corestriction p A B γ hcop a b ha hb
  exact DFunLike.congr_fun hmaps x

/-- The actual polynomial Milnor K₂ norm intertwines the original raw motivic
symbol and finite corestriction on every element. -/
theorem raw_norm (p : MonicIrreducible k) (x : MilnorK.K2.Group (AdjoinRoot p.val)) :
    rawMilnorSymbol k (polynomialNorm p x) =
      corestriction (k := k) (E := AdjoinRoot p.val) (rawMilnorSymbol (AdjoinRoot p.val) x) := by
  have hall : ∀ n : ℕ, ∀ r : MonicIrreducible k, r.val.natDegree = n →
      ∀ y : MilnorK.K2.Group (AdjoinRoot r.val),
        rawMilnorSymbol k (polynomialNorm r y) =
          corestriction (k := k) (E := AdjoinRoot r.val)
            (rawMilnorSymbol (AdjoinRoot r.val) y) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro r hr y
      by_cases h₁ : r.val.natDegree = 1
      · exact raw_norm_degree_one r h₁ y
      · have hn : 1 < r.val.natDegree := by
          have := r.property.2.natDegree_pos
          omega
        exact raw_norm_degree_step r hn
          (fun s hs z => ih s.val.natDegree (by omega) s rfl z) y
  exact hall p.val.natDegree p rfl x

/-- The comparison is also an equality of the two original additive maps. -/
theorem raw_norm_square (p : MonicIrreducible k) :
    (rawMilnorSymbol k).comp (polynomialNorm p).toAddMonoidHom =
      (corestriction (k := k) (E := AdjoinRoot p.val)).comp (rawMilnorSymbol (AdjoinRoot p.val)) :=
  AddMonoidHom.ext (raw_norm p)

variable (p : MonicIrreducible k)
variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of (AdjoinRoot p.val)))) AddCommGrpCat.{u + 1})]

/-- The full comparison in the originally defined derived integral group. -/
theorem derived_norm (x : MilnorK.K2.Group (AdjoinRoot p.val)) :
    motivicMilnorSymbol k (polynomialNorm p x) =
      motivicCorestriction (k := k) (motivicMilnorSymbol (AdjoinRoot p.val) x) := by
  apply (motivicRawBaseEvaluationComparison k 2 2).injective
  rw [motivicMilnorSymbol_comparison, motivicCorestriction_comparison,
    motivicMilnorSymbol_comparison, raw_norm]

/-- Original coefficient reduction preserves the full comparison for every
natural coefficient level, including zero, one, and composite levels. -/
theorem finite_norm (n : ℕ) (x : MilnorK.K2.Group (AdjoinRoot p.val)) :
    finiteMilnorSymbol k n (polynomialNorm p x) =
      finiteCorestriction (k := k) n (finiteMilnorSymbol (AdjoinRoot p.val) n x) := by
  change motivicBaseIntegralReduction k 2 2 n (motivicMilnorSymbol k _) =
    finiteCorestriction (k := k) n
      (motivicBaseIntegralReduction (AdjoinRoot p.val) 2 2 n (motivicMilnorSymbol _ _))
  rw [finiteCorestriction_integralReduction, derived_norm]

end Motivic.WeightTwoMilnorNormComparison
