/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightTwo.CubicBoundary
public import Motivic.Aglib.RingTheory.AdjoinRoot.SimpleFactorLocalization

/-!
# Rational branches of the actual two-unit polynomial cycle

The whole monic quotient maps by its original root and its complement. When
each maximal quotient's root is a specified ground-field scalar, its literal
image is the corresponding rational pair graph. The coefficients are the
original localized ring lengths, including all nilpotent multiplicities.
No separability, distinctness, or Steinberg relation is assumed or asserted.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open Polynomial.TwoUnitPolynomialFamily
open scoped BigOperators

universe u

namespace Motivic.WeightTwoSplitPolynomialCycle
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Hom

open _root_.AlgebraicGeometry.Scheme.FiniteAlgebra
open _root_.Motivic.WeightOneFundamentalNorm
open WeightTwoCubicBoundary
open WeightTwoSymbols

variable {k : Type u} [Field k]

/-- The field structure on `R ⧸ q.asIdeal` supplied by maximality of `q`. -/
local instance quotientField {R : Type u} [CommRing R] (q : MaximalSpectrum R) :
    Field (R ⧸ q.asIdeal) := Ideal.Quotient.field q.asIdeal

/-- The affine two-unit map is precisely the existing rational pair map. -/
theorem pairMap_eq_rationalPair (a b : kˣ) :
    pairMap (RingHom.id k) a b = (rationalPair k a b).left := by
  apply pair_hom_ext
  · rw [pairMap_first]
    exact (congrArg (fun f => f.left)
      (SmoothSite.torusPowerLift_coordinate (.of k) 2
        ![WeightOnePointNorm.rationalTorusPoint k a,
          WeightOnePointNorm.rationalTorusPoint k b] 0)).symm
  · rw [pairMap_second]
    exact (congrArg (fun f => f.left)
      (SmoothSite.torusPowerLift_coordinate (.of k) 2
        ![WeightOnePointNorm.rationalTorusPoint k a,
          WeightOnePointNorm.rationalTorusPoint k b] 1)).symm

/-- Both original quotient coordinates agree with the specified scalar pair. -/
theorem polynomialQuotient_target (p : k[X])
    (h0 : IsUnit (p.eval 0)) (h1 : IsUnit (p.eval 1))
    (q : MaximalSpectrum (AdjoinRoot p)) (a b : kˣ)
    (ha : Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root p) =
      algebraMap k (AdjoinRoot p ⧸ q.asIdeal) (a : k))
    (hb : (b : k) = 1 - (a : k)) :
    quotientMap q ≫ polynomialTargetMap p h0 h1 =
      Spec.map (CommRingCat.ofHom (algebraMap k (AdjoinRoot p ⧸ q.asIdeal))) ≫
        (rationalPair k a b).left := by
  rw [← pairMap_eq_rationalPair]
  unfold polynomialTargetMap
  rw [pairMap_comp (RingHom.id k) _ (algebraMap k (AdjoinRoot p ⧸ q.asIdeal))
    a b (Units.map (algebraMap k (AdjoinRoot p ⧸ q.asIdeal)) a)
      (Units.map (algebraMap k (AdjoinRoot p ⧸ q.asIdeal)) b) (by ext; rfl) rfl rfl]
  apply pairMap_comp
  · ext; rfl
  · change Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root p) =
      algebraMap k (AdjoinRoot p ⧸ q.asIdeal) (a : k)
    exact ha
  · change Ideal.Quotient.mk q.asIdeal (1 - AdjoinRoot.root p) =
      algebraMap k (AdjoinRoot p ⧸ q.asIdeal) (b : k)
    simp only [map_sub, map_one, hb, ha]

/-- The original rational pair graph is its actual geometric basis vector. -/
theorem graph_eq_single (a b : kˣ) :
    (Cor.graphFunctor k).map (rationalPair k a b) =
      Finsupp.single (graphGeneratorOver (rationalPair k a b).left
        (MorphismProperty.Over.w (rationalPair k a b))) 1 := by
  rw [Cor.graphFunctor_map, componentGraphCycleOver_eq_graphGeneratorOver_cycle]
  rfl

/-- A scalar root identifies the actual entire maximal quotient image with its graph.
The quotient is the ground field by the existing root-generation proof. -/
theorem polynomialQuotient_support (p : k[X]) (hp : p.Monic)
    (h0 : IsUnit (p.eval 0)) (h1 : IsUnit (p.eval 1))
    (q : MaximalSpectrum (AdjoinRoot p)) (a b : kˣ)
    (ha : Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root p) =
      algebraMap k (AdjoinRoot p ⧸ q.asIdeal) (a : k))
    (hb : (b : k) = 1 - (a : k)) :
    (quotientSupport q).finiteImage (polynomialInclusion p h0 h1) =
      (graphGeneratorOver (rationalPair k a b).left
        (MorphismProperty.Over.w (rationalPair k a b))).toIntegralClosedSubscheme := by
  let := hp.finite_adjoinRoot
  let g := graphGeneratorOver (rationalPair k a b).left
    (MorphismProperty.Over.w (rationalPair k a b))
  let s := Spec.map (CommRingCat.ofHom (algebraMap k (AdjoinRoot p ⧸ q.asIdeal)))
  have : IsIso (CommRingCat.ofHom (algebraMap k (AdjoinRoot p ⧸ q.asIdeal))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨(algebraMap k (AdjoinRoot p ⧸ q.asIdeal)).injective,
        WeightOneSplitPolynomialCycle.quotient_scalar_surjective p q (a : k) ha⟩
  have : IsIso s := by dsimp only [s]; infer_instance
  have hj : quotientMap q ≫ polynomialInclusion p h0 h1 =
      (s ≫ inv g.projection) ≫ g.inclusion := by
    apply pullback.hom_ext
    · change _ = (s ≫ inv g.projection) ≫ g.projection
      rw [Category.assoc, polynomialInclusion_fst, Category.assoc, IsIso.inv_hom_id,
        Category.comp_id]
      change Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp]
      rfl
    · change _ = (s ≫ inv g.projection) ≫ g.targetProjection
      rw [Category.assoc, polynomialInclusion_snd,
        ← graphGeneratorOver_projection_target, Category.assoc,
        IsIso.inv_hom_id_assoc]
      exact polynomialQuotient_target p h0 h1 q a b ha hb
  have hsupport : (quotientSupport q).finiteImage (polynomialInclusion p h0 h1) =
      ⟨(quotientMap q ≫ polynomialInclusion p h0 h1).ker,
        IsIntegral.of_isIso (quotientMap q ≫ polynomialInclusion p h0 h1).toImage⟩ := by
    apply IntegralClosedSubscheme.point_injective
    rw [IntegralClosedSubscheme.point_finiteImage, quotientSupport_point]
    exact (imageι_genericPoint (quotientMap q ≫ polynomialInclusion p h0 h1)).trans
      (by rw [Scheme.Hom.comp_apply, quotientMap_genericPoint]) |>.symm
  rw [hsupport]
  apply Subtype.ext
  change (quotientMap q ≫ polynomialInclusion p h0 h1).ker = g.val
  rw [hj, Scheme.Hom.ker_comp_of_isIso]
  exact g.val.ker_subschemeι

/-- The full original two-coordinate polynomial cycle is its rational graph sum,
weighted by every original local length. -/
theorem polynomialCycle_eq_sum_graph (p : k[X]) (hp : p.Monic)
    (h0 : IsUnit (p.eval 0)) (h1 : IsUnit (p.eval 1))
    (a b : MaximalSpectrum (AdjoinRoot p) → kˣ)
    (ha : ∀ q, Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root p) =
      algebraMap k (AdjoinRoot p ⧸ q.asIdeal) (a q : k))
    (hb : ∀ q, (b q : k) = 1 - (a q : k)) :
    letI := hp.finite_adjoinRoot
    letI : IsArtinianRing (AdjoinRoot p) := .of_finite k _
    letI : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
    polynomialCycle p hp h0 h1 = ∑ q : MaximalSpectrum (AdjoinRoot p),
      ((Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal)).toNat : ℤ) •
        (Cor.graphFunctor k).map (rationalPair k (a q) (b q)) := by
  classical
  let := hp.finite_adjoinRoot
  let : IsArtinianRing (AdjoinRoot p) := .of_finite k _
  let : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
  apply FiniteCorrespondence.toIntegralCycle_injective
  rw [toIntegralCycle_polynomialCycle, fundamentalCycle_affine_eq_sum (k := k), map_sum,
    map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [IntegralCycle.finitePushforward_single, residueDegree_of_surjectiveOnStalks,
    Nat.cast_one, mul_one, polynomialQuotient_support p hp h0 h1 q (a q) (b q) (ha q) (hb q),
    map_zsmul, graph_eq_single, FiniteCorrespondence.toIntegralCycle_single,
    Finsupp.smul_single]
  simp

/-- Coalescing all residual roots preserves the full degree as the graph multiplicity. -/
theorem polynomialCycle_eq_degree_smul_graph (p : k[X]) (hp : p.Monic)
    (h0 : IsUnit (p.eval 0)) (h1 : IsUnit (p.eval 1)) (a b : kˣ)
    (ha : ∀ q : MaximalSpectrum (AdjoinRoot p),
      Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root p) =
        algebraMap k (AdjoinRoot p ⧸ q.asIdeal) (a : k))
    (hb : (b : k) = 1 - (a : k)) :
    polynomialCycle p hp h0 h1 = (p.natDegree : ℤ) •
      (Cor.graphFunctor k).map (rationalPair k a b) := by
  classical
  let := hp.finite_adjoinRoot
  let : IsArtinianRing (AdjoinRoot p) := .of_finite k _
  let : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
  rw [polynomialCycle_eq_sum_graph p hp h0 h1 (fun _ => a) (fun _ => b) ha (fun _ => hb),
    ← Finset.sum_smul, ← Nat.cast_sum,
    WeightOneSplitPolynomialCycle.sum_local_length_eq_natDegree p hp (fun q => ⟨a, ha q⟩)]

/-- A doubled unit root retains its nonreduced multiplicity in the actual pair cycle. -/
theorem polynomialCycle_double_root (a b : kˣ)
    (h0 : IsUnit (((X - C (a : k)) * (X - C (a : k))).eval 0))
    (h1 : IsUnit (((X - C (a : k)) * (X - C (a : k))).eval 1))
    (hb : (b : k) = 1 - (a : k)) :
    polynomialCycle ((X - C (a : k)) * (X - C (a : k)))
      (WeightOneSplitPolynomialCycle.twoLinear_monic a a) h0 h1 =
        (2 : ℤ) • (Cor.graphFunctor k).map (rationalPair k a b) := by
  have hr (q : MaximalSpectrum
      (AdjoinRoot ((X - C (a : k)) * (X - C (a : k))))) :=
    (WeightOneSplitPolynomialCycle.twoLinear_residual_root a a q).elim id id
  simpa only [WeightOneSplitPolynomialCycle.twoLinear_natDegree, Nat.cast_ofNat] using
    polynomialCycle_eq_degree_smul_graph _ _ h0 h1 a b hr hb

/-- Passing the actual graph decomposition to raw homology keeps its local lengths. -/
theorem cycleClass_polynomialCycle_eq_sum_graphSymbol (p : k[X]) (hp : p.Monic)
    (h0 : IsUnit (p.eval 0)) (h1 : IsUnit (p.eval 1))
    (a b : MaximalSpectrum (AdjoinRoot p) → kˣ)
    (ha : ∀ q, Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root p) =
      algebraMap k (AdjoinRoot p ⧸ q.asIdeal) (a q : k))
    (hb : ∀ q, (b q : k) = 1 - (a q : k)) :
    letI := hp.finite_adjoinRoot
    letI : IsArtinianRing (AdjoinRoot p) := .of_finite k _
    letI : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
    cycleClass k (polynomialCycle p hp h0 h1) = ∑ q : MaximalSpectrum (AdjoinRoot p),
      ((Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal)).toNat : ℤ) • graphSymbol k (a q) (b q) := by
  classical
  let := hp.finite_adjoinRoot
  let : IsArtinianRing (AdjoinRoot p) := .of_finite k _
  let : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
  rw [polynomialCycle_eq_sum_graph p hp h0 h1 a b ha hb, map_sum]
  simp only [map_zsmul, graphSymbol]

/-- A degree-three quotient with two scalar roots and one simple original branch
has coefficients one and two, including the nonreduced remaining branch. -/
theorem polynomialCycle_twoRoots_degree_three (p : k[X]) (hp : p.Monic)
    (h0 : IsUnit (p.eval 0)) (h1 : IsUnit (p.eval 1)) (hd : p.natDegree = 3)
    (a a' b b' : kˣ) (ha' : (a' : k) = 1 - (a : k)) (hb' : (b' : k) = 1 - (b : k))
    (hroots : ∀ q : MaximalSpectrum (AdjoinRoot p),
      Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root p) =
          algebraMap k (AdjoinRoot p ⧸ q.asIdeal) a ∨
        Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root p) =
          algebraMap k (AdjoinRoot p ⧸ q.asIdeal) b)
    (q₀ : MaximalSpectrum (AdjoinRoot p))
    (hq₀ : Ideal.Quotient.mk q₀.asIdeal (AdjoinRoot.root p) =
      algebraMap k (AdjoinRoot p ⧸ q₀.asIdeal) a)
    (hlength : Module.length (Localization.AtPrime q₀.asIdeal)
      (Localization.AtPrime q₀.asIdeal) = 1) :
    polynomialCycle p hp h0 h1 = (Cor.graphFunctor k).map (rationalPair k a a') +
      (2 : ℤ) • (Cor.graphFunctor k).map (rationalPair k b b') := by
  classical
  let := hp.finite_adjoinRoot
  let : IsArtinianRing (AdjoinRoot p) := .of_finite k _
  let : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
  let roots : MaximalSpectrum (AdjoinRoot p) → kˣ := fun q => if q = q₀ then a else b
  let complements : MaximalSpectrum (AdjoinRoot p) → kˣ :=
    fun q => if q = q₀ then a' else b'
  have hroot (q : MaximalSpectrum (AdjoinRoot p)) :
      Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root p) =
        algebraMap k (AdjoinRoot p ⧸ q.asIdeal) (roots q : k) := by
    by_cases hq : q = q₀
    · subst q
      simpa only [roots, ite_eq_left rfl] using hq₀
    · rcases hroots q with h | h
      · exact (hq (WeightOneSplitPolynomialCycle.maximal_eq_of_root_eq p q q₀ a h hq₀)).elim
      · simpa only [roots, ite_eq_right hq] using h
  have hcomplement (q : MaximalSpectrum (AdjoinRoot p)) :
      (complements q : k) = 1 - (roots q : k) := by
    dsimp only [complements, roots]
    split_ifs <;> assumption
  let lengths (q : MaximalSpectrum (AdjoinRoot p)) : ℕ :=
    (Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal)).toNat
  have hzero : lengths q₀ = 1 := congrArg ENat.toNat hlength
  have htotal : ∑ q : MaximalSpectrum (AdjoinRoot p), lengths q = 3 := by
    change ∑ q : MaximalSpectrum (AdjoinRoot p),
      (Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal)).toNat = _
    rw [WeightOneSplitPolynomialCycle.sum_local_length_eq_natDegree p hp
      (fun q => ⟨roots q, hroot q⟩), hd]
  have hrest : ∑ q ∈ Finset.univ.erase q₀, lengths q = 2 := by
    have h := Finset.add_sum_erase Finset.univ lengths (Finset.mem_univ q₀)
    rw [hzero, htotal] at h
    omega
  rw [polynomialCycle_eq_sum_graph p hp h0 h1 roots complements hroot hcomplement]
  change (∑ q : MaximalSpectrum (AdjoinRoot p),
    (lengths q : ℤ) • (Cor.graphFunctor k).map (rationalPair k (roots q) (complements q))) = _
  rw [← Finset.add_sum_erase Finset.univ
    (fun q => (lengths q : ℤ) •
      (Cor.graphFunctor k).map (rationalPair k (roots q) (complements q))) (Finset.mem_univ q₀)]
  simp only [hzero, Nat.cast_one, one_zsmul, roots, complements, ite_eq_left rfl]
  congr 1
  calc
    _ = ∑ q ∈ Finset.univ.erase q₀,
        (lengths q : ℤ) • (Cor.graphFunctor k).map (rationalPair k b b') := by
      apply Finset.sum_congr rfl
      intro q hq
      simp only [ite_eq_right (Finset.mem_erase.mp hq).1]
    _ = _ := by rw [← Finset.sum_smul, ← Nat.cast_sum, hrest, Nat.cast_ofNat]

/-- Two simple original branches and the total degree determine all three graph
coefficients; the assertion is about the entire polynomial correspondence. -/
theorem polynomialCycle_threeRoots_of_local_length (p : k[X]) (hp : p.Monic)
    (h0 : IsUnit (p.eval 0)) (h1 : IsUnit (p.eval 1)) (hd : p.natDegree = 3)
    (a a' b b' c c' : kˣ)
    (ha' : (a' : k) = 1 - (a : k)) (hb' : (b' : k) = 1 - (b : k))
    (hc' : (c' : k) = 1 - (c : k))
    (hroots : ∀ q : MaximalSpectrum (AdjoinRoot p),
      Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root p) =
          algebraMap k (AdjoinRoot p ⧸ q.asIdeal) a ∨
        Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root p) =
          algebraMap k (AdjoinRoot p ⧸ q.asIdeal) b ∨
        Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root p) =
          algebraMap k (AdjoinRoot p ⧸ q.asIdeal) c)
    (q₀ q₁ : MaximalSpectrum (AdjoinRoot p)) (hq01 : q₀ ≠ q₁)
    (hq₀ : Ideal.Quotient.mk q₀.asIdeal (AdjoinRoot.root p) =
      algebraMap k (AdjoinRoot p ⧸ q₀.asIdeal) a)
    (hq₁ : Ideal.Quotient.mk q₁.asIdeal (AdjoinRoot.root p) =
      algebraMap k (AdjoinRoot p ⧸ q₁.asIdeal) b)
    (hlength₀ : Module.length (Localization.AtPrime q₀.asIdeal)
      (Localization.AtPrime q₀.asIdeal) = 1)
    (hlength₁ : Module.length (Localization.AtPrime q₁.asIdeal)
      (Localization.AtPrime q₁.asIdeal) = 1) :
    polynomialCycle p hp h0 h1 = (Cor.graphFunctor k).map (rationalPair k a a') +
      (Cor.graphFunctor k).map (rationalPair k b b') +
      (Cor.graphFunctor k).map (rationalPair k c c') := by
  classical
  let := hp.finite_adjoinRoot
  let : IsArtinianRing (AdjoinRoot p) := .of_finite k _
  let : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
  let roots : MaximalSpectrum (AdjoinRoot p) → kˣ :=
    fun q => if q = q₀ then a else if q = q₁ then b else c
  let complements : MaximalSpectrum (AdjoinRoot p) → kˣ :=
    fun q => if q = q₀ then a' else if q = q₁ then b' else c'
  have hroot (q : MaximalSpectrum (AdjoinRoot p)) :
      Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root p) =
        algebraMap k (AdjoinRoot p ⧸ q.asIdeal) (roots q : k) := by
    by_cases hq0 : q = q₀
    · subst q
      simpa only [roots, ite_eq_left rfl] using hq₀
    by_cases hq1 : q = q₁
    · subst q
      simpa [roots, hq0] using hq₁
    rcases hroots q with h | h | h
    · exact (hq0 (WeightOneSplitPolynomialCycle.maximal_eq_of_root_eq p q q₀ a h hq₀)).elim
    · exact (hq1 (WeightOneSplitPolynomialCycle.maximal_eq_of_root_eq p q q₁ b h hq₁)).elim
    · simpa only [roots, ite_eq_right hq0, ite_eq_right hq1] using h
  have hcomplement (q : MaximalSpectrum (AdjoinRoot p)) :
      (complements q : k) = 1 - (roots q : k) := by
    dsimp only [complements, roots]
    split_ifs <;> assumption
  let lengths (q : MaximalSpectrum (AdjoinRoot p)) : ℕ :=
    (Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal)).toNat
  have hzero : lengths q₀ = 1 := congrArg ENat.toNat hlength₀
  have hone : lengths q₁ = 1 := congrArg ENat.toNat hlength₁
  have htotal : ∑ q : MaximalSpectrum (AdjoinRoot p), lengths q = 3 := by
    change ∑ q : MaximalSpectrum (AdjoinRoot p),
      (Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal)).toNat = _
    rw [WeightOneSplitPolynomialCycle.sum_local_length_eq_natDegree p hp
      (fun q => ⟨roots q, hroot q⟩), hd]
  have hq1mem : q₁ ∈ Finset.univ.erase q₀ :=
    Finset.mem_erase.mpr ⟨Ne.symm hq01, Finset.mem_univ _⟩
  have hrest : ∑ q ∈ (Finset.univ.erase q₀).erase q₁, lengths q = 1 := by
    have h := Finset.add_sum_erase Finset.univ lengths (Finset.mem_univ q₀)
    have h' := Finset.add_sum_erase (Finset.univ.erase q₀) lengths hq1mem
    rw [hzero, htotal] at h
    rw [hone] at h'
    omega
  rw [polynomialCycle_eq_sum_graph p hp h0 h1 roots complements hroot hcomplement]
  change (∑ q : MaximalSpectrum (AdjoinRoot p),
    (lengths q : ℤ) • (Cor.graphFunctor k).map (rationalPair k (roots q) (complements q))) = _
  rw [← Finset.add_sum_erase Finset.univ
    (fun q => (lengths q : ℤ) •
      (Cor.graphFunctor k).map (rationalPair k (roots q) (complements q))) (Finset.mem_univ q₀),
    ← Finset.add_sum_erase (Finset.univ.erase q₀)
      (fun q => (lengths q : ℤ) •
        (Cor.graphFunctor k).map (rationalPair k (roots q) (complements q))) hq1mem]
  simp only [hzero, hone, Nat.cast_one, one_zsmul, roots, complements,
    ite_eq_left rfl, ite_eq_right (Ne.symm hq01)]
  rw [add_assoc]
  congr 2
  calc
    _ = ∑ q ∈ (Finset.univ.erase q₀).erase q₁,
        (lengths q : ℤ) • (Cor.graphFunctor k).map (rationalPair k c c') := by
      apply Finset.sum_congr rfl
      intro q hq
      simp only [ite_eq_right (Finset.mem_erase.mp (Finset.mem_erase.mp hq).2).1,
        ite_eq_right (Finset.mem_erase.mp hq).1]
    _ = _ := by rw [← Finset.sum_smul, ← Nat.cast_sum, hrest, Nat.cast_one, one_zsmul]

/-- The whole product of three linear factors is the sum of its three literal
pair graphs, in every characteristic and with arbitrary root collisions. -/
theorem polynomialCycle_threeLinear (a a' b b' c c' : kˣ)
    (h0 : IsUnit (((X - C (a : k)) * (X - C (b : k)) * (X - C (c : k))).eval 0))
    (h1 : IsUnit (((X - C (a : k)) * (X - C (b : k)) * (X - C (c : k))).eval 1))
    (ha' : (a' : k) = 1 - (a : k)) (hb' : (b' : k) = 1 - (b : k))
    (hc' : (c' : k) = 1 - (c : k)) :
    polynomialCycle ((X - C (a : k)) * (X - C (b : k)) * (X - C (c : k)))
      (AdjoinRoot.three_linear_monic (a : k) b c) h0 h1 =
        (Cor.graphFunctor k).map (rationalPair k a a') +
          (Cor.graphFunctor k).map (rationalPair k b b') +
          (Cor.graphFunctor k).map (rationalPair k c c') := by
  let p : k[X] := (X - C (a : k)) * (X - C (b : k)) * (X - C (c : k))
  have hp : p.Monic := AdjoinRoot.three_linear_monic (a : k) b c
  have hd : p.natDegree = 3 := AdjoinRoot.three_linear_natDegree (a : k) b c
  have hroots := AdjoinRoot.three_linear_residual_root (a : k) b c
  have hsimple (x y z : kˣ) (hfact : p = (X - C (x : k)) * (X - C (y : k)) * (X - C (z : k)))
      (hxy : x ≠ y) (hxz : x ≠ z) (q : MaximalSpectrum (AdjoinRoot p))
      (hq : Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root p) =
        algebraMap k (AdjoinRoot p ⧸ q.asIdeal) x) :
      Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) = 1 := by
    apply AdjoinRoot.simple_factor_local_length (x : k)
      (hfact.trans (mul_assoc _ _ _)) q hq
    simp only [eval_mul, eval_sub, eval_X, eval_C]
    exact mul_ne_zero (sub_ne_zero.mpr (fun h => hxy (Units.ext h)))
      (sub_ne_zero.mpr (fun h => hxz (Units.ext h)))
  change polynomialCycle p hp h0 h1 = _
  by_cases hab : a = b
  · subst b
    have hb'a' : b' = a' := Units.ext (hb'.trans ha'.symm)
    subst b'
    by_cases hac : a = c
    · subst c
      have hc'a' : c' = a' := Units.ext (hc'.trans ha'.symm)
      subst c'
      have hr (q : MaximalSpectrum (AdjoinRoot p)) :
          Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root p) =
            algebraMap k (AdjoinRoot p ⧸ q.asIdeal) a := by
        rcases hroots q with h | h | h <;> exact h
      rw [polynomialCycle_eq_degree_smul_graph p hp h0 h1 a a' hr ha', hd]
      norm_num only [Nat.cast_ofNat]
      abel
    · have hpc : p.eval (c : k) = 0 := by simp [p]
      let q := WeightOneSplitPolynomialCycle.scalarMaximal p (c : k) hpc
      have hq := WeightOneSplitPolynomialCycle.scalarMaximal_root p (c : k) hpc
      have hr (q : MaximalSpectrum (AdjoinRoot p)) :
          Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root p) =
              algebraMap k (AdjoinRoot p ⧸ q.asIdeal) c ∨
            Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root p) =
              algebraMap k (AdjoinRoot p ⧸ q.asIdeal) a := by
        rcases hroots q with h | h | h
        · exact Or.inr h
        · exact Or.inr h
        · exact Or.inl h
      rw [polynomialCycle_twoRoots_degree_three p hp h0 h1 hd c c' a a' hc' ha'
        hr q hq (hsimple c a a (by dsimp only [p]; ring) (Ne.symm hac) (Ne.symm hac) q hq)]
      abel
  by_cases hac : a = c
  · subst c
    have hc'a' : c' = a' := Units.ext (hc'.trans ha'.symm)
    subst c'
    have hpb : p.eval (b : k) = 0 := by simp [p]
    let q := WeightOneSplitPolynomialCycle.scalarMaximal p (b : k) hpb
    have hq := WeightOneSplitPolynomialCycle.scalarMaximal_root p (b : k) hpb
    have hr (q : MaximalSpectrum (AdjoinRoot p)) :
        Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root p) =
            algebraMap k (AdjoinRoot p ⧸ q.asIdeal) b ∨
          Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root p) =
            algebraMap k (AdjoinRoot p ⧸ q.asIdeal) a := by
      rcases hroots q with h | h | h
      · exact Or.inr h
      · exact Or.inl h
      · exact Or.inr h
    rw [polynomialCycle_twoRoots_degree_three p hp h0 h1 hd b b' a a' hb' ha'
      hr q hq (hsimple b a a (by dsimp only [p]; ring) (Ne.symm hab) (Ne.symm hab) q hq)]
    abel
  by_cases hbc : b = c
  · subst c
    have hc'b' : c' = b' := Units.ext (hc'.trans hb'.symm)
    subst c'
    have hpa : p.eval (a : k) = 0 := by simp [p]
    let q := WeightOneSplitPolynomialCycle.scalarMaximal p (a : k) hpa
    have hq := WeightOneSplitPolynomialCycle.scalarMaximal_root p (a : k) hpa
    have hr (q : MaximalSpectrum (AdjoinRoot p)) :
        Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root p) =
            algebraMap k (AdjoinRoot p ⧸ q.asIdeal) a ∨
          Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root p) =
            algebraMap k (AdjoinRoot p ⧸ q.asIdeal) b := by
      rcases hroots q with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact Or.inr h
    rw [polynomialCycle_twoRoots_degree_three p hp h0 h1 hd a a' b b' ha' hb'
      hr q hq (hsimple a b b rfl hab hab q hq)]
    abel
  have hpa : p.eval (a : k) = 0 := by simp [p]
  have hpb : p.eval (b : k) = 0 := by simp [p]
  let q₀ := WeightOneSplitPolynomialCycle.scalarMaximal p (a : k) hpa
  let q₁ := WeightOneSplitPolynomialCycle.scalarMaximal p (b : k) hpb
  have hq₀ := WeightOneSplitPolynomialCycle.scalarMaximal_root p (a : k) hpa
  have hq₁ := WeightOneSplitPolynomialCycle.scalarMaximal_root p (b : k) hpb
  have hq01 : q₀ ≠ q₁ := by
    intro h
    have hq₀' : Ideal.Quotient.mk q₁.asIdeal (AdjoinRoot.root p) =
        algebraMap k (AdjoinRoot p ⧸ q₁.asIdeal) a := h ▸ hq₀
    exact hab (Units.ext ((algebraMap k (AdjoinRoot p ⧸ q₁.asIdeal)).injective
      (hq₀'.symm.trans hq₁)))
  exact polynomialCycle_threeRoots_of_local_length p hp h0 h1 hd a a' b b' c c'
    ha' hb' hc' hroots q₀ q₁ hq01 hq₀ hq₁
    (hsimple a b c rfl hab hac q₀ hq₀)
    (hsimple b a c (by dsimp only [p]; ring) (Ne.symm hab) hbc q₁ hq₁)

/-- A specified three-linear factorization decomposes the original whole quotient
without changing its polynomial presentation or losing coincident-root lengths. -/
theorem polynomialCycle_eq_three_graph_of_factorization (p : k[X]) (hp : p.Monic)
    (h0 : IsUnit (p.eval 0)) (h1 : IsUnit (p.eval 1)) (a a' b b' c c' : kˣ)
    (hfactor : p = (X - C (a : k)) * (X - C (b : k)) * (X - C (c : k)))
    (ha' : (a' : k) = 1 - (a : k)) (hb' : (b' : k) = 1 - (b : k))
    (hc' : (c' : k) = 1 - (c : k)) :
    polynomialCycle p hp h0 h1 = (Cor.graphFunctor k).map (rationalPair k a a') +
      (Cor.graphFunctor k).map (rationalPair k b b') +
      (Cor.graphFunctor k).map (rationalPair k c c') := by
  subst p
  exact polynomialCycle_threeLinear a a' b b' c c' h0 h1 ha' hb' hc'

/-- The literal three-factor decomposition gives the corresponding three actual
raw graph-symbol classes, also when factors coincide. -/
theorem cycleClass_eq_three_graphSymbol_of_factorization (p : k[X]) (hp : p.Monic)
    (h0 : IsUnit (p.eval 0)) (h1 : IsUnit (p.eval 1)) (a a' b b' c c' : kˣ)
    (hfactor : p = (X - C (a : k)) * (X - C (b : k)) * (X - C (c : k)))
    (ha' : (a' : k) = 1 - (a : k)) (hb' : (b' : k) = 1 - (b : k))
    (hc' : (c' : k) = 1 - (c : k)) :
    cycleClass k (polynomialCycle p hp h0 h1) =
      graphSymbol k a a' + graphSymbol k b b' + graphSymbol k c c' := by
  rw [polynomialCycle_eq_three_graph_of_factorization p hp h0 h1 a a' b b' c c'
    hfactor ha' hb' hc', map_add, map_add]
  rfl

/-- The full `X³-a³` endpoint decomposes under explicit scalar-root hypotheses. -/
theorem zeroCycle_eq_sum_graph (a : k) (ha : a ≠ 0) (ha3 : a ^ 3 ≠ 1)
    (r s : MaximalSpectrum (AdjoinRoot (cubicZero a)) → kˣ)
    (hr : ∀ q, Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root (cubicZero a)) =
      algebraMap k (AdjoinRoot (cubicZero a) ⧸ q.asIdeal) (r q : k))
    (hs : ∀ q, (s q : k) = 1 - (r q : k)) :
    letI := (cubicZero_monic a).finite_adjoinRoot
    letI : IsArtinianRing (AdjoinRoot (cubicZero a)) := .of_finite k _
    letI : Fintype (MaximalSpectrum (AdjoinRoot (cubicZero a))) := Fintype.ofFinite _
    zeroCycle a ha ha3 = ∑ q : MaximalSpectrum (AdjoinRoot (cubicZero a)),
      ((Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal)).toNat : ℤ) •
        (Cor.graphFunctor k).map (rationalPair k (r q) (s q)) :=
  polynomialCycle_eq_sum_graph _ _ _ _ r s hr hs

/-- The full `(X-a³)(X²-X+1)` endpoint keeps both factors and every repeated-root length. -/
theorem oneCycle_eq_sum_graph (a : k) (ha : a ≠ 0) (ha3 : a ^ 3 ≠ 1)
    (r s : MaximalSpectrum (AdjoinRoot (cubicOne a)) → kˣ)
    (hr : ∀ q, Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root (cubicOne a)) =
      algebraMap k (AdjoinRoot (cubicOne a) ⧸ q.asIdeal) (r q : k))
    (hs : ∀ q, (s q : k) = 1 - (r q : k)) :
    letI := (cubicOne_monic a).finite_adjoinRoot
    letI : IsArtinianRing (AdjoinRoot (cubicOne a)) := .of_finite k _
    letI : Fintype (MaximalSpectrum (AdjoinRoot (cubicOne a))) := Fintype.ofFinite _
    oneCycle a ha ha3 = ∑ q : MaximalSpectrum (AdjoinRoot (cubicOne a)),
      ((Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal)).toNat : ℤ) •
        (Cor.graphFunctor k).map (rationalPair k (r q) (s q)) :=
  polynomialCycle_eq_sum_graph _ _ _ _ r s hr hs

/-- The actual cubic boundary becomes an equality of length-weighted graph-symbol sums.
The root assignments are explicit; no splitting or separability is silently inferred. -/
theorem cubic_graphSymbol_relation (a : k) (ha : a ≠ 0) (ha3 : a ^ 3 ≠ 1)
    (r₀ s₀ : MaximalSpectrum (AdjoinRoot (cubicZero a)) → kˣ)
    (r₁ s₁ : MaximalSpectrum (AdjoinRoot (cubicOne a)) → kˣ)
    (hr₀ : ∀ q, Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root (cubicZero a)) =
      algebraMap k (AdjoinRoot (cubicZero a) ⧸ q.asIdeal) (r₀ q : k))
    (hs₀ : ∀ q, (s₀ q : k) = 1 - (r₀ q : k))
    (hr₁ : ∀ q, Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root (cubicOne a)) =
      algebraMap k (AdjoinRoot (cubicOne a) ⧸ q.asIdeal) (r₁ q : k))
    (hs₁ : ∀ q, (s₁ q : k) = 1 - (r₁ q : k)) :
    letI := (cubicZero_monic a).finite_adjoinRoot
    letI := (cubicOne_monic a).finite_adjoinRoot
    letI : IsArtinianRing (AdjoinRoot (cubicZero a)) := .of_finite k _
    letI : IsArtinianRing (AdjoinRoot (cubicOne a)) := .of_finite k _
    letI : Fintype (MaximalSpectrum (AdjoinRoot (cubicZero a))) := Fintype.ofFinite _
    letI : Fintype (MaximalSpectrum (AdjoinRoot (cubicOne a))) := Fintype.ofFinite _
    (∑ q : MaximalSpectrum (AdjoinRoot (cubicZero a)),
      ((Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal)).toNat : ℤ) • graphSymbol k (r₀ q) (s₀ q)) =
      ∑ q : MaximalSpectrum (AdjoinRoot (cubicOne a)),
        ((Module.length (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime q.asIdeal)).toNat : ℤ) • graphSymbol k (r₁ q) (s₁ q) := by
  classical
  let := (cubicZero_monic a).finite_adjoinRoot
  let := (cubicOne_monic a).finite_adjoinRoot
  let : IsArtinianRing (AdjoinRoot (cubicZero a)) := .of_finite k _
  let : IsArtinianRing (AdjoinRoot (cubicOne a)) := .of_finite k _
  let : Fintype (MaximalSpectrum (AdjoinRoot (cubicZero a))) := Fintype.ofFinite _
  let : Fintype (MaximalSpectrum (AdjoinRoot (cubicOne a))) := Fintype.ofFinite _
  have h := cubic_cycleClass_endpoints a ha ha3
  rw [zeroCycle_eq_sum_graph a ha ha3 r₀ s₀ hr₀ hs₀,
    oneCycle_eq_sum_graph a ha ha3 r₁ s₁ hr₁ hs₁] at h
  simpa only [map_sum, map_zsmul, graphSymbol] using h

end Motivic.WeightTwoSplitPolynomialCycle
