/-
Copyright (c) 2025 Sihan Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Sihan Su, Wan Lin, Xiaoyang Su
-/
module
public import Motivic.Aglib.RingTheory.NoetherNormalizationFirstJets

/-! # Parameterized finite-coordinate changes

For every nonzero ground-field parameter the same triangular coordinate change
has the degree separation needed for finite elimination. At parameter zero it
is the identity, allowing simultaneous open rank conditions to be imposed later.
-/
@[expose] public noncomputable section
open Polynomial MvPolynomial Ideal Nat RingHom List
universe u
namespace ParameterizedNoetherNormalization
variable {k : Type u} [Field k] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) k)
variable (v w : Fin (n + 1) →₀ ℕ)
section equivT

/-- `up` is defined as `2 + f.totalDegree`. Any big enough number would work. -/
local notation3 "up" => 2 + f.totalDegree

variable {f v} in
private lemma lt_up (vlt : ∀ i, v i < up) : ∀ l ∈ ofFn v, l < up := by
  grind

/-- `r` maps `(i : Fin (n + 1))` to `up ^ i`. -/
local notation3 "r" => fun (i : Fin (n + 1)) ↦ up ^ i.1

/-- We construct an algebra map `T1 f c` which maps `X_i` into `X_i + c • X_0 ^ r_i` when `i ≠ 0`
and `X_0` to `X_0`. -/
noncomputable abbrev T1 (c : k) := NoetherNormalization.T1 f c

lemma t1_comp_t1_neg (c : k) : (T1 f c).comp (T1 f (-c)) = AlgHom.id _ _ := by
  rw [comp_aeval, ← MvPolynomial.aeval_X_left]
  ext i v
  cases i using Fin.cases <;> simp

/-- `T1 f 1` leads to an algebra equiv `T f`. -/
noncomputable abbrev coordinateChange (c : k) := AlgEquiv.ofAlgHom (T1 f c) (T1 f (-c))
  (t1_comp_t1_neg f c) (by simpa using t1_comp_t1_neg f (-c))

variable (c : k) (hc : c ≠ 0)

private lemma sum_r_mul_ne (vlt : ∀ i, v i < up) (wlt : ∀ i, w i < up) (ne : v ≠ w) :
    ∑ x : Fin (n + 1), r x * v x ≠ ∑ x : Fin (n + 1), r x * w x := by
  intro h
  refine ne <| Finsupp.ext <| congrFun <| ofFn_inj.mp ?_
  apply ofDigits_inj_of_len_eq (Nat.lt_add_right f.totalDegree one_lt_two)
    (by simp) (lt_up vlt) (lt_up wlt)
  simpa only [ofDigits_eq_sum_mapIdx, mapIdx_eq_ofFn, get_ofFn, length_ofFn,
    Fin.val_cast, mul_comm, sum_ofFn] using! h

include hc in
private lemma degreeOf_zero_t {a : k} (ha : a ≠ 0) :
    ((coordinateChange f c) (monomial v a)).degreeOf 0 =
    ∑ i : Fin (n + 1), (r i) * v i := by
  rw [← natDegree_finSuccEquiv, monomial_eq, Finsupp.prod_pow v fun a ↦ X a]
  simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, map_mul, map_prod, map_pow,
    AlgEquiv.ofAlgHom_apply, MvPolynomial.aeval_C, MvPolynomial.aeval_X, ite_eq_left,
    Fin.succ_ne_zero, ite_false, map_smul, map_add, finSuccEquiv_X_zero, finSuccEquiv_X_succ,
    algebraMap_eq]
  have h (i : Fin n) :
      (Polynomial.C (X (R := k) i) + c • Polynomial.X ^ r i.succ) ^ v i.succ ≠ 0 :=
    pow_ne_zero (v i.succ) (by
      intro he
      have := congrArg Polynomial.natDegree he
      simp [add_comm, Polynomial.natDegree_smul _ hc] at this)
  rw [natDegree_mul (by simp [ha]) (mul_ne_zero (by simp) (Finset.prod_ne_zero_iff.mpr
    (fun i _ ↦ h i))), natDegree_mul (by simp) (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ h i)),
    natDegree_prod _ _ (fun i _ ↦ h i), natDegree_finSuccEquiv, degreeOf_C]
  simpa only [natDegree_pow, zero_add, natDegree_X, mul_one, Fin.val_zero, pow_zero, one_mul,
    add_right_inj] using Finset.sum_congr rfl (fun i _ ↦ by
    rw [add_comm (Polynomial.C _), natDegree_add_C, Polynomial.natDegree_smul _ hc,
      natDegree_pow, natDegree_X, mul_one, mul_comm])

include hc in
/-- Distinct monomials have distinct degrees in the eliminated variable. -/
private lemma degreeOf_t_ne_of_ne (hv : v ∈ f.support) (hw : w ∈ f.support) (ne : v ≠ w) :
    (coordinateChange f c <| monomial v <| f.coeff v).degreeOf 0 ≠
    (coordinateChange f c <| monomial w <| f.coeff w).degreeOf 0 := by
  rw [degreeOf_zero_t _ _ c hc <| mem_support_iff.mp hv,
    degreeOf_zero_t _ _ c hc <| mem_support_iff.mp hw]
  refine sum_r_mul_ne f v w (fun i ↦ ?_) (fun i ↦ ?_) ne <;>
  exact lt_of_le_of_lt ((monomial_le_degreeOf i ‹_›).trans (degreeOf_le_totalDegree f i))
    (by lia)

include hc in
private lemma leadingCoeff_finSuccEquiv_t {v : Fin (n + 1) →₀ ℕ}
    (hv : v ∈ f.support) :
    IsUnit (finSuccEquiv k n <| coordinateChange f c <| monomial v <| f.coeff v).leadingCoeff := by
  rw [monomial_eq, Finsupp.prod_fintype]
  · simp only [map_mul, map_prod, leadingCoeff_mul, leadingCoeff_prod]
    apply IsUnit.mul
    · simpa [coordinateChange, finSuccEquiv_apply] using
        (mem_support_iff.mp hv).isUnit.map (algebraMap k (MvPolynomial (Fin n) k))
    · apply Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one
      intro j _
      simp only [map_pow, leadingCoeff_pow]
      apply IsUnit.pow
      by_cases h : j = 0
      · simp [coordinateChange, h, finSuccEquiv_apply]
      · obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr h
        have hr : 0 < (2 + f.totalDegree) ^ i.succ.val := pow_pos (by omega) _
        simp only [coordinateChange, AlgEquiv.ofAlgHom_apply, aeval_eq_bind₁,
          bind₁_X_right, Fin.succ_ne_zero, ite_false, map_add, map_smul, map_pow,
          finSuccEquiv_X_succ, finSuccEquiv_X_zero]
        rw [leadingCoeff_add_of_degree_lt]
        · simpa [Algebra.smul_def] using hc.isUnit.map (algebraMap k (MvPolynomial (Fin n) k))
        · apply degree_lt_degree
          simp [Polynomial.natDegree_smul _ hc]
  exact fun i ↦ pow_zero _

include hc in
/-- The transformed relation has an invertible leading coefficient. -/
private lemma T_leadingcoeff_isUnit (fne : f ≠ 0) :
    IsUnit (finSuccEquiv k n (coordinateChange f c f)).leadingCoeff := by
  obtain ⟨v, vin, vs⟩ := Finset.exists_max_image f.support
    (fun v ↦ (coordinateChange f c <| monomial v <| f.coeff v).degreeOf 0) 
    (support_nonempty.mpr fne)
  set h := fun w ↦ MvPolynomial.monomial w (f.coeff w)
  simp only [← natDegree_finSuccEquiv] at vs
  replace vs : ∀ x ∈ f.support \ {v}, (finSuccEquiv k n ((coordinateChange f c) (h x))).degree <
      (finSuccEquiv k n ((coordinateChange f c) (h v))).degree := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hx
    apply degree_lt_degree <| lt_of_le_of_ne (vs x h1) ?_
    simpa only [natDegree_finSuccEquiv]
      using degreeOf_t_ne_of_ne f _ _ c hc h1 vin <| ne_of_not_mem_cons h2
  have coeff :
      (finSuccEquiv k n ((coordinateChange f c) (h v + ∑ x ∈ f.support \ {v}, h x))).leadingCoeff =
      (finSuccEquiv k n ((coordinateChange f c) (h v))).leadingCoeff := by
    simp only [map_add, map_sum]
    rw [add_comm]
    apply leadingCoeff_add_of_degree_lt <| (lt_of_le_of_lt <| degree_sum_le _ _) ?_
    have h2 : h v ≠ 0 := by simpa [h] using mem_support_iff.mp vin
    replace h2 : (finSuccEquiv k n ((coordinateChange f c) (h v))) ≠ 0 := fun eq ↦ h2 <|
      by simpa only [map_eq_zero_iff _ (AlgEquiv.injective _)] using eq
    exact (Finset.sup_lt_iff <| Ne.bot_lt (fun x ↦ h2 <| degree_eq_bot.mp x)).mpr vs
  nth_rw 2 [← f.support_sum_monomial_coeff]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem vin h]
  rw [coeff]
  exact leadingCoeff_finSuccEquiv_t f c hc vin

end equivT

/-- Every nonzero parameter gives an actual coordinate automorphism with a unit
leading coefficient for the chosen relation. -/
theorem coordinateChange_unitLeadingCoeff (c : k) (hc : c ≠ 0) (hf : f ≠ 0) :
    IsUnit (finSuccEquiv k n (coordinateChange f c f)).leadingCoeff :=
  T_leadingcoeff_isUnit f c hc hf

/-- The parameter-zero member is the identity, including at nonrational points. -/
@[simp] theorem coordinateChange_zero : coordinateChange f 0 = AlgEquiv.refl := by
  have h : (coordinateChange f 0).toAlgHom = AlgHom.id k _ := by
    apply MvPolynomial.algHom_ext
    intro i
    by_cases hi : i = 0 <;> simp [coordinateChange, hi]
  exact AlgEquiv.ext fun x => DFunLike.congr_fun h x

/-- Monic elimination for every nonzero parameter on the unchanged original ideal. -/
theorem coordinateChange_monicRelation
    (I : Ideal (MvPolynomial (Fin (n + 1)) k)) (c : k) (hc : c ≠ 0)
    (hf : f ≠ 0) (hIf : f ∈ I) :
    ∃ g : (MvPolynomial (Fin n) k)[X], g.Monic ∧
      g ∈ (I.map (coordinateChange f c)).map (finSuccEquiv k n) := by
  have hu := coordinateChange_unitLeadingCoeff f c hc hf
  refine ⟨hu.unit⁻¹.val • finSuccEquiv k n (coordinateChange f c f),
    monic_of_isUnit_leadingCoeff_inv_smul hu, ?_⟩
  exact Submodule.smul_of_tower_mem _ hu.unit⁻¹.val
    (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hIf))

end ParameterizedNoetherNormalization
