/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightOne.InterpolationCycle
public import Mathlib.RingTheory.Polynomial.Quotient
public import Motivic.Aglib.RingTheory.AdjoinRoot.SimpleLocalization

/-!
# Actual cycles of split endpoint polynomials

The full quotient scheme is retained. Its maximal quotients identify the actual
rational graph supports, while the coefficients remain the lengths of the
original local rings.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Polynomial
open scoped BigOperators TensorProduct

universe u

namespace Motivic.WeightOneSplitPolynomialCycle
open _root_.AlgebraicGeometry.Scheme

open WeightOnePointNorm
open _root_.AlgebraicGeometry.Scheme.FiniteAlgebra
open _root_.Motivic.WeightOneFundamentalNorm
open WeightOneInterpolationCycle

variable {k : Type u} [Field k]

/-- The field structure on `R ⧸ q.asIdeal` supplied by maximality of `q`. -/
local instance quotientField {R : Type u} [CommRing R] (q : MaximalSpectrum R) :
    Field (R ⧸ q.asIdeal) := Ideal.Quotient.field q.asIdeal

/-- A branch whose original root becomes a scalar is the literal graph of that scalar. -/
theorem polynomialBranchGenerator_eq_graph (p : k[X]) (hp : p.Monic)
    (h0 : p.coeff 0 ≠ 0) (q : MaximalSpectrum (AdjoinRoot p)) (a : kˣ)
    (ha : Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root p) =
      algebraMap k (AdjoinRoot p ⧸ q.asIdeal) (a : k)) :
    letI := hp.finite_adjoinRoot
    branchGenerator (polynomialInclusion p h0) (polynomialInclusion_fst p h0) q =
      graphSupport (rationalPoint k a) := by
  let := hp.finite_adjoinRoot
  let : IsIntegral (SmoothSite.base (Spec (.of k))).left :=
    inferInstanceAs (IsIntegral (Spec (.of k)))
  let j := quotientMap q ≫ polynomialInclusion p h0
  have htorus : quotientMap q ≫ polynomialTorusMap p h0 =
      Spec.map (CommRingCat.ofHom (algebraMap k (AdjoinRoot p ⧸ q.asIdeal))) ≫
        (rationalTorusPoint k a).left := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    simp only [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply laurentRingHom_ext
    · apply RingHom.ext
      intro r
      change Ideal.Quotient.mk q.asIdeal
          (LaurentPolynomial.eval₂ (AdjoinRoot.of p) (polynomialUnit p h0)
            (LaurentPolynomial.C r)) =
        algebraMap k (AdjoinRoot p ⧸ q.asIdeal)
          (LaurentPolynomial.eval₂ (RingHom.id k) a (LaurentPolynomial.C r))
      simp only [LaurentPolynomial.eval₂_C, RingHom.id_apply]
      rfl
    · change Ideal.Quotient.mk q.asIdeal
          (LaurentPolynomial.eval₂ (AdjoinRoot.of p) (polynomialUnit p h0)
            (LaurentPolynomial.T 1)) =
        algebraMap k (AdjoinRoot p ⧸ q.asIdeal)
          (LaurentPolynomial.eval₂ (RingHom.id k) a (LaurentPolynomial.T 1))
      simpa only [LaurentPolynomial.eval₂_T, zpow_one, polynomialUnit_val] using ha
  have htarget : j ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap k (AdjoinRoot p ⧸ q.asIdeal))) ≫
        (rationalPoint k a).left := by
    have : IsIso (SmoothSite.torusCoordinate (.of k) 1 0).left := by
      change IsIso (SmoothSite.torusPowerOneIso (.of k)).hom.left
      infer_instance
    apply (cancel_mono (SmoothSite.torusCoordinate (.of k) 1 0).left).mp
    have hc : (rationalPoint k a).left ≫
        (SmoothSite.torusCoordinate (.of k) 1 0).left = (rationalTorusPoint k a).left :=
      congrArg (fun f => f.left)
        (SmoothSite.torusPowerLift_coordinate (.of k) 1 (fun _ => rationalTorusPoint k a) 0)
    simpa only [j, Category.assoc, polynomialInclusion_snd,
      polynomialTargetMap_coordinate, hc] using htorus
  apply FiniteCorrespondenceGenerator.eq_of_graph_range_eq
    (rationalPoint k a).left (MorphismProperty.Over.w (rationalPoint k a))
  · apply (cancel_epi j.toImage).mp
    change j.toImage ≫ (fieldGenerator j
      (branch_projection (polynomialInclusion p h0) (polynomialInclusion_fst p h0) q)).projection ≫
        (rationalPoint k a).left = j.toImage ≫ j.imageι ≫ pullback.snd _ _
    rw [fieldGenerator_toImage_projection_assoc, ← Category.assoc,
      Scheme.Hom.toImage_imageι]
    exact htarget.symm
  · exact graphGeneratorOver_projection_target _ _
  · rw [Set.range_eq_univ.mpr (FiniteCorrespondenceGenerator.projection_surjective _),
      Set.range_eq_univ.mpr (FiniteCorrespondenceGenerator.projection_surjective _)]

/-- A scalar root makes the entire maximal quotient its original ground field. -/
theorem quotient_scalar_surjective (p : k[X]) (q : MaximalSpectrum (AdjoinRoot p))
    (a : k) (ha : Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root p) =
      algebraMap k (AdjoinRoot p ⧸ q.asIdeal) a) :
    Function.Surjective (algebraMap k (AdjoinRoot p ⧸ q.asIdeal)) := by
  have h : (Ideal.Quotient.mk q.asIdeal).comp (AdjoinRoot.mk p) =
      (algebraMap k (AdjoinRoot p ⧸ q.asIdeal)).comp (Polynomial.evalRingHom a) := by
    apply Polynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_C]
      rfl
    · simpa only [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_X,
        AdjoinRoot.root] using ha
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective r
  exact ⟨f.eval a, (RingHom.congr_fun h f).symm⟩

/-- If every residual root is scalar, total original local length is the polynomial degree. -/
theorem sum_local_length_eq_natDegree (p : k[X]) (hp : p.Monic)
    (hroot : ∀ q : MaximalSpectrum (AdjoinRoot p), ∃ a : k,
      Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root p) =
        algebraMap k (AdjoinRoot p ⧸ q.asIdeal) a) :
    letI := hp.finite_adjoinRoot
    letI : IsArtinianRing (AdjoinRoot p) := .of_finite k _
    letI : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
    ∑ q : MaximalSpectrum (AdjoinRoot p),
      (Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal)).toNat =
      p.natDegree := by
  classical
  let := hp.finite_adjoinRoot
  let : IsArtinianRing (AdjoinRoot p) := .of_finite k _
  let : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
  have hdeg (q : MaximalSpectrum (AdjoinRoot p)) :
      (Module.finiteAlgebraResidueDegree k (AdjoinRoot p) q : ℕ∞) = 1 := by
    rw [← Module.finiteAlgebra_residue_length k (AdjoinRoot p) q,
      Module.length_eq_finrank]
    obtain ⟨a, ha⟩ := hroot q
    rw [Module.finrank_of_bijective_algebraMap
      ⟨(algebraMap k (AdjoinRoot p ⧸ q.asIdeal)).injective,
        quotient_scalar_surjective p q a ha⟩]
    rfl
  have h := Module.finiteAlgebra_length_eq_sum
    (R := k) (S := AdjoinRoot p) (M := AdjoinRoot p) Module.length_ne_top
  have hlocal (q : MaximalSpectrum (AdjoinRoot p)) :
      Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal ⊗[AdjoinRoot p] AdjoinRoot p) =
      Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) :=
    (TensorProduct.AlgebraTensorModule.rid (AdjoinRoot p)
      (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal)).length_eq
  simp only [hdeg, mul_one, hlocal] at h
  rw [Module.length_eq_finrank] at h
  have hd : Module.finrank k (AdjoinRoot p) = p.natDegree :=
    finrank_quotient_span_eq_natDegree
  rw [hd] at h
  have hn (q : MaximalSpectrum (AdjoinRoot p)) :
      ((Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal)).toNat : ℕ∞) =
      Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) :=
    ENat.natCast_toNat (Algebra.local_length_ne_top_of_finite (k := k) q)
  apply ENat.natCast_inj.mp
  push_cast
  simpa only [hn] using h.symm

/-- Two actual maximal branches with the same scalar root are the same branch. -/
theorem maximal_eq_of_root_eq (p : k[X]) (q r : MaximalSpectrum (AdjoinRoot p))
    (a : k)
    (hq : Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root p) =
      algebraMap k (AdjoinRoot p ⧸ q.asIdeal) a)
    (hr : Ideal.Quotient.mk r.asIdeal (AdjoinRoot.root p) =
      algebraMap k (AdjoinRoot p ⧸ r.asIdeal) a) : q = r := by
  have h (s : MaximalSpectrum (AdjoinRoot p))
      (hs : Ideal.Quotient.mk s.asIdeal (AdjoinRoot.root p) =
        algebraMap k (AdjoinRoot p ⧸ s.asIdeal) a) :
      (Ideal.Quotient.mk s.asIdeal).comp (AdjoinRoot.mk p) =
        (algebraMap k (AdjoinRoot p ⧸ s.asIdeal)).comp (Polynomial.evalRingHom a) := by
    apply Polynomial.ringHom_ext
    · intro x
      simp only [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_C]
      rfl
    · simpa only [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_X,
        AdjoinRoot.root] using hs
  apply MaximalSpectrum.ext
  ext x
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective x
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.eq_zero_iff_mem]
  have hq' := RingHom.congr_fun (h q hq) f
  have hr' := RingHom.congr_fun (h r hr) f
  simp only [RingHom.comp_apply, Polynomial.coe_evalRingHom] at hq' hr'
  rw [hq', hr', map_eq_zero, map_eq_zero]

/-- The actual maximal ideal of a scalar polynomial root. -/
def scalarMaximal (p : k[X]) (a : k) (ha : p.eval a = 0) :
    MaximalSpectrum (AdjoinRoot p) := by
  let f : AdjoinRoot p →+* k := AdjoinRoot.lift (RingHom.id k) a (by simpa using ha)
  refine ⟨RingHom.ker f, RingHom.ker_isMaximal_of_surjective f ?_⟩
  intro x
  refine ⟨AdjoinRoot.of p x, ?_⟩
  exact AdjoinRoot.lift_of _

/-- The maximal quotient at a scalar root retains that exact root. -/
theorem scalarMaximal_root (p : k[X]) (a : k) (ha : p.eval a = 0) :
    Ideal.Quotient.mk (scalarMaximal p a ha).asIdeal (AdjoinRoot.root p) =
      algebraMap k (AdjoinRoot p ⧸ (scalarMaximal p a ha).asIdeal) a := by
  change Ideal.Quotient.mk _ (AdjoinRoot.root p) =
    Ideal.Quotient.mk _ (AdjoinRoot.of p a)
  rw [Ideal.Quotient.eq]
  change AdjoinRoot.lift (RingHom.id k) a _ (AdjoinRoot.root p - AdjoinRoot.of p a) = 0
  simp only [map_sub, AdjoinRoot.lift_root, AdjoinRoot.lift_of, RingHom.id_apply, sub_self]

/-- Every branch of the split polynomial is at one of its two literal scalar roots. -/
theorem split_residual_root (a : k) (m : ℕ)
    (q : MaximalSpectrum (AdjoinRoot ((X - C 1) ^ m * (X - C a)))) :
    Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root _) =
        algebraMap k (AdjoinRoot ((X - C 1) ^ m * (X - C a)) ⧸ q.asIdeal) 1 ∨
      Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root _) =
        algebraMap k (AdjoinRoot ((X - C 1) ^ m * (X - C a)) ⧸ q.asIdeal) a := by
  have h := congrArg (Ideal.Quotient.mk q.asIdeal)
    (AdjoinRoot.eval₂_root ((X - C 1) ^ m * (X - C a)))
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_sub,
    Polynomial.eval₂_X, Polynomial.eval₂_C, map_mul, map_pow, map_sub, map_zero] at h
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl (sub_eq_zero.mp (eq_zero_of_pow_eq_zero h))
  · exact Or.inr (sub_eq_zero.mp h)

/-- The correspondence graph is its genuine geometric graph basis vector. -/
theorem graph_eq_single (a : kˣ) :
    (Cor.graphFunctor k).map (rationalPoint k a) =
      Finsupp.single (graphSupport (rationalPoint k a)) 1 := by
  let : IsIntegral (SmoothSite.base (Spec (.of k))).left :=
    inferInstanceAs (IsIntegral (Spec (.of k)))
  rw [Cor.graphFunctor_map, componentGraphCycleOver_eq_graphGeneratorOver_cycle]
  rfl

/-- The full polynomial cycle is the sum of its actual rational branches,
with the original local lengths as signed coefficients. -/
theorem polynomialCycle_eq_sum_graph (p : k[X]) (hp : p.Monic) (h0 : p.coeff 0 ≠ 0)
    (a : MaximalSpectrum (AdjoinRoot p) → kˣ)
    (ha : ∀ q, Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root p) =
      algebraMap k (AdjoinRoot p ⧸ q.asIdeal) (a q : k)) :
    letI := hp.finite_adjoinRoot
    letI : IsArtinianRing (AdjoinRoot p) := .of_finite k _
    letI : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
    polynomialCycle p hp h0 = ∑ q : MaximalSpectrum (AdjoinRoot p),
      ((Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal)).toNat : ℤ) •
        (Cor.graphFunctor k).map (rationalPoint k (a q)) := by
  classical
  let := hp.finite_adjoinRoot
  let : IsArtinianRing (AdjoinRoot p) := .of_finite k _
  let : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
  unfold polynomialCycle affineFundamentalCorrespondence
  apply Finset.sum_congr rfl
  intro q _
  rw [polynomialBranchGenerator_eq_graph p hp h0 q (a q) (ha q), graph_eq_single]
  rw [Finsupp.smul_single]
  simp

/-- Coalesced roots keep their entire scheme-theoretic multiplicity. -/
theorem polynomialCycle_eq_degree_smul_graph (p : k[X]) (hp : p.Monic)
    (h0 : p.coeff 0 ≠ 0) (a : kˣ)
    (ha : ∀ q : MaximalSpectrum (AdjoinRoot p),
      Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root p) =
        algebraMap k (AdjoinRoot p ⧸ q.asIdeal) (a : k)) :
    polynomialCycle p hp h0 = (p.natDegree : ℤ) •
      (Cor.graphFunctor k).map (rationalPoint k a) := by
  classical
  let := hp.finite_adjoinRoot
  let : IsArtinianRing (AdjoinRoot p) := .of_finite k _
  let : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
  rw [polynomialCycle_eq_sum_graph p hp h0 (fun _ => a) ha, ← Finset.sum_smul,
    ← Nat.cast_sum, sum_local_length_eq_natDegree p hp (fun q => ⟨a, ha q⟩)]

/-- The two-factor endpoint polynomial is monic, also when its roots coincide. -/
theorem split_monic (a : kˣ) (m : ℕ) :
    (((X - C 1) ^ m * (X - C (a : k))) : k[X]).Monic :=
  ((monic_X_sub_C 1).pow m).mul (monic_X_sub_C (a : k))

/-- The endpoint's constant coefficient is nonzero in every characteristic. -/
theorem split_coeff_zero_ne_zero (a : kˣ) (m : ℕ) :
    (((X - C 1) ^ m * (X - C (a : k))) : k[X]).coeff 0 ≠ 0 := by
  simp only [coeff_zero_eq_eval_zero, eval_mul, eval_pow, eval_sub, eval_X, eval_C,
    zero_sub]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (neg_ne_zero.mpr a.ne_zero)

/-- The degree counts every repeated linear factor. -/
theorem split_natDegree (a : kˣ) (m : ℕ) :
    (((X - C 1) ^ m * (X - C (a : k))) : k[X]).natDegree = m + 1 := by
  rw [Monic.natDegree_mul ((monic_X_sub_C 1).pow m) (monic_X_sub_C (a : k)),
    natDegree_pow, natDegree_X_sub_C, natDegree_X_sub_C, mul_one]

/-- The repeated-identity endpoint has its full multiplicity, including characteristic two. -/
theorem polynomialCycle_split_one (m : ℕ) :
    polynomialCycle (((X - C 1) ^ m * (X - C 1)) : k[X])
      (split_monic (1 : kˣ) m) (split_coeff_zero_ne_zero (1 : kˣ) m) =
        ((m + 1 : ℕ) : ℤ) • (Cor.graphFunctor k).map (rationalPoint k 1) := by
  have h := polynomialCycle_eq_degree_smul_graph _ (split_monic (1 : kˣ) m)
    (split_coeff_zero_ne_zero (1 : kˣ) m) 1 (fun q => (split_residual_root (1 : k) m q).elim
      (fun h => h) (fun h => h))
  have hd : (((X - C 1) ^ m * (X - C 1)) : k[X]).natDegree = m + 1 :=
    split_natDegree (1 : kˣ) m
  simpa only [Units.val_one, hd] using h

/-- Separating one simple scalar branch leaves exactly the original repeated-identity length. -/
theorem polynomialCycle_split_of_local_length (a : kˣ) (m : ℕ)
    (q₀ : MaximalSpectrum (AdjoinRoot ((X - C 1) ^ m * (X - C (a : k)))))
    (hq₀ : Ideal.Quotient.mk q₀.asIdeal (AdjoinRoot.root _) =
      algebraMap k (AdjoinRoot ((X - C 1) ^ m * (X - C (a : k))) ⧸ q₀.asIdeal) (a : k))
    (hlength : Module.length (Localization.AtPrime q₀.asIdeal)
      (Localization.AtPrime q₀.asIdeal) = 1) :
    polynomialCycle ((X - C 1) ^ m * (X - C (a : k)))
      (split_monic a m) (split_coeff_zero_ne_zero a m) =
        (Cor.graphFunctor k).map (rationalPoint k a) +
          (m : ℤ) • (Cor.graphFunctor k).map (rationalPoint k 1) := by
  classical
  let p : k[X] := (X - C 1) ^ m * (X - C (a : k))
  let := (split_monic a m).finite_adjoinRoot
  let : IsArtinianRing (AdjoinRoot p) := .of_finite k _
  let : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
  let roots : MaximalSpectrum (AdjoinRoot p) → kˣ := fun q => if q = q₀ then a else 1
  have hroot (q : MaximalSpectrum (AdjoinRoot p)) :
      Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root p) =
        algebraMap k (AdjoinRoot p ⧸ q.asIdeal) (roots q : k) := by
    by_cases hq : q = q₀
    · subst q
      simpa only [roots, ite_eq_left rfl] using hq₀
    · rcases split_residual_root (a : k) m q with h | h
      · simpa only [roots, ite_eq_right hq, Units.val_one] using h
      · exact (hq (maximal_eq_of_root_eq p q q₀ a h hq₀)).elim
  let lengths (q : MaximalSpectrum (AdjoinRoot p)) : ℕ :=
    (Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal)).toNat
  have hzero : lengths q₀ = 1 := congrArg ENat.toNat hlength
  have htotal : ∑ q : MaximalSpectrum (AdjoinRoot p), lengths q = m + 1 := by
    change ∑ q : MaximalSpectrum (AdjoinRoot p),
      (Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal)).toNat = _
    rw [sum_local_length_eq_natDegree p (split_monic a m)
      (fun q => ⟨roots q, hroot q⟩)]
    exact split_natDegree a m
  have hrest : ∑ q ∈ Finset.univ.erase q₀, lengths q = m := by
    have h := Finset.add_sum_erase Finset.univ lengths (Finset.mem_univ q₀)
    rw [hzero, htotal] at h
    change 1 + (∑ q ∈ Finset.univ.erase q₀, lengths q) = m + 1 at h
    omega
  have hsum := polynomialCycle_eq_sum_graph p (split_monic a m)
    (split_coeff_zero_ne_zero a m) roots hroot
  change polynomialCycle p (split_monic a m) (split_coeff_zero_ne_zero a m) = _
  rw [hsum]
  change (∑ q : MaximalSpectrum (AdjoinRoot p),
    (lengths q : ℤ) • (Cor.graphFunctor k).map (rationalPoint k (roots q))) = _
  rw [← Finset.add_sum_erase Finset.univ
    (fun q => (lengths q : ℤ) • (Cor.graphFunctor k).map (rationalPoint k (roots q)))
      (Finset.mem_univ q₀)]
  simp only [hzero, Nat.cast_one, one_zsmul, roots, ite_eq_left rfl]
  congr 1
  calc
    _ = ∑ q ∈ Finset.univ.erase q₀,
        (lengths q : ℤ) • (Cor.graphFunctor k).map (rationalPoint k 1) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [ite_eq_right (Finset.mem_erase.mp hq).1]
    _ = _ := by rw [← Finset.sum_smul, ← Nat.cast_sum, hrest]

/-- The actual split polynomial cycle, including coincident roots and all characteristics. -/
theorem polynomialCycle_split (a : kˣ) (m : ℕ) :
    polynomialCycle ((X - C 1) ^ m * (X - C (a : k)))
      (split_monic a m) (split_coeff_zero_ne_zero a m) =
        (Cor.graphFunctor k).map (rationalPoint k a) +
          (m : ℤ) • (Cor.graphFunctor k).map (rationalPoint k 1) := by
  by_cases ha : a = 1
  · subst a
    have h := polynomialCycle_split_one (k := k) m
    simpa only [Units.val_one, Nat.cast_add, Nat.cast_one, add_zsmul, one_zsmul,
      add_comm] using h
  · have ha' : (a : k) ≠ 1 := fun h => ha (Units.ext h)
    let p : k[X] := (X - C 1) ^ m * (X - C (a : k))
    have hpa : p.eval (a : k) = 0 := by simp [p]
    let q := scalarMaximal p (a : k) hpa
    have hq := scalarMaximal_root p (a : k) hpa
    apply polynomialCycle_split_of_local_length a m q hq
    exact AdjoinRoot.split_simple_local_length (a : k) ha' m q hq

/-- The interpolation endpoint is the norm graph plus every repeated identity graph. -/
theorem polynomialCycle_target (p : k[X]) (hd : 1 ≤ p.natDegree)
    (h0 : p.coeff 0 ≠ 0) :
    polynomialCycle (Polynomial.MonicUnitInterpolation.target p)
      (Polynomial.MonicUnitInterpolation.target_monic p)
      ((Polynomial.MonicUnitInterpolation.target_coeff_zero p hd).trans_ne h0) =
        (Cor.graphFunctor k).map (rationalPoint k
          (Units.mk0 (Polynomial.MonicUnitInterpolation.normValue p)
            (Polynomial.MonicUnitInterpolation.normValue_ne_zero p h0))) +
        ((p.natDegree - 1 : ℕ) : ℤ) •
          (Cor.graphFunctor k).map (rationalPoint k 1) :=
by
  let a : kˣ := Units.mk0 (Polynomial.MonicUnitInterpolation.normValue p)
    (Polynomial.MonicUnitInterpolation.normValue_ne_zero p h0)
  have h := polynomialCycle_split a (p.natDegree - 1)
  exact h

/-- The product of two arbitrary unit-root factors is monic. -/
theorem twoLinear_monic (a b : kˣ) :
    ((X - C (a : k)) * (X - C (b : k))).Monic :=
  (monic_X_sub_C (a : k)).mul (monic_X_sub_C (b : k))

/-- The literal quadratic's constant coefficient is the product of its two units. -/
theorem twoLinear_coeff_zero (a b : kˣ) :
    ((X - C (a : k)) * (X - C (b : k))).coeff 0 = (a : k) * (b : k) := by
  simp only [coeff_zero_eq_eval_zero, eval_mul, eval_sub, eval_X, eval_C, zero_sub,
    neg_mul_neg]

/-- The quadratic stays inside the torus in every characteristic. -/
theorem twoLinear_coeff_zero_ne_zero (a b : kˣ) :
    ((X - C (a : k)) * (X - C (b : k))).coeff 0 ≠ 0 := by
  rw [twoLinear_coeff_zero]
  exact mul_ne_zero a.ne_zero b.ne_zero

/-- Both factors contribute to degree even when the roots coincide. -/
theorem twoLinear_natDegree (a b : kˣ) :
    ((X - C (a : k)) * (X - C (b : k))).natDegree = 2 := by
  rw [Monic.natDegree_mul (monic_X_sub_C (a : k)) (monic_X_sub_C (b : k)),
    natDegree_X_sub_C, natDegree_X_sub_C]

/-- The norm value of the actual quadratic is the unit product. -/
theorem twoLinear_normValue (a b : kˣ) :
    Polynomial.MonicUnitInterpolation.normValue
      ((X - C (a : k)) * (X - C (b : k))) = (a : k) * (b : k) := by
  rw [Polynomial.MonicUnitInterpolation.normValue, twoLinear_natDegree, twoLinear_coeff_zero]
  simp

/-- Every maximal quotient of the quadratic has one of its original scalar roots. -/
theorem twoLinear_residual_root (a b : kˣ)
    (q : MaximalSpectrum (AdjoinRoot ((X - C (a : k)) * (X - C (b : k))))) :
    Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root _) =
        algebraMap k (AdjoinRoot ((X - C (a : k)) * (X - C (b : k))) ⧸ q.asIdeal) a ∨
      Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root _) =
        algebraMap k (AdjoinRoot ((X - C (a : k)) * (X - C (b : k))) ⧸ q.asIdeal) b := by
  have h := congrArg (Ideal.Quotient.mk q.asIdeal)
    (AdjoinRoot.eval₂_root ((X - C (a : k)) * (X - C (b : k))))
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_sub,
    Polynomial.eval₂_X, Polynomial.eval₂_C, map_mul, map_sub, map_zero] at h
  exact (mul_eq_zero.mp h).imp sub_eq_zero.mp sub_eq_zero.mp

/-- At either distinct quadratic root the literal localization has length one. -/
theorem twoLinear_simple_local_length (a b : kˣ) (hab : a ≠ b)
    (q : MaximalSpectrum (AdjoinRoot ((X - C (a : k)) * (X - C (b : k)))))
    (hq : Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root _) =
      algebraMap k (AdjoinRoot ((X - C (a : k)) * (X - C (b : k))) ⧸ q.asIdeal) a) :
    Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) = 1 := by
  let p : k[X] := (X - C (a : k)) * (X - C (b : k))
  let R := AdjoinRoot p
  let L := Localization.AtPrime q.asIdeal
  change Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root p) =
    algebraMap k (R ⧸ q.asIdeal) a at hq
  have hu : IsUnit (algebraMap R L (AdjoinRoot.root p - algebraMap k R b)) := by
    apply (IsLocalization.AtPrime.isUnit_to_map_iff L q.asIdeal _).mpr
    change AdjoinRoot.root p - algebraMap k R b ∉ q.asIdeal
    intro h
    have hz := (Ideal.Quotient.eq_zero_iff_mem).mpr h
    have he : algebraMap k (R ⧸ q.asIdeal) a = algebraMap k (R ⧸ q.asIdeal) b := by
      apply sub_eq_zero.mp
      rw [map_sub] at hz
      change Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root p) -
        algebraMap k (R ⧸ q.asIdeal) b = 0 at hz
      rwa [hq] at hz
    exact hab (Units.ext ((algebraMap k (R ⧸ q.asIdeal)).injective he))
  have hrel : (AdjoinRoot.root p - algebraMap k R a) *
      (AdjoinRoot.root p - algebraMap k R b) = 0 := by
    change (AdjoinRoot.root p - AdjoinRoot.of p a) *
      (AdjoinRoot.root p - AdjoinRoot.of p b) = 0
    simpa only [p, eval₂_mul, eval₂_sub, eval₂_X, eval₂_C] using AdjoinRoot.eval₂_root p
  have hp : (algebraMap R L (AdjoinRoot.root p) - algebraMap k L a) *
      (algebraMap R L (AdjoinRoot.root p) - algebraMap k L b) = 0 := by
    have h := congrArg (algebraMap R L) hrel
    simpa only [map_mul, map_sub, map_zero, ← IsScalarTower.algebraMap_apply] using h
  have hu' : IsUnit (algebraMap R L (AdjoinRoot.root p) - algebraMap k L b) := by
    simpa only [map_sub, ← IsScalarTower.algebraMap_apply] using hu
  exact AdjoinRoot.local_length_eq_one_of_root_eq q.toPrimeSpectrum a
    (sub_eq_zero.mp (hu'.mul_left_eq_zero.mp hp))

/-- A monic degree-two cycle with two scalar residual roots and one simple branch
is the sum of those actual rational graph cycles. -/
theorem polynomialCycle_twoRoots_of_local_length (p : k[X]) (hp : p.Monic)
    (h0 : p.coeff 0 ≠ 0) (hd : p.natDegree = 2) (a b : kˣ)
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
    polynomialCycle p hp h0 = (Cor.graphFunctor k).map (rationalPoint k a) +
      (Cor.graphFunctor k).map (rationalPoint k b) := by
  classical
  let := hp.finite_adjoinRoot
  let : IsArtinianRing (AdjoinRoot p) := .of_finite k _
  let : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
  let roots : MaximalSpectrum (AdjoinRoot p) → kˣ := fun q => if q = q₀ then a else b
  have hroot (q : MaximalSpectrum (AdjoinRoot p)) :
      Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root p) =
        algebraMap k (AdjoinRoot p ⧸ q.asIdeal) (roots q : k) := by
    by_cases hq : q = q₀
    · subst q
      simpa only [roots, ite_eq_left rfl] using hq₀
    · rcases hroots q with h | h
      · exact (hq (maximal_eq_of_root_eq p q q₀ a h hq₀)).elim
      · simpa only [roots, ite_eq_right hq] using h
  let lengths (q : MaximalSpectrum (AdjoinRoot p)) : ℕ :=
    (Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal)).toNat
  have hzero : lengths q₀ = 1 := congrArg ENat.toNat hlength
  have htotal : ∑ q : MaximalSpectrum (AdjoinRoot p), lengths q = 2 := by
    change ∑ q : MaximalSpectrum (AdjoinRoot p),
      (Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal)).toNat = _
    rw [sum_local_length_eq_natDegree p hp (fun q => ⟨roots q, hroot q⟩), hd]
  have hrest : ∑ q ∈ Finset.univ.erase q₀, lengths q = 1 := by
    have h := Finset.add_sum_erase Finset.univ lengths (Finset.mem_univ q₀)
    rw [hzero, htotal] at h
    omega
  rw [polynomialCycle_eq_sum_graph p hp h0 roots hroot]
  change (∑ q : MaximalSpectrum (AdjoinRoot p),
    (lengths q : ℤ) • (Cor.graphFunctor k).map (rationalPoint k (roots q))) = _
  rw [← Finset.add_sum_erase Finset.univ
    (fun q => (lengths q : ℤ) • (Cor.graphFunctor k).map (rationalPoint k (roots q)))
      (Finset.mem_univ q₀)]
  simp only [hzero, Nat.cast_one, one_zsmul, roots, ite_eq_left rfl]
  congr 1
  calc
    _ = ∑ q ∈ Finset.univ.erase q₀,
        (lengths q : ℤ) • (Cor.graphFunctor k).map (rationalPoint k b) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [ite_eq_right (Finset.mem_erase.mp hq).1]
    _ = _ := by rw [← Finset.sum_smul, ← Nat.cast_sum, hrest, Nat.cast_one, one_zsmul]

/-- The actual quadratic polynomial cycle is the sum of its two graph cycles,
including coincident roots and arbitrary characteristic. -/
theorem polynomialCycle_twoLinear (a b : kˣ) :
    polynomialCycle ((X - C (a : k)) * (X - C (b : k)))
      (twoLinear_monic a b) (twoLinear_coeff_zero_ne_zero a b) =
        (Cor.graphFunctor k).map (rationalPoint k a) +
          (Cor.graphFunctor k).map (rationalPoint k b) := by
  by_cases hab : a = b
  · subst b
    have h := polynomialCycle_eq_degree_smul_graph _ (twoLinear_monic a a)
      (twoLinear_coeff_zero_ne_zero a a) a (fun q =>
        (twoLinear_residual_root a a q).elim (fun h => h) (fun h => h))
    simpa only [twoLinear_natDegree, Nat.cast_ofNat, two_zsmul] using h
  · let p : k[X] := (X - C (a : k)) * (X - C (b : k))
    have hpa : p.eval (a : k) = 0 := by simp [p]
    let q := scalarMaximal p (a : k) hpa
    have hq := scalarMaximal_root p (a : k) hpa
    exact polynomialCycle_twoRoots_of_local_length p (twoLinear_monic a b)
      (twoLinear_coeff_zero_ne_zero a b) (twoLinear_natDegree a b) a b
      (twoLinear_residual_root a b) q hq (twoLinear_simple_local_length a b hab q hq)

end Motivic.WeightOneSplitPolynomialCycle
