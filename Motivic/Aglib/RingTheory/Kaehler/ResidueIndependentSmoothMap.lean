/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Kaehler.SmoothCotangentTrdeg
public import Motivic.Aglib.RingTheory.Kaehler.ResidueFunctionBasis
public import Motivic.Aglib.RingTheory.Etale.ResidueCoordinateCriterion
public import Motivic.Aglib.AlgebraicGeometry.Normalization.ConstantEtaleCurve

/-! # Original independent functions give a relative curve near the original prime -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Module TensorProduct KaehlerDifferential CategoryTheory AlgebraicGeometry
universe u
namespace KaehlerDifferential

/-- Complete the prescribed functions by one actual original function, without changing them. -/
theorem exists_residue_basis_cons (k R K : Type u) [Field k] [CommRing R] [Field K]
    [Algebra k R] [Algebra R K] [Algebra.EssFiniteType k R] (d : ℕ) (f : Fin d → R)
    (hf : LinearIndependent K (fun i => (1 ⊗ₜ[R] D k R (f i) : K ⊗[R] Ω[R⁄k])))
    (hd : Module.finrank K (K ⊗[R] Ω[R⁄k]) = d + 1) :
    ∃ t : R, ∃ b : Basis (Fin (d + 1)) K (K ⊗[R] Ω[R⁄k]),
      ∀ i, b i = 1 ⊗ₜ[R] D k R ((Fin.cons t f : Fin (d + 1) → R) i) := by
  classical
  let v : R → K ⊗[R] Ω[R⁄k] := fun r => 1 ⊗ₜ[R] D k R r
  let W := Submodule.span K (Set.range (fun i => v (f i)))
  have hW : W ≠ ⊤ := by
    intro h
    have he := finrank_span_eq_card hf
    rw [show Submodule.span K (Set.range (fun i => v (f i))) = ⊤ from h,
      finrank_top, hd, Fintype.card_fin] at he
    omega
  have hex : ∃ t, v t ∉ W := by
    by_contra! h
    apply hW
    apply top_unique
    rw [← span_residue_original_differentials k R K]
    exact Submodule.span_le.mpr (by rintro _ ⟨r, rfl⟩; exact h r)
  obtain ⟨t, ht⟩ := hex
  have hli : LinearIndependent K (fun i => v ((Fin.cons t f : Fin (d + 1) → R) i)) := by
    convert hf.finCons ht using 1
    ext i
    cases i using Fin.cases <;> rfl
  let b := basisOfLinearIndependentOfCardEqFinrank'
    (fun i => v ((Fin.cons t f : Fin (d + 1) → R) i)) hli (by simpa using hd.symm)
  exact ⟨t, b, fun i => Basis.mk_apply _ _ _⟩

end KaehlerDifferential
namespace Algebra

/-- One added function makes an étale chart in a genuine principal neighborhood;
the original first `d` functions remain its unchanged tail. -/
theorem exists_etale_cons_of_residue_independent
    (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R] [Smooth k R]
    (p : Ideal R) [p.IsPrime] (d : ℕ) (f : Fin d → R)
    (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (hf : LinearIndependent p.ResidueField
      (fun i => (1 ⊗ₜ[R] D k R (f i) : p.ResidueField ⊗[R] Ω[R⁄k]))) :
    ∃ t : R, ∃ r ∉ p, ((algebraMap R (Localization.Away r)).comp
      (MvPolynomial.aeval (R := k) (Fin.cons t f : Fin (d + 1) → R)).toRingHom).Etale := by
  have hrank : Module.finrank p.ResidueField (p.ResidueField ⊗[R] Ω[R⁄k]) = d + 1 := by
    rw [cotangent_finrank_eq_trdeg_toNat k R p.ResidueField, hd]
    simp
  obtain ⟨t, b, hb⟩ := exists_residue_basis_cons k R p.ResidueField d f hf hrank
  obtain ⟨r, hr, he⟩ := exists_etale_polynomial_map_of_residue_differential_basis
    k R p (Fin.cons t f) b hb
  exact ⟨t, r, hr, he⟩

end Algebra

namespace AlgebraicGeometry

/-- The original polynomial map on the genuine principal neighborhood is smooth
of relative dimension one. Adding a coordinate is used only to prove this property. -/
theorem exists_smooth_one_of_residue_independent
    (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R] [Algebra.Smooth k R]
    (p : Ideal R) [p.IsPrime] (d : ℕ) (f : Fin d → R)
    (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (hf : LinearIndependent p.ResidueField
      (fun i => (1 ⊗ₜ[R] D k R (f i) : p.ResidueField ⊗[R] Ω[R⁄k]))) :
    ∃ r ∉ p, SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom ((algebraMap R (Localization.Away r)).comp
        (MvPolynomial.aeval (R := k) f).toRingHom))) := by
  obtain ⟨t, r, hr, he⟩ := Algebra.exists_etale_cons_of_residue_independent k R p d f hd hf
  let P := MvPolynomial (Fin d) k
  let Q := MvPolynomial (Fin (d + 1)) k
  let a : Q →+* Localization.Away r := (algebraMap R (Localization.Away r)).comp
    (MvPolynomial.aeval (R := k) (Fin.cons t f : Fin (d + 1) → R)).toRingHom
  let e := (MvPolynomial.finSuccEquiv k d).toRingEquiv.toCommRingCatIso
  let m := Spec.map (CommRingCat.ofHom a)
  let j := Spec.map e.inv
  let π := Spec.map (CommRingCat.ofHom (Polynomial.C : P →+* Polynomial P))
  have : Etale m := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr he
  have : SmoothOfRelativeDimension 1 π :=
    Scheme.AffineLineEtaleCompactification.polynomialProjection_smooth_one P
  have hcomp : SmoothOfRelativeDimension 1 ((m ≫ j) ≫ π) :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) ((m ≫ j) ≫ π))
  refine ⟨r, hr, ?_⟩
  convert hcomp using 1
  dsimp only [m, j, π]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply MvPolynomial.ringHom_ext
  · intro x
    change algebraMap R (Localization.Away r) ((MvPolynomial.aeval f) (MvPolynomial.C x)) =
      a ((MvPolynomial.finSuccEquiv k d).symm (Polynomial.C (MvPolynomial.C x)))
    have hx : (MvPolynomial.finSuccEquiv k d).symm (Polynomial.C (MvPolynomial.C x)) =
        MvPolynomial.C x := by
      apply (MvPolynomial.finSuccEquiv k d).injective
      simp [MvPolynomial.finSuccEquiv_apply]
    rw [hx]
    change algebraMap R (Localization.Away r) _ = algebraMap R (Localization.Away r) _
    congr 1
    exact (MvPolynomial.aeval_C f x).trans
      (MvPolynomial.aeval_C (Fin.cons t f : Fin (d + 1) → R) x).symm
  · intro i
    change algebraMap R (Localization.Away r) ((MvPolynomial.aeval f) (MvPolynomial.X i)) =
      a ((MvPolynomial.finSuccEquiv k d).symm (Polynomial.C (MvPolynomial.X i)))
    have hx : (MvPolynomial.finSuccEquiv k d).symm (Polynomial.C (MvPolynomial.X i)) =
        MvPolynomial.X i.succ := by
      apply (MvPolynomial.finSuccEquiv k d).injective
      simp [MvPolynomial.finSuccEquiv_X_succ]
    rw [hx]
    change algebraMap R (Localization.Away r) _ = algebraMap R (Localization.Away r) _
    congr 1
    exact (MvPolynomial.aeval_X f i).trans
      (MvPolynomial.aeval_X (Fin.cons t f : Fin (d + 1) → R) i.succ).symm

end AlgebraicGeometry
