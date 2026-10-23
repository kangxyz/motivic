/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Etale.ResidueCoordinateCriterion
public import Motivic.Aglib.RingTheory.Kaehler.ResidueFunctionBasis

/-! # Complete independent base coordinates to an actual relative-curve chart

The given functions are unchanged. One original affine function is added to make
an actual étale map to a polynomial line over their polynomial base.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Module TensorProduct KaehlerDifferential
universe u v
namespace Algebra

/-- Independent `d` original coordinate differentials in a smooth `(d+1)`-dimensional
fiber extend by one actual original function to an étale polynomial chart. -/
theorem exists_etale_curve_chart_preserving_coordinates
    (k : Type u) (R : Type v) [Field k] [CommRing R] [Algebra k R] [Smooth k R]
    (p : Ideal R) [p.IsPrime] {d : ℕ} (g : Fin d → R)
    (hd : Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime p))
      (IsLocalRing.ResidueField (Localization.AtPrime p) ⊗[R] Ω[R⁄k]) = d + 1)
    (hg : LinearIndependent (IsLocalRing.ResidueField (Localization.AtPrime p))
      (fun j => (1 ⊗ₜ[R] D k R (g j) :
        IsLocalRing.ResidueField (Localization.AtPrime p) ⊗[R] Ω[R⁄k]))) :
    ∃ t : R, ∃ r ∉ p, ((algebraMap R (Localization.Away r)).comp
      (MvPolynomial.aeval (R := k) (Fin.cons (α := fun _ => R) t g)).toRingHom).Etale := by
  classical
  let K := IsLocalRing.ResidueField (Localization.AtPrime p)
  let v : Fin d → K ⊗[R] Ω[R⁄k] := fun j => 1 ⊗ₜ[R] D k R (g j)
  let W := Submodule.span K (Set.range v)
  have hW : W ≠ ⊤ := by
    intro h
    have hdim := finrank_span_eq_card hg
    rw [show Submodule.span K (Set.range (fun j =>
      (1 ⊗ₜ[R] D k R (g j) : K ⊗[R] Ω[R⁄k]))) = ⊤ from h,
      finrank_top, hd, Fintype.card_fin] at hdim
    omega
  have hex : ∃ t : R, (1 ⊗ₜ[R] D k R t : K ⊗[R] Ω[R⁄k]) ∉ W := by
    by_contra! hh
    apply hW
    apply top_le_iff.mp
    rw [← span_residue_original_differentials k R K]
    apply Submodule.span_le.mpr
    rintro _ ⟨t, rfl⟩
    exact hh t
  obtain ⟨t, ht⟩ := hex
  have hli : LinearIndependent K
      (fun j : Fin (d + 1) =>
        (1 ⊗ₜ[R] D k R (Fin.cons (α := fun _ => R) t g j) : K ⊗[R] Ω[R⁄k])) := by
    convert hg.finCons ht using 1
    ext j
    cases j using Fin.cases <;> rfl
  let bK := basisOfLinearIndependentOfCardEqFinrank'
    (fun j : Fin (d + 1) =>
        (1 ⊗ₜ[R] D k R (Fin.cons (α := fun _ => R) t g j) : K ⊗[R] Ω[R⁄k])) hli
      (by simpa using hd.symm)
  obtain ⟨r, hr, he⟩ := exists_etale_polynomial_map_of_residue_differential_basis
    k R p (Fin.cons (α := fun _ => R) t g) bK
      (fun j => congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _) j)
  exact ⟨t, r, hr, he⟩

end Algebra
