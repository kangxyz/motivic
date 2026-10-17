/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.MovingPointIncidenceDimension
public import Motivic.Aglib.RingTheory.Bertini.QuadraticIncidenceParameterMap
public import Motivic.Aglib.RingTheory.Bertini.IncidenceNonDominance

/-! # A nonzero original parameter equation for each whole bad-point chart

The generic-component dimension bound is applied to the actual parameter map
into the full incidence ring. Nilpotents and noninjective coefficient maps are
retained; no independent finiteness or dimension premise is supplied.
-/
@[expose] public noncomputable section
universe u
namespace QuadraticIncidence.MovingPointChart
variable (k R B : Type u) [Field k] [CommRing R] [IsDomain R] [CommRing B]
  [Algebra k R] [Algebra k B] [Algebra R B] [IsScalarTower k R B]
  [Module.Finite R B] [Algebra.Smooth k R] {σ : Type u} [Fintype σ]

/-- The actual ground-coefficient parameter map for the original normalized chart. -/
def chartParameterMap (g : σ → R) (a : σ → B) (d : ℕ) (i₀ : Fin d) (j : σ) :
    MvPolynomial (Fin d × Exponent σ) k →ₐ[k] incidenceRing k R B g a d i₀ j :=
  let t := algebraMap R B (g j) - a j
  let A := Ring B d i₀ t
  parameterMap k R A g (algebraMap B A ∘ a) d (weight B d i₀ t)

/-- The original prime quotient, not only its fraction field, has strictly
smaller transcendence degree than the full parameter space. -/
theorem trdeg_component_lt
    (g : σ → R) (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (a : σ → B) (d : ℕ) (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (i₀ : Fin d) (j : σ) (P : Ideal (incidenceRing k R B g a d i₀ j)) [P.IsPrime] :
    Algebra.trdeg k (incidenceRing k R B g a d i₀ j ⧸ P) <
      (d * Fintype.card (Exponent σ) : ℕ) := by
  let C := incidenceRing k R B g a d i₀ j ⧸ P
  let E := FractionRing C
  have hc : Algebra.trdeg k C ≤ Algebra.trdeg k E := by
    apply trdeg_le_of_injective (IsScalarTower.toAlgHom k C E)
    intro x y hxy
    exact IsFractionRing.injective C E hxy
  have hf := trdeg_component_fractionField_add_one_le k R B g hg a d hd i₀ j P
  have h : Algebra.trdeg k C + 1 ≤ (d * Fintype.card (Exponent σ) : ℕ) :=
    (add_le_add hc le_rfl).trans hf
  have hfin : Algebra.trdeg k C < Cardinal.aleph0 :=
    (le_self_add.trans h).trans_lt Cardinal.natCast_lt_aleph0
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp hfin
  change Algebra.trdeg k C < _
  rw [hn] at h ⊢
  exact Cardinal.natCast_add_one_le_iff.mp h

/-- A nonzero polynomial vanishes on the full original bad-fiber incidence chart. -/
theorem exists_nonzero_parameter_relation
    (g : σ → R) (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (a : σ → B) (d : ℕ) (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (i₀ : Fin d) (j : σ) :
    ∃ f : MvPolynomial (Fin d × Exponent σ) k,
      f ≠ 0 ∧ chartParameterMap k R B g a d i₀ j f = 0 := by
  apply Algebra.exists_nonzero_kernel_of_minimal_quotient_trdeg_lt
  intro P hP
  have : P.IsPrime := hP.isPrime
  simpa only [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fintype,
    Cardinal.lift_natCast, Fintype.card_prod, Fintype.card_fin] using
      trdeg_component_lt k R B g hg a d hd i₀ j P

end QuadraticIncidence.MovingPointChart
