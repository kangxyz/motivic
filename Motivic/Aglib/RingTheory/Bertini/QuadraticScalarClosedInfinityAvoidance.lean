/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Bertini.QuadraticScalarBoundaryAvoidance
public import Motivic.Aglib.RingTheory.Bertini.QuadraticClosedInfinityAvoidance
public import Motivic.Aglib.RingTheory.MinimalPrimeGoingDown

/-! # Closed infinity avoidance on all actual scalar minimal components -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MvPolynomial

namespace QuadraticIncidence.InfinityChart

universe u

/-- Every minimal component of the actual extended ideal is controlled by its
original contracted component. No reduced substitute replaces the original ideal. -/
theorem noCommonClosedInfinityZero_of_original_eval₂_relations
    (k L R S : Type u) [Field k] [Field L] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k L] [Algebra L S] [Algebra k S]
    [IsScalarTower k L S] [Algebra R S] [IsScalarTower k R S]
    [Algebra.HasGoingDown R S] (I : Ideal R)
    {σ : Type u} [Finite σ] (g : σ → R) (d : ℕ)
    (Q : I.minimalPrimes → MvPolynomial (Fin d × Exponent σ) k)
    (hQ : ∀ P : I.minimalPrimes, letI : P.val.IsPrime := P.property.isPrime
      ∀ j : Exponent σ,
        monomialFunction k (R ⧸ P.val) (Ideal.Quotient.mk P.val ∘ g) j ≠ 0 →
        ProjectiveEvaluationIncidence.parameterMap
          (boundaryRing k (R ⧸ P.val) (Ideal.Quotient.mk P.val ∘ g) j) k
          (boundaryCoordinate k (R ⧸ P.val) (Ideal.Quotient.mk P.val ∘ g) j) d (Q P) = 0)
    (c : Fin d × Exponent σ → L)
    (hc : ∀ P, eval₂ (algebraMap k L) c (Q P) ≠ 0) :
    NoCommonClosedInfinityZero L S (I.map (algebraMap R S))
      (algebraMap R S ∘ g) d c := by
  intro P
  let : P.val.IsPrime := P.property.isPrime
  let p : I.minimalPrimes :=
    ⟨P.val.under R, Ideal.under_mem_minimalPrimes_of_hasGoingDown I P.val P.property⟩
  let : p.val.IsPrime := p.property.isPrime
  let f : R ⧸ p.val →ₐ[k] S ⧸ P.val :=
    Ideal.quotientMapₐ P.val (IsScalarTower.toAlgHom k R S) le_rfl
  have hf : Function.Injective f := Ideal.quotientMap_injective
  have hg : f ∘ (Ideal.Quotient.mk p.val ∘ g) =
      Ideal.Quotient.mk P.val ∘ (algebraMap R S ∘ g) := by
    funext j
    rfl
  have h := noCommonBoundaryZero_of_original_eval₂_relation
    k L (R ⧸ p.val) (S ⧸ P.val) f hf (Ideal.Quotient.mk p.val ∘ g) d
      (Q p) (hQ p) c (hc p)
  exact h

end QuadraticIncidence.InfinityChart
