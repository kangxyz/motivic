/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.LargePrimeOriginalEtalePresentation
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.PolynomialZeroOriginalEtalePresentation
public import Motivic.Aglib.RingTheory.Kaehler.SmoothCotangentTrdeg

/-! # Actual two-prime presentations of original whole polynomial-zero diagrams

Finite generators, positive dimension and the residue cotangent basis are
constructed from the original coefficient algebra. The entire original zero
square is retained through its literal quotient and subsequent scalar pullback.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial Module
open AlgebraicGeometry.Scheme.RelativeCurve AlgebraicGeometry.PolynomialOpenQuotient
open scoped TensorProduct

universe u

namespace QuadraticIncidence.InfinityChart

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The original polynomial-zero diagram produces actual presentations over the
same two prime extensions, with no supplied coordinates, rank, or presentation. -/
theorem exists_two_prime_polynomialZero_originalEtalePresentations
    (k R : Type u) [Field k] [Finite k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.Smooth k R]
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (x : PrimeSpectrum (Polynomial R)) [x.asIdeal.IsMaximal]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of (Polynomial R)))
    [Etale p] [QuasiCompact p] [IsSeparated p]
    (s₀ : Spec (.of R) ⟶ Y)
    (hs₀ : s₀ ≫ p = Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))))
    (H₀ : IsPullback s₀ (𝟙 _) p
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))))
    (N₀ : ℕ) :
    ∃ n m : ℕ, N₀ < n ∧ N₀ < m ∧ n.Coprime m ∧
      ∀ (r : ℕ) [NeZero r], r = n ∨ r = m →
        let L := ULift.{u} (FiniteField.Extension k ℓ r)
        let S := (Polynomial R) ⊗[k] L
        let ρ := Spec.map (CommRingCat.ofHom (algebraMap (Polynomial R) S))
        let J : Ideal (Polynomial R) := Ideal.span {Polynomial.X}
        let s := source (Polynomial.X : Polynomial R) ≫ s₀
        let hs : s ≫ p = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
          change (source (Polynomial.X : Polynomial R) ≫ s₀) ≫ p =
            inclusion (Polynomial.X : Polynomial R)
          rw [Category.assoc, hs₀, polynomial_zero_quotient_inclusion]
        Module.finrank k L = r ∧ ∃ hdom : IsDomain S,
          letI : IsDomain S := hdom
          ∃ y : PrimeSpectrum S,
            PrimeSpectrum.comap (algebraMap (Polynomial R) S) y = x ∧
            (∀ z : PrimeSpectrum S,
              PrimeSpectrum.comap (algebraMap (Polynomial R) S) z = x → z = y) ∧
            Nonempty (OriginalEtalePresentation L
              (Spec.map (CommRingCat.ofHom (algebraMap L S)))
              (pullback.snd p ρ)
              (pullback.snd (Scheme.Opens.ι (X := Spec (.of (Polynomial R)))
                (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R))) ρ)
              (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (J.map (algebraMap (Polynomial R) S)))))
              (Scheme.quotientBaseChangeEtaleLift (Polynomial R) S J p s hs) y) := by
  classical
  let : Algebra.Smooth R (Polynomial R) := {}
  let : Algebra.Smooth k (Polynomial R) := Algebra.Smooth.comp k R (Polynomial R)
  let J : Ideal (Polynomial R) := Ideal.span {Polynomial.X}
  have hJ : J ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr Polynomial.X_ne_zero
  obtain ⟨G, hG⟩ := Algebra.FiniteType.out (R := k) (A := Polynomial R)
  have hg : Algebra.adjoin k (Set.range (fun g : G => (g : Polynomial R))) = ⊤ := by
    convert hG using 1
    congr 1
    ext g
    simp
  obtain ⟨d, hd⟩ := Cardinal.lt_aleph0.mp
    (trdeg_lt_aleph0_of_finiteType (R := k) (S := R))
  have hd' : Algebra.trdeg k (Polynomial R) = (d + 1 : ℕ) := by
    rw [← trdeg_add_eq k R (A := Polynomial R),
      Polynomial.trdeg_of_isDomain, hd, Nat.cast_add, Nat.cast_one]
  have hdim : Module.finrank x.asIdeal.ResidueField
      (x.asIdeal.ResidueField ⊗[Polynomial R] KaehlerDifferential k (Polynomial R)) = d + 1 := by
    rw [Algebra.residue_cotangent_finrank_eq_trdeg_toNat k (Polynomial R) x.asIdeal,
      hd', Cardinal.toNat_natCast]
  obtain ⟨_, basis, _⟩ := KaehlerDifferential.exists_residue_basis_fin_original_functions
    k (Polynomial R) x.asIdeal.ResidueField (d + 1) hdim
  have : IsIso (source (Polynomial.X : Polynomial R)) := by
    have hp : (Polynomial.X - Polynomial.C (0 : R) : Polynomial R) = Polynomial.X := by
      rw [Polynomial.C_0, sub_zero]
    exact (congrArg (fun q : Polynomial R => IsIso (source q)) hp).mp
      (source_linear_isIso (0 : R))
  let s := source (Polynomial.X : Polynomial R) ≫ s₀
  have hs : s ≫ p = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
    change (source (Polynomial.X : Polynomial R) ≫ s₀) ≫ p =
      inclusion (Polynomial.X : Polynomial R)
    rw [Category.assoc, hs₀, polynomial_zero_quotient_inclusion]
  have H : IsPullback s (𝟙 _) p
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) := by
    apply H₀.of_iso' (asIso (source (Polynomial.X : Polynomial R))) (Iso.refl _)
      (asIso (source (Polynomial.X : Polynomial R))) (Iso.refl _)
    · simp [s]
    · simp
    · simp
    · change source (Polynomial.X : Polynomial R) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) =
          inclusion (Polynomial.X : Polynomial R)
      exact polynomial_zero_quotient_inclusion R
  apply exists_two_prime_originalEtalePresentations k (Polynomial R) ℓ x J hJ
    (fun g : G => (g : Polynomial R)) hg d hd' basis p
    (Scheme.Opens.ι (X := Spec (.of (Polynomial R)))
      (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R))) s hs H
    (N₀ := N₀)
  · change Disjoint (Set.range (principalOpen (Polynomial.X : Polynomial R)).ι)
      (Set.range (inclusion (Polynomial.X : Polynomial R)))
    rw [Scheme.Opens.range_ι, range_inclusion_complement]
    exact disjoint_compl_right
  · intro y
    change y ∈ Set.range (principalOpen (Polynomial.X : Polynomial R)).ι ∨
      y ∈ Set.range (inclusion (Polynomial.X : Polynomial R))
    rw [Scheme.Opens.range_ι, range_inclusion_complement]
    exact em (y ∈ principalOpen (Polynomial.X : Polynomial R))

end QuadraticIncidence.InfinityChart
