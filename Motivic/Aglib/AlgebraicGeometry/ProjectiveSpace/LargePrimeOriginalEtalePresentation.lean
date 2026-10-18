/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.LargePrimeQuadraticCompactification
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.ChosenRetainedPresentation
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.ChosenOriginalEtalePresentation
public import Motivic.Aglib.AlgebraicGeometry.AffineEtaleScalarClosedSquare
public import Motivic.Aglib.AlgebraicGeometry.Normalization.FixedFiniteLocusBadIdeal

/-! # Original étale presentations over the same two large prime extensions

The bad ideal is fixed from the original étale map before choosing either
extension or any quadratic parameter. Each presentation retains the actual
scalar pullback and full mapped closed quotient. Its selected point is the
unique point of the entire original closed-point fiber.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module MvPolynomial
open AlgebraicGeometry.Scheme.RelativeCurve
open scoped TensorProduct

universe u

namespace QuadraticIncidence.InfinityChart

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The same two coprime prime extensions give presentations for the literal
scalar pullbacks of the original étale diagram. No geometry is supplied. -/
theorem exists_two_prime_originalEtalePresentations
    (k B : Type u) [Field k] [Finite k] [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.Smooth k B]
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (x : PrimeSpectrum B) [x.asIdeal.IsMaximal]
    (J : Ideal B) (hJ : J ≠ ⊥)
    {σ : Type u} [Finite σ] (g : σ → B)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k B = (d + 1 : ℕ))
    (basis : Basis (Fin (d + 1)) x.asIdeal.ResidueField
      (x.asIdeal.ResidueField ⊗[B] KaehlerDifferential k B))
    {Y A : Scheme.{u}} (p : Y ⟶ Spec (.of B)) [Etale p] [QuasiCompact p] [IsSeparated p]
    (a : A ⟶ Spec (.of B)) [IsOpenImmersion a]
    (s : Spec (.of (B ⧸ J)) ⟶ Y)
    (hs : s ≫ p = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
    (H : IsPullback s (𝟙 _) p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    (ha : Disjoint (Set.range a)
      (Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))))
    (hcover : ∀ y : Spec (.of B), y ∈ Set.range a ∨
      y ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    (N₀ : ℕ) :
    ∃ n m : ℕ, N₀ < n ∧ N₀ < m ∧ n.Coprime m ∧
      ∀ (r : ℕ) [NeZero r], r = n ∨ r = m →
        let L := ULift.{u} (FiniteField.Extension k ℓ r)
        let S := B ⊗[k] L
        let ρ := Spec.map (CommRingCat.ofHom (algebraMap B S))
        Module.finrank k L = r ∧ ∃ hdom : IsDomain S,
          letI : IsDomain S := hdom
          ∃ y : PrimeSpectrum S,
            PrimeSpectrum.comap (algebraMap B S) y = x ∧
            (∀ z : PrimeSpectrum S, PrimeSpectrum.comap (algebraMap B S) z = x → z = y) ∧
            Nonempty (OriginalEtalePresentation L
              (Spec.map (CommRingCat.ofHom (algebraMap L S)))
              (pullback.snd p ρ) (pullback.snd a ρ)
              (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.map (algebraMap B S)))))
              (Scheme.quotientBaseChangeEtaleLift B S J p s hs) y) := by
  let := Fintype.ofFinite σ
  obtain ⟨I, hI, hIJ, U, hU, hpU⟩ :=
    exists_fixed_finite_locus_bad_ideal k B p J hJ
  obtain ⟨n, m, hn, hm, hnm, h⟩ :=
    exists_two_prime_quadratic_compactifications k B ℓ x I hI g hg d hd basis
      1 one_ne_zero N₀
  refine ⟨n, m, hn, hm, hnm, ?_⟩
  intro r _ hr
  obtain ⟨hdeg, hdom, y, hy, hyunique, a₀, c, _hq, hcompact⟩ := h r hr
  let L := ULift.{u} (FiniteField.Extension k ℓ r)
  let S := B ⊗[k] L
  let gS := algebraMap B S ∘ g
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap B S))
  let : IsDomain S := hdom
  let : Algebra.Smooth L S :=
    Algebra.Smooth.of_equiv (Algebra.TensorProduct.commRight k L B)
  have hxy : y.asIdeal.under B = x.asIdeal := congrArg PrimeSpectrum.asIdeal hy
  let : y.asIdeal.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under
    y.asIdeal (show (y.asIdeal.under B).IsMaximal from
      hxy.symm ▸ (inferInstance : x.asIdeal.IsMaximal))
  have hretained := exists_chosen_retained_presentation L S y
    (I.map (algebraMap B S)) gS d a₀ c hcompact
  have : IsFinite (p ∣_ U) := hpU
  obtain ⟨hUS, hpUS⟩ :=
    Scheme.finite_pullback_on_mapped_ideal_complement B S p I U hU
  refine ⟨hdeg, hdom, y, hy, hyunique, ?_⟩
  exact nonempty_originalEtalePresentation_of_chosen_retained L S y
    (I.map (algebraMap B S)) (J.map (algebraMap B S)) (Ideal.map_mono hIJ)
    gS d a₀ c hretained (pullback.snd p ρ) (pullback.snd a ρ)
    (Scheme.quotientBaseChangeEtaleLift B S J p s hs)
    (Scheme.quotientBaseChangeEtaleLift_snd B S J p s hs)
    (Scheme.quotientBaseChangeEtaleLift_isPullback B S J p s hs H)
    (Scheme.quotientBaseChange_punctured_disjoint B S J a ha)
    (Scheme.quotientBaseChange_punctured_cover B S J a hcover)
    (ρ ⁻¹ᵁ U) hUS hpUS

end QuadraticIncidence.InfinityChart
