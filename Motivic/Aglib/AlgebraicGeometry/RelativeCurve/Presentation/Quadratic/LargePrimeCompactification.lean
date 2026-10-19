/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.ChosenCompactification
public import Motivic.Aglib.RingTheory.Bertini.LargePrimeQuadraticEtaleInfinity
public import Motivic.Aglib.RingTheory.Bertini.ScalarWholeFiberSmoothProjection
public import Motivic.Aglib.RingTheory.Bertini.MovingPointParameterAvoidance

/-! # Actual quadratic compactifications over the same two large prime extensions -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Module _root_.MvPolynomial
open scoped TensorProduct

namespace QuadraticIncidence.InfinityChart

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The actual H choice constructs every geometric condition of the chosen
compactification over each of the same two prime extensions. The whole marked
fiber and the original nonreduced mapped ideal are retained. -/
theorem exists_two_prime_quadratic_compactifications
    (k R : Type u) [Field k] [Finite k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.Smooth k R]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (x : PrimeSpectrum R) [x.asIdeal.IsMaximal]
    (I : Ideal R) (hI : I ≠ ⊥)
    {σ : Type u} [Fintype σ] (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (B : Basis (Fin (d + 1)) x.asIdeal.ResidueField
      (x.asIdeal.ResidueField ⊗[R] KaehlerDifferential k R))
    (q : MvPolynomial (Fin d × Exponent σ) k) (hq : q ≠ 0) (N₀ : ℕ) :
    ∃ n m : ℕ, N₀ < n ∧ N₀ < m ∧ n.Coprime m ∧
      ∀ (r : ℕ) [NeZero r], r = n ∨ r = m →
        let L := ULift.{u} (FiniteField.Extension k p r)
        let S := R ⊗[k] L
        let gS := algebraMap R S ∘ g
        Module.finrank k L = r ∧ ∃ hdom : IsDomain S,
          letI : IsDomain S := hdom
          ∃ y : PrimeSpectrum S,
            PrimeSpectrum.comap (algebraMap R S) y = x ∧
            (∀ z : PrimeSpectrum S, PrimeSpectrum.comap (algebraMap R S) z = x → z = y) ∧
          ∃ (a : Exponent σ → L) (c : Fin d × Exponent σ → L),
            eval₂ (algebraMap k L) c q ≠ 0 ∧
      IsFinite (Spec.map (CommRingCat.ofHom
        (R := MvPolynomial (Fin d) L) (S := S ⧸ I.map (algebraMap R S))
        ((Ideal.Quotient.mk (I.map (algebraMap R S))).comp (quadraticCoordinateHom L S gS d c)))) ∧
      (∃ r : S,
        r - 1 ∈ Ideal.map (quadraticCoordinateHom L S gS d c)
          (Ideal.comap (quadraticCoordinateHom L S gS d c) y.asIdeal) ∧
        (∀ Q : PrimeSpectrum S,
          Ideal.comap (quadraticCoordinateHom L S gS d c) y.asIdeal =
            Ideal.comap (quadraticCoordinateHom L S gS d c) Q.asIdeal → r ∉ Q.asIdeal) ∧
        IsAffine (Scheme.Opens.toScheme (X := Spec (.of S)) (PrimeSpectrum.basicOpen r)) ∧
        SmoothOfRelativeDimension 1
          (Scheme.Opens.ι (X := Spec (.of S)) (PrimeSpectrum.basicOpen r) ≫
            Spec.map (CommRingCat.ofHom (quadraticCoordinateHom L S gS d c)))) ∧
    ∃ (N D : Scheme.{u}) (i : Spec (.of S) ⟶ N)
      (π : N ⟶ ProjectiveSpace (MvPolynomial (Fin d) L) (ULift.{u} (Fin 2))) (b : D ⟶ N),
      IsIntegral N ∧ IsLocallyNoetherian N ∧
      (∀ n : N, IsIntegrallyClosed (N.presheaf.stalk n)) ∧
      IsOpenImmersion i ∧ IsFinite π ∧ IsClosedImmersion b ∧
      IsFinite (b ≫ π ≫ ProjectiveSpace.toSpec (MvPolynomial (Fin d) L) _) ∧
      Set.range b = (Set.range i)ᶜ ∧
      i ≫ π = Spec.map (CommRingCat.ofHom (quadraticRelativeCoordinateHom L S gS d a c)) ≫
        RelativeProjectiveLine.chart (MvPolynomial (Fin d) L) 0 ∧
      i ≫ π ≫ ProjectiveSpace.toSpec (MvPolynomial (Fin d) L) _ =
        Spec.map (CommRingCat.ofHom (quadraticCoordinateHom L S gS d c)) := by
  obtain ⟨f, hf, hz⟩ := MovingPointChart.exists_nonzero_common_parameter_relation k R
    (ClosedPoint.CoefficientRing k R x) g hg
    (fun j => ClosedPoint.selectedValue k R x (g j)) d hd
  have hd' : Algebra.trdeg k R ≤ (d : Cardinal.{u}) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hd.le
  obtain ⟨n, m, hn, hm, hnm, h⟩ := exists_two_prime_quadratic_etale_infinity
    k R p x I hI g hg d hd' B f q hf hq N₀
  refine ⟨n, m, hn, hm, hnm, ?_⟩
  intro r _ hr
  obtain ⟨hdeg, hdom, hyunique, a, c, hf', hq', hW, hZ, hD, he⟩ := h r hr
  let L := ULift.{u} (FiniteField.Extension k p r)
  let S := R ⊗[k] L
  let gS := algebraMap R S ∘ g
  let : IsDomain S := hdom
  let : Algebra.Smooth L S :=
    Algebra.Smooth.of_equiv (Algebra.TensorProduct.commRight k L R)
  obtain ⟨y, hy, hyunique⟩ := hyunique
  have hxy : y.asIdeal.under R = x.asIdeal := congrArg PrimeSpectrum.asIdeal hy
  let : y.asIdeal.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under
    (R := R) (S := S) y.asIdeal (by rw [hxy]; infer_instance)
  have hgS : Algebra.adjoin L (Set.range gS) = ⊤ := by
    let e := Algebra.TensorProduct.commRight k L R
    have ht := Algebra.TensorProduct.adjoin_one_tmul_image_eq_top
      (R := k) (A := L) (Set.range g) hg
    have hm := congrArg (Subalgebra.map e.toAlgHom) ht
    rw [← Algebra.adjoin_image, Algebra.map_top,
      (AlgHom.range_eq_top e.toAlgHom).mpr e.surjective] at hm
    have hset : e '' ((fun x : R => (1 : L) ⊗ₜ[k] x) '' Set.range g) =
        Set.range gS := by
      rw [← Set.image_comp, ← Set.range_comp]
      rfl
    change Algebra.adjoin L
      (e '' ((fun x : R => (1 : L) ⊗ₜ[k] x) '' Set.range g)) = ⊤ at hm
    rw [hset] at hm
    exact hm
  refine ⟨hdeg, hdom, y, hy, hyunique, a, c, hq', ?_⟩
  apply exists_chosen_quadratic_compactification L S y (I.map (algebraMap R S))
    gS hgS d a c hZ hW (he y hy)
  intro Q hQ
  exact exists_scalar_wholeFiber_smooth_projection k R L x y hy
    g hg d B f c hf' hz hD hd Q hQ

end QuadraticIncidence.InfinityChart
