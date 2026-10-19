/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.SimultaneousCompactification
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Compactification.Retained.CompactRetainedPrincipalNeighborhood

/-! # Actual simultaneous quadratic presentation with an affine retained curve -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry _root_.MvPolynomial
open AlgebraicGeometry.Scheme.RelativeCurve
universe u
namespace QuadraticIncidence.InfinityChart

/-- One original quadratic tuple gives the normal finite compactification, an affine
smooth retained curve, and a single principal base shrink on which the complete new
boundary is finite and the full original nonreduced prescribed scheme is retained. -/
theorem exists_simultaneous_retained_presentation
    (k B : Type u) [Field k] [Infinite k] [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.Smooth k B] (P : PrimeSpectrum B) [P.asIdeal.IsMaximal]
    (I : Ideal B) (hI : I ≠ ⊥) {σ : Type u} [Fintype σ] (g : σ → B)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k B = (d + 1 : ℕ))
    (q : MvPolynomial (Fin d × Exponent σ) k) (hq : q ≠ 0) :
    ∃ (a : Exponent σ → k) (c : Fin d × Exponent σ → k), eval c q ≠ 0 ∧
    ∃ (N : Scheme.{u}) (i : Spec (.of B) ⟶ N)
      (π : N ⟶ ProjectiveSpace (MvPolynomial (Fin d) k) (ULift.{u} (Fin 2)))
      (V : N.Opens) (t : MvPolynomial (Fin d) k),
      IsIntegral N ∧ IsLocallyNoetherian N ∧
      (∀ n : N, IsIntegrallyClosed (N.presheaf.stalk n)) ∧
      IsOpenImmersion i ∧ IsFinite π ∧
      i ≫ π = Spec.map (CommRingCat.ofHom (quadraticRelativeCoordinateHom k B g d a c)) ≫
        RelativeProjectiveLine.chart (MvPolynomial (Fin d) k) 0 ∧
      i ≫ π ≫ ProjectiveSpace.toSpec (MvPolynomial (Fin d) k) _ =
        Spec.map (CommRingCat.ofHom (quadraticCoordinateHom k B g d c)) ∧
      (∀ x : Spec (.of B),
        Spec.map (CommRingCat.ofHom (quadraticCoordinateHom k B g d c)) x =
          Spec.map (CommRingCat.ofHom (quadraticCoordinateHom k B g d c)) P → i x ∈ V) ∧
      (V : Set N) ⊆ Set.range i ∧ IsAffine V.toScheme ∧
      SmoothOfRelativeDimension 1 (V.ι ≫ π ≫ ProjectiveSpace.toSpec _ _) ∧
      Spec.map (CommRingCat.ofHom (quadraticCoordinateHom k B g d c)) P ∈
        PrimeSpectrum.basicOpen t ∧
      IsFinite ((retainedBoundaryInclusion V ≫ π ≫ ProjectiveSpace.toSpec _ _) ∣_
        PrimeSpectrum.basicOpen t) ∧
      IsAffine (((V.ι ≫ π ≫ ProjectiveSpace.toSpec _ _) ⁻¹ᵁ
        PrimeSpectrum.basicOpen t).toScheme) ∧
      IsFinite (Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk I).comp (quadraticCoordinateHom k B g d c)))) ∧
      ∀ z : Spec (.of (B ⧸ I)),
        (Spec.map (CommRingCat.ofHom
          ((Ideal.Quotient.mk I).comp (quadraticCoordinateHom k B g d c)))) z ∈
            PrimeSpectrum.basicOpen t →
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ i) z ∈ V := by
  obtain ⟨a, c, hc, hZ, ⟨r, _, hr, ha, hs⟩,
    N, D, i, π, b, hN, hNoeth, hnormal, hi, hπ, hb, hbfin, hbrange, hfull, htail⟩ :=
    exists_simultaneous_quadratic_compactification k B P I hI g hg d hd q hq
  let f := Spec.map (CommRingCat.ofHom (quadraticCoordinateHom k B g d c))
  let v : (Spec (.of B)).Opens := PrimeSpectrum.basicOpen r
  let z := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let p := π ≫ ProjectiveSpace.toSpec (MvPolynomial (Fin d) k) _
  have : IsOpenImmersion i := hi
  have : IsFinite π := hπ
  have : IsFinite (b ≫ p) := hbfin
  have : IsAffine v.toScheme := ha
  have : SmoothOfRelativeDimension 1 (v.ι ≫ f) := hs
  have hzcomp : z ≫ f = Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk I).comp (quadraticCoordinateHom k B g d c))) := by
    exact (Spec.map_comp _ _).symm
  have : IsFinite (z ≫ f) := hzcomp.symm ▸ hZ
  have hwhole : ∀ x : Spec (.of B), f x = f P → x ∈ v := by
    intro x hx
    apply hr x
    exact (congrArg PrimeSpectrum.asIdeal hx).symm
  obtain ⟨t, ht, hva, hvs, hbf, hav, hretain⟩ :=
    exists_compact_retained_principal_neighborhood (MvPolynomial (Fin d) k)
      i p f htail b hbrange v (f P) hwhole z
  refine ⟨a, c, hc, N, i, π, i ''ᵁ v, t, hN, hNoeth, hnormal, hi, hπ,
    hfull, htail, ?_, ?_, hva, hvs, ht, hbf, hav, hZ, ?_⟩
  · intro x hx
    exact ⟨x, hwhole x hx, rfl⟩
  · rintro _ ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  · intro x hx
    apply hretain x
    simpa only [hzcomp] using hx

end QuadraticIncidence.InfinityChart
