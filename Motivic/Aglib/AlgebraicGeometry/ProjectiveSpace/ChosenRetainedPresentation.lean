/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.ChosenQuadraticCompactification
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.CompactRetainedPrincipalNeighborhood

/-! # A chosen quadratic compactification retains the full prescribed scheme -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial
open AlgebraicGeometry.Scheme.RelativeCurve
universe u
namespace QuadraticIncidence.InfinityChart

/-- Retain the entire prescribed quotient using the given compactification and
quadratic parameters. No parameter choice or field-cardinality hypothesis is used. -/
theorem exists_chosen_retained_presentation
    (k B : Type u) [Field k] [CommRing B] [Algebra k B]
    (P : PrimeSpectrum B)
    (I : Ideal B) {σ : Type u} [Fintype σ] (g : σ → B) (d : ℕ)
    (a : Exponent σ → k) (c : Fin d × Exponent σ → k)
    (hcompact : IsFinite (Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk I).comp (quadraticCoordinateHom k B g d c)))) ∧
      (∃ r : B,
        r - 1 ∈ Ideal.map (quadraticCoordinateHom k B g d c)
          (Ideal.comap (quadraticCoordinateHom k B g d c) P.asIdeal) ∧
        (∀ Q : PrimeSpectrum B,
          Ideal.comap (quadraticCoordinateHom k B g d c) P.asIdeal =
            Ideal.comap (quadraticCoordinateHom k B g d c) Q.asIdeal → r ∉ Q.asIdeal) ∧
        IsAffine (Scheme.Opens.toScheme (X := Spec (.of B)) (PrimeSpectrum.basicOpen r)) ∧
        SmoothOfRelativeDimension 1
          (Scheme.Opens.ι (X := Spec (.of B)) (PrimeSpectrum.basicOpen r) ≫
            Spec.map (CommRingCat.ofHom (quadraticCoordinateHom k B g d c)))) ∧
    ∃ (N D : Scheme.{u}) (i : Spec (.of B) ⟶ N)
      (π : N ⟶ ProjectiveSpace (MvPolynomial (Fin d) k) (ULift.{u} (Fin 2))) (b : D ⟶ N),
      IsIntegral N ∧ IsLocallyNoetherian N ∧
      (∀ n : N, IsIntegrallyClosed (N.presheaf.stalk n)) ∧
      IsOpenImmersion i ∧ IsFinite π ∧ IsClosedImmersion b ∧
      IsFinite (b ≫ π ≫ ProjectiveSpace.toSpec (MvPolynomial (Fin d) k) _) ∧
      Set.range b = (Set.range i)ᶜ ∧
      i ≫ π = Spec.map (CommRingCat.ofHom (quadraticRelativeCoordinateHom k B g d a c)) ≫
        RelativeProjectiveLine.chart (MvPolynomial (Fin d) k) 0 ∧
      i ≫ π ≫ ProjectiveSpace.toSpec (MvPolynomial (Fin d) k) _ =
        Spec.map (CommRingCat.ofHom (quadraticCoordinateHom k B g d c))) :
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
  obtain ⟨hZ, ⟨r, _, hr, ha, hs⟩,
    N, D, i, π, b, hN, hNoeth, hnormal, hi, hπ, hb, hbfin, hbrange, hfull, htail⟩ :=
    hcompact
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
  refine ⟨N, i, π, i ''ᵁ v, t, hN, hNoeth, hnormal, hi, hπ,
    hfull, htail, ?_, ?_, hva, hvs, ht, hbf, hav, hZ, ?_⟩
  · intro x hx
    exact ⟨x, hwhole x hx, rfl⟩
  · rintro _ ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  · intro x hx
    apply hretain x
    simpa only [hzcomp] using hx


end QuadraticIncidence.InfinityChart
