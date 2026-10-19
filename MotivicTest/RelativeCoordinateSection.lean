module
import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.ProjectiveLine.CoordinateSection.Basic
import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Charts.BaseChange
import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.AffineZeroNeighborhood
/-! Literal original graph ideal and nonmonic affine neighborhood consumers. -/
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry RelativeProjectiveLine
universe u
variable (R : Type u) [CommRing R]
example (a : R) : Scheme.Modules.Invertible.IsLocallyRankOne
    (ProjectiveSpace R (ULift.{u} (Fin 2)))
    (Scheme.Hom.idealModule (coordinateSection R a)) :=
  coordinateSection_ideal_rankOne R a
example (A : Type u) [CommRing A] (ρ : R →+* A) (i : ULift.{u} (Fin 2)) :
    chart A i ≫ ProjectiveSpace.map ρ (ULift.{u} (Fin 2)) =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom ρ)) ≫ chart R i :=
  chart_map ρ i
example (V : (Spec (.of (Polynomial R))).Opens)
    (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
    (s : Spec (.of R)) :
    ∃ f : Polynomial R, s ∈ PrimeSpectrum.basicOpen (f.eval 0) ∧
      PrimeSpectrum.basicOpen f ≤ V := by
  obtain ⟨f, hf, hsub, _⟩ := exists_principal_zero_neighborhood R V hV s
  exact ⟨f, hf, hsub⟩
#print axioms coordinateSection_ideal_rankOne
#print axioms chart_map
#print axioms exists_principal_zero_neighborhood
