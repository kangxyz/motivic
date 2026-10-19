/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.ProjectionFinite
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.Charts.RelativeCoordinates
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.Boundary.CoordinateBoundary

/-! # Actual normal compactification and full finite infinity from the same quadratic tuple -/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry _root_.MvPolynomial
universe u
namespace QuadraticIncidence.InfinityChart

/-- Infinity avoidance and the selected étale chart produce one actual normal
relative curve compactification. The finite map and full finite boundary are conclusions. -/
theorem exists_quadratic_normal_compactification
    (k B : Type u) [Field k] [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.Smooth k B] {σ : Type u} [Fintype σ] (g : σ → B)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (a : Exponent σ → k) (c : Fin d × Exponent σ → k)
    (hW : NoCommonInfinityZero k B g d (prependParameters k d a c))
    (p : PrimeSpectrum B) (r : B) (hr : r ∉ p.asIdeal)
    (he : ((algebraMap B (Localization.Away r)).comp
      (quadraticCoordinateHom k B g (d + 1) (prependParameters k d a c))).Etale) :
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
        Spec.map (CommRingCat.ofHom (quadraticCoordinateHom k B g d c)) := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have hfinite := quadraticTupleMap_isFinite k B g d hg (prependParameters k d a c) hW
  have hf : (quadraticRelativeCoordinateHom k B g d a c).Finite :=
    relativeCoordinateHom_finite k B d _ ((IsFinite.SpecMap_iff _).mp hfinite)
  have he' : ((algebraMap B (Localization.Away r)).comp
      (quadraticRelativeCoordinateHom k B g d a c)).Etale :=
    relativeCoordinateHom_etale_away k B d _ r he
  obtain ⟨N, i, π, hN, hnoeth, hnormal, hi, hπ, _, hw, hfull⟩ :=
    exists_normal_projectiveLine_cover_of_finite_coordinates k (MvPolynomial (Fin d) k) B
      (quadraticRelativeCoordinateHom k B g d a c) hf p r hr he'
  have := hi
  have := hπ
  let D := Scheme.RelativeCurve.retainedBoundary i.opensRange
  let b : D ⟶ N := Scheme.RelativeCurve.retainedBoundaryInclusion i.opensRange
  refine ⟨N, D, i, π, b, hN, hnoeth, hnormal, hi, hπ, inferInstance,
    finite_retainedBoundary_of_full_projectiveLine_chart _ π i hfull, ?_, hw, ?_⟩
  · exact Scheme.RelativeCurve.range_retainedBoundaryInclusion i.opensRange
  · rw [← Category.assoc, hw, Category.assoc, RelativeProjectiveLine.chart_toSpec,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, quadraticRelativeCoordinateHom_comp_C]

end QuadraticIncidence.InfinityChart
