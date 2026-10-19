module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Charts.Basic
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.FiniteChartBoundary
public import Mathlib.RingTheory.Polynomial.Ideal
/-! # The original zero section and the opposite projective chart -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
attribute [local instance] otherUnique
variable (R : Type u) [CommRing R]

lemma chartRingEquiv_ratio (i j : ULift.{u} (Fin 2)) (h : j ≠ i) :
    chartRingEquiv R i (ProjectiveSpace.coordinateRatio R _ i j) = Polynomial.X := by
  change MvPolynomial.uniqueAlgEquiv R {j // j ≠ i}
    (ProjectiveSpace.coordinateRingToPolynomial R _ i
      (ProjectiveSpace.coordinateRatio R _ i j)) = _
  rw [ProjectiveSpace.coordinateRingToPolynomial_ratio R _ i ⟨j, h⟩]
  simp

lemma chart_preimage_other (i j : ULift.{u} (Fin 2)) (h : j ≠ i) :
    chart R i ⁻¹ᵁ ProjectiveSpace.coordinateOpen R _ j =
      PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R) := by
  rw [chart, Scheme.Hom.comp_preimage,
    ProjectiveSpace.coordinateChart_preimage_coordinateOpen, SpecMap_preimage_basicOpen]
  change PrimeSpectrum.basicOpen (chartRingEquiv R i
    (ProjectiveSpace.coordinateRatio R _ i j)) = _
  rw [chartRingEquiv_ratio R i j h]

/-- The literal polynomial zero section followed by the first chart. -/
def zeroSection : Spec (.of R) ⟶ ProjectiveSpace R (ULift.{u} (Fin 2)) :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) ≫ chart R ⟨0⟩

lemma range_affine_zero :
    Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) =
      (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R) :
          Set (PrimeSpectrum (Polynomial R)))ᶜ := by
  change Set.range (PrimeSpectrum.comap (Polynomial.evalRingHom (0 : R))) = _
  rw [range_comap_of_surjective _ _
    (fun x => ⟨Polynomial.C x, by simp⟩), Polynomial.ker_evalRingHom]
  simp only [Polynomial.C_0, sub_zero, PrimeSpectrum.zeroLocus_span]
  ext x
  simp

lemma range_zeroSection : Set.range (zeroSection R) =
    (ProjectiveSpace.coordinateOpen R (ULift.{u} (Fin 2)) ⟨1⟩ : Set _)ᶜ := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    have hy : Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) y ∉
        (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R) :
          Set (PrimeSpectrum (Polynomial R))) := by
      rw [← Set.mem_compl_iff, ← range_affine_zero R]
      exact ⟨y, rfl⟩
    change chart R ⟨0⟩ _ ∉ _
    intro hx
    apply hy
    rw [← chart_preimage_other R ⟨0⟩ ⟨1⟩ (by decide)]
    exact hx
  · intro hx
    have hx0 : x ∈ (chart R ⟨0⟩).opensRange := by
      have hxall : x ∈ ⨆ i, (chart R i).opensRange := by
        rw [iSup_chart_opensRange]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxall
      rcases i with ⟨i⟩
      fin_cases i
      · exact hi
      · exact (hx (by simpa [chart_opensRange] using hi)).elim
    obtain ⟨y, hy⟩ := hx0
    have hy0 : y ∈ Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) := by
      rw [range_affine_zero]
      change y ∉ (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R) :
          Set (PrimeSpectrum (Polynomial R)))
      rw [← chart_preimage_other R ⟨0⟩ ⟨1⟩ (by decide)]
      exact fun h => hx (hy ▸ h)
    obtain ⟨z, hz⟩ := hy0
    exact ⟨z, by simpa only [zeroSection, Scheme.Hom.comp_apply, hz] using hy⟩
end AlgebraicGeometry.RelativeProjectiveLine
