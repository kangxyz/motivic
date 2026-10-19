module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.RelativeCurve.LocalBaseFrame
public import Motivic.Aglib.AlgebraicGeometry.QuasiAffine.FiniteNeighborhood
/-! # Affine source frames retaining the full relative boundary after base shrinking -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Hom

private theorem affineOpen_inside {X : Scheme.{u}} [IsAffine X]
    (U : X.Opens) (P : Set X) (hP : P.Finite) (hPU : P ⊆ U) :
    ∃ W : X.Opens, IsAffineOpen W ∧ P ⊆ W ∧ W ≤ U := by
  obtain ⟨r, hr, hrU⟩ := PrimeSpectrum.exists_basicOpen_of_finite_subset
    (X.toSpecΓ ''ᵁ U) (X.toSpecΓ '' P) (hP.image _) (Set.image_mono hPU)
  refine ⟨X.basicOpen r, (isAffineOpen_top X).basicOpen r, ?_, ?_⟩
  · intro x hx
    rw [← X.toSpecΓ_preimage_basicOpen]
    exact hr (Set.mem_image_of_mem _ hx)
  · intro x hx
    rw [← X.toSpecΓ_preimage_basicOpen] at hx
    obtain ⟨y, hy, he⟩ := hrU hx
    exact (Scheme.Hom.injective X.toSpecΓ he) ▸ hy

/-- The unchanged full boundary over a base neighborhood lies in an actual affine source
open carrying the original graph-ideal frame. No infinite-field argument is used. -/
theorem exists_affine_relativeBoundaryFrame_over_base_neighborhood
    {S X Z : Scheme.{u}} (q : X ⟶ S) [IsSeparated q]
    [SmoothOfRelativeDimension 1 q] [IsAffine X]
    (z : Z ⟶ X) [IsFinite (z ≫ q)] (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∃ V : S.Opens, q x ∈ V ∧
      (∀ t : Z, (z ≫ q) t ∈ V → z t ∈ U) ∧
      Nonempty ((idealModule (boundaryGraphTarget q z)).restrict
        ((pullback.fst q (z ≫ q)) ⁻¹ᵁ U).ι ≅
          SheafOfModules.unit ((pullback.fst q (z ≫ q)) ⁻¹ᵁ U).toScheme.ringCatSheaf) := by
  let f := z ≫ q
  let P : Set X := {x} ∪ z '' (f ⁻¹' {q x})
  have hP : P.Finite := (Set.finite_singleton x).union
    ((f.finite_preimage_singleton (q x)).image z)
  obtain ⟨U, hU, ⟨e⟩⟩ := exists_relativeBoundaryFrame_around_finite q z P hP
  obtain ⟨W, hW, hPW, hWU⟩ := affineOpen_inside U P hP hU
  let V : S.Opens := ⟨(f '' (z ⁻¹' (W : Set X))ᶜ)ᶜ,
    (f.isClosedMap _ ((W.isOpen.preimage z.continuous).isClosed_compl)).isOpen_compl⟩
  refine ⟨W, hW, hPW (Or.inl rfl), V, ?_, ?_, ?_⟩
  · rintro ⟨t, ht, he⟩
    exact ht (hPW (Or.inr ⟨t, he, rfl⟩))
  · intro t ht
    change f t ∉ f '' (z ⁻¹' (W : Set X))ᶜ at ht
    by_contra hn
    exact ht ⟨t, hn, rfl⟩
  · exact ⟨restrictUnitIsoOfLE (relativeBoundaryGraphLine q z).val
      (fun _ hx => hWU hx) e⟩
end AlgebraicGeometry.Scheme.Hom
