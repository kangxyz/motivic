module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.BoundaryFrame
/-! # One source frame retains the whole finite boundary after an actual base shrink -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Hom

/-- The frame is chosen around the entire finite boundary fibre, not merely one marked point.
Properness of the finite boundary then retains all of it over a genuine base neighborhood. -/
theorem exists_relativeBoundaryFrame_over_base_neighborhood
    {S X Z : Scheme.{u}} (q : X ⟶ S) [IsSeparated q]
    [SmoothOfRelativeDimension 1 q] [IsAffine X]
    (z : Z ⟶ X) [IsFinite (z ≫ q)] (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ V : S.Opens, q x ∈ V ∧
      (∀ t : Z, (z ≫ q) t ∈ V → z t ∈ U) ∧
      Nonempty ((idealModule (boundaryGraphTarget q z)).restrict
        ((pullback.fst q (z ≫ q)) ⁻¹ᵁ U).ι ≅
          SheafOfModules.unit ((pullback.fst q (z ≫ q)) ⁻¹ᵁ U).toScheme.ringCatSheaf) := by
  let f := z ≫ q
  let points : Set X := {x} ∪ z '' (f ⁻¹' {q x})
  have hp : points.Finite := (Set.finite_singleton x).union
    ((f.finite_preimage_singleton (q x)).image z)
  obtain ⟨U, hU, e⟩ := exists_relativeBoundaryFrame_around_finite q z points hp
  let V : S.Opens := ⟨(f '' (z ⁻¹' (U : Set X))ᶜ)ᶜ,
    (f.isClosedMap _ ((U.isOpen.preimage z.continuous).isClosed_compl)).isOpen_compl⟩
  refine ⟨U, hU (Or.inl rfl), V, ?_, ?_, e⟩
  · rintro ⟨t, ht, he⟩
    exact ht (hU (Or.inr ⟨t, he, rfl⟩))
  · intro t ht
    change f t ∉ f '' (z ⁻¹' (U : Set X))ᶜ at ht
    by_contra hn
    exact ht ⟨t, hn, rfl⟩
end AlgebraicGeometry.Scheme.Hom
