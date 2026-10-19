/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.Basic
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Constant.EtaleCurve

/-! # The original overlap and full complement in the relative compactification -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
variable (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
  {Y A : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial R))) [Etale p] [QuasiCompact p] [IsSeparated p]
  (a : A ⟶ Spec (.of (Polynomial R))) [IsOpenImmersion a]

/-- The unchanged original overlap, not a smaller parameter open. -/
def overlapInclusion : pullback p a ⟶ compactification R p :=
  pullback.fst p a ≫ inclusion R p

instance overlapInclusion_open : IsOpenImmersion (overlapInclusion R p a) := by
  dsimp [overlapInclusion]
  infer_instance

/-- Relative smoothness is supplied by the actual original étale affine-line map. -/
instance overlapInclusion_smooth :
    SmoothOfRelativeDimension 1 (overlapInclusion R p a ≫ projection R p) := by
  have := AffineLineEtaleCompactification.polynomialProjection_smooth_one R
  have he : overlapInclusion R p a ≫ projection R p =
      (pullback.fst p a ≫ p) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) := by
    simp only [overlapInclusion, Category.assoc, inclusion_projection]
  rw [he]
  exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1)
    ((pullback.fst p a ≫ p) ≫ Spec.map (CommRingCat.ofHom Polynomial.C)))

omit [IsOpenImmersion a] in
/-- The whole original overlap, whole infinity, and whole prescribed Cartesian
complement cover the compactification. No extra omitted component is permitted. -/
theorem overlap_infinity_boundary_cover
    {Z : Scheme.{u}} (z : Z ⟶ Spec (.of (Polynomial R))) (s : Z ⟶ Y)
    (H : IsPullback s (𝟙 _) p z)
    (hcomp : Set.range z = (Set.range a)ᶜ) (c : compactification R p) :
    c ∈ Set.range (overlapInclusion R p a) ∨
      c ∈ Set.range (infinityInclusion R p) ∨ c ∈ Set.range (s ≫ inclusion R p) := by
  by_cases hc : c ∈ Set.range (inclusion R p)
  · obtain ⟨y, rfl⟩ := hc
    by_cases hy : p y ∈ Set.range a
    · obtain ⟨b, hb⟩ := hy
      obtain ⟨w, hw, _⟩ := exists_preimage_of_isPullback (IsPullback.of_hasPullback p a)
        y b hb.symm
      exact Or.inl ⟨w, congrArg (inclusion R p) hw⟩
    · have hz : p y ∈ Set.range z := by rw [hcomp]; exact hy
      obtain ⟨b, hb⟩ := hz
      obtain ⟨w, hw, _⟩ := exists_preimage_of_isPullback H y b hb.symm
      exact Or.inr (Or.inr ⟨w, congrArg (inclusion R p) hw⟩)
  · right
    left
    rw [EtaleCompactification.range_infinityInclusion]
    exact hc

end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
