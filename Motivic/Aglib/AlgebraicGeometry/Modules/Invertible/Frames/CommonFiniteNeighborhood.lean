/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Etale.Neighborhood.AffineClosedSectionNeighborhood
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# A common affine neighborhood for fixed source and target frames

The full inverse boundary lies in the fixed source frame domain. Removing the
finite closed image of its complement and refining inside the fixed target
frame domain gives a principal target open. No frame or section is chosen again.
No freeness of global sections on the resulting open is asserted.


Intended upstream module:
`Aglib.AlgebraicGeometry.Modules.Invertible.Frames.CommonFiniteNeighborhood`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.CommonFiniteUnitNeighborhood`.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry

universe u
namespace AlgebraicGeometry.Scheme

/-- Preserve the entire closed target boundary and both already fixed frame
domains on an actual principal affine neighborhood of the original target. -/
theorem exists_principal_common_frame_neighborhood
    {Y X Z : Scheme.{u}} [IsAffine X]
    (p : Y ⟶ X) [IsFinite p] (z : Z ⟶ X) [IsClosedImmersion z]
    (U : Y.Opens) (V : X.Opens)
    (hsource : p ⁻¹' Set.range z ⊆ U) (htarget : Set.range z ⊆ V) :
    ∃ r : Γ(X, ⊤),
      IsAffineOpen (X.basicOpen r) ∧ IsAffineOpen (p ⁻¹ᵁ X.basicOpen r) ∧
      X.basicOpen r ≤ V ∧ p ⁻¹ᵁ X.basicOpen r ≤ U ∧
      ∃ t : Z ⟶ (X.basicOpen r).toScheme, t ≫ (X.basicOpen r).ι = z := by
  let O : X.Opens := V ⊓
    ⟨(p '' (U : Set Y)ᶜ)ᶜ, (p.isClosedMap _ U.isOpen.isClosed_compl).isOpen_compl⟩
  have hZO : Set.range z ⊆ O := by
    intro x hx
    refine ⟨htarget hx, ?_⟩
    rintro ⟨y, hy, he⟩
    have hp : p y ∈ Set.range z := he.symm ▸ hx
    exact hy (hsource hp)
  obtain ⟨r, hr, hrO⟩ := exists_basicOpen_between_closed (Set.range z)
    z.isClosedEmbedding.isClosed_range O hZO
  have hW : IsAffineOpen (X.basicOpen r) := (isAffineOpen_top X).basicOpen r
  have hWU : p ⁻¹ᵁ X.basicOpen r ≤ U := by
    intro y hy
    by_contra hn
    exact (hrO hy).2 ⟨y, hn, rfl⟩
  have hz : Set.range z ⊆ Set.range (X.basicOpen r).ι := by
    simpa only [Scheme.Opens.range_ι] using hr
  exact ⟨r, hW, hW.preimage p, fun x hx => (hrO hx).1, hWU,
    IsOpenImmersion.lift (X.basicOpen r).ι z hz,
    IsOpenImmersion.lift_fac (X.basicOpen r).ι z hz⟩

end AlgebraicGeometry.Scheme
