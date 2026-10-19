/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# The actual image of a support finite over the base

In a proper ambient scheme the scheme-theoretic image of a base-finite support
is still finite over the same base. This uses its actual kernel ideal, not a
reduced image. The native toImage map retains the full support scheme.


Intended upstream module: `Aglib.AlgebraicGeometry.Morphisms.Finite.FiniteSupportImage`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.Boundary.FiniteSourceBoundaryAffineNeighborhood`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry

universe u
namespace AlgebraicGeometry.Scheme.Hom

/-- The actual closed image has the original range because the support map is finite. -/
theorem range_imageι_of_finite_over_base {B X S : Scheme.{u}}
    (q : X ⟶ S) [IsSeparated q] (b : B ⟶ X) [IsFinite (b ≫ q)] :
    Set.range b.imageι = Set.range b := by
  have : IsFinite b := IsFinite.of_comp b q
  change Set.range b.ker.subschemeι = _
  rw [IdealSheafData.range_subschemeι, Hom.support_ker,
    (b.isClosedMap.isClosed_range).closure_eq]

/-- The full scheme-theoretic image, including its nilpotents, remains finite
 over the original base. The original support factors through it by `b.toImage`. -/
theorem isFinite_image_over_base {B X S : Scheme.{u}}
    (q : X ⟶ S) [IsProper q] (b : B ⟶ X) [IsFinite (b ≫ q)] :
    IsFinite (b.imageι ≫ q) := by
  have hrange := range_imageι_of_finite_over_base q b
  let : LocallyQuasiFinite (b.imageι ≫ q) :=
    LocallyQuasiFinite.of_finite_preimage_singleton (b.imageι ≫ q) (fun s => by
      have hsubset : b.imageι '' ((b.imageι ≫ q) ⁻¹' {s}) ⊆
          b '' ((b ≫ q) ⁻¹' {s}) := by
        rintro _ ⟨x, hx, rfl⟩
        have hxrange : b.imageι x ∈ Set.range b := hrange ▸ Set.mem_range_self x
        obtain ⟨y, hy⟩ := hxrange
        refine ⟨y, ?_, hy⟩
        change q (b y) = s
        rw [hy]
        exact hx
      exact (((b ≫ q).finite_preimage (Set.finite_singleton s)).image b).subset
        hsubset |>.of_finite_image b.imageι.isClosedEmbedding.injective.injOn)
  exact IsFinite.of_isProper_of_locallyQuasiFinite (b.imageι ≫ q)

end AlgebraicGeometry.Scheme.Hom
