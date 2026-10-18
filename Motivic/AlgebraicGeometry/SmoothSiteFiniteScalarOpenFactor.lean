/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSiteFiniteScalarMarkedOpen

/-! # Actual scalar open factors over one original affine neighborhood

The extension opens remain their actual smooth-site objects. Retention of both
entire scalar fibers supplies a common original affine open; open-immersion
lifting gives literal factor maps to the two produced objects. This asserts
containment, not descent equality for arbitrary extension opens.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.SmoothSite

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  [Module.Finite k L] [Algebra.IsSeparable k L]

/-- An original scalar preimage contained in an actual open immersion factors
through its actual source, with the original base-change equation. -/
theorem exists_fieldBaseChange_factor_of_open_range
    (X : SmoothSite (Spec (.of k))) (U : X.left.Opens)
    {B : SmoothSite (Spec (.of L))}
    (i : B ⟶ (fieldBaseChange (algebraMap k L)).obj X) [IsOpenImmersion i.left]
    (hU : (finiteScalarProjection (E := L) X).left ⁻¹ᵁ U ≤ i.left.opensRange) :
    let U₀ := mk (U.ι ≫ X.hom)
    let j : U₀ ⟶ X := homMk U.ι rfl
    ∃ b : (fieldBaseChange (algebraMap k L)).obj U₀ ⟶ B,
      b ≫ i = (fieldBaseChange (algebraMap k L)).map j := by
  dsimp only
  let U₀ := mk (U.ι ≫ X.hom)
  let j : U₀ ⟶ X := homMk U.ι rfl
  let m := (fieldBaseChange (algebraMap k L)).map j
  obtain ⟨e, he⟩ := exists_fieldBaseChange_open_factor X U i.left.opensRange hU
  have hr : Set.range m.left ⊆ Set.range i.left := by
    rintro _ ⟨y, rfl⟩
    have hm := congrArg (fun f => f.left y) he
    change i.left.opensRange.ι (e.left y) = m.left y at hm
    rw [← hm]
    exact (e.left y).property
  let b₀ := IsOpenImmersion.lift i.left m.left hr
  have hb₀ : b₀ ≫ i.left = m.left := IsOpenImmersion.lift_fac _ _ _
  refine ⟨homMk b₀ ?_, ?_⟩
  · rw [← MorphismProperty.Over.w i, ← Category.assoc, hb₀,
      MorphismProperty.Over.w m]
  · apply MorphismProperty.Over.Hom.ext
    exact hb₀

variable {E : Type u} [Field E] [Algebra k E]
  [Module.Finite k E] [Algebra.IsSeparable k E]

/-- Two actual scalar open immersions retaining the entire fibers over a mark
admit concrete factors from the same original affine neighborhood. -/
theorem exists_common_affine_scalar_open_factor
    (X : SmoothSite (Spec (.of k))) (x : X.left)
    {BE : SmoothSite (Spec (.of E))} {BL : SmoothSite (Spec (.of L))}
    (iE : BE ⟶ (fieldBaseChange (algebraMap k E)).obj X) [IsOpenImmersion iE.left]
    (iL : BL ⟶ (fieldBaseChange (algebraMap k L)).obj X) [IsOpenImmersion iL.left]
    (hE : (finiteScalarProjection (E := E) X).left ⁻¹' {x} ⊆ Set.range iE.left)
    (hL : (finiteScalarProjection (E := L) X).left ⁻¹' {x} ⊆ Set.range iL.left) :
    ∃ (U : X.left.Opens) (hU : IsAffineOpen U), x ∈ U ∧
      let : IsAffine U.toScheme := hU
      let U₀ := mk (U.ι ≫ X.hom)
      let j : U₀ ⟶ X := homMk U.ι rfl
      ∃ (bE : (fieldBaseChange (algebraMap k E)).obj U₀ ⟶ BE)
        (bL : (fieldBaseChange (algebraMap k L)).obj U₀ ⟶ BL),
        bE ≫ iE = (fieldBaseChange (algebraMap k E)).map j ∧
        bL ≫ iL = (fieldBaseChange (algebraMap k L)).map j := by
  obtain ⟨U, hU, hxU, hUE, hUL, _⟩ := exists_common_affine_scalar_open X x
    iE.left.opensRange iL.left.opensRange hE hL
  obtain ⟨bE, hbE⟩ := exists_fieldBaseChange_factor_of_open_range X U iE hUE
  obtain ⟨bL, hbL⟩ := exists_fieldBaseChange_factor_of_open_range X U iL hUL
  exact ⟨U, hU, hxU, bE, bL, hbE, hbL⟩

end Motivic.SmoothSite
