/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Open.FiniteMarkedOpenDescent
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.BaseChange.FiniteScalarComparison
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Noetherian

/-! # An original affine open inside two actual scalar opens

Full fibers over the original mark are retained, not just chosen lifts.
The original affine open has scalar preimages contained in the given opens;
no equality or descent of those arbitrary extension opens is asserted.
Factor maps live over each extension field and use actual open immersions.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  [Module.Finite k L] [Algebra.IsSeparable k L]

/-- Containment of the whole scalar preimage gives a map from the actual native
field base change of the original open into the specified extension open. -/
theorem exists_fieldBaseChange_open_factor
    (X : SmoothSite (Spec (.of k))) (U : X.left.Opens)
    (V : ((fieldBaseChange (algebraMap k L)).obj X).left.Opens)
    (hUV : (finiteScalarProjection (E := L) X).left ⁻¹ᵁ U ≤ V) :
    let U₀ := mk (U.ι ≫ X.hom)
    let V₀ := mk (V.ι ≫ ((fieldBaseChange (algebraMap k L)).obj X).hom)
    let j : U₀ ⟶ X := homMk U.ι rfl
    let i : V₀ ⟶ (fieldBaseChange (algebraMap k L)).obj X := homMk V.ι rfl
    ∃ e : (fieldBaseChange (algebraMap k L)).obj U₀ ⟶ V₀,
      e ≫ i = (fieldBaseChange (algebraMap k L)).map j := by
  dsimp only
  let U₀ := mk (U.ι ≫ X.hom)
  let j : U₀ ⟶ X := homMk U.ι rfl
  let m := (fieldBaseChange (algebraMap k L)).map j
  have hn : m.left ≫ (finiteScalarProjection (E := L) X).left =
      (finiteScalarProjection (E := L) U₀).left ≫ U.ι :=
    baseChange_map_fst (Spec.map (CommRingCat.ofHom (algebraMap k L))) j
  have hr : Set.range m.left ⊆ Set.range V.ι := by
    rintro _ ⟨y, rfl⟩
    have hy : (finiteScalarProjection (E := L) X).left (m.left y) ∈ U := by
      have he := congrArg (fun f => f y) hn
      change (finiteScalarProjection (E := L) X).left (m.left y) =
        U.ι ((finiteScalarProjection (E := L) U₀).left y) at he
      rw [he]
      exact ((finiteScalarProjection (E := L) U₀).left y).property
    exact ⟨⟨m.left y, hUV hy⟩, rfl⟩
  let e := IsOpenImmersion.lift V.ι m.left hr
  have he : e ≫ V.ι = m.left := IsOpenImmersion.lift_fac _ _ _
  refine ⟨homMk e ?_, ?_⟩
  · change e ≫ (V.ι ≫ _) = _
    rw [← Category.assoc, he, MorphismProperty.Over.w]
  · apply MorphismProperty.Over.Hom.ext
    exact he

variable {E : Type u} [Field E] [Algebra k E]
  [Module.Finite k E] [Algebra.IsSeparable k E]

/-- The two complete scalar fibers over a mark admit one original affine open,
with actual factor maps into both native extension opens. -/
theorem exists_common_affine_scalar_open
    (X : SmoothSite (Spec (.of k))) (x : X.left)
    (V : ((fieldBaseChange (algebraMap k E)).obj X).left.Opens)
    (W : ((fieldBaseChange (algebraMap k L)).obj X).left.Opens)
    (hV : (finiteScalarProjection (E := E) X).left ⁻¹' {x} ⊆
      (V : Set ((fieldBaseChange (algebraMap k E)).obj X).left))
    (hW : (finiteScalarProjection (E := L) X).left ⁻¹' {x} ⊆
      (W : Set ((fieldBaseChange (algebraMap k L)).obj X).left)) :
    ∃ U : X.left.Opens, IsAffineOpen U ∧ x ∈ U ∧
      (finiteScalarProjection (E := E) X).left ⁻¹ᵁ U ≤ V ∧
      (finiteScalarProjection (E := L) X).left ⁻¹ᵁ U ≤ W ∧
      let U₀ := mk (U.ι ≫ X.hom)
      let j : U₀ ⟶ X := homMk U.ι rfl
      let V₀ := mk (V.ι ≫ ((fieldBaseChange (algebraMap k E)).obj X).hom)
      let W₀ := mk (W.ι ≫ ((fieldBaseChange (algebraMap k L)).obj X).hom)
      let iV : V₀ ⟶ (fieldBaseChange (algebraMap k E)).obj X := homMk V.ι rfl
      let iW : W₀ ⟶ (fieldBaseChange (algebraMap k L)).obj X := homMk W.ι rfl
      ∃ (eV : (fieldBaseChange (algebraMap k E)).obj U₀ ⟶ V₀)
        (eW : (fieldBaseChange (algebraMap k L)).obj U₀ ⟶ W₀),
        eV ≫ iV = (fieldBaseChange (algebraMap k E)).map j ∧
        eW ≫ iW = (fieldBaseChange (algebraMap k L)).map j := by
  obtain ⟨B, hx, hBV, hBW⟩ :=
    (finiteScalarProjection (E := E) X).left.exists_common_marked_open
      (finiteScalarProjection (E := L) X).left V W {x} hV hW
  obtain ⟨U, hU, hxU, hUB⟩ :=
    exists_isAffineOpen_mem_and_subset (hx (show x ∈ ({x} : Set X.left) from rfl))
  have hUV : (finiteScalarProjection (E := E) X).left ⁻¹ᵁ U ≤ V :=
    fun y hy => hBV (hUB hy)
  have hUW : (finiteScalarProjection (E := L) X).left ⁻¹ᵁ U ≤ W :=
    fun y hy => hBW (hUB hy)
  refine ⟨U, hU, hxU, hUV, hUW, ?_⟩
  obtain ⟨eV, heV⟩ := exists_fieldBaseChange_open_factor X U V hUV
  obtain ⟨eW, heW⟩ := exists_fieldBaseChange_open_factor X U W hUW
  exact ⟨eV, eW, heV, heW⟩

end AlgebraicGeometry.Scheme.SmoothSite
