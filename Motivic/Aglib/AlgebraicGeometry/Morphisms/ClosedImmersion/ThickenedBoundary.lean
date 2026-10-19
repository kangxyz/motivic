/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# A scheme-theoretic thickening of a closed boundary

The scheme-theoretic image of the coproduct of three actual closed immersions
contains all three as schemes, not merely their reduced supports. If the two
extra supports lie in the first boundary, the new boundary has the same support.
Properness of the ambient projection and finiteness of the old boundary then
imply finiteness of this thickening. The extra closed schemes are explicit inputs;
this leaf does not construct a residual norm fiber or choose pencil sections.


Intended upstream module: `Aglib.AlgebraicGeometry.Morphisms.ClosedImmersion.ThickenedBoundary`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.Boundary.ThickenedBoundary`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u
namespace AlgebraicGeometry.Scheme

private theorem range_coprod_desc_boundary {D E C : Scheme.{u}}
    (d : D ⟶ C) (e : E ⟶ C) :
    Set.range (coprod.desc d e) = Set.range d ∪ Set.range e := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨y | y, rfl⟩ := (coprodMk D E).surjective y
    · rw [coprodMk_inl]
      left
      exact ⟨y, by simp [← Scheme.Hom.comp_apply]⟩
    · rw [coprodMk_inr]
      right
      exact ⟨y, by simp [← Scheme.Hom.comp_apply]⟩
  · rintro (⟨y, rfl⟩ | ⟨y, rfl⟩)
    · exact ⟨(coprod.inl : D ⟶ D ⨿ E) y, by simp [← Scheme.Hom.comp_apply]⟩
    · exact ⟨(coprod.inr : E ⟶ D ⨿ E) y, by simp [← Scheme.Hom.comp_apply]⟩

/-- Form the actual closed union, retaining full scheme factorizations of the old
boundary and both additional closed schemes. Range containment is used only to
identify supports, never to factor through the old (possibly reduced) boundary. -/
theorem exists_thickened_closed_boundary
    {C S Y D E F : Scheme.{u}} (q : C ⟶ S) [IsProper q]
    (j : Y ⟶ C) (d : D ⟶ C) (e : E ⟶ C) (f : F ⟶ C)
    [IsClosedImmersion d] [IsClosedImmersion e] [IsClosedImmersion f]
    [IsFinite (d ≫ q)]
    (he : Set.range e ⊆ Set.range d) (hf : Set.range f ⊆ Set.range d)
    (hd : Disjoint (Set.range j) (Set.range d)) :
    ∃ (D' : Scheme.{u}) (d' : D' ⟶ C), IsClosedImmersion d' ∧
      Set.range d' = Set.range d ∧ Disjoint (Set.range j) (Set.range d') ∧
      IsFinite (d' ≫ q) ∧
      ∃ (a : D ⟶ D') (b : E ⟶ D') (c : F ⟶ D'),
        a ≫ d' = d ∧ b ≫ d' = e ∧ c ≫ d' = f := by
  let unionMap : D ⨿ (E ⨿ F) ⟶ C := coprod.desc d (coprod.desc e f)
  have hU : Set.range unionMap = Set.range d := by
    rw [range_coprod_desc_boundary, range_coprod_desc_boundary]
    exact Set.union_eq_left.mpr (Set.union_subset he hf)
  let D' := unionMap.image
  let d' : D' ⟶ C := unionMap.imageι
  have hrange : Set.range d' = Set.range d := by
    change Set.range unionMap.ker.subschemeι = _
    rw [IdealSheafData.range_subschemeι, Hom.support_ker, hU,
      d.isClosedEmbedding.isClosed_range.closure_eq]
  let a : D ⟶ D' := coprod.inl ≫ unionMap.toImage
  let b : E ⟶ D' := coprod.inl ≫ coprod.inr ≫ unionMap.toImage
  let c : F ⟶ D' := coprod.inr ≫ coprod.inr ≫ unionMap.toImage
  have ha : a ≫ d' = d := by simp [a, d', unionMap]
  have hb : b ≫ d' = e := by simp [b, d', unionMap]
  have hc : c ≫ d' = f := by simp [c, d', unionMap]
  have hfinite : IsFinite (d' ≫ q) := by
    let : LocallyQuasiFinite (d' ≫ q) :=
      LocallyQuasiFinite.of_finite_preimage_singleton (d' ≫ q) (fun s => by
        have hsubset : d' '' ((d' ≫ q) ⁻¹' {s}) ⊆ d '' ((d ≫ q) ⁻¹' {s}) := by
          rintro _ ⟨x, hx, rfl⟩
          have hxrange : d' x ∈ Set.range d := hrange ▸ Set.mem_range_self x
          obtain ⟨y, hy⟩ := hxrange
          refine ⟨y, ?_, hy⟩
          change q (d y) = s
          rw [hy]
          exact hx
        exact (((d ≫ q).finite_preimage (Set.finite_singleton s)).image d).subset
          hsubset |>.of_finite_image d'.isClosedEmbedding.injective.injOn)
    exact IsFinite.of_isProper_of_locallyQuasiFinite (d' ≫ q)
  exact ⟨D', d', inferInstance, hrange, hrange.symm ▸ hd, hfinite, a, b, c, ha, hb, hc⟩

end AlgebraicGeometry.Scheme
