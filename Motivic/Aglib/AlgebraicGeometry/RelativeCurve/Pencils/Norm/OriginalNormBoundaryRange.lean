/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.OriginalRetainedNormMaps
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Marked.ResidualFiberPullback
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.FullBoundaryProduct
/-! # The entire original inverse boundary lies in the chosen source boundary

Only the original inverse-infinity and residual-fiber factor maps are used.
Containment is used to factor through opens, never to compare functions on a
nonreduced closed scheme. No equality with a retained-open complement is assumed.

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.OriginalNormBoundaryRange`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Correction.FunctionalUnitBoundary`, `Correction.NormBoundaryCover`,
`Norm.SectionPairNormNeighborhood`.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Hom

/-- The range of the actual two-component scheme map is the union of its ranges. -/
theorem range_coprod_desc {D E C : Scheme.{u}} (d : D ⟶ C) (e : E ⟶ C) :
    Set.range (coprod.desc d e) = Set.range d ∪ Set.range e := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨y | y, rfl⟩ := (coprodMk D E).surjective y
    · rw [coprodMk_inl]
      exact Or.inl ⟨y, by simp [← Scheme.Hom.comp_apply]⟩
    · rw [coprodMk_inr]
      exact Or.inr ⟨y, by simp [← Scheme.Hom.comp_apply]⟩
  · rintro (⟨y, rfl⟩ | ⟨y, rfl⟩)
    · exact ⟨(coprod.inl : D ⟶ D ⨿ E) y, by simp [← Scheme.Hom.comp_apply]⟩
    · exact ⟨(coprod.inr : E ⟶ D ⨿ E) y, by simp [← Scheme.Hom.comp_apply]⟩

/-- The two full boundary products with an arbitrary unchanged parameter. -/
def normFullBoundaryMap {S P A D Z : Scheme.{u}}
    (π : P ⟶ S) (b : A ⟶ S) (d : D ⟶ P) (z : Z ⟶ P) :=
  coprod.desc (RelativeCurvePencil.retainedProductInclusion b π d)
    (RelativeCurvePencil.retainedProductInclusion b π z)

/-- The range calculation keeps both boundary scheme structures untouched. -/
theorem range_normFullBoundaryMap {S P A D Z : Scheme.{u}}
    (π : P ⟶ S) (b : A ⟶ S) (d : D ⟶ P) (z : Z ⟶ P) :
    Set.range (normFullBoundaryMap π b d z) =
      (pullback.snd b π) ⁻¹' (Set.range d ∪ Set.range z) := by
  rw [normFullBoundaryMap, range_coprod_desc, Set.preimage_union]
  congr 1
  · exact Scheme.range_snd_eq_preimage_of_isPullback _ _ _ _
      (RelativeCurvePencil.retainedProductInclusion_isPullback b π d)
  · exact Scheme.range_snd_eq_preimage_of_isPullback _ _ _ _
      (RelativeCurvePencil.retainedProductInclusion_isPullback b π z)

/-- The original graph-boundary presentation has the same full support formula. -/
theorem range_fullBoundaryProductMap {S C Y D Z : Scheme.{u}}
    (q : C ⟶ S) (j : Y ⟶ C) (d : D ⟶ C) (s : Z ⟶ Y) :
    Set.range (fullBoundaryProductMap q j d s) =
      (pullback.snd (j ≫ q) q) ⁻¹' (Set.range d ∪ Set.range (s ≫ j)) := by
  rw [fullBoundaryProductMap, range_coprod_desc, Set.preimage_union]
  congr 1
  · exact Scheme.Pullback.range_fst _ _
  · exact Scheme.range_snd_eq_preimage_of_isPullback _ _ _ _
      (graphBoundaryRestriction_isPullback q j s).flip

variable {S C P A Y Z D I : Scheme.{u}}
  (π : P ⟶ S) (f : C ⟶ P) [IsFinite f]
  (j : Y ⟶ C) [IsOpenImmersion j] (z : Z ⟶ P) [IsClosedImmersion z]
  (s : Z ⟶ Y) (hs : (s ≫ j) ≫ f = z)
  (d : D ⟶ C) (i : I ⟶ P)
  (bI : pullback f i ⟶ D) (hbI : bI ≫ d = pullback.fst f i)
  (bE : (Scheme.residualMarkedFiberOpen f j z s hs).toScheme ⟶ D)
  (hbE : bE ≫ d = Scheme.residualMarkedFiberMap f j z s hs)

omit [IsOpenImmersion j] [IsClosedImmersion z] in
include hbI hbE in
/-- Every original inverse-boundary point is either marked or belongs to the
chosen boundary, using the whole inverse infinity and whole residual fiber. -/
theorem preimage_originalBoundary_subset :
    f ⁻¹' (Set.range i ∪ Set.range z) ⊆ Set.range d ∪ Set.range (s ≫ j) := by
  intro x hx
  rcases hx with ⟨y, hy⟩ | ⟨y, hy⟩
  · obtain ⟨v, hv, _⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
    left
    refine ⟨bI v, ?_⟩
    exact (congrArg (fun m => m v) hbI).trans hv
  · obtain ⟨v, hv, _⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
    by_cases h : v ∈ Set.range (Scheme.markedFiberSection f j z s hs)
    · obtain ⟨w, rfl⟩ := h
      right
      refine ⟨w, ?_⟩
      exact (congrArg (fun m => m w) (Scheme.markedFiberSection_fst f j z s hs)).symm.trans hv
    · left
      let v' : (Scheme.residualMarkedFiberOpen f j z s hs).toScheme := ⟨v, h⟩
      refine ⟨bE v', ?_⟩
      exact (congrArg (fun m => m v') hbE).trans hv

omit [IsOpenImmersion j] [IsClosedImmersion z] in
include hbI hbE in
/-- The original norm map on products retains the entire inverse boundary. -/
theorem normProductMap_preimage_fullBoundary_subset (b : A ⟶ S) :
    (normProductMap π f b) ⁻¹' Set.range (normFullBoundaryMap π b i z) ⊆
      Set.range (normFullBoundaryMap (f ≫ π) b d (s ≫ j)) := by
  rw [range_normFullBoundaryMap, range_normFullBoundaryMap]
  intro x hx
  apply preimage_originalBoundary_subset f j z s hs d i bI hbI bE hbE
  change f ((pullback.snd b (f ≫ π)) x) ∈ Set.range i ∪ Set.range z
  have he := congrArg (fun m => m x) (normProductMap_snd π f b)
  exact he ▸ hx

omit [IsOpenImmersion j] [IsClosedImmersion z] in
include hbI hbE in
/-- In the original source-parameter instance the containment lands in the
literal fullBoundaryProductMap used to prescribe the original sections. -/
theorem graphProductMap_preimage_fullBoundary_subset :
    (graphProductMap π f j) ⁻¹' Set.range (normFullBoundaryMap π (j ≫ f ≫ π) i z) ⊆
      Set.range (fullBoundaryProductMap (f ≫ π) j d s) := by
  rw [range_fullBoundaryProductMap]
  intro x hx
  have h := normProductMap_preimage_fullBoundary_subset π f j z s hs d i bI hbI bE hbE
    (j ≫ f ≫ π) hx
  rwa [range_normFullBoundaryMap] at h

end AlgebraicGeometry.Scheme.Hom
