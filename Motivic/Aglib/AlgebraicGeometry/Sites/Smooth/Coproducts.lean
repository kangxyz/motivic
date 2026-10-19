/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts

/-!
# Disjoint unions in the smooth category

The binary coproduct is the literal disjoint union of the underlying schemes,
with the structure morphism induced by the two structure morphisms. Its
inclusions are open and closed immersions, and in particular finite. The
construction works over an arbitrary base scheme.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
instance coproduct_smooth (X Y : SmoothSite S) : Smooth (coprod.desc X.hom Y.hom) := by
  apply IsZariskiLocalAtSource.of_openCover (coprodOpenCover.{_, 0} X.left Y.left)
  rintro (i | i)
  · simpa [coprodOpenCover] using (inferInstance : Smooth X.hom)
  · simpa [coprodOpenCover] using (inferInstance : Smooth Y.hom)

set_option backward.isDefEq.respectTransparency false in
private theorem isSeparated_coprodDesc {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsSeparated f] [IsSeparated g] : IsSeparated (coprod.desc f g) := by
  have : IsSeparated (coprod.map f g) :=
    IsZariskiLocalAtTarget.coprodMap _ _ inferInstance inferInstance
  have : IsSeparated (coprod.map f g ≫ coprod.desc (𝟙 Z) (𝟙 Z)) := inferInstance
  simpa only [coprod.map_desc, Category.comp_id] using this

instance coproduct_isSeparated (X Y : SmoothSite S) :
    IsSeparated (coprod.desc X.hom Y.hom) := isSeparated_coprodDesc _ _

set_option backward.isDefEq.respectTransparency false in
private theorem quasiCompact_coprodDesc {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiCompact g] : QuasiCompact (coprod.desc f g) := by
  have : QuasiCompact (coprod.map f g) :=
    IsZariskiLocalAtTarget.coprodMap _ _ inferInstance inferInstance
  have : QuasiCompact (coprod.map f g ≫ coprod.desc (𝟙 Z) (𝟙 Z)) := inferInstance
  simpa only [coprod.map_desc, Category.comp_id] using this

instance coproduct_quasiCompact (X Y : SmoothSite S) :
    QuasiCompact (coprod.desc X.hom Y.hom) := quasiCompact_coprodDesc _ _

/-- The actual disjoint union, with its smooth structure morphism. -/
def coproduct (X Y : SmoothSite S) : SmoothSite S :=
  mk (coprod.desc X.hom Y.hom)

@[simp] theorem coproduct_left (X Y : SmoothSite S) :
    (coproduct X Y).left = (X.left ⨿ Y.left) := rfl

@[simp] theorem coproduct_hom (X Y : SmoothSite S) :
    (coproduct X Y).hom = coprod.desc X.hom Y.hom := rfl

/-- Inclusion of the first component of the disjoint union. -/
def coproductInl (X Y : SmoothSite S) : X ⟶ coproduct X Y :=
  homMk coprod.inl (coprod.inl_desc X.hom Y.hom)

/-- Inclusion of the second component of the disjoint union. -/
def coproductInr (X Y : SmoothSite S) : Y ⟶ coproduct X Y :=
  homMk coprod.inr (coprod.inr_desc X.hom Y.hom)

@[simp] theorem coproductInl_left (X Y : SmoothSite S) :
    (coproductInl X Y).left = coprod.inl := rfl

@[simp] theorem coproductInr_left (X Y : SmoothSite S) :
    (coproductInr X Y).left = coprod.inr := rfl

instance (X Y : SmoothSite S) : IsOpenImmersion (coproductInl X Y).left :=
  inferInstanceAs (IsOpenImmersion (coprod.inl : X.left ⟶ X.left ⨿ Y.left))

instance (X Y : SmoothSite S) : IsOpenImmersion (coproductInr X Y).left :=
  inferInstanceAs (IsOpenImmersion (coprod.inr : Y.left ⟶ X.left ⨿ Y.left))

instance (X Y : SmoothSite S) : IsClosedImmersion (coproductInl X Y).left := by
  apply IsClosedImmersion.of_isPreimmersion
  change IsClosed (Set.range (coprod.inl : X.left ⟶ X.left ⨿ Y.left))
  rw [(isCompl_range_inl_inr X.left Y.left).eq_compl]
  exact (coprod.inr : Y.left ⟶ X.left ⨿ Y.left).opensRange.isOpen.isClosed_compl

instance (X Y : SmoothSite S) : IsClosedImmersion (coproductInr X Y).left := by
  apply IsClosedImmersion.of_isPreimmersion
  change IsClosed (Set.range (coprod.inr : Y.left ⟶ X.left ⨿ Y.left))
  rw [(isCompl_range_inl_inr X.left Y.left).symm.eq_compl]
  exact (coprod.inl : X.left ⟶ X.left ⨿ Y.left).opensRange.isOpen.isClosed_compl

instance (X Y : SmoothSite S) : IsFinite (coproductInl X Y).left := inferInstance

instance (X Y : SmoothSite S) : IsFinite (coproductInr X Y).left := inferInstance

/-- Every irreducible component of a disjoint union lies in one of its two summands. -/
theorem irreducibleComponent_subset_coproduct_range (X Y : SmoothSite S)
    {C : Set (coproduct X Y).left} (hC : C ∈ irreducibleComponents (coproduct X Y).left) :
    C ⊆ Set.range (coproductInl X Y).left ∨ C ⊆ Set.range (coproductInr X Y).left := by
  refine isPreirreducible_iff_isClosed_union_isClosed.mp hC.1.2 _ _
    (coproductInl X Y).left.isClosedEmbedding.isClosed_range
    (coproductInr X Y).left.isClosedEmbedding.isClosed_range ?_
  change C ⊆ Set.range (coprod.inl : X.left ⟶ X.left ⨿ Y.left) ∪
    Set.range (coprod.inr : Y.left ⟶ X.left ⨿ Y.left)
  intro x _
  exact (isCompl_range_inl_inr X.left Y.left).sup_eq_top.ge (Set.mem_univ x)

/-- A nonempty irreducible component cannot lie in both disjoint summands. -/
theorem irreducibleComponent_not_subset_both_coproduct_ranges (X Y : SmoothSite S)
    {C : Set (coproduct X Y).left} (hC : C ∈ irreducibleComponents (coproduct X Y).left) :
    ¬ (C ⊆ Set.range (coproductInl X Y).left ∧
      C ⊆ Set.range (coproductInr X Y).left) := by
  rintro ⟨hL, hR⟩
  obtain ⟨x, hx⟩ := hC.1.1
  exact (isCompl_range_inl_inr X.left Y.left).disjoint.notMem_of_mem_left (hL hx) (hR hx)

/-- The coproduct descendent retains the original two scheme morphisms. -/
def coproductDesc {W X Y : SmoothSite S} (f : X ⟶ W) (g : Y ⟶ W) :
    coproduct X Y ⟶ W :=
  homMk (coprod.desc f.left g.left) (by
    change coprod.desc f.left g.left ≫ W.hom = coprod.desc X.hom Y.hom
    apply coprod.hom_ext
    · simpa only [coprod.inl_desc_assoc, coprod.inl_desc] using MorphismProperty.Over.w f
    · simpa only [coprod.inr_desc_assoc, coprod.inr_desc] using MorphismProperty.Over.w g)

@[simp] theorem coproductDesc_left {W X Y : SmoothSite S} (f : X ⟶ W) (g : Y ⟶ W) :
    (coproductDesc f g).left = coprod.desc f.left g.left := rfl

@[reassoc (attr := simp)]
theorem coproductInl_desc {W X Y : SmoothSite S} (f : X ⟶ W) (g : Y ⟶ W) :
    coproductInl X Y ≫ coproductDesc f g = f := by
  apply MorphismProperty.Over.Hom.ext
  exact coprod.inl_desc _ _

@[reassoc (attr := simp)]
theorem coproductInr_desc {W X Y : SmoothSite S} (f : X ⟶ W) (g : Y ⟶ W) :
    coproductInr X Y ≫ coproductDesc f g = g := by
  apply MorphismProperty.Over.Hom.ext
  exact coprod.inr_desc _ _

/-- Maps out of the disjoint union are determined by their restrictions to its components. -/
@[ext] theorem coproduct_hom_ext {W X Y : SmoothSite S} {f g : coproduct X Y ⟶ W}
    (h₁ : coproductInl X Y ≫ f = coproductInl X Y ≫ g)
    (h₂ : coproductInr X Y ≫ f = coproductInr X Y ≫ g) : f = g := by
  apply MorphismProperty.Over.Hom.ext
  exact coprod.hom_ext (congrArg (fun a => a.left) h₁) (congrArg (fun a => a.left) h₂)

/-- Disjoint union acts on arbitrary smooth-site morphisms in both components. -/
def coproductMap {X X' Y Y' : SmoothSite S} (f : X ⟶ X') (g : Y ⟶ Y') :
    coproduct X Y ⟶ coproduct X' Y' :=
  coproductDesc (f ≫ coproductInl X' Y') (g ≫ coproductInr X' Y')

@[reassoc (attr := simp)]
theorem coproductInl_map {X X' Y Y' : SmoothSite S} (f : X ⟶ X') (g : Y ⟶ Y') :
    coproductInl X Y ≫ coproductMap f g = f ≫ coproductInl X' Y' := by
  simp [coproductMap]

@[reassoc (attr := simp)]
theorem coproductInr_map {X X' Y Y' : SmoothSite S} (f : X ⟶ X') (g : Y ⟶ Y') :
    coproductInr X Y ≫ coproductMap f g = g ≫ coproductInr X' Y' := by
  simp [coproductMap]

@[simp] theorem coproductMap_id (X Y : SmoothSite S) :
    coproductMap (𝟙 X) (𝟙 Y) = 𝟙 (coproduct X Y) := by
  apply coproduct_hom_ext <;> simp

theorem coproductMap_comp {X X' X'' Y Y' Y'' : SmoothSite S}
    (f : X ⟶ X') (f' : X' ⟶ X'') (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    coproductMap (f ≫ f') (g ≫ g') = coproductMap f g ≫ coproductMap f' g' := by
  apply coproduct_hom_ext <;> simp

/-- The literal disjoint union is a categorical binary coproduct in the smooth site. -/
def coproductIsColimit (X Y : SmoothSite S) :
    IsColimit (BinaryCofan.mk (coproductInl X Y) (coproductInr X Y)) :=
  BinaryCofan.isColimitMk (fun s => coproductDesc s.inl s.inr)
    (fun s => coproductInl_desc s.inl s.inr)
    (fun s => coproductInr_desc s.inl s.inr)
    (fun _ _ h₁ h₂ => coproduct_hom_ext (h₁.trans (coproductInl_desc _ _).symm)
      (h₂.trans (coproductInr_desc _ _).symm))

instance (X Y : SmoothSite S) : HasBinaryCoproduct X Y :=
  ⟨⟨_, coproductIsColimit X Y⟩⟩

instance : HasBinaryCoproducts (SmoothSite S) :=
  hasBinaryCoproducts_of_hasColimit_pair _

/-- The chosen categorical coproduct is canonically the literal scheme disjoint union. -/
def categoricalCoproductIso (X Y : SmoothSite S) : X ⨿ Y ≅ coproduct X Y :=
  colimit.isoColimitCocone ⟨_, coproductIsColimit X Y⟩

@[reassoc (attr := simp)]
theorem categoricalCoproductIso_inl_hom (X Y : SmoothSite S) :
    coprod.inl ≫ (categoricalCoproductIso X Y).hom = coproductInl X Y :=
  colimit.isoColimitCocone_ι_hom ⟨_, coproductIsColimit X Y⟩ ⟨WalkingPair.left⟩

@[reassoc (attr := simp)]
theorem categoricalCoproductIso_inr_hom (X Y : SmoothSite S) :
    coprod.inr ≫ (categoricalCoproductIso X Y).hom = coproductInr X Y :=
  colimit.isoColimitCocone_ι_hom ⟨_, coproductIsColimit X Y⟩ ⟨WalkingPair.right⟩

@[reassoc (attr := simp)]
theorem categoricalCoproductIso_inl_inv (X Y : SmoothSite S) :
    coproductInl X Y ≫ (categoricalCoproductIso X Y).inv = coprod.inl :=
  colimit.isoColimitCocone_ι_inv ⟨_, coproductIsColimit X Y⟩ ⟨WalkingPair.left⟩

@[reassoc (attr := simp)]
theorem categoricalCoproductIso_inr_inv (X Y : SmoothSite S) :
    coproductInr X Y ≫ (categoricalCoproductIso X Y).inv = coprod.inr :=
  colimit.isoColimitCocone_ι_inv ⟨_, coproductIsColimit X Y⟩ ⟨WalkingPair.right⟩

/-- Ordinary categorical coproduct maps agree with the displayed disjoint-union maps. -/
@[reassoc]
theorem categoricalCoproductIso_naturality {X X' Y Y' : SmoothSite S}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    coprod.map f g ≫ (categoricalCoproductIso X' Y').hom =
      (categoricalCoproductIso X Y).hom ≫ coproductMap f g := by
  apply coprod.hom_ext <;> simp

end AlgebraicGeometry.Scheme.SmoothSite
