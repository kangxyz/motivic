/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Point.Normalization
public import Motivic.Aglib.AlgebraicGeometry.ResidueField.ResidueFieldLiftIsomorphism
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered

/-!
# Sections in the actual smooth Nisnevich point fiber

The germ of a section uses the identity pointed neighborhood and the already
constructed fiber colimit. It vanishes exactly when its restriction vanishes
on an actual pointed neighborhood. Such a zero representative can be normalized
over any selected finite set of closed centers without changing its germ.

The coefficient universe can be any universe at least that of the neighborhood
index. This smooth-site consumer is not a standalone upstream extraction.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} {X : SmoothSite S} {x : X.left}

namespace NisnevichNeighborhood

instance isIso_residueFieldMap_center (N : NisnevichNeighborhood X x) :
    IsIso (N.toBase.left.residueFieldMap N.center) :=
  N.toBase.left.isIso_residueFieldMap_of_canonicalPoint_lift x
    N.obj.val.left (Over.w N.obj.val)

set_option backward.isDefEq.respectTransparency false in
/-- The identity neighborhood with the original canonical residue-field point. -/
def identity (X : SmoothSite S) (x : X.left) : NisnevichNeighborhood X x :=
  ⟨Functor.elementsMk _ (Scheme.Etale.mk (𝟙 X.left))
    (Over.homMk (X.left.fromSpecResidueField x) (Category.comp_id _)),
    by
      change smoothSeparatedFiniteType ((𝟙 X.left) ≫ X.hom)
      rw [Category.id_comp]
      exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- The actual structural map to the identity pointed neighborhood. -/
def toIdentity (N : NisnevichNeighborhood X x) : N ⟶ identity X x :=
  ObjectProperty.homMk (Functor.Elements.homMk
    (MorphismProperty.Over.homMk N.obj.obj.hom (Category.comp_id _)) (by
      apply Over.OverMorphism.ext
      exact Over.w N.obj.val))

@[reassoc (attr := simp)]
theorem map_toBase {M N : NisnevichNeighborhood X x} (q : M ⟶ N) :
    (nisnevichNeighborhoodFunctor X x).map q ≫ N.toBase = M.toBase := by
  apply MorphismProperty.Over.Hom.ext
  exact MorphismProperty.Over.w q.hom.hom

end NisnevichNeighborhood

variable [IsAffine S] (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v})

/-- The original section-to-fiber map, computed at the identity neighborhood. -/
def sectionToNisnevichPoint (X : SmoothSite S) (x : X.left) :
    F.obj (op X) ⟶ (nisnevichPoint X x).presheafFiber.obj F :=
  F.map (NisnevichNeighborhood.identity X x).toBase.op ≫
    (nisnevichPointFiberCocone X x F).ι.app (op (NisnevichNeighborhood.identity X x))

/-- Any actual neighborhood computes the same germ map using its restriction. -/
@[reassoc]
theorem restriction_sectionToNisnevichPoint (N : NisnevichNeighborhood X x) :
    F.map N.toBase.op ≫ (nisnevichPointFiberCocone X x F).ι.app (op N) =
      sectionToNisnevichPoint F X x := by
  have h := (nisnevichPointFiberCocone X x F).w N.toIdentity.op
  dsimp only [Functor.comp_map, Functor.op_map] at h
  rw [sectionToNisnevichPoint, ← h, ← Category.assoc, ← F.map_comp,
    ← op_comp, NisnevichNeighborhood.map_toBase]

/-- A germ vanishes precisely when the section vanishes on a genuine pointed neighborhood. -/
theorem sectionToNisnevichPoint_eq_zero_iff (s : F.obj (op X)) :
    sectionToNisnevichPoint F X x s = 0 ↔
      ∃ N : NisnevichNeighborhood X x, F.map N.toBase.op s = 0 := by
  constructor
  · intro hs
    have : PreservesFilteredColimitsOfSize.{u, u + 1}
        (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v}) :=
      preservesFilteredColimitsOfSize_shrink.{u + 1, max (u + 1) v, u, max (u + 1) v} _
    let I := NisnevichNeighborhood.identity X x
    change (nisnevichPointFiberCocone X x F).ι.app (op I) (F.map I.toBase.op s) = 0 at hs
    have h : (nisnevichPointFiberCocone X x F).ι.app (op I) (F.map I.toBase.op s) =
        (nisnevichPointFiberCocone X x F).ι.app (op I) 0 := by
      simpa only [map_zero] using hs
    obtain ⟨M, q, hq⟩ := (isColimitNisnevichPointFiberCocone X x F).eq_iff' _ _ |>.mp h
    refine ⟨M.unop, ?_⟩
    have hm := NisnevichNeighborhood.map_toBase q.unop
    change F.map ((nisnevichNeighborhoodFunctor X x).map q.unop).op
      (F.map I.toBase.op s) = _ at hq
    rw [← ConcreteCategory.comp_apply, ← F.map_comp] at hq
    simpa only [← op_comp, hm, map_zero] using hq
  · rintro ⟨N, hN⟩
    rw [← restriction_sectionToNisnevichPoint F N, ConcreteCategory.comp_apply, hN, map_zero]

/-- A zero germ has a zero representative with precisely its chosen branch
above any selected finite set of closed centers containing the base point. -/
theorem exists_normalized_zero_representative (s : F.obj (op X))
    (hs : sectionToNisnevichPoint F X x s = 0)
    (T : Set X.left) (hT : T.Finite) (hclosed : ∀ y ∈ T, IsClosed ({y} : Set X.left))
    (hx : x ∈ T) :
    ∃ N : NisnevichNeighborhood X x, IsAffine N.obj.obj.left ∧
      N.toBase.left ⁻¹' T = {N.center} ∧ F.map N.toBase.op s = 0 := by
  obtain ⟨N, hN⟩ := (sectionToNisnevichPoint_eq_zero_iff F s).mp hs
  obtain ⟨M, q, hM, _, _, hfiber⟩ := N.exists_normalized_refinement T hT hclosed hx
  refine ⟨M, hM, hfiber, ?_⟩
  rw [← NisnevichNeighborhood.map_toBase q, op_comp, F.map_comp,
    ConcreteCategory.comp_apply, hN, map_zero]

end AlgebraicGeometry.Scheme.SmoothSite
