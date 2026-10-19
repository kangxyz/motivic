/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.BoundarySections

/-! # One retained choice of the original whole-boundary sections

Intended upstream module: `Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.BoundarySectionData`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.BoundarySectionRegularity`,
`Motivic.Transfers.Presheaf.Actions.Pencils.Restriction`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

section Sections
variable {S X Y A Z C D : Scheme.{u}}
  (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (π : C ⟶ S) [IsSeparated π]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  (p : Y ⟶ X) [Flat p] (hq : j ≫ π = p ≫ q)
  (a : A ⟶ X) [IsOpenImmersion a]
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 _) p z)
  (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    Hom.idealModule (Hom.boundaryGraphTarget q z))
  (ha : Disjoint (Set.range a) (Set.range z)) (d : D ⟶ C)
  (hd : Disjoint (Set.range j) (Set.range d))

/-- The original global sections and their full scheme-theoretic boundary witnesses.
No correspondence action or homotopy relation is part of this data. -/
structure BoundarySectionData where
  /-- The retained line bundle on `pullback (j ≫ π) π` for the original section pair. -/
  T : LineBundle (pullback (j ≫ π) π)
  /-- The retained line bundle on `pullback (a ≫ q) π` for the correction sections. -/
  N : LineBundle (pullback (a ≫ q) π)
  /-- The chosen section of `T` tensored with the dual relative compactification graph line. -/
  aS : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶
    (tensorLineBundle _ T (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))).val
  /-- The chosen section of the original line bundle `T`. -/
  bS : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶ T.val
  /-- The chosen numerator section of `N` on the correction product. -/
  nS : SheafOfModules.unit (pullback (a ≫ q) π).ringCatSheaf ⟶ N.val
  /-- The chosen denominator section of `N` on the correction product. -/
  dS : SheafOfModules.unit (pullback (a ≫ q) π).ringCatSheaf ⟶ N.val
  hA :
    let zA := coprod.desc (Hom.infinityProductMap π j d) (Hom.graphBoundaryRestriction π j s)
    pullbackSectionMap zA aS ≫ pullbackTensorMap zA T.val
      (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j)).val =
    tensorUnitSection (pullbackSectionMap zA bS)
      (Hom.relativeFullBoundaryFrame q π j p hq z s hs H e d hd).inv
  hN : pullbackSectionMap (psiBoundaryInclusion q π j p hq a z s hs d) nS =
    (fixedProductBoundaryFrame q π a z e ha d).hom ≫
      pullbackSectionMap (psiBoundaryInclusion q π j p hq a z s hs d) dS
  a_unit : IsIso (pullbackSectionMap
    (coprod.desc (Hom.infinityProductMap π j d) (Hom.graphBoundaryRestriction π j s)) aS)
  b_unit : IsIso (pullbackSectionMap
    (coprod.desc (Hom.infinityProductMap π j d) (Hom.graphBoundaryRestriction π j s)) bS)
  n_unit : IsIso (pullbackSectionMap (psiBoundaryInclusion q π j p hq a z s hs d) nS)
  d_unit : IsIso (pullbackSectionMap (psiBoundaryInclusion q π j p hq a z s hs d) dS)
end Sections

local instance {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
    Smooth f := SmoothOfRelativeDimension.smooth 1 f
variable (k : Type u) [Field k] {S X Y A B Z C D V : Scheme.{u}}
  [IsAffine S] [IsAffine Y] [IsAffine A] [IsAffine B] [IsAffine V]
  (t : S ⟶ Spec (.of k)) [Smooth t]
  (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (π : C ⟶ S) [IsProper π]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  (p : Y ⟶ X) [Flat p] (hq : j ≫ π = p ≫ q)
  (a : A ⟶ X) [IsOpenImmersion a]
  (α : B ⟶ Y) [Smooth α] (β : B ⟶ A) [Flat β] (h : α ≫ p = β ≫ a)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 _) p z)
  (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    Hom.idealModule (Hom.boundaryGraphTarget q z))
  (ha : Disjoint (Set.range a) (Set.range z)) (d : D ⟶ C)
  (hd : Disjoint (Set.range j) (Set.range d))

/-- Construct all finite-flat pencil data from this same retained global choice. -/
def BoundarySectionData.toData
    (c : BoundarySectionData q π j p hq a z s hs H e ha d hd)
    (v : V ⟶ C) [IsOpenImmersion v] [SmoothOfRelativeDimension 1 (v ≫ π)]
    (hc : ∀ x : C, x ∈ Set.range v ∨ x ∈ Set.range d ∨ x ∈ Set.range (s ≫ j))
    (φ : B ⟶ V) (hφ : φ ≫ v = α ≫ j) :
    _root_.AlgebraicGeometry.Scheme.SmoothSite.GraphDivisorPencil.Data
      (relativeAlpha k t π j α) (relativeBeta k t q π j a α p hq β h)
      (relativeGraphMap k t π j α v φ hφ) := by
  letI := c.a_unit
  letI := c.b_unit
  letI := c.n_unit
  letI := c.d_unit
  exact dataOfBoundarySections k t q π j p hq a α β h z s hs H e ha d hd v hc
    c.T c.N c.aS c.bS c.nS c.dS c.hA c.hN φ hφ

end AlgebraicGeometry.Scheme.RelativeCurvePencil
