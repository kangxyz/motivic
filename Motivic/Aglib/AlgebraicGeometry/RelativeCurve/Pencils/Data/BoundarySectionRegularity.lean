/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.BoundarySectionData
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Sections.SerreDivisorRegularity

/-! # Global regularity of the same boundary-prescribed source sections

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.BoundarySectionRegularity`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {S X Y A Z C D V : Scheme.{u}}
  [IsAffine S] [IsAffine Y] [IsAffine A] [IsAffine V]
  (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (π : C ⟶ S) [IsProper π]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  (p : Y ⟶ X) [Flat p] (hq : j ≫ π = p ≫ q)
  (a : A ⟶ X) [IsOpenImmersion a]
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 _) p z)
  (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    Hom.idealModule (Hom.boundaryGraphTarget q z))
  (ha : Disjoint (Set.range a) (Set.range z)) (d : D ⟶ C)
  (hd : Disjoint (Set.range j) (Set.range d))
  (c : BoundarySectionData q π j p hq a z s hs H e ha d hd)

/-- The original boundary units and actual retained cover give global monicity of all
four original section functionals. No stored Serre zero witnesses or new choices are used. -/
theorem BoundarySectionData.global_mono
    (v : V ⟶ C) [IsOpenImmersion v] [SmoothOfRelativeDimension 1 (v ≫ π)]
    (hc : ∀ x : C, x ∈ Set.range v ∨ x ∈ Set.range d ∨ x ∈ Set.range (s ≫ j)) :
    Mono (sectionDualFunctional _
      (tensorLineBundle _ c.T (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j)))
      c.aS) ∧ Mono (sectionDualFunctional _ c.T c.bS) ∧
      Mono (sectionDualFunctional _ c.N c.nS) ∧ Mono (sectionDualFunctional _ c.N c.dS) := by
  let iA := retainedProductInclusion (j ≫ π) π v
  let iN := retainedProductInclusion (a ≫ q) π v
  let zA := coprod.desc (Hom.infinityProductMap π j d) (Hom.graphBoundaryRestriction π j s)
  let zN := psiBoundaryInclusion q π j p hq a z s hs d
  have : IsAffine (retainedProduct (j ≫ π) π v) := retainedProduct_affine (j ≫ π) π v
  have : IsAffine (retainedProduct (a ≫ q) π v) := retainedProduct_affine (a ≫ q) π v
  have : SmoothOfRelativeDimension 1 (iA ≫ pullback.fst (j ≫ π) π) :=
    retainedProduct_smooth (j ≫ π) π v
  have : SmoothOfRelativeDimension 1 (iN ≫ pullback.fst (a ≫ q) π) :=
    retainedProduct_smooth (a ≫ q) π v
  have : IsIso (pullbackSectionMap zA c.aS) := c.a_unit
  have : IsIso (pullbackSectionMap zA c.bS) := c.b_unit
  have : IsIso (pullbackSectionMap zN c.nS) := c.n_unit
  have : IsIso (pullbackSectionMap zN c.dS) := c.d_unit
  have hcA := lambdaBoundary_retained_cover π j s d v hc
  have hcN := psiBoundary_retained_cover q π j p hq a z s hs d v hc
  have hFa := CoherentGraph.sectionDivisorFiniteFlat_of_boundary_unit zA
    (pullback.fst (j ≫ π) π) iA hcA
    (tensorLineBundle _ c.T (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))) c.aS
  have hFb := CoherentGraph.sectionDivisorFiniteFlat_of_boundary_unit zA
    (pullback.fst (j ≫ π) π) iA hcA c.T c.bS
  have hFn := CoherentGraph.sectionDivisorFiniteFlat_of_boundary_unit zN
    (pullback.fst (a ≫ q) π) iN hcN c.N c.nS
  have hFd := CoherentGraph.sectionDivisorFiniteFlat_of_boundary_unit zN
    (pullback.fst (a ≫ q) π) iN hcN c.N c.dS
  exact ⟨hFa.mono, hFb.mono, hFn.mono, hFd.mono⟩

end AlgebraicGeometry.Scheme.RelativeCurvePencil
