/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.GraphBoundaryRestriction
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# The original source and target graph triangle under a finite map

The parameter is the same scheme on both sides. The target graph is the literal
map with coordinates identity and j followed by f. Its restriction to a target
chart and the source graph restriction have canonically the same domain.


Intended upstream module: `Aglib.AlgebraicGeometry.Graph.Frames.OriginalTriangle`.
Incoming project consumers: `Motivic.Aglib.AlgebraicGeometry.Graph.Frames.FreeProductCharts`,
`Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.OpenGraphTriangle`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u
namespace AlgebraicGeometry.Scheme.Hom
variable {S C X T : Scheme.{u}} (q : X ⟶ S) (f : C ⟶ X) (j : T ⟶ C)

/-- The original finite map on the second factor, with the parameter unchanged. -/
def graphProductMap : pullback (j ≫ f ≫ q) (f ≫ q) ⟶ pullback (j ≫ f ≫ q) q :=
  (pullbackLeftPullbackSndIso (j ≫ f ≫ q) q f).inv ≫
    pullback.fst (pullback.snd (j ≫ f ≫ q) q) f

instance [IsFinite f] : IsFinite (graphProductMap q f j) := by
  unfold graphProductMap
  infer_instance

@[reassoc (attr := simp)]
theorem graphProductMap_fst : graphProductMap q f j ≫ pullback.fst _ _ = pullback.fst _ _ := by
  simp [graphProductMap]

@[reassoc (attr := simp)]
theorem graphProductMap_snd : graphProductMap q f j ≫ pullback.snd _ _ =
    pullback.snd _ _ ≫ f := by
  simp [graphProductMap]

/-- The actual target graph, not a separately chosen closed subscheme. -/
def targetCompactificationGraph : T ⟶ pullback (j ≫ f ≫ q) q :=
  pullback.lift (𝟙 T) (j ≫ f) (by simp [Category.assoc])

@[reassoc (attr := simp)]
theorem compactificationGraph_comp_graphProductMap :
    compactificationGraph (f ≫ q) j ≫ graphProductMap q f j =
      targetCompactificationGraph q f j := by
  apply pullback.hom_ext <;> simp [compactificationGraph, targetCompactificationGraph]

instance targetCompactificationGraph_closed [IsSeparated q] :
    IsClosedImmersion (targetCompactificationGraph q f j) := by
  have : IsClosedImmersion (targetCompactificationGraph q f j ≫ pullback.fst _ _) := by
    simp only [targetCompactificationGraph, pullback.lift_fst]
    infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.fst _ _)

/-- The source graph restricted to the full finite inverse chart has the very
same scheme as the target graph restricted to that chart, via native pullbacks. -/
def graphChartDomainIso {W : Scheme.{u}} (w : W ⟶ pullback (j ≫ f ≫ q) q) :
    pullback (compactificationGraph (f ≫ q) j) (pullback.fst (graphProductMap q f j) w) ≅
      pullback (targetCompactificationGraph q f j) w :=
  pullbackRightPullbackFstIso (graphProductMap q f j) w (compactificationGraph (f ≫ q) j) ≪≫
    pullback.congrHom (compactificationGraph_comp_graphProductMap q f j) rfl

/-- Both actual graph restrictions form a closed triangle over the original
finite chart map; the domain comparison is constructed, not assumed. -/
theorem graphChart_triangle {W : Scheme.{u}} (w : W ⟶ pullback (j ≫ f ≫ q) q) :
    pullback.snd (compactificationGraph (f ≫ q) j)
        (pullback.fst (graphProductMap q f j) w) ≫ pullback.snd (graphProductMap q f j) w =
      (graphChartDomainIso q f j w).hom ≫ pullback.snd (targetCompactificationGraph q f j) w := by
  simp [graphChartDomainIso]

end AlgebraicGeometry.Scheme.Hom
