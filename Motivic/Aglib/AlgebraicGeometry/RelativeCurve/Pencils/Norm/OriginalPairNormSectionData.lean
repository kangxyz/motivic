/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.OriginalPairNormDiagram
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.BoundarySectionData
/-! # The same original source and target sections in the norm action family

The source entry is a projection of the retained BoundarySectionData. The target
entry is the original target pair, not a second source datum. Both graph ideal
lines are the literal ideals of the unchanged original compactification graphs.

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.OriginalPairNormSectionData`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Norm.OriginalPairNormBoundaryUnits`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Hom

variable {S C P X Y : Scheme.{u}} (π : P ⟶ S) (f : C ⟶ P)
  [IsSeparated π] [IsSeparated (f ≫ π)]
  (jB : Y ⟶ C) [IsOpenImmersion jB] [SmoothOfRelativeDimension 1 (jB ≫ (f ≫ π))]
  (jA : X ⟶ P) [IsOpenImmersion jA] [SmoothOfRelativeDimension 1 (jA ≫ π)]

/-- Each original graph remains a closed immersion before component restriction. -/
instance (i : Fin 2) : IsClosedImmersion (originalNormPairGraph π f jB jA i) := by
  fin_cases i
  · change IsClosedImmersion (compactificationGraph (f ≫ π) jB)
    dsimp [compactificationGraph]
    infer_instance
  · change IsClosedImmersion (compactificationGraph π jA)
    dsimp [compactificationGraph]
    infer_instance

/-- Rank one for each literal original graph ideal. -/
theorem originalNormPairGraph_rankOne (i : Fin 2) :
    IsLocallyRankOne (originalNormPairCompact π f jB jA i)
      (idealModule (originalNormPairGraph π f jB jA i)) := by
  fin_cases i
  · exact (relativeCompactificationGraphLine (f ≫ π) jB).property
  · exact (relativeCompactificationGraphLine π jA).property

/-- The graph line used by the original norm consumer has the unchanged ideal module. -/
def originalNormPairGraphLine (i : Fin 2) :
    LineBundle (originalNormPairCompact π f jB jA i) :=
  ⟨idealModule (originalNormPairGraph π f jB jA i),
    originalNormPairGraph_rankOne π f jB jA i⟩

@[simp] theorem originalNormPairGraphLine_zero :
    originalNormPairGraphLine π f jB jA 0 = relativeCompactificationGraphLine (f ≫ π) jB := rfl

@[simp] theorem originalNormPairGraphLine_one :
    originalNormPairGraphLine π f jB jA 1 = relativeCompactificationGraphLine π jA := rfl

end AlgebraicGeometry.Scheme.Hom
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {S C P X Y A Z D : Scheme.{u}}
  (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (π : P ⟶ S) (f : C ⟶ P)
  [IsSeparated π] [IsSeparated (f ≫ π)]
  (jB : Y ⟶ C) [IsOpenImmersion jB] [SmoothOfRelativeDimension 1 (jB ≫ (f ≫ π))]
  (jA : X ⟶ P) [IsOpenImmersion jA] [SmoothOfRelativeDimension 1 (jA ≫ π)]
  (p : Y ⟶ X) [Flat p]
  (hq : jB ≫ (f ≫ π) = p ≫ q)
  (a : A ⟶ X) [IsOpenImmersion a]
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 _) p z)
  (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    Hom.idealModule (Hom.boundaryGraphTarget q z))
  (ha : Disjoint (Set.range a) (Set.range z)) (d : D ⟶ C)
  (hd : Disjoint (Set.range jB) (Set.range d))
  (c : BoundarySectionData q (f ≫ π) jB p hq a z s hs H e ha d hd)
  (LA : LineBundle (pullback (jA ≫ π) π))
  (aA : SheafOfModules.unit (pullback (jA ≫ π) π).ringCatSheaf ⟶
    (tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA))).val)
  (bA : SheafOfModules.unit (pullback (jA ≫ π) π).ringCatSheaf ⟶ LA.val)

/-- The actual source line is c.T, and the actual target line is LA. -/
def BoundarySectionData.originalNormPairLine :
    ∀ i, LineBundle (Hom.originalNormPairCompact π f jB jA i) :=
  Fin.twoCases c.T LA

/-- The numerator family contains the SAME source section c.aS. -/
def BoundarySectionData.originalNormPairNumerator : ∀ i,
    SheafOfModules.unit (Hom.originalNormPairCompact π f jB jA i).ringCatSheaf ⟶
      (tensorLineBundle _ (c.originalNormPairLine q π f jB jA p hq a z s hs H e ha d hd LA i)
        (dualLineBundle _ (Hom.originalNormPairGraphLine π f jB jA i))).val :=
  Fin.twoCases c.aS aA

/-- The pole family contains the SAME source section c.bS. -/
def BoundarySectionData.originalNormPairPole : ∀ i,
    SheafOfModules.unit (Hom.originalNormPairCompact π f jB jA i).ringCatSheaf ⟶
      (c.originalNormPairLine q π f jB jA p hq a z s hs H e ha d hd LA i).val :=
  Fin.twoCases c.bS bA

omit [IsSeparated π] [IsOpenImmersion jA] [SmoothOfRelativeDimension 1 (jA ≫ π)] in
@[simp] theorem BoundarySectionData.originalNormPairLine_zero :
    c.originalNormPairLine q π f jB jA p hq a z s hs H e ha d hd LA 0 = c.T := rfl

omit [IsSeparated π] [IsOpenImmersion jA] [SmoothOfRelativeDimension 1 (jA ≫ π)] in
@[simp] theorem BoundarySectionData.originalNormPairLine_one :
    c.originalNormPairLine q π f jB jA p hq a z s hs H e ha d hd LA 1 = LA := rfl

@[simp] theorem BoundarySectionData.originalNormPairNumerator_zero :
    c.originalNormPairNumerator q π f jB jA p hq a z s hs H e ha d hd LA aA 0 = c.aS := rfl

@[simp] theorem BoundarySectionData.originalNormPairNumerator_one :
    c.originalNormPairNumerator q π f jB jA p hq a z s hs H e ha d hd LA aA 1 = aA := rfl

omit [IsSeparated π] [IsOpenImmersion jA] [SmoothOfRelativeDimension 1 (jA ≫ π)] in
@[simp] theorem BoundarySectionData.originalNormPairPole_zero :
    c.originalNormPairPole q π f jB jA p hq a z s hs H e ha d hd LA bA 0 = c.bS := rfl

omit [IsSeparated π] [IsOpenImmersion jA] [SmoothOfRelativeDimension 1 (jA ≫ π)] in
@[simp] theorem BoundarySectionData.originalNormPairPole_one :
    c.originalNormPairPole q π f jB jA p hq a z s hs H e ha d hd LA bA 1 = bA := rfl

/-- Original numerator regularity is used separately on each unchanged curve. -/
theorem BoundarySectionData.originalNormPairNumerator_mono
    [Mono (sectionDualFunctional _
      (tensorLineBundle _ c.T
        (dualLineBundle _ (Hom.relativeCompactificationGraphLine (f ≫ π) jB))) c.aS)]
    [Mono (sectionDualFunctional _
      (tensorLineBundle _ LA
        (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA))) aA)]
    (i : Fin 2) :
    Mono (sectionDualFunctional _
      (tensorLineBundle _ (c.originalNormPairLine q π f jB jA p hq a z s hs H e ha d hd LA i)
        (dualLineBundle _ (Hom.originalNormPairGraphLine π f jB jA i)))
      (c.originalNormPairNumerator q π f jB jA p hq a z s hs H e ha d hd LA aA i)) := by
  fin_cases i
  · change Mono (sectionDualFunctional _
      (tensorLineBundle _ c.T
        (dualLineBundle _ (Hom.relativeCompactificationGraphLine (f ≫ π) jB))) c.aS)
    infer_instance
  · change Mono (sectionDualFunctional _
      (tensorLineBundle _ LA
        (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA))) aA)
    infer_instance

omit [IsSeparated π] [IsOpenImmersion jA] [SmoothOfRelativeDimension 1 (jA ≫ π)] in
/-- Original pole regularity comes from the same c.bS and target bA. -/
theorem BoundarySectionData.originalNormPairPole_mono
    [Mono (sectionDualFunctional _ c.T c.bS)] [Mono (sectionDualFunctional _ LA bA)]
    (i : Fin 2) :
    Mono (sectionDualFunctional _
      (c.originalNormPairLine q π f jB jA p hq a z s hs H e ha d hd LA i)
      (c.originalNormPairPole q π f jB jA p hq a z s hs H e ha d hd LA bA i)) := by
  fin_cases i
  · change Mono (sectionDualFunctional _ c.T c.bS)
    infer_instance
  · change Mono (sectionDualFunctional _ LA bA)
    infer_instance

end AlgebraicGeometry.Scheme.RelativeCurvePencil
