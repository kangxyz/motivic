/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.OriginalPairNormSectionData
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.OriginalCorrectionInfinityUnits
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.OriginalCorrectionActionGeometry
/-! # Infinity units of the same original source section datum

The large retained curve uses infinity only. The smaller marked boundary carries
units of a and b, never a purported unit of the graph-twisted pole at incidence.

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.OriginalPairNormBoundaryUnits`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Pencils.NativeOriginalPairTransferAction`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

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
  (c : BoundarySectionData q π j p hq a z s hs H e ha d hd)

/-- The actual numerator remains a unit on the original infinity summand. -/
theorem BoundarySectionData.originalNumerator_infinity_isIso :
    IsIso (pullbackSectionMap (Hom.infinityProductMap π j d) c.aS) := by
  let : IsIso (pullbackSectionMap
      (coprod.desc (Hom.infinityProductMap π j d) (Hom.graphBoundaryRestriction π j s)) c.aS) :=
    c.a_unit
  exact pullbackSectionMap_coprod_left_isIso
    (Hom.infinityProductMap π j d) (Hom.graphBoundaryRestriction π j s) _

/-- The actual pole remains a unit on the original infinity summand. -/
theorem BoundarySectionData.originalPole_infinity_isIso :
    IsIso (pullbackSectionMap (Hom.infinityProductMap π j d) c.bS) := by
  let : IsIso (pullbackSectionMap
      (coprod.desc (Hom.infinityProductMap π j d) (Hom.graphBoundaryRestriction π j s)) c.bS) :=
    c.b_unit
  exact pullbackSectionMap_coprod_left_isIso
    (Hom.infinityProductMap π j d) (Hom.graphBoundaryRestriction π j s) _

/-- The same graph-twisted pole is a unit at infinity by the original frame equation. -/
theorem BoundarySectionData.originalTwistedPole_infinity_isIso :
    IsIso (pullbackSectionMap (Hom.infinityProductMap π j d)
      (twistedIdealSection _ (Hom.relativeCompactificationGraphLine π j) c.T
        (Hom.idealInclusion (Hom.compactificationGraph π j)) c.bS)) := by
  let : IsIso (pullbackSectionMap (Hom.fullBoundaryProductMap π j d s) c.aS) := c.a_unit
  exact graphTwistedSection_infinity_isIso q π j p hq z s hs H e d hd c.T c.aS c.bS c.hA

end AlgebraicGeometry.Scheme.RelativeCurvePencil


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

variable {DA : Scheme.{u}} (dA : DA ⟶ P)
  [IsIso (pullbackSectionMap (Hom.infinityProductMap π jA dA) aA)]
  [IsIso (pullbackSectionMap (Hom.infinityProductMap π jA dA) bA)]

/-- The actual two original numerators are units on their infinity boundaries. -/
theorem BoundarySectionData.originalNormPairNumerator_infinity_isIso (i : Fin 2) :
    IsIso (pullbackSectionMap (Hom.originalNormPairInfinityInclusion π f jB jA d dA i)
      (c.originalNormPairNumerator q π f jB jA p hq a z s hs H e ha d hd LA aA i)) := by
  fin_cases i
  · change IsIso (pullbackSectionMap (Hom.infinityProductMap (f ≫ π) jB d) c.aS)
    exact c.originalNumerator_infinity_isIso q (f ≫ π) jB p hq a z s hs H e ha d hd
  · change IsIso (pullbackSectionMap (Hom.infinityProductMap π jA dA) aA)
    infer_instance

omit [IsSeparated π] [IsOpenImmersion jA] [SmoothOfRelativeDimension 1 (jA ≫ π)] in
/-- The actual two original poles are units on their infinity boundaries. -/
theorem BoundarySectionData.originalNormPairPole_infinity_isIso (i : Fin 2) :
    IsIso (pullbackSectionMap (Hom.originalNormPairInfinityInclusion π f jB jA d dA i)
      (c.originalNormPairPole q π f jB jA p hq a z s hs H e ha d hd LA bA i)) := by
  fin_cases i
  · change IsIso (pullbackSectionMap (Hom.infinityProductMap (f ≫ π) jB d) c.bS)
    exact c.originalPole_infinity_isIso q (f ≫ π) jB p hq a z s hs H e ha d hd
  · change IsIso (pullbackSectionMap (Hom.infinityProductMap π jA dA) bA)
    infer_instance

end AlgebraicGeometry.Scheme.RelativeCurvePencil

namespace AlgebraicGeometry.Scheme.Hom

/-- The actual first-parameter square transports each original infinity section
unit to the functional unit required on the finite norm source. -/
theorem originalNormPairInfinity_functional_isIso
    {S C P X Y K DB DA : Scheme.{u}} (π : P ⟶ S) (f : C ⟶ P)
    (jB : Y ⟶ C) (α : K ⟶ Y) (jA : X ⟶ P) (p : Y ⟶ X)
    (hret : jB ≫ f = p ≫ jA) (dB : DB ⟶ C) (dA : DA ⟶ P)
    (M : ∀ i, LineBundle (originalNormPairCompact π f jB jA i))
    (s : ∀ i, SheafOfModules.unit (originalNormPairCompact π f jB jA i).ringCatSheaf ⟶
      (M i).val)
    [∀ i, IsIso (pullbackSectionMap (originalNormPairInfinityInclusion π f jB jA dB dA i)
      (s i))] (i : Fin 2) :
    IsIso ((Modules.pullback (originalNormPairChangedInfinityInclusion π f jB α dB dA i)).map
      (pullbackUnitMap (originalNormPairCompactMap π f jB α jA p hret i)
        (sectionDualFunctional _ (M i) (s i)))) := by
  let : IsIso (Hom.pullbackToUnit (sectionDualFunctional _ (M i) (s i))
      (originalNormPairInfinityInclusion π f jB jA dB dA i)) :=
    sectionDualFunctional_pullback_isIso _ _ _
  let : IsIso (pullbackUnitMap (originalNormPairInfinityInclusion π f jB jA dB dA i)
      (sectionDualFunctional _ (M i) (s i))) :=
    inferInstanceAs (IsIso (Hom.pullbackToUnit (sectionDualFunctional _ (M i) (s i))
      (originalNormPairInfinityInclusion π f jB jA dB dA i)))
  let : IsIso ((Modules.pullback (originalNormPairInfinityInclusion π f jB jA dB dA i)).map
      (sectionDualFunctional _ (M i) (s i))) :=
    pullback_map_isIso_of_pullbackUnitMap _ _
  exact pullback_map_unit_isIso_of_comm
    (originalNormPairCompactMap π f jB α jA p hret i)
    (originalNormPairInfinityInclusion π f jB jA dB dA i)
    (originalNormPairChangedInfinityInclusion π f jB α dB dA i)
    (originalNormPairInfinityMap π f jB α jA p hret dB dA i)
    (originalNormPairInfinityMap_inclusion π f jB α jA p hret dB dA i).symm _

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Hom

/-- The actual original compact curves are covered by their retained open and infinity. -/
theorem originalNormPairInfinity_cover
    {S C P X Y DB DA : Scheme.{u}} (π : P ⟶ S) (f : C ⟶ P)
    (jB : Y ⟶ C) (jA : X ⟶ P) (dB : DB ⟶ C) (dA : DA ⟶ P)
    (hcB : (Set.range jB)ᶜ ⊆ Set.range dB) (hcA : (Set.range jA)ᶜ ⊆ Set.range dA)
    (i : Fin 2) (x : originalNormPairCompact π f jB jA i) :
    x ∈ Set.range (originalNormPairRetainedInclusion π f jB jA i) ∨
      x ∈ Set.range (originalNormPairInfinityInclusion π f jB jA dB dA i) := by
  fin_cases i
  · exact RelativeCurvePencil.retainedProduct_infinity_cover
      (originalNormPairBase π f jB) (f ≫ π) jB dB hcB x
  · exact RelativeCurvePencil.retainedProduct_infinity_cover (jA ≫ π) π jA dA hcA x

/-- The same original complement covers survive the actual component parameter change. -/
theorem originalNormPairChangedInfinity_cover
    {S C P X Y K DB DA : Scheme.{u}} (π : P ⟶ S) (f : C ⟶ P)
    (jB : Y ⟶ C) (α : K ⟶ Y) (jA : X ⟶ P) (dB : DB ⟶ C) (dA : DA ⟶ P)
    (hcB : (Set.range jB)ᶜ ⊆ Set.range dB) (hcA : (Set.range jA)ᶜ ⊆ Set.range dA)
    (i : Fin 2) (x : originalNormPairChangedCompact π f jB α i) :
    x ∈ Set.range (originalNormPairChangedInclusion π f jB α jA i) ∨
      x ∈ Set.range (originalNormPairChangedInfinityInclusion π f jB α dB dA i) := by
  fin_cases i
  · exact RelativeCurvePencil.retainedProduct_infinity_cover
      (originalNormPairComponentBase π f jB α) (f ≫ π) jB dB hcB x
  · exact RelativeCurvePencil.retainedProduct_infinity_cover
      (originalNormPairComponentBase π f jB α) π jA dA hcA x

end AlgebraicGeometry.Scheme.Hom
