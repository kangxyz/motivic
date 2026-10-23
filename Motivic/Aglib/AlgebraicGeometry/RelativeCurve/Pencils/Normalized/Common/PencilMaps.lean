/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Normalized.Common.SectionProducer
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Boundary.MixedProductBoundaryPullback
/-! # The genuine two maps of the compact correcting pencil -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
variable (k : Type u) [Field k] {Y S A X : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
  (r : S ⟶ Y) [IsOpenImmersion r] (v : A ⟶ Spec (.of (Polynomial k)))
  (α : X ⟶ S) (β : X ⟶ A) (h : α ≫ r ≫ p = β ≫ v)
  (T : LineBundle (diagonalAmbient k p r)) (N : LineBundle (fixedAmbient k p v))

/-- Tensor the pulled dual diagonal coefficient with the pulled dual fixed coefficient. -/
abbrev commonPencilBundle : LineBundle (commonAmbient k p r α) :=
  tensorLineBundle _
    (pullbackLineBundle (commonToDiagonal k p r α)
      (dualLineBundle _ (tensorLineBundle _ T (actualDivisorLineBundle k p r))))
    (pullbackLineBundle (commonToFixed k p r v α β h) (dualLineBundle _ N))

/-- The first compact product section retains the literal canonical diagonal section. -/
def commonPencilStart
    (b : SheafOfModules.unit (diagonalAmbient k p r).ringCatSheaf ⟶ T.val)
    (d : SheafOfModules.unit (fixedAmbient k p v).ringCatSheaf ⟶ N.val) :
    (commonPencilBundle k p r v α β h T N).val ⟶
      SheafOfModules.unit (commonAmbient k p r α).ringCatSheaf :=
  mixedProductFunctional (commonToDiagonal k p r α) (commonToFixed k p r v α β h)
    (tensorLineBundle _ T (actualDivisorLineBundle k p r)) N
    (twistedIdealSection _ (actualIdealLineBundle k p r) T
      (Hom.idealInclusion (Hom.compactificationGraph (projection k p) (r ≫ inclusion k p))) b) d

/-- The second compact product section uses the two actually lifted numerators. -/
def commonPencilEnd
    (a : SheafOfModules.unit (diagonalAmbient k p r).ringCatSheaf ⟶
      (tensorLineBundle _ T (actualDivisorLineBundle k p r)).val)
    (n : SheafOfModules.unit (fixedAmbient k p v).ringCatSheaf ⟶ N.val) :
    (commonPencilBundle k p r v α β h T N).val ⟶
      SheafOfModules.unit (commonAmbient k p r α).ringCatSheaf :=
  mixedProductFunctional (commonToDiagonal k p r α) (commonToFixed k p r v α β h)
    (tensorLineBundle _ T (actualDivisorLineBundle k p r)) N a n

variable (B : Type u) [CommRing B] (z : Polynomial k →+* B) (s : Spec (.of B) ⟶ S)
  (hs : s ≫ r ≫ p = Hom.boundaryCoordinateMap k B z)

omit [IsOpenImmersion r] in
/-- The constructed common-boundary section identity is an equality of restrictions of
these original compact pencil maps, not of substitute boundary-only maps. -/
theorem commonPencil_boundary
    (a : SheafOfModules.unit (diagonalAmbient k p r).ringCatSheaf ⟶
      (tensorLineBundle _ T (actualDivisorLineBundle k p r)).val)
    (b : SheafOfModules.unit (diagonalAmbient k p r).ringCatSheaf ⟶ T.val)
    (n d : SheafOfModules.unit (fixedAmbient k p v).ringCatSheaf ⟶ N.val)
    (hT : tensorSectionMap _
        (pullbackSectionMap (commonBoundaryToDiagonal k p r α B s ≫
          diagonalBoundaryMap k p r s) a)
        (pullbackSectionMap (commonBoundaryToFixed k p r v α β h B z s hs ≫
          fixedBoundaryMap k p v B z (s ≫ r) (by simpa only [Category.assoc] using hs)) n) =
      tensorSectionMap _
        (pullbackSectionMap (commonBoundaryToDiagonal k p r α B s ≫
          diagonalBoundaryMap k p r s)
          (twistedIdealSection _ (actualIdealLineBundle k p r) T
            (Hom.idealInclusion
              (Hom.compactificationGraph (projection k p) (r ≫ inclusion k p))) b))
        (pullbackSectionMap (commonBoundaryToFixed k p r v α β h B z s hs ≫
          fixedBoundaryMap k p v B z (s ≫ r) (by simpa only [Category.assoc] using hs)) d)) :
    Hom.pullbackToUnit (commonPencilStart k p r v α β h T N b d)
        (commonBoundaryInclusion k p r α B s) =
      Hom.pullbackToUnit (commonPencilEnd k p r v α β h T N a n)
        (commonBoundaryInclusion k p r α B s) := by
  apply Eq.symm
  apply mixedProductFunctional_boundary
  rw [← commonBoundaryToDiagonal_inclusion k p r α B s,
    ← commonBoundaryToFixed_inclusion k p r v α β h B z s hs]
  exact hT

omit [IsOpenImmersion r] in
/-- Unit boundary values of the two actual numerators make the compact second map a unit. -/
theorem commonPencilEnd_boundary_isIso
    (a : SheafOfModules.unit (diagonalAmbient k p r).ringCatSheaf ⟶
      (tensorLineBundle _ T (actualDivisorLineBundle k p r)).val)
    (n : SheafOfModules.unit (fixedAmbient k p v).ringCatSheaf ⟶ N.val)
    [IsIso (pullbackSectionMap (diagonalBoundaryMap k p r s) a)]
    [IsIso (pullbackSectionMap (fixedBoundaryMap k p v B z (s ≫ r)
      (by simpa only [Category.assoc] using hs)) n)] :
    IsIso (Hom.pullbackToUnit (commonPencilEnd k p r v α β h T N a n)
      (commonBoundaryInclusion k p r α B s)) := by
  have hA : IsIso (pullbackSectionMap
      (commonBoundaryInclusion k p r α B s ≫ commonToDiagonal k p r α) a) := by
    rw [← commonBoundaryToDiagonal_inclusion k p r α B s,
      ← pullbackSectionMap_comp]
    have : IsIso (pullbackSectionMap (commonBoundaryToDiagonal k p r α B s)
        (pullbackSectionMap (diagonalBoundaryMap k p r s) a)) := by
      change IsIso ((pullbackUnitIso _).inv ≫
        (Scheme.Modules.pullback _).map (pullbackSectionMap (diagonalBoundaryMap k p r s) a))
      infer_instance
    infer_instance
  have hN : IsIso (pullbackSectionMap
      (commonBoundaryInclusion k p r α B s ≫ commonToFixed k p r v α β h) n) := by
    rw [← commonBoundaryToFixed_inclusion k p r v α β h B z s hs,
      ← pullbackSectionMap_comp]
    have : IsIso (pullbackSectionMap (commonBoundaryToFixed k p r v α β h B z s hs)
        (pullbackSectionMap (fixedBoundaryMap k p v B z (s ≫ r)
          (by simpa only [Category.assoc] using hs)) n)) := by
      change IsIso ((pullbackUnitIso _).inv ≫ (Scheme.Modules.pullback _).map
        (pullbackSectionMap (fixedBoundaryMap k p v B z (s ≫ r)
          (by simpa only [Category.assoc] using hs)) n))
      infer_instance
    infer_instance
  exact mixedProductFunctional_boundary_isIso _ _ _ _ _ a n
end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
