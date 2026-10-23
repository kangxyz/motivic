/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Normalized.Common.BoundaryCoordinate
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Boundary.MixedPrescribedPencilBoundary
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Sections.Normalized.DiagonalPair
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Sections.Normalized.FixedOpenPair
/-! # Actual lambda and fixed-U psi values give the common pencil boundary equation -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
variable (k : Type u) [Field k] {Y S X : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
  (r : S ⟶ Y) [IsOpenImmersion r] {Q : Type u} [CommRing Q]
  (v : Spec (.of Q) ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion v]
  (α : X ⟶ S) (β : X ⟶ Spec (.of Q)) (h : α ≫ r ≫ p = β ≫ v)
  (B : Type u) [CommRing B] (z : Polynomial k →+* B)
  (hd : Disjoint (Set.range v) (Set.range (Hom.boundaryCoordinateMap k B z)))
  (s : Spec (.of B) ⟶ S) (hs : s ≫ r ≫ p = Hom.boundaryCoordinateMap k B z)
  (H : IsPullback s (𝟙 _) (r ≫ p) (Hom.boundaryCoordinateMap k B z))

/-- Pullback of the literal two producer equations yields the actual common-boundary
pencil tensor equality. The coordinate relation is proved from the original geometry. -/
theorem actualCommonBoundary_tensor
    (T : LineBundle (diagonalAmbient k p r)) (N : LineBundle (fixedAmbient k p v))
    (a : SheafOfModules.unit (diagonalAmbient k p r).ringCatSheaf ⟶
      (tensorLineBundle _ T (actualDivisorLineBundle k p r)).val)
    (b : SheafOfModules.unit (diagonalAmbient k p r).ringCatSheaf ⟶ T.val)
    (n d : SheafOfModules.unit (fixedAmbient k p v).ringCatSheaf ⟶ N.val)
    (ha : pullbackSectionMap (diagonalBoundaryMap k p r s) a ≫
        pullbackTensorMap (diagonalBoundaryMap k p r s) T.val
          (actualDivisorLineBundle k p r).val =
      tensorUnitSection (pullbackSectionMap (diagonalBoundaryMap k p r s) b)
        (actualBoundaryIso k p r B z s hs H).inv)
    (hn : pullbackSectionMap (fixedBoundaryMap k p v B z (s ≫ r)
        (by simpa only [Category.assoc] using hs)) n =
      (fixedBoundaryUnit k p v B z hd).hom ≫
        pullbackSectionMap (fixedBoundaryMap k p v B z (s ≫ r)
          (by simpa only [Category.assoc] using hs)) d) :
    let f := commonBoundaryToDiagonal k p r α B s ≫ diagonalBoundaryMap k p r s
    let g := commonBoundaryToFixed k p r v α β h B z s hs ≫
      fixedBoundaryMap k p v B z (s ≫ r) (by simpa only [Category.assoc] using hs)
    tensorSectionMap _ (pullbackSectionMap f a) (pullbackSectionMap g n) =
      tensorSectionMap _
        (pullbackSectionMap f (twistedIdealSection _ (actualIdealLineBundle k p r) T
          (Hom.idealInclusion (Hom.compactificationGraph (projection k p) (r ≫ inclusion k p))) b))
        (pullbackSectionMap g d) := by
  let vA := commonBoundaryToDiagonal k p r α B s
  let zA := diagonalBoundaryMap k p r s
  let vN := commonBoundaryToFixed k p r v α β h B z s hs
  let zN := fixedBoundaryMap k p v B z (s ≫ r) (by simpa only [Category.assoc] using hs)
  let E := actualBoundaryIso k p r B z s hs H
  let I := actualIdealLineBundle k p r
  let φ := Hom.idealInclusion (Hom.compactificationGraph (projection k p) (r ≫ inclusion k p))
  have hn' := scalar_pair_pullback vN zN n d (fixedBoundaryUnit k p v B z hd).hom hn
  have hc := commonBoundary_coordinate_eq k p r v α β h B z hd s hs H
  rw [← hc] at hn'
  have hδ := compositeBoundaryFrame_coordinate vA zA (actualDivisorLineBundle k p r).val E
    (canonicalDualHom _ I.val φ)
  change pullbackSectionMap (vA ≫ zA) (canonicalDualHom _ I.val φ) ≫
      (compositeBoundaryFrame vA zA (actualDivisorLineBundle k p r).val E).hom =
    Hom.unitEndomorphismPullback vA (actualDiagonalBoundaryCoordinate k p r B z s hs H) at hδ
  rw [← hδ] at hn'
  exact mixed_prescribed_boundary_tensor (vA ≫ zA) (vN ≫ zN) I T N φ b d n a
    (compositeBoundaryFrame vA zA (actualDivisorLineBundle k p r).val E)
    (prescribed_pair_pullback vA zA T.val (actualDivisorLineBundle k p r).val E a b ha) hn'
end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
