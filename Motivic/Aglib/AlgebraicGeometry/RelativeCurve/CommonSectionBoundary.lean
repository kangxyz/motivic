module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.CommonBoundaryCoordinate
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.CommonBoundaryInclusions
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.PrescribedPairPullback
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.MixedPrescribedPencilBoundary
/-! # Actual relative section values force the full common pencil boundary equality -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil
variable {S X Y A B Z C D : Scheme.{u}}
  (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (π : C ⟶ S) [IsSeparated π]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  (p : Y ⟶ X) [Flat p] (hq : j ≫ π = p ≫ q)
  (a : A ⟶ X) [Flat a] (α : B ⟶ Y) (β : B ⟶ A) (h : α ≫ p = β ≫ a)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 _) p z)
  (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    Hom.idealModule (Hom.boundaryGraphTarget q z))
  (ha : Disjoint (Set.range a) (Set.range z)) (d : D ⟶ C)
  (hd : Disjoint (Set.range j) (Set.range d))

/-- Only the two actual producer equations are used; the scalar compatibility is derived
from the original source square and original full-boundary graph frame. -/
theorem relativeCommonBoundary_tensor
    (T : LineBundle (pullback (j ≫ π) π)) (N : LineBundle (pullback (a ≫ q) π))
    (aS : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶
      (tensorLineBundle _ T (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))).val)
    (bS : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶ T.val)
    (nS dS : SheafOfModules.unit (pullback (a ≫ q) π).ringCatSheaf ⟶ N.val)
    (hA : let zA := coprod.desc (Hom.infinityProductMap π j d) (Hom.graphBoundaryRestriction π j s)
      pullbackSectionMap zA aS ≫ pullbackTensorMap zA T.val
        (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j)).val =
      tensorUnitSection (pullbackSectionMap zA bS)
        (Hom.relativeFullBoundaryFrame q π j p hq z s hs H e d hd).inv)
    (hN : pullbackSectionMap (psiBoundaryInclusion q π j p hq a z s hs d) nS =
      (fixedProductBoundaryFrame q π a z e ha d).hom ≫
        pullbackSectionMap (psiBoundaryInclusion q π j p hq a z s hs d) dS) :
    let f := commonBoundaryToLambda π j α s d ≫
      coprod.desc (Hom.infinityProductMap π j d) (Hom.graphBoundaryRestriction π j s)
    let g := commonBoundaryToPsi q π j p hq a α β h z s hs d ≫
      psiBoundaryInclusion q π j p hq a z s hs d
    tensorSectionMap _ (pullbackSectionMap f aS) (pullbackSectionMap g nS) =
      tensorSectionMap _ (pullbackSectionMap f
        (twistedIdealSection _ (Hom.relativeCompactificationGraphLine π j) T
          (Hom.idealInclusion (Hom.compactificationGraph π j)) bS))
        (pullbackSectionMap g dS) := by
  let vA := commonBoundaryToLambda π j α s d
  let zA := coprod.desc (Hom.infinityProductMap π j d) (Hom.graphBoundaryRestriction π j s)
  let vN := commonBoundaryToPsi q π j p hq a α β h z s hs d
  let zN := psiBoundaryInclusion q π j p hq a z s hs d
  let E := Hom.relativeFullBoundaryFrame q π j p hq z s hs H e d hd
  let I := Hom.relativeCompactificationGraphLine π j
  let φ := Hom.idealInclusion (Hom.compactificationGraph π j)
  have hn := scalar_pair_pullback vN zN nS dS (fixedProductBoundaryFrame q π a z e ha d).hom hN
  have hc := commonBoundary_coordinate_eq q π a z e ha d j p hq α β h s hs H hd
  rw [← hc] at hn
  have hδ := compositeBoundaryFrame_coordinate vA zA (dualLineBundle _ I).val E
    (canonicalDualHom _ I.val φ)
  change pullbackSectionMap (vA ≫ zA) (canonicalDualHom _ I.val φ) ≫
      (compositeBoundaryFrame vA zA (dualLineBundle _ I).val E).hom =
    Hom.unitEndomorphismPullback vA (Hom.relativeFullBoundaryCoordinate q π j p hq z s hs H e d hd)
      at hδ
  rw [← hδ] at hn
  exact mixed_prescribed_boundary_tensor (vA ≫ zA) (vN ≫ zN) I T N φ bS dS nS aS
    (compositeBoundaryFrame vA zA (dualLineBundle _ I).val E)
    (prescribed_pair_pullback vA zA T.val (dualLineBundle _ I).val E aS bS hA) hn
end AlgebraicGeometry.Scheme.RelativeCurvePencil
