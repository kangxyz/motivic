module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.PencilMaps
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.CurveGeometry
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Pencils.Polynomial.FiniteFlat
/-! # The actual relative correcting polynomial family is finite flat -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible PolynomialBoundaryPencil
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil
variable (R : Type u) [CommRing R] {S X Y A B Z C D V : Scheme.{u}} [IsAffine S] [IsAffine B]
  [IsAffine V] (b : B ⟶ Spec (.of R))
  (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (π : C ⟶ S) [IsProper π]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  (p : Y ⟶ X) [Flat p] (hq : j ≫ π = p ≫ q)
  (a : A ⟶ X) [Flat a] (α : B ⟶ Y) (β : B ⟶ A) (h : α ≫ p = β ≫ a)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 _) p z)
  (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    Hom.idealModule (Hom.boundaryGraphTarget q z))
  (ha : Disjoint (Set.range a) (Set.range z)) (d : D ⟶ C)
  (hd : Disjoint (Set.range j) (Set.range d))

/-- The literal polynomial zero family is derived, not a premise. -/
theorem relativePencil_finite_flat
    (v : V ⟶ C) [IsOpenImmersion v] [SmoothOfRelativeDimension 1 (v ≫ π)]
    (hc : ∀ c : C, c ∈ Set.range v ∨ c ∈ Set.range d ∨ c ∈ Set.range (s ≫ j))
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
        pullbackSectionMap (psiBoundaryInclusion q π j p hq a z s hs d) dS)
    [IsIso (pullbackSectionMap
      (coprod.desc (Hom.infinityProductMap π j d) (Hom.graphBoundaryRestriction π j s)) aS)]
    [IsIso (pullbackSectionMap (psiBoundaryInclusion q π j p hq a z s hs d) nS)] :
    let qX := commonProjection π j α
    let i := retainedProductInclusion qX π v
    let qR := pullback.fst qX (v ≫ π)
    let f := familyMap (qR ≫ b)
      (pullbackLineBundle i (commonPencilBundle q π j p hq a α β h T N))
      (Hom.pullbackToUnit (commonPencilStart q π j p hq a α β h T N bS dS) i)
      (Hom.pullbackToUnit (commonPencilEnd q π j p hq a α β h T N aS nS) i)
    IsFinite (Hom.zeroInclusion f ≫ parameterMap b qR) ∧
      Flat (Hom.zeroInclusion f ≫ parameterMap b qR) := by
  let qX := commonProjection π j α
  let i := retainedProductInclusion qX π v
  let L := commonPencilBundle q π j p hq a α β h T N
  let c0 := commonPencilStart q π j p hq a α β h T N bS dS
  let c1 := commonPencilEnd q π j p hq a α β h T N aS nS
  let zD := commonBoundaryInclusion π j α s d
  have : IsAffine (retainedProduct qX π v) := retainedProduct_affine qX π v
  have : SmoothOfRelativeDimension 1 (i ≫ pullback.fst qX π) :=
    retainedProduct_smooth qX π v
  have heq : Hom.pullbackToUnit c0 zD = Hom.pullbackToUnit c1 zD :=
    (relativeCommonPencil_boundary q π j p hq a α β h z s hs H e ha d hd
      T N aS bS nS dS hA hN).symm
  have : IsIso (Hom.pullbackToUnit c1 zD) := commonProduct_boundary_isIso
    q π j p hq a α β h z s hs d
    (tensorLineBundle _ T (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))) N aS nS
  have : IsIso (Hom.pullbackToUnit c0 zD) := heq ▸ inferInstance
  have : IsIso ((Scheme.Modules.pullback zD).map c0) := by
    have hu : (Scheme.Modules.pullback zD).map c0 =
        Hom.pullbackToUnit c0 zD ≫ (pullbackUnitIso zD).inv := by simp [Hom.pullbackToUnit]
    rw [hu]
    infer_instance
  have hf := retained_familySource_finite_flat b (pullback.fst qX π) i zD L c0 c1 heq
    (commonBoundary_retained_cover π v j α s d hc)
  dsimp only [i] at hf
  rw [retainedProductInclusion_fst] at hf
  exact hf
end AlgebraicGeometry.Scheme.RelativeCurvePencil
