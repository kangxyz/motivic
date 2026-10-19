module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Normalized.Common.PencilMaps
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Normalized.Common.RetainedCover
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Pencils.Polynomial.FiniteFlat
/-! # Finiteness and flatness of the actual correcting polynomial family -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible PolynomialBoundaryPencil
universe u
namespace AlgebraicGeometry.Scheme.AffineLineEtaleCompactification

/-- The entire literal polynomial zero family on the original overlap is finite flat.
Only the actual compact boundary equation is used; family properties are derived. -/
theorem commonPencil_finite_flat
    (k : Type u) [Field k] {Y S A X : Scheme.{u}} [IsAffine X]
    (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
    (r : S ⟶ Y) [IsOpenImmersion r] (v : A ⟶ Spec (.of (Polynomial k)))
    (α : X ⟶ S) (β : X ⟶ A) (h : α ≫ r ≫ p = β ≫ v)
    (T : LineBundle (diagonalAmbient k p r)) (N : LineBundle (fixedAmbient k p v))
    (B : Type u) [CommRing B] (z : Polynomial k →+* B) (s : Spec (.of B) ⟶ S)
    (hs : s ≫ r ≫ p = Hom.boundaryCoordinateMap k B z)
    (U : (Spec (.of (Polynomial k))).Opens)
    (H0 : IsPullback (s ≫ r) (𝟙 _) p (Hom.boundaryCoordinateMap k B z))
    (hz : Set.range (Hom.boundaryCoordinateMap k B z) =
      (U : Set (Spec (.of (Polynomial k))))ᶜ)
    (a : SheafOfModules.unit (diagonalAmbient k p r).ringCatSheaf ⟶
      (tensorLineBundle _ T (actualDivisorLineBundle k p r)).val)
    (b : SheafOfModules.unit (diagonalAmbient k p r).ringCatSheaf ⟶ T.val)
    (n d : SheafOfModules.unit (fixedAmbient k p v).ringCatSheaf ⟶ N.val)
    [IsIso (pullbackSectionMap (diagonalBoundaryMap k p r s) a)]
    [IsIso (pullbackSectionMap (fixedBoundaryMap k p v B z (s ≫ r)
      (by simpa only [Category.assoc] using hs)) n)]
    (heq : Hom.pullbackToUnit (commonPencilStart k p r v α β h T N b d)
        (commonBoundaryInclusion k p r α B s) =
      Hom.pullbackToUnit (commonPencilEnd k p r v α β h T N a n)
        (commonBoundaryInclusion k p r α B s)) :
    let qX := commonSourceProjection k p r α
    let j := constantRetainedInclusion k p U qX
    let qD := pullback.fst qX (retainedProjection k p U)
    let f := familyMap (qD ≫ qX) (pullbackLineBundle j (commonPencilBundle k p r v α β h T N))
      (Hom.pullbackToUnit (commonPencilStart k p r v α β h T N b d) j)
      (Hom.pullbackToUnit (commonPencilEnd k p r v α β h T N a n) j)
    IsFinite (Hom.zeroInclusion f ≫ parameterMap qX qD) ∧
      Flat (Hom.zeroInclusion f ≫ parameterMap qX qD) := by
  let qX := commonSourceProjection k p r α
  let j := constantRetainedInclusion k p U qX
  have : (constantRetainedTarget k p U qX).IsQuasiAffine :=
    constantRetainedTarget_quasiAffine k p U qX
  have : SmoothOfRelativeDimension 1 (j ≫ pullback.fst qX (projection k p)) := by
    dsimp only [j]
    rw [constantRetainedInclusion_fst]
    exact constantRetainedTarget_smooth k p U qX
  have : IsIso (Hom.pullbackToUnit (commonPencilEnd k p r v α β h T N a n)
      (commonBoundaryInclusion k p r α B s)) :=
    commonPencilEnd_boundary_isIso k p r v α β h T N B z s hs a n
  have : IsIso (Hom.pullbackToUnit (commonPencilStart k p r v α β h T N b d)
      (commonBoundaryInclusion k p r α B s)) := heq ▸ inferInstance
  have : IsIso ((Scheme.Modules.pullback (commonBoundaryInclusion k p r α B s)).map
      (commonPencilStart k p r v α β h T N b d)) := by
    have he : (Scheme.Modules.pullback (commonBoundaryInclusion k p r α B s)).map
        (commonPencilStart k p r v α β h T N b d) =
        Hom.pullbackToUnit (commonPencilStart k p r v α β h T N b d)
          (commonBoundaryInclusion k p r α B s) ≫ (pullbackUnitIso _).inv := by
      simp [Hom.pullbackToUnit]
    rw [he]
    infer_instance
  have hh := retained_familySource_finite_flat qX (pullback.fst qX (projection k p)) j
    (commonBoundaryInclusion k p r α B s) (commonPencilBundle k p r v α β h T N)
    (commonPencilStart k p r v α β h T N b d)
    (commonPencilEnd k p r v α β h T N a n) heq
    (commonBoundary_retained_cover k p r α B s U (Hom.boundaryCoordinateMap k B z) H0 hz)
  dsimp only [j] at hh
  rw [constantRetainedInclusion_fst] at hh
  exact hh
end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
