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

/-- A genuine unit-valued boundary functional has its whole finite flat zero divisor on
our original retained overlap; this applies in particular to the product denominator. -/
theorem commonFunctional_finite_mono_flat
    (k : Type u) [Field k] {Y S X : Scheme.{u}} [IsAffine X]
    (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
    (r : S ⟶ Y) (α : X ⟶ S)
    (B : Type u) [CommRing B] (s : Spec (.of B) ⟶ S)
    (U : (Spec (.of (Polynomial k))).Opens)
    (z : Spec (.of B) ⟶ Spec (.of (Polynomial k)))
    (H0 : IsPullback (s ≫ r) (𝟙 _) p z)
    (hz : Set.range z = (U : Set (Spec (.of (Polynomial k))))ᶜ)
    (L : LineBundle (commonAmbient k p r α))
    (a : L.val ⟶ SheafOfModules.unit (commonAmbient k p r α).ringCatSheaf)
    [IsIso (Hom.pullbackToUnit a (commonBoundaryInclusion k p r α B s))] :
    let qX := commonSourceProjection k p r α
    let j := constantRetainedInclusion k p U qX
    let qD := pullback.fst qX (retainedProjection k p U)
    IsFinite (Hom.zeroInclusion (Hom.pullbackToUnit a j) ≫ qD) ∧
      Mono (Hom.pullbackToUnit a j) ∧ Flat (Hom.zeroInclusion (Hom.pullbackToUnit a j) ≫ qD) := by
  let qX := commonSourceProjection k p r α
  let j := constantRetainedInclusion k p U qX
  have : (constantRetainedTarget k p U qX).IsQuasiAffine :=
    constantRetainedTarget_quasiAffine k p U qX
  have : SmoothOfRelativeDimension 1 (j ≫ pullback.fst qX (projection k p)) := by
    dsimp only [j]
    rw [constantRetainedInclusion_fst]
    exact constantRetainedTarget_smooth k p U qX
  have : IsIso ((Scheme.Modules.pullback (commonBoundaryInclusion k p r α B s)).map a) := by
    have he : (Scheme.Modules.pullback (commonBoundaryInclusion k p r α B s)).map a =
        Hom.pullbackToUnit a (commonBoundaryInclusion k p r α B s) ≫ (pullbackUnitIso _).inv := by
      simp [Hom.pullbackToUnit]
    rw [he]
    infer_instance
  have hh := GlobalBoundaryPencil.pencil_finite_flat_on_open
    (commonBoundaryInclusion k p r α B s) (pullback.fst qX (projection k p)) j L a a 0 rfl
    (commonBoundary_retained_cover k p r α B s U z H0 hz)
  rw [GlobalBoundaryPencil.pencil_zero] at hh
  dsimp only [j] at hh
  rw [constantRetainedInclusion_fst] at hh
  exact hh
variable (k : Type u) [Field k] {Y S A X : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
  (r : S ⟶ Y) (v : A ⟶ Spec (.of (Polynomial k)))
  (α : X ⟶ S) (β : X ⟶ A) (h : α ≫ r ≫ p = β ≫ v)
  (T : LineBundle (diagonalAmbient k p r)) (N : LineBundle (fixedAmbient k p v))
  (B : Type u) [CommRing B] (z : Polynomial k →+* B) (s : Spec (.of B) ⟶ S)
  (hs : s ≫ r ≫ p = Hom.boundaryCoordinateMap k B z)

/-- Unit boundary values of the two actual numerators make the compact second map a unit. -/
theorem commonProduct_boundary_isIso
    (a : SheafOfModules.unit (diagonalAmbient k p r).ringCatSheaf ⟶
      T.val)
    (n : SheafOfModules.unit (fixedAmbient k p v).ringCatSheaf ⟶ N.val)
    [IsIso (pullbackSectionMap (diagonalBoundaryMap k p r s) a)]
    [IsIso (pullbackSectionMap (fixedBoundaryMap k p v B z (s ≫ r)
      (by simpa only [Category.assoc] using hs)) n)] :
    IsIso (Hom.pullbackToUnit (mixedProductFunctional (commonToDiagonal k p r α)
        (commonToFixed k p r v α β h) T N a n)
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

/-- The original product pole has a whole regular finite flat zero divisor. -/
theorem commonPole_finite_mono_flat [IsAffine X]
    (U : (Spec (.of (Polynomial k))).Opens)
    (H0 : IsPullback (s ≫ r) (𝟙 _) p (Hom.boundaryCoordinateMap k B z))
    (hz : Set.range (Hom.boundaryCoordinateMap k B z) =
      (U : Set (Spec (.of (Polynomial k))))ᶜ)
    (b : SheafOfModules.unit (diagonalAmbient k p r).ringCatSheaf ⟶ T.val)
    (d : SheafOfModules.unit (fixedAmbient k p v).ringCatSheaf ⟶ N.val)
    [IsIso (pullbackSectionMap (diagonalBoundaryMap k p r s) b)]
    [IsIso (pullbackSectionMap (fixedBoundaryMap k p v B z (s ≫ r)
      (by simpa only [Category.assoc] using hs)) d)] :
    let j := constantRetainedInclusion k p U (commonSourceProjection k p r α)
    let qD := pullback.fst (commonSourceProjection k p r α) (retainedProjection k p U)
    let pole := Hom.pullbackToUnit
      (mixedProductFunctional (commonToDiagonal k p r α) (commonToFixed k p r v α β h) T N b d) j
    IsFinite (Hom.zeroInclusion pole ≫ qD) ∧ Mono pole ∧
      Flat (Hom.zeroInclusion pole ≫ qD) := by
  have := commonProduct_boundary_isIso k p r v α β h T N B z s hs b d
  exact commonFunctional_finite_mono_flat k p r α B s U (Hom.boundaryCoordinateMap k B z) H0 hz
    (tensorLineBundle _ (pullbackLineBundle (commonToDiagonal k p r α) (dualLineBundle _ T))
      (pullbackLineBundle (commonToFixed k p r v α β h) (dualLineBundle _ N)))
    (mixedProductFunctional (commonToDiagonal k p r α) (commonToFixed k p r v α β h) T N b d)
end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
