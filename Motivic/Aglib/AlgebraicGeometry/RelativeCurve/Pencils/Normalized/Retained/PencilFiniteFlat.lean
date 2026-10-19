module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Normalized.Common.FiniteFlatPencil
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Normalized.Retained.ProductPullback
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Pencils.Polynomial.PrecompIso
/-! # The actual correcting family in its original diagonal-times-pole domain -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible PolynomialBoundaryPencil
universe u
namespace AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
variable (k : Type u) [Field k] {Y S A X : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
  (r : S ⟶ Y) [IsOpenImmersion r] (v : A ⟶ Spec (.of (Polynomial k)))
  (α : X ⟶ S) (β : X ⟶ A) (h : α ≫ r ≫ p = β ≫ v)
  (U : (Spec (.of (Polynomial k))).Opens)
  (φ : X ⟶ pullback U.ι p)
  (hφ : φ ≫ retainedInclusion k p U = α ≫ r ≫ inclusion k p) [Flat α]
  (T : LineBundle (diagonalAmbient k p r)) (N : LineBundle (fixedAmbient k p v))

abbrev retainedGraphPencilBundle := tensorLineBundle _
  ⟨Hom.idealModule (commonRetainedGraph k p r α U φ hφ),
    commonRetainedGraph_locallyRankOne k p r α U φ hφ⟩
  (tensorLineBundle _
    (retainedDiagonalLine k p r α U (dualLineBundle _ T))
    (retainedFixedLine k p r v α β h U (dualLineBundle _ N)))

variable
  (a : SheafOfModules.unit (diagonalAmbient k p r).ringCatSheaf ⟶
    (tensorLineBundle _ T (actualDivisorLineBundle k p r)).val)
  (b : SheafOfModules.unit (diagonalAmbient k p r).ringCatSheaf ⟶ T.val)
  (n d : SheafOfModules.unit (fixedAmbient k p v).ringCatSheaf ⟶ N.val)

/-- The exact finite-flat property of the original graph-domain polynomial family. -/
def retainedGraphFamilyFiniteFlat : Prop :=
    let qX := commonSourceProjection k p r α
    let qD := pullback.fst qX (retainedProjection k p U)
    let f := familyMap (qD ≫ qX) (retainedGraphPencilBundle k p r v α β h U φ hφ T N)
      (Hom.productSection (Hom.idealInclusion (commonRetainedGraph k p r α U φ hφ))
        (Hom.productSection
          (retainedDiagonalFunctional k p r α U (sectionDualFunctional _ T b))
          (retainedFixedFunctional k p r v α β h U (sectionDualFunctional _ N d))))
      ((retainedPencilLineIso k p r v α β h U φ hφ T N).hom ≫
        Hom.productSection
          (retainedDiagonalFunctional k p r α U
            (sectionDualFunctional _ (tensorLineBundle _ T (actualDivisorLineBundle k p r)) a))
          (retainedFixedFunctional k p r v α β h U (sectionDualFunctional _ N n)))
    IsFinite (Hom.zeroInclusion f ≫ parameterMap qX qD) ∧
      Flat (Hom.zeroInclusion f ≫ parameterMap qX qD)

omit [IsOpenImmersion r] in
/-- Finite flatness transports to the actual graph-times-pole coefficient domain.
The input family is the constructed compact pencil, not an assumed endpoint cycle. -/
theorem retainedGraphFamily_finite_flat
    (hf :
      let qX := commonSourceProjection k p r α
      let j := constantRetainedInclusion k p U qX
      let qD := pullback.fst qX (retainedProjection k p U)
      let f := familyMap (qD ≫ qX) (pullbackLineBundle j (commonPencilBundle k p r v α β h T N))
        (Hom.pullbackToUnit (commonPencilStart k p r v α β h T N b d) j)
        (Hom.pullbackToUnit (commonPencilEnd k p r v α β h T N a n) j)
      IsFinite (Hom.zeroInclusion f ≫ parameterMap qX qD) ∧
        Flat (Hom.zeroInclusion f ≫ parameterMap qX qD)) :
    retainedGraphFamilyFiniteFlat k p r v α β h U φ hφ T N a b n d := by
  unfold retainedGraphFamilyFiniteFlat
  have hfin := hf.1
  have hflat := hf.2
  let qX := commonSourceProjection k p r α
  let j := constantRetainedInclusion k p U qX
  let qD := pullback.fst qX (retainedProjection k p U)
  let L := retainedGraphPencilBundle k p r v α β h U φ hφ T N
  let M := pullbackLineBundle j (commonPencilBundle k p r v α β h T N)
  let e := retainedPencilCompactIso k p r v α β h U φ hφ T N
  let a0 := Hom.pullbackToUnit (commonPencilStart k p r v α β h T N b d) j
  let a1 := Hom.pullbackToUnit (commonPencilEnd k p r v α β h T N a n) j
  have hi := familyZeroPrecomp_isFinite (qD ≫ qX) L M e a0 a1 (parameterMap qX qD)
  have hj := familyZeroPrecomp_flat (qD ≫ qX) L M e a0 a1 (parameterMap qX qD)
  dsimp only [e, a0, a1, j, commonPencilStart, commonPencilEnd] at hi hj
  rw [retainedPencilCompactIso_start, retainedPencilCompactIso_end] at hi hj
  exact ⟨hi, hj⟩

/-- The exact finite-flat property of the original twice-pulled product pole. -/
def retainedPoleFiniteFlat : Prop :=
    let qD := pullback.fst (commonSourceProjection k p r α) (retainedProjection k p U)
    let pole := Hom.productSection
      (retainedDiagonalFunctional k p r α U (sectionDualFunctional _ T b))
      (retainedFixedFunctional k p r v α β h U (sectionDualFunctional _ N d))
    IsFinite (Hom.zeroInclusion pole ≫ qD) ∧ Flat (Hom.zeroInclusion pole ≫ qD)

omit [IsSeparated p] [IsOpenImmersion r] [Flat α] in
/-- The original product pole, expressed on the twice-pulled factor modules, remains
finite flat with its full scheme structure. -/
theorem retainedPole_finite_flat
    (hp :
      let j := constantRetainedInclusion k p U (commonSourceProjection k p r α)
      let qD := pullback.fst (commonSourceProjection k p r α) (retainedProjection k p U)
      let pole := Hom.pullbackToUnit
        (mixedProductFunctional (commonToDiagonal k p r α) (commonToFixed k p r v α β h) T N b d) j
      IsFinite (Hom.zeroInclusion pole ≫ qD) ∧ Mono pole ∧ Flat (Hom.zeroInclusion pole ≫ qD)) :
    retainedPoleFiniteFlat k p r v α β h U T N b d := by
  unfold retainedPoleFiniteFlat
  have hfin := hp.1
  have hflat := hp.2.2
  let j := constantRetainedInclusion k p U (commonSourceProjection k p r α)
  let qD := pullback.fst (commonSourceProjection k p r α) (retainedProjection k p U)
  let pole := Hom.pullbackToUnit
    (mixedProductFunctional (commonToDiagonal k p r α) (commonToFixed k p r v α β h) T N b d) j
  let e := retainedProductPullbackIso k p r v α β h U (dualLineBundle _ T) (dualLineBundle _ N)
  have he := zeroSchemePrecompIso_hom_inclusion e pole
  have hi : IsFinite (Hom.zeroInclusion (e.hom ≫ pole) ≫ qD) := by
    rw [← he, Category.assoc]
    infer_instance
  have hj : Flat (Hom.zeroInclusion (e.hom ≫ pole) ≫ qD) := by
    rw [← he, Category.assoc]
    infer_instance
  dsimp only [e, pole, mixedProductFunctional, j] at hi hj
  rw [retainedProductPullbackIso_functional] at hi hj
  exact ⟨hi, hj⟩
end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
