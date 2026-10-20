module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Retained.CompactIso
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.PencilFiniteFlat
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.PoleFiniteFlat
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Pencils.Polynomial.PrecompIso
/-! # The original graph-domain family and pole, with full scheme structure -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible PolynomialBoundaryPencil
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil
variable (R : Type u) [CommRing R] {S X Y A B C V : Scheme.{u}}
  (bR : B ⟶ Spec (.of R))
  (q : X ⟶ S) (π : C ⟶ S) [IsSeparated π]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  (p : Y ⟶ X) (hq : j ≫ π = p ≫ q) (a₀ : A ⟶ X)
  (α : B ⟶ Y) [Flat α] (β : B ⟶ A) (h : α ≫ p = β ≫ a₀)
  (v : V ⟶ C) [IsOpenImmersion v] (φ : B ⟶ V) (hφ : φ ≫ v = α ≫ j)
  (T : LineBundle (pullback (j ≫ π) π)) (N : LineBundle (pullback (a₀ ≫ q) π))

/-- Tensor the retained graph ideal line with the pulled dual lambda and psi coefficients. -/
abbrev retainedGraphPencilBundle := tensorLineBundle _
  ⟨Hom.idealModule (relativeRetainedGraph π j α v φ hφ),
    commonRetainedGraph_locallyRankOne π j α v φ hφ⟩
  (tensorLineBundle _
    (retainedLambdaLine π j α v (dualLineBundle _ T))
    (retainedPsiLine q π j p hq a₀ α β h v (dualLineBundle _ N)))

variable
  (a : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶
    (tensorLineBundle _ T (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))).val)
  (b : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶ T.val)
  (n d : SheafOfModules.unit (pullback (a₀ ≫ q) π).ringCatSheaf ⟶ N.val)

/-- The exact finite-flat property of the original graph-domain polynomial family. -/
def retainedGraphFamilyFiniteFlat : Prop :=
    let qX := commonProjection π j α
    let qD := pullback.fst qX (v ≫ π)
    let f := familyMap (qD ≫ bR) (retainedGraphPencilBundle q π j p hq a₀ α β h v φ hφ T N)
      (Hom.productSection (Hom.idealInclusion (relativeRetainedGraph π j α v φ hφ))
        (Hom.productSection
          (retainedLambdaFunctional π j α v (sectionDualFunctional _ T b))
          (retainedPsiFunctional q π j p hq a₀ α β h v (sectionDualFunctional _ N d))))
      ((retainedPencilLineIso q π j p hq a₀ α β h v φ hφ T N).hom ≫
        Hom.productSection
          (retainedLambdaFunctional π j α v
            (sectionDualFunctional _ (tensorLineBundle _ T
              (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))) a))
          (retainedPsiFunctional q π j p hq a₀ α β h v (sectionDualFunctional _ N n)))
    IsFinite (Hom.zeroInclusion f ≫ parameterMap bR qD) ∧
      Flat (Hom.zeroInclusion f ≫ parameterMap bR qD)

/-- Finite flatness transports to the actual graph-times-pole coefficient domain.
The input family is the constructed compact pencil, not an assumed endpoint cycle. -/
theorem retainedGraphFamily_finite_flat
    (hf :
      let qX := commonProjection π j α
      let i := retainedProductInclusion qX π v
      let qD := pullback.fst qX (v ≫ π)
      let f := familyMap (qD ≫ bR)
        (pullbackLineBundle i (commonPencilBundle q π j p hq a₀ α β h T N))
        (Hom.pullbackToUnit (commonPencilStart q π j p hq a₀ α β h T N b d) i)
        (Hom.pullbackToUnit (commonPencilEnd q π j p hq a₀ α β h T N a n) i)
      IsFinite (Hom.zeroInclusion f ≫ parameterMap bR qD) ∧
        Flat (Hom.zeroInclusion f ≫ parameterMap bR qD)) :
    retainedGraphFamilyFiniteFlat R bR q π j p hq a₀ α β h v φ hφ T N a b n d := by
  unfold retainedGraphFamilyFiniteFlat
  have hfin := hf.1
  have hflat := hf.2
  let qX := commonProjection π j α
  let i := retainedProductInclusion qX π v
  let qD := pullback.fst qX (v ≫ π)
  let L := retainedGraphPencilBundle q π j p hq a₀ α β h v φ hφ T N
  let M := pullbackLineBundle i (commonPencilBundle q π j p hq a₀ α β h T N)
  let e := retainedPencilCompactIso q π j p hq a₀ α β h v φ hφ T N
  let a0 := Hom.pullbackToUnit (commonPencilStart q π j p hq a₀ α β h T N b d) i
  let a1 := Hom.pullbackToUnit (commonPencilEnd q π j p hq a₀ α β h T N a n) i
  have hi := familyZeroPrecomp_isFinite (qD ≫ bR) L M e a0 a1 (parameterMap bR qD)
  have hj := familyZeroPrecomp_flat (qD ≫ bR) L M e a0 a1 (parameterMap bR qD)
  dsimp only [e, a0, a1, i, commonPencilStart, commonPencilEnd] at hi hj
  rw [retainedPencilCompactIso_start, retainedPencilCompactIso_end] at hi hj
  exact ⟨hi, hj⟩

/-- The exact finite-flat property of the original twice-pulled product pole. -/
def retainedPoleFiniteFlat : Prop :=
    let qD := pullback.fst (commonProjection π j α) (v ≫ π)
    let pole := Hom.productSection
      (retainedLambdaFunctional π j α v (sectionDualFunctional _ T b))
      (retainedPsiFunctional q π j p hq a₀ α β h v (sectionDualFunctional _ N d))
    IsFinite (Hom.zeroInclusion pole ≫ qD) ∧ Flat (Hom.zeroInclusion pole ≫ qD)

omit [IsSeparated π] [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  [Flat α] [IsOpenImmersion v] in
/-- The original product pole, expressed on the twice-pulled factor modules, remains
finite flat with its full scheme structure. -/
theorem retainedPole_finite_flat
    (hp :
      let i := retainedProductInclusion (commonProjection π j α) π v
      let qD := pullback.fst (commonProjection π j α) (v ≫ π)
      let pole := Hom.pullbackToUnit
        (mixedProductFunctional (commonToLambda π j α)
          (commonToPsi q π j p hq a₀ α β h) T N b d) i
      IsFinite (Hom.zeroInclusion pole ≫ qD) ∧ Mono pole ∧
        Flat (Hom.zeroInclusion pole ≫ qD)) :
    retainedPoleFiniteFlat q π j p hq a₀ α β h v T N b d := by
  unfold retainedPoleFiniteFlat
  have hfin := hp.1
  have hflat := hp.2.2
  let i := retainedProductInclusion (commonProjection π j α) π v
  let qD := pullback.fst (commonProjection π j α) (v ≫ π)
  let pole := Hom.pullbackToUnit
    (mixedProductFunctional (commonToLambda π j α)
          (commonToPsi q π j p hq a₀ α β h) T N b d) i
  let e := retainedProductPullbackIso q π j p hq a₀ α β h v
    (dualLineBundle _ T) (dualLineBundle _ N)
  have he := zeroSchemePrecompIso_hom_inclusion e pole
  have hi : IsFinite (Hom.zeroInclusion (e.hom ≫ pole) ≫ qD) := by
    rw [← he, Category.assoc]
    infer_instance
  have hj : Flat (Hom.zeroInclusion (e.hom ≫ pole) ≫ qD) := by
    rw [← he, Category.assoc]
    infer_instance
  dsimp only [e, pole, mixedProductFunctional, i] at hi hj
  rw [retainedProductPullbackIso_functional] at hi hj
  exact ⟨hi, hj⟩
end AlgebraicGeometry.Scheme.RelativeCurvePencil
