module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.CommonPencilUnit
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.CommonCurveGeometry
public import Motivic.Aglib.AlgebraicGeometry.GlobalBoundaryPencil
/-! # The actual two-factor pole divisor is finite flat on the retained curve -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil
variable {S X Y A B Z C D V : Scheme.{u}} [IsAffine S] [IsAffine B] [IsAffine V]
  (q : X ⟶ S) (π : C ⟶ S) [IsProper π] (j : Y ⟶ C) (p : Y ⟶ X)
  (hq : j ≫ π = p ≫ q) (a : A ⟶ X)
  (α : B ⟶ Y) (β : B ⟶ A) (h : α ≫ p = β ≫ a)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (d : D ⟶ C)

/-- No finiteness or regularity premise is imposed on the product divisor. -/
theorem commonPole_finite_mono_flat
    (v : V ⟶ C) [IsOpenImmersion v] [SmoothOfRelativeDimension 1 (v ≫ π)]
    (hc : ∀ c : C, c ∈ Set.range v ∨ c ∈ Set.range d ∨ c ∈ Set.range (s ≫ j))
    (T : LineBundle (pullback (j ≫ π) π)) (N : LineBundle (pullback (a ≫ q) π))
    (bS : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶ T.val)
    (dS : SheafOfModules.unit (pullback (a ≫ q) π).ringCatSheaf ⟶ N.val)
    [IsIso (pullbackSectionMap
      (coprod.desc (Hom.infinityProductMap π j d) (Hom.graphBoundaryRestriction π j s)) bS)]
    [IsIso (pullbackSectionMap (psiBoundaryInclusion q π j p hq a z s hs d) dS)] :
    let i := retainedProductInclusion (commonProjection π j α) π v
    let f := Hom.pullbackToUnit
      (mixedProductFunctional (commonToLambda π j α)
        (commonToPsi q π j p hq a α β h) T N bS dS) i
    IsFinite (Hom.zeroInclusion f ≫ pullback.fst (commonProjection π j α) (v ≫ π)) ∧
      Mono f ∧ Flat (Hom.zeroInclusion f ≫ pullback.fst (commonProjection π j α) (v ≫ π)) := by
  let qX := commonProjection π j α
  let i := retainedProductInclusion qX π v
  let L := tensorLineBundle _ (pullbackLineBundle (commonToLambda π j α) (dualLineBundle _ T))
    (pullbackLineBundle (commonToPsi q π j p hq a α β h) (dualLineBundle _ N))
  let f := mixedProductFunctional (commonToLambda π j α)
    (commonToPsi q π j p hq a α β h) T N bS dS
  let zD := commonBoundaryInclusion π j α s d
  have : IsAffine (retainedProduct qX π v) := retainedProduct_affine qX π v
  have : SmoothOfRelativeDimension 1 (i ≫ pullback.fst qX π) :=
    retainedProduct_smooth qX π v
  have : IsIso (Hom.pullbackToUnit f zD) :=
    commonProduct_boundary_isIso q π j p hq a α β h z s hs d T N bS dS
  have : IsIso ((Modules.pullback zD).map f) := by
    have hf : (Modules.pullback zD).map f =
        Hom.pullbackToUnit f zD ≫ (pullbackUnitIso zD).inv := by simp [Hom.pullbackToUnit]
    rw [hf]
    infer_instance
  have hf := GlobalBoundaryPencil.pencil_finite_flat_on_open zD (pullback.fst qX π)
    i L f f 0 rfl (commonBoundary_retained_cover π v j α s d hc)
  rw [GlobalBoundaryPencil.pencil_zero] at hf
  dsimp only [i] at hf
  rw [retainedProductInclusion_fst] at hf
  exact hf
end AlgebraicGeometry.Scheme.RelativeCurvePencil
