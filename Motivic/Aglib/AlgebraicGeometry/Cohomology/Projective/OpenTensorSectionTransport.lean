module
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.OpenPrescribedPair
/-! # Literal open tensor sections under native coefficient normalization -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible Scheme.Modules.Pullback.OpenRestriction
universe u
namespace AlgebraicGeometry.Scheme.CoherentGraph

/-- Tensor normalization of an actual open section. -/
def normalizeOpenTensorSection {C : Scheme.{u}} (U : C.Opens) (T M : C.Modules)
    {N : U.toScheme.Modules} (q : (Modules.restrictFunctor U.ι).obj M ≅ N)
    (a : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
      (Modules.restrictFunctor U.ι).obj (tensorSheaf C T M)) :
    SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
      tensorSheaf U.toScheme ((Modules.restrictFunctor U.ι).obj T) N :=
  a ≫ (tensorRestrictionIso U.ι T M).inv ≫ tensorSheafMap U.toScheme (𝟙 _) q.hom

/-- Normalization retains the original open boundary tensor comparison. -/
theorem normalizeOpenTensorSection_pullback {Z C : Scheme.{u}} (z : Z ⟶ C)
    (U : C.Opens) (T M : C.Modules) {N : U.toScheme.Modules}
    (q : (Modules.restrictFunctor U.ι).obj M ≅ N)
    (a : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
      (Modules.restrictFunctor U.ι).obj (tensorSheaf C T M)) :
    pullbackSectionMap (z ∣_ U) (normalizeOpenTensorSection U T M q a) ≫
        pullbackTensorMap (z ∣_ U) ((Modules.restrictFunctor U.ι).obj T) N ≫
        tensorSheafMap (z ⁻¹ᵁ U).toScheme ((localPullbackIso z U).inv.app T)
          ((Modules.pullback (z ∣_ U)).map q.inv ≫ (localPullbackIso z U).inv.app M) ≫
        (tensorRestrictionIso (z ⁻¹ᵁ U).ι ((Modules.pullback z).obj T)
          ((Modules.pullback z).obj M)).hom =
      pullbackSectionMap (z ∣_ U) a ≫ openBoundaryTensorComparison z U T M := by
  simp only [normalizeOpenTensorSection, pullbackSectionMap, Functor.map_comp, Category.assoc]
  rw [pullbackTensorMap_naturality_assoc]
  rw [tensorSheafMap_comp_assoc]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  have hq := ((Modules.pullback (z ∣_ U)).mapIso q).hom_inv_id_assoc
    ((localPullbackIso z U).inv.app M)
  simp only [Functor.mapIso_hom, Functor.mapIso_inv] at hq
  rw [hq]
  exact congrArg (fun f => (pullbackUnitIso (z ∣_ U)).inv ≫
    (Modules.pullback (z ∣_ U)).map a ≫ f)
      (openBoundaryTensorComparison_tensor z U T M)

end AlgebraicGeometry.Scheme.CoherentGraph
