module
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.Boundary.Sections.OpenRestrictionPullback
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.PairNormalization
/-! # Actual open prescribed pair equations in native restricted tensor coefficients -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible Scheme.Modules.Pullback.OpenRestriction
universe u
namespace AlgebraicGeometry.Scheme.CoherentGraph

/-- The exact boundary tensor comparison for an actual section on an open. -/
def openBoundaryTensorComparison {Z C : Scheme.{u}} (z : Z ⟶ C) (U : C.Opens)
    (T M : C.Modules) :
    (Modules.pullback (z ∣_ U)).obj ((Modules.restrictFunctor U.ι).obj (tensorSheaf C T M)) ⟶
      (Modules.restrictFunctor (z ⁻¹ᵁ U).ι).obj
        (tensorSheaf Z ((Modules.pullback z).obj T) ((Modules.pullback z).obj M)) :=
  (localPullbackIso z U).inv.app (tensorSheaf C T M) ≫
    (Modules.restrictFunctor (z ⁻¹ᵁ U).ι).map (pullbackTensorMap z T M)

/-- Native tensor restriction and local pullback retain the original comparison. -/
theorem openBoundaryTensorComparison_tensor {Z C : Scheme.{u}} (z : Z ⟶ C)
    (U : C.Opens) (T M : C.Modules) :
    (Modules.pullback (z ∣_ U)).map (tensorRestrictionIso U.ι T M).inv ≫
      pullbackTensorMap (z ∣_ U) ((Modules.restrictFunctor U.ι).obj T)
        ((Modules.restrictFunctor U.ι).obj M) ≫
      tensorSheafMap (z ⁻¹ᵁ U).toScheme ((localPullbackIso z U).inv.app T)
        ((localPullbackIso z U).inv.app M) ≫
      (tensorRestrictionIso (z ⁻¹ᵁ U).ι ((Modules.pullback z).obj T)
        ((Modules.pullback z).obj M)).hom = openBoundaryTensorComparison z U T M := by
  have h := pullbackTensorMap_restrict z U T M
  change (Modules.pullback (z ∣_ U)).map (tensorRestrictionIso U.ι T M).hom ≫
    openBoundaryTensorComparison z U T M = _ at h
  dsimp only [restrictTensorMap] at h
  erw [← h, ← Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- Both original boundary equations imply the literal relation of the open section maps. -/
theorem open_prescribed_pair {Z C : Scheme.{u}} (z : Z ⟶ C) [IsClosedImmersion z]
    (U : C.Opens) (T M : C.Modules)
    (E : (Modules.pullback z).obj M ≅ SheafOfModules.unit Z.ringCatSheaf)
    (a : Γ(tensorSheaf C T M, U))
    (b : Γ(tensorSheaf C T (SheafOfModules.unit C.ringCatSheaf), U))
    (σ : Γ(tensorSheaf Z ((Modules.pullback z).obj T)
      ((Modules.pullback z).obj (SheafOfModules.unit C.ringCatSheaf)), z ⁻¹ᵁ U))
    (ha : (boundaryRestriction z T M).app U a =
      Modules.Hom.app (tensorSheafMap Z (𝟙 ((Modules.pullback z).obj T))
        ((pullbackUnitIso z).hom ≫ E.inv)) (z ⁻¹ᵁ U) σ)
    (hb : (boundaryRestriction z T (SheafOfModules.unit C.ringCatSheaf)).app U b = σ) :
    pullbackSectionMap (z ∣_ U) (openSectionHom C U (tensorSheaf C T M) a) ≫
        openBoundaryTensorComparison z U T M =
      pullbackSectionMap (z ∣_ U)
          (openSectionHom C U (tensorSheaf C T (SheafOfModules.unit C.ringCatSheaf)) b) ≫
        openBoundaryTensorComparison z U T (SheafOfModules.unit C.ringCatSheaf) ≫
        (Modules.restrictFunctor (z ⁻¹ᵁ U).ι).map
          (tensorSheafMap Z (𝟙 ((Modules.pullback z).obj T))
            ((pullbackUnitIso z).hom ≫ E.inv)) := by
  have h₁ := pullback_openSection_of_boundary_value z T M U a _ ha
  have h₂ := pullback_openSection_of_boundary_value z T
    (SheafOfModules.unit C.ringCatSheaf) U b σ hb
  change pullbackSectionMap (z ∣_ U) (openSectionHom C U (tensorSheaf C T M) a) ≫
    openBoundaryTensorComparison z U T M = _ at h₁
  change pullbackSectionMap (z ∣_ U)
    (openSectionHom C U (tensorSheaf C T (SheafOfModules.unit C.ringCatSheaf)) b) ≫
      openBoundaryTensorComparison z U T (SheafOfModules.unit C.ringCatSheaf) = _ at h₂
  rw [← Category.assoc, h₂, h₁]
  exact (openSectionHom_naturality Z (z ⁻¹ᵁ U) _ σ).symm

end AlgebraicGeometry.Scheme.CoherentGraph
