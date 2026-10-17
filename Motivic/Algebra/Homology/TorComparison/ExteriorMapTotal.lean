/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Additive functors and actual signed total complexes

The canonical coproduct comparison of an additive functor commutes with both
signed total differentials. If the functor preserves the diagonal coproducts,
it is an isomorphism of complexes. This is a comparison of actual constructions;
no exactness or quasi-isomorphism of a total complex is assumed.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂

namespace Motivic.TorComparison

variable {C D I₁ I₂ J : Type*} [Category* C] [Category* D]
  [Preadditive C] [Preadditive D]
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (F : C ⥤ D) [F.Additive]
  (K : HomologicalComplex₂ C c₁ c₂)
  (c : ComplexShape J) [DecidableEq J] [TotalComplexShape c₁ c₂ c]

/-- Applying a functor to both levels of a bicomplex. -/
abbrev exteriorMapBicomplex : HomologicalComplex₂ D c₁ c₂ :=
  ((F.mapHomologicalComplex c₂).mapHomologicalComplex c₁).obj K

variable [(exteriorMapBicomplex F K).HasTotal c]

/-- The diagonal coproduct of mapped summands exists whenever the mapped total does. -/
instance exteriorMapTotal_hasCoproduct (j : J) :
    HasCoproduct (fun b => F.obj
      (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) j b)) := by
  have h : (exteriorMapBicomplex F K).HasTotal c := inferInstance
  exact h j

variable [K.HasTotal c]

/-- The actual coproduct comparison in one degree of a total complex. -/
noncomputable def exteriorTotalComparisonComponent (j : J) :
    ((exteriorMapBicomplex F K).total c).X j ⟶ F.obj ((K.total c).X j) :=
  sigmaComparison F (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) j)

/-- The comparison takes each summand inclusion to its image under the functor. -/
@[reassoc (attr := simp)]
theorem exteriorTotalComparisonComponent_ι (i₁ : I₁) (i₂ : I₂) (j : J)
    (h : ComplexShape.π c₁ c₂ c (i₁, i₂) = j) :
    (exteriorMapBicomplex F K).ιTotal c i₁ i₂ j h ≫
      exteriorTotalComparisonComponent F K c j = F.map (K.ιTotal c i₁ i₂ j h) :=
  ι_comp_sigmaComparison F
    (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) j) ⟨(i₁, i₂), h⟩

/-- The comparison also respects the zero extension of summand inclusions. -/
@[reassoc (attr := simp)]
theorem exteriorTotalComparisonComponent_ιOrZero (i₁ : I₁) (i₂ : I₂) (j : J) :
    (exteriorMapBicomplex F K).ιTotalOrZero c i₁ i₂ j ≫
      exteriorTotalComparisonComponent F K c j = F.map (K.ιTotalOrZero c i₁ i₂ j) := by
  by_cases h : ComplexShape.π c₁ c₂ c (i₁, i₂) = j
  · rw [ιTotalOrZero_eq _ _ _ _ _ h, ιTotalOrZero_eq _ _ _ _ _ h]
    exact exteriorTotalComparisonComponent_ι F K c i₁ i₂ j h
  · rw [ιTotalOrZero_eq_zero _ _ _ _ _ h, ιTotalOrZero_eq_zero _ _ _ _ _ h,
      zero_comp, F.map_zero]

/-- The comparison respects the signed horizontal differential on each summand. -/
@[reassoc]
theorem exteriorTotalComparisonComponent_d₁ (i₁ : I₁) (i₂ : I₂) (j : J) :
    (exteriorMapBicomplex F K).d₁ c i₁ i₂ j ≫ exteriorTotalComparisonComponent F K c j =
      F.map (K.d₁ c i₁ i₂ j) := by
  by_cases h : c₁.Rel i₁ (c₁.next i₁)
  · rw [d₁_eq' _ _ h, d₁_eq' _ _ h, Linear.units_smul_comp,
      Category.assoc, exteriorTotalComparisonComponent_ιOrZero,
      Functor.map_units_smul, Functor.map_comp]
    rfl
  · rw [d₁_eq_zero _ _ _ _ _ h, d₁_eq_zero _ _ _ _ _ h, zero_comp, F.map_zero]

/-- The comparison respects the signed vertical differential on each summand. -/
@[reassoc]
theorem exteriorTotalComparisonComponent_d₂ (i₁ : I₁) (i₂ : I₂) (j : J) :
    (exteriorMapBicomplex F K).d₂ c i₁ i₂ j ≫ exteriorTotalComparisonComponent F K c j =
      F.map (K.d₂ c i₁ i₂ j) := by
  by_cases h : c₂.Rel i₂ (c₂.next i₂)
  · rw [d₂_eq' _ _ _ h, d₂_eq' _ _ _ h, Linear.units_smul_comp,
      Category.assoc, exteriorTotalComparisonComponent_ιOrZero,
      Functor.map_units_smul, Functor.map_comp]
    rfl
  · rw [d₂_eq_zero _ _ _ _ _ h, d₂_eq_zero _ _ _ _ _ h, zero_comp, F.map_zero]

/-- The canonical coproduct comparisons form a chain map on signed total complexes. -/
noncomputable def exteriorTotalComparison :
    (exteriorMapBicomplex F K).total c ⟶ (F.mapHomologicalComplex c).obj (K.total c) where
  f := exteriorTotalComparisonComponent F K c
  comm' j j' _ := by
    apply HomologicalComplex₂.total.hom_ext
    intro i₁ i₂ h
    change (exteriorMapBicomplex F K).ιTotal c i₁ i₂ j h ≫
        (exteriorTotalComparisonComponent F K c j ≫ F.map ((K.total c).d j j')) =
      (exteriorMapBicomplex F K).ιTotal c i₁ i₂ j h ≫
        (((exteriorMapBicomplex F K).total c).d j j' ≫
          exteriorTotalComparisonComponent F K c j')
    rw [exteriorTotalComparisonComponent_ι_assoc, ← F.map_comp,
      total_d, Preadditive.comp_add, ι_D₁, ι_D₂, F.map_add,
      total_d, Preadditive.add_comp, Preadditive.comp_add,
      ι_D₁_assoc, ι_D₂_assoc, exteriorTotalComparisonComponent_d₁,
      exteriorTotalComparisonComponent_d₂]

/-- The total comparison is natural in the actual bicomplex map. -/
@[reassoc]
theorem exteriorTotalComparison_naturality
    {L : HomologicalComplex₂ C c₁ c₂}
    [L.HasTotal c] [(exteriorMapBicomplex F L).HasTotal c] (φ : K ⟶ L) :
    HomologicalComplex₂.total.map
        (((F.mapHomologicalComplex c₂).mapHomologicalComplex c₁).map φ) c ≫
      exteriorTotalComparison F L c =
    exteriorTotalComparison F K c ≫
      (F.mapHomologicalComplex c).map (HomologicalComplex₂.total.map φ c) := by
  ext j i₁ i₂ h
  simp only [HomologicalComplex.comp_f, HomologicalComplex₂.ιTotal_map_assoc]
  change F.map ((φ.f i₁).f i₂) ≫
      (exteriorMapBicomplex F L).ιTotal c i₁ i₂ j h ≫
        exteriorTotalComparisonComponent F L c j =
    (exteriorMapBicomplex F K).ιTotal c i₁ i₂ j h ≫
      exteriorTotalComparisonComponent F K c j ≫ F.map ((HomologicalComplex₂.total.map φ c).f j)
  rw [exteriorTotalComparisonComponent_ι_assoc, exteriorTotalComparisonComponent_ι,
    ← F.map_comp, ← F.map_comp,
    HomologicalComplex₂.ιTotal_map]

variable [∀ j, PreservesColimit
  (Discrete.functor (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) j)) F]

/-- Preserving the diagonal coproducts makes the total-complex comparison an isomorphism. -/
noncomputable def exteriorMapTotalIso :
    (exteriorMapBicomplex F K).total c ≅ (F.mapHomologicalComplex c).obj (K.total c) := by
  haveI (j : J) : IsIso ((exteriorTotalComparison F K c).f j) :=
    inferInstanceAs (IsIso (sigmaComparison F
      (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) j)))
  haveI : IsIso (exteriorTotalComparison F K c) := HomologicalComplex.Hom.isIso_of_components _
  exact asIso (exteriorTotalComparison F K c)

/-- The isomorphism uses the already constructed canonical chain comparison. -/
@[simp]
theorem exteriorMapTotalIso_hom :
    (exteriorMapTotalIso F K c).hom = exteriorTotalComparison F K c := rfl

end Motivic.TorComparison
