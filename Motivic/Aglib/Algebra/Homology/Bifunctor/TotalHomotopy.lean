/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# Homotopy equivalences on genuine exterior total complexes

An additive bifunctor sends two homotopy equivalences to a homotopy equivalence
of its actual signed total complexes. The proof uses the two explicit homotopies
from `BifunctorHomotopy`, rather than assuming a totalization exactness criterion.
For a projective target, the forward map of a resolution's comparison with the
single complex is its literal augmentation. These are the homotopical inputs
for the field-specific exterior-resolution construction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HomologicalComplex

section Bifunctor

variable {C₁ C₂ D I₁ I₂ J : Type*}
  [Category* C₁] [Category* C₂] [Category* D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X₁, (F.obj X₁).Additive]
  (c : ComplexShape J) [DecidableEq J] [TotalComplexShape c₁ c₂ c]

/-- The identity maps induce the identity on the signed total complex. -/
@[simp]
theorem exteriorTotalMap_id
    (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂)
    [HasMapBifunctor K₁ K₂ F c] :
    mapBifunctorMap (𝟙 K₁) (𝟙 K₂) F c = 𝟙 (mapBifunctor K₁ K₂ F c) := by
  ext j i₁ i₂ h
  simp

/-- Componentwise composition agrees with composition of maps of total complexes. -/
theorem exteriorTotalMap_comp
    {K₁ L₁ M₁ : HomologicalComplex C₁ c₁}
    {K₂ L₂ M₂ : HomologicalComplex C₂ c₂}
    (f₁ : K₁ ⟶ L₁) (g₁ : L₁ ⟶ M₁) (f₂ : K₂ ⟶ L₂) (g₂ : L₂ ⟶ M₂)
    [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c]
    [HasMapBifunctor M₁ M₂ F c] :
    mapBifunctorMap (f₁ ≫ g₁) (f₂ ≫ g₂) F c =
      mapBifunctorMap f₁ f₂ F c ≫ mapBifunctorMap g₁ g₂ F c := by
  ext j i₁ i₂ h
  simp only [HomologicalComplex.comp_f, ι_mapBifunctorMap, Category.assoc,
    ι_mapBifunctorMap_assoc, Functor.map_comp, NatTrans.comp_app]
  rw [NatTrans.naturality_assoc]

/-- A pair of homotopy equivalences induces a homotopy equivalence of the actual
signed total complexes, with forward map the tensor of the original maps. -/
noncomputable def exteriorTotalHomotopyEquiv
    {K₁ L₁ : HomologicalComplex C₁ c₁}
    {K₂ L₂ : HomologicalComplex C₂ c₂}
    (e₁ : HomotopyEquiv K₁ L₁) (e₂ : HomotopyEquiv K₂ L₂)
    [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c] :
    HomotopyEquiv (mapBifunctor K₁ K₂ F c) (mapBifunctor L₁ L₂ F c) where
  hom := mapBifunctorMap e₁.hom e₂.hom F c
  inv := mapBifunctorMap e₁.inv e₂.inv F c
  homotopyHomInvId := by
    simpa only [exteriorTotalMap_comp, exteriorTotalMap_id] using
      (mapBifunctorMapHomotopy₁ e₁.homotopyHomInvId (e₂.hom ≫ e₂.inv) F c).trans
        (mapBifunctorMapHomotopy₂ (𝟙 K₁) e₂.homotopyHomInvId F c)
  homotopyInvHomId := by
    simpa only [exteriorTotalMap_comp, exteriorTotalMap_id] using
      (mapBifunctorMapHomotopy₁ e₁.homotopyInvHomId (e₂.inv ≫ e₂.hom) F c).trans
        (mapBifunctorMapHomotopy₂ (𝟙 L₁) e₂.homotopyInvHomId F c)

/-- The forward map of the total homotopy equivalence is definitionally the
map induced by the two forward maps. -/
@[simp]
theorem exteriorTotalHomotopyEquiv_hom
    {K₁ L₁ : HomologicalComplex C₁ c₁}
    {K₂ L₂ : HomologicalComplex C₂ c₂}
    (e₁ : HomotopyEquiv K₁ L₁) (e₂ : HomotopyEquiv K₂ L₂)
    [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c] :
    (exteriorTotalHomotopyEquiv F c e₁ e₂).hom =
      mapBifunctorMap e₁.hom e₂.hom F c := rfl

end Bifunctor

section Augmentation

variable {C : Type*} [Category* C] [Abelian C]
  {M : C} [Projective M] (P : ProjectiveResolution M)

/-- A resolution of a projective object is homotopy equivalent to that object
in degree zero, with the given augmentation as its forward map. -/
noncomputable def augmentationHomotopyEquiv :
    HomotopyEquiv P.complex ((ChainComplex.single₀ C).obj M) := by
  let e := P.homotopyEquiv (ProjectiveResolution.self M)
  have h : e.hom = P.π := by
    have h := P.homotopyEquiv_hom_π (ProjectiveResolution.self M)
    change e.hom ≫ 𝟙 _ = P.π at h
    simpa only [Category.comp_id] using h
  exact e.copy (Homotopy.ofEq h)

/-- The comparison just constructed uses the literal resolution augmentation. -/
@[simp]
theorem augmentationHomotopyEquiv_hom : (augmentationHomotopyEquiv P).hom = P.π := rfl

end Augmentation

end HomologicalComplex
