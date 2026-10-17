/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.CategoryTheory.Adjunction.Additive

/-! # The actual additive adjunction on homotopy categories -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
universe v₁ v₂ u₁ u₂
namespace CategoryTheory.Adjunction
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D] {L : C ⥤ D} {R : D ⥤ C}
  [L.Additive] [R.Additive] (adj : L ⊣ R) {ι : Type*} (c : ComplexShape ι)

/-- The actual unit, applied degreewise then passed to homotopy classes. -/
def homotopyUnit : 𝟭 (HomotopyCategory C c) ⟶
    L.mapHomotopyCategory c ⋙ R.mapHomotopyCategory c where
  app K := (HomotopyCategory.quotient C c).map
    ((NatTrans.mapHomologicalComplex adj.unit c).app K.as)
  naturality := by
    rintro ⟨K⟩ ⟨K'⟩ ⟨f : K ⟶ K'⟩
    simp only [HomotopyCategory.quot_mk_eq_quotient_map, Functor.id_map,
      Functor.comp_map, Functor.mapHomotopyCategory_map, ← Functor.map_comp]
    congr 1
    exact (NatTrans.mapHomologicalComplex adj.unit c).naturality f

/-- The actual counit, applied degreewise then passed to homotopy classes. -/
def homotopyCounit : R.mapHomotopyCategory c ⋙ L.mapHomotopyCategory c ⟶
    𝟭 (HomotopyCategory D c) where
  app K := (HomotopyCategory.quotient D c).map
    ((NatTrans.mapHomologicalComplex adj.counit c).app K.as)
  naturality := by
    rintro ⟨K⟩ ⟨K'⟩ ⟨f : K ⟶ K'⟩
    simp only [HomotopyCategory.quot_mk_eq_quotient_map, Functor.id_map,
      Functor.comp_map, Functor.mapHomotopyCategory_map, ← Functor.map_comp]
    congr 1
    exact (NatTrans.mapHomologicalComplex adj.counit c).naturality f

/-- The homotopy adjunction has the original degreewise unit and counit. -/
def homotopyAdjunction : L.mapHomotopyCategory c ⊣ R.mapHomotopyCategory c :=
  Adjunction.mkOfUnitCounit
    { unit := adj.homotopyUnit c
      counit := adj.homotopyCounit c
      left_triangle := by
        ext K
        change (HomotopyCategory.quotient D c).map _ ≫
          (HomotopyCategory.quotient D c).map _ = 𝟙 _
        rw [← Functor.map_comp, ← Functor.map_id]
        congr 1
        ext i
        change L.map (adj.unit.app (K.as.X i)) ≫
          𝟙 _ ≫ adj.counit.app (L.obj (K.as.X i)) = 𝟙 _
        simpa only [Category.id_comp, Functor.id_obj] using adj.left_triangle_components (K.as.X i)
      right_triangle := by
        ext K
        change (HomotopyCategory.quotient C c).map _ ≫
          (HomotopyCategory.quotient C c).map _ = 𝟙 _
        rw [← Functor.map_comp, ← Functor.map_id]
        congr 1
        ext i
        change adj.unit.app (R.obj (K.as.X i)) ≫
          𝟙 _ ≫ R.map (adj.counit.app (K.as.X i)) = 𝟙 _
        simpa only [Category.id_comp, Functor.id_obj] using
          adj.right_triangle_components (K.as.X i) }

end CategoryTheory.Adjunction
