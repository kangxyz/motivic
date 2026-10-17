/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology

/-! # Naturality of Hom-complex cohomology in both complexes -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
universe v u
namespace CochainComplex.HomComplex
variable {C : Type u} [Category.{v} C] [Preadditive C]
  {K K' L L' : CochainComplex C ℤ} (f : K' ⟶ K) (g : L ⟶ L')

/-- The genuine contravariant/covariant map of Hom complexes. -/
def map : HomComplex K L ⟶ HomComplex K' L' where
  f n := AddCommGrpCat.ofHom
    { toFun := fun α => ((Cochain.ofHom f).comp α (zero_add n)).comp
        (Cochain.ofHom g) (add_zero n)
      map_zero' := by simp
      map_add' := by intros; simp }
  comm' i j _ := by ext α; simp

/-- The induced map on cocycles, without choosing representatives of cohomology classes. -/
def cocycleMap (n : ℤ) : Cocycle K L n →+ Cocycle K' L' n where
  toFun α := (α.precomp f).postcomp g
  map_zero' := by ext; simp [Cocycle.precomp, Cocycle.postcomp]
  map_add' := by intros; ext; simp [Cocycle.precomp, Cocycle.postcomp]

/-- The cohomology-class map is characterized by composition in the actual homotopy category. -/
def classMap (n : ℤ) : CohomologyClass K L n →+ CohomologyClass K' L' n where
  toFun x := CohomologyClass.homAddEquiv.symm
    ((HomotopyCategory.quotient C _).map f ≫ CohomologyClass.toHom x ≫
      (HomotopyCategory.quotient C _).map (g⟦n⟧'))
  map_zero' := by simp
  map_add' := by intros; simp

@[simp]
theorem classMap_mk (n : ℤ) (z : Cocycle K L n) :
    classMap f g n (CohomologyClass.mk z) =
      CohomologyClass.mk ((z.precomp f).postcomp g) := by
  apply CohomologyClass.homAddEquiv.injective
  simp [classMap, CohomologyClass.homAddEquiv, CohomologyClass.toHom_mk,
    Cocycle.equivHomShift_symm_precomp, Cocycle.equivHomShift_symm_postcomp,
    Functor.map_comp]

/-- The quotient cocycle construction computes the genuine map on homology. -/
def mapLeftHomologyData (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor _ _ n).map (map f g))
      (leftHomologyData K L n) (leftHomologyData K' L' n) where
  φK := AddCommGrpCat.ofHom (cocycleMap f g n)
  φH := AddCommGrpCat.ofHom (classMap f g n)
  commi := by ext z; rfl
  commf' := by
    apply (cancel_mono (leftHomologyData K' L' n).i).1
    have hi : AddCommGrpCat.ofHom (cocycleMap f g n) ≫ (leftHomologyData K' L' n).i =
        (leftHomologyData K L n).i ≫ (map f g).f n := by ext z; rfl
    rw [Category.assoc, hi, ← Category.assoc, ShortComplex.LeftHomologyData.f'_i,
      Category.assoc, ShortComplex.LeftHomologyData.f'_i]
    exact ((HomologicalComplex.shortComplexFunctor _ _ n).map (map f g)).comm₁₂.symm
  commπ := by ext z; exact classMap_mk f g n z

/-- Hom-complex homology and cohomology classes have the same actual functorial maps. -/
theorem homologyAddEquiv_naturality (n : ℤ) (x : (HomComplex K L).homology n) :
    homologyAddEquiv K' L' n (HomologicalComplex.homologyMap (map f g) n x) =
      classMap f g n (homologyAddEquiv K L n x) :=
  ConcreteCategory.congr_hom (mapLeftHomologyData f g n).homologyMap_comm x

end CochainComplex.HomComplex
