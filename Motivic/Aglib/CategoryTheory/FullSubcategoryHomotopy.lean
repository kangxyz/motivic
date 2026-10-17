/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.FullSubcategory
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Lifting actual homotopy equivalences to full subcategories

When the terms of two complexes satisfy an object property, their maps and
homotopies lift componentwise. No abelian-category structure on the full
subcategory is needed. We also record additivity of a retract of an additive
functor, using its explicit natural inclusion and retraction.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]

/-- A natural retract of an additive functor is additive. -/
theorem additive_of_retract {F G : C ⥤ D} [G.Additive]
    (i : F ⟶ G) (p : G ⟶ F) (h : i ≫ p = 𝟙 F) : F.Additive where
  map_add {X Y f g} := by
    have hi : i.app Y ≫ p.app Y = 𝟙 (F.obj Y) := congrArg (fun α => α.app Y) h
    have hf (f : X ⟶ Y) : F.map f = i.app X ≫ G.map f ≫ p.app Y := by
      rw [← i.naturality_assoc, hi, Category.comp_id]
    rw [hf (f + g), G.map_add, Preadditive.add_comp, Preadditive.comp_add, ← hf f, ← hf g]

end CategoryTheory.Functor

namespace HomologicalComplex

variable {ι V : Type*} [Category* V] [Preadditive V] {c : ComplexShape ι}
  (P : ObjectProperty V) {K L : HomologicalComplex V c}
  (hK : ∀ n, P (K.X n)) (hL : ∀ n, P (L.X n))

/-- A chain map lifts to the full subcategory whenever its two complexes do. -/
def liftHomObjectProperty (f : K ⟶ L) :
    K.liftObjectProperty P hK ⟶ L.liftObjectProperty P hL where
  f n := ObjectProperty.homMk (f.f n)
  comm' i j _ := ObjectProperty.hom_ext P (f.comm i j)

end HomologicalComplex

namespace Homotopy

variable {ι V : Type*} [Category* V] [Preadditive V] {c : ComplexShape ι}
  (P : ObjectProperty V) {K L : HomologicalComplex V c}
  (hK : ∀ n, P (K.X n)) (hL : ∀ n, P (L.X n)) {f g : K ⟶ L}

/-- Every homotopy lifts to the full subcategory, retaining its exact components. -/
def liftObjectProperty (h : Homotopy f g) :
    Homotopy (HomologicalComplex.liftHomObjectProperty P hK hL f)
      (HomologicalComplex.liftHomObjectProperty P hK hL g) where
  hom i j := ObjectProperty.homMk (h.hom i j)
  zero i j hij := ObjectProperty.hom_ext P (h.zero i j hij)
  comm i := ObjectProperty.hom_ext P (h.comm i)

end Homotopy

namespace HomotopyEquiv

variable {ι V : Type*} [Category* V] [Preadditive V] {c : ComplexShape ι}
  (P : ObjectProperty V) {K L : HomologicalComplex V c}
  (hK : ∀ n, P (K.X n)) (hL : ∀ n, P (L.X n))

/-- An actual homotopy equivalence lifts whenever its terms lie in the full subcategory. -/
def liftObjectProperty (e : HomotopyEquiv K L) :
    HomotopyEquiv (K.liftObjectProperty P hK) (L.liftObjectProperty P hL) where
  hom := HomologicalComplex.liftHomObjectProperty P hK hL e.hom
  inv := HomologicalComplex.liftHomObjectProperty P hL hK e.inv
  homotopyHomInvId := e.homotopyHomInvId.liftObjectProperty P hK hK
  homotopyInvHomId := e.homotopyInvHomId.liftObjectProperty P hL hL

end HomotopyEquiv

namespace HomotopyEquiv

open CategoryTheory.Limits

variable {ι ι' V : Type*} [Category* V] [Preadditive V] [HasZeroObject V]
  {c : ComplexShape ι} {c' : ComplexShape ι'} {K L : HomologicalComplex V c}

/-- Extend both maps and both homotopies along a faithful complex-shape embedding. -/
noncomputable def extend (h : HomotopyEquiv K L) (e : c.Embedding c') [e.IsRelIff] :
    HomotopyEquiv (K.extend e) (L.extend e) where
  hom := HomologicalComplex.extendMap h.hom e
  inv := HomologicalComplex.extendMap h.inv e
  homotopyHomInvId := by
    simpa only [HomologicalComplex.extendMap_comp, HomologicalComplex.extendMap_id] using
      h.homotopyHomInvId.extend e
  homotopyInvHomId := by
    simpa only [HomologicalComplex.extendMap_comp, HomologicalComplex.extendMap_id] using
      h.homotopyInvHomId.extend e

/-- Shift an actual cochain homotopy equivalence, with the standard homotopy signs. -/
def shift {K L : CochainComplex V ℤ} (h : HomotopyEquiv K L) (n : ℤ) :
    HomotopyEquiv (K⟦n⟧) (L⟦n⟧) where
  hom := h.hom⟦n⟧'
  inv := h.inv⟦n⟧'
  homotopyHomInvId := by
    rw [← (shiftFunctor (CochainComplex V ℤ) n).map_comp,
      ← (shiftFunctor (CochainComplex V ℤ) n).map_id]
    exact h.homotopyHomInvId.shift n
  homotopyInvHomId := by
    rw [← (shiftFunctor (CochainComplex V ℤ) n).map_comp,
      ← (shiftFunctor (CochainComplex V ℤ) n).map_id]
    exact h.homotopyInvHomId.shift n

end HomotopyEquiv
