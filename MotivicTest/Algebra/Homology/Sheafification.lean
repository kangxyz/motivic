/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Motivic.Algebra.Homology.Sheafification
import Mathlib.Algebra.Category.Grp.Abelian

/-!
# Consumers of canonical complex sheafification

These consumers check the actual chain-complex adjunction, its termwise unit,
its all-degree homology comparison, naturality, and quasi-isomorphism
preservation. The trivial topology test obtains sheafification from Mathlib,
without postulating an additional functor or comparison isomorphism.
-/

noncomputable section

open CategoryTheory

universe v u w t

variable {C : Type u} [Category.{v} C]
variable {ι : Type t} (c : ComplexShape ι)
variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{w}]
variable (K L : HomologicalComplex (Cᵒᵖ ⥤ AddCommGrpCat.{w}) c)

example (i : ι) :
    ((Motivic.Sheafification.unit J c).app K).f i = toSheafify J (K.X i) := rfl

example (i : ι) :
    (Motivic.Sheafification.obj J K).homology i ≅
      (presheafToSheaf J AddCommGrpCat).obj (K.homology i) :=
  Motivic.Sheafification.homologyIso J K i

example (f : K ⟶ L) (i : ι) :
    HomologicalComplex.homologyMap (Motivic.Sheafification.map J f) i ≫
        (Motivic.Sheafification.homologyIso J L i).hom =
      (Motivic.Sheafification.homologyIso J K i).hom ≫
        (presheafToSheaf J AddCommGrpCat).map (HomologicalComplex.homologyMap f i) :=
  Motivic.Sheafification.homologyIso_hom_naturality J f i

example (f : K ⟶ L) [QuasiIso f] : QuasiIso (Motivic.Sheafification.map J f) := inferInstance

example (F : HomologicalComplex (Sheaf J AddCommGrpCat.{w}) c) :
    (Motivic.Sheafification.obj J K ⟶ F) ≃
      (K ⟶ (Motivic.Sheafification.underlyingFunctor J c).obj F) :=
  (Motivic.Sheafification.adjunction J c).homEquiv K F

example : (Motivic.Sheafification.obj (⊥ : GrothendieckTopology C) K).X =
    fun i => (presheafToSheaf (⊥ : GrothendieckTopology C) AddCommGrpCat).obj (K.X i) := rfl

set_option linter.hashCommand false in
#print axioms Motivic.Sheafification.adjunction
set_option linter.hashCommand false in
#print axioms Motivic.Sheafification.homologyIso
set_option linter.hashCommand false in
#print axioms Motivic.Sheafification.homologyFunctorIso
set_option linter.hashCommand false in
#print axioms Motivic.Sheafification.map_quasiIso
