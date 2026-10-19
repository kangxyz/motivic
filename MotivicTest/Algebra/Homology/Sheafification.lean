/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Motivic.Aglib.Algebra.Homology.Sheafification.Basic
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
    ((Sheafification.unit J c).app K).f i = toSheafify J (K.X i) := rfl

example (i : ι) :
    (Sheafification.obj J K).homology i ≅
      (presheafToSheaf J AddCommGrpCat).obj (K.homology i) :=
  Sheafification.homologyIso J K i

example (f : K ⟶ L) (i : ι) :
    HomologicalComplex.homologyMap (Sheafification.map J f) i ≫
        (Sheafification.homologyIso J L i).hom =
      (Sheafification.homologyIso J K i).hom ≫
        (presheafToSheaf J AddCommGrpCat).map (HomologicalComplex.homologyMap f i) :=
  Sheafification.homologyIso_hom_naturality J f i

example (f : K ⟶ L) [QuasiIso f] : QuasiIso (Sheafification.map J f) := inferInstance

example (F : HomologicalComplex (Sheaf J AddCommGrpCat.{w}) c) :
    (Sheafification.obj J K ⟶ F) ≃
      (K ⟶ (Sheafification.underlyingFunctor J c).obj F) :=
  (Sheafification.adjunction J c).homEquiv K F

example : (Sheafification.obj (⊥ : GrothendieckTopology C) K).X =
    fun i => (presheafToSheaf (⊥ : GrothendieckTopology C) AddCommGrpCat).obj (K.X i) := rfl

set_option linter.hashCommand false in
#print axioms Sheafification.adjunction
set_option linter.hashCommand false in
#print axioms Sheafification.homologyIso
set_option linter.hashCommand false in
#print axioms Sheafification.homologyFunctorIso
set_option linter.hashCommand false in
#print axioms Sheafification.map_quasiIso
