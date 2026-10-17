/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.Sheafification
public import Motivic.Algebra.Homology.SingularComplexPresheaf
public import Motivic.Cohomology.Motivic.Indexing
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
# Canonically sheafified ordinary singular complexes

For an ordinary presheaf `P`, the actual complex `sheafObj J Δ P` sheafifies
`U ↦ P(U × Δⁿ)` in every chain degree. Its unit comes from ordinary
sheafification, and the construction is functorial in `P`.

`sheafCochainObj J Δ P q` first places singular chain degree `r` in cochain
degree `q-r`, extends by zero above `q`, and then applies canonical
sheafification. We give the literal term and differential dictionary and an
all-degree homology isomorphism with sheafified singular presheaf homology.
The placement preserves the alternating differential, without asserting an
identification with a signed shift functor.

This module neither adds transfers to `P` nor constructs the reduced transfer
torus. Consequently these complexes are not named `Z(q)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open scoped Simplicial

namespace Motivic.SingularComplex

universe v u v' u'

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
variable {A : Type u'} [Category.{v'} A] [Abelian A]
variable (J : GrothendieckTopology C) [HasSheafify J A]

/-- Canonical sheafification of the ordinary presheaf singular-chain construction. -/
def sheafFunctor (Δ : CosimplicialObject C) :
    (Cᵒᵖ ⥤ A) ⥤ ChainComplex (Sheaf J A) ℕ :=
  presheafConstruction Δ ⋙ Sheafification.functor J (ComplexShape.down ℕ)

/-- The actual sheaf complex with terms `a_J(U ↦ P(U × Δⁿ))`. -/
abbrev sheafObj (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) :
    ChainComplex (Sheaf J A) ℕ :=
  (sheafFunctor J Δ).obj P

@[simp]
theorem sheafObj_X (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    (sheafObj J Δ P).X n = (presheafToSheaf J A).obj ((presheafObj Δ P).X n) := rfl

@[simp]
theorem sheafObj_d (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) (i j : ℕ) :
    (sheafObj J Δ P).d i j = (presheafToSheaf J A).map ((presheafObj Δ P).d i j) := rfl

/-- The singular sheafification unit, natural in the original ordinary presheaf. -/
def sheafUnit (Δ : CosimplicialObject C) : presheafConstruction (A := A) Δ ⟶
    sheafFunctor J Δ ⋙ Sheafification.underlyingFunctor J (ComplexShape.down ℕ) :=
  whiskerLeft (presheafConstruction Δ) (Sheafification.unit J (ComplexShape.down ℕ))

@[simp]
theorem sheafUnit_app_f (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    ((sheafUnit J Δ).app P).f n = toSheafify J ((presheafObj Δ P).X n) := rfl

/-- Homology of sheafified singular chains is sheafified presheaf homology. -/
def sheafHomologyIso (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    (sheafObj J Δ P).homology n ≅
      (presheafToSheaf J A).obj ((presheafObj Δ P).homology n) :=
  Sheafification.homologyIso J (presheafObj Δ P) n

/-- The ordinary singular presheaf complex placed in cochain degrees `q-r`. -/
def presheafCochainFunctor (Δ : CosimplicialObject C) (q : ℕ) :
    (Cᵒᵖ ⥤ A) ⥤ CochainComplex (Cᵒᵖ ⥤ A) ℤ :=
  presheafConstruction Δ ⋙ (ComplexShape.embeddingUpIntLE (q : ℤ)).extendFunctor _

/-- The placed ordinary presheaf complex, before sheafification. -/
abbrev presheafCochainObj (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) (q : ℕ) :
    CochainComplex (Cᵒᵖ ⥤ A) ℤ :=
  (presheafCochainFunctor Δ q).obj P

/-- Sheafification of the all-degree, weight-placed ordinary singular presheaf complex. -/
def sheafCochainFunctor (Δ : CosimplicialObject C) (q : ℕ) :
    (Cᵒᵖ ⥤ A) ⥤ CochainComplex (Sheaf J A) ℤ :=
  presheafCochainFunctor Δ q ⋙ Sheafification.functor J (ComplexShape.up ℤ)

/-- The canonically sheafified ordinary singular cochain complex. -/
abbrev sheafCochainObj (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) (q : ℕ) :
    CochainComplex (Sheaf J A) ℤ :=
  (sheafCochainFunctor J Δ q).obj P

/-- The canonical term isomorphism for the sheafified placement `q-r`. -/
def sheafCochainXIso (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) (q r : ℕ) :
    (sheafCochainObj J Δ P q).X (Indexing.singularDegree q r) ≅
      (presheafToSheaf J A).obj ((presheafObj Δ P).X r) :=
  (presheafToSheaf J A).mapIso
    ((presheafObj Δ P).extendXIso (ComplexShape.embeddingUpIntLE (q : ℤ)) rfl)

/-- The sheaf complex is zero above its stated weight. -/
theorem isZero_sheafCochainObj_X (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A)
    (q : ℕ) (i : ℤ) (hi : (q : ℤ) < i) :
    IsZero ((sheafCochainObj J Δ P q).X i) := by
  apply (presheafToSheaf J A).map_isZero
  apply (presheafObj Δ P).isZero_extend_X
  exact (ComplexShape.notMem_range_embeddingUpIntLE_iff (q : ℤ) i).2 hi

/-- The placed differential is exactly the sheafified alternating presheaf differential. -/
theorem sheafCochainObj_d (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) (q r : ℕ) :
    (sheafCochainObj J Δ P q).d (Indexing.singularDegree q (r + 1))
        (Indexing.singularDegree q r) =
      (sheafCochainXIso J Δ P q (r + 1)).hom ≫
        (presheafToSheaf J A).map ((presheafObj Δ P).d (r + 1) r) ≫
        (sheafCochainXIso J Δ P q r).inv := by
  change (presheafToSheaf J A).map
      (((presheafObj Δ P).extend (ComplexShape.embeddingUpIntLE (q : ℤ))).d
        (Indexing.singularDegree q (r + 1)) (Indexing.singularDegree q r)) =
    (presheafToSheaf J A).map
        ((presheafObj Δ P).extendXIso (ComplexShape.embeddingUpIntLE (q : ℤ))
          (i := r + 1) (i' := Indexing.singularDegree q (r + 1)) rfl).hom ≫
      (presheafToSheaf J A).map ((presheafObj Δ P).d (r + 1) r) ≫
        (presheafToSheaf J A).map
          ((presheafObj Δ P).extendXIso (ComplexShape.embeddingUpIntLE (q : ℤ))
            (i := r) (i' := Indexing.singularDegree q r) rfl).inv
  simpa only [Functor.map_comp] using
    congrArg (fun f => (presheafToSheaf J A).map f)
      ((presheafObj Δ P).extend_d_eq (ComplexShape.embeddingUpIntLE (q : ℤ))
        (i := r + 1) (j := r) (i' := Indexing.singularDegree q (r + 1))
        (j' := Indexing.singularDegree q r) rfl rfl)

/-- Canonical comparison of placed sheaf homology and ordinary singular presheaf homology. -/
def sheafCochainHomologyIso (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) (q r : ℕ) :
    (sheafCochainObj J Δ P q).homology (Indexing.singularDegree q r) ≅
      (presheafToSheaf J A).obj ((presheafObj Δ P).homology r) :=
  Sheafification.homologyIso J (presheafCochainObj Δ P q) (Indexing.singularDegree q r) ≪≫
    (presheafToSheaf J A).mapIso
      ((presheafObj Δ P).extendHomologyIso (ComplexShape.embeddingUpIntLE (q : ℤ)) rfl)

/-- The canonical cochain-level unit, natural in the ordinary presheaf. -/
def sheafCochainUnit (Δ : CosimplicialObject C) (q : ℕ) :
    presheafCochainFunctor (A := A) Δ q ⟶
      sheafCochainFunctor J Δ q ⋙ Sheafification.underlyingFunctor J (ComplexShape.up ℤ) :=
  whiskerLeft (presheafCochainFunctor Δ q) (Sheafification.unit J (ComplexShape.up ℤ))

/-- A presheaf morphism gives an actual map of canonically sheafified cochain complexes. -/
abbrev sheafCochainMap (Δ : CosimplicialObject C) {P Q : Cᵒᵖ ⥤ A}
    (α : P ⟶ Q) (q : ℕ) : sheafCochainObj J Δ P q ⟶ sheafCochainObj J Δ Q q :=
  (sheafCochainFunctor J Δ q).map α

theorem sheafCochainMap_id (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) (q : ℕ) :
    sheafCochainMap J Δ (𝟙 P) q = 𝟙 (sheafCochainObj J Δ P q) :=
  (sheafCochainFunctor J Δ q).map_id P

theorem sheafCochainMap_comp (Δ : CosimplicialObject C) {P Q R : Cᵒᵖ ⥤ A}
    (α : P ⟶ Q) (β : Q ⟶ R) (q : ℕ) :
    sheafCochainMap J Δ (α ≫ β) q =
      sheafCochainMap J Δ α q ≫ sheafCochainMap J Δ β q :=
  (sheafCochainFunctor J Δ q).map_comp α β

/-- The low-degree weight-two term in degree one is the sheafified singular chain-one term. -/
def sheafWeightTwoXOneIso (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) :
    (sheafCochainObj J Δ P 2).X 1 ≅
      (presheafToSheaf J A).obj ((presheafObj Δ P).X 1) :=
  sheafCochainXIso J Δ P 2 1

/-- The low-degree weight-two term in degree two is the sheafified singular chain-zero term. -/
def sheafWeightTwoXTwoIso (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) :
    (sheafCochainObj J Δ P 2).X 2 ≅
      (presheafToSheaf J A).obj ((presheafObj Δ P).X 0) :=
  sheafCochainXIso J Δ P 2 0

end Motivic.SingularComplex
