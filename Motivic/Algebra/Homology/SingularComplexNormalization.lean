/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.SingularComplex
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Normalization of ordinary singular complexes

For a presheaf with values in an abelian category, its normalized Moore complex
maps naturally to its alternating-face singular complex. Mathlib's constructive
Dold–Kan normalization gives `normalizationHomotopyEquiv`, with the actual
Moore inclusion as its forward map. In particular this inclusion is a
quasi-isomorphism in every degree.

This is normalization for the ordinary presheaf singular construction. It does
not supply finite correspondences, transfers, or a sheafified motivic complex.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor AlgebraicTopology

namespace Motivic.SingularComplex

universe v u v' u'

variable {C : Type u} [Category.{v} C]
variable {A : Type u'} [Category.{v'} A] [Abelian A]

/-- The normalized singular-chain construction as a functor of presheaves. -/
noncomputable def normalizedFunctor (Δ : CosimplicialObject C) : (Cᵒᵖ ⥤ A) ⥤ ChainComplex A ℕ :=
  (whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ A).obj Δ.op ⋙ normalizedMooreComplex A

/-- The normalized Moore singular complex of a presheaf. -/
noncomputable def normalizedObj (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) : ChainComplex A ℕ :=
  (normalizedFunctor Δ).obj P

/-- The natural inclusion from normalized singular chains to all singular chains. -/
noncomputable def normalizedInclusion (Δ : CosimplicialObject C) :
    normalizedFunctor (A := A) Δ ⟶ functor Δ :=
  whiskerLeft ((whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ A).obj Δ.op)
    (inclusionOfMooreComplex A)

/-- The actual Moore inclusion is a homotopy equivalence in every degree. -/
noncomputable def normalizationHomotopyEquiv (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) :
    HomotopyEquiv (normalizedObj Δ P) (obj Δ P) :=
  DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
    (Y := simplicial Δ P)

@[simp]
theorem normalizationHomotopyEquiv_hom (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) :
    (normalizationHomotopyEquiv Δ P).hom = (normalizedInclusion Δ).app P :=
  rfl

/-- The specified normalization inclusion is a quasi-isomorphism. -/
instance normalizedInclusion_quasiIso (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) :
    QuasiIso ((normalizedInclusion Δ).app P) :=
  (normalizationHomotopyEquiv Δ P).quasiIso_hom

end Motivic.SingularComplex
