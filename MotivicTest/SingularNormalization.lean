/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Motivic.Aglib.Algebra.Homology.SingularComplex.Normalization
import Mathlib.Algebra.Category.Grp.Abelian

/-!
# Consumers of the actual singular normalization inclusion

The tests check that the specified inclusion induces an isomorphism on
homology in arbitrary degree and that it commutes with presheaf morphisms.
-/

noncomputable section

open CategoryTheory
open _root_.CategoryTheory.SingularComplex

universe v u w

variable {C : Type u} [Category.{v} C]
variable (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ AddCommGrpCat.{w})

example (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap ((normalizedInclusion Δ).app P) n) :=
  (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance

example {Q : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (α : P ⟶ Q) :
    (normalizedFunctor Δ).map α ≫ (normalizedInclusion Δ).app Q =
      (normalizedInclusion Δ).app P ≫ map Δ α :=
  (normalizedInclusion Δ).naturality α

example : Homotopy
    ((normalizationHomotopyEquiv Δ P).inv ≫ (normalizedInclusion Δ).app P)
    (𝟙 (obj Δ P)) :=
  (normalizationHomotopyEquiv Δ P).homotopyInvHomId
