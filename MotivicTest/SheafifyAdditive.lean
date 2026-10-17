/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.CategoryTheory.SheafifyAdditive
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Lean.Util.CollectAxioms

/-!
# Consumers of source-arrow additivity after ordinary sheafification

The generic test uses objects in `Type (u + 1)` and coefficients in
`AddCommGrpCat.{u + 1}`. It derives signed source-arrow laws for actual sections
of Mathlib's ordinary sheafification. The bottom-topology tests discharge the
principal-covering-basis and forgetful-functor assumptions, rather than assuming
additivity of the sheafified object.
-/

@[expose] public section

open CategoryTheory Opposite

universe u v

namespace MotivicTest.SheafifyAdditive

section LargeSource

variable {C : Type (u + 1)} [Category.{u} C] [Preadditive C]
  (J : GrothendieckTopology C)
  (hJ : ∀ (X : C) (S : Sieve X), S ∈ J X →
    ∃ (Y : C) (q : Y ⟶ X), S q ∧ Sieve.generate (Presieve.singleton q) ∈ J X)
  [HasWeakSheafify J AddCommGrpCat.{u + 1}]
  [J.HasSheafCompose (forget AddCommGrpCat.{u + 1})]
  [J.PreservesSheafification (forget AddCommGrpCat.{u + 1})]
  (F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) [F.Additive]

include hJ

/-- Signed combinations are combinations of source arrows, tested on sections. -/
theorem signedSourceAction {X Y : C} (α β : X ⟶ Y)
    (s : (sheafify J F).obj (op Y)) :
    (sheafify J F).map (((-3 : ℤ) • (α - β)).op) s =
      (-3 : ℤ) • ((sheafify J F).map α.op s - (sheafify J F).map β.op s) := by
  let := sheafify_additive_of_principal_covering_basis J hJ F
  simp only [op_zsmul, op_sub, Functor.map_zsmul, Functor.map_sub]
  rfl

/-- The zero correspondence acts by the actual zero map on sheafified sections. -/
theorem zeroSourceAction {X Y : C} (s : (sheafify J F).obj (op Y)) :
    (sheafify J F).map (0 : X ⟶ Y).op s = 0 := by
  let := sheafify_additive_of_principal_covering_basis J hJ F
  simp

end LargeSource

section BottomTopology

variable {C : Type u} [Category.{v} C]

/-- The trivial Grothendieck topology has the required basis, witnessed by identities. -/
theorem botPrincipalCoveringBasis (X : C) (S : Sieve X)
    (hS : S ∈ (⊥ : GrothendieckTopology C) X) :
    ∃ (Y : C) (q : Y ⟶ X), S q ∧
      Sieve.generate (Presieve.singleton q) ∈ (⊥ : GrothendieckTopology C) X := by
  obtain rfl := GrothendieckTopology.bot_covering.mp hS
  refine ⟨X, 𝟙 X, trivial, ?_⟩
  simp only [Sieve.generate_of_singleton_isSplitEpi, GrothendieckTopology.top_mem]

variable [Preadditive C]

/-- An unconditional consumer on an actual topology; all sheafification and
forgetful-functor instances are synthesized, with no assumed target additivity. -/
theorem botSheafifyAdditive (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) [F.Additive] :
    (sheafify (⊥ : GrothendieckTopology C) F).Additive :=
  sheafify_additive_of_principal_covering_basis _ botPrincipalCoveringBasis F

/-- The ordinary sheafification unit intertwines signed source actions. -/
theorem botSheafifyUnitSigned (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) [F.Additive]
    {X Y : C} (α β : X ⟶ Y) (t : F.obj (op Y)) :
    (sheafify (⊥ : GrothendieckTopology C) F).map α.op
        ((toSheafify (⊥ : GrothendieckTopology C) F).app _ t) -
      (sheafify (⊥ : GrothendieckTopology C) F).map β.op
        ((toSheafify (⊥ : GrothendieckTopology C) F).app _ t) =
      (toSheafify (⊥ : GrothendieckTopology C) F).app _ (F.map (α - β).op t) := by
  rw [op_sub, F.map_sub]
  change _ = (toSheafify (⊥ : GrothendieckTopology C) F).app _
    (F.map α.op t - F.map β.op t)
  rw [map_sub, NatTrans.naturality_apply, NatTrans.naturality_apply]

end BottomTopology

section Representable

variable {C : Type u} [Category.{max u v} C] [Preadditive C]

/-- The actual additive representable is accepted without any assumption of
additivity on either the input or the sheafified output. -/
theorem botSheafifyRepresentableAdditive (Y : C) :
    (sheafify (⊥ : GrothendieckTopology C) (preadditiveYoneda.obj Y)).Additive :=
  botSheafifyAdditive _

/-- The action on the ordinary sheafification of an actual representable
respects differences of arrows. -/
theorem botSheafifyRepresentableSub (Z : C) {X Y : C} (α β : X ⟶ Y) :
    (sheafify (⊥ : GrothendieckTopology C) (preadditiveYoneda.obj Z)).map (α - β).op =
      (sheafify (⊥ : GrothendieckTopology C) (preadditiveYoneda.obj Z)).map α.op -
        (sheafify (⊥ : GrothendieckTopology C) (preadditiveYoneda.obj Z)).map β.op := by
  let := botSheafifyRepresentableAdditive Z
  rw [op_sub, Functor.map_sub]

end Representable

open Lean in
run_cmd do
  for name in #[``CategoryTheory.Presheaf.additive_of_isLocallySurjective_of_isSeparated,
      ``CategoryTheory.sheafify_additive_of_principal_covering_basis,
      ``signedSourceAction, ``zeroSourceAction, ``botSheafifyAdditive,
      ``botSheafifyUnitSigned, ``botSheafifyRepresentableAdditive,
      ``botSheafifyRepresentableSub] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Source-arrow additivity of ordinary sheafification uses only standard Lean foundations."

end MotivicTest.SheafifyAdditive
