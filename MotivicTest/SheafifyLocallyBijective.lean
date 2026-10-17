/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.CategoryTheory.SheafifyLocallyBijective
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Lean.Util.CollectAxioms

/-!
# Consumers of comparison with ordinary sheafification

For abelian-group coefficients in the source-object universe, a locally
bijective map to a sheaf yields an actual comparison isomorphism. Both unit
identities are checked. The bottom-topology consumer synthesizes all
sheafification and forgetful-functor assumptions.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace MotivicTest.SheafifyLocallyBijective

section LargeSource

variable {C : Type (u + 1)} [Category.{u} C]
  (J : GrothendieckTopology C)
  [HasWeakSheafify J AddCommGrpCat.{u + 1}]
  [J.HasSheafCompose (forget AddCommGrpCat.{u + 1})]
  [J.PreservesSheafification (forget AddCommGrpCat.{u + 1})]
  {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
  (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
  [Presheaf.IsLocallyInjective J η] [Presheaf.IsLocallySurjective J η]

/-- A locally bijective presentation produces an actual isomorphism of presheaves. -/
noncomputable def comparisonIso : sheafify J P ≅ Q :=
  let := isIso_sheafifyLift_of_isLocallyBijective J η hQ
  asIso (sheafifyLift J η hQ)

/-- The comparison is the canonical lift of the original map. -/
theorem comparisonIso_unit :
    toSheafify J P ≫ (comparisonIso J η hQ).hom = η :=
  toSheafify_sheafifyLift J η hQ

/-- The inverse identifies the original map with the ordinary sheafification unit. -/
theorem comparisonIso_inverse_unit :
    η ≫ (comparisonIso J η hQ).inv = toSheafify J P := by
  calc
    η ≫ (comparisonIso J η hQ).inv =
        (toSheafify J P ≫ (comparisonIso J η hQ).hom) ≫
          (comparisonIso J η hQ).inv := by rw [comparisonIso_unit]
    _ = toSheafify J P := by simp

/-- Inverting the comparison recovers the same sheafified section as the unit. -/
theorem comparisonIso_inverse_unit_apply (X : Cᵒᵖ) (s : P.obj X) :
    (comparisonIso J η hQ).inv.app X (η.app X s) = (toSheafify J P).app X s := by
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (comparisonIso_inverse_unit J η hQ) X) s

end LargeSource

section BottomTopology

variable {C : Type u} [Category.{v} C]

/-- An actual topology and actual sheaf discharge every class hypothesis.
No local-bijectivity or sheafification assumptions are supplied by the caller. -/
theorem bot_identity_lift_isIso (P : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    IsIso (sheafifyLift (⊥ : GrothendieckTopology C) (𝟙 P)
      (Presheaf.isSheaf_bot P)) :=
  isIso_sheafifyLift_of_isLocallyBijective _ _ _

end BottomTopology

open Lean in
run_cmd do
  for name in #[``CategoryTheory.isIso_sheafifyLift_of_isLocallyBijective,
      ``comparisonIso, ``comparisonIso_unit, ``comparisonIso_inverse_unit,
      ``comparisonIso_inverse_unit_apply, ``bot_identity_lift_isIso] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Locally bijective sheafification comparison uses only standard Lean foundations."

end MotivicTest.SheafifyLocallyBijective
