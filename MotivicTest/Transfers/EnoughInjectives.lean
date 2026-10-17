/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.EnoughInjectives
public import Lean.Util.CollectAxioms

/-!
# Genuine Grothendieck and injective consumers

The actual additive transfer category supplies its own injective presentations.
No ordinary underlying-sheaf acyclicity or positive-degree transfers are assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Motivic

universe u v

namespace MotivicTest.Transfers.EnoughInjectives

section General

variable (C : Type u) [Category.{v} C] [Preadditive C]

example : AB5OfSize.{max u v, max u v} (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v}) :=
  inferInstance

example : IsGrothendieckAbelian.{max u v} (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v}) :=
  inferInstance

end General

variable {k : Type u} [Field k]

example : IsGrothendieckAbelian.{u + 1} (SheafWithTransfers.{u + 1} k) :=
  inferInstance

/-- Each actual transfer sheaf embeds into an injective object of that category. -/
theorem actual_injective_embedding (F : SheafWithTransfers.{u + 1} k) :
    ∃ (J : SheafWithTransfers.{u + 1} k) (_ : Injective J) (i : F ⟶ J), Mono i := by
  let p := (EnoughInjectives.presentation F).some
  exact ⟨p.J, p.injective, p.f, p.mono⟩

open Lean in
run_cmd do
  for name in #[``CategoryTheory.AdditiveFunctor.liftedYonedaAddEquiv,
      ``CategoryTheory.AdditiveFunctor.liftedRepresentables_isSeparating,
      ``CategoryTheory.AdditiveFunctor.hasExactColimitsOfShape,
      ``CategoryTheory.AdditiveFunctor.isGrothendieckAbelian,
      ``Motivic.SheafWithTransfers.isGrothendieckAbelian,
      ``Motivic.SheafWithTransfers.enoughInjectives,
      ``actual_injective_embedding] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Transfer sheaf injective presentations use only standard Lean foundations."

end MotivicTest.Transfers.EnoughInjectives
