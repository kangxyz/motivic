/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.SmoothSiteNisnevichEvaluation
public import Lean.Util.CollectAxioms

/-! # Exact smooth-site evaluation at its actual base field -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Motivic Motivic.SmoothSite

universe u

namespace MotivicTest.SmoothSiteNisnevichEvaluation

variable (k : Type u) [Field k]

/-- The geometric witness is a section in the smooth category, over the same field. -/
example {R : Presieve (base (Spec (.of k)))}
    (hR : R ∈ nisnevichPrecoverage (Spec (.of k)) _) :
    ∃ (Y : SmoothSite (Spec (.of k))) (f : Y ⟶ base (Spec (.of k))), R f ∧
      ∃ s : base (Spec (.of k)) ⟶ Y, s ≫ f = 𝟙 _ :=
  exists_section_of_mem_nisnevichPrecoverage_base k hR

example (R : Sieve (base (Spec (.of k)))) :
    R ∈ nisnevichTopology (Spec (.of k)) _ ↔ R = ⊤ :=
  mem_nisnevichTopology_base_iff k R

example {F G : Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}}
    (φ : F ⟶ G) [Epi φ] :
    Function.Surjective (φ.hom.app (op (base (Spec (.of k))))) :=
  surjective_app_base_of_epi k φ

example (F : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    IsIso ((toSheafify (nisnevichTopology (Spec (.of k))) F).app
      (op (base (Spec (.of k))))) := isIso_toSheafify_app_base k F

example : (nisnevichBaseEvaluation k).PreservesEpimorphisms := inferInstance

example : PreservesFiniteLimits (nisnevichBaseEvaluation k) := inferInstance

example : (nisnevichBaseEvaluation k).PreservesHomology := inferInstance

example (S : ShortComplex
    (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}))
    (hS : S.Exact) : (S.map (nisnevichBaseEvaluation k)).Exact :=
  exact_map_nisnevichBaseEvaluation k S hS

open Lean in
run_cmd do
  for name in #[``exists_section_of_mem_nisnevichPrecoverage_base,
      ``nisnevich_covering_sieve_base_eq_top, ``mem_nisnevichTopology_base_iff,
      ``surjective_app_base_of_isLocallySurjective,
      ``injective_app_base_of_isLocallyInjective, ``nisnevichBaseEvaluation,
      ``surjective_app_base_of_epi, ``isIso_toSheafify_app_base,
      ``exact_map_nisnevichBaseEvaluation] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Exact smooth-site base-field evaluation uses only standard Lean foundations."

end MotivicTest.SmoothSiteNisnevichEvaluation
