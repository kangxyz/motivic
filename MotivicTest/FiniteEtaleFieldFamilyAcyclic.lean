/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Ordinary.FieldFamilyAcyclic
public import Lean.Util.CollectAxioms

/-! Direct tests of the actual all-point residue coefficient family and its injective steps. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite AlgebraicGeometry
universe w u
namespace MotivicTest.FiniteEtaleFieldFamilyAcyclic
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable (X : Scheme.{u}) (F : Sheaf (nisnevichTopology X) AddCommGrpCat.{u + 1})

/-- The coefficients are actual residue inverse images at every original point. -/
def actualResidueFamily : FieldCoefficientFamily (fun x => (X.residueField x : Type u)) :=
  fun x => (inverseImage (X.fromSpecResidueField x)).obj F

/-- This concrete short exact sequence contains the chosen field embeddings and cokernels. -/
theorem actual_residue_step_shortExact :
    (fieldFamilyProductStep (fun x => (X.residueField x : Type u))
      (fun x => X.fromSpecResidueField x)
      (actualResidueFamily X F)).ShortExact :=
  fieldFamilyProductStep_shortExact _ _ _

/-- The middle sheaf is actually ordinary injective, not merely acyclic by assumption. -/
theorem actual_residue_step_injective :
    Injective (fieldFamilyProductStep (fun x => (X.residueField x : Type u))
      (fun x => X.fromSpecResidueField x)
      (actualResidueFamily X F)).X₂ := inferInstance

/-- The actual final map is surjective on each original small-site section group. -/
theorem actual_residue_step_sections_surjective (V : Scheme.EtaleSeparatedFiniteType X) :
    Function.Surjective ((fieldFamilyProductStep (fun x => (X.residueField x : Type u))
      (fun x => X.fromSpecResidueField x)
      (actualResidueFamily X F)).g.hom.app (op V)) := by
  have := fieldFamilyProductStep_presheaf_epi (fun x => (X.residueField x : Type u))
      (fun x => X.fromSpecResidueField x)
    (actualResidueFamily X F)
  exact (AddCommGrpCat.epi_iff_surjective _).mp inferInstance

variable [HasExt.{w} (Sheaf (nisnevichTopology X) AddCommGrpCat.{u + 1})]

/-- No transfer-injectivity, homotopy invariance, purity or vanishing premise is used. -/
theorem actual_residue_product_H_succ_eq_zero (V : Scheme.EtaleSeparatedFiniteType X) (n : ℕ)
    (e : Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1} (nisnevichTopology X)
      (∏ᶜ fun x => (directImage (X.fromSpecResidueField x)).obj
        ((inverseImage (X.fromSpecResidueField x)).obj F)) (n + 1) V) : e = 0 :=
  fieldFamilyProduct_H_succ_eq_zero (fun x => (X.residueField x : Type u))
      (fun x => X.fromSpecResidueField x)
    (actualResidueFamily X F) V n e

open Lean in
run_cmd do
  for name in #[``actual_residue_step_shortExact, ``actual_residue_step_injective,
      ``actual_residue_step_sections_surjective, ``actual_residue_product_H_succ_eq_zero,
      ``exists_fieldFamily_resolution_step,
      ``fieldFamilyProduct_ext_succ_eq_zero] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual residue-field steps and product acyclicity: standard foundations only."

end MotivicTest.FiniteEtaleFieldFamilyAcyclic
