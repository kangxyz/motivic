/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.FiniteFieldResidueDegree
public import Lean.Util.CollectAxioms

/-!
# Consumers of the actual residue degree of field spectra

These consumers use the original field map and its induced residue action.
In particular the statements impose neither finiteness nor separability.
Every new public declaration is checked by a rejecting axiom audit.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Motivic.MotivicTest.FiniteFieldResidueDegree

/-- The original field homomorphism, rather than an independently chosen
algebra structure, determines both sides. -/
theorem original_scalar_degree {F E : Type u} [Field F] [Field E]
    (φ : F →+* E) (x : Spec (.of E)) :
    let : Algebra F E := φ.toAlgebra
    (Spec.map (CommRingCat.ofHom φ)).residueDegree x = Module.finrank F E :=
  Scheme.Hom.residueDegree_SpecMap F E φ x

/-- A consumer can use the exact pre-existing algebra action. -/
theorem original_algebra_degree {F E : Type u} [Field F] [Field E] [Algebra F E]
    (x : Spec (.of E)) :
    (Spec.map (CommRingCat.ofHom (algebraMap F E))).residueDegree x =
      Module.finrank F E :=
  Scheme.Hom.residueDegree_SpecMap_algebraMap F E x

/-- The scalar square records the actual residue field map. -/
theorem original_residue_action {F E : Type u} [Field F] [Field E]
    (φ : F →+* E) (x : Spec (.of E)) (a : F) :
    (Spec.map (CommRingCat.ofHom φ)).residueFieldMap x
        (Scheme.Spec.fieldEquivResidueField F
          (Spec.map (CommRingCat.ofHom φ) x) a) =
      Scheme.Spec.fieldEquivResidueField E x (φ a) :=
  congrArg (fun f : CommRingCat.of F ⟶ (Spec (.of E)).residueField x => f a)
    (Scheme.Spec.fieldEquivResidueField_naturality φ x)

/-- The identity extension has geometric residue degree one. -/
theorem identity_degree (F : Type u) [Field F] (x : Spec (.of F)) :
    (Spec.map (CommRingCat.ofHom (algebraMap F F))).residueDegree x = 1 := by
  rw [Scheme.Hom.residueDegree_SpecMap_algebraMap, Module.finrank_self]

open Lean in
run_cmd do
  for name in #[``Scheme.Spec.fieldEquivResidueField,
      ``Scheme.Spec.fieldEquivResidueField_eq_evaluation,
      ``Scheme.Spec.fieldEquivResidueField_naturality,
      ``Scheme.Hom.residueDegree_SpecMap,
      ``Scheme.Hom.residueDegree_SpecMap_algebraMap,
      ``original_scalar_degree, ``original_algebra_degree,
      ``original_residue_action, ``identity_degree] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual field-spectrum residue degrees use only standard Lean foundations."

end Motivic.MotivicTest.FiniteFieldResidueDegree
