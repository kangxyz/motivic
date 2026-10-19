/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightTwo.CorestrictionBoundary
public import Lean.Util.CollectAxioms

/-!
# Actual signed one-simplex endpoints under finite corestriction

These consumers use the original correspondence category and its literal
singular cofaces. No separability or extension-field smoothness is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Motivic
open WeightTwoCorestriction

universe u

namespace MotivicTest.WeightTwoCorestrictionBoundary

variable {k E : Type u} [Field k] [Field E] [Algebra k E] [Module.Finite k E]

/-- Each original endpoint commutes with the actual cycle pushforward. -/
theorem actual_endpoint (i : Fin 2)
    (α : Cor.simplexProduct (WeightOnePointNorm.point E) 1 ⟶ WeightTwoSymbols.target E) :
    cyclePushforward (k := k) (E := E) 0 2
      ((Cor.simplexProductCosimplicial (WeightOnePointNorm.point E)).δ i ≫ α) =
    (Cor.simplexProductCosimplicial (WeightOnePointNorm.point k)).δ i ≫
      cyclePushforward (k := k) (E := E) 1 2 α :=
  cyclePushforward_face 2 i α

/-- Both original endpoints commute with transfer on an explicitly signed
combination of actual one-simplex correspondences. -/
theorem actual_signed_input (i : Fin 2) (n m : ℤ)
    (α β : Cor.simplexProduct (WeightOnePointNorm.point E) 1 ⟶ WeightTwoSymbols.target E) :
    cyclePushforward (k := k) (E := E) 0 2
      ((Cor.simplexProductCosimplicial (WeightOnePointNorm.point E)).δ i ≫
        (n • α - m • β)) =
    (Cor.simplexProductCosimplicial (WeightOnePointNorm.point k)).δ i ≫
      cyclePushforward (k := k) (E := E) 1 2 (n • α - m • β) :=
  cyclePushforward_face 2 i (n • α - m • β)

/-- Negative signed input uses the identical whole-endpoint pushforward. -/
theorem actual_negative_endpoint (i : Fin 2)
    (α : Cor.simplexProduct (WeightOnePointNorm.point E) 1 ⟶ WeightTwoSymbols.target E) :
    cyclePushforward (k := k) (E := E) 0 2
      ((Cor.simplexProductCosimplicial (WeightOnePointNorm.point E)).δ i ≫ (-α)) =
    (Cor.simplexProductCosimplicial (WeightOnePointNorm.point k)).δ i ≫
      cyclePushforward (k := k) (E := E) 1 2 (-α) :=
  cyclePushforward_face 2 i (-α)

open Lean in
run_cmd do
  for name in #[``sourceFace, ``ambientFace, ``ambientFace_isClosedImmersion,
      ``ambientIso_face, ``ambientMap_face, ``graphPullbackMap_ambientFace,
      ``finitePushforward_scalar_endpoint, ``generator_projection_flat,
      ``sourceFace_isClosedImmersion, ``toIntegralCycle_face_push,
      ``finitePushforward_face_generator, ``cyclePushforward_face,
      ``actual_endpoint, ``actual_signed_input, ``actual_negative_endpoint] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual signed graph-endpoint corestriction uses only standard foundations."

end MotivicTest.WeightTwoCorestrictionBoundary
