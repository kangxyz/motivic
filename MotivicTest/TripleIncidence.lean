/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Associativity.IncidenceSupport
public import Motivic.Aglib.AlgebraicGeometry.Cycles.IntegralCycle
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Actual common-incidence and finite intermediate-image consumers -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.MotivicTest.TripleIncidence
open _root_.AlgebraicGeometry.Scheme

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g)
  (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

/-- Actual integral cycles have the same output under the geometric associator. -/
theorem actualOutputPushforward [IsSeparated i] (α : IntegralCycle (F.tripleIncidence G H)) :
    IntegralCycle.finitePushforward (F.rightTripleIncidenceMap G H)
      (IntegralCycle.finitePushforward (F.tripleIncidenceAssoc G H).hom α) =
    IntegralCycle.finitePushforward (F.tripleIncidenceMap G H) α := by
  rw [← AddMonoidHom.comp_apply, ← IntegralCycle.finitePushforward_comp]
  simp only [F.tripleIncidenceAssoc_map G H]

/-- The left projection formula is indexed by the entire actual finite fiber. -/
theorem leftImageFiberFinite [IsSeparated h] (y : F.leftIntermediateImageProduct G H) :
    Set.Finite (F.leftIntermediateImageMap G H ⁻¹' {y}) :=
  (F.leftIntermediateImageMap G H).finite_preimage_singleton y

/-- The right product map is finite without any finite right-pair projection assumption. -/
theorem rightImageFiberFinite [IsSeparated i] (y : F.rightIntermediateImageProduct G H) :
    Set.Finite (F.rightIntermediateImageMap G H ⁻¹' {y}) :=
  (F.rightIntermediateImageMap G H).finite_preimage_singleton y

/-- The right image-product square uses the actual second-pair scheme-image factor. -/
theorem rightImageFactor :
    F.tripleIncidenceToRightSupportProduct G H ≫ F.rightIntermediateImageMap G H ≫
      pullback.snd (F.targetProjection ≫ g)
        ((G.incidenceMap H).imageι ≫ pullback.fst g i ≫ g) =
      F.tripleIncidenceToRightPair G H ≫ (G.incidenceMap H).toImage := by
  rw [F.rightIntermediateImageMap_snd G H]
  rw [F.tripleIncidenceToRightSupportProduct_snd_assoc]

end Motivic.MotivicTest.TripleIncidence
