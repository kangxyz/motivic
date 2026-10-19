/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.LinearDisjoint
public import Mathlib.FieldTheory.Finite.Extension

/-! # Coprime finite field extensions have a field as their entire tensor product -/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra.TensorProduct

universe u v w

/-- Coprime degrees make the entire tensor algebra a field, not merely one of
its residue branches. The proof uses the actual linear-disjointness API. -/
theorem isField_of_coprime_finrank
    (k : Type u) [Field k] (K : Type v) [Field K] [Algebra k K]
    (L : Type w) [Field L] [Algebra k L]
    (h : (Module.finrank k K).Coprime (Module.finrank k L)) :
    IsField (K ⊗[k] L) := by
  apply IntermediateField.LinearDisjoint.isField_of_forall k K L
  intro E _ _ f g
  apply IntermediateField.LinearDisjoint.of_finrank_coprime
  rwa [← f.equivFieldRange.toLinearEquiv.finrank_eq,
    ← g.equivFieldRange.toLinearEquiv.finrank_eq]

/-- The canonical degree-n finite extension has a single full residue fiber
whenever n is coprime to the original finite residue degree. -/
theorem isField_residue_finiteExtension
    (k : Type u) [Field k] [Finite k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (K : Type v) [Field K] [Algebra k K]
    (n : ℕ) [NeZero n] (h : (Module.finrank k K).Coprime n) :
    IsField (K ⊗[k] FiniteField.Extension k p n) := by
  apply isField_of_coprime_finrank k K (FiniteField.Extension k p n)
  simpa only [FiniteField.finrank_extension] using h

end Algebra.TensorProduct
