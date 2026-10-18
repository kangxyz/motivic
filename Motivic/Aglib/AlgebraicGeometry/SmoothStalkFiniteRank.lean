/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Regularity

/-! # Finite natural local rank of an actual smooth stalk -/

@[expose] public noncomputable section
open CategoryTheory
universe u
namespace AlgebraicGeometry.Scheme

/-- Smooth-field regularity makes the dimension of every original stalk a natural
number. No global dimension bound or induction on the ambient scheme is needed. -/
theorem exists_nat_ringKrullDim_stalk_of_smooth
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f] (x : X) :
    ∃ d : ℕ, ringKrullDim (X.presheaf.stalk x) = d := by
  let : IsRegularLocalRing (X.presheaf.stalk x) :=
    smoothFieldRegularity k X f inferInstance x
  exact ⟨(IsLocalRing.maximalIdeal (X.presheaf.stalk x)).spanFinrank,
    IsRegularLocalRing.spanFinrank_maximalIdeal.symm⟩

end AlgebraicGeometry.Scheme
