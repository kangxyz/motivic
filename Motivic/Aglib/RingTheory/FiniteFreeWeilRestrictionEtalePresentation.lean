/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.FiniteFreeWeilRestrictionPresentation
public import Motivic.Aglib.RingTheory.FiniteFreeWeilRestrictionEtale

/-!
# Étaleness of the concrete affine finite-free restriction of scalars

The representing equivalence is constructed from coefficient equations, not
supplied as a hypothesis. The original presented algebra and literal evaluation
remain those of `FiniteFreeWeilRestrictionPresentation`.
-/

@[expose] public section

noncomputable section

open Module

namespace Algebra.WeilRestriction

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C]
variable {ι κ σ : Type*} [Fintype κ]
variable (b : Basis κ A B) (P : Presentation B C ι σ)

/-- Formal étaleness of the actual coefficient quotient. -/
instance [FormallyEtale B C] : FormallyEtale A (CoordinateQuotient b P.relation) :=
  formallyEtale_of_homEquiv (A := A) (B := B) (C := C)
    (fun T _ _ => homEquiv (T := T) b P)
    (fun _ _ _ I h c => homEquiv_natural b P h (Ideal.Quotient.mkₐ A I) c)

/-- A finite presentation of an étale algebra produces an actual étale representing algebra. -/
instance [Finite ι] [Finite σ] [Etale B C] :
    Etale A (CoordinateQuotient b P.relation) where

/-- The concrete restriction algebra obtained from a chosen finite presentation. -/
abbrev Ring (b : Basis κ A B) (C : Type*) [CommRing C] [Algebra B C]
    [FinitePresentation B C] :=
  CoordinateQuotient b (Presentation.ofFinitePresentation B C).relation

/-- Étaleness for the finitely presented algebra itself, with no presentation input. -/
instance [Etale B C] : Etale A (Ring b C) := by
  change Etale A (CoordinateQuotient b (Presentation.ofFinitePresentation B C).relation)
  infer_instance

end Algebra.WeilRestriction
