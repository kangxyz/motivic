/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.PrescribedBoundaryPencil
public import Mathlib.Data.ZMod.Basic

/-! # Constructed affine pencils and whole scheme-theoretic fibers -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial
open Scheme.PrescribedBoundaryPencil

universe u

namespace Motivic.MotivicTest.PrescribedBoundaryPencil

/-- The supplied boundary value is extended, not assumed to lift beforehand. -/
example {R : Type u} [CommRing R] (I J : Ideal R) (hIJ : IsCoprime I J)
    (r : R ⧸ J) : ∃ h : R, Ideal.Quotient.mk I h = 1 ∧ Ideal.Quotient.mk J h = r :=
  exists_boundary_function I J hIJ r

/-- The actual categorical endpoint fiber retains the original principal ideal. -/
example {R : Type u} [CommRing R] (a b : R) :
    Limits.pullback (Spec.map (CommRingCat.ofHom (evalRingHom (1 : R))))
      (familyInclusion a b) ≅ Spec (.of (R ⧸ Ideal.span {b})) :=
  oneFiberSchemeIso a b

/-- Boundary avoidance concerns the whole categorical boundary fiber. -/
example {R : Type u} [CommRing R] (I : Ideal R) (a b : R)
    (hab : Ideal.Quotient.mk I a = Ideal.Quotient.mk I b)
    (ha : IsUnit (Ideal.Quotient.mk I a)) :
    IsEmpty (Limits.pullback
      (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (Ideal.Quotient.mk I))))
      (familyInclusion a b) : Scheme.{u}) :=
  boundaryFiber_isEmpty I a b hab ha

/-- A genuinely thickened boundary over a nonreduced coefficient ring. -/
example :
    (pencil (1 : (ZMod 4)[X]) (1 + X ^ 2)).map
      (Ideal.Quotient.mk (Ideal.span {X ^ 2})) = 1 := by
  have hz : Ideal.Quotient.mk (Ideal.span {X ^ 2}) (X ^ 2 : (ZMod 4)[X]) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  simpa using pencil_map_quotient (Ideal.span {X ^ 2})
    (1 : (ZMod 4)[X]) (1 + X ^ 2) (by simp [hz])

/-- The literal repeated-factor endpoint, not its radical or a selected branch. -/
example :
    Limits.pullback
      (Spec.map (CommRingCat.ofHom (evalRingHom (1 : (ZMod 4)[X]))))
      (familyInclusion (X ^ 2 : (ZMod 4)[X]) (((X : (ZMod 4)[X]) - 1) ^ 2)) ≅
      Spec (.of ((ZMod 4)[X] ⧸ Ideal.span {((X : (ZMod 4)[X]) - 1) ^ 2})) :=
  oneFiberSchemeIso (X ^ 2 : (ZMod 4)[X]) (((X : (ZMod 4)[X]) - 1) ^ 2)

/-- Fiberwise nondegeneracy is derived from the boundary, not postulated. -/
example {R : Type u} [CommRing R] [IsDomain R] (I : Ideal R) (hI : I ≠ ⊤)
    (a b t : R) (hab : Ideal.Quotient.mk I a = Ideal.Quotient.mk I b)
    (ha : IsUnit (Ideal.Quotient.mk I a)) : (pencil a b).eval t ∈ nonZeroDivisors R :=
  pencil_eval_regular_of_boundary I hI a b t hab ha

#print axioms pencil_eval_regular_of_boundary
#print axioms exists_prescribed_principal_pencil
#print axioms principal_pencil_regular
#print axioms familyBaseChangeIso
#print axioms oneFiberSchemeIso
#print axioms boundaryFiber_isEmpty

end Motivic.MotivicTest.PrescribedBoundaryPencil
