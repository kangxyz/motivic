/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Stalk.KernelMinimalPrimes
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Associativity.IncidenceSupport
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Associativity.GenericDominance

/-! # Actual triple-incidence kernel-prime and component consumers -/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme (SmoothSite stalkKernelGenericEquiv)
open CategoryTheory AlgebraicGeometry Motivic

universe u

namespace Motivic.MotivicTest.StalkKernelMinimalPrimes

variable (k : Type u) [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

/-- A literal minimal prime of the actual second-diagonal ambient-stalk kernel
constructs a genuine triple component whose closure contains the chosen point. -/
noncomputable def actualTripleComponentAboveKernel (x : F.tripleIncidence G H)
    (p : (RingHom.ker ((F.tripleIncidenceToLeftSupportProduct G H).stalkMap x).hom).minimalPrimes) :
    {y : genericPoints (F.tripleIncidence G H) // y.1 ⤳ x} :=
  stalkKernelGenericEquiv (F.tripleIncidenceToLeftSupportProduct G H) x p

/-- Every actual local kernel prime indexes a component dominating an original
source generic, without supplying that generic point or its dominance. -/
theorem actualTripleKernelPointSourceGeneric (x : F.tripleIncidence G H)
    (p : (RingHom.ker ((F.tripleIncidenceToLeftSupportProduct G H).stalkMap x).hom).minimalPrimes) :
    F.tripleIncidenceSource G H (actualTripleComponentAboveKernel k F G H x p).1.1 ∈
      genericPoints X.left :=
  F.tripleIncidenceSource_mem_genericPoints k G H _
    (actualTripleComponentAboveKernel k F G H x p).1.2

/-- At an actual triple component generic, the whole unreduced ambient kernel
has only one minimal prime. The conclusion is derived from the point geometry. -/
theorem actualTripleKernelMinimalPrimes_subsingleton
    (x : genericPoints (F.tripleIncidence G H)) :
    Subsingleton ((RingHom.ker
      ((F.tripleIncidenceToLeftSupportProduct G H).stalkMap x.1).hom).minimalPrimes) := by
  let e := stalkKernelGenericEquiv (F.tripleIncidenceToLeftSupportProduct G H) x.1
  have hpoint (y : {y : genericPoints (F.tripleIncidence G H) // y.1 ⤳ x.1}) :
      y.1.1 = x.1 := by
    have hback : x.1 ⤳ y.1.1 := specializes_iff_closure_subset.mpr
      (x.2.2 isIrreducible_singleton.closure y.2.closure_subset)
    exact (y.2.antisymm hback).eq
  constructor
  intro p q
  apply e.injective
  apply Subtype.ext
  exact Subtype.ext ((hpoint (e p)).trans (hpoint (e q)).symm)

/-- The unique minimal-prime type at that actual triple generic is nonempty;
its witness is constructed from the generic point itself, not assumed. -/
theorem actualTripleKernelMinimalPrimes_nonempty
    (x : genericPoints (F.tripleIncidence G H)) :
    Nonempty
      (RingHom.ker ((F.tripleIncidenceToLeftSupportProduct G H).stalkMap x.1).hom).minimalPrimes :=
  ⟨(stalkKernelGenericEquiv (F.tripleIncidenceToLeftSupportProduct G H) x.1).symm
    ⟨x, specializes_rfl⟩⟩

end Motivic.MotivicTest.StalkKernelMinimalPrimes
