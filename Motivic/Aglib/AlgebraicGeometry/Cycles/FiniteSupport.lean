/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.ResidueDegree
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.Finsupp.Ext

/-!
# Finite-support cycles and finite pushforward

A finite-support cycle is an integer linear combination of scheme points,
viewed as the generic points of their irreducible closed supports. Pushforward
along a finite morphism sends `[x]` to `[κ(x) : κ(f x)] [f x]`. This file
constructs that additive map and proves its identity and composition laws
using the actual tower of residue fields.

The auxiliary residue-weighted map is defined for every scheme morphism,
with zero degree for an infinite residue extension. The genuine finite
pushforward on actual integral closed subschemes is constructed separately
in `IntegralCycle`; no proper or intersection-theoretic statement for
arbitrary morphisms is asserted.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- Integer cycles with finite support, indexed by generic points. -/
abbrev FiniteSupportCycle (X : Scheme.{u}) : Type u := X →₀ ℤ

namespace FiniteSupportCycle
open _root_.AlgebraicGeometry.Scheme.Hom

variable {X Y Z : Scheme.{u}}

/-- The residue-degree weighted additive map on actual scheme points. -/
noncomputable def residuePushforward (f : X ⟶ Y) :
    FiniteSupportCycle X →+ FiniteSupportCycle Y :=
  Finsupp.liftAddHom fun x =>
    { toFun := fun n => Finsupp.single (f x) (n * (f.residueDegree x : ℤ))
      map_zero' := by simp
      map_add' := by intro m n; simp [add_mul, Finsupp.single_add] }

@[simp]
theorem residuePushforward_single (f : X ⟶ Y) (x : X) (n : ℤ) :
    residuePushforward f (Finsupp.single x n) =
      Finsupp.single (f x) (n * (f.residueDegree x : ℤ)) :=
  Finsupp.liftAddHom_apply_single _ _ _

/-- The explicit finite sum defining all pushforward coefficients. -/
theorem residuePushforward_eq_sum (f : X ⟶ Y) (c : FiniteSupportCycle X) :
    residuePushforward f c =
      c.sum fun x n => Finsupp.single (f x) (n * (f.residueDegree x : ℤ)) := rfl

@[simp]
theorem residuePushforward_id :
    residuePushforward (𝟙 X) = AddMonoidHom.id (FiniteSupportCycle X) := by
  apply Finsupp.addHom_ext
  intro x n
  simp

/-- Functoriality is proved from field-degree multiplicativity, rather than assumed. -/
theorem residuePushforward_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    residuePushforward (f ≫ g) =
      (residuePushforward g).comp (residuePushforward f) := by
  apply Finsupp.addHom_ext
  intro x n
  simp [residueDegree_comp, mul_assoc, mul_comm]

/-- An isomorphism transports each point coefficient unchanged. -/
theorem residuePushforward_single_of_isIso (f : X ⟶ Y) [IsIso f] (x : X) (n : ℤ) :
    residuePushforward f (Finsupp.single x n) = Finsupp.single (f x) n := by
  simp

/-- A scheme isomorphism induces an actual additive equivalence of cycle groups. -/
noncomputable def isoPushforward (e : X ≅ Y) : FiniteSupportCycle X ≃+ FiniteSupportCycle Y :=
  { residuePushforward e.hom with
    invFun := residuePushforward e.inv
    left_inv := fun c => by
      change ((residuePushforward e.inv).comp (residuePushforward e.hom)) c = c
      rw [← residuePushforward_comp, e.hom_inv_id, residuePushforward_id]
      rfl
    right_inv := fun c => by
      change ((residuePushforward e.hom).comp (residuePushforward e.inv)) c = c
      rw [← residuePushforward_comp, e.inv_hom_id, residuePushforward_id]
      rfl }

end FiniteSupportCycle

end AlgebraicGeometry.Scheme
