/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.GenericPoint
public import Motivic.AlgebraicGeometry.Scheme.RadicalSubscheme

/-!
# Reduced integral supports of points

The closure of every scheme point has a canonical reduced integral closed
subscheme structure. Its ideal sheaf is constructed from the vanishing ideal
and its radical, rather than by using a possibly nonreduced component scheme.
This completes the faithful dictionary between scheme points and actual
integral ideal-sheaf closed subschemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.IntegralClosedSubscheme

variable {X : Scheme.{u}}

/-- The canonical reduced integral closed subscheme supported on the closure of a point. -/
noncomputable def pointClosure (x : X) : IntegralClosedSubscheme X := by
  let I : X.IdealSheafData :=
    (Scheme.IdealSheafData.vanishingIdeal ⟨closure {x}, isClosed_closure⟩).radical
  have : IrreducibleSpace I.subscheme :=
    Subtype.irreducibleSpace isIrreducible_singleton.closure
  exact ⟨I, isIntegral_of_irreducibleSpace_of_isReduced _⟩

/-- The reduced support has exactly the original point's closure. -/
@[simp]
theorem support_pointClosure (x : X) :
    ((pointClosure x).val.support : Set X) = closure {x} := rfl

/-- Its ambient generic point is the original point. -/
@[simp]
theorem point_pointClosure (x : X) : (pointClosure x).point = x := by
  apply (pointClosure x).point_spec.eq
  exact isGenericPoint_closure

/-- Every actual integral closed subscheme is recovered from its generic point. -/
@[simp]
theorem pointClosure_point (V : IntegralClosedSubscheme X) : pointClosure V.point = V := by
  apply point_injective
  exact point_pointClosure V.point

/-- Reduced integral closed subschemes are canonically equivalent to scheme points. -/
noncomputable def pointEquiv : IntegralClosedSubscheme X ≃ X where
  toFun := point
  invFun := pointClosure
  left_inv := pointClosure_point
  right_inv := point_pointClosure

end Motivic.IntegralClosedSubscheme
