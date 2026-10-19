/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.GenericCoefficients

/-!
# Collision-aware finite pushforward of generic coefficient cycles

Actual finite images of point closures are point closures of the actual images.
Finite pushforward therefore sums all source generic coefficients above each
target point, with the original residue degree of every source point. When the
map genuinely preserves generic points, the result is a generic coefficient
cycle on the target. No injectivity or bijection of generic points is assumed.

All enumerations are finite before forming the sums. Coefficients are arbitrary
integers, so cancellation between colliding images is retained. No base-change
identity between pair degrees and exterior closed-fiber lengths is asserted.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped BigOperators

universe u

namespace AlgebraicGeometry.Scheme

namespace IntegralClosedSubscheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]

/-- A finite image retains the literal integral ideal-sheaf support of its image point. -/
theorem pointClosure_finiteImage (x : X) :
    (pointClosure x).finiteImage f = pointClosure (f x) := by
  apply point_injective
  simp only [point_finiteImage, point_pointClosure]

end IntegralClosedSubscheme

namespace IntegralCycle

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]

/-- Two colliding actual point-closure images add their own signed, degree-weighted
coefficients on the same actual integral target support. -/
theorem finitePushforward_two_pointClosures
    (x₁ x₂ : X) (h : f x₁ = f x₂) (m n : ℤ) :
    finitePushforward f
        (Finsupp.single (IntegralClosedSubscheme.pointClosure x₁) m +
          Finsupp.single (IntegralClosedSubscheme.pointClosure x₂) n) =
      Finsupp.single (IntegralClosedSubscheme.pointClosure (f x₂))
        (m * (f.residueDegree x₁ : ℤ) + n * (f.residueDegree x₂ : ℤ)) := by
  simp only [map_add, finitePushforward_single,
    IntegralClosedSubscheme.point_pointClosure,
    IntegralClosedSubscheme.pointClosure_finiteImage, h, Finsupp.single_add]

/-- Opposite cross-degree weights cancel at colliding finite images, even when
the individual residue degrees differ. -/
theorem finitePushforward_collision_cancel
    (x₁ x₂ : X) (h : f x₁ = f x₂) :
    finitePushforward f
        (Finsupp.single (IntegralClosedSubscheme.pointClosure x₁)
            (f.residueDegree x₂ : ℤ) -
          Finsupp.single (IntegralClosedSubscheme.pointClosure x₂)
            (f.residueDegree x₁ : ℤ)) = 0 := by
  simp only [map_sub, finitePushforward_single,
    IntegralClosedSubscheme.point_pointClosure,
    IntegralClosedSubscheme.pointClosure_finiteImage, h]
  rw [mul_comm (f.residueDegree x₂ : ℤ) (f.residueDegree x₁ : ℤ), sub_self]

variable [IsNoetherian X]

open Classical in
/-- The finite sum of every source generic contribution above a target point.
Zero and negative coefficients are retained, as are all genuine residue degrees. -/
def genericPushforwardCoefficient (c : genericPoints X → ℤ) (y : Y) : ℤ :=
  letI := genericPointFintype X
  ∑ x, if f x.1 = y then c x * (f.residueDegree x.1 : ℤ) else 0

/-- The faithful point representation of actual finite pushforward is exactly
the finite collision sum, without a generic-preservation hypothesis. -/
theorem toPoints_finitePushforward_ofGenericCoefficients_apply
    (c : genericPoints X → ℤ) (y : Y) :
    toPoints (finitePushforward f (ofGenericCoefficients X c)) y =
      genericPushforwardCoefficient f c y := by
  classical
  let := genericPointFintype X
  simp only [ofGenericCoefficients_eq_sum, map_sum, Finsupp.finsetSum_apply,
    finitePushforward_single, toPoints_single, IntegralClosedSubscheme.point_finiteImage,
    IntegralClosedSubscheme.point_pointClosure, Finsupp.single_apply,
    genericPushforwardCoefficient]

omit [IsFinite f] in
/-- Proven generic preservation forces every nongeneric target coefficient to
vanish; finite morphisms alone are not asserted to have this property. -/
theorem genericPushforwardCoefficient_eq_zero_of_not_generic
    (hgeneric : ∀ x : genericPoints X, f x.1 ∈ genericPoints Y)
    (c : genericPoints X → ℤ) (y : Y) (hy : y ∉ genericPoints Y) :
    genericPushforwardCoefficient f c y = 0 := by
  classical
  let := genericPointFintype X
  unfold genericPushforwardCoefficient
  apply Finset.sum_eq_zero
  intro x _
  split_ifs with h
  · exact (hy (h ▸ hgeneric x)).elim
  · rfl

/-- Regroup every actual finite-image collision as a generic target coefficient.
The only geometric input beyond finiteness is actual generic preservation. -/
theorem finitePushforward_ofGenericCoefficients [IsNoetherian Y]
    (hgeneric : ∀ x : genericPoints X, f x.1 ∈ genericPoints Y)
    (c : genericPoints X → ℤ) :
    finitePushforward f (ofGenericCoefficients X c) =
      ofGenericCoefficients Y (fun y => genericPushforwardCoefficient f c y.1) := by
  apply toPoints_injective
  ext y
  rw [toPoints_finitePushforward_ofGenericCoefficients_apply,
    toPoints_ofGenericCoefficients_apply]
  by_cases hy : y ∈ genericPoints Y
  · rw [dite_eq_left hy]
  · rw [dite_eq_right hy]
    exact genericPushforwardCoefficient_eq_zero_of_not_generic f hgeneric c y hy

end IntegralCycle

end AlgebraicGeometry.Scheme
