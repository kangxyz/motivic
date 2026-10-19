/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.FundamentalCycle
public import Motivic.Aglib.AlgebraicGeometry.Cycles.FundamentalSupport

/-!
# Generic coefficients of cycles
-/

@[expose] public noncomputable section


@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

universe u

namespace AlgebraicGeometry.Scheme

namespace IntegralCycle

variable (X : Scheme.{u}) [IsNoetherian X]

/-- A finite enumeration of the actual generic points of a Noetherian scheme. -/
@[instance_reducible]
noncomputable def genericPointFintype : Fintype (genericPoints X) :=
  (genericPoints.finite (finite_irreducibleComponents_of_isNoetherian (X := X))).fintype

/-- The integral component cycle with the specified integer coefficients. -/
noncomputable def ofGenericCoefficients : (genericPoints X → ℤ) →+ IntegralCycle X := by
  classical
  letI := genericPointFintype X
  exact
    { toFun := fun c => ∑ x, Finsupp.single (IntegralClosedSubscheme.pointClosure x.val) (c x)
      map_zero' := by simp
      map_add' := by intro c d; simp [Finsupp.single_add, Finset.sum_add_distrib] }

variable {X}

/-- The finite sum uses all actual generic points, including disconnected components. -/
theorem ofGenericCoefficients_eq_sum (c : genericPoints X → ℤ) :
    ofGenericCoefficients X c =
      letI := genericPointFintype X
      ∑ x, Finsupp.single (IntegralClosedSubscheme.pointClosure x.val) (c x) := rfl

open Classical in
/-- The point representation has exactly the specified generic coefficients. -/
theorem toPoints_ofGenericCoefficients_apply (c : genericPoints X → ℤ) (x : X) :
    toPoints (ofGenericCoefficients X c) x =
      if hx : x ∈ genericPoints X then c ⟨x, hx⟩ else 0 := by
  let := genericPointFintype X
  rw [ofGenericCoefficients_eq_sum, map_sum, Finsupp.finsetSum_apply]
  simp only [toPoints_single, IntegralClosedSubscheme.point_pointClosure]
  by_cases hx : x ∈ genericPoints X
  · rw [dite_eq_left hx]
    rw [Finset.sum_eq_single (⟨x, hx⟩ : genericPoints X)]
    · simp
    · intro y _ hy
      exact Finsupp.single_eq_of_ne (fun h => hy (Subtype.ext h.symm))
    · simp
  · rw [dite_eq_right hx]
    apply Finset.sum_eq_zero
    intro y _
    exact Finsupp.single_eq_of_ne (fun h => hx (h ▸ y.property))

/-- Genuine generic local lengths give exactly the ordinary fundamental cycle. -/
theorem ofGenericCoefficients_genericMultiplicity :
    ofGenericCoefficients X (fun x => (genericMultiplicity x : ℤ)) = fundamentalCycle X := by
  apply toPoints_injective
  ext x
  rw [toPoints_fundamentalCycle, toPoints_ofGenericCoefficients_apply,
    fundamentalPointCycle_apply]

end IntegralCycle

end AlgebraicGeometry.Scheme
