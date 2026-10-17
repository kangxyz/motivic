/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.FundamentalStalk
public import Motivic.AlgebraicGeometry.Cycles.FundamentalSupport
public import Motivic.AlgebraicGeometry.Cycles.IntegralCycle

/-!
# Fundamental cycles with actual generic local multiplicities

For a Noetherian scheme, the fundamental cycle is supported on its finitely
many irreducible components, given their reduced integral closed subscheme
structures. The coefficient of a component is the length of the original
scheme's local ring at its generic point. Finiteness and positivity of these
lengths are proved in `FundamentalStalk`; nilpotents are retained in the
multiplicities, even though cycle supports are reduced.

This construction is the ordinary fundamental cycle. In particular, applying
it to a scheme-theoretic fiber product does not identify it with the derived
intersection cycle or the alternating Tor-length cycle.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic

variable (X : Scheme.{u}) [IsNoetherian X]

/-- The fundamental cycle in the point representation, with literal local lengths. -/
noncomputable def fundamentalPointCycle : FiniteSupportCycle X := by
  classical
  exact Finsupp.onFinset
    (genericPoints.finite (finite_irreducibleComponents_of_isNoetherian (X := X))).toFinset
    (fun x => if hx : x ∈ genericPoints X then (genericMultiplicity ⟨x, hx⟩ : ℤ) else 0)
    (by intro x hx; simpa only [Set.Finite.mem_toFinset] using
      (by_contra fun h => hx (dite_eq_right h)))

/-- The actual integral-subscheme fundamental cycle of a Noetherian scheme. -/
noncomputable def fundamentalCycle : IntegralCycle X :=
  Finsupp.equivMapDomain IntegralClosedSubscheme.pointEquiv.symm (fundamentalPointCycle X)

variable {X}

open Classical in
/-- Its coefficient at every point, including vanishing away from the generic points. -/
theorem fundamentalPointCycle_apply (x : X) :
    fundamentalPointCycle X x =
      if hx : x ∈ genericPoints X then (genericMultiplicity ⟨x, hx⟩ : ℤ) else 0 := rfl

/-- The faithful point representation preserves the fundamental cycle exactly. -/
@[simp]
theorem toPoints_fundamentalCycle :
    IntegralCycle.toPoints (fundamentalCycle X) = fundamentalPointCycle X := by
  rw [fundamentalCycle, Finsupp.equivMapDomain_eq_mapDomain]
  change Finsupp.mapDomain IntegralClosedSubscheme.point
    (Finsupp.mapDomain IntegralClosedSubscheme.pointClosure _) = _
  rw [← Finsupp.mapDomain_comp]
  simpa only [Function.comp_def, IntegralClosedSubscheme.point_pointClosure, id_eq] using
    Finsupp.mapDomain_id (v := fundamentalPointCycle X)

open Classical in
/-- The coefficient is measured in the original stalk, not in its reduced support. -/
theorem fundamentalCycle_apply (V : IntegralClosedSubscheme X) :
    fundamentalCycle X V = if hx : V.point ∈ genericPoints X then
      (genericMultiplicity ⟨V.point, hx⟩ : ℤ) else 0 := rfl

/-- Every component support has its positive generic local length as coefficient. -/
theorem fundamentalCycle_component (x : genericPoints X) :
    fundamentalCycle X (IntegralClosedSubscheme.pointClosure x.val) =
      (genericMultiplicity x : ℤ) := by
  simp [fundamentalCycle_apply, x.property]

/-- Reduced schemes have coefficient one on every irreducible component. -/
theorem fundamentalCycle_component_of_isReduced [IsReduced X] (x : genericPoints X) :
    fundamentalCycle X (IntegralClosedSubscheme.pointClosure x.val) = 1 := by
  rw [fundamentalCycle_component, genericMultiplicity_eq_one]
  rfl

/-- The point support is precisely the generic points of irreducible components. -/
theorem mem_support_fundamentalPointCycle (x : X) :
    x ∈ (fundamentalPointCycle X).support ↔ x ∈ genericPoints X := by
  classical
  rw [Finsupp.mem_support_iff, fundamentalPointCycle_apply]
  split_ifs with hx
  · simp [hx, (genericMultiplicity_pos ⟨x, hx⟩).ne']
  · simp [hx]

/-- Even without reducedness an irreducible scheme has one support, with its actual local length. -/
theorem fundamentalCycle_of_irreducibleSpace [IrreducibleSpace X] :
    fundamentalCycle X =
      Finsupp.single (IntegralClosedSubscheme.pointClosure (genericPoint X))
        ((Module.length (X.presheaf.stalk (genericPoint X))
          (X.presheaf.stalk (genericPoint X))).toNat : ℤ) := by
  apply IntegralCycle.toPoints_injective
  rw [toPoints_fundamentalCycle, IntegralCycle.toPoints_single,
    IntegralClosedSubscheme.point_pointClosure]
  classical
  ext x
  by_cases hx : x = genericPoint X
  · subst x
    simp [fundamentalPointCycle_apply, genericPoints_eq_singleton, genericMultiplicity]
  · simp [fundamentalPointCycle_apply, genericPoints_eq_singleton, hx]

/-- For an integral scheme the fundamental cycle is the single integral support with weight one. -/
theorem fundamentalCycle_of_isIntegral [IsIntegral X] :
    fundamentalCycle X =
      Finsupp.single (IntegralClosedSubscheme.pointClosure (genericPoint X)) 1 := by
  apply IntegralCycle.toPoints_injective
  rw [toPoints_fundamentalCycle, IntegralCycle.toPoints_single,
    IntegralClosedSubscheme.point_pointClosure]
  classical
  ext x
  simp [fundamentalPointCycle_apply, genericPoints_eq_singleton, Finsupp.single_apply,
    eq_comm]

end Motivic
