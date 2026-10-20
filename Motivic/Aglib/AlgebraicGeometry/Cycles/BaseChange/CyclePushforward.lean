/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.BaseChange.DegreeLength
public import Motivic.Aglib.AlgebraicGeometry.Cycles.GenericFinitePushforward
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.QuasiFinite.GenericFiber
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Generalizing.Components

/-!
# Global fundamental-cycle realization of an actual exterior support map

The actual all-branch degree-length identity becomes a GLOBAL finite
pushforward identity only after generic preservation is proved. The finite
pushforward's coefficients at nongeneric target points are explicitly zero.
No assertion that arbitrary finite maps preserve generic points is used.

A common geometric criterion supplies the missing preservation: the source
projection is an actual finite-type base change of a finite integral support
onto a normal component, and the target projection is quasi-finite. Only the
original normal base has normal stalks; the image support and both exterior
schemes can be nonnormal, disconnected, or nonreduced.

The point-closure Cartesian theorem retains the whole fundamental cycles and
the original ambient residue degree. Its generic-preservation input is
explicit; the companion actual SmoothSite pair consumer discharges it using
the original smooth source and the actual pair component's dominance.

Validation scope and recorded evidence are maintained in
`docs/VERIFICATION.md`.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Cycles.BaseChange.Pushforward
open _root_.AlgebraicGeometry.Scheme.Hom _root_.AlgebraicGeometry.Scheme.Products

open _root_.AlgebraicGeometry.Scheme.Cycles.BaseChange.DegreeLength

/-- Generic preservation follows from the literal normal-component Cartesian
projection and quasi-finite reflection. Normality of the image is not needed. -/
theorem mem_genericPoints_of_component_projection
    {A B U C N : Scheme.{u}} [IsNoetherian N] [IsIntegral C]
    (a : A ⟶ B) (p : A ⟶ U) (q : B ⟶ U) (r : A ⟶ C)
    (t : U ⟶ N) (s : C ⟶ N)
    [IsFinite s] [LocallyOfFiniteType t] [LocallyQuasiFinite q]
    (sq : IsPullback p r t s) (hcomm : a ≫ q = p)
    (hs : Set.range s ∈ irreducibleComponents N)
    (hN : ∀ n : N, IsDomain (N.presheaf.stalk n) ∧
      IsIntegrallyClosed (N.presheaf.stalk n))
    (w : genericPoints A) : a w.1 ∈ genericPoints B := by
  apply mem_genericPoints_of_image_generic q
  change (a ≫ q) w.1 ∈ genericPoints U
  rw [hcomm]
  exact mem_genericPoints_of_generalizing p
    (generalizingMap_of_isPullback_component p r t s sq hs hN) w.1 w.2

section GlobalCycles

variable {A B : Scheme.{u}} (a : A ⟶ B) [IsFinite a] [IsNoetherian A]

/-- The full actual generic fiber sum is precisely the collision-aware
coefficient of the pushforward of the original whole fundamental cycle. -/
theorem genericPushforwardCoefficient_eq_actualGenericFiberDegreeLengthSum (y : B) :
    IntegralCycle.genericPushforwardCoefficient a (fun w => (genericMultiplicity w : ℤ)) y =
      actualGenericFiberDegreeLengthSum a y := by
  classical
  let cyclePushforward_sourceGenericFintype := IntegralCycle.genericPointFintype A
  let cyclePushforward_actualFiberFintype := actualGenericFiberFintype a y
  unfold IntegralCycle.genericPushforwardCoefficient actualGenericFiberDegreeLengthSum
  rw [← finsum_eq_sum_of_fintype
    (fun w : {w : genericPoints A // a w.1 = y} =>
      (genericMultiplicity w.1 : ℤ) * (a.residueDegree w.1.1 : ℤ))]
  rw [finsum_subtype_eq_finsum_cond
    (f := fun w : genericPoints A =>
      (genericMultiplicity w : ℤ) * (a.residueDegree w.1 : ℤ))
    (fun w => a w.1 = y)]
  simp only [finsum_eq_if, finsum_eq_sum_of_fintype]

/-- Every coefficient, not only the generic target coefficients, is read from
the actual pushforward on integral closed-subscheme cycles. -/
theorem toPoints_finitePushforward_fundamentalCycle (y : B) :
    IntegralCycle.toPoints (IntegralCycle.finitePushforward a (fundamentalCycle A)) y =
      actualGenericFiberDegreeLengthSum a y := by
  rw [← IntegralCycle.ofGenericCoefficients_genericMultiplicity (X := A),
    IntegralCycle.toPoints_finitePushforward_ofGenericCoefficients_apply,
    genericPushforwardCoefficient_eq_actualGenericFiberDegreeLengthSum]

/-- Proven preservation rules out all off-generic coefficients of the actual
pushed fundamental cycle. Finiteness of the morphism alone would not suffice. -/
theorem toPoints_finitePushforward_fundamentalCycle_eq_zero_of_not_generic
    (hgeneric : ∀ w : genericPoints A, a w.1 ∈ genericPoints B)
    (y : B) (hy : y ∉ genericPoints B) :
    IntegralCycle.toPoints (IntegralCycle.finitePushforward a (fundamentalCycle A)) y = 0 := by
  rw [← IntegralCycle.ofGenericCoefficients_genericMultiplicity (X := A),
    IntegralCycle.toPoints_finitePushforward_ofGenericCoefficients_apply]
  exact IntegralCycle.genericPushforwardCoefficient_eq_zero_of_not_generic
    a hgeneric (fun w => (genericMultiplicity w : ℤ)) y hy

variable [IsNoetherian B]

/-- The generic degree-length balance and the PROVED off-generic vanishing
together give equality of the full integral cycles, by faithful point extensionality. -/
theorem finitePushforward_fundamentalCycle_of_degreeLength
    (hgeneric : ∀ w : genericPoints A, a w.1 ∈ genericPoints B)
    (d : ℤ)
    (hdegree : ∀ y : genericPoints B,
      actualGenericFiberDegreeLengthSum a y.1 = d * (genericMultiplicity y : ℤ)) :
    IntegralCycle.finitePushforward a (fundamentalCycle A) = d • fundamentalCycle B := by
  classical
  apply IntegralCycle.toPoints_injective
  ext y
  simp only [map_zsmul, toPoints_fundamentalCycle, Finsupp.smul_apply, zsmul_eq_mul,
    fundamentalPointCycle_apply]
  by_cases hy : y ∈ genericPoints B
  · rw [dite_eq_left hy, toPoints_finitePushforward_fundamentalCycle]
    exact hdegree ⟨y, hy⟩
  · rw [dite_eq_right hy, mul_zero]
    exact toPoints_finitePushforward_fundamentalCycle_eq_zero_of_not_generic
      a hgeneric y hy

end GlobalCycles

section ActualPointClosure

open _root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (x : X)
  {X' Y' : Scheme.{u}} {i : X' ⟶ (pointClosure x).val.subscheme}
  {f' : X' ⟶ Y'} {g : Y' ⟶ (pointClosure (f x)).val.subscheme}
  (sq : IsPullback i f' (pointClosureMap f x) g)
  [IsNoetherian X'] [IsNoetherian Y']

/-- Global cycle realization for an actual Cartesian base change of the
actual finite point-closure map. Both geometric genericity inputs are explicit.
The actual SmoothSite consumer proves them, rather than adding hypotheses. -/
theorem finitePushforward_fundamentalCycle_pointClosure_baseChange
    (hgeneric : ∀ w : genericPoints X', f' w.1 ∈ genericPoints Y')
    (hprojection : ∀ y : genericPoints Y',
      g y.1 = genericPoint (pointClosure (f x)).val.subscheme) :
    letI : IsFinite f' := MorphismProperty.of_isPullback sq inferInstance
    IntegralCycle.finitePushforward f' (fundamentalCycle X') =
      (f.residueDegree x : ℤ) • fundamentalCycle Y' := by
  let : IsFinite f' := MorphismProperty.of_isPullback sq inferInstance
  exact finitePushforward_fundamentalCycle_of_degreeLength f' hgeneric _
    (fun y => actualGenericFiberDegreeLengthSum_eq f x sq y (hprojection y))

end ActualPointClosure

end AlgebraicGeometry.Scheme.Cycles.BaseChange.Pushforward
