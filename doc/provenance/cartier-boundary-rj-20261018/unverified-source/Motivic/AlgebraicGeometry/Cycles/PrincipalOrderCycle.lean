/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Motivic.AlgebraicGeometry.Cycles.FiniteSupport
public import Motivic.AlgebraicGeometry.Cycles.FundamentalSupport
public import Motivic.AlgebraicGeometry.Cycles.CodimensionOneDominance
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.BoundaryNeighborhoodComplement

/-!
# The finite principal order cycle of a boundary-unit rational function

The coefficients are the native function-field orders, not supplied cycle data.
A nonempty open on which the given function is a unit proves finite support.
For a proper relative curve, the actual reduced closure of each support point
is finite over the unchanged affine base when the open contains its boundary.
The retained smooth relative-curve hypothesis also proves component dominance.
Assembly into the correspondence category and its A1 relation remain separate.
Integrality is explicit; componentwise assembly for a disconnected normal scheme is not hidden.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Order

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]

/-- The original rational function has only finitely many nonzero orders when
it is a unit on the specified nonempty open. -/
theorem finite_support_ord_of_unit_on_open (U : X.Opens) [Nonempty U]
    (h : Γ(X, U)) (hh : IsUnit h) :
    (Function.support (X.ord (X.germToFunctionField U h))).Finite := by
  let p : Set X := (U : Set X)ᶜ
  have hp : IsClosed p := U.isOpen.isClosed_compl
  have : QuasiSober p := hp.isClosedEmbedding_subtypeVal.quasiSober
  have hproper : closure p ≠ Set.univ := by
    rw [hp.closure_eq]
    obtain ⟨x⟩ := ‹Nonempty U›
    intro he
    have hx : x.1 ∈ p := he.symm ▸ Set.mem_univ x.1
    exact hx x.2
  apply (NoetherianSpace.finite_coheight_one_of_closure_ne_univ hproper).subset
  intro x hx
  refine ⟨?_, ?_⟩
  · intro hxU
    exact hx (X.ord_of_isUnit hh hxU)
  · by_contra hn
    exact hx (X.ord_eq_zero_of_coheight_neq_one hn _)

end AlgebraicGeometry.Scheme

namespace Motivic

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]

/-- The actual principal order cycle, with its finite support proved from the
specified unit neighborhood. -/
def principalOrderCycle (U : X.Opens) [Nonempty U] (h : Γ(X, U)) (hh : IsUnit h) :
    FiniteSupportCycle X :=
  Finsupp.ofSupportFinite (X.ord (X.germToFunctionField U h))
    (X.finite_support_ord_of_unit_on_open U h hh)

@[simp]
theorem principalOrderCycle_apply (U : X.Opens) [Nonempty U]
    (h : Γ(X, U)) (hh : IsUnit h) (x : X) :
    principalOrderCycle U h hh x = X.ord (X.germToFunctionField U h) x := rfl

/-- No order coefficient is supported on the original whole unit neighborhood. -/
theorem principalOrderCycle_eq_zero_on_open (U : X.Opens) [Nonempty U]
    (h : Γ(X, U)) (hh : IsUnit h) {x : X} (hx : x ∈ U) :
    principalOrderCycle U h hh x = 0 :=
  X.ord_of_isUnit hh hx

/-- Every actual integral support of the principal cycle is finite over the
unchanged affine base. No finite-flat or dominance input is substituted. -/
theorem principalOrderCycle_support_isFinite
    {S V : Scheme.{u}} [IsAffine S] [V.IsQuasiAffine]
    (q : X ⟶ S) [IsProper q] (j : V ⟶ X) [IsOpenImmersion j]
    (U : X.Opens) [Nonempty U] (hU : (Set.range j)ᶜ ⊆ (U : Set X))
    (h : Γ(X, U)) (hh : IsUnit h) (x : X)
    (hx : principalOrderCycle U h hh x ≠ 0) :
    IsFinite ((IntegralClosedSubscheme.pointClosure x).val.subschemeι ≫ q) := by
  apply Scheme.RelativeCurve.isFinite_closed_support_in_quasiAffine_open q j
  rw [Scheme.IdealSheafData.range_subschemeι,
    IntegralClosedSubscheme.support_pointClosure]
  have hxU : x ∉ U := fun hm => hx (principalOrderCycle_eq_zero_on_open U h hh hm)
  have hc : closure ({x} : Set X) ⊆ (U : Set X)ᶜ :=
    closure_minimal (Set.singleton_subset_iff.mpr hxU) U.isOpen.isClosed_compl
  intro y hy
  by_contra hn
  exact hc hy (hU hn)

/-- Every nonzero principal-order support dominates a base component. The
smooth curve is only the retained open; its coheight is transferred through
that original open immersion rather than assumed on the compactification. -/
theorem principalOrderCycle_support_dominates_component
    {S V : Scheme.{u}} [IsAffine S] [V.IsQuasiAffine]
    (q : X ⟶ S) [IsProper q] (j : V ⟶ X) [IsOpenImmersion j]
    [SmoothOfRelativeDimension 1 (j ≫ q)]
    (U : X.Opens) [Nonempty U] (hU : (Set.range j)ᶜ ⊆ (U : Set X))
    (h : Γ(X, U)) (hh : IsUnit h) (x : X)
    (hx : principalOrderCycle U h hh x ≠ 0) :
    Set.range ((IntegralClosedSubscheme.pointClosure x).val.subschemeι ≫ q) ∈
      irreducibleComponents S := by
  let D := IntegralClosedSubscheme.pointClosure x
  let d := D.val.subschemeι
  have hd : Set.range d ⊆ Set.range j := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      IntegralClosedSubscheme.support_pointClosure]
    have hxU : x ∉ U := fun hm => hx (principalOrderCycle_eq_zero_on_open U h hh hm)
    have hc : closure ({x} : Set X) ⊆ (U : Set X)ᶜ :=
      closure_minimal (Set.singleton_subset_iff.mpr hxU) U.isOpen.isClosed_compl
    intro y hy
    by_contra hn
    exact hc hy (hU hn)
  let i := IsOpenImmersion.lift j d hd
  have hi : i ≫ j = d := IsOpenImmersion.lift_fac j d hd
  have : IsClosedImmersion (i ≫ j) := by rw [hi]; infer_instance
  have : IsClosedImmersion i := IsClosedImmersion.of_comp i j
  have : IsFinite (d ≫ q) := principalOrderCycle_support_isFinite q j U hU h hh x hx
  have hcomp : i ≫ (j ≫ q) = d ≫ q := by rw [← Category.assoc, hi]
  have : IsFinite (i ≫ (j ≫ q)) := by rw [hcomp]; infer_instance
  let a := genericPoint D.val.subscheme
  have hda : d a = x := IntegralClosedSubscheme.point_pointClosure x
  have hx1 : coheight x = 1 := by
    by_contra hn
    exact hx (Scheme.ord_eq_zero_of_coheight_neq_one hn _)
  have ha : coheight (i a) = 1 := by
    rw [← Scheme.coheight_eq_of_isOpenImmersion j]
    change coheight ((i ≫ j) a) = 1
    rw [hi, hda]
    exact hx1
  have hg := image_mem_genericPoints_of_coheight_one_finite_closed_support i (j ≫ q) a ha
  have hga : (j ≫ q) (i a) = (d ≫ q) a :=
    congrArg (fun f : D.val.subscheme ⟶ S => f a) hcomp
  rw [hga] at hg
  have he : closure ({(d ≫ q) a} : Set S) = Set.range (d ≫ q) := by
    simpa only [Set.image_univ, (d ≫ q).isClosedMap.isClosed_range.closure_eq] using
      ((genericPoint_spec D.val.subscheme).image (d ≫ q).continuous).def
  rwa [genericPoints, Set.mem_setOf_eq, he] at hg

end Motivic
