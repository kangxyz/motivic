/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.PrincipalOrderCycle
public import Motivic.AlgebraicGeometry.Correspondences.FiniteFlat

/-!
# Principal orders as actual finite correspondences

The original function-field orders weight the finite images of their actual
integral supports. Finiteness and component dominance are proved from the
proper compactification, the retained smooth relative curve, and the specified
whole boundary unit neighborhood. No flatness of the supports is assumed.
Distinct supports with the same image contribute additively, with their actual
residue degrees. This is a correspondence producer, not a principal-divisor
A1 relation or a standard-triple nullhomotopy theorem.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

universe u

namespace Motivic.PrincipalOrderCorrespondence

variable {k : Type u} [Field k] {X Y : SmoothSite (Spec (.of k))}
  [IsAffine X.left] {C V : Scheme.{u}} [IsIntegral C] [IsNoetherian C]
  [V.IsQuasiAffine] (q : C ⟶ X.left) [IsProper q]
  (j : V ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
  (U : C.Opens) [Nonempty U] (hU : (Set.range j)ᶜ ⊆ (U : Set C))
  (h : Γ(C, U)) (hh : IsUnit h)
  (g : V ⟶ Y.left) (hbase : j ≫ q ≫ X.hom = g ≫ Y.hom)

/-- The actual integral closure of an original nonzero order point. -/
abbrev supportScheme (x : (principalOrderCycle U h hh).support) : Scheme.{u} :=
  (IntegralClosedSubscheme.pointClosure x.val).val.subscheme

include hU in
omit [V.IsQuasiAffine] [IsOpenImmersion j] in
/-- The whole support lies in the retained open, not merely its generic point. -/
theorem support_range (x : (principalOrderCycle U h hh).support) :
    Set.range (IntegralClosedSubscheme.pointClosure x.val).val.subschemeι ⊆ Set.range j := by
  rw [Scheme.IdealSheafData.range_subschemeι, IntegralClosedSubscheme.support_pointClosure]
  have hx : x.val ∉ U := fun hm =>
    (Finsupp.mem_support_iff.mp x.property) (principalOrderCycle_eq_zero_on_open U h hh hm)
  have hc : closure ({x.val} : Set C) ⊆ (U : Set C)ᶜ :=
    closure_minimal (Set.singleton_subset_iff.mpr hx) U.isOpen.isClosed_compl
  intro y hy
  by_contra hn
  exact hc hy (hU hn)

/-- The literal support-to-product map, through the prescribed retained open. -/
def productMap (x : (principalOrderCycle U h hh).support) :
    supportScheme U h hh x ⟶ pullback X.hom Y.hom := by
  let d := (IntegralClosedSubscheme.pointClosure x.val).val.subschemeι
  let a := IsOpenImmersion.lift j d (support_range j U hU h hh x)
  have ha : a ≫ j = d := IsOpenImmersion.lift_fac j d _
  exact pullback.lift (d ≫ q) (a ≫ g) (by
    rw [← ha]
    simp only [Category.assoc, hbase])

omit [IsAffine X.left] [IsProper q] [SmoothOfRelativeDimension 1 (j ≫ q)] [V.IsQuasiAffine] in
@[simp]
theorem productMap_fst (x : (principalOrderCycle U h hh).support) :
    productMap q j U hU h hh g hbase x ≫ pullback.fst X.hom Y.hom =
      (IntegralClosedSubscheme.pointClosure x.val).val.subschemeι ≫ q :=
  pullback.lift_fst _ _ _

/-- Actual finiteness of the product map, without support flatness. -/
instance productMap_isFinite (x : (principalOrderCycle U h hh).support) :
    IsFinite (productMap q j U hU h hh g hbase x) := by
  have := principalOrderCycle_support_isFinite q j U hU h hh x.val
    (Finsupp.mem_support_iff.mp x.property)
  exact FiniteFlatCorrespondence.isFinite_productMap _ _
    (productMap_fst q j U hU h hh g hbase x)

/-- The literal finite image, with its component dominance proved geometrically. -/
def generator (x : (principalOrderCycle U h hh).support) :
    FiniteCorrespondenceGenerator X.hom Y.hom := by
  let e := productMap q j U hU h hh g hbase x
  have : IsFinite (e ≫ pullback.fst X.hom Y.hom) := by
    rw [productMap_fst]
    exact principalOrderCycle_support_isFinite q j U hU h hh x.val
      (Finsupp.mem_support_iff.mp x.property)
  refine ⟨e.ker, isIntegral_finiteImage e,
    isFinite_image_projection e (pullback.fst X.hom Y.hom), ?_⟩
  change Set.range (e.imageι ≫ pullback.fst X.hom Y.hom) ∈ _
  rw [range_image_projection, productMap_fst]
  exact principalOrderCycle_support_dominates_component q j U hU h hh x.val
    (Finsupp.mem_support_iff.mp x.property)

/-- The signed principal correspondence in the existing correspondence category. -/
def correspondence : Cor.mk X ⟶ Cor.mk Y := by
  classical
  exact ∑ x : (principalOrderCycle U h hh).support,
    Finsupp.single (generator q j U hU h hh g hbase x)
      (C.ord (C.germToFunctionField U h) x.val *
        ((productMap q j U hU h hh g hbase x).residueDegree
          (genericPoint (supportScheme U h hh x)) : ℤ))

open Classical in
/-- The coefficient formula keeps every original order and finite residue degree,
including collisions between images of different original support points. -/
theorem correspondence_coefficient (W : FiniteCorrespondenceGenerator X.hom Y.hom) :
    (show FiniteCorrespondence X.hom Y.hom from
      correspondence q j U hU h hh g hbase) W =
      ∑ x : (principalOrderCycle U h hh).support,
        if generator q j U hU h hh g hbase x = W then
          C.ord (C.germToFunctionField U h) x.val *
            ((productMap q j U hU h hh g hbase x).residueDegree
              (genericPoint (supportScheme U h hh x)) : ℤ)
        else 0 := by
  change (∑ x : (principalOrderCycle U h hh).support,
    Finsupp.single (generator q j U hU h hh g hbase x)
      (C.ord (C.germToFunctionField U h) x.val *
        ((productMap q j U hU h hh g hbase x).residueDegree
          (genericPoint (supportScheme U h hh x)) : ℤ))) W = _
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]

end Motivic.PrincipalOrderCorrespondence
