/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Stalk.KernelMinimalPrimes
public import Motivic.Aglib.AlgebraicGeometry.Cycles.ClosedImmersionGenericCycleCoefficient
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Actual component stalk kernels and scalar regularity

An original generic component's closed-immersion kernel is a minimal prime in
an ambient stalk on that component. This follows from the actual stalk-spectrum
map and its naturality, not from a supplied component identification. Outside
the component, the original ideal-sheaf stalk is the whole ring. The ambient
scheme may be nonreduced and need not be Noetherian.


Intended upstream module: `Aglib.AlgebraicGeometry.Cycles.Multiplicity.ComponentStalkRegularity`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyComponentRegularity`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- At a point on the original generic component, its literal ideal-sheaf
stalk is a minimal prime of the original, possibly nonreduced ambient stalk. -/
theorem component_kernel_stalk_mem_minimalPrimes {D : Scheme.{u}}
    (z : genericPoints D)
    (y : (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure z.1).val.subscheme) :
    (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure
        z.1).val.subschemeι.ker.stalk
        ((_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure z.1).val.subschemeι
            y) ∈
      minimalPrimes (D.presheaf.stalk
        ((_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure z.1).val.subschemeι
            y)) := by
  let C := (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure z.1).val.subscheme
  let j : C ⟶ D := (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure
      z.1).val.subschemeι
  let p : Spec (D.presheaf.stalk (j y)) :=
    Spec.map (j.stalkMap y) (⊥ : PrimeSpectrum (C.presheaf.stalk y))
  have hzero : (⊥ : PrimeSpectrum (C.presheaf.stalk y)) ∈
      genericPoints (Spec (C.presheaf.stalk y)) := by
    simp only [genericPoints_eq_singleton, genericPoint_eq_bot_of_affine,
      Set.mem_singleton_iff]
  have hc : C.fromSpecStalk y (⊥ : PrimeSpectrum (C.presheaf.stalk y)) =
      genericPoint C := by
    have hg := (_root_.AlgebraicGeometry.Scheme.fromSpecStalk_mem_genericPoints_iff C y _).mpr hzero
    simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hg
  have hp : D.fromSpecStalk (j y) p = z.1 := by
    change (Spec.map (j.stalkMap y) ≫ D.fromSpecStalk (j y))
      (⊥ : PrimeSpectrum (C.presheaf.stalk y)) = z.1
    rw [Scheme.SpecMap_stalkMap_fromSpecStalk]
    change j (C.fromSpecStalk y (⊥ : PrimeSpectrum (C.presheaf.stalk y))) = z.1
    rw [hc]
    exact _root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.point_pointClosure z.1
  have hgeneric : p ∈ genericPoints (Spec (D.presheaf.stalk (j y))) :=
    (_root_.AlgebraicGeometry.Scheme.fromSpecStalk_mem_genericPoints_iff D (j y) p).mp (hp.symm ▸
        z.2)
  have hminimal := (_root_.AlgebraicGeometry.Scheme.spec_mem_genericPoints_iff_minimalPrime
    (D.presheaf.stalk (j y)) p).mp hgeneric
  change j.ker.stalk (j y) ∈ minimalPrimes (D.presheaf.stalk (j y))
  rw [j.ker_stalk]
  exact hminimal

/-- A regular original stalk scalar remains regular on each actual generic
component quotient. Missing components give the literal zero quotient. -/
theorem component_quotient_regular_of_stalk_regular {D : Scheme.{u}}
    (x : D) (r : D.presheaf.stalk x) (hr : IsSMulRegular (D.presheaf.stalk x) r)
    (z : genericPoints D) :
    IsSMulRegular ((D.presheaf.stalk x) ⧸
      (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure
          z.1).val.subschemeι.ker.stalk x) r := by
  let j := (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure z.1).val.subschemeι
  change IsSMulRegular ((D.presheaf.stalk x) ⧸ j.ker.stalk x) r
  by_cases hx : x ∈ Set.range j
  · obtain ⟨y, rfl⟩ := hx
    have hm := component_kernel_stalk_mem_minimalPrimes z y
    have hn : r ∉ j.ker.stalk (j y) := hr.notMem_of_mem_minimalPrimes (by
      simpa only [Module.annihilator_eq_bot.mpr inferInstance] using hm)
    apply (isSMulRegular_quotient_iff_mem_of_smul_mem (j.ker.stalk (j y)) r).mpr
    intro a ha
    exact (hm.1.1.mem_or_mem ha).resolve_left hn
  · have : Subsingleton ((D.presheaf.stalk x) ⧸ j.ker.stalk x) :=
      Ideal.Quotient.subsingleton_iff.mpr
          (_root_.AlgebraicGeometry.Scheme.Hom.closedImmersion_ker_stalk_eq_top j hx)
    exact fun _ _ _ => Subsingleton.elim _ _

end AlgebraicGeometry.Scheme
