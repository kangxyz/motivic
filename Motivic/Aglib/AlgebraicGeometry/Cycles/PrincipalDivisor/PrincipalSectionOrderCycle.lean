/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyZeroCoefficient
public import Motivic.Aglib.AlgebraicGeometry.Divisors.Order.PrincipalOrderCancellation
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Divisors.Frame.Support

/-!
# The whole zero scheme of a section has its native order cycle

The literal zero fiber of the canonical section map retains its nonreduced
multiplicities. Genericity and codimension one are derived from its actual
principal stalk quotient, not supplied as comparison hypotheses.


Intended upstream module:
`Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.PrincipalSectionOrderCycle`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.PrincipalFamilySignedOrderCycle`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Order
open AlgebraicGeometry.FiniteFlatCurve

universe u

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {P : Scheme.{u}} [IsIntegral P] [IsNoetherian P]
  (p : P ⟶ Spec (.of k)) (s : Γ(P, ⊤)) (hs : s ≠ 0)

omit [AlgebraicGeometry.IsIntegral P] [AlgebraicGeometry.IsNoetherian P] in
private theorem section_zero_kernel (x : P) :
    (fiberInclusion (Scheme.sectionToAffineLine p s) 0).ker.stalk x =
      Ideal.span {P.presheaf.germ ⊤ x (by trivial) s} := by
  rw [fiberInclusion_stalk, Ideal.ofList_singleton, Scheme.sectionToAffineLine_zero_scalar]

include hs

/-- Each actual generic point of the whole zero divisor has ambient coheight one. -/
theorem section_zero_generic_coheight
    (y : fiber (Scheme.sectionToAffineLine p s) 0)
    (hy : y ∈ genericPoints (fiber (Scheme.sectionToAffineLine p s) 0)) :
    coheight (fiberInclusion (Scheme.sectionToAffineLine p s) 0 y) = 1 := by
  let i := fiberInclusion (Scheme.sectionToAffineLine p s) 0
  let r := P.presheaf.germ ⊤ (i y) (show i y ∈ (⊤ : P.Opens) from trivial) s
  have hr : r ≠ 0 :=
    (map_ne_zero_iff (P.presheaf.germ ⊤ (i y) (by trivial)).hom
      (germ_injective_of_isIntegral P (i y) (by trivial))).mpr hs
  have hk : i.ker.stalk (i y) = Ideal.span {r} := section_zero_kernel p s (i y)
  let E : ((P.presheaf.stalk (i y)) ⧸ Ideal.span {r}) ≃+*
      (fiber (Scheme.sectionToAffineLine p s) 0).presheaf.stalk y :=
    (Ideal.quotEquivOfEq (hk.symm.trans (i.ker_stalk y))).trans
        (_root_.AlgebraicGeometry.Scheme.stalkQuotientKerEquiv i y)
  have : IsArtinianRing ((fiber (Scheme.sectionToAffineLine p s) 0).presheaf.stalk y) :=
    _root_.AlgebraicGeometry.Scheme.isArtinianRing_stalk_of_mem_genericPoints y hy
  have : IsArtinianRing ((P.presheaf.stalk (i y)) ⧸ Ideal.span {r}) := E.symm.isArtinianRing
  have : Nontrivial ((P.presheaf.stalk (i y)) ⧸ Ideal.span {r}) := E.toEquiv.nontrivial
  have : Ring.KrullDimLE 0 ((P.presheaf.stalk (i y)) ⧸ Ideal.span {r}) :=
    isArtinianRing_iff_krullDimLE_zero.mp inferInstance
  have hd0 : ringKrullDim ((P.presheaf.stalk (i y)) ⧸ Ideal.span {r}) = 0 :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance
  have hz : (i.stalkMap y).hom r = 0 := by
    change r ∈ RingHom.ker (i.stalkMap y).hom
    rw [← i.ker_stalk, hk]
    exact Ideal.subset_span (Set.mem_singleton r)
  have hnu : ¬ IsUnit r := fun hu => (hu.map (i.stalkMap y).hom).ne_zero hz
  have hjac : r ∈ Ring.jacobson (P.presheaf.stalk (i y)) := by
    rwa [IsLocalRing.ringJacobson_eq_maximalIdeal, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff]
  have hd := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_jacobson
    (IsSMulRegular.of_ne_zero hr) hjac
  rw [hd0, zero_add, ringKrullDim_stalk_eq_coheight] at hd
  exact_mod_cast hd.symm

/-- A point of the actual zero divisor above ambient coheight one is generic. -/
theorem section_zero_generic_of_coheight
    (y : fiber (Scheme.sectionToAffineLine p s) 0)
    (hy : coheight (fiberInclusion (Scheme.sectionToAffineLine p s) 0 y) = 1) :
    y ∈ genericPoints (fiber (Scheme.sectionToAffineLine p s) 0) := by
  let i := fiberInclusion (Scheme.sectionToAffineLine p s) 0
  have : Ring.KrullDimLE 1 (P.presheaf.stalk (i y)) := krullDimLE_of_coheight_le hy.le
  have hr : P.presheaf.germ ⊤ (i y) (by trivial) s ≠ 0 :=
    (map_ne_zero_iff (P.presheaf.germ ⊤ (i y) (by trivial)).hom
      (germ_injective_of_isIntegral P (i y) (by trivial))).mpr hs
  have hl : IsFiniteLength (P.presheaf.stalk (i y))
      ((P.presheaf.stalk (i y)) ⧸ i.ker.stalk (i y)) := by
    rw [section_zero_kernel p s]
    exact isFiniteLength_quotient_span_singleton _ (mem_nonZeroDivisors_iff_ne_zero.mpr hr)
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hl
  have : IsArtinianRing ((P.presheaf.stalk (i y)) ⧸ i.ker.stalk (i y)) :=
    isArtinian_of_tower (P.presheaf.stalk (i y)) inferInstance
  have : IsArtinianRing ((fiber (Scheme.sectionToAffineLine p s) 0).presheaf.stalk y) :=
    ((Ideal.quotEquivOfEq (i.ker_stalk y)).trans
        (_root_.AlgebraicGeometry.Scheme.stalkQuotientKerEquiv i y)).isArtinianRing
  have : Ring.KrullDimLE 0 ((fiber (Scheme.sectionToAffineLine p s) 0).presheaf.stalk y) :=
    isArtinianRing_iff_krullDimLE_zero.mp inferInstance
  apply _root_.AlgebraicGeometry.Scheme.mem_genericPoints_of_coheight_eq_zero
  have hd : ringKrullDim ((fiber (Scheme.sectionToAffineLine p s) 0).presheaf.stalk y) = 0 :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance
  rw [ringKrullDim_stalk_eq_coheight] at hd
  exact_mod_cast hd

/-- All original zero-divisor coefficients equal the native order, including
points outside the zero scheme and every nonreduced generic multiplicity. -/
theorem section_zero_fundamentalCoefficient_eq_ord (x : P) :
    letI : Nonempty (⊤ : P.Opens) := ⟨⟨x, TopologicalSpace.Opens.mem_top x⟩⟩
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (fiberInclusion
          (Scheme.sectionToAffineLine p s) 0)
        (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber (Scheme.sectionToAffineLine p s)
            0))) x =
      P.ord (P.germToFunctionField ⊤ s) x := by
  let : Nonempty (⊤ : P.Opens) := ⟨⟨x, TopologicalSpace.Opens.mem_top x⟩⟩
  by_cases hx : coheight x = 1
  · rw [closedImmersion_fundamentalCoefficient_eq_length_at _ _ (by
      intro y hy
      apply section_zero_generic_of_coheight p s hs y
      simpa only [hy] using hx), section_zero_kernel p s,
      P.ord_germ_eq_quotient_length ⊤ s hs (by trivial) hx]
  · rw [closedImmersion_fundamentalCoefficient_eq_zero_at _ _ (by
      intro y hy hg
      apply hx
      simpa only [hy] using section_zero_generic_coheight p s hs y hg),
      Scheme.ord_eq_zero_of_coheight_neq_one hx]

end AlgebraicGeometry.Scheme
