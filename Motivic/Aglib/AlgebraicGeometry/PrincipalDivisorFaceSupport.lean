/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.PrincipalDivisorFaceCoefficient

/-!
# Support-complete coefficients at original principal-divisor faces

The original weighted component fibers are pushed into the common ambient
scheme. At an actual face point, an absent double-fiber preimage forces the
numerator ideal to be the whole stalk ring. Its scalar cokernel and all pushed
coefficients therefore vanish; no point upstairs is invented.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Motivic
open scoped BigOperators Polynomial

universe u

namespace AlgebraicGeometry.FiniteFlatCurve

variable {k : Type u} [Field k]

/-- The literal original component weights followed by their entire fibers. -/
def weightedComponentFiberCycle {D : Scheme.{u}} [IsNoetherian D]
    (f : D ⟶ Spec (.of k[X])) (a : k) : IntegralCycle D := by
  classical
  let := IntegralCycle.genericPointFintype D
  exact ∑ z : genericPoints D, (genericMultiplicity z : ℤ) •
    IntegralCycle.finitePushforward
      (fiberMap f a (IntegralClosedSubscheme.pointClosure z.1).val.subschemeι ≫
        fiberInclusion f a)
      (fundamentalCycle
        (fiber ((IntegralClosedSubscheme.pointClosure z.1).val.subschemeι ≫ f) a))

/-- The original weighted numerator-face cycle in its unchanged ambient scheme. -/
def principalDivisorFaceCycle {P : Scheme.{u}} [IsNoetherian P]
    (n f : P ⟶ Spec (.of k[X])) (a : k) : IntegralCycle P :=
  IntegralCycle.finitePushforward (fiberInclusion n 0)
    (weightedComponentFiberCycle (fiberInclusion n 0 ≫ f) a)

private theorem coefficient_closed_pushforward {D P : Scheme.{u}}
    (i : D ⟶ P) [IsClosedImmersion i] (c : IntegralCycle D) (x : D) :
    IntegralCycle.toPoints (IntegralCycle.finitePushforward i c) (i x) =
      IntegralCycle.toPoints c x := by
  rw [IntegralCycle.toPoints_finitePushforward_apply,
    residuePushforward_eq_mapDomain_of_surjectiveOnStalks]
  change Finsupp.mapDomain i (IntegralCycle.toPoints c) (i x) = _
  exact Finsupp.mapDomain_apply_of_injective i.isEmbedding.injective _ _

private theorem closed_stalk_quotient_length {D P : Scheme.{u}}
    (i : D ⟶ P) [IsClosedImmersion i] (x : D) :
    Module.length (P.presheaf.stalk (i x))
      ((P.presheaf.stalk (i x)) ⧸ i.ker.stalk (i x)) =
      Module.length (D.presheaf.stalk x) (D.presheaf.stalk x) := by
  rw [i.ker_stalk]
  exact (Module.length_eq_of_surjective
    (Ideal.Quotient.mk_surjective (I := RingHom.ker (i.stalkMap x).hom))).trans
      (ringLength_eq_of_ringEquiv (stalkQuotientKerEquiv i x))

variable {P : Scheme.{u}} [IsNoetherian P]
  (n f : P ⟶ Spec (.of k[X])) (a : k)

/-- The support-complete coefficient formula at an actual face point.
Finite double-cut length supplies genuine genericity in the nonempty case;
in the empty case the numerator quotient is zero. -/
theorem principalDivisorFaceCycle_coefficient
    (x : fiber f a)
    (hcut : Module.length (P.presheaf.stalk (fiberInclusion f a x))
      ((P.presheaf.stalk (fiberInclusion f a x)) ⧸
        (Ideal.ofList [scalar f a (fiberInclusion f a x)] ⊔
          Ideal.ofList [scalar n 0 (fiberInclusion f a x)])) ≠ ⊤)
    (hregular : ∀ (y : fiber (fiberInclusion n 0 ≫ f) a),
      (fiberInclusion (fiberInclusion n 0 ≫ f) a ≫ fiberInclusion n 0) y =
          fiberInclusion f a x →
      ∀ z : genericPoints (fiber n 0),
        IsSMulRegular
          (((fiber n 0).presheaf.stalk (fiberInclusion (fiberInclusion n 0 ≫ f) a y)) ⧸
            (IntegralClosedSubscheme.pointClosure z.1).val.subschemeι.ker.stalk
              (fiberInclusion (fiberInclusion n 0 ≫ f) a y))
          (scalar (fiberInclusion n 0 ≫ f) a
            (fiberInclusion (fiberInclusion n 0 ≫ f) a y))) :
    IntegralCycle.toPoints (principalDivisorFaceCycle n f a) (fiberInclusion f a x) =
      Module.principalEuler
        (N := Module.ScalarCokernel (P.presheaf.stalk (fiberInclusion f a x))
          (scalar n 0 (fiberInclusion f a x)))
        (scalar f a (fiberInclusion f a x)) := by
  classical
  let i := fiberInclusion (fiberInclusion n 0 ≫ f) a ≫ fiberInclusion n 0
  have hi : i.ker.stalk (fiberInclusion f a x) =
      Ideal.ofList [scalar f a (fiberInclusion f a x)] ⊔
        Ideal.ofList [scalar n 0 (fiberInclusion f a x)] := by
    dsimp only [i]
    rw [← fiberMap_inclusion, fiberMap_composite_stalk, fiberInclusion_stalk]
  by_cases hx : fiberInclusion f a x ∈ Set.range i
  · obtain ⟨y, hy⟩ := hx
    have hcy : Module.length
        ((fiber n 0).presheaf.stalk (fiberInclusion (fiberInclusion n 0 ≫ f) a y))
        (((fiber n 0).presheaf.stalk (fiberInclusion (fiberInclusion n 0 ≫ f) a y)) ⧸
          Ideal.ofList [scalar (fiberInclusion n 0 ≫ f) a
            (fiberInclusion (fiberInclusion n 0 ≫ f) a y)]) ≠ ⊤ := by
      rw [← fiber_stalk_length]
      have hh := hcut
      rw [← hi, ← hy, closed_stalk_quotient_length i y] at hh
      exact hh
    have he := weighted_principal_divisor_face_coefficient n f a y hcy (hregular y hy)
    rw [← hy]
    unfold principalDivisorFaceCycle
    change IntegralCycle.toPoints
      (IntegralCycle.finitePushforward (fiberInclusion n 0)
        (weightedComponentFiberCycle (fiberInclusion n 0 ≫ f) a))
      (fiberInclusion n 0 (fiberInclusion (fiberInclusion n 0 ≫ f) a y)) = _
    rw [coefficient_closed_pushforward]
    change IntegralCycle.toPoints
      (weightedComponentFiberCycle (fiberInclusion n 0 ≫ f) a)
      (fiberInclusion (fiberInclusion n 0 ≫ f) a y) =
      Module.principalEuler
        (N := Module.ScalarCokernel
          (P.presheaf.stalk (fiberInclusion n 0
            (fiberInclusion (fiberInclusion n 0 ≫ f) a y)))
          (scalar n 0 (fiberInclusion n 0
            (fiberInclusion (fiberInclusion n 0 ≫ f) a y))))
        (scalar f a (fiberInclusion n 0
          (fiberInclusion (fiberInclusion n 0 ≫ f) a y)))
    simpa only [weightedComponentFiberCycle, map_sum, map_zsmul,
      Finsupp.finsetSum_apply, Finsupp.smul_apply, zsmul_eq_mul, Int.cast_id] using he
  · have htop : Ideal.ofList [scalar f a (fiberInclusion f a x)] ⊔
        Ideal.ofList [scalar n 0 (fiberInclusion f a x)] = ⊤ :=
      hi.symm.trans (closedImmersion_ker_stalk_eq_top i hx)
    have hn : Ideal.ofList [scalar n 0 (fiberInclusion f a x)] = ⊤ := by
      by_contra hn
      have hc : Ideal.ofList [scalar f a (fiberInclusion f a x)] ≤
          IsLocalRing.maximalIdeal (P.presheaf.stalk (fiberInclusion f a x)) := by
        rw [Ideal.ofList_singleton]
        exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (scalar_mem_maximalIdeal f a x))
      have hh := sup_le hc (IsLocalRing.le_maximalIdeal hn)
      rw [htop, top_le_iff] at hh
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top hh
    have : Subsingleton ((P.presheaf.stalk (fiberInclusion f a x)) ⧸
        Ideal.ofList [scalar n 0 (fiberInclusion f a x)]) :=
      Ideal.Quotient.subsingleton_iff.mpr hn
    have : Subsingleton (Module.ScalarCokernel (P.presheaf.stalk (fiberInclusion f a x))
        (scalar n 0 (fiberInclusion f a x))) :=
      (Koszul.singleQuotientRingEquiv (scalar n 0 (fiberInclusion f a x))).injective.subsingleton
    rw [Module.principalEuler_zero_of_finite_length _ Module.length_ne_top]
    unfold principalDivisorFaceCycle weightedComponentFiberCycle
    rw [map_sum, map_sum]
    simp only [map_zsmul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
      zsmul_eq_mul, Int.cast_id]
    apply Finset.sum_eq_zero
    intro z _
    let m := fiberMap (fiberInclusion n 0 ≫ f) a
      (IntegralClosedSubscheme.pointClosure z.1).val.subschemeι ≫
        fiberInclusion (fiberInclusion n 0 ≫ f) a
    have hcomp (v : IntegralCycle _) :
        IntegralCycle.finitePushforward (fiberInclusion n 0)
            (IntegralCycle.finitePushforward m v) =
          IntegralCycle.finitePushforward (m ≫ fiberInclusion n 0) v := by
      dsimp only [m]
      simp only [IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply]
    rw [hcomp]
    rw [closedImmersion_fundamentalCoefficient_eq_zero_at _ _ ?_, mul_zero]
    intro w hw _
    apply hx
    refine ⟨fiberMap (fiberInclusion n 0 ≫ f) a
      (IntegralClosedSubscheme.pointClosure z.1).val.subschemeι w, ?_⟩
    exact hw

end AlgebraicGeometry.FiniteFlatCurve
