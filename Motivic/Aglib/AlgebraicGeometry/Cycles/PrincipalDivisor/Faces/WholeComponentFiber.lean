/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.PrincipalDivisorFaceSupport
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Fundamental.Invariance

/-!
# Additive whole-component scalar fibers

Each actual integral closed support contributes the fundamental cycle of its
whole scalar fiber. Closed-immersion compatibility uses the original image
isomorphism and its literal pullback. No flatness or reduced fiber is assumed.
This is a formal weighted component operation, not arbitrary pullback of a
fundamental cycle; comparison with a whole nonreduced fiber requires the
separate checked Cartier/Euler and component-regularity arguments.


Intended upstream module:
`Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.WholeComponentFiber`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.WholeComponentFiberOpenRestriction`,
`Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.WholeComponentFiberProjection`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteFlatCurve
open scoped BigOperators

universe u

namespace AlgebraicGeometry.Scheme.IntegralCycle

variable {k : Type u} [Field k] {P D : Scheme.{u}} [IsNoetherian P]

/-- Additive specialization of each original integral support to its whole fiber. -/
def wholeComponentFiber (f : P ⟶ Spec (.of (Polynomial k))) (a : k) :
    _root_.AlgebraicGeometry.Scheme.IntegralCycle P →+ _root_.AlgebraicGeometry.Scheme.IntegralCycle
        P :=
  Finsupp.liftAddHom fun Z =>
    { toFun := fun n => n • _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward
        (fiberInclusion (Z.val.subschemeι ≫ f) a ≫ Z.val.subschemeι)
        (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber (Z.val.subschemeι ≫ f) a))
      map_zero' := by simp
      map_add' := by intro m n; simp only [add_smul] }

@[simp]
theorem wholeComponentFiber_single (f : P ⟶ Spec (.of (Polynomial k))) (a : k)
    (Z : _root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme P) (n : ℤ) :
    wholeComponentFiber f a (Finsupp.single Z n) =
      n • _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (fiberInclusion
          (Z.val.subschemeι ≫ f) a ≫ Z.val.subschemeι)
        (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber (Z.val.subschemeι ≫ f) a)) :=
  Finsupp.liftAddHom_apply_single _ _ _

/-- On the actual fundamental cycle the operation is precisely the existing
weighted component-fiber cycle, with its original generic lengths. -/
theorem wholeComponentFiber_fundamentalCycle (f : P ⟶ Spec (.of (Polynomial k))) (a : k) :
    wholeComponentFiber f a (_root_.AlgebraicGeometry.Scheme.fundamentalCycle P) =
        weightedComponentFiberCycle f a := by
  classical
  let := _root_.AlgebraicGeometry.Scheme.IntegralCycle.genericPointFintype P
  rw [← _root_.AlgebraicGeometry.Scheme.IntegralCycle.ofGenericCoefficients_genericMultiplicity,
      _root_.AlgebraicGeometry.Scheme.IntegralCycle.ofGenericCoefficients_eq_sum, map_sum]
  unfold weightedComponentFiberCycle
  apply Finset.sum_congr rfl
  intro z _
  rw [wholeComponentFiber_single]
  simp only [fiberMap_inclusion]

private theorem closed_image_component_fiber
    [IsNoetherian D] (i : D ⟶ P) [IsClosedImmersion i]
    (f : P ⟶ Spec (.of (Polynomial k))) (a : k) (Z :
        _root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme D) :
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward
        (fiberInclusion ((Z.finiteImage i).val.subschemeι ≫ f) a ≫
          (Z.finiteImage i).val.subschemeι)
        (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber ((Z.finiteImage i).val.subschemeι ≫
            f) a)) =
      _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward i
        (_root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (fiberInclusion
            (Z.val.subschemeι ≫ i ≫ f) a ≫ Z.val.subschemeι)
          (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber (Z.val.subschemeι ≫ i ≫ f) a)))
              := by
  let e := Z.val.subschemeι ≫ i
  let E : fiber (Z.val.subschemeι ≫ i ≫ f) a ≅ fiber (e.imageι ≫ f) a :=
    asIso (pullback.map _ _ _ _ (𝟙 _) e.toImage (𝟙 _)
      (by simp) (by simp [e, ← Category.assoc]))
  have hm : E.hom ≫ fiberInclusion (e.imageι ≫ f) a ≫ e.imageι =
      fiberInclusion (Z.val.subschemeι ≫ i ≫ f) a ≫ Z.val.subschemeι ≫ i := by
    simp only [E, asIso_hom, fiberInclusion, pullback.map, pullback.lift_snd_assoc,
      Category.assoc, Scheme.Hom.toImage_imageι]
    rfl
  change _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (fiberInclusion (e.imageι ≫
      f) a ≫ e.imageι)
      (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber (e.imageι ≫ f) a)) = _
  rw [← _root_.AlgebraicGeometry.Scheme.finitePushforward_fundamentalCycle E.hom, ←
      AddMonoidHom.comp_apply,
    ← _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward_comp]
  simp only [hm, ← Category.assoc,
      _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply]

/-- Closed-immersion transport preserves all original component fibers,
including their unreduced multiplicities. -/
theorem wholeComponentFiber_closed_pushforward
    [IsNoetherian D] (i : D ⟶ P) [IsClosedImmersion i]
    (f : P ⟶ Spec (.of (Polynomial k))) (a : k) (c : _root_.AlgebraicGeometry.Scheme.IntegralCycle
        D) :
    wholeComponentFiber f a (_root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward i c) =
      _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward i (wholeComponentFiber (i ≫ f)
          a c) := by
  have h : (wholeComponentFiber f a).comp
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward i) =
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward i).comp (wholeComponentFiber
          (i ≫ f) a) := by
    apply Finsupp.addHom_ext
    intro Z n
    simp only [AddMonoidHom.comp_apply,
        _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward_single,
      _root_.AlgebraicGeometry.Scheme.Hom.residueDegree_of_surjectiveOnStalks, Nat.cast_one,
          mul_one,
      wholeComponentFiber_single, map_zsmul]
    exact congrArg (fun z => n • z) (closed_image_component_fiber i f a Z)
  exact DFunLike.congr_fun h c

/-- The native principal-divisor face cycle is the specialization of its
actual pushed zero-divisor fundamental cycle. -/
theorem wholeComponentFiber_principalDivisor
    (n f : P ⟶ Spec (.of (Polynomial k))) (a : k) :
    wholeComponentFiber f a
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (fiberInclusion n 0)
          (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber n 0))) =
        principalDivisorFaceCycle n f a := by
  rw [wholeComponentFiber_closed_pushforward, wholeComponentFiber_fundamentalCycle]
  rfl

/-- The original signed divisor difference specializes to the existing
weighted face difference, without asserting that either equals an unweighted
whole fiber of the nonreduced divisor. -/
theorem wholeComponentFiber_signed_principalDivisor
    (n d f : P ⟶ Spec (.of (Polynomial k))) (a : k) :
    wholeComponentFiber f a
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (fiberInclusion n 0)
          (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber n 0)) -
        _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (fiberInclusion d 0)
            (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber d 0))) =
      principalDivisorFaceCycle n f a - principalDivisorFaceCycle d f a := by
  rw [map_sub, wholeComponentFiber_principalDivisor, wholeComponentFiber_principalDivisor]

end AlgebraicGeometry.Scheme.IntegralCycle
