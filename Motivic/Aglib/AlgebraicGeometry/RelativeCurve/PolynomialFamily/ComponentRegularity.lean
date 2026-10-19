/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Endpoints.FiniteFlatCurveSpecialization
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Literal endpoint regularity on components of a flat polynomial family

The whole family need not be finite over the affine line. Flat generalization
lifting makes each reduced generic support dominant over that irreducible line.
Its domain stalks therefore retain the nonzero scalar `t - a`. The statement is
about the original ambient ideal-sheaf quotient and its original scalar map;
it does not assert flatness of components over a higher-dimensional base.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped Polynomial

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A generic support of a generalizing map dominates an irreducible target.
No finite, proper, or surjective map hypothesis is needed. -/
theorem isDominant_pointClosure_of_generalizing
    {P S : Scheme.{u}} [IrreducibleSpace S] (f : P ⟶ S)
    (hf : GeneralizingMap f) (z : genericPoints P) :
    IsDominant ((IntegralClosedSubscheme.pointClosure z.val).val.subschemeι ≫ f) := by
  have hz := mem_genericPoints_of_generalizing f hf z.val z.property
  have hclosure : closure ({f z.val} : Set S) = Set.univ := by
    simpa only [genericPoints, Set.mem_ofPred_eq, irreducibleComponents_eq_singleton,
      Set.mem_singleton_iff] using hz
  refine ⟨?_⟩
  rw [DenseRange, dense_iff_closure_eq, ← Set.univ_subset_iff, ← hclosure]
  apply closure_mono
  rintro x (rfl : x = f z.val)
  refine ⟨genericPoint (IntegralClosedSubscheme.pointClosure z.val).val.subscheme, ?_⟩
  change f (IntegralClosedSubscheme.pointClosure z.val).point = f z.val
  rw [IntegralClosedSubscheme.point_pointClosure]

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry

/-- A nonzero affine scalar stays regular in the literal stalk of an integral
scheme dominant over its domain spectrum. The actual structure map is retained. -/
theorem dominant_integral_affineScalar_isSMulRegular
    {R : Type u} [CommRing R] [IsDomain R] {C : Scheme.{u}} [IsIntegral C]
    (g : C ⟶ Spec (.of R)) [IsDominant g] (r : R) (hr : r ≠ 0) (c : C) :
    IsSMulRegular (C.presheaf.stalk c)
      (g.stalkMap c ((Spec (.of R)).presheaf.germ ⊤ (g c) trivial
        ((Scheme.ΓSpecIso (.of R)).inv r))) := by
  obtain ⟨U, hU, hcU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (show c ∈ (⊤ : C.Opens) from trivial)
  have : IsDominant hU.fromSpec := by
    constructor
    change Dense (Set.range hU.fromSpec)
    rw [hU.range_fromSpec]
    exact U.isOpen.dense ⟨c, hcU⟩
  have : IsSchemeTheoreticallyDominant (hU.fromSpec ≫ g) :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  have hg : Function.Injective g.appTop := by
    intro x y hxy
    have hi : Function.Injective (hU.fromSpec ≫ g).appTop := by
      simpa only [Scheme.Hom.appTop, Scheme.Hom.preimage_top] using
        (hU.fromSpec ≫ g).app_injective ⊤
    apply hi
    rw [Scheme.Hom.comp_appTop]
    exact congrArg hU.fromSpec.appTop hxy
  apply IsSMulRegular.of_ne_zero
  rw [Scheme.Hom.germ_stalkMap_apply]
  intro hzero
  apply hr
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv).1
  apply hg
  apply germ_injective_of_isIntegral C c (show c ∈ (⊤ : C.Opens) from trivial)
  simpa only [map_zero, Scheme.Hom.preimage_top, Scheme.Hom.appTop] using hzero

/-- The original parameter stays regular on the actual stalk of each integral
component of a flat family over the affine line, even without finiteness. -/
theorem flat_polynomial_component_scalar_regular
    {k : Type u} [Field k] {P : Scheme.{u}}
    (f : P ⟶ Spec (.of k[X])) [Flat f] (z : genericPoints P) (a : k)
    (c : (Scheme.IntegralClosedSubscheme.pointClosure z.val).val.subscheme) :
    IsSMulRegular
      ((Scheme.IntegralClosedSubscheme.pointClosure z.val).val.subscheme.presheaf.stalk c)
      (FiniteFlatCurve.scalar
        ((Scheme.IntegralClosedSubscheme.pointClosure z.val).val.subschemeι ≫ f) a c) := by
  have := Scheme.Hom.isDominant_pointClosure_of_generalizing f (Flat.generalizingMap f) z
  exact dominant_integral_affineScalar_isSMulRegular _ (Polynomial.X - Polynomial.C a)
    (Polynomial.X_sub_C_ne_zero a) c

/-- On every ambient stalk, `t - a` is regular on the literal quotient by an
original reduced component's kernel. Nilpotents in the whole family are retained;
there is no component-flatness assertion over any larger base. -/
theorem flat_polynomial_component_quotient_scalar_regular
    {k : Type u} [Field k] {P : Scheme.{u}}
    (f : P ⟶ Spec (.of k[X])) [Flat f] (z : genericPoints P) (a : k) (x : P) :
    IsSMulRegular ((P.presheaf.stalk x) ⧸
      (Scheme.IntegralClosedSubscheme.pointClosure z.val).val.subschemeι.ker.stalk x)
      (FiniteFlatCurve.scalar f a x) := by
  let j := (Scheme.IntegralClosedSubscheme.pointClosure z.val).val.subschemeι
  change IsSMulRegular ((P.presheaf.stalk x) ⧸ j.ker.stalk x)
    (FiniteFlatCurve.scalar f a x)
  by_cases hx : x ∈ Set.range j
  · obtain ⟨c, rfl⟩ := hx
    let e := Scheme.Hom.closedStalkQuotientLinearEquiv j c
    apply (e.isSMulRegular_congr _).mpr
    have h := flat_polynomial_component_scalar_regular f z a c
    dsimp only [FiniteFlatCurve.scalar] at h ⊢
    rw [Scheme.Hom.stalkMap_comp] at h
    convert! h using 1
  · have : Subsingleton ((P.presheaf.stalk x) ⧸ j.ker.stalk x) :=
      Ideal.Quotient.subsingleton_iff.mpr (Scheme.Hom.closedImmersion_ker_stalk_eq_top j hx)
    exact fun _ _ _ => Subsingleton.elim _ _

end AlgebraicGeometry
