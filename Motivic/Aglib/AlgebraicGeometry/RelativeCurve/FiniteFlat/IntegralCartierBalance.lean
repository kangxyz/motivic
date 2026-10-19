/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Endpoints.FiniteCurvePushforwardSpecialization

/-!
# Original Cartier lengths for finite dominant integral maps

The balance uses the whole finite algebra and every original source point.
Nonzero endpoint germs on integral schemes replace flatness of the scalar map.
The Artinian target cut remains explicit; this is a local coefficient theorem,
not an assertion that arbitrary endpoint points are generic.


Intended upstream module: `Aglib.AlgebraicGeometry.RelativeCurve.FiniteFlat.IntegralCartierBalance`.
Incoming project consumers:
`Motivic.AlgebraicGeometry.Correspondences.Endpoints.FinitePoint.EndpointBalance`.
-/

open _root_.AlgebraicGeometry.Scheme.Modules.Pushforward.FiniteEuler
  (originalSourceLocalizationIso)

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped Polynomial

universe u

namespace AlgebraicGeometry.FiniteFlatCurve

private theorem scalar_eq_global_germ {k : Type u} [Field k] {D : Scheme.{u}}
    (f : D ⟶ Spec (.of k[X])) (a : k) (y : D) :
    scalar f a y = D.presheaf.germ ⊤ y (TopologicalSpace.Opens.mem_top y)
      (f.appTop ((Scheme.ΓSpecIso (.of k[X])).inv (Polynomial.X - Polynomial.C a))) := by
  simp [scalar, endpointScalar, Scheme.Hom.appTop]

/-- A nonzero original target scalar stays nonzero at every original source
point of a finite dominant integral map. No flatness is used. -/
theorem scalar_comp_ne_zero_of_integral
    {k : Type u} [Field k] {C D : Scheme.{u}} [IsIntegral C] [IsIntegral D]
    (f : D ⟶ Spec (.of k[X])) (a : k) (j : C ⟶ D) [IsFinite j] [IsDominant j]
    (y : D) (hy : scalar f a y ≠ 0) (x : C) :
    scalar (j ≫ f) a x ≠ 0 := by
  let : IsSchemeTheoreticallyDominant j := .of_isDominant j
  have hs : f.appTop ((Scheme.ΓSpecIso (.of k[X])).inv
      (Polynomial.X - Polynomial.C a)) ≠ 0 := by
    intro h
    apply hy
    rw [scalar_eq_global_germ, h, map_zero]
  have hj : Function.Injective j.appTop := by
    simpa [Scheme.Hom.appTop] using j.app_injective ⊤
  have hg := germ_injective_of_isIntegral C x (TopologicalSpace.Opens.mem_top x)
  rw [scalar_eq_global_germ, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  intro hz
  apply hs
  apply hj
  apply hg
  simpa only [map_zero] using hz

open _root_.AlgebraicGeometry.Scheme.Hom.FiniteAffineChart
    _root_.AlgebraicGeometry.Scheme.Modules.Pushforward.FiniteEuler

variable {k : Type u} [Field k] {C D : Scheme.{u}}
  [IsIntegral C] [IsIntegral D] [IsLocallyNoetherian D]
  (f : D ⟶ Spec (.of k[X])) (a : k) (j : C ⟶ D) [IsFinite j] [IsDominant j]
  {U : D.Opens} [Nonempty U] (hU : IsAffineOpen U) (p : Spec Γ(D, U))

/-- The algebra structure on sections over the whole inverse-image open, induced by `j.app U`. -/
local instance chartAlgebra : Algebra Γ(D, U) Γ(C, j ⁻¹ᵁ U) :=
  (j.app U).hom.toAlgebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The complete original source fiber has the native generic-degree Cartier
balance. All nilpotent quotient lengths and residue weights are retained.
Only the actual target cut is assumed Artinian; neither scalar map is flat. -/
theorem originalCartierLength_sum_of_integral
    [IsArtinianRing ((D.presheaf.stalk (hU.fromSpec p)) ⧸
      Ideal.ofList [scalar f a (hU.fromSpec p)])]
    (htarget : scalar f a (hU.fromSpec p) ≠ 0)
    (hm : scalar f a (hU.fromSpec p) ∈
      IsLocalRing.maximalIdeal (D.presheaf.stalk (hU.fromSpec p))) :
    (∑ᶠ x : {x : C // j x = hU.fromSpec p}, (j.residueDegree x.1 : ℤ) *
      ((Module.length (C.presheaf.stalk x.1)
        ((C.presheaf.stalk x.1) ⧸ Ideal.ofList [scalar (j ≫ f) a x.1])).toNat : ℤ)) =
      (j.residueDegree (genericPoint C) : ℤ) *
        ((Module.length (D.presheaf.stalk (hU.fromSpec p))
          ((D.presheaf.stalk (hU.fromSpec p)) ⧸
            Ideal.ofList [scalar f a (hU.fromSpec p)])).toNat : ℤ) := by
  let : IsDomain Γ(D, U) := IsIntegral.component_integral U
  let : IsNoetherianRing Γ(D, U) :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let : Module.Finite Γ(D, U) Γ(C, j ⁻¹ᵁ U) :=
      _root_.AlgebraicGeometry.Scheme.Modules.Pushforward.FiniteEuler.coordinateFinite j hU
  let R := Localization.AtPrime p.asIdeal
  let B := _root_.PrimeSpectrum.FiniteFiber.localAlgebra Γ(D, U) Γ(C, j ⁻¹ᵁ U) p
  let e :=
      (_root_.AlgebraicGeometry.Scheme.Modules.Pushforward.FiniteEuler.targetStalkLocalizationIso hU
      p).commRingCatIsoToRingEquiv
  let t := localScalar f a hU p
  let : IsArtinianRing (R ⧸ Ideal.ofList [t]) :=
    (_root_.ChainComplex.Koszul.cartierQuotientRingEquiv e (scalar f a (hU.fromSpec
        p))).isArtinianRing
  have ht : IsSMulRegular R t :=
    (_root_.ChainComplex.Koszul.cartier_regular_ringEquiv e (scalar f a (hU.fromSpec p))).mp
      (IsSMulRegular.of_ne_zero htarget)
  have hmR : t ∈ IsLocalRing.maximalIdeal R := by
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal e]
    exact Ideal.mem_map_of_mem e hm
  have hregular (q : MaximalSpectrum B) :
      IsSMulRegular (Localization.AtPrime q.asIdeal)
        (algebraMap R (Localization.AtPrime q.asIdeal) t) := by
    apply (_root_.ChainComplex.Koszul.cartier_regular_ringEquiv
      (_root_.AlgebraicGeometry.Scheme.Modules.Pushforward.FiniteEuler.originalSourceLocalizationIso
          j hU p q).commRingCatIsoToRingEquiv _).mpr
    change IsSMulRegular
      (C.presheaf.stalk (_root_.AlgebraicGeometry.Scheme.Hom.FiniteAffineChart.sourceChart j hU
          (_root_.AlgebraicGeometry.Scheme.Modules.Pushforward.FiniteEuler.wholeAlgebraSourcePoint j
          hU p q).1))
      ((originalSourceLocalizationIso j hU p q).hom
        (algebraMap R (Localization.AtPrime q.asIdeal) t))
    have he := originalSourceLocalizationIso_scalar f a j hU p q
    change _ = scalar (j ≫ f) a (_root_.AlgebraicGeometry.Scheme.Hom.FiniteAffineChart.sourceChart j
        hU (_root_.AlgebraicGeometry.Scheme.Modules.Pushforward.FiniteEuler.wholeAlgebraSourcePoint
        j hU p q).1) at he
    rw [he]
    exact IsSMulRegular.of_ne_zero
      (scalar_comp_ne_zero_of_integral f a j (hU.fromSpec p) htarget _)
  have h := _root_.ChainComplex.Koszul.finiteAlgebra_domainCartierLength R B t ht hmR hregular
  have hlength := _root_.ChainComplex.Koszul.cartierQuotient_length_ringEquiv e (scalar f a
      (hU.fromSpec p))
  change Module.length (D.presheaf.stalk (hU.fromSpec p))
    ((D.presheaf.stalk (hU.fromSpec p)) ⧸ Ideal.ofList [scalar f a (hU.fromSpec p)]) =
      Module.length R (R ⧸ Ideal.ofList [t]) at hlength
  rw [← hlength, _root_.AlgebraicGeometry.Scheme.Hom.GenericMultiplicity.scheme_genericLength j hU
      p] at h
  rw [← finsum_comp_equiv
      (_root_.AlgebraicGeometry.Scheme.Modules.Pushforward.FiniteEuler.wholeAlgebraFiberEquiv j hU
      p)]
  refine Eq.trans ?_ h
  apply finsum_congr
  intro q
  rw [← _root_.AlgebraicGeometry.Scheme.Modules.Pushforward.FiniteEuler.wholeAlgebra_residueDegree j
      hU p q,
    ← originalSourceLocalizationIso_cartierLength f a j hU p q]

end AlgebraicGeometry.FiniteFlatCurve
