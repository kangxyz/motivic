/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.FiniteFlatCurveSpecialization
public import Motivic.Aglib.RingTheory.DomainCartierMultiplicity
public import Motivic.Aglib.AlgebraicGeometry.GenericFinitePushforwardMultiplicity
public import Motivic.AlgebraicGeometry.Cycles.GenericFinitePushforward
public import Motivic.Algebra.Homology.KoszulFiniteFamilyRealization
public import Motivic.Algebra.Homology.KoszulFlatLocalMultiplicity
public import Motivic.AlgebraicGeometry.Cycles.FinitePushforwardKoszul

/-!
# Finite maps of actual Cartier endpoint fibers

The actual Cartesian fiber map is finite without flatness of the map between
curves. Its residue weights are the original map's residue weights. Endpoint
multiplicities are lengths of the original singleton stalk quotient, retaining
all branches and nilpotents. The whole semilocal finite algebra proves the
original-point Cartier length balance and finite pushforward compatibility.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Motivic
open scoped BigOperators Polynomial

universe u

namespace AlgebraicGeometry.FiniteFlatCurve

variable {k : Type u} [Field k] {C D : Scheme.{u}}
  (f : D ⟶ Spec (.of k[X])) (a : k) (j : C ⟶ D)

instance fiberMap_isFinite [IsFinite j] : IsFinite (fiberMap f a j) :=
  MorphismProperty.of_isPullback (fiberMap_isPullback f a j).flip
    (inferInstanceAs (IsFinite j))

instance fiberMap_surjective [Surjective j] : Surjective (fiberMap f a j) :=
  MorphismProperty.of_isPullback (fiberMap_isPullback f a j).flip
    (inferInstanceAs (Surjective j))

/-- A closed endpoint changes neither of the original finite-map residue weights. -/
theorem fiberMap_residueDegree (x : fiber (j ≫ f) a) :
    (fiberMap f a j).residueDegree x =
      j.residueDegree (fiberInclusion (j ≫ f) a x) := by
  have h := congrArg (fun g => g.residueDegree x) (fiberMap_inclusion f a j)
  simpa only [residueDegree_comp, residueDegree_of_surjectiveOnStalks,
    one_mul, mul_one] using h

/-- The original target equation maps to the same original source equation. -/
theorem scalar_stalkMap (x : C) :
    j.stalkMap x (scalar f a (j x)) = scalar (j ≫ f) a x := by
  simp only [scalar, Scheme.Hom.stalkMap_comp, CommRingCat.comp_apply]
  rfl

omit j in
/-- Actual endpoint local length equals the original ambient Cartier quotient length. -/
theorem fiber_stalk_length (y : fiber f a) :
    Module.length ((fiber f a).presheaf.stalk y) ((fiber f a).presheaf.stalk y) =
      Module.length (D.presheaf.stalk (fiberInclusion f a y))
        ((D.presheaf.stalk (fiberInclusion f a y)) ⧸
          Ideal.ofList [scalar f a (fiberInclusion f a y)]) := by
  rw [← fiberInclusion_stalk, Scheme.Hom.ker_stalk]
  exact ((Module.length_eq_of_surjective
    (Ideal.Quotient.mk_surjective
      (I := RingHom.ker ((fiberInclusion f a).stalkMap y).hom))).trans
        (ringLength_eq_of_ringEquiv
          (stalkQuotientKerEquiv (fiberInclusion f a) y))).symm

omit j in
/-- The literal quotient has finite length before its integer coefficient is formed. -/
theorem fiber_cut_length_ne_top [IsFinite f] [IsNoetherian D] (y : fiber f a) :
    Module.length (D.presheaf.stalk (fiberInclusion f a y))
      ((D.presheaf.stalk (fiberInclusion f a y)) ⧸
        Ideal.ofList [scalar f a (fiberInclusion f a y)]) ≠ ⊤ := by
  rw [← fiber_stalk_length]
  exact stalk_length_ne_top_of_mem_genericPoints y (fiber_all_generic f a y)

omit j in
/-- Every actual endpoint coefficient retains the full quotient multiplicity. -/
theorem fiber_fundamentalCoefficient [IsFinite f] [IsNoetherian D] (y : fiber f a) :
    IntegralCycle.toPoints (fundamentalCycle (fiber f a)) y =
      ((Module.length (D.presheaf.stalk (fiberInclusion f a y))
        ((D.presheaf.stalk (fiberInclusion f a y)) ⧸
          Ideal.ofList [scalar f a (fiberInclusion f a y)])).toNat : ℤ) := by
  rw [toPoints_fundamentalCycle, fundamentalPointCycle_apply,
    dite_eq_left (fiber_all_generic f a y)]
  exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) (fiber_stalk_length f a y)

/-- The point fiber of the actual endpoint map is the whole original source
fiber. The equivalence uses closed-immersion injectivity, not branch choices. -/
def fiberMapPointEquiv (y : fiber f a) :
    {x : fiber (j ≫ f) a // fiberMap f a j x = y} ≃
      {x : C // j x = fiberInclusion f a y} := by
  let e : {x : fiber (j ≫ f) a // fiberMap f a j x = y} →
      {x : C // j x = fiberInclusion f a y} := fun x =>
    ⟨fiberInclusion (j ≫ f) a x.1, by
      rw [← Scheme.Hom.comp_apply, ← fiberMap_inclusion, Scheme.Hom.comp_apply, x.2]⟩
  apply Equiv.ofBijective e
  constructor
  · intro x x' h
    apply Subtype.ext
    exact (fiberInclusion (j ≫ f) a).isEmbedding.injective (congrArg Subtype.val h)
  · intro x
    have h : endpoint a (pullback.fst (endpoint a) f y) = (j ≫ f) x.1 := by
      rw [Scheme.Hom.comp_apply, x.2]
      exact congrArg (fun g => g y) (pullback.condition (f := endpoint a) (g := f))
    obtain ⟨z, _, hz⟩ := Scheme.Pullback.exists_preimage_pullback
      (pullback.fst (endpoint a) f y) x.1 h
    refine ⟨⟨z, ?_⟩, ?_⟩
    · apply (fiberInclusion f a).isEmbedding.injective
      rw [← Scheme.Hom.comp_apply, fiberMap_inclusion, Scheme.Hom.comp_apply]
      exact (congrArg j hz).trans x.2
    · exact Subtype.ext hz

@[simp] theorem fiberMapPointEquiv_apply_val (y : fiber f a)
    (x : {x : fiber (j ≫ f) a // fiberMap f a j x = y}) :
    (fiberMapPointEquiv f a j y x).1 = fiberInclusion (j ≫ f) a x.1 := rfl

omit j in
/-- All actual endpoint points, with their original structures, enumerate the
endpoint generic points. This is a bijection of points, not a reduction. -/
def fiberGenericPointEquiv [IsFinite f] : fiber f a ≃ genericPoints (fiber f a) where
  toFun x := ⟨x, fiber_all_generic f a x⟩
  invFun x := x.1
  left_inv _ := rfl
  right_inv _ := rfl

/-- The finite-pushed actual endpoint coefficient is the sum over every
original point above the target point, with its original residue weight and
its full literal Cartier quotient length. -/
theorem fiberMap_fundamentalCoefficient [IsFinite f] [IsFinite j] [IsNoetherian C]
    (y : fiber f a) :
    IntegralCycle.toPoints (IntegralCycle.finitePushforward (fiberMap f a j)
        (fundamentalCycle (fiber (j ≫ f) a))) y =
      ∑ᶠ x : {x : C // j x = fiberInclusion f a y},
        (j.residueDegree x.1 : ℤ) *
          ((Module.length (C.presheaf.stalk x.1)
            ((C.presheaf.stalk x.1) ⧸ Ideal.ofList [scalar (j ≫ f) a x.1])).toNat : ℤ) := by
  classical
  let := IntegralCycle.genericPointFintype (fiber (j ≫ f) a)
  rw [← IntegralCycle.ofGenericCoefficients_genericMultiplicity,
    IntegralCycle.toPoints_finitePushforward_ofGenericCoefficients_apply]
  unfold IntegralCycle.genericPushforwardCoefficient
  rw [← finsum_eq_sum_of_fintype]
  rw [← finsum_comp_equiv (fiberGenericPointEquiv (j ≫ f) a)]
  change (∑ᶠ x : fiber (j ≫ f) a,
    if fiberMap f a j x = y then
      (genericMultiplicity ⟨x, fiber_all_generic (j ≫ f) a x⟩ : ℤ) *
        ((fiberMap f a j).residueDegree x : ℤ) else 0) = _
  simp_rw [← finsum_eq_if]
  rw [← finsum_subtype_eq_finsum_cond]
  rw [← finsum_comp_equiv (fiberMapPointEquiv f a j y)]
  apply finsum_congr
  intro x
  rw [fiberMap_residueDegree]
  change ((Module.length ((fiber (j ≫ f) a).presheaf.stalk x.1)
      ((fiber (j ≫ f) a).presheaf.stalk x.1)).toNat : ℤ) * _ = _
  rw [fiber_stalk_length]
  exact mul_comm _ _

/-- Equality of the actual original Cartier length sums suffices for equality
of whole endpoint cycles. The local balance is an explicit premise here. -/
theorem finitePushforward_fiber_of_cartierLength
    [IsFinite f] [IsFinite j] [IsNoetherian C] [IsNoetherian D] (d : ℤ)
    (hdegree : ∀ y : fiber f a,
      (∑ᶠ x : {x : C // j x = fiberInclusion f a y},
        (j.residueDegree x.1 : ℤ) *
          ((Module.length (C.presheaf.stalk x.1)
            ((C.presheaf.stalk x.1) ⧸ Ideal.ofList [scalar (j ≫ f) a x.1])).toNat : ℤ)) =
        d * ((Module.length (D.presheaf.stalk (fiberInclusion f a y))
          ((D.presheaf.stalk (fiberInclusion f a y)) ⧸
            Ideal.ofList [scalar f a (fiberInclusion f a y)])).toNat : ℤ)) :
    IntegralCycle.finitePushforward (fiberMap f a j)
        (fundamentalCycle (fiber (j ≫ f) a)) = d • fundamentalCycle (fiber f a) := by
  apply IntegralCycle.toPoints_injective
  ext y
  rw [fiberMap_fundamentalCoefficient]
  simp only [map_zsmul, Finsupp.smul_apply, zsmul_eq_mul,
    fiber_fundamentalCoefficient]
  exact hdegree y

end AlgebraicGeometry.FiniteFlatCurve

namespace Motivic.Koszul

open LengthEuler

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
  [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R B]
  (t : R) [IsArtinianRing (R ⧸ Ideal.ofList [t])]

/-- The whole finite algebra's singleton Euler test equals all actual maximal
Cartier quotient lengths with their original residue weights. Only the whole
algebra is finite over the base; its individual local rings need not be. -/
theorem finiteAlgebra_cartierEuler
    (hregular : ∀ q : MaximalSpectrum B,
      IsSMulRegular (Localization.AtPrime q.asIdeal)
        (algebraMap R (Localization.AtPrime q.asIdeal) t)) :
    letI : IsArtinianRing (R ⧸ (Ideal.ofList [t] ⊔ (⊥ : Ideal R))) := by
      rw [sup_bot_eq]; infer_instance
    chainEuler (coefficientComplex (finiteFamilyRestriction R B (ModuleCat.of B B)) [t])
        (finiteFamilyRestriction_finiteHomology R B (ModuleCat.of B B) [t] ⊥ bot_le) =
      ∑ᶠ q : MaximalSpectrum B, (LocalLength.finiteAlgebraResidueDegree R B q : ℤ) *
        ((Module.length (Localization.AtPrime q.asIdeal)
          ((Localization.AtPrime q.asIdeal) ⧸
            Ideal.ofList [algebraMap R (Localization.AtPrime q.asIdeal) t])).toNat : ℤ) := by
  let : IsArtinianRing (R ⧸ (Ideal.ofList [t] ⊔ (⊥ : Ideal R))) := by
    rw [sup_bot_eq]; infer_instance
  rw [finiteFamily_coefficient_projection R B (ModuleCat.of B B) [t] ⊥ bot_le]
  apply finsum_congr
  intro q
  congr 1
  let Q := Localization.AtPrime q.asIdeal
  let v := algebraMap B Q (algebraMap R B t)
  have hv : v = algebraMap R Q t := (IsScalarTower.algebraMap_apply R B Q t).symm
  let e := extendScalarsRegularIso (algebraMap B Q)
  have hl := finiteFamilyLocal_finiteHomology R B (ModuleCat.of B B) [t] ⊥ bot_le q
  change FiniteHomology (coefficientComplex (finiteFamilyLocalization B (ModuleCat.of B B) q)
    [v]) at hl
  have hc := hl.of_quasiIso ((coefficientFunctor [v]).mapIso e).hom
  have h := coefficient_chainEuler_eq_of_linearEquiv _ (ModuleCat.of Q Q)
    e.toLinearEquiv [v] hl hc
  have hreg : IsSMulRegular Q v := hv ▸ hregular q
  rw [singleton_chainEuler_eq_ring_quotient_length v hreg] at h
  exact h.trans (by rw [hv])

end Motivic.Koszul

namespace Motivic.Koszul

/-- The actual principal quotient transports along a specified ring isomorphism. -/
def cartierQuotientRingEquiv {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (t : R) :
    R ⧸ Ideal.ofList [t] ≃+* S ⧸ Ideal.ofList [e t] :=
  Ideal.quotientEquiv _ _ e (by rw [Ideal.map_ofList]; rfl)

/-- Both quotient lengths are measured over their original ambient rings. -/
theorem cartierQuotient_length_ringEquiv {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (t : R) :
    Module.length R (R ⧸ Ideal.ofList [t]) =
      Module.length S (S ⧸ Ideal.ofList [e t]) :=
  (Module.length_eq_of_surjective (Ideal.Quotient.mk_surjective (I := Ideal.ofList [t]))).trans
    ((ringLength_eq_of_ringEquiv (cartierQuotientRingEquiv e t)).trans
      (Module.length_eq_of_surjective
        (Ideal.Quotient.mk_surjective (I := Ideal.ofList [e t]))).symm)

/-- Regularity transports the specified scalar, rather than a chosen generator. -/
theorem cartier_regular_ringEquiv {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (t : R) : IsSMulRegular R t ↔ IsSMulRegular S (e t) :=
  e.toEquiv.isSMulRegular_congr (fun x => e.map_mul t x)

end Motivic.Koszul

namespace AlgebraicGeometry.FiniteFlatCurve

open Motivic.FiniteAffineChart Motivic.FiniteSchemeEuler

variable {k : Type u} [Field k] {C D : Scheme.{u}}
  (f : D ⟶ Spec (.of k[X])) (a : k) (j : C ⟶ D) [IsFinite j]
  {U : D.Opens} (hU : IsAffineOpen U) (p : Spec Γ(D, U))

/-- The original endpoint equation in the actual target prime-localization. -/
def localScalar : Localization.AtPrime p.asIdeal :=
  (targetStalkLocalizationIso hU p).hom (scalar f a (hU.fromSpec p))

omit [IsFinite j] in
/-- Aligned source stalks carry exactly the original endpoint equation. -/
theorem alignedStalkMap_scalar (x : C) (y : D) (h : y = j x) :
    Graph.alignedStalkMap j x y h (scalar f a y) = scalar (j ≫ f) a x := by
  subst y
  rw [Graph.alignedStalkMap_rfl, scalar_stalkMap]

local instance cartierCoordinateAlgebra : Algebra Γ(D, U) Γ(C, j ⁻¹ᵁ U) :=
  (j.app U).hom.toAlgebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (q : MaximalSpectrum (FiniteFiber.localAlgebra Γ(D, U) Γ(C, j ⁻¹ᵁ U) p))

local instance canonicalCartierLocalizationRing : Ring (Localization.AtPrime q.asIdeal) :=
  (inferInstance : CommRing (Localization.AtPrime q.asIdeal)).toRing

local instance canonicalCartierLocalizationSemiring : Semiring (Localization.AtPrime q.asIdeal) :=
  (inferInstance : CommRing (Localization.AtPrime q.asIdeal)).toSemiring

/-- The whole-algebra source localization sends the same target equation to
its original source stalk, through the actual finite-map scalar square. -/
theorem originalSourceLocalizationIso_scalar :
    (originalSourceLocalizationIso j hU p q).hom
      (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)
        (localScalar f a hU p)) =
      scalar (j ≫ f) a (wholeAlgebraFiberEquiv j hU p q).1 := by
  have h := ConcreteCategory.congr_hom (originalSourceLocalizationIso_base_square j hU p q)
    (localScalar f a hU p)
  change (originalSourceLocalizationIso j hU p q).hom
      (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)
        (localScalar f a hU p)) =
    originalFiberStalkMap j hU p (wholeAlgebraFiberEquiv j hU p q)
      ((targetStalkLocalizationIso hU p).inv (localScalar f a hU p)) at h
  rw [localScalar, Iso.hom_inv_id_apply] at h
  exact h.trans (alignedStalkMap_scalar f a j _ _ _)

/-- Each full local Cartier quotient is identified with its original source
quotient; no source stalk is asserted finite over the target stalk. -/
theorem originalSourceLocalizationIso_cartierLength :
    Module.length (Localization.AtPrime q.asIdeal)
      ((Localization.AtPrime q.asIdeal) ⧸
        Ideal.ofList [algebraMap (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime q.asIdeal) (localScalar f a hU p)]) =
      Module.length (C.presheaf.stalk (wholeAlgebraFiberEquiv j hU p q).1)
        ((C.presheaf.stalk (wholeAlgebraFiberEquiv j hU p q).1) ⧸
          Ideal.ofList [scalar (j ≫ f) a (wholeAlgebraFiberEquiv j hU p q).1]) := by
  have h := Koszul.cartierQuotient_length_ringEquiv
    (originalSourceLocalizationIso j hU p q).commRingCatIsoToRingEquiv
    (algebraMap (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) (localScalar f a hU p))
  change Module.length (Localization.AtPrime q.asIdeal) _ =
    Module.length (C.presheaf.stalk (wholeAlgebraFiberEquiv j hU p q).1)
      ((C.presheaf.stalk (wholeAlgebraFiberEquiv j hU p q).1) ⧸
        Ideal.ofList [(originalSourceLocalizationIso j hU p q).hom
          (algebraMap (Localization.AtPrime p.asIdeal)
            (Localization.AtPrime q.asIdeal) (localScalar f a hU p))]) at h
  rwa [originalSourceLocalizationIso_scalar] at h

/-- The original family's flatness proves regularity of the same parameter
in every actual maximal localization of the whole finite algebra. -/
theorem originalSourceLocalizationIso_regular [Flat (j ≫ f)] :
    IsSMulRegular (Localization.AtPrime q.asIdeal)
      (algebraMap (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime q.asIdeal) (localScalar f a hU p)) := by
  apply (Koszul.cartier_regular_ringEquiv
    (originalSourceLocalizationIso j hU p q).commRingCatIsoToRingEquiv _).mpr
  change IsSMulRegular (C.presheaf.stalk (sourceChart j hU (wholeAlgebraSourcePoint j hU p q).1))
    ((originalSourceLocalizationIso j hU p q).hom
      (algebraMap (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime q.asIdeal) (localScalar f a hU p)))
  have he := originalSourceLocalizationIso_scalar f a j hU p q
  change _ = scalar (j ≫ f) a (sourceChart j hU (wholeAlgebraSourcePoint j hU p q).1) at he
  rw [he]
  exact scalar_regular (j ≫ f) a _

end AlgebraicGeometry.FiniteFlatCurve

namespace Motivic.Koszul

open LengthEuler

/-- The complete semilocal Cartier length sum equals the actual generic
coefficient times the target cut length. No flatness of the finite algebra is assumed. -/
theorem finiteAlgebra_domainCartierLength
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R B]
    (t : R) [IsArtinianRing (R ⧸ Ideal.ofList [t])]
    (ht : IsSMulRegular R t) (hm : t ∈ IsLocalRing.maximalIdeal R)
    (hregular : ∀ q : MaximalSpectrum B,
      IsSMulRegular (Localization.AtPrime q.asIdeal)
        (algebraMap R (Localization.AtPrime q.asIdeal) t)) :
    (∑ᶠ q : MaximalSpectrum B, (LocalLength.finiteAlgebraResidueDegree R B q : ℤ) *
      ((Module.length (Localization.AtPrime q.asIdeal)
        ((Localization.AtPrime q.asIdeal) ⧸
          Ideal.ofList [algebraMap R (Localization.AtPrime q.asIdeal) t])).toNat : ℤ)) =
      domainGenericLength (finiteFamilyRestriction R B (ModuleCat.of B B)) *
        ((Module.length R (R ⧸ Ideal.ofList [t])).toNat : ℤ) :=
  (finiteAlgebra_cartierEuler R B t hregular).symm.trans
    (domainCartier_chainEuler (finiteFamilyRestriction R B (ModuleCat.of B B)) t ht hm)

end Motivic.Koszul

namespace AlgebraicGeometry.FiniteFlatCurve

open Motivic.FiniteAffineChart Motivic.FiniteSchemeEuler

variable {k : Type u} [Field k] {C D : Scheme.{u}}
  (f : D ⟶ Spec (.of k[X])) (a : k) (j : C ⟶ D) [IsFinite j]
  {U : D.Opens} (hU : IsAffineOpen U) (p : Spec Γ(D, U))

local instance cartierBalanceCoordinateAlgebra : Algebra Γ(D, U) Γ(C, j ⁻¹ᵁ U) :=
  (j.app U).hom.toAlgebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The original finite-map source fiber satisfies the Cartier balance with
the actual generic length of its whole finite algebra. The target and source
equations, lengths and residue degrees are all the original scheme ones. -/
theorem originalCartierLength_sum
    [IsDomain Γ(D, U)] [IsNoetherianRing Γ(D, U)] [Flat f] [Flat (j ≫ f)]
    [IsArtinianRing ((D.presheaf.stalk (hU.fromSpec p)) ⧸
      Ideal.ofList [scalar f a (hU.fromSpec p)])]
    (hm : scalar f a (hU.fromSpec p) ∈
      IsLocalRing.maximalIdeal (D.presheaf.stalk (hU.fromSpec p))) :
    letI : Module.Finite Γ(D, U) Γ(C, j ⁻¹ᵁ U) := coordinateFinite j hU
    (∑ᶠ x : {x : C // j x = hU.fromSpec p}, (j.residueDegree x.1 : ℤ) *
      ((Module.length (C.presheaf.stalk x.1)
        ((C.presheaf.stalk x.1) ⧸ Ideal.ofList [scalar (j ≫ f) a x.1])).toNat : ℤ)) =
      Koszul.domainGenericLength
        (Koszul.finiteFamilyRestriction (Localization.AtPrime p.asIdeal)
          (FiniteFiber.localAlgebra Γ(D, U) Γ(C, j ⁻¹ᵁ U) p)
          (ModuleCat.of (FiniteFiber.localAlgebra Γ(D, U) Γ(C, j ⁻¹ᵁ U) p)
            (FiniteFiber.localAlgebra Γ(D, U) Γ(C, j ⁻¹ᵁ U) p))) *
        ((Module.length (D.presheaf.stalk (hU.fromSpec p))
          ((D.presheaf.stalk (hU.fromSpec p)) ⧸
            Ideal.ofList [scalar f a (hU.fromSpec p)])).toNat : ℤ) := by
  let : Module.Finite Γ(D, U) Γ(C, j ⁻¹ᵁ U) := coordinateFinite j hU
  let R := Localization.AtPrime p.asIdeal
  let B := FiniteFiber.localAlgebra Γ(D, U) Γ(C, j ⁻¹ᵁ U) p
  let e := (targetStalkLocalizationIso hU p).commRingCatIsoToRingEquiv
  let t := localScalar f a hU p
  let : IsArtinianRing (R ⧸ Ideal.ofList [t]) :=
    (Koszul.cartierQuotientRingEquiv e (scalar f a (hU.fromSpec p))).isArtinianRing
  have ht : IsSMulRegular R t :=
    (Koszul.cartier_regular_ringEquiv e (scalar f a (hU.fromSpec p))).mp (scalar_regular f a _)
  have hmR : t ∈ IsLocalRing.maximalIdeal R := by
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal e]
    exact Ideal.mem_map_of_mem e hm
  have h := Koszul.finiteAlgebra_domainCartierLength R B t ht hmR
    (fun q => originalSourceLocalizationIso_regular f a j hU p q)
  have hlength := Koszul.cartierQuotient_length_ringEquiv e (scalar f a (hU.fromSpec p))
  change Module.length (D.presheaf.stalk (hU.fromSpec p))
    ((D.presheaf.stalk (hU.fromSpec p)) ⧸ Ideal.ofList [scalar f a (hU.fromSpec p)]) =
      Module.length R (R ⧸ Ideal.ofList [t]) at hlength
  rw [← hlength] at h
  rw [← finsum_comp_equiv (wholeAlgebraFiberEquiv j hU p)]
  refine Eq.trans ?_ h
  apply finsum_congr
  intro q
  rw [← wholeAlgebra_residueDegree j hU p q,
    ← originalSourceLocalizationIso_cartierLength f a j hU p q]

end AlgebraicGeometry.FiniteFlatCurve

namespace AlgebraicGeometry

open FiniteFlatCurve

/-- Finite pushforward commutes with the actual Cartier endpoint cut for
finite surjective maps of integral curves. The multiplier is the original
generic residue degree. Neither curve is assumed normal, the finite curve map
need not be flat, and the actual endpoint fibers can be nonreduced. -/
theorem finiteCurve_finitePushforward_fiber
    {k : Type u} [Field k] {C D : Scheme.{u}} [IsIntegral C] [IsIntegral D]
    (f : D ⟶ Spec (.of k[X])) [IsFinite f] [Surjective f]
    (j : C ⟶ D) [IsFinite j] [Surjective j] (a : k) :
    letI : IsNoetherian D := isNoetherian_of_finiteType f
    letI : IsNoetherian C := isNoetherian_of_finiteType j
    IntegralCycle.finitePushforward (fiberMap f a j)
        (fundamentalCycle (fiber (j ≫ f) a)) =
      (j.residueDegree (genericPoint C) : ℤ) • fundamentalCycle (fiber f a) := by
  let : IsNoetherian D := isNoetherian_of_finiteType f
  let : IsNoetherian C := isNoetherian_of_finiteType j
  let : Flat f := finiteCurve_flat_of_integral_surjective f
  let : Flat (j ≫ f) := finiteCurve_flat_of_integral_surjective (j ≫ f)
  apply finitePushforward_fiber_of_cartierLength f a j
  intro y
  obtain ⟨U, hU, p, hp⟩ := FiniteAffineChart.exists_targetChart (fiberInclusion f a y)
  let : Nonempty U := ⟨⟨hU.fromSpec p, by
    change hU.fromSpec p ∈ (U : Set D)
    rw [← hU.range_fromSpec]
    exact ⟨p, rfl⟩⟩⟩
  let : IsDomain Γ(D, U) := IsIntegral.component_integral U
  let : IsNoetherianRing Γ(D, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let : IsArtinianRing ((D.presheaf.stalk (hU.fromSpec p)) ⧸
      Ideal.ofList [scalar f a (hU.fromSpec p)]) := by
    rw [hp]
    have hcut := scalar_cut_isArtinian f a y
    rw [sup_bot_eq] at hcut
    exact hcut
  have hm : scalar f a (hU.fromSpec p) ∈
      IsLocalRing.maximalIdeal (D.presheaf.stalk (hU.fromSpec p)) := by
    rw [hp]
    exact scalar_mem_maximalIdeal f a y
  have h := originalCartierLength_sum f a j hU p hm
  rw [GenericFinitePushforwardMultiplicity.scheme_genericLength j hU p] at h
  rw [hp] at h
  exact h

end AlgebraicGeometry
