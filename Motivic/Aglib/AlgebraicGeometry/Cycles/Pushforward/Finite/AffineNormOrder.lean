/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.AffineNormStalkLength
public import Motivic.Aglib.AlgebraicGeometry.Divisors.Order.PrincipalOrderCancellation
public import Mathlib.Data.ENat.BigOperators
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Fundamental.Invariance

/-!
# Signed orders of the original affine determinant norm

This leaf retains the domain and finite-free hypotheses on the whole source
chart. Disconnected normal sources, local-free chart selection and global cycle
assembly are not inferred from these hypotheses.


Intended upstream module: `Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.AffineNormOrder`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.AffineNormPrincipalCycle`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Order
open scoped TensorProduct nonZeroDivisors

universe u
namespace PrimeSpectrum.FiniteFiber

local instance {X : Scheme.{u}} [IsIntegral X] : Nonempty (⊤ : X.Opens) :=
  ⟨⟨genericPoint X, trivial⟩⟩

/-- The original chart element in the function field, through its canonical section. -/
def affineFunction (R : CommRingCat.{u}) [IsDomain R] (a : R) : (Spec R).functionField :=
  (Spec R).germToFunctionField ⊤ ((Scheme.ΓSpecIso R).inv a)

/-- A nonzero original affine scalar remains nonzero in the function field. -/
theorem affineFunction_ne_zero (R : CommRingCat.{u}) [IsDomain R]
    (a : R) (ha : a ≠ 0) : affineFunction R a ≠ 0 := by
  unfold affineFunction
  apply (map_ne_zero_iff _ ((Spec R).germToFunctionField_injective ⊤)).mpr
  exact (map_ne_zero_iff _ (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv.injective).mpr ha

/-- The original affine scalar order is its actual localized principal quotient length. -/
theorem affine_ord_eq_length (R : CommRingCat.{u}) [IsDomain R]
    [IsNoetherianRing R] (p : PrimeSpectrum R) (hp : p.asIdeal.height = 1)
    (a : R) (ha : a ≠ 0) :
    (Spec R).ord (affineFunction R a) p =
      ((Module.length (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⧸
          Ideal.span {algebraMap R (Localization.AtPrime p.asIdeal) a})).toNat : ℤ) := by
  have ha' : (Scheme.ΓSpecIso R).inv a ≠ 0 :=
    (map_ne_zero_iff _ (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv.injective).mpr ha
  have hp' : @coheight (Spec R) Scheme.instPreorderCarrierCarrierCommRingCat p = 1 :=
    (idealHeight_eq_coheight R p).symm.trans hp
  rw [affineFunction, (Spec R).ord_germ_eq_quotient_length ⊤ _ ha' trivial hp']
  let e := (Spec.stalkIso R p).symm.commRingCatIsoToRingEquiv
  let t := algebraMap R (Localization.AtPrime p.asIdeal) a
  let I : Ideal (Localization.AtPrime p.asIdeal) := Ideal.span {t}
  let J : Ideal ((Spec R).presheaf.stalk p) := Ideal.span {e t}
  let E := Ideal.quotientEquiv I J e (by simp [I, J, Ideal.map_span])
  have hl : Module.length (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal ⧸ I) =
      Module.length ((Spec R).presheaf.stalk p) (((Spec R).presheaf.stalk p) ⧸ J) :=
    (Module.length_eq_of_surjective (Ideal.Quotient.mk_surjective (I := I))).trans
      ((_root_.AlgebraicGeometry.Scheme.ringLength_eq_of_ringEquiv E).trans
        (Module.length_eq_of_surjective (Ideal.Quotient.mk_surjective (I := J))).symm)
  dsimp only [I, J, e, t] at hl
  have hg := ConcreteCategory.congr_hom (Spec.algebraMap_stalkIso_inv (R := R) p) a
  change (Spec.stalkIso R p).symm.commRingCatIsoToRingEquiv
    (algebraMap R (Localization.AtPrime p.asIdeal) a) = _ at hg
  have heq := congrArg
    (fun x : (Spec R).presheaf.stalk p =>
      Module.length ((Spec R).presheaf.stalk p)
        (((Spec R).presheaf.stalk p) ⧸ Ideal.span {x})) hg
  exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) (hl.trans heq).symm

variable (A B : CommRingCat.{u}) [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
  [IsDomain B] [Algebra A B] [Module.Finite A B] [Module.Free A B]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Every actual branch over the height-one target point has codimension one.
The argument uses the entire finite DVR algebra, not finite source stalks. -/
theorem sourcePoint_coheight_one (p : PrimeSpectrum A) (hp : p.asIdeal.height = 1)
    (q : MaximalSpectrum (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p)) :
    @coheight (Spec B) Scheme.instPreorderCarrierCarrierCommRingCat
      (_root_.PrimeSpectrum.FiniteFiber.sourcePoint A B p q).1 = 1 := by
  let R := Localization.AtPrime p.asIdeal
  let S := _root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p
  let := _root_.PrimeSpectrum.FiniteFiber.targetLocalization_isDiscreteValuationRing A p hp
  have hden : Algebra.algebraMapSubmonoid B p.asIdeal.primeCompl ≤ nonZeroDivisors B :=
    map_le_nonZeroDivisors_of_injective (algebraMap A B)
      (FaithfulSMul.algebraMap_injective A B) p.asIdeal.primeCompl_le_nonZeroDivisors
  let : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors S hden
  let : Ring.DimensionLEOne S := Ring.DimensionLEOne.of_isIntegral R S
  have hqne : q.asIdeal ≠ ⊥ := by
    intro he
    have hunder := _root_.PrimeSpectrum.FiniteFiber.maximal_under_base A B p q
    have hinj : Function.Injective (algebraMap A S) := by
      intro x y h
      apply FaithfulSMul.algebraMap_injective A B
      apply IsLocalization.injective S hden
      simpa only [← IsScalarTower.algebraMap_apply] using h
    rw [he, Ideal.under_def, Ideal.comap_bot_of_injective (algebraMap A S) hinj] at hunder
    exact p.asIdeal.ne_bot_of_height_eq_one hp hunder.symm
  have hqle : q.asIdeal.height ≤ 1 := by
    exact WithBot.coe_le_coe.mp (q.asIdeal.height_le_ringKrullDim_of_isPrime.trans
      (Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 S)))
  have hq : q.asIdeal.height = 1 := le_antisymm hqle
    (Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hqne))
  rw [← idealHeight_eq_coheight B]
  exact (IsLocalization.height_under
    (Algebra.algebraMapSubmonoid B p.asIdeal.primeCompl) q.asIdeal).trans hq

/-- The local determinant coefficient is the sum of the orders at all original
source points, weighted by the actual affine scheme residue degrees. -/
theorem affine_ord_norm (p : PrimeSpectrum A) (hp : p.asIdeal.height = 1)
    (a : B) (ha : a ≠ 0) :
    letI : IsNoetherianRing B := IsNoetherianRing.of_finite A B
    letI : Finite (MaximalSpectrum (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p)) :=
      Module.finiteAlgebra_maximalSpectrum_finite (Localization.AtPrime p.asIdeal)
        (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p)
    letI := Fintype.ofFinite (MaximalSpectrum (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p))
    (Spec A).ord (affineFunction A (Algebra.norm A a)) p =
      ∑ q : MaximalSpectrum (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p),
        (Spec B).ord (affineFunction B a) (_root_.PrimeSpectrum.FiniteFiber.sourcePoint A B p q).1 *
          ((Spec.map (CommRingCat.ofHom (algebraMap A B) : A ⟶ B)).residueDegree
            (_root_.PrimeSpectrum.FiniteFiber.sourcePoint A B p q).1 : ℤ) := by
  let : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  let := _root_.PrimeSpectrum.FiniteFiber.targetLocalization_isDiscreteValuationRing A p hp
  let : Finite (MaximalSpectrum (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p)) :=
    Module.finiteAlgebra_maximalSpectrum_finite (Localization.AtPrime p.asIdeal)
      (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p)
  let := Fintype.ofFinite (MaximalSpectrum (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p))
  have hn := _root_.PrimeSpectrum.FiniteFiber.localized_norm_coefficient A B p hp a ha
  have hnorm : algebraMap A (Localization.AtPrime p.asIdeal) (Algebra.norm A a) ≠ 0 :=
    (map_ne_zero_iff _ (IsLocalization.injective _ p.asIdeal.primeCompl_le_nonZeroDivisors)).mpr
      (Algebra.norm_ne_zero_iff.mpr ha)
  have hsum : (∑ q : MaximalSpectrum (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p),
      _root_.PrimeSpectrum.FiniteFiber.localizedPrincipalQuotientLength (algebraMap B
          (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p) a) q *
        ((Spec.map (CommRingCat.ofHom (algebraMap A B) : A ⟶ B)).residueDegree
          (_root_.PrimeSpectrum.FiniteFiber.sourcePoint A B p q).1 : ℕ∞)) ≠ ⊤ := by
    rw [← hn]
    exact IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr hnorm
  have hnat := congrArg ENat.toNat hn
  rw [ENat.toNat_sum (fun q hq => ne_top_of_le_ne_top hsum
    (Finset.single_le_sum (fun _ _ => zero_le) hq))] at hnat
  rw [affine_ord_eq_length A p hp _ (Algebra.norm_ne_zero_iff.mpr ha),
    IsDiscreteValuationRing.length_quotient_span_eq_addVal _ hnorm]
  rw [hnat, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro q _
  simp only [ENat.toNat_mul, Nat.cast_mul, ENat.toNat_natCast]
  rw [_root_.PrimeSpectrum.FiniteFiber.localizedPrincipalQuotientLength_eq_source_stalk]
  have ha' : (Scheme.ΓSpecIso B).inv a ≠ 0 :=
    (map_ne_zero_iff _ (Scheme.ΓSpecIso B).symm.commRingCatIsoToRingEquiv.injective).mpr ha
  rw [affineFunction, (Spec B).ord_germ_eq_quotient_length ⊤ _ ha' trivial
    (sourcePoint_coheight_one A B p hp q)]

/-- Signed compatibility for the same original numerator and denominator and
their actual determinant norms. All branches and residue degrees are retained. -/
theorem affine_ord_norm_ratio (p : PrimeSpectrum A) (hp : p.asIdeal.height = 1)
    (a b : B) (ha : a ≠ 0) (hb : b ≠ 0) :
    letI : IsNoetherianRing B := IsNoetherianRing.of_finite A B
    letI : Finite (MaximalSpectrum (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p)) :=
      Module.finiteAlgebra_maximalSpectrum_finite (Localization.AtPrime p.asIdeal)
        (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p)
    letI := Fintype.ofFinite (MaximalSpectrum (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p))
    (Spec A).ord (affineFunction A (Algebra.norm A a) /
      affineFunction A (Algebra.norm A b)) p =
      ∑ q : MaximalSpectrum (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p),
        (Spec B).ord (affineFunction B a / affineFunction B b)
            (_root_.PrimeSpectrum.FiniteFiber.sourcePoint A B p q).1 *
          ((Spec.map (CommRingCat.ofHom (algebraMap A B) : A ⟶ B)).residueDegree
            (_root_.PrimeSpectrum.FiniteFiber.sourcePoint A B p q).1 : ℤ) := by
  let : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  let : Finite (MaximalSpectrum (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p)) :=
    Module.finiteAlgebra_maximalSpectrum_finite (Localization.AtPrime p.asIdeal)
      (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p)
  let := Fintype.ofFinite (MaximalSpectrum (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p))
  have htarget := (Spec A).ord_add_ord_ratio
    (affineFunction A (Algebra.norm A b)) (affineFunction A (Algebra.norm A a))
    (affineFunction_ne_zero A _ (Algebra.norm_ne_zero_iff.mpr hb))
    (affineFunction_ne_zero A _ (Algebra.norm_ne_zero_iff.mpr ha)) p
  have hsource (q : MaximalSpectrum (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p)) :=
    (Spec B).ord_add_ord_ratio (affineFunction B b) (affineFunction B a)
      (affineFunction_ne_zero B b hb) (affineFunction_ne_zero B a ha)
      (_root_.PrimeSpectrum.FiniteFiber.sourcePoint A B p q).1
  rw [show (Spec A).ord (affineFunction A (Algebra.norm A a) /
    affineFunction A (Algebra.norm A b)) p = _ - _ from
      eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using htarget)]
  rw [affine_ord_norm A B p hp a ha, affine_ord_norm A B p hp b hb,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _
  rw [← sub_mul]
  congr 1
  exact (eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using hsource q)).symm

end PrimeSpectrum.FiniteFiber
