/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.FiniteAffineChart
public import Motivic.RingTheory.Localization.FiniteFiberPoints
public import Mathlib.Algebra.Category.Ring.Constructions

/-!
# The whole finite algebra of an actual Cartesian affine chart

For an actual Cartesian square with finite vertical map, affine target opens
`U` and `V ≤ g ⁻¹ᵁ U` give the entire source opens `f ⁻¹ᵁ U` and `f' ⁻¹ᵁ V`.
The restricted square is Cartesian as a square of schemes. Affine duality turns
this square into a ring pushout, and the tensor-product pushout gives a literal
`Γ(Y', V)`-algebra equivalence

`Γ(X', f' ⁻¹ᵁ V) ≃ Γ(Y', V) ⊗[Γ(Y, U)] Γ(X, f ⁻¹ᵁ U)`.

Both original section maps are recorded. Further scalar extension and target
localization retain the entire finite algebra, including every maximal branch
and all nilpotents. No tensor equivalence or ring pushout is an input, and no
ring comparison is inferred from a bijection of points.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Motivic.FiniteCartesianAffineAlgebra

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
  {i : X' ⟶ X} {g : Y' ⟶ Y} (sq : IsPullback i f' f g) [IsFinite f]
  {U : Y.Opens} {V : Y'.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
  (hVU : V ≤ g ⁻¹ᵁ U)

include sq in
/-- Finiteness of the actual base-changed map follows from the Cartesian square. -/
theorem baseChanged_isFinite : IsFinite f' :=
  MorphismProperty.of_isPullback sq inferInstance

include sq hV in
/-- The entire base-changed inverse image is affine; no smaller source chart is chosen. -/
theorem baseChangedSource_isAffineOpen : IsAffineOpen (f' ⁻¹ᵁ V) := by
  let : IsFinite f' := baseChanged_isFinite sq
  exact hV.preimage f'

omit [IsFinite f] in
include sq hVU in
/-- The entire base-changed inverse image maps into the original whole source chart. -/
theorem sourceOpen_le : f' ⁻¹ᵁ V ≤ i ⁻¹ᵁ (f ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, sq.w, Scheme.Hom.comp_preimage]
  exact f'.preimage_mono hVU

/-- The actual source horizontal section map, restricted only to the whole inverse image. -/
abbrev sourceSectionMap : Γ(X, f ⁻¹ᵁ U) ⟶ Γ(X', f' ⁻¹ᵁ V) :=
  i.appLE (f ⁻¹ᵁ U) (f' ⁻¹ᵁ V) (sourceOpen_le sq hVU)

omit [IsFinite f] in
/-- The restriction of the given square is still Cartesian as a square of schemes. -/
theorem restricted_isPullback :
    IsPullback
      (i.resLE (f ⁻¹ᵁ U) (f' ⁻¹ᵁ V) (sourceOpen_le sq hVU))
      (f'.resLE V (f' ⁻¹ᵁ V) le_rfl)
      (f.resLE U (f ⁻¹ᵁ U) le_rfl) (g.resLE U V hVU) := by
  exact Scheme.Hom.isPullback_resLE sq hVU le_rfl
    (inf_eq_right.mpr (sourceOpen_le sq hVU)).symm

include hU hV in
/-- Affine duality applied to the actual restricted Cartesian square gives the
pushout of the original section maps. The target chart is placed first. -/
theorem coordinate_isPushout :
    IsPushout (g.appLE U V hVU) (f.app U) (f'.app V) (sourceSectionMap sq hVU) := by
  let : IsAffine U.toScheme := hU
  let : IsAffine V.toScheme := hV
  let : IsAffine (f ⁻¹ᵁ U).toScheme := hU.preimage f
  have hp := isPushout_appTop_of_isPullback (restricted_isPullback sq hVU)
  have hp' := hp.of_iso U.topIso (f ⁻¹ᵁ U).topIso V.topIso (f' ⁻¹ᵁ V).topIso
    (f' := f.app U) (g' := g.appLE U V hVU)
    (inl' := sourceSectionMap sq hVU) (inr' := f'.app V)
    (by simp [Scheme.Hom.appTop, Scheme.Hom.appLE_eq_app])
    (by simp [Scheme.Hom.appTop])
    (by simp [Scheme.Hom.appTop, sourceSectionMap])
    (by simp [Scheme.Hom.appTop, Scheme.Hom.appLE_eq_app])
  exact hp'.flip

/-- Original source coordinates carry the actual finite-map scalar action. -/
abbrev sourceAlgebra : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) :=
  (f.app U).hom.toAlgebra

/-- New target coordinates carry the actual horizontal pullback scalar action. -/
abbrev targetAlgebra : Algebra Γ(Y, U) Γ(Y', V) :=
  (g.appLE U V hVU).hom.toAlgebra

/-- The whole base-changed source algebra uses the actual base-changed finite map. -/
abbrev baseChangedAlgebra : Algebra Γ(Y', V) Γ(X', f' ⁻¹ᵁ V) :=
  (f'.app V).hom.toAlgebra

/-- Original affine target coordinate ring. -/
abbrev targetRing : CommRingCat.{u} := Γ(Y, U)

/-- Original whole affine source coordinate ring. -/
abbrev sourceRing : CommRingCat.{u} := Γ(X, f ⁻¹ᵁ U)

/-- Actual new affine target coordinate ring. -/
abbrev baseChangedTargetRing : CommRingCat.{u} := Γ(Y', V)

/-- Actual whole base-changed affine source coordinate ring. -/
abbrev baseChangedSourceRing : CommRingCat.{u} := Γ(X', f' ⁻¹ᵁ V)

local notation "A" => targetRing (Y := Y) (U := U)
local notation "B" => sourceRing (f := f) (U := U)
local notation "C" => baseChangedTargetRing (Y' := Y') (V := V)
local notation "D" => baseChangedSourceRing (f' := f') (V := V)

/-- The actual section ring is isomorphic to the tensor-product pushout.
This is constructed from affine scheme duality, rather than supplied as data. -/
def coordinateRingIso :
    let := sourceAlgebra (f := f) (U := U)
    let := targetAlgebra hVU
    D ≅ CommRingCat.of (C ⊗[A] B) := by
  let := sourceAlgebra (f := f) (U := U)
  let := targetAlgebra hVU
  exact (coordinate_isPushout sq hU hV hVU).isoIsPushout _ _
    (CommRingCat.isPushout_tensorProduct A C B)

/-- The tensor comparison preserves the actual target section map. -/
@[reassoc] theorem coordinateRingIso_scalarSquare :
    let := sourceAlgebra (f := f) (U := U)
    let := targetAlgebra hVU
    f'.app V ≫ (coordinateRingIso sq hU hV hVU).hom =
      CommRingCat.ofHom (algebraMap C (C ⊗[A] B)) := by
  let := sourceAlgebra (f := f) (U := U)
  let := targetAlgebra hVU
  exact (coordinate_isPushout sq hU hV hVU).inl_isoIsPushout_hom _ _ _

/-- The tensor comparison preserves the original source numerator map. -/
@[reassoc] theorem coordinateRingIso_numeratorSquare :
    let := sourceAlgebra (f := f) (U := U)
    let := targetAlgebra hVU
    sourceSectionMap sq hVU ≫ (coordinateRingIso sq hU hV hVU).hom =
      CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight.toRingHom : B →+* C ⊗[A] B) := by
  let := sourceAlgebra (f := f) (U := U)
  let := targetAlgebra hVU
  exact (coordinate_isPushout sq hU hV hVU).inr_isoIsPushout_hom _ _ _

/-- The literal `Γ(Y', V)`-algebra equivalence of the entire finite inverse image. -/
def coordinateAlgEquiv :
    let := sourceAlgebra (f := f) (U := U)
    let := targetAlgebra hVU
    let := baseChangedAlgebra (f' := f') (V := V)
    D ≃ₐ[C] C ⊗[A] B := by
  let := sourceAlgebra (f := f) (U := U)
  let := targetAlgebra hVU
  let := baseChangedAlgebra (f' := f') (V := V)
  exact { (coordinateRingIso sq hU hV hVU).commRingCatIsoToRingEquiv with
    commutes' c := ConcreteCategory.congr_hom
      (coordinateRingIso_scalarSquare sq hU hV hVU) c }

/-- Every original source section becomes the literal right tensor numerator. -/
@[simp] theorem coordinateAlgEquiv_source (b : B) :
    let := sourceAlgebra (f := f) (U := U)
    let := targetAlgebra hVU
    let := baseChangedAlgebra (f' := f') (V := V)
    coordinateAlgEquiv sq hU hV hVU (sourceSectionMap sq hVU b) = 1 ⊗ₜ[A] b := by
  let := sourceAlgebra (f := f) (U := U)
  let := targetAlgebra hVU
  let := baseChangedAlgebra (f' := f') (V := V)
  exact ConcreteCategory.congr_hom (coordinateRingIso_numeratorSquare sq hU hV hVU) b

/-- Every actual target section becomes the literal left tensor scalar. -/
@[simp] theorem coordinateAlgEquiv_target (c : C) :
    let := sourceAlgebra (f := f) (U := U)
    let := targetAlgebra hVU
    let := baseChangedAlgebra (f' := f') (V := V)
    coordinateAlgEquiv sq hU hV hVU (f'.app V c) = c ⊗ₜ[A] (1 : B) := by
  let := sourceAlgebra (f := f) (U := U)
  let := targetAlgebra hVU
  let := baseChangedAlgebra (f' := f') (V := V)
  exact (coordinateAlgEquiv sq hU hV hVU).commutes c

/-- The inverse on pure tensors is the product of the two original section maps. -/
@[simp] theorem coordinateAlgEquiv_symm_tmul (c : C) (b : B) :
    let := sourceAlgebra (f := f) (U := U)
    let := targetAlgebra hVU
    let := baseChangedAlgebra (f' := f') (V := V)
    (coordinateAlgEquiv sq hU hV hVU).symm (c ⊗ₜ[A] b) =
      (f'.app V c) * sourceSectionMap sq hVU b := by
  let := sourceAlgebra (f := f) (U := U)
  let := targetAlgebra hVU
  let := baseChangedAlgebra (f' := f') (V := V)
  apply (coordinateAlgEquiv sq hU hV hVU).injective
  simp only [AlgEquiv.apply_symm_apply, map_mul, coordinateAlgEquiv_target,
    coordinateAlgEquiv_source, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

include hU in
/-- Module finiteness refers to the full original coordinate algebra. -/
theorem source_finite :
    let := sourceAlgebra (f := f) (U := U)
    Module.Finite A B := f.finite_app U hU

include sq hV in
/-- Module finiteness also holds for the full base-changed coordinate algebra. -/
theorem baseChanged_finite :
    let := baseChangedAlgebra (f' := f') (V := V)
    Module.Finite C D := by
  let : IsFinite f' := baseChanged_isFinite sq
  exact f'.finite_app V hV

section FurtherBaseChange

variable (R : Type u) [CommRing R] [Algebra Γ(Y', V) R]

/-- Scalar extension of the actual finite algebra cancels the intermediate
chart ring. The original-chart action on R is the composite with the given C-action;
no unspecified scalar tower is accepted as extra data. -/
def wholeBaseChangeEquiv :
    let := sourceAlgebra (f := f) (U := U)
    let := targetAlgebra hVU
    let := baseChangedAlgebra (f' := f') (V := V)
    let : Algebra A R := ((algebraMap C R).comp (g.appLE U V hVU).hom).toAlgebra
    R ⊗[C] D ≃ₐ[R] R ⊗[A] B := by
  let := sourceAlgebra (f := f) (U := U)
  let := targetAlgebra hVU
  let := baseChangedAlgebra (f' := f') (V := V)
  let : Algebra A R := ((algebraMap C R).comp (g.appLE U V hVU).hom).toAlgebra
  let : IsScalarTower A C R := IsScalarTower.of_algebraMap_eq' rfl
  exact (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R)
    (coordinateAlgEquiv sq hU hV hVU)).trans
      (Algebra.TensorProduct.cancelBaseChange A C R R B)

/-- Original source numerators survive further target base change literally. -/
@[simp] theorem wholeBaseChangeEquiv_source (r : R) (b : B) :
    let := sourceAlgebra (f := f) (U := U)
    let := targetAlgebra hVU
    let := baseChangedAlgebra (f' := f') (V := V)
    let : Algebra A R := ((algebraMap C R).comp (g.appLE U V hVU).hom).toAlgebra
    wholeBaseChangeEquiv sq hU hV hVU R
        (r ⊗ₜ[C] sourceSectionMap sq hVU b) = r ⊗ₜ[A] b := by
  let := sourceAlgebra (f := f) (U := U)
  let := targetAlgebra hVU
  let := baseChangedAlgebra (f' := f') (V := V)
  let : Algebra A R := ((algebraMap C R).comp (g.appLE U V hVU).hom).toAlgebra
  simp [wholeBaseChangeEquiv]

/-- The comparison is linear over the whole target ring, including its nilpotents. -/
theorem wholeBaseChangeEquiv_scalarSquare :
    let := sourceAlgebra (f := f) (U := U)
    let := targetAlgebra hVU
    let := baseChangedAlgebra (f' := f') (V := V)
    let : Algebra A R := ((algebraMap C R).comp (g.appLE U V hVU).hom).toAlgebra
    (wholeBaseChangeEquiv sq hU hV hVU R).toRingHom.comp
        (algebraMap R (R ⊗[C] D)) = algebraMap R (R ⊗[A] B) := by
  let := sourceAlgebra (f := f) (U := U)
  let := targetAlgebra hVU
  let := baseChangedAlgebra (f' := f') (V := V)
  let : Algebra A R := ((algebraMap C R).comp (g.appLE U V hVU).hom).toAlgebra
  ext r
  exact (wholeBaseChangeEquiv sq hU hV hVU R).commutes r

include sq hV in
/-- The whole finite algebra remains finite after arbitrary target scalar extension. -/
theorem wholeBaseChange_finite :
    let := baseChangedAlgebra (f' := f') (V := V)
    Module.Finite R (R ⊗[C] D) := by
  let := baseChangedAlgebra (f' := f') (V := V)
  let := baseChanged_finite sq hV
  infer_instance

end FurtherBaseChange

/-- Fix the commutative localization structure also for dependent prime ideals. -/
local instance localizationRing {S : Type u} [CommRing S] (P : Ideal S) [P.IsPrime] :
    Ring (Localization.AtPrime P) :=
  (inferInstance : CommRing (Localization.AtPrime P)).toRing

/-- Use the same semiring in the finite-algebra and tensor localizations. -/
local instance localizationSemiring {S : Type u} [CommRing S] (P : Ideal S) [P.IsPrime] :
    Semiring (Localization.AtPrime P) :=
  (inferInstance : CommRing (Localization.AtPrime P)).toSemiring

section TargetLocalization

variable (p : PrimeSpectrum Γ(Y', V))

/-- The actual whole algebra localized only on the new target has the literal
original-coordinate tensor presentation. Every maximal branch is retained. -/
def wholeLocalEquiv :
    let := sourceAlgebra (f := f) (U := U)
    let := baseChangedAlgebra (f' := f') (V := V)
    let : Algebra A (Localization.AtPrime p.asIdeal) :=
      ((algebraMap C (Localization.AtPrime p.asIdeal)).comp
      (g.appLE U V hVU).hom).toAlgebra
    FiniteFiber.localAlgebra C D p ≃ₐ[Localization.AtPrime p.asIdeal]
      Localization.AtPrime p.asIdeal ⊗[A] B := by
  let := sourceAlgebra (f := f) (U := U)
  let := baseChangedAlgebra (f' := f') (V := V)
  let : Algebra A (Localization.AtPrime p.asIdeal) :=
      ((algebraMap C (Localization.AtPrime p.asIdeal)).comp
    (g.appLE U V hVU).hom).toAlgebra
  exact wholeBaseChangeEquiv sq hU hV hVU (Localization.AtPrime p.asIdeal)

/-- Localization still sends original source sections to their original tensor numerators. -/
@[simp] theorem wholeLocalEquiv_source (r : Localization.AtPrime p.asIdeal) (b : B) :
    let := sourceAlgebra (f := f) (U := U)
    let := baseChangedAlgebra (f' := f') (V := V)
    let : Algebra A (Localization.AtPrime p.asIdeal) :=
      ((algebraMap C (Localization.AtPrime p.asIdeal)).comp
      (g.appLE U V hVU).hom).toAlgebra
    wholeLocalEquiv sq hU hV hVU p (r ⊗ₜ[C] sourceSectionMap sq hVU b) =
      r ⊗ₜ[A] b := by
  exact wholeBaseChangeEquiv_source sq hU hV hVU (Localization.AtPrime p.asIdeal) r b

/-- The target-localized comparison preserves the entire target localization action. -/
theorem wholeLocalEquiv_scalarSquare :
    let := sourceAlgebra (f := f) (U := U)
    let := baseChangedAlgebra (f' := f') (V := V)
    let : Algebra A (Localization.AtPrime p.asIdeal) :=
      ((algebraMap C (Localization.AtPrime p.asIdeal)).comp
      (g.appLE U V hVU).hom).toAlgebra
    (wholeLocalEquiv sq hU hV hVU p).toRingHom.comp
        (algebraMap (Localization.AtPrime p.asIdeal) (FiniteFiber.localAlgebra C D p)) =
      algebraMap (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⊗[A] B) := by
  exact wholeBaseChangeEquiv_scalarSquare sq hU hV hVU (Localization.AtPrime p.asIdeal)

end TargetLocalization

section OriginalTargetStalk

variable (y : V)

/-- Sections of the actual new target chart act through their original germs. -/
abbrev targetStalkAlgebra : Algebra C (Y'.presheaf.stalk y.1) :=
  (Y'.presheaf.germ V y.1 y.2).hom.toAlgebra

/-- The whole finite algebra over the original new-target stalk, with the
literal germ action, has the original-coordinate tensor presentation. The
stalk may be a nonreduced Artinian ring; no field structure is imposed. -/
def wholeStalkEquiv :
    let := sourceAlgebra (f := f) (U := U)
    let := baseChangedAlgebra (f' := f') (V := V)
    let := targetStalkAlgebra y
    let := ((Y'.presheaf.germ V y.1 y.2).hom.comp (g.appLE U V hVU).hom).toAlgebra
    Y'.presheaf.stalk y.1 ⊗[C] D ≃ₐ[Y'.presheaf.stalk y.1]
      Y'.presheaf.stalk y.1 ⊗[A] B := by
  let := sourceAlgebra (f := f) (U := U)
  let := baseChangedAlgebra (f' := f') (V := V)
  let := targetStalkAlgebra y
  let := ((Y'.presheaf.germ V y.1 y.2).hom.comp (g.appLE U V hVU).hom).toAlgebra
  exact wholeBaseChangeEquiv sq hU hV hVU (Y'.presheaf.stalk y.1)

/-- The original-target-stalk comparison preserves each actual source numerator. -/
@[simp] theorem wholeStalkEquiv_source (r : Y'.presheaf.stalk y.1) (b : B) :
    let := sourceAlgebra (f := f) (U := U)
    let := baseChangedAlgebra (f' := f') (V := V)
    let := targetStalkAlgebra y
    let := ((Y'.presheaf.germ V y.1 y.2).hom.comp (g.appLE U V hVU).hom).toAlgebra
    wholeStalkEquiv sq hU hV hVU y (r ⊗ₜ[C] sourceSectionMap sq hVU b) =
      r ⊗ₜ[A] b := by
  let := targetStalkAlgebra y
  exact wholeBaseChangeEquiv_source sq hU hV hVU (Y'.presheaf.stalk y.1) r b

/-- The target-stalk scalar square holds before quotienting or choosing a branch. -/
theorem wholeStalkEquiv_scalarSquare :
    let := sourceAlgebra (f := f) (U := U)
    let := baseChangedAlgebra (f' := f') (V := V)
    let := targetStalkAlgebra y
    let := ((Y'.presheaf.germ V y.1 y.2).hom.comp (g.appLE U V hVU).hom).toAlgebra
    (wholeStalkEquiv sq hU hV hVU y).toRingHom.comp
        (algebraMap (Y'.presheaf.stalk y.1) (Y'.presheaf.stalk y.1 ⊗[C] D)) =
      algebraMap (Y'.presheaf.stalk y.1) (Y'.presheaf.stalk y.1 ⊗[A] B) := by
  let := targetStalkAlgebra y
  exact wholeBaseChangeEquiv_scalarSquare sq hU hV hVU (Y'.presheaf.stalk y.1)

/-- The composite original-coordinate action is the actual horizontal stalk map
applied to original germs. This identifies the new stalk scalar action geometrically. -/
@[reassoc] theorem originalGerm_stalkSquare :
    g.appLE U V hVU ≫ Y'.presheaf.germ V y.1 y.2 =
      Y.presheaf.germ U (g y.1) (hVU y.2) ≫ g.stalkMap y.1 := by
  rw [Scheme.Hom.germ_stalkMap]
  simp only [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]

include sq hV in
/-- The whole actual-stalk algebra is finite even when it has several maximal branches. -/
theorem wholeStalk_finite :
    let := baseChangedAlgebra (f' := f') (V := V)
    let := targetStalkAlgebra y
    Module.Finite (Y'.presheaf.stalk y.1) (Y'.presheaf.stalk y.1 ⊗[C] D) := by
  let := targetStalkAlgebra y
  exact wholeBaseChange_finite sq hV (Y'.presheaf.stalk y.1)

/-- The actual target stalk, with its germ action, is the localization of the
actual affine chart at the prime corresponding to that same point. -/
def targetStalkLocalizationEquiv :
    let := targetStalkAlgebra y
    Y'.presheaf.stalk y.1 ≃ₐ[C] Localization.AtPrime (hV.primeIdealOf y).asIdeal := by
  let := targetStalkAlgebra y
  let : IsLocalization.AtPrime (Y'.presheaf.stalk y.1) (hV.primeIdealOf y).asIdeal :=
    hV.isLocalization_stalk y
  exact IsLocalization.algEquiv (hV.primeIdealOf y).asIdeal.primeCompl _ _

/-- The target-stalk/localization comparison sends literal germs to the same fractions. -/
@[simp] theorem targetStalkLocalizationEquiv_germ (c : C) :
    let := targetStalkAlgebra y
    targetStalkLocalizationEquiv hV y (Y'.presheaf.germ V y.1 y.2 c) =
      algebraMap C (Localization.AtPrime (hV.primeIdealOf y).asIdeal) c := by
  exact (targetStalkLocalizationEquiv hV y).commutes c

/-- Tensoring the actual target-stalk chart isomorphism identifies the entire
stalk algebra with the existing `FiniteFiber.localAlgebra`, without discarding
any maximal ideal. This comparison is C-linear and its stronger base square
is recorded separately. -/
def wholeStalkToLocalEquiv :
    let := baseChangedAlgebra (f' := f') (V := V)
    let := targetStalkAlgebra y
    Y'.presheaf.stalk y.1 ⊗[C] D ≃ₐ[C]
      FiniteFiber.localAlgebra C D (hV.primeIdealOf y) := by
  let := baseChangedAlgebra (f' := f') (V := V)
  let := targetStalkAlgebra y
  exact Algebra.TensorProduct.congr (targetStalkLocalizationEquiv hV y)
    (AlgEquiv.refl : D ≃ₐ[C] D)

/-- Each whole source-coordinate numerator is unchanged by the stalk/localization comparison. -/
@[simp] theorem wholeStalkToLocalEquiv_source (d : D) :
    let := baseChangedAlgebra (f' := f') (V := V)
    let := targetStalkAlgebra y
    wholeStalkToLocalEquiv (f' := f') hV y (1 ⊗ₜ[C] d) = 1 ⊗ₜ[C] d := by
  let := baseChangedAlgebra (f' := f') (V := V)
  let := targetStalkAlgebra y
  simp [wholeStalkToLocalEquiv]

/-- The actual target-stalk scalar map agrees with its literal affine localization map. -/
theorem wholeStalkToLocalEquiv_scalar (r : Y'.presheaf.stalk y.1) :
    let := baseChangedAlgebra (f' := f') (V := V)
    let := targetStalkAlgebra y
    wholeStalkToLocalEquiv (f' := f') hV y (r ⊗ₜ[C] (1 : D)) =
      targetStalkLocalizationEquiv hV y r ⊗ₜ[C] (1 : D) := by
  let := baseChangedAlgebra (f' := f') (V := V)
  let := targetStalkAlgebra y
  simp [wholeStalkToLocalEquiv]

end OriginalTargetStalk

end Motivic.FiniteCartesianAffineAlgebra
