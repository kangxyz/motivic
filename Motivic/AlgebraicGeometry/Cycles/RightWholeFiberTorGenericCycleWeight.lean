/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.RightWholeFiberTorTargetGenericStalk
public import Motivic.AlgebraicGeometry.Intersection.RightWholeFiberTorGeneric
public import Motivic.AlgebraicGeometry.Cycles.GenericFinitePushforward
public import Motivic.AlgebraicGeometry.Cycles.GenericFiniteFiber

/-!
# Actual right target generic weights of the whole Tor cycle

The localized target weight is attached to the coefficient of the actual
finite pushforward of `rightFirstStageWholeTorGenericCycle` on the SAME affine open.
The proof uses the actual whole finite algebra at the target generic point,
its original pushforward/source module isomorphisms, and the finite-algebra
signed-length formula. The original smooth Z-diagonal whole Tor bound supplies
finite outer support. The right support is F times the original G,H incidence;
the right target is F times its actual scheme image.

Quasi-coherence is required only on the entire inverse-image open, as in the
accepted whole-coefficient construction. All points of the finite fiber are
retained. Quasi-finite reflection proves that those points are generic; the
opposite generic-preservation assertion is neither used nor made. Every
nonreduced generic-stalk length and every literal residue degree is retained.

SOURCE-ONLY PROPOSAL: no compilation or acceptance is claimed. This module
uses no exterior degree formula, remaining-diagonal devissage, iterated-pairing
comparison, or associativity theorem.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators TensorProduct

universe u

namespace Motivic.FiniteCorrespondenceGenerator

open Intersection FiniteSchemeEuler LengthEuler

namespace RightGenericWeightAux

private theorem finiteLengthSupport_of_lengths
    {R T : Type u} [CommRing R] [CommRing T]
    {M : ℕ → ModuleCat.{u} R} {N : ℕ → ModuleCat.{u} T}
    (hM : FiniteLengthSupport M)
    (h : ∀ n, Module.length R (M n) = Module.length T (N n)) :
    FiniteLengthSupport N where
  finite_length n := by rw [← h n]; exact hM.finite_length n
  finite_support := by
    have he : (fun n => Module.length T (N n)) = fun n => Module.length R (M n) :=
      funext (fun n => (h n).symm)
    rw [he]
    exact hM.finite_support

private theorem signedLengthSum_eq_of_lengths
    {R T : Type u} [CommRing R] [CommRing T]
    {M : ℕ → ModuleCat.{u} R} {N : ℕ → ModuleCat.{u} T}
    (sign : ℕ → ℤ) (hM : FiniteLengthSupport M) (hN : FiniteLengthSupport N)
    (h : ∀ n, Module.length R (M n) = Module.length T (N n)) :
    signedLengthSum M sign hM = signedLengthSum N sign hN := by
  unfold signedLengthSum
  apply finsum_congr
  intro n
  simp only [integerLength, h n]

end RightGenericWeightAux

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

/-- The inferred smooth-site base is the original affine scheme Spec k. -/
local instance rightGenericWeightBaseIsSeparated :
    ((Functor.fromPUnit (Spec (.of k))).obj X.right).IsSeparated :=
  inferInstanceAs (Spec (.of k)).IsSeparated

local instance : (correspondenceSixfoldAmbient X.hom Y.hom Z.hom W.hom).IsSeparated :=
  correspondenceSixfoldAmbient_isSeparated (S := Spec (.of k)) X.hom Y.hom Z.hom W.hom

local instance : IsLocallyNoetherian
    (correspondenceSixfoldAmbient X.hom Y.hom Z.hom W.hom) :=
  isLocallyNoetherian_correspondenceSixfoldAmbient (S := Spec (.of k))
    X.hom Y.hom Z.hom W.hom

/-- The actual right target is locally finite type over the closed G,H image
inside the smooth Y-times-W product. No flatness of F over Y is required. -/
local instance : IsLocallyNoetherian (F.rightIntermediateImageProduct G H) := by
  have : IsLocallyNoetherian Y.left :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := Spec (.of k)) Y.hom
  have : IsLocallyNoetherian (pullback Y.hom W.hom) :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := Y.left) (pullback.fst Y.hom W.hom)
  have : IsLocallyNoetherian (G.incidenceMap H).image :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := pullback Y.hom W.hom)
      (G.incidenceMap H).imageι
  exact LocallyOfFiniteType.isLocallyNoetherian (Y := (G.incidenceMap H).image)
    (pullback.snd (F.targetProjection ≫ Y.hom)
      ((G.incidenceMap H).imageι ≫ pullback.fst Y.hom W.hom ≫ Y.hom))

variable (V : (F.rightIntermediateImageProduct G H).affineOpens)

/-- Restricting the actual finite map to the chosen open changes neither
residue-field extension nor its degree. Both open stalk maps are the original ones. -/
theorem rightFirstStageWholeOpen_residueDegree (w : F.rightFirstStageWholeOpen G H V) :
    (F.rightIntermediateImageMap G H ∣_ V).residueDegree w =
      (F.rightIntermediateImageMap G H).residueDegree w.1 := by
  have h := congrArg (fun m => m.residueDegree w)
    (morphismRestrict_ι (F.rightIntermediateImageMap G H) V.1)
  simpa only [residueDegree_comp, residueDegree_of_surjectiveOnStalks,
    one_mul, mul_one, Scheme.Opens.ι_apply] using h

/-- Every coefficient of the actual finite pushforward sums ALL generic
branches above that point, with their signed whole-Tor weights and literal degrees. -/
theorem rightFirstStageWholeTorGenericCycle_pushforward_coefficient
    (y : V.1.toScheme) :
    IntegralCycle.toPoints
        (IntegralCycle.finitePushforward (F.rightIntermediateImageMap G H ∣_ V)
          (F.rightFirstStageWholeTorGenericCycle G H V)) y =
      ∑ᶠ w : {w : genericPoints (F.rightFirstStageWholeOpen G H V) //
        (F.rightIntermediateImageMap G H ∣_ V) w.1 = y},
        F.rightFirstStageWholeTorGenericCoefficient G H V w.1 *
          ((F.rightIntermediateImageMap G H ∣_ V).residueDegree w.1.1 : ℤ) := by
  classical
  let := IntegralCycle.genericPointFintype (F.rightFirstStageWholeOpen G H V)
  rw [rightFirstStageWholeTorGenericCycle,
    IntegralCycle.toPoints_finitePushforward_ofGenericCoefficients_apply]
  unfold IntegralCycle.genericPushforwardCoefficient
  rw [finsum_subtype_eq_finsum_cond
    (f := fun w : genericPoints (F.rightFirstStageWholeOpen G H V) =>
      F.rightFirstStageWholeTorGenericCoefficient G H V w *
        ((F.rightIntermediateImageMap G H ∣_ V).residueDegree w.1 : ℤ))
    (fun w => (F.rightIntermediateImageMap G H ∣_ V) w.1 = y)]
  simp only [finsum_eq_if, finsum_eq_sum_of_fintype]

variable (r : Spec Γ(F.rightIntermediateImageProduct G H, V))

/-- The literal target point of the existing affine spectrum, viewed in V. -/
abbrev rightFirstStageTargetChartOpenPoint : V.1.toScheme :=
  ⟨V.2.fromSpec r, V.2.range_fromSpec.subset (Set.mem_range_self r)⟩

/-- The original full fiber and the full fiber of the actual restricted finite
map have exactly the same points. No branch selection is made. -/
def rightFirstStageWholeOpenFiberEquiv :
    {x : F.rightIntermediateSupportProduct G H //
      F.rightIntermediateImageMap G H x = V.2.fromSpec r} ≃
    {w : F.rightFirstStageWholeOpen G H V //
      (F.rightIntermediateImageMap G H ∣_ V) w =
        F.rightFirstStageTargetChartOpenPoint G H V r} where
  toFun x := ⟨⟨x.1, wholeFiberTor_source_mem (F.rightIntermediateImageMap G H) V r x⟩, by
    apply Subtype.ext
    exact (morphismRestrict_base_coe (F.rightIntermediateImageMap G H) V.1 _).trans x.2⟩
  invFun w := ⟨w.1.1, by
    exact (morphismRestrict_base_coe (F.rightIntermediateImageMap G H) V.1 w.1).symm.trans
      (congrArg Subtype.val w.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The whole original source fiber above a genuine target generic consists
exactly of the generic points of the whole inverse image above that same point.
This is quasi-finite REFLECTION through the actual restricted finite map. -/
def rightFirstStageWholeGenericFiberEquiv
    (hr : V.2.fromSpec r ∈ genericPoints (F.rightIntermediateImageProduct G H)) :
    {x : F.rightIntermediateSupportProduct G H //
      F.rightIntermediateImageMap G H x = V.2.fromSpec r} ≃
    {w : genericPoints (F.rightFirstStageWholeOpen G H V) //
      (F.rightIntermediateImageMap G H ∣_ V) w.1 =
        F.rightFirstStageTargetChartOpenPoint G H V r} :=
  (F.rightFirstStageWholeOpenFiberEquiv G H V r).trans
    (genericFiberEquiv (F.rightIntermediateImageMap G H ∣_ V)
      ⟨F.rightFirstStageTargetChartOpenPoint G H V r,
        Motivic.mem_genericPoints_of_image_generic V.1.ι
          (F.rightFirstStageTargetChartOpenPoint G H V r) hr⟩)

@[simp] theorem rightFirstStageWholeGenericFiberEquiv_apply_val
    (hr : V.2.fromSpec r ∈ genericPoints (F.rightIntermediateImageProduct G H))
    (x : {x : F.rightIntermediateSupportProduct G H //
      F.rightIntermediateImageMap G H x = V.2.fromSpec r}) :
    (F.rightFirstStageWholeGenericFiberEquiv G H V r hr x).1.1.1 = x.1 := rfl

@[simp] theorem rightFirstStageWholeGenericFiberEquiv_symm_apply_val
    (hr : V.2.fromSpec r ∈ genericPoints (F.rightIntermediateImageProduct G H))
    (w : {w : genericPoints (F.rightFirstStageWholeOpen G H V) //
      (F.rightIntermediateImageMap G H ∣_ V) w.1 =
        F.rightFirstStageTargetChartOpenPoint G H V r}) :
    ((F.rightFirstStageWholeGenericFiberEquiv G H V r hr).symm w).1 = w.1.1.1 := rfl

/-- All coefficient algebras use the literal original section map. -/
local instance rightGenericWeightCoordinateAlgebra :
    Algebra Γ(F.rightIntermediateImageProduct G H, V)
      Γ(F.rightIntermediateSupportProduct G H, (F.rightIntermediateImageMap G H) ⁻¹ᵁ V) :=
  ((F.rightIntermediateImageMap G H).app V).hom.toAlgebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The algebraic maximal-quotient degree is the literal residue degree of
this same branch of the restricted finite map. The first equality uses the
accepted target/source residue scalar square, not an abstract field isomorphism. -/
theorem rightFirstStageWholeGenericFiber_residueDegree
    (hr : V.2.fromSpec r ∈ genericPoints (F.rightIntermediateImageProduct G H))
    (a : MaximalSpectrum
      (FiniteFiber.localAlgebra Γ(F.rightIntermediateImageProduct G H, V)
        Γ(F.rightIntermediateSupportProduct G H, (F.rightIntermediateImageMap G H) ⁻¹ᵁ V) r)) :
    letI := coordinateFinite (F.rightIntermediateImageMap G H) V.2
    LocalLength.finiteAlgebraResidueDegree (Localization.AtPrime r.asIdeal)
        (FiniteFiber.localAlgebra Γ(F.rightIntermediateImageProduct G H, V)
          Γ(F.rightIntermediateSupportProduct G H, (F.rightIntermediateImageMap G H) ⁻¹ᵁ V) r) a =
      (F.rightIntermediateImageMap G H ∣_ V).residueDegree
        (F.rightFirstStageWholeGenericFiberEquiv G H V r hr
          (wholeAlgebraFiberEquiv (F.rightIntermediateImageMap G H) V.2 r a)).1.1 := by
  have := coordinateFinite (F.rightIntermediateImageMap G H) V.2
  rw [F.rightFirstStageWholeOpen_residueDegree G H V]
  exact wholeAlgebra_residueDegree (F.rightIntermediateImageMap G H) V.2 r a

/-- The original generic target makes the WHOLE localized finite algebra
Artinian. Every actual coefficient is finite, and the proved whole Tor bound
excludes infinite outer support before any signed sum is evaluated. -/
theorem rightFirstStageWholeAtGeneric_finiteLengthSupport
    (hr : V.2.fromSpec r ∈ genericPoints (F.rightIntermediateImageProduct G H)) :
    FiniteLengthSupport (F.rightFirstStageWholeLocalizedCoefficient G H V r) := by
  have := coordinateFinite (F.rightIntermediateImageMap G H) V.2
  let R := Localization.AtPrime r.asIdeal
  let T := FiniteFiber.localAlgebra Γ(F.rightIntermediateImageProduct G H, V)
    Γ(F.rightIntermediateSupportProduct G H, (F.rightIntermediateImageMap G H) ⁻¹ᵁ V) r
  have := isArtinianRing_stalk_of_mem_genericPoints (V.2.fromSpec r) hr
  have : IsArtinianRing R :=
    (targetStalkLocalizationIso V.2 r).commRingCatIsoToRingEquiv.isArtinianRing
  have : IsArtinianRing T := IsArtinianRing.of_finite R T
  refine ⟨fun n => ?_, ?_⟩
  · have := wholeFiberTorLocalizedSections_finite
      (F.tripleSupportProductInclusion G H)
      (correspondenceSecondAmbientInclusion X.hom Y.hom Z.hom W.hom)
      (F.rightIntermediateSupportInclusion G H) (F.rightIntermediateToTripleSupport G H)
      (F.rightIntermediate_ambient_isPullback G H) (F.rightIntermediateImageMap G H) V r n
    exact Module.length_ne_top
  · apply (F.rightFirstStageWholeLocalized_nonzero_finite G H V r).subset
    intro n hn hz
    have := hz
    exact hn Module.length_eq_zero

/-- The actual target stalk length is the length of restriction of the whole
coefficient along the original finite algebra, through the actual chart isomorphism. -/
theorem rightFirstStageWholePushforward_coefficient_length (n : ℕ) :
    Module.length (Localization.AtPrime r.asIdeal)
      ((ModuleCat.restrictScalars (algebraMap (Localization.AtPrime r.asIdeal)
        (FiniteFiber.localAlgebra Γ(F.rightIntermediateImageProduct G H, V)
          Γ(F.rightIntermediateSupportProduct G H, (F.rightIntermediateImageMap G H) ⁻¹ᵁ V) r))).obj
        (F.rightFirstStageWholeLocalizedCoefficient G H V r n)) =
    Module.length ((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec r))
      (F.rightFirstStagePushforwardCoefficient G H V r n) :=
  (F.rightFirstStageWholePushforwardModuleIso G H V r n).toLinearEquiv.length_eq.trans
    (TorComparison.length_restrictScalars_of_surjective _
      (targetStalkLocalizationIso V.2 r).symm.commRingCatIsoToRingEquiv.surjective _)

/-- The original finite-pushed stalk family at a generic point has genuine
finite length and finite outer support, transported from the same whole family. -/
theorem rightFirstStagePushforwardAtGeneric_finiteLengthSupport
    (hr : V.2.fromSpec r ∈ genericPoints (F.rightIntermediateImageProduct G H)) :
    FiniteLengthSupport (F.rightFirstStagePushforwardCoefficient G H V r) := by
  have := coordinateFinite (F.rightIntermediateImageMap G H) V.2
  have := coordinateLocal_noetherian V.2 r
  exact RightGenericWeightAux.finiteLengthSupport_of_lengths
    ((F.rightFirstStageWholeAtGeneric_finiteLengthSupport G H V r hr).finiteAlgebra_restrict
      (Localization.AtPrime r.asIdeal)
      (FiniteFiber.localAlgebra Γ(F.rightIntermediateImageProduct G H, V)
        Γ(F.rightIntermediateSupportProduct G H, (F.rightIntermediateImageMap G H) ⁻¹ᵁ V) r)
      (F.rightFirstStageWholeLocalizedCoefficient G H V r))
    (F.rightFirstStageWholePushforward_coefficient_length G H V r)

/-- Use canonical commutative-localization instances at variable maximal points. -/
local instance rightGenericWeightLocalizationRing {R : Type u} [CommRing R]
    (P : Ideal R) [P.IsPrime] : Ring (Localization.AtPrime P) :=
  (inferInstance : CommRing (Localization.AtPrime P)).toRing

/-- The canonical semiring structure on the same localization at the actual prime. -/
local instance rightGenericWeightLocalizationSemiring {R : Type u} [CommRing R]
    (P : Ideal R) [P.IsPrime] : Semiring (Localization.AtPrime P) :=
  (inferInstance : CommRing (Localization.AtPrime P)).toSemiring

/-- A maximal localization of the actual whole coefficient has the length of
the original whole-open generic Tor stalk. Both scalar changes are the actual
source-localization and open-inclusion maps; nilpotents are not discarded. -/
theorem rightFirstStageWholeMaximal_genericStalk_length
    (hr : V.2.fromSpec r ∈ genericPoints (F.rightIntermediateImageProduct G H))
    (a : MaximalSpectrum
      (FiniteFiber.localAlgebra Γ(F.rightIntermediateImageProduct G H, V)
        Γ(F.rightIntermediateSupportProduct G H, (F.rightIntermediateImageMap G H) ⁻¹ᵁ V) r))
    (n : ℕ) :
    let w := (F.rightFirstStageWholeGenericFiberEquiv G H V r hr
      (wholeAlgebraFiberEquiv (F.rightIntermediateImageMap G H) V.2 r a)).1
    Module.length (Localization.AtPrime a.asIdeal)
      ((ModuleCat.extendScalars
        (R := FiniteFiber.localAlgebra Γ(F.rightIntermediateImageProduct G H, V)
          Γ(F.rightIntermediateSupportProduct G H, (F.rightIntermediateImageMap G H) ⁻¹ᵁ V) r)
        (S := Localization.AtPrime a.asIdeal) (algebraMap
        (FiniteFiber.localAlgebra Γ(F.rightIntermediateImageProduct G H, V)
          Γ(F.rightIntermediateSupportProduct G H, (F.rightIntermediateImageMap G H) ⁻¹ᵁ V) r)
        (Localization.AtPrime a.asIdeal))).obj
          (F.rightFirstStageWholeLocalizedCoefficient G H V r n)) =
      Module.length ((F.rightFirstStageWholeOpen G H V).presheaf.stalk w.1)
        (F.rightFirstStageWholeGenericStalk G H V w n) := by
  let x := wholeAlgebraFiberEquiv (F.rightIntermediateImageMap G H) V.2 r a
  let w : genericPoints (F.rightFirstStageWholeOpen G H V) :=
    (F.rightFirstStageWholeGenericFiberEquiv G H V r hr x).1
  let supported : ModuleCat ((F.rightIntermediateSupportProduct G H).presheaf.stalk x.1) :=
    F.rightFirstStageSupportedStalkTor G H x.1 n
  let stalk : ModuleCat ((F.rightFirstStageWholeOpen G H V).presheaf.stalk w.1) :=
    F.rightFirstStageWholeGenericStalk G H V w n
  have hsource := (F.rightFirstStageWholeMaximalCoefficientIso G H V r a n).toLinearEquiv.length_eq
  let sourceIso := originalSourceLocalizationIso (F.rightIntermediateImageMap G H) V.2 r a
  have hsourceRestriction := TorComparison.length_restrictScalars_of_surjective
    sourceIso.hom.hom sourceIso.commRingCatIsoToRingEquiv.surjective supported
  have hopen := (wholeFiberTorCoefficientOriginalStalkIso
    (F.tripleSupportProductInclusion G H)
    (correspondenceSecondAmbientInclusion X.hom Y.hom Z.hom W.hom)
    (F.rightIntermediateSupportInclusion G H) (F.rightIntermediateToTripleSupport G H)
    (F.rightIntermediate_ambient_isPullback G H) (F.rightIntermediateImageMap G H)
    V w.1 n).toLinearEquiv.length_eq
  have hopenRestriction := TorComparison.length_restrictScalars_of_surjective
    (((F.rightIntermediateImageMap G H) ⁻¹ᵁ V).ι.stalkMap w.1).hom
    (((F.rightIntermediateImageMap G H) ⁻¹ᵁ V).ι.stalkMap_surjective w.1) stalk
  exact (hsource.trans hsourceRestriction).trans (hopen.symm.trans hopenRestriction)

/-- At a generic point of the original target, the all-degree Euler of the
original finite pushforward sheaf is the actual finite-pushed whole Tor cycle
coefficient on V. The finite-algebra theorem performs the justified degree/fiber
exchange using the proved common finite support. -/
theorem rightFirstStagePushforwardAtGenericEuler_eq_cycleCoefficient
    (hr : V.2.fromSpec r ∈ genericPoints (F.rightIntermediateImageProduct G H)) :
    signedLengthSum (F.rightFirstStagePushforwardCoefficient G H V r) (fun n => (-1 : ℤ) ^ n)
        (F.rightFirstStagePushforwardAtGeneric_finiteLengthSupport G H V r hr) =
      IntegralCycle.toPoints
        (IntegralCycle.finitePushforward (F.rightIntermediateImageMap G H ∣_ V)
          (F.rightFirstStageWholeTorGenericCycle G H V))
        (F.rightFirstStageTargetChartOpenPoint G H V r) := by
  classical
  have := coordinateFinite (F.rightIntermediateImageMap G H) V.2
  have := coordinateLocal_noetherian V.2 r
  let R := Localization.AtPrime r.asIdeal
  let T := FiniteFiber.localAlgebra Γ(F.rightIntermediateImageProduct G H, V)
    Γ(F.rightIntermediateSupportProduct G H, (F.rightIntermediateImageMap G H) ⁻¹ᵁ V) r
  let M : ℕ → ModuleCat.{u} T := F.rightFirstStageWholeLocalizedCoefficient G H V r
  let hM : FiniteLengthSupport M := F.rightFirstStageWholeAtGeneric_finiteLengthSupport G H V r hr
  have : Finite (MaximalSpectrum T) := LocalLength.finiteAlgebra_maximalSpectrum_finite R T
  let : Fintype (MaximalSpectrum T) := Fintype.ofFinite _
  let A := {x : F.rightIntermediateSupportProduct G H //
    F.rightIntermediateImageMap G H x = V.2.fromSpec r}
  let B := {w : genericPoints (F.rightFirstStageWholeOpen G H V) //
    (F.rightIntermediateImageMap G H ∣_ V) w.1 =
      F.rightFirstStageTargetChartOpenPoint G H V r}
  let e : A ≃ B := F.rightFirstStageWholeGenericFiberEquiv G H V r hr
  let d : A → ℤ := fun x => ((F.rightIntermediateImageMap G H).residueDegree x.1 : ℤ) *
    F.rightFirstStageWholeTorGenericCoefficient G H V (e x).1
  calc
    _ = signedLengthSum
        (fun n => (ModuleCat.restrictScalars (algebraMap R T)).obj (M n))
        (fun n => (-1 : ℤ) ^ n) (hM.finiteAlgebra_restrict R T M) :=
      RightGenericWeightAux.signedLengthSum_eq_of_lengths
        (M := F.rightFirstStagePushforwardCoefficient G H V r)
        (N := fun n => (ModuleCat.restrictScalars (algebraMap R T)).obj (M n))
        (fun n => (-1 : ℤ) ^ n)
        (F.rightFirstStagePushforwardAtGeneric_finiteLengthSupport G H V r hr)
        (hM.finiteAlgebra_restrict R T M)
        (fun n => (F.rightFirstStageWholePushforward_coefficient_length G H V r n).symm)
    _ = ∑ a : MaximalSpectrum T, (LocalLength.finiteAlgebraResidueDegree R T a : ℤ) *
        signedLengthSum
          (fun n => (ModuleCat.extendScalars (R := T) (S := Localization.AtPrime a.asIdeal)
            (algebraMap T (Localization.AtPrime a.asIdeal))).obj
            (M n)) (fun n => (-1 : ℤ) ^ n) (hM.finiteAlgebra_localized R T M a) :=
      signedLengthSum_finiteAlgebra R T M (fun n => (-1 : ℤ) ^ n) hM
    _ = ∑ᶠ a : MaximalSpectrum T,
        d (wholeAlgebraFiberEquiv (F.rightIntermediateImageMap G H) V.2 r a) := by
      refine Eq.trans (b := ∑ a : MaximalSpectrum T,
        d (wholeAlgebraFiberEquiv (F.rightIntermediateImageMap G H) V.2 r a))
        ?_ (finsum_eq_sum_of_fintype _).symm
      apply Finset.sum_congr rfl
      intro a _
      dsimp only [d]
      refine congrArg₂ (fun b c : ℤ => b * c) ?_ ?_
      · exact congrArg (fun b : ℕ => (b : ℤ))
          (wholeAlgebra_residueDegree (F.rightIntermediateImageMap G H) V.2 r a)
      · exact RightGenericWeightAux.signedLengthSum_eq_of_lengths
          (M := fun n => (ModuleCat.extendScalars (R := T) (S := Localization.AtPrime a.asIdeal)
            (algebraMap T (Localization.AtPrime a.asIdeal))).obj (M n))
          (N := F.rightFirstStageWholeGenericStalk G H V
            (e (wholeAlgebraFiberEquiv (F.rightIntermediateImageMap G H) V.2 r a)).1)
          (fun n => (-1 : ℤ) ^ n) (hM.finiteAlgebra_localized R T M a)
          (F.rightFirstStageWholeGeneric_finiteLengthSupport G H V
            (e (wholeAlgebraFiberEquiv (F.rightIntermediateImageMap G H) V.2 r a)).1)
          (F.rightFirstStageWholeMaximal_genericStalk_length G H V r hr a)
    _ = ∑ᶠ x : A, d x :=
      finsum_comp_equiv (wholeAlgebraFiberEquiv (F.rightIntermediateImageMap G H) V.2 r)
    _ = ∑ᶠ w : B, d (e.symm w) := (finsum_comp_equiv e.symm (f := d)).symm
    _ = ∑ᶠ w : B, F.rightFirstStageWholeTorGenericCoefficient G H V w.1 *
        ((F.rightIntermediateImageMap G H ∣_ V).residueDegree w.1.1 : ℤ) := by
      apply finsum_congr
      intro w
      dsimp only [d]
      rw [e.apply_symm_apply]
      change ((F.rightIntermediateImageMap G H).residueDegree w.1.1.1 : ℤ) *
        F.rightFirstStageWholeTorGenericCoefficient G H V w.1 = _
      rw [F.rightFirstStageWholeOpen_residueDegree G H V w.1.1]
      exact mul_comm _ _
    _ = _ := (F.rightFirstStageWholeTorGenericCycle_pushforward_coefficient G H V _).symm

variable (p : Spec Γ(F.rightIntermediateImageProduct G H, V))

/-- The exact missing attachment: the existing localized target Euler weight,
at the inverse of the original target-generic index, is the actual point
coefficient of the finite-pushed existing whole Tor cycle on the SAME affine V. -/
theorem rightFirstStagePushforwardGenericEuler_eq_finitePushforward_coefficient
    (q : {q : genericPoints (F.rightIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p}) :
    F.rightFirstStagePushforwardGenericEuler G H V p
        ((F.rightFirstStageTargetGenericEquiv G H V p).symm q) =
      IntegralCycle.toPoints
        (IntegralCycle.finitePushforward (F.rightIntermediateImageMap G H ∣_ V)
          (F.rightFirstStageWholeTorGenericCycle G H V))
        ⟨q.1.1, F.rightFirstStagePushforwardGeneric_mem G H V p q⟩ := by
  let y : V.1.toScheme := ⟨q.1.1, F.rightFirstStagePushforwardGeneric_mem G H V p q⟩
  let r := V.2.primeIdealOf y
  have hr : V.2.fromSpec r = q.1.1 := V.2.fromSpec_primeIdealOf y
  have hg : V.2.fromSpec r ∈ genericPoints (F.rightIntermediateImageProduct G H) :=
    hr.symm ▸ q.1.2
  calc
    _ = signedLengthSum (F.rightFirstStagePushforwardCoefficient G H V r)
        (fun n => (-1 : ℤ) ^ n)
        (F.rightFirstStagePushforwardAtGeneric_finiteLengthSupport G H V r hg) := by
      unfold rightFirstStagePushforwardGenericEuler signedLengthSum
      apply finsum_congr
      intro n
      rw [F.rightFirstStagePushforwardGenericLength_eq_original G H V p q n]
      simp only [integerLength, rightFirstStagePushforwardGenericStalk,
        rightFirstStagePushforwardCoefficient]
      exact congrArg
        (fun z : F.rightIntermediateImageProduct G H =>
          (-1 : ℤ) ^ n *
            ((Module.length ((F.rightIntermediateImageProduct G H).presheaf.stalk z)
              ((ModuleStalk.functor z).obj
                ((Scheme.Modules.pushforward (F.rightIntermediateImageMap G H)).obj
                  (F.rightFirstStageWholeAmbientCoefficient G H V n)))).toNat : ℤ))
        hr.symm
    _ = _ := by
      have h := F.rightFirstStagePushforwardAtGenericEuler_eq_cycleCoefficient G H V r hg
      simpa only [rightFirstStageTargetChartOpenPoint, hr] using h

end Motivic.FiniteCorrespondenceGenerator
