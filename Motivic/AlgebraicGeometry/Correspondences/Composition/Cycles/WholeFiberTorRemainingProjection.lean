/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.WholeFiberTorRemainingLength

/-!
# Actual remaining-Koszul projection in each first-stage Tor degree

The left coefficient is the original finite pushforward of the constructed
whole-preimage Tor equalizer, taken at the original target stalk. Its remaining
Koszul complex is compared with restriction of the actual whole finite-algebra
complex. Every right-hand coefficient is genuine supported Tor on the complete
original source fiber, with the same original middle list and actual residue degree.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Hom
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules.Pushforward
open _root_.AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open _root_.AlgebraicGeometry.Scheme.Products

open _root_.AlgebraicGeometry.Scheme.Intersection
open _root_.AlgebraicGeometry.Scheme.Modules.Pushforward.FiniteEuler
open _root_.HomologicalComplex.ModuleLengthEuler

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  [S.IsSeparated] [IsSeparated f] [IsSeparated g] [IsSeparated h] [IsSeparated i]
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

local instance : (correspondenceSixfoldAmbient f g h i).IsSeparated :=
  correspondenceSixfoldAmbient_isSeparated f g h i

variable (V : (F.leftIntermediateImageProduct G H).affineOpens)
  (p : Spec Γ(F.leftIntermediateImageProduct G H, V))

/-- The coefficient algebra is the actual finite image-product section map. -/
local instance remainingProjectionCoordinateAlgebra :
    Algebra Γ(F.leftIntermediateImageProduct G H, V)
      Γ(F.leftIntermediateSupportProduct G H, (F.leftIntermediateImageMap G H) ⁻¹ᵁ V) :=
  ((F.leftIntermediateImageMap G H).app V).hom.toAlgebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The original target stalk of the actual finite pushforward Tor coefficient. -/
abbrev firstStagePushforwardCoefficient (n : ℕ) :=
  (Stalk.functor (V.2.fromSpec p)).obj
    ((Scheme.Modules.pushforward (F.leftIntermediateImageMap G H)).obj
      (F.firstStageWholeAmbientCoefficient G H V n))

/-- Actual whole coefficient restriction identifies the original global
pushforward stalk, using only quasi-coherence on the full inverse-image open. -/
def firstStageWholePushforwardModuleIso (n : ℕ) :
    (ModuleCat.restrictScalars (algebraMap (Localization.AtPrime p.asIdeal)
      (_root_.PrimeSpectrum.FiniteFiber.localAlgebra Γ(F.leftIntermediateImageProduct G H, V)
        Γ(F.leftIntermediateSupportProduct G H,
          (F.leftIntermediateImageMap G H) ⁻¹ᵁ V) p))).obj
      (F.firstStageWholeLocalizedCoefficient G H V p n) ≅
    (ModuleCat.restrictScalars (targetStalkLocalizationIso V.2 p).inv.hom).obj
      (F.firstStagePushforwardCoefficient G H V p n) := by
  let φ := F.leftIntermediateImageMap G H
  let N := F.firstStageWholeAmbientCoefficient G H V n
  have : ((Scheme.Modules.restrictFunctor (φ ⁻¹ᵁ V).ι).obj N).IsQuasicoherent :=
    wholeFiberTorGlued_relativeQuasicoherent _ _ _ _ _ _ _ n
  have := RelativeAffine.sourceChart_quasicoherent φ V.2 N
  let e := (Stalk.functor p).mapIso
      ((Scheme.Modules.pushforward (FiniteAffineChart.coordinateMap φ)).mapIso
          (asIso (((Scheme.Modules.restrictFunctor
            (FiniteAffineChart.sourceChart φ V.2)).obj N).fromTildeΓ)) ≪≫
        ((FiniteRestriction.wholeChartPushforwardIso φ V.2).app N).symm) ≪≫
    (Stalk.openRestrictionIso V.2.fromSpec p).app ((Scheme.Modules.pushforward φ).obj N)
  exact (ModuleCat.restrictScalars (algebraMap (Localization.AtPrime p.asIdeal)
      (_root_.PrimeSpectrum.FiniteFiber.localAlgebra Γ(F.leftIntermediateImageProduct G H, V)
        Γ(F.leftIntermediateSupportProduct G H, φ ⁻¹ᵁ V) p))).mapIso
      (wholeFiberTorLocalizedSectionsIso (F.tripleSupportProductInclusion G H)
        (correspondenceFirstDiagonalInclusion f g h i) (F.leftIntermediateSupportInclusion G H)
        (F.leftIntermediateToTripleSupport G H) (F.leftIntermediate_ambient_isPullback G H)
        φ V p n).symm ≪≫
    ((Affine.pushforwardPrimeStalkIso Γ(F.leftIntermediateImageProduct G H, V)
      Γ(F.leftIntermediateSupportProduct G H, φ ⁻¹ᵁ V) p).app
        (originalCoordinateModule φ V.2 N)).symm ≪≫
    (ModuleCat.restrictScalars
      (Spec.stalkIso Γ(F.leftIntermediateImageProduct G H, V) p).inv.hom).mapIso e ≪≫
    (ModuleCat.restrictScalarsComp
      (Spec.stalkIso Γ(F.leftIntermediateImageProduct G H, V) p).inv.hom
      (inv (V.2.fromSpec.stalkMap p)).hom).symm.app
        (F.firstStagePushforwardCoefficient G H V p n)

/-- The remaining list acts on the actual original global pushforward stalk. -/
abbrev firstStagePushforwardRemainingKoszul
    (s : List ((pullback h h).presheaf.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p)))) (n : ℕ) :=
  _root_.ChainComplex.Koszul.coefficientComplex (F.firstStagePushforwardCoefficient G H V p n)
    (F.leftTargetRemainingList G H (V.2.fromSpec p) s)

/-- Both actual remaining complexes retain the original scalar maps and differentials. -/
def firstStageWholePushforwardRemainingIso
    (s : List ((pullback h h).presheaf.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p)))) (n : ℕ) :
    finiteAlgebraRestrictedComplex (Localization.AtPrime p.asIdeal)
      (_root_.PrimeSpectrum.FiniteFiber.localAlgebra Γ(F.leftIntermediateImageProduct G H, V)
        Γ(F.leftIntermediateSupportProduct G H, (F.leftIntermediateImageMap G H) ⁻¹ᵁ V) p)
      (F.firstStageWholeRemainingKoszul G H V p s n) ≅
    ((ModuleCat.restrictScalars (targetStalkLocalizationIso V.2 p).inv.hom).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
        (F.firstStagePushforwardRemainingKoszul G H V p s n) := by
  let t := F.leftTargetRemainingList G H (V.2.fromSpec p) s
  let e := targetStalkLocalizationIso V.2 p
  have ht : (t.map e.hom.hom).map e.inv.hom = t := by
    rw [List.map_map]
    change t.map (fun r => e.inv (e.hom r)) = t
    simp only [Iso.hom_inv_id_apply]
    exact List.map_id t
  exact (_root_.ChainComplex.Koszul.coefficientRestrictIso _ (F.firstStageWholeLocalizedCoefficient
      G H V p n)
      (t.map e.hom.hom)).symm ≪≫
    _root_.ChainComplex.Koszul.coefficientIso (F.firstStageWholePushforwardModuleIso G H V p n) _ ≪≫
    _root_.ChainComplex.Koszul.coefficientRestrictIso e.inv.hom (F.firstStagePushforwardCoefficient
        G H V p n) _ ≪≫
    ((ModuleCat.restrictScalars e.inv.hom).mapHomologicalComplex _).mapIso
      (eqToIso (congrArg (_root_.ChainComplex.Koszul.coefficientComplex
        (F.firstStagePushforwardCoefficient G H V p n)) ht))

/-- The genuine restricted whole complex and original pushforward stalk complex
have the same homology lengths through the literal target structure-stalk map. -/
theorem firstStageWholePushforwardRemaining_length
    (s : List ((pullback h h).presheaf.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p)))) (n r : ℕ) :
    Module.length (Localization.AtPrime p.asIdeal)
      ((finiteAlgebraRestrictedComplex (Localization.AtPrime p.asIdeal)
        (_root_.PrimeSpectrum.FiniteFiber.localAlgebra Γ(F.leftIntermediateImageProduct G H, V)
          Γ(F.leftIntermediateSupportProduct G H, (F.leftIntermediateImageMap G H) ⁻¹ᵁ V) p)
        (F.firstStageWholeRemainingKoszul G H V p s n)).homology r) =
    Module.length ((F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))
      ((F.firstStagePushforwardRemainingKoszul G H V p s n).homology r) := by
  let D := F.firstStagePushforwardRemainingKoszul G H V p s n
  let e := targetStalkLocalizationIso V.2 p
  exact ((HomologicalComplex.homologyFunctor _ _ r).mapIso
      (F.firstStageWholePushforwardRemainingIso G H V p s n)).toLinearEquiv.length_eq.trans
    (((D.sc r).mapHomologyIso (ModuleCat.restrictScalars e.inv.hom)).toLinearEquiv.length_eq.trans
      (_root_.ModuleCat.length_restrictScalars_of_surjective e.inv.hom
        e.symm.commRingCatIsoToRingEquiv.surjective _))

/-- Actual localized-complex homology retains every original branch's scalar length. -/
theorem firstStageWholeSourceRemaining_length
    (q : MaximalSpectrum
      (_root_.PrimeSpectrum.FiniteFiber.localAlgebra Γ(F.leftIntermediateImageProduct G H, V)
        Γ(F.leftIntermediateSupportProduct G H, (F.leftIntermediateImageMap G H) ⁻¹ᵁ V) p))
    (s : List ((pullback h h).presheaf.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p)))) (n r : ℕ) :
    Module.length (Localization.AtPrime q.asIdeal)
      ((finiteAlgebraLocalizedComplex
        (_root_.PrimeSpectrum.FiniteFiber.localAlgebra Γ(F.leftIntermediateImageProduct G H, V)
          Γ(F.leftIntermediateSupportProduct G H, (F.leftIntermediateImageMap G H) ⁻¹ᵁ V) p)
        (F.firstStageWholeRemainingKoszul G H V p s n) q).homology r) =
    Module.length ((F.leftIntermediateSupportProduct G H).presheaf.stalk
      (wholeAlgebraFiberEquiv (F.leftIntermediateImageMap G H) V.2 p q).1)
      ((F.firstStageSourceRemainingKoszul G H V p s
        (wholeAlgebraFiberEquiv (F.leftIntermediateImageMap G H) V.2 p q) n).homology r) :=
  (finiteAlgebraLocalizedHomologyIso _
    (F.firstStageWholeRemainingKoszul G H V p s n) q r).toLinearEquiv.length_eq.trans
      (F.firstStageWholeRemainingLocalizedHomology_length G H V p q s n r)

private theorem finiteHomology_of_lengths {R T : Type u} [CommRing R] [CommRing T]
    {C : ChainComplex (ModuleCat.{u} R) ℕ} {D : ChainComplex (ModuleCat.{u} T) ℕ}
    (hC : FiniteHomology C)
    (h : ∀ r, Module.length R (C.homology r) = Module.length T (D.homology r)) :
    FiniteHomology D where
  finite_length r := by rw [← h r]; exact hC.finite_length r
  finite_support := by simpa only [show (fun r => Module.length R (C.homology r)) =
    (fun r => Module.length T (D.homology r)) from funext h] using hC.finite_support

private theorem chainEuler_eq_of_lengths {R T : Type u} [CommRing R] [CommRing T]
    {C : ChainComplex (ModuleCat.{u} R) ℕ} {D : ChainComplex (ModuleCat.{u} T) ℕ}
    (h : ∀ r, Module.length R (C.homology r) = Module.length T (D.homology r))
    (hC : FiniteHomology C) (hD : FiniteHomology D) : chainEuler C hC = chainEuler D hD := by
  unfold chainEuler homologyEuler signedLengthSum
  apply finsum_congr
  intro r
  simp only [integerLength, h r]

variable [IsNoetherianRing
  ((F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))]

/-- Whole remaining finite homology gives the actual pushforward stalk finite homology. -/
theorem firstStagePushforwardRemaining_finiteHomology
    (s : List ((pullback h h).presheaf.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p)))) (n : ℕ)
    (hwhole : FiniteHomology (F.firstStageWholeRemainingKoszul G H V p s n)) :
    FiniteHomology (F.firstStagePushforwardRemainingKoszul G H V p s n) := by
  have := coordinateFinite (F.leftIntermediateImageMap G H) V.2
  have := coordinateLocal_noetherian V.2 p
  exact finiteHomology_of_lengths
    (hwhole.finiteAlgebra_restrict (Localization.AtPrime p.asIdeal) _ _)
    (F.firstStageWholePushforwardRemaining_length G H V p s n)

/-- The same proved whole finite homology supplies every original fiber Euler term. -/
theorem firstStageSourceRemaining_finiteHomology
    (s : List ((pullback h h).presheaf.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p)))) (n : ℕ)
    (hwhole : FiniteHomology (F.firstStageWholeRemainingKoszul G H V p s n))
    (x : {w : F.leftIntermediateSupportProduct G H //
      F.leftIntermediateImageMap G H w = V.2.fromSpec p}) :
    FiniteHomology (F.firstStageSourceRemainingKoszul G H V p s x n) := by
  have := coordinateFinite (F.leftIntermediateImageMap G H) V.2
  have := coordinateLocal_noetherian V.2 p
  obtain ⟨q, rfl⟩ :=
    (wholeAlgebraFiberEquiv (F.leftIntermediateImageMap G H) V.2 p).surjective x
  exact finiteHomology_of_lengths
    (hwhole.finiteAlgebra_localized (Localization.AtPrime p.asIdeal) _ _ q)
    (F.firstStageWholeSourceRemaining_length G H V p q s n)

/-- Actual per-outer-degree projection uses the original global finite pushforward,
the complete original source fiber and the literal original scheme residue degrees. -/
theorem firstStageRemainingProjectionEuler_of_finiteHomology
    (s : List ((pullback h h).presheaf.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p)))) (n : ℕ)
    (hwhole : FiniteHomology (F.firstStageWholeRemainingKoszul G H V p s n)) :
    chainEuler (F.firstStagePushforwardRemainingKoszul G H V p s n)
        (F.firstStagePushforwardRemaining_finiteHomology G H V p s n hwhole) =
      ∑ᶠ x : {w : F.leftIntermediateSupportProduct G H //
        F.leftIntermediateImageMap G H w = V.2.fromSpec p},
        ((F.leftIntermediateImageMap G H).residueDegree x.1 : ℤ) *
          chainEuler (F.firstStageSourceRemainingKoszul G H V p s x n)
            (F.firstStageSourceRemaining_finiteHomology G H V p s n hwhole x) := by
  have := coordinateFinite (F.leftIntermediateImageMap G H) V.2
  have := coordinateLocal_noetherian V.2 p
  let R := Localization.AtPrime p.asIdeal
  let T := _root_.PrimeSpectrum.FiniteFiber.localAlgebra Γ(F.leftIntermediateImageProduct G H, V)
    Γ(F.leftIntermediateSupportProduct G H, (F.leftIntermediateImageMap G H) ⁻¹ᵁ V) p
  let C := F.firstStageWholeRemainingKoszul G H V p s n
  let hres := hwhole.finiteAlgebra_restrict R T C
  let hloc := hwhole.finiteAlgebra_localized R T C
  have : Finite (MaximalSpectrum T) := Module.finiteAlgebra_maximalSpectrum_finite R T
  let : Fintype (MaximalSpectrum T) := Fintype.ofFinite _
  calc
    _ = chainEuler (finiteAlgebraRestrictedComplex R T C) hres :=
      (chainEuler_eq_of_lengths (F.firstStageWholePushforwardRemaining_length G H V p s n)
        _ _).symm
    _ = ∑ᶠ q : MaximalSpectrum T, (Module.finiteAlgebraResidueDegree R T q : ℤ) *
        chainEuler (finiteAlgebraLocalizedComplex T C q) (hloc q) := by
      rw [finsum_eq_sum_of_fintype]
      exact chainEuler_finiteAlgebra R T C hwhole
    _ = ∑ᶠ q : MaximalSpectrum T,
        ((F.leftIntermediateImageMap G H).residueDegree
          (wholeAlgebraFiberEquiv (F.leftIntermediateImageMap G H) V.2 p q).1 : ℤ) *
        chainEuler (F.firstStageSourceRemainingKoszul G H V p s
          (wholeAlgebraFiberEquiv (F.leftIntermediateImageMap G H) V.2 p q) n)
          (F.firstStageSourceRemaining_finiteHomology G H V p s n hwhole
            (wholeAlgebraFiberEquiv (F.leftIntermediateImageMap G H) V.2 p q)) := by
      apply finsum_congr
      intro q
      rw [wholeAlgebra_residueDegree (F.leftIntermediateImageMap G H) V.2 p q]
      congr 1
      exact chainEuler_eq_of_lengths (F.firstStageWholeSourceRemaining_length G H V p q s n) _ _
    _ = _ := finsum_comp_equiv (wholeAlgebraFiberEquiv (F.leftIntermediateImageMap G H) V.2 p)
      (f := fun x => ((F.leftIntermediateImageMap G H).residueDegree x.1 : ℤ) *
        chainEuler (F.firstStageSourceRemainingKoszul G H V p s x n)
          (F.firstStageSourceRemaining_finiteHomology G H V p s n hwhole x))

/-- At actual generic final image-incidence points the whole finite-homology
premise is discharged by the proved geometric support and semilocal descent. -/
theorem firstStageRemainingProjectionEuler
    [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]
    (y : F.leftImageIncidence G H) (hy : y ∈ genericPoints (F.leftImageIncidence G H))
    (hp : V.2.fromSpec p = F.leftImageIncidenceInclusion G H y)
    (s : List ((pullback h h).presheaf.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p))))
    (hs : (pullback.diagonal h).ker.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s) (n : ℕ) :
    let hwhole := F.firstStageWholeRemaining_finiteHomology G H V p y hy hp s hs n
    chainEuler (F.firstStagePushforwardRemainingKoszul G H V p s n)
        (F.firstStagePushforwardRemaining_finiteHomology G H V p s n hwhole) =
      ∑ᶠ x : {w : F.leftIntermediateSupportProduct G H //
        F.leftIntermediateImageMap G H w = V.2.fromSpec p},
        ((F.leftIntermediateImageMap G H).residueDegree x.1 : ℤ) *
          chainEuler (F.firstStageSourceRemainingKoszul G H V p s x n)
            (F.firstStageSourceRemaining_finiteHomology G H V p s n hwhole x) :=
  F.firstStageRemainingProjectionEuler_of_finiteHomology G H V p s n
    (F.firstStageWholeRemaining_finiteHomology G H V p y hy hp s hs n)

end Motivic.FiniteCorrespondenceGenerator
