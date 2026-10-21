/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.RightWholeFiberTorRemainingOuterSum
public import Motivic.Aglib.AlgebraicGeometry.Stalk.Generic.Localization
public import Motivic.Aglib.Algebra.Homology.Koszul.CycleReplacement

/-!
# Fixed-support replacement on the original right finite-image target stalk

The actual right image-product stalk is the common support ring, with fixed
ideal zero in every outer Tor degree. The remaining Y-diagonal list cuts out
the actual right final image incidence, whose generic stalk is Artinian.
Finite generation of the actual pushed coefficient follows from the whole
right finite algebra; its degree bound comes from the original smooth Z
diagonal. The resulting generic weights are literal localizations of the
actual right pushforward stalk. Attachment to global generic sheaf stalks and
to the iterated correspondence cycle remains a separate obligation.

This source-only continuation awaits its own compiler, lint, axiom, and
independent-review gates. Its right outer-sum dependency is not admitted by
this packet. No left target-replacement theorem is imported or used.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Hom
open _root_.AlgebraicGeometry.Scheme.Products

open _root_.AlgebraicGeometry.Scheme.Intersection
open _root_.AlgebraicGeometry.Scheme.Modules.Pushforward.FiniteEuler
open _root_.HomologicalComplex.ModuleLengthEuler

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

/-- The genuine target remaining incidence is cut out by the literal pullback
of the same middle diagonal, including its nonreduced ideal sheaf. -/
theorem rightImageRemaining_kernel [IsSeparated g] :
    (F.rightImageIncidenceInclusion G H).ker =
      (pullback.diagonal g).ker.comap (F.rightImageMiddlePair G H) :=
  ker_eq_comap_of_isPullback _ _ _ _ (F.rightImageIncidenceRemaining_isPullback G H).flip

/-- The original common list generates the exact target remaining-support ideal. -/
theorem rightTargetRemainingList_ideal [IsSeparated g]
    (x : F.rightIntermediateImageProduct G H)
    (s : List ((pullback g g).presheaf.stalk (F.rightImageMiddlePair G H x)))
    (hs : (pullback.diagonal g).ker.stalk (F.rightImageMiddlePair G H x) = Ideal.ofList s) :
    Ideal.ofList (F.rightTargetRemainingList G H x s) =
      (F.rightImageIncidenceInclusion G H).ker.stalk x := by
  rw [F.rightImageRemaining_kernel G H, Scheme.IdealSheafData.stalk_comap,
    hs, Ideal.map_ofList]
  rfl

/-- Properness of the actual final-incidence stalk kernel puts every remaining
equation in the original target maximal ideal. -/
theorem rightTargetRemainingList_mem_maximalIdeal [IsSeparated g]
    (x : F.rightIntermediateImageProduct G H) (y : F.rightImageIncidence G H)
    (hxy : x = F.rightImageIncidenceInclusion G H y)
    (s : List ((pullback g g).presheaf.stalk (F.rightImageMiddlePair G H x)))
    (hs : (pullback.diagonal g).ker.stalk (F.rightImageMiddlePair G H x) = Ideal.ofList s) :
    ∀ a ∈ F.rightTargetRemainingList G H x s,
      a ∈ IsLocalRing.maximalIdeal ((F.rightIntermediateImageProduct G H).presheaf.stalk x) := by
  have hproper : (F.rightImageIncidenceInclusion G H).ker.stalk x ≠ ⊤ := by
    rw [hxy, (F.rightImageIncidenceInclusion G H).ker_stalk y]
    exact RingHom.ker_ne_top _
  have hle := IsLocalRing.le_maximalIdeal hproper
  rw [← F.rightTargetRemainingList_ideal G H x s hs] at hle
  intro a ha
  exact hle (Ideal.subset_span ha)

/-- With the fixed support ideal zero, the remaining-support quotient is the
actual generic final-incidence stalk and is therefore Artinian. -/
theorem rightTargetRemainingList_support_isArtinian [IsSeparated g]
    [IsLocallyNoetherian (F.rightIntermediateImageProduct G H)]
    (x : F.rightIntermediateImageProduct G H) (y : F.rightImageIncidence G H)
    (hy : y ∈ genericPoints (F.rightImageIncidence G H))
    (hxy : x = F.rightImageIncidenceInclusion G H y)
    (s : List ((pullback g g).presheaf.stalk (F.rightImageMiddlePair G H x)))
    (hs : (pullback.diagonal g).ker.stalk (F.rightImageMiddlePair G H x) = Ideal.ofList s) :
    IsArtinianRing (((F.rightIntermediateImageProduct G H).presheaf.stalk x) ⧸
      (Ideal.ofList (F.rightTargetRemainingList G H x s) ⊔ ⊥)) := by
  have hclosed : IsClosedImmersion (F.rightImageIncidenceInclusion G H) := inferInstance
  have hfinite := (IsClosedImmersion.iff_isFinite_and_mono
    (F.rightImageIncidenceInclusion G H)).mp hclosed
  have : LocallyOfFiniteType (F.rightImageIncidenceInclusion G H) :=
    ((IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mp hfinite.1).2
  have := LocallyOfFiniteType.isLocallyNoetherian (F.rightImageIncidenceInclusion G H)
  rw [sup_bot_eq, F.rightTargetRemainingList_ideal G H x s hs,
    hxy, (F.rightImageIncidenceInclusion G H).ker_stalk y]
  exact stalk_quotient_ker_isArtinian (F.rightImageIncidenceInclusion G H) y hy

variable [S.IsSeparated] [IsSeparated f] [IsSeparated g] [IsSeparated h] [IsSeparated i]

/-- The separatedness instance used in this module. -/
local instance cyclesRightWholeFiberTorTargetReplacementSeparated
    : (correspondenceSixfoldAmbient f g h i).IsSeparated :=
  correspondenceSixfoldAmbient_isSeparated f g h i

variable (V : (F.rightIntermediateImageProduct G H).affineOpens)
  (p : Spec Γ(F.rightIntermediateImageProduct G H, V))

/-- The finite coefficient algebra is the literal original image-product section map. -/
local instance rightTargetReplacementCoordinateAlgebra :
    Algebra Γ(F.rightIntermediateImageProduct G H, V)
      Γ(F.rightIntermediateSupportProduct G H, (F.rightIntermediateImageMap G H) ⁻¹ᵁ V) :=
  ((F.rightIntermediateImageMap G H).app V).hom.toAlgebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]

/-- The actual original pushforward coefficient is finite over the original
target stalk. This uses the whole finite algebra and the original stalk iso. -/
theorem rightFirstStagePushforwardCoefficient_finite (n : ℕ) :
    Module.Finite ((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))
      (F.rightFirstStagePushforwardCoefficient G H V p n) := by
  have := coordinateFinite (F.rightIntermediateImageMap G H) V.2
  let R := Localization.AtPrime p.asIdeal
  let T := _root_.PrimeSpectrum.FiniteFiber.localAlgebra Γ(F.rightIntermediateImageProduct G H, V)
    Γ(F.rightIntermediateSupportProduct G H, (F.rightIntermediateImageMap G H) ⁻¹ᵁ V) p
  let M := F.rightFirstStageWholeLocalizedCoefficient G H V p n
  have : Module.Finite T M := wholeFiberTorLocalizedSections_finite
    (F.tripleSupportProductInclusion G H) (correspondenceSecondAmbientInclusion f g h i)
    (F.rightIntermediateSupportInclusion G H) (F.rightIntermediateToTripleSupport G H)
    (F.rightIntermediate_ambient_isPullback G H) (F.rightIntermediateImageMap G H) V p n
  have hres : Module.Finite R ((ModuleCat.restrictScalars (algebraMap R T)).obj M) := by
    let := Module.compHom M (algebraMap R T)
    have : IsScalarTower R T M := IsScalarTower.of_compHom R T M
    change Module.Finite R M
    exact Module.Finite.trans T M
  let e := targetStalkLocalizationIso V.2 p
  let : RingHomSurjective e.inv.hom :=
    ⟨e.symm.commRingCatIsoToRingEquiv.surjective⟩
  let N := F.rightFirstStagePushforwardCoefficient G H V p n
  let N' := (ModuleCat.restrictScalars e.inv.hom).obj N
  have : Module.Finite R N' := Module.Finite.of_surjective
    (F.rightFirstStageWholePushforwardModuleIso G H V p n).toLinearEquiv.toLinearMap
    (F.rightFirstStageWholePushforwardModuleIso G H V p n).toLinearEquiv.surjective
  let a : N' →ₛₗ[e.inv.hom] N :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact Module.Finite.of_surjective a Function.surjective_id

omit [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)] in
/-- A vanished whole coefficient gives a vanished original pushforward module,
before taking any Euler characteristic or local generic length. -/
theorem rightFirstStagePushforwardCoefficient_subsingleton (n : ℕ)
    [Subsingleton (F.rightFirstStageWholeLocalizedCoefficient G H V p n)] :
    Subsingleton (F.rightFirstStagePushforwardCoefficient G H V p n) := by
  let e := F.rightFirstStageWholePushforwardModuleIso G H V p n
  have hres : Subsingleton ((ModuleCat.restrictScalars
      (algebraMap (Localization.AtPrime p.asIdeal)
        (_root_.PrimeSpectrum.FiniteFiber.localAlgebra Γ(F.rightIntermediateImageProduct G H, V)
          Γ(F.rightIntermediateSupportProduct G H,
            (F.rightIntermediateImageMap G H) ⁻¹ᵁ V) p))).obj
      (F.rightFirstStageWholeLocalizedCoefficient G H V p n)) := by
    change Subsingleton (F.rightFirstStageWholeLocalizedCoefficient G H V p n)
    infer_instance
  have hr := e.toLinearEquiv.toEquiv.subsingleton_congr.mp hres
  change Subsingleton (F.rightFirstStagePushforwardCoefficient G H V p n) at hr
  exact hr

variable [IsLocallyNoetherian (F.rightIntermediateImageProduct G H)]

/-- The original target generic multiplicity uses the same fixed zero ideal
in every outer degree; its finite localized length is proved before conversion. -/
def rightFirstStagePushforwardGenericLength (n : ℕ)
    (q : minimalPrimes
      ((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))) : ℤ :=
  letI := F.rightFirstStagePushforwardCoefficient_finite G H V p n
  _root_.ChainComplex.Koszul.fixedSupportGenericLength (F.rightFirstStagePushforwardCoefficient G H
      V p n) ⊥ bot_le q

/-- The zero fixed support annihilates every genuine coefficient simultaneously;
replacement uses its actual finite localized lengths, not supplied cycle weights. -/
theorem rightFirstStagePushforwardRemainingEuler_replacement
    (s : List ((pullback g g).presheaf.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p))))
    (y : F.rightImageIncidence G H) (hy : y ∈ genericPoints (F.rightImageIncidence G H))
    (hp : V.2.fromSpec p = F.rightImageIncidenceInclusion G H y)
    (hs : (pullback.diagonal g).ker.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s) (n : ℕ) :
    let := F.rightTargetRemainingList_support_isArtinian G H (V.2.fromSpec p) y hy hp s hs
    F.rightFirstStagePushforwardRemainingEuler G H V p s y hy hp hs n =
      ∑ᶠ q : minimalPrimes
          ((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)),
        F.rightFirstStagePushforwardGenericLength G H V p n q *
          chainEuler (_root_.ChainComplex.Koszul.coefficientComplex
            (ModuleCat.of ((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))
              (((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)) ⧸ q.1))
            (F.rightTargetRemainingList G H (V.2.fromSpec p) s))
            (_root_.ChainComplex.Koszul.fixedSupport_prime_finiteHomology
              (F.rightTargetRemainingList G H (V.2.fromSpec p) s) ⊥ q.1 q.2.le) := by
  let := F.rightTargetRemainingList_support_isArtinian G H (V.2.fromSpec p) y hy hp s hs
  let := F.rightFirstStagePushforwardCoefficient_finite G H V p n
  exact _root_.ChainComplex.Koszul.fixedSupport_chainEuler_replacement
    (F.rightFirstStagePushforwardCoefficient G H V p n)
    (F.rightTargetRemainingList G H (V.2.fromSpec p) s) ⊥
    (F.rightTargetRemainingList_mem_maximalIdeal G H (V.2.fromSpec p) y hp s hs) bot_le

/-- The genuine target minimal primes are exactly original image-product
generic points specializing to the chosen final-incidence point. -/
def rightFirstStageTargetGenericEquiv :
    minimalPrimes ((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)) ≃
      {q : genericPoints (F.rightIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p} :=
  (specGenericMinimalPrimeEquiv _).symm.trans
    (stalkGenericPointEquiv (F.rightIntermediateImageProduct G H) (V.2.fromSpec p))

omit [S.IsSeparated] [IsSeparated f] [IsSeparated g] [IsSeparated h] [IsSeparated i]
  [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]
  [IsLocallyNoetherian (F.rightIntermediateImageProduct G H)] in
/-- The inverse generic index retains the exact original local prime. -/
theorem rightFirstStageTargetGenericEquiv_symm_val
    (q : {q : genericPoints (F.rightIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p}) :
    ((F.rightFirstStageTargetGenericEquiv G H V p).symm q).1 =
      (genericStalkLocalizationPrime (F.rightIntermediateImageProduct G H)
        (V.2.fromSpec p) q).asIdeal :=
  rfl


omit [S.IsSeparated] [IsSeparated f] [IsSeparated g] [IsSeparated h] [IsSeparated i]
  [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]
  [IsLocallyNoetherian (F.rightIntermediateImageProduct G H)] in
/-- Reindex a fixed target-generic sum by its genuine global component points.
The specialization condition and every original summand are unchanged. -/
theorem rightFirstStageTargetGeneric_finsum
    (a : minimalPrimes
      ((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)) → ℤ) :
    (∑ᶠ q, a q) =
      ∑ᶠ q : {q : genericPoints (F.rightIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p},
        a ((F.rightFirstStageTargetGenericEquiv G H V p).symm q) :=
  (finsum_comp_equiv (F.rightFirstStageTargetGenericEquiv G H V p).symm (f := a)).symm

/-- The alternating target generic weight is formed only from actual
localized original pushforward modules, using one fixed generic index set. -/
def rightFirstStagePushforwardGenericEuler
    (q : minimalPrimes
      ((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))) : ℤ :=
  ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * F.rightFirstStagePushforwardGenericLength G H V p n q

variable [Flat f] [Flat g] [Smooth h] [Flat i]

/-- The actual whole-fiber degree bound kills every target generic weight at
once; no assumed numerical support bound is used. -/
theorem rightFirstStagePushforwardGenericLength_exists_bound :
    ∃ b : ℕ, ∀ n, b ≤ n → ∀ q,
      F.rightFirstStagePushforwardGenericLength G H V p n q = 0 := by
  obtain ⟨b, hb⟩ := F.rightFirstStageWholeLocalized_exists_bound G H V p
  refine ⟨b, fun n hn q => ?_⟩
  have := hb n hn
  have := F.rightFirstStagePushforwardCoefficient_subsingleton G H V p n
  let : q.1.IsPrime := q.2.isPrime
  simp only [rightFirstStagePushforwardGenericLength,
      _root_.ChainComplex.Koszul.fixedSupportGenericLength,
    integerLength, Module.length_eq_zero, ENat.toNat_zero, Nat.cast_zero]

/-- Actual generic localized multiplicities have finite outer-degree support. -/
theorem rightFirstStagePushforwardGenericLength_finiteSupport
    (q : minimalPrimes ((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))) :
    Function.HasFiniteSupport (fun n => F.rightFirstStagePushforwardGenericLength G H V p n q) := by
  obtain ⟨b, hb⟩ := F.rightFirstStagePushforwardGenericLength_exists_bound G H V p
  apply (Set.finite_Iio b).subset
  intro n hn
  exact Nat.lt_of_not_ge (fun h => hn (hb n h q))

/-- Genuine fixed-support replacement can be summed over all outer Tor degrees.
One actual target generic index set is retained throughout the finite signed sum. -/
theorem rightFirstStagePushforwardRemainingOuter_replacement
    (s : List ((pullback g g).presheaf.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p))))
    (y : F.rightImageIncidence G H) (hy : y ∈ genericPoints (F.rightImageIncidence G H))
    (hp : V.2.fromSpec p = F.rightImageIncidenceInclusion G H y)
    (hs : (pullback.diagonal g).ker.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s) :
    let := F.rightTargetRemainingList_support_isArtinian G H (V.2.fromSpec p) y hy hp s hs
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      F.rightFirstStagePushforwardRemainingEuler G H V p s y hy hp hs n) =
      ∑ᶠ q : minimalPrimes
          ((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)),
        F.rightFirstStagePushforwardGenericEuler G H V p q *
          chainEuler (_root_.ChainComplex.Koszul.coefficientComplex
            (ModuleCat.of ((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))
              (((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)) ⧸ q.1))
            (F.rightTargetRemainingList G H (V.2.fromSpec p) s))
            (_root_.ChainComplex.Koszul.fixedSupport_prime_finiteHomology
              (F.rightTargetRemainingList G H (V.2.fromSpec p) s) ⊥ q.1 q.2.le) := by
  classical
  let := F.rightTargetRemainingList_support_isArtinian G H (V.2.fromSpec p) y hy hp s hs
  let R := (F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)
  let Q := minimalPrimes R
  let : Fintype Q := (Ideal.finite_minimalPrimes_of_isNoetherianRing R ⊥).fintype
  let L : ℕ → Q → ℤ := F.rightFirstStagePushforwardGenericLength G H V p
  let C : Q → ℤ := fun q => chainEuler
    (_root_.ChainComplex.Koszul.coefficientComplex (ModuleCat.of R (R ⧸ q.1))
      (F.rightTargetRemainingList G H (V.2.fromSpec p) s))
    (_root_.ChainComplex.Koszul.fixedSupport_prime_finiteHomology
      (F.rightTargetRemainingList G H (V.2.fromSpec p) s) ⊥ q.1 q.2.le)
  have hproj (n : ℕ) : F.rightFirstStagePushforwardRemainingEuler G H V p s y hy hp hs n =
      ∑ᶠ q : Q, L n q * C q :=
    F.rightFirstStagePushforwardRemainingEuler_replacement G H V p s y hy hp hs n
  have hfin (q : Q) : Function.HasFiniteSupport
      (fun n : ℕ => (-1 : ℤ) ^ n * (L n q * C q)) := by
    apply (F.rightFirstStagePushforwardGenericLength_finiteSupport G H V p q).subset
    intro n hn hz
    change L n q = 0 at hz
    exact hn (by change (-1 : ℤ) ^ n * (L n q * C q) = 0; rw [hz, zero_mul, mul_zero])
  change (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      F.rightFirstStagePushforwardRemainingEuler G H V p s y hy hp hs n) =
    ∑ᶠ q : Q, (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * L n q) * C q
  simp_rw [hproj, finsum_eq_sum_of_fintype, Finset.mul_sum]
  rw [finsum_sum_comm Finset.univ _ (fun q _ => hfin q)]
  apply Finset.sum_congr rfl
  intro q _
  rw [finsum_mul]
  apply finsum_congr
  intro n
  exact (mul_assoc _ _ _).symm

/-- The signed replacement is indexed by the literal global image-product
components specializing to the original final-incidence point. The generic
weights are still actual localized pushforward lengths, not cycle weights. -/
theorem rightFirstStagePushforwardRemainingOuter_globalReplacement
    (s : List ((pullback g g).presheaf.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p))))
    (y : F.rightImageIncidence G H) (hy : y ∈ genericPoints (F.rightImageIncidence G H))
    (hp : V.2.fromSpec p = F.rightImageIncidenceInclusion G H y)
    (hs : (pullback.diagonal g).ker.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s) :
    let := F.rightTargetRemainingList_support_isArtinian G H (V.2.fromSpec p) y hy hp s hs
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      F.rightFirstStagePushforwardRemainingEuler G H V p s y hy hp hs n) =
      ∑ᶠ q : {q : genericPoints (F.rightIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p},
        F.rightFirstStagePushforwardGenericEuler G H V p
            ((F.rightFirstStageTargetGenericEquiv G H V p).symm q) *
          chainEuler (_root_.ChainComplex.Koszul.coefficientComplex
            (ModuleCat.of ((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))
              (((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)) ⧸
                (genericStalkLocalizationPrime (F.rightIntermediateImageProduct G H)
                  (V.2.fromSpec p) q).asIdeal))
            (F.rightTargetRemainingList G H (V.2.fromSpec p) s))
            (_root_.ChainComplex.Koszul.fixedSupport_prime_finiteHomology
              (F.rightTargetRemainingList G H (V.2.fromSpec p) s) ⊥
              (genericStalkLocalizationPrime (F.rightIntermediateImageProduct G H)
                (V.2.fromSpec p) q).asIdeal bot_le) := by
  let := F.rightTargetRemainingList_support_isArtinian G H (V.2.fromSpec p) y hy hp s hs
  rw [F.rightFirstStagePushforwardRemainingOuter_replacement G H V p s y hy hp hs]
  exact F.rightFirstStageTargetGeneric_finsum G H V p _

end Motivic.FiniteCorrespondenceGenerator
