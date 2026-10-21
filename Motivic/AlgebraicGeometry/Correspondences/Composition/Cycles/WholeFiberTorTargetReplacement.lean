/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.WholeFiberTorRemainingOuterSum
public import Motivic.Aglib.AlgebraicGeometry.Stalk.Generic.Localization
public import Motivic.Aglib.Algebra.Homology.Koszul.CycleReplacement

/-!
# Fixed-support replacement on the original finite-image target stalk

The actual image-product stalk itself is the common support ring: the fixed
ideal is zero in every outer Tor degree. The remaining list cuts out the actual
final image incidence, whose generic stalk is Artinian. Finite generation of
the actual pushed coefficient follows from the whole finite algebra, before
fixed-support replacement is applied. No image-coefficient comparison is an
input. The resulting generic weights are still literal localizations of the
actual pushforward stalk; attachment to global generic sheaf stalks and to the
iterated correspondence cycle are separate obligations.
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
theorem leftImageRemaining_kernel [IsSeparated h] :
    (F.leftImageIncidenceInclusion G H).ker =
      (pullback.diagonal h).ker.comap (F.leftImageMiddlePair G H) :=
  ker_eq_comap_of_isPullback _ _ _ _ (F.leftImageIncidenceRemaining_isPullback G H).flip

/-- The original common list generates the exact target remaining-support ideal. -/
theorem leftTargetRemainingList_ideal [IsSeparated h]
    (x : F.leftIntermediateImageProduct G H)
    (s : List ((pullback h h).presheaf.stalk (F.leftImageMiddlePair G H x)))
    (hs : (pullback.diagonal h).ker.stalk (F.leftImageMiddlePair G H x) = Ideal.ofList s) :
    Ideal.ofList (F.leftTargetRemainingList G H x s) =
      (F.leftImageIncidenceInclusion G H).ker.stalk x := by
  rw [F.leftImageRemaining_kernel G H, Scheme.IdealSheafData.stalk_comap,
    hs, Ideal.map_ofList]
  rfl

/-- Properness of the actual final-incidence stalk kernel puts every remaining
equation in the original target maximal ideal. -/
theorem leftTargetRemainingList_mem_maximalIdeal [IsSeparated h]
    (x : F.leftIntermediateImageProduct G H) (y : F.leftImageIncidence G H)
    (hxy : x = F.leftImageIncidenceInclusion G H y)
    (s : List ((pullback h h).presheaf.stalk (F.leftImageMiddlePair G H x)))
    (hs : (pullback.diagonal h).ker.stalk (F.leftImageMiddlePair G H x) = Ideal.ofList s) :
    ∀ a ∈ F.leftTargetRemainingList G H x s,
      a ∈ IsLocalRing.maximalIdeal ((F.leftIntermediateImageProduct G H).presheaf.stalk x) := by
  have hproper : (F.leftImageIncidenceInclusion G H).ker.stalk x ≠ ⊤ := by
    rw [hxy, (F.leftImageIncidenceInclusion G H).ker_stalk y]
    exact RingHom.ker_ne_top _
  have hle := IsLocalRing.le_maximalIdeal hproper
  rw [← F.leftTargetRemainingList_ideal G H x s hs] at hle
  intro a ha
  exact hle (Ideal.subset_span ha)

/-- With the fixed support ideal zero, the remaining-support quotient is the
actual generic final-incidence stalk and is therefore Artinian. -/
theorem leftTargetRemainingList_support_isArtinian [IsSeparated h]
    [IsLocallyNoetherian (F.leftIntermediateImageProduct G H)]
    (x : F.leftIntermediateImageProduct G H) (y : F.leftImageIncidence G H)
    (hy : y ∈ genericPoints (F.leftImageIncidence G H))
    (hxy : x = F.leftImageIncidenceInclusion G H y)
    (s : List ((pullback h h).presheaf.stalk (F.leftImageMiddlePair G H x)))
    (hs : (pullback.diagonal h).ker.stalk (F.leftImageMiddlePair G H x) = Ideal.ofList s) :
    IsArtinianRing (((F.leftIntermediateImageProduct G H).presheaf.stalk x) ⧸
      (Ideal.ofList (F.leftTargetRemainingList G H x s) ⊔ ⊥)) := by
  have hclosed : IsClosedImmersion (F.leftImageIncidenceInclusion G H) := inferInstance
  have hfinite := (IsClosedImmersion.iff_isFinite_and_mono
    (F.leftImageIncidenceInclusion G H)).mp hclosed
  have : LocallyOfFiniteType (F.leftImageIncidenceInclusion G H) :=
    ((IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mp hfinite.1).2
  have := LocallyOfFiniteType.isLocallyNoetherian (F.leftImageIncidenceInclusion G H)
  rw [sup_bot_eq, F.leftTargetRemainingList_ideal G H x s hs,
    hxy, (F.leftImageIncidenceInclusion G H).ker_stalk y]
  exact stalk_quotient_ker_isArtinian (F.leftImageIncidenceInclusion G H) y hy

variable [S.IsSeparated] [IsSeparated f] [IsSeparated g] [IsSeparated h] [IsSeparated i]

/-- The separatedness instance used in this module. -/
local instance cyclesWholeFiberTorTargetReplacementSeparated
    : (correspondenceSixfoldAmbient f g h i).IsSeparated :=
  correspondenceSixfoldAmbient_isSeparated f g h i

variable (V : (F.leftIntermediateImageProduct G H).affineOpens)
  (p : Spec Γ(F.leftIntermediateImageProduct G H, V))

/-- The finite coefficient algebra is the literal original image-product section map. -/
local instance targetReplacementCoordinateAlgebra :
    Algebra Γ(F.leftIntermediateImageProduct G H, V)
      Γ(F.leftIntermediateSupportProduct G H, (F.leftIntermediateImageMap G H) ⁻¹ᵁ V) :=
  ((F.leftIntermediateImageMap G H).app V).hom.toAlgebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]

/-- The actual original pushforward coefficient is finite over the original
target stalk. This uses the whole finite algebra and the original stalk iso. -/
theorem firstStagePushforwardCoefficient_finite (n : ℕ) :
    Module.Finite ((F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))
      (F.firstStagePushforwardCoefficient G H V p n) := by
  have := coordinateFinite (F.leftIntermediateImageMap G H) V.2
  let R := Localization.AtPrime p.asIdeal
  let T := _root_.PrimeSpectrum.FiniteFiber.localAlgebra Γ(F.leftIntermediateImageProduct G H, V)
    Γ(F.leftIntermediateSupportProduct G H, (F.leftIntermediateImageMap G H) ⁻¹ᵁ V) p
  let M := F.firstStageWholeLocalizedCoefficient G H V p n
  have : Module.Finite T M := wholeFiberTorLocalizedSections_finite
    (F.tripleSupportProductInclusion G H) (correspondenceFirstDiagonalInclusion f g h i)
    (F.leftIntermediateSupportInclusion G H) (F.leftIntermediateToTripleSupport G H)
    (F.leftIntermediate_ambient_isPullback G H) (F.leftIntermediateImageMap G H) V p n
  have hres : Module.Finite R ((ModuleCat.restrictScalars (algebraMap R T)).obj M) := by
    let := Module.compHom M (algebraMap R T)
    have : IsScalarTower R T M := IsScalarTower.of_compHom R T M
    change Module.Finite R M
    exact Module.Finite.trans T M
  let e := targetStalkLocalizationIso V.2 p
  let : RingHomSurjective e.inv.hom :=
    ⟨e.symm.commRingCatIsoToRingEquiv.surjective⟩
  let N := F.firstStagePushforwardCoefficient G H V p n
  let N' := (ModuleCat.restrictScalars e.inv.hom).obj N
  have : Module.Finite R N' := Module.Finite.of_surjective
    (F.firstStageWholePushforwardModuleIso G H V p n).toLinearEquiv.toLinearMap
    (F.firstStageWholePushforwardModuleIso G H V p n).toLinearEquiv.surjective
  let a : N' →ₛₗ[e.inv.hom] N :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact Module.Finite.of_surjective a Function.surjective_id

omit [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)] in
/-- A vanished whole coefficient gives a vanished original pushforward module,
before taking any Euler characteristic or local generic length. -/
theorem firstStagePushforwardCoefficient_subsingleton (n : ℕ)
    [Subsingleton (F.firstStageWholeLocalizedCoefficient G H V p n)] :
    Subsingleton (F.firstStagePushforwardCoefficient G H V p n) := by
  let e := F.firstStageWholePushforwardModuleIso G H V p n
  have hres : Subsingleton ((ModuleCat.restrictScalars
      (algebraMap (Localization.AtPrime p.asIdeal)
        (_root_.PrimeSpectrum.FiniteFiber.localAlgebra Γ(F.leftIntermediateImageProduct G H, V)
          Γ(F.leftIntermediateSupportProduct G H,
            (F.leftIntermediateImageMap G H) ⁻¹ᵁ V) p))).obj
      (F.firstStageWholeLocalizedCoefficient G H V p n)) := by
    change Subsingleton (F.firstStageWholeLocalizedCoefficient G H V p n)
    infer_instance
  exact e.toLinearEquiv.toEquiv.subsingleton_congr.mp hres

variable [IsLocallyNoetherian (F.leftIntermediateImageProduct G H)]

/-- The original target generic multiplicity uses the same fixed zero ideal
in every outer degree; its finite localized length is proved before conversion. -/
def firstStagePushforwardGenericLength (n : ℕ)
    (q : minimalPrimes
      ((F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))) : ℤ :=
  letI := F.firstStagePushforwardCoefficient_finite G H V p n
  _root_.ChainComplex.Koszul.fixedSupportGenericLength (F.firstStagePushforwardCoefficient G H V p
      n) ⊥ bot_le q

/-- The zero fixed support annihilates every genuine coefficient simultaneously;
replacement uses its actual finite localized lengths, not supplied cycle weights. -/
theorem firstStagePushforwardRemainingEuler_replacement
    (s : List ((pullback h h).presheaf.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p))))
    (y : F.leftImageIncidence G H) (hy : y ∈ genericPoints (F.leftImageIncidence G H))
    (hp : V.2.fromSpec p = F.leftImageIncidenceInclusion G H y)
    (hs : (pullback.diagonal h).ker.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s) (n : ℕ) :
    let := F.leftTargetRemainingList_support_isArtinian G H (V.2.fromSpec p) y hy hp s hs
    F.firstStagePushforwardRemainingEuler G H V p s y hy hp hs n =
      ∑ᶠ q : minimalPrimes
          ((F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)),
        F.firstStagePushforwardGenericLength G H V p n q *
          chainEuler (_root_.ChainComplex.Koszul.coefficientComplex
            (ModuleCat.of ((F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))
              (((F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)) ⧸ q.1))
            (F.leftTargetRemainingList G H (V.2.fromSpec p) s))
            (_root_.ChainComplex.Koszul.fixedSupport_prime_finiteHomology
              (F.leftTargetRemainingList G H (V.2.fromSpec p) s) ⊥ q.1 q.2.le) := by
  let := F.leftTargetRemainingList_support_isArtinian G H (V.2.fromSpec p) y hy hp s hs
  let := F.firstStagePushforwardCoefficient_finite G H V p n
  exact _root_.ChainComplex.Koszul.fixedSupport_chainEuler_replacement
    (F.firstStagePushforwardCoefficient G H V p n)
    (F.leftTargetRemainingList G H (V.2.fromSpec p) s) ⊥
    (F.leftTargetRemainingList_mem_maximalIdeal G H (V.2.fromSpec p) y hp s hs) bot_le

/-- The genuine target minimal primes are exactly original image-product
generic points specializing to the chosen final-incidence point. -/
def firstStageTargetGenericEquiv :
    minimalPrimes ((F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)) ≃
      {q : genericPoints (F.leftIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p} :=
  (specGenericMinimalPrimeEquiv _).symm.trans
    (stalkGenericPointEquiv (F.leftIntermediateImageProduct G H) (V.2.fromSpec p))

omit [S.IsSeparated] [IsSeparated f] [IsSeparated g] [IsSeparated h] [IsSeparated i]
  [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]
  [IsLocallyNoetherian (F.leftIntermediateImageProduct G H)] in
/-- The inverse generic index retains the exact original local prime. -/
theorem firstStageTargetGenericEquiv_symm_val
    (q : {q : genericPoints (F.leftIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p}) :
    ((F.firstStageTargetGenericEquiv G H V p).symm q).1 =
      (genericStalkLocalizationPrime (F.leftIntermediateImageProduct G H)
        (V.2.fromSpec p) q).asIdeal :=
  rfl


omit [S.IsSeparated] [IsSeparated f] [IsSeparated g] [IsSeparated h] [IsSeparated i]
  [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]
  [IsLocallyNoetherian (F.leftIntermediateImageProduct G H)] in
/-- Reindex a fixed target-generic sum by its genuine global component points.
The specialization condition and every original summand are unchanged. -/
theorem firstStageTargetGeneric_finsum
    (a : minimalPrimes ((F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)) → ℤ) :
    (∑ᶠ q, a q) =
      ∑ᶠ q : {q : genericPoints (F.leftIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p},
        a ((F.firstStageTargetGenericEquiv G H V p).symm q) :=
  (finsum_comp_equiv (F.firstStageTargetGenericEquiv G H V p).symm (f := a)).symm

/-- The alternating target generic weight is formed only from actual
localized original pushforward modules, using one fixed generic index set. -/
def firstStagePushforwardGenericEuler
    (q : minimalPrimes
      ((F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))) : ℤ :=
  ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * F.firstStagePushforwardGenericLength G H V p n q

variable [Flat f] [Smooth g] [Flat h] [Flat i]

/-- The actual whole-fiber degree bound kills every target generic weight at
once; no assumed numerical support bound is used. -/
theorem firstStagePushforwardGenericLength_exists_bound :
    ∃ b : ℕ, ∀ n, b ≤ n → ∀ q,
      F.firstStagePushforwardGenericLength G H V p n q = 0 := by
  obtain ⟨b, hb⟩ := F.firstStageWholeLocalized_exists_bound G H V p
  refine ⟨b, fun n hn q => ?_⟩
  have := hb n hn
  have := F.firstStagePushforwardCoefficient_subsingleton G H V p n
  let : q.1.IsPrime := q.2.isPrime
  simp only [firstStagePushforwardGenericLength,
      _root_.ChainComplex.Koszul.fixedSupportGenericLength,
    integerLength, Module.length_eq_zero, ENat.toNat_zero, Nat.cast_zero]

/-- Actual generic localized multiplicities have finite outer-degree support. -/
theorem firstStagePushforwardGenericLength_finiteSupport
    (q : minimalPrimes ((F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))) :
    Function.HasFiniteSupport (fun n => F.firstStagePushforwardGenericLength G H V p n q) := by
  obtain ⟨b, hb⟩ := F.firstStagePushforwardGenericLength_exists_bound G H V p
  apply (Set.finite_Iio b).subset
  intro n hn
  exact Nat.lt_of_not_ge (fun h => hn (hb n h q))

/-- Genuine fixed-support replacement can be summed over all outer Tor degrees.
One actual target generic index set is retained throughout the finite signed sum. -/
theorem firstStagePushforwardRemainingOuter_replacement
    (s : List ((pullback h h).presheaf.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p))))
    (y : F.leftImageIncidence G H) (hy : y ∈ genericPoints (F.leftImageIncidence G H))
    (hp : V.2.fromSpec p = F.leftImageIncidenceInclusion G H y)
    (hs : (pullback.diagonal h).ker.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s) :
    let := F.leftTargetRemainingList_support_isArtinian G H (V.2.fromSpec p) y hy hp s hs
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      F.firstStagePushforwardRemainingEuler G H V p s y hy hp hs n) =
      ∑ᶠ q : minimalPrimes
          ((F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)),
        F.firstStagePushforwardGenericEuler G H V p q *
          chainEuler (_root_.ChainComplex.Koszul.coefficientComplex
            (ModuleCat.of ((F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))
              (((F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)) ⧸ q.1))
            (F.leftTargetRemainingList G H (V.2.fromSpec p) s))
            (_root_.ChainComplex.Koszul.fixedSupport_prime_finiteHomology
              (F.leftTargetRemainingList G H (V.2.fromSpec p) s) ⊥ q.1 q.2.le) := by
  classical
  let := F.leftTargetRemainingList_support_isArtinian G H (V.2.fromSpec p) y hy hp s hs
  let R := (F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)
  let Q := minimalPrimes R
  let : Fintype Q := (Ideal.finite_minimalPrimes_of_isNoetherianRing R ⊥).fintype
  let L : ℕ → Q → ℤ := F.firstStagePushforwardGenericLength G H V p
  let C : Q → ℤ := fun q => chainEuler
    (_root_.ChainComplex.Koszul.coefficientComplex (ModuleCat.of R (R ⧸ q.1))
      (F.leftTargetRemainingList G H (V.2.fromSpec p) s))
    (_root_.ChainComplex.Koszul.fixedSupport_prime_finiteHomology
      (F.leftTargetRemainingList G H (V.2.fromSpec p) s) ⊥ q.1 q.2.le)
  have hproj (n : ℕ) : F.firstStagePushforwardRemainingEuler G H V p s y hy hp hs n =
      ∑ᶠ q : Q, L n q * C q :=
    F.firstStagePushforwardRemainingEuler_replacement G H V p s y hy hp hs n
  have hfin (q : Q) : Function.HasFiniteSupport
      (fun n : ℕ => (-1 : ℤ) ^ n * (L n q * C q)) := by
    apply (F.firstStagePushforwardGenericLength_finiteSupport G H V p q).subset
    intro n hn hz
    change L n q = 0 at hz
    exact hn (by change (-1 : ℤ) ^ n * (L n q * C q) = 0; rw [hz, zero_mul, mul_zero])
  change (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      F.firstStagePushforwardRemainingEuler G H V p s y hy hp hs n) =
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
theorem firstStagePushforwardRemainingOuter_globalReplacement
    (s : List ((pullback h h).presheaf.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p))))
    (y : F.leftImageIncidence G H) (hy : y ∈ genericPoints (F.leftImageIncidence G H))
    (hp : V.2.fromSpec p = F.leftImageIncidenceInclusion G H y)
    (hs : (pullback.diagonal h).ker.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s) :
    let := F.leftTargetRemainingList_support_isArtinian G H (V.2.fromSpec p) y hy hp s hs
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      F.firstStagePushforwardRemainingEuler G H V p s y hy hp hs n) =
      ∑ᶠ q : {q : genericPoints (F.leftIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p},
        F.firstStagePushforwardGenericEuler G H V p
            ((F.firstStageTargetGenericEquiv G H V p).symm q) *
          chainEuler (_root_.ChainComplex.Koszul.coefficientComplex
            (ModuleCat.of ((F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))
              (((F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)) ⧸
                (genericStalkLocalizationPrime (F.leftIntermediateImageProduct G H)
                  (V.2.fromSpec p) q).asIdeal))
            (F.leftTargetRemainingList G H (V.2.fromSpec p) s))
            (_root_.ChainComplex.Koszul.fixedSupport_prime_finiteHomology
              (F.leftTargetRemainingList G H (V.2.fromSpec p) s) ⊥
              (genericStalkLocalizationPrime (F.leftIntermediateImageProduct G H)
                (V.2.fromSpec p) q).asIdeal bot_le) := by
  let := F.leftTargetRemainingList_support_isArtinian G H (V.2.fromSpec p) y hy hp s hs
  rw [F.firstStagePushforwardRemainingOuter_replacement G H V p s y hy hp hs]
  exact F.firstStageTargetGeneric_finsum G H V p _

end Motivic.FiniteCorrespondenceGenerator
