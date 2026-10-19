/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Stalk.Generic.Localization
public import Motivic.Aglib.AlgebraicGeometry.Stalk.Generic.Support
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Restriction.Open
public import Motivic.Aglib.AlgebraicGeometry.Intersection.ClosedIntersectionTorLocalization
public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.AmbientLength
public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.FlatBaseChangeLocalization
public import Motivic.Aglib.Algebra.Homology.Koszul.CycleReplacement

/-!
# Closed-support generic lengths and actual fundamental-cycle coefficients

The literal kernel ideal of a closed immersion is specialized through the
original structure-stalk map. Its quotient, localized at an actual ambient
component generic, has the coefficient of the pushed fundamental cycle at
that same point. The comparison uses the original, possibly nonreduced,
closed subscheme. Source component generics are not assumed to map to ambient
component generics; genericity is reflected only for the actual inverse image
of the ambient generic under the closed immersion.

Open restriction gives the same coefficient in the actual restricted pushed
fundamental cycle. The point outside the closed image is handled by the unit
stalk ideal and the zero quotient module.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- Specialization extends the actual stalk ideal along the actual stalk map. -/
theorem stalk_map_specializes {x y : X} (h : y ⤳ x) :
    (I.stalk x).map (X.presheaf.stalkSpecializes h).hom = I.stalk y := by
  obtain ⟨U, hU, hxU, -⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ (⊤ : X.Opens) from trivial)
  have hyU : y ∈ U := h.mem_open U.isOpen hxU
  rw [I.stalk_eq_map ⟨U, hU⟩ hxU, I.stalk_eq_map ⟨U, hU⟩ hyU,
    Ideal.map_map]
  exact congrArg (Ideal.map · (I.ideal ⟨U, hU⟩))
    (congrArg CommRingCat.Hom.hom (X.presheaf.germ_stalkSpecializes hxU h))

/-- Away from the actual closed support, the stalk ideal is the unit ideal. -/
theorem stalk_eq_top_of_not_mem_support {x : X} (hx : x ∉ I.support) :
    I.stalk x = ⊤ := by
  classical
  obtain ⟨U, hU, hxU, -⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ (⊤ : X.Opens) from trivial)
  have hz : x ∉ X.zeroLocus (U := U) (I.ideal ⟨U, hU⟩) :=
    mt (Scheme.IdealSheafData.mem_support_iff_of_mem
      (I := I) (U := ⟨U, hU⟩) (x := x) hxU).mpr hx
  simp only [Scheme.mem_zeroLocus_iff, SetLike.mem_coe, not_forall, not_not] at hz
  obtain ⟨s, hs, hxs⟩ := hz
  exact Ideal.eq_top_of_isUnit_mem (I.stalk x) (I.germ_mem_stalk ⟨U, hU⟩ hxU hs)
    ((X.mem_basicOpen s x hxU).mp hxs)

/-- Scalar extension of the quotient uses the same ideal-sheaf stalk at the generization. -/
def stalkQuotientSpecializationIso {x y : X} (h : y ⤳ x) :
    (ModuleCat.extendScalars (X.presheaf.stalkSpecializes h).hom).obj
        (ModuleCat.of (X.presheaf.stalk x) ((X.presheaf.stalk x) ⧸ I.stalk x)) ≅
      ModuleCat.of (X.presheaf.stalk y) ((X.presheaf.stalk y) ⧸ I.stalk y) :=
  _root_.ModuleCat.TorComparison.extendedIdealQuotientIso _ _ ≪≫
    (Ideal.quotientEquivAlgOfEq (X.presheaf.stalk y)
      (I.stalk_map_specializes h)).toLinearEquiv.toModuleIso

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.Hom

variable {E T : Scheme.{u}}

/-- The actual closed-immersion kernel has unit stalk outside its actual image. -/
theorem closedImmersion_ker_stalk_eq_top (j : E ⟶ T) [IsClosedImmersion j]
    {x : T} (hx : x ∉ Set.range j) : j.ker.stalk x = ⊤ := by
  apply j.ker.stalk_eq_top_of_not_mem_support
  change x ∉ (j.ker.support : Set T)
  rw [j.support_ker]
  simpa only [j.isClosedEmbedding.isClosed_range.closure_eq] using hx

/-- Literal quotient localization, with the original generic-stalk scalar isomorphism. -/
def genericStalkQuotientIso (I : T.IdealSheafData) (x : T)
    (q : {q : genericPoints T // q.1 ⤳ x}) :
    ModuleCat.of (Localization.AtPrime (genericStalkLocalizationPrime T x q).asIdeal)
        (Localization.AtPrime (genericStalkLocalizationPrime T x q).asIdeal ⊗[T.presheaf.stalk x]
          ((T.presheaf.stalk x) ⧸ I.stalk x)) ≅
      (ModuleCat.restrictScalars (genericStalkLocalizationIso T x q).inv.hom).obj
        (ModuleCat.of (T.presheaf.stalk q.1.1)
          ((T.presheaf.stalk q.1.1) ⧸ I.stalk q.1.1)) := by
  let M := ModuleCat.of (T.presheaf.stalk x) ((T.presheaf.stalk x) ⧸ I.stalk x)
  let g := (T.presheaf.stalkSpecializes q.2).hom
  let e := (genericStalkLocalizationIso T x q).commRingCatIsoToRingEquiv
  have hg : e.toRingHom.comp g = algebraMap (T.presheaf.stalk x)
      (Localization.AtPrime (genericStalkLocalizationPrime T x q).asIdeal) :=
    congrArg CommRingCat.Hom.hom (stalkSpecializes_genericStalkLocalizationIso T x q)
  exact (LocalizedModule.equivTensorProduct _ M).symm.toModuleIso ≪≫
    _root_.ModuleCat.TorComparison.localizedModuleExtendScalarsIso _ M ≪≫
    eqToIso (congrArg (fun r => (ModuleCat.extendScalars r).obj M) hg.symm) ≪≫
    (ModuleCat.extendScalarsComp g e.toRingHom).app M ≪≫
    (ModuleCat.extendScalars e.toRingHom).mapIso (I.stalkQuotientSpecializationIso q.2) ≪≫
    Intersection.extendScalarsRingEquivIso e _

/-- The localized quotient length is measured in the same actual generic stalk. -/
theorem genericStalkQuotient_length (I : T.IdealSheafData) (x : T)
    (q : {q : genericPoints T // q.1 ⤳ x}) :
    Module.length (Localization.AtPrime (genericStalkLocalizationPrime T x q).asIdeal)
        (Localization.AtPrime (genericStalkLocalizationPrime T x q).asIdeal ⊗[T.presheaf.stalk x]
          ((T.presheaf.stalk x) ⧸ I.stalk x)) =
      Module.length (T.presheaf.stalk q.1.1)
        ((T.presheaf.stalk q.1.1) ⧸ I.stalk q.1.1) := by
  rw [(genericStalkQuotientIso I x q).toLinearEquiv.length_eq]
  exact _root_.ModuleCat.length_restrictScalars_of_surjective _
    (ConcreteCategory.bijective_of_isIso (genericStalkLocalizationIso T x q).inv).2 _

/-- At an actual ambient generic the full quotient length is finite. -/
theorem genericStalkQuotient_length_ne_top [IsLocallyNoetherian T]
    (I : T.IdealSheafData) (x : T) (q : {q : genericPoints T // q.1 ⤳ x}) :
    Module.length (Localization.AtPrime (genericStalkLocalizationPrime T x q).asIdeal)
        (Localization.AtPrime (genericStalkLocalizationPrime T x q).asIdeal ⊗[T.presheaf.stalk x]
          ((T.presheaf.stalk x) ⧸ I.stalk x)) ≠ ⊤ := by
  rw [genericStalkQuotient_length]
  exact stalk_module_length_ne_top_of_mem_genericPoints q.1.1 q.1.2 _

/-- A closed pushforward coefficient at an ambient component generic is the
length of the actual closed-stalk quotient, including zero outside the image. -/
theorem closedImmersion_fundamentalCoefficient_eq_stalkQuotientLength
    (j : E ⟶ T) [IsClosedImmersion j] [IsNoetherian E] (q : genericPoints T) :
    IntegralCycle.toPoints (IntegralCycle.finitePushforward j (fundamentalCycle E)) q.1 =
      ((Module.length (T.presheaf.stalk q.1)
        ((T.presheaf.stalk q.1) ⧸ j.ker.stalk q.1)).toNat : ℤ) := by
  classical
  rw [IntegralCycle.toPoints_finitePushforward_apply, toPoints_fundamentalCycle,
    residuePushforward_eq_mapDomain_of_surjectiveOnStalks]
  change Finsupp.mapDomain j (fundamentalPointCycle E) q.1 = _
  by_cases hq : q.1 ∈ Set.range j
  · obtain ⟨z, hz⟩ := hq
    have hzgen : z ∈ genericPoints E :=
      mem_genericPoints_of_preimmersion_image j z (hz.symm ▸ q.2)
    have hcoeff := Finsupp.mapDomain_apply_of_injective j.isEmbedding.injective
      (fundamentalPointCycle E) z
    rw [hz, fundamentalPointCycle_apply, dite_eq_left hzgen] at hcoeff
    rw [hcoeff, ← hz, j.ker_stalk]
    have hlength : Module.length (T.presheaf.stalk (j z))
        ((T.presheaf.stalk (j z)) ⧸ RingHom.ker (j.stalkMap z).hom) =
        Module.length (E.presheaf.stalk z) (E.presheaf.stalk z) :=
      (Module.length_eq_of_surjective
        (Ideal.Quotient.mk_surjective (I := RingHom.ker (j.stalkMap z).hom))).trans
          (ringLength_eq_of_ringEquiv (stalkQuotientKerEquiv j z))
    rw [hlength]
    rfl
  · rw [Finsupp.mapDomain_of_notMem_range _ _ hq]
    have : Subsingleton ((T.presheaf.stalk q.1) ⧸ j.ker.stalk q.1) :=
      Ideal.Quotient.subsingleton_iff.mpr (closedImmersion_ker_stalk_eq_top j hq)
    simp only [Module.length_eq_zero, ENat.toNat_zero, Nat.cast_zero]

/-- The fixed-support weight at the literal local minimal prime is the
coefficient of the actual pushed closed fundamental cycle at the same generic. -/
theorem fixedSupportGenericLength_closedImmersion
    (j : E ⟶ T) [IsClosedImmersion j] [IsNoetherian E] [IsLocallyNoetherian T]
    (x : T) (q : {q : genericPoints T // q.1 ⤳ x}) :
    _root_.ChainComplex.Koszul.fixedSupportGenericLength
        (ModuleCat.of (T.presheaf.stalk x) ((T.presheaf.stalk x) ⧸ j.ker.stalk x))
        ⊥ bot_le ⟨(genericStalkLocalizationPrime T x q).asIdeal,
          genericStalkLocalizationPrime_mem_minimalPrimes T x q⟩ =
      IntegralCycle.toPoints (IntegralCycle.finitePushforward j (fundamentalCycle E)) q.1.1 := by
  rw [closedImmersion_fundamentalCoefficient_eq_stalkQuotientLength]
  simp only [_root_.ChainComplex.Koszul.fixedSupportGenericLength,
      _root_.HomologicalComplex.ModuleLengthEuler.integerLength]
  rw [genericStalkQuotient_length]

/-- Restriction retains the identical generic point and the identical length
in the actual restricted closed immersion's full fundamental-cycle pushforward. -/
theorem fixedSupportGenericLength_closedImmersion_openRestriction
    (j : E ⟶ T) [IsClosedImmersion j] [IsNoetherian E] [IsLocallyNoetherian T]
    (V : T.Opens) [IsNoetherian (j ⁻¹ᵁ V).toScheme]
    (x : T) (hx : x ∈ V) (q : {q : genericPoints T // q.1 ⤳ x}) :
    _root_.ChainComplex.Koszul.fixedSupportGenericLength
        (ModuleCat.of (T.presheaf.stalk x) ((T.presheaf.stalk x) ⧸ j.ker.stalk x))
        ⊥ bot_le ⟨(genericStalkLocalizationPrime T x q).asIdeal,
          genericStalkLocalizationPrime_mem_minimalPrimes T x q⟩ =
      IntegralCycle.toPoints
        (IntegralCycle.finitePushforward (j ∣_ V) (fundamentalCycle (j ⁻¹ᵁ V).toScheme))
        ⟨q.1.1, q.2.mem_open V.isOpen hx⟩ := by
  let y : V.toScheme := ⟨q.1.1, q.2.mem_open V.isOpen hx⟩
  exact (fixedSupportGenericLength_closedImmersion j x q).trans
    ((IntegralCycle.toPoints_openRestriction_apply V
      (IntegralCycle.finitePushforward j (fundamentalCycle E)) y).symm.trans
        (congrArg (fun c : IntegralCycle V.toScheme => IntegralCycle.toPoints c y)
          (IntegralCycle.openRestriction_finitePushforward_fundamentalCycle j V)))

end AlgebraicGeometry.Scheme.Hom
