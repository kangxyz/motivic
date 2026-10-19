/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Sections.Generic.Open
public import Motivic.Aglib.AlgebraicGeometry.Sites.Nisnevich.Lifting.FiniteSplitting

/-! # The unchanged generic section spreads over an actual base localization -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.GenericSection
variable (R B : Type u) [CommRing R] [IsDomain R] [CommRing B] [Algebra R B]

abbrev awayMap (r : R) : Spec (.of (Localization.Away r)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))
abbrev awayFiber (r : R) := pullback (baseMap R B) (awayMap R r)

def awayToFraction (r : R) (hr : r ≠ 0) : Localization.Away r →+* FractionRing R :=
  IsLocalization.Away.lift r (IsUnit.mk0 _ ((map_ne_zero_iff _
    (IsFractionRing.injective R (FractionRing R))).mpr hr))

lemma awayToFraction_comp (r : R) (hr : r ≠ 0) :
    (awayToFraction R r hr).comp (algebraMap R (Localization.Away r)) =
      algebraMap R (FractionRing R) := IsLocalization.Away.lift_comp _ _

/-- The canonical original generic-to-localized-fibre map. -/
def genericFiberToAway (r : R) (hr : r ≠ 0) : genericFiber R B ⟶ awayFiber R B r :=
  pullback.map (baseMap R B) (genericMap R) (baseMap R B) (awayMap R r)
    (𝟙 _) (Spec.map (CommRingCat.ofHom (awayToFraction R r hr))) (𝟙 _)
    (by simp) (by
      simp only [Category.comp_id, ← Spec.map_comp]
      exact congrArg Spec.map (congrArg CommRingCat.ofHom (awayToFraction_comp R r hr).symm))

@[reassoc (attr := simp)]
lemma genericFiberToAway_fst (r : R) (hr : r ≠ 0) :
    genericFiberToAway R B r hr ≫ pullback.fst (baseMap R B) (awayMap R r) =
      pullback.fst (baseMap R B) (genericMap R) := by
  simp [genericFiberToAway]

variable [IsFinite (baseMap R B)] [Flat (baseMap R B)]

/-- Finite closed-image removal makes a generic-containing source open contain
the whole pullback over one nonzero principal base open. -/
theorem exists_principal_preimage_le (O : (Spec (.of B)).Opens)
    (hO : genericPoints (Spec (.of B)) ⊆ (O : Set (Spec (.of B)))) :
    ∃ r : R, r ≠ 0 ∧
      Set.range (pullback.fst (baseMap R B) (awayMap R r)) ⊆ (O : Set (Spec (.of B))) := by
  obtain ⟨T, hT, hd⟩ := exists_open_preimage_disjoint_of_isFinite (baseMap R B)
    (O : Set (Spec (.of B)))ᶜ O.isOpen.isClosed_compl (genericPoint (Spec (.of R)))
    (fun x hx h => hx (hO ((baseMap_generic_iff R B x).mp h)))
  obtain ⟨_, ⟨_, ⟨r : R, rfl⟩, rfl⟩, hr, hrT⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hT T.isOpen
  have hr0 : r ≠ 0 := by
    rw [genericPoint_eq_bot_of_affine] at hr
    exact hr
  refine ⟨r, hr0, ?_⟩
  rw [Scheme.Pullback.range_fst]
  change (baseMap R B) ⁻¹' Set.range
    (PrimeSpectrum.comap (algebraMap R (Localization.Away r))) ⊆ _
  rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
  intro x hx
  by_contra hn
  exact Set.disjoint_left.mp hd (hrT hx) hn

/-- The original section over the whole generic fibre extends over the actual
`R[1/r]` base change, with literal equality after the canonical generic restriction.
No reducedness or connectedness is assumed for the finite flat source. -/
theorem exists_section_over_away [IsNoetherianRing B]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of B)) [LocallyOfFiniteType f]
    (s : genericFiber R B ⟶ Y)
    (hs : s ≫ f = pullback.fst (baseMap R B) (genericMap R)) :
    ∃ (r : R) (hr : r ≠ 0) (t : awayFiber R B r ⟶ Y),
      t ≫ f = pullback.fst (baseMap R B) (awayMap R r) ∧
      genericFiberToAway R B r hr ≫ t = s := by
  obtain ⟨O, hO, sO, hsO, he⟩ := exists_generic_open_section R B f s hs
  obtain ⟨r, hr, hpre⟩ := exists_principal_preimage_le R B O hO
  let a : awayFiber R B r ⟶ O.toScheme :=
    IsOpenImmersion.lift O.ι (pullback.fst (baseMap R B) (awayMap R r)) (by
      rw [Opens.range_ι]
      exact hpre)
  have ha : a ≫ O.ι = pullback.fst (baseMap R B) (awayMap R r) :=
    IsOpenImmersion.lift_fac _ _ _
  have heq : genericFiberToAway R B r hr ≫ a = genericFiberToOpen R B O hO := by
    apply (cancel_mono O.ι).mp
    rw [Category.assoc, ha, genericFiberToAway_fst, genericFiberToOpen_ι]
  exact ⟨r, hr, a ≫ sO, by rw [Category.assoc, hsO, ha],
    by rw [← Category.assoc, heq, he]⟩

end AlgebraicGeometry.Scheme.GenericSection
