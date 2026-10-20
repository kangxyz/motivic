/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.AlgebraicGeometry.SpreadingOut
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Spreading the original generic section at primes of an affine finite scheme

The source ring is not assumed reduced or a domain. The only domain is the
base. Every prime above its generic point admits a canonical stalk map into
the original generic fibre, so the original section, including its nilpotent
data, spreads on a genuine open of the original source.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.GenericSection
variable (R B : Type u) [CommRing R] [IsDomain R] [CommRing B] [Algebra R B]

/-- The affine scheme map `Spec B ⟶ Spec R` induced by the given algebra structure. -/
abbrev baseMap : Spec (.of B) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R B))
/-- The canonical map from the spectrum of `FractionRing R` to `Spec R`. -/
abbrev genericMap : Spec (.of (FractionRing R)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
/-- The actual pullback of `Spec B ⟶ Spec R` along `genericMap R`. -/
abbrev genericFiber := pullback (baseMap R B) (genericMap R)

variable (p : PrimeSpectrum B) (hp : Ideal.comap (algebraMap R B) p.asIdeal = ⊥)

include hp in
lemma stalkBase_units (r : nonZeroDivisors R) :
    IsUnit (((StructureSheaf.toStalk B p).hom.comp (algebraMap R B)) r) := by
  have hr : algebraMap R B r ∉ p.asIdeal := by
    intro h
    have : (r : R) ∈ Ideal.comap (algebraMap R B) p.asIdeal := h
    rw [hp, Ideal.mem_bot] at this
    exact (mem_nonZeroDivisors_iff_ne_zero.mp r.property) this
  exact IsLocalization.map_units ((Spec.structureSheaf B).presheaf.stalk p)
    (⟨algebraMap R B r, hr⟩ : p.asIdeal.primeCompl)

/-- The canonical fraction-field map into the original (possibly nonreduced) stalk. -/
def fractionToStalk : FractionRing R →+* (Spec (.of B)).presheaf.stalk p :=
  IsLocalization.lift (M := nonZeroDivisors R) (stalkBase_units R B p hp)

lemma fractionToStalk_comp :
    (fractionToStalk R B p hp).comp (algebraMap R (FractionRing R)) =
      (StructureSheaf.toStalk B p).hom.comp (algebraMap R B) :=
  IsLocalization.lift_comp _

/-- The exact original stalk factors through the exact generic-fibre pullback. -/
def stalkToGenericFiber : Spec ((Spec (.of B)).presheaf.stalk p) ⟶ genericFiber R B :=
  pullback.lift ((Spec (.of B)).fromSpecStalk p)
    (Spec.map (CommRingCat.ofHom (fractionToStalk R B p hp))) (by
      rw [Spec.fromSpecStalk_eq', ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      exact congrArg CommRingCat.ofHom (fractionToStalk_comp R B p hp).symm)

@[reassoc (attr := simp)]
lemma stalkToGenericFiber_fst :
    stalkToGenericFiber R B p hp ≫ pullback.fst (baseMap R B) (genericMap R) =
      (Spec (.of B)).fromSpecStalk p := pullback.lift_fst _ _ _

/-- The original generic section spreads around every actual prime over the
base generic point. Both the section equation and its original stalk value
are retained. No reducedness, separability, or rational-point assumption enters. -/
theorem exists_open_section_of_generic_section [IsNoetherianRing B]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of B)) [LocallyOfFiniteType f]
    (s : genericFiber R B ⟶ Y)
    (hs : s ≫ f = pullback.fst (baseMap R B) (genericMap R)) :
    ∃ (U : (Spec (.of B)).Opens) (hpU : p ∈ U) (t : U.toScheme ⟶ Y),
      t ≫ f = U.ι ∧
      U.fromSpecStalkOfMem p hpU ≫ t = stalkToGenericFiber R B p hp ≫ s := by
  obtain ⟨U, hpU, t, ht, hf⟩ := spread_out_of_isGermInjective'
    (𝟙 (Spec (.of B))) f (stalkToGenericFiber R B p hp ≫ s) (by simp [hs])
  exact ⟨U, hpU, t, by simpa using hf, ht.symm⟩

end AlgebraicGeometry.Scheme.GenericSection
