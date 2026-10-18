/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.RingTheory.LocalLength.FlatGenericMultiplicity
public import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# A nonreduced generic fiber of length two

The trivial square-zero extension of a field by itself is a literal flat
algebra with a length-two generic local ring. The full generic closed-fiber
factor in flat base-change multiplicity is therefore not always one.
-/

@[expose] public section

-- The nested square-zero/localization scalar structures need three pending levels.
set_option maxSynthPendingDepth 3

open scoped TensorProduct
open TensorProduct Module

universe u

namespace MotivicTest.FlatGenericDualNumbers

variable (k : Type u) [Field k]

/-- The actual dual-number ring, as a trivial square-zero extension. -/
abbrev dualNumbers := TrivSqZeroExt k k

/-- Its projection to the coefficient field. -/
def residueMap : dualNumbers k →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom

/-- The prime of square-zero elements in the actual dual-number ring. -/
def genericPrime : Ideal (dualNumbers k) := RingHom.ker (residueMap k)

instance genericPrime_isPrime : (genericPrime k).IsPrime := RingHom.ker_isPrime _

/-- The dual numbers have length two as a module over themselves, from their
actual square-zero ideal and residue field exact sequence. -/
theorem length_self : Module.length (dualNumbers k) (dualNumbers k) = 2 := by
  let : Algebra (dualNumbers k) k := TrivSqZeroExt.algebraBase k k
  let f : k →ₗ[dualNumbers k] dualNumbers k :=
    { toFun := TrivSqZeroExt.inr
      map_add' := TrivSqZeroExt.inr_add k
      map_smul' := by
        intro b a
        change TrivSqZeroExt.inr (b.fst * a) = b * TrivSqZeroExt.inr a
        apply TrivSqZeroExt.ext <;> simp }
  let g : dualNumbers k →ₗ[dualNumbers k] k := Algebra.linearMap (dualNumbers k) k
  have hf : Function.Injective f := TrivSqZeroExt.inr_injective
  have hg : Function.Surjective g := TrivSqZeroExt.fst_surjective
  have hex : Function.Exact f g := by
    intro b
    constructor
    · intro hb
      refine ⟨b.snd, ?_⟩
      apply TrivSqZeroExt.ext
      · exact hb.symm
      · rfl
    · rintro ⟨a, rfl⟩
      rfl
  have he := Module.length_eq_add_of_exact f g hf hg hex
  have hk : Module.length (dualNumbers k) k = 1 := by
    rw [Module.length_eq_of_surjective (R := k) (M := k)
      (TrivSqZeroExt.fst_surjective : Function.Surjective (algebraMap (dualNumbers k) k))]
    exact Module.length_eq_one k k
  simpa only [hk, one_add_one_eq_two] using he

/-- Every element outside the square-zero prime is already a unit. -/
theorem unit_of_not_mem (b : dualNumbers k) (hb : b ∉ genericPrime k) : IsUnit b := by
  apply TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
  apply isUnit_iff_ne_zero.mpr
  exact hb

/-- Localizing at the actual generic prime preserves the full dual-number
ring, including its nonzero square-zero element. -/
noncomputable def genericLocalizationEquiv :
    Localization.AtPrime (genericPrime k) ≃ₐ[dualNumbers k] dualNumbers k := by
  letI : IsLocalization (genericPrime k).primeCompl (dualNumbers k) :=
    IsLocalization.of_le_isUnit (fun b hb => unit_of_not_mem k b hb)
  exact IsLocalization.algEquiv (genericPrime k).primeCompl _ _

/-- The actual generic local ring has length two. -/
theorem generic_local_length :
    Module.length (Localization.AtPrime (genericPrime k))
      (Localization.AtPrime (genericPrime k)) = 2 := by
  let e := genericLocalizationEquiv k
  have hsurj : Function.Surjective
      (algebraMap (dualNumbers k) (Localization.AtPrime (genericPrime k))) := by
    intro x
    refine ⟨e x, ?_⟩
    apply e.injective
    simp
  rw [← Module.length_eq_of_surjective hsurj, e.toLinearEquiv.length_eq]
  exact length_self k

/-- The square-zero prime is minimal over zero, as every prime contains
all of its square-zero elements. -/
theorem genericPrime_minimal : genericPrime k ∈ (⊥ : Ideal (dualNumbers k)).minimalPrimes := by
  refine ⟨⟨inferInstance, bot_le⟩, ?_⟩
  intro P hP _
  have : P.IsPrime := hP.1
  intro b hb
  have hb0 : b.fst = 0 := hb
  have he : b = TrivSqZeroExt.inr b.snd := by
    apply TrivSqZeroExt.ext
    · exact hb0
    · rfl
  have hsquare : b ^ 2 = 0 := by rw [pow_two, he, TrivSqZeroExt.inr_mul_inr]
  exact hP.1.mem_of_pow_mem 2 (hsquare ▸ P.zero_mem)

/-- Contraction of the actual generic prime to the field is zero. -/
theorem genericPrime_under : (genericPrime k).under k = ⊥ := by
  ext a
  change (residueMap k) (algebraMap k (dualNumbers k) a) = 0 ↔ a = 0
  rfl

/-- The full closed-fiber factor in the actual flat generic multiplicity
formula is two, not one, for the map from a field to its dual numbers. -/
theorem closedFiber_length_two :
    Module.length (Localization.AtPrime (genericPrime k))
      (Localization.AtPrime (genericPrime k) ⧸ ((genericPrime k).under k).map
        (algebraMap k (Localization.AtPrime (genericPrime k)))) = 2 := by
  rw [genericPrime_under, Ideal.map_bot,
    (Submodule.quotEquivOfEqBot (R := Localization.AtPrime (genericPrime k)) ⊥ rfl).length_eq]
  exact generic_local_length k

/-- Applying the actual L7 formula retains the doubled generic multiplicity
of the nonreduced fiber; its factor has been calculated rather than assumed. -/
theorem actual_flat_generic_factor_two :
    Module.length (Localization.AtPrime (genericPrime k))
      (Localization.AtPrime (genericPrime k) ⊗[dualNumbers k]
        (dualNumbers k ⊗[k] (k × k))) =
      Module.length (Localization.AtPrime ((genericPrime k).under k))
        (Localization.AtPrime ((genericPrime k).under k) ⊗[k] (k × k)) * 2 := by
  have he := flatGeneric_multiplicity (A := k) (B := dualNumbers k)
    (k × k) ⊥ bot_le (genericPrime k)
    (by simpa only [Ideal.map_bot] using genericPrime_minimal k)
  rw [closedFiber_length_two] at he
  exact he

end MotivicTest.FlatGenericDualNumbers
