/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.RingTheory.LocalLength.ArtinianQuotient
public import Motivic.RingTheory.LocalLength.PrincipalEulerAssociativity
public import Mathlib.RingTheory.KrullDimension.Regular

/-!
# The local dimension bound for finite lists of equations

For a finite module over a Noetherian local ring, quotienting by a list of
maximal-ideal elements lowers support dimension by at most the list length.
If the equation quotient on coefficient support is Artinian, the original
support dimension is consequently at most that length. No regularity is
assumed. The local and maximal-ideal hypotheses are essential.

These are dimension prerequisites for Koszul Euler vanishing. This module
makes no claim that dimension vanishing or cycle devissage is already proved.
-/

@[expose] public section

universe u v

namespace Motivic.LocalLength

variable {R : Type u} [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- The equation ideal and every original coefficient annihilator kill the
literal quotient by the equation-generated submodule. -/
theorem koszulDimension_quotient_annihilator (s : List R) :
    Ideal.ofList s ⊔ Module.annihilator R M ≤
      Module.annihilator R (M ⧸ (Ideal.ofList s • ⊤ : Submodule R M)) := by
  apply sup_le
  · rw [Submodule.annihilator_quotient]
    exact fun _ ha => Submodule.mem_colon.mpr fun _ hm => Submodule.smul_mem_smul ha hm
  · exact (Ideal.ofList s • (⊤ : Submodule R M)).mkQ.annihilator_le_of_surjective
      (Submodule.mkQ_surjective _)

variable [IsNoetherianRing R] [Module.Finite R M]

/-- Artinianness of the equations together with the coefficient annihilator
proves finite length of the actual equation quotient. -/
theorem koszulDimension_quotient_length_ne_top (s : List R)
    [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔ Module.annihilator R M))] :
    Module.length R (M ⧸ (Ideal.ofList s • ⊤ : Submodule R M)) ≠ ⊤ :=
  length_ne_top_of_artinian_quotient _ _ (koszulDimension_quotient_annihilator M s)

variable [IsLocalRing R]

/-- An arbitrary list of maximal-ideal equations lowers support dimension by
at most its length, without requiring the equations to be regular. -/
theorem koszulDimension_le_quotient_add_length (s : List R)
    (hs : ∀ a ∈ s, a ∈ IsLocalRing.maximalIdeal R) :
    Module.supportDim R M ≤
      Module.supportDim R (M ⧸ (Ideal.ofList s • ⊤ : Submodule R M)) + s.length := by
  induction s generalizing M with
  | nil =>
    rw [Ideal.ofList_nil, Submodule.bot_smul]
    simpa using (Module.supportDim_eq_of_equiv
      (Submodule.quotEquivOfEqBot (R := R) (M := M) ⊥ rfl)).ge
  | cons a s ih =>
    have ha := Module.supportDim_le_supportDim_quotSMulTop_succ (M := M)
      (hs a List.mem_cons_self)
    have hb := ih (QuotSMulTop a M) (fun b hb => hs b (List.mem_cons_of_mem a hb))
    have he := Module.supportDim_eq_of_equiv
      (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M a s)
    calc
      Module.supportDim R M ≤ Module.supportDim R (QuotSMulTop a M) + 1 := ha
      _ ≤ (Module.supportDim R (QuotSMulTop a M ⧸
          (Ideal.ofList s • ⊤ : Submodule R (QuotSMulTop a M))) + s.length) + 1 :=
        add_le_add hb le_rfl
      _ = Module.supportDim R (M ⧸ (Ideal.ofList (a :: s) • ⊤ : Submodule R M)) +
          (a :: s).length := by rw [← he]; simp [add_assoc]

/-- In a Noetherian local ring, an Artinian equation quotient on coefficient
support bounds the support dimension by the number of maximal-ideal equations. -/
theorem koszulDimension_le_length_of_artinian_support_quotient (s : List R)
    (hs : ∀ a ∈ s, a ∈ IsLocalRing.maximalIdeal R)
    [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔ Module.annihilator R M))] :
    Module.supportDim R M ≤ s.length := by
  have hd := supportDim_nonpos_of_length_ne_top (koszulDimension_quotient_length_ne_top M s)
  exact (koszulDimension_le_quotient_add_length M s hs).trans
    (by simpa using add_le_add hd (le_refl (s.length : WithBot ℕ∞)))

/-- The actual ring quotient version of the local finite-list dimension bound. -/
theorem koszulDimension_quotient_le_length (J : Ideal R) (s : List R)
    (hs : ∀ a ∈ s, a ∈ IsLocalRing.maximalIdeal R)
    [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔ J))] :
    Module.supportDim R (R ⧸ J) ≤ s.length := by
  have : IsArtinianRing (R ⧸ (Ideal.ofList s ⊔ Module.annihilator R (R ⧸ J))) := by
    rw [Ideal.annihilator_quotient]
    infer_instance
  exact koszulDimension_le_length_of_artinian_support_quotient (R ⧸ J) s hs

end Motivic.LocalLength
