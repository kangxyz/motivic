/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Ideal.GoingDown

/-!
# Going down after quotienting the base

The going-down property descends to the actual quotient algebra `S / IS` over
`R / I`. No integrality, normality, domain, or Noetherian hypothesis is needed.
The algebra structure is the canonical quotient map induced by `R → S`.

## Upstream candidate

Intended upstream module: `Aglib.RingTheory.Ideal.GoingDown.Quotient`.
The source and target commutative rings may lie in independent universes;
the ideal is arbitrary, including the unit ideal. The current consumer is
`Motivic.Aglib.RingTheory.Ideal.GoingDown.TensorProduct`, which applies this result to the
actual quotient of the left tensor factor.

Extracted from `Motivic.RingTheory.GoingDown.Quotient`, source SHA-256
`e9480ed85615b50562f045a1b3b304b53230d2a73a347ec3501d89d044843c3b`.
The mathematical declaration now extends `Algebra.HasGoingDown`.
-/

@[expose] public section

universe u v

namespace Algebra.HasGoingDown

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Going down is preserved when the base is quotiented by an arbitrary ideal
and the target is quotiented by its extension. The quotient algebra is
`Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map`. -/
theorem quotient_map [Algebra.HasGoingDown R S] (I : Ideal R) :
    Algebra.HasGoingDown (R ⧸ I) (S ⧸ I.map (algebraMap R S)) := by
  let J := I.map (algebraMap R S)
  constructor
  intro p hp Q hQ hlt
  let p' := p.comap (Ideal.Quotient.mk I)
  let Q' := Q.comap (Ideal.Quotient.mk J)
  have : p'.IsPrime := Ideal.comap_isPrime _ _
  have : Q'.IsPrime := Ideal.comap_isPrime _ _
  have hle : p' ≤ Q'.under R := by
    change p.comap (Ideal.Quotient.mk I) ≤
      (Q.comap (Ideal.Quotient.mk J)).comap (algebraMap R S)
    rw [Ideal.comap_comap, ← Ideal.quotientMap_comp_mk Ideal.le_comap_map,
      ← Ideal.comap_comap]
    exact Ideal.comap_mono hlt.le
  obtain ⟨P, hPQ, hP, hPp⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := p') (q := Q'.under R) Q' hle
  have hJP : J ≤ P := by
    apply Ideal.map_le_iff_le_comap.mpr
    change I ≤ P.under R
    rw [← hPp.over]
    intro x hx
    change Ideal.Quotient.mk I x ∈ p
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact p.zero_mem
  refine ⟨P.map (Ideal.Quotient.mk J), ?_, ?_, ⟨?_⟩⟩
  · exact (Ideal.map_mono hPQ).trans_eq
      (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective Q)
  · apply Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    simpa only [Ideal.mk_ker] using hJP
  · apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
    change p' =
      ((P.map (Ideal.Quotient.mk J)).comap
        (Ideal.quotientMap J (algebraMap R S) Ideal.le_comap_map)).comap
          (Ideal.Quotient.mk I)
    rw [Ideal.comap_comap, Ideal.quotientMap_comp_mk, ← Ideal.comap_comap,
      Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
    simpa only [← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_of_le_left hJP] using hPp.over

end Algebra.HasGoingDown
