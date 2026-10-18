/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.RingTheory.LocalLength.KoszulPairFiniteLength

/-!
# Support-sensitive finiteness of two-element Koszul homology

The annihilator of the coefficient module annihilates each actual Koszul
homology module. Together with the two equations, it therefore provides a
smaller support on which finite length can be checked: the quotient by
`Ideal.span {a, b} ⊔ Module.annihilator R M` need only be Artinian.
No regularity of either equation is required.
-/

@[expose] public section

universe u v

namespace Module.KoszulPair

variable {R : Type u} [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M] (a b : R)

/-- The coefficient annihilator kills the actual degree-zero quotient. -/
theorem annihilator_le_annihilator_H₀ :
    Module.annihilator R M ≤ Module.annihilator R (H₀ M a b) :=
  (LinearMap.range (d₁ M a b)).mkQ.annihilator_le_of_surjective
    (Submodule.mkQ_surjective _)

/-- The coefficient annihilator kills the actual degree-one cycles modulo boundaries. -/
theorem annihilator_le_annihilator_H₁ :
    Module.annihilator R M ≤ Module.annihilator R (H₁ M a b) := by
  have hprod : Module.annihilator R M ≤ Module.annihilator R (M × M) := by
    rw [Module.annihilator_prod, inf_idem]
  exact hprod.trans (((Cycles M a b).subtype.annihilator_le_of_injective
    (Submodule.subtype_injective _)).trans
    ((LinearMap.range (toCycles M a b)).mkQ.annihilator_le_of_surjective
      (Submodule.mkQ_surjective _)))

/-- The coefficient annihilator kills the actual degree-two cycles. -/
theorem annihilator_le_annihilator_H₂ :
    Module.annihilator R M ≤ Module.annihilator R (H₂ M a b) :=
  (LinearMap.ker (d₂ M a b)).subtype.annihilator_le_of_injective
    (Submodule.subtype_injective _)

/-- The equations together with the coefficient annihilator kill degree-zero homology. -/
theorem span_sup_annihilator_le_annihilator_H₀ :
    Ideal.span ({a, b} : Set R) ⊔ Module.annihilator R M ≤
      Module.annihilator R (H₀ M a b) :=
  sup_le (span_le_annihilator_H₀ M a b) (annihilator_le_annihilator_H₀ M a b)

/-- The equations together with the coefficient annihilator kill degree-one homology. -/
theorem span_sup_annihilator_le_annihilator_H₁ :
    Ideal.span ({a, b} : Set R) ⊔ Module.annihilator R M ≤
      Module.annihilator R (H₁ M a b) :=
  sup_le (span_le_annihilator_H₁ M a b) (annihilator_le_annihilator_H₁ M a b)

/-- The equations together with the coefficient annihilator kill degree-two homology. -/
theorem span_sup_annihilator_le_annihilator_H₂ :
    Ideal.span ({a, b} : Set R) ⊔ Module.annihilator R M ≤
      Module.annihilator R (H₂ M a b) :=
  sup_le (span_le_annihilator_H₂ M a b) (annihilator_le_annihilator_H₂ M a b)

/-- An Artinian quotient by the equations and any coefficient-annihilating ideal
supplies finite length in all three actual Koszul degrees. -/
theorem hasFiniteHomology_of_artinian_quotient_of_le_annihilator
    [IsNoetherianRing R] [Module.Finite R M] (I : Ideal R)
    [IsArtinianRing (R ⧸ (Ideal.span ({a, b} : Set R) ⊔ I))]
    (hI : I ≤ Module.annihilator R M) : HasFiniteHomology M a b := by
  refine ⟨length_ne_top_of_artinian_quotient (H₀ M a b)
      (Ideal.span {a, b} ⊔ I) ?_,
    length_ne_top_of_artinian_quotient (H₁ M a b) (Ideal.span {a, b} ⊔ I) ?_,
    length_ne_top_of_artinian_quotient (H₂ M a b) (Ideal.span {a, b} ⊔ I) ?_⟩
  · exact sup_le (span_le_annihilator_H₀ M a b)
      (hI.trans (annihilator_le_annihilator_H₀ M a b))
  · exact sup_le (span_le_annihilator_H₁ M a b)
      (hI.trans (annihilator_le_annihilator_H₁ M a b))
  · exact sup_le (span_le_annihilator_H₂ M a b)
      (hI.trans (annihilator_le_annihilator_H₂ M a b))

/-- Artinianness on the coefficient support supplies finite Koszul homology.
The ambient two-equation quotient itself need not be Artinian. -/
theorem hasFiniteHomology_of_artinian_support_quotient
    [IsNoetherianRing R] [Module.Finite R M]
    [IsArtinianRing (R ⧸ (Ideal.span ({a, b} : Set R) ⊔ Module.annihilator R M))] :
    HasFiniteHomology M a b :=
  hasFiniteHomology_of_artinian_quotient_of_le_annihilator M a b
    (Module.annihilator R M) le_rfl

/-- The support-sensitive Artinian criterion gives finite length in degree zero. -/
theorem length_H₀_ne_top_of_artinian_support_quotient
    [IsNoetherianRing R] [Module.Finite R M]
    [IsArtinianRing (R ⧸ (Ideal.span ({a, b} : Set R) ⊔ Module.annihilator R M))] :
    Module.length R (H₀ M a b) ≠ ⊤ :=
  (hasFiniteHomology_of_artinian_support_quotient M a b).1

/-- The support-sensitive Artinian criterion gives finite length in degree one. -/
theorem length_H₁_ne_top_of_artinian_support_quotient
    [IsNoetherianRing R] [Module.Finite R M]
    [IsArtinianRing (R ⧸ (Ideal.span ({a, b} : Set R) ⊔ Module.annihilator R M))] :
    Module.length R (H₁ M a b) ≠ ⊤ :=
  (hasFiniteHomology_of_artinian_support_quotient M a b).2.1

/-- The support-sensitive Artinian criterion gives finite length in degree two. -/
theorem length_H₂_ne_top_of_artinian_support_quotient
    [IsNoetherianRing R] [Module.Finite R M]
    [IsArtinianRing (R ⧸ (Ideal.span ({a, b} : Set R) ⊔ Module.annihilator R M))] :
    Module.length R (H₂ M a b) ≠ ⊤ :=
  (hasFiniteHomology_of_artinian_support_quotient M a b).2.2

end Module.KoszulPair
