/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulDimensionReduction
public import Motivic.RingTheory.LocalLength.KoszulDimensionBound

/-!
# Artinian support through actual coefficient subquotients

Artinianness passes from an equation-support quotient to a further quotient.
In particular, after the first scalar is absorbed into the literal scalar
coefficient quotient, the tail equation-support quotient is Artinian. These
facts make regular-head dimension induction usable with exact hypotheses.
-/

@[expose] public section

universe u

open CategoryTheory Motivic.LengthEuler

namespace Motivic.Koszul

variable {R : Type u} [CommRing R]

/-- An Artinian ideal quotient remains Artinian after enlarging its ideal. -/
theorem koszulDimension_artinian_quotient_of_le [IsNoetherianRing R] (I J : Ideal R)
    [IsArtinianRing (R ⧸ I)] (hIJ : I ≤ J) : IsArtinianRing (R ⧸ J) := by
  have hlen : Module.length R (R ⧸ J) ≠ ⊤ :=
    Module.length_ne_top_of_artinian_quotient (R ⧸ J) I
      (by rwa [Ideal.annihilator_quotient])
  have hArt : IsArtinian R (R ⧸ J) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (Module.length_ne_top_iff.mp hlen)).2
  exact isArtinian_of_tower R hArt

/-- The head scalar belongs to the annihilator of the literal quotient
coefficient module used by the regular-head comparison. -/
theorem koszulDimension_mem_annihilator_scalarQuotient (M : ModuleCat R) (a : R) :
    a ∈ Module.annihilator R ((scalarQuotientFunctor a).obj M) := by
  apply Module.mem_annihilator.mpr
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩

/-- The original coefficient annihilator also kills its literal scalar quotient. -/
theorem koszulDimension_annihilator_le_scalarQuotient (M : ModuleCat R) (a : R) :
    Module.annihilator R M ≤ Module.annihilator R ((scalarQuotientFunctor a).obj M) :=
  (LinearMap.range (LinearMap.lsmul R M a)).mkQ.annihilator_le_of_surjective
    (Submodule.mkQ_surjective _)

/-- Every original support equation either remains in the tail or is absorbed
into the actual quotient coefficient annihilator. -/
theorem koszulDimension_supportIdeal_le_scalarQuotient (M : ModuleCat R) (a : R) (s : List R) :
    Ideal.ofList (a :: s) ⊔ Module.annihilator R M ≤
      Ideal.ofList s ⊔ Module.annihilator R ((scalarQuotientFunctor a).obj M) := by
  rw [Ideal.ofList_cons]
  apply sup_le
  · apply sup_le
    · exact le_sup_of_le_right ((Ideal.span_singleton_le_iff_mem _).mpr
        (koszulDimension_mem_annihilator_scalarQuotient M a))
    · exact le_sup_left
  · exact le_sup_of_le_right (koszulDimension_annihilator_le_scalarQuotient M a)

/-- Artinian equation support survives regular-head reduction to the tail.
This support fact does not itself need regularity of the scalar. -/
theorem koszulDimension_artinian_scalarQuotient [IsNoetherianRing R]
    (M : ModuleCat R) (a : R) (s : List R)
    [IsArtinianRing (R ⧸ (Ideal.ofList (a :: s) ⊔ Module.annihilator R M))] :
    IsArtinianRing (R ⧸ (Ideal.ofList s ⊔
      Module.annihilator R ((scalarQuotientFunctor a).obj M))) :=
  koszulDimension_artinian_quotient_of_le _ _
    (koszulDimension_supportIdeal_le_scalarQuotient M a s)

end Motivic.Koszul
