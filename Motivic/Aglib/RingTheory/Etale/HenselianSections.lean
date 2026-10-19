/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Unramified.LocalStructure
public import Mathlib.RingTheory.AdicCompletion.Noetherian

/-!
# Residue-compatible sections of étale algebras over henselian local rings

Every residue-field point of an étale algebra over a henselian local ring lifts
to a point over that ring, with the prescribed reduction. The proof first uses
simple-root lifting for a standard étale pair, then passes to a standard étale
chart containing the kernel of the given residue-field point.
Local Artinian rings satisfy the same lifting statement by maximal-ideal
completeness; no reducedness assumption is needed.

This is the implication from henselianity to étale lifting in
[Stacks Project, Tag 04GE](https://stacks.math.columbia.edu/tag/04GE).
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing

namespace Algebra.Etale.Henselian

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]

section Henselian

variable [HenselianLocalRing R]

/-- A residue-field point of a standard étale pair lifts with its prescribed reduction. -/
theorem exists_lift_of_standardEtalePair (P : StandardEtalePair R)
    (φ : P.Ring →ₐ[R] ResidueField R) :
    ∃ ψ : P.Ring →ₐ[R] R,
      (IsScalarTower.toAlgHom R R (ResidueField R)).comp ψ = φ := by
  have hx : P.HasMap (φ P.X) := P.hasMap_X.map φ
  obtain ⟨a, ha, hres⟩ := ((HenselianLocalRing.TFAE R).out 1 2 rfl rfl).mp
    ‹HenselianLocalRing R› P.f P.monic_f (φ P.X) hx.1
      (StandardEtalePair.HasMap.isUnit_derivative_f P hx).ne_zero
  have ha' : P.HasMap a := by
    refine ⟨?_, ?_⟩
    · simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, IsRoot] using ha
    · apply (residue_ne_zero_iff_isUnit _).mp
      change (IsScalarTower.toAlgHom R R (ResidueField R)) (aeval a P.g) ≠ 0
      rw [← aeval_algHom_apply]
      change aeval (residue R a) P.g ≠ 0
      rw [hres]
      exact hx.2.ne_zero
  refine ⟨P.lift a ha', P.hom_ext ?_⟩
  simpa using hres

/-- A point of a standard étale algebra over the residue field lifts to the local ring. -/
theorem exists_lift_of_isStandardEtale [Algebra.IsStandardEtale R B]
    (φ : B →ₐ[R] ResidueField R) :
    ∃ ψ : B →ₐ[R] R,
      (IsScalarTower.toAlgHom R R (ResidueField R)).comp ψ = φ := by
  let P : StandardEtalePresentation R B :=
    Algebra.IsStandardEtale.nonempty_standardEtalePresentation.some
  obtain ⟨ψ, hψ⟩ := exists_lift_of_standardEtalePair P.P
    (φ.comp P.equivRing.symm.toAlgHom)
  refine ⟨ψ.comp P.equivRing.toAlgHom, ?_⟩
  ext b
  simpa using DFunLike.congr_fun hψ (P.equivRing b)

/-- Every residue-field point of an étale algebra over a henselian local ring lifts
to the ring, with exactly the given residue-field reduction. -/
theorem exists_lift_of_etale [Algebra.Etale R B] (φ : B →ₐ[R] ResidueField R) :
    ∃ ψ : B →ₐ[R] R,
      (IsScalarTower.toAlgHom R R (ResidueField R)).comp ψ = φ := by
  let Q : Ideal B := RingHom.ker φ
  have : Q.IsPrime := RingHom.ker_isPrime φ
  obtain ⟨s, hs, hstandard⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) Q
  have : Algebra.IsStandardEtale R (Localization.Away s) := hstandard
  have hsunit : IsUnit (φ s) := isUnit_iff_ne_zero.mpr hs
  let φ' : Localization.Away s →ₐ[R] ResidueField R :=
    IsLocalization.Away.liftAlgHom s hsunit
  obtain ⟨ψ, hψ⟩ := exists_lift_of_isStandardEtale φ'
  refine ⟨ψ.comp (IsScalarTower.toAlgHom R B (Localization.Away s)), ?_⟩
  ext b
  simpa [φ'] using DFunLike.congr_fun hψ (algebraMap B (Localization.Away s) b)

end Henselian

/-- Residue-field points of étale algebras over local Artinian rings lift with
their prescribed reduction, including when the base ring is nonreduced. -/
theorem exists_lift_of_etale_of_artinian [IsLocalRing R] [IsArtinianRing R]
    [Algebra.Etale R B] (φ : B →ₐ[R] ResidueField R) :
    ∃ ψ : B →ₐ[R] R,
      (IsScalarTower.toAlgHom R R (ResidueField R)).comp ψ = φ := by
  have : HenselianLocalRing R :=
    { is_henselian := fun f hf a ha hd ↦
        HenselianRing.is_henselian f hf a ha (hd.map (residue R)) }
  exact exists_lift_of_etale φ

end Algebra.Etale.Henselian
