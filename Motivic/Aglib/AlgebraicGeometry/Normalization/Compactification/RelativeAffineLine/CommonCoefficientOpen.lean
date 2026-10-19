/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.Boundary.RelativeInfinityFiniteBaseOpen
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.FiniteFlat
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.WholeTarget

/-! # A common generic coefficient open before any boundary frames or sections

Intended upstream module:
`Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.CommonCoefficientOpen`.
Incoming project consumers:
Module prefix: `Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.`
Module suffix: `RelativeAffineLine.NormalizedBoundaryChoice`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification

private theorem finite_restrict_of_le {X S : Scheme.{u}} (f : X ⟶ S)
    {U O : S.Opens} (h : O ≤ U) [IsFinite (f ∣_ U)] : IsFinite (f ∣_ O) := by
  have hf : IsFinite ((f ∣_ U) ∣_ (U.ι ⁻¹ᵁ O)) := inferInstance
  have h' := (MorphismProperty.arrow_mk_iso_iff (P := @IsFinite)
    (morphismRestrictRestrict f U (U.ι ⁻¹ᵁ O))).mp hf
  have he : U.ι ''ᵁ (U.ι ⁻¹ᵁ O) = O := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, inf_eq_right.mpr h]
  rw [he] at h'
  exact h'

/-- The original normalization has a finite missing boundary on a common affine
neighborhood of the generic point inside the original free-chart localization.
Both free-chart witnesses still refer to the original normalization and the single
chosen coefficient `r`. No arbitrary base point is claimed to survive. -/
theorem exists_common_coefficient_open
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (.of (Polynomial R))) [Etale p] [QuasiCompact p] [IsSeparated p] :
    ∃ (r : R), r ≠ 0 ∧
      (∀ i : ULift.{u} (Fin 2),
        let A := Localization.Away r
        let g := RelativeProjectiveLine.chart A i ≫
          ProjectiveSpace.map (algebraMap R A) (ULift.{u} (Fin 2))
        let : Algebra (Polynomial A) Γ(pullback (toProjectiveLine R p) g, ⊤) :=
          (FiniteSchemeNormBaseChange.scalarMap (pullback.snd (toProjectiveLine R p) g)).toAlgebra
        Module.Free (Polynomial A) Γ(pullback (toProjectiveLine R p) g, ⊤)) ∧
      ∃ (O : (Spec (.of R)).Opens) (_hO : IsAffineOpen O),
        genericPoint (Spec (.of R)) ∈ O ∧ O ≤ PrimeSpectrum.basicOpen r ∧
        IsFinite (Hom.boundaryBaseWholeMap (projection R p) (infinityInclusion R p) O ≫
          pullback.fst O.ι (projection R p)) := by
  obtain ⟨r, hr, hfree⟩ := exists_free_chart_sections_baseChange R p
  obtain ⟨U, hηU, hfinite⟩ := exists_base_open_finite_infinity R p
  have hηr : genericPoint (Spec (.of R)) ∈ PrimeSpectrum.basicOpen r := by
    rw [genericPoint_eq_bot_of_affine]
    change r ∉ (⊥ : Ideal R)
    simpa only [Ideal.mem_bot] using hr
  obtain ⟨O, hO, hηO, hOU⟩ := exists_isAffineOpen_mem_and_subset
    (show genericPoint (Spec (.of R)) ∈ U ⊓ PrimeSpectrum.basicOpen r from ⟨hηU, hηr⟩)
  refine ⟨r, hr, hfree, O, hO, hηO, fun x hx => (hOU hx).2, ?_⟩
  rw [Hom.boundaryBaseWholeMap_fst]
  let := hfinite
  exact finite_restrict_of_le _ (fun x hx => (hOU hx).1)

end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
