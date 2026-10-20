/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.BaseChange.TwoLocalizationRetained
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.Basic
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.Compactification
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Constant.EtaleCurve
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.QuasiAffine

/-!
# The same retained normalization curve and its smooth coefficient base

The original quasi-compact separated etale affine-line map supplies an open
retained source and quasi-affineness. Its first affine coefficient restriction
and the two subsequent literal localizations are affine restrictions. Relative
smoothness comes from the original affine-line projection. Absolute smoothness
retains the supplied smooth field structure map, with the exact composite
`baseMap ≫ O.isoSpec.inv ≫ O.ι ≫ t`; normality alone is not used for it.

Intended upstream module:
Module prefix: `Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.`
Module suffix: `TwoLocalizationRetainedGeometry`.
Current consumer: the same-witness standard-triple geometry assembly. No new
normalization, open, boundary, section or frame is chosen. Separatedness remains
in the open-inclusion and quasi-affineness conclusions, and is omitted only from
the relative and absolute smoothness theorems whose proofs do not require it.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification

open Scheme.Hom RelativeProjectiveLine

section Base

variable (R : Type u) [CommRing R]
  (O : (Spec (.of R)).Opens) [IsAffine O.toScheme]
  (a : Γ(O.toScheme, ⊤)) (b : Localization.Away a)
  {k : Type u} [Field k] (t : Spec (.of R) ⟶ Spec (.of k))

/-- The actual final base retains the original field structure map. -/
abbrev twoLocalizationFieldMap : Spec (.of (Localization.Away b)) ⟶ Spec (.of k) :=
  TwoLocalizations.baseMap Γ(O.toScheme, ⊤) a b ≫ O.toScheme.isoSpec.inv ≫ O.ι ≫ t

/-- Smoothness of the final base uses the original `Smooth t`, not normality. -/
theorem twoLocalization_base_smooth [Smooth t] : Smooth (twoLocalizationFieldMap R O a b t) := by
  dsimp only [twoLocalizationFieldMap]
  infer_instance

end Base

variable (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [IsNoetherianRing R] {Y : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial R))) [Etale p] [QuasiCompact p] [IsSeparated p]
  (O : (Spec (.of R)).Opens) [IsAffine O.toScheme]
  (a : Γ(O.toScheme, ⊤)) (b : Localization.Away a)

local notation "F" => boundaryBaseProjectiveMap R (ULift (Fin 2)) (toProjectiveLine R p) O
local notation "J" => boundaryBaseCoverInclusion (boundaryLineProjection R) p (projection R p)
  (inclusion R p) (inclusion_projection R p) ⊤ O

/-- The same original retained source remains openly included after both localizations. -/
theorem twoLocalization_retained_open :
    IsOpenImmersion (TwoLocalizations.retainedInclusion Γ(O.toScheme, ⊤) a b F J) := by
  let : IsOpenImmersion J := boundaryBaseCoverInclusion_open ..
  infer_instance

omit [IsSeparated p] in
/-- Relative smoothness is supplied by the original étale affine-line curve. -/
theorem twoLocalization_retained_smooth :
    SmoothOfRelativeDimension 1
      (TwoLocalizations.retainedProjection Γ(O.toScheme, ⊤) a b F J) := by
  let : SmoothOfRelativeDimension 1 (boundaryLineProjection R) :=
    AffineLineEtaleCompactification.polynomialProjection_smooth_one R
  let : SmoothOfRelativeDimension 1
      (J ≫ (F ≫ ProjectiveSpace.toSpec Γ(O.toScheme, ⊤) (ULift.{u} (Fin 2)))) := by
    rw [boundaryBaseProjectiveMap_toSpec, ← Category.assoc]
    let := boundaryBaseCoverInclusion_smooth (boundaryLineProjection R) p
      (projection R p) (inclusion R p) (inclusion_projection R p) ⊤ O
    exact smoothOfRelativeDimension_comp (n := 1) (m := 0) _ _
  infer_instance

/-- The original étale source supplies quasi-affineness; both coefficient
restrictions use affine morphisms, not an arbitrary-open quasi-compactness claim. -/
theorem twoLocalization_retained_quasiAffine :
    (TwoLocalizations.retainedSource Γ(O.toScheme, ⊤) a b F J).IsQuasiAffine := by
  let : Y.IsQuasiAffine := isQuasiAffine_of_etale_affine_target p
  have hι : IsAffineHom (((p ≫ boundaryLineProjection R) ⁻¹ᵁ O).ι) :=
    MorphismProperty.of_isPullback
      (isPullback_morphismRestrict (p ≫ boundaryLineProjection R) O) inferInstance
  let : IsAffineHom ((boundaryBaseCoverOpen (boundaryLineProjection R) p ⊤ O).ι) := by
    change IsAffineHom ((p ⁻¹ᵁ (⊤ ⊓ (boundaryLineProjection R) ⁻¹ᵁ O)).ι)
    rw [top_inf_eq]
    simpa only [Scheme.Hom.comp_preimage] using hι
  let : (boundaryBaseCoverOpen (boundaryLineProjection R) p ⊤ O).toScheme.IsQuasiAffine :=
    IsQuasiAffine.of_isAffineHom (boundaryBaseCoverOpen (boundaryLineProjection R) p ⊤ O).ι
  exact TwoLocalizations.retainedSource_quasiAffine Γ(O.toScheme, ⊤) a b F J

omit [IsSeparated p] in
/-- Absolute smoothness uses the same original smooth field structure map. -/
theorem twoLocalization_retained_field_smooth
    {k : Type u} [Field k] (t : Spec (.of R) ⟶ Spec (.of k)) [Smooth t] :
    Smooth (TwoLocalizations.retainedProjection Γ(O.toScheme, ⊤) a b F J ≫
      twoLocalizationFieldMap R O a b t) := by
  let : SmoothOfRelativeDimension 1
      (TwoLocalizations.retainedProjection Γ(O.toScheme, ⊤) a b F J) :=
    twoLocalization_retained_smooth R p O a b
  let : Smooth (TwoLocalizations.retainedProjection Γ(O.toScheme, ⊤) a b F J) :=
    SmoothOfRelativeDimension.smooth 1 _
  let : Smooth (twoLocalizationFieldMap R O a b t) := twoLocalization_base_smooth R O a b t
  infer_instance

end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
