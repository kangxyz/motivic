/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Properties.Normal.Affine
public import Mathlib.AlgebraicGeometry.Noetherian
/-! # Normal-domain coefficients on the same nonempty section-choice opens

Intended upstream module:
`Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.CoefficientNormalDomain`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumer:
`Normalization.Compactification.RelativeAffineLine.OriginalLocalizationHistory`.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification

/-- A retained point, rather than a new coefficient shrink, supplies the nonempty
normal-domain coefficient ring on an actual affine open. -/
theorem originalCoefficientRing_properties
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
    (O : (Spec (.of R)).Opens) [IsAffine O.toScheme]
    (x : Spec (.of R)) (hx : x ∈ O) :
    IsDomain Γ(O.toScheme, ⊤) ∧ IsIntegrallyClosed Γ(O.toScheme, ⊤) ∧
      IsNoetherianRing Γ(O.toScheme, ⊤) := by
  let : Nonempty O.toScheme := ⟨⟨x, hx⟩⟩
  let : IsIntegral O.toScheme := isIntegral_of_isOpenImmersion O.ι
  let (y : O.toScheme) : IsIntegrallyClosed (O.toScheme.presheaf.stalk y) := by
    let := (Scheme.isIntegrallyClosed_and_isDomain_stalk_Spec R (O.ι y)).1
    exact IsIntegrallyClosed.of_equiv (asIso (O.ι.stalkMap y)).commRingCatIsoToRingEquiv
  let : Nonempty (⊤ : O.toScheme.Opens) := ⟨⟨⟨x, hx⟩, trivial⟩⟩
  exact ⟨inferInstance,
    O.toScheme.isIntegrallyClosed_sections_of_isAffineOpen ⊤ (isAffineOpen_top _),
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩⟩

/-- Both original coefficient restrictions preserve the actual normal domain.
The points are those already retained by normalization and the common chooser. -/
theorem finalCoefficientRing_properties
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
    (O : (Spec (.of R)).Opens) [IsAffine O.toScheme]
    (x : Spec (.of R)) (hx : x ∈ O)
    (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme]
    (y : Spec Γ(O.toScheme, ⊤)) (hy : y ∈ V) :
    IsDomain Γ(V.toScheme, ⊤) ∧ IsIntegrallyClosed Γ(V.toScheme, ⊤) ∧
      IsNoetherianRing Γ(V.toScheme, ⊤) := by
  obtain ⟨hd, hn, hno⟩ := originalCoefficientRing_properties R O x hx
  let := hd
  let := hn
  let := hno
  exact originalCoefficientRing_properties Γ(O.toScheme, ⊤) V y hy

end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
