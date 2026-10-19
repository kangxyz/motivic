/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.CylinderNativeCoordinates
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Affine.PrincipalCoefficient
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.Diagrams.OriginalAffineRefinement
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.NormalizedBoundaryChoice
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Boundary.Nonempty


/-! # Normalize the exact native original affine representative once -/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RelativeProjectiveLine Scheme Scheme.Hom Scheme.RelativeAffineLineEtaleCompactification
open _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
universe u
namespace Motivic.PresheafWithTransfers
variable {k : Type u} [Field k]
  (U T : SmoothSite (Spec (.of k))) [IsAffine U.left]
  (e : T ≅ SmoothSite.a1Cylinder (.of k) U)
  {Y Z : Scheme.{u}} (p : Y ⟶ T.left) (z : Z ⟶ T.left)
  (r : Γ(U.left, ⊤)) (W : Y.Opens)
/-- The literal coefficient projection of the original presented cylinder. -/
def originalRepresentativeCoefficientMap : T.left ⟶ Spec Γ(U.left, ⊤) :=
  e.hom.left ≫ (SmoothSite.a1Projection (.of k) U).left ≫ U.left.isoSpec.hom

variable (hW : W ≤ p ⁻¹ᵁ
    (originalRepresentativeCoefficientMap U T e ⁻¹ᵁ PrimeSpectrum.basicOpen r))
  (t : ((z ≫ originalRepresentativeCoefficientMap U T e) ⁻¹ᵁ
    PrimeSpectrum.basicOpen r).toScheme ⟶ W.toScheme)

/-- Exact produced native evidence and normalized-boundary output. These are
conclusions, never premises of the original representative constructor. -/
def OriginalRefinedNormalization : Prop :=
  let O : (Spec Γ(U.left, ⊤)).Opens := PrimeSpectrum.basicOpen r
  let : IsAffine O.toScheme := IsAffineOpen.Spec_basicOpen (R := Γ(U.left, ⊤)) r
  let eN := originalCylinderNativeIso U T e
  let pN := originalAffineRefinedNativeMap Γ(U.left, ⊤) eN
    (originalRepresentativeCoefficientMap U T e)
    (originalCylinderNativeIso_projection U T e) O p W hW
  let zN := originalAffineRefinedNativeMarked Γ(U.left, ⊤) eN
    (originalRepresentativeCoefficientMap U T e)
    (originalCylinderNativeIso_projection U T e) O z
  ∃ hd : IsDomain Γ(O.toScheme, ⊤), ∃ hn : IsIntegrallyClosed Γ(O.toScheme, ⊤),
    ∃ hno : IsNoetherianRing Γ(O.toScheme, ⊤),
    letI := hd
    letI := hn
    letI := hno
    ∃ hp : Etale pN, ∃ hqc : QuasiCompact pN, ∃ hsep : IsSeparated pN,
      ∃ hzc : IsClosedImmersion zN,
      ∃ hzf : IsFinite (zN ≫ boundaryLineProjection Γ(O.toScheme, ⊤)),
      letI := hp
      letI := hqc
      letI := hsep
      letI := hzc
      letI := hzf
      ∃ hs : t ≫ pN = zN,
        CommonRestrictedThickenedBoundary Γ(O.toScheme, ⊤) pN zN t hs ∧
        Nonempty (neighborhoodBoundary Γ(O.toScheme, ⊤) ⊤)

/-- All native normalization hypotheses follow from the actual original affine
refinement. Both generic restriction and thickening are chosen exactly once. -/
theorem originalRefinedNormalization_of_square [IsIntegral U.left]
    (hr : r ≠ 0) (hWa : IsAffineOpen W) [Etale p] [IsClosedImmersion z]
    [IsFinite (z ≫ (originalRepresentativeCoefficientMap U T e))]
    (H : IsPullback t (𝟙 _)
      (p.resLE (originalRepresentativeCoefficientMap U T e ⁻¹ᵁ
        PrimeSpectrum.basicOpen r) W hW)
      (z ∣_ ((originalRepresentativeCoefficientMap U T e) ⁻¹ᵁ PrimeSpectrum.basicOpen r))) :
    OriginalRefinedNormalization U T e p z r W hW t := by
  obtain ⟨hd, hn, hno⟩ := principalCoefficientRing_properties U r hr
  let O : (Spec Γ(U.left, ⊤)).Opens := PrimeSpectrum.basicOpen r
  let : IsAffine O.toScheme := IsAffineOpen.Spec_basicOpen (R := Γ(U.left, ⊤)) r
  let : IsDomain Γ(O.toScheme, ⊤) := hd
  let : IsIntegrallyClosed Γ(O.toScheme, ⊤) := hn
  let : IsNoetherianRing Γ(O.toScheme, ⊤) := hno
  let : IsAffine W.toScheme := hWa
  let eN := originalCylinderNativeIso U T e
  let pN := originalAffineRefinedNativeMap Γ(U.left, ⊤) eN
    (originalRepresentativeCoefficientMap U T e)
    (originalCylinderNativeIso_projection U T e) O p W hW
  let zN := originalAffineRefinedNativeMarked Γ(U.left, ⊤) eN
    (originalRepresentativeCoefficientMap U T e)
    (originalCylinderNativeIso_projection U T e) O z
  have HN : IsPullback t (𝟙 _) pN zN :=
    originalAffineRefinedNativeMarked_isPullback Γ(U.left, ⊤) eN
      (originalRepresentativeCoefficientMap U T e)
      (originalCylinderNativeIso_projection U T e) O p W hW z t H
  have hs : t ≫ pN = zN := by simpa only [Category.id_comp] using HN.w
  refine ⟨hd, hn, hno, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hs, ?_, neighborhoodBoundary_nonempty _ _⟩
  exact exists_common_restricted_thickened_boundary _ pN zN t hs HN

end Motivic.PresheafWithTransfers
