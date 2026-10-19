/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.Actions.Norm.RefinedNormalization
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Affine.PrincipalCoefficient
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.Diagrams.OriginalAffineRefinement
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.OriginalSectionChoice
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Boundary.Nonempty
/-! # Bind the original native refinement to one normalized section choice -/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RelativeProjectiveLine Scheme Scheme.Hom Scheme.RelativeAffineLineEtaleCompactification
open AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
universe u
namespace Motivic.PresheafWithTransfers
variable {k : Type u} [Field k]
  (U T : SmoothSite (Spec (.of k))) [IsAffine U.left]
  (e : T ≅ SmoothSite.a1Cylinder (.of k) U)
  {Y Z A : Scheme.{u}} [IsAffine A]
  (a : A ⟶ T.left) [IsOpenImmersion a] (p : Y ⟶ T.left) (z : Z ⟶ T.left)
  (r : Γ(U.left, ⊤)) (W : Y.Opens)
variable (hW : W ≤ p ⁻¹ᵁ
    (originalRepresentativeCoefficientMap U T e ⁻¹ᵁ PrimeSpectrum.basicOpen r))
  (t : ((z ≫ originalRepresentativeCoefficientMap U T e) ⁻¹ᵁ
    PrimeSpectrum.basicOpen r).toScheme ⟶ W.toScheme)

/-- Exact produced native evidence and normalized-boundary output. These are
conclusions, never premises of the original representative constructor. -/
def OriginalRefinedSectionChoice (hWa : IsAffineOpen W) : Prop :=
  let : IsAffine W.toScheme := hWa
  let O : (Spec Γ(U.left, ⊤)).Opens := PrimeSpectrum.basicOpen r
  let : IsAffine O.toScheme := IsAffineOpen.Spec_basicOpen (R := Γ(U.left, ⊤)) r
  let eN := originalCylinderNativeIso U T e
  let pN := originalAffineRefinedNativeMap Γ(U.left, ⊤) eN
    (originalRepresentativeCoefficientMap U T e)
    (originalCylinderNativeIso_projection U T e) O p W hW
  let zN := originalAffineRefinedNativeMarked Γ(U.left, ⊤) eN
    (originalRepresentativeCoefficientMap U T e)
    (originalCylinderNativeIso_projection U T e) O z
  let aN := originalAffineRefinedNativePuncture Γ(U.left, ⊤) eN
    (originalRepresentativeCoefficientMap U T e)
    (originalCylinderNativeIso_projection U T e) O a
  let : IsAffine ((a ≫ originalRepresentativeCoefficientMap U T e) ⁻¹ᵁ O).toScheme :=
    originalAffineRefinedNativePuncture_affine Γ(U.left, ⊤) eN
      (originalRepresentativeCoefficientMap U T e)
      (originalCylinderNativeIso_projection U T e) O a
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
        ∃ HN : IsPullback t (𝟙 _) pN zN,
        NormalizedOriginalSectionChoice Γ(O.toScheme, ⊤) pN zN t hs aN HN

/-- All native normalization hypotheses follow from the actual original affine
refinement. Both generic restriction and thickening are chosen exactly once. -/
theorem originalRefinedSectionChoice_of_square [IsIntegral U.left]
    (hr : r ≠ 0) (hWa : IsAffineOpen W)
    (hz : Set.range z = (Set.range a)ᶜ) [Etale p] [IsClosedImmersion z]
    [IsFinite (z ≫ (originalRepresentativeCoefficientMap U T e))]
    (H : IsPullback t (𝟙 _)
      (p.resLE (originalRepresentativeCoefficientMap U T e ⁻¹ᵁ
        PrimeSpectrum.basicOpen r) W hW)
      (z ∣_ ((originalRepresentativeCoefficientMap U T e) ⁻¹ᵁ PrimeSpectrum.basicOpen r))) :
    OriginalRefinedSectionChoice U T e a p z r W hW t hWa := by
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
  let aN := originalAffineRefinedNativePuncture Γ(U.left, ⊤) eN
    (originalRepresentativeCoefficientMap U T e)
    (originalCylinderNativeIso_projection U T e) O a
  let : IsAffine ((a ≫ originalRepresentativeCoefficientMap U T e) ⁻¹ᵁ O).toScheme :=
    originalAffineRefinedNativePuncture_affine Γ(U.left, ⊤) eN
      (originalRepresentativeCoefficientMap U T e)
      (originalCylinderNativeIso_projection U T e) O a
  refine ⟨hd, hn, hno, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hs, HN, ?_⟩
  exact exists_normalizedOriginalSectionChoice _ pN zN t hs aN HN
    (originalAffineRefinedNative_complement Γ(U.left, ⊤) eN
      (originalRepresentativeCoefficientMap U T e)
      (originalCylinderNativeIso_projection U T e) O a z hz)

end Motivic.PresheafWithTransfers
