/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.OriginalLocalizationInput
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.NativeMiddleInput
public import Motivic.Transfers.Presheaf.Sheafification.Representatives.SectionChosen
public import Motivic.Transfers.Presheaf.Actions.Norm.NativeRefinement.NativeOriginalRefinedCover

/-! # Shared data for the original localization history

The original geometry, its localizations and its section witnesses are stored
once. Line comparisons, restrictions and lifting are proved for a variable
`OriginalHistoryContext`; the original representative producer instantiates
that context at its boundary. The original maps and geometric hypotheses are
retained as fields rather than repeatedly expanded argument lists.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Scheme Scheme.Hom Scheme.RelativeAffineLineEtaleCompactification
open RelativeProjectiveLine AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates

universe u

namespace Motivic.PresheafWithTransfers.OriginalHistorySiteLifting

/-- Original representatives and their first affine coefficient and source restrictions. -/
structure OriginalRepresentativeGeometry (k : Type u) [Field k] where
  /-- The original smooth base. -/
  U : SmoothSite (Spec (.of k))
  /-- Affineness of that base. -/
  [affineU : IsAffine U.left]
  /-- The original cylinder representative. -/
  Tc : SmoothSite (Spec (.of k))
  /-- Its given comparison with the whole original cylinder. -/
  eT : Tc ≅ SmoothSite.a1Cylinder (.of k) U
  /-- The original puncture representative. -/
  A : SmoothSite (Spec (.of k))
  /-- Affineness of the puncture representative. -/
  [affineA : IsAffine A.left]
  /-- The original source representative. -/
  Y : SmoothSite (Spec (.of k))
  /-- The given puncture inclusion. -/
  a : A ⟶ Tc
  /-- The puncture inclusion is open. -/
  [openA : IsOpenImmersion a.left]
  /-- The given source map. -/
  p : Y ⟶ Tc
  /-- The whole marked complement. -/
  Z : Scheme.{u}
  /-- Its original marking in the cylinder representative. -/
  z : Z ⟶ Tc.left
  /-- The first coefficient open. -/
  B₀ : (Spec Γ(U.left, ⊤)).Opens
  /-- Affineness of that coefficient open. -/
  [affineB : IsAffine B₀.toScheme]
  /-- The original affine source open. -/
  W : Y.left.Opens
  /-- Affineness of that source open. -/
  [affineW : IsAffine W.toScheme]
  /-- The original containment witness. -/
  hW : W ≤ p.left ⁻¹ᵁ ((originalRepresentativeCoefficientMap U Tc eT) ⁻¹ᵁ B₀)
  /-- The original marked lift into that same source open. -/
  s₀ : ((z ≫ originalRepresentativeCoefficientMap U Tc eT) ⁻¹ᵁ B₀).toScheme ⟶ W.toScheme
  /-- The marking is the full puncture complement. -/
  hcomp : Set.range z = (Set.range a.left)ᶜ
  /-- The first chosen localization of the coefficient ring. -/
  O : (Spec Γ(B₀.toScheme, ⊤)).Opens
  /-- Affineness of the chosen localization. -/
  [affineO : IsAffine O.toScheme]

attribute [local instance] OriginalRepresentativeGeometry.affineU
  OriginalRepresentativeGeometry.affineA OriginalRepresentativeGeometry.openA
  OriginalRepresentativeGeometry.affineB OriginalRepresentativeGeometry.affineW
  OriginalRepresentativeGeometry.affineO

namespace OriginalRepresentativeGeometry
variable {k : Type u} [Field k] (D : OriginalRepresentativeGeometry k)

/-- The original coefficient map, with no replacement representative. -/
abbrev coefficientMap := originalRepresentativeCoefficientMap D.U D.Tc D.eT

/-- The original affine-line coordinate comparison. -/
abbrev coordinateIso := originalCylinderNativeIso D.U D.Tc D.eT

/-- The literal native map on the original chosen source open. -/
abbrev nativeSourceMap := Scheme.originalAffineRefinedNativeMap Γ(D.U.left, ⊤)
  D.coordinateIso D.coefficientMap
  (originalCylinderNativeIso_projection D.U D.Tc D.eT) D.B₀ D.p.left D.W D.hW

/-- The literal native marked map. -/
abbrev nativeMarkedMap := Scheme.originalAffineRefinedNativeMarked Γ(D.U.left, ⊤)
  D.coordinateIso D.coefficientMap
  (originalCylinderNativeIso_projection D.U D.Tc D.eT) D.B₀ D.z

/-- The literal native puncture map. -/
abbrev nativePunctureMap := Scheme.originalAffineRefinedNativePuncture Γ(D.U.left, ⊤)
  D.coordinateIso D.coefficientMap
  (originalCylinderNativeIso_projection D.U D.Tc D.eT) D.B₀ D.a.left

end OriginalRepresentativeGeometry

/-- The geometric hypotheses of the original first localization, stored once. -/
structure OriginalHistorySeedData (k : Type u) [Field k]
    extends OriginalRepresentativeGeometry k where
  /-- The first coefficient ring is a domain. -/
  hd₀ : IsDomain Γ(B₀.toScheme, ⊤)
  /-- It is integrally closed. -/
  hn₀ : IsIntegrallyClosed Γ(B₀.toScheme, ⊤)
  /-- It is Noetherian. -/
  hno₀ : IsNoetherianRing Γ(B₀.toScheme, ⊤)
  /-- The original restricted source map is étale. -/
  hp₀ : Etale toOriginalRepresentativeGeometry.nativeSourceMap
  /-- That source map is quasi-compact. -/
  hqc₀ : QuasiCompact toOriginalRepresentativeGeometry.nativeSourceMap
  /-- That source map is separated. -/
  hsep₀ : IsSeparated toOriginalRepresentativeGeometry.nativeSourceMap
  /-- The restricted original marking is closed. -/
  hzc₀ : IsClosedImmersion toOriginalRepresentativeGeometry.nativeMarkedMap
  /-- The whole marking is finite over the coefficient base. -/
  hzf₀ : IsFinite (toOriginalRepresentativeGeometry.nativeMarkedMap ≫
    boundaryLineProjection Γ(B₀.toScheme, ⊤))
  /-- The marked lift retains its original equation. -/
  hsN : s₀ ≫ toOriginalRepresentativeGeometry.nativeSourceMap =
    toOriginalRepresentativeGeometry.nativeMarkedMap
  /-- The original marked square is Cartesian. -/
  HN : IsPullback s₀ (𝟙 _) toOriginalRepresentativeGeometry.nativeSourceMap
    toOriginalRepresentativeGeometry.nativeMarkedMap

namespace OriginalHistorySeedData
variable {k : Type u} [Field k] (D : OriginalHistorySeedData k)

/-- Package the same first-stage geometry into the generic localization seed. -/
def toSeed : OriginalLocalizationSeed.{u} where
  R := (Γ(D.B₀.toScheme, ⊤)).carrier
  commRing := (Γ(D.B₀.toScheme, ⊤)).commRing
  domain := D.hd₀
  normal := D.hn₀
  noetherian := D.hno₀
  Y := D.W.toScheme
  A := ((D.a.left ≫ D.toOriginalRepresentativeGeometry.coefficientMap) ⁻¹ᵁ D.B₀).toScheme
  Z := ((D.z ≫ D.toOriginalRepresentativeGeometry.coefficientMap) ⁻¹ᵁ D.B₀).toScheme
  affineY := D.affineW
  affineA := Scheme.originalAffineRefinedNativePuncture_affine Γ(D.U.left, ⊤)
    D.toOriginalRepresentativeGeometry.coordinateIso
    D.toOriginalRepresentativeGeometry.coefficientMap
    (originalCylinderNativeIso_projection D.U D.Tc D.eT) D.B₀ D.a.left
  p := D.toOriginalRepresentativeGeometry.nativeSourceMap
  etaleP := D.hp₀
  quasiCompactP := D.hqc₀
  separatedP := D.hsep₀
  a := D.toOriginalRepresentativeGeometry.nativePunctureMap
  openA := inferInstance
  z := D.toOriginalRepresentativeGeometry.nativeMarkedMap
  closedZ := D.hzc₀
  finiteZ := D.hzf₀
  s := D.s₀
  hs := D.hsN
  H := D.HN
  hz := Scheme.originalAffineRefinedNative_complement Γ(D.U.left, ⊤)
    D.toOriginalRepresentativeGeometry.coordinateIso
    D.toOriginalRepresentativeGeometry.coefficientMap
    (originalCylinderNativeIso_projection D.U D.Tc D.eT) D.B₀ D.a.left D.z D.hcomp
  O := D.O
  affineO := D.affineO


end OriginalHistorySeedData

/-- The same two chosen coefficient opens and their original common-choice equations. -/
structure OriginalHistoryData (k : Type u) [Field k] extends OriginalHistorySeedData k where
  /-- The final chosen coefficient open. -/
  V : (Spec Γ(O.toScheme, ⊤)).Opens
  /-- Affineness of the final open. -/
  [affineV : IsAffine V.toScheme]
  /-- The first retained source square over the common coefficient ring. -/
  hq₁ : toOriginalHistorySeedData.toSeed.j₁ ≫
      (toOriginalHistorySeedData.toSeed.F₁ ≫ ProjectiveSpace.toSpec
        toOriginalHistorySeedData.toSeed.R₁ (ULift.{u} (Fin 2))) =
    toOriginalHistorySeedData.toSeed.p₁ ≫
      boundaryLineProjection toOriginalHistorySeedData.toSeed.R₁
  /-- The original marked equation on that common choice. -/
  hs₁ : toOriginalHistorySeedData.toSeed.s₁ ≫ toOriginalHistorySeedData.toSeed.p₁ =
    toOriginalHistorySeedData.toSeed.z₁

attribute [local instance] OriginalHistoryData.affineV

namespace OriginalHistoryData
variable {k : Type u} [Field k] (D : OriginalHistoryData k)

/-- The generic two-localization history of the stored original data. -/
def history : OriginalLocalizationHistory.{u} where
  seed := D.toOriginalHistorySeedData.toSeed
  V := D.V
  affineV := D.affineV
  hq₁ := D.hq₁
  hs₁ := D.hs₁

end OriginalHistoryData

/-- One fixed history together with its boundary, source and target section witnesses. -/
structure OriginalHistoryContext (k : Type u) [Field k] where
  /-- The original geometry and chosen localizations. -/
  data : OriginalHistoryData k
  /-- Boundary witnesses for that history. -/
  boundary : data.history.BoundaryWitnesses
  /-- Source witnesses using that same boundary. -/
  source : data.history.SourceWitnesses boundary
  /-- Target witnesses for that same history. -/
  target : data.history.TargetWitnesses

namespace OriginalHistoryContext
variable {k : Type u} [Field k] (C : OriginalHistoryContext k)

/-- The literal final coefficient-to-field map of the stored original base. -/
abbrev fieldMap := SmoothSite.nativeOriginalFinalFieldMap C.data.U C.data.B₀ C.data.O C.data.V

/-- The native middle input of this variable history. -/
def native : NativeOriginalMiddleInput k := C.source.toNative C.target C.fieldMap

/-- Its two actual localization restrictions. -/
def ancestry : C.native.NativeAncestry := C.source.toNativeAncestry C.target C.fieldMap

end OriginalHistoryContext
end Motivic.PresheafWithTransfers.OriginalHistorySiteLifting
