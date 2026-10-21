/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.Sheafification.NativeActionLifting
public import Motivic.Transfers.Presheaf.Actions.Norm.NativeRefinement.OriginalHistoryRestrictions
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.NativeMiddleInput
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.NativeOriginalBase
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.NativeOriginalCylinder

/-! # Whole-cylinder lifting on the original history

For an HI `P : PresheafWithTransfers.{u + 1} k` over a field, join the fixed
original history and its boundary, source and target witnesses to the original
matching image representatives. The displayed affine coefficient/source
refinements and the whole marked scheme with its pullback square are retained.

The native source and puncture restrictions and the original cylinder
comparison transport the given Nisnevich cover into the lifting adapter.
`wholeCylinder_lift` returns an image section on the whole cylinder over
`nativeOriginalBaseSite`, retaining the composite original base inclusion and
its sheafification-unit equation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Scheme Scheme.Hom Scheme.Modules Scheme.Modules.Invertible
open Scheme.RelativeAffineLineEtaleCompactification Scheme.RelativeCurvePencil
open RelativeProjectiveLine AlgebraicGeometry.FiniteSchemeNormBaseChange
open Motivic Motivic.PresheafWithTransfers
universe u v w
open AlgebraicGeometry.FiniteSchemeNormBaseChange
open AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates

namespace Motivic.PresheafWithTransfers.NativeOwnedOriginalHistorySiteLifting
open OriginalHistorySiteLifting

-- These are caller-local instances, not assumed exports of a native action leaf.
local instance sharedInputSmoothOfRelativeDimension {X Y : Scheme.{u}} (f : X ⟶ Y)
    [SmoothOfRelativeDimension 1 f] : Smooth f :=
  SmoothOfRelativeDimension.smooth 1 f

local instance (R : Type u) [CommRing R] :
    SmoothOfRelativeDimension 1 (boundaryLineProjection R) :=
  Scheme.AffineLineEtaleCompactification.polynomialProjection_smooth_one R

local instance (R : Type u) [CommRing R] :
    SmoothOfRelativeDimension 1
      (chart R 0 ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) := by
  rw [chart_toSpec]
  infer_instance


variable {k : Type u} [Field k]
  (U Tc : SmoothSite (Spec (.of k))) [IsAffine U.left]
  (eT : Tc ≅ SmoothSite.a1Cylinder (.of k) U)
  (A Y : SmoothSite (Spec (.of k))) [IsAffine A.left]
  (a : A ⟶ Tc) [IsOpenImmersion a.left] (p : Y ⟶ Tc) [Etale p.left]
  {Z : Scheme.{u}} (z : Z ⟶ Tc.left)
  (B₀ : (Spec Γ(U.left, ⊤)).Opens) [IsAffine B₀.toScheme]
  (W : Y.left.Opens) [IsAffine W.toScheme]


variable (hW : W ≤ p.left ⁻¹ᵁ ((originalRepresentativeCoefficientMap U Tc eT) ⁻¹ᵁ B₀))


variable (s₀ : ((z ≫ (originalRepresentativeCoefficientMap U Tc eT)) ⁻¹ᵁ B₀).toScheme ⟶ W.toScheme)
  (hcomp : Set.range z = (Set.range a.left)ᶜ)
  (hd₀ : IsDomain ((B₀.toScheme.presheaf.obj (Opposite.op ⊤)))) (hn₀ : IsIntegrallyClosed
      ((B₀.toScheme.presheaf.obj (Opposite.op ⊤)))) (hno₀ : IsNoetherianRing
      ((B₀.toScheme.presheaf.obj (Opposite.op ⊤))))
  (hp₀ : Etale (Scheme.originalAffineRefinedNativeMap
  (U.left.presheaf.obj (Opposite.op ⊤)) (originalCylinderNativeIso U Tc eT)
      (originalRepresentativeCoefficientMap U Tc eT) (originalCylinderNativeIso_projection U Tc
      eT) B₀ p.left W hW)) (hqc₀ : QuasiCompact (Scheme.originalAffineRefinedNativeMap
  (U.left.presheaf.obj (Opposite.op ⊤)) (originalCylinderNativeIso U Tc eT)
      (originalRepresentativeCoefficientMap U Tc eT) (originalCylinderNativeIso_projection U Tc
      eT) B₀ p.left W hW)) (hsep₀ : IsSeparated (Scheme.originalAffineRefinedNativeMap
  (U.left.presheaf.obj (Opposite.op ⊤)) (originalCylinderNativeIso U Tc eT)
      (originalRepresentativeCoefficientMap U Tc eT) (originalCylinderNativeIso_projection U Tc
      eT) B₀ p.left W hW))
  (hzc₀ : IsClosedImmersion (Scheme.originalAffineRefinedNativeMarked
  (U.left.presheaf.obj (Opposite.op ⊤)) (originalCylinderNativeIso U Tc eT)
      (originalRepresentativeCoefficientMap U Tc eT) (originalCylinderNativeIso_projection U Tc
      eT) B₀ z)) (hzf₀ : IsFinite ((Scheme.originalAffineRefinedNativeMarked
  (U.left.presheaf.obj (Opposite.op ⊤)) (originalCylinderNativeIso U Tc eT)
      (originalRepresentativeCoefficientMap U Tc eT) (originalCylinderNativeIso_projection U Tc
      eT) B₀ z) ≫ boundaryLineProjection ((B₀.toScheme.presheaf.obj (Opposite.op ⊤)))))
  (hsN : s₀ ≫ (Scheme.originalAffineRefinedNativeMap
  (U.left.presheaf.obj (Opposite.op ⊤)) (originalCylinderNativeIso U Tc eT)
      (originalRepresentativeCoefficientMap U Tc eT) (originalCylinderNativeIso_projection U Tc
      eT) B₀ p.left W hW) = (Scheme.originalAffineRefinedNativeMarked
  (U.left.presheaf.obj (Opposite.op ⊤)) (originalCylinderNativeIso U Tc eT)
      (originalRepresentativeCoefficientMap U Tc eT) (originalCylinderNativeIso_projection U Tc
      eT) B₀ z)) (HN : IsPullback s₀ (𝟙 _) (Scheme.originalAffineRefinedNativeMap
  (U.left.presheaf.obj (Opposite.op ⊤)) (originalCylinderNativeIso U Tc eT)
      (originalRepresentativeCoefficientMap U Tc eT) (originalCylinderNativeIso_projection U Tc
      eT) B₀ p.left W hW) (Scheme.originalAffineRefinedNativeMarked
  (U.left.presheaf.obj (Opposite.op ⊤)) (originalCylinderNativeIso U Tc eT)
      (originalRepresentativeCoefficientMap U Tc eT) (originalCylinderNativeIso_projection U Tc
      eT) B₀ z))
  (O : (Spec (.of ((B₀.toScheme.presheaf.obj (Opposite.op ⊤))))).Opens) [IsAffine O.toScheme]

variable (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme]
  (hq₁ : ((originalHistorySeed
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O))).j₁ ≫
      (((originalHistorySeed
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O))).F₁ ≫
      ProjectiveSpace.toSpec ((originalHistorySeed
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O))).R₁ (ULift.{u}
      (Fin 2))) =
    ((originalHistorySeed
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O))).p₁ ≫
      boundaryLineProjection ((originalHistorySeed
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O))).R₁)
  (hs₁ : ((originalHistorySeed
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O))).s₁ ≫
      ((originalHistorySeed
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O))).p₁ =
      ((originalHistorySeed
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O))).z₁)

omit [Etale p.left] in
/-- Lift the original representatives through the native-owned restriction diagram. -/
theorem wholeCylinder_lift
    (Bounds : ((originalHistory
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O)
  (V := V) (hq₁ := hq₁) (hs₁ := hs₁))).BoundaryWitnesses) (Wsrc : ((originalHistory
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O)
  (V := V) (hq₁ := hq₁) (hs₁ := hs₁))).SourceWitnesses Bounds)
    (Tsec : ((originalHistory
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O)
  (V := V) (hq₁ := hq₁) (hs₁ := hs₁))).TargetWitnesses)
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    {X Borig : SmoothSite (Spec (.of k))} (jU : U ⟶ X) [IsOpenImmersion jU.left]
    (bAorig : Borig ⟶ A) (bYorig : Borig ⟶ Y) (HB : IsPullback bAorig bYorig a p)
    (g : ((nisnevichSheafify k).obj P).obj.sections
      ((Cor.graphFunctor k).obj (SmoothSite.a1Cylinder (.of k) X)))
    (sA : (nisnevichImage P).sections ((Cor.graphFunctor k).obj A))
    (sY : (nisnevichImage P).sections ((Cor.graphFunctor k).obj Y))
    (hm : (nisnevichImage P).transfer ((Cor.graphFunctor k).map bAorig) sA =
      (nisnevichImage P).transfer ((Cor.graphFunctor k).map bYorig) sY)
    (hgA : (nisnevichImageι P).hom.app (op ((Cor.graphFunctor k).obj A)) sA =
      ((nisnevichSheafify k).obj P).obj.transfer
        ((Cor.graphFunctor k).map (a ≫ eT.hom ≫ SmoothSite.a1Map (.of k) jU)) g)
    (hgY : (nisnevichImageι P).hom.app (op ((Cor.graphFunctor k).obj Y)) sY =
      ((nisnevichSheafify k).obj P).obj.transfer
        ((Cor.graphFunctor k).map (p ≫ eT.hom ≫ SmoothSite.a1Map (.of k) jU)) g) :
    let U₂ := SmoothSite.nativeOriginalBaseSite U B₀ O V
    let l := SmoothSite.nativeOriginalBaseInclusion U B₀ O V
    IsOpenImmersion (l ≫ jU).left ∧ Nonempty U₂.left ∧
      ∃ t : (nisnevichImage P).sections
        ((Cor.graphFunctor k).obj (SmoothSite.a1Cylinder (.of k) U₂)),
        (nisnevichImageι P).hom.app
          (op ((Cor.graphFunctor k).obj (SmoothSite.a1Cylinder (.of k) U₂))) t =
          ((nisnevichSheafify k).obj P).obj.transfer
            ((Cor.graphFunctor k).map (SmoothSite.a1Map (.of k) (l ≫ jU))) g := by
  classical
  let t₂ := SmoothSite.nativeOriginalFinalFieldMap U B₀ O V
  let N := Wsrc.toNative Tsec (SmoothSite.nativeOriginalFinalFieldMap U B₀ O V)
  let m := (OriginalHistoryNativeLine.ownedLineRestriction
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
  (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
  (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
  (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec)
  let e := (OriginalHistoryNativeLine.ownedCylinderIso
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
  (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
  (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
  (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec)
  let rA := (OriginalHistoryNativeSiteAssembly.punctureRestriction
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
  (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
  (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
  (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec)
  let rY := (OriginalHistoryNativeSiteAssembly.sourceRestriction
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
  (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
  (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
  (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec)
  let D := (OriginalHistoryNativeSiteAssembly.transport
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
  (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
  (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
  (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec)
  have hD := (OriginalHistoryNativeSiteAssembly.transport_compatible
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
  (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
  (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
  (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec)
  let U₂ := SmoothSite.nativeOriginalBaseSite U B₀ O V
  let l := SmoothSite.nativeOriginalBaseInclusion U B₀ O V
  let : IsOpenImmersion l.left := inferInstance
  have hU₂ : Nonempty U₂.left :=
    SmoothSite.nativeOriginalBaseSite_nonempty U B₀ O V Bounds.x Bounds.hxV
  let h := SmoothSite.nativeOriginalWholeCylinderMap U Tc eT B₀ O V
  have he : h ≫ eT.hom = SmoothSite.a1Map (.of k) l :=
    SmoothSite.nativeOriginalWholeCylinderMap_comp U Tc eT B₀ O V
  let i' := N.aSite ≫ e.hom
  let v' := N.toInput.pSite ≫ e.hom
  have hline : e.hom ≫ h = m :=
    (OriginalHistoryNativeLine.ownedCylinderIso_comp
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
  (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
  (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
  (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec)
  have hA : rA ≫ a = N.aSite ≫ m :=
    (OriginalHistoryNativeSiteAssembly.punctureRestriction_comp
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
  (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
  (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
  (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec)
  have hY : rY ≫ p = N.toInput.pSite ≫ m :=
    (OriginalHistoryNativeSiteAssembly.sourceRestriction_comp
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
  (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
  (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
  (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec)
  have hi' : rA ≫ a = i' ≫ h :=
    hA.trans ((congrArg (fun f => N.aSite ≫ f) hline.symm).trans
      (Category.assoc N.aSite e.hom h).symm)
  have hv' : rY ≫ p = v' ≫ h :=
    hY.trans ((congrArg (fun f => N.toInput.pSite ≫ f) hline.symm).trans
      (Category.assoc N.toInput.pSite e.hom h).symm)
  let H := originalHistory
    (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
    (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
    (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
    (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁)
  have hp : N.p = H.p₂ := OriginalHistoryEndpointEqualities.native_p_eq_history
    (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
    (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
    (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
    (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec
  let : Etale N.p := by
    rw [hp]
    exact OriginalLocalizationHistory.sourceEtale H
  have hcover' : Sieve.ofTwoArrows i' v' ∈
      SmoothSite.nisnevichTopology (Spec (.of k)) (SmoothSite.a1Cylinder (.of k) U₂) :=
    N.nativeCover_mem_nisnevichTopology e
  exact Wsrc.wholeCylinder_lift Tsec t₂ P hP jU l hU₂ eT h he
    a p bAorig bYorig HB i' v' rA rY hi' hv' hcover'
    D.sourceComparison D.punctureComparison D.cylinderComparison
    D.sourceRestriction D.parameterRestriction
    hD.source hD.puncture hD.sourceRestriction hD.parameterRestriction hD.overlap
    g sA sY hm hgA hgY

end Motivic.PresheafWithTransfers.NativeOwnedOriginalHistorySiteLifting
