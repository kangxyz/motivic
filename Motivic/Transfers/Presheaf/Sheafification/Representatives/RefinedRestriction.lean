/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.Actions.Norm.NativeRefinement.NativeOriginalRefinedCover
public import Motivic.Transfers.Presheaf.Sheafification.Representatives.Restriction
/-! # Preserve the original representatives on the final common coefficient open

Only graph restrictions of the original sA and sV are used. Their images and
matching equation are transported along the literal final cover arrows.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Scheme.Hom RelativeProjectiveLine
universe u
namespace Motivic.PresheafWithTransfers
variable {k : Type u} [Field k]
  (P : PresheafWithTransfers.{u + 1} k)
  (U T : SmoothSite (Spec (.of k))) [IsAffine U.left]
  (e : T ≅ SmoothSite.a1Cylinder (.of k) U)
  (A Y : SmoothSite (Spec (.of k))) [IsAffine A.left]
  (a : A ⟶ T) [IsOpenImmersion a.left] (p : Y ⟶ T) [Etale p.left]
  (B : (Spec Γ(U.left, ⊤)).Opens) [IsAffine B.toScheme]
  (W : Y.left.Opens) [IsAffine W.toScheme]
  (hW : W ≤ p.left ⁻¹ᵁ (originalRepresentativeCoefficientMap U T e ⁻¹ᵁ B))
  (O : (Spec Γ(B.toScheme, ⊤)).Opens) [IsAffine O.toScheme]
  (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme]

local notation "a₂" => SmoothSite.nativeOriginalRefinedPunctureArrow U T e A a B O V
local notation "p₂" => SmoothSite.nativeOriginalRefinedSourceArrow U T e Y p B W hW O V
local notation "rA" => SmoothSite.nativeOriginalRefinedPunctureRestriction U T e A a B O V
local notation "rY" => SmoothSite.nativeOriginalRefinedSourceRestriction U T e Y p B W hW O V
local notation "h₂" => SmoothSite.nativeOriginalWholeCylinderMap U T e B O V

private theorem image_restriction
    {D E X : SmoothSite (Spec (.of k))} (r : D ⟶ E) (v : E ⟶ X)
    (s : (nisnevichImage P).sections (Cor.mk E))
    (g : ((nisnevichSheafify k).obj P).obj.sections (Cor.mk X))
    (hs : (nisnevichImageι P).hom.app (op (Cor.mk E)) s =
      ((nisnevichSheafify k).obj P).obj.transfer ((Cor.graphFunctor k).map v) g) :
    (nisnevichImageι P).hom.app (op (Cor.mk D))
      ((nisnevichImage P).transfer ((Cor.graphFunctor k).map r) s) =
        ((nisnevichSheafify k).obj P).obj.transfer ((Cor.graphFunctor k).map (r ≫ v)) g := by
  have hn : (nisnevichImageι P).hom.app (op (Cor.mk D))
      ((nisnevichImage P).transfer ((Cor.graphFunctor k).map r) s) =
      ((nisnevichSheafify k).obj P).obj.transfer ((Cor.graphFunctor k).map r)
        ((nisnevichImageι P).hom.app (op (Cor.mk E)) s) :=
    (nisnevichImageι P).hom.naturality_apply ((Cor.graphFunctor k).map r).op s
  rw [hn, hs]
  simp only [Functor.map_comp, transfer_comp, ConcreteCategory.comp_apply]

/-- The original source representative has exactly its original sheafification
image after the final restriction, with no new representative selected. -/
theorem originalRefinedSource_representative_image
    {X : SmoothSite (Spec (.of k))} (j : U ⟶ X)
    (sY : (nisnevichImage P).sections (Cor.mk Y))
    (g : ((nisnevichSheafify k).obj P).obj.sections (Cor.mk (SmoothSite.a1Cylinder (.of k) X)))
    (hs : (nisnevichImageι P).hom.app (op (Cor.mk Y)) sY =
      ((nisnevichSheafify k).obj P).obj.transfer
        ((Cor.graphFunctor k).map (p ≫ e.hom ≫ SmoothSite.a1Map (.of k) j)) g) :
    (nisnevichImageι P).hom.app
      (op (Cor.mk (SmoothSite.nativeOriginalRefinedSourceSite U T e Y p B W hW O V)))
      ((nisnevichImage P).transfer ((Cor.graphFunctor k).map rY) sY) =
      ((nisnevichSheafify k).obj P).obj.transfer
        ((Cor.graphFunctor k).map (p₂ ≫ h₂ ≫ e.hom ≫ SmoothSite.a1Map (.of k) j)) g := by
  have h := image_restriction P rY (p ≫ e.hom ≫ SmoothSite.a1Map (.of k) j) sY g hs
  simpa only [← Category.assoc, SmoothSite.nativeOriginalRefinedSourceRestriction_comp] using h

/-- The original puncture representative is likewise only restricted. -/
theorem originalRefinedPuncture_representative_image
    {X : SmoothSite (Spec (.of k))} (j : U ⟶ X)
    (sA : (nisnevichImage P).sections (Cor.mk A))
    (g : ((nisnevichSheafify k).obj P).obj.sections (Cor.mk (SmoothSite.a1Cylinder (.of k) X)))
    (hs : (nisnevichImageι P).hom.app (op (Cor.mk A)) sA =
      ((nisnevichSheafify k).obj P).obj.transfer
        ((Cor.graphFunctor k).map (a ≫ e.hom ≫ SmoothSite.a1Map (.of k) j)) g) :
    (nisnevichImageι P).hom.app
      (op (Cor.mk (SmoothSite.nativeOriginalRefinedPunctureSite U T e A a B O V)))
      ((nisnevichImage P).transfer ((Cor.graphFunctor k).map rA) sA) =
      ((nisnevichSheafify k).obj P).obj.transfer
        ((Cor.graphFunctor k).map (a₂ ≫ h₂ ≫ e.hom ≫ SmoothSite.a1Map (.of k) j)) g := by
  have h := image_restriction P rA (a ≫ e.hom ≫ SmoothSite.a1Map (.of k) j) sA g hs
  simpa only [← Category.assoc, SmoothSite.nativeOriginalRefinedPunctureRestriction_comp] using h

/-- Matching of the same two original sections survives every test overlap of
the final cover. In particular this applies to its actual étale pullback. -/
theorem originalRefined_representatives_matching
    {D C : SmoothSite (Spec (.of k))}
    (bA : C ⟶ A) (bY : C ⟶ Y) (H : IsPullback bA bY a p)
    (dA : D ⟶ SmoothSite.nativeOriginalRefinedPunctureSite U T e A a B O V)
    (dY : D ⟶ SmoothSite.nativeOriginalRefinedSourceSite U T e Y p B W hW O V)
    (hd : dA ≫ a₂ = dY ≫ p₂)
    (sA : (nisnevichImage P).sections (Cor.mk A))
    (sY : (nisnevichImage P).sections (Cor.mk Y))
    (hm : (nisnevichImage P).transfer ((Cor.graphFunctor k).map bA) sA =
      (nisnevichImage P).transfer ((Cor.graphFunctor k).map bY) sY) :
    (nisnevichImage P).transfer ((Cor.graphFunctor k).map dA)
      ((nisnevichImage P).transfer ((Cor.graphFunctor k).map rA) sA) =
    (nisnevichImage P).transfer ((Cor.graphFunctor k).map dY)
      ((nisnevichImage P).transfer ((Cor.graphFunctor k).map rY) sY) := by
  have hc : (dA ≫ rA) ≫ a = (dY ≫ rY) ≫ p := by
    rw [Category.assoc, SmoothSite.nativeOriginalRefinedPunctureRestriction_comp,
      ← Category.assoc, hd, Category.assoc,
      ← SmoothSite.nativeOriginalRefinedSourceRestriction_comp,
      ← Category.assoc]
  let δ := H.lift (dA ≫ rA) (dY ≫ rY) hc
  have hA := congrArg (fun f => (nisnevichImage P).transfer
    ((Cor.graphFunctor k).map f) sA) (H.lift_fst (dA ≫ rA) (dY ≫ rY) hc)
  have hY := congrArg (fun f => (nisnevichImage P).transfer
    ((Cor.graphFunctor k).map f) sY) (H.lift_snd (dA ≫ rA) (dY ≫ rY) hc)
  simp only [Functor.map_comp, transfer_comp, ConcreteCategory.comp_apply] at hA hY
  exact hA.symm.trans ((congrArg (fun x => (nisnevichImage P).transfer
    ((Cor.graphFunctor k).map δ) x) hm).trans hY)

end Motivic.PresheafWithTransfers
