/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.SmoothSiteNisnevichDistinguishedSquare
public import Motivic.Cohomology.SheafCohomologyH1SquareDescent
public import Motivic.Cohomology.A1.SquareDifferenceActions

/-!
# Ordinary H¹ descent on an actual smooth Nisnevich distinguished square

The geometric distinguished-square theorem supplies the gluing of the actual
ordinary injective sheaf and its actual cokernel. A surjective coefficient
difference and the displayed local lifts then kill the original H¹ class.
Neither difference surjectivity nor the existence of these lifts is assumed
as part of the geometry or hidden in a replacement coefficient object.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry Opposite

universe w u

namespace Motivic.SheafCohomology

variable {S : Scheme.{u}}
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})]
  [EnoughInjectives (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})]

/-- A literal surjective coefficient difference on a geometric Nisnevich
square kills a represented ordinary H¹ class with the displayed local lifts.
Gluing for the original injective presentation is proved from the geometry. -/
theorem h_one_eq_zero_of_nisnevich_square_difference_surjective
    (F : Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})
    (sq : Square (SmoothSite S)) (hpb : sq.IsPullback)
    [IsOpenImmersion sq.f₂₄.left] [Etale sq.f₃₄.left]
    {Z : Scheme.{u}} (z : Z ⟶ sq.X₄.left) [IsClosedImmersion z]
    (hcomp : Set.range z = (Set.range sq.f₂₄.left)ᶜ)
    [IsIso (pullback.snd sq.f₃₄.left z)]
    (hsurj : Function.Surjective (fun a : F.obj.obj (op sq.X₂) × F.obj.obj (op sq.X₃) =>
      F.obj.map sq.f₁₂.op a.1 - F.obj.map sq.f₁₃.op a.2))
    (x : H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology S) F 1 sq.X₄)
    (s : (cokernel (Injective.ι F)).obj.obj (op sq.X₄))
    (hs : injectiveSectionBoundary (SmoothSite.nisnevichTopology S) F sq.X₄ s = x)
    (lA : (Injective.under F).obj.obj (op sq.X₂))
    (lY : (Injective.under F).obj.obj (op sq.X₃))
    (hA : (cokernel.π (Injective.ι F)).hom.app (op sq.X₂) lA =
      (cokernel (Injective.ι F)).obj.map sq.f₂₄.op s)
    (hY : (cokernel.π (Injective.ι F)).hom.app (op sq.X₃) lY =
      (cokernel (Injective.ι F)).obj.map sq.f₃₄.op s) : x = 0 := by
  have hI := SmoothSite.isPullback_op_map_of_iso_complement sq hpb z hcomp
    (Injective.under F)
  have hQ := SmoothSite.isPullback_op_map_of_iso_complement sq hpb z hcomp
    (cokernel (Injective.ι F))
  exact h_one_eq_zero_of_square_difference_surjective (SmoothSite.nisnevichTopology S)
    F sq ((forget AddCommGrpCat.{u + 1}).map_isPullback hI)
    ((forget AddCommGrpCat.{u + 1}).map_isPullback hQ) hsurj x s hs lA lY hA hY

/-- Correcting the discrepancy of these two actual lifts suffices; no
surjectivity of the difference map on all overlap sections is required. -/
theorem h_one_eq_zero_of_nisnevich_square_correction
    (F : Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})
    (sq : Square (SmoothSite S)) (hpb : sq.IsPullback)
    [IsOpenImmersion sq.f₂₄.left] [Etale sq.f₃₄.left]
    {Z : Scheme.{u}} (z : Z ⟶ sq.X₄.left) [IsClosedImmersion z]
    (hcomp : Set.range z = (Set.range sq.f₂₄.left)ᶜ)
    [IsIso (pullback.snd sq.f₃₄.left z)]
    (x : H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology S) F 1 sq.X₄)
    (s : (cokernel (Injective.ι F)).obj.obj (op sq.X₄))
    (hs : injectiveSectionBoundary (SmoothSite.nisnevichTopology S) F sq.X₄ s = x)
    (lA : (Injective.under F).obj.obj (op sq.X₂))
    (lY : (Injective.under F).obj.obj (op sq.X₃))
    (hA : (cokernel.π (Injective.ι F)).hom.app (op sq.X₂) lA =
      (cokernel (Injective.ι F)).obj.map sq.f₂₄.op s)
    (hY : (cokernel.π (Injective.ι F)).hom.app (op sq.X₃) lY =
      (cokernel (Injective.ι F)).obj.map sq.f₃₄.op s)
    (aA : F.obj.obj (op sq.X₂)) (aY : F.obj.obj (op sq.X₃))
    (hcorr : (Injective.under F).obj.map sq.f₁₂.op lA -
        (Injective.under F).obj.map sq.f₁₃.op lY =
      (Injective.ι F).hom.app (op sq.X₁)
        (F.obj.map sq.f₁₂.op aA - F.obj.map sq.f₁₃.op aY)) : x = 0 := by
  let J := SmoothSite.nisnevichTopology S
  let E := injectivePresentation.{u + 1, u, u + 1} J F
  have hE : E.ShortExact := injectivePresentation_shortExact.{u + 1, u, u + 1} J F
  have hI := (forget AddCommGrpCat.{u + 1}).map_isPullback
    (SmoothSite.isPullback_op_map_of_iso_complement sq hpb z hcomp E.X₂)
  have hQ := (forget AddCommGrpCat.{u + 1}).map_isPullback
    (SmoothSite.isPullback_op_map_of_iso_complement sq hpb z hcomp E.X₃)
  change E.X₂.obj.obj (op sq.X₂) at lA
  change E.X₂.obj.obj (op sq.X₃) at lY
  have hcompat :
      E.X₂.obj.map sq.f₁₂.op (lA - E.f.hom.app (op sq.X₂) aA) =
        E.X₂.obj.map sq.f₁₃.op (lY - E.f.hom.app (op sq.X₃) aY) := by
    rw [map_sub, map_sub, ← E.f.hom.naturality_apply sq.f₁₂.op aA,
      ← E.f.hom.naturality_apply sq.f₁₃.op aY]
    change E.X₂.obj.map sq.f₁₂.op lA - E.X₂.obj.map sq.f₁₃.op lY =
      E.f.hom.app (op sq.X₁)
        (E.X₁.obj.map sq.f₁₂.op aA - E.X₁.obj.map sq.f₁₃.op aY) at hcorr
    rw [map_sub] at hcorr
    exact sub_eq_sub_iff_sub_eq_sub.mp hcorr
  obtain ⟨l, hlA, hlY⟩ := Types.exists_of_isPullback hI
    (lA - E.f.hom.app (op sq.X₂) aA) (lY - E.f.hom.app (op sq.X₃) aY) hcompat
  change E.X₂.obj.map sq.f₂₄.op l = _ at hlA
  change E.X₂.obj.map sq.f₃₄.op l = _ at hlY
  have hzero (T : SmoothSite S) (a : E.X₁.obj.obj (op T)) :
      E.g.hom.app (op T) (E.f.hom.app (op T) a) = 0 := by
    exact ConcreteCategory.congr_hom
      (congrArg (fun η => η.hom.app (op T)) E.zero) a
  have hl : E.g.hom.app (op sq.X₄) l = s := by
    apply Types.ext_of_isPullback hQ
    · change E.X₃.obj.map sq.f₂₄.op (E.g.hom.app (op sq.X₄) l) =
        E.X₃.obj.map sq.f₂₄.op s
      rw [← E.g.hom.naturality_apply sq.f₂₄.op l, hlA, map_sub, hzero, sub_zero]
      exact hA
    · change E.X₃.obj.map sq.f₃₄.op (E.g.hom.app (op sq.X₄) l) =
        E.X₃.obj.map sq.f₃₄.op s
      rw [← E.g.hom.naturality_apply sq.f₃₄.op l, hlY, map_sub, hzero, sub_zero]
      exact hY
  rw [← hs, injectiveSectionBoundary_apply]
  have h := boundary_restriction_eq_zero_of_imageSieve.{w, u + 1, u, u + 1} J hE
    ((zeroSections.{w, u + 1, u, u + 1} J E.X₃ sq.X₄).symm s) (𝟙 sq.X₄)
    ⟨l, by simpa using hl⟩
  change ((zeroSections.{w, u + 1, u, u + 1} J E.X₃ sq.X₄).symm s).comp
    hE.extClass rfl = 0
  simpa using h

variable {k : Type u} [Field k]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [EnoughInjectives (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- A homotopy with graph endpoint from a smaller overlap corrects a specific
restricted discrepancy and kills the represented class on the smaller square.
It does not assert surjectivity on arbitrary sections of that overlap. -/
theorem h_one_eq_zero_of_nisnevich_square_restricted_homotopy
    (F : SheafWithTransfers.{u + 1} k)
    (hF : PresheafWithTransfers.IsA1Invariant F.obj)
    (sq : Square (SmoothSite (Spec (.of k)))) (hpb : sq.IsPullback)
    [IsOpenImmersion sq.f₂₄.left] [Etale sq.f₃₄.left]
    {Z : Scheme.{u}} (z : Z ⟶ sq.X₄.left) [IsClosedImmersion z]
    (hcomp : Set.range z = (Set.range sq.f₂₄.left)ᶜ)
    [IsIso (pullback.snd sq.f₃₄.left z)]
    (x : H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) 1 sq.X₄)
    (s : (cokernel (Injective.ι ((SheafWithTransfers.toSheaf k).obj F))).obj.obj (op sq.X₄))
    (hs : injectiveSectionBoundary (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) sq.X₄ s = x)
    (lA : (Injective.under ((SheafWithTransfers.toSheaf k).obj F)).obj.obj (op sq.X₂))
    (lY : (Injective.under ((SheafWithTransfers.toSheaf k).obj F)).obj.obj (op sq.X₃))
    (hA : (cokernel.π (Injective.ι ((SheafWithTransfers.toSheaf k).obj F))).hom.app (op sq.X₂) lA =
      (cokernel (Injective.ι ((SheafWithTransfers.toSheaf k).obj F))).obj.map sq.f₂₄.op s)
    (hY : (cokernel.π (Injective.ι ((SheafWithTransfers.toSheaf k).obj F))).hom.app (op sq.X₃) lY =
      (cokernel (Injective.ι ((SheafWithTransfers.toSheaf k).obj F))).obj.map sq.f₃₄.op s)
    {B : SmoothSite (Spec (.of k))} (jB : sq.X₁ ⟶ B)
    (lam : Cor.mk sq.X₃ ⟶ Cor.mk B) (ψ : Cor.mk sq.X₂ ⟶ Cor.mk B)
    (α : Cor.mk (SmoothSite.a1Cylinder (.of k) sq.X₁) ⟶ Cor.mk B)
    (h₀ : (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) sq.X₁ 0) ≫ α =
      (Cor.graphFunctor k).map jB)
    (h₁ : (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) sq.X₁ 1) ≫ α =
      (Cor.graphFunctor k).map sq.f₁₃ ≫ lam - (Cor.graphFunctor k).map sq.f₁₂ ≫ ψ)
    (d : ((SheafWithTransfers.toSheaf k).obj F).obj.obj (op B))
    (hd : (Injective.under ((SheafWithTransfers.toSheaf k).obj F)).obj.map sq.f₁₂.op lA -
        (Injective.under ((SheafWithTransfers.toSheaf k).obj F)).obj.map sq.f₁₃.op lY =
      (Injective.ι ((SheafWithTransfers.toSheaf k).obj F)).hom.app (op sq.X₁)
        (((SheafWithTransfers.toSheaf k).obj F).obj.map jB.op d)) : x = 0 := by
  apply h_one_eq_zero_of_nisnevich_square_correction
    ((SheafWithTransfers.toSheaf k).obj F) sq hpb z hcomp x s hs lA lY hA hY
    (-F.obj.transfer ψ d) (-F.obj.transfer lam d)
  rw [F.restriction_difference_eq_restriction_of_homotopy hF jB sq.f₁₂ sq.f₁₃
    lam ψ α h₀ h₁ d]
  exact hd

end Motivic.SheafCohomology
