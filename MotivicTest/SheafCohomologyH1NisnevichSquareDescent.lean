/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.SheafCohomologyH1NisnevichSquareDescent
public import Lean.Util.CollectAxioms

/-! # Geometric square descent for the original ordinary H¹ class -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry Opposite

universe w u

open Motivic Motivic.SheafCohomology

namespace MotivicTest.SheafCohomologyH1NisnevichSquareDescent

variable {S : Scheme.{u}}
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})]
  [EnoughInjectives (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})]

example
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
      (cokernel (Injective.ι F)).obj.map sq.f₃₄.op s) : x = 0 :=
  h_one_eq_zero_of_nisnevich_square_difference_surjective F sq hpb z hcomp
    hsurj x s hs lA lY hA hY

example
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
        (F.obj.map sq.f₁₂.op aA - F.obj.map sq.f₁₃.op aY)) : x = 0 :=
  h_one_eq_zero_of_nisnevich_square_correction
    F sq hpb z hcomp x s hs lA lY hA hY aA aY hcorr

variable {k : Type u} [Field k]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [EnoughInjectives (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

example
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
        (((SheafWithTransfers.toSheaf k).obj F).obj.map jB.op d)) : x = 0 :=
  h_one_eq_zero_of_nisnevich_square_restricted_homotopy
    F hF sq hpb z hcomp x s hs lA lY hA hY jB lam ψ α h₀ h₁ d hd

open Lean in
run_cmd do
  for name in #[``h_one_eq_zero_of_nisnevich_square_difference_surjective,
      ``h_one_eq_zero_of_nisnevich_square_correction,
      ``h_one_eq_zero_of_nisnevich_square_restricted_homotopy] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Geometric smooth Nisnevich H¹ square descent uses only standard Lean foundations."

end MotivicTest.SheafCohomologyH1NisnevichSquareDescent
