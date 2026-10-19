/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Source.NativeParameter
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.NativeComplement
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.DistinguishedSquare
/-! # Field lifting for the actual twice-restricted native cover

The original affine source and puncture are restricted on exactly the two
retained coefficient opens. Their final arrows cover the whole native line.
No representative or section of a transfer presheaf is chosen here.

Intended upstream module:
`Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.NativeCoefficientFieldLifting`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Nisnevich.NativeCoefficientCover`, `NativeRefinement.NativeOriginalRefinedCover`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Hom RelativeProjectiveLine
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite
variable {k : Type u} [Field k]
  (R : Type u) [CommRing R]
  (O : (Spec (.of R)).Opens) [IsAffine O.toScheme]
  (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme]
  {Y A Z : Scheme.{u}} [IsAffine Y] [IsAffine A]
  (p : Y ⟶ Spec (.of (Polynomial R))) [hp : Etale p]
  (a : A ⟶ Spec (.of (Polynomial R))) [ha : IsOpenImmersion a]
  (z : Z ⟶ Spec (.of (Polynomial R))) [hzClosed : IsClosedImmersion z]
  (s : Z ⟶ Y) (hs : s ≫ p = z)
  (hz : Set.range z = (Set.range a)ᶜ)

local notation "p₁" => sourceNativeCoverMap R O p
local notation "a₁" => sourceNativeCoverMap R O a
local notation "z₁" => targetNativeMarked R O z
local notation "p₂" => sourceNativeCoverMap (O.toScheme.presheaf.obj (Opposite.op ⊤)) V p₁
local notation "a₂" => sourceNativeCoverMap (O.toScheme.presheaf.obj (Opposite.op ⊤)) V a₁
local notation "z₂" => targetNativeMarked (O.toScheme.presheaf.obj (Opposite.op ⊤)) V z₁

omit [IsAffine Y] [IsAffine A] hp in
include z s hs hz ha hzClosed in
/-- The same marked section proves joint field lifting after both restrictions. -/
theorem nativeCoefficientCover_field_lifting
    {K : Type u} [Field K] (x : Spec (.of K) ⟶ Spec (.of (Polynomial Γ(V.toScheme, ⊤)))) :
    (∃ b, b ≫ a₂ = x) ∨ (∃ c, c ≫ p₂ = x) := by
  let s₁ := boundaryBaseCoverLift (boundaryLineProjection R) p z s hs ⊤ O
    (fun _ _ => trivial)
  have hs₁ : s₁ ≫ p₁ = z₁ := sourceNativeCoverLift_map R O z p s hs
  let s₂ := boundaryBaseCoverLift (boundaryLineProjection Γ(O.toScheme, ⊤))
    p₁ z₁ s₁ hs₁ ⊤ V (fun _ _ => trivial)
  have hs₂ : s₂ ≫ p₂ = z₂ :=
    sourceNativeCoverLift_map Γ(O.toScheme, ⊤) V z₁ p₁ s₁ hs₁
  have hz₂ : Set.range z₂ = (Set.range a₂)ᶜ :=
    sourceNativeCoverMap_marked_complement Γ(O.toScheme, ⊤) V a₁ z₁
      (sourceNativeCoverMap_marked_complement R O a z hz)
  obtain h | ⟨c, hc⟩ := Scheme.exists_field_lift_open_or_closed a₂ z₂ hz₂ x
  · exact Or.inl h
  · exact Or.inr ⟨c ≫ s₂, by rw [Category.assoc, hs₂, hc]⟩

include z s hs hz hp ha hzClosed in
/-- With the actual field structure on the final native line, its literal final
puncture and affine source form a Nisnevich cover. -/
theorem nativeCoefficientCover_mem_nisnevichTopology
    (t : Spec (.of (Polynomial Γ(V.toScheme, ⊤))) ⟶ Spec (.of k))
    [Smooth t] [IsSeparated t] [QuasiCompact t] :
    Sieve.ofTwoArrows
      (homMk a₂ (by rfl) : mk (a₂ ≫ t) ⟶ mk t)
      (homMk p₂ (by rfl) : mk (p₂ ≫ t) ⟶ mk t) ∈
        nisnevichTopology (Spec (.of k)) (mk t) := by
  let : Etale (homMk a₂ (by rfl) : mk (a₂ ≫ t) ⟶ mk t).left := by
    change Etale a₂
    infer_instance
  let : Etale (homMk p₂ (by rfl) : mk (p₂ ≫ t) ⟶ mk t).left := by
    change Etale p₂
    infer_instance
  apply ofTwoArrows_mem_nisnevichTopology_of_field_lifting
  intro K _ x
  exact nativeCoefficientCover_field_lifting R O V p a z s hs hz x

end AlgebraicGeometry.Scheme.SmoothSite
