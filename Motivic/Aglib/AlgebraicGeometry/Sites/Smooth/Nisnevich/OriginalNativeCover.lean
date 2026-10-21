/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.NativeCover
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.NativeCoefficientFieldLifting

/-! # The original native cover before coefficient specialization

Intended upstream module: `Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.OriginalNativeCover`.

An original étale source, open puncture, closed complementary marked scheme and
its unchanged Cartesian lifting square yield the twice restricted Nisnevich
cover. The actual source and target site objects are retained. Their underlying
maps are the literal restrictions followed by the specified target scheme isomorphism.
The coefficient ring is a native `CommRingCat` object. The current consumer is
`NativeRefinement.NativeOriginalRefinedCover`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.Hom RelativeProjectiveLine

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

/-- Transport a chosen lift through the same target isomorphism. -/
private theorem lift_comp_iso_eq {C : Type*} [Category C] {Z Y L T : C}
    (b : Z ⟶ Y) (a : Y ⟶ L) (x : Z ⟶ T) (e : L ≅ T)
    (h : b ≫ a = x ≫ e.inv) : b ≫ (a ≫ e.hom) = x := by
  rw [← Category.assoc, h, Category.assoc, e.inv_hom_id, Category.comp_id]

variable {k : Type u} [Field k] (R : CommRingCat.{u})
  {T A Y : Scheme.{u}}
  (e : T ≅ Spec (.of (Polynomial R))) (q : T ⟶ Spec R)
  (hq : e.hom ≫ boundaryLineProjection R = q)
  (a : A ⟶ T) [IsOpenImmersion a] (p : Y ⟶ T)
  (B : (Spec R).Opens) [IsAffine B.toScheme]
  (W : Y.Opens) (hW : W ≤ p ⁻¹ᵁ (q ⁻¹ᵁ B))
  (O : (Spec Γ(B.toScheme, ⊤)).Opens) [IsAffine O.toScheme]
  (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme]
  (u : originalAffineRefinedPunctureScheme R e q hq B a O V ⟶ Spec (.of k))
  [Smooth u] [IsSeparated u] [QuasiCompact u]
  (v : originalAffineRefinedSourceScheme R e q hq B p W hW O V ⟶ Spec (.of k))
  [Smooth v] [IsSeparated v] [QuasiCompact v]
  (D : SmoothSite (Spec (.of k)))
  (α : mk u ⟶ D) [Etale α.left] (β : mk v ⟶ D) [Etale β.left]
  (f : Spec (.of (Polynomial Γ(V.toScheme, ⊤))) ≅ D.left)
  (hα : α.left = originalAffineRefinedPunctureMap R e q hq B a O V ≫ f.hom)
  (hβ : β.left = originalAffineRefinedSourceMap R e q hq B p W hW O V ≫ f.hom)

include f hα hβ in
/-- The original marked lift covers the actual site arrows with the specified native maps. -/
theorem originalAffineRefinedCover_mem_nisnevichTopology
    {Z : Scheme.{u}} (z : Z ⟶ T) [IsClosedImmersion z]
    (hz : Set.range z = (Set.range a)ᶜ)
    (s : ((z ≫ q) ⁻¹ᵁ B).toScheme ⟶ W.toScheme)
    (H : IsPullback s (𝟙 _) (p.resLE (q ⁻¹ᵁ B) W hW) (z ∣_ (q ⁻¹ᵁ B))) :
    Sieve.ofTwoArrows α β ∈ nisnevichTopology (Spec (.of k)) D := by
  let p₀ := originalAffineRefinedNativeMap R e q hq B p W hW
  let a₀ := originalAffineRefinedNativePuncture R e q hq B a
  let z₀ := originalAffineRefinedNativeMarked R e q hq B z
  have H₀ := originalAffineRefinedNativeMarked_isPullback R e q hq B p W hW z s H
  have hs : s ≫ p₀ = z₀ := by simpa only [Category.id_comp] using H₀.w
  have hz₀ : Set.range z₀ = (Set.range a₀)ᶜ :=
    originalAffineRefinedNative_complement R e q hq B a z hz
  apply ofTwoArrows_mem_nisnevichTopology_of_field_lifting
  intro K _ x
  obtain ⟨b, hb⟩ | ⟨c, hc⟩ := nativeCoefficientCover_field_lifting
    Γ(B.toScheme, ⊤) O V p₀ a₀ z₀ s hs hz₀ (x ≫ f.inv)
  · exact Or.inl ⟨b, (congrArg (fun m => b ≫ m) hα).trans
      (lift_comp_iso_eq b (originalAffineRefinedPunctureMap R e q hq B a O V) x f hb)⟩
  · exact Or.inr ⟨c, (congrArg (fun m => c ≫ m) hβ).trans
      (lift_comp_iso_eq c (originalAffineRefinedSourceMap R e q hq B p W hW O V) x f hc)⟩

end AlgebraicGeometry.Scheme.SmoothSite
