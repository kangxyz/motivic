/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.NativeCoefficientFieldLifting
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.OriginalCoefficientRestriction
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.NativeComplement
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.DistinguishedSquare
/-! # The actual twice-restricted native distinguished cover

The original affine source and puncture are restricted on exactly the two
retained coefficient opens. Their final arrows cover the whole native line.
No representative or section of a transfer presheaf is chosen here.

Intended upstream module:
`Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.NativeCoefficientCover`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`NativeRefinement.OriginalRefinedCover`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Hom RelativeProjectiveLine
universe u


namespace AlgebraicGeometry.Scheme
variable (R : Type u) [CommRing R] {T A : Scheme.{u}}
  (e : T ≅ Spec (.of (Polynomial R))) (q : T ⟶ Spec (.of R))
  (hq : e.hom ≫ boundaryLineProjection R = q)
  (B : (Spec (.of R)).Opens) [IsAffine B.toScheme]
  (a : A ⟶ T)
  (O : (Spec Γ(B.toScheme, ⊤)).Opens) [IsAffine O.toScheme]
  (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme]

/-- The native puncture remembers its original map and literal coefficient restriction. -/
@[reassoc]
theorem originalAffineRefinedNativePuncture_coordinate :
    originalAffineRefinedNativePuncture R e q hq B a ≫
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
        (ConstantCurve.affineSourceCoefficientMap R B.ι))) =
      ((a ≫ q) ⁻¹ᵁ B).ι ≫ a ≫ e.hom := by
  rw [originalAffineRefinedNativePuncture, Category.assoc,
    originalAffineRefinedTargetIso_coordinate, ← Category.assoc, morphismRestrict_ι]
  simp only [Category.assoc, Scheme.Hom.comp_preimage]

local notation "a₀" => originalAffineRefinedNativePuncture R e q hq B a
local notation "a₁" => sourceNativeCoverMap (B.toScheme.presheaf.obj (Opposite.op ⊤)) O a₀

/-- Both final puncture restrictions retain the original puncture arrow. -/
theorem originalAffineRefinedNativePuncture_twice_coordinate :
    sourceNativeCoverMap Γ(O.toScheme, ⊤) V a₁ ≫
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
        (ConstantCurve.affineSourceCoefficientMap Γ(O.toScheme, ⊤) V.ι))) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
        (ConstantCurve.affineSourceCoefficientMap Γ(B.toScheme, ⊤) O.ι))) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
        (ConstantCurve.affineSourceCoefficientMap R B.ι))) ≫ e.inv =
    (boundaryBaseCoverOpen (boundaryLineProjection Γ(O.toScheme, ⊤)) a₁ ⊤ V).ι ≫
      (boundaryBaseCoverOpen (boundaryLineProjection Γ(B.toScheme, ⊤)) a₀ ⊤ O).ι ≫
        ((a ≫ q) ⁻¹ᵁ B).ι ≫ a := by
  let m := Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
    (ConstantCurve.affineSourceCoefficientMap R B.ι)))
  let i₁ := (boundaryBaseCoverOpen (boundaryLineProjection Γ(B.toScheme, ⊤)) a₀ ⊤ O).ι
  let i₂ := (boundaryBaseCoverOpen (boundaryLineProjection Γ(O.toScheme, ⊤)) a₁ ⊤ V).ι
  have h₁ := sourceNativeCoverMap_twice_coordinate Γ(B.toScheme, ⊤) O V a₀
  have h₂ := originalAffineRefinedNativePuncture_coordinate R e q hq B a
  have h₁' := congrArg (fun f => f ≫ m ≫ e.inv) h₁
  have h₂' := congrArg (fun f => i₂ ≫ i₁ ≫ f ≫ e.inv) h₂
  have h₂'' : i₂ ≫ i₁ ≫ a₀ ≫ m ≫ e.inv =
      i₂ ≫ i₁ ≫ ((a ≫ q) ⁻¹ᵁ B).ι ≫ a := by
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h₂'
  calc
    _ = i₂ ≫ i₁ ≫ a₀ ≫ m ≫ e.inv := by
      simpa only [Category.assoc] using h₁'
    _ = _ := h₂''

end AlgebraicGeometry.Scheme
