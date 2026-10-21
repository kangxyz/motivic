/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.NativeComplement
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.PencilSites
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Target.AffineSpecSquare

/-! # Smooth-site objects of twice restricted native covers

Intended upstream module: `Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.NativeCover`.

The original source and puncture are restricted over the same two affine
coefficient opens. Their scheme objects, literal native maps, affineness,
étaleness and original restriction squares are constructed over a native ring
object before specialization. Smooth-site arrows use the actual target site
object. Current consumers are `NativeOriginalRefinedSource`,
`NativeOriginalRefinedPuncture` and `Nisnevich.OriginalNativeCover`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Scheme.Hom RelativeProjectiveLine

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

/-- Compose three actual restriction squares and cancel the two coordinate isomorphisms. -/
theorem threeRestrictionSquares
    {C : Type*} [Category C] {Y₂ Y₁ Y₀ Y L₂ L₁ L₀ N T D : C}
    (p₂ : Y₂ ⟶ L₂) (p₁ : Y₁ ⟶ L₁) (p₀ : Y₀ ⟶ L₀) (p : Y ⟶ T)
    (i₂ : Y₂ ⟶ Y₁) (i₁ : Y₁ ⟶ Y₀) (i₀ : Y₀ ⟶ Y)
    (τV : L₂ ⟶ L₁) (τO : L₁ ⟶ L₀) (τB : L₀ ⟶ N)
    (e : T ≅ N) (f : L₂ ≅ D)
    (hV : p₂ ≫ τV = i₂ ≫ p₁) (hO : p₁ ≫ τO = i₁ ≫ p₀)
    (hB : p₀ ≫ τB = i₀ ≫ p ≫ e.hom) :
    (i₂ ≫ i₁ ≫ i₀) ≫ p =
      (p₂ ≫ f.hom) ≫ (f.inv ≫ ((τV ≫ τO ≫ τB) ≫ e.inv)) := by
  have hc : p₂ ≫ ((τV ≫ τO ≫ τB) ≫ e.inv) = i₂ ≫ i₁ ≫ i₀ ≫ p := by
    calc
      _ = i₂ ≫ p₁ ≫ τO ≫ τB ≫ e.inv := by
        simpa only [Category.assoc] using congrArg (fun m => m ≫ τO ≫ τB ≫ e.inv) hV
      _ = i₂ ≫ i₁ ≫ p₀ ≫ τB ≫ e.inv := by
        simpa only [Category.assoc] using congrArg (fun m => i₂ ≫ m ≫ τB ≫ e.inv) hO
      _ = _ := by
        simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
          congrArg (fun m => i₂ ≫ i₁ ≫ m ≫ e.inv) hB
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hc.symm

/-- Compose an actual smooth-site structure with an already verified morphism. -/
def mkOverSmoothSite {S Y : Scheme.{u}} (X : SmoothSite S) (p : Y ⟶ X.left)
    [Smooth p] [IsSeparated p] [QuasiCompact p] : SmoothSite S :=
  mk (p ≫ X.hom)

/-- A commutative square supplies the unique restriction morphism over the base. -/
def restrictionOfSquare {S : Scheme.{u}} {X A T : SmoothSite S}
    (i : X.left ⟶ A.left) (a : A ⟶ T) (b : X ⟶ T)
    (h : i ≫ a.left = b.left) : X ⟶ A :=
  homMk i (by
    rw [← MorphismProperty.Over.w a, ← Category.assoc, h, MorphismProperty.Over.w])

/-- The restriction constructed from a square has the original composite. -/
theorem restrictionOfSquare_comp {S : Scheme.{u}} {X A T : SmoothSite S}
    (i : X.left ⟶ A.left) (a : A ⟶ T) (b : X ⟶ T)
    (h : i ≫ a.left = b.left) : restrictionOfSquare i a b h ≫ a = b := by
  apply MorphismProperty.Over.Hom.ext
  exact h

section NativeRestrictions

variable (R : CommRingCat.{u})
  (O : (Spec R).Opens) [IsAffine O.toScheme]
  (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme]
  {Y : Scheme.{u}} (p : Y ⟶ Spec (.of (Polynomial R)))

local notation "p₁" => sourceNativeCoverMap R O p
local notation "p₂" =>
  sourceNativeCoverMap (O.toScheme.presheaf.obj (Opposite.op ⊤)) V p₁

/-- Both native coefficient restrictions preserve the given étale cover. -/
theorem twiceNativeCoverMap_etale [Etale p] : Etale p₂ := by
  let : Etale p₁ := sourceNativeCoverMap_etale R O p
  exact sourceNativeCoverMap_etale Γ(O.toScheme, ⊤) V p₁

/-- Both actual restricted source schemes remain affine. -/
theorem twiceNativeCoverSource_affine [IsAffine Y] :
    IsAffine (boundaryBaseCoverOpen (boundaryLineProjection Γ(O.toScheme, ⊤)) p₁ ⊤ V).toScheme := by
  let : IsAffine (boundaryBaseCoverOpen (boundaryLineProjection R) p ⊤ O).toScheme :=
    boundaryBaseCoverOpen_affine_instance _ p ⊤ O
  exact boundaryBaseCoverOpen_affine_instance _ p₁ ⊤ V

/-- The two native restrictions compose with any preceding restriction square. -/
theorem twiceNativeCoverRestriction_square
    {A T N D : Scheme.{u}} (a : A ⟶ T) (i : Y ⟶ A)
    (τ : Spec (.of (Polynomial R)) ⟶ N)
    (e : T ≅ N) (f : Spec (.of (Polynomial Γ(V.toScheme, ⊤))) ≅ D)
    (h : p ≫ τ = i ≫ a ≫ e.hom) :
    ((boundaryBaseCoverOpen (boundaryLineProjection Γ(O.toScheme, ⊤)) p₁ ⊤ V).ι ≫
        (boundaryBaseCoverOpen (boundaryLineProjection R) p ⊤ O).ι ≫ i) ≫ a =
      (p₂ ≫ f.hom) ≫ (f.inv ≫
        ((nativeAffineLineRestriction Γ(O.toScheme, ⊤) V.ι ≫
          nativeAffineLineRestriction R O.ι ≫ τ) ≫ e.inv)) :=
  threeRestrictionSquares p₂ p₁ p a
    (boundaryBaseCoverOpen (boundaryLineProjection Γ(O.toScheme, ⊤)) p₁ ⊤ V).ι
    (boundaryBaseCoverOpen (boundaryLineProjection R) p ⊤ O).ι i
    (nativeAffineLineRestriction Γ(O.toScheme, ⊤) V.ι)
    (nativeAffineLineRestriction R O.ι) τ e f
    (sourceNativeCoverMap_coordinate _ V p₁) (sourceNativeCoverMap_coordinate _ O p) h

end NativeRestrictions

/-- Package an affine étale map over the actual target site object. -/
def affineEtaleOverArrow {S Y : Scheme.{u}} [IsAffine Y]
    (X : SmoothSite S) [IsAffine X.left] (p : Y ⟶ X.left) [Etale p] :
    mkOverSmoothSite X p ⟶ X := homMk p rfl

/-- The composite over the actual target object retains the literal scheme map. -/
theorem affineEtaleOverArrow_comp_iso_left {S Y : Scheme.{u}} [IsAffine Y]
    (X : SmoothSite S) [IsAffine X.left] (p : Y ⟶ X.left) [Etale p]
    {D : SmoothSite S} (e : X ≅ D) :
    (affineEtaleOverArrow X p ≫ e.hom).left = p ≫ e.hom.left := rfl

/-- Étaleness of the same composite is proved before specialization. -/
theorem affineEtaleOverArrow_comp_iso_etale {S Y : Scheme.{u}} [IsAffine Y]
    (X : SmoothSite S) [IsAffine X.left] (p : Y ⟶ X.left) [Etale p]
    {D : SmoothSite S} (e : X ≅ D) :
    Etale (affineEtaleOverArrow X p ≫ e.hom).left := by
  change Etale (p ≫ e.hom.left)
  infer_instance

section Original

variable {S : Scheme.{u}} (R₀ : CommRingCat.{u}) {T₀ Y₀ : Scheme.{u}}
  (e₀ : T₀ ≅ Spec (.of (Polynomial R₀))) (q₀ : T₀ ⟶ Spec R₀)
  (hq₀ : e₀.hom ≫ boundaryLineProjection R₀ = q₀)
  (B₀ : (Spec R₀).Opens) [IsAffine B₀.toScheme]
  (g : Y₀ ⟶ T₀) (W₀ : Y₀.Opens) [IsAffine W₀.toScheme]
  (hW₀ : W₀ ≤ g ⁻¹ᵁ (q₀ ⁻¹ᵁ B₀))
  (O₀ : (Spec Γ(B₀.toScheme, ⊤)).Opens) [IsAffine O₀.toScheme]
  (V₀ : (Spec Γ(O₀.toScheme, ⊤)).Opens) [IsAffine V₀.toScheme]
  (t₀ : Spec (.of (Polynomial Γ(V₀.toScheme, ⊤))) ⟶ S)
  [Smooth t₀] [IsSeparated t₀] [QuasiCompact t₀]

local notation "p₀" => originalAffineRefinedNativeMap R₀ e₀ q₀ hq₀ B₀ g W₀ hW₀
local notation "p₁" => sourceNativeCoverMap (B₀.toScheme.presheaf.obj (Opposite.op ⊤)) O₀ p₀
local notation "a₀" => originalAffineRefinedNativePuncture R₀ e₀ q₀ hq₀ B₀ g
local notation "a₁" => sourceNativeCoverMap (B₀.toScheme.presheaf.obj (Opposite.op ⊤)) O₀ a₀

/-- The actual twice restricted original source scheme. -/
def originalAffineRefinedSourceScheme : Scheme.{u} :=
  (boundaryBaseCoverOpen (boundaryLineProjection Γ(O₀.toScheme, ⊤)) p₁ ⊤ V₀).toScheme

/-- The literal native map of the original source after both coefficient restrictions. -/
def originalAffineRefinedSourceMap :
    originalAffineRefinedSourceScheme R₀ e₀ q₀ hq₀ B₀ g W₀ hW₀ O₀ V₀ ⟶
      Spec (.of (Polynomial Γ(V₀.toScheme, ⊤))) :=
  sourceNativeCoverMap Γ(O₀.toScheme, ⊤) V₀ p₁

/-- Affineness of the actual restricted source is proved over the native ring object. -/
theorem originalAffineRefinedSourceScheme_affine :
    IsAffine (originalAffineRefinedSourceScheme R₀ e₀ q₀ hq₀ B₀ g W₀ hW₀ O₀ V₀) :=
  twiceNativeCoverSource_affine Γ(B₀.toScheme, ⊤) O₀ V₀ p₀

omit [IsAffine W₀.toScheme] in
/-- Étaleness of the literal source map is proved before coefficient specialization. -/
theorem originalAffineRefinedSourceMap_etale [Etale g] :
    Etale (originalAffineRefinedSourceMap R₀ e₀ q₀ hq₀ B₀ g W₀ hW₀ O₀ V₀) := by
  let : Etale p₀ := originalAffineRefinedNativeMap_etale R₀ e₀ q₀ hq₀ B₀ g W₀ hW₀
  exact twiceNativeCoverMap_etale Γ(B₀.toScheme, ⊤) O₀ V₀ p₀

/-- The actual twice restricted original puncture scheme. -/
def originalAffineRefinedPunctureScheme : Scheme.{u} :=
  (boundaryBaseCoverOpen (boundaryLineProjection Γ(O₀.toScheme, ⊤)) a₁ ⊤ V₀).toScheme

/-- The literal native map of the original puncture after both coefficient restrictions. -/
def originalAffineRefinedPunctureMap :
    originalAffineRefinedPunctureScheme R₀ e₀ q₀ hq₀ B₀ g O₀ V₀ ⟶
      Spec (.of (Polynomial Γ(V₀.toScheme, ⊤))) :=
  sourceNativeCoverMap Γ(O₀.toScheme, ⊤) V₀ a₁

/-- Affineness of the actual restricted puncture uses the original affine source. -/
theorem originalAffineRefinedPunctureScheme_affine [IsAffine Y₀] :
    IsAffine (originalAffineRefinedPunctureScheme R₀ e₀ q₀ hq₀ B₀ g O₀ V₀) := by
  let : IsAffine ((g ≫ q₀) ⁻¹ᵁ B₀).toScheme :=
    originalAffineRefinedNativePuncture_affine R₀ e₀ q₀ hq₀ B₀ g
  exact twiceNativeCoverSource_affine Γ(B₀.toScheme, ⊤) O₀ V₀ a₀

/-- Étaleness of the literal puncture map follows from the original open immersion. -/
theorem originalAffineRefinedPunctureMap_etale [IsOpenImmersion g] :
    Etale (originalAffineRefinedPunctureMap R₀ e₀ q₀ hq₀ B₀ g O₀ V₀) := by
  let : Etale a₀ := inferInstance
  exact twiceNativeCoverMap_etale Γ(B₀.toScheme, ⊤) O₀ V₀ a₀

/-- The original source restricted over the same final line structure. -/
def originalAffineRefinedSourceSite [Etale g] : SmoothSite S := by
  letI := originalAffineRefinedSourceScheme_affine R₀ e₀ q₀ hq₀ B₀ g W₀ hW₀ O₀ V₀
  letI := originalAffineRefinedSourceMap_etale R₀ e₀ q₀ hq₀ B₀ g W₀ hW₀ O₀ V₀
  exact mk (originalAffineRefinedSourceMap R₀ e₀ q₀ hq₀ B₀ g W₀ hW₀ O₀ V₀ ≫ t₀)

/-- The original puncture restricted over the same final line structure. -/
def originalAffineRefinedPunctureSite [IsAffine Y₀] [IsOpenImmersion g] : SmoothSite S := by
  letI := originalAffineRefinedPunctureScheme_affine R₀ e₀ q₀ hq₀ B₀ g O₀ V₀
  letI := originalAffineRefinedPunctureMap_etale R₀ e₀ q₀ hq₀ B₀ g O₀ V₀
  exact mk (originalAffineRefinedPunctureMap R₀ e₀ q₀ hq₀ B₀ g O₀ V₀ ≫ t₀)

/-- The literal original source restriction map. -/
def originalAffineRefinedSourceRestrictionMap :
    originalAffineRefinedSourceScheme R₀ e₀ q₀ hq₀ B₀ g W₀ hW₀ O₀ V₀ ⟶ Y₀ :=
  (boundaryBaseCoverOpen (boundaryLineProjection Γ(O₀.toScheme, ⊤)) p₁ ⊤ V₀).ι ≫
    (boundaryBaseCoverOpen (boundaryLineProjection Γ(B₀.toScheme, ⊤)) p₀ ⊤ O₀).ι ≫ W₀.ι

/-- The literal original puncture restriction map. -/
def originalAffineRefinedPunctureRestrictionMap :
    originalAffineRefinedPunctureScheme R₀ e₀ q₀ hq₀ B₀ g O₀ V₀ ⟶ Y₀ :=
  (boundaryBaseCoverOpen (boundaryLineProjection Γ(O₀.toScheme, ⊤)) a₁ ⊤ V₀).ι ≫
    (boundaryBaseCoverOpen (boundaryLineProjection Γ(B₀.toScheme, ⊤)) a₀ ⊤ O₀).ι ≫
      ((g ≫ q₀) ⁻¹ᵁ B₀).ι

omit [IsAffine W₀.toScheme] in
/-- The complete source restriction square before specializing the schemes and coefficients. -/
theorem originalAffineRefinedSourceRestriction_square
    {D₀ : Scheme.{u}} (f : Spec (.of (Polynomial Γ(V₀.toScheme, ⊤))) ≅ D₀) :
    originalAffineRefinedSourceRestrictionMap R₀ e₀ q₀ hq₀ B₀ g W₀ hW₀ O₀ V₀ ≫ g =
      (originalAffineRefinedSourceMap R₀ e₀ q₀ hq₀ B₀ g W₀ hW₀ O₀ V₀ ≫ f.hom) ≫
        (f.inv ≫ ((nativeAffineLineRestriction Γ(O₀.toScheme, ⊤) V₀.ι ≫
          nativeAffineLineRestriction Γ(B₀.toScheme, ⊤) O₀.ι ≫
          nativeAffineLineRestriction R₀ B₀.ι) ≫ e₀.inv)) :=
  twiceNativeCoverRestriction_square Γ(B₀.toScheme, ⊤) O₀ V₀ p₀ g W₀.ι
    (nativeAffineLineRestriction R₀ B₀.ι) e₀ f
    (originalAffineRefinedNativeMap_coordinate R₀ e₀ q₀ hq₀ B₀ g W₀ hW₀)

/-- The complete puncture restriction square before specializing the schemes and coefficients. -/
theorem originalAffineRefinedPunctureRestriction_square
    {D₀ : Scheme.{u}} (f : Spec (.of (Polynomial Γ(V₀.toScheme, ⊤))) ≅ D₀) :
    originalAffineRefinedPunctureRestrictionMap R₀ e₀ q₀ hq₀ B₀ g O₀ V₀ ≫ g =
      (originalAffineRefinedPunctureMap R₀ e₀ q₀ hq₀ B₀ g O₀ V₀ ≫ f.hom) ≫
        (f.inv ≫ ((nativeAffineLineRestriction Γ(O₀.toScheme, ⊤) V₀.ι ≫
          nativeAffineLineRestriction Γ(B₀.toScheme, ⊤) O₀.ι ≫
          nativeAffineLineRestriction R₀ B₀.ι) ≫ e₀.inv)) := by
  let τB := nativeAffineLineRestriction R₀ B₀.ι
  have hB : a₀ ≫ τB = ((g ≫ q₀) ⁻¹ᵁ B₀).ι ≫ g ≫ e₀.hom := by
    have hc : (originalAffineRefinedTargetIso R₀ e₀ q₀ hq₀ B₀).hom ≫ τB =
        (q₀ ⁻¹ᵁ B₀).ι ≫ e₀.hom :=
      originalAffineRefinedTargetIso_coordinate R₀ e₀ q₀ hq₀ B₀
    have hr := morphismRestrict_ι g (q₀ ⁻¹ᵁ B₀)
    exact (Category.assoc (g ∣_ (q₀ ⁻¹ᵁ B₀))
        (originalAffineRefinedTargetIso R₀ e₀ q₀ hq₀ B₀).hom τB).trans
      ((congrArg (fun m => (g ∣_ (q₀ ⁻¹ᵁ B₀)) ≫ m) hc).trans
        ((Category.assoc (g ∣_ (q₀ ⁻¹ᵁ B₀)) (q₀ ⁻¹ᵁ B₀).ι e₀.hom).symm.trans
          ((congrArg (fun m => m ≫ e₀.hom) hr).trans
            (Category.assoc ((g ≫ q₀) ⁻¹ᵁ B₀).ι g e₀.hom))))
  exact twiceNativeCoverRestriction_square Γ(B₀.toScheme, ⊤) O₀ V₀ a₀ g
    ((g ≫ q₀) ⁻¹ᵁ B₀).ι (nativeAffineLineRestriction R₀ B₀.ι) e₀ f hB

end Original

end AlgebraicGeometry.Scheme.SmoothSite
