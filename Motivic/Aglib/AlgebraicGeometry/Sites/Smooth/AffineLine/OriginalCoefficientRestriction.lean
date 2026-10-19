/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.CylinderNativeCoordinates
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.Diagrams.OriginalAffineRefinement
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Source.NativeParameter
/-! # The final common coefficient open inside the original smooth base

The three opens are precisely the initial affine refinement, the normalization
restriction and the common section restriction. The final scheme is the last
open itself, not an arbitrarily chosen dense open in the total affine line.

Intended upstream module:
`Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.OriginalCoefficientRestriction`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Nisnevich.NativeCoefficientCover`.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Hom RelativeProjectiveLine
universe u
namespace AlgebraicGeometry.Scheme

/-- Three polynomial coefficient restrictions compose in the original order. -/
theorem polynomialSpecMap_comp_three
    {R S T Q : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing Q]
    (f : R →+* S) (g : S →+* T) (h : T →+* Q) :
    Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom h)) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom g)) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)) =
        Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (h.comp (g.comp f)))) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  change (Polynomial.mapRingHom h).comp
    ((Polynomial.mapRingHom g).comp (Polynomial.mapRingHom f)) = _
  rw [Polynomial.mapRingHom_comp g f, Polynomial.mapRingHom_comp h (g.comp f)]
  rfl

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.SmoothSite
variable {k : Type u} [Field k]
  (U : SmoothSite (Spec (.of k))) [IsAffine U.left]
  (B : (Spec Γ(U.left, ⊤)).Opens) [IsAffine B.toScheme]
  (O : (Spec Γ(B.toScheme, ⊤)).Opens) [IsAffine O.toScheme]
  (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme]

/-- The literal composite of the three retained coefficient-open inclusions. -/
def originalCoefficientRestriction : V.toScheme ⟶ U.left :=
  V.ι ≫ O.toScheme.isoSpec.inv ≫ O.ι ≫ B.toScheme.isoSpec.inv ≫ B.ι ≫ U.left.isoSpec.inv

instance originalCoefficientRestriction_open :
    IsOpenImmersion (originalCoefficientRestriction U B O V) := by
  unfold originalCoefficientRestriction
  infer_instance

/-- The last common coefficient open, with its original structure map to the field. -/
def originalCoefficientSite : SmoothSite (Spec (.of k)) :=
  mk (originalCoefficientRestriction U B O V ≫ U.hom)

/-- Inclusion into the original base, not into its affine-line cylinder. -/
def originalCoefficientInclusion : originalCoefficientSite U B O V ⟶ U :=
  homMk (originalCoefficientRestriction U B O V) rfl

instance originalCoefficientInclusion_open :
    IsOpenImmersion (originalCoefficientInclusion U B O V).left :=
  originalCoefficientRestriction_open U B O V

instance originalCoefficientSite_affine :
    IsAffine (originalCoefficientSite U B O V).left := ‹IsAffine V.toScheme›

/-- The point already retained by the common section choice proves nonemptiness. -/
theorem originalCoefficientSite_nonempty (x : Spec Γ(O.toScheme, ⊤)) (hx : x ∈ V) :
    Nonempty (originalCoefficientSite U B O V).left := ⟨⟨x, hx⟩⟩

/-- The native coefficient composite is the actual restriction of global sections
along the final original-base inclusion. -/
theorem originalCoefficientInclusion_appTop :
    (Scheme.ConstantCurve.affineSourceCoefficientMap Γ(O.toScheme, ⊤) V.ι).comp
      ((Scheme.ConstantCurve.affineSourceCoefficientMap Γ(B.toScheme, ⊤) O.ι).comp
        (Scheme.ConstantCurve.affineSourceCoefficientMap Γ(U.left, ⊤) B.ι)) =
      (originalCoefficientInclusion U B O V).left.appTop.hom := by
  have h : CommRingCat.ofHom
      ((Scheme.ConstantCurve.affineSourceCoefficientMap Γ(O.toScheme, ⊤) V.ι).comp
        ((Scheme.ConstantCurve.affineSourceCoefficientMap Γ(B.toScheme, ⊤) O.ι).comp
          (Scheme.ConstantCurve.affineSourceCoefficientMap Γ(U.left, ⊤) B.ι))) =
      (originalCoefficientInclusion U B O V).left.appTop := by
    apply Spec.map_injective
    apply (cancel_mono U.left.isoSpec.inv).mp
    change Spec.map
      (CommRingCat.ofHom (Scheme.ConstantCurve.affineSourceCoefficientMap Γ(U.left, ⊤) B.ι) ≫
        CommRingCat.ofHom (Scheme.ConstantCurve.affineSourceCoefficientMap Γ(B.toScheme, ⊤) O.ι) ≫
        CommRingCat.ofHom (Scheme.ConstantCurve.affineSourceCoefficientMap Γ(O.toScheme, ⊤) V.ι)) ≫
        U.left.isoSpec.inv = _
    simp only [Spec.map_comp, Scheme.ConstantCurve.affineSourceCoefficientMap,
      Scheme.ConstantCurve.map_coefficientMap, Category.assoc,
      Scheme.isoSpec_inv_naturality]
    rfl
  exact congrArg (fun f => f.hom) h

variable {T : SmoothSite (Spec (.of k))} (e : T ≅ a1Cylinder (.of k) U)

/-- Restrict the whole cylinder over the same last coefficient open. -/
def originalCoefficientCylinderMap : a1Cylinder (.of k) (originalCoefficientSite U B O V) ⟶ T :=
  a1Map (.of k) (originalCoefficientInclusion U B O V) ≫ e.inv

@[reassoc]
theorem originalCoefficientCylinderMap_comp :
    originalCoefficientCylinderMap U B O V e ≫ e.hom =
      a1Map (.of k) (originalCoefficientInclusion U B O V) := by
  simp only [originalCoefficientCylinderMap, Category.assoc, e.inv_hom_id, Category.comp_id]

end AlgebraicGeometry.Scheme.SmoothSite

namespace AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
open AlgebraicGeometry.Scheme.PolynomialLaurent AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
attribute [local instance] sectionsAlgebra
variable {k : Type u} [Field k]
  {X Y : SmoothSite (Spec (.of k))} [IsAffine X.left] [IsAffine Y.left]

/-- The whole-cylinder coordinates preserve the actual global-section restriction. -/
@[reassoc]
theorem affineLineIso_naturality (f : X ⟶ Y) :
    lineMap (sectionsMap f) ≫ (affineLineIso Y).hom =
      (affineLineIso X).hom ≫ SmoothSite.a1Map (.of k) f := by
  simp only [affineLineIso, Iso.trans_hom, cylinderIso, ← Category.assoc,
    lineCylinderIso_naturality]
  rw [Category.assoc, ← SmoothSite.a1Map_comp, affineIso_naturality,
    SmoothSite.a1Map_comp, ← Category.assoc]

variable (U : SmoothSite (Spec (.of k))) [IsAffine U.left]
  (B : (Spec Γ(U.left, ⊤)).Opens) [IsAffine B.toScheme]
  (O : (Spec Γ(B.toScheme, ⊤)).Opens) [IsAffine O.toScheme]
  (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme]

/-- The three native line maps are the polynomial map of the actual base inclusion. -/
theorem originalCoefficientLineMap_eq :
    Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
      (Scheme.ConstantCurve.affineSourceCoefficientMap Γ(O.toScheme, ⊤) V.ι))) ≫
    Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
      (Scheme.ConstantCurve.affineSourceCoefficientMap Γ(B.toScheme, ⊤) O.ι))) ≫
    Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
      (Scheme.ConstantCurve.affineSourceCoefficientMap Γ(U.left, ⊤) B.ι))) =
    (lineMap (sectionsMap (SmoothSite.originalCoefficientInclusion U B O V))).left := by
  let f₀ := Scheme.ConstantCurve.affineSourceCoefficientMap Γ(U.left, ⊤) B.ι
  let f₁ := Scheme.ConstantCurve.affineSourceCoefficientMap Γ(B.toScheme, ⊤) O.ι
  let f₂ := Scheme.ConstantCurve.affineSourceCoefficientMap Γ(O.toScheme, ⊤) V.ι
  exact (Scheme.polynomialSpecMap_comp_three f₀ f₁ f₂).trans
    (congrArg (fun f : Γ(U.left, ⊤) →+* Γ(V.toScheme, ⊤) =>
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)))
        (SmoothSite.originalCoefficientInclusion_appTop U B O V))

/-- The native line restriction is exactly the original whole-cylinder map.
Together with `originalCoefficientLineMap_eq`, this identifies the literal three
coefficient restrictions, not an unrelated cylinder over an isomorphic base. -/
theorem originalCoefficientCylinderMap_native
    {T : SmoothSite (Spec (.of k))} (e : T ≅ SmoothSite.a1Cylinder (.of k) U) :
    (lineMap (sectionsMap (SmoothSite.originalCoefficientInclusion U B O V))).left ≫
        (originalCylinderNativeIso U T e).inv =
      (affineLineIso (SmoothSite.originalCoefficientSite U B O V)).hom.left ≫
        (SmoothSite.originalCoefficientCylinderMap U B O V e).left := by
  have h := congrArg (fun f => f.left)
    (affineLineIso_naturality (SmoothSite.originalCoefficientInclusion U B O V))
  change (lineMap (sectionsMap (SmoothSite.originalCoefficientInclusion U B O V))).left ≫
      (affineLineIso U).hom.left =
    (affineLineIso (SmoothSite.originalCoefficientSite U B O V)).hom.left ≫
      (SmoothSite.a1Map (.of k) (SmoothSite.originalCoefficientInclusion U B O V)).left at h
  change (lineMap (sectionsMap (SmoothSite.originalCoefficientInclusion U B O V))).left ≫
      ((affineLineIso U).hom.left ≫ e.inv.left) =
    (affineLineIso (SmoothSite.originalCoefficientSite U B O V)).hom.left ≫
      ((SmoothSite.a1Map (.of k) (SmoothSite.originalCoefficientInclusion U B O V)).left ≫
        e.inv.left)
  rw [← Category.assoc, h, Category.assoc]

/-- The literal three native restrictions recover the original whole-cylinder map. -/
theorem originalCoefficientCylinderMap_native_three
    {T : SmoothSite (Spec (.of k))} (e : T ≅ SmoothSite.a1Cylinder (.of k) U) :
    Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
      (Scheme.ConstantCurve.affineSourceCoefficientMap Γ(O.toScheme, ⊤) V.ι))) ≫
    Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
      (Scheme.ConstantCurve.affineSourceCoefficientMap Γ(B.toScheme, ⊤) O.ι))) ≫
    Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
      (Scheme.ConstantCurve.affineSourceCoefficientMap Γ(U.left, ⊤) B.ι))) ≫
        (originalCylinderNativeIso U T e).inv =
      (affineLineIso (SmoothSite.originalCoefficientSite U B O V)).hom.left ≫
        (SmoothSite.originalCoefficientCylinderMap U B O V e).left := by
  have h := congrArg (fun f => f ≫ (originalCylinderNativeIso U T e).inv)
    (originalCoefficientLineMap_eq U B O V)
  have h' := h.trans (originalCoefficientCylinderMap_native U B O V e)
  simpa only [Category.assoc] using h'

end AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates

namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]
  (O : (Spec (.of R)).Opens) [IsAffine O.toScheme]
  (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme]
  {Y : Scheme.{u}} (p : Y ⟶ Spec (.of (Polynomial R)))

/-- Both native restrictions preserve the original source map, with no new source. -/
theorem sourceNativeCoverMap_twice_coordinate :
    sourceNativeCoverMap Γ(O.toScheme, ⊤) V (sourceNativeCoverMap R O p) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
        (Scheme.ConstantCurve.affineSourceCoefficientMap Γ(O.toScheme, ⊤) V.ι))) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
        (Scheme.ConstantCurve.affineSourceCoefficientMap R O.ι))) =
    (boundaryBaseCoverOpen (boundaryLineProjection Γ(O.toScheme, ⊤))
      (sourceNativeCoverMap R O p) ⊤ V).ι ≫
        (boundaryBaseCoverOpen (boundaryLineProjection R) p ⊤ O).ι ≫ p := by
  rw [← Category.assoc, sourceNativeCoverMap_coordinate, Category.assoc,
    sourceNativeCoverMap_coordinate]

end AlgebraicGeometry.RelativeProjectiveLine

namespace AlgebraicGeometry.Scheme
variable (R : Type u) [CommRing R] {T Y : Scheme.{u}}
  (e : T ≅ Spec (.of (Polynomial R))) (q : T ⟶ Spec (.of R))
  (hq : e.hom ≫ boundaryLineProjection R = q)
  (B : (Spec (.of R)).Opens) [IsAffine B.toScheme]
  (p : Y ⟶ T) (W : Y.Opens) (hW : W ≤ p ⁻¹ᵁ (q ⁻¹ᵁ B))
  (O : (Spec Γ(B.toScheme, ⊤)).Opens) [IsAffine O.toScheme]
  (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme]

local notation "p₀" => originalAffineRefinedNativeMap R e q hq B p W hW
local notation "p₁" => sourceNativeCoverMap (B.toScheme.presheaf.obj (Opposite.op ⊤)) O p₀

/-- The final native affine source is the same original affine open W restricted
on the two retained coefficient opens, with its original map to T. -/
theorem originalAffineRefinedNativeMap_twice_coordinate :
    sourceNativeCoverMap Γ(O.toScheme, ⊤) V p₁ ≫
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
        (ConstantCurve.affineSourceCoefficientMap Γ(O.toScheme, ⊤) V.ι))) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
        (ConstantCurve.affineSourceCoefficientMap Γ(B.toScheme, ⊤) O.ι))) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
        (ConstantCurve.affineSourceCoefficientMap R B.ι))) ≫ e.inv =
    (boundaryBaseCoverOpen (boundaryLineProjection Γ(O.toScheme, ⊤)) p₁ ⊤ V).ι ≫
      (boundaryBaseCoverOpen (boundaryLineProjection Γ(B.toScheme, ⊤)) p₀ ⊤ O).ι ≫
        W.ι ≫ p := by
  let m := Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
    (ConstantCurve.affineSourceCoefficientMap R B.ι)))
  let i₁ := (boundaryBaseCoverOpen (boundaryLineProjection Γ(B.toScheme, ⊤)) p₀ ⊤ O).ι
  let i₂ := (boundaryBaseCoverOpen (boundaryLineProjection Γ(O.toScheme, ⊤)) p₁ ⊤ V).ι
  have h₁ := sourceNativeCoverMap_twice_coordinate Γ(B.toScheme, ⊤) O V p₀
  have h₂ := originalAffineRefinedNativeMap_coordinate R e q hq B p W hW
  have h₁' := congrArg (fun f => f ≫ m ≫ e.inv) h₁
  have h₂' := congrArg (fun f => i₂ ≫ i₁ ≫ f ≫ e.inv) h₂
  have h₂'' : i₂ ≫ i₁ ≫ p₀ ≫ m ≫ e.inv = i₂ ≫ i₁ ≫ W.ι ≫ p := by
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h₂'
  calc
    _ = i₂ ≫ i₁ ≫ p₀ ≫ m ≫ e.inv := by
      simpa only [Category.assoc] using h₁'
    _ = _ := h₂''

end AlgebraicGeometry.Scheme
