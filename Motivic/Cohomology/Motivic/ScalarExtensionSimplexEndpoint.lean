/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ScalarExtensionEndpointFiber
public import Motivic.Cohomology.Motivic.RawFieldChange
public import Motivic.Cohomology.Motivic.WeightOneBoundaryNorm

/-!
# Literal simplex charts for scalar-restricted endpoint fibers

The zero- and one-simplex source products are identified with their actual
field and polynomial spectra. Both scalar restriction and the original
product cofaces commute with these charts. The induced fiber comparisons
preserve the source inclusion and the whole endpoint scheme.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Motivic.WeightOneBoundaryNorm AlgebraicGeometry.FiniteFlatCurve
open AlgebraicGeometry.ScalarExtensionEndpointFiber
open scoped Polynomial Simplicial

universe u

namespace Motivic.ScalarExtensionSimplexEndpoint

/-- The literal parameter object of the raw singular complex. -/
abbrev source (F : Type u) [Field F] (r : ℕ) : SmoothSite (Spec (.of F)) :=
  SmoothSite.product (SmoothSite.base (Spec (.of F)))
    (AlgebraicSimplex.smoothSiteObj F r)

/-- The original zero-simplex chart, including the base product projection. -/
def sourceChart0 (F : Type u) [Field F] : (source F 0).left ≅ Spec (.of F) :=
  (SmoothSite.forgetScheme (Spec (.of F))).mapIso
    (baseProductIso F (AlgebraicSimplex.smoothSiteObj F 0)) ≪≫ zeroSchemeIso F

/-- The original one-simplex chart, with coordinate the first barycentric coordinate. -/
def sourceChart1 (F : Type u) [Field F] : (source F 1).left ≅ Spec (.of F[X]) :=
  (SmoothSite.forgetScheme (Spec (.of F))).mapIso
    (baseProductIso F (AlgebraicSimplex.smoothSiteObj F 1)) ≪≫ oneSchemeIso F

variable {k E : Type u} [Field k] [Field E] (c : k →+* E)

/-- Scalar restriction on the actual base-times-simplex source. -/
def sourceScalarMap (r : ℕ) : (source E r).left ⟶ (source k r).left :=
  (SmoothSite.baseSimplexFieldChangeIso c ⦋r⦌).inv.left ≫
    pullback.fst (source k r).hom (Spec.map (CommRingCat.ofHom c))

/-- Removing the base factor retains the literal barycentric coefficient map. -/
@[reassoc]
theorem sourceScalarMap_snd (r : ℕ) :
    sourceScalarMap c r ≫ (baseProductIso k (AlgebraicSimplex.smoothSiteObj k r)).hom.left =
      (baseProductIso E (AlgebraicSimplex.smoothSiteObj E r)).hom.left ≫
        Spec.map (CommRingCat.ofHom (AlgebraicSimplex.mapCoefficients c r)) := by
  let φ := Spec.map (CommRingCat.ofHom c)
  have hs : (SmoothSite.baseSimplexFieldChangeIso c ⦋r⦌).inv ≫
      (SmoothSite.baseChange φ).map
        (baseProductIso k (AlgebraicSimplex.smoothSiteObj k r)).hom =
      (baseProductIso E (AlgebraicSimplex.smoothSiteObj E r)).hom ≫
        (AlgebraicSimplex.smoothSiteBaseChangeIso c r).inv := by
    change (SmoothSite.productMap (SmoothSite.baseChangeBaseIso φ).inv
      (AlgebraicSimplex.smoothSiteBaseChangeIso c r).inv ≫
      (SmoothSite.baseChangeProductIso φ (SmoothSite.base (Spec (.of k)))
        (AlgebraicSimplex.smoothSiteObj k r)).inv) ≫
      (SmoothSite.baseChange φ).map (SmoothSite.productSnd _ _) = _
    rw [Category.assoc, SmoothSite.baseChangeProductIso_inv_snd]
    exact SmoothSite.productMap_snd _ _
  have hn := SmoothSite.baseChange_map_fst φ
    (baseProductIso k (AlgebraicSimplex.smoothSiteObj k r)).hom
  calc
    _ = (SmoothSite.baseSimplexFieldChangeIso c ⦋r⦌).inv.left ≫
        ((SmoothSite.baseChange φ).map
          (baseProductIso k (AlgebraicSimplex.smoothSiteObj k r)).hom).left ≫
        pullback.fst (AlgebraicSimplex.smoothSiteObj k r).hom φ := by
      exact (Category.assoc _ _ _).trans
        (congrArg (fun f => (SmoothSite.baseSimplexFieldChangeIso c ⦋r⦌).inv.left ≫ f)
          hn.symm)
    _ = (baseProductIso E (AlgebraicSimplex.smoothSiteObj E r)).hom.left ≫
        (AlgebraicSimplex.smoothSiteBaseChangeIso c r).inv.left ≫
        pullback.fst (AlgebraicSimplex.smoothSiteObj k r).hom φ := by
      simpa only [MorphismProperty.Comma.comp_left, Category.assoc] using
        congrArg (fun f => f.left ≫
          pullback.fst (AlgebraicSimplex.smoothSiteObj k r).hom φ) hs
    _ = _ := congrArg (fun f =>
      (baseProductIso E (AlgebraicSimplex.smoothSiteObj E r)).hom.left ≫ f)
        (AlgebraicSimplex.smoothSiteBaseChangeIso_inv_fst c r)

/-- The polynomial chart commutes with the original coefficient homomorphism. -/
theorem oneCoordinateEquiv_symm_coefficients :
    (AlgebraicSimplex.mapCoefficients c 1).comp (oneCoordinateEquiv k).symm.toRingHom =
      (oneCoordinateEquiv E).symm.toRingHom.comp (Polynomial.mapRingHom c) := by
  apply Polynomial.ringHom_ext
  · intro r
    change AlgebraicSimplex.mapCoefficients c 1
        ((oneCoordinateEquiv k).symm (Polynomial.C r)) =
      (oneCoordinateEquiv E).symm (Polynomial.map c (Polynomial.C r))
    rw [oneCoordinateEquiv_symm_C, Polynomial.map_C,
      oneCoordinateEquiv_symm_C, AlgebraicSimplex.mapCoefficients_constant]
  · change AlgebraicSimplex.mapCoefficients c 1
        ((oneCoordinateEquiv k).symm Polynomial.X) =
      (oneCoordinateEquiv E).symm (Polynomial.map c Polynomial.X)
    rw [oneCoordinateEquiv_symm_X, Polynomial.map_X,
      oneCoordinateEquiv_symm_X, AlgebraicSimplex.mapCoefficients_coordinate]

/-- The underlying one-simplex map is exactly polynomial coefficient change. -/
@[reassoc]
theorem oneSchemeIso_coefficients :
    Spec.map (CommRingCat.ofHom (AlgebraicSimplex.mapCoefficients c 1)) ≫
        (oneSchemeIso k).hom =
      (oneSchemeIso E).hom ≫ coefficientMap c := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact oneCoordinateEquiv_symm_coefficients c

/-- The whole source chart retains the actual polynomial scalar map. -/
@[reassoc]
theorem sourceScalarMap_chart1 :
    sourceScalarMap c 1 ≫ (sourceChart1 k).hom =
      (sourceChart1 E).hom ≫ coefficientMap c := by
  change sourceScalarMap c 1 ≫
      (baseProductIso k (AlgebraicSimplex.smoothSiteObj k 1)).hom.left ≫
      (oneSchemeIso k).hom =
    ((baseProductIso E (AlgebraicSimplex.smoothSiteObj E 1)).hom.left ≫
      (oneSchemeIso E).hom) ≫ coefficientMap c
  rw [sourceScalarMap_snd_assoc, oneSchemeIso_coefficients, Category.assoc]

/-- The zero-simplex chart retains the original field homomorphism. -/
@[reassoc]
theorem sourceScalarMap_chart0 :
    sourceScalarMap c 0 ≫ (sourceChart0 k).hom =
      (sourceChart0 E).hom ≫ Spec.map (CommRingCat.ofHom c) := by
  change sourceScalarMap c 0 ≫
      (baseProductIso k (AlgebraicSimplex.smoothSiteObj k 0)).hom.left ≫
      (zeroSchemeIso k).hom =
    ((baseProductIso E (AlgebraicSimplex.smoothSiteObj E 0)).hom.left ≫
      (zeroSchemeIso E).hom) ≫ Spec.map (CommRingCat.ofHom c)
  rw [sourceScalarMap_snd_assoc, zeroSchemeIso_hom, zeroSchemeIso_hom,
    Category.assoc]
  exact congrArg (fun f =>
    (baseProductIso E (AlgebraicSimplex.smoothSiteObj E 0)).hom.left ≫ f)
      (AlgebraicSimplex.mapCoefficients_isPullback c 0).w

/-- The actual product coface on the parameter source. -/
def faceMap (F : Type u) [Field F] (i : Fin 2) :
    (source F 0).left ⟶ (source F 1).left :=
  (SmoothSite.productMap (𝟙 (SmoothSite.base (Spec (.of F))))
    ((AlgebraicSimplex.cosimplicialSmoothSite F).δ i)).left

/-- Each normalized simplex face is its specified evaluation point. -/
theorem facePoint_chart (F : Type u) [Field F] (i : Fin 2) :
    (facePoint F i).left ≫ (oneSchemeIso F).hom = endpoint (i.val : F) := by
  fin_cases i
  · change (facePoint F 0).left ≫ (oneSchemeIso F).hom = endpoint ((0 : ℕ) : F)
    rw [Nat.cast_zero, facePoint_zero]
    exact evaluationPoint_oneSchemeIso F 0
  · change (facePoint F 1).left ≫ (oneSchemeIso F).hom = endpoint ((1 : ℕ) : F)
    rw [Nat.cast_one, facePoint_one]
    exact evaluationPoint_oneSchemeIso F 1

/-- The actual simplex coface is its literal endpoint in the affine chart. -/
@[reassoc]
theorem simplexFace_chart (F : Type u) [Field F] (i : Fin 2) :
    ((AlgebraicSimplex.cosimplicialSmoothSite F).δ i).left ≫ (oneSchemeIso F).hom =
      (zeroSchemeIso F).hom ≫ endpoint (i.val : F) := by
  apply (cancel_epi (zeroSchemeIso F).inv).mp
  rw [Iso.inv_hom_id_assoc]
  have h := facePoint_chart F i
  change ((zeroSchemeIso F).inv ≫
    ((AlgebraicSimplex.cosimplicialSmoothSite F).δ i).left) ≫
      (oneSchemeIso F).hom = endpoint (i.val : F) at h
  exact (Category.assoc _ _ _).symm.trans h

/-- Each original product coface is the literal endpoint in the source charts. -/
@[reassoc]
theorem faceMap_chart (F : Type u) [Field F] (i : Fin 2) :
    faceMap F i ≫ (sourceChart1 F).hom =
      (sourceChart0 F).hom ≫ endpoint (i.val : F) := by
  have hp := congrArg (fun f => f.left)
    (SmoothSite.productMap_snd (𝟙 (SmoothSite.base (Spec (.of F))))
      ((AlgebraicSimplex.cosimplicialSmoothSite F).δ i))
  change faceMap F i ≫
      (baseProductIso F (AlgebraicSimplex.smoothSiteObj F 1)).hom.left ≫
      (oneSchemeIso F).hom =
    ((baseProductIso F (AlgebraicSimplex.smoothSiteObj F 0)).hom.left ≫
      (zeroSchemeIso F).hom) ≫ endpoint (i.val : F)
  change faceMap F i ≫
      (baseProductIso F (AlgebraicSimplex.smoothSiteObj F 1)).hom.left =
    (baseProductIso F (AlgebraicSimplex.smoothSiteObj F 0)).hom.left ≫
      ((AlgebraicSimplex.cosimplicialSmoothSite F).δ i).left at hp
  rw [← Category.assoc, hp, Category.assoc, simplexFace_chart, Category.assoc]

variable (F : Type u) [Field F] {C : Scheme.{u}}
  (f : C ⟶ (source F 1).left) (i : Fin 2)

/-- The actual product-coface fiber is Cartesian over the polynomial chart. -/
theorem chartFiber_isPullback :
    IsPullback (pullback.fst (faceMap F i) f ≫ (sourceChart0 F).hom)
      (pullback.snd (faceMap F i) f) (endpoint (i.val : F))
      (f ≫ (sourceChart1 F).hom) := by
  exact (IsPullback.of_hasPullback (faceMap F i) f).of_iso
    (Iso.refl _) (sourceChart0 F) (Iso.refl _) (sourceChart1 F)
    (by simp) (by simp) (faceMap_chart F i) (by simp)

/-- The full original product-coface fiber, with no reduction, in its endpoint chart. -/
def chartFiberIso : pullback (faceMap F i) f ≅
    fiber (f ≫ (sourceChart1 F).hom) (i.val : F) :=
  (chartFiber_isPullback F f i).isoPullback

/-- The endpoint chart preserves the original source inclusion. -/
@[reassoc (attr := simp)]
theorem chartFiberIso_hom_inclusion :
    (chartFiberIso F f i).hom ≫
        fiberInclusion (f ≫ (sourceChart1 F).hom) (i.val : F) =
      pullback.snd (faceMap F i) f :=
  (chartFiber_isPullback F f i).isoPullback_hom_snd

/-- The endpoint chart preserves the exact point projection. -/
@[reassoc (attr := simp)]
theorem chartFiberIso_hom_scalar :
    (chartFiberIso F f i).hom ≫
        pullback.fst (endpoint (i.val : F)) (f ≫ (sourceChart1 F).hom) =
      pullback.fst (faceMap F i) f ≫ (sourceChart0 F).hom :=
  (chartFiber_isPullback F f i).isoPullback_hom_fst

end Motivic.ScalarExtensionSimplexEndpoint
