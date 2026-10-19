/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.OriginalPresentationCombinedCorrection
public import Motivic.Cohomology.A1.PresheafBoundaryPolynomialOverlap
public import Motivic.Cohomology.A1.PresheafBoundaryGeometricRefinement
public import Motivic.Cohomology.A1.RestrictionDifferenceIsoAmbient
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleSmoothNeighborhood

/-! # The constructed polynomial corrections give the original boundary image sieve

The original generator is restricted through the original overlap, and the two
actual corrections are transported only through their canonical geometric
isomorphisms. The resulting image arrow is the prescribed original open arrow.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.RelativeCurve
open Motivic.SmoothSiteAffineCoordinates

universe u

namespace Motivic.FiniteEtaleSite.OriginalPresheaf

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
  (W : FiniteEtaleSite (SmoothSite.a1Cylinder (.of k) X).left)
  (R : Type u) [CommRing R] [Algebra k R] [Algebra.Smooth k R]
  {Y : SmoothSite (Spec (.of k))} [IsAffine Y.left]
  (p : Y ⟶ RelativePolynomialOpenSpans.lineSite (k := k) (R := R)) [Etale p.left]
  {Z : Scheme.{u}} (z : Z ⟶ Spec (.of (Polynomial R))) (s : Z ⟶ Y.left)
  (w : Spec (.of R))
  (presentation : OriginalEtalePresentation k
    (boundaryLineProjection R ≫ AffineTorusPolynomialPresentation.baseMap k R) p.left
    (Scheme.Opens.ι (X := Spec (.of (Polynomial R)))
      (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R))) z s
    (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) w))
  (s₀ : Spec (.of R) ⟶ Y.left)
  (hs₀ : s₀ ≫ p.left = Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))))
  (v₀ : AffineTorusPolynomialPresentation.affineSite k R ⟶
    (toSmoothSite X).obj ((baseChange (SmoothSite.a1Section (.of k) X 0).left).obj W))
  [IsOpenImmersion v₀.left]
  (e₀ : Y ⟶ (toSmoothSite (SmoothSite.a1Cylinder (.of k) X)).obj W)
  (hp : p ≫ (lineCylinderIso (k := k) (R := R)).hom ≫
      SmoothSite.a1Map (.of k)
        (v₀ ≫ toBase X ((baseChange (SmoothSite.a1Section (.of k) X 0).left).obj W)) =
      e₀ ≫ toBase (SmoothSite.a1Cylinder (.of k) X) W)
  (hmark : s₀ ≫ e₀.left = v₀.left ≫
    pullback.fst W.hom (SmoothSite.a1Section (.of k) X 0).left)

include hP presentation hs₀ hp hmark in
/-- Every original punctured section has an actual open-base image-sieve witness
through the two constructed corrections and the unchanged whole-zero marking. -/
theorem exists_polynomial_boundary_image_neighborhood
    (d : ((PresheafWithTransfers.toPresheaf k).obj P).obj (op
      ((toSmoothSite (SmoothSite.torusCylinder (.of k) X)).obj
        ((baseChange (SmoothSite.contractionOpen (.of k) X).left).obj W)))) :
    ∃ (V : FiniteEtaleSite X.left)
      (v : V ⟶ (baseChange (SmoothSite.a1Section (.of k) X 0).left).obj W),
      IsOpenImmersion v.left ∧ v₀.left w ∈ Set.range v.left ∧
      Presheaf.imageSieve (contractionToBoundary X P).hom
        ((presheafBoundaryGenerator ((PresheafWithTransfers.toPresheaf k).obj P)
          (SmoothSite.contractionOpen (.of k) X)
          (SmoothSite.a1Section (.of k) X 0)).app (op W) d) v := by
  obtain ⟨B, v, hv, hw, E, η, q, ζ, hq, hbase, hζq, hζη,
    O, α, β, φ, H, hφ, hL⟩ :=
    OriginalEtalePresentation.exists_original_torus_neighborhood_lifting
      R p z s w presentation P hP s₀ hs₀
  let : IsOpenImmersion v.left := hv
  let : Etale q.left := hq
  let W₀ := (baseChange (SmoothSite.a1Section (.of k) X 0).left).obj W
  let fB := (v ≫ v₀) ≫ toBase X W₀
  let : Etale fB.left := by
    change Etale ((v.left ≫ v₀.left) ≫ W₀.hom)
    infer_instance
  let V := ofSmoothMap X B fB
  let eB := ofSmoothMapIso X B fB
  let eL := cylinderIso eB
  let eT := (SmoothSite.parameterProduct (SmoothSite.torus (.of k))).mapIso eB
  let v' : V ⟶ W₀ := MorphismProperty.Over.homMk (v.left ≫ v₀.left) rfl
  let q' := q ≫ eL.hom
  let η' := η ≫ e₀
  let : IsIso eL.hom.left :=
    inferInstanceAs (IsIso ((SmoothSite.forgetScheme (Spec (.of k))).mapIso eL).hom)
  let : Etale q'.left := by
    change Etale (q.left ≫ eL.hom.left)
    infer_instance
  have hqbase : η' ≫ toBase (SmoothSite.a1Cylinder (.of k) X) W =
      q' ≫ SmoothSite.a1Map (.of k) (toBase X V) := by
    calc
      _ = η ≫ p ≫ (lineCylinderIso (k := k) (R := R)).hom ≫
          SmoothSite.a1Map (.of k) (v₀ ≫ toBase X W₀) := by
        simpa only [η', Category.assoc] using congrArg (fun h => η ≫ h) hp.symm
      _ = q ≫ SmoothSite.a1Map (.of k) v ≫
          SmoothSite.a1Map (.of k) (v₀ ≫ toBase X W₀) := by
        simpa only [Category.assoc] using congrArg
          (fun h => h ≫ SmoothSite.a1Map (.of k) (v₀ ≫ toBase X W₀)) hbase
      _ = q ≫ SmoothSite.a1Map (.of k) fB := by
        rw [← SmoothSite.a1Map_comp]
        simp only [fB, Category.assoc]
      _ = q' ≫ SmoothSite.a1Map (.of k) (toBase X V) := by
        change _ = (q ≫ SmoothSite.a1Map (.of k) eB.hom) ≫
          SmoothSite.a1Map (.of k) (toBase X V)
        rw [Category.assoc, ← SmoothSite.a1Map_comp, ofSmoothMapIso_toBase]
  have he : η'.left ≫ W.hom = q'.left ≫ ((cylinderNeighborhood X).obj V).hom :=
    congrArg (fun f => f.left) hqbase
  let W' := geometricRefinementNeighborhood X V E q'
  let eE := geometricRefinementIso X V E q'
  let f := geometricRefinementToOriginal X V E q' η' he
  let b := geometricRefinementToCylinder X V E q'
  let α' := α ≫ eE.hom
  let β' := β ≫ eT.hom
  let τ := polynomialOverlapToPunctured X (v₀ ≫ toBase X W₀) W p e₀ hp
  let φ' := φ ≫ τ
  have hz : ζ ≫ b.left =
      (SmoothSite.a1Section (.of k) ((toSmoothSite X).obj V) 0).left := by
    change ζ ≫ (q.left ≫ eL.hom.left) = _
    rw [← Category.assoc, hζq]
    have h := congrArg (fun f => f.left)
      (SmoothSite.a1Section_naturality (.of k) eB.hom 0)
    change (SmoothSite.a1Section (.of k) B 0).left ≫ eL.hom.left =
      𝟙 B.left ≫ (SmoothSite.a1Section (.of k) ((toSmoothSite X).obj V) 0).left at h
    exact h.trans (Category.id_comp _)
  have hzη : ζ ≫ η'.left = v'.left ≫
      pullback.fst W.hom (SmoothSite.a1Section (.of k) X 0).left := by
    change ζ ≫ (η.left ≫ e₀.left) = (v.left ≫ v₀.left) ≫ _
    rw [← Category.assoc, hζη, Category.assoc, hmark, ← Category.assoc]
  have H' : IsPullback β'.left α'.left
      (SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj V)).left b.left := by
    apply H.of_iso (Iso.refl O.left)
      ((SmoothSite.forgetScheme (Spec (.of k))).mapIso eT)
      ((SmoothSite.forgetScheme (Spec (.of k))).mapIso eE)
      ((SmoothSite.forgetScheme (Spec (.of k))).mapIso eL)
    · change β.left ≫ eT.hom.left = 𝟙 O.left ≫ (β.left ≫ eT.hom.left)
      rw [Category.id_comp]
    · change α.left ≫ eE.hom.left = 𝟙 O.left ≫ (α.left ≫ eE.hom.left)
      rw [Category.id_comp]
    · exact congrArg (fun f => f.left)
        (SmoothSite.contractionOpen_naturality (.of k) eB.hom)
    · change q.left ≫ eL.hom.left = 𝟙 E.left ≫ (q.left ≫ eL.hom.left)
      rw [Category.id_comp]
  have hφ₁ : φ'.left ≫ pullback.fst W.hom
      (SmoothSite.contractionOpen (.of k) X).left = α'.left ≫ f.left := by
    have hφleft := congrArg (fun f => f.left) hφ
    change (φ.left ≫ τ.left) ≫ pullback.fst W.hom
      (SmoothSite.contractionOpen (.of k) X).left = (α.left ≫ 𝟙 E.left) ≫ η'.left
    rw [Category.comp_id, Category.assoc, polynomialOverlapToPunctured_fst,
      ← Category.assoc, hφleft]
    simp only [η', Category.assoc]
  have hφ₂ : φ'.left ≫ pullback.snd W.hom
      (SmoothSite.contractionOpen (.of k) X).left = β'.left ≫
        (SmoothSite.productMap (toBase X V) (𝟙 (SmoothSite.torus (.of k)))).left := by
    apply (cancel_mono (SmoothSite.contractionOpen (.of k) X).left).mp
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hφ₁]
    have hf : f.left ≫ W.hom = b.left ≫ ((cylinderNeighborhood X).obj V).hom := he
    rw [Category.assoc, hf, ← Category.assoc, ← H'.w, Category.assoc]
    exact congrArg (fun h => β'.left ≫ h) (contractionOpen_base_isPullback X V).w
  have hL' := PresheafWithTransfers.HasRestrictionDifferenceLifting.restrict P hL τ
  have hL'' := PresheafWithTransfers.HasRestrictionDifferenceLifting.iso_right P hL' eT
  have hL''' := PresheafWithTransfers.HasRestrictionDifferenceLifting.iso_ambient P hL'' eE
  obtain ⟨a, c, hac⟩ := hL''' d
  have hi := imageSieve_of_geometric_difference X V b ζ hz P O α' β' H' f φ'
    hφ₁ hφ₂ d a c hac
  have hzv := geometricRefinement_zero_arrow X V E q' η' he ζ hz v' hzη
  rw [hzv] at hi
  refine ⟨V, v', ?_, ?_, hi⟩
  · change IsOpenImmersion (v.left ≫ v₀.left)
    infer_instance
  · obtain ⟨y, hy⟩ := hw
    refine ⟨y, ?_⟩
    change v₀.left (v.left y) = v₀.left w
    rw [hy]

end Motivic.FiniteEtaleSite.OriginalPresheaf
