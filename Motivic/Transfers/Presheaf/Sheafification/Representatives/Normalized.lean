/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.Sheafification.Representatives.Affine
public import Motivic.Transfers.Presheaf.Actions.Norm.RefinedNormalization


/-! # Bind original representatives to their single actual normalization

No source/target sections or frames are chosen here. The original representatives,
full marked scheme and restriction equations remain in the output alongside the
single normalized boundary construction on their actual affine refinement.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.PresheafWithTransfers
variable {k : Type u} [Field k]

/-- Refine the actual original étale representative to an affine open containing
its whole marked fiber, after a nonzero coefficient restriction. -/
theorem exists_normalized_distinguished_nisnevichImage_representatives
    (P : PresheafWithTransfers.{u + 1} k)
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left]
    (g : ((nisnevichSheafify k).obj P).obj.sections
      (Cor.mk (SmoothSite.a1Cylinder (.of k) X))) :
    ∃ (U : SmoothSite (Spec (.of k))) (j : U ⟶ X),
      IsOpenImmersion j.left ∧ Nonempty U.left ∧
      ∃ hUa : IsAffine U.left,
      letI : IsAffine U.left := hUa
      ∃ (T : SmoothSite (Spec (.of k))) (e : T ≅ SmoothSite.a1Cylinder (.of k) U)
        (A V : SmoothSite (Spec (.of k))) (i : A ⟶ T) (v : V ⟶ T),
        IsAffine A.left ∧
        ∃ hi : IsOpenImmersion i.left,
        letI : IsOpenImmersion i.left := hi
        Etale v.left ∧
        Sieve.ofTwoArrows i v ∈ SmoothSite.nisnevichTopology (Spec (.of k)) T ∧
        ∃ (Z : Scheme.{u}) (z : Z ⟶ T.left), IsClosedImmersion z ∧
          IsFinite (z ≫ e.hom.left ≫ (SmoothSite.a1Projection (.of k) U).left) ∧
          Set.range z = (Set.range i.left)ᶜ ∧
          ∃ hz : IsIso (pullback.snd v.left z),
          letI : IsIso (pullback.snd v.left z) := hz
          ∃ (B : SmoothSite (Spec (.of k))) (bA : B ⟶ A) (bV : B ⟶ V),
            IsPullback bA bV i v ∧
            ∃ (sA : (nisnevichImage P).sections (Cor.mk A))
              (sV : (nisnevichImage P).sections (Cor.mk V)),
              (nisnevichImage P).transfer ((Cor.graphFunctor k).map bA) sA =
                (nisnevichImage P).transfer ((Cor.graphFunctor k).map bV) sV ∧
              (nisnevichImageι P).hom.app (op (Cor.mk A)) sA =
                ((nisnevichSheafify k).obj P).obj.transfer
                  ((Cor.graphFunctor k).map (i ≫ e.hom ≫ SmoothSite.a1Map (.of k) j)) g ∧
              (nisnevichImageι P).hom.app (op (Cor.mk V)) sV =
                ((nisnevichSheafify k).obj P).obj.transfer
                  ((Cor.graphFunctor k).map (v ≫ e.hom ≫ SmoothSite.a1Map (.of k) j)) g ∧
              let q := e.hom.left ≫ (SmoothSite.a1Projection (.of k) U).left ≫
                U.left.isoSpec.hom
              let s := inv (pullback.snd v.left z) ≫ pullback.fst v.left z
              let gT := ((nisnevichSheafify k).obj P).obj.transfer
                ((Cor.graphFunctor k).map (e.hom ≫ SmoothSite.a1Map (.of k) j)) g
              ∃ (r : Γ(U.left, ⊤)), r ≠ 0 ∧ ∃ (W : V.left.Opens) (hWa : IsAffineOpen W)
                (hW : W ≤ v.left ⁻¹ᵁ (q ⁻¹ᵁ PrimeSpectrum.basicOpen r)),
                ∃ t : ((z ≫ q) ⁻¹ᵁ PrimeSpectrum.basicOpen r).toScheme ⟶ W.toScheme,
                  t ≫ W.ι = ((z ≫ q) ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι ≫ s ∧
                  IsPullback t (𝟙 _)
                    (v.left.resLE (q ⁻¹ᵁ PrimeSpectrum.basicOpen r) W hW)
                    (z ∣_ (q ⁻¹ᵁ PrimeSpectrum.basicOpen r)) ∧
                  let : IsAffine W.toScheme := hWa
                  let c := SmoothSite.affineOpenInclusion V W
                  let sW := (nisnevichImage P).transfer ((Cor.graphFunctor k).map c) sV
                  IsAffine (SmoothSite.etalePullback i (c ≫ v)).left ∧
                  (nisnevichImageι P).hom.app (op (Cor.mk (SmoothSite.affineOpenSite V W))) sW =
                    ((nisnevichSheafify k).obj P).obj.transfer
                      ((Cor.graphFunctor k).map (c ≫ v)) gT ∧
                  (nisnevichImage P).transfer ((Cor.graphFunctor k).map
                    (SmoothSite.etalePullbackFst i (c ≫ v))) sA =
                    (nisnevichImage P).transfer ((Cor.graphFunctor k).map
                      (SmoothSite.etalePullbackSnd i (c ≫ v))) sW ∧
                  OriginalRefinedNormalization U T e v.left z r W hW t := by
  obtain ⟨U, j, hj, hUn, hUa, T, e, A, V, i, v, hAa, hi, hv, hcover,
    Z, z, hzc, hfin, hcomp, hVz, B, bA, bV, HB, sA, sV, hm, hgA, hgV,
    r, hr, W, hWa, hW, t, ht, Ht, haff, hgW, hmW⟩ :=
    exists_affine_refined_distinguished_nisnevichImage_representatives P X g
  let : IsAffine U.left := hUa
  let : Nonempty U.left := hUn
  let : IsOpenImmersion j.left := hj
  let : IsIntegral U.left := isIntegral_of_isOpenImmersion j.left
  let : IsOpenImmersion i.left := hi
  let : Etale v.left := hv
  let : IsClosedImmersion z := hzc
  let : IsIso (pullback.snd v.left z) := hVz
  let : IsAffine W.toScheme := hWa
  let : IsFinite (z ≫ originalRepresentativeCoefficientMap U T e) := by
    have : IsFinite (z ≫ e.hom.left ≫ (SmoothSite.a1Projection (.of k) U).left) := hfin
    simpa only [originalRepresentativeCoefficientMap, Category.assoc] using
      (inferInstance : IsFinite ((z ≫ e.hom.left ≫
        (SmoothSite.a1Projection (.of k) U).left) ≫ U.left.isoSpec.hom))
  refine ⟨U, j, hj, hUn, hUa, T, e, A, V, i, v, hAa, hi, hv, hcover,
    Z, z, hzc, hfin, hcomp, hVz, B, bA, bV, HB, sA, sV, hm, hgA, hgV,
    r, hr, W, hWa, hW, t, ht, Ht, haff, hgW, hmW, ?_⟩
  exact originalRefinedNormalization_of_square U T e v.left z r W hW t hr hWa Ht

end Motivic.PresheafWithTransfers
