/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.Sheafification.Representatives.Distinguished
public import Motivic.Transfers.Presheaf.Sheafification.Representatives.Restriction


/-! # Actual affine refinement of original distinguished representatives

The original distinguished producer and the full-support affine refinement are
each used once. The entire marked scheme and the original representative maps
remain in the output; no normalization, frame, or section choices occur here.
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
theorem exists_affine_refined_distinguished_nisnevichImage_representatives
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
                      (SmoothSite.etalePullbackSnd i (c ≫ v))) sW := by
  obtain ⟨U, j, hj, hUn, hUa, T, e, A, V, i, v, hAa, hi, hv, hcover,
    Z, z, hz, hfin, hcomp, hVz, B, bA, bV, HB, sA, sV, hm, hgA, hgV⟩ :=
    exists_affine_open_distinguished_nisnevichImage_representatives P X g
  let : IsAffine U.left := hUa
  let : Nonempty U.left := hUn
  let : IsOpenImmersion j.left := hj
  let : IsIntegral U.left := isIntegral_of_isOpenImmersion j.left
  let : IsAffine A.left := hAa
  let : IsOpenImmersion i.left := hi
  let : Etale v.left := hv
  let : IsIso (pullback.snd v.left z) := hVz
  let : IsAffine (SmoothSite.a1Cylinder (.of k) U).left := by
    change IsAffine (pullback U.hom (Scheme.PolynomialLaurent.polynomialProjection (.of k)))
    exact Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine
      (show U.left ⟶ Spec (.of k) from U.hom)
      (Scheme.PolynomialLaurent.polynomialProjection (.of k))
  let : IsAffine T.left := IsAffine.of_isIso e.hom.left
  let q := e.hom.left ≫ (SmoothSite.a1Projection (.of k) U).left ≫ U.left.isoSpec.hom
  let : IsFinite (z ≫ q) := by
    have : IsFinite (z ≫ e.hom.left ≫ (SmoothSite.a1Projection (.of k) U).left) := hfin
    dsimp only [q]
    simpa only [Category.assoc] using
      (inferInstance : IsFinite ((z ≫ e.hom.left ≫
        (SmoothSite.a1Projection (.of k) U).left) ≫ U.left.isoSpec.hom))
  let s := inv (pullback.snd v.left z) ≫ pullback.fst v.left z
  have hs : s ≫ v.left = z := by simp [s, pullback.condition]
  have Hs : IsPullback s (𝟙 Z) v.left z :=
    (IsPullback.of_hasPullback v.left z).of_iso (asIso (pullback.snd v.left z))
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [s])
      (by simp) (by simp) (by simp)
  let gT := ((nisnevichSheafify k).obj P).obj.transfer
    ((Cor.graphFunctor k).map (e.hom ≫ SmoothSite.a1Map (.of k) j)) g
  have hg : (nisnevichImageι P).hom.app (op (Cor.mk V)) sV =
      ((nisnevichSheafify k).obj P).obj.transfer ((Cor.graphFunctor k).map v) gT := by
    simpa only [gT, Functor.map_comp, transfer_comp, ConcreteCategory.comp_apply] using hgV
  refine ⟨U, j, hj, hUn, hUa, T, e, A, V, i, v, hAa, hi, hv, hcover,
    Z, z, hz, hfin, hcomp, hVz, B, bA, bV, HB, sA, sV, hm, hgA, hgV, ?_⟩
  exact exists_affine_marked_representative_refinement P Γ(U.left, ⊤)
    q v i bA bV HB z s hs Hs sA sV hm gT hg

end Motivic.PresheafWithTransfers
