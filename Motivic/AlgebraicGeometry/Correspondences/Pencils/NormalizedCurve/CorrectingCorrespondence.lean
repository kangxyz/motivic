/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Normalized.SectionPencilData
public import Motivic.AlgebraicGeometry.Correspondences.Moving.Pencils.DiagonalSigned
/-! # Constructing the actual correcting correspondence data from the original curve -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
theorem exists_actualCorrectingCorrespondence
    (k : Type u) [Field k] {Y X : Scheme.{u}} [IsAffine X]
    (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
    {R Q : Type u} [CommRing R] [IsNoetherianRing R] [CommRing Q] [IsNoetherianRing Q]
    (r : Spec (.of R) ⟶ Y) [IsOpenImmersion r] [QuasiCompact r]
    (v : Spec (.of Q) ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion v]
    (α : X ⟶ Spec (.of R)) [IsOpenImmersion α] [QuasiCompact α]
    (β : X ⟶ Spec (.of Q)) [Etale β] (h : α ≫ r ≫ p = β ≫ v)
    (B : Type u) [CommRing B] (z : Polynomial k →+* B)
    [IsClosedImmersion (Hom.boundaryCoordinateMap k B z)]
    [IsFinite (Hom.boundaryCoordinateMap k B z ≫ Hom.boundaryLineProjection k)]
    (hd : Disjoint (Set.range v) (Set.range (Hom.boundaryCoordinateMap k B z)))
    (s : Spec (.of B) ⟶ Spec (.of R))
    (hs : s ≫ r ≫ p = Hom.boundaryCoordinateMap k B z)
    (H : IsPullback s (𝟙 _) (r ≫ p) (Hom.boundaryCoordinateMap k B z))
    (U : (Spec (.of (Polynomial k))).Opens)
    (φ : X ⟶ pullback U.ι p)
    (hφ : φ ≫ retainedInclusion k p U = α ≫ r ≫ inclusion k p)
    (H0 : IsPullback (s ≫ r) (𝟙 _) p (Hom.boundaryCoordinateMap k B z))
    (hz : Set.range (Hom.boundaryCoordinateMap k B z) =
      (U : Set (Spec (.of (Polynomial k))))ᶜ) :
    ∃ (lam : Cor.mk (diagonalSourceSite k p r) ⟶ Cor.mk (retainedTargetSite k p U))
      (psi : Cor.mk (fixedSourceSite k v) ⟶ Cor.mk (retainedTargetSite k p U))
      (alpha : Cor.mk (SmoothSite.a1Cylinder (.of k) (commonSourceSite k p r α)) ⟶
        Cor.mk (retainedTargetSite k p U)),
      (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) (commonSourceSite k p r α) 0) ≫
          alpha = (Cor.graphFunctor k).map (pencilGraphMap k p r α U φ hφ) ∧
        (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) (commonSourceSite k p r α) 1) ≫
          alpha = (Cor.graphFunctor k).map (pencilAlpha k p r α) ≫ lam -
            (Cor.graphFunctor k).map (pencilBeta k p r v α β h) ≫ psi := by
  obtain ⟨P⟩ := exists_actualSectionPencilData k p r v α β h B z hd s hs H U φ hφ H0 hz
  exact ⟨P.lam, P.psi, P.correspondence, P.endpoints⟩
end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
