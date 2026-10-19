module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Normalized.GraphFiniteFlatPencil
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Normalized.SiteMaps
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Normalized.SectionPencilDataCore
/-! # Constructing the actual correcting correspondence data from the original curve -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
open _root_.AlgebraicGeometry.Scheme.SmoothSite
theorem exists_actualSectionPencilData
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
    Nonempty (GraphDivisorPencil.Data
      (pencilAlpha k p r α) (pencilBeta k p r v α β h) (pencilGraphMap k p r α U φ hφ)) := by
  obtain ⟨degree, a, b, n, d, _, _, _, _, hFa, hFb, hFn, hFd, _, hfamily, hpole⟩ :=
    exists_actualGraphFiniteFlatPencil k p r v α β h B z hd s hs H U φ hφ H0 hz
  exact ⟨actualSectionPencilDataOfSections k p r v α β h U φ hφ
    (diagonalTwistBundle k p r degree) (fixedTwistBundle k p v degree)
    a b n d hFa hFb hFn hFd hfamily hpole⟩
end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
