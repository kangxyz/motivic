module
public import Motivic.AlgebraicGeometry.Correspondences.Pencils.NormalizedCurve.CorrectingCorrespondence
/-! Direct consumer of the literal correcting endpoint construction. -/
@[expose] public noncomputable section
set_option linter.hashCommand false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
example
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
      (U : Set (Spec (.of (Polynomial k))))ᶜ) :=
  exists_actualCorrectingCorrespondence k p r v α β h B z hd s hs H U φ hφ H0 hz
#print axioms exists_actualCorrectingCorrespondence
#print axioms exists_actualSectionPencilData
#print axioms exists_actualGraphFiniteFlatPencil
end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
