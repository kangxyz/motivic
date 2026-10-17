module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.ActualCorrectingCorrespondence
/-! # A compact statement of the actual correcting endpoints

This predicate only abbreviates the original existential endpoint equations.
The geometry theorem constructs it from precisely the original input data.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
universe u
namespace Motivic
/-- Actual correcting correspondences with both literal cylinder endpoints. -/
def HasCorrectingEndpoints {k : Type u} [Field k]
    {X T V Y : SmoothSite (Spec (.of k))}
    (f : X ⟶ T) (g : X ⟶ V) (j : X ⟶ Y) : Prop :=
  ∃ (lam : Cor.mk T ⟶ Cor.mk Y) (psi : Cor.mk V ⟶ Cor.mk Y)
    (alpha : Cor.mk (SmoothSite.a1Cylinder (.of k) X) ⟶ Cor.mk Y),
    (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) X 0) ≫ alpha =
      (Cor.graphFunctor k).map j ∧
    (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) X 1) ≫ alpha =
      (Cor.graphFunctor k).map f ≫ lam - (Cor.graphFunctor k).map g ≫ psi
/-- The actual geometric pencil supplies the compact endpoint statement. -/
theorem hasCorrectingEndpoints_of_data {k : Type u} [Field k]
    {X T V Y : SmoothSite (Spec (.of k))}
    {f : X ⟶ T} {g : X ⟶ V} {j : X ⟶ Y}
    (P : DiagonalSignedPencilProducer.Data f g j) : HasCorrectingEndpoints f g j :=
  ⟨P.lam, P.psi, P.correspondence, P.endpoints⟩
end Motivic
namespace AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
theorem has_actualCorrectingEndpoints
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
    HasCorrectingEndpoints (pencilAlpha k p r α) (pencilBeta k p r v α β h)
      (pencilGraphMap k p r α U φ hφ) := by
  obtain ⟨P⟩ := exists_actualSectionPencilData k p r v α β h B z hd s hs H U φ hφ H0 hz
  exact hasCorrectingEndpoints_of_data P
end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
