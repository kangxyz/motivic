module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Sections.Normalized.Diagonal.BoundaryCoordinate
/-! # The chosen original diagonal frame retains both literal component coordinates -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
universe u
example (k : Type u) [Field k] {Y S : Scheme.{u}}
    (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
    (r : S ⟶ Y) [IsOpenImmersion r]
    (B : Type u) [CommRing B] (z : Polynomial k →+* B) (s : Spec (.of B) ⟶ S)
    (hs : s ≫ (r ≫ p) = Scheme.Hom.boundaryCoordinateMap k B z)
    (H : IsPullback s (𝟙 _) (r ≫ p) (Scheme.Hom.boundaryCoordinateMap k B z)) :
    Scheme.Hom.unitEndomorphismPullback coprod.inl
        (actualDiagonalBoundaryCoordinate k p r B z s hs H) = 𝟙 _ ∧
      Scheme.Hom.unitEndomorphismPullback coprod.inr
        (actualDiagonalBoundaryCoordinate k p r B z s hs H) =
      Scheme.Hom.boundaryCoordinateEndomorphism k B z
        (actualDiagonalCoordinateMap k p r B z s hs) :=
  ⟨actualDiagonalBoundaryCoordinate_inl k p r B z s hs H,
    actualDiagonalBoundaryCoordinate_inr k p r B z s hs H⟩
