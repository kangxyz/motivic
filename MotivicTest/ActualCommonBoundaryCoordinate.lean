module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Normalized.Common.BoundaryCoordinate
/-! # Literal full common-boundary coordinate consumer and foundation audit -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible Scheme.AffineLineEtaleCompactification
universe u
example (k : Type u) [Field k] {Y S X : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
  (r : S ⟶ Y) [IsOpenImmersion r]
  {R : Type u} [CommRing R] (a : Spec (.of R) ⟶ Spec (.of (Polynomial k)))
  [IsOpenImmersion a] (α : X ⟶ S) (β : X ⟶ Spec (.of R))
  (h : α ≫ r ≫ p = β ≫ a)
  (B : Type u) [CommRing B] (z : Polynomial k →+* B)
  (hd : Disjoint (Set.range a) (Set.range (Scheme.Hom.boundaryCoordinateMap k B z)))
  (s : Spec (.of B) ⟶ S) (hs : s ≫ r ≫ p = Scheme.Hom.boundaryCoordinateMap k B z)
  (H : IsPullback s (𝟙 _) (r ≫ p) (Scheme.Hom.boundaryCoordinateMap k B z)) :
    Scheme.Hom.unitEndomorphismPullback (commonBoundaryToDiagonal k p r α B s)
      (pullbackSectionMap (diagonalBoundaryMap k p r s)
        (canonicalDualHom _ (actualIdealLineBundle k p r).val
          (Scheme.Hom.idealInclusion
            (Scheme.Hom.compactificationGraph (projection k p) (r ≫ inclusion k p)))) ≫
      (actualBoundaryIso k p r B z s hs H).hom) =
    Scheme.Hom.unitEndomorphismPullback (commonBoundaryToFixed k p r a α β h B z s hs)
      (fixedBoundaryUnit k p a B z hd).hom :=
  commonBoundary_coordinate_eq k p r a α β h B z hd s hs H

open Lean in
run_cmd do
  for name in #[``commonZero_coordinateMap_eq, ``commonBoundary_coordinate_eq] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Whole original common-boundary coordinate equality uses only standard foundations."
