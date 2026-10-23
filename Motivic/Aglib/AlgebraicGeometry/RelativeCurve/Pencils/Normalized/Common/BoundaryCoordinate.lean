/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Sections.Normalized.Diagonal.BoundaryCoordinate
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Normalized.CommonBoundary
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Sections.Normalized.FixedOpen.SectionPair
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.CoordinateProductPullback
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.CoproductUnitEndomorphism
/-! # Literal coordinate agreement on the whole common boundary -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
variable (k : Type u) [Field k] {Y S A X : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
  (r : S ⟶ Y) [IsOpenImmersion r] (a : A ⟶ Spec (.of (Polynomial k)))
  (α : X ⟶ S) (β : X ⟶ A) (h : α ≫ r ≫ p = β ≫ a)
  (B : Type u) [CommRing B] (z : Polynomial k →+* B) (s : Spec (.of B) ⟶ S)
  (hs : s ≫ r ≫ p = Hom.boundaryCoordinateMap k B z)

omit [IsSeparated p] [IsOpenImmersion r] in
/-- Both original source legs give the same coordinate map on the full Z component. -/
theorem commonZero_coordinateMap_eq :
    constantSourceMapOfEq α ((r ≫ inclusion k p) ≫ projection k p)
        (s ≫ (r ≫ inclusion k p) ≫ projection k p) (commonSourceProjection k p r α) rfl ≫
      actualDiagonalCoordinateMap k p r B z s hs =
      commonZeroToFixed k p r a α β h B z s hs ≫
        Hom.boundaryProductMap (Hom.boundaryLineProjection k) a
          (Hom.boundaryCoordinateMap k B z) := by
  dsimp only [actualDiagonalCoordinateMap]
  apply pullback.hom_ext
  · simp [Hom.boundaryProductMap, pullback.congrHom, commonZeroToFixed,
      Category.assoc]
    simpa only [Category.assoc] using congrArg
      (fun f => pullback.fst (commonSourceProjection k p r α)
        (s ≫ (r ≫ inclusion k p) ≫ projection k p) ≫ f) h
  · simp [Hom.boundaryProductMap, constantSourceMapOfEq, commonZeroToFixed,
      pullback.congrHom, Category.assoc]

end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification

namespace AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
variable (k : Type u) [Field k] {Y : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
  {R : Type u} [CommRing R] (a : Spec (.of R) ⟶ Spec (.of (Polynomial k)))
  [IsOpenImmersion a] (B : Type u) [CommRing B] (z : Polynomial k →+* B)
  (hd : Disjoint (Set.range a) (Set.range (Hom.boundaryCoordinateMap k B z)))

/-- The chosen fixed-source unit has literal normalized infinity value one. -/
theorem fixedBoundaryUnit_pullback_inl :
    Hom.unitEndomorphismPullback (coprod.inl : fixedInfinity k p a ⟶ fixedBoundary k p a B z)
      (fixedBoundaryUnit k p a B z hd).hom = 𝟙 _ := by
  apply Hom.unitEndomorphismPullback_eq_of_restrict
  rw [fixedBoundaryUnit_infinity]
  simp only [Category.id_comp, Category.comp_id]

/-- Its normalized zero-component value is the original coordinate, including nilpotents. -/
theorem fixedBoundaryUnit_pullback_inr :
    Hom.unitEndomorphismPullback (coprod.inr : fixedZero k a B z ⟶ fixedBoundary k p a B z)
      (fixedBoundaryUnit k p a B z hd).hom =
    Hom.boundaryCoordinateEndomorphism k B z
      (Hom.boundaryProductMap (Hom.boundaryLineProjection k) a (Hom.boundaryCoordinateMap k B z)) :=
  Hom.unitEndomorphismPullback_eq_of_restrict _ _ _ (fixedBoundaryUnit_coordinate k p a B z hd)

end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification

namespace AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
variable (k : Type u) [Field k] {Y S X : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
  (r : S ⟶ Y) [IsOpenImmersion r]
  {R : Type u} [CommRing R] (a : Spec (.of R) ⟶ Spec (.of (Polynomial k)))
  [IsOpenImmersion a] (α : X ⟶ S) (β : X ⟶ Spec (.of R))
  (h : α ≫ r ≫ p = β ≫ a)
  (B : Type u) [CommRing B] (z : Polynomial k →+* B)
  (hd : Disjoint (Set.range a) (Set.range (Hom.boundaryCoordinateMap k B z)))
  (s : Spec (.of B) ⟶ S) (hs : s ≫ r ≫ p = Hom.boundaryCoordinateMap k B z)
  (H : IsPullback s (𝟙 _) (r ≫ p) (Hom.boundaryCoordinateMap k B z))

/-- The original canonical diagonal coordinate and the fixed-source numerator ratio agree
on the entire common infinity-plus-Z boundary, with their literal chosen frames. -/
theorem commonBoundary_coordinate_eq :
    Hom.unitEndomorphismPullback (commonBoundaryToDiagonal k p r α B s)
      (actualDiagonalBoundaryCoordinate k p r B z s hs H) =
    Hom.unitEndomorphismPullback (commonBoundaryToFixed k p r a α β h B z s hs)
      (fixedBoundaryUnit k p a B z hd).hom := by
  apply Hom.unitEndomorphism_ext_coprod
  · simp only [Hom.unitEndomorphismPullback_comp, commonBoundaryToDiagonal,
      commonBoundaryToFixed, coprod.inl_map]
    rw [← Hom.unitEndomorphismPullback_comp, ← Hom.unitEndomorphismPullback_comp,
      actualDiagonalBoundaryCoordinate_inl, fixedBoundaryUnit_pullback_inl]
    simp [Hom.unitEndomorphismPullback]
  · simp only [Hom.unitEndomorphismPullback_comp, commonBoundaryToDiagonal,
      commonBoundaryToFixed, coprod.inr_map]
    rw [← Hom.unitEndomorphismPullback_comp, ← Hom.unitEndomorphismPullback_comp,
      actualDiagonalBoundaryCoordinate_inr, fixedBoundaryUnit_pullback_inr,
      ← Hom.boundaryCoordinateEndomorphism_comp, ← Hom.boundaryCoordinateEndomorphism_comp,
      commonZero_coordinateMap_eq]

end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
