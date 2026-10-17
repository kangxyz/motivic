module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.ActualDiagonalSectionPair
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.PrescribedPairPullback
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.CoordinateUnitOnOpen
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.CoproductUnitEndomorphism
/-! # The original diagonal section in its literal full-boundary coordinate -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
variable (k : Type u) [Field k] {Y S : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
  (r : S ⟶ Y) [IsOpenImmersion r]
  (B : Type u) [CommRing B] (z : Polynomial k →+* B)
  (s : Spec (.of B) ⟶ S)
  (hs : s ≫ (r ≫ p) = Hom.boundaryCoordinateMap k B z)

/-- The exact product comparison followed by the unchanged coordinate product map. -/
def actualDiagonalCoordinateMap :
    pullback ((r ≫ inclusion k p) ≫ projection k p)
      (s ≫ (r ≫ inclusion k p) ≫ projection k p) ⟶
    pullback (Hom.boundaryLineProjection k)
      (Hom.boundaryCoordinateMap k B z ≫ Hom.boundaryLineProjection k) :=
  (pullback.congrHom
    (show (r ≫ inclusion k p) ≫ projection k p =
      (r ≫ p) ≫ Hom.boundaryLineProjection k by
        simp only [Category.assoc, inclusion_projection])
    (show s ≫ (r ≫ inclusion k p) ≫ projection k p =
      Hom.boundaryCoordinateMap k B z ≫ Hom.boundaryLineProjection k by
        simpa only [Category.assoc, inclusion_projection] using
          congrArg (fun f => f ≫ Hom.boundaryLineProjection k) hs)).hom ≫
    Hom.boundaryProductMap (Hom.boundaryLineProjection k) (r ≫ p)
      (Hom.boundaryCoordinateMap k B z)

/-- The zero-boundary canonical section has the original pulled coordinate difference. -/
theorem actualDiagonalZero_coordinate
    (H : IsPullback s (𝟙 _) (r ≫ p) (Hom.boundaryCoordinateMap k B z)) :
    Hom.pullbackCanonicalDualHom
        (Hom.graphBoundaryRestriction (projection k p) (r ≫ inclusion k p) s)
        (actualIdealLineBundle k p r)
        (Hom.idealInclusion (Hom.compactificationGraph (projection k p) (r ≫ inclusion k p))) ≫
      (Hom.compactificationBoundaryDivisorIso k B z (projection k p) (r ≫ inclusion k p)
        (r ≫ p) (by simp only [Category.assoc, inclusion_projection])
        s hs H (actualIdealLineBundle k p r).property).hom =
    Hom.boundaryCoordinateEndomorphism k B z (actualDiagonalCoordinateMap k p r B z s hs) := by
  have h := Hom.compactificationBoundaryDivisorIso_coordinate k B z
    (projection k p) (r ≫ inclusion k p) (r ≫ p)
    (by simp only [Category.assoc, inclusion_projection]) s hs H
    (actualIdealLineBundle k p r).property
  exact h.trans (Hom.boundaryCoordinateEndomorphism_comp k B z _ _).symm

omit B z s hs in
/-- The infinity-boundary canonical section has literal coordinate one. -/
theorem actualDiagonalInfinity_coordinate :
    Hom.pullbackCanonicalDualHom
        (Hom.infinityProductMap (projection k p) (r ≫ inclusion k p) (infinityInclusion k p))
        (actualIdealLineBundle k p r)
        (Hom.idealInclusion (Hom.compactificationGraph (projection k p) (r ≫ inclusion k p))) ≫
      (Hom.infinityBoundaryDivisorIso (projection k p) (r ≫ inclusion k p)
        (infinityInclusion k p) (refined_disjoint_infinity k p r)
        (actualIdealLineBundle k p r).property).hom = 𝟙 _ :=
  Hom.infinityBoundaryDivisorIso_canonical (projection k p) (r ≫ inclusion k p)
    (infinityInclusion k p) (refined_disjoint_infinity k p r)
    (actualIdealLineBundle k p r).property

/-- The canonical diagonal section evaluated in the originally chosen full-boundary frame. -/
def actualDiagonalBoundaryCoordinate
    (H : IsPullback s (𝟙 _) (r ≫ p) (Hom.boundaryCoordinateMap k B z)) :
    SheafOfModules.unit (diagonalBoundary k p r s).ringCatSheaf ⟶
      SheafOfModules.unit (diagonalBoundary k p r s).ringCatSheaf :=
  pullbackSectionMap (diagonalBoundaryMap k p r s)
      (canonicalDualHom (diagonalAmbient k p r) (actualIdealLineBundle k p r).val
        (Hom.idealInclusion (Hom.compactificationGraph (projection k p) (r ≫ inclusion k p)))) ≫
    (actualBoundaryIso k p r B z s hs H).hom

/-- The original full-boundary coordinate restricts to one on the whole infinity component. -/
theorem actualDiagonalBoundaryCoordinate_inl
    (H : IsPullback s (𝟙 _) (r ≫ p) (Hom.boundaryCoordinateMap k B z)) :
    Hom.unitEndomorphismPullback coprod.inl
      (actualDiagonalBoundaryCoordinate k p r B z s hs H) = 𝟙 _ := by
  have hE := (Classical.choose_spec
    (exists_actualFullBoundaryDivisorIso k p r B z s hs H)).1
  have h := Hom.unitEndomorphismPullback_coprod_inl_coordinate
    (Hom.infinityProductMap (projection k p) (r ≫ inclusion k p) (infinityInclusion k p))
    (Hom.graphBoundaryRestriction (projection k p) (r ≫ inclusion k p) s)
    (actualDivisorLineBundle k p r).val
    (canonicalDualHom (diagonalAmbient k p r) (actualIdealLineBundle k p r).val
      (Hom.idealInclusion (Hom.compactificationGraph (projection k p) (r ≫ inclusion k p))))
    (actualBoundaryIso k p r B z s hs H)
    (Hom.infinityBoundaryDivisorIso (projection k p) (r ≫ inclusion k p)
      (infinityInclusion k p) (refined_disjoint_infinity k p r)
      (actualIdealLineBundle k p r).property) hE
  exact h.trans (actualDiagonalInfinity_coordinate k p r)

/-- The original full-boundary coordinate restricts to the literal coordinate difference on Z. -/
theorem actualDiagonalBoundaryCoordinate_inr
    (H : IsPullback s (𝟙 _) (r ≫ p) (Hom.boundaryCoordinateMap k B z)) :
    Hom.unitEndomorphismPullback coprod.inr
      (actualDiagonalBoundaryCoordinate k p r B z s hs H) =
      Hom.boundaryCoordinateEndomorphism k B z (actualDiagonalCoordinateMap k p r B z s hs) := by
  have hE := (Classical.choose_spec
    (exists_actualFullBoundaryDivisorIso k p r B z s hs H)).2
  have h := Hom.unitEndomorphismPullback_coprod_inr_coordinate
    (Hom.infinityProductMap (projection k p) (r ≫ inclusion k p) (infinityInclusion k p))
    (Hom.graphBoundaryRestriction (projection k p) (r ≫ inclusion k p) s)
    (actualDivisorLineBundle k p r).val
    (canonicalDualHom (diagonalAmbient k p r) (actualIdealLineBundle k p r).val
      (Hom.idealInclusion (Hom.compactificationGraph (projection k p) (r ≫ inclusion k p))))
    (actualBoundaryIso k p r B z s hs H)
    (Hom.compactificationBoundaryDivisorIso k B z (projection k p) (r ≫ inclusion k p)
      (r ≫ p) (by simp only [Category.assoc, inclusion_projection])
      s hs H (actualIdealLineBundle k p r).property) hE
  exact h.trans (actualDiagonalZero_coordinate k p r B z s hs H)
end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
