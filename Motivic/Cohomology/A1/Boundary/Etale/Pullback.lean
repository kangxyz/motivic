module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.InverseImage.EtaleLocalization

/-! # Actual punctured-neighborhood comparison for étale boundary excision -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Motivic.FiniteEtaleSite
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {B : Scheme.{u}} {U Y U' Y' : SmoothSite B}
  (j : U ⟶ Y) (p : Y' ⟶ Y) (j' : U' ⟶ Y') (q : U' ⟶ U)
  [Etale p.left] [IsSeparated p.left] [QuasiCompact p.left]
  (hpb : IsPullback q j' j p)

/-- Forgetting étale postcomposition is compatible with the original smooth object. -/
def etaleToSmoothIso :
    etalePostcompose p.left ⋙ toSmoothSite Y ≅ toSmoothSite Y' :=
  NatIso.ofComponents (fun V ↦ MorphismProperty.Over.isoMk (Iso.refl _) (by
    change 𝟙 V.left ≫ (V.hom ≫ Y'.hom) = (V.hom ≫ p.left) ≫ Y.hom
    simp only [Category.id_comp, Category.assoc, MorphismProperty.Over.w]))
    (by intro V W f; ext; simp; rfl)

include hpb
omit [IsSeparated p.left] [QuasiCompact p.left]

/-- The iterated punctured-neighborhood square is literally Cartesian. -/
theorem puncturedNeighborhood_isPullback (V : EtaleSeparatedFiniteType Y'.left) :
    IsPullback (pullback.fst V.hom j'.left)
      (pullback.snd V.hom j'.left ≫ q.left) (V.hom ≫ p.left) j.left := by
  have H := ((SmoothSite.forgetScheme B).map_isPullback hpb.flip).flip
  exact ((IsPullback.of_hasPullback V.hom j'.left).flip.paste_horiz H).flip

/-- The true underlying scheme isomorphism, with both original projections. -/
def puncturedNeighborhoodIso (V : EtaleSeparatedFiniteType Y'.left) :
    pullback V.hom j'.left ≅ pullback (V.hom ≫ p.left) j.left :=
  (puncturedNeighborhood_isPullback j p j' q hpb V).isoPullback

@[reassoc (attr := simp)]
theorem puncturedNeighborhoodIso_hom_fst (V : EtaleSeparatedFiniteType Y'.left) :
    (puncturedNeighborhoodIso j p j' q hpb V).hom ≫
      pullback.fst (V.hom ≫ p.left) j.left = pullback.fst V.hom j'.left :=
  (puncturedNeighborhood_isPullback j p j' q hpb V).isoPullback_hom_fst

@[reassoc (attr := simp)]
theorem puncturedNeighborhoodIso_hom_snd (V : EtaleSeparatedFiniteType Y'.left) :
    (puncturedNeighborhoodIso j p j' q hpb V).hom ≫
      pullback.snd (V.hom ≫ p.left) j.left = pullback.snd V.hom j'.left ≫ q.left :=
  (puncturedNeighborhood_isPullback j p j' q hpb V).isoPullback_hom_snd

/-- Restricting to the punctured source commutes with the étale Cartesian square. -/
def etalePuncturedToSmoothIso :
    baseChange j'.left ⋙ toSmoothSite U' ≅
      etalePostcompose p.left ⋙ baseChange j.left ⋙ toSmoothSite U :=
  NatIso.ofComponents (fun V ↦ MorphismProperty.Over.isoMk
    (puncturedNeighborhoodIso j p j' q hpb V) (by
      change (puncturedNeighborhoodIso j p j' q hpb V).hom ≫
        (pullback.snd (V.hom ≫ p.left) j.left ≫ U.hom) =
          pullback.snd V.hom j'.left ≫ U'.hom
      rw [← Category.assoc, puncturedNeighborhoodIso_hom_snd,
        Category.assoc, MorphismProperty.Over.w])) (by
    intro V W f
    apply MorphismProperty.Over.Hom.ext
    change pullback.lift (pullback.fst V.hom j'.left ≫ f.left)
        (pullback.snd V.hom j'.left) (by simp [Category.assoc, pullback.condition]) ≫
          (puncturedNeighborhoodIso j p j' q hpb W).hom =
      (puncturedNeighborhoodIso j p j' q hpb V).hom ≫
        pullback.lift (pullback.fst (V.hom ≫ p.left) j.left ≫ f.left)
          (pullback.snd (V.hom ≫ p.left) j.left)
          (by
            rw [Category.assoc, ← Category.assoc f.left W.hom p.left,
              MorphismProperty.Over.w]
            exact pullback.condition)
    apply pullback.hom_ext <;>
      simp only [Category.assoc, puncturedNeighborhoodIso_hom_fst,
        puncturedNeighborhoodIso_hom_snd, puncturedNeighborhoodIso_hom_fst_assoc,
        pullback.lift_fst, pullback.lift_snd, pullback.lift_snd_assoc])

end Motivic.FiniteEtaleSite
