/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.LocalVanishing.Laurent.GenericOpenZero
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Cohomology.GenericOpen
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Affine.Coordinates
/-! # Actual affine-localization witnesses give zero on an original generic neighborhood -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Polynomial
universe v u
namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme
open _root_.Algebra.Smooth
open _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
open _root_.AlgebraicGeometry.PolynomialOpenQuotient.Laurent
open _root_.AlgebraicGeometry.Scheme.PolynomialLaurent
open _root_.AlgebraicGeometry.Scheme.SmoothSite
variable {k : Type u} [Field k]
attribute [local instance] away_smooth

/-- A representative-level property on actual smooth affine models. -/
def AffineLocalizationZero (P : PresheafWithTransfers.{v} k) : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [Algebra k R] [Algebra.Smooth k R]
    (s : P.sections (Cor.mk (affineSite k R))),
    ∃ r : R, r ≠ 0 ∧ P.transfer ((Cor.graphFunctor k).map
      (affineMorphism (IsScalarTower.toAlgHom k R (Localization.Away r)))) s = 0

/-- The actual affine model and original generic point are preserved. -/
theorem exists_generic_open_zero_of_affineLocalizationZero
    (P : PresheafWithTransfers.{v} k) (hP : AffineLocalizationZero P)
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left]
    (s : P.sections (Cor.mk X)) :
    ∃ (V : X.left.Opens), genericPoint X.left ∈ V ∧
      P.transfer ((Cor.graphFunctor k).map (openInclusion X V)) s = 0 := by
  let R := Γ(X.left, ⊤)
  let : Algebra k R := AffineCoordinates.sectionsAlgebra X
  let : Algebra.Smooth k R := AffineCoordinates.sectionsSmooth X
  let e := AffineCoordinates.affineIso X
  obtain ⟨r, hr, hz⟩ := hP R (P.transfer ((Cor.graphFunctor k).map e.hom) s)
  let : IsDomain (Localization.Away r) := Localization.Away.isDomain hr
  let : IsIntegral (affineSite k (Localization.Away r)).left :=
    inferInstanceAs (IsIntegral (Spec (.of (Localization.Away r))))
  let a : affineSite k (Localization.Away r) ⟶ X :=
    affineMorphism (IsScalarTower.toAlgHom k R (Localization.Away r)) ≫ e.hom
  have ha : IsOpenImmersion a.left := by
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap R (Localization.Away r))) ≫ X.left.isoSpec.inv)
    infer_instance
  let : IsOpenImmersion a.left := ha
  let V := a.left.opensRange
  have hV : genericPoint X.left ∈ V := by
    refine ⟨genericPoint (Spec (.of (Localization.Away r))), ?_⟩
    exact genericPoint_eq_of_isOpenImmersion a.left
  let ev := IsOpenImmersion.isoOfRangeEq a.left V.ι (by
    rw [Scheme.Opens.range_ι]
    rfl)
  have hev : ev.hom ≫ V.ι = a.left := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  let E : affineSite k (Localization.Away r) ≅ (opensFunctor X).obj V :=
    MorphismProperty.Over.isoMk ev (by
      change ev.hom ≫ (V.ι ≫ X.hom) = _
      rw [← Category.assoc, hev]
      exact MorphismProperty.Over.w a)
  have hE : E.hom ≫ openInclusion X V = a := by
    apply MorphismProperty.Over.Hom.ext
    exact hev
  have hz' : P.transfer ((Cor.graphFunctor k).map a) s = 0 := by
    change P.transfer ((Cor.graphFunctor k).map (_ ≫ e.hom)) s = 0
    rw [Functor.map_comp, transfer_comp, ConcreteCategory.comp_apply]
    exact hz
  refine ⟨V, hV, ?_⟩
  have hi := (ConcreteCategory.bijective_of_isIso
    (P.transfer ((Cor.graphFunctor k).map E.hom))).injective
  apply hi
  have heq : P.transfer ((Cor.graphFunctor k).map E.hom)
      (P.transfer ((Cor.graphFunctor k).map (openInclusion X V)) s) = 0 := by
    rw [← ConcreteCategory.comp_apply, ← transfer_comp, ← Functor.map_comp, hE]
    exact hz'
  exact heq.trans (map_zero (P.transfer ((Cor.graphFunctor k).map E.hom)).hom).symm

end Motivic.PresheafWithTransfers
