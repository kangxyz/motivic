/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSiteSimplex
public import Motivic.AlgebraicGeometry.SmoothSiteBaseChange
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Cartesian coefficient change for the algebraic simplex

The literal barycentric coefficient square is a pushout for every ring map.
Its spectrum is therefore a pullback, with both original projections retained.
The resulting smooth-site comparison is natural in every simplex map, hence
in every coface and codegeneracy. No finite-type assumption on the coefficient
map is made.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Simplicial

universe u

namespace Motivic.AlgebraicSimplex

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The coefficient square retains the actual constant and barycentric maps. -/
theorem mapCoefficients_square (c : R →+* S) (n : ℕ) :
    CommRingCat.ofHom c ≫ CommRingCat.ofHom (constant S n) =
      CommRingCat.ofHom (constant R n) ≫ CommRingCat.ofHom (mapCoefficients c n) := by
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun r => (mapCoefficients_constant c n r).symm)

/-- The literal barycentric coefficient square is a pushout for any ring map. -/
theorem mapCoefficients_isPushout (c : R →+* S) (n : ℕ) :
    IsPushout (CommRingCat.ofHom c) (CommRingCat.ofHom (constant R n))
      (CommRingCat.ofHom (constant S n)) (CommRingCat.ofHom (mapCoefficients c n)) := by
  apply IsPushout.of_isColimit (c := PushoutCocone.mk _ _ (mapCoefficients_square c n))
  apply PushoutCocone.isColimitAux'
  intro s
  have hx : ∑ i, s.inr (coordinate R n i) = 1 := by
    rw [← map_sum, sum_coordinate, map_one]
  let d : CommRingCat.of (CoordinateRing S n) ⟶ s.pt :=
    CommRingCat.ofHom (lift s.inl.hom (fun i => s.inr (coordinate R n i)) hx)
  refine ⟨d, ?_, ?_, ?_⟩
  · apply CommRingCat.hom_ext
    exact RingHom.ext (fun r => lift_constant _ _ hx r)
  · apply CommRingCat.hom_ext
    apply ringHom_ext
    · intro r
      change lift _ _ hx (mapCoefficients c n (constant R n r)) = _
      rw [mapCoefficients_constant, lift_constant]
      exact congrArg (fun f => f r) s.condition
    · intro i
      change lift _ _ hx (mapCoefficients c n (coordinate R n i)) = _
      rw [mapCoefficients_coordinate, lift_coordinate]
  · intro h hl hr
    apply CommRingCat.hom_ext
    apply ringHom_ext
    · intro r
      change h (constant S n r) = lift _ _ hx (constant S n r)
      rw [lift_constant]
      exact congrArg (fun f => f r) hl
    · intro i
      change h (coordinate S n i) = lift _ _ hx (coordinate S n i)
      rw [lift_coordinate]
      have hi := congrArg (fun f => f (coordinate R n i)) hr
      change h (mapCoefficients c n (coordinate R n i)) = _ at hi
      rwa [mapCoefficients_coordinate] at hi

/-- Applying spectrum gives the original coefficient-change Cartesian square. -/
theorem mapCoefficients_isPullback (c : R →+* S) (n : ℕ) :
    IsPullback (Spec.map (CommRingCat.ofHom (mapCoefficients c n)))
      (structureMap S n) (structureMap R n) (Spec.map (CommRingCat.ofHom c)) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _ (mapCoefficients_isPushout c n)).flip

/-- The actual base-changed simplex is the simplex over the new coefficient ring. -/
def smoothSiteBaseChangeIso (c : R →+* S) (n : ℕ) :
    (SmoothSite.baseChange (Spec.map (CommRingCat.ofHom c))).obj (smoothSiteObj R n) ≅
      smoothSiteObj S n :=
  (MorphismProperty.Over.isoMk (mapCoefficients_isPullback c n).isoPullback
    (mapCoefficients_isPullback c n).isoPullback_hom_snd).symm

/-- The inverse comparison retains the literal coefficient map to the old simplex. -/
@[reassoc (attr := simp)]
theorem smoothSiteBaseChangeIso_inv_fst (c : R →+* S) (n : ℕ) :
    (smoothSiteBaseChangeIso c n).inv.left ≫
      pullback.fst (structureMap R n) (Spec.map (CommRingCat.ofHom c)) =
        Spec.map (CommRingCat.ofHom (mapCoefficients c n)) :=
  (mapCoefficients_isPullback c n).isoPullback_hom_fst

/-- The inverse comparison retains the new coefficient structure map. -/
@[reassoc (attr := simp)]
theorem smoothSiteBaseChangeIso_inv_snd (c : R →+* S) (n : ℕ) :
    (smoothSiteBaseChangeIso c n).inv.left ≫
      pullback.snd (structureMap R n) (Spec.map (CommRingCat.ofHom c)) =
        structureMap S n :=
  (mapCoefficients_isPullback c n).isoPullback_hom_snd

/-- The forward comparison identifies the old projection without changing coordinates. -/
@[reassoc (attr := simp)]
theorem smoothSiteBaseChangeIso_hom_coefficientMap (c : R →+* S) (n : ℕ) :
    (smoothSiteBaseChangeIso c n).hom.left ≫
      Spec.map (CommRingCat.ofHom (mapCoefficients c n)) =
        pullback.fst (structureMap R n) (Spec.map (CommRingCat.ofHom c)) :=
  (mapCoefficients_isPullback c n).isoPullback_inv_fst

/-- The forward comparison identifies the exact scalar projection. -/
@[reassoc (attr := simp)]
theorem smoothSiteBaseChangeIso_hom_structureMap (c : R →+* S) (n : ℕ) :
    (smoothSiteBaseChangeIso c n).hom.left ≫ structureMap S n =
      pullback.snd (structureMap R n) (Spec.map (CommRingCat.ofHom c)) :=
  (mapCoefficients_isPullback c n).isoPullback_inv_snd

/-- The forward comparison retains every actual barycentric global section. -/
theorem smoothSiteBaseChangeIso_coordinate (c : R →+* S) (n : ℕ) (i : Fin (n + 1)) :
    (smoothSiteBaseChangeIso c n).hom.left.appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing S n))).inv (coordinate S n i)) =
        (pullback.fst (structureMap R n) (Spec.map (CommRingCat.ofHom c))).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing R n))).inv (coordinate R n i)) := by
  have hc : (Spec.map (CommRingCat.ofHom (mapCoefficients c n))).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing R n))).inv (coordinate R n i)) =
        (Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing S n))).inv (coordinate S n i) := by
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
      CommRingCat.comp_apply]
    exact congrArg (Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing S n))).inv
      (mapCoefficients_coordinate c n i)
  have h := congrArg (fun f => f.appTop
    ((Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing R n))).inv (coordinate R n i)))
      (smoothSiteBaseChangeIso_hom_coefficientMap c n)
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h
  exact (congrArg (smoothSiteBaseChangeIso c n).hom.left.appTop hc.symm).trans h

/-- All simplicial operators commute with the Cartesian comparison. -/
def cosimplicialSmoothSiteBaseChangeIso (c : R →+* S) :
    cosimplicialSmoothSite R ⋙ SmoothSite.baseChange (Spec.map (CommRingCat.ofHom c)) ≅
      cosimplicialSmoothSite S :=
  (NatIso.ofComponents (fun n => (smoothSiteBaseChangeIso c n.len).symm)
    (fun {m n} f => by
      apply MorphismProperty.Over.Hom.ext
      change ((cosimplicialSmoothSite S).map f).left ≫
        (smoothSiteBaseChangeIso c n.len).inv.left =
          (smoothSiteBaseChangeIso c m.len).inv.left ≫
            ((SmoothSite.baseChange (Spec.map (CommRingCat.ofHom c))).map
              ((cosimplicialSmoothSite R).map f)).left
      apply pullback.hom_ext
      · calc
          _ = ((cosimplicialSmoothSite S).map f).left ≫
              Spec.map (CommRingCat.ofHom (mapCoefficients c n.len)) :=
            (Category.assoc _ _ _).trans (congrArg (fun g =>
              ((cosimplicialSmoothSite S).map f).left ≫ g)
                (smoothSiteBaseChangeIso_inv_fst c n.len))
          _ = Spec.map (CommRingCat.ofHom (mapCoefficients c m.len)) ≫
              ((cosimplicialSmoothSite R).map f).left :=
            (cosimplicialSchemeMap c).naturality f
          _ = _ := Eq.symm ((Category.assoc _ _ _).trans
            ((congrArg (fun g => (smoothSiteBaseChangeIso c m.len).inv.left ≫ g)
              (SmoothSite.baseChange_map_fst _ ((cosimplicialSmoothSite R).map f))).trans
                (smoothSiteBaseChangeIso_inv_fst_assoc c m.len _)))
      · calc
          _ = ((cosimplicialSmoothSite S).map f).left ≫ structureMap S n.len :=
            (Category.assoc _ _ _).trans (congrArg (fun g =>
              ((cosimplicialSmoothSite S).map f).left ≫ g)
                (smoothSiteBaseChangeIso_inv_snd c n.len))
          _ = structureMap S m.len := structureMap_naturality S f
          _ = _ := Eq.symm ((Category.assoc _ _ _).trans
            ((congrArg (fun g => (smoothSiteBaseChangeIso c m.len).inv.left ≫ g)
              (SmoothSite.baseChange_map_snd _ ((cosimplicialSmoothSite R).map f))).trans
                (smoothSiteBaseChangeIso_inv_snd c m.len))))).symm

/-- Every cosimplicial map commutes with the displayed objectwise comparison. -/
@[reassoc]
theorem smoothSiteBaseChangeIso_naturality (c : R →+* S)
    {m n : SimplexCategory} (f : m ⟶ n) :
    (SmoothSite.baseChange (Spec.map (CommRingCat.ofHom c))).map
        ((cosimplicialSmoothSite R).map f) ≫ (smoothSiteBaseChangeIso c n.len).hom =
      (smoothSiteBaseChangeIso c m.len).hom ≫ (cosimplicialSmoothSite S).map f :=
  (cosimplicialSmoothSiteBaseChangeIso c).hom.naturality f

/-- Arbitrary field extensions use the same actual Cartesian comparison. -/
def cosimplicialFieldBaseChangeIso {K L : Type u} [Field K] [Field L] (c : K →+* L) :
    cosimplicialSmoothSite K ⋙ SmoothSite.fieldBaseChange c ≅
      cosimplicialSmoothSite L :=
  cosimplicialSmoothSiteBaseChangeIso c

end Motivic.AlgebraicSimplex
