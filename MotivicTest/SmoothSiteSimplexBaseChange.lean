/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Simplex.BaseChange
public import Mathlib.Data.ZMod.Basic
public import Lean.Util.CollectAxioms

/-! # Literal Cartesian simplex coefficient-change consumers -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicSimplex _root_.AlgebraicGeometry.Scheme.SmoothSite
open scoped Simplicial

universe u

namespace Motivic.MotivicTest.SmoothSiteSimplexBaseChange

variable {R S : Type u} [CommRing R] [CommRing S]

example (c : R →+* S) (n : ℕ) :
    IsPushout (CommRingCat.ofHom c) (CommRingCat.ofHom (constant R n))
      (CommRingCat.ofHom (constant S n)) (CommRingCat.ofHom (mapCoefficients c n)) :=
  mapCoefficients_isPushout c n

/-- No flatness, field, or finite-type hypothesis is needed, even modulo a composite. -/
example (n : ℕ) :
    IsPullback (Spec.map (CommRingCat.ofHom (mapCoefficients (Int.castRingHom (ZMod 6)) n)))
      (structureMap (ZMod 6) n) (structureMap ℤ n)
      (Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod 6)))) :=
  mapCoefficients_isPullback _ n

example (c : R →+* S) (n : ℕ) :
    (smoothSiteBaseChangeIso c n).hom.left ≫
      Spec.map (CommRingCat.ofHom (mapCoefficients c n)) =
        pullback.fst (structureMap R n) (Spec.map (CommRingCat.ofHom c)) :=
  smoothSiteBaseChangeIso_hom_coefficientMap c n

example (c : R →+* S) (n : ℕ) :
    (smoothSiteBaseChangeIso c n).hom.left ≫ structureMap S n =
      pullback.snd (structureMap R n) (Spec.map (CommRingCat.ofHom c)) :=
  smoothSiteBaseChangeIso_hom_structureMap c n

example (c : R →+* S) (n : ℕ) (i : Fin (n + 1)) :
    (smoothSiteBaseChangeIso c n).hom.left.appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing S n))).inv (coordinate S n i)) =
        (pullback.fst (structureMap R n) (Spec.map (CommRingCat.ofHom c))).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing R n))).inv (coordinate R n i)) :=
  smoothSiteBaseChangeIso_coordinate c n i

example (c : R →+* S) (n : ℕ) (i : Fin (n + 2)) :
    (baseChange (Spec.map (CommRingCat.ofHom c))).map ((cosimplicialSmoothSite R).δ i) ≫
        (smoothSiteBaseChangeIso c (n + 1)).hom =
      (smoothSiteBaseChangeIso c n).hom ≫ (cosimplicialSmoothSite S).δ i :=
  smoothSiteBaseChangeIso_naturality c (SimplexCategory.δ i)

example (c : R →+* S) (n : ℕ) (i : Fin (n + 1)) :
    (baseChange (Spec.map (CommRingCat.ofHom c))).map ((cosimplicialSmoothSite R).σ i) ≫
        (smoothSiteBaseChangeIso c n).hom =
      (smoothSiteBaseChangeIso c (n + 1)).hom ≫ (cosimplicialSmoothSite S).σ i :=
  smoothSiteBaseChangeIso_naturality c (SimplexCategory.σ i)

example {K L : Type u} [Field K] [Field L] (c : K →+* L) :
    cosimplicialSmoothSite K ⋙ fieldBaseChange c ≅ cosimplicialSmoothSite L :=
  cosimplicialFieldBaseChangeIso c

open Lean in
run_cmd do
  for name in #[``_root_.AlgebraicSimplex.mapCoefficients_isPushout,
      ``_root_.AlgebraicSimplex.mapCoefficients_isPullback,
      ``_root_.AlgebraicSimplex.smoothSiteBaseChangeIso,
          ``_root_.AlgebraicSimplex.smoothSiteBaseChangeIso_inv_fst,
      ``_root_.AlgebraicSimplex.smoothSiteBaseChangeIso_inv_snd,
          ``_root_.AlgebraicSimplex.smoothSiteBaseChangeIso_hom_coefficientMap,
      ``_root_.AlgebraicSimplex.smoothSiteBaseChangeIso_hom_structureMap,
          ``_root_.AlgebraicSimplex.smoothSiteBaseChangeIso_coordinate,
      ``_root_.AlgebraicSimplex.cosimplicialSmoothSiteBaseChangeIso,
          ``_root_.AlgebraicSimplex.smoothSiteBaseChangeIso_naturality,
      ``_root_.AlgebraicSimplex.cosimplicialFieldBaseChangeIso] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"

end Motivic.MotivicTest.SmoothSiteSimplexBaseChange
