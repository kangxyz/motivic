/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Simplex.AlgebraicSimplexUnitSchemeComplex
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Simplex.BaseChange

/-! # Unit chains on actual affine-base relative simplex products -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
  AlgebraicTopology AlgebraicGeometry Opposite

universe u

namespace AlgebraicSimplex
open _root_.AlgebraicGeometry.Scheme

variable {k R : Type u} [CommRing k] [CommRing R] [IsReduced R]

/-- Literal relative products of the original base simplex with `Spec R`. -/
def affineRelativeSimplex (c : k →+* R) : CosimplicialObject Scheme.{u} :=
  cosimplicialSmoothSite k ⋙ SmoothSite.baseChange (Spec.map (CommRingCat.ofHom c)) ⋙
    SmoothSite.forgetScheme (Spec (.of R))

/-- The original Cartesian comparison retains every face and degeneracy. -/
def affineRelativeSimplexIso (c : k →+* R) :
    affineRelativeSimplex c ≅ cosimplicialScheme R :=
  isoWhiskerRight (cosimplicialSmoothSiteBaseChangeIso c)
    (SmoothSite.forgetScheme (Spec (.of R)))

/-- Global units on the actual relative products, not on a replacement complex,
are chain-homotopy equivalent to the original affine-base units in degree zero. -/
def affineRelativeUnitChainHomotopyEquiv (c : k →+* R) :
    HomotopyEquiv
      (SingularComplex.obj (affineRelativeSimplex c) (Scheme.Γ ⋙ ringUnits))
      ((ChainComplex.single₀ AddCommGrpCat).obj (AddCommGrpCat.of (Additive Rˣ))) :=
  (HomotopyEquiv.ofIso ((alternatingFaceMapComplex AddCommGrpCat).mapIso
    (isoWhiskerRight (NatIso.op (affineRelativeSimplexIso c).symm) (Scheme.Γ ⋙ ringUnits)))).trans
      (schemeUnitChainHomotopyEquiv R)

instance affineRelativeUnitChainHomotopyEquiv_quasiIso (c : k →+* R) :
    QuasiIso (affineRelativeUnitChainHomotopyEquiv c).hom :=
  (affineRelativeUnitChainHomotopyEquiv c).quasiIso_hom

/-- The literal relative-product projection induces an isomorphism on global units. -/
instance isIso_units_affineRelativeProjection (c : k →+* R) (n : ℕ) :
    IsIso (ringUnits.map
      (pullback.snd (structureMap k n) (Spec.map (CommRingCat.ofHom c))).appTop) := by
  rw [← (mapCoefficients_isPullback c n).isoPullback_inv_snd,
    Scheme.Hom.comp_appTop, ringUnits.map_comp]
  infer_instance

end AlgebraicSimplex
