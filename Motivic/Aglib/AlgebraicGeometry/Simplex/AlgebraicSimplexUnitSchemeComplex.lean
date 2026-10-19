/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Simplex.AlgebraicSimplexUnitComplex
public import Motivic.Aglib.AlgebraicGeometry.Simplex.AlgebraicSimplexScheme
public import Motivic.Aglib.Algebra.Homology.SingularComplex.Basic

/-! # Global-unit chains on the actual simplex schemes -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicGeometry Opposite

universe u

namespace AlgebraicSimplex
open _root_.AlgebraicGeometry.Scheme

variable (R : Type u) [CommRing R] [IsReduced R]

/-- The coordinate comparison uses the actual global functions on every simplex scheme. -/
def schemeUnitSimplicialIso :
    SingularComplex.simplicial (cosimplicialScheme R) (Scheme.Γ ⋙ ringUnits) ≅
      unitSimplicial R :=
  NatIso.ofComponents (fun n =>
    ringUnits.mapIso (Scheme.ΓSpecIso (.of (CoordinateRing R n.unop.len)))) (by
      intro n m f
      change ringUnits.map _ ≫ ringUnits.map _ = ringUnits.map _ ≫ ringUnits.map _
      rw [← ringUnits.map_comp, ← ringUnits.map_comp]
      exact congrArg ringUnits.map (Scheme.ΓSpecIso_naturality ((simplicialRing R).map f)))

/-- The genuine global-unit singular complex of simplex schemes retracts to units. -/
def schemeUnitChainHomotopyEquiv :
    HomotopyEquiv (SingularComplex.obj (cosimplicialScheme R) (Scheme.Γ ⋙ ringUnits))
      ((ChainComplex.single₀ AddCommGrpCat).obj (AddCommGrpCat.of (Additive Rˣ))) :=
  (HomotopyEquiv.ofIso
    ((alternatingFaceMapComplex AddCommGrpCat).mapIso (schemeUnitSimplicialIso R))).trans
      (unitChainHomotopyEquiv R)

instance schemeUnitChainHomotopyEquiv_quasiIso :
    QuasiIso (schemeUnitChainHomotopyEquiv R).hom :=
  (schemeUnitChainHomotopyEquiv R).quasiIso_hom

/-- Constant pullback is the actual units isomorphism, not an assumed HI property. -/
instance isIso_ringUnits_constant (n : ℕ) :
    IsIso (ringUnits.map (CommRingCat.ofHom (constant R n))) := by
  let e : AddCommGrpCat.of (Additive Rˣ) ≅
      AddCommGrpCat.of (Additive (CoordinateRing R n)ˣ) :=
    (constantUnitsEquiv R n).toAdditive.toAddCommGrpIso
  change IsIso e.hom
  infer_instance

/-- Unit sections on the actual affine simplex are invariant under its projection. -/
instance isIso_units_structureMap (n : ℕ) :
    IsIso (ringUnits.map (structureMap R n).appTop) := by
  have h : (structureMap R n).appTop =
      (Scheme.ΓSpecIso (.of R)).hom ≫ CommRingCat.ofHom (constant R n) ≫
        (Scheme.ΓSpecIso (.of (CoordinateRing R n))).inv := by
    rw [← Scheme.ΓSpecIso_naturality_assoc]
    simp [structureMap]
  rw [h, ringUnits.map_comp, ringUnits.map_comp]
  infer_instance

end AlgebraicSimplex
