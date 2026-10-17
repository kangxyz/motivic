/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.AlgebraicSimplexUnits
public import Motivic.AlgebraicGeometry.SmoothSiteUnits
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.Grp.Abelian

/-! # The actual simplex-unit complex retracts to units in degree zero -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite

universe u

namespace Motivic.AlgebraicSimplex

variable (R : Type u) [CommRing R] [IsReduced R]

/-- Units of the original barycentric coordinate rings with their original operators. -/
def unitSimplicial : SimplicialObject AddCommGrpCat.{u} :=
  simplicialRing R ⋙ ringUnits

/-- Constant units identify the actual unit simplicial object with a constant one. -/
def constantUnitSimplicialIso :
    (Functor.const SimplexCategoryᵒᵖ).obj (AddCommGrpCat.of (Additive Rˣ)) ≅
      unitSimplicial R :=
  NatIso.ofComponents (fun n => (constantUnitsEquiv R n.unop.len).toAdditive.toAddCommGrpIso)
    (by
      intro n m f
      ext x
      exact congrArg Additive.ofMul
        (constantUnitsEquiv_pullback R f.unop.toOrderHom x.toMul).symm)

/-- All-degree affine unit chains, not just degree-zero unit sections. -/
def unitChainComplex : ChainComplex AddCommGrpCat.{u} ℕ :=
  (alternatingFaceMapComplex AddCommGrpCat).obj (unitSimplicial R)

/-- A genuine chain homotopy equivalence to the original units in degree zero. -/
def unitChainHomotopyEquiv : HomotopyEquiv (unitChainComplex R)
    ((ChainComplex.single₀ AddCommGrpCat).obj (AddCommGrpCat.of (Additive Rˣ))) :=
  (HomotopyEquiv.ofIso
    ((alternatingFaceMapComplex AddCommGrpCat).mapIso (constantUnitSimplicialIso R).symm)).trans
      (SimplicialObject.Augmented.ExtraDegeneracy.const
        (AddCommGrpCat.of (Additive Rˣ))).homotopyEquiv

/-- The displayed augmentation is a quasi-isomorphism in every degree. -/
instance unitChainHomotopyEquiv_quasiIso : QuasiIso (unitChainHomotopyEquiv R).hom :=
  (unitChainHomotopyEquiv R).quasiIso_hom

end Motivic.AlgebraicSimplex
