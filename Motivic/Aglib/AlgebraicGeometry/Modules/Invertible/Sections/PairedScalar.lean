/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.TensorSectionEvaluation
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.Prescribed.Neighborhood.General

/-! # Original scalar quotients in the actual pulled evaluation pairing

The pairing is retained literally, so no chosen frame or identification of a
pulled dual with a new dual is required.


Intended upstream module: `Aglib.AlgebraicGeometry.Modules.Invertible.Sections.PairedScalar`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Boundary.FunctionalRatio`,
`Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberLocalRatio`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
open scoped TensorProduct
universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- A scalar on the inserted section is the same scalar on its actual paired functional. -/
theorem pairedSectionFunctional_unitEnd (X : Scheme.{u}) {D L : X.Modules}
    (P : tensorSheaf X D L ⟶ SheafOfModules.unit X.ringCatSheaf)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ L)
    (θ : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    pairedSectionFunctional X P (θ ≫ s) = pairedSectionFunctional X P s ≫ θ := by
  ext U x
  change (pairedSectionFunctional X P (θ ≫ s)).val.app (op U) x =
    θ.val.app (op U) ((pairedSectionFunctional X P s).val.app (op U) x)
  rw [pairedSectionFunctional_apply]
  change P.val.app (op U) ((tensorSheafUnit X D L).app (op U)
      (x ⊗ₜ s.val.app (op U) (θ.val.app (op U) (1 : X.presheaf.obj (op U))))) =
    θ.val.app (op U) ((pairedSectionFunctional X P s).val.app (op U) x)
  rw [pairedSectionFunctional_apply]
  let r : X.presheaf.obj (op U) := θ.val.app (op U) (1 : X.presheaf.obj (op U))
  have hs : s.val.app (op U) r = r • s.val.app (op U) (1 : X.presheaf.obj (op U)) := by
    simpa only [smul_eq_mul, mul_one] using
      (s.val.app (op U)).hom.map_smul r (1 : X.presheaf.obj (op U))
  change P.val.app (op U) ((tensorSheafUnit X D L).app (op U) (x ⊗ₜ s.val.app (op U) r)) = _
  rw [hs, TensorProduct.tmul_smul, ((tensorSheafUnit X D L).app (op U)).hom.map_smul,
    (P.val.app (op U)).hom.map_smul]
  let v : X.presheaf.obj (op U) := P.val.app (op U) ((tensorSheafUnit X D L).app (op U)
    (x ⊗ₜ s.val.app (op U) (1 : X.presheaf.obj (op U))))
  have hθ : θ.val.app (op U) v = v * r := by
    simpa only [smul_eq_mul, mul_one] using
      (θ.val.app (op U)).hom.map_smul v (1 : X.presheaf.obj (op U))
  change r * v = θ.val.app (op U) v
  exact (mul_comm r v).trans hθ.symm

/-- The SAME local numerator-over-denominator section quotient satisfies the
original pulled dual-functional equation. Only this actual denominator is inverted. -/
theorem pullback_sectionQuotient_dualFunctional {X W : Scheme.{u}} (f : W ⟶ X)
    (L : LineBundle X)
    (n d : SheafOfModules.unit X.ringCatSheaf ⟶ L.val)
    [IsIso (pullbackSectionMap f d)] :
    pullbackUnitMap f (sectionDualFunctional X L d) ≫
        (pullbackSectionMap f n ≫ inv (pullbackSectionMap f d)) =
      pullbackUnitMap f (sectionDualFunctional X L n) := by
  let θ := pullbackSectionMap f n ≫ inv (pullbackSectionMap f d)
  have h : θ ≫ pullbackSectionMap f d = pullbackSectionMap f n := by
    simp only [θ, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  change Hom.pullbackToUnit (sectionDualFunctional X L d) f ≫ θ =
    Hom.pullbackToUnit (sectionDualFunctional X L n) f
  rw [sectionDualFunctional_pullback, sectionDualFunctional_pullback]
  let P := (PullbackTensor.Local.pullbackLineBundleTensorIso f (dualLineBundle X L) L).inv ≫
    (Modules.pullback f).map (dualEvaluationIso X L).hom ≫ (pullbackUnitIso f).hom
  change pairedSectionFunctional W P (pullbackSectionMap f d) ≫ θ =
    pairedSectionFunctional W P (pullbackSectionMap f n)
  rw [← h, pairedSectionFunctional_unitEnd]

end AlgebraicGeometry.Scheme.Modules.Invertible
