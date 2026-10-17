/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.FiniteDomainGenericFiber
public import Motivic.AlgebraicGeometry.Cycles.FiniteAffineChart

/-!
# Actual finite dominant integral-map consumers

The coordinate algebra is that of the whole inverse image of an affine target
open under a genuine finite dominant map of integral schemes. Domain structures,
injectivity and finiteness come from those geometric hypotheses. The resulting
whole residue isomorphism is transported through the actual source open chart;
its scalar square retains the original morphism's residueFieldMap and the
inverse target-stalk chart. This does not construct the future integral
point-closure/image factorization or any exterior tensor-ring comparison.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Motivic.FiniteFiber Motivic.FiniteDomainGenericFiber Motivic.FiniteAffineChart

universe u

namespace MotivicTest.FiniteDomainGenericFiber

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section Chart

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
  {U : Y.Opens} (hU : IsAffineOpen U)

/-- The target chart stalk is transported to a specified, proved coordinate point. -/
def pointedTargetStalkIso (p : Spec Γ(Y, U)) (q : Spec Γ(X, f ⁻¹ᵁ U))
    (hq : coordinateMap f q = p) :
    Y.presheaf.stalk (f (sourceChart f hU q)) ≅ (Spec Γ(Y, U)).presheaf.stalk p :=
  targetStalkIsoAtSource f hU q ≪≫
    (Spec Γ(Y, U)).presheaf.stalkCongr (.of_eq hq)

/-- The coordinate residue square is the actual finite map's residue square. -/
theorem pointed_chart_residue_square (p : Spec Γ(Y, U)) (q : Spec Γ(X, f ⁻¹ᵁ U))
    (hq : coordinateMap f q = p) :
    (pointedTargetStalkIso f hU p q hq).hom ≫ (Spec Γ(Y, U)).residue p ≫
        pointedSpecResidueMap (f.app U) p q hq =
      Y.residue (f (sourceChart f hU q)) ≫ f.residueFieldMap (sourceChart f hU q) ≫
        (sourceChart f hU).residueFieldMap q := by
  subst p
  simp only [pointedTargetStalkIso, Iso.trans_hom,
    TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
    Category.comp_id, pointedSpecResidueMap, Scheme.residueFieldCongr_refl,
    Iso.refl_hom, Category.id_comp]
  calc
    _ = (targetStalkIsoAtSource f hU q).hom ≫
        (coordinateMap f).stalkMap q ≫ (Spec Γ(X, f ⁻¹ᵁ U)).residue q := by
      rw [Scheme.residue_residueFieldMap]
    _ = f.stalkMap (sourceChart f hU q) ≫
        (sourceStalkIso f hU q).hom ≫ (Spec Γ(X, f ⁻¹ᵁ U)).residue q := by
      rw [← stalk_square_at_source_assoc]
    _ = f.stalkMap (sourceChart f hU q) ≫ X.residue (sourceChart f hU q) ≫
        (sourceChart f hU).residueFieldMap q := by
      simpa only [sourceStalkIso, asIso_hom, Category.assoc] using
        congrArg (fun k => f.stalkMap (sourceChart f hU q) ≫ k)
          (Scheme.residue_residueFieldMap (sourceChart f hU) q).symm
    _ = _ := by rw [Scheme.residue_residueFieldMap_assoc]

end Chart

section Integral

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IsDominant f]
  [IsIntegral X] [IsIntegral Y] {U : Y.Opens} [Nonempty U]

/-- A nonempty target open has nonempty whole inverse image under the finite dominant map. -/
instance wholePreimage_nonempty : Nonempty (f ⁻¹ᵁ U) := by
  let : Surjective f := surjective_of_isDominant_of_isClosed_range f
    f.isClosedMap.isClosed_range
  obtain ⟨⟨y, hy⟩⟩ := ‹Nonempty U›
  obtain ⟨x, hx⟩ := f.surjective y
  exact ⟨⟨x, by change f x ∈ U; simpa only [hx] using hy⟩⟩

variable (hU : IsAffineOpen U)

include hU

omit [IsIntegral X] [Nonempty U] in
/-- Injectivity is derived from the original scheme morphism, not added as a field hypothesis. -/
theorem coordinate_injective : Function.Injective (f.app U).hom := by
  have hk : f.ker = ⊥ := by
    rw [← Scheme.IdealSheafData.support_eq_top_iff,
      ← SetLike.coe_injective.eq_iff, TopologicalSpace.Closeds.coe_top,
      ← Set.univ_subset_iff, ← f.denseRange.closure_eq,
      f.ker.support.isClosed.closure_subset_iff]
    exact f.range_subset_ker_support
  rw [RingHom.injective_iff_ker_eq_bot, ← f.ker_apply ⟨U, hU⟩, hk]
  simp

/-- The actual whole generic affine algebra is a field. -/
theorem actualWholeGeneric_isField :
    let := (f.app U).hom.toAlgebra
    IsField (localAlgebra (Γ(Y, U)) (Γ(X, f ⁻¹ᵁ U)) (zeroPrime (Γ(Y, U)))) := by
  let := (f.app U).hom.toAlgebra
  let : Module.Finite (Γ(Y, U)) (Γ(X, f ⁻¹ᵁ U)) := coordinateRingMap_finite f hU
  exact whole_isField (Γ(Y, U)) (Γ(X, f ⁻¹ᵁ U)) (coordinate_injective f hU)

/-- The source chart's actual generic prime maps to the target chart's generic prime. -/
theorem actualGeneric_contraction :
    coordinateMap f (zeroPrime (Γ(X, f ⁻¹ᵁ U))) = zeroPrime (Γ(Y, U)) := by
  let := (f.app U).hom.toAlgebra
  exact zeroPrime_comap (Γ(Y, U)) (Γ(X, f ⁻¹ᵁ U)) (coordinate_injective f hU)

/-- The actual original scheme morphism maps the source chart point to the target chart point. -/
theorem actualGeneric_image :
    f (sourceChart f hU (zeroPrime (Γ(X, f ⁻¹ᵁ U)))) =
      hU.fromSpec (zeroPrime (Γ(Y, U))) := by
  calc
    _ = hU.fromSpec (coordinateMap f (zeroPrime (Γ(X, f ⁻¹ᵁ U)))) :=
      (chart_point f hU (zeroPrime (Γ(X, f ⁻¹ᵁ U)))).symm
    _ = _ := congrArg hU.fromSpec (actualGeneric_contraction f hU)

/-- The whole generic algebra identifies with the original scheme source residue field. -/
def actualWholeGenericResidueIso :
    let := (f.app U).hom.toAlgebra
    CommRingCat.of (localAlgebra (Γ(Y, U)) (Γ(X, f ⁻¹ᵁ U)) (zeroPrime (Γ(Y, U)))) ≅
      X.residueField (sourceChart f hU (zeroPrime (Γ(X, f ⁻¹ᵁ U)))) := by
  let := (f.app U).hom.toAlgebra
  let : Module.Finite (Γ(Y, U)) (Γ(X, f ⁻¹ᵁ U)) := coordinateRingMap_finite f hU
  exact wholeResidueIso (Γ(Y, U)) (Γ(X, f ⁻¹ᵁ U)) (coordinate_injective f hU) ≪≫
    (asIso ((sourceChart f hU).residueFieldMap (zeroPrime (Γ(X, f ⁻¹ᵁ U))))).symm

/-- The actual finite-map scalar square, including the original target-stalk inverse chart. -/
theorem actualWholeGenericResidueIso_base_square :
    let := (f.app U).hom.toAlgebra
    CommRingCat.ofHom (algebraMap (Localization.AtPrime (zeroPrime (Γ(Y, U))).asIdeal)
      (localAlgebra (Γ(Y, U)) (Γ(X, f ⁻¹ᵁ U)) (zeroPrime (Γ(Y, U))))) ≫
        (actualWholeGenericResidueIso f hU).hom =
      (Spec.stalkIso (Γ(Y, U)) (zeroPrime (Γ(Y, U)))).inv ≫
        (pointedTargetStalkIso f hU (zeroPrime (Γ(Y, U))) (zeroPrime (Γ(X, f ⁻¹ᵁ U)))
          (actualGeneric_contraction f hU)).inv ≫
        Y.residue (f (sourceChart f hU (zeroPrime (Γ(X, f ⁻¹ᵁ U))))) ≫
        f.residueFieldMap (sourceChart f hU (zeroPrime (Γ(X, f ⁻¹ᵁ U)))) := by
  let := (f.app U).hom.toAlgebra
  let : Module.Finite (Γ(Y, U)) (Γ(X, f ⁻¹ᵁ U)) := coordinateRingMap_finite f hU
  change _ ≫ ((wholeResidueIso (Γ(Y, U)) (Γ(X, f ⁻¹ᵁ U))
    (coordinate_injective f hU)).hom ≫
    (asIso ((sourceChart f hU).residueFieldMap (zeroPrime (Γ(X, f ⁻¹ᵁ U))))).inv) = _
  rw [← Category.assoc, wholeResidueIso_base_square, Category.assoc]
  have hs := congrArg (fun k =>
      (Spec.stalkIso (Γ(Y, U)) (zeroPrime (Γ(Y, U)))).inv ≫
        (pointedTargetStalkIso f hU (zeroPrime (Γ(Y, U))) (zeroPrime (Γ(X, f ⁻¹ᵁ U)))
          (actualGeneric_contraction f hU)).inv ≫ k ≫
        (asIso ((sourceChart f hU).residueFieldMap (zeroPrime (Γ(X, f ⁻¹ᵁ U))))).inv)
    (pointed_chart_residue_square f hU (zeroPrime (Γ(Y, U))) (zeroPrime (Γ(X, f ⁻¹ᵁ U)))
      (actualGeneric_contraction f hU))
  simpa only [Category.assoc, RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom,
    Iso.inv_hom_id_assoc, asIso_hom, asIso_inv,
    IsIso.hom_inv_id, Category.comp_id] using hs

/-- The source-coordinate action retains the actual germ and inverse residue chart. -/
theorem actualWholeGenericResidueIso_source_square :
    let := (f.app U).hom.toAlgebra
    CommRingCat.ofHom (algebraMap (Γ(X, f ⁻¹ᵁ U))
      (localAlgebra (Γ(Y, U)) (Γ(X, f ⁻¹ᵁ U)) (zeroPrime (Γ(Y, U))))) ≫
        (actualWholeGenericResidueIso f hU).hom =
      (Scheme.ΓSpecIso (Γ(X, f ⁻¹ᵁ U))).inv ≫
        (Spec (Γ(X, f ⁻¹ᵁ U))).presheaf.germ ⊤ (zeroPrime (Γ(X, f ⁻¹ᵁ U))) trivial ≫
        (Spec (Γ(X, f ⁻¹ᵁ U))).residue (zeroPrime (Γ(X, f ⁻¹ᵁ U))) ≫
          (asIso ((sourceChart f hU).residueFieldMap (zeroPrime (Γ(X, f ⁻¹ᵁ U))))).inv := by
  let := (f.app U).hom.toAlgebra
  let : Module.Finite (Γ(Y, U)) (Γ(X, f ⁻¹ᵁ U)) := coordinateRingMap_finite f hU
  change _ ≫ ((wholeResidueIso (Γ(Y, U)) (Γ(X, f ⁻¹ᵁ U))
    (coordinate_injective f hU)).hom ≫ _) = _
  rw [← Category.assoc, wholeResidueIso_source_square]
  simp only [Category.assoc, Iso.symm_hom]

end Integral

end MotivicTest.FiniteDomainGenericFiber
