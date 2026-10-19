/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Diagonal.Corestriction
public import Motivic.Cohomology.Diagonal.FieldChange
public import Motivic.Cohomology.WeightTwo.CorestrictionDegree

/-! # Actual diagonal transfer after restriction is field degree in every weight -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped Simplicial
universe u
namespace Motivic.DiagonalCorestriction
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicSimplex
open _root_.Motivic.PresheafWithTransfers
open DiagonalTopDegree
open DiagonalCycleSymbols
open WeightOneBoundaryNorm
variable {k E : Type u} [Field k] [Field E] [Algebra k E] [Module.Finite k E]

/-- Every original signed point cycle has transfer after scalar extension equal to degree. -/
theorem pointPushforward_baseTorusCycleFieldChange (q : ℕ)
    (α : point k ⟶ DiagonalCycleSymbols.target k q) :
    pointPushforward (k := k) (E := E) q
      (baseTorusCycleFieldChange (algebraMap k E) q α) =
        (Module.finrank k E : ℤ) • α := by
  have h := WeightTwoCorestriction.cyclePushforward_fieldBaseChange (E := E) 0 q
    ((zeroProductIso k).hom ≫ α)
  have hz :
      (Cor.graphFunctor E).map
          (SmoothSite.baseSimplexFieldChangeIso (algebraMap k E) ⦋0⦌).inv ≫
        (Cor.fieldBaseChange (algebraMap k E)).map ((zeroProductIso k).hom ≫ α) ≫
          (Cor.graphFunctor E).map
            (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom (algebraMap k E)) q).hom =
        (zeroProductIso E).hom ≫ baseTorusCycleFieldChange (algebraMap k E) q α := by
    apply (cancel_epi (zeroProductIso E).inv).mp
    rw [Functor.map_comp]
    simp only [← Category.assoc,
      WeightOneCohomologyFieldChange.zeroProductIso_fieldChange_inv]
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  rw [hz] at h
  rw [pointPushforward_apply, h, Preadditive.comp_zsmul, Iso.inv_hom_id_assoc]

/-- Transfer after scalar extension is degree multiplication on every original diagonal class. -/
theorem corestriction_fieldChange (q : ℕ) (x : (motivicRawBaseComplex k q).homology q) :
    corestriction (k := k) (E := E) q
      (HomologicalComplex.homologyMap
        (motivicRawBaseComplexMap (algebraMap k E) q) q x) =
      (Module.finrank k E : ℤ) • x := by
  obtain ⟨α, rfl⟩ := DiagonalCycleSymbols.cycleClass_surjective k q x
  rw [DiagonalFieldChange.cycleClass_fieldChange, corestriction_cycleClass,
    pointPushforward_baseTorusCycleFieldChange, map_zsmul]

end Motivic.DiagonalCorestriction
