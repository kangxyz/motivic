/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.GenericallyEtale
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.FiniteChart.CompactificationChart

/-! # The entire original finite chart is retained in its generic normalization -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
universe u
namespace AlgebraicGeometry.Scheme.GenericallyEtaleCompactification
variable (X Y : Scheme.{u}) [IsIntegral X] [IsIntegral Y]
  [∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)]
  (f : Y ⟶ X) [IsDominant f] [QuasiCompact f] [QuasiSeparated f]
  [IsFinite (Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap f)))]

/-- The original open source contains every point over an integral chart. -/
theorem mem_range_inclusion_of_integral_chart (U : X.Opens)
    [IsIntegralHom (pullback.snd f U.ι)]
    (x : (genericMap X Y f).normalization)
    (hx : (genericMap X Y f).fromNormalization x ∈ U) :
    x ∈ Set.range (inclusion X Y f) := by
  let e := normalizationIso X Y f
  have ho : e.inv ≫ f.fromNormalization = (genericMap X Y f).fromNormalization := by
    rw [← normalizationIso_hom_over X Y f]
    simp only [e, Iso.inv_hom_id_assoc]
  have hx' : f.fromNormalization (e.inv x) ∈ U := by
    simpa only [← Scheme.Hom.comp_apply, ho] using hx
  obtain ⟨y, hy⟩ := f.mem_range_toNormalization_of_integral_chart U (e.inv x) hx'
  refine ⟨y, ?_⟩
  have he : f.toNormalization ≫ e.hom = inclusion X Y f := by simp [e, normalizationIso]
  have hpoint := congrArg (fun z => e.hom z) hy
  simp only [← Scheme.Hom.comp_apply, he, Iso.inv_hom_id] at hpoint
  exact hpoint

end AlgebraicGeometry.Scheme.GenericallyEtaleCompactification
