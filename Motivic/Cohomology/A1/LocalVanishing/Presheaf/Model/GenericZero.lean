/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.LocalVanishing.Presheaf.AffineModelGenericZero
public import Mathlib.Topology.Sheaves.Stalks
/-! # Original generic model germs vanish from actual affine-localization representatives -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial Opposite TopologicalSpace
universe v u
namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme
variable {k : Type u} [Field k]

/-- Affine refinement uses an actual open of the original integral smooth model. -/
theorem exists_model_generic_open_zero
    (P : PresheafWithTransfers.{max v (u + 1)} k) (hP : AffineLocalizationZero P)
    (X : SmoothSite (Spec (.of k))) [IsIntegral X.left] (s : P.sections (Cor.mk X)) :
    ∃ (V : X.left.Opens), genericPoint X.left ∈ V ∧
      P.transfer ((Cor.graphFunctor k).map (SmoothSite.openInclusion X V)) s = 0 := by
  obtain ⟨U, hU, hη, _⟩ := exists_isAffineOpen_mem_and_subset
    (show genericPoint X.left ∈ (⊤ : X.left.Opens) from trivial)
  let A := (SmoothSite.opensFunctor X).obj U
  let : Nonempty U := ⟨⟨genericPoint X.left, hη⟩⟩
  let : IsIntegral A.left := inferInstanceAs (IsIntegral U.toScheme)
  let : IsAffine A.left := hU
  obtain ⟨W, hW, hz⟩ := exists_generic_open_zero_of_affineLocalizationZero P hP A
    (P.transfer ((Cor.graphFunctor k).map (SmoothSite.openInclusion X U)) s)
  let j := W.ι ≫ U.ι
  let V := j.opensRange
  have hV : genericPoint X.left ∈ V := by
    exact ⟨⟨genericPoint A.left, hW⟩, genericPoint_eq_of_isOpenImmersion U.ι⟩
  let t : V.toScheme ⟶ W.toScheme := IsOpenImmersion.lift j V.ι (by
    rw [Scheme.Opens.range_ι]
    exact Set.Subset.rfl)
  have ht : t ≫ j = V.ι := IsOpenImmersion.lift_fac _ _ _
  let b : (SmoothSite.opensFunctor X).obj V ⟶ (SmoothSite.opensFunctor A).obj W :=
    SmoothSite.homMk t (by
      change t ≫ (W.ι ≫ (U.ι ≫ X.hom)) = V.ι ≫ X.hom
      simpa only [j, Category.assoc] using congrArg (fun z => z ≫ X.hom) ht)
  have hb : b ≫ SmoothSite.openInclusion A W ≫ SmoothSite.openInclusion X U =
      SmoothSite.openInclusion X V := by
    apply MorphismProperty.Over.Hom.ext
    exact ht
  refine ⟨V, hV, ?_⟩
  rw [← hb, Functor.map_comp, Functor.map_comp, transfer_comp, transfer_comp,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hz]
  exact map_zero (P.transfer ((Cor.graphFunctor k).map b)).hom

/-- The underlying original graph presheaf on actual opens of the model. -/
def modelOpenPresheaf (P : PresheafWithTransfers.{max v (u + 1)} k)
    (X : SmoothSite (Spec (.of k))) : X.left.carrier.Presheaf AddCommGrpCat.{max v (u + 1)} :=
  (SmoothSite.opensFunctor X).op ⋙ (toPresheaf k).obj P

/-- Every original generic-neighborhood representative dies on a smaller one. -/
theorem exists_smaller_model_generic_open_zero
    (P : PresheafWithTransfers.{max v (u + 1)} k) (hP : AffineLocalizationZero P)
    (X : SmoothSite (Spec (.of k))) [IsIntegral X.left]
    (U : X.left.Opens) (hU : genericPoint X.left ∈ U)
    (s : (modelOpenPresheaf P X).obj (op U)) :
    ∃ (V : X.left.Opens) (_ : genericPoint X.left ∈ V) (hVU : V ≤ U),
      (modelOpenPresheaf P X).map (homOfLE hVU).op s = 0 := by
  let A := (SmoothSite.opensFunctor X).obj U
  let : Nonempty U := ⟨⟨genericPoint X.left, hU⟩⟩
  let : IsIntegral A.left := inferInstanceAs (IsIntegral U.toScheme)
  obtain ⟨W, hW, hz⟩ := exists_model_generic_open_zero P hP A s
  let j := W.ι ≫ U.ι
  let V := j.opensRange
  have hV : genericPoint X.left ∈ V :=
    ⟨⟨genericPoint A.left, hW⟩, genericPoint_eq_of_isOpenImmersion U.ι⟩
  have hVU : V ≤ U := by
    rintro x ⟨y, rfl⟩
    exact (W.ι y).property
  let t : V.toScheme ⟶ W.toScheme := IsOpenImmersion.lift j V.ι (by
    rw [Scheme.Opens.range_ι]
    exact Set.Subset.rfl)
  have ht : t ≫ j = V.ι := IsOpenImmersion.lift_fac _ _ _
  have htU : t ≫ W.ι = X.left.homOfLE hVU := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, ht, Scheme.homOfLE_ι]
  let b : (SmoothSite.opensFunctor X).obj V ⟶ (SmoothSite.opensFunctor A).obj W :=
    SmoothSite.homMk t (by
      change t ≫ (W.ι ≫ (U.ι ≫ X.hom)) = V.ι ≫ X.hom
      rw [← Category.assoc, htU, ← Category.assoc, Scheme.homOfLE_ι])
  have hb : b ≫ SmoothSite.openInclusion A W =
      (SmoothSite.opensFunctor X).map (homOfLE hVU) := by
    apply MorphismProperty.Over.Hom.ext
    exact htU
  refine ⟨V, hV, hVU, ?_⟩
  change P.transfer ((Cor.graphFunctor k).map
    ((SmoothSite.opensFunctor X).map (homOfLE hVU))) s = 0
  rw [← hb, Functor.map_comp, transfer_comp, ConcreteCategory.comp_apply, hz]
  exact map_zero (P.transfer ((Cor.graphFunctor k).map b)).hom

/-- The actual filtered colimit over original generic-point open neighborhoods. -/
def genericModelGerm (P : PresheafWithTransfers.{max v (u + 1)} k)
    (X : SmoothSite (Spec (.of k))) [IsIntegral X.left] : AddCommGrpCat.{max v (u + 1)} :=
  colimit ((OpenNhds.inclusion (genericPoint X.left)).op ⋙ modelOpenPresheaf P X)

/-- The original filtered model colimit is zero, from proved representative-level witnesses. -/
theorem genericModelGerm_eq_zero
    (P : PresheafWithTransfers.{max v (u + 1)} k) (hP : AffineLocalizationZero P)
    (X : SmoothSite (Spec (.of k))) [IsIntegral X.left] (s : genericModelGerm P X) :
    s = 0 := by
  let D := (OpenNhds.inclusion (genericPoint X.left)).op ⋙ modelOpenPresheaf P X
  have hid : 𝟙 (colimit D) = 0 := by
    apply colimit.hom_ext
    intro U
    rw [Category.comp_id, Limits.comp_zero]
    ext e
    obtain ⟨V, hV, hVU, hz⟩ := exists_smaller_model_generic_open_zero
      P hP X U.unop.val U.unop.property e
    let i : (⟨V, hV⟩ : OpenNhds (genericPoint X.left)) ⟶ U.unop := homOfLE hVU
    have h := ConcreteCategory.congr_hom (colimit.w D i.op) e
    change (colimit.ι D (op ⟨V, hV⟩))
      ((modelOpenPresheaf P X).map (homOfLE hVU).op e) = _ at h
    rw [hz, map_zero] at h
    exact h.symm
  exact ConcreteCategory.congr_hom hid s

end Motivic.PresheafWithTransfers
