/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.SheafCohomologyGenericOpen
public import Mathlib.Topology.Sheaves.Stalks

/-! # Actual filtered generic germs of positive ordinary cohomology vanish -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
universe w u
namespace Motivic.SheafCohomology
variable {S : Scheme.{u}} [IsNoetherian S]
  [HasExt.{max w (u + 1)} (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})]

/-- The original cohomology presheaf restricted to actual Zariski opens. -/
def modelOpenPresheaf
    (F : Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})
    (n : ℕ) (X : SmoothSite S) : X.left.carrier.Presheaf AddCommGrpCat.{max w (u + 1)} :=
  (SmoothSite.opensFunctor X).op ⋙
    presheaf.{max w (u + 1), u + 1, u, u + 1} (SmoothSite.nisnevichTopology S) F n

/-- Each representative on a generic neighborhood dies on a smaller generic neighborhood. -/
theorem exists_smaller_generic_open_restriction_eq_zero
    (F : Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})
    (n : ℕ) (X : SmoothSite S) [IsIntegral X.left]
    (U : X.left.Opens) (hU : genericPoint X.left ∈ U)
    (e : (modelOpenPresheaf.{w, u} F (n + 1) X).obj (op U)) :
    ∃ (V : X.left.Opens) (_hV : genericPoint X.left ∈ V) (hVU : V ≤ U),
      (modelOpenPresheaf.{w, u} F (n + 1) X).map (homOfLE hVU).op e = 0 := by
  let A := (SmoothSite.opensFunctor X).obj U
  have : Nonempty U := ⟨⟨genericPoint X.left, hU⟩⟩
  have : IsIntegral A.left := inferInstanceAs (IsIntegral U.toScheme)
  obtain ⟨W, hW, he⟩ := exists_generic_open_restriction_eq_zero.{max w (u + 1), u} F n A e
  let j : W.toScheme ⟶ X.left := W.ι ≫ U.ι
  let V : X.left.Opens := j.opensRange
  have hV : genericPoint X.left ∈ V := by
    change genericPoint X.left ∈ Set.range j
    refine ⟨⟨genericPoint A.left, hW⟩, ?_⟩
    exact genericPoint_eq_of_isOpenImmersion U.ι
  have hVU : V ≤ U := by
    intro x hx
    obtain ⟨y, rfl⟩ := hx
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
  change (presheaf.{max w (u + 1), u + 1, u, u + 1} (SmoothSite.nisnevichTopology S) F (n + 1)).map
    ((SmoothSite.opensFunctor X).map (homOfLE hVU)).op e = 0
  rw [← hb, op_comp, Functor.map_comp, ConcreteCategory.comp_apply, he, map_zero]

/-- This is the actual filtered colimit over all generic open neighborhoods, not
cohomology of a function-field object or a henselization inserted into the site. -/
def genericGerm
    (F : Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})
    (n : ℕ) (X : SmoothSite S) [IsIntegral X.left] : AddCommGrpCat.{max w (u + 1)} :=
  colimit ((OpenNhds.inclusion (genericPoint X.left)).op ⋙ modelOpenPresheaf.{w, u} F n X)

/-- Every actual positive-degree generic filtered germ is zero. -/
theorem genericGerm_succ_eq_zero
    (F : Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})
    (n : ℕ) (X : SmoothSite S) [IsIntegral X.left]
    (e : genericGerm.{w, u} F (n + 1) X) : e = 0 := by
  let D := (OpenNhds.inclusion (genericPoint X.left)).op ⋙
    modelOpenPresheaf.{w, u} F (n + 1) X
  have hid : 𝟙 (colimit D) = 0 := by
    apply colimit.hom_ext
    intro U
    rw [Category.comp_id, comp_zero]
    ext s
    obtain ⟨V, hV, hVU, hz⟩ := exists_smaller_generic_open_restriction_eq_zero.{w, u}
      F n X U.unop.val U.unop.property s
    let i : (⟨V, hV⟩ : OpenNhds (genericPoint X.left)) ⟶ U.unop := homOfLE hVU
    have h := ConcreteCategory.congr_hom (colimit.w D i.op) s
    change (colimit.ι D (op ⟨V, hV⟩))
        ((modelOpenPresheaf.{w, u} F (n + 1) X).map (homOfLE hVU).op s) = _ at h
    rw [hz, map_zero] at h
    exact h.symm
  exact ConcreteCategory.congr_hom hid e

end Motivic.SheafCohomology
