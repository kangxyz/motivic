/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Point.Sections
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Point.CommonRefinement

/-!
# Section detection by smooth-site germs
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Opposite AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite
variable {S : Scheme.{u}} [IsAffine S]
  (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
  (hF : Presheaf.IsSheaf (nisnevichTopology S) F) (X : SmoothSite S)
include hF

/-- A section with zero original germ at every scheme point is zero, by an actual
Nisnevich family of its vanishing pointed neighborhoods. -/
theorem section_eq_zero_of_original_germs (s : F.obj (op X))
    (hs : ∀ x : X.left, sectionToNisnevichPoint.{u, 0} F X x s = 0) : s = 0 := by
  classical
  choose N hN using fun x =>
    (sectionToNisnevichPoint_eq_zero_iff.{u, 0} F (X := X) (x := x) s).mp (hs x)
  let V := fun x => (nisnevichNeighborhoodFunctor X x).obj (N x)
  let q : ∀ x, V x ⟶ X := fun x => (N x).toBase
  have hq : Presieve.ofArrows V q ∈ nisnevichPrecoverage S X := by
    rw [ofArrows_mem_nisnevichPrecoverage_iff]
    exact ⟨fun _ => inferInstance, fun x =>
      ⟨x, (N x).center, (N x).toBase_center, inferInstance⟩⟩
  have hc : Sieve.ofArrows V q ∈ nisnevichTopology S X :=
    mem_nisnevichTopology_iff.mpr ⟨_, hq, Sieve.le_generate _⟩
  let e : AddCommGrpCat.of (ULift.{u + 1} ℤ) ⟶ F.obj (op X) :=
    AddCommGrpCat.ofHom
      { toFun := fun m => m.down • s
        map_zero' := zero_zsmul s
        map_add' := fun m n => add_zsmul s m.down n.down }
  have he : e = 0 := hF.hom_ext_ofArrows q hc (by
    intro x
    ext m
    change F.map (q x).op (m.down • s) = F.map (q x).op 0
    rw [map_zsmul, hN x, smul_zero, map_zero])
  have h := ConcreteCategory.congr_hom he (ULift.up (1 : ℤ))
  change (1 : ℤ) • s = 0 at h
  simpa only [one_zsmul] using h

/-- Equality of all original point germs detects equality of actual sections. -/
theorem original_germ_tuple_injective :
    Function.Injective (fun s : F.obj (op X) =>
      fun x : X.left => sectionToNisnevichPoint.{u, 0} F X x s) := by
  intro s t h
  apply sub_eq_zero.mp
  apply section_eq_zero_of_original_germs F hF X (s - t)
  intro x
  simpa only [map_sub, sub_eq_zero] using congrFun h x

end AlgebraicGeometry.Scheme.SmoothSite
