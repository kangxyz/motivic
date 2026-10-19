/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Sheaf.H1.Descent
public import Mathlib.AlgebraicGeometry.SpreadingOut
public import Mathlib.AlgebraicGeometry.FunctionField

/-!
# A generic open lift of an actual ordinary H¹ representative

For an integral smooth-site object over an affine base, the quotient section
representing an ordinary H¹ class lifts on an affine open containing the generic
point. A field-valued lift of the generic stalk is spread out as a scheme map,
and the actual section on the covering object is restricted along that map.
The generic field spectrum is never treated as a smooth finite-type site object.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w u

namespace Motivic.SheafCohomology
open _root_.AlgebraicGeometry.Scheme _root_.CategoryTheory.Sheaf.LargeCohomology

variable {S : Scheme.{u}} [IsAffine S]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})]
  [EnoughInjectives (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})]

/-- An actual H¹ class admits its original injective-quotient representative
and a genuine lift of that section on a smooth affine open containing the
generic point. The open and its inclusion are constructed, not assumed. -/
theorem exists_generic_affine_open_lift_of_h_one
    (F : Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})
    (X : SmoothSite S) [IsIntegral X.left]
    (x : H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology S) F 1 X) :
    ∃ (s : (cokernel (Injective.ι F)).obj.obj (op X)),
      injectiveSectionBoundary (SmoothSite.nisnevichTopology S) F X s = x ∧
    ∃ (A : SmoothSite S) (j : A ⟶ X), IsAffine A.left ∧ IsOpenImmersion j.left ∧
      genericPoint X.left ∈ Set.range j.left ∧
    ∃ l : (Injective.under F).obj.obj (op A),
      (cokernel.π (Injective.ι F)).hom.app (op A) l =
        (cokernel (Injective.ι F)).obj.map j.op s := by
  obtain ⟨s, hs, ι, U, p, hp, l, hl⟩ := exists_nisnevich_local_lifts_of_h_one F X x
  have hp' : Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (p i).left) ∈
      Nisnevich.precoverage X.left := by
    have h := SmoothSite.mem_nisnevichPrecoverage_iff.mp hp
    rw [Presieve.map_ofArrows] at h
    exact h
  obtain ⟨_, _, ⟨i⟩, g, hg⟩ := Nisnevich.mem_fieldLiftingPrecoverage_iff.mp hp'.2
    X.left.functionField (X.left.fromSpecStalk (genericPoint X.left))
  have : Etale (p i).left :=
    (SmoothSite.ofArrows_mem_nisnevichPrecoverage_iff p).mp hp |>.1 i
  obtain ⟨W, hηW, t, _, ht⟩ := spread_out_of_isGermInjective' (𝟙 X.left)
    (p i).left g (by simpa using hg)
  obtain ⟨R, j, hj, hηj, hjW⟩ := Scheme.exists_affine_mem_range_and_range_subset hηW
  let a : Spec R ⟶ W.toScheme := IsOpenImmersion.lift W.ι j (by
    simpa only [Scheme.Opens.range_ι] using hjW)
  have ha : a ≫ W.ι = j := IsOpenImmersion.lift_fac W.ι j _
  have hat : (a ≫ t) ≫ (p i).left = j := by
    rw [Category.assoc, ht, Category.comp_id, ha]
  let A : SmoothSite S := SmoothSite.mk (j ≫ X.hom)
  let j' : A ⟶ X := SmoothSite.homMk j rfl
  let b : A ⟶ U i := SmoothSite.homMk (a ≫ t) (by
    change (a ≫ t) ≫ (U i).hom = j ≫ X.hom
    rw [← MorphismProperty.Over.w (p i), ← Category.assoc, hat])
  have hb : b ≫ p i = j' := by
    apply MorphismProperty.Over.Hom.ext
    exact hat
  refine ⟨s, hs, A, j', inferInstanceAs (IsAffine (Spec R)), hj, hηj,
    (Injective.under F).obj.map b.op (l i), ?_⟩
  rw [(cokernel.π (Injective.ι F)).hom.naturality_apply, hl,
    ← Functor.map_comp_apply, ← op_comp, hb]

end Motivic.SheafCohomology
