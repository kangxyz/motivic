/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSiteNisnevich
public import Mathlib.CategoryTheory.Sites.SheafOfTypes
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Algebra.Category.Grp.Limits

/-! # Section detection by actual smooth Nisnevich families -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u v

namespace Motivic.SmoothSite

/-- A section of an ordinary abelian Nisnevich sheaf vanishes if its original
restrictions vanish on an étale family splitting every residue field. -/
theorem section_eq_zero_of_residue_splitting_family {S : Scheme.{u}}
    (G : Sheaf (nisnevichTopology S) AddCommGrpCat.{v})
    {X : SmoothSite S} {ι : Type*} (Y : ι → SmoothSite S)
    (f : ∀ i, Y i ⟶ X) (hf : ∀ i, Etale (f i).left)
    (hcover : ∀ x : X.left, ∃ (i : ι) (y : (Y i).left),
      (f i).left y = x ∧ IsIso ((f i).left.residueFieldMap y))
    (s : G.obj.obj (op X)) (hzero : ∀ i, G.obj.map (f i).op s = 0) :
    s = 0 := by
  have hpre : Presieve.ofArrows Y f ∈ nisnevichPrecoverage S X :=
    (ofArrows_mem_nisnevichPrecoverage_iff f).mpr ⟨hf, hcover⟩
  have hcov : Sieve.ofArrows Y f ∈ nisnevichTopology S X :=
    Precoverage.generate_mem_toGrothendieck hpre
  have hsheaf := ((isSheaf_iff_isSheaf_of_type (nisnevichTopology S) _).mp
    ((sheafCompose (nisnevichTopology S)
      (CategoryTheory.forget AddCommGrpCat.{v})).obj G).property).isSheafFor
        (Presieve.ofArrows Y f) hcov
  apply hsheaf.isSeparatedFor.ext
  rintro Z g ⟨i⟩
  change G.obj.map (f i).op s = G.obj.map (f i).op 0
  rw [hzero, map_zero]

end Motivic.SmoothSite
