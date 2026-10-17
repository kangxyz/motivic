/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleMarkedResidueGerms

/-! # Conservative detection by all original marked residue-point fibers -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite
variable {S : Scheme.{u}}

/-- All marked germs of a section vanish only if the original section vanishes.
The cover consists of actual small-site arrows into the original test object. -/
theorem section_eq_zero_of_marked_residue_germs
    (G : Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1})
    (V : FiniteEtaleSite S) (s : G.obj.obj (op V))
    (hs : ∀ z : V.left, markedSectionGerm G.obj V z s = 0) : s = 0 := by
  classical
  choose W f y hy hi hz using fun z => exists_marked_zero_neighborhood G.obj V z s (hs z)
  have hpre : Presieve.ofArrows W f ∈ nisnevichPrecoverage S V := by
    apply (ofArrows_mem_nisnevichPrecoverage_iff f).mpr
    refine ⟨?_, fun z => ⟨z, y z, hy z, hi z⟩⟩
    intro z
    have : Etale ((f z).left ≫ V.hom) := by
      rw [MorphismProperty.Over.w]
      infer_instance
    exact Etale.of_comp (f z).left V.hom
  have hcov : Sieve.ofArrows W f ∈ nisnevichTopology S V :=
    Precoverage.generate_mem_toGrothendieck hpre
  have hsheaf := ((isSheaf_iff_isSheaf_of_type (nisnevichTopology S) _).mp
    ((sheafCompose (nisnevichTopology S)
      (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G).property).isSheafFor
        (Presieve.ofArrows W f) hcov
  apply hsheaf.isSeparatedFor.ext
  rintro B a ⟨z⟩
  change G.obj.map (f z).op s = G.obj.map (f z).op 0
  rw [hz, map_zero]

/-- These fibers are conservative because they include every point of every test object,
not merely the canonical residue points of the base scheme. -/
theorem isZero_of_all_marked_residue_fibers
    (G : Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1})
    (h : ∀ (V : FiniteEtaleSite S) (z : V.left),
      IsZero ((markedResiduePoint V z).sheafFiber.obj G)) : IsZero G := by
  apply (IsZero.iff_id_eq_zero G).mpr
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  ext s
  change s = 0
  apply section_eq_zero_of_marked_residue_germs G V.unop s
  intro z
  have ht := ConcreteCategory.congr_hom
    ((IsZero.iff_id_eq_zero _).mp (h V.unop z)) (markedSectionGerm G.obj V.unop z s)
  exact ht

end Motivic.FiniteEtaleSite
