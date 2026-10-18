/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.ContractionBoundaryLocalKernel
public import Motivic.AlgebraicGeometry.SmoothSiteSectionDetection
public import Motivic.Aglib.AlgebraicGeometry.ResidueFieldLiftIsomorphism

/-! # Monicity of the canonical boundary map for homotopy-invariant sheaves -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite
variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)

/-- The actual canonical zero-section boundary detects the original contraction
section. Residue-splitting local cylinder extensions are glued using separatedness
of the original contraction sheaf, without generic detection or supplied purity. -/
theorem contractionToBoundary_eq_zero
    (V : FiniteEtaleSite X.left)
    (c : (((toSmoothSite X).op ⋙ (PresheafWithTransfers.toPresheaf k).obj
      (PresheafWithTransfers.contraction F.obj)).obj (op V)))
    (hc : (contractionToBoundary X F hF).hom.app (op V) c = 0) : c = 0 := by
  classical
  let Y := (toSmoothSite X).obj V
  let G := (SheafWithTransfers.toSheaf k).obj (SheafWithTransfers.contraction F hF)
  obtain ⟨s, rfl⟩ := PresheafWithTransfers.toContraction_surjective F.obj (Cor.mk Y) c
  have hs : (ambientCokernelToBoundary X F).app (op V)
      ((laurentToAmbientCokernel X F).app (op V) s) = 0 := by
    have h := ConcreteCategory.congr_hom (congr_app
      (toContraction_contractionToBoundaryPresheaf X F) (op V)) s
    exact h.symm.trans hc
  have hlocal (v : V.left) : ∃ (W : FiniteEtaleSite V.left) (y : W.left),
      W.hom y = v ∧ IsIso (W.hom.residueFieldMap y) ∧
      G.obj.map (toBase Y W).op ((PresheafWithTransfers.toContraction F.obj).hom.app
        (op (Cor.mk Y)) s) = 0 := by
    obtain ⟨W, cW, hcW, t, ht⟩ :=
      exists_marked_cylinder_extension_of_boundary_zero X F V v s hs
    refine ⟨W, cW default, ?_,
      W.hom.isIso_residueFieldMap_of_canonicalPoint_lift v cW hcW, ?_⟩
    · exact (congrArg (fun f => f default) hcW).trans
        (V.left.fromSpecResidueField_apply v default)
    · change PresheafWithTransfers.transfer (PresheafWithTransfers.contraction F.obj)
          ((Cor.graphFunctor k).map (toBase Y W))
          ((PresheafWithTransfers.toContraction F.obj).hom.app (op (Cor.mk Y)) s) = 0
      rw [PresheafWithTransfers.contraction_graph_apply]
      change (PresheafWithTransfers.toContraction F.obj).hom.app
          (op (Cor.mk ((toSmoothSite Y).obj W)))
          (((SheafWithTransfers.toSheaf k).obj F).obj.map
            (SmoothSite.productMap (toBase Y W) (𝟙 (SmoothSite.torus (.of k)))).op s) = 0
      rw [← ht]
      exact ConcreteCategory.congr_hom (congr_app (congrArg (fun f => f.hom)
        (PresheafWithTransfers.contractionRestriction_toContraction F.obj))
          (op (Cor.mk ((toSmoothSite Y).obj W)))) t
  choose W y hy hi hz using hlocal
  exact SmoothSite.section_eq_zero_of_residue_splitting_family G
    (fun v => (toSmoothSite Y).obj (W v)) (fun v => toBase Y (W v))
    (fun v => inferInstanceAs (Etale (W v).hom))
    (fun v => ⟨v, y v, hy v, hi v⟩) _ hz

/-- The canonical map from the unchanged contraction sheaf to the genuine closed
inverse-image boundary is monic over every field. Only ordinary HI is assumed. -/
theorem contractionToBoundary_mono : Mono (contractionToBoundary X F hF) := by
  apply (sheafToPresheaf _ _).mono_of_mono_map
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro V
  apply (AddCommGrpCat.mono_iff_injective _).mpr
  apply (injective_iff_map_eq_zero _).mpr
  exact contractionToBoundary_eq_zero X F hF V.unop

end Motivic.FiniteEtaleSite
