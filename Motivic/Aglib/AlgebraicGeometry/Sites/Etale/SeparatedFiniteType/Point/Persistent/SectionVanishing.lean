/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.OpenZeroFamily

/-! # Persistent point detection for arbitrary ordinary small-Nis sheaves -/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite Topology
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

/-- Vanishing of the original residue-point germs at all points persistent near
`x` kills an arbitrary small-Nis sheaf section after an actual base-open shrink.
No extension to the big site or inverse-image coefficient comparison is assumed. -/
theorem exists_open_restriction_eq_zero_of_persistent_residue_germs
    {U X : Scheme.{u}} [IsNoetherian U] (g : U ⟶ X) (x : X)
    (G : Sheaf (nisnevichTopology U) AddCommGrpCat.{u + 1})
    (s : G.obj.obj (op (baseObject U)))
    (hs : ∀ z : U, g z ⤳ x → sectionResidueGerm G.obj z s = 0) :
    ∃ W : X.Opens, x ∈ W ∧
      G.obj.map (toBaseObject (openObject (g ⁻¹ᵁ W))).op s = 0 := by
  classical
  let I := {z : U // g z ⤳ x}
  have hn (i : I) := exists_residue_splitting_zero_neighborhood G.obj i.val s
    (hs i.val i.property)
  choose V y hy hi hz using hn
  have hf : ∀ z : U, g z ⤳ x → ∃ (i : I) (a : (V i).left),
      (V i).hom a = z ∧ IsIso ((V i).hom.residueFieldMap a) := by
    intro z h
    exact ⟨⟨z, h⟩, y ⟨z, h⟩, hy ⟨z, h⟩, hi ⟨z, h⟩⟩
  obtain ⟨W, hx, t, ht⟩ :=
    Nisnevich.exists_open_finset_persistent_residueFieldLifting g x
      (fun i => (V i).hom) hf
  refine ⟨W, hx, open_restriction_eq_zero_of_residue_splitting_family G s
    (g ⁻¹ᵁ W) V hz ?_⟩
  intro z h
  obtain ⟨i, _, a, ha, hi⟩ := ht z h
  exact ⟨i, a, ha, hi⟩

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
