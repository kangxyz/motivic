/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Sheaf.H1.Descent
public import Motivic.Aglib.AlgebraicGeometry.Sites.Nisnevich.Lifting.ArtinianNeighborhood
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.FiniteSections
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Noetherian
public import Motivic.AlgebraicGeometry.Correspondences.Noetherian

/-! # Actual quotient lifts on étale neighborhoods of Artinian closed subschemes -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Motivic.SheafCohomology
open _root_.AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} [IsNoetherian S]

/-- A section of any epimorphic quotient of ordinary abelian Nisnevich sheaves
lifts on a genuine étale neighborhood of an Artinian closed subscheme. -/
theorem exists_etale_neighborhood_lift
    {I Q : Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1}}
    (φ : I ⟶ Q) [Epi φ] (X : SmoothSite S) (s : Q.obj.obj (op X))
    {Z : Scheme.{u}} (z : Z ⟶ X.left) [IsClosedImmersion z] [IsLocallyArtinian Z] :
    ∃ (Y : SmoothSite S) (p : Y ⟶ X), Etale p.left ∧
      IsIso (pullback.snd p.left z) ∧
      ∃ l : I.obj.obj (op Y), φ.hom.app (op Y) l = Q.obj.map p.op s := by
  let J := SmoothSite.nisnevichTopology S
  have : Sheaf.IsLocallySurjective φ :=
    (Sheaf.isLocallySurjective_iff_epi' (J := J) AddCommGrpCat.{u + 1} φ).mpr inferInstance
  obtain ⟨P, hP, hPQ⟩ := SmoothSite.mem_nisnevichTopology_iff.mp
    (Presheaf.imageSieve_mem J φ.hom s)
  obtain ⟨ι, U, p, rfl⟩ := P.exists_eq_ofArrows
  choose l hl using fun i => hPQ _ _ (Presieve.ofArrows.mk i)
  have hp : Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (p i).left) ∈
      Nisnevich.precoverage X.left := by
    have h := SmoothSite.mem_nisnevichPrecoverage_iff.mp hP
    rw [Presieve.map_ofArrows] at h
    exact h
  let N := SmoothSite.normalizeFiniteNisnevichCoverOfMem p hp
  obtain ⟨t, ht⟩ := SmoothSite.exists_section_finiteCoproduct I
    (fun i ↦ U (N.index i)) (fun i ↦ l (N.index i))
  have hqt : φ.hom.app (op N.total) t = Q.obj.map N.map.op s := by
    have hcover : Sieve.ofArrows _ N.inclusion ∈ J N.total :=
      SmoothSite.mem_nisnevichTopology_iff.mpr
        ⟨_, SmoothSite.finiteCoproductι_mem_nisnevichPrecoverage _, Sieve.le_generate _⟩
    have hsheaf := ((isSheaf_iff_isSheaf_of_type J _).mp
      ((sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj Q).property).isSheafFor
        (Presieve.ofArrows _ N.inclusion) hcover
    apply hsheaf.isSeparatedFor.ext
    rintro W f ⟨i⟩
    change Q.obj.map (N.inclusion i).op (φ.hom.app (op N.total) t) =
      Q.obj.map (N.inclusion i).op (Q.obj.map N.map.op s)
    rw [← φ.hom.naturality_apply, ht, hl,
      ← Functor.map_comp_apply, ← op_comp, N.inclusion_map]
  obtain ⟨W, hW⟩ := SmoothSite.exists_open_iso_over_artinian_closed
    N.map.left N.mem_precoverage z
  let Y : SmoothSite S := SmoothSite.mk (W.ι ≫ N.total.hom)
  let r : Y ⟶ N.total := SmoothSite.homMk W.ι rfl
  refine ⟨Y, r ≫ N.map, ?_, hW, I.obj.map r.op t, ?_⟩
  · change Etale (W.ι ≫ N.map.left)
    infer_instance
  · rw [φ.hom.naturality_apply, hqt, ← Functor.map_comp_apply, ← op_comp]

end Motivic.SheafCohomology
