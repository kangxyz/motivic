/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Etale.Sections.ArtinianEtaleSections
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Etale.Neighborhood.EtaleNeighborhoodFromClosedSection
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.FiniteCovers

/-! # An actual étale neighborhood of an Artinian closed subscheme -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite
open _root_.AlgebraicGeometry.Scheme.Hom

/-- A singleton Nisnevich cover has an open refinement isomorphic over any
locally Artinian closed subscheme. The isomorphism is scheme-theoretic. -/
theorem exists_open_iso_over_artinian_closed
    {X Y Z : Scheme.{u}} (p : Y ⟶ X) [Etale p]
    (hp : Presieve.singleton p ∈ Nisnevich.precoverage X)
    (z : Z ⟶ X) [IsClosedImmersion z] [IsLocallyArtinian Z] :
    ∃ W : Y.Opens, IsIso (pullback.snd (W.ι ≫ p) z) := by
  have h : ∀ c : Z, ∃ a : Spec (Z.residueField c) ⟶ pullback p z,
      a ≫ pullback.snd p z = Z.fromSpecResidueField c := by
    intro c
    obtain ⟨_, _, hf, b, hb⟩ := Nisnevich.mem_fieldLiftingPrecoverage_iff.mp hp.2
      (Z.residueField c) (Z.fromSpecResidueField c ≫ z)
    cases hf
    exact ⟨pullback.lift b (Z.fromSpecResidueField c) hb, pullback.lift_snd _ _ _⟩
  obtain ⟨s, hs⟩ := ArtinianEtale.exists_section_of_etale_of_isLocallyArtinian
    (pullback.snd p z) h
  exact Scheme.Hom.exists_open_iso_over_closed_of_section p z s hs

end AlgebraicGeometry.Scheme.SmoothSite
