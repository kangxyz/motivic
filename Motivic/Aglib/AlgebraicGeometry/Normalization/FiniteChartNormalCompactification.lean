/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.GenericallyEtaleCompactification
public import Motivic.Aglib.AlgebraicGeometry.Normalization.FunctionFieldOpenComposition
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.Stalks
public import Motivic.Aglib.AlgebraicGeometry.Normalization.GenericallyEtaleFiniteChart
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Normality

/-! # One actual normal finite compactification from the original finite coordinate chart -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace
universe u
namespace AlgebraicGeometry.Scheme

/-- The original smooth source embeds into one normal finite cover of the fixed
compact target. Generic separability is derived from its actual étale neighborhood. -/
theorem exists_normal_finite_cover_of_finite_chart
    (k : Type u) [Field k] {X Y Z : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z] [IsLocallyNoetherian Z]
    [∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z)]
    (f : X ⟶ Y) [IsFinite f] (j : Y ⟶ Z) [IsOpenImmersion j] [QuasiCompact j]
    (p : X ⟶ Spec (.of k)) [Smooth p]
    (U : X.Opens) (hU : (U : Set X).Nonempty) [Etale (U.ι ≫ f)] :
    ∃ (N : Scheme.{u}) (i : X ⟶ N) (π : N ⟶ Z),
      IsIntegral N ∧ IsLocallyNoetherian N ∧
      (∀ n : N, IsIntegrallyClosed (N.presheaf.stalk n)) ∧
      IsOpenImmersion i ∧ IsFinite π ∧ i ≫ π = f ≫ j ∧
      Set.range i = π ⁻¹' Set.range j := by
  have : IsDominant f := isDominant_of_nonempty_etale_open f U hU
  have : IsDominant j := ⟨j.isOpenMap.denseRange_of_isPreirreducibleSpace _⟩
  have (x : X) : IsIntegrallyClosed (X.presheaf.stalk x) :=
    (smoothFieldNormality k X p inferInstance x).2
  have : IsFinite (Spec.map (CommRingCat.ofHom (functionFieldMap f))) :=
    finite_functionFieldMap f
  have : Etale (Spec.map (CommRingCat.ofHom (functionFieldMap f))) :=
    etale_functionFieldMap_of_etale_open f U
      (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hU))
  obtain ⟨hfinite, hetale⟩ := finite_etale_functionFieldSpecMap_comp_open f j
  have := hfinite
  have := hetale
  let g := GenericallyEtaleCompactification.genericMap Z X (f ≫ j)
  have : IsFinite g.fromNormalization := inferInstance
  have : IsLocallyNoetherian g.normalization :=
    LocallyOfFiniteType.isLocallyNoetherian g.fromNormalization
  refine ⟨g.normalization, GenericallyEtaleCompactification.inclusion Z X (f ≫ j),
    g.fromNormalization, inferInstance, inferInstance, ?_, inferInstance, inferInstance, ?_, ?_⟩
  · intro n
    exact (FiniteEtale.GenericNormalization.stalk_normal_domain Z
      (GenericallyEtaleCompactification.genericCover Z X (f ≫ j)) n).1
  · exact GenericallyEtaleCompactification.inclusion_over Z X (f ≫ j)
  · have := finite_comp_pullback_open_image f j ⊤
    ext n
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨f x, (congrArg (fun t => t x)
        (GenericallyEtaleCompactification.inclusion_over Z X (f ≫ j))).symm⟩
    · intro hn
      apply GenericallyEtaleCompactification.mem_range_inclusion_of_integral_chart
        Z X (f ≫ j) (j ''ᵁ ⊤) n
      obtain ⟨y, hy⟩ := hn
      exact ⟨y, trivial, hy⟩

end AlgebraicGeometry.Scheme
