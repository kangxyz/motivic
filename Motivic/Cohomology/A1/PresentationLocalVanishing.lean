/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.OneSidedLocalVanishing
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.PresentationMissingBoundary

/-! # Local moving on the genuine missing boundary of the constructed presentation -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open AlgebraicGeometry.Scheme.RelativeCurve
universe u w
namespace AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation
variable {k : Type u} [Field k] {X A : SmoothSite (Spec (.of k))}
  [IsAffine X.left] [IsAffine A.left] {Y Z : Scheme.{u}}
  (p : Y ⟶ X.left) (a : A ⟶ X) [IsOpenImmersion a.left]
  (z : Z ⟶ X.left) [IsClosedImmersion z] (s : Z ⟶ Y) (x : X.left)
  (e : OriginalEtalePresentation k X.hom p a.left z s x)
local instance : IsNoetherianRing e.base := e.base_noetherian
local instance : IsAffine e.target := e.target_affine
local instance : IsOpenImmersion e.refinement := e.refinement_open
local instance : IsFinite e.projectiveMap := e.projective_finite
local instance : IsOpenImmersion e.inclusion := e.inclusion_open
local instance : IsLocallyNoetherian e.compact := e.compact_noetherian
local instance : IsLocallyNoetherian e.target :=
  LocallyOfFiniteType.isLocallyNoetherian e.inclusion
local instance : IsNoetherian e.target := {}
local instance : SmoothOfRelativeDimension 1
    (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) := e.target_smooth
local instance : IsFinite
    (e.closedInclusion ≫ e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) :=
  e.closed_finite

/-- The original section vanishes on an actual open neighborhood inside the constructed
open target. Its target remains the original X, not the small parameter open. -/
theorem exists_zero_on_target_open
    (P : PresheafWithTransfers.{w} k) (hP : P.IsA1Invariant)
    (v : P.sections (Cor.mk X)) (hv : P.transfer ((Cor.graphFunctor k).map a) v = 0) :
    ∃ (O : e.target.Opens) (hO : IsAffineOpen O), e.point ∈ O ∧
      let : IsAffine O.toScheme := hO
      P.transfer ((Cor.graphFunctor k).map
        (SmoothSite.homMk (X := SmoothSite.mk (O.ι ≫ e.refinement ≫ X.hom))
          (Y := X) (O.ι ≫ e.refinement) (by simp))) v = 0 := by
  let T : SmoothSite (Spec (.of k)) := SmoothSite.mk (e.refinement ≫ X.hom)
  let B : SmoothSite (Spec (.of k)) :=
    SmoothSite.mk (pullback.fst a.left e.refinement ≫ A.hom)
  let r : T ⟶ X := SmoothSite.homMk e.refinement rfl
  let j : B ⟶ T := SmoothSite.homMk (pullback.snd a.left e.refinement) (by
    change pullback.snd a.left e.refinement ≫ e.refinement ≫ X.hom =
      pullback.fst a.left e.refinement ≫ A.hom
    rw [← Category.assoc, ← pullback.condition, Category.assoc]
    exact congrArg (fun f => pullback.fst a.left e.refinement ≫ f) a.w)
  let b : B ⟶ A := SmoothSite.homMk (pullback.fst a.left e.refinement) rfl
  have : IsAffine T.left := e.target_affine
  have : IsAffine B.left := inferInstanceAs (IsAffine (pullback a.left e.refinement))
  have : IsClosedImmersion e.closedInclusion :=
    MorphismProperty.of_isPullback e.closed_cartesian inferInstance
  have : IsFinite ((e.closedInclusion ≫ e.inclusion) ≫
      e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) := by
    simpa only [Category.assoc] using e.closed_finite
  have : IsClosedImmersion (e.closedInclusion ≫ e.inclusion) :=
    prescribed_closed_in_compactification e.inclusion
      (e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) e.closedInclusion
  have : IsFinite (e.missingInclusion ≫ e.projectiveMap ≫
      ProjectiveSpace.toSpec e.base _) := e.missing_finite
  have : IsFinite ((coprod.desc e.missingInclusion (e.closedInclusion ≫ e.inclusion) ≫
      e.projectiveMap) ≫ ProjectiveSpace.toSpec e.base _) := by
    rw [Category.assoc, coprod.desc_comp]
    infer_instance
  have hd : Disjoint (Set.range e.inclusion) (Set.range e.missingInclusion) := by
    rw [e.missing_range]
    exact disjoint_compl_right
  have hX : ∀ c, c ∈ Set.range e.inclusion ∨ c ∈ Set.range e.missingInclusion := by
    intro c
    rw [e.missing_range]
    exact Classical.em _
  have hA : ∀ c, c ∈ Set.range (j.left ≫ e.inclusion) ∨
      c ∈ Set.range e.missingInclusion ∨ c ∈ Set.range (e.closedInclusion ≫ e.inclusion) := by
    intro c
    rcases hX c with ⟨y, rfl⟩ | hc
    · rcases e.punctured_cover y with ⟨v, rfl⟩ | ⟨v, rfl⟩
      · exact Or.inl ⟨v, rfl⟩
      · exact Or.inr (Or.inr ⟨v, rfl⟩)
    · exact Or.inr (Or.inl hc)
  have : IsOpenImmersion j.left :=
    inferInstanceAs (IsOpenImmersion (pullback.snd a.left e.refinement))
  have hj : j ≫ r = b ≫ a := by
    apply MorphismProperty.Over.Hom.ext
    exact pullback.condition.symm
  have hv' : P.transfer ((Cor.graphFunctor k).map j)
      (P.transfer ((Cor.graphFunctor k).map r) v) = 0 := by
    have he := ConcreteCategory.congr_hom
      (congrArg P.transfer (congrArg (Cor.graphFunctor k).map hj)) v
    simpa only [Functor.map_comp, PresheafWithTransfers.transfer_comp,
      ConcreteCategory.comp_apply, hv, map_zero] using he
  obtain ⟨O, hO, hxO, hzero⟩ :=
    P.exists_zero_neighborhood_of_curve_presentation (X := T) (A := B)
      e.base (ULift.{u} (Fin 2)) 1 Equiv.ulift e.projectiveMap e.inclusion j
      e.toField e.base_compatibility.symm e.closedInclusion e.missingInclusion
      hd hX hA e.point hP (P.transfer ((Cor.graphFunctor k).map r) v) hv'
  let : IsAffine O.toScheme := hO
  refine ⟨O, hO, hxO, ?_⟩
  let o : SmoothSite.mk (O.ι ≫ T.hom) ⟶ T := SmoothSite.homMk O.ι rfl
  change P.transfer ((Cor.graphFunctor k).map (o ≫ r)) v = 0
  rw [Functor.map_comp, PresheafWithTransfers.transfer_comp]
  exact hzero

end AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation
