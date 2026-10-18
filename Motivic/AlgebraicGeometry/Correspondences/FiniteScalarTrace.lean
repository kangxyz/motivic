/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.FlatSpanBaseChange
public import Motivic.AlgebraicGeometry.Correspondences.DiagonalZeroCycle
public import Motivic.Aglib.AlgebraicGeometry.FiniteScalarFundamentalCycle
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Etale.Field

/-!
# Actual finite scalar traces

The trace is the whole finite-flat span, not an additional action supplied on
coefficients. Cartesian flat restriction retains all components and lengths.
The scalar degree identity is on the original ground-field object only.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.Cor

variable {k : Type u} [Field k]

/-- Transpose of an actual finite-flat map between smooth objects. -/
def finiteFlatTrace {X Y : SmoothSite (Spec (.of k))} (p : Y ⟶ X)
    [IsFinite p.left] [Flat p.left] : Cor.mk X ⟶ Cor.mk Y :=
  ofFiniteFlatSpan p.left (𝟙 Y.left) (by simp [MorphismProperty.Over.w p])

/-- Cartesian flat restriction commutes with the original whole-support trace.
In particular this applies to open restrictions. -/
theorem finiteFlatTrace_cartesian {X Y U V : SmoothSite (Spec (.of k))}
    (p : Y ⟶ X) [IsFinite p.left] [Flat p.left]
    (q : V ⟶ U) [IsFinite q.left] [Flat q.left]
    (j : U ⟶ X) [Flat j.left] (i : V ⟶ Y)
    (sq : IsPullback q.left i.left j.left p.left) :
    finiteFlatTrace q ≫ (graphFunctor k).map i =
      (graphFunctor k).map j ≫ finiteFlatTrace p := by
  have hc : IsClosedImmersion
      (pullback.lift (f := X.hom) (g := Y.hom) p.left (𝟙 Y.left)
        (by simp [MorphismProperty.Over.w p])) := by
    have : IsClosedImmersion
        (pullback.lift (f := X.hom) (g := Y.hom) p.left (𝟙 Y.left)
          (by simp [MorphismProperty.Over.w p]) ≫
          pullback.snd X.hom Y.hom) := by
      rw [pullback.lift_snd]
      infer_instance
    exact IsClosedImmersion.of_comp _ (pullback.snd X.hom Y.hom)
  rw [finiteFlatTrace, finiteFlatTrace, ofFiniteFlatSpan_comp_graph,
    graph_ofFiniteFlatSpan_of_flat]
  have h := GlobalBoundaryPencil.ofFiniteFlatSpan_precompIso
    (X := U) (Y := Y) sq.isoPullback (pullback.fst j.left p.left)
    (pullback.snd j.left p.left)
    (by rw [← MorphismProperty.Over.w j, ← Category.assoc, pullback.condition,
      Category.assoc, MorphismProperty.Over.w p])
  simp only [sq.isoPullback_hom_fst, sq.isoPullback_hom_snd] at h
  simpa only [Category.id_comp, Category.comp_id, graphFunctor_obj] using h

end Motivic.Cor

namespace Motivic.SmoothSite

variable {k E : Type u} [Field k] [Field E] [Algebra k E]
  [Module.Finite k E] [Algebra.IsSeparable k E]

local instance : Algebra.FormallyEtale k E := Algebra.FormallyEtale.of_isSeparable k E
local instance : Algebra.Etale k E :=
  ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
local instance : Etale (Spec.map (CommRingCat.ofHom (algebraMap k E))) :=
  HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
local instance : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k E))) :=
  (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

/-- A finite separable scalar extension, viewed over its original ground field. -/
def finiteScalarExtension (X : SmoothSite (Spec (.of k))) :
    SmoothSite (Spec (.of k)) :=
  mk (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k E))) ≫ X.hom)

/-- The literal finite scalar projection, as a morphism over the ground field. -/
def finiteScalarProjection (X : SmoothSite (Spec (.of k))) :
    finiteScalarExtension (E := E) X ⟶ X :=
  homMk (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k E)))) rfl

instance (X : SmoothSite (Spec (.of k))) :
    IsFinite (finiteScalarProjection (E := E) X).left :=
  inferInstanceAs (IsFinite
    (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k E)))))

instance (X : SmoothSite (Spec (.of k))) :
    Flat (finiteScalarProjection (E := E) X).left :=
  inferInstanceAs (Flat
    (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k E)))))

/-- The original map after finite scalar extension, still viewed over k. -/
def finiteScalarMap {U X : SmoothSite (Spec (.of k))} (j : U ⟶ X) :
    finiteScalarExtension (E := E) U ⟶ finiteScalarExtension (E := E) X :=
by
  let f := Spec.map (CommRingCat.ofHom (algebraMap k E))
  let g : pullback U.hom f ⟶ pullback X.hom f :=
    pullback.lift (pullback.fst U.hom f ≫ j.left) (pullback.snd U.hom f)
      (by rw [Category.assoc, MorphismProperty.Over.w, pullback.condition])
  refine homMk g ?_
  change g ≫ (pullback.fst X.hom f ≫ X.hom) = pullback.fst U.hom f ≫ U.hom
  rw [← Category.assoc, show g ≫ pullback.fst X.hom f =
    pullback.fst U.hom f ≫ j.left from pullback.lift_fst _ _ _]
  rw [Category.assoc, MorphismProperty.Over.w]

/-- The actual scalar projection square is Cartesian, without a supplied square. -/
theorem finiteScalarMap_isPullback {U X : SmoothSite (Spec (.of k))} (j : U ⟶ X) :
    IsPullback (finiteScalarProjection (E := E) U).left
      (finiteScalarMap (E := E) j).left j.left
      (finiteScalarProjection (E := E) X).left := by
  apply IsPullback.flip
  apply IsPullback.of_right
    (h₁₂ := pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap k E))))
    (h₂₂ := X.hom) (v₁₃ := Spec.map (CommRingCat.ofHom (algebraMap k E)))
  · simp only [finiteScalarMap, homMk_left, pullback.lift_snd,
      finiteScalarProjection, MorphismProperty.Over.w]
    exact (IsPullback.of_hasPullback U.hom _).flip
  · simp [finiteScalarMap, finiteScalarProjection]
  · exact (IsPullback.of_hasPullback X.hom _).flip

end Motivic.SmoothSite

namespace Motivic.Cor

variable {k E : Type u} [Field k] [Field E] [Algebra k E]
  [Module.Finite k E] [Algebra.IsSeparable k E]

/-- Restriction followed by trace has the original scalar degree. This is not
an assertion about the reverse composite on the scalar-extended object. -/
theorem finiteScalarTrace_comp_graph (X : SmoothSite (Spec (.of k))) :
    finiteFlatTrace (SmoothSite.finiteScalarProjection (E := E) X) ≫
        (graphFunctor k).map (SmoothSite.finiteScalarProjection (E := E) X) =
      (Module.finrank k E : ℤ) • 𝟙 (Cor.mk X) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap k E))
  let p := pullback.fst X.hom f
  have : IsFinite f :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have : Flat f := Flat.SpecMap_iff.mpr
    (RingHom.Flat.of_isField (Field.toIsField k) (algebraMap k E))
  have : IsNoetherian ((𝟭 Scheme).obj X.left) :=
    inferInstanceAs (IsNoetherian X.left)
  have : IsNoetherian (pullback X.hom f) := isNoetherian_of_finiteType p
  let d : (𝟭 Scheme).obj X.left ⟶ pullback X.hom X.hom :=
    pullback.lift (𝟙 ((𝟭 Scheme).obj X.left)) (𝟙 ((𝟭 Scheme).obj X.left)) (by simp)
  have : IsFinite d :=
    FiniteFlatCorrespondence.isFinite_productMap (𝟙 X.left) d (pullback.lift_fst _ _ _)
  have : IsFinite (pullback.lift (f := X.hom) (g := X.hom) p p (by rfl)) :=
    FiniteFlatCorrespondence.isFinite_productMap p _ (pullback.lift_fst _ _ _)
  have hd : pullback.lift p p rfl = p ≫ d := by
    apply pullback.hom_ext <;>
      simp only [d, Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.comp_id]
  have hid : ofFiniteFlatSpan (X := X) (Y := X) (𝟙 X.left) (𝟙 X.left)
      (by simp) = 𝟙 (Cor.mk X) := by
    simpa using DiagonalZeroCycle.ofFiniteFlatSpan_id (𝟙 X)
  rw [finiteFlatTrace, ofFiniteFlatSpan_comp_graph, ← hid]
  apply FiniteCorrespondence.toIntegralCycle_injective
  rw [map_zsmul, toIntegralCycle_ofFiniteFlatSpan, toIntegralCycle_ofFiniteFlatSpan]
  change IntegralCycle.finitePushforward (pullback.lift p p rfl)
      (fundamentalCycle (pullback X.hom f)) =
    (Module.finrank k E : ℤ) • IntegralCycle.finitePushforward d (fundamentalCycle X.left)
  have he : IntegralCycle.finitePushforward (pullback.lift p p rfl)
      (fundamentalCycle (pullback X.hom f)) =
      IntegralCycle.finitePushforward (p ≫ d) (fundamentalCycle (pullback X.hom f)) := by
    have aux {A B : Scheme.{u}} (a b : A ⟶ B) [IsFinite a] [IsFinite b]
        (h : a = b) (c : IntegralCycle A) :
        IntegralCycle.finitePushforward a c = IntegralCycle.finitePushforward b c := by
      cases h
      rfl
    exact aux _ _ hd _
  rw [he, IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply,
    finitePushforward_scalar_fundamentalCycle, map_zsmul]
  rfl

/-- Scalar trace commutes with every flat original restriction, in particular
with open restrictions, using the actual scalar-extended map. -/
theorem finiteScalarTrace_naturality {U X : SmoothSite (Spec (.of k))}
    (j : U ⟶ X) [Flat j.left] :
    finiteFlatTrace (SmoothSite.finiteScalarProjection (E := E) U) ≫
        (graphFunctor k).map (SmoothSite.finiteScalarMap (E := E) j) =
      (graphFunctor k).map j ≫
        finiteFlatTrace (SmoothSite.finiteScalarProjection (E := E) X) :=
  finiteFlatTrace_cartesian _ _ j _ (SmoothSite.finiteScalarMap_isPullback j)

end Motivic.Cor
