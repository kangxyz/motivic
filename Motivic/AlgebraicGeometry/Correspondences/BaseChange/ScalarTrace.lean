/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.ScalarExtension.Finite.Basic

public import Motivic.AlgebraicGeometry.Correspondences.BaseChange.FlatSpan
public import Motivic.AlgebraicGeometry.Correspondences.Composition.DiagonalZeroCycle
public import Motivic.Aglib.AlgebraicGeometry.Cycles.ScalarExtension.FiniteScalarFundamentalCycle
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
open _root_.AlgebraicGeometry.Scheme

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


namespace Motivic.Cor
open _root_.AlgebraicGeometry.Scheme

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
