/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Coproducts.Binary
public import Motivic.AlgebraicGeometry.Correspondences.Graph.Flat.LeftComposition
public import Motivic.Aglib.AlgebraicGeometry.Cycles.ScalarExtension.FlatFundamentalCycleTower
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.BaseChangeProducts

/-!
# Actual graph transport by scheme isomorphisms

An isomorphic source change has an isomorphic first target projection in its
actual incidence diagram. The proved Tor coefficient formula therefore gives
the whole fiber fundamental cycle, with no flatness assumption on the second
correspondence support. This realizes graph transport as finite pushforward
through the literal source-target product isomorphism.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.Cor
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]

/-- The actual source-target ambient isomorphism underlying graph transport. -/
def graphTransportIso {X X' Y Y' : SmoothSite (Spec (.of k))}
    (e : X ≅ X') (d : Y ≅ Y') :
    pullback X.hom Y.hom ≅ pullback X'.hom Y'.hom :=
  (SmoothSite.forgetScheme (Spec (.of k))).mapIso (SmoothSite.productIso e d)

@[reassoc (attr := simp)]
theorem graphTransportIso_hom_fst {X X' Y Y' : SmoothSite (Spec (.of k))}
    (e : X ≅ X') (d : Y ≅ Y') :
    (graphTransportIso k e d).hom ≫ pullback.fst X'.hom Y'.hom =
      pullback.fst X.hom Y.hom ≫ e.hom.left :=
  congrArg (fun f => f.left) (SmoothSite.productMap_fst e.hom d.hom)

@[reassoc (attr := simp)]
theorem graphTransportIso_hom_snd {X X' Y Y' : SmoothSite (Spec (.of k))}
    (e : X ≅ X') (d : Y ≅ Y') :
    (graphTransportIso k e d).hom ≫ pullback.snd X'.hom Y'.hom =
      pullback.snd X.hom Y.hom ≫ d.hom.left :=
  congrArg (fun f => f.left) (SmoothSite.productMap_snd e.hom d.hom)

end Motivic.Cor

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] {X X' Y : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom) (e : X ≅ X')
  [IsIntegral X'.left]

local instance source_isNoetherian (T : SmoothSite (Spec (.of k))) :
    IsNoetherian ((𝟭 Scheme).obj T.left) := inferInstanceAs (IsNoetherian T.left)

local instance source_isIntegral : IsIntegral ((𝟭 Scheme).obj X'.left) :=
  inferInstanceAs (IsIntegral X'.left)

local instance support_isNoetherian : IsNoetherian A.scheme :=
  isNoetherian_of_finiteType A.projection

/-- An actual isomorphism graph has isomorphic target projection, so the
existing genuine left-incidence Tor theorem applies to every second support. -/
theorem toIntegralCycle_graphIso_comp_cycle :
    FiniteCorrespondence.toIntegralCycle (f := X'.hom) (g := Y.hom)
      ((Cor.graphFunctor k).map e.inv ≫ (show Cor.mk X ⟶ Cor.mk Y from A.cycle)) =
      IntegralCycle.finitePushforward (A.graphPullbackMap e.inv.left
        (MorphismProperty.Over.w e.inv)) (fundamentalCycle (A.graphPullback e.inv.left)) := by
  let : IsIso (graphGeneratorOver e.inv.left
      (MorphismProperty.Over.w e.inv)).targetProjection := by
    rw [← graphGeneratorOver_projection_target]
    infer_instance
  change FiniteCorrespondence.toIntegralCycle
    (FiniteCorrespondence.incidenceTorPairing k (X := X') (Y := X) (Z := Y)
      (componentGraphCycleOver e.inv.left (MorphismProperty.Over.w e.inv)) A.cycle) = _
  rw [componentGraphCycleOver_eq_graphGeneratorOver_cycle,
    FiniteCorrespondence.incidenceTorPairing_cycle,
    incidenceTorCorrespondence_eq_fundamental_of_isIso_targetProjection,
    toIntegralCycle_incidenceFundamentalCorrespondence]
  simp only [A.incidenceMap_graph_left, IntegralCycle.finitePushforward_comp,
    AddMonoidHom.comp_apply,
    finitePushforward_fundamentalCycle]

omit [IsIntegral X'.left] in
/-- The literal whole graph pullback and the product comparison have the same
source and target projections. -/
theorem graphPullbackMap_iso_eq :
    A.graphPullbackMap e.inv.left (MorphismProperty.Over.w e.inv) =
      pullback.snd e.inv.left A.projection ≫ A.inclusion ≫
        (Cor.graphTransportIso k e (Iso.refl Y)).hom := by
  apply pullback.hom_ext
  · simp only [graphPullbackMap_fst, Category.assoc,
      Cor.graphTransportIso_hom_fst]
    change pullback.fst e.inv.left A.projection =
      (pullback.snd e.inv.left A.projection ≫ A.projection) ≫ e.hom.left
    rw [← pullback.condition, Category.assoc]
    have he : e.inv.left ≫ e.hom.left = 𝟙 X'.left :=
      congrArg (fun f => f.left) e.inv_hom_id
    rw [he, Category.comp_id]
  · simp only [graphPullbackMap_snd, Category.assoc,
      Cor.graphTransportIso_hom_snd, Iso.refl_hom]
    rfl

/-- Left graph transport of the original generator is the finite pushforward
through the actual ambient source isomorphism. -/
theorem toIntegralCycle_graphIso_comp_cycle_pushforward :
    FiniteCorrespondence.toIntegralCycle (f := X'.hom) (g := Y.hom)
      ((Cor.graphFunctor k).map e.inv ≫ (show Cor.mk X ⟶ Cor.mk Y from A.cycle)) =
      IntegralCycle.finitePushforward (Cor.graphTransportIso k e (Iso.refl Y)).hom
        (FiniteCorrespondence.toIntegralCycle A.cycle) := by
  rw [A.toIntegralCycle_graphIso_comp_cycle k e]
  rw [IntegralCycle.finitePushforward_congr (A.graphPullbackMap_iso_eq k e)]
  simp only [IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply,
    finitePushforward_fundamentalCycle]
  congr 1
  let : IsNoetherian (pullback X.hom Y.hom) :=
    isNoetherian_of_finiteType (pullback.fst X.hom Y.hom)
  change closedFundamentalCycle A.val = FiniteCorrespondence.toIntegralCycle A.cycle
  rw [closedFundamentalCycle_of_isIntegral, cycle,
    FiniteCorrespondence.toIntegralCycle_single]
  rfl

end Motivic.FiniteCorrespondenceGenerator


namespace Motivic.Cor
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] {X X' Y Y' : SmoothSite (Spec (.of k))}
  (e : X ≅ X') [IsIntegral X'.left]

/-- Source-isomorphism graph transport agrees with the actual ambient finite
pushforward on every signed correspondence. -/
theorem toIntegralCycle_graphIso_comp (α : Cor.mk X ⟶ Cor.mk Y) :
    FiniteCorrespondence.toIntegralCycle (f := X'.hom) (g := Y.hom)
      ((graphFunctor k).map e.inv ≫ α) =
      IntegralCycle.finitePushforward (graphTransportIso k e (Iso.refl Y)).hom
        (FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Y.hom) α) := by
  have heq :
      (FiniteCorrespondence.toIntegralCycle (f := X'.hom) (g := Y.hom)).comp
          (FiniteCorrespondence.incidenceTorPairing k (X := X') (Y := X) (Z := Y)
            ((graphFunctor k).map e.inv)) =
        (IntegralCycle.finitePushforward (graphTransportIso k e (Iso.refl Y)).hom).comp
          (FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Y.hom)) := by
    apply Finsupp.addHom_ext
    intro A n
    have hsingle : Finsupp.single A n = n • A.cycle := by
      simp [FiniteCorrespondenceGenerator.cycle]
    rw [hsingle]
    simp only [map_zsmul]
    congr 1
    exact A.toIntegralCycle_graphIso_comp_cycle_pushforward k e
  exact congrArg (fun f => f α) heq

/-- Conjugation by the actual source and target graphs is finite pushforward
through the literal product isomorphism, for arbitrary signed cycles. -/
theorem toIntegralCycle_graphIso_transport (d : Y ≅ Y') (α : Cor.mk X ⟶ Cor.mk Y) :
    FiniteCorrespondence.toIntegralCycle (f := X'.hom) (g := Y'.hom)
      ((graphFunctor k).map e.inv ≫ α ≫ (graphFunctor k).map d.hom) =
      IntegralCycle.finitePushforward (graphTransportIso k e d).hom
        (FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Y.hom) α) := by
  rw [← Category.assoc, toIntegralCycle_comp_graph_of_finite,
    toIntegralCycle_graphIso_comp]
  have hmap : (graphTransportIso k e (Iso.refl Y)).hom ≫
      graphTargetMap k X' d.hom = (graphTransportIso k e d).hom := by
    apply pullback.hom_ext
    · simp only [Category.assoc, graphTargetMap_fst,
        graphTransportIso_hom_fst]
    · simp only [Category.assoc, graphTargetMap_snd,
        graphTransportIso_hom_snd_assoc, graphTransportIso_hom_snd, Iso.refl_hom]
      rfl
  rw [← AddMonoidHom.comp_apply, ← IntegralCycle.finitePushforward_comp,
    IntegralCycle.finitePushforward_congr hmap]

end Motivic.Cor
