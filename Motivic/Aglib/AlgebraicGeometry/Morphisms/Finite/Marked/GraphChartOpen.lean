/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Marked.GraphChartFactors

/-! # The marked factor of an actual open graph chart

Cartesianity of the target marked restriction is essential. Mere commutation
of its maps does not imply that the marked factor is open or flat.


Intended upstream module: `Aglib.AlgebraicGeometry.Morphisms.Finite.Marked.GraphChartOpen`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.AffineMarkedGraphRegular`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme

variable {S C Y Z K T V Q A : Scheme.{u}}
  (q : C ⟶ S) (j : Y ⟶ C) (s : Z ⟶ Y)
  (f : C ⟶ K) (z : Z ⟶ K) (hs : (s ≫ j) ≫ f = z)
  (n : T ⟶ A) (k : V ⟶ T) (σ : Q ⟶ V)
  (z' : Q ⟶ A) (hn : (σ ≫ k) ≫ n = z')
  (u : T ⟶ C) (t : A ⟶ K) (Hf : IsPullback u n f t)
  (a : Q ⟶ Z) (Hz : IsPullback a z' z t)
  (hj : a ≫ (s ≫ j) = (σ ≫ k) ≫ u)
  (v : T ⟶ pullback (j ≫ q) q)
  (hv : v ≫ pullback.snd (j ≫ q) q = u)

include hs hn Hf Hz
/-- The constructed marked factor is the actual base change of the source
ambient chart. The target marked square is retained, not replaced by its
commutativity equation. -/
theorem graphChartMarkedFactor_isPullback :
    IsPullback (graphChartMarkedFactor q j s k σ u a hj v hv) (σ ≫ k)
      (Hom.graphBoundaryRestriction q j s) v := by
  have ho : IsPullback ((σ ≫ k) ≫ n) a t ((s ≫ j) ≫ f) := by
    rw [hn, hs]
    exact Hz.flip
  have hm : IsPullback (σ ≫ k) a u (s ≫ j) :=
    ho.of_right hj.symm Hf.flip
  have hm' : IsPullback (σ ≫ k)
      (graphChartMarkedFactor q j s k σ u a hj v hv ≫
        pullback.snd (j ≫ q) (s ≫ j ≫ q))
      (v ≫ pullback.snd (j ≫ q) q) (s ≫ j) := by
    simpa only [graphChartMarkedFactor, pullback.lift_snd, hv] using hm
  exact (hm'.of_bot
    (graphChartMarkedFactor_ambient q j s k σ u a hj v hv).symm
    (Hom.graphBoundaryRestriction_isPullback q j s)).flip

/-- An actual open source chart gives an open marked factor by base change. -/
theorem graphChartMarkedFactor_isOpenImmersion [IsOpenImmersion v] :
    IsOpenImmersion (graphChartMarkedFactor q j s k σ u a hj v hv) :=
  MorphismProperty.of_isPullback
    (graphChartMarkedFactor_isPullback q j s f z hs n k σ z' hn u t Hf a Hz hj v hv).flip
    inferInstance

/-- The same marked factor is flat; no closed-pullback regularity is used. -/
theorem graphChartMarkedFactor_flat [IsOpenImmersion v] :
    Flat (graphChartMarkedFactor q j s k σ u a hj v hv) := by
  let := graphChartMarkedFactor_isOpenImmersion
    q j s f z hs n k σ z' hn u t Hf a Hz hj v hv
  infer_instance

end AlgebraicGeometry.Scheme
