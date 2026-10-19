/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.PrescribedGraphCoordinate
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Marked.GraphChartFactors
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.MarkedFiber

/-! # The actual marked norm of the original prescribed graph scalar

The marked and residual factors are constructed from the original chart square.
The supplied target frame is unchanged; no residual freeness or scalar-one
normalization is assumed.


Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Norm.PrescribedGraphMarked`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Norm.RetainedPrescribedGraph`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable {S X Y Z C D : Scheme.{u}} (q : X ⟶ S) [IsSeparated q]
  [SmoothOfRelativeDimension 1 q] (qC : C ⟶ S) [IsSeparated qC]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ qC)]
  (p : Y ⟶ X) [Flat p] (hq : j ≫ qC = p ≫ q)
  (z : Z ⟶ X) (s : Z ⟶ Y) (h : s ≫ p = z) (H : IsPullback s (𝟙 _) p z)
  (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    idealModule (boundaryGraphTarget q z))
  (d : D ⟶ C) (hd : Disjoint (Set.range j) (Set.range d))


variable (A : (pullback (j ≫ qC) qC).affineOpens)
  (b : (pullback (pullback.snd (j ≫ qC) qC) d ⨿ pullback (j ≫ qC) (s ≫ j ≫ qC)) ⟶
    A.val.toScheme)
  (hc : b ≫ A.val.ι =
    coprod.desc (infinityProductMap qC j d) (graphBoundaryRestriction qC j s))
  (E : PrescribedAffineFrameExtension A b (relativeCompactificationGraphLine qC j)
    ((Modules.pullbackComp b A.val.ι).app (relativeCompactificationGraphLine qC j).val ≪≫
      (Modules.pullbackCongr hc).app (relativeCompactificationGraphLine qC j).val ≪≫
      relativeFullBoundaryIdealFrame q qC j p hq z s h H e d hd))


variable {R Q : Type u} [CommRing R] [CommRing Q] {T V K : Scheme.{u}}
  (f : C ⟶ K) [IsFinite f] (zK : Z ⟶ K) (hsK : (s ≫ j) ≫ f = zK)
  (n : T ⟶ Spec (.of R)) [IsFinite n] (φ : R →+* Q)
  (k : V ⟶ T) [IsOpenImmersion k] (σ : Spec (.of Q) ⟶ V)
  (hn : (σ ≫ k) ≫ n = Spec.map (CommRingCat.ofHom φ))
  (HN : IsPullback σ (𝟙 _) (k ≫ n) (Spec.map (CommRingCat.ofHom φ)))
  (u : T ⟶ C) (t : Spec (.of R) ⟶ K) (Hf : IsPullback u n f t)
  (a : Spec (.of Q) ⟶ Z)
  (hz : Spec.map (CommRingCat.ofHom φ) ≫ t = a ≫ zK)
  (hj : a ≫ (s ≫ j) = (σ ≫ k) ≫ u)
  (w : T ⟶ E.neighborhood)
  (hw : (w ≫ E.ambientInclusion) ≫ pullback.snd (j ≫ qC) qC = u)
  (bE : (Scheme.residualMarkedFiberOpen f j zK s hsK).toScheme ⟶ D)
  (hbE : bE ≫ d = Scheme.residualMarkedFiberMap f j zK s hsK)

include hn HN Hf hz hbE in
/-- The original graph scalar has the supplied marked value after norm. Both
actual component maps are constructed internally from the original finite chart
square. Freeness is required only for the original total chart algebra. -/
theorem prescribedGraphFrame_norm_marked_value :
    let c := Modules.Hom.app
      (E.frame.inv ≫ pullbackUnitMap E.inclusion
        (pullbackUnitMap A.val.ι (idealInclusion (compactificationGraph qC j)))) ⊤
      (1 : Γ(E.neighborhood, ⊤))
    let α := Scheme.graphChartMarkedFactor qC j s k σ u a hj (w ≫ E.ambientInclusion) hw
    let m := Modules.Hom.app (unitEndomorphismPullback
      (α ≫ (relativeBoundaryProductIso q qC j p hq z s h).hom ≫ boundaryProductMap q p z)
      (e.hom ≫ idealInclusion (boundaryGraphTarget q z))) ⊤ (1 : Γ(Spec (.of Q), ⊤))
    let : Algebra R Γ(T, ⊤) := (FiniteSchemeNormBaseChange.scalarMap n).toAlgebra
    ∀ [Module.Free R Γ(T, ⊤)],
      φ (Algebra.norm R (w.appTop c)) = (Scheme.ΓSpecIso (.of Q)).hom m := by
  dsimp only
  let c := Modules.Hom.app
    (E.frame.inv ≫ pullbackUnitMap E.inclusion
      (pullbackUnitMap A.val.ι (idealInclusion (compactificationGraph qC j)))) ⊤
    (1 : Γ(E.neighborhood, ⊤))
  let α := Scheme.graphChartMarkedFactor qC j s k σ u a hj (w ≫ E.ambientInclusion) hw
  let r := Scheme.graphChartResidualFactor qC j s f zK hsK n k σ
    (Spec.map (CommRingCat.ofHom φ)) hn u t Hf a hz hj (w ≫ E.ambientInclusion) hw d bE hbE
  apply FiniteSchemeNormBaseChange.norm_eq_marked_value n φ k σ hn HN (w.appTop c)
  · have hm := prescribedGraphFrame_marked_scalar_of_ambient_eq
      q qC j p hq z s h H e d hd A b hc E ((σ ≫ k) ≫ w) α (by
        simpa only [Category.assoc] using
          (Scheme.graphChartMarkedFactor_ambient qC j s k σ u a hj
            (w ≫ E.ambientInclusion) hw).symm)
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      Iso.hom_inv_id_apply] using hm
  · have hr := prescribedGraphFrame_infinity_scalar_of_ambient_eq
      q qC j p hq z s h H e d hd A b hc E
      (Scheme.residualMarkedFiberMap n k (Spec.map (CommRingCat.ofHom φ)) σ hn ≫ w) r (by
        simpa only [Category.assoc] using
          (Scheme.graphChartResidualFactor_ambient qC j s f zK hsK n k σ
            (Spec.map (CommRingCat.ofHom φ)) hn u t Hf a hz hj
            (w ≫ E.ambientInclusion) hw d bE hbE).symm)
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using hr

end AlgebraicGeometry.Scheme.Hom
