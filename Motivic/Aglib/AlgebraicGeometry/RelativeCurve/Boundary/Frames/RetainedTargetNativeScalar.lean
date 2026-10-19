/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.RetainedTargetPrescribedScalar
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.RetainedMarkedCoordinateComparison

/-! # The original target coefficient on the actual retained marked chart

The same target prescribed extension is used throughout. Its marked factor is
identified with the native target factor by the original finite chart square
and the literal inverse-frame lift, not by a prescribed scalar equality.


Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.RetainedTargetNativeScalar`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Hom

private theorem graph_boundary_lift_eq_of_ambient_eq
    {S C Y Z Q : Scheme.{u}} (π : C ⟶ S) (j : Y ⟶ C) (s : Z ⟶ Y)
    (γ γ' : Q ⟶ pullback (j ≫ π) π) (a : Q ⟶ Z)
    (h : γ ≫ pullback.snd (j ≫ π) π = a ≫ (s ≫ j))
    (h' : γ' ≫ pullback.snd (j ≫ π) π = a ≫ (s ≫ j)) (he : γ = γ') :
    (graphBoundaryRestriction_isPullback π j s).lift γ a h =
      (graphBoundaryRestriction_isPullback π j s).lift γ' a h' := by
  subst γ'
  rfl

variable {S X Y Z C P D : Scheme.{u}} (q : X ⟶ S) [IsSeparated q]
  [SmoothOfRelativeDimension 1 q] (π : P ⟶ S) [IsSeparated π]
  (jA : X ⟶ P) [IsOpenImmersion jA] [SmoothOfRelativeDimension 1 (jA ≫ π)]
  (hA : jA ≫ π = q) (z : Z ⟶ X)
  (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    idealModule (boundaryGraphTarget q z))
  (d : D ⟶ P) (hd : Disjoint (Set.range jA) (Set.range d))
  (A : (pullback (jA ≫ π) π).affineOpens)
  (b : (pullback (pullback.snd (jA ≫ π) π) d ⨿
    pullback (jA ≫ π) (z ≫ jA ≫ π)) ⟶ A.val.toScheme)
  (hc : b ≫ A.val.ι =
    coprod.desc (infinityProductMap π jA d) (graphBoundaryRestriction π jA z))
  (E : PrescribedAffineFrameExtension A b (relativeCompactificationGraphLine π jA)
    ((Modules.pullbackComp b A.val.ι).app (relativeCompactificationGraphLine π jA).val ≪≫
      (Modules.pullbackCongr hc).app (relativeCompactificationGraphLine π jA).val ≪≫
      relativeFullBoundaryIdealFrame q π jA (𝟙 X) (by simpa using hA)
        z z (by simp) (IsPullback.id_vert z) e d hd))
  (f : C ⟶ P) (jB : Y ⟶ C) (p : Y ⟶ X) [Flat p]
  (hret : jB ≫ f = p ≫ jA) (s : Z ⟶ Y) (hs : s ≫ p = z)
  {R Q : Type u} [CommRing R] [CommRing Q] {T : Scheme.{u}}
  (v : T ⟶ pullback (jB ≫ f ≫ π) (f ≫ π)) (n : T ⟶ Spec (.of R))
  (w : Spec (.of R) ⟶ pullback (jB ≫ f ≫ π) π)
  (hn : v ≫ graphProductMap π f jB = n ≫ w)
  (l : Spec (.of R) ⟶ pullback (retainedParameterProductMap π f jB jA p hret)
    E.ambientInclusion)
  (hl : l ≫ pullback.fst (retainedParameterProductMap π f jB jA p hret)
    E.ambientInclusion = w)
  (δ : Spec (.of Q) ⟶ T) (a : Spec (.of Q) ⟶ Z)
  (hp : (δ ≫ v) ≫ pullback.snd (jB ≫ f ≫ π) (f ≫ π) = a ≫ s ≫ jB)

local instance : IsClosedImmersion (compactificationGraph π jA) := by
  dsimp [compactificationGraph]
  infer_instance

/-- The exact native target scalar equation, retaining all original maps and frame data. -/
def RetainedTargetNativeScalarEquation : Prop :=
    let eT := retainedTargetChartFrame π f jB jA p hret
      (relativeCompactificationGraphLine π jA).property E.ambientInclusion E.ambientFrame
    let θT := eT.inv ≫ pullbackUnitMap
      (pullback.fst (retainedParameterProductMap π f jB jA p hret) E.ambientInclusion)
      (idealInclusion (targetCompactificationGraph π f jB))
    let rT := retainedNativeTargetMarkedFactor π f jB jA p hret z s hs (δ ≫ v) a hp
    (Scheme.ΓSpecIso (.of Q)).hom
      ((δ ≫ n ≫ l).appTop (Modules.Hom.app θT ⊤
        (1 : Γ(pullback (retainedParameterProductMap π f jB jA p hret)
          E.ambientInclusion, ⊤)))) =
    (Scheme.ΓSpecIso (.of Q)).hom (Modules.Hom.app (unitEndomorphismPullback
      (rT ≫ (relativeBoundaryProductIso q π jA (𝟙 X) (by simpa using hA)
        z z (by simp)).hom ≫ boundaryProductMap q (𝟙 X) z)
      (e.hom ≫ idealInclusion (boundaryGraphTarget q z))) ⊤ (1 : Γ(Spec (.of Q), ⊤)))

include hn hl in
/-- The exact target coefficient has the native marked value on the original
selected chart, before any graph-generator unit normalization. -/
theorem retainedTargetChartFrame_native_marked_equation :
    RetainedTargetNativeScalarEquation (q := q) (π := π) (jA := jA) (hA := hA)
      (z := z) (e := e) (d := d) (hd := hd) (A := A) (b := b) (hc := hc) (E := E)
      (f := f) (jB := jB) (p := p) (hret := hret) (s := s) (hs := hs)
      (v := v) (n := n) (l := l) (δ := δ) (a := a) (hp := hp) := by
  let eval : (Spec (.of Q) ⟶ pullback (jA ≫ π) (z ≫ jA ≫ π)) → Q := fun r =>
    (Scheme.ΓSpecIso (.of Q)).hom (Modules.Hom.app (unitEndomorphismPullback
      (r ≫ (relativeBoundaryProductIso q π jA (𝟙 X) (by simpa using hA)
        z z (by simp)).hom ≫ boundaryProductMap q (𝟙 X) z)
      (e.hom ≫ idealInclusion (boundaryGraphTarget q z))) ⊤
        (1 : Γ(Spec (.of Q), ⊤)))
  with_reducible
    unfold RetainedTargetNativeScalarEquation
    have hβ := retainedMarkedChart_ambient π f jB jA p hret v n w hn
      E.ambientInclusion l hl δ
    have hpT : ((δ ≫ n ≫ l) ≫
        pullback.snd (retainedParameterProductMap π f jB jA p hret) E.ambientInclusion ≫
          E.ambientInclusion) ≫ pullback.snd (jA ≫ π) π = a ≫ (z ≫ jA) := by
      rw [show (δ ≫ n ≫ l) ≫
          pullback.snd (retainedParameterProductMap π f jB jA p hret) E.ambientInclusion ≫
            E.ambientInclusion = retainedMarkedTargetAmbient π f jB jA p hret (δ ≫ v) by
              simpa only [Category.assoc] using hβ]
      exact retainedMarkedTargetAmbient_point π f jB jA p hret z s hs (δ ≫ v) a hp
    have hvalue := retainedTargetChartFrame_marked_value q π jA (𝟙 X)
      (by simpa using hA) z z (by simp) (IsPullback.id_vert z) e d hd A b hc E
      f jB p hret (δ ≫ n ≫ l) a hpT
    have hfactor : retainedTargetMarkedFactor q π jA (𝟙 X)
        (by simpa using hA) z z (by simp) (IsPullback.id_vert z) e d hd A b hc E
        f jB p hret (δ ≫ n ≫ l) a hpT =
        retainedNativeTargetMarkedFactor π f jB jA p hret z s hs (δ ≫ v) a hp := by
      dsimp only [retainedTargetMarkedFactor, retainedNativeTargetMarkedFactor]
      apply graph_boundary_lift_eq_of_ambient_eq
      simpa only [Category.assoc] using hβ
    have heval := congrArg eval hfactor
    with_reducible exact hvalue.trans heval

include hn hl in
/-- The original explicit equality form of the same checked native equation. -/
theorem retainedTargetChartFrame_native_marked_value :
    let eT := retainedTargetChartFrame π f jB jA p hret
      (relativeCompactificationGraphLine π jA).property E.ambientInclusion E.ambientFrame
    let θT := eT.inv ≫ pullbackUnitMap
      (pullback.fst (retainedParameterProductMap π f jB jA p hret) E.ambientInclusion)
      (idealInclusion (targetCompactificationGraph π f jB))
    let rT := retainedNativeTargetMarkedFactor π f jB jA p hret z s hs (δ ≫ v) a hp
    (Scheme.ΓSpecIso (.of Q)).hom
      ((δ ≫ n ≫ l).appTop (Modules.Hom.app θT ⊤
        (1 : Γ(pullback (retainedParameterProductMap π f jB jA p hret)
          E.ambientInclusion, ⊤)))) =
    (Scheme.ΓSpecIso (.of Q)).hom (Modules.Hom.app (unitEndomorphismPullback
      (rT ≫ (relativeBoundaryProductIso q π jA (𝟙 X) (by simpa using hA)
        z z (by simp)).hom ≫ boundaryProductMap q (𝟙 X) z)
      (e.hom ≫ idealInclusion (boundaryGraphTarget q z))) ⊤ (1 : Γ(Spec (.of Q), ⊤))) := by
  have h := retainedTargetChartFrame_native_marked_equation
      (q := q) (π := π) (jA := jA) (hA := hA) (z := z) (e := e)
      (d := d) (hd := hd) (A := A) (b := b) (hc := hc) (E := E)
      (f := f) (jB := jB) (p := p) (hret := hret) (s := s) (hs := hs)
      (v := v) (n := n) (w := w) (hn := hn) (l := l) (hl := hl)
      (δ := δ) (a := a) (hp := hp)
  unfold RetainedTargetNativeScalarEquation at h
  with_reducible exact h

end AlgebraicGeometry.Scheme.Hom
