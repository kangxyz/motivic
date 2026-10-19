/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.MarkedChartSquare
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Marked.GraphChartOpen
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.GraphRegular

/-! # Regular marked values on the literal affine graph chart

The whole marked chart ring and its Cartesian square are canonical. Regularity
holds for the original supplied target ideal frame, not merely a chosen monic
polynomial frame, and retains nilpotents in the marked ring.


Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.AffineMarkedGraphRegular`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Hom

variable {S X Y Z C K T V : Scheme.{u}} {R : Type u} [CommRing R]
  (q : X ⟶ S) (qC : C ⟶ S) (j : Y ⟶ C)
  (p : Y ⟶ X) [Flat p] (hq : j ≫ qC = p ≫ q)
  (z : Z ⟶ X) (s : Z ⟶ Y) (h : s ≫ p = z)
  (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    idealModule (boundaryGraphTarget q z))
  (f : C ⟶ K) (zK : Z ⟶ K) [IsAffineHom zK]
  (hsK : (s ≫ j) ≫ f = zK)
  (n : T ⟶ Spec (.of R)) (k : V ⟶ T) (t : Spec (.of R) ⟶ K)


variable (σ : Spec (.of Γ(pullback zK t, ⊤)) ⟶ V)
  (hn : (σ ≫ k) ≫ n = Spec.map (CommRingCat.ofHom
      (FiniteSchemeNormBaseChange.scalarMap (pullback.snd zK t))))
  (u : T ⟶ C) (Hf : IsPullback u n f t)
  (hj : ((pullback zK t).isoSpec.inv ≫ pullback.fst zK t) ≫ (s ≫ j) = (σ ≫ k) ≫ u)
  (v : T ⟶ pullback (j ≫ qC) qC) [IsOpenImmersion v]
  (hv : v ≫ pullback.snd (j ≫ qC) qC = u)

include hsK hn Hf in
/-- The exact marked scalar entering the prescribed graph norm formula is
regular on the whole canonical marked chart. Its square is constructed from
the literal marked pullback, not assumed as extra geometry. -/
theorem affineMarkedGraph_frame_scalar_regular :
    let α := Scheme.graphChartMarkedFactor qC j s k σ u
      ((pullback zK t).isoSpec.inv ≫ pullback.fst zK t) hj v hv
    let θ := unitEndomorphismPullback
      (α ≫ (relativeBoundaryProductIso q qC j p hq z s h).hom ≫ boundaryProductMap q p z)
      (e.hom ≫ idealInclusion (boundaryGraphTarget q z))
    IsSMulRegular Γ(pullback zK t, ⊤) ((Scheme.ΓSpecIso (.of Γ(pullback zK t, ⊤))).hom
      (Modules.Hom.app θ ⊤ (1 : Γ(Spec (.of Γ(pullback zK t, ⊤)), ⊤)))) := by
  dsimp only
  let α := Scheme.graphChartMarkedFactor qC j s k σ u
    ((pullback zK t).isoSpec.inv ≫ pullback.fst zK t) hj v hv
  have : Flat α := Scheme.graphChartMarkedFactor_flat
    qC j s f zK hsK n k σ (Spec.map (CommRingCat.ofHom
      (FiniteSchemeNormBaseChange.scalarMap (pullback.snd zK t)))) hn u t Hf
    ((pullback zK t).isoSpec.inv ≫ pullback.fst zK t)
    (Scheme.affineMarkedChart_isPullback zK t) hj v hv
  let b := α ≫ (relativeBoundaryProductIso q qC j p hq z s h).hom ≫
    boundaryProductMap q p z
  let θ := e.hom ≫ idealInclusion (boundaryGraphTarget q z)
  have : Mono (idealInclusion (boundaryGraphTarget q z)) :=
    idealInclusionMono (boundaryGraphTarget q z)
  have : Mono θ := mono_comp _ _
  have hr := Modules.isSMulRegular_unitEnd_app_one_flat_pullback b θ
  rw [← unitEndomorphismPullback_app_one] at hr
  let c : Γ(Spec (.of Γ(pullback zK t, ⊤)), ⊤) :=
    Modules.Hom.app (unitEndomorphismPullback b θ) ⊤ (1 : Γ(Spec (.of Γ(pullback zK t, ⊤)), ⊤))
  change IsSMulRegular Γ(pullback zK t, ⊤) ((Scheme.ΓSpecIso (.of Γ(pullback zK t, ⊤))).hom c)
  change IsSMulRegular Γ(Spec (.of Γ(pullback zK t, ⊤)), ⊤) c at hr
  intro x y hxy
  apply (Scheme.ΓSpecIso (.of Γ(pullback zK t, ⊤))).commRingCatIsoToRingEquiv.symm.injective
  apply hr
  change c * (Scheme.ΓSpecIso (.of Γ(pullback zK t, ⊤))).inv x =
    c * (Scheme.ΓSpecIso (.of Γ(pullback zK t, ⊤))).inv y
  change (Scheme.ΓSpecIso (.of Γ(pullback zK t, ⊤))).hom c * x =
    (Scheme.ΓSpecIso (.of Γ(pullback zK t, ⊤))).hom c * y at hxy
  simpa only [map_mul, Iso.hom_inv_id_apply] using
    congrArg (Scheme.ΓSpecIso (.of Γ(pullback zK t, ⊤))).inv hxy

end AlgebraicGeometry.Scheme.Hom
