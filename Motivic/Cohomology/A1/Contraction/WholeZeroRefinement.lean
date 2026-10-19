/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.Boundary.Contraction.Geometry
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Etale.Neighborhood.EtaleZeroFiberWholeNeighborhood

/-! # Whole-zero refinements of actual small-site ambient neighborhoods -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Motivic.FiniteEtaleSite
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))

local instance zeroSection_closed (Y : SmoothSite (Spec (.of k))) :
    IsClosedImmersion (SmoothSite.a1Section (.of k) Y 0).left := by
  have h := congrArg (fun f => f.left) (SmoothSite.a1Section_projection (.of k) Y 0)
  change (SmoothSite.a1Section (.of k) Y 0).left ≫
    (SmoothSite.a1Projection (.of k) Y).left = 𝟙 Y.left at h
  have : IsClosedImmersion ((SmoothSite.a1Section (.of k) Y 0).left ≫
      (SmoothSite.a1Projection (.of k) Y).left) := by rw [h]; infer_instance
  exact IsClosedImmersion.of_comp _ (SmoothSite.a1Projection (.of k) Y).left

/-- Every actual zero-fiber point admits an affine whole-zero refinement over an
open neighborhood in that fiber. The ambient neighborhood need not split at zero. -/
theorem exists_whole_zero_neighborhood_refinement
    (W : EtaleSeparatedFiniteType (SmoothSite.a1Cylinder (.of k) X).left)
    (w : ((baseChange (SmoothSite.a1Section (.of k) X 0).left).obj W).left) :
    ∃ (V : EtaleSeparatedFiniteType X.left)
      (v : V ⟶ (baseChange (SmoothSite.a1Section (.of k) X 0).left).obj W),
      IsAffine V.left ∧ IsOpenImmersion v.left ∧ w ∈ Set.range v.left ∧
      ∃ (E : EtaleSeparatedFiniteType (SmoothSite.a1Cylinder (.of k) X).left)
        (e : E ⟶ W) (q : E ⟶ (cylinderNeighborhood X).obj V)
        (a : V.left ⟶ E.left)
        (zV : V ⟶ (baseChange (SmoothSite.a1Section (.of k) X 0).left).obj E),
        IsAffine E.left ∧ Etale q.left ∧ QuasiCompact q.left ∧ IsSeparated q.left ∧
        IsPullback a (𝟙 V.left) q.left
          (SmoothSite.a1Section (.of k) ((toSmoothSite X).obj V) 0).left ∧
        zV.left ≫ pullback.fst E.hom (SmoothSite.a1Section (.of k) X 0).left = a ∧
        zV ≫ (baseChange (SmoothSite.a1Section (.of k) X 0).left).map q =
          zeroNeighborhoodLift X V ∧
        zV ≫ (baseChange (SmoothSite.a1Section (.of k) X 0).left).map e = v := by
  let z := (SmoothSite.a1Section (.of k) X 0).left
  let W₀ := (baseChange z).obj W
  let b : (SmoothSite.a1Cylinder (.of k) X).left ⟶ Spec (.of k) :=
    (SmoothSite.a1Cylinder (.of k) X).hom
  obtain ⟨O, hO, hw, hV, h⟩ := Scheme.Hom.exists_affine_whole_zeroFiber_refinement
    b W.hom z w
  let U := (pullback.fst W.hom z) ⁻¹ᵁ O
  let : IsAffine U.toScheme := hV
  let V : EtaleSeparatedFiniteType X.left := MorphismProperty.Over.mk ⊤ (U.ι ≫ W₀.hom)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have : IsAffine V.left := hV
  have : IsAffine (SmoothSite.a1Cylinder (.of k) ((toSmoothSite X).obj V)).left := by
    change IsAffine (pullback (V.hom ≫ X.hom)
      (Scheme.PolynomialLaurent.polynomialProjection (.of k)))
    exact Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine
      (show V.left ⟶ Spec (.of k) from V.hom ≫ X.hom)
      (Scheme.PolynomialLaurent.polynomialProjection (.of k))
  let v : V ⟶ W₀ := MorphismProperty.Over.homMk U.ι rfl
  let j := ((cylinderNeighborhood X).obj V).hom
  let z' := (SmoothSite.a1Section (.of k) ((toSmoothSite X).obj V) 0).left
  have hcompat : z' ≫ j = U.ι ≫ pullback.snd W.hom z ≫ z := by
    exact congrArg (fun f => f.left)
      (SmoothSite.a1Section_naturality (.of k) (toBase X V) 0)
  obtain ⟨E₀, hE₀, e₀, q₀, a, hq₀, hqc₀, hqs₀, he₀, ha, H⟩ :=
    h (SmoothSite.a1Cylinder (.of k) ((toSmoothSite X).obj V)).left j z' hcompat
  let : Etale q₀ := hq₀
  let : QuasiCompact q₀ := hqc₀
  let : IsSeparated q₀ := hqs₀
  let E : EtaleSeparatedFiniteType (SmoothSite.a1Cylinder (.of k) X).left :=
    MorphismProperty.Over.mk ⊤ (q₀ ≫ j) ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  let e : E ⟶ W := MorphismProperty.Over.homMk e₀ he₀
  let q : E ⟶ (cylinderNeighborhood X).obj V := MorphismProperty.Over.homMk q₀ rfl
  have haz : a ≫ E.hom = V.hom ≫ z := by
    change a ≫ (q₀ ≫ j) = _
    rw [← Category.assoc, H.w, Category.id_comp, hcompat]
    rfl
  let zV : V ⟶ (baseChange z).obj E := MorphismProperty.Over.homMk
    (pullback.lift a V.hom haz) (pullback.lift_snd _ _ _)
  have hv : IsOpenImmersion v.left := inferInstanceAs (IsOpenImmersion U.ι)
  have hmf {A B : EtaleSeparatedFiniteType (SmoothSite.a1Cylinder (.of k) X).left}
      (f : A ⟶ B) : ((baseChange z).map f).left ≫ pullback.fst B.hom z =
        pullback.fst A.hom z ≫ f.left := pullback.lift_fst _ _ _
  have hms {A B : EtaleSeparatedFiniteType (SmoothSite.a1Cylinder (.of k) X).left}
      (f : A ⟶ B) : ((baseChange z).map f).left ≫ pullback.snd B.hom z =
        pullback.snd A.hom z := pullback.lift_snd _ _ _
  have hzf : (zeroNeighborhoodLift X V).left ≫ pullback.fst j z = z' :=
    pullback.lift_fst _ _ _
  have hzs : (zeroNeighborhoodLift X V).left ≫ pullback.snd j z = V.hom :=
    pullback.lift_snd _ _ _
  refine ⟨V, v, hV, hv, ⟨⟨w, hw⟩, rfl⟩, E, e, q, a, zV,
    hE₀, hq₀, hqc₀, hqs₀, H, pullback.lift_fst _ _ _, ?_, ?_⟩
  · apply MorphismProperty.Over.Hom.ext
    change (zV.left ≫ ((baseChange z).map q).left) = (zeroNeighborhoodLift X V).left
    apply pullback.hom_ext
    · rw [Category.assoc, hmf]
      change pullback.lift a V.hom haz ≫ (pullback.fst E.hom z ≫ q₀) =
        (zeroNeighborhoodLift X V).left ≫ pullback.fst _ z
      rw [pullback.lift_fst_assoc]
      rw [hzf]
      exact H.w.trans (Category.id_comp _)
    · rw [Category.assoc, hms, hzs]
      exact pullback.lift_snd _ _ _
  · apply MorphismProperty.Over.Hom.ext
    change zV.left ≫ ((baseChange z).map e).left = v.left
    apply pullback.hom_ext
    · rw [Category.assoc, hmf]
      change pullback.lift a V.hom haz ≫ (pullback.fst E.hom z ≫ e₀) = _
      rw [pullback.lift_fst_assoc]
      exact ha
    · rw [Category.assoc, hms]
      exact pullback.lift_snd _ _ _

end Motivic.FiniteEtaleSite
