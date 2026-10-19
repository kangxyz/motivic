/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.Contraction.WholeZeroRefinement
public import Motivic.Cohomology.A1.Boundary.Contraction.SheafKernel
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.Complement

/-! # Pointed ambient extensions give genuine local cylinder extensions -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite
variable {k : Type u} [Field k]

/-- An extension on an actual étale ambient neighborhood, marked over the original
residue field, extends over the entire cylinder after a residue-splitting base
neighborhood. The proof uses whole-zero refinement and ordinary Nisnevich gluing. -/
theorem exists_local_cylinder_extension_of_pointed_extension
    (F : Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
    (X E : SmoothSite (Spec (.of k))) (f : E ⟶ a1Cylinder (.of k) X)
    [Etale f.left] (x : X.left)
    (c : Spec (X.left.residueField x) ⟶ E.left)
    (hc : c ≫ f.left = X.left.fromSpecResidueField x ≫ (a1Section (.of k) X 0).left)
    (s : F.obj.obj (op (torusCylinder (.of k) X))) (t : F.obj.obj (op E))
    (h : F.obj.map (etalePullbackFst f (contractionOpen (.of k) X)).op t =
      F.obj.map (etalePullbackSnd f (contractionOpen (.of k) X)).op s) :
    ∃ (V : EtaleSeparatedFiniteType X.left)
      (cV : Spec (X.left.residueField x) ⟶ V.left),
      cV ≫ V.hom = X.left.fromSpecResidueField x ∧
      ∃ a : F.obj.obj (op (a1Cylinder (.of k) ((EtaleSeparatedFiniteType.toSmoothSite X).obj V))),
        F.obj.map (contractionOpen (.of k) ((EtaleSeparatedFiniteType.toSmoothSite X).obj V)).op a =
          F.obj.map (productMap (EtaleSeparatedFiniteType.toBase X V) (𝟙 (torus (.of k)))).op s :=
              by
  let W : EtaleSeparatedFiniteType (a1Cylinder (.of k) X).left :=
    MorphismProperty.Over.mk ⊤ f.left ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  let z := (a1Section (.of k) X 0).left
  let c₀ : Spec (X.left.residueField x) ⟶
      ((EtaleSeparatedFiniteType.baseChange z).obj W).left :=
    pullback.lift c (X.left.fromSpecResidueField x) hc
  let ξ := IsLocalRing.closedPoint (X.left.residueField x)
  obtain ⟨V, v, hV, hv, hw, N, e, q, a, zV, hN, hq, hqc, hqs, H, haz, hzq, hze⟩ :=
    _root_.Motivic.FiniteEtaleSite.exists_whole_zero_neighborhood_refinement X W (c₀ ξ)
  let : IsOpenImmersion v.left := hv
  have hretain : Set.range c₀ ⊆ Set.range v.left := by
    rintro _ ⟨η, rfl⟩
    simpa only [Subsingleton.elim η ξ] using hw
  let cV := IsOpenImmersion.lift v.left c₀ hretain
  have hcV : cV ≫ V.hom = X.left.fromSpecResidueField x := by
    rw [← MorphismProperty.Over.w v, ← Category.assoc, IsOpenImmersion.lift_fac]
    exact pullback.lift_snd _ _ _
  let Y := (EtaleSeparatedFiniteType.toSmoothSite X).obj V
  let M := (EtaleSeparatedFiniteType.toSmoothSite (a1Cylinder (.of k) X)).obj N
  let p : M ⟶ a1Cylinder (.of k) Y :=
    (EtaleSeparatedFiniteType.toSmoothSite (a1Cylinder (.of k) X)).map q ≫
      (EtaleSeparatedFiniteType.parameterProductUnderlyingIso X (affineLine (.of k))).hom.app V
  let e' : M ⟶ E := homMk e.left (by
    have he : e.left ≫ f.left = N.hom := MorphismProperty.Over.w e
    change e.left ≫ E.hom = N.hom ≫ (a1Cylinder (.of k) X).hom
    rw [← MorphismProperty.Over.w f, ← Category.assoc]
    exact congrArg (fun g => g ≫ (a1Cylinder (.of k) X).hom) he)
  let b : Y ⟶ X := EtaleSeparatedFiniteType.toBase X V
  have hp : p ≫ a1Map (.of k) b = e' ≫ f := by
    apply MorphismProperty.Over.Hom.ext
    change (q.left ≫ 𝟙 _) ≫ _ = e.left ≫ f.left
    rw [Category.comp_id]
    exact (MorphismProperty.Over.w q).trans (MorphismProperty.Over.w e).symm
  have : Etale p.left := by
    change Etale (q.left ≫ 𝟙 _)
    rw [Category.comp_id]
    exact hq
  have hpb : IsPullback a (𝟙 V.left) p.left (a1Section (.of k) Y 0).left := by
    change IsPullback a (𝟙 V.left) (q.left ≫ 𝟙 _) _
    simpa only [Category.comp_id] using H
  have : IsIso (pullback.snd p.left (a1Section (.of k) Y 0).left) := by
    have hi : IsIso (hpb.isoPullback.hom ≫
        pullback.snd p.left (a1Section (.of k) Y 0).left) := by
      rw [hpb.isoPullback_hom_snd]
      infer_instance
    exact IsIso.of_isIso_comp_left hpb.isoPullback.hom _
  let j := contractionOpen (.of k) Y
  let O := etalePullback j p
  let α : O ⟶ torusCylinder (.of k) Y := etalePullbackFst j p
  let β : O ⟶ M := etalePullbackSnd j p
  have hO : IsPullback α β j p := IsPullback.of_isLimit (etalePullbackConeIsLimit j p)
  have hnat : j ≫ a1Map (.of k) b =
      productMap b (𝟙 (torus (.of k))) ≫ contractionOpen (.of k) X := by
    simp only [j, contractionOpen, a1Map, ← productMap_comp,
      Category.comp_id, Category.id_comp]
  have hr : (β ≫ e') ≫ f =
      (α ≫ productMap b (𝟙 (torus (.of k)))) ≫ contractionOpen (.of k) X := by
    rw [Category.assoc, ← hp, ← Category.assoc β, ← hO.w,
      Category.assoc, hnat, ← Category.assoc]
  let H₀ := IsPullback.of_isLimit (etalePullbackConeIsLimit f (contractionOpen (.of k) X))
  let r := H₀.lift (β ≫ e') (α ≫ productMap b (𝟙 (torus (.of k)))) hr
  have heq : F.obj.map α.op
        (F.obj.map (productMap b (𝟙 (torus (.of k)))).op s) =
      F.obj.map β.op (F.obj.map e'.op t) := by
    have hr₁ : r ≫ etalePullbackFst f (contractionOpen (.of k) X) = β ≫ e' :=
      H₀.lift_fst _ _ _
    have hr₂ : r ≫ etalePullbackSnd f (contractionOpen (.of k) X) =
        α ≫ productMap b (𝟙 (torus (.of k))) := H₀.lift_snd _ _ _
    have hm₁ : F.obj.map (etalePullbackFst f (contractionOpen (.of k) X)).op ≫
        F.obj.map r.op = F.obj.map e'.op ≫ F.obj.map β.op := by
      rw [← F.obj.map_comp, ← op_comp, hr₁, op_comp, F.obj.map_comp]
    have hm₂ : F.obj.map (etalePullbackSnd f (contractionOpen (.of k) X)).op ≫
        F.obj.map r.op = F.obj.map (productMap b (𝟙 (torus (.of k)))).op ≫
          F.obj.map α.op := by
      rw [← F.obj.map_comp, ← op_comp, hr₂, op_comp, F.obj.map_comp]
    change (F.obj.map (productMap b (𝟙 (torus (.of k)))).op ≫ F.obj.map α.op) s =
      (F.obj.map e'.op ≫ F.obj.map β.op) t
    rw [← hm₁, ← hm₂]
    exact (congrArg (F.obj.map r.op) h).symm
  let sq : Square (SmoothSite (Spec (.of k))) := ⟨α, β, j, p, hO.w⟩
  obtain ⟨a', ha', _⟩ := exists_extension_of_iso_complement_neighborhood F sq hO
    (a1Section (.of k) Y 0).left (range_a1Section_zero (.of k) Y)
    (F.obj.map (productMap b (𝟙 (torus (.of k)))).op s) (F.obj.map e'.op t) heq
  exact ⟨V, cV, hcV, a', ha'⟩

end AlgebraicGeometry.Scheme.SmoothSite
