/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Point.Normalization
public import Lean.Util.CollectAxioms

/-!
# Consumers of finite closed-center normalization

The actual open immersion, canonical field-valued lift, and singleton preimage
are tested over arbitrary affine bases. The common-refinement consumer uses
the existing cofiltered neighborhood category and original fiber colimit maps.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open  _root_.AlgebraicGeometry.Scheme.SmoothSite

universe u v w

section Schemes

variable {U X : Scheme.{u}} (f : U ⟶ X) [LocallyQuasiFinite f] [QuasiCompact f]
  (T : Set X) (hT : T.Finite) (hclosed : ∀ x ∈ T, IsClosed ({x} : Set X)) (u : U)

example : ∃ W : U.Opens, u ∈ W ∧ ∀ v ∈ W, f v ∈ T → v = u :=
  f.exists_open_isolating_finite_closed_fibers T hT hclosed u

example : ∃ (R : CommRingCat.{u}) (j : Spec R ⟶ U), IsOpenImmersion j ∧
    u ∈ Set.range j ∧ ∀ v : Spec R, f (j v) ∈ T → j v = u :=
  f.exists_affine_isolating_finite_closed_fibers T hT hclosed u

end Schemes

section Neighborhoods

variable {S : Scheme.{u}} [IsAffine S] {X : SmoothSite S} {x : X.left}
  (N : NisnevichNeighborhood X x) (T : Set X.left) (hT : T.Finite)
  (hclosed : ∀ y ∈ T, IsClosed ({y} : Set X.left)) (hx : x ∈ T)

example : N.toBase.left N.center = x := N.toBase_center

example : ∃ (M : NisnevichNeighborhood X x) (q : M ⟶ N),
    IsAffine M.obj.obj.left ∧ IsOpenImmersion q.hom.hom.left ∧
    M.obj.val.left ≫ q.hom.hom.left = N.obj.val.left ∧
    M.toBase.left ⁻¹' T = {M.center} :=
  N.exists_normalized_refinement T hT hclosed hx

example (N' : NisnevichNeighborhood X x) :
    ∃ (M : NisnevichNeighborhood X x) (q : M ⟶ N) (q' : M ⟶ N'),
      IsAffine M.obj.obj.left ∧
      M.obj.val.left ≫ q.hom.hom.left = N.obj.val.left ∧
      M.obj.val.left ≫ q'.hom.hom.left = N'.obj.val.left ∧
      M.toBase.left ⁻¹' T = {M.center} := by
  obtain ⟨M, r, hM, _, _, hfiber⟩ :=
    (IsCofiltered.min N N').exists_normalized_refinement T hT hclosed hx
  exact ⟨M, r ≫ IsCofiltered.minToLeft N N', r ≫ IsCofiltered.minToRight N N', hM,
    NisnevichNeighborhood.refinement_point _, NisnevichNeighborhood.refinement_point _, hfiber⟩

variable {A : Type v} [Category.{w} A] [HasColimitsOfSize.{u + 1, u + 1} A]

example (F : (SmoothSite S)ᵒᵖ ⥤ A) :
    ∃ (M : NisnevichNeighborhood X x) (q : M ⟶ N),
      M.toBase.left ⁻¹' T = {M.center} ∧
      F.map ((nisnevichNeighborhoodFunctor X x).map q).op ≫
          (nisnevichPointFiberCocone X x F).ι.app (op M) =
        (nisnevichPointFiberCocone X x F).ι.app (op N) := by
  obtain ⟨M, q, _, _, _, hfiber⟩ := N.exists_normalized_refinement T hT hclosed hx
  exact ⟨M, q, hfiber, (nisnevichPointFiberCocone X x F).w q.op⟩

end Neighborhoods

open Lean in
open _root_.AlgebraicGeometry.Scheme.SmoothSite.NisnevichNeighborhood in
run_cmd do
  for name in #[``AlgebraicGeometry.Scheme.Hom.exists_open_isolating_finite_closed_fibers,
      ``AlgebraicGeometry.Scheme.Hom.exists_affine_isolating_finite_closed_fibers,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.NisnevichNeighborhood.refinement_point,
      ``exists_normalized_refinement] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Finite closed-center normalization uses only standard Lean foundations."
