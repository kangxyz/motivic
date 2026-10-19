/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Germs.Pullback

/-!
# Étale invariance of the literal original Nisnevich germ pullback

For an étale map which preserves the residue field at the chosen point, composing
pointed neighborhoods in the opposite direction gives an explicit inverse to the
already defined original-germ pullback. Both inverse identities are proved by
actual refinements in the original neighborhood categories. No sheaf hypothesis
or replacement of the original point-fiber colimits is used.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u v

namespace AlgebraicGeometry.Scheme.SmoothSite.NisnevichNeighborhood
variable {S : Scheme.{u}} {X Y : SmoothSite S} (f : X ⟶ Y) [Etale f.left]
  (x : X.left) [IsIso (f.left.residueFieldMap x)]

/-- The inverse residue-field point, followed by the source neighborhood's point. -/
def composeAlongPoint (M : NisnevichNeighborhood X x) :
    Spec (Y.left.residueField (f.left x)) ⟶ M.obj.obj.left :=
  inv (Spec.map (f.left.residueFieldMap x)) ≫ M.obj.val.left

omit [Etale f.left] in
@[reassoc]
theorem composeAlongPoint_toBase (M : NisnevichNeighborhood X x) :
    composeAlongPoint f x M ≫ (M.toBase.left ≫ f.left) =
      Y.left.fromSpecResidueField (f.left x) := by
  rw [composeAlongPoint, Category.assoc, ← Category.assoc M.obj.val.left,
    show M.obj.val.left ≫ M.toBase.left = X.left.fromSpecResidueField x from Over.w M.obj.val,
    ← f.left.SpecMap_residueFieldMap_fromSpecResidueField x,
    IsIso.inv_hom_id_assoc]

/-- Compose a source neighborhood with the étale residue-isomorphic base map. -/
def composeAlong (M : NisnevichNeighborhood X x) : NisnevichNeighborhood Y (f.left x) :=
  ⟨Functor.elementsMk _ (Scheme.Etale.mk (M.toBase.left ≫ f.left))
    (Over.homMk (composeAlongPoint f x M) (composeAlongPoint_toBase f x M)),
    by
      change smoothSeparatedFiniteType ((M.toBase.left ≫ f.left) ≫ Y.hom)
      rw [Category.assoc, MorphismProperty.Over.w]
      exact M.property⟩

/-- Reassociation is the only change in the underlying smooth-site object. -/
def composeAlongIso (M : NisnevichNeighborhood X x) :
    (nisnevichNeighborhoodFunctor Y (f.left x)).obj (composeAlong f x M) ≅
      (nisnevichNeighborhoodFunctor X x).obj M :=
  MorphismProperty.Over.isoMk (Iso.refl _) (by
    change (𝟙 _) ≫ (M.toBase.left ≫ X.hom) = (M.toBase.left ≫ f.left) ≫ Y.hom
    rw [Category.id_comp, Category.assoc, MorphismProperty.Over.w f])

/-- Composition preserves actual pointed refinements. -/
def composeAlongMap {M N : NisnevichNeighborhood X x} (q : M ⟶ N) :
    composeAlong f x M ⟶ composeAlong f x N :=
  ObjectProperty.homMk (Functor.Elements.homMk
    (MorphismProperty.Over.homMk q.hom.hom.left (by
      change q.hom.hom.left ≫ (N.toBase.left ≫ f.left) = M.toBase.left ≫ f.left
      rw [← Category.assoc]
      exact congrArg (fun t => t ≫ f.left) (MorphismProperty.Over.w q.hom.hom))) (by
      apply Over.OverMorphism.ext
      change composeAlongPoint f x M ≫ q.hom.hom.left = composeAlongPoint f x N
      rw [composeAlongPoint, Category.assoc, refinement_point]
      rfl))

@[reassoc]
theorem composeAlongMap_iso {M N : NisnevichNeighborhood X x} (q : M ⟶ N) :
    (nisnevichNeighborhoodFunctor Y (f.left x)).map (composeAlongMap f x q) ≫
        (composeAlongIso f x N).hom =
      (composeAlongIso f x M).hom ≫ (nisnevichNeighborhoodFunctor X x).map q := by
  apply MorphismProperty.Over.Hom.ext
  change q.hom.hom.left ≫ 𝟙 _ = 𝟙 _ ≫ q.hom.hom.left
  simp only [Category.comp_id, Category.id_comp]

/-- Pulling back and then composing gives an actual refinement of the target. -/
def composePullbackToTarget (N : NisnevichNeighborhood Y (f.left x)) :
    composeAlong f x (pullbackAlong f x N) ⟶ N :=
  ObjectProperty.homMk (Functor.Elements.homMk
    (MorphismProperty.Over.homMk (pullback.fst N.toBase.left f.left)
      (pullback.condition)) (by
      apply Over.OverMorphism.ext
      change (inv (Spec.map (f.left.residueFieldMap x)) ≫ pullbackAlongPoint f x N) ≫
        pullback.fst N.toBase.left f.left = N.obj.val.left
      rw [Category.assoc, pullbackAlongPoint, pullback.lift_fst,
        pullbackAlongTargetPoint, IsIso.inv_hom_id_assoc]))

@[reassoc]
theorem composePullbackToTarget_map (N : NisnevichNeighborhood Y (f.left x)) :
    (nisnevichNeighborhoodFunctor Y (f.left x)).map (composePullbackToTarget f x N) =
      (composeAlongIso f x (pullbackAlong f x N)).hom ≫ pullbackAlongToTarget f x N := by
  apply MorphismProperty.Over.Hom.ext
  change pullback.fst N.toBase.left f.left = 𝟙 _ ≫ pullback.fst N.toBase.left f.left
  exact (Category.id_comp _).symm

/-- The actual diagonal refines a source neighborhood to its composed pullback. -/
def toPullbackCompose (M : NisnevichNeighborhood X x) :
    M ⟶ pullbackAlong f x (composeAlong f x M) :=
  ObjectProperty.homMk (Functor.Elements.homMk
    (MorphismProperty.Over.homMk
      (pullback.lift (𝟙 M.obj.obj.left) M.toBase.left (Category.id_comp _))
      (pullback.lift_snd _ _ _)) (by
      apply Over.OverMorphism.ext
      change M.obj.val.left ≫
          pullback.lift (𝟙 M.obj.obj.left) M.toBase.left (Category.id_comp _) =
        pullbackAlongPoint f x (composeAlong f x M)
      apply pullback.hom_ext
      · erw [Category.assoc, pullback.lift_fst, Category.comp_id,
          pullbackAlongPoint, pullback.lift_fst]
        change M.obj.val.left = Spec.map (f.left.residueFieldMap x) ≫
          (inv (Spec.map (f.left.residueFieldMap x)) ≫ M.obj.val.left)
        rw [IsIso.hom_inv_id_assoc]
      · erw [Category.assoc, pullback.lift_snd, pullbackAlongPoint, pullback.lift_snd]
        exact Over.w M.obj.val))

@[reassoc]
theorem toPullbackCompose_map (M : NisnevichNeighborhood X x) :
    (nisnevichNeighborhoodFunctor X x).map (toPullbackCompose f x M) ≫
        pullbackAlongToTarget f x (composeAlong f x M) ≫ (composeAlongIso f x M).hom =
      𝟙 _ := by
  apply MorphismProperty.Over.Hom.ext
  change pullback.lift (𝟙 M.obj.obj.left) M.toBase.left (Category.id_comp _) ≫
    (pullback.fst (M.toBase.left ≫ f.left) f.left ≫ 𝟙 _) = 𝟙 _
  rw [Category.comp_id, pullback.lift_fst]

end AlgebraicGeometry.Scheme.SmoothSite.NisnevichNeighborhood

namespace AlgebraicGeometry.Scheme.SmoothSite
variable {S : Scheme.{u}} [IsAffine S] {X Y : SmoothSite S}
  (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v})
  (f : X ⟶ Y) [Etale f.left] (x : X.left) [IsIso (f.left.residueFieldMap x)]
open _root_.AlgebraicGeometry.Scheme.SmoothSite.NisnevichNeighborhood

/-- Compose every original source representative with the pointed étale base map. -/
def originalGermEtaleInverseCocone :
    Cocone ((nisnevichNeighborhoodFunctor X x).op ⋙ F) where
  pt := (nisnevichPointFiberCocone Y (f.left x) F).pt
  ι :=
    { app := fun M => F.map (NisnevichNeighborhood.composeAlongIso f x M.unop).hom.op ≫
        (nisnevichPointFiberCocone Y (f.left x) F).ι.app (op (NisnevichNeighborhood.composeAlong f x
            M.unop))
      naturality := by
        intro M N q
        change F.map ((nisnevichNeighborhoodFunctor X x).map q.unop).op ≫
            (F.map (NisnevichNeighborhood.composeAlongIso f x N.unop).hom.op ≫
              (nisnevichPointFiberCocone Y (f.left x) F).ι.app
                (op (NisnevichNeighborhood.composeAlong f x N.unop))) =
          (F.map (NisnevichNeighborhood.composeAlongIso f x M.unop).hom.op ≫
            (nisnevichPointFiberCocone Y (f.left x) F).ι.app
              (op (NisnevichNeighborhood.composeAlong f x M.unop))) ≫ 𝟙 _
        rw [Category.comp_id, ← Category.assoc, ← F.map_comp, ← op_comp,
          ← NisnevichNeighborhood.composeAlongMap_iso, op_comp, F.map_comp, Category.assoc]
        have h := (nisnevichPointFiberCocone Y (f.left x) F).w
          (NisnevichNeighborhood.composeAlongMap f x q.unop).op
        exact congrArg (fun t => F.map (NisnevichNeighborhood.composeAlongIso f x M.unop).hom.op ≫
            t) h }

/-- Explicit inverse induced on the original point-fiber colimit. -/
def originalGermEtaleInverse : (nisnevichPointFiberCocone X x F).pt ⟶
    (nisnevichPointFiberCocone Y (f.left x) F).pt :=
  (isColimitNisnevichPointFiberCocone X x F).desc (originalGermEtaleInverseCocone F f x)

@[reassoc]
theorem originalGermEtaleInverse_ι (M : NisnevichNeighborhood X x) :
    (nisnevichPointFiberCocone X x F).ι.app (op M) ≫ originalGermEtaleInverse F f x =
      F.map (NisnevichNeighborhood.composeAlongIso f x M).hom.op ≫
        (nisnevichPointFiberCocone Y (f.left x) F).ι.app (op (NisnevichNeighborhood.composeAlong f x
            M)) :=
  (isColimitNisnevichPointFiberCocone X x F).fac (originalGermEtaleInverseCocone F f x) _

@[reassoc (attr := simp)]
theorem originalGermPullback_etaleInverse :
    originalGermPullback F f x ≫ originalGermEtaleInverse F f x = 𝟙 _ := by
  apply (isColimitNisnevichPointFiberCocone Y (f.left x) F).hom_ext
  intro N
  rw [originalGermPullback_ι_assoc, originalGermEtaleInverse_ι,
    ← Category.assoc, ← F.map_comp, ← op_comp, ← NisnevichNeighborhood.composePullbackToTarget_map]
  simpa only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op, op_unop, Category.comp_id] using
    (nisnevichPointFiberCocone Y (f.left x) F).w (NisnevichNeighborhood.composePullbackToTarget f x
        N.unop).op

@[reassoc (attr := simp)]
theorem originalGermEtaleInverse_pullback :
    originalGermEtaleInverse F f x ≫ originalGermPullback F f x = 𝟙 _ := by
  apply (isColimitNisnevichPointFiberCocone X x F).hom_ext
  intro M
  rw [originalGermEtaleInverse_ι_assoc, originalGermPullback_ι]
  have h := (nisnevichPointFiberCocone X x F).w (NisnevichNeighborhood.toPullbackCompose f x
      M.unop).op
  change F.map ((nisnevichNeighborhoodFunctor X x).map (NisnevichNeighborhood.toPullbackCompose f x
      M.unop)).op ≫
    (nisnevichPointFiberCocone X x F).ι.app (op M.unop) =
      (nisnevichPointFiberCocone X x F).ι.app
        (op (NisnevichNeighborhood.pullbackAlong f x (NisnevichNeighborhood.composeAlong f x
            M.unop))) at h
  rw [← h, ← Category.assoc, ← Category.assoc, ← F.map_comp, ← F.map_comp,
    ← op_comp, ← op_comp, NisnevichNeighborhood.toPullbackCompose_map, op_id, F.map_id]
  erw [Category.id_comp]

/-- Étale residue-isomorphic restriction is invertible on the literal original
Nisnevich germs of every additive presheaf, without a sheaf assumption. -/
def originalGermEtaleIso : (nisnevichPointFiberCocone Y (f.left x) F).pt ≅
    (nisnevichPointFiberCocone X x F).pt where
  hom := originalGermPullback F f x
  inv := originalGermEtaleInverse F f x
  hom_inv_id := originalGermPullback_etaleInverse F f x
  inv_hom_id := originalGermEtaleInverse_pullback F f x

instance isIso_originalGermPullback : IsIso (originalGermPullback F f x) :=
  (originalGermEtaleIso F f x).isIso_hom

end AlgebraicGeometry.Scheme.SmoothSite
