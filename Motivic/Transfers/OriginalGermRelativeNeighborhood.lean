/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.OriginalGermEtalePullback

/-!
# Original germs over an étale ambient scheme

The chosen field is the actual residue field of the source point, not necessarily
the residue field of its image. Composition of pointed neighborhoods is initial;
thus changing this ambient scheme does not change the original germ colimit.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u v w
namespace Motivic.SmoothSite
variable {S : Scheme.{u}} {U X : SmoothSite S} (f : U ⟶ X) (u : U.left)

/-- Étale neighborhoods of the actual field-valued point obtained from `(U,u)`. -/
abbrev RelativePointedEtaleNeighborhood :=
  (Scheme.Etale.forget X.left ⋙ coyoneda.obj
    (op (Over.mk (U.left.fromSpecResidueField u ≫ f.left)))).Elements

/-- Retain precisely the neighborhoods which belong to the original smooth site. -/
def relativeSmoothNeighborhoodProperty : ObjectProperty (RelativePointedEtaleNeighborhood f u) :=
  fun N => smoothSeparatedFiniteType (N.obj.hom ≫ X.hom)

/-- Pointed neighborhoods using the original source residue field over the ambient scheme. -/
abbrev RelativeNisnevichNeighborhood := (relativeSmoothNeighborhoodProperty f u).FullSubcategory

namespace RelativeNisnevichNeighborhood

/-- The underlying object of the original smooth site. -/
def forget : RelativeNisnevichNeighborhood f u ⥤ SmoothSite S where
  obj N := MorphismProperty.Over.mk ⊤ (N.obj.obj.hom ≫ X.hom) N.property
  map {N M} q := homMk q.hom.hom.left (by
    change q.hom.hom.left ≫ (M.obj.obj.hom ≫ X.hom) = N.obj.obj.hom ≫ X.hom
    rw [← Category.assoc, MorphismProperty.Over.w])

/-- The actual structural map of a relative neighborhood. -/
def toBase (N : RelativeNisnevichNeighborhood f u) : (forget f u).obj N ⟶ X :=
  homMk N.obj.obj.hom rfl

instance (N : RelativeNisnevichNeighborhood f u) : Etale (toBase f u N).left :=
  inferInstanceAs (Etale N.obj.obj.hom)

variable [Etale f.left]

/-- Compose an original neighborhood with the given étale map, leaving its field point unchanged. -/
def compose (M : NisnevichNeighborhood U u) : RelativeNisnevichNeighborhood f u :=
  ⟨Functor.elementsMk _ (Scheme.Etale.mk (M.toBase.left ≫ f.left))
    (Over.homMk M.obj.val.left (by
      change M.obj.val.left ≫ (M.toBase.left ≫ f.left) =
        U.left.fromSpecResidueField u ≫ f.left
      rw [← Category.assoc]
      exact congrArg (fun t => t ≫ f.left) (Over.w M.obj.val))), by
    change smoothSeparatedFiniteType ((M.toBase.left ≫ f.left) ≫ X.hom)
    rw [Category.assoc, MorphismProperty.Over.w]
    exact M.property⟩

/-- Composition on actual pointed refinements. -/
def composeMap {M N : NisnevichNeighborhood U u} (q : M ⟶ N) :
    compose f u M ⟶ compose f u N :=
  ObjectProperty.homMk (Functor.Elements.homMk
    (MorphismProperty.Over.homMk q.hom.hom.left (by
      change q.hom.hom.left ≫ (N.toBase.left ≫ f.left) = M.toBase.left ≫ f.left
      rw [← Category.assoc]
      exact congrArg (fun t => t ≫ f.left) (MorphismProperty.Over.w q.hom.hom))) (by
      apply Over.OverMorphism.ext
      exact NisnevichNeighborhood.refinement_point q))

/-- The actual composition functor whose initiality compares the two germ diagrams. -/
def composeFunctor : NisnevichNeighborhood U u ⥤ RelativeNisnevichNeighborhood f u where
  obj := compose f u
  map := composeMap f u
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Pull back a relative neighborhood along the original étale map. -/
def pullbackNeighborhood (N : RelativeNisnevichNeighborhood f u) : NisnevichNeighborhood U u :=
  ⟨Functor.elementsMk _ (Scheme.Etale.mk (pullback.snd (toBase f u N).left f.left))
    (Over.homMk
      (pullback.lift N.obj.val.left (U.left.fromSpecResidueField u) (Over.w N.obj.val))
      (pullback.lift_snd _ _ _)), by
    exact (etalePullback (toBase f u N) f).prop⟩

/-- The pullback projection is a genuine refinement of the relative neighborhood. -/
def pullbackToRelative (N : RelativeNisnevichNeighborhood f u) :
    compose f u (pullbackNeighborhood f u N) ⟶ N :=
  ObjectProperty.homMk (Functor.Elements.homMk
    (MorphismProperty.Over.homMk (pullback.fst (toBase f u N).left f.left)
      pullback.condition) (by
      apply Over.OverMorphism.ext
      exact pullback.lift_fst _ _ _))

/-- Lift an actual relative pointed map into the pullback neighborhood. -/
def liftToPullback {M : NisnevichNeighborhood U u} {N : RelativeNisnevichNeighborhood f u}
    (q : compose f u M ⟶ N) : M ⟶ pullbackNeighborhood f u N :=
  ObjectProperty.homMk (Functor.Elements.homMk
    (MorphismProperty.Over.homMk
      (pullback.lift q.hom.hom.left M.toBase.left (MorphismProperty.Over.w q.hom.hom))
      (pullback.lift_snd _ _ _)) (by
      apply Over.OverMorphism.ext
      change M.obj.val.left ≫
        pullback.lift q.hom.hom.left M.toBase.left (MorphismProperty.Over.w q.hom.hom) =
        pullback.lift N.obj.val.left (U.left.fromSpecResidueField u) (Over.w N.obj.val)
      apply pullback.hom_ext
      · exact (Category.assoc _ _ _).trans
          ((congrArg (fun t => M.obj.val.left ≫ t) (pullback.lift_fst _ _ _)).trans
            ((congrArg (fun t => t.left) q.hom.map_val).trans
              (pullback.lift_fst _ _ _).symm))
      · exact (Category.assoc _ _ _).trans
          ((congrArg (fun t => M.obj.val.left ≫ t) (pullback.lift_snd _ _ _)).trans
            ((Over.w M.obj.val).trans (pullback.lift_snd _ _ _).symm))))

/-- Initiality is proved by actual pointed pullbacks and cofiltered equalizers,
without identifying the residue fields of the source and its image. -/
instance composeFunctor_initial [IsAffine S] : (composeFunctor f u).Initial := by
  apply Functor.initial_of_exists_of_isCofiltered
  · intro N
    exact ⟨pullbackNeighborhood f u N, ⟨pullbackToRelative f u N⟩⟩
  · intro N M a b
    let a' := liftToPullback f u a
    let b' := liftToPullback f u b
    refine ⟨IsCofiltered.eq a' b', IsCofiltered.eqHom a' b', ?_⟩
    have h := IsCofiltered.eq_condition a' b'
    have h' := congrArg (fun q => q.hom.hom.left ≫
      pullback.fst (toBase f u N).left f.left) h
    apply ObjectProperty.hom_ext
    apply Functor.Elements.hom_ext
    apply MorphismProperty.Over.Hom.ext
    change (IsCofiltered.eqHom a' b').hom.hom.left ≫ a.hom.hom.left =
      (IsCofiltered.eqHom a' b').hom.hom.left ≫ b.hom.hom.left
    change (IsCofiltered.eqHom a' b').hom.hom.left ≫
      (a'.hom.hom.left ≫ pullback.fst (toBase f u N).left f.left) =
      (IsCofiltered.eqHom a' b').hom.hom.left ≫
      (b'.hom.hom.left ≫ pullback.fst (toBase f u N).left f.left) at h'
    have ha : a'.hom.hom.left ≫ pullback.fst (toBase f u N).left f.left =
        a.hom.hom.left := pullback.lift_fst _ _ _
    have hb : b'.hom.hom.left ≫ pullback.fst (toBase f u N).left f.left =
        b.hom.hom.left := pullback.lift_fst _ _ _
    rw [ha, hb] at h'
    exact h'


/-- The underlying neighborhoods agree by the literal identity on their schemes. -/
def composeForgetIso : composeFunctor f u ⋙ forget f u ≅ nisnevichNeighborhoodFunctor U u :=
  NatIso.ofComponents (fun M => MorphismProperty.Over.isoMk (Iso.refl _) (by
    change (𝟙 _) ≫ (M.toBase.left ≫ U.hom) = (M.toBase.left ≫ f.left) ≫ X.hom
    exact (Category.id_comp _).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun t => M.toBase.left ≫ t) (MorphismProperty.Over.w f))).symm)) (by
      intro M N q
      apply MorphismProperty.Over.Hom.ext
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

variable [IsAffine S] {A : Type v} [Category.{w} A]
  [HasColimitsOfSize.{u + 1, u + 1} A]
  (F : (SmoothSite S)ᵒᵖ ⥤ A)

instance sourceDiagramHasColimit : HasColimit ((nisnevichNeighborhoodFunctor U u).op ⋙ F) :=
  ⟨⟨_, isColimitNisnevichPointFiberCocone U u F⟩⟩

instance relativeDiagramHasColimit : HasColimit ((forget f u).op ⋙ F) := by
  let : HasColimit ((composeFunctor f u).op ⋙ (forget f u).op ⋙ F) :=
    hasColimit_of_iso (Functor.isoWhiskerRight (NatIso.op (composeForgetIso f u).symm) F)
  exact Functor.Final.hasColimit_of_comp (composeFunctor f u).op

/-- The relative pointed-neighborhood colimit is the original source germ.
There is no residue-isomorphism hypothesis on the ambient étale map. -/
def originalFiberIso : colimit ((forget f u).op ⋙ F) ≅
    (nisnevichPointFiberCocone U u F).pt :=
  (Functor.Final.colimitIso (composeFunctor f u).op ((forget f u).op ⋙ F)).symm ≪≫
    HasColimit.isoOfNatIso (Functor.isoWhiskerRight (NatIso.op (composeForgetIso f u).symm) F) ≪≫
    colimit.isoColimitCocone ⟨_, isColimitNisnevichPointFiberCocone U u F⟩


/-- The comparison preserves each original representative using the literal
identity of underlying neighborhood schemes. -/
@[reassoc]
theorem originalFiberIso_ι (M : NisnevichNeighborhood U u) :
    colimit.ι ((forget f u).op ⋙ F) (op (compose f u M)) ≫
        (originalFiberIso f u F).hom =
      F.map ((composeForgetIso f u).app M).inv.op ≫
        (nisnevichPointFiberCocone U u F).ι.app (op M) := by
  dsimp only [originalFiberIso, Iso.trans_hom, Iso.symm_hom]
  erw [Functor.Final.ι_colimitIso_inv_assoc (composeFunctor f u).op
    ((forget f u).op ⋙ F) (op M)]
  rw [HasColimit.ι_isoOfNatIso_hom_assoc, colimit.isoColimitCocone_ι_hom]
  rfl

end RelativeNisnevichNeighborhood
end Motivic.SmoothSite
