/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleFieldEvaluation
public import Motivic.Aglib.AlgebraicGeometry.EtaleFieldCoproduct

/-! # Exact evaluation on actual finite étale objects over a field

The canonical residue-field inclusions are a finite disjoint Nisnevich cover.
The ordinary sheaf condition identifies sections with the product of sections on
those literal components. This proves exactness of evaluation without asserting
that the topology on disconnected objects is trivial.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u w

namespace Motivic.FiniteEtaleSite

section Empty

variable {S : Scheme.{u}} (P : (FiniteEtaleSite S)ᵒᵖ ⥤ Type w)
  (hP : Presieve.IsSheaf (nisnevichTopology S) P)

include hP

/-- The empty Nisnevich cover forces sections on an empty scheme to be unique. -/
theorem sections_subsingleton_of_isEmpty (V : FiniteEtaleSite S) [IsEmpty V.left] :
    Subsingleton (P.obj (op V)) := by
  let Y : Empty → FiniteEtaleSite S := Empty.elim
  let f : ∀ i, Y i ⟶ V := fun i ↦ i.elim
  have hf : Presieve.ofArrows Y f ∈ nisnevichPrecoverage S V := by
    apply (ofArrows_mem_nisnevichPrecoverage_iff f).mpr
    exact ⟨fun i ↦ i.elim, fun v ↦ isEmptyElim v⟩
  have h := hP.isSheafFor _ (Precoverage.generate_mem_toGrothendieck hf)
  refine ⟨fun x y ↦ h.isSeparatedFor.ext ?_⟩
  rintro W g ⟨i⟩
  exact i.elim

end Empty

section Field

variable {K : Type u} [Field K] (V : FiniteEtaleSite (Spec (.of K)))

local instance : DiscreteTopology V.left :=
  Scheme.discreteTopology_of_etale_over_field V.hom

local instance : IsReduced V.left :=
  Scheme.isReduced_of_etale_over_field V.hom

/-- The literal residue-field component, retaining its composite structure map. -/
def residueComponent (v : V.left) : FiniteEtaleSite (Spec (.of K)) :=
  fieldObject (V.left.residueField v) (V.left.fromSpecResidueField v ≫ V.hom)

/-- The component inclusion is the original canonical residue-field morphism. -/
def residueComponentHom (v : V.left) : residueComponent V v ⟶ V :=
  MorphismProperty.Over.homMk (V.left.fromSpecResidueField v) rfl

@[simp]
theorem residueComponentHom_left (v : V.left) :
    (residueComponentHom V v).left = V.left.fromSpecResidueField v := rfl

instance (v : V.left) : Mono (residueComponentHom V v) :=
  (forgetScheme _).mono_of_mono_map (by
    change Mono (V.left.fromSpecResidueField v)
    infer_instance)

/-- The actual residue components form a Nisnevich covering family. -/
theorem residueComponents_mem_precoverage :
    Presieve.ofArrows (residueComponent V) (residueComponentHom V) ∈
      nisnevichPrecoverage (Spec (.of K)) V := by
  apply (ofArrows_mem_nisnevichPrecoverage_iff _).mpr
  refine ⟨fun v ↦ ?_, fun v ↦ ?_⟩
  · change Etale (V.left.fromSpecResidueField v)
    infer_instance
  · refine ⟨v, IsLocalRing.closedPoint _, V.left.fromSpecResidueField_apply _ _, ?_⟩
    have : IsOpenImmersion (V.left.fromSpecResidueField v) := inferInstance
    change IsIso ((V.left.fromSpecResidueField v).residueFieldMap _)
    infer_instance

/-- The component family is finite because the original structure morphism is quasi-compact. -/
theorem finite_residueComponents : Finite V.left :=
  Scheme.finite_of_etale_over_field V.hom

/-- Restriction to the actual disjoint components is bijective for ordinary sheaves. -/
theorem residueComponent_restriction_bijective
    (P : (FiniteEtaleSite (Spec (.of K)))ᵒᵖ ⥤ Type w)
    (hP : Presieve.IsSheaf (nisnevichTopology (Spec (.of K))) P) :
    Function.Bijective (fun s : P.obj (op V) ↦
      fun v : V.left ↦ P.map (residueComponentHom V v).op s) := by
  have h := hP.isSheafFor _
    (Precoverage.generate_mem_toGrothendieck (residueComponents_mem_precoverage V))
  constructor
  · intro s t hst
    apply h.isSeparatedFor.ext
    rintro W g ⟨v⟩
    exact congrFun hst v
  · intro x
    obtain ⟨s, hs, _⟩ := (Presieve.isSheafFor_arrows_iff _ _).mp h x (by
      intro i j W a b hab
      by_cases hij : i = j
      · subst j
        have hab' : a = b := (cancel_mono (residueComponentHom V i)).mp hab
        subst b
        rfl
      · have : IsEmpty W.left := ⟨fun w ↦ hij (by
          have hw := congrArg (fun f : W ⟶ V ↦ f.left w) hab
          change V.left.fromSpecResidueField i (a.left w) =
            V.left.fromSpecResidueField j (b.left w) at hw
          exact (V.left.fromSpecResidueField_apply i (a.left w)).symm.trans
            (hw.trans (V.left.fromSpecResidueField_apply j (b.left w))))⟩
        have := sections_subsingleton_of_isEmpty P hP W
        exact Subsingleton.elim _ _)
    exact ⟨s, funext hs⟩

/-- The canonical additive restriction map to all actual residue components. -/
def residueComponentRestriction
    (F : Sheaf (nisnevichTopology (Spec (.of K))) AddCommGrpCat.{u + 1}) :
    F.obj.obj (op V) →+ ∀ v : V.left, F.obj.obj (op (residueComponent V v)) where
  toFun s v := F.obj.map (residueComponentHom V v).op s
  map_zero' := funext fun _ ↦ map_zero _
  map_add' s t := funext fun _ ↦ map_add _ s t

/-- Ordinary sections are the product of their literal residue-field restrictions. -/
def residueComponentSectionsEquiv
    (F : Sheaf (nisnevichTopology (Spec (.of K))) AddCommGrpCat.{u + 1}) :
    F.obj.obj (op V) ≃+ ∀ v : V.left, F.obj.obj (op (residueComponent V v)) :=
  AddEquiv.ofBijective (residueComponentRestriction V F)
    (residueComponent_restriction_bijective V (F.obj ⋙ forget _) <|
      (isSheaf_iff_isSheaf_of_type _ _).mp <|
        Presheaf.isSheaf_comp_of_isSheaf _ _ (forget _) F.property)

@[simp]
theorem residueComponentSectionsEquiv_apply
    (F : Sheaf (nisnevichTopology (Spec (.of K))) AddCommGrpCat.{u + 1})
    (s : F.obj.obj (op V)) (v : V.left) :
    residueComponentSectionsEquiv V F s v = F.obj.map (residueComponentHom V v).op s := rfl

/-- The product identification is natural in the original ordinary coefficient sheaf. -/
theorem residueComponentSectionsEquiv_naturality
    {F G : Sheaf (nisnevichTopology (Spec (.of K))) AddCommGrpCat.{u + 1}}
    (a : F ⟶ G) (s : F.obj.obj (op V)) :
    residueComponentSectionsEquiv V G (a.hom.app (op V) s) =
      fun v ↦ a.hom.app (op (residueComponent V v))
        (residueComponentSectionsEquiv V F s v) := by
  funext v
  exact (ConcreteCategory.congr_hom (a.hom.naturality (residueComponentHom V v).op) s).symm

/-- Every ordinary sheaf epimorphism is surjective on every actual finite étale object. -/
theorem objectEvaluation_surjective_of_epi
    {F G : Sheaf (nisnevichTopology (Spec (.of K))) AddCommGrpCat.{u + 1}}
    (a : F ⟶ G) [Epi a] : Function.Surjective (a.hom.app (op V)) := by
  intro t
  have hv (v : V.left) := fieldEvaluation_surjective_of_epi (V.left.residueField v)
    (V.left.fromSpecResidueField v ≫ V.hom) a
    (G.obj.map (residueComponentHom V v).op t)
  choose s hs using hv
  refine ⟨(residueComponentSectionsEquiv V F).symm s, ?_⟩
  apply (residueComponentSectionsEquiv V G).injective
  rw [residueComponentSectionsEquiv_naturality, AddEquiv.apply_symm_apply]
  exact funext hs

/-- Evaluation retains the actual object and its original sheaf sections. -/
def objectEvaluation : Sheaf (nisnevichTopology (Spec (.of K))) AddCommGrpCat.{u + 1} ⥤
    AddCommGrpCat.{u + 1} :=
  sheafToPresheaf _ _ ⋙ (evaluation (FiniteEtaleSite (Spec (.of K)))ᵒᵖ _).obj (op V)

instance : (objectEvaluation V).Additive := by
  unfold objectEvaluation
  infer_instance

instance : PreservesFiniteLimits (objectEvaluation V) := by
  unfold objectEvaluation
  infer_instance

instance : (objectEvaluation V).PreservesEpimorphisms where
  preserves a := (AddCommGrpCat.epi_iff_surjective ((objectEvaluation V).map a)).mpr
    (objectEvaluation_surjective_of_epi V a)

instance : (objectEvaluation V).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels (objectEvaluation V)

/-- Ordinary short exact sequences remain exact on arbitrary finite étale field objects. -/
theorem objectEvaluation_shortExact
    (C : ShortComplex (Sheaf (nisnevichTopology (Spec (.of K))) AddCommGrpCat.{u + 1}))
    (hC : C.ShortExact) : (C.map (objectEvaluation V)).ShortExact := by
  have := hC.mono_f
  have := hC.epi_g
  exact hC.map (objectEvaluation V)

end Field

end Motivic.FiniteEtaleSite
