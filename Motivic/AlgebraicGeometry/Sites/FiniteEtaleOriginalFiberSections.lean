/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleFieldObjectEvaluation
public import Motivic.Aglib.AlgebraicGeometry.EtaleOriginalFiberCoproduct

/-! # Sections on an étale fiber, indexed by original points -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u w
namespace Motivic.FiniteEtaleSite
variable {X : Scheme.{u}} (V : FiniteEtaleSite X) (x : X)

instance originalFiberFieldMap_etale (v : V.hom ⁻¹' {x}) :
    Etale (V.hom.originalFiberFieldMap x v) := by
  rcases v with ⟨v, hv⟩
  change V.hom v = x at hv
  subst x
  exact inferInstanceAs (Etale (Spec.map (V.hom.residueFieldMap v)))

/-- The literal original residue-field object above the chosen base point. -/
def originalFiberObject (v : V.hom ⁻¹' {x}) :
    FiniteEtaleSite (Spec (X.residueField x)) :=
  fieldObject (V.left.residueField v.1) (V.hom.originalFiberFieldMap x v)

/-- The actual component inclusion into the base-changed object. -/
def originalFiberObjectHom (v : V.hom ⁻¹' {x}) :
    originalFiberObject V x v ⟶ (baseChange (X.fromSpecResidueField x)).obj V :=
  MorphismProperty.Over.homMk (V.hom.originalFiberComponent x v)
    (V.hom.originalFiberComponent_fiberToSpecResidueField x v)

instance originalFiberObjectHom_mono (v : V.hom ⁻¹' {x}) :
    Mono (originalFiberObjectHom V x v) :=
  (forgetScheme _).mono_of_mono_map (by
    change Mono (V.hom.originalFiberComponent x v)
    infer_instance)

/-- The original components are an actual small-site Nisnevich cover. -/
theorem originalFiberObjects_mem_precoverage :
    Presieve.ofArrows (originalFiberObject V x) (originalFiberObjectHom V x) ∈
      nisnevichPrecoverage (Spec (X.residueField x))
        ((baseChange (X.fromSpecResidueField x)).obj V) := by
  apply (ofArrows_mem_nisnevichPrecoverage_iff _).mpr
  refine ⟨fun v ↦ ?_, fun z ↦ ?_⟩
  · change Etale (V.hom.originalFiberComponent x v)
    infer_instance
  · refine ⟨V.hom.fiberHomeo x z, IsLocalRing.closedPoint _, ?_, ?_⟩
    · exact (V.hom.originalFiberComponent_apply x _ _).trans
        ((V.hom.fiberHomeo x).symm_apply_apply z)
    · change IsIso ((V.hom.originalFiberComponent x _).residueFieldMap _)
      infer_instance

/-- Restriction to the original components is bijective for ordinary sheaves. -/
theorem originalFiber_restriction_bijective
    (P : (FiniteEtaleSite (Spec (X.residueField x)))ᵒᵖ ⥤ Type w)
    (hP : Presieve.IsSheaf (nisnevichTopology (Spec (X.residueField x))) P) :
    Function.Bijective (fun s : P.obj (op ((baseChange (X.fromSpecResidueField x)).obj V)) ↦
      fun v : V.hom ⁻¹' {x} ↦ P.map (originalFiberObjectHom V x v).op s) := by
  have h := hP.isSheafFor _
    (Precoverage.generate_mem_toGrothendieck (originalFiberObjects_mem_precoverage V x))
  constructor
  · intro s t hst
    apply h.isSeparatedFor.ext
    rintro W g ⟨v⟩
    exact congrFun hst v
  · intro s
    obtain ⟨t, ht, _⟩ := (Presieve.isSheafFor_arrows_iff _ _).mp h s (by
      intro i j W a b hab
      by_cases hij : i = j
      · subst j
        have hab' : a = b := (cancel_mono (originalFiberObjectHom V x i)).mp hab
        subst b
        rfl
      · have : IsEmpty W.left := ⟨fun w ↦ hij (by
          apply (V.hom.fiberHomeo x).symm.injective
          have hw := congrArg (fun f ↦ f.left w) hab
          change V.hom.originalFiberComponent x i (a.left w) =
            V.hom.originalFiberComponent x j (b.left w) at hw
          simpa only [Scheme.Hom.originalFiberComponent_apply] using hw)⟩
        have := sections_subsingleton_of_isEmpty P hP W
        exact Subsingleton.elim _ _)
    exact ⟨t, funext ht⟩

/-- Canonical additive restriction to original residue-field components. -/
def originalFiberRestriction
    (F : Sheaf (nisnevichTopology (Spec (X.residueField x))) AddCommGrpCat.{u + 1}) :
    F.obj.obj (op ((baseChange (X.fromSpecResidueField x)).obj V)) →+
      ∀ v : V.hom ⁻¹' {x}, F.obj.obj (op (originalFiberObject V x v)) where
  toFun s v := F.obj.map (originalFiberObjectHom V x v).op s
  map_zero' := funext fun _ ↦ map_zero _
  map_add' s t := funext fun _ ↦ map_add _ s t

/-- Ordinary fiber sections, without replacing any original residue field. -/
def originalFiberSectionsEquiv
    (F : Sheaf (nisnevichTopology (Spec (X.residueField x))) AddCommGrpCat.{u + 1}) :
    F.obj.obj (op ((baseChange (X.fromSpecResidueField x)).obj V)) ≃+
      ∀ v : V.hom ⁻¹' {x}, F.obj.obj (op (originalFiberObject V x v)) :=
  AddEquiv.ofBijective (originalFiberRestriction V x F)
    (originalFiber_restriction_bijective V x (F.obj ⋙ forget _) <|
      (isSheaf_iff_isSheaf_of_type _ _).mp <|
        Presheaf.isSheaf_comp_of_isSheaf _ _ (forget _) F.property)

@[simp]
theorem originalFiberSectionsEquiv_apply
    (F : Sheaf (nisnevichTopology (Spec (X.residueField x))) AddCommGrpCat.{u + 1})
    (s) (v : V.hom ⁻¹' {x}) :
    originalFiberSectionsEquiv V x F s v = F.obj.map (originalFiberObjectHom V x v).op s := rfl

/-- Coefficient naturality retains the actual restriction maps. -/
theorem originalFiberSectionsEquiv_naturality
    {F G : Sheaf (nisnevichTopology (Spec (X.residueField x))) AddCommGrpCat.{u + 1}}
    (a : F ⟶ G) (s) :
    originalFiberSectionsEquiv V x G
        (a.hom.app (op ((baseChange (X.fromSpecResidueField x)).obj V)) s) =
      fun v ↦ a.hom.app (op (originalFiberObject V x v))
        (originalFiberSectionsEquiv V x F s v) := by
  funext v
  exact (ConcreteCategory.congr_hom (a.hom.naturality (originalFiberObjectHom V x v).op) s).symm

variable {V} {U : FiniteEtaleSite X} (g : U ⟶ V)

/-- The map of original fiber indices is the original map of scheme points. -/
def originalFiberIndex (v : U.hom ⁻¹' {x}) : V.hom ⁻¹' {x} :=
  ⟨g.left v.1, by
    change (g.left ≫ V.hom) v.1 = x
    rw [MorphismProperty.Over.w]
    exact v.2⟩

/-- The component arrow retains the literal native residue-field homomorphism. -/
def originalFiberObjectMap (v : U.hom ⁻¹' {x}) :
    originalFiberObject U x v ⟶ originalFiberObject V x (originalFiberIndex x g v) :=
  MorphismProperty.Over.homMk (Spec.map (g.left.residueFieldMap v.1)) (by
    apply (cancel_mono (X.fromSpecResidueField x)).mp
    have fac (W : FiniteEtaleSite X) (w : W.hom ⁻¹' {x}) :
        W.hom.originalFiberFieldMap x w ≫ X.fromSpecResidueField x =
          W.left.fromSpecResidueField w.1 ≫ W.hom := by
      rcases w with ⟨w, hw⟩
      change W.hom w = x at hw
      subst x
      exact W.hom.SpecMap_residueFieldMap_fromSpecResidueField w
    change (Spec.map (g.left.residueFieldMap v.1) ≫
      V.hom.originalFiberFieldMap x (originalFiberIndex x g v)) ≫
        X.fromSpecResidueField x =
      U.hom.originalFiberFieldMap x v ≫ X.fromSpecResidueField x
    rw [Category.assoc, fac, ← Category.assoc]
    dsimp only [originalFiberIndex]
    rw [g.left.SpecMap_residueFieldMap_fromSpecResidueField]
    rw [Category.assoc, MorphismProperty.Over.w, fac])

/-- Actual component inclusions commute with the original base-change restriction. -/
@[reassoc]
theorem originalFiberObjectHom_naturality (v : U.hom ⁻¹' {x}) :
    originalFiberObjectHom U x v ≫ (baseChange (X.fromSpecResidueField x)).map g =
      originalFiberObjectMap x g v ≫
        originalFiberObjectHom V x (originalFiberIndex x g v) := by
  apply MorphismProperty.Over.Hom.ext
  change U.hom.originalFiberComponent x v ≫
      pullback.map U.hom (X.fromSpecResidueField x) V.hom (X.fromSpecResidueField x)
        g.left (𝟙 _) (𝟙 _) (by simp) (by simp) =
    Spec.map (g.left.residueFieldMap v.1) ≫
      V.hom.originalFiberComponent x (originalFiberIndex x g v)
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.map, pullback.lift_fst]
    change U.hom.originalFiberComponent x v ≫ (U.hom.fiberι x ≫ g.left) =
      Spec.map (g.left.residueFieldMap v.1) ≫
        (V.hom.originalFiberComponent x (originalFiberIndex x g v) ≫ V.hom.fiberι x)
    rw [← Category.assoc, Scheme.Hom.originalFiberComponent_fiberι,
      Scheme.Hom.originalFiberComponent_fiberι]
    dsimp only [originalFiberIndex]
    exact (g.left.SpecMap_residueFieldMap_fromSpecResidueField v.1).symm
  · simp only [Category.assoc, pullback.map, pullback.lift_snd, Category.comp_id]
    change U.hom.originalFiberComponent x v ≫ U.hom.fiberToSpecResidueField x =
      Spec.map (g.left.residueFieldMap v.1) ≫
        (V.hom.originalFiberComponent x (originalFiberIndex x g v) ≫
          V.hom.fiberToSpecResidueField x)
    rw [Scheme.Hom.originalFiberComponent_fiberToSpecResidueField,
      Scheme.Hom.originalFiberComponent_fiberToSpecResidueField]
    exact (MorphismProperty.Over.w (originalFiberObjectMap x g v)).symm

/-- Restriction in the original étale object agrees with literal residue-field restriction. -/
theorem originalFiberSectionsEquiv_map
    (F : Sheaf (nisnevichTopology (Spec (X.residueField x))) AddCommGrpCat.{u + 1})
    (s : F.obj.obj (op ((baseChange (X.fromSpecResidueField x)).obj V)))
    (v : U.hom ⁻¹' {x}) :
    originalFiberSectionsEquiv U x F
        (F.obj.map ((baseChange (X.fromSpecResidueField x)).map g).op s) v =
      F.obj.map (originalFiberObjectMap x g v).op
        (originalFiberSectionsEquiv V x F s (originalFiberIndex x g v)) := by
  change (F.obj.map ((baseChange (X.fromSpecResidueField x)).map g).op ≫
    F.obj.map (originalFiberObjectHom U x v).op) s =
      (F.obj.map (originalFiberObjectHom V x (originalFiberIndex x g v)).op ≫
        F.obj.map (originalFiberObjectMap x g v).op) s
  rw [← F.obj.map_comp, ← F.obj.map_comp, ← op_comp, ← op_comp,
    originalFiberObjectHom_naturality]

end Motivic.FiniteEtaleSite
