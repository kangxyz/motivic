/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleImageFamily
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleImageExact
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleInjectives
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleFieldDirectImageExact
public import Motivic.Cohomology.SheafProductShortExact
public import Motivic.Cohomology.ExtAcyclicResolutionSteps

/-! # Actual injective steps for products of residue-field direct images

Each step chooses the ordinary injective embedding on each field site and its
actual cokernel. Only the proved sectionwise epimorphisms from field direct images
are multiplied. No arbitrary exactness of sheaf products is asserted.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite AlgebraicGeometry
universe w u
namespace Motivic.FiniteEtaleSite
variable {I : Type u} {X : Scheme.{u}} (K : I → Type u) [∀ i, Field (K i)]
  (b : ∀ i, Spec (.of (K i)) ⟶ X)

/-- The original ordinary coefficient family on the specified field sites. -/
abbrev FieldCoefficientFamily := ImageFamily (fun i => Spec (.of (K i)))

/-- The actual product of the genuine field direct images. -/
abbrev fieldFamilyProduct (A : FieldCoefficientFamily K) :
    Sheaf (nisnevichTopology X) AddCommGrpCat.{u + 1} :=
  (productDirectImage (fun i => Spec (.of (K i))) b).obj A

/-- The next coefficient family is the actual cokernel of each injective embedding. -/
def fieldFamilyQuotient (A : FieldCoefficientFamily K) : FieldCoefficientFamily K :=
  fun i => cokernel (Injective.ι (A i))

/-- Each field contributes its ordinary injective embedding and its actual cokernel. -/
def fieldFamilyStep (A : FieldCoefficientFamily K) (i : I) :
    ShortComplex (Sheaf (nisnevichTopology (Spec (.of (K i)))) AddCommGrpCat.{u + 1}) :=
  ShortComplex.mk (Injective.ι (A i)) (cokernel.π (Injective.ι (A i)))
    (cokernel.condition (Injective.ι (A i)))

/-- These chosen coefficient steps are genuinely short exact. -/
theorem fieldFamilyStep_shortExact (A : FieldCoefficientFamily K) (i : I) :
    (fieldFamilyStep K A i).ShortExact :=
  { exact := ShortComplex.exact_of_g_is_cokernel _
      (cokernelIsCokernel (Injective.ι (A i)))
    mono_f := inferInstanceAs (Mono (Injective.ι (A i)))
    epi_g := inferInstanceAs (Epi (cokernel.π (Injective.ι (A i)))) }

/-- Pushing the chosen field steps and taking their actual product. -/
def fieldFamilyProductStep (A : FieldCoefficientFamily K) :
    ShortComplex (Sheaf (nisnevichTopology X) AddCommGrpCat.{u + 1}) :=
  SheafProduct.productComplex (nisnevichTopology X)
    (fun i => (fieldFamilyStep K A i).map (directImage (b i)))

/-- The injective term is an actual product of ordinary injective direct images. -/
instance fieldFamilyProductStep_injective (A : FieldCoefficientFamily K) :
    Injective (fieldFamilyProductStep K b A).X₂ := by
  change Injective (∏ᶜ fun i => (directImage (b i)).obj (Injective.under (A i)))
  infer_instance

/-- Sectionwise exactness of field direct images supplies the needed product epimorphism. -/
theorem fieldFamilyProductStep_presheaf_epi (A : FieldCoefficientFamily K) :
    Epi (fieldFamilyProductStep K b A).g.hom := by
  have (i : I) : Epi (((fieldFamilyStep K A i).map (directImage (b i))).g).hom :=
    fieldDirectImage_map_presheaf_epi (b i) (cokernel.π (Injective.ι (A i)))
  exact SheafProduct.presheaf_epi_piMap_of_presheaf_epi (nisnevichTopology X) _ _ _

/-- No sheaf-category AB4* assumption enters this actual product short exact sequence. -/
theorem fieldFamilyProductStep_shortExact (A : FieldCoefficientFamily K) :
    (fieldFamilyProductStep K b A).ShortExact := by
  have (i : I) : Epi (((fieldFamilyStep K A i).map (directImage (b i))).g).hom :=
    fieldDirectImage_map_presheaf_epi (b i) (cokernel.π (Injective.ι (A i)))
  exact SheafProduct.productComplex_shortExact (nisnevichTopology X) _
    (fun i => fieldDirectImage_shortExact (b i) _ (fieldFamilyStep_shortExact K A i))

/-- The actual free section source sees a surjection in each chosen injective step. -/
theorem fieldFamilyProductStep_hom_surjective (A : FieldCoefficientFamily K)
    (V : FiniteEtaleSite X) :
    Function.Surjective (fun s : Hypercohomology.freeAbelianSheaf.{u + 1, u, u + 1}
      (nisnevichTopology X) V ⟶ (fieldFamilyProductStep K b A).X₂ =>
        s ≫ (fieldFamilyProductStep K b A).g) := by
  have := fieldFamilyProductStep_presheaf_epi K b A
  have : Epi ((fieldFamilyProductStep K b A).g.hom.app (op V)) := inferInstance
  intro t
  obtain ⟨s, hs⟩ := (AddCommGrpCat.epi_iff_surjective _).mp this
    (Hypercohomology.sectionsEquiv.{u + 1, u, u + 1} (nisnevichTopology X) V _ t)
  refine ⟨(Hypercohomology.sectionsEquiv.{u + 1, u, u + 1} (nisnevichTopology X) V _).symm s, ?_⟩
  apply (Hypercohomology.sectionsEquiv.{u + 1, u, u + 1} (nisnevichTopology X) V _).injective
  rw [Hypercohomology.sectionsEquiv_naturality, Equiv.apply_symm_apply, hs]

/-- A concrete witness for the ordinary Ext resolution-step consumer. -/
theorem exists_fieldFamily_resolution_step (A : FieldCoefficientFamily K)
    (V : FiniteEtaleSite X) :
    ∃ (A' : FieldCoefficientFamily K)
      (J : Sheaf (nisnevichTopology X) AddCommGrpCat.{u + 1})
      (f : fieldFamilyProduct K b A ⟶ J) (g : J ⟶ fieldFamilyProduct K b A')
      (hfg : f ≫ g = 0),
      Injective J ∧ (ShortComplex.mk f g hfg).ShortExact ∧
        Function.Surjective (fun s : Hypercohomology.freeAbelianSheaf.{u + 1, u, u + 1}
          (nisnevichTopology X) V ⟶ J => s ≫ g) := by
  refine ⟨fieldFamilyQuotient K A, (fieldFamilyProductStep K b A).X₂,
    (fieldFamilyProductStep K b A).f, (fieldFamilyProductStep K b A).g,
    (fieldFamilyProductStep K b A).zero, inferInstance, ?_, ?_⟩
  · exact fieldFamilyProductStep_shortExact K b A
  · exact fieldFamilyProductStep_hom_surjective K b A V

variable [HasExt.{w} (Sheaf (nisnevichTopology X) AddCommGrpCat.{u + 1})]

/-- Every positive-degree ordinary cohomology class of the actual family product vanishes. -/
theorem fieldFamilyProduct_ext_succ_eq_zero (A : FieldCoefficientFamily K)
    (V : FiniteEtaleSite X) (n : ℕ)
    (e : Ext.{w} (Hypercohomology.freeAbelianSheaf.{u + 1, u, u + 1} (nisnevichTopology X) V)
      (fieldFamilyProduct K b A) (n + 1)) : e = 0 :=
  Cohomology.ext_eq_zero_of_resolution_steps (fieldFamilyProduct K b)
    (Hypercohomology.freeAbelianSheaf.{u + 1, u, u + 1} (nisnevichTopology X) V)
    (fun A => exists_fieldFamily_resolution_step K b A V) n A e

/-- The vanishing theorem consumes the unchanged ordinary small-site cohomology group. -/
theorem fieldFamilyProduct_H_succ_eq_zero (A : FieldCoefficientFamily K)
    (V : FiniteEtaleSite X) (n : ℕ)
    (e : SheafCohomology.H.{w, u + 1, u, u + 1} (nisnevichTopology X)
      (fieldFamilyProduct K b A) (n + 1) V) : e = 0 :=
  fieldFamilyProduct_ext_succ_eq_zero K b A V n e

end Motivic.FiniteEtaleSite
