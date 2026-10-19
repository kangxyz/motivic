/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Actual affine witnesses in their canonical Weil-restriction coordinates

The algebra and whole marking are derived from actual scheme morphisms using
canonical isoSpec and the full faithfulness of Spec. No affine comparison
isomorphism or algebraic marking is an independent input.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.AffineWeilRestriction

variable {B : Type u} [CommRing B] {E : Scheme.{u}} [IsAffine E]
variable (f : E ⟶ Spec (.of B))

/-- The action on the actual coordinate ring induced by the original affine witness. -/
@[instance_reducible] def witnessAlgebra : Algebra B Γ(E, ⊤) :=
  (Spec.preimage (E.isoSpec.inv ≫ f)).hom.toAlgebra

/-- The coordinate projection is literally the original morphism through canonical isoSpec. -/
theorem witnessAlgebra_projection :
    letI := witnessAlgebra f
    Spec.algebraMap B Γ(E, ⊤) = E.isoSpec.inv ≫ f := by
  let := witnessAlgebra f
  exact Spec.map_preimage (E.isoSpec.inv ≫ f)

/-- Étaleness of the actual witness proves étaleness of its actual coordinate algebra. -/
theorem witnessAlgebra_etale [Etale f] :
    letI := witnessAlgebra f
    Algebra.Etale B Γ(E, ⊤) := by
  let := witnessAlgebra f
  apply RingHom.etale_algebraMap.mp
  apply (HasRingHomProperty.Spec_iff (P := @Etale)).mp
  rw [Spec.map_preimage]
  infer_instance

variable {U : Type u} [CommRing U] [Algebra B U]
variable (s : Spec (.of U) ⟶ E) (hs : s ≫ f = Spec.algebraMap B U)

/-- The coordinate algebra map of the prescribed whole marking. -/
def witnessMarkHom :
    letI := witnessAlgebra f
    Γ(E, ⊤) →ₐ[B] U := by
  let := witnessAlgebra f
  refine { __ := (Spec.preimage (s ≫ E.isoSpec.hom)).hom, commutes' := ?_ }
  intro b
  have h : CommRingCat.ofHom (algebraMap B Γ(E, ⊤)) ≫
      Spec.preimage (s ≫ E.isoSpec.hom) = CommRingCat.ofHom (algebraMap B U) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage]
    change (s ≫ E.isoSpec.hom) ≫ Spec.algebraMap B Γ(E, ⊤) = Spec.algebraMap B U
    rw [witnessAlgebra_projection]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hs
  exact ConcreteCategory.congr_hom h b

/-- Passing to coordinates and back recovers the entire original marking. -/
theorem witnessMarkHom_spec :
    letI := witnessAlgebra f
    Spec.map (CommRingCat.ofHom (witnessMarkHom f s hs).toRingHom) ≫ E.isoSpec.inv = s := by
  let := witnessAlgebra f
  change Spec.map (Spec.preimage (s ≫ E.isoSpec.hom)) ≫ E.isoSpec.inv = s
  rw [Spec.map_preimage, Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable {A T : Type u} [CommRing A] [CommRing T] [Algebra A B] [Algebra A T]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- An actual marking on the whole scalar pullback supplies the exact tensor-valued ring map. -/
def witnessScalarMarkHom
    (t : pullback (Spec.algebraMap A T) (Spec.algebraMap A B) ⟶ E)
    (ht : t ≫ f = pullback.snd (Spec.algebraMap A T) (Spec.algebraMap A B)) :
    letI := witnessAlgebra f
    Γ(E, ⊤) →ₐ[B] T ⊗[A] B :=
  witnessMarkHom f ((pullbackSpecIso A T B).inv ≫ t) (by
    rw [Category.assoc, ht]
    exact pullbackSpecIso_inv_snd A T B)

/-- The tensor-coordinate marking recovers the actual whole scalar marking, including nilpotents. -/
theorem witnessScalarMarkHom_spec
    (t : pullback (Spec.algebraMap A T) (Spec.algebraMap A B) ⟶ E)
    (ht : t ≫ f = pullback.snd (Spec.algebraMap A T) (Spec.algebraMap A B)) :
    letI := witnessAlgebra f
    (pullbackSpecIso A T B).hom ≫
      Spec.map (CommRingCat.ofHom (witnessScalarMarkHom f t ht).toRingHom) ≫
        E.isoSpec.inv = t := by
  let := witnessAlgebra f
  rw [witnessScalarMarkHom, witnessMarkHom_spec]
  exact (pullbackSpecIso A T B).hom_inv_id_assoc t

end AlgebraicGeometry.AffineWeilRestriction
