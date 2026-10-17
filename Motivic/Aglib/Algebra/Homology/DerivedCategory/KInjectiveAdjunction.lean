/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.HomotopyCategory.Adjunction
public import Motivic.Aglib.Algebra.Homology.DerivedCategory.ExtRightDerived

/-! # The actual adjunction on derived morphisms into K-injective complexes -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
universe w₁ w₂ v₁ v₂ u₁ u₂
namespace CochainComplex.IsKInjective
variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  (K J : CochainComplex C ℤ) [J.IsKInjective]

/-- Localizing homotopy classes into a K-injective complex is an actual additive equivalence. -/
def localizedHomAddEquiv :
    ((HomotopyCategory.quotient C (.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj J) ≃+
      (DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj J) :=
  (AddEquiv.ofBijective DerivedCategory.Qh.mapAddHom
    (Qh_map_bijective _ J)).trans
      (CategoryTheory.Iso.homCongrAddEquiv
        ((DerivedCategory.quotientCompQhIso C).app K)
        ((DerivedCategory.quotientCompQhIso C).app J))

/-- The equivalence sends an original chain map to its original localization. -/
@[simp]
theorem localizedHomAddEquiv_map (f : K ⟶ J) :
    localizedHomAddEquiv K J ((HomotopyCategory.quotient C (.up ℤ)).map f) =
      DerivedCategory.Q.map f := by
  change (DerivedCategory.quotientCompQhIso C).inv.app K ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map f) ≫
      (DerivedCategory.quotientCompQhIso C).hom.app J = _
  erw [(DerivedCategory.quotientCompQhIso C).hom.naturality f]
  simp

/-- Every derived morphism into a K-injective complex has an original chain-map representative. -/
theorem Q_map_surjective :
    Function.Surjective (DerivedCategory.Q.map : (K ⟶ J) → _) := by
  intro x
  obtain ⟨f, rfl⟩ := (localizedHomAddEquiv K J).surjective x
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective f
  exact ⟨f, (localizedHomAddEquiv_map K J f).symm⟩

end CochainComplex.IsKInjective

namespace CategoryTheory.Adjunction
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive] (adj : L ⊣ R)
  (K : CochainComplex C ℤ) (J : CochainComplex D ℤ)
  [J.IsKInjective] [CochainComplex.IsKInjective ((R.mapHomologicalComplex (.up ℤ)).obj J)]

/-- The derived Hom adjunction is constructed on the actual K-injective targets. -/
def kInjectiveHomAddEquiv :
    (DerivedCategory.Q.obj K ⟶
      DerivedCategory.Q.obj ((R.mapHomologicalComplex (.up ℤ)).obj J)) ≃+
    (DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      DerivedCategory.Q.obj J) :=
  (CochainComplex.IsKInjective.localizedHomAddEquiv K _).symm.trans
    (((adj.homotopyAdjunction (.up ℤ)).homAddEquiv _ _).symm.trans
      (CochainComplex.IsKInjective.localizedHomAddEquiv _ J))

/-- On original chain maps this is exactly inverse image followed by the original counit. -/
theorem kInjectiveHomAddEquiv_map
    (f : K ⟶ (R.mapHomologicalComplex (.up ℤ)).obj J) :
    adj.kInjectiveHomAddEquiv K J (DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((L.mapHomologicalComplex (.up ℤ)).map f ≫
        (NatTrans.mapHomologicalComplex adj.counit (.up ℤ)).app J) := by
  rw [← CochainComplex.IsKInjective.localizedHomAddEquiv_map K _ f]
  simp only [kInjectiveHomAddEquiv, AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
  change CochainComplex.IsKInjective.localizedHomAddEquiv _ J
    ((L.mapHomotopyCategory (.up ℤ)).map
      ((HomotopyCategory.quotient C (.up ℤ)).map f) ≫
        (adj.homotopyAdjunction (.up ℤ)).counit.app _) = _
  change CochainComplex.IsKInjective.localizedHomAddEquiv _ J
    ((HomotopyCategory.quotient D (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient D (.up ℤ)).map _) = _
  rw [← Functor.map_comp, CochainComplex.IsKInjective.localizedHomAddEquiv_map]

end CategoryTheory.Adjunction
