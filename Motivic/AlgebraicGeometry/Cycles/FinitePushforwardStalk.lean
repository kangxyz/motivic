/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.RingTheory.Localization.FiniteFiberPoints
public import Motivic.AlgebraicGeometry.Modules.AffinePushforwardStalk
public import Motivic.AlgebraicGeometry.Cycles.FiniteStalkLength

/-!
# Actual scalar squares for finite pushforward stalks

The maximal points of the whole finite algebra over a target localization are
identified with source scheme stalks through the literal scheme stalk map.
The comparisons retain the scalar and residue maps needed for geometric length
and Euler formulas. Individual source stalks are not assumed finite over the
target stalk.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.FiniteFiber

variable {A B : CommRingCat.{u}} (f : A ⟶ B) (p : PrimeSpectrum A)
  (x : PrimeSpectrum B) (h : x.comap f.hom = p)

/-- The literal affine scheme stalk map, with its target point identified with p. -/
def pointedSpecStalkMap : (Spec A).presheaf.stalk p ⟶ (Spec B).presheaf.stalk x :=
  ((Spec A).presheaf.stalkCongr (.of_eq h.symm)).hom ≫ (Spec.map f).stalkMap x

/-- The pointed scheme map and prime-localization map form the actual scalar square. -/
@[reassoc]
theorem pointedSpecStalkMap_square :
    (Spec.stalkIso A p).hom ≫ CommRingCat.ofHom
        (Localization.localRingHom p.asIdeal x.asIdeal f.hom
          (congrArg PrimeSpectrum.asIdeal h.symm)) =
      pointedSpecStalkMap f p x h ≫ (Spec.stalkIso B x).hom := by
  subst p
  apply (cancel_mono (Spec.stalkIso B x).inv).mp
  simpa [pointedSpecStalkMap] using Scheme.localRingHom_comp_stalkIso f x

/-- The same scalar square solved for the actual scheme stalk map. -/
theorem pointedSpecStalkMap_eq :
    pointedSpecStalkMap f p x h =
      (Spec.stalkIso A p).hom ≫ CommRingCat.ofHom
        (Localization.localRingHom p.asIdeal x.asIdeal f.hom
          (congrArg PrimeSpectrum.asIdeal h.symm)) ≫ (Spec.stalkIso B x).inv := by
  rw [pointedSpecStalkMap_square_assoc, Iso.hom_inv_id, Category.comp_id]

/-- The actual pointed stalk map is local. -/
instance pointedSpecStalkMap_isLocalHom : IsLocalHom (pointedSpecStalkMap f p x h).hom := by
  subst p
  simpa [pointedSpecStalkMap] using
    (inferInstance : IsLocalHom ((Spec.map f).stalkMap x).hom)

/-- The residue map of the literal pointed scheme stalk map. -/
def pointedSpecResidueMap : (Spec A).residueField p ⟶ (Spec B).residueField x :=
  (Scheme.residueFieldCongr (X := Spec A) h.symm).hom ≫ (Spec.map f).residueFieldMap x

/-- Residues of actual stalk elements commute with the pointed map. -/
@[reassoc]
theorem pointedSpecStalkMap_residue :
    (Spec A).residue p ≫ pointedSpecResidueMap f p x h =
      pointedSpecStalkMap f p x h ≫ (Spec B).residue x := by
  subst p
  simp only [pointedSpecStalkMap, pointedSpecResidueMap, Scheme.residueFieldCongr_refl,
    Iso.refl_hom, TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp]
  ext z
  rfl

/-- The actual residue map is induced by the literal pointed stalk map. -/
theorem pointedSpecResidueMap_eq :
    (pointedSpecResidueMap f p x h).hom =
      IsLocalRing.ResidueField.map (pointedSpecStalkMap f p x h).hom := by
  subst p
  simp only [pointedSpecResidueMap, Scheme.residueFieldCongr_refl, Iso.refl_hom,
    Category.id_comp]
  simp [pointedSpecStalkMap, Scheme.Hom.residueFieldMap]

section Finite

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (A B : CommRingCat.{u}) [Algebra A B] [Module.Finite A B]
  (p : PrimeSpectrum A) (q : MaximalSpectrum (localAlgebra A B p))

/-- A localization of the whole finite algebra is the actual source structure stalk. -/
def sourceSchemeStalkIso :
    CommRingCat.of (Localization.AtPrime q.asIdeal) ≅
      (Spec B).presheaf.stalk (sourcePoint A B p q).1 :=
  (sourceLocalizationEquiv A B p q).toRingEquiv.toCommRingCatIso ≪≫
    (Spec.stalkIso B (sourcePoint A B p q).1).symm

/-- This comparison uses precisely the actual target-to-source scheme stalk scalar map. -/
theorem sourceSchemeStalkIso_base_square :
    CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal)) ≫ (sourceSchemeStalkIso A B p q).hom =
      (Spec.stalkIso A p).inv ≫
        pointedSpecStalkMap (A := A) (B := B) (CommRingCat.ofHom (algebraMap A B)) p
          (sourcePoint A B p q).1 (sourcePoint A B p q).2 := by
  have hs : (CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal)) : CommRingCat.of (Localization.AtPrime p.asIdeal) ⟶
        CommRingCat.of (Localization.AtPrime q.asIdeal)) ≫
      (sourceLocalizationEquiv A B p q).toRingEquiv.toCommRingCatIso.hom =
        CommRingCat.ofHom (sourceLocalMap A B p q) := by
    apply CommRingCat.hom_ext
    change (sourceLocalizationEquiv A B p q).toRingHom.comp
      (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)) = _
    exact sourceLocalizationEquiv_base_square A B p q
  rw [sourceSchemeStalkIso, Iso.trans_hom, ← Category.assoc, hs,
    pointedSpecStalkMap_eq]
  simp only [Iso.symm_hom, Iso.inv_hom_id_assoc, sourceLocalMap]
  rfl

/-- The source residue comparison is induced by the actual source structure-stalk isomorphism. -/
def sourceSchemeResidueIso :
    CommRingCat.of q.asIdeal.ResidueField ≅ (Spec B).residueField (sourcePoint A B p q).1 :=
  (IsLocalRing.ResidueField.mapEquiv
    (sourceSchemeStalkIso A B p q).commRingCatIsoToRingEquiv).toCommRingCatIso

/-- The source residue comparison preserves reduction of every local element. -/
@[simp]
theorem sourceSchemeResidueIso_residue (z : Localization.AtPrime q.asIdeal) :
    (sourceSchemeResidueIso A B p q).hom (IsLocalRing.residue _ z) =
      (Spec B).residue (sourcePoint A B p q).1 ((sourceSchemeStalkIso A B p q).hom z) := rfl

/-- The induced residue square uses the actual target residue action on the actual source point. -/
theorem sourceSchemeResidueIso_base_square :
    (CommRingCat.ofHom (IsLocalRing.ResidueField.map
      (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal))) :
      CommRingCat.of p.asIdeal.ResidueField ⟶ CommRingCat.of q.asIdeal.ResidueField) ≫
        (sourceSchemeResidueIso A B p q).hom =
      (Scheme.Spec.residueFieldIso A p).inv ≫
        pointedSpecResidueMap (A := A) (B := B) (CommRingCat.ofHom (algebraMap A B)) p
          (sourcePoint A B p q).1 (sourcePoint A B p q).2 := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective z
  change (Spec B).residue (sourcePoint A B p q).1
      ((sourceSchemeStalkIso A B p q).hom
        (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) a)) =
    (pointedSpecResidueMap (A := A) (B := B) (CommRingCat.ofHom (algebraMap A B)) p
      (sourcePoint A B p q).1 (sourcePoint A B p q).2).hom
        (IsLocalRing.residue _ ((Spec.stalkIso A p).inv a))
  have hs := ConcreteCategory.congr_hom (sourceSchemeStalkIso_base_square A B p q) a
  have hr := ConcreteCategory.congr_hom
    (pointedSpecStalkMap_residue (A := A) (B := B) (CommRingCat.ofHom (algebraMap A B)) p
      (sourcePoint A B p q).1 (sourcePoint A B p q).2) ((Spec.stalkIso A p).inv a)
  exact (congrArg ((Spec B).residue (sourcePoint A B p q).1) hs).trans hr.symm

end Finite

end Motivic.FiniteFiber
