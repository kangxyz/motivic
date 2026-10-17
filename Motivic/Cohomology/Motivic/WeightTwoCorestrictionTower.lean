/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.WeightTwoCorestrictionMixed
public import Motivic.Cohomology.Motivic.WeightTwoCorestrictionFinite
public import Motivic.Cohomology.Motivic.RawFieldChangeCoherence

/-!
# Towers of actual weight-two corestrictions

The literal scalar projections on the base-times-simplex and torus satisfy the
field-tower equation. Actual finite integral-cycle pushforward then supplies the
tower law, with every original support and residue degree. The original
zero-simplex comparisons, raw homology and derived comparison are retained.
No separability hypothesis or integrality claim for arbitrary smooth sources is
used. These are transfer coherence laws, not a Milnor norm comparison.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped Simplicial

universe w u

namespace Motivic.WeightTwoCorestriction

open PresheafWithTransfers WeightOnePointNorm WeightOneBoundaryNorm
open CommRingCat.PolynomialLaurent

section Geometry

variable {k L E : Type u} [Field k] [Field L] [Field E]
  [Algebra k L] [Algebra L E] [Algebra k E] [IsScalarTower k L E]

/-- The actual simplex scalar projections compose along the given field tower. -/
theorem sourceMap_comp (r : ℕ) :
    sourceMap (k := L) (E := E) r ≫ sourceMap (k := k) (E := L) r =
      sourceMap (k := k) (E := E) r := by
  have h := SmoothSite.fieldBaseChangeComparison_inv_original
    (algebraMap k L) (algebraMap L E)
    (SmoothSite.baseSimplexFieldChangeIso (algebraMap k L) ⦋r⦌)
    (SmoothSite.baseSimplexFieldChangeIso (algebraMap L E) ⦋r⦌)
  rw [← SmoothSite.baseSimplexFieldChangeIso_comp_inv,
    ← IsScalarTower.algebraMap_eq k L E] at h
  simpa only [sourceMap, source, AlgebraicSimplex.cosimplicialSmoothSite,
    Category.assoc] using h.symm

/-- Each Laurent coordinate and the base projection retain their literal tower. -/
theorem torusMap_comp (q : ℕ) :
    torusMap (k := L) (E := E) q ≫ torusMap (k := k) (E := L) q =
      torusMap (k := k) (E := E) q := by
  apply torusPower_scheme_hom_ext
  · simp only [Category.assoc, torusMap_projection, torusMap_projection_assoc]
    rw [← Spec.map_comp]
    congr 2
    exact congrArg CommRingCat.ofHom (IsScalarTower.algebraMap_eq k L E).symm
  · intro i
    simp only [Category.assoc, torusMap_coordinate, torusMap_coordinate_assoc]
    rw [← Spec.map_comp, ← laurentMap_comp]
    congr 3
    exact congrArg CommRingCat.ofHom (IsScalarTower.algebraMap_eq k L E).symm

/-- The actual finite ambient maps compose before any cycle quotient is taken. -/
theorem ambientMap_comp (r q : ℕ) :
    ambientMap (k := L) (E := E) r q ≫ ambientMap (k := k) (E := L) r q =
      ambientMap (k := k) (E := E) r q := by
  apply pullback.hom_ext
  · simp only [Category.assoc, ambientMap_fst, ambientMap_fst_assoc]
    rw [sourceMap_comp]
  · simp only [Category.assoc, ambientMap_snd, ambientMap_snd_assoc]
    rw [torusMap_comp]

end Geometry

section IdentityGeometry

variable (k : Type u) [Field k]

/-- The literal source projection for the identity extension is the identity. -/
theorem sourceMap_id (r : ℕ) : sourceMap (k := k) (E := k) r = 𝟙 _ := by
  change (SmoothSite.baseSimplexFieldChangeIso (RingHom.id k) ⦋r⦌).inv.left ≫ _ = _
  rw [SmoothSite.baseSimplexFieldChangeIso_id_inv]
  exact congrArg (fun f => f.left)
    (SmoothSite.fieldBaseChangeObjectIdIso k (source k r)).inv_hom_id

/-- The literal torus scalar projection for the identity extension is the identity. -/
theorem torusMap_id (q : ℕ) : torusMap (k := k) (E := k) q = 𝟙 _ := by
  have h := congrArg Iso.inv (Iso.ext (SmoothSite.torusPowerBaseChangeIso_id (k := k) q))
  change (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom (RingHom.id k)) q).inv.left ≫ _ = _
  rw [h]
  exact congrArg (fun f => f.left)
    (SmoothSite.fieldBaseChangeObjectIdIso k (target k q)).inv_hom_id

/-- Identity transfer starts with the identity map of the original ambient scheme. -/
theorem ambientMap_id (r q : ℕ) : ambientMap (k := k) (E := k) r q = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [ambientMap_fst, sourceMap_id, Category.id_comp]
    exact Category.comp_id _
  · rw [ambientMap_snd, torusMap_id, Category.id_comp]
    exact Category.comp_id _

end IdentityGeometry

section Tower

variable {k L E : Type u} [Field k] [Field L] [Field E]
  [Algebra k L] [Algebra L E] [Algebra k E] [IsScalarTower k L E]
  [Module.Finite k L] [Module.Finite L E] [Module.Finite k E]

/-- Iterated finite images are the same original admissible integral support. -/
theorem imageGenerator_comp (r q : ℕ)
    (A : FiniteCorrespondenceGenerator (source E r).hom (target E q).hom) :
    imageGenerator (k := k) (E := L) r q (imageGenerator (k := L) (E := E) r q A) =
      imageGenerator (k := k) (E := E) r q A := by
  apply FiniteCorrespondenceGenerator.toIntegralClosedSubscheme_injective
  simp only [imageGenerator_toIntegralClosedSubscheme]
  apply IntegralClosedSubscheme.point_injective
  simp only [IntegralClosedSubscheme.point_finiteImage]
  change (ambientMap (k := L) (E := E) r q ≫ ambientMap (k := k) (E := L) r q)
    A.point = (ambientMap (k := k) (E := E) r q) A.point
  rw [ambientMap_comp]

omit [Module.Finite k L] [Module.Finite k E] in
/-- The coefficient is the product of the original support residue degrees. -/
theorem ambientMap_residueDegree_comp (r q : ℕ)
    (A : FiniteCorrespondenceGenerator (source E r).hom (target E q).hom) :
    (ambientMap (k := k) (E := E) r q).residueDegree A.point =
      (ambientMap (k := k) (E := L) r q).residueDegree
          (imageGenerator (k := L) (E := E) r q A).point *
        (ambientMap (k := L) (E := E) r q).residueDegree A.point := by
  have h := residueDegree_comp (ambientMap (k := L) (E := E) r q)
    (ambientMap (k := k) (E := L) r q) A.point
  rw [ambientMap_comp] at h
  change _ = (ambientMap (k := k) (E := L) r q).residueDegree
    (A.toIntegralClosedSubscheme.finiteImage (ambientMap (k := L) (E := E) r q)).point * _
  rw [IntegralClosedSubscheme.point_finiteImage]
  exact h

/-- The signed correspondence transfer composes with the original image degrees. -/
theorem cyclePushforward_comp (r q : ℕ) :
    (cyclePushforward (k := k) (E := L) r q).comp
      (cyclePushforward (k := L) (E := E) r q) =
        cyclePushforward (k := k) (E := E) r q := by
  ext α
  apply FiniteCorrespondence.toIntegralCycle_injective
  change FiniteCorrespondence.toIntegralCycle
      (cyclePushforward (k := k) (E := L) r q
        (cyclePushforward (k := L) (E := E) r q α)) =
    FiniteCorrespondence.toIntegralCycle (cyclePushforward (k := k) (E := E) r q α)
  rw [toIntegralCycle_cyclePushforward, toIntegralCycle_cyclePushforward,
    toIntegralCycle_cyclePushforward, ← AddMonoidHom.comp_apply,
    ← IntegralCycle.finitePushforward_comp,
    IntegralCycle.finitePushforward_congr (ambientMap_comp r q)]

/-- The actual objectwise identity-axis quotients retain the same tower law. -/
theorem reducedPushforward_comp (r q : ℕ) :
    reducedPushforward (k := L) (E := E) r q ≫
      reducedPushforward (k := k) (E := L) r q =
        reducedPushforward (k := k) (E := E) r q := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  obtain ⟨⟨α⟩, rfl⟩ := toReducedTorus_surjective E q (Cor.mk (source E r)) x
  change reducedPushforward (k := k) (E := L) r q
      (reducedPushforward (k := L) (E := E) r q
        ((toReducedTorus E q).hom.app _ (ULift.up α))) = _
  rw [reducedPushforward_quotient, reducedPushforward_quotient,
    reducedPushforward_quotient]
  exact congrArg (fun β => (toReducedTorus k q).hom.app _ (ULift.up β))
    (DFunLike.congr_fun (cyclePushforward_comp (k := k) (L := L) (E := E) r q) α)

/-- Removing the zero simplex cancels the actual intermediate comparison isomorphism. -/
theorem pointPushforward_comp :
    (pointPushforward (k := k) (E := L)).comp (pointPushforward (k := L) (E := E)) =
      pointPushforward (k := k) (E := E) := by
  ext α
  simp only [AddMonoidHom.comp_apply, pointPushforward_apply, Iso.hom_inv_id_assoc]
  exact congrArg (fun β => (zeroProductIso k).inv ≫ β)
    (DFunLike.congr_fun (cyclePushforward_comp (k := k) (L := L) (E := E) 0 2)
      ((zeroProductIso E).hom ≫ α))

/-- The two original raw maps in degree one satisfy the finite tower law. -/
theorem rawDegreeOnePushforward_comp :
    rawDegreeOnePushforward (k := L) (E := E) ≫
      rawDegreeOnePushforward (k := k) (E := L) =
        rawDegreeOnePushforward (k := k) (E := E) := by
  simp only [rawDegreeOnePushforward, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (reducedPushforward (k := L) (E := E) 1 2),
    reducedPushforward_comp]

/-- The original top raw maps satisfy the finite tower law. -/
theorem rawDegreeTwoPushforward_comp :
    rawDegreeTwoPushforward (k := L) (E := E) ≫
      rawDegreeTwoPushforward (k := k) (E := L) =
        rawDegreeTwoPushforward (k := k) (E := E) := by
  simp only [rawDegreeTwoPushforward, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (reducedPushforward (k := L) (E := E) 0 2),
    reducedPushforward_comp]

/-- Actual finite corestriction composes on the original weight-two raw homology. -/
theorem corestriction_comp :
    (corestriction (k := k) (E := L)).comp (corestriction (k := L) (E := E)) =
      corestriction (k := k) (E := E) := by
  ext x
  obtain ⟨α, rfl⟩ := WeightTwoSymbols.cycleClass_surjective E x
  simp only [AddMonoidHom.comp_apply, corestriction_cycleClass]
  exact congrArg (WeightTwoSymbols.cycleClass k)
    (DFunLike.congr_fun (pointPushforward_comp (k := k) (L := L) (E := E)) α)

section Derived

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of L))) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of E))) AddCommGrpCat.{u + 1})]

/-- The same finite tower law holds on actual derived integral motivic H22. -/
theorem motivicCorestriction_comp :
    (motivicCorestriction (k := k) (E := L)).comp
      (motivicCorestriction (k := L) (E := E)) =
        motivicCorestriction (k := k) (E := E) := by
  ext x
  apply (motivicRawBaseEvaluationComparison k 2 2).injective
  simp only [AddMonoidHom.comp_apply, motivicCorestriction_comparison]
  exact DFunLike.congr_fun (corestriction_comp (k := k) (L := L) (E := E)) _

/-- Actual finite-coefficient corestrictions compose at every natural level. -/
theorem finiteCorestriction_comp (n : ℕ) :
    (finiteCorestriction (k := k) (E := L) n).comp
      (finiteCorestriction (k := L) (E := E) n) =
        finiteCorestriction (k := k) (E := E) n := by
  apply finiteCorestriction_unique
  intro x
  rw [AddMonoidHom.comp_apply, finiteCorestriction_integralReduction,
    finiteCorestriction_integralReduction]
  exact congrArg (motivicBaseIntegralReduction k 2 2 n)
    (DFunLike.congr_fun (motivicCorestriction_comp (k := k) (L := L) (E := E)) x)

end Derived
end Tower

section Identity

variable (k : Type u) [Field k]

/-- Identity scalar extension gives the identity on every signed correspondence group. -/
theorem cyclePushforward_id (r q : ℕ) :
    cyclePushforward (k := k) (E := k) r q = AddMonoidHom.id _ := by
  ext α
  apply FiniteCorrespondence.toIntegralCycle_injective
  rw [toIntegralCycle_cyclePushforward,
    IntegralCycle.finitePushforward_congr (ambientMap_id k r q),
    IntegralCycle.finitePushforward_id]
  rfl

/-- The original zero-simplex comparison also cancels for the identity extension. -/
theorem pointPushforward_id : pointPushforward (k := k) (E := k) = AddMonoidHom.id _ := by
  ext α
  rw [pointPushforward_apply, cyclePushforward_id, AddMonoidHom.id_apply,
    Iso.inv_hom_id_assoc]
  rfl

/-- The identity field extension acts identically on original weight-two raw homology. -/
theorem corestriction_id : corestriction (k := k) (E := k) = AddMonoidHom.id _ := by
  ext x
  obtain ⟨α, rfl⟩ := WeightTwoSymbols.cycleClass_surjective k x
  rw [corestriction_cycleClass, pointPushforward_id]
  rfl

section Derived

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The identity extension acts identically on actual derived integral motivic H22. -/
theorem motivicCorestriction_id :
    motivicCorestriction (k := k) (E := k) = AddMonoidHom.id _ := by
  ext x
  apply (motivicRawBaseEvaluationComparison k 2 2).injective
  rw [motivicCorestriction_comparison, corestriction_id]
  rfl

/-- The identity extension acts identically on actual finite motivic H22 at every level. -/
theorem finiteCorestriction_id (n : ℕ) :
    finiteCorestriction (k := k) (E := k) n = AddMonoidHom.id _ := by
  ext x
  obtain ⟨y, rfl⟩ := FieldTopDegree.integralReduction_surjective k 2 n x
  erw [finiteCorestriction_integralReduction, motivicCorestriction_id]
  rfl

end Derived
end Identity

end Motivic.WeightTwoCorestriction
