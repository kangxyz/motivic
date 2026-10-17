/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ExteriorPairStalks
public import Motivic.AlgebraicGeometry.Cycles.GenericStalkSupport

/-!
# Actual closed fibers and exterior integral-support stalks

An integral closed support is first exterior-base-changed as a scheme, retaining
all nilpotents created by that base change. At an actual exterior generic point,
flatness makes its projection a generic point of the original integral support.
Only this original integral generic stalk is a field. The Cartesian stalk-kernel
formula then identifies the exterior support stalk with the quotient of the
whole exterior ambient stalk by the original base maximal ideal.

The equivalence is induced by the actual closed-immersion stalk map and preserves
its scalar action. No whole ambient scheme is reduced, no exterior multiplicity
is replaced by one, and no finite tensor-algebra branch indexing is asserted.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.Intersection

variable {W D Q P : Scheme.{u}} {a : W ⟶ D} {b : W ⟶ Q}
  {i : D ⟶ P} {q : Q ⟶ P} [IsClosedImmersion i]

/-- If the original support stalk is a field, its Cartesian exterior stalk
kernel is the literal original-base maximal ideal extended by the projection. -/
theorem fieldStalkBaseChange_kernel (sq : IsPullback a b i q) (w : W)
    (hf : IsField (D.presheaf.stalk (a w))) :
    RingHom.ker (b.stalkMap w).hom =
      (IsLocalRing.maximalIdeal (P.presheaf.stalk (q (b w)))).map
        (q.stalkMap (b w)).hom := by
  let := hf.toField
  rw [Diagonal.baseChange_stalk_kernel sq w,
    IsLocalRing.ker_eq_maximalIdeal (i.stalkMap (a w)).hom (i.stalkMap_surjective (a w))]
  change (IsLocalRing.maximalIdeal (P.presheaf.stalk (i (a w)))).map
    ((q.stalkMap (b w)).hom.comp (Diagonal.baseChangeStalkIso sq w).hom.hom) = _
  rw [← Ideal.map_map,
    IsLocalRing.map_maximalIdeal_of_surjective (Diagonal.baseChangeStalkIso sq w).hom.hom
      (Diagonal.baseChangeStalkIso sq w).commRingCatIsoToRingEquiv.surjective]

/-- The whole exterior local ring is quotiented only by the proved maximal-ideal
extension. The result is the actual support-product stalk, with all nilpotents. -/
def fieldStalkBaseChangeClosedFiberEquiv (sq : IsPullback a b i q) (w : W)
    (hf : IsField (D.presheaf.stalk (a w))) :
    Koszul.coefficientClosedFiber (q.stalkMap (b w)).hom ≃+* W.presheaf.stalk w := by
  have : IsClosedImmersion b := MorphismProperty.of_isPullback sq inferInstance
  exact (Ideal.quotEquivOfEq (fieldStalkBaseChange_kernel sq w hf).symm).trans
    (stalkQuotientKerEquiv b w)

/-- The equivalence is induced by the original immersion map on every numerator. -/
@[simp] theorem fieldStalkBaseChangeClosedFiberEquiv_mk
    (sq : IsPullback a b i q) (w : W) (hf : IsField (D.presheaf.stalk (a w)))
    (r : Q.presheaf.stalk (b w)) :
    fieldStalkBaseChangeClosedFiberEquiv sq w hf
        (Ideal.Quotient.mk _ r) = (b.stalkMap w) r := by
  simp only [fieldStalkBaseChangeClosedFiberEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, stalkQuotientKerEquiv,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

/-- The quotient equivalence commutes with the literal whole-exterior stalk action. -/
theorem fieldStalkBaseChangeClosedFiberEquiv_scalarSquare
    (sq : IsPullback a b i q) (w : W) (hf : IsField (D.presheaf.stalk (a w))) :
    (fieldStalkBaseChangeClosedFiberEquiv sq w hf).toRingHom.comp
        (Ideal.Quotient.mk _) = (b.stalkMap w).hom := by
  ext r
  exact fieldStalkBaseChangeClosedFiberEquiv_mk sq w hf r

/-- The actual quotient-ring equivalence also identifies the original scalar modules. -/
def fieldStalkBaseChangeClosedFiberModuleIso
    (sq : IsPullback a b i q) (w : W) (hf : IsField (D.presheaf.stalk (a w))) :
    ModuleCat.of (Q.presheaf.stalk (b w))
        (Koszul.coefficientClosedFiber (q.stalkMap (b w)).hom) ≅
      (ModuleCat.restrictScalars (b.stalkMap w).hom).obj
        (ModuleCat.of (W.presheaf.stalk w) (W.presheaf.stalk w)) := by
  let e := fieldStalkBaseChangeClosedFiberEquiv sq w hf
  let N := (ModuleCat.restrictScalars (b.stalkMap w).hom).obj
    (ModuleCat.of (W.presheaf.stalk w) (W.presheaf.stalk w))
  let l : ModuleCat.of (Q.presheaf.stalk (b w))
      (Koszul.coefficientClosedFiber (q.stalkMap (b w)).hom) ≃ₗ[Q.presheaf.stalk (b w)] N :=
    { e.toAddEquiv with
      map_smul' := by
        intro r x
        obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
        change e (Ideal.Quotient.mk _ (r * s)) =
          (b.stalkMap w).hom r * e (Ideal.Quotient.mk _ s)
        simp only [e, fieldStalkBaseChangeClosedFiberEquiv_mk, map_mul] }
  exact l.toModuleIso

/-- The genuine closed-fiber length is the regular length of the actual exterior
support stalk. Surjective original stalk scalars, not reducedness, give the equality. -/
theorem fieldStalkBaseChangeClosedFiber_length
    (sq : IsPullback a b i q) (w : W) (hf : IsField (D.presheaf.stalk (a w))) :
    Module.length (Q.presheaf.stalk (b w))
        (Koszul.coefficientClosedFiber (q.stalkMap (b w)).hom) =
      Module.length (W.presheaf.stalk w) (W.presheaf.stalk w) := by
  have : IsClosedImmersion b := MorphismProperty.of_isPullback sq inferInstance
  exact (fieldStalkBaseChangeClosedFiberModuleIso sq w hf).toLinearEquiv.length_eq.trans
    (TorComparison.length_restrictScalars_of_surjective (b.stalkMap w).hom
      (b.stalkMap_surjective w) _)

end Motivic.Intersection

namespace Motivic.IntegralClosedSubscheme

variable {P S T : Scheme.{u}} (V : IntegralClosedSubscheme P) (p : P ⟶ S) (t : T ⟶ S)

/-- The original integral-support generic stalk is the maximal-ideal quotient of
the unreduced ambient stalk under its actual closed-immersion map. -/
theorem genericStalk_kernel :
    RingHom.ker (V.val.subschemeι.stalkMap (genericPoint V.val.subscheme)).hom =
      IsLocalRing.maximalIdeal (P.presheaf.stalk V.point) := by
  let := (isField_stalk_of_closure_mem_irreducibleComponents V.val.subscheme
    (genericPoint V.val.subscheme) (by simp [irreducibleComponents_eq_singleton])).toField
  exact IsLocalRing.ker_eq_maximalIdeal
    (V.val.subschemeι.stalkMap (genericPoint V.val.subscheme)).hom
    (V.val.subschemeι.stalkMap_surjective (genericPoint V.val.subscheme))

/-- The ambient point's actual residue field identifies with the integral-support
generic stalk through the original closed-immersion quotient, not an abstract field choice. -/
def genericStalkResidueEquiv :
    P.residueField V.point ≃+* V.val.subscheme.presheaf.stalk (genericPoint V.val.subscheme) :=
  (Ideal.quotEquivOfEq V.genericStalk_kernel.symm).trans
    (stalkQuotientKerEquiv V.val.subschemeι (genericPoint V.val.subscheme))

/-- The generic-stalk residue comparison preserves the literal original ambient stalk map. -/
theorem genericStalkResidueEquiv_scalarSquare :
    V.genericStalkResidueEquiv.toRingHom.comp (P.residue V.point).hom =
      (V.val.subschemeι.stalkMap (genericPoint V.val.subscheme)).hom := by
  ext r
  rfl

/-- The actual exterior scheme of one integral cycle support, before any reduction. -/
abbrev exteriorProduct : Scheme.{u} := pullback (V.val.subschemeι ≫ p) t

/-- The literal closed support inclusion into the whole exterior ambient scheme. -/
def exteriorInclusion : V.exteriorProduct p t ⟶ pullback p t :=
  pullback.map _ _ _ _ V.val.subschemeι (𝟙 T) (𝟙 S) (by simp) (by simp)

/-- The exterior support inclusion retains the original support immersion. -/
@[reassoc (attr := simp)] theorem exteriorInclusion_fst :
    V.exteriorInclusion p t ≫ pullback.fst p t =
      pullback.fst (V.val.subschemeι ≫ p) t ≫ V.val.subschemeι :=
  pullback.lift_fst _ _ _

/-- The additional exterior factor is unchanged by the support inclusion. -/
@[reassoc (attr := simp)] theorem exteriorInclusion_snd :
    V.exteriorInclusion p t ≫ pullback.snd p t =
      pullback.snd (V.val.subschemeι ≫ p) t := by
  simp only [exteriorInclusion, pullback.map, pullback.lift_snd, Category.comp_id]

/-- The actual exterior support inclusion is the Cartesian base change of the
original integral-support closed immersion. -/
theorem exteriorInclusion_isPullback :
    IsPullback (pullback.fst (V.val.subschemeι ≫ p) t)
      (V.exteriorInclusion p t) V.val.subschemeι (pullback.fst p t) := by
  refine IsPullback.of_bot (t := IsPullback.of_hasPullback p t) ?_
    (V.exteriorInclusion_fst p t).symm
  simpa only [V.exteriorInclusion_snd p t] using
    (IsPullback.of_hasPullback (V.val.subschemeι ≫ p) t)

/-- The exterior inclusion is a genuine closed immersion with its full pulled-back support ideal. -/
instance exteriorInclusion_isClosedImmersion : IsClosedImmersion (V.exteriorInclusion p t) :=
  MorphismProperty.of_isPullback (V.exteriorInclusion_isPullback p t) inferInstance

variable [Flat t]

/-- Genuine exterior generic points project to the generic point of this one
integral support, using flatness of the actual exterior projection. -/
theorem exteriorGeneric_projection (w : genericPoints (V.exteriorProduct p t)) :
    pullback.fst (V.val.subschemeι ≫ p) t w.1 = genericPoint V.val.subscheme := by
  have hg := mem_genericPoints_of_generalizing
    (pullback.fst (V.val.subschemeι ≫ p) t) (Flat.generalizingMap _) w.1 w.2
  simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hg

/-- The projected point in the original whole ambient scheme is this support's point. -/
theorem exteriorGeneric_ambientProjection (w : genericPoints (V.exteriorProduct p t)) :
    pullback.fst p t (V.exteriorInclusion p t w.1) = V.point := by
  change (V.exteriorInclusion p t ≫ pullback.fst p t) w.1 = _
  rw [V.exteriorInclusion_fst p t, Scheme.Hom.comp_apply,
    V.exteriorGeneric_projection p t w]
  rfl

/-- Only the original integral-support generic stalk is made a field. The exterior
stalk, and both whole ambient stalks, are left unreduced. -/
theorem exteriorGeneric_originalStalk_isField
    (w : genericPoints (V.exteriorProduct p t)) :
    IsField (V.val.subscheme.presheaf.stalk
      (pullback.fst (V.val.subschemeι ≫ p) t w.1)) := by
  apply isField_stalk_of_closure_mem_irreducibleComponents
  exact mem_genericPoints_of_generalizing
    (pullback.fst (V.val.subschemeι ≫ p) t) (Flat.generalizingMap _) w.1 w.2

/-- The literal original-base maximal ideal generates the actual exterior immersion
kernel. The base point is the projection in the original whole ambient scheme. -/
theorem exteriorGeneric_kernel (w : genericPoints (V.exteriorProduct p t)) :
    RingHom.ker ((V.exteriorInclusion p t).stalkMap w.1).hom =
      (IsLocalRing.maximalIdeal (P.presheaf.stalk
        (pullback.fst p t (V.exteriorInclusion p t w.1)))).map
          ((pullback.fst p t).stalkMap (V.exteriorInclusion p t w.1)).hom :=
  Intersection.fieldStalkBaseChange_kernel
    (V.exteriorInclusion_isPullback p t) w.1 (V.exteriorGeneric_originalStalk_isField p t w)

/-- The actual integral-exterior stalk is the literal closed fiber of the original
whole exterior projection, via its own support immersion. -/
def exteriorGenericClosedFiberEquiv (w : genericPoints (V.exteriorProduct p t)) :
    Koszul.coefficientClosedFiber
        ((pullback.fst p t).stalkMap (V.exteriorInclusion p t w.1)).hom ≃+*
      (V.exteriorProduct p t).presheaf.stalk w.1 :=
  Intersection.fieldStalkBaseChangeClosedFiberEquiv
    (V.exteriorInclusion_isPullback p t) w.1 (V.exteriorGeneric_originalStalk_isField p t w)

/-- The support-stalk identification is induced by its actual original closed immersion. -/
@[simp] theorem exteriorGenericClosedFiberEquiv_mk
    (w : genericPoints (V.exteriorProduct p t))
    (r : (pullback p t : Scheme.{u}).presheaf.stalk (V.exteriorInclusion p t w.1)) :
    V.exteriorGenericClosedFiberEquiv p t w (Ideal.Quotient.mk _ r) =
      (V.exteriorInclusion p t).stalkMap w.1 r :=
  Intersection.fieldStalkBaseChangeClosedFiberEquiv_mk
    (V.exteriorInclusion_isPullback p t) w.1 (V.exteriorGeneric_originalStalk_isField p t w) r

/-- The generic exterior quotient comparison preserves its literal ambient stalk action. -/
theorem exteriorGenericClosedFiberEquiv_scalarSquare
    (w : genericPoints (V.exteriorProduct p t)) :
    (V.exteriorGenericClosedFiberEquiv p t w).toRingHom.comp
        (Ideal.Quotient.mk _) = ((V.exteriorInclusion p t).stalkMap w.1).hom :=
  Intersection.fieldStalkBaseChangeClosedFiberEquiv_scalarSquare
    (V.exteriorInclusion_isPullback p t) w.1 (V.exteriorGeneric_originalStalk_isField p t w)

/-- The exterior closed-fiber quotient and actual support stalk have the same original
ambient scalar module, with the scalar action supplied by the actual immersion. -/
def exteriorGenericClosedFiberModuleIso
    (w : genericPoints (V.exteriorProduct p t)) :
    ModuleCat.of ((pullback p t : Scheme.{u}).presheaf.stalk (V.exteriorInclusion p t w.1))
        (Koszul.coefficientClosedFiber
          ((pullback.fst p t).stalkMap (V.exteriorInclusion p t w.1)).hom) ≅
      (ModuleCat.restrictScalars ((V.exteriorInclusion p t).stalkMap w.1).hom).obj
        (ModuleCat.of ((V.exteriorProduct p t).presheaf.stalk w.1)
          ((V.exteriorProduct p t).presheaf.stalk w.1)) :=
  Intersection.fieldStalkBaseChangeClosedFiberModuleIso
    (V.exteriorInclusion_isPullback p t) w.1 (V.exteriorGeneric_originalStalk_isField p t w)

/-- The actual closed-fiber multiplicity equals the whole nonreduced exterior-support
stalk multiplicity. It is not the multiplicity of the whole scheme image. -/
theorem exteriorGenericClosedFiber_length
    (w : genericPoints (V.exteriorProduct p t)) :
    Module.length ((pullback p t : Scheme.{u}).presheaf.stalk (V.exteriorInclusion p t w.1))
        (Koszul.coefficientClosedFiber
          ((pullback.fst p t).stalkMap (V.exteriorInclusion p t w.1)).hom) =
      Module.length ((V.exteriorProduct p t).presheaf.stalk w.1)
        ((V.exteriorProduct p t).presheaf.stalk w.1) :=
  Intersection.fieldStalkBaseChangeClosedFiber_length
    (V.exteriorInclusion_isPullback p t) w.1 (V.exteriorGeneric_originalStalk_isField p t w)

end Motivic.IntegralClosedSubscheme
