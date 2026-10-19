/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal

/-!
# Separating the two factors of a product diagonal

Imposing equality of the parameter coordinates on two copies of `Y ×[S] T`
leaves `(Y ×[S] Y) ×[S] T`. The remaining map to `Y ×[S] Y` is flat when
`T → S` is flat, and the full diagonal is its Cartesian pullback of `Δ Y`.
Neither the isomorphism nor the Cartesian square needs smoothness or reducedness.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProductDiagonal

variable {S Y T : Scheme.{u}} (y : Y ⟶ S) (t : T ⟶ S)

/-- The product with the parameter scheme. -/
abbrev product := pullback y t

/-- The structure map of the product, using its first projection. -/
abbrev productBase : product y t ⟶ S := pullback.fst y t ≫ y

/-- The pair of parameterized points over the original base. -/
abbrev ambient := pullback (productBase y t) (productBase y t)

/-- The two actual parameter coordinates of a pair of product points. -/
def parameterPair : ambient y t ⟶ pullback t t :=
  pullback.map (productBase y t) (productBase y t) t t
    (pullback.snd y t) (pullback.snd y t) (𝟙 S)
    (by simpa using (pullback.condition (f := y) (g := t)))
    (by simpa using (pullback.condition (f := y) (g := t)))

/-- The literal inverse image of the parameter diagonal. -/
abbrev parameterDiagonal := pullback (pullback.diagonal t) (parameterPair y t)

/-- The inclusion into the pair of parameterized points. -/
abbrev inclusion : parameterDiagonal y t ⟶ ambient y t :=
  pullback.snd (pullback.diagonal t) (parameterPair y t)

/-- The original pair with one common parameter. -/
abbrev commonParameter := pullback (pullback.fst y y ≫ y) t

/-- Re-express the ambient base maps through the parameter projections. -/
def baseIso : ambient y t ≅
    pullback (pullback.snd y t ≫ t) (pullback.snd y t ≫ t) :=
  pullback.congrHom pullback.condition pullback.condition

/-- The canonical parameter-pair map in the parameter presentation. -/
abbrev canonicalParameterPair :=
  pullback.map (pullback.snd y t ≫ t) (pullback.snd y t ≫ t) t t
    (pullback.snd y t) (pullback.snd y t) (𝟙 S) (by simp) (by simp)

@[reassoc]
theorem baseIso_hom_pair :
    (baseIso y t).hom ≫ canonicalParameterPair y t = parameterPair y t := by
  apply pullback.hom_ext <;>
    simp [baseIso, canonicalParameterPair, parameterPair, pullback.congrHom_hom, pullback.map]

/-- Include the pullback over the common parameter in the original ambient scheme. -/
def parameterPullbackInclusion :
    pullback (pullback.snd y t) (pullback.snd y t) ⟶ ambient y t :=
  pullback.mapDesc (pullback.snd y t) (pullback.snd y t) t ≫ (baseIso y t).inv

/-- Equality of parameter coordinates is exactly the parameter diagonal condition. -/
theorem parameterPullback_isPullback :
    IsPullback
      (pullback.fst (pullback.snd y t) (pullback.snd y t) ≫ pullback.snd y t)
      (parameterPullbackInclusion y t) (pullback.diagonal t) (parameterPair y t) := by
  apply (pullback_map_diagonal_isPullback (pullback.snd y t) (pullback.snd y t) t).of_iso
    (Iso.refl _) (Iso.refl _) (baseIso y t).symm (Iso.refl _)
  · simp
  · simp [parameterPullbackInclusion]
  · simp
  · simpa only [Iso.refl_hom, Category.comp_id, Iso.symm_hom,
      ← baseIso_hom_pair y t] using
      (Iso.inv_hom_id_assoc (baseIso y t) (canonicalParameterPair y t)).symm

/-- The common-parameter pullback is the literal parameter-diagonal inverse image. -/
def parameterPullbackIso :
    pullback (pullback.snd y t) (pullback.snd y t) ≅ parameterDiagonal y t :=
  (parameterPullback_isPullback y t).isoPullback

/-- Pullback associativity collects the two original coordinates together. -/
def commonParameterIso :
    commonParameter y t ≅ pullback (pullback.snd y t) (pullback.snd y t) :=
  pullback.congrHom pullback.condition rfl ≪≫
    pullbackAssoc y y y t ≪≫
    pullback.congrHom rfl (pullback.condition (f := y) (g := t)) ≪≫
    (pullbackLeftPullbackSndIso y t (pullback.snd y t)).symm

/-- Removing the parameter diagonal leaves the original pair times the parameter. -/
def quotientIso : commonParameter y t ≅ parameterDiagonal y t :=
  commonParameterIso y t ≪≫ parameterPullbackIso y t

@[reassoc (attr := simp)]
theorem parameterPullbackIso_hom_inclusion :
    (parameterPullbackIso y t).hom ≫ inclusion y t = parameterPullbackInclusion y t :=
  (parameterPullback_isPullback y t).isoPullback_hom_snd

@[reassoc (attr := simp)]
theorem parameterPullbackIso_hom_parameter :
    (parameterPullbackIso y t).hom ≫
      pullback.fst (pullback.diagonal t) (parameterPair y t) =
        pullback.fst (pullback.snd y t) (pullback.snd y t) ≫ pullback.snd y t :=
  (parameterPullback_isPullback y t).isoPullback_hom_fst

@[reassoc (attr := simp)]
theorem baseIso_inv_fst :
    (baseIso y t).inv ≫ pullback.fst (productBase y t) (productBase y t) =
      pullback.fst (pullback.snd y t ≫ t) (pullback.snd y t ≫ t) := by
  simp [baseIso, pullback.congrHom_inv, pullback.map]

@[reassoc (attr := simp)]
theorem baseIso_inv_snd :
    (baseIso y t).inv ≫ pullback.snd (productBase y t) (productBase y t) =
      pullback.snd (pullback.snd y t ≫ t) (pullback.snd y t ≫ t) := by
  simp [baseIso, pullback.congrHom_inv, pullback.map]

@[reassoc (attr := simp)]
theorem commonParameterIso_hom_first :
    (commonParameterIso y t).hom ≫
      pullback.fst (pullback.snd y t) (pullback.snd y t) ≫ pullback.fst y t =
        pullback.fst _ t ≫ pullback.fst y y := by
  simp [commonParameterIso, pullback.congrHom_hom, pullback.map, Category.assoc]

@[reassoc (attr := simp)]
theorem commonParameterIso_hom_second :
    (commonParameterIso y t).hom ≫
      pullback.snd (pullback.snd y t) (pullback.snd y t) ≫ pullback.fst y t =
        pullback.fst _ t ≫ pullback.snd y y := by
  simp [commonParameterIso, pullback.congrHom_hom, pullback.map, Category.assoc]

@[reassoc (attr := simp)]
theorem commonParameterIso_hom_parameter :
    (commonParameterIso y t).hom ≫
      pullback.fst (pullback.snd y t) (pullback.snd y t) ≫ pullback.snd y t =
        pullback.snd _ t := by
  simp [commonParameterIso, pullback.congrHom_hom, pullback.map, Category.assoc]

@[reassoc (attr := simp)]
theorem quotientIso_hom_parameter :
    (quotientIso y t).hom ≫ pullback.fst (pullback.diagonal t) (parameterPair y t) =
      pullback.snd _ t := by
  simp [quotientIso, Category.assoc]

@[reassoc (attr := simp)]
theorem quotientIso_hom_first :
    (quotientIso y t).hom ≫ inclusion y t ≫
      pullback.fst (productBase y t) (productBase y t) ≫ pullback.fst y t =
        pullback.fst _ t ≫ pullback.fst y y := by
  simp only [quotientIso, Iso.trans_hom, Category.assoc,
    parameterPullbackIso_hom_inclusion_assoc, parameterPullbackInclusion,
    baseIso_inv_fst_assoc, pullback.mapDesc, pullback.map,
    pullback.lift_fst_assoc, Category.comp_id, commonParameterIso_hom_first]

@[reassoc (attr := simp)]
theorem quotientIso_hom_second :
    (quotientIso y t).hom ≫ inclusion y t ≫
      pullback.snd (productBase y t) (productBase y t) ≫ pullback.fst y t =
        pullback.fst _ t ≫ pullback.snd y y := by
  simp only [quotientIso, Iso.trans_hom, Category.assoc,
    parameterPullbackIso_hom_inclusion_assoc, parameterPullbackInclusion,
    baseIso_inv_snd_assoc, pullback.mapDesc, pullback.map,
    pullback.lift_snd_assoc, Category.comp_id, commonParameterIso_hom_second]

/-- The remaining pair of original coordinates after identifying the parameters. -/
def remainingYPair : parameterDiagonal y t ⟶ pullback y y :=
  (quotientIso y t).inv ≫ pullback.fst _ t

instance remainingYPair_flat [Flat t] : Flat (remainingYPair y t) := by
  unfold remainingYPair
  infer_instance

@[reassoc (attr := simp)]
theorem quotientIso_hom_remainingYPair :
    (quotientIso y t).hom ≫ remainingYPair y t = pullback.fst _ t := by
  simp [remainingYPair]

@[reassoc]
theorem remainingYPair_fst :
    remainingYPair y t ≫ pullback.fst y y = inclusion y t ≫
      pullback.fst (productBase y t) (productBase y t) ≫ pullback.fst y t := by
  apply (cancel_epi (quotientIso y t).hom).mp
  simp only [quotientIso_hom_remainingYPair_assoc, quotientIso_hom_first]

@[reassoc]
theorem remainingYPair_snd :
    remainingYPair y t ≫ pullback.snd y y = inclusion y t ≫
      pullback.snd (productBase y t) (productBase y t) ≫ pullback.fst y t := by
  apply (cancel_epi (quotientIso y t).hom).mp
  simp only [quotientIso_hom_remainingYPair_assoc, quotientIso_hom_second]

@[reassoc (attr := simp)]
theorem inclusion_first_parameter :
    inclusion y t ≫ pullback.fst (productBase y t) (productBase y t) ≫ pullback.snd y t =
      pullback.fst (pullback.diagonal t) (parameterPair y t) := by
  have h := congrArg (fun f => f ≫ pullback.fst t t)
    (pullback.condition (f := pullback.diagonal t) (g := parameterPair y t))
  simpa [inclusion, parameterPair, pullback.map] using h.symm

@[reassoc (attr := simp)]
theorem inclusion_second_parameter :
    inclusion y t ≫ pullback.snd (productBase y t) (productBase y t) ≫ pullback.snd y t =
      pullback.fst (pullback.diagonal t) (parameterPair y t) := by
  have h := congrArg (fun f => f ≫ pullback.snd t t)
    (pullback.condition (f := pullback.diagonal t) (g := parameterPair y t))
  simpa [inclusion, parameterPair, pullback.map] using h.symm

/-- The full product diagonal, lifted through its parameter-diagonal factor. -/
def fullDiagonalLift : product y t ⟶ parameterDiagonal y t :=
  pullback.lift (pullback.snd y t) (pullback.diagonal (productBase y t)) (by
    apply pullback.hom_ext <;> simp [parameterPair, pullback.map])

@[reassoc (attr := simp)]
theorem fullDiagonalLift_inclusion :
    fullDiagonalLift y t ≫ inclusion y t = pullback.diagonal (productBase y t) :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem fullDiagonalLift_parameter :
    fullDiagonalLift y t ≫ pullback.fst (pullback.diagonal t) (parameterPair y t) =
      pullback.snd y t := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem fullDiagonalLift_remainingYPair :
    fullDiagonalLift y t ≫ remainingYPair y t = pullback.fst y t ≫ pullback.diagonal y := by
  apply pullback.hom_ext <;>
    simp [Category.assoc, remainingYPair_fst, remainingYPair_snd]

/-- The literal base change of the original diagonal in the common-parameter presentation. -/
def diagonalBaseChange : product y t ⟶ commonParameter y t :=
  pullback.lift (pullback.fst y t ≫ pullback.diagonal y) (pullback.snd y t)
    (by simpa using (pullback.condition (f := y) (g := t)))

/-- The original diagonal times the parameter gives a Cartesian square. -/
theorem diagonalBaseChange_isPullback :
    IsPullback (pullback.fst y t) (diagonalBaseChange y t)
      (pullback.diagonal y) (pullback.fst (pullback.fst y y ≫ y) t) := by
  apply IsPullback.of_bot (v₂₁ := pullback.snd (pullback.fst y y ≫ y) t)
    (v₂₂ := pullback.fst y y ≫ y)
  · simpa [diagonalBaseChange] using (IsPullback.of_hasPullback y t)
  · simp [diagonalBaseChange]
  · exact IsPullback.of_hasPullback _ _

/-- The lifted full diagonal is the same actual base-change map under the quotient isomorphism. -/
theorem diagonalBaseChange_quotientIso :
    diagonalBaseChange y t ≫ (quotientIso y t).hom = fullDiagonalLift y t := by
  apply pullback.hom_ext
  · simp [Category.assoc, diagonalBaseChange]
  · apply pullback.hom_ext <;> apply pullback.hom_ext <;>
      simp [Category.assoc, diagonalBaseChange]

/-- After imposing the parameter diagonal, the full diagonal is the Cartesian base change
of the original diagonal along the remaining pair. -/
theorem fullDiagonalLift_isPullback :
    IsPullback (pullback.fst y t) (fullDiagonalLift y t)
      (pullback.diagonal y) (remainingYPair y t) := by
  apply (diagonalBaseChange_isPullback y t).of_iso
    (Iso.refl _) (Iso.refl _) (quotientIso y t) (Iso.refl _)
  · simp
  · simpa using diagonalBaseChange_quotientIso y t
  · simp
  · simp

end AlgebraicGeometry.ProductDiagonal
