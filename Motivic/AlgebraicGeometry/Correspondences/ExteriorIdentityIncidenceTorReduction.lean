/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ExteriorIdentityParameterCommonList
public import Motivic.Aglib.Algebra.Homology.KoszulTorRegularBlockReduction

/-!
# Actual exterior incidence Tor after the parameter block

Every degree of the actual exterior incidence Tor is the remaining Koszul
homology in the actual coefficient parameter quotient. The remaining list is
the literal image of the chosen original middle-diagonal list. Only the
leading parameter list is eliminated; no coefficient regularity of the
remaining equations, genericity, or finite-length assumption is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence

universe u

namespace Motivic.Intersection

/-- The two actual stalk squares attach the regular-block algebra theorem. -/
private theorem factorTor_length
    {L P₁ P E D : Scheme.{u}}
    (a : L ⟶ P₁) (i : P₁ ⟶ P) (d : D ⟶ P₁) (c : D ⟶ E) (j : E ⟶ P)
    [IsClosedImmersion a] [IsClosedImmersion i] [IsClosedImmersion c]
    [IsClosedImmersion j]
    (hcj : d ≫ i = c ≫ j) (q : L) (z : D) (hq : a q = d z)
    (hp : (a ≫ i) q = j (c z))
    (hcommon : ∃ t : List (ambientStalk i (d z)),
      IsRegular (ambientStalk i (d z)) t ∧
      RingHom.ker (i.stalkMap (d z)).hom = Ideal.ofList t ∧
      IsRegular (E.presheaf.stalk (c z))
        (t.map (coefficientStalkMap i (d z) j (c z)
          (congrArg (fun f : D ⟶ P => f z) hcj)).hom) ∧
      RingHom.ker (c.stalkMap z).hom = Ideal.ofList
        (t.map (coefficientStalkMap i (d z) j (c z)
          (congrArg (fun f : D ⟶ P => f z) hcj)).hom))
    (s : List (P₁.presheaf.stalk (a q)))
    (hs : IsRegular (P₁.presheaf.stalk (a q)) s)
    (hker : RingHom.ker (a.stalkMap q).hom = Ideal.ofList s) (n : ℕ) :
    Module.length (ambientStalk (a ≫ i) q)
      (((Tor (ModuleCat (ambientStalk (a ≫ i) q)) n).obj
        (coefficientStalkModule (a ≫ i) q j (c z) hp)).obj
          (sourceStalkModule (a ≫ i) q)) =
      Module.length (D.presheaf.stalk z)
        ((Koszul.coefficientComplex
          (ModuleCat.of (D.presheaf.stalk z) (D.presheaf.stalk z))
          (s.map (coefficientStalkMap a q d z hq).hom)).homology n) := by
  have hf : Function.Surjective (i.stalkMap (a q)).hom := i.stalkMap_surjective _
  obtain ⟨u, hu⟩ := (List.map_surjective_iff.mpr hf) s
  have hcommon' : ∃ t : List (ambientStalk (a ≫ i) q),
      IsRegular (ambientStalk (a ≫ i) q) t ∧
      RingHom.ker (i.stalkMap (a q)).hom = Ideal.ofList t ∧
      IsRegular (E.presheaf.stalk (c z))
        (t.map (coefficientStalkMap (a ≫ i) q j (c z) hp).hom) ∧
      RingHom.ker (c.stalkMap z).hom = Ideal.ofList
        (t.map (coefficientStalkMap (a ≫ i) q j (c z) hp).hom) := by
    have h (v : P₁) (hv : v = d z) :
        ∃ t : List (ambientStalk i v),
          IsRegular (ambientStalk i v) t ∧
          RingHom.ker (i.stalkMap v).hom = Ideal.ofList t ∧
          IsRegular (E.presheaf.stalk (c z))
            (t.map (coefficientStalkMap i v j (c z)
              ((congrArg i hv).trans (congrArg (fun f : D ⟶ P => f z) hcj))).hom) ∧
          RingHom.ker (c.stalkMap z).hom = Ideal.ofList
            (t.map (coefficientStalkMap i v j (c z)
              ((congrArg i hv).trans (congrArg (fun f : D ⟶ P => f z) hcj))).hom) := by
      subst v
      exact hcommon
    exact h (a q) hq
  obtain ⟨t, ht, hft, hCt, hct⟩ := hcommon'
  have hscalar :
      coefficientStalkMap (a ≫ i) q j (c z) hp ≫ c.stalkMap z =
        i.stalkMap (a q) ≫ coefficientStalkMap a q d z hq := by
    change StalkTransport.pointedMap j (c z) (i (a q)) hp ≫ c.stalkMap z =
      i.stalkMap (a q) ≫ StalkTransport.pointedMap d z (a q) hq
    simpa only [StalkTransport.pointedMap_image] using
      StalkTransport.pointedMap_square c j d i hcj.symm z (c z) (a q)
        (i (a q)) rfl hq hp rfl
  have hlist :
      (u.map (coefficientStalkMap (a ≫ i) q j (c z) hp).hom).map
          (c.stalkMap z).hom =
        s.map (coefficientStalkMap a q d z hq).hom := by
    rw [← hu]
    simp only [List.map_map]
    congr 1
    funext r
    exact ConcreteCategory.congr_hom hscalar r
  have hlength := Koszul.regularLeadingBlockTor_length
    (i.stalkMap (a q)).hom (a.stalkMap q).hom hf (a.stalkMap_surjective q)
    (coefficientStalkMap (a ≫ i) q j (c z) hp).hom (c.stalkMap z).hom
    (coefficientStalkMap_surjective (a ≫ i) q j (c z) hp)
    (c.stalkMap_surjective z) t u ht hft
    (hu ▸ hs) (hu ▸ hker) hct hCt.toIsWeaklyRegular n
  have hlength' := hlength.trans
    (congrArg (fun l : List (D.presheaf.stalk z) =>
      Module.length (D.presheaf.stalk z)
        ((Koszul.coefficientComplex
          (ModuleCat.of (D.presheaf.stalk z) (D.presheaf.stalk z)) l).homology n)) hlist)
  change Module.length (ambientStalk (a ≫ i) q)
    (((Tor (ModuleCat (ambientStalk (a ≫ i) q)) n).obj
      ((ModuleCat.restrictScalars (coefficientStalkMap (a ≫ i) q j (c z) hp).hom).obj
        (ModuleCat.of (E.presheaf.stalk (c z)) (E.presheaf.stalk (c z))))).obj
      ((ModuleCat.restrictScalars ((a ≫ i).stalkMap q).hom).obj
        (ModuleCat.of (L.presheaf.stalk q) (L.presheaf.stalk q)))) = _
  rw [Scheme.Hom.stalkMap_comp]
  exact hlength' 

end Motivic.Intersection

namespace Motivic.FiniteCorrespondenceGenerator

variable {k : Type u} [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]

/-- The old middle point of the actual exterior incidence. -/
abbrev exteriorIncidenceOldMiddlePoint
    (w : (A.exteriorIdentityGenerator T).incidence (B.exteriorIdentityGenerator T)) :=
  pullback.fst Y.hom T.hom
    (correspondenceTripleMiddle (SmoothSite.product X T).hom
      (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom
        ((A.exteriorIdentityGenerator T).incidenceInclusion (B.exteriorIdentityGenerator T) w))

/-- The actual remaining coefficient action after imposing the parameter diagonal. -/
abbrev exteriorIncidenceRemainingCoefficientStalkMap
    (w : (A.exteriorIdentityGenerator T).incidence (B.exteriorIdentityGenerator T)) :=
  Intersection.coefficientStalkMap (exteriorAmbientRemainingInclusion X Y Z T)
    ((A.exteriorIdentityGenerator T).incidenceInclusion (B.exteriorIdentityGenerator T) w)
    (A.exteriorCoefficientQuotientInclusion B T)
    (A.exteriorIncidenceToCoefficientQuotient B T w)
    (Intersection.point_eq _ _ _ _ (A.exteriorRemainingIncidence_isPullback B T) w)

/-- The same chosen original middle equations in the actual coefficient quotient. -/
abbrev exteriorIncidenceRemainingList
    (w : (A.exteriorIdentityGenerator T).incidence (B.exteriorIdentityGenerator T))
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom (A.exteriorIncidenceOldMiddlePoint B T w)))) :=
  (s.map (Diagonal.baseChangeStalkMap (exteriorAmbientRemaining_isPullback X Y Z T)
    ((A.exteriorIdentityGenerator T).incidenceInclusion (B.exteriorIdentityGenerator T) w)).hom).map
      (A.exteriorIncidenceRemainingCoefficientStalkMap B T w).hom

/-- Actual exterior incidence Tor, in every degree, is the remaining homology
of the identical original middle-diagonal list over the actual parameter quotient. -/
theorem exteriorIncidenceTor_length_eq_remaining
    (w : (A.exteriorIdentityGenerator T).incidence (B.exteriorIdentityGenerator T))
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom (A.exteriorIncidenceOldMiddlePoint B T w))))
    (hs : IsRegular ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom (A.exteriorIncidenceOldMiddlePoint B T w))) s)
    (hker : RingHom.ker ((pullback.diagonal Y.hom).stalkMap
      (A.exteriorIncidenceOldMiddlePoint B T w)).hom = Ideal.ofList s) (n : ℕ) :
    Module.length
      ((A.exteriorIdentityGenerator T).incidenceAmbientStalk (B.exteriorIdentityGenerator T) w)
      ((A.exteriorIdentityGenerator T).incidenceTor (B.exteriorIdentityGenerator T) w n) =
    Module.length ((A.exteriorParameterDiagonal T B).presheaf.stalk
        (A.exteriorIncidenceToCoefficientQuotient B T w))
      ((Koszul.coefficientComplex
        (ModuleCat.of ((A.exteriorParameterDiagonal T B).presheaf.stalk
            (A.exteriorIncidenceToCoefficientQuotient B T w))
          ((A.exteriorParameterDiagonal T B).presheaf.stalk
            (A.exteriorIncidenceToCoefficientQuotient B T w)))
        (A.exteriorIncidenceRemainingList B T w s)).homology n) := by
  let q := (A.exteriorIdentityGenerator T).incidenceInclusion (B.exteriorIdentityGenerator T) w
  let z := A.exteriorIncidenceToCoefficientQuotient B T w
  have hq : exteriorAmbientRemainingInclusion X Y Z T q =
      A.exteriorCoefficientQuotientInclusion B T z :=
    Intersection.point_eq _ _ _ _ (A.exteriorRemainingIncidence_isPullback B T) w
  have he : A.exteriorParameterDiagonalInclusion T B z =
      (A.exteriorIdentityGenerator T).incidenceToSupportProduct (B.exteriorIdentityGenerator T) w :=
    congrArg (fun f => f w) (A.exteriorIncidenceToCoefficientQuotient_parameterInclusion B T)
  obtain ⟨hs', hker'⟩ := exteriorAmbientRemaining_mapped_regular_kernel X Y Z T q s hs hker
  have hp :
      (exteriorAmbientRemainingInclusion X Y Z T ≫ exteriorAmbientParameterInclusion X Y Z T) q =
        ((A.exteriorIdentityGenerator T).supportProductInclusion (B.exteriorIdentityGenerator T))
          (A.exteriorParameterDiagonalInclusion T B z) := by
    rw [exteriorAmbientRemainingInclusion_parameterInclusion, he]
    exact Intersection.point_eq _ _ _ _
      ((A.exteriorIdentityGenerator T).incidence_ambient_isPullback
        (B.exteriorIdentityGenerator T)) w
  have hlength := Intersection.factorTor_length
    (exteriorAmbientRemainingInclusion X Y Z T) (exteriorAmbientParameterInclusion X Y Z T)
    (A.exteriorCoefficientQuotientInclusion B T) (A.exteriorParameterDiagonalInclusion T B)
    ((A.exteriorIdentityGenerator T).supportProductInclusion (B.exteriorIdentityGenerator T))
    (A.exteriorCoefficientQuotientInclusion_ambient B T) q z hq hp
    (A.exteriorParameter_exists_common_regular_list B T z)
    (s.map (Diagonal.baseChangeStalkMap (exteriorAmbientRemaining_isPullback X Y Z T) q).hom)
    hs' hker' n
  let htor (b : correspondenceTripleProduct (SmoothSite.product X T).hom
      (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom ⟶
        correspondenceIntersectionAmbient (SmoothSite.product X T).hom
          (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom)
      (e : ((A.exteriorIdentityGenerator T).supportProduct (B.exteriorIdentityGenerator T)))
      (h : b q = ((A.exteriorIdentityGenerator T).supportProductInclusion
        (B.exteriorIdentityGenerator T)) e) :=
    Module.length (Intersection.ambientStalk b q)
      (((Tor (ModuleCat (Intersection.ambientStalk b q)) n).obj
        (Intersection.coefficientStalkModule b q
          ((A.exteriorIdentityGenerator T).supportProductInclusion (B.exteriorIdentityGenerator T))
          e h)).obj (Intersection.sourceStalkModule b q))
  change htor _ _ hp = _ at hlength
  simp only [exteriorAmbientRemainingInclusion_parameterInclusion, he] at hlength
  change htor
    (correspondenceTripleInclusion (SmoothSite.product X T).hom
      (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom)
    ((A.exteriorIdentityGenerator T).incidenceToSupportProduct (B.exteriorIdentityGenerator T) w)
    (Intersection.point_eq _ _ _ _
      ((A.exteriorIdentityGenerator T).incidence_ambient_isPullback
        (B.exteriorIdentityGenerator T)) w) = _
  exact hlength

end Motivic.FiniteCorrespondenceGenerator
