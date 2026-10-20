/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.NativeOriginalMiddleInput
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.NativeOriginalBase
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.DistinguishedSquare

/-! # Native middle-input sites and restriction transport

The same native input supplies its coefficient-line comparison, actual
Nisnevich cover and five-map transport. Genuine original restriction squares
induce the source, puncture, parameter and overlap site equations. Current
consumers are the original-history line and restriction assembly.

Intended upstream module:
`Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.NativeMiddleInput`.

The exact hypotheses are the record fields and declaration signatures below.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open Scheme Scheme.Hom RelativeProjectiveLine
open Scheme.RelativeAffineLineEtaleCompactification Scheme.RelativeCurvePencil
universe u

namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification.NativeOriginalMiddleInput
attribute [local instance] commRing smoothT
variable {k : Type u} [Field k] (N : NativeOriginalMiddleInput k)

/-- The coefficient line of the same native input, with its original field map. -/
def nativeLineSite : Scheme.SmoothSite (Spec (.of k)) := by
  let : SmoothOfRelativeDimension 1 (boundaryLineProjection N.R) :=
    Scheme.AffineLineEtaleCompactification.polynomialProjection_smooth_one N.R
  let : Smooth (boundaryLineProjection N.R) := SmoothOfRelativeDimension.smooth 1 _
  exact Scheme.SmoothSite.mk (boundaryLineProjection N.R ≫ N.t)

/-- The target-lambda line and coefficient line have the identical underlying scheme. -/
def nativeLineSiteIso : N.toInput.siteX ≅ N.nativeLineSite := by
  refine MorphismProperty.Over.isoMk (Iso.refl N.toInput.siteX.left) ?_
  change 𝟙 _ ≫ (boundaryLineProjection N.R ≫ N.t) =
    (chart N.R 0 ≫ ProjectiveSpace.toSpec N.R (ULift.{u} (Fin 2))) ≫ N.t
  exact (Category.id_comp (boundaryLineProjection N.R ≫ N.t)).trans
    (congrArg (fun f => f ≫ N.t) (chart_toSpec N.R 0).symm)

end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification.NativeOriginalMiddleInput

namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification.NativeOriginalMiddleInput
variable {k : Type u} [Field k] (N : NativeOriginalMiddleInput k)

/-- The two owned line sites have the same underlying scheme. -/
theorem nativeLineSite_left : N.toInput.siteX.left = N.nativeLineSite.left := rfl

end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification.NativeOriginalMiddleInput

namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification.NativeOriginalMiddleInput
variable {k : Type u} [Field k] (N : NativeOriginalMiddleInput k)

/-- The line comparison followed by a proved site equality has the canonical transport map. -/
theorem nativeLineSiteIso_transport_hom_left
    {L : Scheme.SmoothSite (Spec (.of k))} (h : N.nativeLineSite = L) :
    (N.nativeLineSiteIso ≪≫ eqToIso h).hom.left =
      eqToHom (N.nativeLineSite_left.trans (congrArg (fun S => S.left) h)) := by
  cases h
  rfl

end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification.NativeOriginalMiddleInput

namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification.NativeOriginalMiddleInput
attribute [local instance] commRing openA closedZChart
variable {k : Type u} [Field k] (N : NativeOriginalMiddleInput k) [Etale N.p]

/-- The original marked complement covers the native sites, then any chosen target isomorphism. -/
theorem nativeCover_mem_nisnevichTopology
    {X : SmoothSite (Spec (.of k))} (e : N.toInput.siteX ≅ X) :
    Sieve.ofTwoArrows (N.aSite ≫ e.hom) (N.toInput.pSite ≫ e.hom) ∈
      SmoothSite.nisnevichTopology (Spec (.of k)) X := by
  let : IsClosedImmersion N.z := IsClosedImmersion.of_comp N.z (chart N.R 0)
  have hcomp : Set.range N.z = (Set.range N.a)ᶜ := by
    apply le_antisymm
    · intro x hz ha
      exact Set.disjoint_left.mp N.ha ha hz
    · exact N.hpuncture
  let eS : Spec (.of (Polynomial N.R)) ≅ X.left :=
    (SmoothSite.forgetScheme (Spec (.of k))).mapIso e
  let : Etale (N.aSite ≫ e.hom).left := by
    change Etale (N.a ≫ eS.hom)
    infer_instance
  let : Etale (N.toInput.pSite ≫ e.hom).left := by
    change Etale (N.p ≫ eS.hom)
    infer_instance
  apply SmoothSite.ofTwoArrows_mem_nisnevichTopology_of_field_lifting
  intro K _ x
  obtain ⟨b, hb⟩ | ⟨c, hc⟩ :=
    Scheme.exists_field_lift_open_or_closed N.a N.z hcomp (x ≫ eS.inv)
  · left
    refine ⟨b, ?_⟩
    change b ≫ (N.a ≫ eS.hom) = x
    rw [← Category.assoc, hb, Category.assoc, eS.inv_hom_id, Category.comp_id]
  · right
    refine ⟨c ≫ N.s, ?_⟩
    change (c ≫ N.s) ≫ (N.p ≫ eS.hom) = x
    rw [← Category.assoc, Category.assoc c N.s N.p, N.hs,
      hc, Category.assoc, eS.inv_hom_id, Category.comp_id]
end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification.NativeOriginalMiddleInput

namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification.NativeOriginalMiddleInput
variable {k : Type u} [Field k]

/-- The five existing maps transporting one original refined diagram to one native input. -/
structure SiteLiftTransport (N : NativeOriginalMiddleInput k)
    (A Y A' Y' X' : SmoothSite (Spec (.of k))) where
  sourceComparison : Y' ⟶ N.toInput.siteY
  punctureComparison : A' ⟶ N.toInput.siteA
  cylinderComparison : X' ⟶ N.toInput.siteX
  sourceRestriction : N.toInput.siteY ⟶ Y
  parameterRestriction : N.toInput.siteQ ⟶ A

namespace SiteLiftTransport
variable {N : NativeOriginalMiddleInput k}
  {A Y A' Y' X' Tc : SmoothSite (Spec (.of k))}

/-- The original source, puncture, restriction and overlap diagrams for the stored maps. -/
structure Compatible (D : SiteLiftTransport N A Y A' Y' X')
    (a : A ⟶ Tc) (p : Y ⟶ Tc) (i' : A' ⟶ X') (v' : Y' ⟶ X')
    (rA : A' ⟶ A) (rY : Y' ⟶ Y) : Prop where
  source : D.sourceComparison ≫ N.toInput.pSite = v' ≫ D.cylinderComparison
  puncture : D.punctureComparison ≫ N.aSite = i' ≫ D.cylinderComparison
  sourceRestriction : D.sourceComparison ≫ D.sourceRestriction = rY
  parameterRestriction : D.punctureComparison ≫ N.delta ≫ D.parameterRestriction = rA
  overlap : (N.toInput.wSite ≫ D.parameterRestriction) ≫ a =
    (N.toInput.uSite ≫ D.sourceRestriction) ≫ p

end SiteLiftTransport
end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification.NativeOriginalMiddleInput

namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification.NativeOriginalMiddleInput
attribute [local instance] commRing
variable {k : Type u} [Field k] (N : NativeOriginalMiddleInput k)

/-- A genuine source restriction square equips its original map with the native site structure. -/
def sourceRestrictionOfSquare {Y Tc : SmoothSite (Spec (.of k))}
    (p : Y ⟶ Tc) (m : N.toInput.siteX ⟶ Tc) (r : N.Y ⟶ Y.left)
    (hs : r ≫ p.left = N.p ≫ m.left) : N.toInput.siteY ⟶ Y :=
  let tNative : N.Y ⟶ Spec (.of k) := N.toInput.siteY.hom
  let tLine : Spec (.of (Polynomial N.R)) ⟶ Spec (.of k) := N.toInput.siteX.hom
  have hNative : N.p ≫ tLine = tNative := MorphismProperty.Over.w N.toInput.pSite
  have hLine : m.left ≫ Tc.hom = tLine := MorphismProperty.Over.w m
  have hField : r ≫ Y.hom = tNative :=
    (congrArg (fun f => r ≫ f) (MorphismProperty.Over.w p).symm).trans
      ((Category.assoc r p.left Tc.hom).symm.trans
        ((congrArg (fun f => f ≫ Tc.hom) hs).trans
          ((Category.assoc N.p m.left Tc.hom).trans
            ((congrArg (fun f => N.p ≫ f) hLine).trans hNative))))
  SmoothSite.homMk r hField

/-- The site source square is the already proved underlying original square. -/
theorem sourceRestrictionOfSquare_comp {Y Tc : SmoothSite (Spec (.of k))}
    (p : Y ⟶ Tc) (m : N.toInput.siteX ⟶ Tc) (r : N.Y ⟶ Y.left)
    (hs : r ≫ p.left = N.p ≫ m.left) :
    N.sourceRestrictionOfSquare p m r hs ≫ p = N.toInput.pSite ≫ m := by
  apply MorphismProperty.Over.Hom.ext
  exact hs

/-- A genuine puncture restriction square equips its original map with the native site structure. -/
def punctureRestrictionOfSquare {A Tc : SmoothSite (Spec (.of k))}
    (a : A ⟶ Tc) (m : N.toInput.siteX ⟶ Tc) (r : N.A ⟶ A.left)
    (hs : r ≫ a.left = N.a ≫ m.left) : N.toInput.siteA ⟶ A :=
  let tNative : N.A ⟶ Spec (.of k) := N.toInput.siteA.hom
  let tLine : Spec (.of (Polynomial N.R)) ⟶ Spec (.of k) := N.toInput.siteX.hom
  have hNative : N.a ≫ tLine = tNative := MorphismProperty.Over.w N.aSite
  have hLine : m.left ≫ Tc.hom = tLine := MorphismProperty.Over.w m
  have hField : r ≫ A.hom = tNative :=
    (congrArg (fun f => r ≫ f) (MorphismProperty.Over.w a).symm).trans
      ((Category.assoc r a.left Tc.hom).symm.trans
        ((congrArg (fun f => f ≫ Tc.hom) hs).trans
          ((Category.assoc N.a m.left Tc.hom).trans
            ((congrArg (fun f => N.a ≫ f) hLine).trans hNative))))
  SmoothSite.homMk r hField

/-- The site puncture square is the already proved underlying original square. -/
theorem punctureRestrictionOfSquare_comp {A Tc : SmoothSite (Spec (.of k))}
    (a : A ⟶ Tc) (m : N.toInput.siteX ⟶ Tc) (r : N.A ⟶ A.left)
    (hs : r ≫ a.left = N.a ≫ m.left) :
    N.punctureRestrictionOfSquare a m r hs ≫ a = N.aSite ≫ m := by
  apply MorphismProperty.Over.Hom.ext
  exact hs

/-- The native small-parameter comparison has the unchanged identity underlying map. -/
theorem delta_left : N.delta.left = 𝟙 N.A := rfl

/-- Use the same puncture restriction on the native parameter site. -/
def parameterRestriction {A : SmoothSite (Spec (.of k))} (r : N.toInput.siteA ⟶ A) :
    N.toInput.siteQ ⟶ A :=
  SmoothSite.homMk r.left (by
    have hfield : N.toInput.siteQ.hom = N.toInput.siteA.hom := by
      have h := MorphismProperty.Over.w N.delta
      change (𝟙 _) ≫ N.toInput.siteQ.hom = N.toInput.siteA.hom at h
      simpa only [Category.id_comp] using h
    exact (MorphismProperty.Over.w r).trans hfield.symm)

/-- The parameter restriction retains exactly the original underlying map. -/
theorem parameterRestriction_left {A : SmoothSite (Spec (.of k))}
    (r : N.toInput.siteA ⟶ A) : (N.parameterRestriction r).left = r.left := rfl

/-- The native small-parameter comparison cancels without any reconstructed puncture site. -/
theorem delta_parameterRestriction {A : SmoothSite (Spec (.of k))}
    (r : N.toInput.siteA ⟶ A) : N.delta ≫ N.parameterRestriction r = r := by
  apply MorphismProperty.Over.Hom.ext
  change (𝟙 _) ≫ r.left = r.left
  exact Category.id_comp _

/-- The stored overlap square and the two original restriction squares imply compatibility. -/
theorem restriction_overlap {A Y Tc : SmoothSite (Spec (.of k))}
    (a : A ⟶ Tc) (p : Y ⟶ Tc) (m : N.toInput.siteX ⟶ Tc)
    (rA : N.toInput.siteA ⟶ A) (rY : N.toInput.siteY ⟶ Y)
    (hA : rA ≫ a = N.aSite ≫ m) (hY : rY ≫ p = N.toInput.pSite ≫ m) :
    (N.toInput.wSite ≫ N.parameterRestriction rA) ≫ a =
      (N.toInput.uSite ≫ rY) ≫ p := by
  let mS : Spec (.of (Polynomial N.R)) ⟶ Tc.left := m.left
  let rAS : N.A ⟶ A.left := rA.left
  let rYS : N.Y ⟶ Y.left := rY.left
  have ha : rAS ≫ a.left = N.a ≫ mS := congrArg (fun f => f.left) hA
  have hy : rYS ≫ p.left = N.p ≫ mS := congrArg (fun f => f.left) hY
  apply MorphismProperty.Over.Hom.ext
  change (N.vA ≫ rAS) ≫ a.left = (N.vB ≫ rYS) ≫ p.left
  rw [Category.assoc, ha, ← Category.assoc, N.hsmall.symm,
    Category.assoc, ← hy, ← Category.assoc]

/-- The existing five-map adapter on native-owned source and puncture sites. -/
def nativeTransport {A Y C : SmoothSite (Spec (.of k))}
    (e : N.toInput.siteX ≅ C) (rA : N.toInput.siteA ⟶ A) (rY : N.toInput.siteY ⟶ Y) :
    SiteLiftTransport N A Y N.toInput.siteA N.toInput.siteY C where
  sourceComparison := 𝟙 _
  punctureComparison := 𝟙 _
  cylinderComparison := e.inv
  sourceRestriction := rY
  parameterRestriction := N.parameterRestriction rA

/-- The native adapter's five equations follow from the two genuine original squares. -/
theorem nativeTransport_compatible {A Y C Tc : SmoothSite (Spec (.of k))}
    (a : A ⟶ Tc) (p : Y ⟶ Tc) (m : N.toInput.siteX ⟶ Tc)
    (e : N.toInput.siteX ≅ C) (rA : N.toInput.siteA ⟶ A) (rY : N.toInput.siteY ⟶ Y)
    (hA : rA ≫ a = N.aSite ≫ m) (hY : rY ≫ p = N.toInput.pSite ≫ m) :
    (N.nativeTransport e rA rY).Compatible a p (N.aSite ≫ e.hom)
      (N.toInput.pSite ≫ e.hom) rA rY := by
  refine {
    source := ?_
    puncture := ?_
    sourceRestriction := ?_
    parameterRestriction := ?_
    overlap := ?_ }
  · change (𝟙 _) ≫ N.toInput.pSite = (N.toInput.pSite ≫ e.hom) ≫ e.inv
    simp only [Category.id_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · change (𝟙 _) ≫ N.aSite = (N.aSite ≫ e.hom) ≫ e.inv
    simp only [Category.id_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · exact Category.id_comp rY
  · change (𝟙 _) ≫ N.delta ≫ N.parameterRestriction rA = rA
    rw [Category.id_comp, N.delta_parameterRestriction]
  · exact N.restriction_overlap a p m rA rY hA hY

end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification.NativeOriginalMiddleInput
