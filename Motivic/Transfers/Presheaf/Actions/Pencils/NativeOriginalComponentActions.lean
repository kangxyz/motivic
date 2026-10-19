/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.Actions.Components.NisnevichImage
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.NativeSectionPairParameterComponents
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.CorrespondenceSites
/-! # Original image actions on the native parameter components

The actual component inclusions use the same relative common sites as the
native norm action. Only separatedness of the original image is used to pass
from these component actions to its whole source, including the empty source.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.RelativeCurvePencil Scheme.RelativeAffineLineEtaleCompactification
universe u
namespace Motivic.PresheafWithTransfers

variable (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [IsNoetherianRing R] {Y : Scheme.{u}} [IsAffine Y]
  (p : Y ⟶ Spec (.of (Polynomial R))) [Etale p] [QuasiCompact p] [IsSeparated p]
  (O : (Spec (.of R)).Opens) [IsAffine O.toScheme]
  (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme]
  (k : Type u) [Field k] {S C : Scheme.{u}} [IsAffine S]
  (t : S ⟶ Spec (.of k)) [Smooth t] (π : C ⟶ S)
  (j : finalOriginalSource R p O V ⟶ C) [Smooth (j ≫ π)]

/-- The canonical original parameter components cover through their literal
native relative-alpha maps, without replacing their smooth-site structures. -/
theorem nativeOriginalComponent_cover :
    Sieve.ofArrows
      (fun i => relativeCommonSite k t π j
        ((nativeSectionPairParameterComponentCover R p O V).f i))
      (fun i => relativeAlpha k t π j
        ((nativeSectionPairParameterComponentCover R p O V).f i)) ∈
      SmoothSite.nisnevichTopology (Spec (.of k)) (lambdaSourceSite k t π j) := by
  let D := nativeSectionPairParameterComponentCover R p O V
  let X (i : D.I₀) := relativeCommonSite k t π j (D.f i)
  let f (i : D.I₀) : X i ⟶ lambdaSourceSite k t π j :=
    relativeAlpha k t π j (D.f i)
  apply (SmoothSite.mem_nisnevichTopology_iff).mpr
  refine ⟨Presieve.ofArrows X f, ?_, Sieve.le_generate _⟩
  change (Presieve.ofArrows X f).map (SmoothSite.forgetScheme _) ∈
    Nisnevich.precoverage (finalOriginalSource R p O V)
  rw [Presieve.map_ofArrows]
  exact Nisnevich.zariskiPrecoverage_le_precoverage _ D.mem₀

/-- Reassemble the actual native component comparisons on the original image.
This does not cancel restriction for an arbitrary presheaf with transfers. -/
theorem nisnevichImage_transfer_eq_of_nativeOriginalComponents
    (P : PresheafWithTransfers.{u + 1} k) (Q : SmoothSite (Spec (.of k)))
    (c d : Cor.mk (lambdaSourceSite k t π j) ⟶ Cor.mk Q)
    (h : ∀ i, (nisnevichImage P).transfer
        ((Cor.graphFunctor k).map (relativeAlpha k t π j
          ((nativeSectionPairParameterComponentCover R p O V).f i)) ≫ c) =
      (nisnevichImage P).transfer
        ((Cor.graphFunctor k).map (relativeAlpha k t π j
          ((nativeSectionPairParameterComponentCover R p O V).f i)) ≫ d)) :
    (nisnevichImage P).transfer c = (nisnevichImage P).transfer d := by
  exact nisnevichImage_transfer_eq_of_cover P _ _
    (nativeOriginalComponent_cover R p O V k t π j) c d h

end Motivic.PresheafWithTransfers
