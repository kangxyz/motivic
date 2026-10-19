/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.Actions.Principal.Family


/-!
# Principal action on the original open section

The canonical open immersion and its top-section isomorphism feed the actual
principal homotopy. The concluding correspondence uses the original open and
section, with their original function-field germ and signed order coefficients.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v u

namespace Motivic.PrincipalOrderCorrespondence

attribute [local instance] Scheme.nonempty_image_open
  _root_.AlgebraicGeometry.PrincipalFamilyUnitOpen.nonemptyTop

/-- Canonical open presentation retains the exact original function-field germ
and hence every signed order coefficient. -/
theorem principalOrderCycle_topIso {C : Scheme.{u}} [IsIntegral C] [IsNoetherian C]
    (W : C.Opens) [Nonempty W] (r : Γ(C, W)) (hr : IsUnit r) :
    _root_.AlgebraicGeometry.Scheme.principalOrderCycle (W.ι ''ᵁ ⊤)
      ((W.ι.appIso ⊤).inv (W.topIso.inv r))
      ((hr.map W.topIso.inv.hom).map (W.ι.appIso ⊤).inv.hom) =
      _root_.AlgebraicGeometry.Scheme.principalOrderCycle W r hr := by
  ext x
  rw [_root_.AlgebraicGeometry.Scheme.principalOrderCycle_apply,
      _root_.AlgebraicGeometry.Scheme.principalOrderCycle_apply]
  congr 1
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
  exact C.presheaf.germ_res_apply (eqToHom W.ι_image_top) _ _ r

private theorem toPoints_original
    {k : Type u} [Field k] (X Y : SmoothSite (Spec (.of k))) [IsAffine X.left]
    {C V : Scheme.{u}} [IsIntegral C] [IsNoetherian C] [V.IsQuasiAffine]
    (q : C ⟶ X.left) [IsProper q] (j : V ⟶ C) [IsOpenImmersion j]
    [SmoothOfRelativeDimension 1 (j ≫ q)]
    (W : C.Opens) [Nonempty W] (hW : (Set.range j)ᶜ ⊆ (W : Set C))
    (r : Γ(C, W)) (hr : IsUnit r) (g : V ⟶ Y.left)
    (hbase : j ≫ q ≫ X.hom = g ≫ Y.hom) :
    FiniteCorrespondence.toPoints (f := X.hom) (g := Y.hom)
      (correspondence q j W hW r hr g hbase) =
      _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
        (pullback.lift (j ≫ q) g (by simpa only [Category.assoc] using hbase))
        (_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
            (_root_.AlgebraicGeometry.Scheme.IntegralCycle.openImmersionRestriction j
          (_root_.AlgebraicGeometry.Scheme.IntegralCycle.fromPoints
              (_root_.AlgebraicGeometry.Scheme.principalOrderCycle W r hr)))) := by
  have he := correspondence_eq_finitePointCycle (X := X) (Y := Y)
    q j W hW r hr g hbase
  exact (congrArg (FiniteCorrespondence.toPoints (f := X.hom) (g := Y.hom)) he).trans
    (FinitePointCycleCorrespondence.toPoints_correspondence_retained_pushforward
      X Y q j (_root_.AlgebraicGeometry.Scheme.principalOrderCycle W r hr)
          (_root_.AlgebraicGeometry.Scheme.principalOrderCycle_support_range j W hW r hr)
      (fun x => _root_.AlgebraicGeometry.Scheme.principalOrderCycle_support_isFinite q j W hW r hr
          x.val
        (Finsupp.mem_support_iff.mp x.property))
      (fun x => _root_.AlgebraicGeometry.Scheme.principalOrderCycle_support_dominates_component q j
          W hW r hr x.val
        (Finsupp.mem_support_iff.mp x.property)) g hbase)

/-- The original omitted locus is covered by the original canonical open. -/
theorem canonical_boundary_cover {C V B : Scheme.{u}} (j : V ⟶ C) (W : C.Opens)
    (b : B ⟶ W.toScheme) (hcover : (Set.range j)ᶜ ⊆ Set.range (b ≫ W.ι)) :
    (Set.range j)ᶜ ⊆ (W : Set C) := by
  intro x hx
  obtain ⟨z, hz⟩ := hcover hx
  rw [← hz]
  exact (b z).property

end Motivic.PrincipalOrderCorrespondence

namespace Motivic.PresheafWithTransfers

attribute [local instance] Scheme.nonempty_image_open
  _root_.AlgebraicGeometry.PrincipalFamilyUnitOpen.nonemptyTop

/-- The principal correspondence of the original section on the original open
acts by zero on any ordinary HI PST. The actual boundary is neither reduced
nor replaced, and its full omitted-locus coverage remains a hypothesis. -/
theorem transfer_principalOrder_open_eq_zero
    {k : Type u} [Field k] (P : PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant)
    (X Y : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left]
    {C V B : Scheme.{u}} [IsIntegral C] [IsNoetherian C]
    [IsNoetherian V] [V.IsQuasiAffine]
    (q : C ⟶ X.left) [IsProper q] (j : V ⟶ C) [IsOpenImmersion j]
    [SmoothOfRelativeDimension 1 (j ≫ q)]
    (W : C.Opens) [Nonempty W] (r : Γ(C, W)) (hr : IsUnit r)
    (b : B ⟶ W.toScheme) [Nonempty B]
    (hcover : (Set.range j)ᶜ ⊆ Set.range (b ≫ W.ι))
    (hboundary : b.appTop (W.topIso.inv r) = 1)
    (g : V ⟶ Y.left) (hbase : j ≫ q ≫ X.hom = g ≫ Y.hom) :
    P.transfer (PrincipalOrderCorrespondence.correspondence q j W
      (PrincipalOrderCorrespondence.canonical_boundary_cover j W b hcover)
      r hr g hbase) = 0 := by
  let : IsNoetherian W.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      toCompactSpace := isCompact_iff_compactSpace.mp
        (TopologicalSpace.NoetherianSpace.isCompact (W : Set C)) }
  have ha := transfer_principalOrder_eq_zero P hP X Y q j W.ι b hcover
    (W.topIso.inv r) hboundary (hr.map W.topIso.inv.hom) g hbase
  have he : PrincipalOrderCorrespondence.correspondence q j (W.ι ''ᵁ ⊤)
      (PrincipalFamilyCorrespondence.original_boundary_cover j W.ι b hcover)
      ((W.ι.appIso ⊤).inv (W.topIso.inv r))
      ((hr.map W.topIso.inv.hom).map (W.ι.appIso ⊤).inv.hom) g hbase =
      PrincipalOrderCorrespondence.correspondence q j W
        (PrincipalOrderCorrespondence.canonical_boundary_cover j W b hcover) r hr g hbase := by
    apply FiniteCorrespondence.toPoints_injective
    rw [PrincipalOrderCorrespondence.toPoints_original,
      PrincipalOrderCorrespondence.toPoints_original,
      PrincipalOrderCorrespondence.principalOrderCycle_topIso]
  exact (congrArg P.transfer he).symm.trans ha

end Motivic.PresheafWithTransfers
