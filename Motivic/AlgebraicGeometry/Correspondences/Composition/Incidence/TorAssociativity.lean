/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Incidence.LeftComposition
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Incidence.RightComposition

/-!
# Associativity of the actual incidence Tor pairing

Both literal generator brackets equal the same canonical triple Tor
correspondence. Their proved comparisons give generator associativity directly.
The existing biadditive pairing then extends this equality to every signed
finite correspondence by additive-homomorphism extensionality in each of the
three arguments. Integer scalar preservation includes negative multiplicities
and zero without imposing any effectiveness condition.

The field is arbitrary, and the four smooth-site objects need not be connected
or integral. No comparison is supplied by the caller. This file does not
construct a category, a graph functor, or a replacement composition operation.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondence
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] {X Y Z W : SmoothSite (Spec (.of k))}

/-- The two actual nested generator pairings agree through their independently
proved equalities with the same canonical triple Tor correspondence. -/
theorem incidenceTorPairing_assoc_cycle
    (F : FiniteCorrespondenceGenerator X.hom Y.hom)
    (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
    (H : FiniteCorrespondenceGenerator Z.hom W.hom) :
    incidenceTorPairing k (X := X) (Y := Z) (Z := W)
        (incidenceTorPairing k (X := X) (Y := Y) (Z := Z) F.cycle G.cycle) H.cycle =
      incidenceTorPairing k (X := X) (Y := Y) (Z := W)
        F.cycle (incidenceTorPairing k (X := Y) (Y := Z) (Z := W) G.cycle H.cycle) :=
  (F.incidenceTorPairing_left_cycle_eq_tripleTorCorrespondence
    (X := X) (Y := Y) (Z := Z) (W := W) k G H).trans
      (F.incidenceTorPairing_right_cycle_eq_tripleTorCorrespondence
        (X := X) (Y := Y) (Z := Z) (W := W) k G H).symm

/-- The actual incidence Tor pairing is associative on all signed finite
correspondence cycles over an arbitrary field. -/
theorem incidenceTorPairing_assoc
    (α : FiniteCorrespondence X.hom Y.hom)
    (β : FiniteCorrespondence Y.hom Z.hom)
    (γ : FiniteCorrespondence Z.hom W.hom) :
    incidenceTorPairing k (X := X) (Y := Z) (Z := W)
        (incidenceTorPairing k (X := X) (Y := Y) (Z := Z) α β) γ =
      incidenceTorPairing k (X := X) (Y := Y) (Z := W)
        α (incidenceTorPairing k (X := Y) (Y := Z) (Z := W) β γ) := by
  have hthird (F : FiniteCorrespondenceGenerator X.hom Y.hom)
      (G : FiniteCorrespondenceGenerator Y.hom Z.hom) :
      incidenceTorPairing k (X := X) (Y := Z) (Z := W)
          (incidenceTorPairing k (X := X) (Y := Y) (Z := Z) F.cycle G.cycle) =
        (incidenceTorPairing k (X := X) (Y := Y) (Z := W) F.cycle).comp
          (incidenceTorPairing k (X := Y) (Y := Z) (Z := W) G.cycle) := by
    apply Finsupp.addHom_ext
    intro H n
    have hsingle : Finsupp.single H n = n • H.cycle := by
      simp [FiniteCorrespondenceGenerator.cycle]
    rw [hsingle, map_zsmul, map_zsmul]
    change n • incidenceTorPairing k (X := X) (Y := Z) (Z := W)
        (incidenceTorPairing k (X := X) (Y := Y) (Z := Z) F.cycle G.cycle) H.cycle =
      n • incidenceTorPairing k (X := X) (Y := Y) (Z := W)
        F.cycle (incidenceTorPairing k (X := Y) (Y := Z) (Z := W) G.cycle H.cycle)
    exact congrArg (fun δ => n • δ)
      (incidenceTorPairing_assoc_cycle k (X := X) (Y := Y) (Z := Z) (W := W) F G H)
  have hsecond (F : FiniteCorrespondenceGenerator X.hom Y.hom) :
      ((incidenceTorPairing k (X := X) (Y := Z) (Z := W)).flip γ).comp
          (incidenceTorPairing k (X := X) (Y := Y) (Z := Z) F.cycle) =
        (incidenceTorPairing k (X := X) (Y := Y) (Z := W) F.cycle).comp
          ((incidenceTorPairing k (X := Y) (Y := Z) (Z := W)).flip γ) := by
    apply Finsupp.addHom_ext
    intro G n
    have hsingle : Finsupp.single G n = n • G.cycle := by
      simp [FiniteCorrespondenceGenerator.cycle]
    rw [hsingle, map_zsmul, map_zsmul]
    change n • incidenceTorPairing k (X := X) (Y := Z) (Z := W)
        (incidenceTorPairing k (X := X) (Y := Y) (Z := Z) F.cycle G.cycle) γ =
      n • incidenceTorPairing k (X := X) (Y := Y) (Z := W)
        F.cycle (incidenceTorPairing k (X := Y) (Y := Z) (Z := W) G.cycle γ)
    exact congrArg (fun f => n • f γ) (hthird F G)
  have hfirst :
      ((incidenceTorPairing k (X := X) (Y := Z) (Z := W)).flip γ).comp
          ((incidenceTorPairing k (X := X) (Y := Y) (Z := Z)).flip β) =
        (incidenceTorPairing k (X := X) (Y := Y) (Z := W)).flip
          (incidenceTorPairing k (X := Y) (Y := Z) (Z := W) β γ) := by
    apply Finsupp.addHom_ext
    intro F n
    have hsingle : Finsupp.single F n = n • F.cycle := by
      simp [FiniteCorrespondenceGenerator.cycle]
    rw [hsingle, map_zsmul, map_zsmul]
    change n • incidenceTorPairing k (X := X) (Y := Z) (Z := W)
        (incidenceTorPairing k (X := X) (Y := Y) (Z := Z) F.cycle β) γ =
      n • incidenceTorPairing k (X := X) (Y := Y) (Z := W)
        F.cycle (incidenceTorPairing k (X := Y) (Y := Z) (Z := W) β γ)
    exact congrArg (fun f => n • f β) (hsecond F)
  exact congrArg (fun f => f α) hfirst

end Motivic.FiniteCorrespondence
