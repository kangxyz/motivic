/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.IncidenceCycle
public import Motivic.AlgebraicGeometry.Correspondences.IncidenceTor

/-!
# Actual diagonal-Tor incidence cycles and their biadditive extension

The genuine finite-length categorical Tor coefficient on every generic
incidence component is fed into the degree-weighted finite-image assembly.
Thus two smooth-site correspondence generators give an actual finite
correspondence, including higher Tor corrections, residue-field degrees,
and possible collisions of component images.

The faithful integral-cycle representation is the actual finite pushforward
of the Tor-weighted generic component cycle. A biadditive extension is
constructed on arbitrary finite correspondence cycles. This is a diagonal-Tor
candidate composition operation. Its change-of-ambient comparison with
pulled-back-support Tor inside the triple product remains separate. No
associativity, unit law, graph comparison, or equality with an ordinary
fundamental cycle is asserted here.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

universe u

namespace Motivic

namespace FiniteCorrespondenceGenerator

variable (k : Type u) [Field k]
  {X Y Z : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)

/-- The actual Tor-weighted incidence correspondence, using its proved finite local
lengths, finite component images, and genuine residue-field degrees. -/
noncomputable def incidenceTorCorrespondence : FiniteCorrespondence X.hom Z.hom :=
  A.incidenceCycleAssembly k B (A.incidenceTorCoefficient (S := Spec (.of k)) B)

/-- Forgetting admissibility gives exactly the finite pushforward of the actual
categorical Tor coefficient cycle on the genuine incidence scheme. -/
theorem toIntegralCycle_incidenceTorCorrespondence :
    FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Z.hom)
      (A.incidenceTorCorrespondence k B) =
      IntegralCycle.finitePushforward (A.incidenceMap B)
        (IntegralCycle.ofGenericCoefficients (A.incidence B)
          (A.incidenceTorCoefficient (S := Spec (.of k)) B)) :=
  A.toIntegralCycle_incidenceCycleAssembly k B (A.incidenceTorCoefficient (S := Spec (.of k)) B)

open Classical in
/-- All genuine Tor contributions whose finite images coincide are added with their
own actual residue-field degrees. No injectivity of component images is assumed. -/
theorem incidenceTorCorrespondence_coefficient
    (V : FiniteCorrespondenceGenerator X.hom Z.hom) :
    A.incidenceTorCorrespondence k B V =
      letI := IntegralCycle.genericPointFintype (A.incidence B)
      ∑ x, if A.smoothIncidenceComponentGenerator k B x = V then
        A.incidenceTorCoefficient (S := Spec (.of k)) B x *
          ((A.incidenceMap B).residueDegree x.val : ℤ) else 0 :=
  A.incidenceCycleAssembly_coefficient k B (A.incidenceTorCoefficient (S := Spec (.of k)) B) V

end FiniteCorrespondenceGenerator

namespace FiniteCorrespondence

variable (k : Type u) [Field k]
  {X Y Z : SmoothSite (Spec (.of k))}

/-- The biadditive diagonal-Tor candidate operation on actual generators.
The triple-product Tor comparison, associativity, and unit laws remain unproved. -/
noncomputable def incidenceTorPairing :
    FiniteCorrespondence X.hom Y.hom →+
      FiniteCorrespondence Y.hom Z.hom →+ FiniteCorrespondence X.hom Z.hom :=
  Finsupp.liftAddHom fun A =>
    zmultiplesHom _ (Finsupp.liftAddHom fun B =>
      zmultiplesHom _ (A.incidenceTorCorrespondence k B))

/-- On any two actual basis vectors, both integer multiplicities are retained. -/
@[simp]
theorem incidenceTorPairing_single
    (A : FiniteCorrespondenceGenerator X.hom Y.hom)
    (B : FiniteCorrespondenceGenerator Y.hom Z.hom) (m n : ℤ) :
    incidenceTorPairing k (X := X) (Y := Y) (Z := Z) (Finsupp.single A m) (Finsupp.single B n) =
      (m * n) • A.incidenceTorCorrespondence k B := by
  simp [incidenceTorPairing, smul_smul]

/-- Multiplicity-one geometric input cycles recover the actual Tor incidence cycle. -/
@[simp]
theorem incidenceTorPairing_cycle
    (A : FiniteCorrespondenceGenerator X.hom Y.hom)
    (B : FiniteCorrespondenceGenerator Y.hom Z.hom) :
    incidenceTorPairing k (X := X) (Y := Y) (Z := Z) A.cycle B.cycle =
      A.incidenceTorCorrespondence k B := by
  simpa only [FiniteCorrespondenceGenerator.cycle, one_mul, one_smul] using
    incidenceTorPairing_single k A B 1 1

/-- The candidate operation is additive in its first cycle argument. -/
theorem incidenceTorPairing_add_left (α α' : FiniteCorrespondence X.hom Y.hom)
    (β : FiniteCorrespondence Y.hom Z.hom) :
    incidenceTorPairing k (X := X) (Y := Y) (Z := Z) (α + α') β =
      incidenceTorPairing k (X := X) (Y := Y) (Z := Z) α β +
        incidenceTorPairing k (X := X) (Y := Y) (Z := Z) α' β := by
  rw [map_add, AddMonoidHom.add_apply]

/-- The candidate operation is additive in its second cycle argument. -/
theorem incidenceTorPairing_add_right (α : FiniteCorrespondence X.hom Y.hom)
    (β β' : FiniteCorrespondence Y.hom Z.hom) :
    incidenceTorPairing k (X := X) (Y := Y) (Z := Z) α (β + β') =
      incidenceTorPairing k (X := X) (Y := Y) (Z := Z) α β +
        incidenceTorPairing k (X := X) (Y := Y) (Z := Z) α β' :=
  map_add _ _ _

end FiniteCorrespondence

end Motivic
