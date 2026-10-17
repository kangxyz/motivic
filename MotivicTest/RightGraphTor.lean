/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.RightGraphTor

/-!
# Consumers of genuine right-graph Tor multiplicities and the right unit

These consumers use the actual Tor objects and their canonical finite Euler
coefficients. The regular list is obtained from smooth graph geometry rather
than supplied as a hypothesis. The single identity generator requires an
integral middle object; the source may be disconnected. Arbitrary signed
cycles are handled by the actual biadditive pairing.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence Motivic

universe u

namespace MotivicTest.RightGraphTor

variable (k : Type u) [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (ψ : ((𝟭 Scheme).obj Y.left) ⟶ ((𝟭 Scheme).obj Z.left))
  (hw : ψ ≫ Z.hom = Y.hom) [IsIntegral ((𝟭 Scheme).obj Y.left)]

/-- Genuine positive Tor vanishes at every actual incidence point of a right graph. -/
theorem graph_positive_tor
    (w : A.incidence (graphGeneratorOver (f := Y.hom) (g := Z.hom) ψ hw)) (n : ℕ) :
    IsZero (A.incidenceTor (graphGeneratorOver (f := Y.hom) (g := Z.hom) ψ hw) w (n + 1)) :=
  A.isZero_incidenceTor_succ_of_isIso_projection
    (graphGeneratorOver (f := Y.hom) (g := Z.hom) ψ hw) w n

/-- The actual generic Euler coefficient is proved equal to full local multiplicity. -/
theorem graph_actual_coefficient
    (x : genericPoints (A.incidence (graphGeneratorOver (f := Y.hom) (g := Z.hom) ψ hw))) :
    A.incidenceTorCoefficient (S := Spec (.of k))
      (graphGeneratorOver (f := Y.hom) (g := Z.hom) ψ hw) x =
      (genericMultiplicity x : ℤ) :=
  A.incidenceTorCoefficient_eq_genericMultiplicity_of_isIso_projection k (Z := Z)
    (graphGeneratorOver (f := Y.hom) (g := Z.hom) ψ hw) x

/-- Both signed generator coefficients are retained in the genuine graph comparison. -/
theorem signed_graph_basis (m n : ℤ) :
    FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := Z)
      (Finsupp.single A m) (Finsupp.single (graphGeneratorOver (f := Y.hom) (g := Z.hom) ψ hw) n) =
      (m * n) • A.incidenceFundamentalCorrespondence k (Z := Z)
        (graphGeneratorOver (f := Y.hom) (g := Z.hom) ψ hw) := by
  rw [FiniteCorrespondence.incidenceTorPairing_single,
    A.incidenceTorCorrespondence_graph_right k (Z := Z) ψ hw]

/-- Faithful forgetting gives the actual full fundamental pushforward for a graph. -/
theorem graph_actual_pushforward :
    FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Z.hom)
      (A.incidenceTorCorrespondence k (Z := Z)
        (graphGeneratorOver (f := Y.hom) (g := Z.hom) ψ hw)) =
      IntegralCycle.finitePushforward
        (A.incidenceMap (graphGeneratorOver (f := Y.hom) (g := Z.hom) ψ hw))
        (fundamentalCycle (A.incidence (graphGeneratorOver (f := Y.hom) (g := Z.hom) ψ hw))) := by
  rw [A.incidenceTorCorrespondence_graph_right k (Z := Z) ψ hw]
  exact A.toIntegralCycle_incidenceFundamentalCorrespondence k (Z := Z)
    (graphGeneratorOver (f := Y.hom) (g := Z.hom) ψ hw)

/-- The actual identity coefficient has multiplicity one, with no higher Tor corrections. -/
theorem identity_actual_coefficient (x : genericPoints (A.incidence (identityGenerator Y.hom))) :
    A.incidenceTorCoefficient (S := Spec (.of k)) (identityGenerator Y.hom) x = 1 := by
  rw [A.incidenceTorCoefficient_eq_genericMultiplicity_of_isIso_projection k]
  have hm := genericMultiplicity_mapGenericPoint A.rightIdentityIncidenceIso.hom x
  rw [genericMultiplicity_eq_one] at hm
  exact congrArg (fun n : ℕ => (n : ℤ)) hm.symm

/-- The genuine single identity graph is a right unit for every signed correspondence. -/
theorem arbitrary_signed_right_unit (α : FiniteCorrespondence X.hom Y.hom) :
    FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := Y)
      α (identityGenerator Y.hom).cycle = α :=
  FiniteCorrespondence.incidenceTorPairing_identity_right k α

end MotivicTest.RightGraphTor
