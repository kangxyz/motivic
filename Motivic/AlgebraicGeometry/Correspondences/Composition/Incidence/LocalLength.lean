/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Support.Embedding
public import Motivic.Aglib.AlgebraicGeometry.Stalk.Generic.Support
public import Motivic.Aglib.RingTheory.LocalLength.KoszulPairSupport

/-!
# Local finite lengths on actual incidence supports

The incidence closed embedding identifies its actual generic stalk with an
Artinian quotient of the ambient triple-product stalk. A literal kernel
containment in the equations plus the coefficient annihilator therefore gives
finite two-element Koszul homology. This proves a conditional geometric length
bridge; it does not construct equations for a general smooth diagonal, impose
regularity on coefficient modules, or define correspondence composition.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace Motivic
open _root_.AlgebraicGeometry.Scheme.Products

variable {S X Y Z : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S}

/-- Finite-type outer factors over a locally Noetherian middle factor give a
locally Noetherian actual triple product. -/
theorem isLocallyNoetherian_correspondenceTripleProduct
    [LocallyOfFiniteType f] [LocallyOfFiniteType h] [IsLocallyNoetherian Y] :
    IsLocallyNoetherian (correspondenceTripleProduct f g h) := by
  have : IsLocallyNoetherian (pullback f g) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f g)
  exact LocallyOfFiniteType.isLocallyNoetherian
    (pullback.fst (pullback.snd f g) (pullback.fst g h))

namespace FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Products

variable (A : FiniteCorrespondenceGenerator f g) (B : FiniteCorrespondenceGenerator g h)

/-- Incidence is locally Noetherian over a locally Noetherian source. -/
theorem isLocallyNoetherian_incidence [IsLocallyNoetherian X] :
    IsLocallyNoetherian (A.incidence B) :=
  LocallyOfFiniteType.isLocallyNoetherian (A.incidenceSource B)

/-- The ambient stalk modulo the literal incidence stalk kernel is Artinian
at each actual generic point of the incidence scheme. -/
theorem incidence_stalk_quotient_isArtinian [IsLocallyNoetherian X]
    (w : A.incidence B) (hw : w ∈ genericPoints (A.incidence B)) :
    IsArtinianRing
      (((correspondenceTripleProduct f g h).presheaf.stalk ((A.incidenceInclusion B) w)) ⧸
        RingHom.ker ((A.incidenceInclusion B).stalkMap w).hom) := by
  have := isLocallyNoetherian_incidence A B
  exact stalk_quotient_ker_isArtinian (A.incidenceInclusion B) w hw

/-- A literal support-kernel containment supplies finite Koszul homology at an
actual incidence generic point. The two equations need not be regular. -/
theorem incidence_koszul_hasFiniteHomology
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [LocallyOfFiniteType f] [LocallyOfFiniteType h]
    (w : A.incidence B) (hw : w ∈ genericPoints (A.incidence B))
    (M : Type v) [AddCommGroup M]
    [Module ((correspondenceTripleProduct f g h).presheaf.stalk
      ((A.incidenceInclusion B) w)) M]
    [Module.Finite ((correspondenceTripleProduct f g h).presheaf.stalk
      ((A.incidenceInclusion B) w)) M]
    (a b : (correspondenceTripleProduct f g h).presheaf.stalk ((A.incidenceInclusion B) w))
    (hker : RingHom.ker ((A.incidenceInclusion B).stalkMap w).hom ≤
      Ideal.span ({a, b} : Set _) ⊔ Module.annihilator _ M) :
    Module.KoszulPair.HasFiniteHomology M a b := by
  have := isLocallyNoetherian_incidence A B
  have := isLocallyNoetherian_correspondenceTripleProduct (f := f) (g := g) (h := h)
  refine ⟨length_ne_top_of_generic_stalk_support (A.incidenceInclusion B) w hw
      (Module.KoszulPair.H₀ M a b) ?_,
    length_ne_top_of_generic_stalk_support (A.incidenceInclusion B) w hw
      (Module.KoszulPair.H₁ M a b) ?_,
    length_ne_top_of_generic_stalk_support (A.incidenceInclusion B) w hw
      (Module.KoszulPair.H₂ M a b) ?_⟩
  · exact hker.trans (Module.KoszulPair.span_sup_annihilator_le_annihilator_H₀ M a b)
  · exact hker.trans (Module.KoszulPair.span_sup_annihilator_le_annihilator_H₁ M a b)
  · exact hker.trans (Module.KoszulPair.span_sup_annihilator_le_annihilator_H₂ M a b)

end FiniteCorrespondenceGenerator

end Motivic
