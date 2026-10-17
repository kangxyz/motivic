/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Graph.CommonStalkTransport

/-!
# Point-identification transport of a common regular stalk list

The actual source and coefficient points of a common-list presentation may be
replaced by equal points. This explicit dependent transport retains both maps,
the exact kernel, and regularity of the same literal image list.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open RingTheory.Sequence

universe u

namespace Motivic.Graph

/-- Replacing the three points by equal points preserves the actual common-list statement. -/
theorem common_regular_list_congr_points {D Q P : Scheme.{u}}
    (i : D ⟶ P) (q : Q ⟶ P)
    (d d' : D) (z z' : Q) (p p' : P) (hd : d = d') (hz : z = z') (hp : p = p')
    (hdi : p = i d) (hzq : p = q z) (hdi' : p' = i d') (hzq' : p' = q z')
    (h : ∃ rs : List (P.presheaf.stalk p), IsRegular (P.presheaf.stalk p) rs ∧
      RingHom.ker (alignedStalkMap i d p hdi).hom = Ideal.ofList rs ∧
      IsRegular (Q.presheaf.stalk z) (rs.map (alignedStalkMap q z p hzq).hom)) :
    ∃ rs : List (P.presheaf.stalk p'), IsRegular (P.presheaf.stalk p') rs ∧
      RingHom.ker (alignedStalkMap i d' p' hdi').hom = Ideal.ofList rs ∧
      IsRegular (Q.presheaf.stalk z') (rs.map (alignedStalkMap q z' p' hzq').hom) := by
  subst d'
  subst z'
  subst p'
  exact h

/-- An equal coefficient point preserves a common list with the source kernel map unchanged. -/
theorem common_regular_list_congr_coefficient_point {D Q P : Scheme.{u}}
    (i : D ⟶ P) (q : Q ⟶ P) (d : D) (z z' : Q) (hz : z = z')
    (hq : i d = q z) (hq' : i d = q z')
    (h : ∃ rs : List (P.presheaf.stalk (i d)), IsRegular (P.presheaf.stalk (i d)) rs ∧
      RingHom.ker (i.stalkMap d).hom = Ideal.ofList rs ∧
      IsRegular (Q.presheaf.stalk z) (rs.map (alignedStalkMap q z (i d) hq).hom)) :
    ∃ rs : List (P.presheaf.stalk (i d)), IsRegular (P.presheaf.stalk (i d)) rs ∧
      RingHom.ker (i.stalkMap d).hom = Ideal.ofList rs ∧
      IsRegular (Q.presheaf.stalk z') (rs.map (alignedStalkMap q z' (i d) hq').hom) := by
  subst z'
  exact h

end Motivic.Graph
