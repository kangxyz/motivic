/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Original.FiberSections
public import Lean.Util.CollectAxioms

/-! Actual original-point fiber sections and their original restriction square. -/
@[expose] public noncomputable section
open CategoryTheory Opposite AlgebraicGeometry
universe u
namespace MotivicTest.OriginalFiberSections
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {X : Scheme.{u}} {V U : Scheme.EtaleSeparatedFiniteType X} (x : X) (g : U ⟶ V)
  (F : Sheaf (nisnevichTopology (Spec (X.residueField x))) AddCommGrpCat.{u + 1})

/-- The consumer uses the original field-map restriction and original fiber index. -/
theorem actual_restriction_square
    (s : F.obj.obj (op ((baseChange (X.fromSpecResidueField x)).obj V)))
    (v : U.hom ⁻¹' {x}) :
    originalFiberSectionsEquiv U x F
        (F.obj.map ((baseChange (X.fromSpecResidueField x)).map g).op s) v =
      F.obj.map (originalFiberObjectMap x g v).op
        (originalFiberSectionsEquiv V x F s (originalFiberIndex x g v)) :=
  originalFiberSectionsEquiv_map x g F s v

open Lean in
run_cmd do
  for name in #[``actual_restriction_square,
      ``_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.originalFiberSectionsEquiv,
      ``originalFiberObjects_mem_precoverage,
      ``originalFiberSectionsEquiv_naturality] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original fiber section products and restriction naturality: standard foundations only."

end MotivicTest.OriginalFiberSections
