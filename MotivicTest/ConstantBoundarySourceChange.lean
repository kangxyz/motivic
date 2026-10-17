module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.ConstantBoundarySourceChange
/-! Both whole boundary components commute with the original ambient source change. -/
@[expose] public noncomputable section
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry
universe u
example {X S C K D Z : Scheme.{u}} (α : X ⟶ S) (q : S ⟶ K) (π : C ⟶ K)
    (qX : X ⟶ K) (h : qX = α ≫ q) (d : D ⟶ C) (z : Z ⟶ C) :=
  Scheme.constantFullBoundarySourceMap_inclusion α q π qX h d z
#print axioms Scheme.constantFullBoundarySourceMap_inclusion
