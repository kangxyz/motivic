module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Normalized.CommonBoundary
/-! Both original source products use the same full nilpotent-sensitive boundary. -/
@[expose] public noncomputable section
set_option linter.hashCommand false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.AffineLineEtaleCompactification
universe u
variable (k : Type u) [Field k] {Y S A X : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
  (r : S ⟶ Y) [IsOpenImmersion r] (a : A ⟶ Spec (.of (Polynomial k)))
  (α : X ⟶ S) (β : X ⟶ A) (h : α ≫ r ≫ p = β ≫ a)
  (B : Type u) [CommRing B] (z : Polynomial k →+* B) (s : Spec (.of B) ⟶ S)
  (hs : s ≫ r ≫ p = Scheme.Hom.boundaryCoordinateMap k B z)
example := commonBoundaryToDiagonal_inclusion k p r α B s
example := commonBoundaryToFixed_inclusion k p r a α β h B z s hs
example := commonToDiagonal_isPullback k p r α
example := commonToFixed_isPullback k p r a α β h
#print axioms commonBoundaryToFixed_inclusion
#print axioms commonToDiagonal_isPullback
#print axioms commonToFixed_isPullback
