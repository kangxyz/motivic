# Sections on a boundary coproduct

[CoproductBoundary](CoproductBoundary.lean) supplies two native
`AlgebraicGeometry.Scheme` interfaces for schemes in universe `u`.
`section_eq_of_coprod_app_eq` says that sections `s,t` on any open of
`B₁ ⨿ B₂` are equal when their pullbacks along both coproduct injections
are equal. It uses the actual coproduct presheaf isomorphism.
`coprod_desc_app_eq_one` applies this to a section on any target open:
value one along `b₁ : B₁ ⟶ T` and `b₂ : B₂ ⟶ T` implies value one
along `coprod.desc b₁ b₂`.

No reducedness, nonemptiness, affineness or integrality hypothesis is imposed.
In particular, the two full boundary schemes retain their nilpotents. The
[R3/R5 constructors](../../RelativeCurve/Pencils/README.md) use this detection after
separate marked and infinity section calculations; agreement on underlying
supports would not provide either input. Intended upstream module:
`Aglib.AlgebraicGeometry.Scheme.Sections.CoproductBoundary`.
