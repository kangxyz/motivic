# Dependent two-entry families

[TwoCases](TwoCases.lean) supplies the native `Fin.twoCases` for any dependent
family `M : Fin 2 → Sort v`, with values `a : M 0`, `b : M 1` and result
`∀ i, M i`. Its definition is the literal nested `Fin.cases` eliminator.
`Fin.twoCases_zero`, `Fin.twoCases_one`, `Fin.twoCases_mk_zero` and
`Fin.twoCases_mk_one` are the numeral and explicit-constructor simp rules.
The proof witnesses in the constructor forms are arbitrary proofs of the
corresponding bounds.

There are no scheme or motivic hypotheses. The current consumers construct
[original norm-pair](../../AlgebraicGeometry/RelativeCurve/Pencils/Norm/OriginalPairNormDiagram.lean)
and [correction-pair](../../AlgebraicGeometry/RelativeCurve/Pencils/Correction/OriginalCorrectionNormDiagram.lean)
dependent diagrams. Intended upstream module: `Aglib.Data.Fin.TwoCases`.
