import Game.Levels.Combo.L03inter_distrib_union

variable {U : Type}

World "Combination"
Level 4
Title "Distributividad de la unión respecto a la intersección"

Introduction
"
Este es diferente del anterior: el papel de la unión e intersección se ha intercambiado.

De nuevo, se puede usar un atajo: hay una forma de usar el teorema anterior para demostrar este
teorema.

Pero si no ves el atajo, puedes usar el método directo. ¡Si pudiste con el anterior, podrás con
este!
"

LemmaTab "∩∪"

LemmaDoc union_distrib_over_inter as "union_distrib_over_inter" in "∩∪"
"Dados conjuntos `A`, `B`, y `C`, `union_distrib_over_inter A B C` es una prueba de
`A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)`."

/-- Dados conjuntos $A$, $B$, y $C$, $A \cup (B \cap C) = (A \cup B) \cap (A \cup C)$. -/
Statement union_distrib_over_inter (A B C : Set U) : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  rewrite [← comp_comp (A ∪ (B ∩ C))]
  rewrite [comp_union]
  rewrite [comp_inter B C]
  rewrite [inter_distrib_over_union]
  rewrite [comp_union]
  rewrite [comp_inter, comp_inter]
  rewrite [comp_comp, comp_comp, comp_comp]
  rfl

NewLemma union_distrib_over_inter

Conclusion
"
Para terminar el mundo de las uniones, veremos un último teorema complicadillo.
"
