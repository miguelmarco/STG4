import Game.Levels.Union.L04union_sub_swap

variable {U : Type}

World "Uniones"
Level 5
Title "La union is conmutativa"

Introduction
"
Si empiezas tu prueba con `apply sub_antisymm`, podrás usar el teorema `union_sub_swap` que probaste
en el nivel anterior.
"

LemmaTab  "∩∪"

LemmaDoc union_comm as "union_comm" in  "∩∪"
"Dados dos conjuntos `A` y `B`, `union_comm A B` es una prueba de que `A ∪ B = B ∪ A`."

/-- Dados conjuntos $A$ y $B$, $A \cup B = B \cup A$. -/
Statement union_comm (A B : Set U) : A ∪ B = B ∪ A := by
  apply sub_antisymm
  exact union_sub_swap A B
  exact union_sub_swap B A

NewLemma union_comm

Conclusion
"
Ahora probaremos la asociatividad de la unión.
"
