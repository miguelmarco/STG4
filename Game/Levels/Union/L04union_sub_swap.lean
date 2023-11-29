import Game.Levels.Union.L03cases

variable {U : Type}

World "Uniones"
Level 4
Title "La unión es subconjunto de la unión conmutada"

Introduction
"
En el siguiente nivel probaremos que la unión es conmutativa; es decir, que `A ∪ B = B ∪ A`.
Seguiremos el mismo enfoque usado en el mundo de las interseciones. Empezaremos probando
`A ∪ B ⊆ B ∪ A`.
"

LemmaTab "Teoria de conjuntos"

LemmaDoc union_sub_swap as "union_sub_swap" in "Teoría de conjuntos"
"Para conjuntos `A` y `B`, `union_sub_swap A B` es una prueba de
`A ∪ B ⊆ B ∪ A`."

/-- Para conjuntos $A$ y $B$, $A \cup B \subseteq B \cup A$. -/
Statement union_sub_swap (A B : Set U) : A ∪ B ⊆ B ∪ A := by
  intro x h
  Hint (hidden := true) "Puede ser útil reescribir la definición de union en la hipótesis {h}
  y el objetivo."
  rewrite [union_def]
  rewrite [union_def] at h
  Hint (hidden := true) "La forma de la hipótesis {h} sugiere demostrar por casos."
  cases' h with hA hB
  exact Or.inr hA
  exact Or.inl hB

NewLemma union_sub_swap

Conclusion
"
En el siguiente nivel podrás usar `union_sub_swap` para probar que la unión es conmutativa.
"
