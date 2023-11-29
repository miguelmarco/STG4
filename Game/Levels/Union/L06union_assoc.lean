import Game.Levels.Union.L05union_comm

variable {U : Type}

World "Uniones"
Level 6
Title "La unión is asociativa"

Introduction
"
En esta prueba, puede resultar útil la siguiente idea:
Si quieres demostrar una afirmación de tipo \"o\", y crees que puedes probar el lado izquierdo
, `apply Or.inl` establecerá el lado izquierdo como objetivo. Análogamente `apply Or.inr` para
el lado derecho.
"

LemmaTab "Teoría de conjuntos"

LemmaDoc union_assoc as "union_assoc" in "Teoría de conjuntos"
"Dados conjuntos `A`, `B`, y `C`, `union_assoc A B C` es una prueba de que
`(A ∪ B) ∪ C = A ∪ (B ∪ C)`."

/-- For any sets $A$, $B$, and $C$, $(A \cup B) \cup C = A \cup (B \cup C)$. -/
Statement union_assoc (A B C : Set U) : (A ∪ B) ∪ C = A ∪ (B ∪ C) := by
  apply sub_antisymm
  intro x h
  cases' h with hAB hC
  cases' hAB with hA hB
  exact Or.inl hA
  apply Or.inr
  exact Or.inl hB
  apply Or.inr
  exact Or.inr hC
  intro x h
  cases' h with hA hBC
  apply Or.inl
  exact Or.inl hA
  cases' hBC with hB hC
  apply Or.inl
  exact Or.inr hB
  exact Or.inr hC

NewLemma union_comm

Conclusion
"
Ya has aprendido a razonar sobre complementarios, intersecciones y uniones. ¡En el siguiente mundo,
los mezclaremos!
"
