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
el lado derecho. Alternativamente, la táctica `left` tiene el mismo efecto que `apply Or.inl`, y
`right` tiene el mismo efecto que `apply Or.inr`.

Puedes empezar esta prueba con `ext x` o `apply sub_antisymm`.
"

LemmaTab "∩∪"

LemmaDoc union_assoc as "union_assoc" in "∩∪"
"Dados conjuntos `A`, `B`, y `C`, `union_assoc A B C` es una prueba de que
`(A ∪ B) ∪ C = A ∪ (B ∪ C)`."

/-- Dados conjuntos $A$, $B$, y $C$, $(A \cup B) \cup C = A \cup (B \cup C)$. -/
Statement union_assoc (A B C : Set U) : (A ∪ B) ∪ C = A ∪ (B ∪ C) := by
  apply sub_antisymm
  intro x h
  rewrite [union_def]
  rewrite [union_def] at h
  cases' h with hAB hC
  cases' hAB with hA hB
  exact Or.inl hA
  Hint "Do you know which half of the goal you're going to prove now?"
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

NewHiddenTactic left right

Conclusion
"
Ya has aprendido a razonar sobre complementarios, intersecciones y uniones. ¡En el siguiente mundo,
los mezclaremos!
"
