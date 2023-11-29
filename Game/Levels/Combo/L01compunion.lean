import Game.Levels.Union

variable {U : Type}

World "Combination"
Level 1
Title "Complementario de la unión"

Introduction
"
Conforme las pruebas se van volviendo más difíciles, puedes descubrir que es útil usar la
táctica `have` para establecer una afirmación cuya demostración es demasíado compleja para hacerla
en una línea.
Para ver ayuda sobre cómo hacerlo, puedes pulsar en `have` en la lista de tácticas a la derecha.
"

LemmaTab "Teoría de conjuntos"

LemmaDoc comp_union as "comp_union" in "Teoría de conjuntos"
"Dados conjuntos `A` and `B`, `comp_union A B` es una prueba de que `(A ∪ B)ᶜ = Aᶜ ∩ Bᶜ`."

/-- Dados conjuntos $A$ y $B$, $(A \cup B)^c = A^c \cap B^c$. -/
Statement comp_union (A B : Set U) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  apply sub_antisymm
  intro x h1
  rewrite [comp_def] at h1
  rewrite [inter_def, comp_def, comp_def]
  apply And.intro
  by_contra h2
  have h3 : x ∈ A ∪ B := Or.inl h2
  exact h1 h3
  by_contra h2
  have h3 : x ∈ A ∪ B := Or.inr h2
  exact h1 h3
  intro x h1
  rewrite [inter_def, comp_def, comp_def] at h1
  rewrite [comp_def]
  by_contra h2
  cases' h2 with h2A h2B
  exact h1.left h2A
  exact h1.right h2B

NewLemma comp_union

Conclusion
"

"
