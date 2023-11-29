import Game.Levels.Inter.L07inter_comm

variable {U : Type}

World "Intersecciones"
Level 8
Title "La intersección es asociativa"

Introduction
"
Intenta usar los teoremas y tácticas aprendidos en los niveles anteriores para demostrar
este teorema por tus propios medios.
"

LemmaTab "Teoría de conjuntos"

LemmaDoc inter_assoc as "inter_assoc" in "Teoría de conjuntos"
"Dados tres conjuntos `A`, `B`, y `C`, `inter_assoc A B C` es una prueba de que
`(A ∩ B) ∩ C = A ∩ (B ∩ C)`."

/-- Dados tres conjuntos $A$, $B$, y $C$, $(A \cap B) \cap C = A \cap (B \cap C)$. -/
Statement inter_assoc (A B C : Set U) : (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  apply sub_antisymm
  intro x h1
  rewrite [inter_def]
  rewrite [inter_def] at h1
  Hint (strict := true) (hidden := true) "Si no ves cómo seguir, puede ser útil
  separar la primera parte de `{h1}` como una hipótesis separada.
  Puedes hacer esto con `have hAB : {x} ∈ A ∩ B := {h1}.left`."
  have h2 : x ∈ A ∩ B := h1.left
  rewrite [inter_def] at h2
  apply And.intro
  exact h2.left
  exact And.intro h2.right h1.right
  intro x h1
  apply And.intro
  exact And.intro h1.left h1.right.left
  exact h1.right.right

NewLemma inter_assoc

Conclusion
"
¡Bien hecho! Ahora puedes seguir al mundo de las uniones.
"
