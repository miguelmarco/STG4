import Game.Levels.Inter.L07inter_comm

variable {U : Type}

World "Intersecciones"
Level 8
Title "La intersección es asociativa"

Introduction
"
Nuestro objetivo en este nivel es, de nuevo, una igualdad entre conjuntos. En otras pruebas
anteriores de este tipo, empezamos con la táctica `apply sub_antisymm`, y eso también funcionaría
aquí. Pero vamos a probar una alternativa: la táctica `ext`. Esta táctica aplica el *principio de
extensionalidad* para conjuntos, que dice que si dos conjuntos tienen exactamente los mismos
elementos, son iguales.
"

/-
Si tu objetivo es `A = B`, donde `A` y `B` son conjuntos, y usas la táctica `ext x`, Lean
introducirá un nuevo objeto arbitrario `x` y establecerá `x ∈ A ↔ x ∈ B` como nuevo objetiv. Al
probarlo, habrás mostrado que `A` y `B` tienen exactamente los mismos elementos, y por el principio
de extensionalidad, que son iguales.

Intenta usar los teoremas y tácticas aprendidos en los niveles anteriores para demostrar
este teorema por tus propios medios.
-/

LemmaTab "∩∪"

LemmaDoc inter_assoc as "inter_assoc" in "∩∪"
"Dados tres conjuntos `A`, `B`, y `C`, `inter_assoc A B C` es una prueba de que
`(A ∩ B) ∩ C = A ∩ (B ∩ C)`."

TacticDoc ext
"
Si tu objetivo es `A = B`, donde `A` y `B` son conjuntos, la táctica `ext x` introducirá un nuevo
objeto `x` y cambiará el objetivo a `x ∈ A ↔ x ∈ B`.
"

NewTactic ext

/-- Dados tres conjuntos $A$, $B$, y $C$, $(A \cap B) \cap C = A \cap (B \cap C)$. -/
Statement inter_assoc (A B C : Set U) : (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  Hint "To start this proof, use the tactic `ext x`."
  ext x
  Hint "Notice that Lean has introduced the new object `{x} : U` into the proof, and
  your goal is now `{x} ∈ (A ∩ B) ∩ C ↔ {x} ∈ A ∩ (B ∩ C)`.  Proving this goal will show that
  `(A ∩ B) ∩ C` and `A ∩ (B ∩ C)` have exactly the same elements, and by the principle of
  extensionality, that will show that the sets are equal."
  Hint (hidden := true) "Since your goal is an \"if and only if\" statement, a good next step
  is `apply Iff.intro`."
  apply Iff.intro
  Hint (hidden := true) "Since your goal is an \"if-then\" statement, a good next step
  is `intro h1`."
  intro h1
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
  intro h1
  apply And.intro
  exact And.intro h1.left h1.right.left
  exact h1.right.right

NewLemma inter_assoc

Conclusion
"
¡Bien hecho! Ahora puedes seguir al mundo de las uniones.
"
