import Game.Levels.Union.L01or

variable {U : Type}

World "Uniones"
Level 2
Title "Subconjunto de una unión"

Introduction
"
Al igual que con complementarios e intersecciones, una de las herramientas clave para demostrar
teoremas sobre uniones es un teorema que establece la definición. Si tienes
`x : U`, `A : Set U` y `B : Set U`,
entonces `union_def x A B` es una prueba de la afirmación `x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B`.
Esto significa que puedes usar `rewrite [union_def]` para reescribir la definición de
`x ∈ A ∪ B` si aparece en alguna hipótesis o en el objetivo.
"

DefinitionDoc union as "∪"
"Si `A` y `B` son conjuntos, entonces `A ∪ B` es la unión de `A` y `B`.
Para introducir el símbolo `∪`, teclea `\\union`."

NewDefinition union

LemmaTab "∩∪"

LemmaDoc union_def as "union_def" in "∩∪"
"Si tenemos `x : U`, `A : Set U`, y `B : Set U`, entonces `union_def x A B` es una prueba de la
afirmación `x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B`."

lemma union_def (x : U) (A B : Set U) : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := by rfl

NewLemma union_def

/-- Supón que $A$ y $B$ son conjuntos. Entonces $B \subseteq A \cup B$. -/
Statement (A B : Set U) : B ⊆ A ∪ B := by
  Hint (hidden := true) "Tu objetivo es probar un contenido.
  Esto debería decirte cómo empezar."
  intro x h
  Hint "Reescriibir la definición de unión en el objetivo debería ayudarte a saber cómo seguir."
  rewrite [union_def]
  exact Or.inr h

Conclusion
"
A continuación, veremos como probar que una unión es subconjunto de otro conjunto.
"
