import Game.Levels.Comp

variable {U : Type}

World "Intersecciones"
Level 1
Title "Y"

Introduction
"
Para trabajar con intersecciones, hay que entender la palabra \"y\".

Si `P` y `Q` son afirmaciones, entonces `P ∧ Q` significa \"P y Q\".  Para introducir el
símbolo `∧`, teclea `\\and`. Para que la afirmación `P ∧ Q` sea cierta, `P` y `Q` deben
serlo. Si tenemos `h : P ∧ Q`--es decir, `h` es una prueba de la afirmación
`P ∧ Q`--entonces, en Lean, `h.left` es una prueba de `P` y `h.right` es
una prueba de `Q`. Esto es todo lo que necesitas para completar este nivel.
"

DefinitionDoc and as "∧"
"`P ∧ Q` significa \"P y Q\".  Para introducir el símbolo `∧`, teclea `\\and`."

NewDefinition and

LemmaTab "Teoría de conjuntos"

/-- Supón que $x \in A$ y $x \in B$.  Entonces $x \in A$. -/
Statement (x : U) (A B : Set U) (h : x ∈ A ∧ x ∈ B) : x ∈ A := by
  exact h.left

Conclusion
"
Ahora podemos demostrar propiedades de intersecciones.
"
