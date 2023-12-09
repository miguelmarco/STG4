import Game.Levels.Subset.L01exact

variable {U : Type}

World "Subconjunto"
Level 2
Title "Una hipótesis sobre subconjuntos"

Introduction
"
Si `A` and `B` son conjuntos, decimos que `A` es un *subconjunto* de `B` si
todo elemento de `A` es también un elemento de `B`. Esto lo denotamos como `A ⊆ B`.
(Para introducir el símbolo `⊆`, teclea `\\sub`, seguido por un espacio.)

Si tienes `h1 : A ⊆ B`, entonces `h1` is una prueba de que, si algo es un elemento de `A`,
también es un elemento de `B`. Así, si tienes también `h2 : x ∈ A`,
puedes aplicar `h1` a `h2` para concluir que `x ∈ B`.  Para aplicar `h1` a `h2`,
símplemente escribe `h1` seguido de `h2`, con un espacio en medio. Así, en esta situación,
`h1 h2` es una prueba de `x ∈ B`.

Intenta completar este nivel. Si necesitas ayuda, pulsa en
\"Show more help!\".
"

DefinitionDoc sub as "⊆"
"`A ⊆ B` significa que `A` es un subconjunto de `B`.  Para introducir el símbolo `⊆`,
teclea `\\sub`."

NewDefinition sub

/-- Supón que $A$ y $B$ son conjuntos, $A \subseteq B$, y $x \in A$.
Entonces $x \in B$. -/
Statement (x : U) (A B : Set U) (h1 : A ⊆ B) (h2 : x ∈ A) : x ∈ B := by
  Hint (hidden := true) "Como `h1 h2` es una prueba de `x ∈ B`, puedes cerrar el objetivo con
  `exact h1 h2`."
  exact h1 h2

Conclusion
"
Este ejemplo ilustra mejor cómo se usa normalmente la táctica `exact`.
A menudo, `exact` va seguido de una expresión que combina hipótesis para demostrar el objetivo.
En niveles posteriores, veremos otras formas en las que las hipótesis se pueden combinar para
demostrar un objetivo.

Observa que en esta prueba, `h1` podría pensarse como una función que se puede
aplicar a una prueba de cualquier afirmación de la forma `x ∈ A` para producir una prueba
de `x ∈ B`. Muchas pruebas en Lean se comportan como funciones.
"
