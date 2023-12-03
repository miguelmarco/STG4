import Game.Levels.Subset

variable {U : Type}

World "Complementario"
Level 1
Title "Demostración por contradicción"

Introduction
"
Para trabajar con complementos, necesitaremos entender declaraciones negativas, es decir, afirmaciones
que indican que algo *no* es cierto.

Si `P` es una afirmación, entonces `¬P` significa \"no es cierto que P\". Para ingresar el símbolo
`¬`, escribe `\\not`.

Un método común para demostrar una afirmación negativa es la *prueba por contradicción*: para
demostrar una afirmación de la forma `¬P`, puedes asumir que `P` es verdadero
y luego mostrar que esta suposición conduce a una contradicción. La táctica a utilizar para este
tipo de prueba es `by_contra`.
"

TacticDoc by_contra
"
Si tu objetivo es `¬P`, para alguna afirmación `P`, entonces la táctica
`by_contra h` introducirá la nueva suposición `h : P` y establecerá el
objetivo como `False`. Si tu objetivo es una afirmación `P` que no es negativa,
entonces `by_contra h` introducirá la nueva suposición
`¬P`.

Para lograr tu nuevo objetivo, deberás establecer
`h1 : Q` y `h2 : ¬Q`, para alguna afirmación `Q`. Si puedes hacer eso,
entonces `h2 h1` demostrará el objetivo `False`. Observa que `h1 h2` no será
reconocido como una prueba de `False`; la afirmación negativa debe venir primero.
"

NewTactic by_contra

DefinitionDoc not as "¬"
"`¬P` significa \"es falso que P\".  Para introducir el símbolo `¬`,
teclea `\\not`."

NewDefinition not

LemmaTab "Teoría de conjuntos"

/-- Supón que $x \in A$ y $x \notin B$.  Entonces $\neg A \subseteq B$. -/
Statement {A B : Set U} {x : U} (h1 : x ∈ A) (h2 : x ∉ B) : ¬A ⊆ B := by
  Hint "Para el teorema en este nivel, tu objetivo es `¬A ⊆ B`. Para utilizar la prueba por contradicción
  en esta demostración, debes comenzar introduciendo la suposición `h3 : A ⊆ B`. Para hacerlo, escribe
  `by_contra h3`."
  by_contra h3
  Hint (strict := true) "Observa que el objetivo es ahora `False`. Para lograr ese objetivo,
  debes demostrar afirmaciones contradictorias. Puedes hacer esto
  usando `have` para afirmar `h4 : x ∈ B`, lo cual contradirá a `h2 : x ∉ B`."
  Hint (strict := true) (hidden := true) "`{h3} h1` es una prueba de `x ∈ B`."
  have h4 : x ∈ B := h3 h1
  Hint (strict := true) "Puedes pensar en `h2 : x ∉ B` (que es una forma abreviada de `h2 : ¬x ∈ B`)
  como significando \"si `x ∈ B` fuera verdadero, eso conduciría a una contradicción\"--dicho
  de otro modo, `x ∈ B → False`.
  Aplicar esto a tu nueva suposición `{h4} : x ∈ B` dará la contradicción
  que necesitas. En otras palabras, `exact h2 {h4}` cerrará el objetivo."
  exact h2 h4

Conclusion
"
Puedes usar la táctica `by_contra` en cualquier prueba para asumir lo contrario de tu objetivo.
Pero es más útil cuando el objetivo comienza con el símbolo `¬`. Después de usar la táctica `by_contra`,
tu objetivo será `False`.

Para completar una prueba por contradicción, debes demostrar afirmaciones contradictorias.
Si tu objetivo es `False` y tienes las suposiciones `h1 : P` y `h2 : ¬P`, para
alguna afirmación `P`, entonces `exact h2 h1` cerrará el objetivo. Ten en cuenta que `exact h1 h2`
no funcionará; debes listar la afirmación negativa primero para establecer una contradicción.
"
