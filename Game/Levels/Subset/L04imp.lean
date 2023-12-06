import Game.Levels.Subset.L03have

variable {U : Type}

World "Subconjunto"
Level 4
Title "Implicaciones"

Introduction
"
Si `P` y `Q` son afirmaciones, entonces `P → Q` significa \"si P, entonces Q\".
Para ingresar el símbolo `→`, escribe `\\imp` (abreviatura de \"implica\").

La manera más directa de demostrar una afirmación de la forma `P → Q` es asumir que
`P` es verdadero y luego demostrar `Q`. Para hacer eso, necesitaremos una nueva táctica: `intro`.
"

DefinitionDoc imp as "→"
"`P → Q` significa \"si `P` entonces `Q`\".  Puedes introducir el símbolo `→` tecleando `\\imp`."

NewDefinition imp

TacticDoc intro
"
Usa `intro` para introducir ya sea una nueva suposición o un nuevo objeto en tu prueba.

Hay dos situaciones en las que puedes usar la táctica `intro`:
- Si estás demostrando una afirmación de la forma `P → Q`, entonces puedes usar
la táctica `intro h` para introducir la suposición `h : P` y establecer `Q` como la meta. Asegúrate
de usar un identificador que no esté en uso.
- Si estás demostrando una afirmación de la forma `∀ x, P x`, donde `P x` es una afirmación sobre
`x`, entonces puedes usar la táctica `intro x` para introducir un nuevo objeto `x` en la prueba.
Asegúrate de usar un nombre de variable que no esté en uso. El objetivo pasará a ser `P x`.

Puedes realizar múltiples introducciones en un solo paso: por ejemplo, `intro x h` tiene el mismo
efecto que realizar `intro x` seguido de `intro h`.
"

NewTactic intro

/-- Sea $x$ be un objeto del the universo $U$, y sean $A$, $B$, y $C$ conjuntos tales que
$A \subseteq B$ y $x \in B \to x \in C$.  Entonces $x \in A → x \in C$.-/
Statement {x : U} {A B C : Set U} (h1 : A ⊆ B) (h2 : x ∈ B → x ∈ C) : x ∈ A → x ∈ C := by
  Hint "Como nuestro objetivo es `x ∈ A → x ∈ C`, el primer paso es asumir `x ∈ A`. Para introducir
  esta hipótesis asignándole el identificador `h3`, teclea `intro h3`."
  intro h3
  Hint "Fíjate en que `{h3} : x ∈ A` aparece ahora en el apartado *Assumptions*, y tu nuevo
  objetivo es `x ∈ C`."
  Hint (hidden := true) "Como vimos en el nivel anterior, puedes aplicar `h1` a `{h3}`
  para justificar que `x ∈ B`, usando la táctica `have`."
  have h4 : x ∈ B := h1 h3
  Hint (strict := true) "Igual que pudiste aplicar `h1` a `{h3}` en el paso anterior,
  ahora puedes aplicar `h2` a `{h4}` para probar el objetivo."
  exact h2 h4

Conclusion
"
En general, si tu objetivo es de la forma `P → Q`, la táctica `intro h` añadirá `h : P` a la lista
de hipótesis, y establecerá `Q` como el objetivo a probar. Si tienes hipótesis
`h1 : P → Q` y `h2 : P`, `h1 h2` es una prueba de `Q`. Este es otro ejemplo de una prueba funcionando
como una función: una prueba de `P → Q` se puede ver como una función que, cuando se aplica a `P`
produce una prueba de `Q`.

Como de costumbre, para más información sobre la táctica `intro`, puedes pulsar en
`intro` en la lista de tácticas de la derecha.
"
