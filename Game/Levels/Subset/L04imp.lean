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
- Si estás demostrando una afirmación de la forma `∀ x, ...`, entonces puedes usar
la táctica `intro x` para introducir un nuevo objeto `x` en la prueba. Asegúrate de
usar un nombre de variable que no esté en uso.

Puedes realizar múltiples introducciones en un solo paso: por ejemplo, `intro x h` tiene el mismo
efecto que realizar `intro x` seguido de `intro h`.
"

NewTactic intro

/-- Supón que $A \subseteq B$ y $x$ es un objeto cualquiera en el universo $U$.
Entonces $x \in A \to x \in B$. -/
Statement {A B : Set U} (h1 : A ⊆ B) (x : U) : x ∈ A → x ∈ B := by
  Hint "Dado que nuestro objetivo en este nivel es la afirmación `x ∈ A → x ∈ B`,
  nuestro primer paso para esta prueba es asumir `x ∈ A`. Para introducir esa
  suposición, asignándole el identificador `h2`, escribe `intro h2`."
  intro h2
  Hint "Fíjate en que `{h2} : x ∈ A` aparece ahora en el apartado *Assumptions*,
  y tu nuevo objetivo es `x ∈ B`."
  Hint (hidden := true) "h1 {h2} es ahoa una prueba del objetivo."
  exact h1 h2

Conclusion
"
Como de costumbre, para más información sobre la táctica `intro`, puedes pulsar en
`intro` en la lista de tácticas de la derecha.
"
