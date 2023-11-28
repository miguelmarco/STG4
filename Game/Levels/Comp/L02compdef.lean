import Game.Levels.Comp.L01contra

variable {U : Type}

World "Complementario"
Level 2
Title "Definición de complementario"

Introduction
"
Si tienes `A : Set U`, entonces `Aᶜ` se define como el conjunto de todos los objetos en el universo
`U` que no son elementos de `A`. Esto significa que si también tienes `x : U`, entonces las
afirmaciones `x ∈ Aᶜ` y `x ∉ A` son equivalentes. Expresamos esto diciendo que la afirmación
`x ∈ Aᶜ ↔ x ∉ A` es verdadera. (El símbolo `↔` significa \"si y solo si\", y puedes introducirlo
escribiendo `\\iff`. Puedes ingresar el superíndice `c` en la notación para el complemento de un
conjunto escribiendo `\\compl` o `\\^c`.)

En este nivel, vamos a demostrar que la afirmación `x ∈ Aᶜ ↔ x ∉ A` es verdadera, y para hacerlo
usaremos una nueva táctica: `rfl`. La táctica `rfl` puede demostrar cualquier afirmación de la forma
`P ↔ Q` si `P` y `Q` son afirmaciones que son equivalentes por virtud de las definiciones de los
símbolos que aparecen en ellas. (Decimos en este caso que `P` y `Q` son *equivalentes por definición*.)
La táctica `rfl` también puede demostrar afirmaciones de la forma `X = Y`,
si `X` e `Y` son iguales por definición.
"

TacticDoc rfl
"
Si tu objetivo es una afirmación de la forma `P ↔ Q`, y `P` y `Q` son equivalentes por definición
(es decir, equivalentes por virtud de las definiciones de los símbolos que aparecen en ellas),
entonces la táctica `rfl` cerrará el objetivo. También cerrará un objetivo de la forma
`X = Y`, si `X` e `Y` son iguales por definición.
"

NewTactic rfl

DefinitionDoc comp as "ᶜ"
"Si `A` es un conjunto de objetos del universo `U`, entonces `Aᶜ` es el complementarioo de `A`;
es decir, `Aᶜ` es el conjunto de objetos de `U` que no son elementos de `A`. Puedes ingresar el
símbolo `ᶜ` escribiendo `\\compl` o `\\^c`."

DefinitionDoc iff as "↔"
"`P ↔ Q` significa \"P si y solo si Q\".  Puedes introducir el símbolo `↔` tecleando `\\iff`."

NewDefinition comp iff

LemmaTab "Teoría de conjuntos"

LemmaDoc comp_def as "comp_def" in "Teoría de conjuntos"
"Si tienes `x : U` y `A : Set U`, entonces `comp_def x A` es una prueba de la afirmación
`x ∈ Aᶜ ↔ x ∉ A`."

/-- Sea $x$ un objeto en el universo $U$, y sea $A$ un conjunto cuyos elementos son de $U$.
Entonces $x \in A^c \leftrightarrow x \notin A$. -/
Statement comp_def (x : U) (A : Set U) : x ∈ Aᶜ ↔ x ∉ A := by
  Hint "La demostración en este nivel es muy fácil.
  Como `x ∈ Aᶜ` y `x ∉ A` son iguales por definición, `rfl` cerrará el objetivo."
  rfl

NewLemma comp_def

Conclusion
"
Hemos llamado al teorema demostrado en este nivel `comp_def`, porque expresa la definición
del complementario. En el siguiente nivel veremos cómo usarlo para demostrar teoremas sobre
complementarios.
"
