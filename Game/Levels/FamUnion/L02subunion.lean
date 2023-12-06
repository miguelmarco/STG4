import Game.Levels.FamUnion.L01proveexists

variable {U : Type}

World "FamUnion"
Level 2
Title "Subconjuntos de la unión de una familia"

Introduction
"
En lenguaje matemático, la unión de una familia $F$ se denota usualmente como $\\bigcup F$.
En Lean, la unión de una familia `F` se denota `⋃₀ F`.  (Puedes introducir el símbolo
`⋃₀` tecleando `\\U0`.)

Supón que tenemos `F : Set (Set U)` y `x : U`. Entonces `x ∈ ⋃₀ F` signific que hay al menos un
conjunto `S` tal que `S ∈ F` y `x ∈ S`. Para escribir esta afirmación en Lean, escribimos
`∃ S, S ∈ F ∧ x ∈ S`. Se puede abreviar como `∃ S ∈ F, x ∈ S`.

Como otras operaciones con conjuntos, tenemos un teorema que expresa esta definición. Si tenemos
`F : Set (Set U)` y `x : U`, `fam_union_def x F` es una prueba de
`x ∈ ⋃₀ F ↔ ∃ S ∈ F, x ∈ S`.

En este nivel trabajaremos con estas ideas.
"

DefinitionDoc famunion as "⋃₀"
"`⋃₀ F` es la unión de la familia de conjuntos `F`. Para introducir el símbolo `⋃₀`, teclea `\\U0`."

NewDefinition famunion

lemma fam_union_def (x : U) (F : Set (Set U)) : x ∈ ⋃₀ F ↔ ∃ S ∈ F, x ∈ S := by rfl

LemmaDoc fam_union_def as "fam_union_def" in "⋂₀⋃₀"
"Si `F : Set (Set U)` y `x : U`, entonces `fam_union_def x F` es una prueba de
`x ∈ ⋃₀ F ↔ ∃ S ∈ F, x ∈ S`."

NewLemma fam_union_def

LemmaTab "⋂₀⋃₀"

TacticDoc use
"
Si tu objetivo es `∃ x, P x`, donde `P x` representa alguna afirmación sobre `x`, y `a` es un posible
valor para `x`, la táctica `use a` establecerá  `P a` como el nuevo objetivo a probar.
Si puede ver que este nuevo objetivo se sigue directamente de tus hipótesis, cerrará el objetivo.
"

NewTactic use

LemmaTab "⋂₀⋃₀"

/-- Supón que $F$ es una familia de conjuntos y $A \in F$. Entonces $A \subseteq \bigcup F$. -/
Statement (A : Set U) (F : Set (Set U)) (h1 : A ∈ F) : A ⊆ ⋃₀ F := by
  intro x h2
  rewrite [fam_union_def]
  Hint "Recuerda que el objetivo `∃ S ∈ F, {x} ∈ S` es una abreviatura de
  `∃ S, S ∈ F ∧ {x} ∈ S`. Como vimos en el nivel anterior, podemos probar esto encontrando un
  testigo--es decir, un valor
  concreto para `S` para el que la afirmación `S ∈ F ∧ {x} ∈ S` se cumpla. Si nos fijamos en
  `h1` y `{h2}`, parece que `S = A` podría servir. Esto nos sugiere una forma de seguir:
  `Exists.intro A hA` probaría el objetivo, si `hA` fuera una demostración de `A ∈ F ∧ {x} ∈ A`.
  Dicho de otro modo, si aplicamos `Exists.intro A` a una prueba de `A ∈ F ∧ {x} ∈ A`, tendremos
  una prueba del objetivo. Así que si usas la táctica `apply Exists.intro A`, Lean establecerá
  `A ∈ F ∧ {x} ∈ A` como tu nuevo objetivo."
  apply Exists.intro A
  exact And.intro h1 h2

Conclusion
"
Hay otra táctica que se podría haber usado. En lugar de `apply Exists.intro A`, podrías haber
escrito `use A`. La táctica `use` puede ser bastante potente. No sólo usa `A` como valor para
`S` en la afirmación de existencia; ¡además intenta ver si puede demostrar el resultado directamente
a partir de las hipótesis existentes!
"
