import Game.Levels.Union.L02subunion

variable {U : Type}

World "Uniones"
Level 3
Title "Demostración por casos"

Introduction
"
En esta prueba, necesitaremos una nueva técnica: la demostración por casos. Para ello necesitaremos
una nueva táctica en Lean: `cases'`.
"

TacticDoc cases'
"Si tienes una hipótesos `h : P ∨ Q`, entonces la táctica `cases' h with h1 h2` descompondrá
tu prueba en casos. En el caso 1, tendrás la nueva hipótesis `h1 : P`, y en el caso 2
tendrás `h2 : Q`. En ambos casos, debes demostrar el objetivo original.
"

NewTactic cases'

LemmaTab "Teoría de conjuntos"

/-- Supón que $A \subseteq C$ y $B \subseteq C$.  Entonces $A \cup B \subseteq C$. -/
Statement (A B C : Set U) (h1 : A ⊆ C) (h2 : B ⊆ C) : A ∪ B ⊆ C := by
  Hint "Como de costumbre, para demostrar un contenido tienes que introducir un objeto `x` y una
  hipótesis `h3`."
  intro x h3
  Hint "Para entender la lógica de esta demostración, puede ser útil reescribir la definición de
  unión en {h3}."
  rewrite [union_def] at h3
  Hint "Ahora la hipótesis {h3} es una afirmación de tipo \"o\". La forma más fácil de usar una
  afirmación así es partirla en casos. Para ello, usa la táctica
  `cases' {h3} with {h3}A {h3}B`."
  cases' h3 with h3A h3B
  Hint "Ahora tienes *dos* objetivos. Para el primero, la hipótesis `{x} ∈ A ∨ {x} ∈ B` ha sido
  sustituida por `{x} ∈ A`, y para el segundo, por `{x} ∈ B`. En ambos casos
  tienes que probar `{x} ∈ C`. Los dos identificadores que has escrito despues de `with` en la
  táctica `cases'` se usan como identificadores de las nuevas hipótesis en los dos casos."
  exact h1 h3A
  exact h2 h3B

Conclusion
"
Notar que also también tiene una táctica `cases`, pero su sintaxis en un poco más complicada.
Por eso hemos optado por usar la táctica `cases'`.
"
