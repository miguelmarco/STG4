import Game.Levels.FamUnion.L02subunion

variable {U : Type}

World "FamUnion"
Level 3
Title "La unión de una familia mayor es mayor"

Introduction
"
En este nivel tenemos dos familias de conjuntos, `F` y `G`, con `F ⊆ G`. En el mundo de la
intersección de familias, probaste que en esta situación, `⋂₀ G ⊆ ⋂₀ F`. En este nivel veremos que
con uniones de familias, se tiene la inclusión en sentido contrario: `⋃₀ F ⊆ ⋃₀ G`.

Necesitaremos una nueva táctica para esta prueba. Una hipótesis de la forma `h : ∃ x, P x` nos dice
que existe un objeto con una cierta propiedad. Si tenemos una hipótesis así, puede ser útil
introducir un nombre para ese objeto. Puedes hacerlo con la táctica `obtain`. Si escribes
`obtain ⟨w, hw⟩ := h`, Lean introducirá un nuevo objeto `w` y una nueva hipótesis
`hw : P w`. Así, el objeto `w` es un testigo de la afirmación de existencia `h`. Fíjate en que en la
táctica `obtain`, `w` y `hw` deben ir entre paréntesis angulados: `⟨ ⟩`. Puedes introducir estos
símbolos tecleando `\\<` y `\\>` (o `\\langle` y `\\rangle`).
"

TacticDoc obtain
"Si tienes una hipótesis `h : ∃ x, P x`, la táctica `obtain ⟨w, hw⟩ := h` introducirá un nuevo objeto
`w` y una hipótesis `hw : P w`. Para introducir los paréntesis angulados `⟨ ⟩`, teclea `\\<` y `\\>`
(o `\\langle` t `\\rangle`)."

NewTactic obtain

/-- Supón que $F$ y $G$ son familias de conjuntos, y $F \subseteq G$.
Entonces $\bigcup F \subseteq \bigcup G$. -/
Statement (F G : Set (Set U)) (h1 : F ⊆ G) : ⋃₀ F ⊆ ⋃₀ G := by
  intro x h2
  rewrite [fam_union_def]
  rewrite [fam_union_def] at h2
  Hint "La hipótesis {h2} afirma que existe un conjunto `S` tal que `S ∈ F ∧ {x} ∈ S`.
  Así que `obtain ⟨B, hB⟩ := {h2}` introducirá un nuevo objeto `B` y una hipótesis
  `hB : B ∈ F ∧ {x} ∈ B. Una vez hemos introducido el testigo `B` la hipótesis `{h2}`
  resulta redundante, así que se elimina."
  obtain ⟨B, hB⟩ := h2
  Hint (hidden := true) "¿Ves por qué `B` es el testigo que hay que usar para `S` en el objetivo? Tu
  próximo paso puede ser `apply Exists.intro B` o `use B`."
  apply Exists.intro B
  have h2 : B ∈ G := h1 hB.left
  exact And.intro h2 hB.right
