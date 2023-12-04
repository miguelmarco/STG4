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
"

/-- Supón que $F$ y $G$ son familias de conjuntos, y $F \subseteq G$.
Entonces $\bigcup F \subseteq \bigcup G$. -/
Statement (F G : Set (Set U)) (h1 : F ⊆ G) : ⋃₀ F ⊆ ⋃₀ G := by
  intro x h2
  rewrite [fam_union_def]
  rewrite [fam_union_def] at h2
  Hint "La hipótesis {h2} afirma que existe un conjunto `S` tal que `S ∈ F ∧ {x} ∈ S`.
  Ayudaría introducir un nombre para ese conjunto. Puedes hacer eso con la táctica `cases'`.
  Si escribes `cases' {h2} with B hB`, Lean introducirá un objeto `B` y una nueva hipótesis
  `hB : B ∈ F ∧ {x} ∈ B`. (Puede parecer extraño usar la táctica `cases'` en esta situación,
  ya que no estamos en una demostración por casos. En cualquier caso, `cases'` es la táctica que
  hace lo que necesitamos.)"
  cases' h2 with B hB
  Hint (hidden := true) "¿Ves por qué `B` es el valor de `S` que hay que usar en el objetivo? Tu
  próximo paso puede ser `apply Exists.intro B` o `use B`."
  apply Exists.intro B
  have h2 : B ∈ G := h1 hB.left
  exact And.intro h2 hB.right
