import Game.Levels.FamUnion.L05unionunion

variable {U : Type}

World "FamUnion"
Level 6
Title "Uniones contenidas en conjuntos"

Introduction
"
Supón que `A` es un conjunto y `F` una familia de conjuntos. En este nivel verás bajo qué condiciones
`⋃₀ F` está contenido en `A`.
"

/-- Supón que $A$ es un conjunto y $F$ es una familia de conjuntos. Entonces $\bigcup F$ está
contenido en $A$ si y solo si todo elemento de $F$ está contenido en $A$. -/
Statement (A : Set U) (F : Set (Set U)) : ⋃₀ F ⊆ A ↔ ∀ B ∈ F, B ⊆ A := by
  apply Iff.intro
  intro h1
  intro B h2
  intro x h3
  Hint (hidden := true) "Date cuenta de que `{h1}` podría aplicarse a una prueba de `{x} ∈ ⋃₀ F`
  para probar el objetivo. Eso significa que `apply {h1}` cambiará el objetivo a `{x} ∈ ⋃₀ F`."
  apply h1
  rewrite [fam_union_def]
  use B
  intro h1
  intro x h2
  rewrite [fam_union_def] at h2
  cases' h2 with B h2
  exact h1 B h2.left h2.right
