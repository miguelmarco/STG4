import Game.Levels.FamUnion

variable {U : Type}

World "FamCombo"
Level 1
Title "Complementario de una unión de familias"

Introduction
"
En este nivel probarás una generalización del teorema `comp_union` que viste en el mundo combinado.
Ese teorema era sobre el complementario de la unión de dos conjuntos; el teorema en este nivel trata
sobre el complementario de la unión de una familia de conjuntos.
"

/-- Dada una familia de conjuntos $F$, $(\bigcup F)^c = \bigcap \{A \mid A^c \in F\}$. -/
Statement (F : Set (Set U)) : (⋃₀ F)ᶜ = ⋂₀ {A | Aᶜ ∈ F} := by
  ext x
  apply Iff.intro
  intro h1
  rewrite [fam_inter_def]
  intro S h2
  rewrite [comp_def] at h1
  rewrite [set_builder_def] at h2
  by_contra h3
  Hint "Aplicando `{h1}` a una prueba de `{x} ∈ ⋃₀ F` probaría el objetivo `False`. Así que la
  táctica `apply {h1}` cambiará el objetivo a `{x} ∈ ⋃₀ F`. Esta técnica puede ser útil siempre que
  estés haciendo una demostración por reducción al absurdo."
  apply h1
  use Sᶜ
  apply And.intro h2
  rewrite [comp_def]
  exact h3
  intro h1
  rewrite [comp_def]
  by_contra h2
  rewrite [fam_union_def] at h2
  cases' h2 with S hS
  rewrite [fam_inter_def] at h1
  Hint (strict := true) "¿A qué conjunto puedes aplicar {h1}?"
  have h3 : Sᶜ ∈ {A | Aᶜ ∈ F}
  rewrite [set_builder_def]
  rewrite [comp_comp]
  exact hS.left
  have h4 := h1 Sᶜ h3
  rewrite [comp_def] at h4
  exact h4 hS.right
