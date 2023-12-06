import Game.Levels.FamCombo.L01compunion

variable {U : Type}

World "FamCombo"
Level 2
Title "Complementario de la intersección de una familia"

Introduction
"
Ya habrás sospechado que hay una versión para interseciones de familias del teorema visto en el
nivel anterior.
"

/-- Dada una familia de conjuntos $F$, $(\bigcap F)^c = \bigcup \{A \mid A^c \in F\}$. -/
Statement (F : Set (Set U)) : (⋂₀ F)ᶜ = ⋃₀ {A | Aᶜ ∈ F} := by
  ext x
  apply Iff.intro
  intro h1
  rewrite [comp_def] at h1
  Branch
    rewrite [fam_union_def]
    by_contra h2
    Hint (strict := true) "Como `{h1}` es una negación, una buena forma de llegar a una
    contradicción sería ver lo contrario de `{h1}`. Como vimos en el nivel anterior, `apply {h1}`
    cambiará el objetivo a `x ∈ ⋂₀ F`."
    apply h1
    rewrite [fam_inter_def]
    intro S h3
    by_contra h4
    Hint "¿Qué afirmación te gustaría negar para completar la prueba? De nuevo, puedes usar `apply`
    para cambiar el objetivo."
  by_contra h2
  Hint (strict := true) "Como `{h1}` es una negación, una buena forma de llegar a una
  contradicción sería ver lo contrario de `{h1}`. Como vimos en el nivel anterior, `apply {h1}`
  cambiará el objetivo a `x ∈ ⋂₀ F`."
  apply h1
  rewrite [fam_inter_def]
  intro S h3
  by_contra h4
  Hint "¿Qué afirmación te gustaría negar para completar la prueba? De nuevo, puedes usar `apply`
  para cambiar el objetivo."
  apply h2
  use Sᶜ
  apply And.intro
  rewrite [set_builder_def]
  rewrite [comp_comp]
  exact h3
  exact h4
  intro h1
  rewrite [comp_def]
  by_contra h2
  cases' h1 with S hS
  have hSl := hS.left
  rewrite [set_builder_def] at hSl
  rewrite [fam_inter_def] at h2
  have h3 := h2 Sᶜ hSl
  exact h3 hS.right
