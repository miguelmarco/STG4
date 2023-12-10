import Game.Levels.FamCombo.L04unionintcompunion

variable {U : Type}

World "FamCombo"
Level 5
Title "Un subconjunto de una unión intersecada con el complemento de otra"

Introduction
"
¿Qué ocurre si tomamos el contenido inverso en el nivel anterior?
"

/-- Supón que $F$ y $G$ son familias de conjuntos y $\bigcup (F \cap G^c) \subseteq (\bigcup F)
\cap (\bigcup G)^c$.  Entonces $(\bigcup F) \cap (\bigcup G) \subseteq \bigcup (F \cap G)$.-/
Statement (F G : Set (Set U)) (h1 : ⋃₀ (F ∩ Gᶜ) ⊆ (⋃₀ F) ∩ (⋃₀ G)ᶜ) :
    (⋃₀ F) ∩ (⋃₀ G) ⊆ ⋃₀ (F ∩ G) := by
  intro x h2
  have h2l := h2.left
  have h2r := h2.right
  rewrite [fam_union_def] at h2l
  obtain ⟨S, hS⟩ := h2l
  use S
  apply And.intro
  apply And.intro
  exact hS.left
  by_contra h3
  have h4 : x ∈ ⋃₀ (F ∩ Gᶜ)
  use S
  apply And.intro
  apply And.intro
  exact hS.left
  rewrite [comp_def]
  exact h3
  exact hS.right
  have h5 := h1 h4
  have h5r := h5.right
  rewrite [comp_def] at h5r
  exact h5r h2r
  exact hS.right
