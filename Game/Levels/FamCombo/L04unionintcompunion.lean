import Game.Levels.FamCombo.L03threefam

variable {U : Type}

World "FamCombo"
Level 4
Title "Una unión intersecada con el complementario de otra unión"

Introduction
"
¿Que ocurre si intersecas `⋃₀ F` con `(⋃₀ G)ᶜ`, siendo `F` y `G` familias de conjuntos?
"

/-- Supón que $F$ y $G$ son familias de conjuntos. Entonces $(\bigcup F) \cap (\bigcup G)^c \subseteq
\bigcup (F \cap G^c)$.-/
Statement (F G : Set (Set U)) : (⋃₀ F) ∩ (⋃₀ G)ᶜ ⊆ ⋃₀ (F ∩ Gᶜ) := by
  intro x h1
  rewrite [inter_def] at h1
  have h1l := h1.left
  rewrite [fam_union_def] at h1l
  obtain ⟨S, hS⟩ := h1l
  rewrite [fam_union_def]
  use S
  apply And.intro
  rewrite [inter_def]
  apply And.intro
  exact hS.left
  rewrite [comp_def]
  by_contra h2
  have h1r := h1.right
  rewrite [comp_def] at h1r
  apply h1r
  rewrite [fam_union_def]
  use S
  exact And.intro h2 hS.right
  exact hS.right
