import Game.Levels.FamInter.L04interunion

variable {U : Type}

World "FamInter"
Level 5
Title "Subconjntos de una intersección"

Introduction
"
Si `A` es un conjunto y `F` es una familia de conjuntos, ¿bajo qué circunstancias se cumple que
`A ⊆ ⋂₀ F`?  Veamos la respuesta a esta pregunta.
"

/-- Supón que $A$ es un conjunto y $F$ una familia de conjuntos. Entonces $A$ es un subconjunto de
$\bigcap F$ si y solo si $A$ está contenido en cada elemento de $F$.-/
Statement (A : Set U) (F : Set (Set U)) : A ⊆ ⋂₀ F ↔ ∀ B ∈ F, A ⊆ B := by
  apply Iff.intro
  intro h1
  intro B h2
  intro x h3
  have h4 : x ∈ ⋂₀ F := h1 h3
  rewrite [fam_inter_def] at h4
  exact h4 B h2
  intro h1
  intro x h2
  rewrite [fam_inter_def]
  intro S h3
  have h4 : A ⊆ S := h1 S h3
  exact h4 h2
