import Game.Levels.FamUnion.L03unionsubunion

variable {U : Type}

World "FamUnion"
Level 4
Title "Unión de una pareja"

Introduction
"
En este nivel, verás que, al igual que con las intersecciones, las familias de uniones generalizan
lo que vimos en el mundo de las uniones.
"

/-- Sean $A$ y $B$ conjuntos. Entonces $A \cup B = \bigcup \{A, B\}$. -/
Statement (A B : Set U) : A ∪ B = ⋃₀ {A, B}:= by
  ext x
  apply Iff.intro
  intro h1
  rewrite [fam_union_def]
  rewrite [union_def] at h1
  cases' h1 with hA hB
  use A
  apply And.intro
  rewrite [pair_def]
  apply Or.inl
  rfl
  exact hA
  use B
  apply And.intro
  rewrite [pair_def]
  right
  rfl
  exact hB
  intro h1
  rewrite [fam_union_def] at h1
  cases' h1 with S h1
  rewrite [pair_def] at h1
  rewrite [union_def]
  cases' h1.left with hA hB
  rewrite [← hA]
  exact Or.inl h1.right
  rewrite [← hB]
  exact Or.inr h1.right
