import Game.Levels.FamInter.L01intersub

variable {U : Type}

World "FamInter"
Level 2
Title "La intersección de una familia mayor es más pequeña."

Introduction
"
En este nivel, tenemos dos familias de conjuntos, `F` y `G`, con `F ⊆ G`. Esto significa que
`⋂₀ G` es la intersección de una familia de conjuntos que incluye todos los conjuntos en `F`,
y quizás más conjuntos. Vas a demostrar que la intersección de esta colección más grande de
conjuntos conduce a un resultado más pequeño; más precisamente, vas a demostrar que
`⋂₀ G ⊆ ⋂₀ F`.

Por supuesto, a estas alturas sabes cómo comenzar una demostración de que un conjunto es un
subconjunto de otro.
"

/-- Supón que $F$ y $G$ son familias de conjuntos, y $F \subseteq G$.
Entonces $\bigcap G \subseteq \bigcap F$. -/
Statement (F G : Set (Set U)) (h1 : F ⊆ G) : ⋂₀ G ⊆ ⋂₀ F := by
  intro x h2
  Hint (hidden := true) "Como de costumbre, si no sabes cómo empezar, reescribir las definiciones
  puede ser útil."
  rewrite [fam_inter_def]; rewrite [fam_inter_def] at h2
  Hint "Ahora tu objetivo empieza con `∀ S`.  Para probarlo, tendrás que introducir un conjunto
  `S`, usando la táctica `intro S`.  Recuerda que el conjunto `S` es
  *arbitrario*--es decir, `S` podría ser cualquier conjunto--así que lo que probemos para `S` será
  cierto para *todos* los conjuntos `S`."
  intro S
  Hint (hidden := true) "Ahora to objetivo es una implicación; eso significa que `intro` vuelve a
  ser la táctica apropiada para introducir `{S} ∈ F` como una nueva hipótesis."
  intro h3
  Hint (hidden := true) "Parece que `{h2}` podría llevarte al objetivo, si supieras que
  `{S} ∈ G`. ¿Puedes probarlo?"
  have h4 : S ∈ G := h1 h3
  Hint "Ahora puedes combinar {h2} y {h4} para llegar al objetivo en un paso."
  Hint (hidden := true) "`{h2} {S} {h4}` es una prueba del objetivo."
  exact h2 S h4

Conclusion
"
Fíjate que, igual que vimos en otras pruebas de que un conjunto está contenido en otro, los dos
`intro` se pueden combinar en un solo paso. Pulsa en `intro` en la lista de tácticas a la derecha
para más detalles.
"
