import Game.Levels.FamInter.L05subinter

variable {U : Type}

World "FamInter"
Level 6
Title "Intersección de una familia de uniones"

Introduction
"
En este nivel, usarás un nuevo tipo de demostración por casos. Para una afirmación `P`, la
táctica `by_cases h : P` separará la demostración en dos casos. En el primer caso, se añade una
nueva hipótesis `h : P`; y en el segundo, se añade la hipótesis `h : ¬P` en su lugar.
Como `P` debe ser cierta o falsa, estos dos casos cubren todas las posibilidades.
"

TacticDoc by_cases
"
La táctica `by_cases h : P` parte la demostración en dos casos. En el primer caso, se añade la
hipótesis `h : P`; y en el segundo caso, se añade `h : ¬P`.
"

NewTactic by_cases

/-- Supón que $A$ es un conjunto, $F$ y $G$ son familias de conjuntos, y para cada conjunto $S$ en
$F$, $A \cup S \in G$. Entonces $\bigcap G \subseteq A \cup (\bigcap F)$.-/
Statement (A : Set U) (F G : Set (Set U)) (h1 : ∀ S ∈ F, A ∪ S ∈ G) : ⋂₀ G ⊆ A ∪ (⋂₀ F) := by
  intro x h2
  Hint "Reescribir el significado del objetivo puede facilitar entender la prueba."
  rewrite [union_def]
  Hint (strict := true) "Si `{x} ∈ A`, el objetivo es fácil de probar. Esto parece sugerir
  partir la prueba en casos dependiendo de si `{x} ∈ A` o no. Puedes hacer esto con la táctica
  `by_cases hA : {x} ∈ A`."
  by_cases hA : x ∈ A
  Hint "El primer caso es el fácil."
  exact Or.inl hA
  Hint "Para el segundo caso, ¿cual de las posibilidades del objetivo crees que puedes probar?
  Puedes usar `apply Or.inl` o `apply Or.inr` (o las tácticas equivalentes `left` y `right`)
  para especificar cual de las dos opciones quieres demostrar."
  apply Or.inr
  rewrite [fam_inter_def]
  intro S h4
  Hint (strict := true) (hidden := true) "Ahora usa `h1`."
  have h5 : A ∪ S ∈ G := h1 S h4
  Hint (strict := true) (hidden := true) "Aún no has usado `{h2}`. Si no ves cómo usarlo, escribe su
  definición."
  rewrite [fam_inter_def] at h2
  Hint (strict := true) (hidden := true) "Date cuenta de que puedes aplicar `{h2}` a `(A ∪ {S})`."
  have h6 : x ∈ A ∪ S := h2 (A ∪ S) h5
  rewrite [union_def] at h6
  cases' h6 with hA2 hS
  Hint (hidden := true) "Notice that you have contradictory assumptions."
  by_contra h6
  exact hA hA2
  exact hS

Conclusion
"
Has completado el mundo de las intersecciones de familias. Como puedes adivinar, también se pueden
tomar uniones de familias. ¿Puedes pensar cómo definirlas? Continua al mundo de las uniones de
familias para verlo.
"
