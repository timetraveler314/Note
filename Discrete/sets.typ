#import "@local/MetaNote:0.0.1" : *

= Set Theory

== Ordinals

#lemma("Properties of Ordinals")[
  (ii) For any ordinals $alpha, beta$, if $alpha subset.neq beta$, then $alpha in beta$.
]

#proof[
  (ii) Denote $gamma$ the minimal element of $(beta backslash alpha, in)$. We assert $alpha = S := {x in beta | x < gamma}$, and $S$ is nothing but $gamma$ by the axiom of foundation ($gamma in S$ breaks the definition; $S = {x in beta | x < gamma} in gamma$ implies $S in S$, a contradiction).

  $S subset alpha$: for any $x in S$, $x < gamma => x in alpha$ by minimal choice of $gamma$.
  
  $alpha subset S$: for any $y in alpha subset beta$, $y != gamma$ because $gamma in.not alpha$; besides, by transitivity, $y subset alpha$ contradicts with $gamma in y$. Therefore, $y < gamma$.
]

#question[
  Is it the case that $
  abs(S union T) = abs(W) => abs(S) = abs(W) or abs(T) = abs(W) ?
  $
]

#solution[
  It is clear that the statement does not hold for finite cases. However, consider $abs(W) >= abs(NN)$.
]

#definition("Dedekind Finite")[
  A set $S$ is Dedekind finite if $
  forall T subset.neq S, abs(T) < abs(S).
  $
  // there is no injective function $f : NN -> S$.
]

