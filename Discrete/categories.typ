#import "@local/MetaNote:0.0.1" : *
#import "@preview/fletcher:0.5.1" as fletcher: diagram, node, edge

#let Ccat = math.cal($C$)
#let CSet = math.serif("Set")
#let Vect = math.serif("Vect")
#let opp = "op"
#let ev = math.op("ev")
#let Ob = math.op("Ob")
#let Yon = "よ"

#let Fct = math.op("Fct")
#let Hom = math.op("Hom")
#let Nat = math

= Categories

== Yoneda Lemma

From the enlightening view of the Yoneda perspective, we deduce that objects in a category are uniquely determined by their morphisms, up to isomorphism. To work with their morphismic representations, we will work in the so-called _presheaf category_ $Ccat^and := Fct(Ccat^opp, CSet)$.

#definition("Presheaf Category")[
  The presheaf category $C^and$ is the category of contravariant functors from $C$ to $CSet$, i.e. functors $F: C^opp -> CSet$. The morphisms in $C^and$ are natural transformations between these functors.

  Similarly, we can define the _copresheaf category_:

  $
  C^and &:= Fct(Ccat^opp, CSet) \
  C^or &:= Fct(Ccat^opp, CSet^opp) = Fct(Ccat, CSet)^opp
  $
]

Now we can formally define the Yoneda embedding, which maps an object $X$ in $C$ to the contravariant functor that sends an vantage object $Z$ to the set of morphisms $Hom(Z, X)$.

#definition("Yoneda Embedding")[
  The Yoneda embedding $Yon: Ccat -> Ccat^and$ is defined by
  $
  Yon &: Ccat -> Ccat^and \
  & S |-> Hom_Ccat (-, S).
  $
]

Naturally, we have the evaluation functor $ev: Ccat^and times Ccat -> CSet$ that evaluates a presheaf $F$ at an object $X$, leading to the set $F(X)$.

#definition("Evaluation Functor")[
  The evaluation functor $ev^and: Ccat^and times Ccat -> CSet$ is defined by
  $
  ev^and &: Ccat^and times Ccat -> CSet \
  & (F, X) |-> F(X).
  $
]

Now we can state the Yoneda lemma, which asserts that the Yoneda embedding is fully faithful as a consequence.

#theorem("Yoneda")[
  For any object $S in Ob(Ccat)$ and any presheaf $F in Ob(Ccat^and)$, we have a natural bijection from natural transformations $eta$ to elements in $F(S)$, given by

  $
  Phi &: Hom_(Ccat^and) (Yon(S), F) -> F(S) \
  & [eta, Hom_Ccat (-,S) ->^eta F(-)] |-> eta_S (id_S),
  $

  which gives rise to a natural functor isomorphism $Hom_(Ccat^and) (Yon(-), -) tilde.equiv ev^and$. As a result, the Yoneda embedding $Yon$ is fully faithful. 
]

#proof[
  For any morphism $f : T->S$ in $Ccat$, let $u_s := eta_S (id_S) in F(S)$. The following diagram suffices to prove the Yoneda lemma:

  #align(center)[
  #diagram(
    node((0, 0), $Hom_C (S,S)$),
    node((0, 1), $Hom_C (T,S)$),
    node((1, 0), $F(S)$),
    node((1, 1), $F(T)$),
    edge((0, 0), (0, 1), "->", $"pullback" f^*$),
    edge((0, 0), (1, 0), "->", $eta_S$),
    edge((0, 1), (1, 1), "->", $eta_T$),
    edge((1, 0), (1, 1), "->", $F(f)$),

    node((-0.5, 0), $in$),
    node((-1, 0), $id_S$),
    node((-0.5, 1), $in$),
    node((-1, 1), $f$),
    edge((-1, 0), (-1, 1), "|->"),

    node((1.5, 0), $in.rev$),
    node((2, 0), $u_S$),
    node((1.5, 1), $in.rev$),
    node((2, 1), $eta_T (f)$),
    edge((2, 0), (2, 1), "|->"),
  )]

  Explanation: To show $Phi$ is a bijection, it suffices to construct an inverse $Psi$. Assume that $Psi(eta_S (id_S)) = beta$, then if $beta = eta$ holds, we have (as is shown in the diagram)

  $
  Psi(eta_S (id_S))_T (f compose id_S) = F(f)(eta_S (id_S)).
  $

  Hence we wish to define $Psi$ as 

  $
  forall x in F(S), Psi(x)_T (f compose id_S) = F(f)(x).
  $

  Now in turn we should verify $Psi(x) = beta$ is indeed natural, i.e. whether the diagram commutes replacing $eta$ to $beta$. For any $g in Hom_Ccat (Q,P)$:

  #align(center)[
  #diagram(
    node((0, 0), $Hom_C (P,S)$),
    node((0, 1), $Hom_C (Q,S)$),
    node((1, 0), $F(P)$),
    node((1, 1), $F(Q)$),
    edge((0, 0), (0, 1), "->", $"pullback" g^*$),
    edge((0, 0), (1, 0), "->", $beta_P$),
    edge((0, 1), (1, 1), "->", $beta_Q$),
    edge((1, 0), (1, 1), "->", $F(g)$),
  )] 

  For any $h in Hom_Ccat (P,S)$,

  $
  beta_P (h) = Psi(x)_P (h compose id_S) = F(h)(x), F(g)(F(h)(x)) = F(g compose h) (x) \
  beta_Q (g compose h) = F(g compose h) (x).
  $

  The diagram commutes. Then it remains to show $Psi compose Phi = Phi compose Psi = id$.

  (i) $
  Psi(Phi(eta)) = Psi(eta_S (id_S)) = f |-> F(f)(eta_S (id_S)) = f |-> eta_T (f compose id_S)
  $

  which is just $eta$!

  (ii) $
  Phi(Psi(x)) = Psi(x)_S (id_S) = F(id_S) (x) = x.
  $

  Finally, Substituting $F = Yon(T)$ gives bijection $Hom_(Ccat^and) (Yon(S),Yon(T)) <-> Hom_Ccat (S,T) = F(S)$. This shows that $Yon$ is fully faithful by definition.
]

Now that objects are basically the same thing as all the morphisms related to it, we will often omit the Yoneda embedding $Yon$ and see $Ccat$ as a full subcategory of $Ccat^and$. We might want to extend the concept to other presheaf in $Ccat^and$, i.e. whether it stands for a object in $Ccat$. So here comes the definition of _representable functor_, which will later be proved to show the property by its universal property.

#definition("Representable Functor")[
  We call $A: C^opp -> CSet$ a _representable functor_, if there exists $X in Ob(Ccat)$ and isomorphism $
  phi: Yon(X) ->^tilde A,
  $
  and $(X, phi)$ its _representation element_. 
]

In terms of the comma category, the representation element can be embedded into $(Yon slash A)$, corresponding to the functor $Ccat ->^Yon Ccat^and <-^(j_A) bold(1)$. Now we can state and prove the universal property and show why the representation element really lives up to its name, as we did to free vector spaces.

#theorem("Universal Property of Representation Element")[
  If $A$ is a representable functor, then its representation element is unique up to isomorphism.
]

#proof[
  For any $Y in Ob(Ccat), psi : Yon(Y)->A$, the following diagram

  #align(center)[
  #diagram(
    node((0, 0), $Yon(Y)$),
    node((1, 0), $Yon(X)$),
    node((1, 1), $A$),
    edge((0, 0), (1, 1), "->", $psi$),
    edge((0, 0), (1, 0), "->", $Yon(f)$),
    edge((1, 0), (1, 1), "<->", $phi$,),
  )] 

  commutes for some unique $f in Hom(Y,X)$, because $Yon(f) = phi^(-1) compose psi$ and the fully faithfulness of $Yon$. By definiton of $(Yon slash A)$, $(X,phi)$ is its final object, and uniqueness is hence determined.
]

#example[
  Review the free vector space functor $V : CSet -> Vect$, whose universal property gives the isomorphism

  $
  Hom_CSet (X, U(-)) ->^tilde Hom_Vect (V(X),-)
  $

  Hence $V(X)$ and the above mapping represents the functor $Hom_CSet (X,U(-))$.
]