#import "@local/MetaNote:0.0.1" : *

= Logic 

#let Prop = math.bold("PROP")
#let ts = math.tack.r
#let tss = math.tack.r.double

== Propositional Logic 

To describe a proposition, we introduce the following syntax defining the set of propositions $prop$:

#definition($"Syntax of" Prop$)[
  Atoms: $A := {p, q, r, ...}$;

  Connectives: $C := {not, and, or, ->, <->, bot}$;

  Propositions: $Prop := A | C(Prop)$.
]

The set of propositions $Prop$ is the smallest set satisfying the above syntax, where "smallest" can be understood as the least fixed point of the grammar, or the intersection of all sets satisfying the syntax.

=== Semantics of Prop

The approach of semantics is to give a meaning to each proposition in $Prop$, which we wish to be true or false. This is called a _truth assignment_, or a _model_.

=== Syntax of Prop

In a pure semantics approach, we forget about the concrete meaning of propositions, only focusing on how the syntax, or strings, are manipulated. We first introduce the big-step natural deduction system for propositional logic.

#definition("Natural Deduction")[
  We define the notation $ts$ as 
]

The other is the small-step system _System K_, which is a sequent calculus.

#definition("System K")[
  System K features $=>$ as the meta
]