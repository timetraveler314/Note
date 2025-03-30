#import "@local/MetaNote:0.0.1" : *
#import "@preview/physica:0.9.0": *

#let detm = math.mat.with(delim: "|")

#show: doc => MetaNote(
  title: [
    Probability Theory and Statistics in Information Science
  ],
  authors: (
    (
      name: "timetraveler314",
      affiliation: "University of Genshin",
      email: "timetraveler314@outlook.com",
    ),
  ),
  doc,
)

= Basics

== Axiomization of Probability

=== Definitions

#definition("Event Field")[
  For a sample space $S$, an event field $cal(F)$ is a collection of subsets of $S$ that satisfies the following properties:

  + $S in cal(F)$,
  + If $A in cal(F)$, then $macron(A) in cal(F)$,
  + If $A_i in cal(F)$, then $union.big_(i=1)^(oo) A_i in cal(F)$.

  The set $cal(F)$ satisfying these properties is called a $sigma$-algebra. When the third property holds only for a finite number of sets, the set is called an boolean algebra.
]

Simply put, $sigma$-algebra is a collection of subsets of $S$ that is closed under countable union and complementation.

#definition("Measure")[
  For a $sigma$-algebra $cal(F)$, the function $P: cal(F) -> RR$ is called a measure if it satisfies the following properties:

  + Non-negativity: $P(A) >= 0$ for all $A in cal(F)$,
  + Countable additivity: $P(union.big_(i=1)^(oo) A_i) = sum_(i=1)^(oo) P(A_i)$ for all $A_i in cal(F)$ such that $A_i sect A_j = emptyset$ for $i != j$.
]

Now we can formally define the probability measure, which is a measure that satisfies the additional property of assigning the value of 1 to the entire sample space.

- Normalization: $P(S) = 1$.

#definition("Probability Space")[
  A probability space is a triple $(S, cal(F), P)$, where $S$ is a sample space, $cal(F)$ is a $sigma$-algebra on $S$, and $P$ is a probability measure on $cal(F)$.
]

=== Properties

#theorem("Properties of Probability Measure")[
  Let $(S, cal(F), P)$ be a probability space. Then the probability measure $P$ satisfies the following properties:

  - Subtractivity: $P(A-B) = P(A) - P(A B)$,
  - ...
  - General Inclusion-Exclusion Principle: $ P(union.big_(i=1)^(n) A_i) = sum_(i=1)^(n) P(A_i) - sum_(i < j) P(A_i A_j) + sum_(i < j < k) P(A_i A_j A_k) - ... + (-1)^(n-1) P(A_1 A_2 ... A_n). $
]

#note("Countable Additivity vs. Finite Additivity")[
  There is a subtle difference between countable additivity and finite additivity, because the limit of sum might not be interchangeable with the probability measure $P$. Often this requires $P$ to be a continuous measure.

  Counterexample: $S = [0,+oo), P(A) = lim_(k -> oo) 1/k lambda(A sect (0,k))$.
  Consider $A_i = [i-1,i)$. $union.big^oo_i A_i = S, P(S) = 1$, but $sum_(i=1)^(oo) P(A_i) = 0$.
]

== Conditional Probability

#definition("Conditional Probability")[
  The conditional probability of an event $A$ given an event $B$ (s.t. $P(B) > 0$) is defined as:

  $ P(A|B) = P(A B) / P(B) $

  where $P(B) > 0$.
]

It's easy to check that conditional probability satisfies the properties of a probability measure.

#theorem("Multiplication Rule")[
  For any two events $A$ and $B$, the probability of their intersection can be expressed as:

  $ P(A B) = P(A|B) P(B) = P(B|A) P(A) $

  Generally, $P(A_1...A_n) = P(A_1) P(A_2|A_1) P(A_3|A_1 A_2) ... P(A_n|A_1...A_(n-1)) $.
]

== Bayes' Theorem

#theorem("Theorem of Total Probability")[
  Let $B_1, B_2, ..., B_n$ be a partition of the sample space $S$. Then for any event $A$:

  $ P(A) = sum_(i=1)^n P(A|B_i) P(B_i) $
]

#proof[
  $
    A = A S = A B_1 union A B_2 union ... union A B_n, \
    "whereas" A B_i sect A B_j = emptyset "for" i != j. \
  $
]

#theorem("Total Probability Theorem for Conditional Probability")[
  Let $B_1, B_2, ..., B_n$ be a partition of the sample space $S$. Then for any event $A$ and $C$ ($P(C) != 0$):

  $ P(A | C) = sum_(i=1)^n P(A | B_i C) P(B_i | C) $
]

#note[
  Actually, the theorems still hold on countable partitions because of the countable additivity of probability measure.
]

#theorem("Bayes' Theorem")[
  Events $A_i$ s.t. $P(A_i) > 0$ and $A_i sect A_j = emptyset$ for $i != j$. Give $P(B) != 0$, then

  $
    P(A_i | B) = (P(A_i) P(B | A_i)) / P(B) = (P(A_i) P(B | A_i)) / (sum_(j=1)^n P(A_j) P(B | A_j))
  $
]

#note("Prior Probability")[
  The *prior probability* $P(A_i)$ is the probability of event $A_i$ before any evidence is taken into account. In Bayes' theorem, it is updated to the *posterior probability* $P(A_i | B)$ after the evidence $B$ is observed.
]

= Random Variables and Distributions

== Continuous Random Variables

#definition("Cumuative Distribution Function (CDF)")[
  The cumulative distribution function (CDF) of a random variable $X$ is defined as:

  $ F_X (x) = P(X <= x) $

  for all $x in RR$.
]

#theorem("Properties of CDF")[
  The CDF $F_X (x)$ satisfies the following properties:

  - Non-decreasing: $F_X (x_1) <= F_X (x_2)$ for $x_1 <= x_2$,
  - Right-continuous: $lim_(x -> x_0^+) F_X (x) = F_X (x_0)$ for all $x_0 in RR$.
]

#proof[
  
  _Right-continuity_: by definition of limits and Kolmogorov's axioms.

  - For any decreasing sequence $h_n -> 0^+$, the events ${X <= x + h_n}$ is a decreasing sequence.
  - By the continuity of probability measure, $
  lim_(n -> oo) P({X <= x + h_n})
  = P(sect.big_(n=1)^oo {X <= x + h_n}).
  $
  - As $h_n->0^+$, $sect.big_(n=1)^oo {X <= x + h_n} = {X <= x}$.
  - Therefore, right-continuity holds.

  #note[
    The left-continuity is not guaranteed, e.g. when $P(X = k) != 0$, the jump at $x = k$ is not continuous.
  ]
]

= Multivariate Random Variables and Distributions

== Discrete Case

== Continuous Case

=== Marginal and Conditional Distributions

#definition("Marginal Distribution")[
  Let the joint distribution of random variables $X$ and $Y$ be $F_(X,Y) (x,y)$. The marginal distribution of $X$ is obtained by summing over all possible values of $Y$:

  $
    F_x (x) = P(X <= x) = F(x, oo).
  $
]

#definition("Conditional Distribution")[
  The conditional distribution of $X$ given $Y = y$ is defined as:

  $
    F_(X|Y) (x|y) = lim_(epsilon -> 0^+) P(X <= x | y < Y <= y + epsilon),
  $

  where $forall epsilon > 0$, $P(y < Y <= y+epsilon) > 0$.
]

#note("Relation to Conditional Probability Density")[
  $
    F_(X|Y) (x|y) &= lim_(epsilon -> 0^+) P(X <= x, y < Y <= y + epsilon) / P(y < Y <= y + epsilon) \
    &= lim_(epsilon -> 0^+) (F(x, y + epsilon) - F(x, y)) / (F_Y (y + epsilon) - F_Y (y)) \
    &= (diff F(x,y) slash diff y)/(diff F_Y (y) slash diff y) \
    &= (diff integral_(-oo)^x integral_(-oo)^y f_(X,Y) (x,y) dif x dif y) / (diff integral_(-oo)^y f_Y (y) dif y) \
    &= integral_(-oo)^x f_(X|Y) (x|y) dif x = integral_(-oo)^x (f_(X,Y)(x,y)) / (f_Y (y)) dif x.
  $
]

