#import "@local/MetaNote:0.0.2" : *
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

#let Cov = math.op("Cov")

= Basics

== Axiomization of Probability

=== Definitions

#definition(title: "Event Field")[
  For a sample space $S$, an event field $cal(F)$ is a collection of subsets of $S$ that satisfies the following properties:

  + $S in cal(F)$,
  + If $A in cal(F)$, then $macron(A) in cal(F)$,
  + If $A_i in cal(F)$, then $union.big_(i=1)^(oo) A_i in cal(F)$.

  The set $cal(F)$ satisfying these properties is called a $sigma$-algebra. When the third property holds only for a finite number of sets, the set is called an boolean algebra.
]

Simply put, $sigma$-algebra is a collection of subsets of $S$ that is closed under countable union and complementation.

#definition(title: "Measure")[
  For a $sigma$-algebra $cal(F)$, the function $P: cal(F) -> RR$ is called a measure if it satisfies the following properties:

  + Non-negativity: $P(A) >= 0$ for all $A in cal(F)$,
  + Countable additivity: $P(union.big_(i=1)^(oo) A_i) = sum_(i=1)^(oo) P(A_i)$ for all $A_i in cal(F)$ such that $A_i inter A_j = emptyset$ for $i != j$.
]

Now we can formally define the probability measure, which is a measure that satisfies the additional property of assigning the value of 1 to the entire sample space.

- Normalization: $P(S) = 1$.

#definition(title: "Probability Space")[
  A probability space is a triple $(S, cal(F), P)$, where $S$ is a sample space, $cal(F)$ is a $sigma$-algebra on $S$, and $P$ is a probability measure on $cal(F)$.
]

=== Properties

#theorem(title: "Properties of Probability Measure")[
  Let $(S, cal(F), P)$ be a probability space. Then the probability measure $P$ satisfies the following properties:

  - Subtractivity: $P(A-B) = P(A) - P(A B)$,
  - ...
  - General Inclusion-Exclusion Principle: $ P(union.big_(i=1)^(n) A_i) = sum_(i=1)^(n) P(A_i) - sum_(i < j) P(A_i A_j) + sum_(i < j < k) P(A_i A_j A_k) - ... + (-1)^(n-1) P(A_1 A_2 ... A_n). $
]

#note(title: "Countable Additivity vs. Finite Additivity")[
  There is a subtle difference between countable additivity and finite additivity, because the limit of sum might not be interchangeable with the probability measure $P$. Often this requires $P$ to be a continuous measure.

  Counterexample: $S = [0,+oo), P(A) = lim_(k -> oo) 1/k lambda(A inter (0,k))$.
  Consider $A_i = [i-1,i)$. $union.big^oo_i A_i = S, P(S) = 1$, but $sum_(i=1)^(oo) P(A_i) = 0$.
]

== Conditional Probability

#definition(title: "Conditional Probability")[
  The conditional probability of an event $A$ given an event $B$ (s.t. $P(B) > 0$) is defined as:

  $ P(A|B) = P(A B) / P(B) $

  where $P(B) > 0$.
]

It's easy to check that conditional probability satisfies the properties of a probability measure.

#theorem(title: "Multiplication Rule")[
  For any two events $A$ and $B$, the probability of their intersection can be expressed as:

  $ P(A B) = P(A|B) P(B) = P(B|A) P(A) $

  Generally, $P(A_1...A_n) = P(A_1) P(A_2|A_1) P(A_3|A_1 A_2) ... P(A_n|A_1...A_(n-1)) $.
]

== Bayes' Theorem

#theorem(title: "Theorem of Total Probability")[
  Let $B_1, B_2, ..., B_n$ be a partition of the sample space $S$. Then for any event $A$:

  $ P(A) = sum_(i=1)^n P(A|B_i) P(B_i) $
]

#proof[
  $
    A = A S = A B_1 union A B_2 union ... union A B_n, \
    "whereas" A B_i inter A B_j = emptyset "for" i != j. \
  $
]

#theorem(title: "Total Probability Theorem for Conditional Probability")[
  Let $B_1, B_2, ..., B_n$ be a partition of the sample space $S$. Then for any event $A$ and $C$ ($P(C) != 0$):

  $ P(A | C) = sum_(i=1)^n P(A | B_i C) P(B_i | C) $
]

#note[
  Actually, the theorems still hold on countable partitions because of the countable additivity of probability measure.
]

#theorem(title: "Bayes' Theorem")[
  Events $A_i$ s.t. $P(A_i) > 0$ and $A_i inter A_j = emptyset$ for $i != j$. Give $P(B) != 0$, then

  $
    P(A_i | B) = (P(A_i) P(B | A_i)) / P(B) = (P(A_i) P(B | A_i)) / (sum_(j=1)^n P(A_j) P(B | A_j))
  $
]

#note(title: "Prior Probability")[
  The *prior probability* $P(A_i)$ is the probability of event $A_i$ before any evidence is taken into account. In Bayes' theorem, it is updated to the *posterior probability* $P(A_i | B)$ after the evidence $B$ is observed.
]

= Random Variables and Distributions

== Continuous Random Variables

#definition(title: "Cumuative Distribution Function (CDF)")[
  The cumulative distribution function (CDF) of a random variable $X$ is defined as:

  $ F_X (x) = P(X <= x) $

  for all $x in RR$.
]

#theorem(title: "Properties of CDF")[
  The CDF $F_X (x)$ satisfies the following properties:

  - Non-decreasing: $F_X (x_1) <= F_X (x_2)$ for $x_1 <= x_2$,
  - Right-continuous: $lim_(x -> x_0^+) F_X (x) = F_X (x_0)$ for all $x_0 in RR$.
]

#proof[
  
  _Right-continuity_: by definition of limits and Kolmogorov's axioms.

  - For any decreasing sequence $h_n -> 0^+$, the events ${X <= x + h_n}$ is a decreasing sequence.
  - By the continuity of probability measure, $
  lim_(n -> oo) P({X <= x + h_n})
  = P(inter.big_(n=1)^oo {X <= x + h_n}).
  $
  - As $h_n->0^+$, $inter.big_(n=1)^oo {X <= x + h_n} = {X <= x}$.
  - Therefore, right-continuity holds.

  #note[
    The left-continuity is not guaranteed, e.g. when $P(X = k) != 0$, the jump at $x = k$ is not continuous.
  ]
]

= Multivariate Random Variables and Distributions

== Discrete Case

== Continuous Case

=== Marginal and Conditional Distributions

#definition(title: "Marginal Distribution")[
  Let the joint distribution of random variables $X$ and $Y$ be $F_(X,Y) (x,y)$. The marginal distribution of $X$ is obtained by summing over all possible values of $Y$:

  $
    F_x (x) = P(X <= x) = F(x, oo).
  $
]

#definition(title: "Conditional Distribution")[
  The conditional distribution of $X$ given $Y = y$ is defined as:

  $
    F_(X|Y) (x|y) = lim_(epsilon -> 0^+) P(X <= x | y < Y <= y + epsilon),
  $

  where $forall epsilon > 0$, $P(y < Y <= y+epsilon) > 0$.
]

#note(title: "Relation to Conditional Probability Density")[
  $
    F_(X|Y) (x|y) &= lim_(epsilon -> 0^+) P(X <= x, y < Y <= y + epsilon) / P(y < Y <= y + epsilon) \
    &= lim_(epsilon -> 0^+) (F(x, y + epsilon) - F(x, y)) / (F_Y (y + epsilon) - F_Y (y)) \
    &= (diff F(x,y) slash diff y)/(diff F_Y (y) slash diff y) \
    &= (diff integral_(-oo)^x integral_(-oo)^y f_(X,Y) (x,y) dif x dif y) / (diff integral_(-oo)^y f_Y (y) dif y) \
    &= integral_(-oo)^x f_(X|Y) (x|y) dif x = integral_(-oo)^x (f_(X,Y)(x,y)) / (f_Y (y)) dif x.
  $
]

= No Title

== Correlation and Covariance

#theorem()[
  $rho_(X Y) = 1$ iff $X$ and $Y$ are perfectly linearly correlated, i.e. 
  $
    exists a, b, P(Y = a X + b) = 1.
  $
]

#proof[
  Recall that to prove a event has probability $1$, we may show its variance is $0$.

  $
    D(Y - a X) &= EE(Y - a X)^2 \
    &= a^2 EE(X^2) - 2 a EE(X Y) + EE(Y^2) = 0.
  $

  It suffices to show that the above equation has a root $a$. $Delta = 0$ obviously, and we're done.
]

#definition(title: "Not Linear Correlated")[
  If $X,Y$ are not linearly correlated, then
  - $rho_(X Y) = Cov(X,Y) = 0$,
  - $Cov(X,Y) = E(X Y) - E(X) E(Y) = 0$,
  - $D(X+Y) = D(X) + D(Y) + 2 Cov(X,Y) = D(X) + D(Y)$,

  and the above conditions are equivalent.
]

#note(title: "Independence and Correlation")[
  Independence do imply irrelevance, but not the other way around. For example, $X tilde cal(N)(0,1), Y = abs(X)$. 
  - $EE(X) = 0, EE(X Y) = 0$, hence they are uncorrelated.
  - $P(X <= c, Y<= c) = P(Y<=c) =^? P(X<=c)P(Y<=c)$, meaning they are not independent.
]

== Higher Moments

#definition(title: "Mixed Moment")[
  The $k+l$ mixed moment of random variables $X$ and $Y$ is defined as $EE(X^k Y^(l))$; the central $k+l$ mixed moment is defined as $EE((X - EE(X))^k (Y - EE(Y))^l)$.
]

= Midterm Review

== Inequalities

#theorem(title: "Single-Sided Chebyshev's Inequality")[
  For any random variable $X$ with finite mean $EE[X]$ and finite variance $sigma^2$, the following inequality holds for all $lambda$:

  $ P(X - EE[X] >= lambda) <= sigma^2 / (sigma^2+lambda^2). $
]

#proof[
  Choose a parameter $u$ and denote $Y = X - EE[X]$. Follow the idea used in Chebyshev's inequality, we have:
  $
    P(X-EE[X] >= lambda) &= P(Y+u >= lambda + u) \
    &<= P((Y+u)^2 >= (lambda + u)^2) \
    &<= EE[(Y+u)^2]/(lambda + u)^2 \
    &= (sigma^2 + u^2) / (lambda + u)^2 \
    &=^(u = sigma^2/lambda) sigma^2 / (sigma^2 + lambda^2).
  $

  The choice of $u$ above minimizes the right-hand side of the inequality.

  Equality holds when:
  - $Pr[Y<= -lambda - 2u] = 0$,
  - Markov's inequality: 
    - equality when $EE[X] = a P(X>=a) <=> EE[X - X dot bold(1)_{X>=a}] = 0$, and since $X, bold(1)_{X>=a} >= 0$, this means $X = X dot bold(1)_{X>=a}$ almost surely. 
    - Further, $Pr(X>a) !=0$ violates $EE[X] = a P(X>=a)$, so $Pr(X>a) = 0$.
    - This means that $X$ follows a two-point distribution almost surely.
    - In this case, $(Y+u)^2$ follows a two-point distribution as well, at $Y = -u$ and $Y = lambda or -lambda - 2u$. $-lambda - 2u$ is not possible since $Pr(Y<= -lambda - 2u) = 0$.

  In simple terms, the equality holds when $X$ is a two-point distribution, where $Pr[X = EE[X]-sigma^2/lambda] = lambda^2/(lambda^2+sigma^2) space (1-"RHS")$ and $Pr[X = EE[X]+lambda] = sigma^2/(lambda^2+sigma^2) space ("RHS")$.
]