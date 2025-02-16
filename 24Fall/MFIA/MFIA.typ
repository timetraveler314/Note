#import "@local/MetaNote:0.0.1" : *
#import "@preview/fletcher:0.5.3" as fletcher: diagram, node, edge

#let detm = math.mat.with(delim: "|")

#show: doc => MetaNote(
  title: [
    Mathematical Foundations for the Information Age
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

#let rank = math.op("rank")
#let ip(x,y) = $lr(angle.l #x, #y angle.r)$

= High Dimensional Space

In high-dimensional space, we often encounter the phenomenon of "concentration of measure". This means that most of the mass of a high-dimensional distribution is concentrated near its mode. This is in stark contrast to the one-dimensional case, where the mass is spread out over the entire space. Now we will explore some of the properties of high-dimensional space, beginning from the basic inequalities in probability theory.

== Tail Bounds

#theorem("Markov")[
  For any non-negative random variable $X$ and any $t > 0$,

  $
  Pr[X >= t] <= E[X] / t.
  $
]

#theorem("Chebyshev")[
  For any random variable $X$ with mean $mu$ and variance $sigma^2$,

  $
  Pr[abs(X - mu) >= t] <= sigma^2 / t^2.
  $
]

#theorem("Higher Moments")[
  For any random variable $X$ with mean $mu$ and variance $sigma^2$,

  $
  Pr[abs(X - mu)^k >= t^k] <= E[(X - mu)^k] / t^k.
  $
]

== Properties of the Unit Ball (Counterintuitive)

We focus on high-dimensional (unit) balls. Overall, we want to solve for the volume of a them first. An elegant way begins with hyper-spherical coordinates, which extends the polar coordinates to higher dimensions in a natural way. Like $r dif r dif theta$, $r^2 sin theta dif r dif theta dif phi$ in 3D, we merge all $d-1$ angles into a single differential term $d Omega$. Then integrating over the unit ball looks like:

$
integral r^(d-1) integral_(SS^(d-1)) d Omega dif r.
$

This gives us the intuition of accumulating layer-by-layer from the center to the surface, like peeling an onion.

#theorem("Volume of a Unit Ball")[
  $
  V(d) = pi^(d/2) / Gamma(d/2 + 1).
  $
]

#proof[
  Using the polar coordinates, we have:

  $
  V(d) = integral_0^1 r^(d-1) dif r integral_(SS^(d-1)) d Omega = A(d)/d,
  $

  where $A(d) = integral_(SS^(d-1)) d Omega$ denotes the surface area. We extract the surface area because it recurringly appears when integrating in the hyper-spherical coordinates.

  Now we extend the Gaussian integral to higher dimensions, which is key to finding out the factor $A(d)$. Consider

  $
  I(d) = integral_RR ... integral_RR e^(-(x_1^2 + ... + x_d^2)) dif x_1 ... dif x_d.
  $

  In Cartesian coordinates, we have $
  I(d) = [integral_RR e^(-x^2) dif x]^d = pi^(d/2).
  $

  In polar coordinates, we have
  $
  I(d) = integral_0^(+oo) e^(-r^2) r^(d-1) dif r integral_(SS^(d-1)) d Omega = integral_0^(+oo) t^(d/2-1) e^(-t) dif t A(d) = 1/2 Gamma(d/2) A(d). 
  $

  Hence 
  
  $ A(d) = (2 pi^(d/2)) / Gamma(d/2), V(d) = (2 pi^(d/2)) / (d Gamma(d/2)) = pi^(d/2) / Gamma(d/2 + 1). $
]

Balls in high dimensions exhibit some counterintuitive properties. We will show some of them.

- *Observation 1*: The volume of a unit ball in high dimensions concentrates near the surface.

$
Pr["Point is in the annulus"] = (V(d)-V(d)(1-epsilon)^d)/(V(d)) = 1 - (1-epsilon)^d >= 1 - e^(-epsilon d).
$

From now on, analysis on the asymptotic behavior will prevail. Here we see that, most of the volume of the $d$-dimensional unit ball is contained in an annulus of width $O(1/d)$ near the boundary. That is to say, at least a constant fraction of the volume is within $O(1/d)$ of the boundary. Wow!

- *Observation 2*: The volume of a unit ball in high dimensions concentrates near the equator.

To formalize this, we need to solve for bounds of the volume of a spherical cap. Take a thin slab of height $h$ of the hemisphere.

A coarse upper bound, but enough for our purpose:

$
V_1 &= V(d-1) integral_h^1 (1 - r^2)^((d-1)/2) dif r \
"where" integral_h^1 (1 - r^2)^((d-1)/2) dif r &<= integral_h^1 e^(-r^2(d-1)/2) dif r <= integral_h^(+oo) r/h e^(-r^2 (d-1)/2) dif r\
&= e^(-(d-1) h^2/2)/(h(d-1)).
$

Then it suffices to obtain a lower bound of the "slab". We approximate by the cylinder with the same height and base area as a lower bound. Specifically, the height is $h$ and the base radius is $sqrt(1-h^2)$.

$
V_2 &>= V(d-1) h (1-h^2)^((d-1)/2) \
&>= V(d-1) h (1-(h^2(d-1))/2) ("Bernoulli", (1-x)^alpha >= 1-alpha x, alpha >= 1)
$

Thus

$
"Ratio" <= (e^(-((d-1)h^2)/2))/((d-1)h^2 (1-((d-1) h^2)/2)).
$

Notice the frequent occurance of $(d-1)h^2$, to make the upper bound asymptotically a constant, we choose $h = c/sqrt(d-1)$, then $
"Ratio" <= 2/c e^(-c^2/2).
$

#note("Why did we use a lower bound for the slab part?")[
  In our approach, $V(d-1)$ remains hard to calculate. By virtue of the cylinder, $V(d-1)$ can be cancelled out, simplifying our discussion.
]

The above discussion boils down to the theorem:

#theorem("Concentrated Volume Near the Equator, Quantized")[
   For $c>=1$ and $d>=3$, at least a $1-2/c e^(-c^2/2)$ fraction of the volume of the $d$-dimensional unit ball has $abs(x_1) <= c/sqrt(d-1)$.
]

Now let's extend the single restriction by considering restriction on more dimensions or more points. For this, union bound is needed to bound the probability of multiple events happening together.

#lemma("Union Bound Abbreviated")[
    $
    Pr[A union B] <= Pr[A] + Pr[B].
    $
]

#proof[
  Trivial.
]

We first consider a small box centered at the origin. By the above theorem, $
Pr[exists i, abs(x_i) >= c/sqrt(d-1)] <= d dot 2/c e^(-c^2/2).
$

This is the probability that a point falls out of the box. Let $c = 2 sqrt(ln d)$, the upper bound becomes $1/(d sqrt(ln d)) <= 1/2$. Then we can say the box takes up at least $1/2$ proportion of the sphere.

Wait - is there anything wrong? One might wonder how it can be that nearly all the points in the sphere are very close to the surface and yet at the same time in a box of side-length $O(sqrt((ln d)/(d-1)))$. To answer this, we notice for each coordinate, a typical vlaue for $x_i$ will be $O(1/sqrt(d))$. Then the relation becomes clear.

With the above observations, an immediate consequence arises when we draw more points: they are likely to have large norms, and are likely to be mutually orthogonal. To be precise, when we draw $n$ points at random, we expect at a high probability $1-O(1/n)$ that they all follow some properties. Here, union bound occurs repeatedly.

#theorem("Near Orthogonality")[
  Consider drawing $n$ points $p_1, ... ,p_n$ at random from the unit ball. With probability $1-O(1/n)$, we have:
  + $forall i, norm(p_i) >= 1 - (2 ln n)/d$;
  + $forall i != j, abs(p_i dot p_j) <= (sqrt(6 ln n))/(sqrt(d-1))$.
]

#proof[
  The first part follows from the observation 1,
  $
  Pr[norm(p_i) < 1 - epsilon] <= e^(-epsilon d).
  $

  By the union bound, we have

  $
  Pr[exists i, norm(p_i) < 1 - epsilon] <= n e^(-epsilon d).
  $

  We wish the upper bound to be $O(1/n)$, so we set $epsilon = (2 ln n)/d$, and the first part is proved.

  The second part follows from the observation 2. Consider pairwise dot products of $p_i, p_j$. Fix $p_i$ as the north pole, then the dot product is no more than the projection $x_1$. By the theorem, we have

  $
  Pr[abs(p_i dot p_j) >= c/sqrt(d-1)] <= 2/c e^(-c^2/2). 
  $

  There are $binom(n,2) = O(n^2)$ pairs in total, again by the union bound, we have

  $
  Pr[exists i != j, abs(p_i dot p_j) >= c/sqrt(d-1)] <= O(n^2) 2/c e^(-c^2/2) <= O(n^2) e^(-c^2/2).
  $

  Letting $c = sqrt(6 ln n)$, the upper bound is $O(1/n)$.
]

== High Dimensional Gaussian Distribution

#definition("Mode")[
  The mode of a distribution is the value that appears most frequently.
  $
  op("Mode")(X) = op("argmax")_x Pr[X = x].
  $
]

=== Concentration Bound

Question: Where will most of the mass of a high-dimensional Gaussian distribution be? Near the mode, or somewhere else? First, let's consider the norm of a random vector drawn from a high-dimensional Gaussian distribution.

$
norm(bold(x)) = sqrt(x_1^2 + ... + x_d^2), "where" x_i tilde cal(N)(0,1).
$

As $d$ goes large, we can actually apply the Law of Large Numbers to sum of random variables under the square root.

$
norm(bold(x)) tilde sqrt(d).
$

Following the intuition, we can say that most of the mass of a high-dimensional Gaussian distribution is near the annulus of radius $sqrt(d)$. Now let's prove this rigorously.

#theorem("Gaussian Annulus Concentration")[
  For any $beta > 0$, 

  $
  Pr[abs(norm(bold(x)) - sqrt(d)) >= beta] <= 3 e^(-c beta^2).
  $
]

#proof[

]

== Johnson-Lindenstrauss Lemma

#align(center)[
  Compression.
]

It's often inefficient to work with high-dimensional data directly. The Johnson-Lindenstrauss lemma provides a way to reduce the dimensionality of the data while preserving the pairwise distances between the points. 

Let's introduce $epsilon$ to denote the distortion factor. The lemma states that for any set of $n$ points in $d$-dimensional space, there exists a linear transformation $A$ to $k$-dimensional space, where $k = O(log n / epsilon^2)$, such that the pairwise distances between the points are approximately preserved.

#theorem("Johnson-Lindenstrauss Lemma")[
  For any $epsilon in (0,1)$ and any set of $n$ points $bold(v)_1, ... , bold(v)_n$ in $d$-dimensional space, there exists a linear affine transformation (random projection) $f$ to $k$-dimensional space, where $k >= 3/(c epsilon^2) ln n$, such that with high probability $Pr >= 1 - 3/(2n)$,

  $
  forall i != j, (1-epsilon) norm(bold(v)_i - bold(v)_j) <= norm(f(bold(v)_i) - f(bold(v)_j)) <= (1+epsilon) norm(bold(v)_i - bold(v)_j).
  $
]

#note[
  A surprising observation is that the lemma does not depend on the dimensionality of the original space $d$.
]

#proof[
  By linearity, $f(bold(v)_i) - f(bold(v)_j) = f(bold(v)_i - bold(v)_j)$. Then it suffices to preserve $f(bold(v))$. We only need to focus on all the unit vectors $norm(bold(v)) = 1$, we want $norm(1/sqrt(k) f(bold(v))) tilde 1$.
]

= Singular Value Decomposition

== Introduction

#theorem("Facts on SVD")[
  - $sum_i sigma_i^2 = norm(A)_F^2$;
  - $A = sum_i sigma_i u_i v_i^dagger$;
  - $sigma_1(A) = sigma_1(A^dagger)$
]

== Low-Rank Approximation

Let's consider the problem of approximating a matrix $A$ by a rank-$k$ matrix $B$. We will finally show that the best rank-$k$ approximation to $A$ is given by the SVD of $A$. First, consider the case $rank(B)=1$. We want to minimize the norm of $A-B$, either the Frobenius norm or the ...:

#definition("Spectral Norm")[
  The spectral norm of a matrix $A$ is the largest singular value of $A$.
  $
  norm(A) = sigma_1(A).
  $
]

== Trace Inequalities

In this section, we will introduce some inequalities involving the trace of matrices. Because the trace is actually inner product of two matrices, many properties are especially useful to convert geometric intuition into algebraic form.

#theorem("Von Neumann Trace Inequality")[
  For any two matrices $A$ and $B$,

  $
  abs(tr(A B)) <= sum_i sigma_i (A) sigma_i (B).
  $
]

There are some advanced techniques like _doubly stochastic matrices_ that can be used. But here we will begin in a more elementary way.

#proof[
  Using SVD on $A$ and $B$, and the fact that the trace is invariant under cyclic permutations, the problem is effectively reduced to
  $
    abs(tr(bold(D) bold(U) bold(S) bold(V)^dagger)) <= tr(bold(D)bold(S)),
  $

  where $bold(D),bold(S)$ are diagonal matrices with descending singular values, and $bold(U),bold(V)$ are unitary matrices.

  Consider the projection matrix $bold(P)_k = op("diag")(bold(I)_k,bold(0)_(n-k))$. We may write $
    bold(D) = (d_1-d_2)bold(P)_1 + (d_2-d_3)bold(P)_2 + ... + d_n bold(P)_n
    $
  as a convex (non-negatively weighted) combination of $bold(P)_i$'s. Similar for $bold(S)$. For sake of simplicity, we write $bold(D) = sum_j p_j bold(P)_j, bold(S) = sum_k q_k bold(P)_k$.

  For any pair $j,k$, we show that 
  $ 
    abs(tr(bold(P)_j bold(U) bold(P)_k bold(V)^(dagger))) <= tr(bold(P)_j bold(P)_k) = k.
   $

  WLOG, assume $j >= k$. If not, just swap their position and the arguments are similar. Then $bold(P)_j bold(U) bold(P)_k = mat(bold(P)_j bold(u)_1,...,bold(bold(P))_j bold(u)_k, bold(0), ..., bold(0))$.

  $
    tr(bold(P)_j bold(U) bold(P)_k bold(V)^(dagger)) &= sum_(i=1)^k ip(bold(P)_j bold(u)_i, bold(v)_i) \
    &<= sqrt((sum_(i=0)^k norm(bold(P)_j bold(u)_i)^2)(sum_(i=0)^k norm(bold(v)_i)^2)) ("Cauchy-Schwarz") \
    &<= sqrt((sum_(i=0)^k 1)(sum_(i=0)^k 1)) ("Orthogonality") = k.
  $

  Then by triangle inequality, we have

  $
    abs(tr(bold(D) bold(U) bold(S) bold(V)^(dagger))) &= abs(sum_(j,k) p_j q_k tr(bold(P)_j bold(U) bold(P)_k bold(V)^(dagger))) \
    &<= sum_(j,k) p_j q_k abs(tr(bold(P)_j bold(U) bold(P)_k bold(V)^(dagger))) <= sum_(j,k) p_j q_k tr(bold(P)_j bold(P)_k) = tr(bold(D) bold(S)).
  $

  The proof is thus completed.
]

= Streaming and Sampling

== Streaming Algorithms

=== Finding Majority

=== Counting Distinct Elements

We prove that the algorithm gives a good approximation of the number of distinct elements in a stream with high probability. Specifically, the actual number is denoted by $d$, and our approximation is $hat(d) = M/"min"$. We want to show that
$
  Pr[d/6 <= hat(d) <= 6d] >= 2/3.
$

For one side of the inequality, the second moment method comes in handy because under the assumption of pairwise independence, the variance of the estimator is uniquely determined.

#note("Second Moment Method")[
  In the method, we often utilize a $0-1$ indicator random variable. In this case, consider $ I_(a_i) = cases(0\, h_(a,b)(a_i)>(6M)/d, 1\, "otherwise"). $

  Often, our bad event is a extreme case where every trial is bad (in the tail). So in the distribution of the sum of the indicators, the badd event $Sigma = 0$ falls in the tail, but not on the infinity side! This is the key point.
]

Using the above indicator, we see that

$
  EE(X) = d dot EE(I_(a_i)) approx 6.
$

So applying tail bounds, we have

$
  &Pr[min > (6M)/d] \
  =& Pr[forall i, h_(a,b)(a_i) > (6M)/d] = Pr[sum_i I_(a_i) = 0] \
  <=& Pr[abs(X-EE(X))^2 >= EE(X)] \
  <=& (op("Var")(X))/EE(X)^2 = (d dot 6/d dot (1-6/d))/6^2 < 1/6.
$

Here the variance is calculated linearly because the indicators are pairwise independent.

== Sampling and Sketching

== Sketching for Matrix Multiplication

Assume we want to approximately compute the matrix product $A B$. Note that the product can be written as $A B = sum_i a_i b_i^dagger$, where $a_i$ and $b_i$ are the columns of $A$ and $B$ respectively. There might be some small 

= Random Graphs

#note("Recall the Asymptotic Notation")[
  - $Omega$ denotes the lower bound, i.e., $f(n) = Omega(g(n))$ means $f(n) >= c g(n)$ for some constant $c$.
  - $omega$ denotes the strict lower bound, i.e., $f(n) = omega(g(n))$ means $f(n) > c g(n)$ for all constants $c$.
]

Denote by $G(n,p)$ the random graph on $n$ vertices where each edge is present with probability $p$. 

One of the most famous results in random graph theory is the phase transition of the emergence of a giant component. We may expect that properties of the random graph $G(n,p)$ will change gradually as $p$ increases. However, the phase transition phenomenon tells us that there is a sharp threshold at which a giant component emerges.

== Existence of Patterns

=== Triangles

$
  EE[sum I_triangle] = sum EE[I_triangle] = binom(n,3) p^3.
$

What's the relation between the probability that a triangle exists and the expection of the number of triangles? We can use the first moment method (Markov Inequality).

$
  Pr[triangle "exists"] = Pr[sum I_triangle >= 1] <= EE[sum I_triangle] = binom(n,3) p^3.
$

This shows that when $p = o(1/n)$, the probability that a triangle exists tend to $0$.

To show the other side of the inequality, we recall that when faced with $Pr[sum I_triangle = 0]$, we can use the second moment method.

$
  Pr[not triangle "exists"] = Pr[sum I_triangle = 0] <= (op("Var")(sum I_triangle))/EE(sum I_triangle)^2.
$

Now we face the problem of calculating the variance of the sum of indicators, since they are not pairwise independent. 

#let Var = math.op("Var")
#let Cov = math.op("Cov")

$
  Var[sum I_triangle] &= sum Var[I_triangle] + sum_(triangle, triangle') Cov[I_triangle, I_triangle'] \
  &<= sum EE[I_triangle] + sum_(triangle, triangle') EE[I_triangle I_triangle'] \
$

#note[
  $
    Var[X] = EE[X^2] - EE[X]^2, Cov[X,Y] = EE[X Y] - EE[X]EE[Y].
  $

  For non-negative indicators, the negative term of expectation is thrown away.
]

The covariance term is the most difficult to calculate. We loosen the bound by only keeping the $EE$ terms, which stands for the case where the two triangles share an edge, like $triangle.l triangle.r$.

Such a shape with $4$ vertices and $5$ edges can be counted by $binom(n,4)$ ways, and the probability is $p^5$. So the term is finally $binom(n,4) p^5 = Theta(n^4 p^5)$.

$
  Pr[not triangle "exists"] <= (Theta(n^3 p^3) + Theta(n^4 p^5))/(EE[sum I_triangle])^2 = Theta(n^(-3) p^(-3)) + Theta(n^(-2) p^(-1)).
$

When $p = omega(1/n)$, the probability that no triangle exists tends to $0$.

=== 4-cliques

Let $X = sum I_4$ be the number of 4-cliques. Beginning with the expection $EE[X] = Theta(n^4 p^6)$, we guess that the threshold for the emergence of a 4-clique is $r(n) = Theta(n^(-2/3))$.

The first side is rather easy: when $p = o(n^(-2/3))$, 
$
  Pr["4-clique exists"] = Pr[X >= 1] <= EE[X] -> 0,
$

Hence $r(n) = Omega(n^(-2/3))$.

The other side requires analysis on the interplay between two 4-cliques.
+ No edge shared: $EE[X]^2$.
+ Two points shared: $Theta(n^6 p^11)$.
+ Three points shared: $Theta(n^5 p^9)$.
+ Complete overlap: $EE[X]$.

Now we take a little different approach. We directly consider $EE[X^2]$, which is just less than the sum of the above terms.

$
  EE[X^2] &<= EE[X]^2 + Theta(n^6 p^11) + Theta(n^5 p^9) + EE[X], \
  => Var[X]/EE[X]^2 &<= Theta(n^(-2) p^(-1)) + Theta(n^(-3) p ^(-3)) + Theta(n^(-4) p^(-6)).
$

When $p = omega(n^(-2/3))$, the probability that no 4-clique exists tends to $0$. Therefore, $r(n) = O(n^(-2/3))$.

=== General Substructures

Generalizing the idea, we may expect for a substructure with $v$ vertices and $e$ edges, the expection is $EE[I_?] = binom(n,v) p^e tilde n^v p^e$. However, does this imply that the threshold for the emergence of a $v$-clique is $r(n) = Theta(n^(-v/e))$?

The answer is no. The reason is that the covariance might be large, in a sense that overlapping substructures are more easily formed than individual ones. We haven't seen this phenomenon in the case of triangles and 4-cliques because the two substructures are too dense, making no denser overlap possible.

Kites are a good example. A kite is a $K_4$ with an additional edge. The expection of the number of kites is $Theta(n^5 p^7)$. However, since it has a $K_4$ as a substructure, which requires $Omega(n^(-2/3))$ (greater than $n^(-5/7)$), the threshold for the emergence of a kite is at least $r(n) = Omega(n^(-2/3))$.

As for intersecting kites, one may be impatient to list all the cases. However, as we will see, what we care about is just the "density" of the intersection.

Regardless of shape, consider a case of intersection where the two substructures share $v$ vertices and $e$ edges. This results in a term of $Theta(n^v p^e)$ in the upper bound of the variance $Var[\#"kites"]$. If we wish $Pr[\#"kites" = 0] -> 0$, we need $r(n) = omega(n^(-v/e))$. So ranging over all possible substructures, we need the maximum of $-v/e$, which is equivalent to the maximum of $rho = e/v$.

In this question, $K_4$ is the most dense substructure, so the threshold for the emergence of a kite is $r(n) = Omega(n^(-2/3))$.

=== Isolated Vertices

=== Diameter 2

#pagebreak()

// Maximum over all pairs of vertices. Indicator variable: $I_(i,j) = 1$ iff $v_i,v_j$ has 

Consider the property of the graph that the diameter is at most 2. We will show that the property has a sharp threshold at $p = sqrt((2 ln n)/n)$.

To get a rough idea, we assume that $p = o(1)$ because we wish the threshold to decrease as $n$ increases.

The indicator variable here is $X = \#"pairs with distance greater than 2"$. 

To solve for the expectation, we have the following observation: a pair of vertices $(i,j)$ has distance greater than 2 if and only if $(i,j) in.not E$ and there is no common neighbor of $i$ and $j$.

$
  EE[X] &= binom(n,2) (1-p)^2 (1-p^2)^(n-2) \
  &= Theta(n^2 e^(-n p^2)).
$

This gives a rough idea that the threshold is around $p = sqrt((2 ln n)/n)$, consistent with our intuition.

Next, we analyze $EE[X^2]$, i.e. the probability that two pairs of vertices have both distance greater than 2.

- No intersection: $EE[X]^2$.
- One vertex in common: denote them as $i,j,k$, sharing $i$. First we have $(i,j)$ and $(i,k)$ are both not edges. Then we discuss whether $(i,m)$ exists for $m != i,j,k$. If so, then distances $> 2$ iff $(m,j), (m,k)$ are not edges. If not, any setting for $(m,j), (m,k), (j,k)$ is valid. The probability is

$
  (1-p)^2 ((1-p) + p (1-p)^2)^(n-3) = Theta(e^(-2n p^2)).
$

#diagram(
  // cell-size: 15mm,
  node((0,0), $i$), node((-1,2), $j$), node((1, 2), $k$), node((-1, 1), $m$),
  edge((0,0), (-1,1)), edge((-1,1), (-1,2)), edge((-1,1), (1,2)),
  edge((-1,2), (1,2), "--")
)

- Complete overlap: $EE[X]$.

In conclusion, we have

$
  Var[X]/EE[X]^2 = (Theta(n^3 e^(-2n p^2)) + Theta(n^2 e^(-n p^2)))/Theta(n^4 e^(-2n p^2)).
$

We will only consider $G(n, p = c sqrt((ln n)/n))$ for some constant $c$. Substituting $p$ into the above expression, we have $Var[X]/EE[X]^2 -> 0$ when $c < sqrt(2)$. Therefore, $r(n) >= sqrt((2 ln n)/n)$.

As for $c > sqrt(2)$, $Pr[diameter > 2] = Pr[X = 0] <= EE[X] = Theta(n^(2-c^2)) -> 0$. Therefore, $r(n) = sqrt((2 ln n)/n)$.