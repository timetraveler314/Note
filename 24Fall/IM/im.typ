#import "@local/MetaNote:0.0.1" : *

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

= High Dimensional Space

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

= Appendix

== Useful Inequalities

#theorem("Bernoulli")[]
