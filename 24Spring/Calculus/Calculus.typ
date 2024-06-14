#import "@local/MetaNote:0.0.1" : *
#import "@preview/physica:0.9.0": *
#import "@preview/pinit:0.1.2": *

#let pinit-highlight-equation-from(height: 2em, pos: bottom, fill: rgb(0, 180, 255), highlight-pins, point-pin, body) = {
  pinit-highlight(..highlight-pins, dy: -0.6em, fill: rgb(..fill.components().slice(0, -1), 40))
  pinit-point-from(
    fill: fill, pin-dx: -0.6em, pin-dy: if pos == bottom { 0.8em } else { -0.6em }, body-dx: 0pt, body-dy: if pos == bottom { -1.7em } else { -1.6em }, offset-dx: -0.6em, offset-dy: if pos == bottom { 0.8em + height } else { -0.6em - height },
    point-pin,
    rect(
      inset: 0.5em,
      stroke: (bottom: 0.12em + fill),
      {
        set text(fill: fill)
        body
      }
    )
  )
}

#let detm = math.mat.with(delim: "|")
#let vol = math.op("Vol")

#let int = math.integral
#let iint = math.integral.double
#let iiint = math.integral.triple
#let oint = math.integral.cont
#let oiint = math.integral.surf
#let oiiint = math.integral.vol

#let vr = math.bold($r$)
#let vs = math.bold($s$)
#let vn = math.bold($n$)
#let vF = math.bold($F$)
#let vS = math.bold($S$)
#let rot = math.op("rot")
#let gradd = math.op("grad")
#let divv = math.op("div")

#let lnf = $lim_(n->+oo)$
#let ser = $sum_(n=1)^(oo)$
#let ser0 = $sum_(n=0)^(oo)$

#show: doc => MetaNote(
  title: [
    Calculus (II)
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

#outline()

= Multiple Integral

== Defining Mass 

Assume $D$ is Jordan measurable. Given a density function $f: D -> RR$, the mass of the object is given by the integral of the density function over the region $D$, denoted by $integral_D f dif sigma$.

How can we define the integral? Like what we learned in the single-variate case, we can use Riemann sums to define the integral.

$ integral_D f dif sigma = lim_(norm(P) -> 0) sum tilde(f) (xi_i) "Vol"(P_i), "if the limit exists." $

Here, $P$ is a partition of $D$, and $xi_i$ is a point in the $i$-th subregion of the partition. The volume of the $i$-th subregion is denoted by $"Vol"(P_i)$.

== Multiple Integral

The intuition above is "using finite combination of straight polyhedron to approximate the region $D$". Similarly, introducing Riemann sums gives us the multiple integral, as in the single-variate case.

By the intuition above, we can define the multiple integral of a function over a region $D$.

#definition("Multiple Integral")[
  Let $D subset Q$ be a bounded Jordan measurable set, where $Q$ is a bounded straight polyhedron in $RR^n$. Let $f: D -> RR$. For any given straight polyhedron partition $P$ of $Q$ and any choice of points $xi_i$ in the $i$-th subregion of the partition, we consider the Riemann sum

  $ sum_(i=1)^(n(P)) tilde(f) (xi_i) "Vol"(P_i) $

  where $ tilde(f)=cases(f(xi) comma "if" xi in D, 0 comma "otherwise"). $

  If the limit of the Riemann sum exists as the norm of the partition goes to zero, we say that $f$ is integrable over $D$, and we define the multiple integral of $f$ over $D$ as

  $ integral_D f dif sigma = lim_(norm(P) -> 0) sum tilde(f) (xi_i) "Vol"(P_i). $
]

#note()[
  (1) $f$ is integral over $D$ $=>$ $f$ is bounded on $D$.

  However, the converse is not true. Consider $ f(x,y) = cases(1 comma space x comma y in QQ sect [0 comma 1], 0 comma "otherwise")$.

  (2) $f$ is integral over $D$ $<=>$ $lim_(norm(P) -> 0) omega(P_i)"Vol"(P_i) = 0$, where $ omega(P_i) = sup_(xi in P_i) f(xi) - inf_(xi in P_i) f(xi) $ stands for the oscillation of $f$ on $P_i$.

  (3) If $f$ is continuous on $accent(D, -)$, then $f$ is integrable over $D$.

  (4) $f$ is integrable over $D$ $<=>$ The Lebesgue measure of the set of discontinuities of $f$ on $D$ is zero.
]

The basic properties of multiple integrals are similar to those of single integrals, omitted here.

=== Calculation of Multiple Integrals - Fubini Theorem

The core idea of the Fubini theorem is "reducing the multiple integral to iterated integrals", which we are able to compute by the single-variable calculus.

#theorem("Fubini Theorem")[
  Let $f$ be continuous on $D = [a,b] times [c,d]$. Then 

  $ integral_a^b #pin("i1") integral_c^d f(x,y)#pin("i3") dif y #pin("i2") dif x  =^((I)) integral.double_D f(x,y) dif sigma =^((J)) integral_c^d integral_a^b f(x,y) dif x dif y . $

  #pinit-highlight-equation-from(("i1", "i2"), "i3", height: 1.5em, pos: bottom, fill: rgb(150, 90, 170))[
    $I(x)$
  ]
]

#corollary[
  (1) $ integral.double_D f(x,y) dif sigma = integral_a^b integral_(g_1(x))^(g_2(x)) f(x,y) dif y dif x. $

  (2) $ integral.double_D f(x,y) dif sigma = integral_c^d integral_(h_1(y))^(h_2(y)) f(x,y) dif x dif y. $
]

#example[
  $ integral_0^1 (x-1)/(ln x) dif x. $
]

#solution[
  $ integral_0^1 (x-1)/(ln x) dif x = integral_0^1 integral_0^1 x^y dif y dif x
  = integral_0^1 integral_0^1 x^y dif x dif y = dots. $
]

#example("Using Periodicity of the Integrand")[
  $ iint_D abs(cos(x+y)) dif sigma, D=[0,pi] times [0,pi]. $
]

#solution[
  Notice $ integral_0^pi abs(cos(a+x)) dif x = integral_0^pi abs(cos x) dif x = 2, $

  $ iint_D abs(cos(x+y)) = integral_0^pi 2 dif y = 2pi. $
]

==== Fubini Theorem for Triple Integrals

The Fubini theorem can be generalized to triple integrals.

#theorem("Fubini Theorem for Triple Integrals, (i)")[
  (i) $Omega$ is a cylindrical set, and $f$ is continuous on $Omega$. 
  
  Let the projection of $Omega$ onto the $x y$-plane be $D$, and the lower and upper surfaces of $Omega$ be $z = h_1(x,y)$ and $z = h_2(x,y)$, respectively. Then

  $ iiint_Omega f(x,y,z) dif V &= iint_D [integral_(h_1(x,y))^(h_2(x,y)) f(x,y,z) dif z] dif x dif y. $

  #figure(image("assets/fubini-1.jpg", width: 10em), caption: "(i)")
]

#example[
  Solve for the volume of the solid bounded by the equations $ cases(z=x^2+3y^2,z=8-x^2-y^2). $
]

#solution[
  The intersection: $x^2+3y^2=8-x^2-y^2$ gives $diff D: x^2/4+y^2/2=1$.

  $ V &= iint_D (integral_(x^2+3y^2)^(8-x^2-y^2) dif z) dif x dif y = iint_D (8-2x^2-4y^2) dif x dif y
  \ &= integral_0^2 dif x integral_(-sqrt((4-x^2)/2))^sqrt((4-x^2)/2) (8-2x^2-4y^2) dif y = dots. $
]

#theorem("Fubini Theorem for Triple Integrals, (ii)")[
  (ii) $Omega$ is a laminar set, and $f$ is continuous on $Omega$.

  Let the $z$-coordinate of the lowermost and uppermost points of $Omega$ be $z = a,b$. Then

  $ iiint_Omega f(x,y,z) dif V &= integral_a^b iint_(D(z)) f(x,y,z) dif x dif y dif z. $

  // #figure(image("assets/fubini-2.jpg", width: 10em), caption: "(ii)")
]

#question("Volume of Hyperspheres")[
  $B_n (a)={(x_1,dots,x_n)|sum x_i^2 <= a^2}$. Solve for $op("Vol") (B_n(a))$.
]

#solution[
  $\#_1:$ Using recurrence.

]

#theorem("Generalized Fubini Theorem")[
  Let $Omega$ be a Jordan measurable set in $RR^n$, and $f$ be continuous on $Omega$. Then

  $ & integral_(X times Y) f(x_1,dots,x_m;y_1,dots,y_n) dif x_1 dots dif x_m dif y_1 dots dif y_n \ =& integral_X (integral_Y f(x_1,dots,x_m;y_1,dots,y_n) dif y_1 dots dif y_n) dif x_1 dots dif x_m. $
]

== Transformation of Coordinates

#theorem[
  Let $O subset RR^2$ be a bounded open set; $phi : O -> RR^2, (u,v) |-> (x,y) $ be a $C^1$ transformation, and $E subset O$ be a Jordan measurable set. If

  - (i) $det D phi (u,v) = diff(x,y)/diff(u,v) != 0, forall (u,v) in E^o$;

  - (ii) $phi$ is injective on $E^0$,

  then $phi(E)$ is still Jordan measurable, and for any continuous function $f$ on $phi(E)$, we have

  $ integral_(phi(E)) f(x,y) dif sigma = integral_E (f compose phi) det D phi dif u dif v. $
]

== Exercises

#question[

]

== Appendix : Random Integrals in Calculation

#question[
  $ int_0^1 sqrt((1-r^2)/(1-r^2)) r^3 dif r. $
]

#solution[
  $ int_0^1 sqrt((1-r^2)/(1-r^2)) r^3 dif r &= 1/2 int_0^1 sqrt((1-t)/(1+t))t dif t quad (t = r^2) \
  &= 1/2 int_0^1 sqrt((1-t)^2/(1-t^2)) t dif t \
  &= 1/2 int_0^1 (1-sin v)/(cos v) sin v dif (sin v) quad (t = sin v) \
  &= 1/2 int_0^(pi/2) (sin v -sin^2 v) dif v = 1 - pi/4.
  $
]



= Curvilinear Integral

== Line Integral : The Second Kind & Green's Theorem

=== Flow and Divergence

Consider the flow of a vector field $F$ along a curve $Gamma^+$ in $RR^2$. The line integral of $F$ along $Gamma^+$ is defined as

$ oint_(Gamma^+) vF dot vn dif s $

where $vn$ is the unit normal vector of $Gamma^+$. Compute as follows:

$ oint_(Gamma^+) vF dot vn dif s &= oint_(Gamma^+) P dif x - Q dif y \
&= iint_D underbrace((pdv(P,x)+pdv(Q,y)), div vF slash divv vF) dif sigma. $

Here, $D$ is the region enclosed by $Gamma^+$, and $P,Q$ are the components of $F$.

Thus $div vF$ is created to measure the "flow" of $F$.

Now if we consider $u$ as the potential function of $F$, then $vF = grad u$. The line integral of $vF$ along $Gamma^+$ is then

$ oint_(Gamma^+) pdv(u,vn) dif s &= oint_(Gamma^+) grad u dot vn dif s \
&= iint_D div grad u dif sigma \
&= iint_D laplace u dif sigma.
$

=== Curl and Circulation

Now we see what happens in $RR^3$ when we consider the circulation of a vector field $vF$ along a small closed curve $Gamma$ in $RR^2$. The line integral of $vF$ along $Gamma$ is defined as

$ oint_Gamma vF dot dif vr $

Consider the projection of $Gamma$ onto those planes $x O y, y O z, z O x$. Then the circulation of $vF$ along $Gamma$ is

$ oint_Gamma vF dot dif vr &= oint_Gamma_1 vF dot dif vr_1 + oint_Gamma_2 vF dot dif vr_2 + oint_Gamma_3 vF dot dif vr_3 \
&= iint_S (pdv(R,y)-pdv(Q,z)) dif x dif y + iint_S (pdv(P,z)-pdv(R,x)) dif y dif z + iint_S (pdv(Q,x)-pdv(P,y)) dif z dif x \
&= iint_S curl vF dot dif sigma. $

== Surface Integral : The First Kind

When the surface is expressed by two parameters $u, v$,

$ norm(bold(r_u) times bold(r_v)) dif u dif v $ is called the "surface element" of the surface $S$. Now we try to evaluate the factor $norm(bold(r_u) times bold(r_v))$.

#theorem[
  $ norm(bold(r_u) times bold(r_v)) = detm(bold(i), bold(j), bold(k); x_u, y_u, z_u; x_v, y_v, z_v) &= (D(y,z)/D(u,v), D(z,x)/D(u,v), D(x,y)/D(u,v)) \
  &= (A,B,C) $
]

After changing the coordinates, we are here with the factor $norm(bold(r_u) times bold(r_v))$. Given the above way of calculating $sqrt(A^2 + B^2 + C^2)$, are there any simpler ways to calculate this? Consider the following.

#note[
  We have the identity (which is just equvalent to $sin^2 + cos^2 = 1$):

  $ (bold(r_u) times bold(r_v)) dot (bold(r_u) times bold(r_v)) = norm(bold(r_u) times bold(r_v))^2 = norm(bold(r_u))^2 norm(bold(r_v))^2 - (bold(r_u) dot bold(r_v))^2. $

  So letting

  $ cases(E = x_u^2 + y_u^2 + z_u^2, F = x_u x_v + y_u y_v + z_u z_v, G = x_v^2 + y_v^2 + z_v^2) $

  yields $norm(bold(r_u) times bold(r_v)) = sqrt(E G - F^2)$. This is the so-called "first fundamental form" of the surface $S$.
]

#corollary[
  For sphere surface $ cases(x = a cos theta sin phi, y = a sin theta sin phi, z = a cos phi) $ we have

  $ bold(r)_theta &= (- a sin theta sin phi, a sin phi cos theta, 0), \
  bold(r)_phi &= (a cos theta cos phi, a cos phi sin theta, - a sin phi), $

  Then $ E=a^2 sin phi, F = 0, G = a^2. $
]

== Surface Integral : The Second Kind

#definition("Surface Integral : The Second Kind")[
  Let $S$ be a orientable smooth surface in $RR^3$, and $vF$ be a vector field defined on $S$, $vn$ is a given unit normal vector of $S$. The surface integral of $vF$ over $S$ is defined as

  $ oiint_S vF dot vn dif sigma $
]

== Exterior Differential

#let wedge = math.and

We call $dif x, dif y, dots$ 1-differential forms. Now we introduce the operation "wedging" of two differential forms, denoted by $wedge$. It is a bilinear operation, and satisfies the following properties:

(1) $dif x wedge dif x = 0$ (Direct consequence of the antisymmetry);

(2) Antisymmetry: $dif x wedge dif y = - dif y wedge dif x$;

(3) Associativity: $(dif x wedge dif y) wedge dif z = dif x wedge (dif y wedge dif z)$;

#definition("k-differential Form")[
  The $k$-differential form is a linear combination of the form

  $ omega = sum a_(i_1 i_2 dots i_k) dif x_(i_1) wedge dif x_(i_2) wedge dots wedge dif x_(i_k), $

  where $a_(i_1 i_2 dots i_k)$ are smooth functions.
]

#definition($"The" dif "-map"$)[
  The $dif$-map is a linear map from the space of $k$-differential forms to the space of $(k+1)$-differential forms, denoted by $dif$. It satisfies the following properties:

  (1) $dif (f dif x) = dif f wedge dif x$;
]

Finally, here's the generalized Stokes' theorem, also known as the "Cartan's magic formula".


== Exercises

#question[
  Evaluate $ oint_C x y dif s, $
  where $C$ is the intersection of the sphere $x^2 + y^2 + z^2 = a^2$ and the plane $x+y+z = 0$.
]

#solution[
  #let ve = math.bold($e$)
  Consider a basis of the plane: $ve_1 = 1/sqrt(3) (1,1,1), ve_2 = 1/sqrt(2)(1,0,-1)$.

  Then $C : bold(x) = a cos theta ve_1 + a sin theta ve_2$ is a parameterization of $C$.

  #note[
    It's wiser to take advantage of the rotational symmetry within the curve.

    $ I &= 1/3 oint_C x y + y z + z x dif s \
    &= 1/6 oint_C (x+y+z)^2 - (x^2+y^2+z^2) dif s \
    &= -1/6 pi a^2. $
  ]
]

=== Harmonic Functions

Before we introduce the concept of harmonic functions, let's see some equalities on the boundary and interior of a domain.

#theorem[
  Let closed region $D$ be bounded by finitely many smooth curves, and $u, v in C^2(D)$. $vn$ is the unit normal vector of $diff D$. Then

  (1) $ iint_D laplace u dif x dif y = oint_(diff D) pdv(u,vn) dif s, $

  (2) $ iint_D v laplace u dif x dif y = oint_(diff D) v pdv(u,vn) dif s - iint_D grad u dot grad v dif x dif y, $

  (3) $ iint_D (u laplace v - v laplace u) dif x dif y = oint_(diff D) (u pdv(v,vn) - v pdv(u,vn)) dif s. $
] <boundary-interior-equalities>

#proof[
  (1) Let $bold(t)$ be the unit tangent vector of $L^+$ with direction cosines $cos alpha, cos beta$, then $bold(n) = (cos beta, -cos alpha)$. By the definition of directional derivative,

  $ oint_(L^+) v pdv(u,bold(n)) dif s &= oint_(L^+) (v cos beta pdv(u,x) - v cos alpha pdv(u,y)) dif s \
  &= oint_(L^+) (v pdv(u,x) dif y - v pdv(u,y) dif x) \ 
  &= iint_D pdv((v pdv(u,x)),x) + pdv((v pdv(u,y)),y) dif sigma ("by Green's theorem") \
  &= iint_D (pdv(v,x) pdv(u,x) + v pdv(u,x,2) + pdv(v,y) pdv(u,y) + v pdv(u,y,2)) dif sigma \
  &= iint_D v Delta u dif sigma + iint_D (pdv(u,x) pdv(v,x) + pdv(u,y) pdv(v,y)) dif sigma
  . $

  Rearranging the terms, we obtain the desired result.

  (2) Omitted, similar to (1)(3).

  (3) The same discussion as in (1),

  $ integral_(L^+) (u pdv(v,bold(n)) - v pdv(u,bold(n))) dif s & = integral_(L^+) (u pdv(v,x) - v pdv(u,x)) dif x + (u pdv(v,y) - v pdv(u,y)) dif y \
  &= iint_D (pdv(u,y) pdv(v,y) + u pdv(v,y,2) - pdv(u,y)pdv(v,y) - v pdv(u,y,2) \
  &- pdv(u,x) pdv(v,x) - u pdv(v,x,2) + pdv(u,x) pdv(v,x) + v pdv(u,x,2)) dif sigma \
  &= iint_D (u Delta v - v Delta u) dif sigma
  . $
]

#note[
  These are all direct consequences of the Green's theorem. However, when expressed in the language of field theory, they are more intuitive.

  $ oint_(diff D) vF dot vn dif s = iint_D div vF dif sigma ("Green"). $

  $ oiint_(diff Omega^+) vF dot vn dif S = iiint_(Omega) div vF dif V ("Gauss"). $ 

  $ oint_(diff S) vF dot dif vr = iint_S (curl vF) dot vn dif S ("Stokes"). $

  Based on these, a simpler proof can be given.
]

#proof[
  (1) $ "RHS" &= oint_(diff D) grad u dot vn dif s = iint_D div grad u dif sigma = "LHS". $

  (2) $ oint_(diff D) v grad u dif s &= iint_D div (v grad u) dif sigma \
  &= iint_D grad u grad v + v div grad u.
   $

  (3) Direct consequence of (2).
]

#definition[
  A function $u$ is called harmonic if it satisfies the Laplace equation $laplace u = 0$.
]

#theorem("Properties of Harmonic Function")[
  (1) Let $D$ be a domain in $RR^2$, and $u in C^2(D)$. Then $u$ is harmonic iff $u$ satisfies 

  $ oint_C pdv(u,vn) dif s = 0, $

  where $C subset D$ is a circle s.t. the interior of $C$ is in $D$.

  (2) Given the same conditions, $u$ is harmonic iff $u$ satisfies the mean value property:

  $ u(x_0,y_0) = 1/(2pi) integral_0^(2pi) u(x_0+r cos theta, y_0 + r sin theta) dif theta, $

  for all $P(x_0,y_0) in D$ and $0<r< op("dist")(P,diff D)$.

  (3) Let $D$ be bounded by finitely many smooth curves, and harmonic function $u$ on $D$. Then $u equiv 0$ if $u = 0$ on the boundary of $D$.

  (4) Let $L$ be simple closed curve in $RR^2$, and $u in C^2(D)$ be harmonic on $D$. Then $u$ reaches its maximum and minimum on $L$.
]

#proof[
  (1) Just a conclusion in @boundary-interior-equalities.

  (2) From (1), 
]

#question("An Exercise on Mean Value Property")[
  Let $u(x,y)$ be continuous on $RR^2$. Prove that 

  $ u(x,y) = 1/(pi r^2) iint_((x-xi)^2+(y-eta)^2<=r^2) u(xi,eta) dif xi dif eta, forall r > 0 $

  holds iff 

  $ u(x,y) = 1/(2 pi r) oint_(C_r(xi,eta)) u(xi,eta) dif s, forall r > 0. $
]

#proof[
  Unify the two equations by change of coordinates.

  $ pi r^2 u(x,y) &= int_0^(2pi) dif theta integral_0^r u(x - rho cos theta, y - rho sin theta) rho dif rho 
  . $

  Take the derivative of the equation above with respect to $r$.

  $ 2pi r u(x,y) &= integral_0^(2pi) u(x - r cos theta, y - r sin theta) r dif theta \
  &= oint_(C_r(xi,eta)) u(xi,eta) dif s. $
]

== More Exercises

#example("Green Formula with Singularities")[
  Solve for 

  $ I = oint_C e^x/(x^2+y^2) [(x sin y - y cos y) dif x + (x cos y + y sin y ) dif y], $

  where $C$ is a close curve enclosing the origin, oriented counterclockwise.
]

#solution[
  Note that $div vF = 0$, denote $L$ as a small enough circle with radius $r$ enclosing the origin, oriented clockwise. Then by Green's theorem,

  $ I &= oint_(C union L) - oint_(L) = 0 -(- int_0^(2pi) e^(r cos theta) cos (r sin theta) dif theta) \
  &= e^(theta_0 r cos theta_0) cos (r sin theta_0) dot integral_0^(2pi) dif theta ("MVT of Integral," theta in (0,1)) \
  &= 2pi e^(theta_0 r cos theta_0) cos (r sin theta_0)
  . $

  Because the integral is independent of $r$, we just take the limit as $r -> 0$. and $I = 2pi.$
]

== Appendix : Field Theory

#theorem("Gradient and Gauss Theorem")[
  #let vp = math.bold($p$)
  Let $M$ be a closed surface in $RR^3$ satisfying the conditions of the Gauss theorem, and $vn$ is the unit normal vector field of $diff M$, scalar field $u in C^1 (M, RR)$, a point $bold(p) in bar(M)$. Then

  $ grad u (bold(p)) = lim_(M -> bold(p)) 1/(op("Vol") (M)) oiint_(diff M) u vn dif sigma. $
]

#proof[
  Consider 

  $ oiint_(diff M) u vn dif sigma &= oiint_(diff M) (u cos alpha, u cos beta, u cos gamma) dot (cos alpha, cos beta, cos gamma) dif sigma \
  &= oiint_(diff M) u dif y dif z + u dif z dif x + u dif x dif y \
  &= iiint_M div u dif sigma ("Gauss"), $

  where $alpha, beta, gamma$ are the angles between $vn$ and the coordinate axes.

  Then $ div u(p) = lim_(M -> bold(p)) 1/(op("Vol") (M)) iiint_M div u dif sigma. $

  Then the conclusion follows.
]

=== Laplacian, Green Formula and Field Theory

#note[
  For curve integral, let $vn = (cos alpha, cos beta)$ be the unit normal vector of the curve $L$, then 

  $ cos alpha dif s = dif y, cos beta dif s = - dif x. $

  Then the curve integral of $vF$ along $L$ is

  $ oint_L vF dot vn dif s = oint_L P dif y - Q dif x. $
]

#corollary[
  $ int_U pdv(u,x_i) dif bold(x) = int_(diff u) u cos (vn_0, bold(e)_i) dif bold(s). $
]

#theorem("Integral by Parts, but Multiple")[
  $ iint_D P dot pdv(f,x) dif x dif y = int_(diff D) f dot P dif y - iint_D pdv(P,x) f dif x dif y. $

  $ iint_D Q dot pdv(f,y) dif x dif y = int_(diff D) f dot Q dif x - iint_D pdv(Q,y) f dif x dif y. $
]

#exercise[
  Let $D : x^2+y^2 = a^2$, $f(x,y)$ has continuous partial derivative on $D$, and $f(x,y) = 0$ on $diff D$. Prove that

  $
  I = abs(iint_D f(x,y) dif x dif y) <= (pi a^3)/3 max_((x,y) in D) abs(grad f).
  $
]

#proof[
  First notice similarity to the Cauchy inequality:

  $ x pdv(f,x) + y pdv(f,y) <= sqrt(x^2+y^2) ((pdv(f,x))^2+(pdv(f,y)^2))^(1/2). $

  To get LHS, integrate by parts:

  $ I = iint_D f(x,y) dif x dif y &= int_(diff D) f dif x - iint_D pdv(f,x) x dif x dif y \
  &= int_(diff D) f dif y- iint_D pdv(f,y) y dif x dif y \
  . $ 

  Because $f = 0$ on $diff D$, we have $ int_(diff D) f dif x = 0, int_(diff D) f dif y = 0. $

  Then 

  $
  I = -1/2 iint_D sqrt(x^2+y^2) dif x dif y max abs(grad f).
  $
]



= Differential Equations

== Existence and Uniqueness of Solutions

=== Picard Iteration

#proof[
  (1) 
  Construct a rectangle area $D = {(x,y) | |x-x_0| <= a, |y-y_0| <= b}$. Because $p(x)$ is continuous, $p(x)$ is bounded on $D$, i.e. $|p(x)| <= M$.
  
  $ derivative(y,x) = f(x,y) = p(x) cos^2 y - sin^2 y, \
  abs(pdv(f,y)) &= abs(-2p(x)sin y cos y - 2 sin y cos y) \
  &<= 2abs(p(x))+2 <= 2M+2. $

  Then $f(x,y)$ is bounded on $D$. By Lagrange Mean Value Theorem, for every $y_1, y_2 in D$,

  $ abs(f(x,y_1) - f(x,y_2)) = pdv(f,y) (x, xi) |y_1 - y_2| <= (2M+2) |y_1 - y_2|. $

  Then $f(x)$ is Lipschitz continuous on $D$. By Picard's theorem, the solution in $[x_0-h, x_0+h]$ exists and is unique, where $h = min(a, b/M), M = max abs(f(x,y))$.

  Consider the endpoint $x_0+h$, which is still in $D$. Then we can repeatedly apply Picard's theorem to get the solution in a larger interval.

  Thus we proved that the solution exists and is unique.

  (2) It's easily
]

== Exercises

#exercise[
  $ (x y-x^3 y^3) dif x + (1+x^2) dif y = 0. $
]

#solution[
  $y$: Divide both sides by $y^3$,

  $ 
  1/y^2 x dif x - x^3 dif x + (1+x^2) dif y/y^3 &= 0 \
  1/y^2 x dif x - x^3 dif x + (1+x^2) dif (1/y^2) &= 0\
  v x dif x - x^3 dif x + (1+x^2) dif v &= 0, v = 1/y^2. $

  Notice $dif (1/(1+x^2)) = - (2x)/(1+x^2)$, divide both sides by $(1+x^2)^2$,

  $
  v dif u + u dif v &= (1/u +1) dif u \
  dif (u v) &= (1/u + 1) dif u \
  v &= ln abs(u)/u + 1 + C/u.
  $
]

#let vy = math.bold($y$)
#let vxi = math.bold($xi$)

#let mA = math.bold($A$)
#let mB = math.bold($B$)
#let mJ = math.bold($J$)
#let mN = math.bold($N$)
#let mP = math.bold($P$)
#let mD = math.bold($D$)

== $n$-th Order Linear ODEs

=== When Coefficients are Constant

Let's begin from the simplest case where the coefficients are constant. 

From the perspective of linear algebra, we can consider the $n$-th order linear ODE in a elegant way:

#definition("Linear ODE")[
  Given the ODE

  $
  y^((n)) + a_(n-1) y^((n-1)) + ... + a_1 y' + a_0 y = 0,
  $

  when we denote $vy = (y,y',...,y^((n-1)))^T$, we can rewrite the ODE as

  $
  vy' = mA vy,
  $

  where $mA$ is the Frobenius matrix

  $
  mat(
    0,1,0,...,0;
    0,0,1,...,0;
    dots.v, dots.v, dots.v, dots.down, dots.v;
    -a_0,-a_1,-a_2,...,-a_(n-1)
  ).
  $
]

At the first glance, we might want to unify $vy'$ and $vy$ in both sides. Note that for normal functions, $e^(A x)$ does the job by $(e^(A x))' = A e^(A x)$. So a natural choice is to consider the exponential function of a matrix.

#definition("Matrix Exponential")[
  Given a matrix $mA$, the exponential of $mA$ is defined as

  $
  e^(mA) = I + mA + 1/2! mA^2 + 1/3! mA^3 + ...
  $

  where $I$ is the identity matrix.
]

We might wonder why the definition makes sence - after all, matrices and numbers are different things altogether. Using the theory of power series, we can show that the series converges for all matrices, omitting the proof here.

We see that $e^(mA x)$ is indeed a solution to the ODE $vy' = mA vy$. So the problem reduces to finding a simple form of $e^(mA x)$. Recall the theory of operators, $mA$ may be better to work with under a change of basis, giving us the Jordan form. Before that, we need the important property of the matrix exponential.

#theorem("Properties of Matrix Exponential")[
  The matrix exponential has the following properties:

  1. $e^(mP^(-1)mA mP) = mP^(-1) e^(mA) mP$ for any invertible matrix $mP$.
]

#proofsk[
  1. We can show that for every polynomial $f(x)$, $f(mP^(-1) mA mP) = mP^(-1) f(mA) mP$. The result follows by considering the power series of $e^(mA)$.
]

So we can work with the Jordan form $mJ = mP^(-1) mA mP$ instead of $mA$. The above property allows us to calculate like this:

$
e^(mA x) = e^(mP mJ x mP^(-1)) => e^(mA) mP = mP e^(mJ x).
$

Multiplying $mP$ to the right of the equation does not change the result, so the solution has a better form $mP e^(mJ x)$. The Jordan form is a block diagonal matrix, so we can calculate the exponential of each block separately.

Before considering the general case, we can consider the simplest case where $mA$ is diagonalizable.

#theorem[
  If $mJ = op("diag")(lambda_1, ..., lambda_n)$ is diagonal, let $mP = (vxi_1, ..., vxi_n)$ be the matrix of eigenvectors. Then

  $
  mP e^(mJ x) = e^(lambda_1 x) vxi_1 + ... + e^(lambda_n x) vxi_n.
  $

  Now $mP e^(mJ x)$ is a basic solution matrix to the ODE. And then we can extract $y$ from the first row of the matrix:

  $
  y(x) = c_1 e^(lambda_1 x) + ... + c_n e^(lambda_n x).
  $
]

When $mJ$ is a non-trivial Jordan form, we calculate $e^(mJ x)$ by considering the Jordan blocks.

#lemma("Exponential of Jordan Blocks")[
  Given a Jordan block

  $
  mJ = mat(
    lambda,1,0,...,0;
    0,lambda,1,...,0;
    dots.v, dots.v, dots.v, dots.down, dots.v;
    0,0,0,...,lambda
  ),
  $

  and a function $f(x)$, if $f(mJ)$ converges, then

  $
  f(mJ) = mat(
    f(lambda),f'(lambda),1/2! f''(lambda),...,1/(n-1)! f^((n-1))(lambda);
    0,f(lambda),f'(lambda),...,1/(n-2)! f^((n-2))(lambda);
    dots.v, dots.v, dots.v, dots.down, dots.v;
    0,0,0,...,f(lambda)
  ).
  $

  In particular, $e^(mJ)$ is calculated by the above formula:

  $
  e^(mJ) = mat(
    e^(lambda),e^(lambda) x,1/2! e^(lambda) x^2,...,1/(n-1)! e^(lambda) x^(n-1);
    0,e^(lambda),e^(lambda) x,...,1/(n-2)! e^(lambda) x^(n-2);
    dots.v, dots.v, dots.v, dots.down, dots.v;
    0,0,0,...,e^(lambda)
  ).
  $
]

#proofsk[
  By virtue of mathematical induction, we can show the fact
  $
  mJ^m = mat(
    lambda^m,binom(m,1) lambda^(m-1),binom(m,2)lambda^(m-2),...,binom(m,n-1) lambda^(m-n+1);
    0,lambda^m,binom(m,1) lambda^(m-1),...,binom(m,n-2) lambda^(m-n+2);
    dots.v, dots.v, dots.v, dots.down, dots.v;
    0,0,0,...,lambda^m
  ).
  $

  Then for polynomial $f$, the lemma is trivial; for others we might need to consider the power series of $f$, and the result follows.
]

Then

$
e^(mJ_i (lambda_i) x) = e^(lambda_i) (I + mN_i x + 1/2! mN_i^2 x^2 + ... + 1/(n-1)! mN_i^(n-1) x^(n-1)),
$

as a result, for every Jordan block $mJ_i$ of order $n_i$, we have a solution matrix block

$
mP_i e^(mJ_i x) = e^(lambda_i x) (vxi_1, x vxi_1 + vxi_2, ..., 1/(n_i-1)! x^(n_i-1) vxi_1 + ... + vxi_n_i),
$

corresponding to the solution family of dimension $n_i$:

$
y(x) = (a_0 + a_1 x + ... + a_(n_i-1) x^(n_i-1)) e^(lambda_i x).
$

The general solution is the linear combination of all solution families.

But for linear ODEs, things are actually simpler than this, because of the special structure of the matrix $mA$, a Frobenius matrix.

#theorem("Minimal Polynomial of Frobenius Matrix")[
  Given the Frobenius matrix $mA$, the minimal polynomial of $mA$ is the characteristic polynomial of $mA$.
]

#proof[
  See the book 谢启鸿.
]

This nice property promises that every eigenvalue only appears once in the Jordan form, so the approach to solve those ODE can be pretty mechanicized.

$
&"Every eigenvalue only appears once" \
<=>&"Eigen root " lambda_i "with multiplicity " n_i "gives a family of solutions" \
& (a_0 + a_1 x + ... + a_(n_i-1) x^(n_i-1)) e^(lambda_i x).
$

This is the general solution to the ODE, well-known as the characteristic equation method.

== Linear Operator $f(D)$

Denote the vector space of $n$-times differentiable functions by $C^n$. The differential operator $D : C^n -> C^0$ is defined as $D = derivative(,x)$. Given a polynomial $f(lambda)$, we can define the linear operator $f(D)$. Then the ODE becomes $f(D) y = 0$. Now it suffice to study the kernel of $f(D)$.

#lemma[
  $
  ker op("lcm") (f(x),g(x))(D) = ker f(D) + ker g(D).
  $
]

By the primary decomposition lemma, we factor $f(lambda)$ into irreducible polynomials

$
f(lambda) = (lambda-lambda_1)^(n_1) ... (lambda-lambda_k)^(n_k).
$



= Series

== Review

=== Uniform Convergence

Criteria : M-test, Abel, Dirichlet ($ser a_n (x) b_n (x)$).

=== Sufficienct Conditions for Commutative Operations

When is it possible to exchange

$
lim_(x->x_0), derivative(,x), integral_a^b dif x " and" lnf, sum_0^oo "?"
$

== Power Series $sum_0^oo a_n (x-x_0)^n$

#note("Questions of Interest")[
  - Region of convergence: find $E$ s.t. $ser0 a_n (x-x_0)^n " converges" <=> x in E$.
  - Exchangeability of operations: $
  lim_(x->x_0), derivative(,x), integral_a^b dif x " and" sum_0^oo.
  $
  - What functions $f(x)$ can be represented by power series? $
  f(x) = f(x_0) + ser f^((n)) / n! (x-x_0)^n, x in E.
  $
]

=== Radius of Convergence

#theorem("Power Series has a Radius of Convergence")[
  For $ser0 a_n x^n$, there exists a number $R in [0, +oo]$ such that

  i) The series converges absolutely for $abs(x) < R$.

  ii) The series diverges for $abs(x) > R$.

  iii) The series may either converge or diverge for $abs(x) = R$.
]

#proof[
  Let $
  R = sup{ abs(r) : ser0 a_n r^n " converges"},
  $

  then $forall x, abs(x) <R, exists r "s.t." ser0 a_n r^n " converges", abs(x) < abs(r) < R$.

  Convergence $=>$ boundedness, i.e. $abs(a_n r^n) <= M, forall n > N$.
  
  By the *comparison test*, $
  abs(a_n x^n) = abs(a_n r^n) (abs(x)/abs(r))^n => abs(a_n x^n) <= M (abs(x)/abs(r))^n ("converges").
  $

  This shows that the series converges absolutely for $abs(x) < R$. By definition, the series diverges for $abs(x) > R$.
]

#note($"When " abs(x) = R$)[
  The series may converge or diverge. E.g.
  $
  ser x^n/n^p, R = 1, E = cases(
    (-1,1)\, quad p = 0,
    [-1,1)\, quad p in (0,1],
    [-1,1]\, quad p > 1.
  )
  $
]

How to find the radius of convergence? The essence lies in the Cauchy-Hadamard formula.

#theorem("Cauchy-Hadamard Formula")[
  Given the power series $ser0 a_n x^n$, let

  $
  R = 1/(limsup_(n->+oo) root(n,abs(a_n))).
  $

  Then the radius of convergence is $R$.
]

#example[
  Recall the series $ser root(n, abs(a_n))$.
]

#corollary("Ratio Test Equivalent")[
  If $lnf abs(a_(n+1)/a_n) = l$, then

  $
  R = 1/l = cases(
    1/l\, l > 0,
    +oo\, l = 0,
    0\, l = +oo.
  ).
  $
]

#proof[
  Fix $x$, consider $b_n = abs(a_n x^n)$. Then by a ratio test, we have

  $
  lim_(n->+oo) b_(n+1)/b_n = abs(x) lim_(n->+oo) abs(a_(n+1)/a_n) = l abs(x).
  $

  Compare the above RHS with $1$.
]

#example[
  $
  ser 1/n^p x^n, ser x^n/sqrt(n!), ser n! x^n.
  $

  All of them have a radius of convergence $R = 1$.
]

#corollary[
  If $lnf root(n, abs(a_n)) = l$, then $R = 1/l$.
]

#proofsk[
  Fix $x$, $root(n, abs(a_n x^n)) = abs(x) root(n, abs(a_n)) -> l abs(x)$.
]

#example[
  $
  ser (3^n + (-2)^n)/n x^n, ser (3^n + (-2)^n)/n (x+1)^n.
  $
]

== Operations on Power Series

Before we start, let's discuss the properties of power series.

=== Sum and Product

#theorem[
  Given two power series $ser0 a_n x^n$ and $ser0 b_n x^n$, their sum and product are also power series. Let $R = min(R_a, R_b)$, then

  i) The sum $ser0 (a_n plus.minus b_n) x^n$ has a radius of convergence $R$.

  ii) The product $ser0 a_n x^n ser0 b_n x^n = ser0 c_n x^n$ has a radius of convergence $R$. $c_n = sum_(k=0)^n a_k b_(n-k)$.
]

#proofsk("Cauchy")[
  ii) By the property of absolute convergence, reordering the terms of the product series does not change the result. Let $ser u_n, ser v_n$ be absolute convergent series, then

  $
  sum u_n sum v_n = sum c_(i_k) d_(j_k),
  $

  where all $(i_k,j_k)$ are a permutation of $NN times NN$.

  $
  sum_0^N abs(c_i_k d_j_k) <= ser abs(c_n) ser abs(d_n).
  $
]

#example[
  Power Series of $1/((1-x)(2-x))$:

  - Sum of two series: $1/(1-x) - 1/(2-x)$.
  - Product of two series: $1/(1-x) dot 1/(2-x)$.
]

#example[
  $
  1/(1-x)^2 = ser0 x^n dot ser0 x^n = ser n x^(n-1), x in (-1,1).
  $
]

Given multiplication, how can we define division? See the following example:

#example("Bernoulli Numbers")[
  $
  x/(e^x-1) -> x = (e^x-1) ser B_n x^n/n!, B_0 = 1.
  $
]

=== Properties of Calculus Operations on Power Series

#theorem("Locally Uniform Convergence (-[-]-)")[
  Given a power series $ser0 a_n x^n$, the series converges uniformly on every compact subset of the interval of convergence.

  i.e. 
  i) $
  forall [a,b] "s.t." -R < a < b < R, ser0 a_n x^n arrows u(x) "on " [a,b].
  $
  ii) If $ser0 a_n R^n$ converges, then $ser0 a_n x^n arrows u(x) "on " [0,R]$.

  iii) If $ser0 a_n (-R)^n$ converges, then $ser0 a_n x^n arrows u(x) "on " [-R,0]$.
]

#proofsk[
  i) $
  abs(a_n x^n) <= abs(a_n) c^n, c = max(abs(a),abs(b)).
  $

  RHS is a convergent geometric series, by M-test, the series converges uniformly on $[a,b]$.

  ii) $
  ser0 a_n x^n = ser underbrace(a_n R^n, ser0 a_n R^n "uniformly converges") underbrace((x/R)^n, "monotone\n and is uniformly bounded"), abs(x/R) < 1.
  $

  The rest follows by Abel test of uniform convergence.

  iii) Similar to ii).
]

#theorem("Continuity of Power Series")[
  Let $ser0 a_n x^n$ be a power series with radius of convergence $R$. Then

  i) $ser0 a_n x^n$ is continuous on $(-R,R)$.

  ii) if $ser0 a_n x^n$ converges at $x =R$, then $ser0 a_n x^n$ is left-continuous at $x = R$.

  iii) if $ser0 a_n x^n$ converges at $x = -R$, then $ser0 a_n x^n$ is right-continuous at $x = -R$.
]

#proofsk[

]

#theorem("Integratability of Power Series")[
  Let $ser0 a_n x^n$ be a power series with radius of convergence $R$. Then

  $
  u(x) = ser0 a_n x^n " is integrable on " (-R,R),\ integral_0^x u(t) dif t = ser0 integral_0^x a_n t^n dif t = ser0 a_n x^(n+1)/(n+1).
   ("integrate termwise")
  $

  #note[
    $ser0 a_n x^(n+1)/(n+1)$ and $ser0 a_n x^n$ have the same radius of convergence. At the endpoints, $1/(n+1)$ gives us a sense of being smaller, hence being more possibly convergent. We'll discuss this later in the examples.
  ]
]

#proofsk[
  // TODO
  $
  limsup root(n, abs(a_n/(n+1))) = limsup root(n, abs(a_n)).
  $
]

#example($ln(1+x)$)[
  $
  1/(1+x) = 1/(1-(-x)) = ser0 (-x)^n, abs(x) < 1. \
  ln(1+x) = integral_0^x 1/(1+t) dif t = ser0 (-1)^n x^(n+1)/(n+1), abs(x) < 1.
  $
]

#solution[
  Because the alternating series $ser0 (-1)^n/(n+1)$ converges, $ser0 (-1)^n x^(n+1)/(n+1)$ is left-continuous at $x = 1$.
  
  At $x = -1$, the series $ser0 1/(n+1)$ diverges.
  
  So $ln(1+x) = ser0 (-1)^n x^(n+1)/(n+1)$ holds on $(-1,1]$.
]

#example($arctan$)[
  $ derivative(,x) arctan x = 1/(1+x^2) $

  $
  1/(1+x^2) = ser0 (-1)^n x^(2n) , abs(x) < 1. \
  forall x in (-1,1), arctan x = ser0 integral_0^x (-1)^n t^(2n) dif t = ser0 (-1)^n x^(2n+1)/(2n+1).
  $

  The series converges at $x = 1, -1$, so $arctan x = ser0 (-1)^n x^(2n+1)/(2n+1)$ holds on $[-1,1]$.

  $
  pi/4 = arctan 1 = ser0 (-1)^n/(2n+1).
  $
]

#theorem("Differentiating Termwise")[
  Let $ser0 a_n x^n$ be a power series with radius of convergence $R$. Then

  $
  u(x) = ser0 a_n x^n " is differentiable on " (-R,R),\ 
  derivative(,x) u(x) = ser0 derivative(,x) a_n x^n = ser0 n a_n x^(n-1). ("differentiate termwise")
  $
]

$
forall r <R, ser0 a_n x^n "converges in " (-R,R) \
and ser0 n a_n x^n "converges uniformly in " [-r,r].
$

The radius of convergence of $ser0 n a_n x^n$ is also $R$.

#corollary("Smoothness of Power Series")[
  $
  ser0 a_n x^n in C^oo (-R,R)
  $
]

#example[
  Prove that $forall x in (-1,1)$,
  $
  ser0 (n+1)(n+2) x^n = 2/(1-x)^3.
  $

  Reminder: dont be too rigid. Solve for
  $
  ser 1/(n(2n+1)) (2ser 1/(2n(2n+1)))
  $
]

== Solving for Infinite Sums

=== Abel Method

Based on Abel's Second Theorem, we can solve for a convergent series $ser a_n x^n$ by studying the power series $ser a_n x^n$, whose radius of convergence is at least $1$. If we are able to caluclate $S(x)$, then we can find the sum of the series by taking the limit $lim_(x->1^-) S(x) = S(1)$.

#example[
  $
  ser (cos n x)/n
  $
]

#solution[
  By Dirichlet test, the series converges when $x != 2k pi$. Then we only need to calculate the sum on $(0,2pi)$. By uniform convergence on compact subsets, $S(x)$ is continuous.

  Introduce variable $alpha in (-1,1)$, consider the power series $
  f(alpha) = ser (cos n x)/n alpha^n.
  $

  Differentiate termwise on $(-1,1)$, we have

  $
  f'(alpha) &= ser alpha^(n-1) cos n x = Re ser alpha^(n-1) e^(i n x) \
  &= Re (e^(i x))/(1-alpha e^(i x)) = Re (cos x-alpha)/(1-2 alpha cos x + alpha^2).
  $

  Integrate on $(-1,1)$ and notice $f(0)=0$, we have
  $ 
  f(alpha) = -1/2 ln(1-2 alpha cos x + alpha^2), alpha in (-1,1).
   $

  Then $
  S(x) = lim_(alpha -> 1^-) f(alpha) = -1/2 ln(1-2 cos x + 1) = - ln 2 - ln abs(sin x/2).
  $

  #note[
    Informally, we have
    $
    integral Re (e^(i x))/(1-alpha e^(i x)) dif alpha &= 1/2( integral e^(i x)/(1-alpha e^(i x)) dif alpha + "c.c.") \
    &= - 1/2 (integral 1/(alpha-e^(-i x)) dif alpha + "c.c.") \
    &= - 1/2 (ln(alpha-e^(-i x)) + ln(alpha-e^(i x))) \
    &= - 1/2 ln (alpha^2 - alpha (e^(i x) + e^(-i x)) + 1) = - 1/2 ln (1-2 alpha cos x + alpha^2).
    $
  ]
]

#note[
  From the example above, we see that trig functions are actually the real (imaginary) part of complex exponentials, so we may treat them as geometric series.
]

=== $Gamma$ and $Beta$ Functions

#example[
  Prove that
  $
  pi = ser0 (n!)^2/(2n+1)!2^(n+1). 
  $
]

#proof[
  Note that
  $
  Beta(n+1,n+1) = (n!)^2/(2n+1)! = 2 integral_0^(pi/2) (cos theta sin theta)^(2n+1) dif theta.
  $

  We have $
  ser0 (n!)^2/(2n+1)!2^(n+1) = 2 ser0 Beta(n+1,n+1) 2^(n+1) = 4 ser0 integral_0^(pi/2) cos theta sin theta (2 cos^2 theta sin^2 theta)^n dif theta.
  $

  Let $u_n = (2 cos^2 theta sin^2 theta)^n = (1-cos 2 theta)^n/4^n$, then $0<= u_n <= 1/2^n$. By the M-test, the series $ser0 u_n$ converges uniformly on $[0,pi/2]$, so by continuity we can exchange the sum and integral.

  $
  ser0 (n!)^2/(2n+1)!2^(n+1) &= 4 integral_0^(pi/2) ser0 cos theta sin theta (2 sin^2 theta cos^2 theta)^n dif theta = 4 integral_0^(pi/2) (sin theta cos theta)/(1-2 sin^2 theta cos^2 theta) dif theta \
  &= 2 integral_0^(pi/2) (dif sin^2 theta)/(2sin^4 theta-2sin^2 theta+1) = 2 integral_(-1)^1 (dif u)/(u^2+1) = pi.
  $
]

= Improper Integrals

== Exercises

#theorem("Frullani")[
  Let $f(x)$ be a continuous function on $(0, +oo)$, then

  $
  integral_0^(+oo) (f(a x)-f(b x))/x dif x = (f(0^+)-f(+oo))ln(b/a) quad (a>0,b>0).
  $

  Even if $f(0^+)$(or $f(+oo)$) does not exist, we may replace them with $0$ if

  $
  integral_k^(+oo) f(x)/x dif x "converges for some " k >= 0, \
  ("or" integral_0^k f(x)/x dif x "converges for some " k > 0).
  $
]

#proof[
  $
  lim_(t -> 0\ T->+oo) integral_t^T (f(a x)-f(b x))/x dif x 
  &=^(u=a x) lim integral_(a t)^(a T) f(u)/u dif u - lim integral_(b t)^(b T) f(u)/u dif u \
  &= lim integral_(a t)^(b t) f(u)/u dif u - lim integral_(a T)^(b T) f(u)/u dif u \
  &= lim f(xi_1) integral_(a t)^(b t) 1/u dif u - f(xi_2) integral_(a T)^(b T) 1/u dif u ("MVT") \
  &= (f(0^+)-f(+oo))ln(b/a) (xi_1->0^+, xi_2->+oo).
  $

  Suppose $f(+oo)$ does not exist, if $integral_k^(+oo) f(x)/x dif x$ converges, by Cauchy criterion, we have

  $
  forall epsilon > 0, exists A "s.t." forall T > A/a, abs(integral_(a T)^(b T) f(u)/u dif u) < epsilon.
  $

  Then we can show that the limit $
  lim_(T->+oo) integral_(a T)^(b T) f(u)/u dif u = 0.
  $
]

#example[
  $
  integral_0^(+oo) (sin a x sin b x)/x dif x.
  $
]

#solution[
  StackExchange: #link("https://math.stackexchange.com/questions/4436436/calculate-int-0-infty-frac-sinax-sinbxx-dx")[https://math.stackexchange.com/questions/4436436/calculate-int-0-infty-frac-sinax-sinbxx-dx]

  Note that $integral_1^(+oo) cos(x)/x dif x$ converges by Dirichlet's test. Then

  $
  I &= 1/2 integral_0^(+oo) (cos(a-b)x - cos(a+b)x)/x dif x \
  &= 1/2 f(0^+) ln (a+b)/(a-b) = 1/2 ln (a+b)/(a-b).
  $
]

= Fourier Series

== Exercises

#question[
  Let $f(x)$ be a $2pi$-periodic function with Fourier series
   $
  f(x) tilde a_0/2 + sum_(n=1)^oo (a_n cos n x + b_n sin n x),
  $

  then what's the Fourier series of $
  F(x) = 1/pi integral_(-pi)^(pi) f(t) f(x+t) dif t?
  $
]

#solution[
  Note that $
  F(x) = iprod(f(t), f(x+t)),
  $

  and because $
  g(t) = f(x+t) tilde a_0/2 + sum_(n=1)^oo (a_n cos n x + b_n sin n x) cos n t + (b_n cos n x - a_n sin n x) sin n t,
  $

  by Parseval's identity, we have

  $
  F(x) &= iprod(f(t), g(t)) \
  &= a_0^2/2 + sum_(n=1)^oo (a_n (a_n cos n x + b_n sin n x) + b_n (b_n cos n x - a_n sin n x)) \
  &= a_0^2/2 + sum_(n=1)^oo (a_n^2 + b_n^2) cos n x.
  $
]

#theorem[
  $f in C^k [-pi,pi]$, and $f^((k+1))$ is integrable or absolute integrable. Then the Fourier coefficients of $f$ satisfy
  $ 
  a_n, b_n = o(1/n^(k+1)).
   $
]

= Useful Integrals

== Trig Functions

#theorem[
  $
  2integral_0^(pi/2) (dif theta)/(A + B cos theta) = integral_0^pi (dif theta)/(A + B cos theta) = 1/2 integral_0^(2pi) (dif theta)/(A + B cos theta) = pi/sqrt(A^2-B^2), A>B>0.
  $
]

#proof[
  $
  I_1 &= integral_0^pi ((A - B cos theta) dif theta)/(A^2 - B^2 cos^2 theta) = integral_0^pi (A dif theta)/(A^2 - B^2 cos^2 theta) ("odd") \
  &= (integral_0^(pi/2) + integral_(pi/2)^(pi)) (A (tan^2 + 1) dif theta)/(A^2 tan^2 + (A^2-B^2)) = integral_(-oo)^(+oo) (A dif t)/(A^2 t^2 + (A^2-B^2)) \
  &= 1/sqrt(A^2-B^2) arctan u|_(-oo)^(+oo) = pi/sqrt(A^2-B^2).
  $
]