#import "@local/MetaNote:0.0.1" : *
#import "@preview/physica:0.9.0": *
#import "@preview/pinit:0.1.2": *

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

#show: doc => MetaNote(
  title: [
    Calculus (II) Problems
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

#let lnf = $lim_(n->+oo)$
#let ser = $sum_(n=1)^(oo)$

#outline()

= Differential Equations

#question[
  Does there exist a differentiable function $f(x,y,y')$ s.t. $y=sin x$ and $y=x-1/6 x^3$ are solutions to the differential equation $y'' = f(x,y,y')$?
]

#solution[
  Let $y' = p$. Then $
  derivative(,x) vec(y,p) = vec(p, f(x,y,p)).
  $

  Choose $y(0)= 0, p(0) = 1$, by the uniqueness of the solution, the answer is no.
]

#question("(Hard)")[
  Prove that $
  x''(t) + x(t) + arctan x(t) = 2 sin t
  $

  has no nontrivial solution of period $2pi$.
]

#proof[
  Hint. Multiply the equation by $sin t$ and integrate.

  Assume there exists a solution $x(t)$ of period $2pi$. Then $
  x'' sin t + x sin t + arctan x sin t = 2 sin^2 t.
  $

  Integrate by parts, $
  integral_0^(2pi) x'' sin t dif t &= x' sin t |_0^(2pi) (=0) - integral_0^(2pi) x' cos t dif t \
  &= - integral_0^(2pi) x sin t dif t - x cos t |_0^(2pi) (=0) \
  $

  Then $
  integral_0^(2pi) arctan x sin t dif t &= integral_0^(2pi) 2 sin^2 t dif t = 2pi \
  &= (integral_0^pi + integral_pi^(2pi)) arctan x sin t dif t \
  &< pi/2 integral_0^pi sin t dif t - pi/2 integral_pi^(2pi) sin t dif t = pi,
  $

  which is a contradiction.
]

= Series

== 1

#question("1")[
  Evaluate the following series:
  $
  ser 1/(n(n+1)(n+2)), ser arctan 1/(n^2+n+1)
  $
]

#solution[
  $
  arctan 1/(n^2+n+1) = arctan ((n+1)-n)/(1+n(n+1)) = arctan (n+1) - arctan n, \
  S_n = arctan(n+1) - arctan_1, ser arctan 1/(n^2+n+1) = pi/2 - pi/4 = pi/4.
  $
]

#question("2")[
  Let $a_n>0$, and ${a_n-a_(n+1)}$ be a strictly decreasing sequence. Show that if $ser a_n$ converges, then
  $
  lnf (1/(a_(n+1))-1/a_n) = +oo.
  $
]

#proof[
  $ser a_n$ converges, so $a_n -> 0$. Then $a_n - a_(n+1) -> 0$, so $
  a_n - a_(n+1) > 0, a_n > a_(n+1).
  $

  $
  a_n^2 &= sum_(k=n)^oo (a_k^2-a_(k+1)^2) = sum_(k=n)^oo (a_k-a_(k+1))(a_k+a_(k+1)) \
  &< (a_n-a_(n+1)) sum_(k=n)^oo (a_k+a_(k+1)).
  $

  $
  (1/(a_(n+1))-1/a_n) &= (a_n-a_(n+1))/(a_n a_(n+1)) > (a_n-a_(n+1))/a_n^2 > 1/(sum_(k=n)^oo a_k+a_(k+1)) -> +oo.
  $
]

#question("3")[
  Let $ser a_n$ be a divergent series of positive terms. Show that

  (1) $ser a_n/(1+a_n)$ diverges, $ser (a_n/(1+n^2 a_n))$ converges.

  (2) study the convergence of $ser a_n/(1+a_n^2), ser a_n/(1+n a_n)$.
]

#solution[
  $a_n/(1+n^2 a_n) <= 1/n^2 => ser a_n/(1+n^2 a_n)$ converges.

  If $ser a_n$ diverges, there are two possibilities:

  (i) $a_n$ is bounded by $M$, then $a_n/(1+a_n) > a_n/(1+M) > 0$, $a_n/(1+a_n^2) > a_n/(1+M^2) > 0$, so $ser a_n/(1+a_n), ser a_n/(1+a_n^2)$ diverges.

  (ii) $a_n$ is unbounded, then there exists a subsequence $a_(n_k) -> +oo$. Then the subsequence $a_n_k/(1+a_n_k) = 1/(1/a_n_k + 1) -> oo$, so $ser a_n/(1+a_n)$ diverges.

  As for $ser a_n/(1+a_n^2)$, we only have : when $a_n -> +oo$, $a_n/(1+a_n^2) ~ 1/a_n$, the convergence is uncertain. Example:

  $
  a_n = cases(
    n\, n = 2k-1,
    0\, n = 2k
  )"(diverges)", a_n = cases(
    n\, n = 2^k,
    0\, n != 2^k
  )"(converges)".
  $
]

#question("4")[
  $
  sum_(n=3)^oo 1/(n^alpha ln^beta n (ln n^gamma ln n)).
  $
]

#question("5")[
  Let $0<a_n<1$. Prove that if $ser a_n$ converges, then $ser ln(1-a_n)$ converges.
]

#proof[
  View as function $f(x) = ln (1-x)$. Then
  $
  f(x) - f(0) = f'(theta x)x = x/(1-theta x) <= x/(1-x), 0 < theta < 1. \
  => ln(1-a_n) <= a_n/(1-a_n).
  $

  Convergence of $ser a_n$ implies $a_n -> 0$. Then $exists N, forall n > N, 1-a_n > 1/2$. So $
  ln(1-a_n) < 2a_n, n > N.
  $

  Which means $ser ln(1-a_n)$ converges.
]

#question("7")[
  Show that $sum_(n=2)^oo 1/(ln n)^(ln n)$ converges.
]

#proof[
]

#question("8")[
  If $I = ser a_n$ is series of positive terms, show that $J = ser sqrt(a_n a_(n+1))$ converges, and the opposite is not necessarily true.
]

#proof[
  Counterexample: 
  $
  a_n = cases(
    1\, n = 2k-1,
    1/n^4\, n = 2k
  )
  $

  Then $J = 1/2 ser 1/n^2$ converges, but $I$ obviously diverges.
]

#question("9")[
  Discuss the convergence of the series
  $
  a_n = ((sqrt(n+sqrt(n+sqrt(n)))-sqrt(n))/n)^p,
  $

  $
  b_n = (1-root(3,(n-1)/(n+1)))^p (p>0).
  $
]

#solution[
  Asymptotically,

  $
  sqrt(n+sqrt(n+sqrt(n))) &= sqrt(n) (1 + sqrt(n+sqrt(n))/n)^(1/2) = sqrt(n) (1+1/2 sqrt(n+sqrt(n))/n + o(1/n^2)) \
  &= sqrt(n) + 1/2 + o(1/sqrt(n)). \
  a_n &= ((1/2 + o(1/sqrt(n)))/n)^p = 1/(2n)^p + o(1/n^(p+1)). ("Needs Recheck")
  $

  So $p > 1$ for convergence.

  $
  root(3,(n-1)/(n+1)) &= (1-2/(n+1))^(1/3) \
  &tilde 1 - 2/(3n) + o(1/n), \

  b_n &= (1-1+2/(3n) + o(1/n))^p = (2/(3n) + o(1/n))^p = 1/((3n)/2)^p + o(1/n^p).
  $
]

= Improper Integrals

#question[
  $
  integral_0^(+oo) 1/(1+x^(4)) dif x.
  $
]

#solution[
  $t := 1/(1+x^4)$.

  $
  I &= 1/4 integral_0^1 t^(-1/4) (1-t)^(-3/4) dif t \
  &= 1/4 Beta(1/4,3/4) = 1/4 (Gamma(1/4)Gamma(3/4))/Gamma(1) = pi/(2sqrt(2)).
  $
]

#proposition[
  $f(x)$ is monotone decreasing on $[0, +oo)$, $f(x) >= 0$, if $
  integral_0^(+oo) f(x) dif x
  $ converges, then $
  lim_(x->+oo) x f(x) = 0, lim_(x -> +oo) x ln x f(x) = 0.
  $
]

#proof[
  By Cauchy's criterion, for any $epsilon > 0$, there exists $N$, for any $n > N$, we choose $x/2 > N$,

  $
  epsilon > integral_(x/2)^x f(t) dif t >= f(x) x/2 => lim_(x->+oo) x f(x) = 0.
  $

  $
  epsilon > integral_(x_1)^(x_2) f(x) dif x &= integral_(x_1)^(x_2) x f(x) dif ln x \
  &>= (min_(x_1 <= x <= x_2) x f(x)) integral_(x_1)^(x_2) dif ln x = 0 \
  &"Choose" x_1 = sqrt(x), x_2 = x. \
  &= 1/2 x f(x) ln x.
  $
]

#question[
  Let $f(x)$ be monotone decreasing on $[1, +oo)$, $f(x) >= 0$, $f(x) -> 0$. Show that if $
  integral_1^(+oo) (f^(p-1)(x))/x^(1/p) dif x (p>1)
  $ converges, then $
  integral_1^(+oo) f^p (x) dif x
  $ converges.
]

#proof[
  Note all the integrand are positive, so we can apply the comparison test.

  $
  lim_(x -> +oo) 
  $
]

#question[
  Let $f(x)>=0$ be monotone increasing on $[0, +oo)$, and $F(x) = integral_0^x f(t) dif t$; $lim_(x -> 0^+) x/F(x) = 1$. Show that $
  I = integral_0^(+oo) 1/f(x) dif x "and" J = integral_0^(+oo) x/F(x) dif x
  $
  both converge or both diverge.
]

#proof[
  $
  & x/2 f(x/2) <= integral_(x/2)^x f(t) dif t <= F(x) <= x f(x) \
  =>& 2x/(2F(2x)) <= 1/f(x) <= x/F(x) 
  $
]

#question[
  Integrate

  $
  integral_0^(pi) 1/(a^2 sin^2 x + b^2 cos^2 x) dif x.
  $
]

#solution[
  $ 
  I &= 1/(a b) integral_0^(pi) (a/b dif (tan x))/((a/b tan x)^2 + 1) dif x \
  & "Let" t = a/b tan x, \
  &= 1/(a b) (integral_0^(+oo) + integral_(-oo)^0) 1/(t^2+1) dif t = pi/(a b).
   $

  #note[
    There's a singularity at $x = pi/2$, so we split the integral into two parts.
  ]
]

#lemma[

]

#question[
  Integrate
  $
  integral_0^1 (ln x)/(1-x^2) dif x.
  $
]

#solution[
  $
  I &= integral_0^1 ln x sum_(k=0)^(oo) x^(2k) dif x \
  &= sum_(k=0)^(oo) integral_0^1 x^(2k) ln x dif x \
  &= - sum_(k=0)^(oo) 1/(2k+1)^2 = -pi^2/8.
  $
]

#question[
  $
  I = integral_0^1 x^alpha ln^beta x dif x
  $

  When is $I$ convergent?
]

#solution[
  The singularities are $0,1$. We consider $
  I_1 = integral_0^(1/2) x^alpha ln^beta x dif x, I_2 = integral_(1/2)^1 x^alpha ln^beta x dif x.
  $

  For $I_1$, use $integral_0^1 x^gamma dif x$. By a ratio test,

  $
  (x^alpha ln^beta x)/(x^(alpha-epsilon)) = x^epsilon ln^beta x -> 0, x -> 0.
  $

  (We need the $epsilon>0$ to ensure the convergence of the ratio).

  Note that $integral_0^(1/2) 1/x^(epsilon-alpha) dif x$ converges iff $epsilon - alpha < 1 => alpha > -1$.

  For $I_2$, $
  x^alpha ln^beta x tilde x^alpha / (1-x)^(-beta), "because" \
  ln x = ln (1-(1-x)) tilde 1-x (x->1^-).
  $

  So $I_2$ converges iff $beta>-1$.
]

= Fourier Series

#question[
  $f(x) tilde a_0/2 + sum_(n=1)^(+oo) (a_n cos n x + b_n sin n x)$, show that 
  $ 
  ser a_n/n, ser b_n/n
   $

  both converge.
]

#proof[
  $
  ser abs(a_n/n) &<= ser (a_n^2+1/n^2)/2 \
  &<= 1/2 (a_0^2/2 + ser (a_n^2+b_n^2) + ser 1/n^2) \
  &<= 1/2 (norm(f)^2 + pi^2/6) < +oo. ("Bessel")
  $
]

