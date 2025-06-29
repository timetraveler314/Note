#import "@local/MetaNote:0.0.2" : *
#import "@preview/physica:0.9.0": *

#let detm = math.mat.with(delim: "|")

#show: doc => MetaNote(
  title: [
    Miscellaneous
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

= Sum of Binomial Coefficients

#let oint = math.integral.cont

#question[
  $
    sum_(i=0)^k ((-1)^i)/(i! (k-i+r)!) = (-1)^k/(k! (r-1)! (k+r))
  $
]

#proof[
  $
    "LHS" &= (-1)^k/((k+r)!) sum_(i=0)^k (-1)^i binom(k+r,i+r).
  $

  $
    sum_(i=0)^k (-1)^i binom(k+r,i+r)
    &= sum_(i=0)^k oint_(abs(z)=1) (-1)^i (1+z)^(r+k)/z^(i+r+1) (dif z)/(2 pi i) \
    &= oint_(abs(z)=1) (1+z)^(r+k-1)/z^r + (-1)^k (1+z)^(k+r-1)/z^(k+r+1) (dif z)/(2 pi i) \
    &= binom(r+k-1,r-1) + (-1)^k binom(k+r-1,k+r) \
    &= (r+k)!/(k! (r-1)! (k+r)).
  $
]

$
  norm(bold(W)bold(X)+bold(B))_F^2 &= tr(bold(W)bold(X)+bold(B))^top (bold(W)bold(X)+bold(B)) \
  &= tr(bold(X)^top bold(W)^(top) bold(W)bold(X)) + tr(bold(B)^top bold(B)) + tr(bold(W)bold(X))^top bold(B) + tr(bold(B)^top bold(W)bold(X)) \
$

$
  pdv(norm(bold(W)bold(X)+bold(B))_F^2,bold(W)) = 2 (bold(W) bold(X) + bold(B)) X^(top)
$