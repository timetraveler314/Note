#import "@local/MetaNote:0.0.1" : *

#show: doc => MetaNote(
  title: [
    Types and Programming Languages
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

#let vd = sym.tack.r

= References

#exerciseb("13.4.1")[
  Find a term whose evaluation will create a cyclic structure in the store.
]

#solution[
  Let's consider the following term:

  ```ml
  let r1 = ref (\x:Nat. x) in
  let r2 = ref (\x:Nat. (!r1) x) in
  (r1 := \x:Nat. (!r2) x);
  r2
  ```
]

#exerciseb("13.5.2")[
  Give an example of a store $mu$ which is well typed with respect to two different store typings $Sigma_1$ and $Sigma_2$, i.e. $
  Gamma | Sigma_1 tack mu "and " Gamma | Sigma_2 tack mu.
  $
]

#solution[
  Let $mu$ be a store with a single location $ell$:

  $
  mu = (ell |-> "\x:Unit. (!"ell") x"),
  $

  and $Gamma$ be the empty context. Then $mu$ is well typed with respect to the following store typings:

  $
  Sigma_1 &= (ell: "Unit" -> "Unit"), \
  Sigma_2 &= (ell: "Unit" -> ("Unit" -> "Unit")).
  $

  #note[
    The key is some sort of recursion achieved by referencing oneself in the store. To prevent 
  ]
]