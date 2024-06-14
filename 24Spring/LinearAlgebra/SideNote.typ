#import "@local/MetaNote:0.0.1" : *
#import "@preview/commute:0.2.0": node, arr, commutative-diagram

#set text(font:("linux libertine", "FandolSong"), lang: "cn")

#let detm = math.mat.with(delim: "|")

#show: doc => MetaNote(
  title: [
    Linear Algebra Side Notes 2024
  ],
  authors: (
    (
      name: "timetraveler314",
      affiliation: "2024 Spring",
      email: "timetraveler314@outlook.com",
    ),
  ),
  doc,
)

#outline()

#let null = math.op("null")
#let range = math.op("range")
#let rank = math.op("rank")
#let lcm = math.op("lcm")
#let Hom = math.op("Hom")
#let opl = math.plus.circle

#let mA = math.bold($A$)
#let mB = math.bold($B$)
#let mC = math.bold($C$)
#let mD = math.bold($D$)
#let mI = math.bold($I$)
#let mJ = math.bold($J$)

= Matrices

== Blocked Matrices

=== Sylvester's Theorem

Sylvester's Theorem is a fantastic result using the technique of blocked matrices. The idea can be tweaked and applied to many other problems. Here are some examples.

#theorem("The First Rank Reduction Theorem")[
  Let $mA$ be invertible, then

  $ rank mat(mA,mB;mC,mD) = rank mA + rank mat(mD - mC mA^(-1) mB). $
]

#proof[
  Apply elementary blocked matrix operations to the matrix $mat(mA,mB;mC,mD)$:

  $ mat(mI,0;-mC mA^(-1),mI) mat(mA,mB;mC,mD) mat(mI,-mA^(-1) mB; 0, mI) = mat(mA,0;0,mD-mC mA^(-1)mB). $

  The result follows.
]

#theorem("The Second Rank Reduction Theorem")[
  Let $mA, mD$ be invertible, then

  $ rank mA + rank mat(mD - mC mA^(-1) mB) = rank mD + rank mat(mA - mB mD^(-1) mC). $
]

#proof[
  Similar to the first theorem.
]

#theorem("Sylvester's Inequality")[
  $ rank mA mB >= rank mA + rank mB - n. $
]

#proof[
  Apply the first rank reduction theorem, or use the trick on 

  $ mat(mA,0;mI,mB) -> mat(0,mA mB;mI, 0). $

  The result follows from $ rank mat(mA,0;mI,mB) >= rank mA + rank mB. $

  #note[
    This is a direct result of the Frobenuis Inequality.
  ]
]

#theorem("Frobenuis Inequality")[
  $ rank mA mB mC >= rank mA mB + rank mB mC - rank mB. $
]

#proof[
  $ mat(mA mB mC, 0; 0,mB)-> mat(mA mB mC, mA mB;0, mB) -> mat(0,mA mB; - mB mC, mB). $
]

As for eigenvalues and eigenvectors, we want to obtain the form $lambda mI - mA mB$, and this can be done similarly.

#theorem("Sylvester's Theorem for Eigenvalues")[
  Let $mA$ be an $m times n$ matrix, $mB$ be an $n times m$ matrix, and $m >= n$. We have

  $ abs(lambda mI_m - mA mB) = lambda^(m-n) abs(lambda mI_n - mB mA). $
]

#proof[
  A direct result of the first theorem when $lambda !=0$.

  When $lambda = 0$, it can either be done by the Cauchy-Binet formula or by the perbutation method.
]

The theorem reveals that $mA mB$ and $mB mA$ have the same non-zero eigenvalues with the same algebraic multiplicities. Furthermore, we can actually show that their geometric multiplicities are also the same.

#corollary[
  Let $mA$ be an $m times n$ matrix, $mB$ be an $n times m$ matrix. Then $mA mB$ and $mB mA$ have the same non-zero eigenvalues with the same algebraic and geometric multiplicities.
]

#proof[
  First theorem with $ mat(lambda mI_m,0;mB,lambda I_n-mB mA) <- mat(lambda mI_m,mA;mB,mI_n)->mat(lambda mI_m - mA mB, mA;0,mI_n). $

  $ n + (n- dim ker (lambda mI_n - mB mA)) = n + (n - dim ker (lambda mI_m - mA mB)). $
]

= Polynomial

== Coprime Polynomials and Linear Transformations

Coprime factorization of polynomials elicits the direct sum decomposition of the vector space. From the geometric perspective, this is the starting point of the Jordan Canonical Form.

Here are some results, all of which use the Bezout's Theorem:

#lemma[
  Let $f(x),g(x)$ be coprime polynomials, $mA$ be a matrix such that $f(mA) = 0$. Then $g(mA)$ is invertible.
]

#proof[
  By the Bezout's Theorem, we have $u(x) f(x) + v(x) g(x) = 1$. Then

  $ u(mA) f(mA) + v(mA) g(mA) = mI. $

  Given that $f(mA) = 0$, we have $g(mA) v(mA) = mI$, which implies that $g(mA)$ is invertible.
]

#theorem[
  Let $f(x),g(x)$ be coprime polynomials, $mA$ be a matrix of order $n$. Then

  $ f(mA)g(mA)=0 <=> rank f(mA) + rank g(mA) = n. $
]

#proof[
  $ 
  mat(f(mA),0;0,g(mA)) &-> mat(f(mA),f(mA)u(mA);0,g(mA)) -> mat(f(mA),mI;0,g(mA)) -> mat(f(mA),mI;-f(mA)g(mA),0) \ &-> mat(0,mI;-f(mA)g(mA),0) -> mat(f(mA)g(mA),0;0,mI).
   $

  The result follows.
]

This result is particularly useful when proving the diagonalizability of matrices that satisfy certain polynomial equations.

#question[
  Let $mA$ be an idempotent matrix, prove that $A$ is diagonalizable.
]

#proof[
  Let $f(x) = x^2 - x$. Then $f(mA) = 0$. By the previous theorem, we have $rank mA + rank (mA - mI) = n$. This implies that $mA$ is diagonalizable.
]

#question[
  Let $T$ be a linear transformation. Prove that

  $ ker gcd(f,g) (T) = ker f(T) sect ker g(T), \
  ker op("lcm")(f,g) (T) = ker f(T) + ker g(T).
   $
]

#proof[
  Let $beta in ker f(T) sect ker g(T)$, then by the Bezout's Theorem, we have $ u(x) f(x) + v(x) g(x) = gcd(f,g)(x). $
  Then
  $ u(T) f(T) beta + v(T) g(T) beta = gcd(f,g)(T) beta = 0, $

  which implies that $beta in ker gcd(f,g)(T)$.

  Let $beta in ker gcd(f,g)(T)$, then because $f = tilde(f) gcd(f,g)$, 

  $ f(T) beta = tilde(f)(T) d(T) beta = 0. $

  The result follows.
]

#proof[
  If $ v in ker (d tilde(f) tilde(g)) (T)$, then

  $ v &= (a tilde(f) + b tilde(g)) (T) v space ("Bezout") \
  &= underbrace(u(T) f(T) v, in ker g(T)) + underbrace(v(T) g(T) v, in ker f(T)).
   $
]

#example[
  If $P in Hom(V,V)$ is a projection s.t. $P^2 = P$. Then $V = ker P opl range P$.
]

#proof[
  From the perspective of space decomposition:

  #lemma[
    ($I-P$ is also a projection)

    $ ker (I-P) = im P. $
  ]

  Because $gcd(x,1-x) = 1, lcm(x,1-x) = x-x^2$, we have $V = ker P opl ker (I-P) = ker P opl im P$.
]

Generally, the similar decomposition can be applied like this:

#theorem[
  Let $f(x),g(x)$ be coprime polynomials, $phi$ be a linear transformation such that $f(phi)g(phi) = 0$. Prove that $V = V_1 plus.circle V_2$ where $V_1 = ker f(phi)$ and $V_2 = ker g(phi)$.
]

#proof[
  By assumption, there exists $u(x),v(x)$ such that $u(x) f(x) + v(x) g(x) = 1$. Then substituting $phi$ into the equation gives

  $ u(phi) f(phi) + v(phi) g(phi) = mI. $

  Then for any $alpha in V$, we have $alpha = u(phi) f(phi) alpha + v(phi) g(phi) alpha$. Note that 
  $ f(phi)u(phi) in ker g(phi), g(phi)v(phi) in ker f(phi), $
  
  we have $V = V_1 + V_2 $.

  By the last question, we have $V_1 sect V_2 = 0$. Therefore $V = V_1 plus.circle V_2$.
]

= Space Decomposition

In this section, we will discuss the decomposition of vector spaces. The main idea is to find a basis that can be used to represent the vector space in a more concise way. To begin with, we will consider the invariant subspaces of a linear transformation.

Before we start, let's recall our tools from the polynomial section.

#theorem[
  $f = f_1,...,f_k$ is coprime factorization, then

  $ ker f(T) = opl.big_(j=1)^k ker f_j(T). $
]

== Invariant Subspaces

Invariance $T(W) subset W$ induces the restriction of the linear transformation to the subspace $ T|_W : W |-> W, v |-> T v. $

Invariant subspace direct-sum decomposes the vector space in the following way.

#note("Invariant Subspace Decomposition")[
  $ V = W_1 opl ... opl W_k, $

  and $T|_W_j$ has matrix representation $[T]_j$ with respect to a basis of $W_j$. Then 

  $ T = op("diag")([T]_1, ..., [T]_k). $
]

=== Commutation and Invariance

#theorem[
  Let $T,S$ be linear transformations that commute, then

  $ ker T, range T $ are invariant under $S$.
]

We've got an important special case of this theorem where $S = f(T)$ is a polynomial of $T$. This is closely related to the decomposition by characteristic polynomials or sth else.

== Primary Decomposition

=== Null Space Stops Growing

#definition[
  $T in Hom(V,V)$ (finite dimensional). Define

  $ ker T^infinity = lim_(k->infinity) ker T^k = union.big_(k=1)^infinity ker T^k, \
  im T^infinity = lim_(k->infinity) im T^k = sect.big_(k=1)^infinity im T^k. $
]

#theorem("Null Space Stops Growing")[
  $ ker T subset ker T^2 subset ... \
  im T supset im T^2 supset ... $

  $ ker T^infinity = ker T^k, im T^infinity = im T^k $ for some $k$.
]

#theorem[
  The following statements are equivalent:

  (1) $V_1 = ker T^infinity, V_2 = im T^infinity$.

  (2) $V = V_1 opl V_2$, where $V_1,V_2$ are $T$-invariant subspaces s.t. $T|_V_1$ is nilpotent and $T|_V_2$ is invertible.
]

#proof[
  (1) If $v in V_1 sect V_2$, then there exists $w$ s.t. $v = T^k w$,

  Then $w in ker T^(2k) = ker T^infinity = ker T^k$. $v = T^k w = 0.$


]

#note[
  (2) shows a nice decomposition of the vector space to study the structure of the linear transformation, while (2)$=>$(1) means the only way to depict the vector space is to consider the null space and the range of the linear transformation.
]

=== Primary Decomposition

#theorem[
  If $W$ is invariant under $T$, then $W = opl.big ker (p_j (T)) sect W$.
]

#note("Projection onto Root Spaces")[
  Bezout's Theorem gives us a way to project onto the root spaces of the characteristic polynomial.

  $
  ker f(T) &= ker p_j (T) opl ker (f slash p_j) (T).
  $

  By Bezout's Theorem, we have $u(x) f/p_j (x) + v(x) p_j (x) = 1$. Then

  $ u(T) f/p_j (T) (x) + 0 = v in ker p_j (T) $

  Thus the projection is $u(T) f/p_j (T)$, which is a polynomial of $T$.
]

== Rational Canonical Form

=== Cayley-Hamilton Theorem

=== Cyclic Spaces

#definition("Krylov Space, or Cyclic Space")[
  $ K^m (v) = op("span")({v, T v, ..., T^(m-1) v}). $

  $ K^infinity (v) = union.big_(m=1)^infinity K^m (v). $

  They are also called cyclic spaces, generated by a single vector $v$.

  By finiteness, the union must stop as some point. If $m_0$ is the smallest integer s.t. $T^(m_0) v$ is a linear combination of $v, ..., T^(m_0-1) v$, then $K^infinity (v) = K^(m_0) (v)$, whereafter the sequence becomes stable. In fact, the vectors $v, ..., T^(m_0-1) v$ form a basis of $K^(m_0) (v)$.
]

It's easy to see that $K^m (v)$ is $T$-invariant. Moreover, under the induced basis, the matrix representation of $T$ is a companion matrix, whose minimal polynomial is the same as the characteristic polynomial.



= Diagonalization

== Simultaneous Diagonalization

#theorem("Simultaneous Diagonalization")[
  Let $T_1, ..., T_k$ be commuting linear transformations. Then there exists a basis s.t. $T_j$ is diagonal for all $j$.
]

#proof[
  By induction on $dim V$. Restricting $T$ to smaller spaces, we might find their common invariant subspaces.

  Take the eigen decomposition
  $
  opl.big ker (lambda I - T_j) = W_1 opl ... opl W_k, \
  $
   of $T_1$. By commutativity, *$W_j$ is $T_r$-invariant for all $r$*.

  Then $T_1|W, ..., T_k|W$ are diagonalizable (induction hypothesis). The result follows.
]

== Diagonalization of Tensor Product

#example[
  If $A,B in FF^(n times n)$ are diagonalizable, then

  $
  T in Hom(FF^(n times n), FF^(n times n)) : X |-> A X B
  $

  is diagonalizable.
]

#let oti = math.times.circle

#proof[
  $
  [T] = B^T oti A \
  (P oti Q)^(-1) [T] (P oti Q) = (P^(-1) B^T Q) oti (P^(-1) A Q) = D_1 oti D_2 = D.
  $

  Alternative: $T = L_A R_B$ where $L_A, R_B$ are left and right multiplication operators. The two multiplication operators are commutative, so it suffices to diagonalize them separately (because they are simultaneously diagonalizable, the $P^(-1)$ and $P$ in the middle cancel out).
]

= Commutativity

== Commutating Linear Transformations

#theorem[
  Let $T,S$ be commuting linear transformations. Then

  $
  ker (T - lambda I)^infinity "is invariant under" S.
  $
]

Choosing a basis s.t. $T$ is Jordan form $op("diag")(J_1,dots,J_n)$, then the matrix representation of $S$ is block diagonal with respect to the Jordan blocks, and $S_i J_i = J_i S_i$.

= Miscellaneous

== Minimal Polynomial

#question[
  If the minimal polynomial of $mA in CC^(n times n)$ is $m(lambda) = product (lambda - lambda_i)^(k_i)$. Prove that the minimal polynomial of $mB = mat(mA,mI;0,mA)$ is $product (lambda - lambda_i)^(k_i+1)$.
]

#proof[
  Note that $mB^t = mat(mA^t,t mA^(t-1);0,mA^t)$, we have$
  f(mB) = mat(f(mA),f'(mA);0,f(mA)), "where " f "is a polynomial".
  $

  Denote $g(lambda)$ as the minimal polynomial of $mB$. Then $g(mB) = 0$ implies that $g(mA) = 0, g'(mA) = 0$. Then $m | g, m | g'$.

  By $m | g$, we have $g = m p$, and $m | g' = m p' + m' p$, then $m | m' p$. Consider every factor $(lambda - lambda_i)^(k_i)$ in $m$, we know that $
  (lambda - lambda_i)^(k_i-1) || m'.
  $

  Therefore, the minimal $p = product (lambda - lambda_i)$, which implies that the minimal polynomial $g = product (lambda - lambda_i)^(k_i+1)$.
]
