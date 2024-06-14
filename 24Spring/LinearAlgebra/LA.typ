#import "@local/MetaNote:0.0.1" : *
#import "@preview/commute:0.2.0": node, arr, commutative-diagram

#let detm = math.mat.with(delim: "|")

#show: doc => MetaNote(
  title: [
    Linear Algebra A (II) Class Notes
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

#let ve = math.bold($e$)
#let opl = math.plus.circle
#let lcm = math.op("lcm")
#let ip(x,y) = $lr(angle.l #x, #y angle.r)$
#let Hom = math.op("Hom")

#outline()

= Vector Spaces

== Operations on Subspaces

#theorem[
  Let $V_1,dots,V_n$ be proper subspaces of a vector space $V$ over an infinite field $FF$. Then the intersection $ V_1 union dots union V_n != V. $
]

#proof[
  (i) First consider the case where $n=2$. Choose $v_1 in V_2 backslash V_1, v_2 in V_1 backslash V_2$. We show that $v = v_1 + v_2 in.not V$.

  Suppose not. If $v in V_1$, then $v_1 = v - v_2$ in $V_1$, a contradiction. Similarly, if $v in V_2$, then $v_2 = v - v_1$ in $V_2$, a contradiction. Thus $v in.not V$.

  (ii) (Vandermonde's Determinant) For general $n in NN$:

  Let $v_i in V backslash V_i, i = 1, dots, n$. We manage to find a linear combination of them that is not covered by the union of $V_i$.

  Consider $u_a = sum_(i=1)^m a^(i-1)v_i, a in FF$. Here, $op("char") FF = 0$. So there exists $V_k$ s.t. $u_a in V_k$ for infinitely many $a$.

  WLOG, assume $u_(a_1),dots,u_(a_m) in V_k$, where $a_i$ are distinct. It suffices to show that $v_k in op("span"){u_(a_1),dots,u_(a_m)} subset V_k$, which leads to a contradiction.

  To obtain $v_k$, consider linear combinations of $u_(a_i)$. We have a Vandermonde matrix:

  $ (u_(a_1),dots,u_(a_m)) vec(x_1,dots,x_m) = v_k
  \ <=> (v_1,dots,v_m) underbrace(mat(1,1,dots,1;a_1,a_2,dots,a_m;dots.v,dots.v,dots.down,dots.v; a_1^(m-1),a_2^(m-1),dots,a_m^(m-1)) vec(x_1,dots.v,x_m)) = v_k
  $

  Letting the underbraced part be $vec(0,dots.v,1 (k-"th"), dots.v,0)$, we have a linear combination of $u_(a_i)$ that equals $v_k$. This is guaranteed by the Vandermonde determinant being nonzero, which gives us a unique solution for $vec(x_1,dots,x_m)$.
]

== Sum of Subspaces

#note[
  The sum $limits(plus)_(i in cal(I)) V_i$ of subspaces $V_i$ is the smallest subspace containing all $V_i$. This is the core idea of the sum.
]

After introducing the operation $+$, we want to check whether the new operation behaves well with respect to the old operations $union$ and $sect$. Here, distributivity does not hold in general, but we have the following result.

#theorem[
  Let $X,Y,Z$ be subspaces.

  (i) $(X sect Z) + (Y sect Z) subset (X+Y) sect Z$,

  (ii) $(X sect Y) + Z subset (X+Z) sect (Y+Z)$.
]

#proof[
  (i) $ X subset X+Y => (X+Y) sect Z subset X sect Z. $

  Similarly, $ Y sect Z subset (X+Y) sect Z. $

  (ii) $ X sect Y subset X+Z, Y sect Z subset Y+Z. $
]

// #proof[
//   记 $d(x) = gcd(f(x),g(x)), f'(x) = f(x)/d(x), g'(x) = g(x)/d(x)$. 我们来考虑 $f'$和$g'$.

//   存在性. 由Bezout定理，存在$h(x),k(x)$使得
//   $ f' h + g' k = 1. $

//   对$h$做带余除法，得到 $h(x)=p(x) g'(x) + u(x)$,其中 $deg u(x)< deg g'(x)$. 代入上式得到
//   $ f' u + g' (p f' + k) = 1. (1)$

//   记 $v(x) = p(x) f'(x) + k(x)$. 断言 $deg v(x) < deg f'(x)$. 若不然，(1)式中 $deg f'(x)u(x) < deg g'(x)v(x)$，二者相加比较次数可知不能成立.

//   故存在 $u(x),v(x)$使得 $f' u + g' v = d$ 且 $deg u < deg g'$, $deg v < deg f'$.

//   唯一性. 若存在 $u',v'$使得 $f' u' + g' v' = d$ 且 $deg u' < deg g'$, $deg v' < deg f'$, 则 $f' (u-u') = g' (v-v')$. 由于 $f',g'$互素，故 $u-u'$是$g'$的倍数，$v-v'$是$f'$的倍数. 由于次数限制，$u-u'=0,v-v'=0$.

//   故存在唯一的 $u,v$ 满足条件 $ f' u + g' v = 1$，这等价于存在唯一的 $u,v$ 满足条件 $ f u + g v = d$.
// ]

= Linear Mappings

#note("Linear Mappings and Matrices")[
  Given $T: V -> W$, choose bases ${e_1, dots, e_n}$ and ${eta_1, dots, eta_m}$ for $V$ and $W$ respectively.

  We say $A$ is a matrix representation of $T$ if 
  $ T(e_1,dots,e_n) = (eta_1,dots,eta_n) A. $

  Specially, let $T$ be a linear mapping from $V$ to itself. Then $A$ is a matrix representation of $T$ with respect to the same basis.

  When basis changes: ${e_1,dots,e_n} -> {f_1,dots,f_n}$, the transition matrix $P$ is defined by

  $ (f) = (e) P. $

  Then the matrix representation of $T$ with respect to the new basis is given by $B=P^(-1) A P$:

  $ T (f) P^(-1) = (f) P^(-1) A => T(f) = P^(-1) A P. $

  Generally, $B=Q^(-1) A P$.
]

== Kernel and Image

#question[
  Let $S,T$ be subspaces of $V$. Show that 

  $ (S+T) slash S tilde.eq T slash (S sect T).  $
]

#proof[
  #note[
    Upon seeing isomorphism of quotient spaces, we should consider the first isomorphism theorem.
  ]

  Consider the mapping $ phi : S+T -> T slash (S sect T), s + t |-> t + (S sect T). $

  Its linearity is clear. Now for any $v = s + t in ker phi$, $ t + (S sect T) = 0 + (S sect T) <=> t in S sect T <=> t in S <=> v in S. $

  Thus $ ker phi = S$. By the first isomorphism theorem, $ (S+T) slash S tilde.eq T slash (S sect T). $
]

#corollary[
  $ phi(U) tilde.eq U slash (U sect ker phi). $
]

== Minimal Polynomial and Characteristic Polynomial

#theorem("Primary Decomposition")[
  Consider factorization over $FF$.

  Let $m_phi = p_1^(r_1) dots p_k^(r_k)$ be the factorization of the minimal polynomial of $phi$. Then

  $ V = plus.circle.big ker p_i^(r_i). $

  Let $f_phi = p_1^(s_1) dots p_k^(s_k)$ be the factorization of the characteristic polynomial of $phi$. Then

  $ V = plus.circle.big ker p_i^(s_i). $

  They are both the primary decomposition of $V$.
]

Denote $K(f)$ by the kernel of $f(phi)$.

#theorem("Projection Map as Polynomials")[
  Let $phi : V -> V$ be a linear mapping. Then the projection map $pi_i : V ->ker p_i^r_i$ is a polynomial of $phi$.
]

#proof[
  The case when $k=1$ is trivial. We prove the general case where $k>2$.

  Let $g_j = p_1^(r_1) dots hat(p)_(j)^(r_(j)) dots p_k^(r_k)$. Then $ K(g_j) = ker g_j (phi) = union.big_(t !=j) ker p_t^(r_t). $

  We see that all $g_j$ are coprime. By Bezout's identity, there exist $h_j$ s.t. 

  $ h_1 g_1 + dots + h_k g_k = 1. $

  Let $x = x_1 + dots + x_k, x_j in ker p_j^(r_j)$. Then $ sum_j x_j = x &= sum_j h_j (phi) g_j (phi) (x) \
  &= sum_(j,t) h_j (phi) g_j (phi) (x_t) \
  &= sum_j h_j (phi) g_j (phi) x_j ("Because" K(g_j) = ker g_j (phi) = union.big_(t !=j) ker p_t^(r_t)). \
  $ 

  Notice the primary decomposition is a direct sum. Then $ x_j = (h_j dot g_j)(phi) x_j, j = 1, ...,k $
  
  This shows that $pi_i = h_i (phi) g_i (phi)$.
]

#example[
  Let $phi in cal(L) (V)$ be diagonalizable. If $W$ is a $phi$-invariant subspace, then $phi|_W$ is also diagonalizable.
]

#proof("1")[
  + Expand a basis $w_1,dots,w_m$ of $W$ to a basis $w_1, dots, w_n$ of $V$.

  Then $ phi(w_1,dots,w_m) = (w_1,dots,w_n) mat(A_1,A_2;0,A_3), $

  where $A_1$ is the matrix representation of $phi|_W$.

  Note that $ mat(A_1,A_2;0,A_3)^k = mat(A_1^k,*;0,A_3^k), $

  This shows that for any polynomial $f$, $f(A) = mat(f(A_1),*;0,f(A_3))$.

  - $phi$ is diagonalizable, so $m_A$ is a product of distinct linear factors.

  $m_A (A) = 0 => m_A (A_1) = 0$, so $m_A_1 | m_A$, which shows that $m_A_1$ is a product of distinct linear factors $=>$ diagonalizable.
]

#proof("2")[
  By factorizing the space.

  $ V = plus.circle.big V_lambda_i (phi) $

  In fact, $W = plus.circle.big (W sect V_lambda_i(phi))$. For all $w in W$, $w = w_1 + ... + w_i, w_k in V_lambda_k$. We prove that $w_i in W$. 

  Consider the projection $p_i : V -> V_lambda_i$,* $p_i$ is a polynomial of $phi$*. 

  $ w_i = p_i(w) = g_i(phi) (w) in W (W "is " phi"-invariant"). $

  The decomposition $W = plus.circle.big (W sect V_lambda_i(phi))$ gives 
]

#example[
  Let $A,B$ be diagonalizable, $A B = B A$. Show that $A,B$ is simultaneously diagonalizable.
]

#proof[
  Let $V_lambda_i$ be the eigenspace of $A$ corresponding to $lambda_i$. Then $V_lambda_i$ is $B$-invariant.

  $B$ is diagonalizable on $V_lambda_i$, so $V_lambda_i$ is the direct sum of eigenspaces of $B$.

  $V = plus.circle.big V_lambda_i$ is the direct sum of eigenspaces of $B$. This shows that $A,B$ is simultaneously diagonalizable.
]

Actually, the primary decomposition is not strong enough. When we expand the field to $CC$, we may get more information.

#note("Space Decompositions")[
  + Primary Decomposition $V = plus.circle.big V_lambda_i (phi)$
  + Cyclic Subspace Decomposition
  + Irreducible $phi$-invariant Decomposition
]

== Cyclic Spaces

Consider the Frobenius matrix

$ A =  mat(0,0,...,0,-a_0;1,0,...,0,-a_1;0,1,...,0,-a_2;0,0,...,1,-a_(n-1)) $

Then $A ve_1 = ve_2, A ve_2 = ve_3, dots, A ve_(n-1) = -a_(n-1) ve_n, A ve_n = -a_0 ve_1 - a_1 ve_2 - dots - a_(n-1) ve_(n-1) $.

We see that a basis can be $ve_1, A ve_1, A^2 ve_1, dots, A^(n-1) ve_1$. This is such a good property that we want to generalize it.

#definition("Cyclic Spaces")[
  Let $phi : V->V, xi in V$. Let 

  $ W = angle.l xi, phi(xi), phi^2(xi), dots, phi^(n-1)(xi) angle.r . $

  $W$ is a $phi$-invariant subspace of $V$ generated by $xi$. We call $W$ a $phi$-cyclic subspace of $V$ generated by $xi$.
]

What is the minimal polynomial of $phi|_W$? How do we construct a basis for $W$?

While trying to construct the maximum number of linearly independent vectors, we may encounter the following problem:

$ a_1 xi + a_2 phi(xi) + dots + a_(n-1) phi^(n-2)(xi) = a_n phi^(n-1)(xi). $

This is equivalent to finding $f(x) in FF[x], f(phi) = 0$. This reduces to finding an annihilating polynomial of $xi$ s.t. $ f(phi)xi = 0$.

Of all the polynomials, the monic polynomial of the smallest degree is unique. Thus we can define the minimal annihilating polynomial of $xi$.

#lemma[
  Let $xi != 0$. If the minimal annihilating polynomial of $xi$ w.r.t. $phi$ is $f(x)$, Then

  $ xi, phi(xi), dots, phi^(deg f - 1)(xi) $ is a basis of $W$.

  A corollary: $dim W = deg m_xi (x)$.
]

#proof[
  Assume there exists some $b_i !=0$ s.t.

  $ b_0 xi + b_1 phi(xi) + dots + b_(deg f - 1) phi^(deg f - 1)(xi) = 0. $

  Then $b_0 + b_1 x + dots + b_(deg f - 1) x^(deg f - 1) != 0$ is an annihilating polynomial of $xi$ with degree less than $deg f$, a contradiction. 
]

We call $m_xi, m_phi$ both "annihilating". What is the relationship between them?

#theorem("Annihilating Polynomials")[
  $ m_xi | m_phi. $
]

Can they be the same?

#lemma("Steps towards Cyclic Decomposition (Hard)")[
  (1) $exists xi in V$ s.t. $m_xi = m_phi$. (An unique $xi$ that cyclically generates $V$)

  (2) $exists U$ s.t. $U$ is $phi-$invariant, and

  $ V = angle.l xi,dots,phi^(s-1) (xi) angle.r plus.circle U. $
]

#note[
  (2) tells us that the complement of the cyclic subspace is still $phi-$invariant. Now go on with $U$ till $U = {0}$, then we get the cyclic decomposition.

  After this, we get a basis of $V$ with nicer properties compared to the primary decomposition.
]

By virtue of dual spaces, we may prove the result in a more general setting.

#proof[
  (1) Let $m_phi = p_1^(r_1) ... p_s^(r_s)$.

  i. $s=1$. Then $m_phi = p^s, p$ is irreducible. By the minimality of $s$, $exists xi, p^(s-1) (phi) (xi) !=0$. 

  By $m_xi | m_phi$, $m_xi = p^k, k<=s$. If $k<s$, then $p^k (phi) (xi) = 0$, a contradiction. Thus $k=s$.

  ii. $s>=2$. By primary decomposition,

  $ V = ker p_1^(r_1) (phi) plus.circle ker p_2^(r_2) (phi) plus.circle ... plus.circle ker p_s^(r_s) (phi). $

  *Consider the restriction map $phi|V_i$.* The minimal polynomial of $phi|V_i$ is $p_i^(r_i)$. By i., $ exists xi_i in V_i, m_xi_i = p_I^(r_i). $

  *Construct $xi = sum xi_i$.* We show that $m_xi = m_phi$.

  By definition, $m_xi (phi) (sum xi_i) = sum m_xi (phi) (xi_i) = 0$. Each term $m_xi (phi) (xi_i) in V_i$. Utilize the *direct sum* property, $m_xi (phi) (xi_i) = 0$. Thus $m_xi_i | m_xi$. Because $p_i$ are coprime, $m_phi | m_xi => m_phi = m_xi$.

  (2) (GTM 23, last chapter).
]

Apply the lemma repeatedly, we get the cyclic decomposition.

How to prove that a space is cyclic?

#theorem[
  $W$ is cyclic iff $dim W = deg m_(phi|_W)$.
]

== Irreducibility

#definition("Irrreducible")[
  $V$ is called $phi$-irreducible if $V != V_1 plus.circle V_2 $, where $V_1, V_2$ are $phi$-invariant subspaces of $V$.
]

#theorem[
  $V$ is $phi$-irreducible $<=>$ $V$ is $phi$-cyclic, $m_phi = f^k, k>=1$ ($f$ is irreducible).
]

#proof[
  $=>$: Let $m_phi = f_1^(k_1) ... f_s^(k_s)$ be the irreducible factorization of $m_phi$.

  Then $V = plus.circle.big ker f_i^(k_i)$. Because $ker f_i^(k_i)$ is $phi$-invariant, $V$ is not $phi$-irreducible if $s>=2$. Thus $s=1$.

  By the cyclic lemma, $exists xi in V$ s.t. $m_xi = m_phi = f^k$. Then $W = angle.l xi, phi(xi), dots, phi^(k-1)(xi) angle.r$ is $phi$-cyclic.

  Moreover, by irreducibility, $W = V$.

  $arrow.l.double$: Proof by contradiction. Let $V = V_1 opl V_2$, $V_1, V_2$ are $phi$-invariant. Then $m_phi = lcm(m_(phi|_V_1), m_(phi|_V_2))$. WLOG, we have $m_(phi|_V_1) = f^k = m_phi$. By analyzing the dimension, we get a contradiction.
]

Hence we are able to determine whether a space is irreducible while decomposing it. Then any $V$ must have a decomposition into irreducible cyclic subspaces.

Diving into the irreducible subspaces, we can give a concrete characterization.

For each irreducible space, let $e$ be the cyclic element, $ m_phi = f^k \ f(phi) = phi^p + a_(p-1) phi^(p-1) + dots + a_1 phi + a_0 = 0. $

Utilizing the relation, we can construct a basis of $V$.

$
e, &phi_e, &&..., &&&phi^(p-1) e, \
f(phi)_e, &f(phi)phi(e), &&..., &&&f(phi)phi^(p-1)(e), \
f^2(phi)_e, &f^2(phi)phi(e), &&..., &&&f^2(phi)phi^(p-1)(e), \
&&dots \
f^(k-1)(phi)_e, &f^(k-1)(phi)phi(e), &&..., &&&f^(k-1)(phi)phi^(p-1)(e).
$

The $k p$ elements together form a basis. Let's prove it.

#proof[
  $M$ denotes the space spanned by the above $k p$ elements.

  It suffices to show $phi(M) subset.eq M$ because of irreducibility. (If there is more than one invariant subspace, $M$ won't be irreducible)

  By direct calclation, ...
]

The matrix of $phi$ under this basis is a block matrix

$
mat(F,,;A,F,;,A,F), F = mat(0,0,...,0,-a_0;1,0,...,0,-a_1;0,1,...,0,-a_2;0,0,...,1,-a_(p-1)), A = mat(0,0,...,1;0,0,...,0;dots.v,dots.v,dots.down,dots.v;0,0,...,0)
$

#example("Jordan Normal Form")[
  When $FF=CC$, every polynomial can be completely factored, giving fine enough matrix as Jordan blocks. $m_phi = (x-a)^k =>$ $mat(a;1,a;,1,a;,,dots.down,dots.down;,,,1,a;)$
]

#example[
  When $FF=RR$, $m_phi (x) = (x^2+a x+b)^k$, $F = mat(0,-b;1,-a)$. 
]

#example[
  $phi : V->V, m_phi (x) = f^k, f(x)$ is irreducible.
]

#solution[
  (1) $m_phi = f$. $V = opl.big V_i$, $m_(phi|_V_i) = f$.

  Then $V$ can be decomposed into $(dim V) / (deg f)$ irreducible subspaces.

  (2) 
]

== Appendix : Linear Maps on Matrix Spaces

#let tov = math.op("vec")
#let oti = math.times.circle

#example[
  Let $A in FF^(m times n), B in FF^(p times q)$, consider $ T : X in FF^(n times p) |-> A X B in FF^(m times q). $

  It's easy to check that $T$ is linear. What is the matrix representation of $T$?
]

Consider the vectorization of matrices.

#definition("Vectorization")[
  Let $A in FF^(m times n)$. The vectorization of $A$ is defined as

  $ X = (x_1,...,x_p) in FF^(n times p) |-> op("vec")(X) = vec(x_1,dots.v,x_p) in FF^(n p times 1). $
]

Then our desired matrix representation is given by

$ underbrace(tov(A X B), "coordinate of" T(X)\ m q) = underbrace((B^T oti A), "matrix representation of" T\ m q times n p) underbrace(tov(X), "coordinate of" X\ n p), $

where $oti$ is the Kroenecker product.

#definition("Kroenecker Product")[
  $ C oti D = mat(c_11 D, c_12 D, dots, c_1n D; c_21 D, c_22 D, dots, c_2n D; dots, dots, dots, dots; c_(m 1) D, c_(m 2) D, dots, c_(m n) D). $
]

$dim ker T$?

#theorem[
  Let $A,B in FF^(n times n)$, $f,g$ be coprime polynomials, $f(A) = g(B) = 0$.

  Prove that $T : X in FF^(n times n) |-> A X- X B in FF^(n times n)$ is an isomorphism.
]

#proof[
  It suffices to show that $ker T = 0$.

  If $A X = X B$, then $f(A) X = X f(B) = 0$. By the coprimality of $f,g$, 

  $ u f+ v g = 1 ("Bezout"). $

  $ X = I X &= (u f + v g) (A) X \
  &= 0 + v(A) X g(B) = 0.
  $

  Thus $ker T = 0$.
]

The form $A B - B A$ is quite common in Lie algebra. We may consider the following.

#theorem[
  Define communitator $[A,B] = A B - B A$. Then

  If $A, B in op("Hom")(V,V)$ s.t. $[A, B] = A B - B A =I$ Then
  
  (1) there exists no annihilating polynomial of $A$.

  (2) $V$ must be infinite-dimensional.
]

#proof[
  (1) By easy induction, $ A^k B - B A^k = k A^(k-1). $

  Then for any polynomial $f$, $f(A) B - B f(A) = f'(A)$. 

  (The core idea is utilizing the fact that derivative reduces the degree of the polynomial, thus giving an infinite descent.)

  Suppose there exists an annihilating polynomial $f$ of $A$. Then $f(A) B - B f(A) = f'(A) = 0$.

  Then $f^((k))$ is an annihilating polynomial of $A$ for all $k$. This is a contradiction since for some $k$, $f^((k)) = "const"$, and the constant is nonzero.

  (2) Suppose $V$ is finite-dimensional. Then

  $ I, A, A^2, ..., A^((dim V)^2) $

  are linearly dependent. Thus there exists a nontrivial linear combination of them that equals $0$. This gives an annihilating polynomial of $A$, a contradiction.
]

#question($A B- B A=C$)[
  Let $A,B,C$ be $n$-dimensional matrices. If $A B-B A=C$ and $A C= C A$, then $C$ is non-invertible. Furthermore, $C$ is nilpotent.
]

#proof[
  We can use a clever identity $A^k B-B A^k = k C A^{k-1}$.

  The proof is done by induction.
  
  #note("Why did we think of this?")[
    To prove that $C$ is nilpotent, we should increase the power of $C$ in the given conditions. This can be easily achieved by repeatedly left-multiplying $C$ and simplifying the expression.
  ]

  Consider the linear map $Phi: X |-> X B-B X$. If $C$ is not nilpotent, i.e., $C^k != 0$ for all $k$, then each $k$ is an eigenvalue of $Phi$, which contradicts the finite-dimensional case.
  
  #link("https://math.stackexchange.com/questions/811160/ab-ba-a-implies-a-is-singular-and-a-is-nilpotent")[$->$ StackExchange, https://math.stackexchange.com/questions/811160/ab-ba-a-implies-a-is-singular-and-a-is-nilpotent]b
]

= Linear Spaces with Metric

#definition("Orthogonal Complement")[
  Let $f : V times V -> FF$ be a (anti-)symmetric non-
   bilinear form. The orthogonal complement of $U$ is defined as

  $ U^perp = {v in V | forall u in U, f(u,v) = 0}. $
]

$ V = U opl W or U subset W $


== Multilinear Functions

#definition[
  A function $f: V times ... times V -> FF$ is called a $k$-linear function if it is linear in each of its arguments.
]

Now, to see how two vectors relate to each other, we consider bilinear functions, of which the most important are symmetric and antisymmetric bilinear functions.

#definition[
  A bilinear function $f: V times V -> FF$ is called symmetric if $f(x, y) = f(y, x)$ for all $x, y in V$.

  A bilinear function $f: V times V -> FF$ is called antisymmetric if $f(x, y) = -f(y, x)$ for all $x, y in V$.

  Actually, bilinearty can be deduced from linearity in the first argument, and use (anti)symmetry to deduce linearity in the second argument.
]

=== Gram Matrix : Representing Bilinear Functions

Given a basis $B = {v_1, ..., v_n}$ of $V$, we can represent a bilinear function $f: V times V -> FF$ by a matrix $M$ such that $f(x, y) = x^T M y$ for all $x, y in V$. $M_(i j) = f(v_i, v_j)$.

#definition("Gram Matrix")[
  The above matrix $M$ is called the Gram matrix of $f$ with respect to the basis $B$. It is denoted by $[f]_B$.
]

Now it suffice to study the properties of the matrix $M$ to understand the bilinear function $f$. For example, if $M$ is symmetric, then $f$ is symmetric.

== Euclidean Spaces and Symplectic Spaces

=== Euclidean Spaces and Inner Products

When $M$ is symmetric and positive definite, we have an inner product similar to the dot product in $RR^n$. This is called an inner product space.

#example("Inner Product of Matrices")[
  When $V = M_(n times n) (RR) tilde.eq RR^(n^2)$, we define

  $ f(A,B) = tr(A B^T). $

  The transpose here is necessary to make the function positive definite, because we have $f(A,A) = tr(A A^T) = sum_(i=1)^n sum_(j=1)^n a_(i j)^2 >= 0$.

  Given basis $B = {E_(i j) | 1 <= i, j <= n}$, the Gram matrix is $[f]_B = I_(n^2)$.
]

#example("Inner Product of Functions")[
  When $V = C^0[0, 1]$, we define

  $ phi(f, g) = integral_0^1 f(t) g(t) dif t. $

  Given basis $B = {1, t, t^2, ...}$, the Gram matrix is $[phi]_B = (1/(i+j+1))_(i, j >= 0)$.
]

$[phi]_B = (1/(i+j+1))$ is not easy to deal with. However, by the general property of Gram matrices, we can deduce that $phi$ is symmetric and positive definite.

In Euclidean spaces, inner products give rise to geometric intuition.

#exercise[
  Let $dim V = n$, $(V,f)$ is an inner product space. Show that if

  $
  B = (f(v_i, v_j))_(1 <= i, j <= n),
  $

  then $
  det B !=0 <=> v_1, ..., v_n "is a basis of" V.
  $
]

#proof[
  If $det B != 0$, then $B$ is invertible. Let $x in V$ be such that $f(x, v_i) = 0$ for all $i$. Then $x^T B = 0$, so $x = 0$. Assume $v_1, ..., v_n$ are not linearly independent. Then there exists $x in V$ such that $x = sum_(i=1)^n a_i v_i$ and $a_i != 0$ for some $i$. Then $f(x, v_i) = a_i f(v_i, v_i) = 0$, so $x = 0$, a contradiction.
]

== Orthogonal Complements

#definition[
  Given a subset $S$ of inner product space $V$, the orthogonal complement of $S$ is the set $ S^perp = {v in V | ip(v,s)= 0, forall s in S}. $

  The orthogonal complement of $S$ is well-defined i.e. $S$ exists and is unique.
]

#theorem[
  $
  V = op("span") S opl S^perp.
   $
]

#proofsk[
  WLOG, we assume $S$ is a subspace by $S^perp = op("span") S^perp$.

  If $v in S sect S^perp$, then 
  $
  ip(v,v) = 0 => v = 0. ("by positive definiteness")
  $

  Besides, $dim S^perp = dim V - dim S$, so that $V = op("span") S opl S^perp$.
]

#theorem("Pythagorean Theorem")[
  If $V = W_1 opl W_2$ and $W_1 perp W_2$. Then $norm(v)^2 = norm(w_1)^2 + norm(w_2)^2$ for all $v = w_1 + w_2$, $w_1 in W_1$, $w_2 in W_2$.
]

== Exercises

#question[
  Prove that there are most $n+1$ vectors in $V (dim V = n)$ such that the angle between any two of them is obtuse.
]

#proof[
  Assume $v_1,...,v_(n+1),v_(n+2)$ are such vectors. Then there exists $lambda_1,...,lambda_(n+1)$ which are not all zero such that $sum_(i=1)^(n+1) lambda_i v_i = 0$. Then $ 
  lambda_1 ip(v_1, v_(n+2)) + ... + lambda_(n+1) ip(v_(n+1), v_(n+2)) = 0.
   $

  Obviously $lambda_i$ are not all of the same sign, so let $
  u = sum_(i : lambda_i > 0) lambda_i v_i = - sum_(i : lambda_i < 0) lambda_i v_i,
  $

  we have

  $
  0 &<= ip(u,u) \
  &= sum_(i : lambda_i > 0, j : lambda_j < 0) lambda_i (-lambda_j) ip(v_i, v_j) < 0,
  $

  a contradiction.
]

#proof("Alternative, Gram-Schmidt")[
  Note a interesting property of Gram-Schmidt process:

  $
  w_k = v_k - sum_(i<k) ip(v_k,w_i)/ip(w_i,w_i) w_i.
  $

  By induction, we see $
  w_k "is orthogonal to" w_i "for all" i < k, \
  w_k "and " v_(k+1), ..., v_n "are obtuse to each other."  
  $

  Because $
  ip(w_k, v_(k+l)) &= underbrace(ip(v_k,v_(k+l)),<0) - underbrace(sum_(i<k) ip(v_k,w_i) ip(w_i,v_(k+l))/ip(w_i,w_i), > 0 "by IH.") \
  $

  so 
]

== Spectral Theorem

=== The Complex Spectral Theorem

Now in the perspective of invariant subspaces, we may prove the spectral theorem in a way different from what we did on matrices (i.e. Schur $->$ diagonalization).

#proof[
  Given an normal operator $A$ s.t. $A A^* = A^* A$, it suffices to show $
  CC^n = opl.big_lambda ker (lambda I -A),
  $

  and $ker (lambda I - A)$ are orthogonal to each other. It is clear that

  $
  CC^n = ker (lambda I - A) opl ker (lambda I - A)^perp.
  $

  Now we need to show that $ker (lambda I - A)^perp$ is $A$-invariant (then we can apply induction on $A|_(ker (lambda I - A)^perp)$).

  For all $v in ker (lambda I -A)^perp$, $
  & A v in ker (lambda I - A)^perp \
  arrow.double.l & A v perp w, forall w in ker(lambda I-A), \
  arrow.double.l & 0 = ip(A v, w) = ip(v, A^* w), \
  arrow.double.l & A^* w in ker ker (lambda I - A), forall w in ker(lambda I - A), \
  arrow.double.l & ker(lambda I - A) "is " A- "invariant" ("by commutativity").
  $
]

#example[
  $A$ is Hermitian $=> A^2$ is Hermitian.
]

#question("Canonical Form of Real Normal Matrix")[
  Let $A$ be a normal real matrix, then $A$ is (orthogonally) similar to $
  op("diag")(a_1,...,a_k, mat(b_1,c_1;-c_1,b_1),...,mat(b_l,c_l;-c_l,b_l)).
  $

  Actually, the building blocks $
  mat(1,0;0,1) |-> 1, mat(0,1;-1,0) |-> i.
  $
]

#proof[
  Merge the complex eigenspaces into $
  W = ker (A^2 - 2b A + (b^2+c^2)I).
  $

  Try to find $v,w in W$ s.t. $A(v,w) = (v,w) mat(b,c;-c,b)$.

  $
  A v &= b v - c w => bold(w) = - c^(-1) (A-b I) bold(v) \
  => A w &= c v + b w. ("Note:" A^2 v = 2b A v - (b^2+c^2) v)
  $

  By the above restriction, find

  $
  1. w perp v\
  2. op("span") (v,w)^perp "is" A "-invariant".
  $

  Then the result follows from simple induction.
]

= Review

== Multilinear Functions

#example[
  Let $f_1,f_2 in V^*$, if $forall v in V, f_1(v) f_2(v) = 0$, prove that $f_1 = 0 "or" f_2 = 0$.
] <product-of-linear-functions>

#proof[
  (Matrix) $
  [f_1(v_1),...,f_n (v_n)] = (a_1,...,a_n),\
  [f_2(v_1),...,f_n (v_n)] = (b_1,...,b_n).
  $

  $ 
  (a_1,...,a_n) vec(x_1,dots.v,x_n) (b_1,...,b_n) vec(x_1,dots.v,x_n) = 0.
   $

  Choosing $(x_i) = e_i$, $a_i b_i = 0, forall i$.

  Choosing $(x_i) = e_i + e_j$, $a_i b_i + a_j b_j = 0, forall i,j$.

  If $f_1 != 0$, then WLOG there exists $i$ s.t. $a_1 != 0$, then $b_1 = 0$. Then $a_1 b_j + a_j b_1 = a_1 b_j = 0, forall j$, so $b_j = 0, forall j$.
]

#question[
  If $g: V times V -> FF$ is a bilinear function s.t. 
  $ 
  g(v_1,v_2) = 0 => g(v_2,v_1) = 0,
   $

  prove that $g$ must be symmetric or antisymmetric.
]

#example[
  Let $g$ be a nonzero alternating bilinear function on $V$, then $g$ cannot be decomposed into the product of two linear functions.
  $
  exists.not f_1,f_2, g(alpha,beta) = f_1(alpha) f_2(beta)
  $
]

#proof[
  Proof by contradiction. Assume $g(alpha,beta) = f_1(alpha) f_2(beta)$.

  $
  g(alpha,beta) &= f_1(alpha) f_2(beta) = - f_1(beta) f_2(alpha). 
  $

  Let $beta = alpha$, By @product-of-linear-functions, we have $f_1 = 0 "or" f_2 = 0$, a contradiction since $g$ is not identically zero.
]

#theorem("Algebraic Problem, Geometric Approach")[
  A real symmetric matrix $A$ of order $n$ is orthogonally similar to a matrix whose diagonal entries are zero

  $
  <=> tr A = 0.
  $
]

#note[
  $ 
  g(v_i+v_j, v_i+v_j) = g(v_i, v_i) + g(v_j, v_j) + 2 g(v_i, v_j).
   $
  
  So studying the properties of the induced quadratic form $q(v) = g(v,v)$ gives us information about the bilinear function $g$.
]

#proofsk[
  $=>$ is trivial. Now assume $tr A = 0$. 

  Discuss the problem on $V slash RR$. $g$ is a symmetric bilinear function, so it induces a quadratic form $q(v) = g(v,v)$.

  Choose a basis, $q(v) = f(X) = X^T A X$ where $v = (bold(v)_1,...,bold(v)_n)^(-1) X$.

  The change of variable $X = P Y$ gives $f(X) = Y^T P^T A P Y$.



  Induction on the dimension of the space.

  If $$
]

#theorem[
  #definition("Zero Cone of a Quadratic Form")[
    The zero cone of a quadratic form $q$ is the set $S = {v in V | q(v) = 0}$.
  ]

  $S$ is a subspace of $V$ $<=>$ $q$ is p.s.d. or n.s.d.
]

#proofsk[
  $
  S &= {v in V | q(v) = 0 } \
  &= {X in RR^n | X^T A X = 0} \
  &=^(X=P Y) {Y in RR^n | y_1^2 + ... + y_p^2 - y_(p+1)^2 - ... - y_r^2 = 0} \
  $

  If $q$ is not definite, then there exists $n$ linearly independent vectors in $S$, so $S = V$, a contradiction.

  $
  mat(
    1,0,...,0\,,1,0,...,0\,,0,...,0;
    0,1,...,0\,,1,0,...,0\,,0,...,0;
    dots.v,dots.v,dots.down, dots.v,dots.v,dots.v, dots.down,dots.v,dots.v,dots.down,dots.v;
    0,0,...,1\,,1,0,...,0\,,0,...,0;
    -1,0,...,0\,,1,0,...,0\,,0,...,0;
    -1,0,...,0\,,0,1,...,0\,,0,...,0;
    dots.v,dots.v,dots.down, dots.v,dots.v,dots.v, dots.down,dots.v,dots.v,dots.down,dots.v;
    -1,0,...,0\,,0,0,...,1\,,0,...,0;
    0,0,...,0\,,0,0,...,0\,,1,...,0;
    dots.v,dots.v,dots.down, dots.v,dots.v,dots.v, dots.down,dots.v,dots.v,dots.down,dots.v;
    0,0,...,0\,,0,0,...,0\,,0,...,1;
  )
  $

  Every row is a vector in $S$.

  If $q$ is p.s.d., then there exists a basis $eta$ s.t $S = angle.l eta_(p+1),...,eta_n angle.r$. If $q$ is n.s.d., the same argument applies.
]

#question[
  $A^H = A$ is p.d. then $det A <= a_(11) a_(22) ... a_(n n)$.
]

#proof[
  By induction.
  $
  A = mat(A_1,alpha;alpha^T,a_(n n)) -> mat(A_1,0;0,a_(n n) - 2alpha^T A_1^(-1) alpha).
  $

  $
  det A = det(A_1) underbrace((a_(n n) - 2alpha^T A_1^(-1) alpha), >0) <= det A_1 a_(n n).
  $

  "$=$" holds iff $alpha = 0$ (by p.d. of $A_1^(-1)$), i.e. $A$ is diagonal.
]

= Miscellaneous

#proof[
  #let mA = math.bold($A$)
  #let mB = math.bold($B$)

  考虑$n$阶分块对称矩阵 $ mat(bold(0),mA;mA^T,mB), mB^T = mB. $

  先设 $mB$ 可逆. 做分块矩阵的初等行变换，不改变行列式是否为$0$的性质.

  $ mat(bold(0),mA;mA^T,mB) -> mat(-mA^T mB^(-1) mA, bold(0); mA^T,mB). $

  则行列式

  $ det mat(-mA^T mB^(-1) mA, bold(0); mA^T,mB) = abs(mB) dot abs(mA^T mB^(-1) mA). $

  下面讨论 $mB$ 是 $k (k<n/2)$ 阶矩阵的情况. 此时 $mB^(-1) mA$ 是 $k times (n-k)$ 阶矩阵，且$k<n/2 => k < n-k$. 因此由Cauchy-Binet公式的直接推论， $abs(mA^T mB^(-1) mA) = 0$.

  故在 $k<n/2$ 时我们可以断定 $det mat(bold(0),mA;mA^T,mB) = 0$.

  若 $mB$ 并不可逆，考虑存在 $epsilon > 0$，微扰 $forall 0<t<epsilon, mB' = mB + t I$ 可逆. 由于 $det mat(bold(0),mA;mA^T,mB + t I)$ 是 $t$ 的多项式，故 $det mat(bold(0),mA;mA^T,mB) = lim_(t->0^+) det mat(bold(0),mA;mA^T,mB + t I) = 0$.
]

