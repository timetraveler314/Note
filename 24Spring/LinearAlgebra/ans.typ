#import "@local/MetaNote:0.0.1" : *
#import "@preview/commute:0.2.0": node, arr, commutative-diagram

#let detm = math.mat.with(delim: "|")

#show: doc => MetaNote(
  title: [
    线性代数（A）2023-2024学年秋季学期答案
  ],
  authors: (
    (
      name: "timetraveler314",
      affiliation: "https://chernoff.bond",
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
#let Ker = math.op("Ker")
#let opl = math.plus.circle

= 

#solution[
  注意到原矩阵实对称，一定可以正交对角化. 只需要求其特征向量并用 Gram-Schmidt 正交化即可.
]

= 

#solution[
  由最小二乘法和正交投影相关性质，只需令 $beta$ 等于 $alpha$ 在 $U$ 中的投影，此时 $beta - alpha$ 垂直于整个 $U$，由勾股定理可以知道这就是使两者距离最小的 $beta$.

  这题算出来好像 $alpha$ 落在 $U$ 内... 不要怀疑自己.
]

= 

#solution[
  (1) 奇异值即 $bold(A)^top bold(A)$ 的特征值的平方根.

  (2) 右奇异向量 $bold(v)_1,...,bold(v)_n$ 即 $bold(A)^top bold(A)$ 的特征向量. 左奇异向量 $bold(u)_i = bold(A) bold(v)_i / sigma_i$. 实际上我去年没有具体算出来左奇异向量，只是列了式子，也没有减分.
]

= 

#solution[
  (1) 略.

  (2) 类似(1)，只需要正交对角化即可.

  (3) 这是 Rayleigh 商的经典应用，答案是二次型矩阵最大的特征值. 可以参考这个讲义：#link("https://www.sjsu.edu/faculty/guangliang.chen/Math253S20/lec4RayleighQuotient.pdf")

  原理即正交替换到新的坐标系后（坐标变换 $bold(y) = bold(P) bold(x) => f(bold(x)) = bold(y)^top bold(D) bold(y)$）. 正交变换保证模长 $norm(bold(x)) = norm(bold(y)) = 1$ 不变，只需要求在 $y_1^2 + ... + y_n^2 = 1$ 条件下
  $
  f(bold(y)) = y_1^2 lambda_1 + ... + y_n^2 lambda_n
  $
  的最大值即可.

  不妨设 $lambda_1 >= ... >= lambda_n$，则容易看出 $f(bold(y)) <= lambda_1$，且 $f(bold(y)) = lambda_1$ 当且仅当 $bold(y) = bold(e)_1$.
]

=

#solution[
  这是可对角化的一个重要性质. 矩阵（即线性变换）可对角化当且仅当全空间等于其特征空间的直和. 也就是有完备的特征向量组成的基. 这给了我们几何和代数上想象的空间. 实际上，我们有如下的一般结论：

  #theorem[
    设 $n$ 阶矩阵 $bold(A)$ 适合首一多项式 $g(x)$，则 $bold(A)$ 可对角化当且仅当 $g(x)$ 在 $CC$ 上无重根.
  ]

  #proof[
    设 $g(x) = (x-a_1)(x-a_2)...(x-a_n)$ 是 $CC$ 上的因式分解. 我们来证明：
    $
      CC^n = Ker(bold(A) - a_1 bold(I)) opl ... opl Ker(bold(A) - a_n bold(I))
    $
  ]

  设 $g_i (x) = product_(j eq.not i) (x-a_j)$，则 $gcd(g_1, ..., g_n) = 1$，由 Bézout 定理，存在 $h_1, ..., h_n$ 使得 $h_1 g_1 + ... + h_n g_n = 1$.

  代入 $x = bold(A)$，可得恒等式

  $
  g_1 (bold(A)) h_1 (bold(A)) + ... + g_n (bold(A)) h_n (bold(A)) = bold(I)
  $

  对任意 $bold(alpha) in CC^n$，有

  $
  bold(alpha) = g_1 (bold(A)) h_1 (bold(A)) bold(alpha) + ... + g_n (bold(A)) h_n (bold(A)) bold(alpha)
  $

  注意到：$(bold(A) - a_i bold(I)) g_i (bold(A)) h_i (bold(A)) bold(alpha) = 0$，所以 $g_i (bold(A)) h_i (bold(A)) bold(alpha) in Ker(bold(A) - a_i bold(I))$. 于是由线性空间和的意义，我们有

  $
    CC^n = Ker(bold(A) - a_1 bold(I)) + ... + Ker(bold(A) - a_n bold(I))
  $

  要证明上式是直和，只需证明：

  任取 $bold(alpha) in Ker(bold(A) - a_1 bold(I)) sect (Ker(bold(A) - a_2 bold(I)) + ... + Ker(bold(A) - a_n bold(I))$，则 $bold(alpha) = bold(alpha)_2 + ... + bold(alpha)_n$，其中 $bold(alpha)_i in Ker(bold(A) - a_i bold(I))$.

  可知 $
       bold(alpha) = h_1 (bold(A)) g_1 (bold(A)) (bold(alpha)_2 + ... + bold(alpha)_n) + h_2 (bold(A)) g_2 (bold(A)) bold(alpha)_2 + ... + h_n (bold(A)) g_n (bold(A)) bold(alpha)_n = bold(0).
     $

  注意到上面推导的下标可任意选，因此我们得到了直和的结论.

  #note[
    实际上，这是特征空间的直和分解，学到 Jordan 标准型以及准素分解等内容后，我们会发现这个结论的深刻意义.
  ]

  回到原题，利用上述定理，我们看到 $g(bold(A)) = bold(A)^2 + bold(I)$ 的根是 $i$ 和 $-i$，因此 $bold(A)$ 可对角化. 且 $bold(A)$ 的所有特征值一定都是 $i$ 和 $-i$ 之一，因此与 $bold(A)$ 相似的矩阵一定是 $op("diag")(i, ..., i, -i, ..., -i)$ 的形式.
]

= 

这是著名的降秩定理，其中用到的分块矩阵技巧在这类特征值问题中非常好用，以下从我的笔记中摘取相关定理：



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
] <matrix-same-eigenvalues>

#proof[
  First theorem with $ mat(lambda mI_m,0;mB,lambda I_n-mB mA) <- mat(lambda mI_m,mA;mB,mI_n)->mat(lambda mI_m - mA mB, mA;0,mI_n). $

  $ n + (n- dim ker (lambda mI_n - mB mA)) = n + (n - dim ker (lambda mI_m - mA mB)). $
]

#proof[
  原题两问的结论即 @matrix-same-eigenvalues. 
]

= 

#solution[
  Linear Algebra Done Right 的习题. 笔者证明有误，喜提 -8 分.

  #image("image.png")
]

=

#question[
  $f(x)=x^T A x$, $A$ is a Gram matrix (or a positive-definite matrix), then
  $ g(x) = det mat(A,x;x^T,0) $
  is negative definite.
]

#proof[
  \#1 : Directly calculate the determinant. We have the lemma below:

  #lemma[
    $ detm(a_(11),a_(12),dots,a_(1 n),x_1; a_(21),a_(22),dots,a_(2 n),x_2; dots.v, dots.v, , dots.v,dots.v; a_(n 1),a_(n 2),dots,a_(n n),x_n;y_1,y_2,dots,y_n,z)= z abs(A) - sum sum A_(i j)x_i y_j. $
  ]

  #proof[
    \#1 (Complicated) :
    Expand the determinant by the last row, the first term is $ (-1)^(n+2) x_1 detm(a_(21),a_(22),dots,a_(2n);dots.v,dots.v,,dots.v;a_(n 1),a_(n 2), dots, a_(n n); y_1,y_2,dots,y_n). $

    Expand the determinant by the last column, we have $ (-1)^(n+2)x_1 (-1)^(n+1) (y_(11)A_(11)+y_(12)A_(12)+dots+y_(1n)A_(1n)) = -sum x_1 A_(1 j) y_j. $

    Similarly, the $i$-th term is $ -sum x_i A_(i j) y_j. $

    Hence the lemma is proved.
  ]

  This problem gives that $g(x) = -x^T A x < 0$.

  \#2(Elementary) :

  做分块初等变换（好用，好用，好用）：

  $ mat(A, x;x^T,0) -> mat(A,x;0,-x^T A^(-1) x) $

  $ g(x) = underbrace(det A, >0) dot (-x^T A^(-1) x) < 0. $
]