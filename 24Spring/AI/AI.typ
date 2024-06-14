#import "@local/MetaNote:0.0.1" : *
#import "@preview/physica:0.9.0": *

#set text(font:("linux libertine", "FandolSong"), lang: "cn")

#show: doc => MetaNote(
  title: [
    Introduction to Artificial Intelligence
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

#let vb = math.bold($b$)
#let vu = math.bold($u$)
#let vv = math.bold($v$)
#let vw = math.bold($w$)
#let vx = math.bold($x$)
#let vy = math.bold($y$)

#let mX = math.bold($X$)
#let mY = math.bold($Y$)

#let argmin = math.limits(math.op("argmin"))
#let argmax = math.limits(math.op("argmax"))
#let sign = math.op("sign")

#outline()

= Lec 9 机器学习和线性回归 (2024/3/21)

== 参数化模型

最简单的参数化模型：线性模型 (Linear Model).

$ f(vx) = vw^T vx + b. $

其中 $vx in RR^d$ 是输入, $vw in RR^d$ 是权重向量, $b in RR$ 是偏置项.

== 线性回归训练

- 训练目标：最小化损失函数.

- 对于线性回归，损失函数通常是均方误差 (Mean Squared Error, MSE), 又名平方损失 (Squared Loss).
$ L(f(vx_i),y_i) = (f(x_i)-y_i)^2. $
惩罚预测值偏离真实值 (ground truth) 太大的情况.

- 通过在训练集上最小化平均损失函数来优化参数.

$ argmin_(w,b) 1/n sum_i L(f(vx_i),y_i) $

训练问题转化为求解以上优化问题.

== 梯度下降

分析上述问题，我们将待优化的*目标* (objective) 定义为 $vw, b$ 的函数：

$ J(vw, b) = 1/n sum_i L(f(x_i)-y_i). $

- 随机选定$vw, b$的初始值，逐步调整$vw, b$的值以降低$J(vw, b)$.
- 思路：每次沿使$J(vw, b)$减小最快的方向走一小步.

$ w <- w - alpha dot pdv(J,vw), b <- b - alpha dot pdv(J,b). $

其中事先指定的超参数 $alpha$ 是*学习率* (learning rate).

- 不断迭代，直至 $J$ 收敛(例如相邻两次迭代$J$的变化小于某个阈值).

这就是*梯度下降* (Gradient Descent) 算法.

=== 梯度的细节

$ grad J = mat(pdv(J,vw);pdv(J,b)) in RR^(d+1) $

上式定义了$J$关于$vw, b$的梯度. 考察梯度的几何意义：

考虑增量 $Delta x, Delta y$.

$ Delta f = pdv(f,x) Delta x + pdv(f,y) Delta y &= grad f dot (Delta x, Delta y) \
&= norm(grad f) norm(mat(Delta x; Delta y)) cos(theta). $

$Delta f$ 最大时，$theta=0$，此时 $Delta x, Delta y$ 与 $grad f$ 同向.

这说明梯度的几何意义：梯度方向是函数增长最快的方向.

== 线性回归的梯度

- 计算 $J(vw, b)$ 关于 $vw, b$ 的梯度, 首先将 $J$ 写成矩阵形式：

$ J = 1/n underbrace((vw^T mX + vb - vy), "行向量") (vw^T mX + vb - vy)^T. $

其中 $mX = mat(vx_1, vx_2, dots, vx_n)$ 是输入数据矩阵, $vy = mat(y_1, y_2, dots, y_n)$ 是标签向量.

#theorem[
  $ pdv(J,vw) &= 2/n sum_i (vw^T vx_i + b - y_i) vx_i = 2/n mX (vw^T mX + vb - vy)^T, \

  pdv(J,b) &= 2/n sum_i (vw^T vx_i + b - y_i). $
]

#note[
  根据“维度相容原则”可简记如下：

  $ pdv(J,vw) = 2/n pdv(vw^T mX + vb - vy, vw) (vw^T mX + vb - vy)^T = 2/n mX (vw^T mX + vb - vy)^T, $

  下面证明是通过严格计算微分得到的.
]

#proof[
  计算 $J$ 的微分：

  $ dif J = 1/n [ dif(vw^T mX + vb - vy) (vw^T mX + vb - vy)^T + (vw^T mX + vb - vy) dif(vw^T mX + vb - vy)^T ]. $

  这里注意应用内积原则：

  #note("矩阵求导常用的内积原则")[
    对列向量 $vu,vv$,

    $ vu^T vv = vv^T vu. $

    对行向量 $vu,vv$,

    $ vu vv^T = vv vu^T. $

    因为以上的式子都表示内积.
  ]

  $ (vw^T mX + vb - vy) dif(vw^T mX + vb - vy)^T &= (vw^T mX + vb - vy) [dif(vw^T mX + vb - vy)]^T \
  &= dif(vw^T mX + vb - vy) (vw^T mX + vb - vy)^T ("与第一项相同") $

  $ dif J &= 2/n dif (vw^T mX + vb - vy) dot (vw^T mX + vb - vy)^T. $

  计算 $dif(vw^T mX + vb - vy)$:

  $ dif(vw^T mX + vb - vy) = dif(vw^T mX) = (dif vw)^T mX. $

  用标量矩阵函数求导的核心：

  $ dif f = tr(pdv(f,mX)^T dif mX). $

  对比 $ dif J = 2/n (dif vw)^T X (vw^T mX + vb - vy)^T = 2/n (vw^T mX + vb - vy) mX^T dif vw, $

  得到 $ pdv(J,vw) &= 2/n mX(vw^T mX + vb - vy)^T \
  &= 2/n sum_i (vw^T vx_i + b - y_i) vx_i. $

  对 $b$ 求导是显然的.
]

== 凹凸性与优化

- 凹函数 (Convex Function) 的定义：对于任意 $x, y$ 和 $0 <= lambda <= 1$,

$ f(lambda x + (1-lambda) y) <= lambda f(x) + (1-lambda) f(y). $

- 凹函数的性质：

#theorem("凹函数的性质")[
  凹函数的局部最小值是全局最小值.
]

#proof[
  反证. 
  
  - 假设 $x^*$ 是局部最小点，$x'$ 是全局最小点，且 $f(x') < f(x^*)$.
  - 则取 $x = lambda x^* + (1-lambda) x'$，有 $f(x) <= lambda f(x^*) + (1-lambda) f(x') < f(x^*)$.
  - 取 $lambda->1$附近，知 $x^*$ 不是局部最小点，矛盾.
]

因此我们可以考虑线性回归问题：

#theorem[
  线性回归的损失函数 $J(vw, b)$ 是凸函数.
]

#proof[
  考虑 Hessian 矩阵 $H$:

  $ H &= mat(pdv(J,vw,2), pdv(J,vw,b); pdv(J,b,vw), pdv(J,b,2))
  = mat(2/n mX mX^T, 2/n mX bold(1)^T; 2/n mX^T bold(1), 2/n n) \
  &= 2/n vec(mX,bold(1)) vec(mX,bold(1))^T. $

  因此 $H$ 是半正定矩阵，$J$ 是凸函数. 
]

=== 学习率的调整

- 学习率过大可能导致算法不收敛，过小可能导致收敛速度慢.
- 要选择适中的学习率，可以考虑自适应学习率算法，逐步减小.


= Lec 10. 逻辑回归、多分类和正则化 (2024/3/25)

== 回顾：经验风险最小化框架 (ERM)

大部分监督学习都遵循基本框架：经验风险最小化 (Empirical Risk Minimization, ERM)，区别仅在于选择的具体损失函数.

- ERM 框架：在训练集上最小化损失函数.

== 逻辑回归

逻辑回归处理二分类问题. 仍然使用线性模型，但采用交叉熵损失函数 (Cross Entropy Loss).

=== 二分类问题

- 标签只有两种. e.g. $y in {-1,1}$.
- 一般不直接让 $f(x)$ 拟合 $y$，而是使用 $sign(f)$ 将实数输出转化为二分类的类别输出. 因而转化为了一个回归问题.

- 损失函数的选择：

朴素想法：0-1 损失函数：

$ L(f(x),y) = cases(0\, space f(x) y >= 0, 1\, space "otherwise") 
<=> L(f(x),y) = cases(0\, space "if " sign(f(x)) = y, 1\, space "otherwise"). $

这是最直接的目标，但是不连续，不易优化.

=== 最大似然框架 (Maximum Likelihood)

- 最大似然估计的原则：
(1) 对观测数据进行(条件)概率建模：
每个观测数据即为一个训练样本.

对于判别式模型，只建模 $p(y|x;theta)$, $theta$ 是模型参数.

(2) 通过最大化观测数据在给定模型下的*似然*（例如，把训练样本预测正确的概率），来调整模型参数.

*独立同分布假设*下，MLE: $theta^* = argmax_theta product_i p(y=y_i|x=x_i;theta). $ 简写为

$ theta^* = argmax_theta product_i p(y_i|x_i;theta). $

但是大量乘法会带来数值精度问题，因此通常转化为对数似然最大化：

$ theta^* = argmax_theta sum_i log p(y_i|x_i;theta). $

=== 逻辑回归的最大似然估计

- 建模：

已有线性模型 $f(x) = vw^T vx + b$. 只需将其转化为正类的概率.

采用 Sigmoid 函数：

#note("Sigmoid 函数")[
  $ sigma(z) = 1/(1+exp(-z)). $

  $ 1- sigma(z) = sigma(-z). $

  将 $RR$ 映射到 $[0,1]$ 区间，可以看作是概率值.
]

则

$ p(y=1|x;vw,b) = sigma(f(x)) = sigma(y dot f(x)), $
$ p(y=-1|x;vw,b) = 1- sigma(f(x)) = sigma(y dot f(x)). $

二者形式恰统一.

- 优化对数似然：

这里最优化问题为

$ &argmax_(vw,b) sum_i log sigma(y dot f(x)) \
= & -argmax_(vw,b) sum_i log (1+exp(-y_i (vw^T vx_i + b))) . $

写成最小化形式，这就是逻辑回归的*ERM*形式.

$ argmin_(vw,b) sum_i log (1+exp(-y_i (vw^T vx_i + b))). $

其中提取出损失函数：Logistic Loss / Log Loss.

=== 另一视角：替代损失函数

以上从最大似然估计的角度推导了逻辑回归的损失函数，但也可以从另一角度看待: 

- 交叉熵损失函数是$0-1$损失的上界，且是凸函数.
- 合页损失 (Hinge Loss)：$L = max(0,1-y_i f(x_i))$ 同样是$0-1$损失的上界.

== 多分类问题: Softmax 回归

#let softmax = math.op("softmax")

=== $K$ 分类问题

- 标签有 $K$ 个类别，$y in {1,2,dots,K}$.
- 共同训练 $K$ 个模型 $f_1(x), f_2(x), dots, f_K(x)$，每个模型输出属于该类别的概率.
- 概率归一化：Softmax函数

#definition("Softmax 函数")[
  $ softmax(z) = [exp(z_1), exp(z_2), dots, exp(z_K)] / (sum_i exp(z_i)). $
]

= Lec 12. 神经网络与反向传播

== 