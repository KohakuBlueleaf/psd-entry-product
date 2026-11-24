# A：一般 $n$ 的證明計畫

目標：對所有 $n\ge4$ 證明 $W(\theta;\alpha,b)\ge0$（$0\le b\le\alpha$），由此得 `Star n`。

## 共用的判準（E29、E31）

分部求和：$2\sin^2x\cdot W=\sum_{j\ge0}e_j\sin^2((j+1)x)$，$x=\theta/2$，
$e_j$ 為 $(2\delta_0,\delta_1,\dots,\delta_{n-2},0,0)$ 的前向二階差分。令 $t=1/\sin x\ge1$。
取指標 $J'$，令 $\hat e_j=\min_{J'\le i\le j}e_i^+$（$j\ge J'$），則

- $\sum_{j\ge J'}\hat e_j\sin^2((j+1)x)\ge P_1(t)=\sum_{k\ge J'}(\hat e_k-\hat e_{k+1})\max\bigl(0,\tfrac{k-J'+1-t}2\bigr)$；
- 同一個和 $\ge P_2(t)=\dfrac4{\pi^2t^2}\sum_{J'\le j\le t-1}\hat e_j(j+1)^2$；
- 負部 $\le N(t)=\sum_je_j^-\min\bigl(1,\tfrac{(j+1)^2}{t^2}\bigr)$。

**判準**：存在 $J'$ 使 $\max(P_1,P_2)\ge N$ 對所有 $t\ge1$ 成立，則 $W\ge0$。

| $n$ | 16 | 25 | 32 | 40 | 50 | 64 | 80 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 最差比值（粗網格） | 64 | 7.6 | 6.1 | 4.8 | 4.1 | 3.6 | 3.3 |
| 負二階差分的個數 | 1 | 1 | 2 | 2 | 3 | 3 | 5 |

比值隨 $n$ 遞減並趨近漸近值（約 3，見 `mono-asymptotics.md`），沒有跌破 1 的趨勢。$n\le15$ 時沒有負的二階差分。

## 需要的引理

記 $N=n-m$。$\delta_m=c_m+\rho_m$（`exact-series.md`）。

- **L1（三次部分的二階差分）**：$c_m$ 的第一族對 $m$ 的二階差分有封閉式
  $(n-m)\cdot2\cosh((c-m)b)(\cosh b-1)+2\sinh((c-m)b)\sinh b$ 乘上 $\dfrac{e^{-c'\alpha}}{c'}$ 的組合，$\alpha\ge b$ 時為正。要給出顯式下界。
- **L2（幾何部分）**：第二族的二階差分為負，絕對值 $\le C\,n\,e^{-(n+m)\alpha}(\cosh nb-1)(1-e^{-\alpha})^2$ 型的顯式上界。
- **L3（$\rho_m$ 與 $m$ 接近 $n$ 的項）**：證明 $j\ge J_0$ 時 $e_j\ge0$，或給出 $|e_j^-|$ 的可求和上界。
  這是最難的一條：$m$ 接近 $n$ 時 $c_m$ 與 $\rho_m$ 同階相消，必須直接處理 $\delta_m=\Gamma_m(\alpha)-\sqrt{\Gamma_m(p)\Gamma_m(q)}$，
  其中 $\Gamma_m=2\sum_{j<N}(N-j)B_j$。
- **L4（$p\to0$）**：級數對 $j$ 不衰減的區域，改用積分表示。
- **L5（組合）**：由 L1–L4 得到判準的比值 $\ge1$。首階估計給出比值 $\to\tfrac32\sinh\alpha\coth\tfrac\alpha2\ge3$。

## 分工

- 平行的嚴格驗證（B）：對 $n\le40$ 用區間算術直接驗證判準，產出在 `rigorous-B.md`。
- A 只需要對 $n>n_0$ 證明 L1–L5，其中 $n_0$ 是 B 能涵蓋的範圍。

## L3 的一個可行思路（尾端凸性）[想法]

記 $\mu(dw)=\rho_n(w)\,dw$，$f_N(w)=\dfrac{\sinh Nw-N\sinh w}{\cosh w-1}=2\sum_{j<N}(N-j)\sinh jw$，則 $\Gamma_m(x)=\int_x^\infty f_N\,d\mu$。定義泛函
$$T(f)=\int_\alpha^\infty f\,d\mu-\sqrt{\int_p^\infty f\,d\mu\cdot\int_q^\infty f\,d\mu},$$
則 $\delta_m=T(f_N)$。$T$ 是凸的一次齊次泛函（線性減去兩個正線性泛函的幾何平均）。
因為 $f_{N+1}+f_{N-1}=2f_N+2\sinh(N\,\cdot)$，由凸性
$$\Delta^2\delta_m\;\ge\;2\bigl[T(f_N+s_N)-T(f_N)\bigr]\;\ge\;2\,T'(f_N;s_N),\qquad s_N=\sinh(N\,\cdot),$$
$$T'(f_N;s_N)=B_N(\alpha)-\tfrac12\Bigl[\frac{B_N(p)}{\lambda}+\lambda B_N(q)\Bigr],\quad\lambda=\sqrt{\Gamma_m(p)/\Gamma_m(q)} .$$
令 $r_N(x)=B_N(x)/\Gamma_m(x)$，則 $T'=r_N(\alpha)\Gamma_m(\alpha)-\tfrac12\sqrt{\Gamma_m(p)\Gamma_m(q)}\,(r_N(p)+r_N(q))$，
由 $\Gamma_m(\alpha)\ge\sqrt{\Gamma_m(p)\Gamma_m(q)}$，只要 $r_N$ 在 $[p,q]$ 上是凹的就有 $T'\ge0$，即 $\Delta^2\delta_m\ge0$。

- 對 $N$ 小（指標接近 $n$）：$s_N/f_N$ 對 $w$ 遞增且變化緩慢，$r_N$ 有機會是凹的。這正是需要的區域。
- 對 $N$ 大（$m$ 小）：主階上 $T'<0$（相對量級 $\cosh b-1$），這個論證不適用，與觀察到的「負二階差分只出現在前幾個指標」一致。

待檢驗：$r_N$ 的凹性在哪個 $N$ 的範圍成立。
