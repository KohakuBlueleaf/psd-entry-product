# 路線 A 筆記：秩一化約（R1）

固定對角線 $d$，$f(A)=\sum_{i\ne j}\log|1-a_{ij}|$，可行集 $K_d=\{A\succeq0,\ \mathrm{diag}\,A=d\}$。
記 $N$ 為非對角元 $N_{ij}=\dfrac1{1-a_{ij}}$、對角為 0 的 Hermite 矩陣。

## 1. 臨界點方程 [已證]

Gram 向量 $a_{ij}=v_j^*v_i$，$\|v_i\|^2=d_i$。對 $v_i$ 變分：
$\delta f=-2\mathrm{Re}\,\,(w_i^*\,\delta v_i)$，$w_i=\sum_{j\ne i}\dfrac{v_j}{1-a_{ji}}$。
臨界點等價於存在實數 $\lambda_i$ 使 $w_i=\lambda_iv_i$，即

$$(\bar N-\Lambda)\,V=0,\qquad \Lambda=\mathrm{diag}\,(\lambda_i)\ \text{實}.$$

## 2. 更正：秩 $\ge2$ 的臨界點存在

E5 的數值搜尋沒有找到秩 $\ge2$ 的臨界點，但它們是存在的。例：$\mathbb R^{n-1}$ 中的正單形，
$\sum_jv_j=0$、$a_{ij}=-\tfrac1{n-1}$，則 $w_i=-\tfrac{n-1}{n}v_i$，是秩 $n-1$ 的臨界點
（$n=3$ 時 $f=6\log\tfrac32\approx2.43<\log27\approx3.30$，不是最大值）。
所以「秩 $\ge2$ 處梯度不為零」是錯的。R1 必須用二階條件或整體論證。

## 3. 最大值點的必要條件（KKT）[已證]

一階條件：$\delta f=-\mathrm{tr}\,(H\bar N)$，所以最大值點 $A$ 使線性泛函 $A'\mapsto\mathrm{tr}\,(A'\bar N)$ 在 $K_d$ 上取最小。
這是一個滿足 Slater 條件的 SDP，由強對偶性：

> 在 $f$ 的任何局部最大值點 $A$，存在實對角矩陣 $\Lambda$ 使
> $$Z:=N-\Lambda\succeq0,\qquad Z\bar A=0 .$$

推論：
- $\mathrm{rank}\,A\le\dim\ker Z$。**R1 等價於：在最大值點 $\ker Z$ 是一維的。**
- $-\lambda_i=Z_{ii}\ge0$。
- $Z\circ(J-A)=J+\Delta$，$\Delta$ 為對角；也就是 $Z$ 是 $J-A$ 的 Hadamard 逆再修正對角線。
- $d_i<1$ 時 $Z=C-D$，$C=[1/(1-a_{ij})]$ 是 Drury–Arveson 核的 Gram 矩陣，$D$ 為實對角。
  條件變成：$C\succeq D$，且等號在 $\bar V$ 的列空間上取到。
- 等對角、單位根構形：$Z$ 是循環矩陣，特徵值 $\dfrac{n\rho^m}{1-\rho^n}-\dfrac1{1-\rho}-\lambda$（$m=0,\dots,n-1$），
  最小的在 $m=n-1$，核恰為一維。

二階資訊（單個向量沿複切方向 $\xi\perp v_i$）：$f''=2\lambda_id_i-2\mathrm{Re}\,\,e^{2i\varphi}S_i(\xi)$，
$S_i(\xi)=\sum_{j\ne i}\dfrac{(v_j^*\xi)^2}{(1-a_{ij})^2}$，所以局部最大值需要 $|S_i(\xi)|\le-\lambda_id_i$。

## 4. 待解

證明：若 $Z=N-\Lambda\succeq0$ 且 $Z\bar A=0$，並滿足二階條件，則 $\mathrm{rank}\,A=1$。
目前想法：利用 $Z\circ A^{\circ k}\succeq0$（Schur）與 $1^{\!\top}(Z\circ A)1=\mathrm{tr}\,(Z\bar A)=0$ 得到的恆等式
$Z\circ A=Z-J-\Delta$、$(Z1)_i=n-1+\mu_i$。
