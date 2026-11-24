# 主定理的證明骨架：「係數幾何平均」證書

狀態：**主定理 ⟸ (CK) + (★★)**。化約本身有完整論證；(CK) 是文獻結果；(★★) 目前只有數值證據。

## 記號

$F_n(t)=1+t+\dots+t^{n-1}$，$\omega=e^{2\pi i/n}$。對 $s>0$：
$g_s(\theta)=-\log|1-se^{i\theta}|=-\tfrac12\log(1+s^2-2s\cos\theta)$。

**(CK) 等參數證書。** 令 $h_s(\theta)=c_0(s)+\sum_{m=1}^{D}c_m(s)\cos m\theta$ 為 $g_s$（視為 $\cos\theta$ 的函數）在節點
$\cos(2\pi k/n)$，$k=1,\dots,\lfloor n/2\rfloor$ 的 Hermite 內插（每個節點二重），$D=n-2$（$n$ 奇）或 $n-1$（$n$ 偶）。則
1. $h_s\le g_s$ 在圓周上；
2. $c_m(s)\ge0$（$m\ge1$）；
3. $(n-1)c_0(s)-\sum_{m\ge1}c_m(s)=-\log F_n(s)$。

第 3 條是直接計算（在正 $n$ 邊形上求和，$D<n$）。第 1、2 條是 Cohn–Kumar (2007) 對絕對單調位勢與 sharp 構形的結果。

**(★★) 雙參數不等式。** 對所有 $s,t>0$ 與 $\theta$：
$$g_{\sqrt{st}}(\theta)\;\ge\;\frac{c_0(s)+c_0(t)}2+\sum_{m=1}^{D}\sqrt{c_m(s)\,c_m(t)}\,\cos m\theta .$$
$s=t$ 時就是 (CK) 第 1 條。

## 化約 [已證]

設 $A\succeq0$，$d_i=a_{ii}>0$，$a_{ij}=\sqrt{d_id_j}\,c_{ij}$，$|c_{ij}|\le1$，$C=(c_{ij})$ 為相關矩陣。

1. 對 $i\ne j$，$z\mapsto-\log|1-\sqrt{d_id_j}\,z|$ 在單位圓盤上是上調和函數；
   $H_{ij}(z)=\tfrac12(c_0(d_i)+c_0(d_j))+\sum_m\sqrt{c_m(d_i)c_m(d_j)}\mathrm{Re}\,z^m$ 是調和函數。
   (★★) 給出圓周上 $H_{ij}\le g$，由最小值原理在整個閉圓盤成立。所以
   $-\log|1-a_{ij}|\ge H_{ij}(c_{ij})$。
2. 令 $\varphi_m(i)=\sqrt{c_m(d_i)}$。Schur 乘積定理：$\sum_{i,j}\varphi_m(i)\varphi_m(j)\,c_{ij}^m\ge0$，所以
   $\sum_{i\ne j}\varphi_m(i)\varphi_m(j)\mathrm{Re}\,c_{ij}^m\ge-\sum_ic_m(d_i)$。
3. 相加：
   $$\sum_{i\ne j}-\log|1-a_{ij}|\;\ge\;\sum_i\Bigl[(n-1)c_0(d_i)-\sum_{m\ge1}c_m(d_i)\Bigr]=-\sum_i\log F_n(d_i).$$

這就是約化形式 `Reduced`，對所有對角線（小於 1、等於 1、大於 1、混合）一次成立，不需要秩一化約。
$d_i=0$ 的情形由連續性或直接刪去該列得到。

## (★★) 的數值證據

- E13：$n=2,3,4,5,6,8$，各 3000 組 $(s,t)\in[e^{-3},e^{2}]^2$，無反例。
- E13b：$n=2..16$，$(s,t)\in[e^{-7},e^{5}]^2$ 與 $s\approx t$ 附近；雙精度下只在雜訊量級（$10^{-11}$ 以下）出現負值。
- E13c：60 位精度，$n=8,9,12,16$，極端參數，全部 $\ge0$；係數 $c_m$ 全部為正。

## $n=3$ 的顯式化 [已推導，待寫成完整證明]

$n=3$ 時 $D=1$，$c_1(s)=\dfrac{s}{1+s+s^2}$，$c_0(s)=-\tfrac12\log(1+s+s^2)+\tfrac12c_1(s)$。
$g$ 對 $\cos\theta$ 是凸函數，(★★) 化為切線條件。令 $s=e^u,t=e^v$，$A=\cosh\frac u2$，$B=\cosh\frac v2$，
$P=4A^2-1$，$Q=4B^2-1$，(★★) 等價於
$$2PQ-P-Q\;\ge\;4\cosh\tfrac{u+v}2\,\sqrt{PQ},$$
$u=v$ 時取等。這是初等不等式。

## 顯式係數

對 $s<1$，令 $G_l=\sum_{k\ge1,\,k\equiv l\,(n)}s^k/k$，$S_l=s^l/(1-s^n)$。內插條件等價於
$c_l+c_{n-l}=G_l+G_{n-l}+2\kappa$、$l\,c_l-(n-l)c_{n-l}=S_l-S_{n-l}$、$c_0=G_0+\kappa$，
$\kappa$ 由次數條件決定（$n$ 奇：$c_{n-1}=0$）。$s>1$ 時用 $c_m(s)=c_m(1/s)$（$m\ge1$）、$c_0(s)=c_0(1/s)-\log s$。

## $n=3$：已完成並形式化

`MatrixIneq/Three.lean`，定理 `mainTheorem_le_three`（無 `sorry`，只依賴標準公理）。證明完全初等，不用對數：
$|1-a_{ij}|^2\le1+d_id_j-2\mathrm{Re}\,a_{ij}$；純量不等式
$(1+st)\sqrt{F(s)F(t)}\le F(s)F(t)-\tfrac12(sF(t)+tF(s))$，其平方差等於
$\tfrac14(s-t)^2(5s^2t^2+4s^2t+4s^2+4st^2+2st+4s+4t^2+4t+5)$；
對權重 $1/\sqrt{F(d_i)}$ 用 PSD；最後三個因子用 AM–GM。
這個寫法在 $n=3$ 可行是因為正三角形的兩個非平凡內積相同；$n\ge4$ 時不同距離類的因子不同，必須用指數（對數）形式。

## (★★) 的結構（E14、E14b、E15）

令 $s=e^u,t=e^v$，$\tau=\sqrt{st}$，$\gamma_m(u)=c_m(e^u)$。定義
$\delta_0=c_0(\tau)-\tfrac12(c_0(s)+c_0(t))$，$\delta_m=c_m(\tau)-\sqrt{c_m(s)c_m(t)}$，
$W(x)=\delta_0+\sum_{m\ge1}\delta_mT_m(x)=h_\tau(x)-R_{s,t}(x)$。由 (CK)，$W\ge0$ 於 $[-1,1]$ 蘊含 (★★)。數值上：

- $\delta_0\ge0$（$\gamma_0$ 為凹函數）；$\delta_m\ge0$（$\gamma_m$ 對數凹）。
- $W\ge0$ 於 $[-1,1]$，最小值在 $x=-1$。相對餘量隨 $n$ 遞減，約為 $2/n^2$ 到 $3/n^2$，到 $n=40$ 仍為正。
- $\delta_0\ge\sum_m\delta_m$ 只在 $n=3$ 成立，所以不能用最粗的估計。
- 偶數 $n$ 時 $x=-1$ 是內插節點，所以 $W(-1)\ge0$ 是 (★★) 的必要條件，而且是最緊的位置。

## 係數的積分表示 [已推導]

$g_s(x)=-\tfrac12\log(2s)+\ell_u(x)$，$\ell_u(x)=-\tfrac12\log(\cosh u-x)=\int_0^\infty\bigl(e^{tx}e^{-t\cosh u}-e^{-t}\bigr)\frac{dt}{2t}$。
內插算子是線性的，所以 $c_m(e^u)=\int_0^\infty E_m(t)e^{-t\cosh u}\frac{dt}{2t}$（$m\ge1$），
$E_m(t)\ge0$ 是 $e^{tx}$ 的內插多項式的 Chebyshev 係數。
這給出一個正定核 $\kappa_m(u,v)=\int E_m(t)e^{-t(\cosh u+\cosh v)/2}\frac{dt}{2t}$，對角線正確，
但對應的常數項方向錯誤（$c_0$ 作為 $\cosh u$ 的函數是凸的），所以這個「算術平均」證書不夠。(★★) 用的是幾何平均。

$n=4$ 的係數已經含對數（超越函數），所以一般 $n$ 不能靠逐個顯式計算，需要結構性的證明。

## 待辦

1. 證明 (★★) 對所有 $n$ 成立。
2. 核對 Cohn–Kumar 原文，或自行證明 (CK) 第 1、2 條。
3. Lean 一般 $n$ 的骨架：最小值原理可用最大模原理代替，對全純函數 $(1-\tau z)e^{P(z)}$ 使用（Mathlib 已有）。
