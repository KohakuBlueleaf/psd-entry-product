# 第二輪解析探索的結果

記號同 `docs/EXPLORATION.md`。$\omega=e^{2\pi i/n}$。

## A. 已排除的方向（有反例或數值反例）

1. **CD 的非交換推廣為假（E8）。** CD 可寫成：對完全正映射 $\Phi(X)=\sum_aT_aXT_a^*$（$\dim=n$，虧量
   $I-\Phi(I)=ee^*$ 秩一），$|\det(\mathrm{id}-\Phi)|\le\det(I-\Phi^n(I))$。$T_a$ 可交換時（Drury–Arveson 模型）數值成立；
   $T_a$ 不交換時大量反例。所以 CD 的證明必須用到交換性，不能走自由 Fock 空間。
2. **R1 不能只靠多重次調和函數的最大值原理。** 秩一集合是一個環面軌道，它的多項式凸包落在簇
   $\{z_{ij}z_{jk}=d_jz_{ik}\}$ 內，而秩 $\ge2$ 的 PSD 矩陣不在其中。R1 依賴位勢的特殊形式。
3. **「調和可表示性」在 $n\ge4$ 為假。** 若每個相關矩陣 $C$ 都能寫成隨機相位向量 $u$ 使
   $\mathbb E(u_i\bar u_j)^m=c_{ij}^m$，則一般情形立刻化為秩一。但 $n\ge4$ 時複橢圓體有秩 2 的端點，線性泛函就給出反例。
   $n\le3$ 時端點全是秩一，與 E6 中 $n=3$ 的緊性一致。
4. **核序比較為假。** $\prod_{i,j}(1-x_i\bar y_j)^{-1}-\prod_i(1-x_i^n\bar y_i^n)^{-1}$ 不是正定核（對稱性論證）。
5. **逐點的加權秩一不等式 $(W_r)$ 在 $r\ge3$ 為假（E10）。** 見 C。
6. **高秩臨界點存在**（正單形），且滿足一階 KKT（$Z\succeq0$、$Z\bar A=0$）。R1 需要二階或整體資訊。

## B. 數值上成立、可作為證明路線的敘述

1. **調和證書對主定理足夠（E9）。** $n=4..7$、六類對角線（含近等對角、跨越 1、單一大值），
   調和 SDP 對偶界全部 $\ge$ 定理要求的界。近等對角時餘量約為擾動的平方量級，仍為正。
   等價的線性敘述（「鬆弛定理」）：設 $Y_m$（$m\ge1$）為單位對角 PSD 矩陣，且對每個 $(i,j)$，
   $(Y_m[i,j])_m$ 是圓周上某機率測度的 Fourier 係數，則
   $$\sum_{i\ne j}\int-\log|1-\rho_i\rho_je^{i\theta}|\,d\mu_{ij}\;\ge\;-\sum_i\log F_n(\rho_i^2).$$
   這只用到「對每個頻率 $m$ 的 PSD」與「對每個元素的 Toeplitz 正性」，與秩無關。
2. **$(W_2)$ 成立（E10，$n=2..5$ 最小值為 0）。** 由 C，這給出秩 $\le2$、$a_{ii}<1$ 的主定理。
3. CD（交換情形）、R1、U 仍然沒有反例。

## C. 球面平均化約 [已證]

設 $v_i\in\mathbb C^r$，$e$ 在單位球面上均勻，$x_i=\langle v_i,e\rangle$，$N_m=\binom{m+r-1}{m}$。則
$s_m(A)=N_m\,\mathbb E|p_m(x)|^2$，$t_m(A)=N_m\,\mathbb E\sum_i|x_i|^{2m}$（$p_m$ 為冪和）。
所以 $a_{ii}<1$ 時主定理等價於
$$\mathbb E_e\Bigl[\sum_{m\ge1}\frac{N_m}{m}\Bigl(|p_m(x)|^2-n\,[n\mid m]\sum_i|x_i|^{2m}\Bigr)\Bigr]\ge0 .$$
被積函數逐點非負就是 $(W_r)$；$r=1$ 是秩一情形，$r=2$ 數值成立，$r\ge3$ 逐點不成立（平均後才成立）。

## D. 有用的改寫 [已證]

1. **Hilbert 空間形式。** 令 $\mathcal H=\bigoplus_m\frac1m\mathrm{Sym}^m$，$\delta_v=(v^{\otimes m})_m$，$P$ 為到 $n\mid m$ 分量的正交投影
   （即對 $v\mapsto\omega v$ 的平均）。主定理（$a_{ii}<1$）等價於
   $$\Bigl\|(1-P)\sum_i\delta_{v_i}\Bigr\|^2\;\ge\;\sum_{i<j}\bigl\|P(\delta_{v_i}-\delta_{v_j})\bigr\|^2 .$$
   白話：任意 $n$ 點構形的能量 $\ge$ 過每個點的正 $n$ 邊形能量的平均。
2. **廣義 Hölder 形式。** 令 $\Psi(w_1,\dots,w_n)=\prod_{i\ne j}|1-\omega^{i-j}\langle w_i,w_j\rangle|$（即 $v_j=\omega^jw_j$）。
   主定理等價於 $\Psi(w_1,\dots,w_n)^n\le\prod_i\Psi(w_i,\dots,w_i)$。
   $n=2$ 時扭轉後的核 $|1+\langle w,w'\rangle|^2$ 是正定核，這就是 Cauchy–Schwarz。
   這是棋盤估計（反射正性）的形狀；$n\ge3$ 時扭轉後的核不是正定的，尚未找到可用的反射。
3. **完全正映射形式。** $\prod_{i,j}(1-a_{ij})=\det(\mathrm{id}-S_A)$，$S_A:X\mapsto A\circ X$ 為 Schur 乘子；
   右邊 $\prod_i(1-d_i^n)=\det(\mathrm{id}-(X\mapsto DXP))$，$P$ 為循環置換。
4. **整體能量最小化形式。** 對 $g(z)=\sum\gamma_m\mathrm{Re}\,z^m$（$\gamma_m\ge0$），固定對角線時
   $\sum_{i\ne j}g(a_{ij})=\sum_m\gamma_m s_m(A)-\text{常數}$，即最小化加權的張量冪和範數 $\|\sum_iv_i^{\otimes m}\|^2$。
   對單一 $m$，秩一最優（三角不等式）。
