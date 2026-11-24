# 定理地圖與證明路徑

方法：先整理用到的定理與它們之間的關係，用文字想清楚證明路徑，再用 Lean 驗證寫下的想法。
計算只用來檢驗某個猜想性質是否可能成立，不作為證明。

每個節點標明狀態：**[Lean]** 已形式化；**[文字]** 有完整的文字證明，尚未形式化；**[猜想]** 只有數值跡象；**[缺]** 沒有證明思路。

## 1. 整體鏈

```
主定理
  ⇐ 約化形式                      [Lean]  |1-tⁿ| = |1-t|·Fₙ(t)
  ⇐ 存在證書 Certificate n          [Lean]  Schur 乘積定理 + 最大模原理
  ⇐ Fejér 證書滿足三個性質
       非負  ⇐ sinh(Nw) ≥ N sinh w  [Lean]
       總和恆等式                    [Lean]  核的恆等式 + 微積分基本定理
       雙參數不等式 Star n
            p = q（等對角）          [Lean]  誤差公式；star_diag、mainTheorem_const_diag
            p ≠ q                    [缺]    見第 4 節
```

## 2. 用到的定理

| 定理 | 在這裡的角色 | 狀態 |
| --- | --- | --- |
| Schur 乘積定理 | 逐元冪次 $A^{\circ m}\succeq0$，所以 $\sum_{i,j}\varphi_i\varphi_j\operatorname{Re}c_{ij}^m\ge0$ | Mathlib |
| 最大模原理 | 圓周上的 $|1-\tau z|\le e^{-\operatorname{Re}P(z)}$ 推到閉圓盤 | Mathlib |
| Oppenheim 不等式 | 秩一情形（備用路線） | [Lean] |
| Hermite 內插誤差公式（差商） | $g_s-h_s=\mathrm{Fej}_n\cdot$（差商），差商為正 | [文字] |
| Fejér 核非負、Poisson 核非負 | 誤差公式右邊每個因子非負 | 初等 |
| Fejér 判準（凸係數） | 係數為凸的餘弦級數非負 | 初等，$n\ge16$ 不夠 |
| Prékopa 定理 | 對數凹函數的尾積分對數凹，給 $\Gamma_m$ 的對數凹性 | Mathlib 未必有 |
| Cauchy–Schwarz／AM–GM | $\sqrt{\Gamma_m(p)\Gamma_m(q)}$ 的各種界 | 初等 |
| Kubo–Ando 幾何平均 | 「係數取幾何平均」是給定對角線的最大正定核 | 只用到 2×2 的情形 |
| Delsarte–Yudin 線性規劃界 | 整個方法的框架（Cohn–Kumar 2007、Miezaki–Tagami 2012） | 不直接引用 |

## 3. 已經確立的性質

記 $t=e^{-w}$，$N=n-m$，$\rho_n(w)=\dfrac{\cosh w-1}{\cosh nw-1}$。

1. **核的緊湊形式。** $k_m(w)=e^{-mw}\chi_m(w)$，$\chi_m=\dfrac{P_N(t)}{(1-t^n)^2}$，$P_N(t)=1-t^{2N}-Nt^{N-1}(1-t^2)$。
   $0\le\chi_m\le1$。[文字]
2. **瞬時核。** $\Pi_w(\theta)=\tfrac12k_0+\sum_{m\ge1}k_m\cos m\theta=\tfrac12\mathcal P_w(\theta)\bigl(1-\rho_n(w)\mathrm{Fej}_n(\theta)\bigr)$。
   因為 $0\le\rho_n\mathrm{Fej}_n\le1$，有 $0\le\Pi_w\le\tfrac12\mathcal P_w$，逐點與逐係數都成立。[文字]
3. **誤差公式。** $g_x-h_x=\int_x^\infty\bigl(\tfrac12\mathcal P_w-\Pi_w\bigr)dw=\tfrac12\mathrm{Fej}_n\int_x^\infty\rho_n\mathcal P_w\,dw\ge0$。
   這就是 Star 在 $p=q$ 的情形。[文字]
4. **線性結構。** $k_{m-1}-2k_m+k_{m+1}=2\rho_n\sinh(Nw)$，所以 $\Gamma_m=2\sum_{j<N}(N-j)B_j$，
   $h_x=\widetilde B(x)+\sum_jB_j(x)\mathrm{Fej}_{n-j}(\theta)$：證書是 Fejér 核的正混合。[文字]
5. **精確級數。** $\zeta_m=1-me^{mx}\Gamma_m$ 與 $\Gamma_0$ 是 $e^{-x}$ 的顯式冪級數。[文字]
6. **缺口的分解。** $W=h_\alpha-R=W^{\rm lin}+W^\rho$，$W^{\rm lin}$ 是 $x\mapsto E_x(e^{x-\alpha}e^{i\theta})$ 的中點凸性虧量，
   $W^\rho=\sum\frac{w_m}2(\sqrt{\sigma_m(p)}-\sqrt{\sigma_m(q)})^2\cos m\theta$。[文字]
7. **單調性。** $\chi_m$ 不減、$k_m\le m\Gamma_m$ [Lean：`chi_mono`、`kern_le_mul_Gam`]；$\Gamma_m$ 對數凹 [猜想，數值成立]。

## 4. 缺口：$p\ne q$ 的雙參數不等式

### 4.1 用文字說它在講什麼

對每個半徑參數 $x$，有三個函數：位勢 $G_x=-\log|1-e^{-x}e^{i\theta}|$、證書 $h_x$、誤差 $E_x=G_x-h_x\ge0$。
$G_x$ 的 Fourier 係數是 $e^{-mx}/m$，所以兩個不同半徑的位勢，其係數的幾何平均恰好是中間半徑的位勢：$G_p\#G_q=G_\alpha$。
雙參數不等式說的是：**對證書做同樣的事（係數取幾何平均），結果仍然在 $G_\alpha$ 的下方**，只是常數項要取算術平均。

等價地，令 $\sigma_m(x)\in[0,1]$ 為證書保留的比例（$\Gamma_m=\frac{e^{-mx}}m\sigma_m$），則
$$L(\theta)=\underbrace{-\tfrac12(\Gamma_0(p)+\Gamma_0(q))}_{\ge0}+\sum_{m\ge1}\frac{e^{-m\alpha}}m\Bigl[1-\sqrt{\sigma_m(p)\sigma_m(q)}\Bigr]\cos m\theta\;\ge\;0 .$$
係數全部非負。所以問題是：**一個正定函數（係數非負）何時逐點非負**。$p=q$ 時它等於 Fejér 核乘 Poisson 核的正混合，所以非負；
$p\ne q$ 時係數被「比例的幾何平均」改動了，要證明這個改動不破壞逐點非負。

### 4.2 候選的原理

| 編號 | 想法（文字） | 需要驗證的性質 | 狀態 |
| --- | --- | --- | --- |
| A | **單調路徑**：固定幾何平均 $\alpha$，把兩個半徑拉開（$b$ 增大），缺口不減。於是只需 $b=0$ 的情形，即誤差公式。 | 導數 $D_{p,q}(\theta)=\Pi_q^{\lambda}-\Pi_p^{1/\lambda}\ge0$，其中 $\lambda_m=\sqrt{\Gamma_m(p)/\Gamma_m(q)}$ 是 Fourier 乘子 | [猜想] |
| B | **Fejér 混合**：把缺口寫成 Fejér 核的組合 $\sum_je_jF_{j+1}$，權重是係數的二階差分。權重大多為正；負的只在前幾個指標，來自一個 Poisson 型的項。 | (i) 尾端權重非負；(ii) 正的部分逐點壓過 Poisson 型的負部分 | (i) [猜想]，(ii) [猜想]，首階有推導 |
| C（不足，見 4.3c） | **凸泛函**：$\delta_m=T(f_N)$，$T$ 是凸的一次齊次泛函，$f_N$ 對 $N$ 為凸。 | 比值 $B_N/\Gamma_m$ 對 $x$ 為凹 | [想法]，未檢驗 |
| D（已否定，見 4.3b） | **瞬時核的比較**：$\lambda_m=e^{mb}$ 時，$D\ge0$ 等價於 $x\mapsto\Pi_x(e^{x-\alpha}e^{i\theta})$ 對 $x$ 遞增，其係數是 $e^{-m\alpha}\chi_m(x)$，逐係數遞增。 | 這個「理想化」版本逐點是否成立，以及真實的 $\lambda_m\le e^{mb}$ 造成的差異 | [想法] |

### 4.3 這些想法之間的關係

- A 是目標，B 是證明 A（或直接證 $W\ge0$）的工具，C 是證明 B(i) 的工具，D 是理解 A 的導數為什麼為正的模型。
- B(ii) 的首階計算給出「正部至少是負部的三倍」，所以結論在數量上很寬裕；困難在於要對所有 $n$ 與所有參數一致地控制。
- 已知不可行的捷徑（不含平方根的線性核、算術平均、在 Fejér 混合表示下取幾何平均、單項式係數的證書）列在 `REPORT.md`。

### 4.3b 這一輪用文字推出的結論

**(1) $e^{mx}\Gamma_m(x)$ 不減，有完整的文字證明。** [文字]
$\chi_m(w)=e^{mw}k_m(w)$。令 $T$ 為參數 $m$ 的指數分布，則 $\sigma_m(x)=m\,e^{mx}\Gamma_m(x)=\mathbb E\,\chi_m(x+T)$。
若 $\chi_m$ 不減，則 $\sigma_m(x)\ge\chi_m(x)$，而 $\sigma_m'=m(\sigma_m-\chi_m)\ge0$。
所以只需 $\chi_m=P_N(t)/(1-t^n)^2$ 對 $w$ 不減，這是一個初等的單變數敘述。
推論：危險率 $r_m=k_m/\Gamma_m\le m$，即 $\kappa_m:=r_m/m=\chi_m/\sigma_m\in[0,1]$。

**(2) 單調性導數的正規化形式。** [文字，E34 數值核對到 15 位]
$$D_{p,q}(\theta)=\tfrac12\bigl(\chi_0(q)-\chi_0(p)\bigr)+\sum_{m=1}^{n-2}e^{-m\alpha}\sqrt{\sigma_m(p)\sigma_m(q)}\;\bigl(\kappa_m(q)-\kappa_m(p)\bigr)\cos m\theta .$$
所有因子都在 $[0,1]$ 內。$\kappa_m$ 不減等價於 $\Gamma_m$ 對數凹。
無窮小形式：$\Omega_x=\partial_x\Pi_x+\sum_m m\,\kappa_m k_m\cos m\theta$，即「瞬時核對 $x$ 的導數」加上「以速率 $\kappa_m$ 逐頻率向圓內平移」。

**(3) 候選 D（理想化的比較）不成立。** [數值反例，E34]
$x\mapsto\Pi_x(e^{x-\alpha}e^{i\theta})$ 不是單調的：$x\to\infty$ 時它趨於截斷的 Poisson 級數 $\tfrac12+\sum_{m\le n-2}e^{-m\alpha}\cos m\theta$，
這個截斷級數有負的旁瓣。用文字說：把一個只有有限多個頻率的核向圓外延拓，高頻被放大，會產生負值。
所以真實乘子 $\lambda_m=e^{mb}\sqrt{\sigma_m(p)/\sigma_m(q)}$ 中的阻尼因子 $\sqrt{\sigma_m(p)/\sigma_m(q)}\le1$ 是必要的，不能當成小修正。

**(4) 逐係數的反向 Cauchy–Schwarz（Aczél）。** [文字]
每個頻率上缺口的係數是 $aa'-bb'$，其中 $a=\sqrt{e^{-mp}/m}$、$b=a\sqrt{\sigma_m(p)}\le a$（$a',b'$ 對應 $q$）。
由 Aczél 不等式 $aa'-bb'\ge\sqrt{(a^2-b^2)(a'^2-b'^2)}$，即缺口的係數 $\ge\sqrt{A_m(p)A_m(q)}$；常數項由 AM–GM 也滿足同樣的關係。
所以**缺口在係數的意義下大於兩個誤差函數的係數幾何平均**：$L\succeq E_p\#E_q$。
這是正定序下的敘述，不直接給逐點的結論，但它說明問題的結構是「逐頻率的 Lorentz 型雙線性形式」：
$L(\theta;p,q)=\mathcal Q_\theta(X_p,X_q)$，$\mathcal Q_\theta$ 是一個固定的不定對稱雙線性形式，$\mathcal Q_\theta(X_x,X_x)=E_x(\theta)\ge0$。
若 $\mathcal Q_\theta$ 在這些向量張成的空間上只有一個正方向，Star 就由反向 Cauchy–Schwarz 得到；但它有很多正方向（每個 $\cos m\theta>0$ 的頻率一個），所以這個論證不能直接用。

### 4.3c $\chi_m$ 遞增的完整文字證明，以及候選 C 的檢討

**引理 χ.** 對 $1\le N\le n$、$w>0$，$\chi(w)=e^{(n-N)w}\,\dfrac{\sinh Nw-N\sinh w}{\cosh nw-1}$ 對 $w$ 不減。[文字]

*證.* 對數導數為 $(n-N)+\dfrac{N(\cosh Nw-\cosh w)}{\sinh Nw-N\sinh w}-n\coth\dfrac{nw}2$，要證它 $\ge0$。

1. $n\coth\frac{nw}2-n=\dfrac{2n}{e^{nw}-1}$，而 $y\mapsto\dfrac{y}{e^{y}-1}$ 遞減，所以對 $n\ge N$：
   $n\coth\frac{nw}2-(n-N)\le N+\dfrac{2N}{e^{Nw}-1}=N\coth\dfrac{Nw}2$。於是只需 $n=N$ 的情形。
2. $\dfrac{N(\cosh Nw-\cosh w)}{\sinh Nw-N\sinh w}\ge N\coth\dfrac{Nw}2$：交叉相乘並用 $\sinh Nw\cosh\frac{Nw}2-\cosh Nw\sinh\frac{Nw}2=\sinh\frac{Nw}2$，
   化為 $N\sinh w\cosh\frac{Nw}2\ge(1+\cosh w)\sinh\frac{Nw}2$，即 $N\tanh\dfrac w2\ge\tanh\dfrac{Nw}2$。
3. 最後一式由 $\tanh(a+b)=\dfrac{\tanh a+\tanh b}{1+\tanh a\tanh b}\le\tanh a+\tanh b$ 歸納得到。∎

與 4.3b(1) 合起來：$k_m(x)\le m\,\Gamma_m(x)$，即 $e^{mx}\Gamma_m(x)$ 不減。形式化時不必取對數，等價的敘述是 $m\,k_m+k_m'\ge0$，再對 $w$ 從 $x$ 積到 $\infty$。

**候選 C 的檢討。** [文字]
C 的充分條件是比值 $r_N=B_N/\Gamma_m$ 對 $x$ 為凹。但 $\sinh(Nw)/f_N(w)\sim\tfrac12e^{w}$（$w\to\infty$），所以 $r_N(x)$ 大致像 $e^{x}$ 一樣增長，是凸的。
這時需要 $\Gamma_m(\alpha)/\sqrt{\Gamma_m(p)\Gamma_m(q)}\ge\cosh b$，即 $-(\log\sigma_m)''\ge1$ 的量級，而尾端的 $\log\sigma_m$ 幾乎是線性的。
所以 **C 照原樣不能用**：凸泛函的一階下界在尾端也是負的，尾端的凸性同樣來自被丟掉的二階項。地圖中把 C 標為「不足」。

### 4.3d 缺口對半徑差的二階導數：精確公式 [文字，E35 以差分核對]

固定 $\alpha,\theta$，令 $p=\alpha-y$、$q=\alpha+y$，$L(y)$ 為缺口。記 $g_m=\sqrt{\Gamma_m(p)\Gamma_m(q)}$，$r_m=k_m/\Gamma_m$（危險率），
$\Delta_m=r_m(q)-r_m(p)$，$S_m=r_m'(p)+r_m'(q)$。直接計算（$\psi=\sqrt\Gamma$，$\psi'=-k/2\psi$，$k'/\Gamma=r'-r^2$）：
$$L'(y)=\tfrac14\bigl(k_0(q)-k_0(p)\bigr)+\tfrac12\sum_m g_m\,\Delta_m\cos m\theta,$$
$$L''(y)=\tfrac14\bigl(k_0'(p)+k_0'(q)\bigr)+\sum_m g_m\Bigl[\tfrac12S_m-\tfrac14\Delta_m^2\Bigr]\cos m\theta .$$
逐頻率的結構是一組 Riccati 型的關係：$g_m'=-\tfrac12g_m\Delta_m$，$(g_m\Delta_m)'=g_m(S_m-\tfrac12\Delta_m^2)$。

用文字說：二階導數是「兩端的無窮小生成元，以幾何平均為權重的平均」減去「危險率之差的平方的四分之一」。
$y=0$ 時第二項消失，$L''(0)=\Omega_\alpha$。先前所有一階論證丟掉的正是這個結構。

**觀察（少量數值，僅作跡象）。** $L''(y)\ge0$ 在測試的情形都成立，而且相對餘量隨 $y$ 增大而**增大**
（$n=20$、$\alpha=0.8$：$y=0.05$ 時 $0.009$，$y=0.4$ 時 $0.07$，$y=0.79$ 時 $0.20$）。
也就是說最緊的是 $y\to0$，即無窮小的情形；兩個半徑拉得越開，不等式越寬裕。

**由此得到的兩個目標。** Star 由下面兩條推出（$L(0)=E_\alpha\ge0$，$L'(0)=0$）：

- **(T1) 無窮小正性**：對所有 $x\ge0$、$\theta$，$\Omega_x(\theta)=\tfrac12k_0'(x)+\sum_m\Gamma_m(x)\,r_m'(x)\cos m\theta\ge0$。這是單參數的敘述。
- **(T2) 凸性的傳遞**：$L''(y)\ge0$ 對所有 $0\le y\le\alpha$。

(T1) 是 (T2) 在 $y=0$ 的特例。跡象顯示 (T1) 是最緊的情形，所以合理的策略是先證 (T1)，再找一個論證說明 $y>0$ 時只會更好。

**另一個觀點（Schrödinger／Sturm）。** $\psi_m=\sqrt{\Gamma_m}$ 滿足 $\psi_m''=V_m\psi_m$，$V_m=\tfrac14r_m^2-\tfrac12r_m'\le\tfrac14m^2$；
位勢 $G$ 的對應物是 $\varphi_m=e^{-mx/2}/\sqrt m$，滿足 $\varphi''=\tfrac14m^2\varphi$。
$L'$ 的係數是 $\psi_m$ 在兩點的 Wronskian 型量 $\psi_m'(p)\psi_m(q)-\psi_m(p)\psi_m'(q)$。
位勢本身 $-\log|1-e^{-(p+q)/2}e^{i\theta}|$ 是半圓柱上 Laplace 算子 Green 函數的鏡像項。這個觀點目前只是重述，還沒有給出論證。

### 4.3e (T1) 的正規化形式與一個教訓 [文字]

由 $\sigma_m\kappa_m'=\chi_m'-m\chi_m(1-\kappa_m)$：
$$\Omega_x(\theta)=\tfrac12\chi_0'(x)+\sum_{m=1}^{n-2}e^{-mx}\,\nu_m(x)\cos m\theta,\qquad
\nu_m=\sigma_m\kappa_m'=\kappa_m\,\mathbb E\Bigl[\chi_m(x+T)\bigl(\ell_m'(x)-\ell_m'(x+T)\bigr)\Bigr],$$
$\ell_m=\log\chi_m$，$T$ 為參數 $m$ 的指數分布。所以 $\nu_m\ge0$ 可由 **$\chi_m$ 對數凹** 推出（待檢驗的單變數性質）。
主階的 $e^{-mx}$ 已被精確提出，$\nu_m$ 是「混疊階」的量。

**教訓：任何用來估計係數的不等式，都必須在幾何數列上取等。**
我試了用 $(k,\Gamma)\mapsto k^2/\Gamma$ 的聯合凸性來證 $\Omega$ 的係數對 $m$ 為凸：
$\Delta^2_m(k_m^2/\Gamma_m)\ge2[2r_m\rho_n\sinh Nx-r_m^2B_N]$。但 $x\to\infty$ 時這個下界在主階上是負的（相對 $-1/(m-1)$），
而真實的量在主階上恰好為零（$k_m\propto e^{-mx}$ 時 $k'+k^2/\Gamma\equiv0$）。
所有先前失敗的一階論證（凸泛函、Fejér 混合表示下的幾何平均、理想化的瞬時核）都是同一個原因：
它們在純幾何數列上不是等式，於是主階的誤差蓋過了真正決定符號的混疊階。
**可行的論證必須用正規化的變數 $(\chi_m,\sigma_m,\kappa_m)$ 來寫**，在那裡主階已經被精確消掉。

### 4.3f $\chi_m$ 的對數凹性、(T1) 的必要形式、與多邊形穩定性的關係 [文字]

**(a) $\chi_m$ 對數凹：化約完成，最後一步未證。**
$(\log\chi_m)''=(\log\sigma_N)''+\dfrac{n^2}{2\sinh^2(nw/2)}$，$\sigma_N=\sinh Nw-N\sinh w$。第二項對 $n$ 遞減（$y^2/\sinh^2y$ 遞減），
所以只需 $n=N$ 的情形：$\varphi_N(w)=\dfrac{\sinh Nw-N\sinh w}{\cosh Nw-1}$ 對數凹（$N\ge2$）。它的對數導數有緊湊形式
$$(\log\varphi_N)'=\coth\tfrac w2\cdot\frac{\eta\,(X-1)}{1-\eta},\qquad\eta=\frac{N\sinh w}{\sinh Nw}\in(0,1),\quad X=\frac{N\tanh(w/2)}{\tanh(Nw/2)}\in[1,N).$$
對數凹性等價於一個雙曲函數的多項式不等式 $E_N(w)\le0$，其中
$E_N=N^2(B-1)^2+2N^2B(B-1)c-N(N^2+1)(B-1)As-2N^3As+N^4s^2$（$A=\sinh Nw$，$B=\cosh Nw$，$s=\sinh w$，$c=\cosh w$）。
展開成 $\cosh(kw)$ 的線性組合後係數和為零、最高頻係數為 $-\tfrac14N(N-1)^2<0$。數值上 $(\log\varphi_N)''<0$（$N\le25$ 的小檢查）。
還缺 $E_N\le0$ 的完整論證（可能的做法：逐項 Taylor 係數的符號，或對 $N$ 歸納）。**狀態：[猜想]，化約為 [文字]。**
這條引理給出係數 $\nu_m\ge0$，即 $\Gamma_m$ 對數凹，但它不是缺口的核心。

**(b) (T1) 真正必要的部分只在節點上。**
$L(y;\theta)=E_\alpha(\theta)+\tfrac12y^2\Omega_\alpha(\theta)+\dots$，而 $E_\alpha$ 只在節點 $\theta_k=2\pi k/n$ 為零。所以局部必要條件是 $\Omega_\alpha(\theta_k)\ge0$。
因為 $h_x$ 在節點上對所有 $x$ 內插 $g_x$，節點上有
$$L(y;\theta_k)=\Bigl[g_\alpha-\tfrac12(g_p+g_q)\Bigr](\theta_k)+\tfrac12\sum_m\bigl(\psi_m(p)-\psi_m(q)\bigr)^2\cos m\theta_k,\qquad\psi_m=\sqrt{\Gamma_m},$$
第一項完全顯式：$\tfrac14\log\dfrac{(\cosh p-x_k)(\cosh q-x_k)}{(\cosh\alpha-x_k)^2}$。無窮小形式：
$$\Omega_\alpha(\theta_k)=\underbrace{\tfrac12\,\frac{1-\cosh\alpha\cos\theta_k}{(\cosh\alpha-\cos\theta_k)^2}}_{\text{位勢對半徑的曲率}}+\underbrace{\sum_m\frac{k_m(\alpha)^2}{\Gamma_m(\alpha)}\cos m\theta_k}_{\text{係數族的 Fisher 資訊量，在 }\mathbb Z_n\text{ 上的離散餘弦變換}} .$$

**(c) 與正多邊形的二階變分（穩定性）的關係。**
主定理在等對角的正 $n$ 邊形處取等，所以能量減去 $\sum_i\varphi(\rho_i)$ 在該處的 Hessian 必須半正定。
這是一個循環矩陣，可用離散 Fourier 模態對角化；每個模態是「徑向／切向」的 $2\times2$ 區塊。
這和 Thomson（1883）、Havelock（1931）對渦旋正多邊形的線性穩定性分析是同一種計算（這裡的交互作用是鏡像型的 $-\log|1-z_i\bar z_j|$）。
(b) 中的節點條件是證書在二階上成立所需的條件；Hessian 半正定是定理本身在二階上的必要條件。兩者的精確關係值得算清楚：
若它們等價，(T1) 在節點上的敘述就化為一個有封閉形式的經典計算。**這是下一步要用文字做的事。**

### 4.3g 正多邊形處的二階變分：結果 [文字，小計算核對]

**恆等式（對任何構形都精確成立）。** 令 $\mathcal E=\sum_{i\ne j}-\log|1-a_{ij}|$，$\varphi(p)=-\log F_n(e^{-p})$，$S_m=\sum_{i,j}\psi_m(p_i)\psi_m(p_j)\operatorname{Re}c_{ij}^m\ge0$。則
$$\mathcal E-\sum_i\varphi(p_i)=\sum_{i\ne j}L(\theta_{ij};p_i,p_j)+\sum_{m=1}^{n-2}S_m .$$
這就是證書論證本身；它說明定理的餘量恰好是「成對缺口」加「Schur 餘量」。

**定理在二階上的必要條件是初等的。** 在等對角的正 $n$ 邊形處，對徑向擾動 $a_i$ 與切向擾動 $t_i$ 的 Hessian 是循環的。記 $d=e^{-x}$，$u=d^n$，
$\mathbb B_\ell=\sum_{j\equiv\ell\,(n)}j\,d^j=d^\ell\bigl[\tfrac{\ell}{1-u}+\tfrac{nu}{(1-u)^2}\bigr]$。直接計算得 $\varphi''=n\mathbb B_0-\tfrac{d}{(1-d)^2}$，每個模態 $\ell$ 的 $2\times2$ 區塊為
$n\begin{pmatrix}T_\ell/4&-is_\ell\\ is_\ell&T_\ell\end{pmatrix}$，$T_\ell=n(\mathbb B_\ell+\mathbb B_{n-\ell}-2\mathbb B_0)$，$s_\ell=\tfrac n2(\mathbb B_\ell-\mathbb B_{n-\ell})$。
半正定等價於 $\min(\mathbb B_\ell,\mathbb B_{n-\ell})\ge\mathbb B_0$，即
$$\frac{e^{nx}-1}{n}\ \ge\ \frac{e^{\ell x}-1}{\ell}\qquad(1\le\ell\le n-1),$$
由指數函數的凸性成立。這與 Lean 中 `exp_sub_one_scaling` 是同一條不等式。

**證書在二階上的條件更強。** 節點上 $\Omega_x(\theta_k)=-\sum_{\ell=1}^{n-1}\varepsilon_\ell(x)\cos\frac{2\pi k\ell}n$，
$\varepsilon_\ell=\mathbb B_\ell-\mathbb B_0-\dfrac{k_\ell^2}{\Gamma_\ell}$（$\varepsilon_0=\varepsilon_n=0$）。所以
**節點上的 (T1) 等價於 $\ell\mapsto\varepsilon_\ell(x)$ 的對稱部分是 $\mathbb Z_n$ 上的負定函數**（Schoenberg 意義；Lévy–Khinchin 權重正比於 $\Omega_x(\theta_k)$）。
首階上 $\varepsilon^{\rm sym}_\ell\approx3\sinh x\,d^n\,\ell(n-\ell)-nd^n\bigl(1-\tfrac{d^\ell+d^{n-\ell}}2\bigr)$：一個凹拋物線（負定）減去一個 Poisson 型的項，與先前的「三倍餘量」一致。

**一條新的單變數不等式 (S)。** [猜想，小計算成立] $\varepsilon_m\ge0$，即 $\dfrac{k_m^2}{\Gamma_m}\le\mathbb B_m-\mathbb B_0$，是 $k_m\le m\Gamma_m$ 的加強。
它由一條顯式的逐點不等式推出：令 $\mathfrak B=\mathbb B_m-\mathbb B_0$，若 $\mathfrak B^2+2k_m'\mathfrak B-k_m\mathfrak B'\ge0$，則 $(k_m^2/\mathfrak B)'\ge-k_m=\Gamma_m'$，積分得 (S)。

### 4.3h 「搬運」的觀點與另一條單調路徑 [文字]

$D_{p,q}(\theta)=\int_p^q\bigl[\tfrac12k_0'(x)+\sum_mM_m(x)\,\omega_m(x)\cos m\theta\bigr]dx$，$M_m(x)=\dfrac{\sqrt{\Gamma_m(p)\Gamma_m(q)}}{\Gamma_m(x)}$，$\omega_m$ 是 $\Omega_x$ 的係數。
若把 $\Gamma_m(x)/\Gamma_m(0)$ 讀成一個隨機變數 $W_m$ 的存活機率（密度正比於 $k_m$，危險率 $r_m\le m$），則 $M_m$ 是條件存活機率的比。
$x<\alpha$ 時 $M_m\le1$（向圓內搬運，保持正性）；$x>\alpha$ 時 $M_m$ 可以大於 1（向圓外搬運）。
所以 (T2) 不能單純由 (T1) 加上「卷積保持正性」得到：外側那一半一定要用到阻尼。

**另一條路徑：固定半徑差 $b$，對 $\alpha$ 單調。** 因為 $\alpha\to\infty$ 時 $L\to0$，若 $\partial_\alpha L\le0$ 則 $L\ge0$。直接計算：
$$-2\,\partial_\alpha L=\mathcal P_\alpha(\theta)-\Pi_p^{1/\lambda}(\theta)-\Pi_q^{\lambda}(\theta),\qquad\lambda_m=\sqrt{\Gamma_m(p)/\Gamma_m(q)},$$
其中 $\Pi^{\lambda}$ 表示把瞬時核的第 $m$ 個係數乘上 $\lambda_m$。$b=0$ 時右邊是 $\mathcal P_\alpha-2\Pi_\alpha=\rho_n\mathrm{Fej}_n\mathcal P_\alpha\ge0$，正是誤差公式的被積函數。
所以這條路徑把誤差公式自然地推廣成「兩點的瞬時不等式」：
$$\textbf{(IP)}\qquad\mathcal P_a(\theta)\ \ge\ \Pi_{a-b}^{1/\lambda}(\theta)+\Pi_{a+b}^{\lambda}(\theta)\qquad(a\ge b\ge0).$$
Star 是 (IP) 對 $a$ 從 $\alpha$ 積到 $\infty$。係數全部非負（$\sqrt{\sigma_p\sigma_q}(\kappa_p+\kappa_q)\le2$）。(IP) 是否逐點成立，正在用小計算檢查。

### 4.3i 單側的化約：Star ⟸ (H_in) [文字；小計算支持]

對 $p\le q$ 把缺口 $L(\theta;p,q)$ 對**較小的參數 $p$** 微分（$\alpha=\frac{p+q}2$，$G_\alpha=-\log|1-e^{-\alpha}e^{i\theta}|$，$\partial_\alpha G_\alpha=-\tfrac12(\mathcal P_\alpha-1)$，$\Gamma_0'=-\tfrac12(k_0-1)$，$\Gamma_m'=-k_m$）：
$$\partial_pL=-\tfrac12\,H_{\rm in}(p,q;\theta),\qquad
H_{\rm in}:=\tfrac12\mathcal P_\alpha(\theta)-\tfrac12k_0(p)-\sum_{m=1}^{n-2}k_m(p)\sqrt{\frac{\Gamma_m(q)}{\Gamma_m(p)}}\,\cos m\theta .$$

**(H_in)：對所有 $0\le p\le q$、$\theta$，$H_{\rm in}\ge0$。**

若 (H_in) 成立，則 $p\mapsto L(\theta;p,q)$ 在 $[0,q]$ 上不增，於是 $L(\theta;p,q)\ge L(\theta;q,q)=E_q(\theta)\ge0$（等對角情形，已在 Lean）。即 **Star ⟸ (H_in)**。

為什麼這個形式比較好：

- 它只涉及**外側**那個點（半徑較大的 $p$）的瞬時核 $\Pi_p$，乘子 $\sqrt{\Gamma_m(q)/\Gamma_m(p)}\in(0,1]$ 是向圓內的搬運。先前所有形式都需要把內側的點向圓外延拓。
- $q=p$ 時 $H_{\rm in}=\tfrac12\rho_n\mathrm{Fej}_n\mathcal P_p\ge0$（已證）；$q\to\infty$ 時 $H_{\rm in}\to\tfrac12(1-k_0(p))\ge0$。
- 若乘子恰為 $e^{-m(q-p)/2}$（Poisson 半群），$H_{\rm in}$ 就是 $\tfrac12\rho_n\mathrm{Fej}_n\mathcal P_p$ 的 Poisson 平滑，顯然非負。真實乘子是 $e^{-mb}\mu_m$，$\mu_m=\sqrt{\sigma_m(q)/\sigma_m(p)}\ge1$，所以
  $$H_{\rm in}=P_b*\bigl(\tfrac12\rho_n\mathrm{Fej}_n\mathcal P_p\bigr)(\theta)-\sum_m e^{-m\alpha}\chi_m(p)\,(\mu_m-1)\cos m\theta ,$$
  要證的是 Poisson 平滑後的正餘量蓋過一個係數為「混疊階」的正定函數。
- 乘子隨 $q$ 的演化是 $\partial_q\nu_m=-\tfrac12r_m(q)\nu_m$：一個符號為危險率 $r_m(q)\le m$ 的「半群」，與 Poisson 半群（符號 $m$）比較。

對應的另外兩個方向導數：$\partial_qL=-\tfrac12H_{\rm out}$，其中 $H_{\rm out}=\tfrac12\mathcal P_\alpha-\Pi_q^{\lambda}$ **可以為負**（小計算，E37）；
$H_{\rm in}+H_{\rm out}=$ (IP) $\ge0$（小計算，E36），$H_{\rm out}-H_{\rm in}=D\ge0$。所以三條單調路徑都成立，但只有 $p$ 方向的那條是單側、向內的。

混合導數有對稱的形式：$\partial_p\partial_qL=\tfrac14\sum_m m\,e^{-m(p+q)/2}\bigl(1-\tilde\kappa_m(p)\tilde\kappa_m(q)\bigr)\cos m\theta$，$\tilde\kappa_m=\chi_m/\sqrt{\sigma_m}\in[0,1]$。

**(H_in) 目前是主要目標。**

### 4.3j (H_in) 的結構 [文字；E38 小計算]

小計算（$n=4..24$，$p\in\{0,0.01,\dots,2\}$，$q-p$ 從 $0.001$ 到 $4$，共 252 組）：$H_{\rm in}\ge0$ 全部成立，沒有負值；最小值出現在 $q\approx p$。

等價的寫法：令 $\mathcal A_p=\rho_n(p)\mathrm{Fej}_n\mathcal P_p\ge0$，$\nu_m=\sqrt{\Gamma_m(q)/\Gamma_m(p)}=e^{-mb}\mu_m$，則
$$H_{\rm in}=\tfrac12\,P_b*\mathcal A_p\;-\;\sum_{m=1}^{n-2}e^{-m\alpha}\chi_m(p)(\mu_m-1)\cos m\theta
=\tfrac12\xi_0(p)+\sum_{m\ge1}e^{-m\alpha}\bigl(1-\chi_m(p)\mu_m\bigr)\cos m\theta .$$
係數 $1-\chi_m(p)\mu_m$ 隨 $q$ 從 $\xi_m(p)$ 遞減到 $1-\tilde\kappa_m(p)\ge0$。

兩個區域的機制不同：

- **$q-p$ 不小**：係數數列對 $m$ 為凸（252 組中約六成），由 Fejér 判準直接得到非負。首階上係數是
  $(n-m)\bigl[(1-\tfrac m{2n})e^{-mb}+\tfrac m{2n}\tfrac{\sinh q}{\sinh p}e^{-2nb}e^{mb}\bigr]$，第一部分是凸的遞減數列。這裡**沒有** Poisson 型的負部分。
- **$q\approx p$**：$H_{\rm in}$ 接近 $\tfrac12\mathcal A_p$，後者在節點為零，係數不是凸的；這裡要用乘積結構。
  對 $q$ 的一階導數在節點上恰為 $\tfrac12\Omega_p(\theta_k)$，所以這個區域的必要條件就是節點上的 (T1)。

所以 (H_in) 的證明要把這兩個機制接起來：節點上的 (T1)（負定函數的敘述，4.3g）處理 $q\to p$，凸性處理其餘。

### 4.3k 這一輪排除與確認的事項 [文字；小計算]

- **$L$ 對較小參數 $p$ 不是凸的**（E39）：$H_{\rm in}(p,q)\ge H_{\rm in}(q,q)=\tfrac12\mathcal A_q$ 在 $p$ 很小時不成立。所以不能用「乘積形式的下界」一步到位。
- **$H_{\rm out}$ 可以為負**（E37），所以把 (IP) 拆成兩半只有內側那一半成立；這再次說明向圓外的搬運不保持正性。
- **$q-p$ 不小時的凸性有首階的理由**：係數的首階形式是 $e^{-np}\bigl\{2\sinh p\,(n-m)(1-\tfrac m{2n})e^{-mb}+\dots-2e^{-m\alpha}\bigr\}$。
  第一項的二階差分約為 $2\sinh p\,(2b+\tfrac1n)$，Poisson 型的第二項的二階差分約為 $-2(1-e^{-\alpha})^2$。
  所以凸性大約在 $b\gtrsim\dfrac{(1-e^{-p})^2}{2\sinh p}$ 時成立（右邊對所有 $p$ 不超過約 $0.16$）。
  $b$ 更小時，Poisson 項不能用凸性處理；$b=0$ 時它恰好把「Fejér 核乘常數」變成「Fejér 核乘 Poisson 核」，這就是乘積結構的來源。
- **節點上的 (T1) 等價於 $\mathbb Z_n$ 上的正定性**：令 $s_\ell=\omega_\ell+\omega_{n-\ell}$（$\omega_m=\Gamma_mr_m'$ 為 $\Omega$ 的係數，$s_0=k_0'$），
  則 $\Omega_x(\theta_k)=\tfrac12\sum_\ell s_\ell\cos\frac{2\pi k\ell}n$。$x=0$ 時 $s_\ell\propto\binom{n-\ell+1}3+\binom{\ell+1}3$ 是凸的，由 $\mathbb Z_n$ 上的 Pólya 判準得到正性。
  一般 $x$ 時 $s_\ell$ 含 $-c\,(e^{-\ell x}+e^{-(n-\ell)x})$ 型的項，在兩端不凸；正性仍成立但要把這一項當作（混疊後的）Poisson 核整體處理。

### 4.3l 算術平均核與幾何平均核：$W$ 的意義 [文字；E41、E42 小計算；`HIn.lean` 已形式化 4.3i]

**已形式化。** `MatrixIneq/HIn.lean`：`star_of_hIn : 3 ≤ n → HIn n → Star n`，`mainTheorem_of_hIn`（無 `sorry`）。

**$W$ 是兩個核的差。** $W:=L-E_\alpha$ 是次數 $\le n-2$ 的餘弦多項式，Poisson 尾項全部消去：
$$W(p,q;\theta)=\Bigl[\Gamma_0(\alpha)-\tfrac12(\Gamma_0(p)+\Gamma_0(q))\Bigr]+\sum_{m=1}^{n-2}\Bigl[\Gamma_m(\alpha)-\sqrt{\Gamma_m(p)\Gamma_m(q)}\Bigr]\cos m\theta
=h^{\rm AM}_{p,q}(\theta)-h^{\rm GM}_{p,q}(\theta).$$
$h^{\rm AM}=h_\alpha$ 是「算術平均核」（係數 $\Gamma_m(\frac{p+q}2)$）的證書，$h^{\rm GM}$ 是幾何平均核的。三個敘述的關係：

| | 對不等式（$g_\alpha\ge h$） | 加總的正性（$\sum_{i\ne j}\hat h\ge$ 目標） |
| --- | --- | --- |
| 幾何平均核 | **Star（未證）** | Schur 乘積定理（已證） |
| 算術平均核 | $E_\alpha\ge0$（已證，`star_diag`） | **(AMpos)（未證）**：核 $\Gamma_m(\frac{p+q}2)$ 不是半正定的 |

$W\ge0$ 同時推出兩個未證的格子（$g_\alpha\ge h^{\rm AM}\ge h^{\rm GM}$）。主定理只需要其中任何一個；(AMpos) 是最弱的充分條件，但它是 $n$ 點的敘述：
$$\sum_{i,j}\Bigl[\Gamma_0(\alpha_{ij})-\tfrac12\Gamma_0(p_i)-\tfrac12\Gamma_0(p_j)\Bigr]+\sum_{m=1}^{n-2}\sum_{i,j}\Gamma_m(\alpha_{ij})\operatorname{Re}c_{ij}^m\ \ge0 .$$
第一個和由 $\Gamma_0$ 的凹性非負（$\Gamma_0''=-\tfrac12k_0'\le0$）。

**(H★)（小計算，E41）。** 比 (H_in) 強的敘述 $H_{\rm in}\ge\tfrac12\mathcal A_\alpha$ 數值上成立，比值在 $q\to p$ 時趨於 1。它等價於
$$\Pi_p^{\nu}(\theta)\le\Pi_\alpha(\theta),\qquad\text{即}\quad
\Delta:=\tfrac12\bigl(k_0(\alpha)-k_0(p)\bigr)+\sum_{m=1}^{n-2}\Bigl[k_m(\alpha)-k_m(p)\sqrt{\tfrac{\Gamma_m(q)}{\Gamma_m(p)}}\Bigr]\cos m\theta\ \ge0 ,$$
也就是 $\partial_pW\le0$（$p\le q$）。E42：係數數列 $(d_m)$ 非負、遞減，而且除了 $n\ge16$ 靠近對角線的情形外都是凸的。
所以 $H_{\rm in}=\tfrac12\mathcal A_\alpha+\Delta$：一個乘積形式的非負項，加上一個「幾乎總是凸係數」的項。(H_in) 只需要 $\Delta\ge-\tfrac12\mathcal A_\alpha$，即 $\Delta$ 只需要在節點附近非負。

**無窮小形式是同一個。** (Mono)、(H★)、(T2) 在 $q\to p$ 時都化為
$$\Xi_p(\theta)=\tfrac12k_0'(p)+\sum_{m=1}^{n-2}\Bigl[k_m'(p)+\frac{k_m(p)^2}{\Gamma_m(p)}\Bigr]\cos m\theta\ \ge0 ,$$
而 $W=\int_0^b(b-v)\,\Upsilon(\alpha-v,\alpha+v)\,dv$，$\Upsilon=\tfrac14(k_0'(p)+k_0'(q))+\sum_m\psi_m(p)\psi_m(q)\,\tfrac12\bigl[r_m'(p)+r_m'(q)-\tfrac12(r_m(p)-r_m(q))^2\bigr]\cos m\theta$（即 (T2)）。
$n\ge16$ 時 $\Xi_p$ 的係數不凸（$p$ 固定、$n$ 大的區域：係數是 $e^{-np}\times$ 三次凸數列減去幾何型修正）。

**排除：絕對單調的緊證書不存在。** 若對角線上有一個緊的證書，其係數函數 $c_m(s)$ 都是 $s$ 的非負係數冪級數，則幾何平均核與算術平均核一致、Star 化為已證的對角情形。
但逐階比較（$s^e$ 的係數必須在節點為零、整體非負、而 $\cos(ln\theta)$ 的係數固定為 $s^{ln}/(ln)$）在 $e=n$ 這一階得到矛盾（$n=3$ 已寫出，一般 $n$ 相同）。所以係數函數裡的負項（混疊項）不可避免。

**排除：其他半正定核。** 任何光滑對稱的半正定核 $K_m(p,q)$（對角 $\Gamma_m$）在對角線附近是 $\sqrt{\Gamma\Gamma'}\,(1-2\varrho_mb^2)$，$\varrho_m\ge0$；
最小型核 $\Gamma_m(\min)e^{-m|p-q|/2}$ 的對不等式可由 Poisson 平滑直接得到，但常數項 $\Gamma_0(\min)$ 不夠（差 $\sum_{i<j}|\Gamma_0(p_i)-\Gamma_0(p_j)|$），與先前的結論一致。

**尺度極限。** $p=x/n$、$\theta=t/n$、$m=n\mu$ 時 $k_m\to\kappa(\mu,x)=\dfrac{\sinh((1-\mu)x)-(1-\mu)x}{\cosh x-1}$，
$h_p$ 成為 $t\mapsto-\tfrac12\log(x^2+t^2)$ 的帶限下界函數（在 $2\pi\mathbb Z\setminus\{0\}$ 二重內插），屬於 Beurling–Selberg 型極值問題（第三輪文獻搜尋的對象）。

### 4.3m 不含 $\theta$ 的化約：(QC) [文字；E45–E50 小計算；Lean：`QC.lean`，`mainTheorem_of_qc`]

**排除（E43、E44）。** 「瞬時」的算術平均核正性 $\sum_{i,j}\hat\Pi_{\alpha_{ij}}(c_{ij})\ge\frac n2\sum_ik_0(p_i)$ 為假（有明確反例）；
缺口核 $(p,q)\mapsto L(p,q;\theta)$ 不是 Lorentz 型（有 3–5 個正特徵值），反向 Cauchy–Schwarz 的路不通。

**分解 $H_{\rm in}=S-R$（E45）。** $S=P_b*(\tfrac12\mathcal A_p)\ge0$，$R=\sum_m e^{-m\alpha}\chi_m(p)(\mu_m-1)\cos m\theta$。數值上 $R\le0.11\,S$（十倍餘量）；
$b$ 小時 $R$ 在 $|\theta|\ge1.5\pi/n$ 為負。首階（$p$ 固定、$n$ 大）：
$$H_{\rm in}\approx2\sinh p\,e^{-np}\Bigl[\tfrac n2\varphi(0)+\sum_{m=1}^{n-1}(n-m)\varphi(m)\cos m\theta\Bigr],\quad
\varphi(m)=w(m)+\gamma\,w(2n-m),\ w(m)=\bigl(1-\tfrac m{2n}\bigr)e^{-mb},\ \gamma=\tfrac{\sinh q}{\sinh p}.$$
$\gamma=1$ 時 $\varphi$ 是 $w$ 的 $2n$ 週期化，$w$ 是正定數列（$\mathrm{Fej}_{2n}/2n$ 與 Poisson 核的卷積），所以這個和是 **Fejér 核平移的正混合** $\sum_k\omega_k\mathrm{Fej}_n(\theta-\pi k/n)$。

**精確的敘述。** 乘上 $2(\cosh\alpha-\cos\theta)>0$（即除以 Poisson 核）：
$$\mathcal Q(\theta):=\sinh\alpha-2(\cosh\alpha-\cos\theta)\,\Pi_p^{\nu}(\theta)=\frac{2\sinh\alpha}{\mathcal P_\alpha(\theta)}\,H_{\rm in}(\theta)$$
是次數 $n-1$ 的餘弦多項式，$\mathcal Q=\tfrac12a_0+\sum_{m=1}^{n-1}a_m\cos m\theta$，
$$a_0=2(\sinh\alpha-u_0\cosh\alpha+u_1),\qquad a_m=u_{m-1}+u_{m+1}-2\cosh\alpha\,u_m\ (m\ge1),\qquad
u_m=k_m(p)\sqrt{\tfrac{\Gamma_m(q)}{\Gamma_m(p)}},\ u_0=k_0(p),\ u_{n-1}=u_n=0 .$$
這個「$\alpha$-扭轉的二階差分」把 Poisson 部分 $e^{-m\alpha}$ **精確消去**；先前所有非凸性都來自那一部分。

**(QC)：對所有 $0<p<q$，數列 $(a_0,a_1,\dots,a_{n-1},0,0,\dots)$ 是凸的。**

由 Fejér 判準，(QC) $\Rightarrow\mathcal Q\ge0\Rightarrow$ (H_in) $\Rightarrow$ Star $\Rightarrow$ 主定理。(QC) 不含 $\theta$：它是 $n$ 條關於 $(p,q)$ 的不等式，每條涉及至多五個相鄰的 $m$。

更強的形式 **(TC)**：$f(0)=a_0/(2n)$、$f(m)=a_m/(2(n-m))$ 非負、不增、凸。此時 $\mathcal Q=\sum_{j,j'<n}f(|j-j'|)e^{i(j-j')\theta}=\mathrm{Fej}_n*\mu_f$，$\mu_f\ge0$，即 Fejér 核平移的正混合；對角線上 $f\equiv\sinh p\,\rho_n(p)$。

小計算（E46、E47）：$n=4,\dots,80$，$p\in[0.02,3]$，$q-p\in[5\cdot10^{-4},6]$，共約 300 組，(QC) 與 (TC) **沒有例外**，包括 $n\ge16$ 靠近對角線的情形（那裡 $W$、$\Delta$、$\Xi$ 的係數都不凸）。
$f$ 的相對曲率 $\Delta^2f/(\Delta f+\Delta f')$ 的最小值約為 $1/(2n)$，與對角線附近 $f\approx c+\kappa(n-m)^2$ 一致；$b$ 大時 $f(m)$（$m\ge1$）近似幾何數列。

$S$ 的部分是顯式的（$N=n-m$，$\rho'=\frac1{2(\cosh np-1)}$）：
$$f^S(m)=2\rho'\sinh p\;e^{-mb}\Bigl[2\sinh\tfrac p2\sinh\tfrac q2-\sinh b\,\frac{1-e^{-Np}}{N}\Bigr],\qquad
f=f^S+\frac{e^{-m\alpha}\bigl[e^{\alpha}(y_{m-1}-y_m)-e^{-\alpha}(y_m-y_{m+1})\bigr]}{2(n-m)},\quad y_m=\chi_m(p)(\mu_m-1).$$

**(QC) 是目前的主要目標。**

### 4.3n (QC) 的結構 [文字；E48–E50 小計算]

**已形式化。** `MatrixIneq/QC.lean`：`fejer_criterion`、`hIn_of_qc`、`mainTheorem_of_qc : (∀ n ≥ 3, QC n) → MainTheorem`。現在唯一未證的敘述是不含 $\theta$ 的 (QC)。

**等價形式：正的 Fejér 分解。** 以 $N=n-m$ 為指標，$\hat u_N=u_m$。因為 $\mathfrak T_\alpha$ 的基本解是 $f_N(\alpha)/(2\sinh\alpha)$，
$$\text{(QC)}\iff\hat u_N(p,q)=\sum_{j\ge0}c_j\,\frac{f_{N-j}(\alpha)}{2\sinh\alpha},\ c_j\ge0
\iff H_{\rm in}(p,q;\theta)=\tfrac12\mathcal P_\alpha(\theta)\sum_{j=0}^{n-1}\hat c_j(p,q)\,\mathrm{Fej}_{n-j}(\theta),\ \hat c_j\ge0 .$$
對角線上只有 $j=0$（$\hat c_0=\rho_n(p)$）。於是缺口有「雙半徑誤差公式」
$$L(p,q;\theta)=\tfrac12\mathrm{Fej}_n\!\int_q^\infty\!\rho_n\mathcal P_w\,dw+\tfrac14\sum_{j}\mathrm{Fej}_{n-j}(\theta)\int_p^q\hat c_j(x,q)\,\mathcal P_{\frac{x+q}2}(\theta)\,dx ,$$
是等對角情形誤差公式 $E=\tfrac12\mathrm{Fej}_n\int\rho\mathcal P$ 的推廣：低階 Fejér 核乘 Poisson 核的正混合。

**係數的對稱寫法。** $u_m=\sqrt{k_m(p)k_m(q)}\cdot\vartheta_m$，$\vartheta_m=\sqrt{r_m(p)/r_m(q)}\in(0,1]$（危險率之比）。
前一個因子是瞬時核的幾何平均（顯式）；對 $b$ 的一階效應全部來自 $\vartheta$：$\vartheta_m\approx1-b\,\lambda_m$，$\lambda_m=(\log r_m)'$。

**顯式部分單獨成立 (S-QC)。** 取 $\nu_m=e^{-mb}$（即 $S=P_b*\tfrac12\mathcal A_p$）時，
$$2(\cosh p-1)\,\mathfrak D_\alpha\bigl[f_N(p)e^{Nb}\bigr]=8\sinh p\,e^{Nb}\Bigl[(\cosh(p-b)-1)\sinh b\,e^{-Np}+2N(\cosh b-1)\sinh(\tfrac p2+b)\sinh\tfrac p2-\sinh b\,(2\cosh b-1-\cosh(p+b))\Bigr]$$
（$\mathfrak D_\alpha=\Delta^2\mathfrak T_\alpha$），數值上恆非負（E50）；即 $P_b*(\mathrm{Fej}_n\mathcal P_p)=\mathcal P_{p+b}\sum_jc^S_j\mathrm{Fej}_{n-j}$，$c^S_j\ge0$。
但把 $a=a^S+a^R$ 分開估計沒有餘量：在頂端指標 $j=n-2$、$p$ 小、靠近對角線時 $-\Delta^2a^R/\Delta^2a^S$ 達 $0.997$。

**頂端指標 $j=n-2$。** 條件是 $\hat u_3\ge2(1+\cosh\alpha)\hat u_2$，即
$$\sqrt{\frac{M(q)}{M(p)}}\ \ge\ \frac{1+\cosh\alpha}{\cosh\alpha+\cosh b},\qquad M(x)=\frac{r_2(x)}{r_3(x)}=\frac{\int_x^\infty(1+\cosh w)\,d\beta}{(1+\cosh x)\int_x^\infty d\beta},\quad d\beta=\sinh w\,\rho_n(w)\,dw .$$
右邊 $\le1$，所以只要 **$M=r_2/r_3$ 不減**（這也是該指標的無窮小條件）。$M$ 由 $1+O(n^{-2})$ 增到 $1+\frac1{n-3}$。
在 $p\to0$、$n\to\infty$ 時這個條件化為 $5\zeta(5)\ge3\zeta(3)^2$（$5.18\ge4.33$）：成立但不是「軟」的，取決於 $\rho_n$ 的矩。

**所以 (QC) 是關於危險率族 $r_N(x)=\dfrac{\rho_n(x)f_N(x)}{\int_x^\infty\rho_nf_N}$ 的一組精細性質**（相鄰 $N$ 的危險率之比的單調性及其高階類比）。
小計算：$p$ 小到 $10^{-4}$、$q-p$ 由 $10^{-5}$ 到 $12$、$n\le14$（E49）以及 $n\le80$（E47）都沒有例外；最緊的指標是 $j=n-2$。

**第三輪文獻（`notes/literature-3.md`）。** 沒有找到能給出 (QC) 或 Star 的結果。相關的新文獻：Ounaïes, arXiv:2601.10411（Alexander 猜想；秩一、等半徑情形，Hardy 空間中的 Cauchy–Schwarz 證書），
其 Theorem 3 $\sum_{j,k}\frac1{1-\bar z_jz_k}\ge\frac{n^2}{1-|\prod z_j|^2}$ 允許不等的模，但對不等對角線比我們需要的弱。Beurling–Selberg 理論（Carneiro–Vaaler、Carneiro–Littmann–Vaaler）給出極值函數的存在與顯式變換，沒有關於兩個參數的係數幾何平均的結果。

### 4.3o 機率結構：輪廓的可除性 [文字；細節在 `notes/qc-route.md` 第 9 節]

- **$\chi_m$ 是分佈函數**：$\chi_m(x)=\mathbb P(\tilde G_1+\tilde G_2+G_3'\le n-m-2)$，$\tilde G_{1,2}$ 為（截斷的）$\mathrm{Geom}(e^{-x})$，$G_3'\sim\mathrm{Geom}(e^{-2x})$。[已證：母函數 $\frac{(1-t)^2(1-t^2)}{(1-x)(1-tx)^2(1-t^2x)}$]
- **(QC) $\iff$ 輪廓 $N\mapsto v_{n-N}$（$v_m=\chi_m(p)\mu_m$）可被參數 $r=e^{-(p+q)/2}$ 的理想輪廓整除**：$v_{n-N}=\mathbb P(S_r+Y\le N-2)$，$Y\ge0$ 獨立。
  等價地 $(z-r)^2(z-r^2)D(z)$ 係數非負。
- **(S-QC) 已證**：$\mu\equiv1$ 時由 $\mathrm{Geom}(t)\overset d=\mathrm{Geom}(r)+Y$（$t\ge r$）得到。即 Poisson 平滑後的對角核 $P_b*(\mathrm{Fej}_n\mathcal P_p)$ 是 $\mathcal P_{p+b}$ 乘上低階 Fejér 核的正混合。
- 剩下的是 $\mu_m=\sqrt{\sigma_m(q)/\sigma_m(p)}$ 的部分：$\sigma_m(x)=\mathbb E\chi_m(x+T/m)$ 是輪廓的混合（混合測度依賴 $m$），外加平方根。

### 4.4 還沒有的東西

沒有一個對一般 $n$ 完整的文字證明。最接近的是 B：需要 (i)、(ii) 兩條引理各自的完整論證，
以及對角線接近 1（$p\to0$）時的處理。在這三件事有文字證明之前，一般 $n$ 的 Star 不能形式化。

## 5. 形式化的順序

依「文字證明已經完整」的程度：

1. **等對角定理（所有 $n$）**：**已完成**（`MatrixIneq/EqualDiag.lean`）。`mainTheorem_const_diag`：對角元全相等的半正定矩陣滿足主不等式；
   `prod_offdiag_le_pow_of_unit_diag`：單位對角時 $\prod_{i\ne j}|1-a_{ij}|\le n^n$。無 `sorry`，只依賴標準公理。
2. 第 3 節第 1、4、7 條這些單變數性質：各自是短的引理，形式化它們就是在檢驗文字推導。
3. 第 4 節的引理：等文字證明完成後再形式化。
