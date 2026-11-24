# (QC)：不含 $\theta$ 的化約

狀態標記：[已證] 有完整文字證明；[Lean] 已形式化；[推導] 計算已做、未嚴格化；[數值] 只有小計算支持。
記號同 `docs/THEORY.md`：$\alpha=\frac{p+q}2$，$b=\frac{q-p}2$，$N=n-m$，$t=e^{-p}$，
$k_m(w)=\rho_n(w)f_N(w)$，$f_N(w)=\dfrac{\sinh Nw-N\sinh w}{\cosh w-1}=2\sum_{j=1}^{N-1}(N-j)\sinh jw$，
$\Gamma_m(x)=\int_x^\infty k_m$，$\psi_m=\sqrt{\Gamma_m}$，$r_m=k_m/\Gamma_m$，$\chi_m=e^{mw}k_m$，$\sigma_m=me^{mx}\Gamma_m$。

## 1. 鏈 [Lean：`HIn.lean`、`QC.lean`，`mainTheorem_of_qc`]

$$\text{(QC)}\ \Rightarrow\ \text{(H\_in)}\ \Rightarrow\ \mathrm{Star}(n)\ \Rightarrow\ \text{主定理}.$$

- **Star ⟸ (H_in)** [已證，Lean `star_of_hIn`]：$p\le q$ 時 $\partial_pL=-\tfrac12H_{\rm in}$，
  $H_{\rm in}=\tfrac12\mathcal P_\alpha-\Pi_p^\nu$，$\Pi_p^\nu=\tfrac12u_0+\sum_{m=1}^{n-2}u_m\cos m\theta$，
  $u_m=k_m(p)\sqrt{\Gamma_m(q)/\Gamma_m(p)}=-2\psi_m'(p)\psi_m(q)$，$u_0=k_0(p)$。$L(q,q)=E_q\ge0$ 已證。
- **(H_in) ⟸ (QC)** [已證，Lean `hIn_of_qc`]：
  $\mathcal Q:=\sinh\alpha-2(\cosh\alpha-\cos\theta)\Pi_p^\nu=\dfrac{2\sinh\alpha}{\mathcal P_\alpha}H_{\rm in}$，
  $\mathcal Q=\tfrac12a_0+\sum_{m=1}^{n-1}a_m\cos m\theta$，
  $$a_0=2(\sinh\alpha-u_0\cosh\alpha+u_1),\qquad a_m=u_{m-1}+u_{m+1}-2\cosh\alpha\,u_m\quad(m\ge1,\ u_{n-1}=u_n=0).$$
  若 $(a_0,a_1,\dots,a_{n-1},0,\dots)$ 是凸數列，由 Fejér 判準 $\mathcal Q\ge0$。

**(QC)：對所有 $0<p<q$，$a_j-2a_{j+1}+a_{j+2}\ge0$（$j\ge0$）。** [數值，E46–E47，$n\le80$ 無例外]

**(TC)**（更強）：$f(0)=\dfrac{a_0}{2n}$，$f(m)=\dfrac{a_m}{2(n-m)}$ 非負、不增、凸。此時 $\mathcal Q=\mathrm{Fej}_n*\mu_f$，$\mu_f\ge0$。[數值，同上]

不成立的更強性質（E48）：$f$ 不是對數凸的（比值最小 $0.990$），不是三階以上完全單調，$e^{mb}f(m)$ 不單調。

## 2. 為什麼 $\alpha$-扭轉有效

算子 $\mathfrak T_x[y]_m=y_{m-1}+y_{m+1}-2\cosh x\,y_m$ 消去 $e^{\pm mx}$。

- $\mathfrak T_w[k_\cdot(w)]_m=2\rho_n(w)\sinh w\,(n-m)$（因為 $f_{N+1}+f_{N-1}-2\cosh w\,f_N=2N\sinh w$）。
  所以對角線上 $a_m=2\rho_n(p)\sinh p\,(n-m)$：線性，位於凸錐的邊界；$\mathcal Q=\sinh p\,\rho_n\mathrm{Fej}_n$。
- $H_{\rm in}$ 的係數 $c_m=e^{-m\alpha}-u_m$ 的尾項 $e^{-m\alpha}$（$m\ge n-1$）被 $\mathfrak T_\alpha$ 消成零，所以 $\mathcal Q$ 是多項式。
- 先前的非凸性（$n\ge16$）全部來自 $-e^{-m\alpha}$ 型的 Poisson 部分；扭轉後它不存在。

## 3. 顯式部分 [推導]

$H_{\rm in}=S-R$，$S=P_b*(\tfrac12\mathcal A_p)$，$R=\sum_me^{-m\alpha}\chi_m(p)(\mu_m-1)\cos m\theta$，$\mu_m=\sqrt{\sigma_m(q)/\sigma_m(p)}$。
$S$ 的係數是顯式的：$s_m=\rho'e^{-mb}\bigl[2(n-m)\sinh p-2e^{-mp}+2e^{-np}\cosh mp\bigr]$，$\rho'=\frac1{2(\cosh np-1)}$。扭轉後
$$f^S(m)=2\rho'\sinh p\;e^{-mb}\Bigl[2\sinh\tfrac p2\sinh\tfrac q2-\sinh b\;g_N\Bigr],\qquad g_N=\frac{1-e^{-Np}}{N}.$$
$f^S$ 本身在對角線附近**不是**凸的（$-g_{n-m}$ 對 $m$ 為凹，量級 $b$）；凸性來自 $R$ 的部分，兩者在 $1/N$ 這一階恰好相消（第 5 節）。

## 4. 對 $q$ 的導數 [推導]

$\partial_qu_m=-\tfrac12r_m(q)u_m$，所以
$$\partial_qa_m=-\sinh\alpha\;u_m-\tfrac12\,\mathfrak T_\alpha[M]_m,\qquad
M_m(p,q)=r_m(q)u_m=\frac{k_m(p)k_m(q)}{\sqrt{\Gamma_m(p)\Gamma_m(q)}}=4\psi_m'(p)\psi_m'(q)\quad(\text{對 }p,q\text{ 對稱}).$$

## 5. 無窮小形式 (ITC) [推導]

$q\to p$：$f(m)=\sinh p\,\rho_n(p)+b\,f_1(m)+O(b^2)$，
$$f_1(m)=-\frac{2\sinh p\,F_N+X_{N+1}+X_{N-1}-2\cosh p\,X_N}{2N},\qquad F_N=k_m(p),\quad X_N=\frac{k_m(p)^2}{\Gamma_m(p)}=k_mr_m,\quad X_0=X_1=X_n=0 .$$

**(ITC)：$N\mapsto\dfrac{2\sinh p\,F_N+\mathfrak T_p[X]_N}{N}$ 在 $N=1,\dots,n$ 上是凹的（且 $f_1$ 對 $m$ 不增）。**

等價寫法：令 $\varpi_m=(m-r_m)k_m\ge0$，$C_2=\dfrac{2\sinh p}{\cosh np-1}$，則 (ITC) $\iff m\mapsto\dfrac{\mathfrak T_p[\varpi]_m}{n-m}-C_2\,g_{n-m}$ 為凸。

- 若沒有虧量（$r_m=m$），則 $\mathfrak T_p[\varpi]=0$，剩下 $-C_2g_{n-m}$ 是凹的：(ITC) 為假。所以 $\varpi$ 的精確大小是必要的。
- 首階（$p$ 固定，$n$ 大，$N$ 不小）：$\varpi_m\approx\dfrac{2\sinh p}{n}e^{-np}\,mN^2$，
  $\dfrac{\mathfrak T_p[\varpi]_m}{N}\approx\dfrac{2\sinh p}{n}e^{-np}\Bigl[-2mN(\cosh p-1)-6+\dfrac{2n}{N}\Bigr]$；
  其中 $\dfrac{4\sinh p\,e^{-np}}{N}$ 與 $-C_2g_N\approx-\dfrac{4\sinh p\,e^{-np}}{N}$ **恰好相消**，
  留下 $\dfrac{4\sinh p(\cosh p-1)}{n}e^{-np}N^2+\text{線性}$：凸，曲率 $\dfrac{8\sinh p(\cosh p-1)}{n}e^{-np}$，與 E47 的相對曲率 $\approx\frac1{2n}$ 相符。

## 6. 首階模型 [推導]

$p$ 固定、$n$ 大時 $H_{\rm in}$ 的係數 $\approx2\sinh p\,e^{-np}(n-m)\varphi(m)$，$\varphi(m)=w(m)+\gamma w(2n-m)$，$w(m)=(1-\frac m{2n})e^{-mb}$，$\gamma=\frac{\sinh q}{\sinh p}$。
$\gamma=1$ 時 $\varphi$ 是正定數列 $w$（核 $\frac{\mathrm{Fej}_{2n}}{2n}*P_b\ge0$）的 $2n$ 週期化，所以
$H_{\rm in}\approx\sum_{k\in\mathbb Z_{2n}}\omega_k\,\mathrm{Fej}_n(\theta-\tfrac{\pi k}n)$，$\omega_k\ge0$。這是 (TC) 的來源。

## 7. 證明 (QC) 還需要的 [未做]

- (ITC) 對所有 $n,p,N$：需要 $r_m$（即 $\Gamma_m$）的雙邊估計，精度要到 $\varpi$ 的首階以下；$N$ 小（$m$ 接近 $n$）時展開失效，要直接處理。
- 由 (ITC) 到 (QC)（$q$ 不接近 $p$）：遠離對角線時 $f(m)\approx Ce^{-mb'}$，凸性的餘量大；中間區域需要一個單調性或直接估計。
- 一個可能的簡化：$n$ 只經由測度 $\rho_n(w)\,dw$ 與範圍 $N\le n$ 進入（$f_N$ 與 $n$ 無關）。把 $\frac1{\cosh nw-1}$ 換成 $2e^{-nw}$（只取混疊的第一項）得到全顯式的模型，誤差的相對量級是 $e^{-np}$。

## 8. 危險率的形式 [推導；E49、E50]

以 $N=n-m$ 為指標：$F_N(x)=\rho_n(x)f_N(x)$，$G_N(x)=\int_x^\infty F_N$，$r_N=F_N/G_N$，$\hat u_N=u_m$。

- $\hat u_N=\sqrt{F_N(p)F_N(q)}\cdot\vartheta_N$，$\vartheta_N=\sqrt{r_N(p)/r_N(q)}=\exp\bigl(-\tfrac12\int_p^q\lambda_N\bigr)$，$\lambda_N=(\log r_N)'=F_N'/F_N+r_N$。
- (QC) $\iff\mathfrak D_\alpha[\hat u]\ge0$，$\mathfrak D_\alpha=\Delta^2\mathfrak T_\alpha$，核為 $\{1,N,e^{\pm N\alpha}\}$；符號 $D(c)=4(\cosh c-1)(\cosh c-\cosh\alpha)$（作用在 $e^{Nc}$ 上），$|c|<\alpha$ 時為負。
- (QC) $\iff\hat u_N=\sum_{j\ge0}c_jf_{N-j}(\alpha)/(2\sinh\alpha)$，$c_j\ge0$（$\mathfrak T_\alpha$ 的基本解是 $\sinh(N\alpha)/\sinh\alpha$，與斜坡卷積得 $f_N(\alpha)/(2\sinh\alpha)$）。
- (ITC) $\iff N\mapsto\mathfrak T_p[F_N\lambda_N]_N/N$ 為凹；$\mathfrak T_p[F\lambda]_N=2N\rho\sinh p\,\lambda_N-F_{N+1}(\lambda_N-\lambda_{N+1})+F_{N-1}(\lambda_{N-1}-\lambda_N)$。
- 頂端（$N=2$）：(ITC) $\iff\lambda_3\le\lambda_2\iff r_2/r_3$ 不減；而且這個無窮小條件直接推出該指標的整體條件（因為 $(1+\cosh p)(1+\cosh q)\ge(1+\cosh\alpha)^2$）。
  $p\to0$、$n\to\infty$：$\dfrac{5\zeta(5)}{6\zeta(3)^2}=0.598\ge\tfrac12$。
- $Np\gg1$、$N\ll n$：$\lambda_N\approx\dfrac{2N^2e^{-Np}}{n}\bigl(N\sinh p-2\cosh p\bigr)$。
- $Np\ll1$：$f_N(w)\approx\frac{N^3-N}3w\bigl[1+w^2(\tfrac{N^2+1}{20}-\tfrac1{12})\bigr]$，$\nu_N$ 的 $N$ 依賴在首階消失，$a_N$ 的 $N^3$ 係數是 $\tfrac{14}{30}+\tfrac6{30}-\tfrac{20}{30}=0$：凸性由下一階決定。

待做：對一般 $N$ 找出像頂端那樣的「無窮小 ⟹ 整體」的論證；把 (ITC) 寫成相鄰危險率的比較並證明。

## 9. 機率形式：可除性 [已證的部分標明；其餘推導]

**輪廓是分佈函數 [已證，直接展開]。** $t=e^{-x}$，$P_N(t)=1-t^{2N}-Nt^{N-1}(1-t^2)$，則
$$P_N(t)=\mathbb P\bigl(G_1+G_2+G_3'\le N-2\bigr),\qquad G_1,G_2\sim\mathrm{Geom}(t),\ G_3'\sim\mathrm{Geom}(t^2)\ \text{獨立},\quad \mathbb P(G=k)=(1-t)t^k ,$$
因為 $\sum_N P_N(t)x^N$ 對應 $\dfrac{(1-t)^2(1-t^2)}{(1-x)(1-tx)^2(1-t^2x)}$（$N=2,3,4$ 已手算核對）。於是
$$\chi_m(x)=\frac{P_{n-m}(t)}{(1-t^n)^2}=\mathbb P\bigl(\tilde G_1+\tilde G_2+G_3'\le n-m-2\bigr),$$
$\tilde G_i$ 是截斷在 $\{0,\dots,n-1\}$ 上的幾何分佈。$\chi_m$ 對 $x$ 遞增（`chi_mono`）對應 $G=\lfloor E/x\rfloor$ 對 $x$ 遞減。

**(QC) 的機率敘述 [推導]。** 令 $v_m=e^{m\alpha}u_m=\chi_m(p)\mu_m$，$\delta_k=v_{k-1}-v_k$（$\delta_0=1-v_0$），$D(z)=\sum_k\delta_kz^k$，$r=e^{-\alpha}$。則
$$\text{(QC)}\iff(z-r)^2(z-r^2)\,D(z)\ \text{的係數非負}\iff N\mapsto v_{n-N}\ \text{是}\ \mathbb P(S_r+Y\le N-2)\ \text{型},$$
$S_r=G_1+G_2+G_3'$（參數 $r,r,r^2$），$Y\ge0$ 與 $S_r$ 獨立。即 **$v$ 的輪廓可被參數 $r=e^{-(p+q)/2}$ 的理想輪廓「整除」**。
$H_{\rm in}$ 的係數是 $e^{-m\alpha}\,\mathbb P(S_r+Y>N-2)$。

**顯式部分 (S-QC) [已證，模邊界指標的整理]。** $\mu\equiv1$ 時 $v_m=\chi_m(p)$，輪廓是 $S_t$ 的分佈函數（$t=e^{-p}>r$）。
$\mathrm{Geom}(t)\overset d=\mathrm{Geom}(r)+Y_{t,r}$，$Y_{t,r}\ge0$：母函數之比 $\dfrac{1-t}{1-r}\cdot\dfrac{1-rx}{1-tx}=\dfrac{1-t}{1-r}\bigl[1+\sum_{k\ge1}(t-r)t^{k-1}x^k\bigr]$ 係數非負（$t\ge r$）。
同理 $t^2\ge r^2$。所以 $S_t\overset d=S_r+Y$，(S-QC) 成立：$P_b*(\mathrm{Fej}_n\mathcal P_p)=\mathcal P_{p+b}\sum_jc^S_j\mathrm{Fej}_{n-j}$，$c_j^S\ge0$。

**完整的 (QC)。** $\sigma_m(x)=\mathbb E\,\chi_m(x+T/m)$（$T\sim\mathrm{Exp}(1)$）是輪廓的混合，但混合測度依賴 $m$，而且 $\mu_m=\sqrt{\sigma_m(q)/\sigma_m(p)}$ 有平方根。
已知的數值事實：$\chi_m(p)\le v_m\le\chi_m(\alpha)$（即 $v_m=\chi_m(x^*_m)$，$p\le x^*_m\le\alpha$）。若 $x^*_m$ 與 $m$ 無關，(QC) 由上面的可除性立即得到；實際上 $x_m^*$ 依賴 $m$，需要的是這個依賴關係與可除性相容。
