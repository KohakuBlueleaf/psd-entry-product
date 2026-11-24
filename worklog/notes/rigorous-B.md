# 選項 B：小 $n$ 的嚴格電腦輔助證明

程式在 `experiments/rigorous/`（`rig.py`、`run.py`、`tails.py`、`prod.sh`、`logs/`）。全部用球算術（python-flint／Arb，320 位元），
判定一律用球的比較（`lo > 0` 為真表示整個球在 0 的右邊）。結果表在第 9 節，未涵蓋的部分在第 10 節。

## 1. 要證的敘述

記號同 `closed-form.md`、`exact-series.md`。固定 $n\ge4$。對 $w>0$：
$$\rho_n(w)=\frac{\cosh w-1}{\cosh nw-1},\quad S_m(w)=\sum_{|l|<n}(n-|l|)e^{-|m-l|w},\quad a_m=\rho_nS_m>0,\quad A_m(x)=\int_x^\infty a_m .$$
**引理 1.** 對 $0\le m\le n-1$，$a_m(w)=e^{-mw}-k_m(w)$，$k_m=\dfrac{\sinh((n-m)w)-(n-m)\sinh w}{\cosh nw-1}$；對 $m\ge n-1$，$a_m=e^{-mw}$。

*證.* $\sum_{|l|<n}(n-|l|)x^l=\bigl(\sum_{k<n}x^k\bigr)\bigl(\sum_{k<n}x^{-k}\bigr)=\frac{2-x^n-x^{-n}}{2-x-x^{-1}}$，取 $x=e^{w}$ 得 $\sum_{|l|<n}(n-|l|)e^{lw}=1/\rho_n$。
對 $0\le m\le n-1$，把 $S_m$ 的求和在 $l\le m$ 與 $l>m$ 處分開：
$S_m=e^{-mw}/\rho_n-2\sum_{i=1}^{N-1}(N-i)\sinh(iw)$（$N=n-m$）。
由 $(2\cosh w-2)\sinh(iw)=\sinh((i+1)w)-2\sinh(iw)+\sinh((i-1)w)$ 逐項相消得
$(2\cosh w-2)\sum_{i=1}^{N-1}(N-i)\sinh(iw)=\sinh(Nw)-N\sinh w$。$m\ge n-1$ 時所有 $l\le m$，$S_m=e^{-mw}/\rho_n$。∎

於是（$1\le m\le n-2$）$\Gamma_m(x)=\int_x^\infty k_m=\frac{e^{-mx}}m-A_m(x)$，$\Gamma_0=-\tfrac12A_0$，
$$\sigma_m:=m\,e^{mx}\Gamma_m=1-\zeta_m,\qquad\zeta_m(x):=m\,e^{mx}A_m(x)\in(0,1).$$
（$\zeta_m>0$ 因 $a_m>0$；$\zeta_m<1$ 因 $k_m>0$。）

對 $0\le p\le q$，$\alpha=\frac{p+q}2$，$b=\frac{q-p}2$，定義
$$\delta_m=\frac{e^{-m\alpha}}m\,\tau_m,\quad\tau_m=\sigma_m(\alpha)-\sqrt{\sigma_m(p)\sigma_m(q)}\ (1\le m\le n-2),\qquad
2\delta_0=\tfrac12A_0(p)+\tfrac12A_0(q)-A_0(\alpha),$$
$$W(\theta)=\delta_0+\sum_{m=1}^{n-2}\delta_m\cos m\theta .$$

**引理 2（$W\ge0\Rightarrow$ Star）.** 對 $\alpha>0$，
$-\log|1-e^{-\alpha}e^{i\theta}|-\tfrac12(\Gamma_0(p)+\Gamma_0(q))-\sum_m\sqrt{\Gamma_m(p)\Gamma_m(q)}\cos m\theta=E_\alpha(\theta)+W(\theta)$，
其中 $E_\alpha(\theta)=\tfrac12\,\mathrm{Fej}_n(\theta)\int_\alpha^\infty\rho_n(w)\mathcal P_w(\theta)\,dw\ge0$。

*證.* $-\log|1-e^{-\alpha}e^{i\theta}|=\sum_{m\ge1}\frac{e^{-m\alpha}}m\cos m\theta$，$\sqrt{\Gamma_m(p)\Gamma_m(q)}=\frac{e^{-m\alpha}}m\sqrt{\sigma_m(p)\sigma_m(q)}$。
所以左邊減 $W$ 等於 $\tfrac12A_0(\alpha)+\sum_{m\ge1}A_m(\alpha)\cos m\theta$（$m\ge n-1$ 時 $A_m=e^{-m\alpha}/m$，引理 1）。
$\tfrac12S_0+\sum_{m\ge1}S_m\cos m\theta$ 是係數數列 $(n-|l|)_+$ 與 $e^{-|l|w}$ 的卷積的 Fourier 級數，等於 $\tfrac12\mathrm{Fej}_n(\theta)\mathcal P_w(\theta)$；
逐項積分（絕對收斂，$\alpha>0$）。∎

$\alpha=0$ 時 $p=q=0$，Star 化為 $E_0\ge0$（$\theta\ne0$ 時由 $\alpha\downarrow0$ 取極限；$\theta=0$ 時左邊為 $+\infty$）。
所以 **Star$(n)$ 由「對所有 $0\le p\le q$、$\theta$，$W\ge0$」推出**。

**引理 3（Fejér）.** 令 $c_0=2\delta_0$，$c_m=\delta_m$（$1\le m\le n-2$），$c_m=0$（$m\ge n-1$），$e_j=c_j-2c_{j+1}+c_{j+2}$。則
$W(\theta)=\tfrac12\sum_{j=0}^{n-2}e_j\,\dfrac{\sin^2((j+1)\theta/2)}{\sin^2(\theta/2)}$。特別地，所有 $e_j\ge0$ 蘊含 $W\ge0$。

*證.* $\frac{\sin^2(M\theta/2)}{\sin^2(\theta/2)}=\sum_{|l|<M}(M-|l|)e^{il\theta}$。右邊 $\cos m\theta$ 的係數是
$\sum_{j\ge m}(j+1-m)e_j=c_m$（有限和、相消），常數項是 $\tfrac12\sum_j(j+1)e_j=\tfrac12c_0$。∎

**本文件驗證的命題 $\mathcal C(n)$：對所有 $0\le p\le q$，$e_j\ge0$（$j=0,\dots,n-2$）。** 由引理 2、3，$\mathcal C(n)\Rightarrow$ Star$(n)$。
（$\mathcal C(n)$ 在 $n\ge16$ 為假，見 `closed-form.md`；所以這個方法只適用於 $n\le15$。）

## 2. 不含相消的公式

為避免球算術中的相消，程式只用下列形式（都是恆等式）：

- $\tau_m=\bigl[\tfrac12(\zeta_m(p)+\zeta_m(q))-\zeta_m(\alpha)\bigr]+\dfrac{(\zeta_m(p)-\zeta_m(q))^2}{2\bigl(\sqrt{1-\zeta_m(p)}+\sqrt{1-\zeta_m(q)}\bigr)^2}$，
  因為 $1-\tfrac{a+b}2-\sqrt{(1-a)(1-b)}=\tfrac12(\sqrt{1-a}-\sqrt{1-b})^2$。
- $\zeta_m$ 以乘積 $m\,e^{mx}A_m(x)$ 計算，$a_m$ 以 $\rho_nS_m$ 計算，
  $\rho_n(w)=\Bigl(\dfrac{\operatorname{shc}(w/2)}{n\operatorname{shc}(nw/2)}\Bigr)^2$，$\operatorname{shc}(y)=\sinh y/y$（在 $w=0$ 正則）。

## 3. 一變數的嚴格計算

**(a) $\operatorname{shc}$ 的 Taylor 係數。** $|y|\le\tfrac12$ 時用 $\sum_{k<40}y^{2k}/(2k+1)!$。尾項 $T(y)=\sum_{k\ge40}y^{2k}/(2k+1)!$ 在 $|y_0|\le\tfrac12$ 處的第 $i$ 個 Taylor 係數
$\le\sum_{k\ge40}\binom{2k}{i}2^{-(2k-i)}/(2k+1)!\le\sum_{k\ge40}\frac{(2k)^i}{i!}\frac{2^{i-2k}}{(2k+1)!}$；$k=40$、$i\le16$ 時首項 $<1.2\times10^{-123}$，相鄰項之比 $<\tfrac12$，
所以 $<10^{-100}$。程式對每個係數加半徑 $10^{-100}$，並斷言階數 $\le16$。$|y|\ge0.1$ 時直接用 $\sinh y/y$。

**(b) $A_m$ 在格點上的值。** 四分之一格點 $t_i=ih/4$。頂端 $A_m(t_{\rm top})$ 用級數
$$A_m=N\sum_{j\ge1}j\Bigl[\frac{s^{jn-1}}{jn-1}-\frac{s^{jn+1}}{jn+1}\Bigr]-\sum_{j\ge1}\frac{(j+1)s^{jn+m}}{jn+m}+\sum_{j\ge2}\frac{(j-1)s^{jn-m}}{jn-m},\qquad s=e^{-x},$$
（把引理 1 的 $a_m$ 以 $(1-t^n)^{-2}=\sum(j+1)t^{jn}$ 展開後逐項積分。）截斷在 $j\le J$。因 $\frac{j}{jn-1},\frac{j+1}{jn+m},\frac{j-1}{jn-m}\le1$，第 $j$ 項的三部分絕對值分別 $\le Ns^{jn-1}$、$s^{jn}$、$s^{jn-m}$，
都 $\le N s^{(j-1)n}$、$s^{(j-1)n}$、$s^{(j-1)n}$，故尾項 $\le(N+2)\sum_{j>J}s^{(j-1)n}=(N+2)s^{Jn}/(1-s^n)$。
往下用 $A_m(t_i)=A_m(t_{i+1})+\int_{t_i}^{t_{i+1}}a_m$，積分以中點的 13 階 Taylor 多項式加 Lagrange 餘項計算：
$\bigl|\int-\sum_{k<14}c_k\!\int_{-d}^{d}u^k\bigr|\le\sup_{\rm cell}|a_m^{(14)}/14!|\cdot\frac{2d^{15}}{15}$，上確界由球輸入的 Taylor 係數給出。

**(c) $Z_m$（$=\zeta_m$，$m\ge1$；$=A_0$，$m=0$）的 Taylor 係數。** 在點 $t_i$：$A_m$ 的係數為 $A_m(t_i)$ 與 $-a_m^{(k-1)}/k!$，再乘 $m\,e^{mx}$ 的級數。
在區間 $[t_c-r,t_c+r]$ 上的包絡（`zjet_ball`）：先以球輸入算到 $D+1$ 階的粗包絡
（$A_m(x)\in A_m(t_c)+a_m(\text{球})\cdot[-r,r]$），再由均值定理自上而下精化：
$z_k(x)\in z_k(t_c)+(k+1)\,z_{k+1}(\text{球})\cdot[-r,r]$（第 $k$ 個 Taylor 係數的導數是 $(k+1)z_{k+1}$），並與粗包絡取交集。

## 4. 緊緻部分的一般方格（`run.py: lower_bound_regular`）

座標 $(p,q)$，均勻格 $x_i=ih$。方格 $[x_i,x_i+h]\times[x_k,x_k+h]$，$k-i\ge K_D$。
$\zeta_m(p)$ 只依賴 $p$，$\zeta_m(q)$ 只依賴 $q$，$\zeta_m(\alpha)$ 與 $e^{-m\alpha}$ 是 $\frac{p+q}2$ 的函數，其二變數 Taylor 係數為
$z_{i+j}\binom{i+j}{i}2^{-(i+j)}$。用截斷的二變數冪級數算術（加、乘、開方、倒數；開方與倒數以冪零部分的二項級數計算）得到 $e_j$ 的

- 中心處到 $d-1$ 階的 Taylor 係數 $f_k$（點輸入，半徑極小）；
- 方格上第 $d$ 階 Taylor 係數的包絡 $F_k$（以第 3(c) 節的區間包絡為輸入；截斷冪級數算術對包含關係單調，所以輸出包住方格內每一點的係數）。

由多變數 Taylor 公式（Lagrange 餘項，方格為凸）：
$$e_j\ \ge\ f_0-\sum_{1\le|k|<d}|f_k|\,(h/2)^{|k|}-\sum_{|k|=d}|F_k|\,(h/2)^{d}.$$
程式取 $d=3$，要求右邊為正。

## 5. 對角線附近的帶狀區（`run.py: strip`，`rig.py: strip_jets`）

$k-i<K_D$ 的方格都落在 $\{\alpha\in[0,Q],\ 0\le b\le b_s\}$，$b_s=K_Dh/2$。在座標 $(\alpha,b)$ 下 $e_j=O(b^2)$，驗證 $\Phi_j:=e_j/b^2>0$。

對一變數函數 $Z$ 令
$$\tilde E=\frac{\tfrac12(Z(\alpha-b)+Z(\alpha+b))-Z(\alpha)}{b^2}=\int_0^1(1-t)\,\tfrac12\bigl[Z''(\alpha+tb)+Z''(\alpha-tb)\bigr]dt,\qquad
\tilde D=\frac{Z(\alpha-b)-Z(\alpha+b)}{b}=-\int_{-1}^{1}Z'(\alpha+tb)\,dt .$$
則 $\tau_m/b^2=\tilde E_m+\tilde D_m^2/(2\,\mathrm{den}_m^2)$，$2\delta_0/b^2=\tilde E_0$，$\Phi_j$ 是 $\frac{e^{-m\alpha}}m(\tilde E_m+\dots)$ 的二階差分。

- 在 $b=0$ 處：$\tilde E$ 的 $(d\alpha)^i(db)^{j}$ 係數為 $z_{i+j+2}(\alpha)\binom{i+j+2}{i}$（$j$ 偶），$\tilde D$ 的為 $-2z_{i+j+1}(\alpha)\binom{i+j+1}{i}$（$j$ 偶），$j$ 奇時為 0。
- 在帶狀方格的任一點：對積分表示式微分，
  $\frac{1}{i!j!}\partial_\alpha^i\partial_b^j\tilde E=\frac1{i!j!}\int_0^1(1-t)t^j\tfrac12[Z^{(s)}(\alpha+tb)+(-1)^jZ^{(s)}(\alpha-tb)]dt$，$s=i+j+2$，
  $\int_0^1(1-t)t^jdt=\frac1{(j+1)(j+2)}$；所以 $j$ 偶時它屬於 $z_s(\mathcal B)\binom{i+j+2}{i}$，$j$ 奇時絕對值不超過同一個量。
  $\tilde D$ 同理，$\int_{-1}^1|t|^jdt=\frac2{j+1}$。這裡 $\mathcal B$ 是方格內所有 $\alpha\pm tb$ 所在的區間，$z_s(\mathcal B)$ 取半格包絡的聯集。

以 $(y_l,0)$ 為中心、$\alpha\in[y_l,y_{l+1}]$（$y_l=lh/2$）、$b\in[0,b_s]$ 的 Taylor 模型（階 4）給出 $\Phi_j$ 的下界，與第 4 節同式（半徑 $h/2$ 與 $b_s$）。
方格與定義域 $p\ge0$ 的交集是凸的，且中心到任一點的線段留在其中，所以 Lagrange 餘項可用；$p$ 的區間在 0 處截斷。

**覆蓋.** 一般方格（$k-i\ge K_D$）與帶狀區合起來覆蓋 $\{0\le p\le q\le Q\}$。

## 6. 無界部分一：$p\ge P_1$（`tails.py: chart_S`）

令 $s=e^{-p}\in(0,s_0]$，$s_0=e^{-P_1}$，$q=p+2b$。由 3(b) 的級數，$Z_m(x)=\sum_e\mathrm{coef}_e\,e^{-ex}$，所有指數 $e\ge c_m:=N-1$（$m\ge1$）或 $n-1$（$m=0$）。令
$H_m(\beta)=Z_m(p+\beta)/s^{c_m}=\sum_e\mathrm{coef}_e\,s^{e-c_m}e^{-e\beta}$，它在 $s\in[0,s_0]$ 上連續，程式以 $s$ 的區間 $[0,s_0]$ 計算。
截斷 $j\le4$；尾項每個單項 $|\mathrm{coef}|\le n^2j$、正規化指數 $\ge(j-1)n-m$、$e\le jn+2$、$e^{-e\beta}\le1$，其 $\beta$-Taylor 係數（階 $\le K$）$\le n^2j(jn+2)^Ks_0^{(j-1)n-m}$，
每個 $j$ 至多 4 個單項，相鄰 $j$ 之比 $\le2^{K+1}s_0^n<\tfrac12$（程式斷言），故尾項 $\le2\times$首項，作為半徑加上。

$e_j/s^{n-1}$ 是下列量的二階差分：
$$F_m=\frac{e^{-mb}}m\Bigl[\tfrac12H_m(0)+\tfrac12H_m(2b)-H_m(b)+\frac{s^{N-1}(H_m(0)-H_m(2b))^2}{2\,\mathrm{den}^2}\Bigr],\qquad2F_0=\tfrac12H_0(0)+\tfrac12H_0(2b)-H_0(b).$$

- **$0\le b\le b_s$**：$\frac{\frac12H(0)+\frac12H(2b)-H(b)}{b^2}=\int_0^1(1-t)[2H''(2tb)-H''(tb)]dt$，其 $b^i$ 係數屬於 $2^{i+1}h_{i+2}([0,2b_s])-h_{i+2}([0,b_s])$；
  $\frac{H(0)-H(2b)}b=-2\int_0^1H'(2tb)dt$，$b^i$ 係數屬於 $-2^{i+1}h_{i+1}([0,2b_s])$。一變數 Taylor 模型（階 4）驗證 $e_j/(s^{n-1}b^2)>0$。
- **$b_s\le b\le B$**：寬 $h_b$ 的格子，一變數 Taylor 模型（階 3）。
- **$b\ge B$**：$H_m\ge0$，且 $H_m(\beta)\le H_m^+(\beta)$（只取正係數的單項，對 $\beta$ 遞減）。令 $G_m=m\,e^{mb}F_m$，則
  $G_m\ge\tfrac12H_m(0)-H_m^+(B)$，$G_m\le\tfrac12H_m(0)+\tfrac12H_m^+(2B)+T_2^{\rm up}$。
  若 $G_m^{\rm low}>0$ 則 $F_m>0$，於是 $e_j\ge F_j-2F_{j+1}\ge e^{-jb}\bigl[G_j^{\rm low}/j-2e^{-B}G_{j+1}^{\rm up}/(j+1)\bigr]$，
  $e_0/s^{n-1}\ge\tfrac12H_0(0)-H_0^+(B)-2e^{-B}G_1^{\rm up}$。

## 7. 無界部分二：$p\le P_1$、$q\ge Q_C$（`tails.py: chart_R`）

$\alpha\ge x_a:=(p_{\rm lo}+Q_C)/2$。$\zeta_m(\alpha)\le\zeta_m^+(x_a)$、$\zeta_m(q)\le\zeta_m^+(Q_C)$（正係數單項之和，遞減），$A_0$ 遞減。
$$\tau_m\ge1-\zeta_m^+(x_a)-\sqrt{1-\zeta_m(p)},\qquad\tau_m\le1-\sqrt{(1-\zeta_m(p))(1-\zeta_m^+(Q_C))}.$$
$e^{-\alpha}\le e^{-p_{\rm lo}/2}v_0$，$v_0=e^{-Q_C/2}$。若 $\tau_m^{\rm low}>0$ 對所有 $m$，則
$e_j\ge\delta_j-2\delta_{j+1}\ge e^{-j\alpha}\bigl[\tau_j^{\rm low}/j-2v_0e^{-p_{\rm lo}/2}\tau_{j+1}^{\rm up}/(j+1)\bigr]$，
$e_0\ge\tfrac12A_0(p)-A_0^+(x_a)-2v_0e^{-p_{\rm lo}/2}\tau_1^{\rm up}$。
$\zeta_m(p)$、$A_0(p)$ 在 $p$ 的每個格子上的包絡來自第 3 節。

## 8. 三個區域的覆蓋

$\{0\le p\le q\}=\{q\le Q_C\}\cup\{p\le P_1,\ q\ge Q_C\}\cup\{p\ge P_1\}$。生產參數：$Q_C=24$，$P_1=12$，$B=6$，$h=h_b=\tfrac1{100}$，$K_D=6$。
若緊緻部分在 $h=\tfrac1{100}$ 下有方格未通過，而它們全部落在 $\{q\le Q_1\}$ 內，則另以更細的格在 $\{0\le p\le q\le Q_1\}$ 上重做（第二輪）；
兩輪合起來仍覆蓋 $\{q\le Q_C\}$。

## 9. 結果

（由生產執行填入，見文末。）

## 10. 未涵蓋與注意事項

（見文末。）
