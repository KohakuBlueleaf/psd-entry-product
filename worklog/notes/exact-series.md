# 精確級數與 $W$ 的分解

記號：$s=e^{-x}$，$N=n-m$，$w_m=e^{-m\alpha}/m$，$p=\alpha-b$，$q=\alpha+b$。
$\sigma_m(x)=m\,e^{mx}\Gamma_m(x)\in[0,1]$，$\zeta_m=1-\sigma_m$。全部 [已推導]。

## 級數

把 $k_m$ 對 $t=e^{-w}$ 展開（$(1-t^n)^{-2}=\sum_{j\ge0}(j+1)t^{jn}$）後逐項積分：
$$\zeta_m(x)=m\Bigl\{N\sum_{j\ge1}j\Bigl[\frac{s^{jn-1-m}}{jn-1}-\frac{s^{jn+1-m}}{jn+1}\Bigr]-\sum_{j\ge1}\frac{(j+1)\,s^{jn}}{jn+m}+\sum_{j\ge2}\frac{(j-1)\,s^{jn-2m}}{jn-m}\Bigr\},$$
$$\Gamma_0(x)=\sum_{j\ge1}\frac{s^{jn}}{jn}-\frac n2\sum_{j\ge1}j\Bigl[\frac{s^{jn-1}}{jn-1}-\frac{s^{jn+1}}{jn+1}\Bigr].$$
所以所有係數都是 $s$ 的收斂冪級數（$0\le s<1$），係數顯式。這對嚴格數值驗證很有用：截斷後的尾項有幾何界。
（$s\to1$ 時收斂慢，該區域要改用積分表示。）

## $W$ 的精確分解

$W=h_\alpha-R=\delta_0+\sum_{m\ge1}w_m\tau_m\cos m\theta$，$\tau_m=\sigma_m(\alpha)-\sqrt{\sigma_m(p)\sigma_m(q)}$。
由 $1-\sqrt{(1-a)(1-b)}=\tfrac{a+b}2+\tfrac12(\sqrt{1-a}-\sqrt{1-b})^2$：
$$W(\theta)=\underbrace{\tfrac12c_0+\sum_{m=1}^{n-2}c_m\cos m\theta}_{W^{\rm lin}}+\underbrace{\sum_{m=1}^{n-2}\rho_m\cos m\theta}_{W^{\rho}},\qquad
\rho_m=\frac{w_m}2\bigl(\sqrt{\sigma_m(p)}-\sqrt{\sigma_m(q)}\bigr)^2\ge0,$$
其中 $c_m=w_m\bigl[\tfrac12(\zeta_m(p)+\zeta_m(q))-\zeta_m(\alpha)\bigr]$。因為 $e^{-cx}$ 在 $(p,\alpha,q)$ 的凸性虧量恰為 $e^{-c\alpha}(\cosh cb-1)$，且 $w_m$ 的因子把 $m$ 依賴消掉：
$$c_m=\sum_{j\ge1}\Bigl\{Nj\Bigl[\frac{e^{-(jn-1)\alpha}\,\mathrm{ch}((jn-1-m)b)}{jn-1}-\frac{e^{-(jn+1)\alpha}\,\mathrm{ch}((jn+1-m)b)}{jn+1}\Bigr]
-\frac{(j+1)e^{-(jn+m)\alpha}\,\mathrm{ch}(jnb)}{jn+m}+\frac{(j-1)e^{-(jn-m)\alpha}\,\mathrm{ch}((jn-2m)b)}{jn-m}\Bigr\},$$
$\mathrm{ch}(y):=\cosh y-1$。常數項恰好是 $\delta_0=\tfrac12c_0$（把 $m=0$ 代入同一公式），所以是標準的 Fejér 半權形式。

- $W^{\rm lin}=\tfrac12\bigl[E_p(e^{-b}e^{i\theta})+E_q(e^{b}e^{i\theta})\bigr]-E_\alpha(\theta)$，是誤差函數的調和延拓的組合，有封閉形式。
- **更正（E32）**：先前寫「第一族對 $m$ 為凸，條件正是 $\alpha\ge b$」是逐項粗估，不精確。精確的情況見下一節。
- $W^{\rho}$ 是正定的；對 $m\ll n$ 是二階小量，但對 $m$ 接近 $n$ 時 $c_m<0$ 而 $\rho_m$ 與之同階相消（那裡 $\sigma_m$ 是凸函數），
  所以 $W^{\rm lin}$ 與 $W^{\rho}$ 不能分開估計，$m$ 接近 $n$ 的項要用 $w_m\tau_m\ge0$ 整體處理。

## 緊湊形式 [已推導，E32 驗證到 18 位]

令
$$\Upsilon(x)=\int_x^\infty\frac{\sinh w}{\cosh nw-1}\,dw,\qquad
V_m(x)=e^{mx}\!\int_x^\infty\! e^{-mw}\bigl[(1-e^{-nw})^{-2}-1\bigr]dw,\qquad
Z_m(x)=e^{mx}\!\int_x^\infty\! e^{mw}\frac{e^{-2nw}}{(1-e^{-nw})^{2}}\,dw .$$
則誤差函數 $E_x=g_x-h_x$ 的 Fourier 係數是
$$A_m(x)=\frac{e^{-mx}}m-\Gamma_m(x)=(n-m)\,\Upsilon(x)-e^{-mx}\bigl(V_m(x)-Z_m(x)\bigr),$$
而 $c_m=D_b\bigl[x\mapsto A_m(x)e^{m(x-\alpha)}\bigr](\alpha)$，$D_b[f](\alpha)=\tfrac12(f(\alpha-b)+f(\alpha+b))-f(\alpha)$。
也就是說 $W^{\rm lin}$ 是函數 $x\mapsto E_x(e^{x-\alpha}e^{i\theta})$ 在 $\alpha$ 處的中點凸性虧量。
另外核有緊湊形式 $e^{mw}k_m(w)=\dfrac{P_N(t)}{(1-t^n)^2}$，$t=e^{-w}$，$P_N(t)=1-t^{2N}-Nt^{N-1}(1-t^2)$，分子只依賴 $N=n-m$。

三族分別是 $c^{(1)}_m=(n-m)\,D_b[e^{m(x-\alpha)}\Upsilon]$、$c^{(2)}_m=-e^{-m\alpha}D_b[V_m]$、$c^{(3)}_m=e^{-m\alpha}D_b[Z_m]$。
第一族的二階差分有封閉式
$$\Delta^2c^{(1)}_m=(n-m)(\cosh b-1)\bigl(e^{-mb}\Upsilon(p)+e^{mb}\Upsilon(q)\bigr)+\sinh b\,\bigl(e^{-mb}\Upsilon(p)-e^{mb}\Upsilon(q)\bigr).$$

## 各族的凸性（E32，數值）

| 情況 | 第一族 | 第二族 | 第三族 | 三族之和 |
| --- | --- | --- | --- | --- |
| $p$ 不小（例：$n=24$，$\alpha=0.6$，$b=0.01$） | 除最後一個指標外為凸 | 全為凹 | 可忽略（比第一族小 $10^{-7}$） | 只在首尾各一個指標為負 |
| $p\to0$（例：$n=12$，$\alpha=1$，$b=0.999$） | 凸 | 全為凹 | **與第一族同階**（比值 7.9） | 混合 |
| $\alpha$ 很小（例：$n=24$，$\alpha=0.05$） | 除尾端外為凸 | 凹 | 同階（比值 6） | 尾端多個指標為負 |

結論：

- 「三次部分減幾何部分」的圖像只在 $p$ 不小時成立。$p\to0$ 或 $\alpha\to0$ 時三族同階，不能分開處理。
- 線性部分之和在指標接近 $n$ 處的二階差分為負，由 $\rho_m$ 補回（那裡兩者同階）。
- 所以一般 $n$ 的嚴格證明至少要分兩個區域：$p\gtrsim c/n$（用三族結構）與 $p\lesssim c/n$（用連續極限的尺度），再加上指標接近 $n$ 的尾端。
