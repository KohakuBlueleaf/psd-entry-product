# Fejér 證書的封閉形式（對所有 $n$ 一致）

狀態：公式 [已推導，並以 30 位精度數值驗證（E20）]。這一族取代先前的 Cohn–Kumar 內插作為主線。

## 定義與公式

令 $s=e^{-p}$，$p\ge0$（$s>1$ 由對稱性 $c_m(s)=c_m(1/s)$、$c_0(s)=c_0(1/s)-\log s$ 處理）。記
$$\mathrm{Fej}_n(\theta)=\frac{1-\cos n\theta}{1-\cos\theta}=\prod_{k=1}^{n-1}|e^{i\theta}-\omega^k|^2,\qquad
\rho_n(w)=\frac{\cosh w-1}{\cosh nw-1},\qquad \mathcal P_w(\theta)=\frac{\sinh w}{\cosh w-\cos\theta}.$$

**誤差公式。** 令 $h_s$ 為 $g_s(\theta)=-\log|1-se^{i\theta}|$ 在所有非平凡 $n$ 次單位根處二重內插、次數 $\le n-2$ 的餘弦多項式。則
$$g_s(\theta)-h_s(\theta)=\tfrac12\,\mathrm{Fej}_n(\theta)\int_p^\infty\rho_n(w)\,\mathcal P_w(\theta)\,dw\;\ge0 .$$
來源：Hermite 誤差公式的差商，$-\tfrac12\log(c-x)$ 的差商是 $\int\prod(c'-x_j)^{-1}dc'$，節點多項式正是 $\mathrm{Fej}_n$。

**係數。** $h_s=c_0(s)+\sum_{m=1}^{n-2}c_m(s)\cos m\theta$，
$$c_m(e^{-p})=\Gamma_m(p)=\int_p^\infty k_m(w)\,dw,\qquad k_m(w)=\frac{\sinh((n-m)w)-(n-m)\sinh w}{\cosh nw-1}\;\ge0\quad(1\le m\le n-2),$$
$$c_0(e^{-p})=\Gamma_0(p)=\int_p^\infty\frac{k_0(w)-1}{2}\,dw,\qquad\frac{k_0-1}2=\frac{1-e^{-nw}-n\sinh w}{2(\cosh nw-1)}\le0 .$$
（$m=n-1$ 時公式給出 0，與次數 $\le n-2$ 一致。）

檢驗：$n=3$：$k_1=\dfrac{2\sinh w}{(1+2\cosh w)^2}$，$\Gamma_1(p)=\dfrac1{1+2\cosh p}=\dfrac s{1+s+s^2}$。
$n=4$：$\Gamma_1=\tfrac12\operatorname{sech}p$，$\Gamma_2=\tfrac14(y-\log(1+y))$，$y=\operatorname{sech}p$。均與先前的顯式結果一致。

## 這帶來什麼

1. **(CK) 不再需要引用文獻。** $h_s\le g_s$ 由誤差公式直接得到（Fejér 核與 Poisson 核都非負）；$c_m\ge0$ 由 $k_m\ge0$ 得到
   （$\sinh Nw\ge N\sinh w$）。兩者都是初等的。
2. **`Certificate n` 的 `nonneg` 與 `total` 對所有 $n$ 都可證。** `total` 是內插恆等式。
3. **(★★) 變成一條顯式的不等式。** 對 $0\le p\le q$、$\alpha=\frac{p+q}2$、所有 $\theta$：
   $$\int_\alpha^\infty\tfrac12(\mathcal P_w(\theta)-1)\,dw\;\ge\;\tfrac12(\Gamma_0(p)+\Gamma_0(q))+\sum_{m=1}^{n-2}\sqrt{\Gamma_m(p)\Gamma_m(q)}\cos m\theta .$$
   數值上（E20）$n=4..16$ 成立；$n=24$ 在 30 位精度下只剩雜訊量級。
4. **無窮小形式的四面體數有了解釋。** $k_m'(0)=\dfrac{N^3-N}{3n^2}$，$N=n-m$，正比於 $\binom{N+1}3$。
5. **對數凹性有了工具。** $\Gamma_m$ 是 $k_m$ 的尾積分；若 $k_m$ 對數凹，由 Prékopa 定理 $\Gamma_m$ 對數凹。

## SDP 的印證（E19）

在一整族對角線上同時最佳化所有正定核：最優核幾乎是秩一的（$m=1$ 精確秩一，其餘第二特徵值約為第一的 1% 到 3%），
而且偶數 $n$ 時最優對角線就是這裡的 Fejér 族（不是 Cohn–Kumar 的次數 $n-1$ 族）。提高次數幾乎沒有幫助。
所以「係數取幾何平均」不是偶然的選擇，而是這個框架裡本質上唯一的形式。

## 還缺的

(★★) 本身。已知的拆法：$L=(g_\alpha-h_\alpha)+W$，$W=\delta_0+\sum_m\delta_m\cos m\theta$，
$\delta_m=\Gamma_m(\alpha)-\sqrt{\Gamma_m(p)\Gamma_m(q)}\ge0$，$\delta_0=\Gamma_0(\alpha)-\tfrac12(\Gamma_0(p)+\Gamma_0(q))\ge0$；
粗估計 $\delta_0\ge\sum\delta_m$ 在 $n\ge4$ 不成立，必須用到 $g_\alpha-h_\alpha$ 的正部或 $\cos$ 的符號結構。

## 單調性猜想 (Mono)（E21、E22）

令 $p=\alpha-b$、$q=\alpha+b$，$L(\theta;p,q)=g_\alpha(\theta)-R_{p,q}(\theta)$。直接微分得
$$2\,\partial_bL=D_{p,q}(\theta):=d_0+\sum_{m=1}^{n-2}d_m\cos m\theta,\qquad
d_0=\hat\kappa_0(q)-\hat\kappa_0(p),\quad d_m=\sqrt{\Gamma_m(p)\Gamma_m(q)}\,\bigl(r_m(q)-r_m(p)\bigr),$$
其中 $\hat\kappa_0=\tfrac12(k_0-1)$，$r_m=k_m/\Gamma_m$ 是 $\Gamma_m$ 的危險率（$-(\log\Gamma_m)'$）。

**(Mono)**：$D_{p,q}(\theta)\ge0$ 對所有 $0\le p\le q$ 與 $\theta$。

若 (Mono) 成立，$L$ 對 $b$ 不減，所以 $L\ge L|_{b=0}=g_\alpha-h_\alpha\ge0$（誤差公式），即 (★★)。

數值：$n=4..40$，多組 $(p,q)$（高精度到 220 位）全部成立；最小值總在 $\theta=\pi$，相對餘量約 $2.3/n^2$，在 $p\to q$ 時最小。
係數 $d_m\ge0$（等價於 $\Gamma_m$ 對數凹）也都成立。

**Fejér 判準只對小 $n$ 夠用。** 若數列 $(2d_0,d_1,\dots,d_{n-2},0,\dots)$ 為凸且不增，則 $D$ 是 Fejér 核的非負組合。
$n\le16$ 時所有測試都滿足；$n\ge20$、$p\approx q$ 時只有第一個二階差分 $2d_0-2d_1+d_2$ 略為負（相對 $-0.003$ 左右），其餘仍為凸。
所以大 $n$ 需要比 Fejér 判準稍精細的論證，但 $D\ge0$ 本身沒有問題。

## 目前的證明鏈

主定理 ⟸ `Certificate n`（Fejér 族）：

| 性質 | 狀態 |
| --- | --- |
| `nonneg`：$k_m\ge0$ | 初等（$\sinh Nw\ge N\sinh w$） |
| `total` | 內插恆等式 |
| 等參數：$g_s\ge h_s$ | 誤差公式（Fejér 核乘 Poisson 核的正混合） |
| 雙參數 (★★) | ⟸ (Mono)：一個係數顯式、非負的餘弦多項式的非負性。**未證** |

## 一個精確的分解 [已推導]

利用 $g_p(e^{-b}e^{i\theta})=g_\alpha(\theta)=g_q(e^{b}e^{i\theta})$（$p=\alpha-b$，$q=\alpha+b$）以及
$\sqrt{xy}=\tfrac12(tx+y/t)-\tfrac12(\sqrt{tx}-\sqrt{y/t})^2$，取 $t=e^{-mb}$：
$$L(\theta;p,q)=\tfrac12\Bigl[E_p\bigl(e^{-b}e^{i\theta}\bigr)+E_q\bigl(e^{b}e^{i\theta}\bigr)\Bigr]+\tfrac12\sum_{m=1}^{n-2}\varepsilon_m^2\cos m\theta,$$
其中 $E_x(z)$ 是誤差函數 $g_x-h_x$ 的調和延拓（在 $|z|<e^{x}$ 上），
$\varepsilon_m=e^{-mb/2}\sqrt{\Gamma_m(p)}-e^{mb/2}\sqrt{\Gamma_m(q)}$。

- 第一項 $E_p(e^{-b}e^{i\theta})\ge0$：非負函數向圓內的調和延拓。
- 第二項是 $E_q$ 向圓外（半徑 $e^{b}$）的延拓，符號不明。
- 第三項係數是二階小量（$\Gamma_m(x)\approx e^{-mx}/m$ 時 $\varepsilon_m\approx0$），是正定函數，在 $\theta=0$ 為正、別處可負。

令 $F(\beta)=E_{\alpha+\beta}(e^{\beta}e^{i\theta})$，前兩項之和是 $\tfrac12(F(-b)+F(b))$。若 $F$ 對 $\beta$ 為凸，則它 $\ge F(0)=g_\alpha-h_\alpha$。
這把 (★★) 的幾何意義說清楚了：把兩個不同半徑的點「拉到」共同的半徑 $e^{-\alpha}$ 上比較。

## 文獻（`literature.md`）對這裡的意義

- 沒有找到這個不等式或其特例的任何出處。
- Miezaki–Tagami（2012）的同心球面 Delsarte–Yudin 界，其假設的核的形狀 $g_0(r,s)+\sum_jg_j(r)g_j(s)Q_j(t)$ 與這裡的秩一證書完全相同。
  所以框架是已知的，(★★) 是把它用到這個位勢時要驗證的條件；文獻沒有替這個位勢驗證過。
- Cohn–Kumar 的相關命題編號已查明（Prop. 4.1、2.2，Lemma 5.3、6.1–6.3），但圓周（$\lambda=0$）情形原文沒有單獨處理。
  現在有了封閉形式，這個依賴可以完全去掉。

## Fejér 判準的門檻恰為 $n=15$（E24）

對 $p\approx q$（最壞區域）掃描 $p\in[0,3]$，數列 $(2d_0,d_1,d_2,\dots)$ 的第一個二階差分 $2d_0-2d_1+d_2$ 的最小相對值：

| $n$ | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 20 | 22 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 最小值 | $+0.0097$ | $+0.0057$ | $+0.0028$ | $+0.0006$ | $-0.0010$ | $-0.0022$ | $-0.0032$ | $-0.0044$ | $-0.0052$ |

最壞點在 $p\approx0.75$–$0.85$。所以**「係數為凸 ⟹ Fejér 核的非負組合」這個論證對 $n\le15$ 成立，從 $n=16$ 開始失效**。
這與原帖「$n\le15$ 已知」完全吻合，強烈暗示原帖的已知證明走的就是這條路，而完整解答需要比 Fejér 判準更精細的一步。

其餘的二階差分在所有測試中都非負，失效的只有第一個（常數項略小）。

## (Mono) 在漸近區的證明 [已推導]

$\alpha\to\infty$（$s,t\to0$）時 $\Gamma_m(x)=\dfrac{e^{-mx}}m-\dfrac{N}{n-1}e^{-(n-1)x}+\dots$（$N=n-m$），代入得
$$D_{p,q}(\theta)\;\approx\;\frac{2e^{-(n-1)\alpha}}{n-1}\cdot\tfrac12\sum_{|m|\le n-2}N(N-1)\sinh\bigl((N-1)b\bigr)e^{im\theta},\qquad N=n-|m| .$$
$N\mapsto N(N-1)\sinh((N-1)b)$ 是凸的，且在 $N=0,1$ 為零，所以這裡 Fejér 判準成立。門檻失效發生在 $\alpha$ 中等大小、$b$ 很小的區域。

## 排除

- 誤差核 $\tfrac12\rho_n\mathrm{Fej}_n\mathcal P_w$ 向圓外的調和延拓不是非負的（E23），所以不能逐個 $w$ 地證明分解中的第二項非負。
