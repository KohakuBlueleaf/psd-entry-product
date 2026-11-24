# (Mono) 的漸近結構與 $n=15$ 門檻的解釋

記號同 `closed-form.md`：$p=\alpha-b$，$q=\alpha+b$，$N=n-m$，
$D_{p,q}(\theta)=\tfrac12a_0+\sum_{m=1}^{n-2}a_m\cos m\theta$，$a_0=2d_0$，$a_m=d_m$。

## 對 $e^{-n\alpha}$ 的首階公式 [已推導，E25 驗證到 5–6 位有效數字]

把 $k_m$、$\Gamma_m$ 對 $\varepsilon=e^{-nx}$ 展開到一階（對 $m$、$n$、$x$ 都是精確的）：
$$k_m=e^{-mx}-2N\sinh x\,e^{-nx}+2e^{-(n+m)x}+O(\varepsilon^2),\qquad
\Gamma_m=\frac{e^{-mx}}m-N\Bigl[\frac{e^{-(n-1)x}}{n-1}-\frac{e^{-(n+1)x}}{n+1}\Bigr]+\frac{2e^{-(n+m)x}}{n+m}+O(\varepsilon^2).$$
由此
$$a_m\;\approx\;2e^{-n\alpha}\Bigl\{N\Bigl[\frac{N-1}{n-1}e^{\alpha}\sinh((N-1)b)-\frac{N+1}{n+1}e^{-\alpha}\sinh((N+1)b)\Bigr]-\frac{2n}{n+m}\,e^{-m\alpha}\sinh(nb)\Bigr\}.$$
$n=20$、$\alpha=0.755$、$b=0.005$ 時，公式給出第一個二階差分的相對值 $-0.004414$，精確值 $-0.004413$。

## 機制

係數是兩部分之差：

- **多項式部分**（正）：$N[\dots]$，$b\to0$ 時約為 $\frac{2b}{n}N^3\cdot2\sinh\alpha$，是 $N$ 的三次式，對 $N$ 為凸。
  對應的核在 $\theta$ 不太小時約為 $2b\cdot n\sinh\alpha\cdot\dfrac{3}{1-\cos\theta}$（Euler–Maclaurin，來自 $m=0$ 處的折角）。
- **幾何部分**（負）：$-\frac{2n}{n+m}e^{-m\alpha}\sinh(nb)$，$b\to0$ 時約為 $-2b\cdot n\,e^{-m\alpha}$，
  對應的核是負的 Poisson 核 $-2b\cdot n\sinh\alpha\cdot\dfrac{1}{\cosh\alpha-\cos\theta}$。

因為 $\cosh\alpha\ge1$，$\dfrac3{1-\cos\theta}-\dfrac1{\cosh\alpha-\cos\theta}\ge\dfrac2{1-\cos\theta}>0$。
所以作為**函數**，$D$ 有約三倍的餘量；但作為**係數數列**，幾何部分 $e^{-m\alpha}$ 在 $m=0$ 的折角貢獻一個量級為 $n$ 的負二階差分
$-2n(1-e^{-\alpha})^2$，而三次部分只貢獻量級 $1$ 的 $12\sinh\alpha$。
兩者相等的位置約在 $n\approx6\sinh\alpha/(1-e^{-\alpha})^2$，對 $\alpha$ 取最小得 $17.5$（$\alpha\approx0.88$）；計入有限 $n$ 修正後就是觀察到的 $15$ 與 $16$ 之間。

**結論：Fejér 判準在 $n\ge16$ 失效不是因為不等式變緊，而是因為判準本身看不到「一個正核減去一個 Poisson 核」這種結構。**

## 嚴格證明還需要的

1. 把首階核求和成封閉形式，證明它非負（上面的三倍餘量是 $\theta$ 不太小時的估計；$\theta\sim1/n$ 的區域要單獨處理）。
2. 控制 $O(e^{-2n\alpha})$ 的餘項。$\alpha\gtrsim1/n$ 時它相對很小。
3. $\alpha\lesssim1/n$（對角線接近 1）的區域：展開失效，要用連續極限的尺度 $x=y/n$、$m=\mu n$、$\theta=\varphi/n$ 另外分析。
   這裡無窮小核在 $\alpha=0$ 時恰為 $(1-\mathrm{Fej}_n/n^2)/(2(1-\cos\theta))\ge0$。

## 這一輪排除的捷徑

- **線性的對證書（E26）。** $e^{mx}\Gamma_m(x)$ 是不減函數（數值成立；等價於危險率 $r_m\le m$），所以
  $K_m(p,q)=e^{-m|p-q|/2}\Gamma_m(\min(p,q))$ 是對角線正確的正定核，而且不含平方根：對應的證書是 $h_p$ 向圓內的調和延拓。
  但它給出的缺口是 $E_p(e^{-b}e^{i\theta})-\tfrac12(\Gamma_0(q)-\Gamma_0(p))$，在所有 $n\ge3$ 都會變負。不可用。
- **單項式係數的證書族**（使 $\sqrt{c_m(s)c_m(t)}=c_m(\sqrt{st})$ 精確成立）：相切條件逐冪次推出係數必須含 $-\sum_qq\tau^{qn}$，在 $\tau\to1$ 發散。不存在。
- **其他對稱平均**：給定對角線的正定核中，幾何平均（秩一）是逐元素最大的；算術平均與對數平均都不是正定核。
- **「精確分解」中把平方根項當作高階餘項**：對 $m$ 接近 $n$ 的項，$\Gamma_m$ 與 $e^{-mx}/m$ 在首階就不同，所以 $\varepsilon_m^2$ 項與線性項同階，不能忽略。

## 目前對 (Mono) 的判斷

機制清楚、數值上有約三倍餘量、漸近公式精確，但嚴格證明必須同時控制 $\Gamma_m$（一個沒有初等封閉形式的積分）的上下界到相對 $1/n^2$ 的精度，
因為在 $\theta=\pi$ 附近正負項的交錯和幾乎完全抵消。目前沒有找到能避開這種估計的恆等式。

## 精細化的 Fejér 論證（E27）

分部求和：$D(\theta)=\sum_{j\ge0}\Delta^2a_j\cdot\dfrac{\sin^2((j+1)\theta/2)}{2\sin^2(\theta/2)}$，$\Delta^2a_j=a_j-2a_{j+1}+a_{j+2}$。
由 $\sin^2kx+\sin^2(k+1)x\ge\tfrac12\sin^2x$，$D\ge0$ 可由下面兩條推出：

- (A) $\Delta^2a_j\ge0$ 對所有 $j\ge1$；
- (B) $\sum_{j=1,3,5,\dots}\min(\Delta^2a_j,\Delta^2a_{j+1})\ge2\max(0,-\Delta^2a_0)$。

數值：$n\le25$ 時 (A)、(B) 都成立（(B) 的比值在 $n=16,20,25$ 為 $35$、$6.6$、$4.2$）。
$n=32,40$ 時 (A) 也失效：負的二階差分擴散到前幾個指標（Poisson 部分 $-e^{-m\alpha}$ 對所有 $m$ 都是凹的，只是以 $e^{-m\alpha}$ 衰減）。
所以這個論證把適用範圍從 $n\le15$ 推到大約 $n\le25$，但仍不是一般 $n$ 的證明。要處理大 $n$，必須把 Poisson 部分當成一個核整體處理，而不是逐個二階差分。

## 係數的線性結構 [已推導，E28 驗證]

$k_{m-1}-2k_m+k_{m+1}=2\rho_n(w)\sinh((n-m)w)$，所以
$$\Gamma_m(x)=2\sum_{j=1}^{n-m-1}(n-m-j)\,B_j(x),\qquad B_j(x)=\int_x^\infty\rho_n(w)\sinh(jw)\,dw>0 .$$
即證書是 **Fejér 核的正混合**：$h_x=\text{常數}+\sum_jB_j(x)\,\mathrm{Fej}_{n-j}(\theta)$。$B_j$ 對數凹（數值成立）。

**在這個表示下取幾何平均不行（E28）。** 核 $K_m(p,q)=2\sum_j(n-m-j)_+\sqrt{B_j(p)B_j(q)}$ 是對角線正確的正定核，
對應的證書是 Fejér 核以權重 $\sqrt{B_j(p)B_j(q)}$ 的正混合，而且會把雙參數不等式化成一條不含 $\theta$ 的條件。
但 $n\ge4$ 時不等式為假。所以必須用 Fourier 係數層面的幾何平均（它的非對角元更大）。

## 第二輪文獻（`literature-2.md`）對這個節點的結論

- 沒有找到雙半徑不等式，也沒有找到涵蓋「多項式係數的核減去 Poisson 核」的現成正性判準。
- Vietoris／Belov 型判準對 Fejér 型係數（常數項取一半）不適用；Gneiting 型判準在一維沒有新內容。
- Cesàro $(C,\delta)$ 核（$\delta\ge1$）的正性正好對應這裡的三次部分：三次係數的核是 Fejér 核的正混合，且在 $\theta\gg1/n$ 時約為 $\sum\omega_M/(1-\cos\theta)$。
- 一般的工具是 Fejér–Riesz／Toeplitz SDP 證書與 Sturm 序列，適合逐個 $n$ 的嚴格驗證，不給一般 $n$ 的證明。

## Fejér 混合形式下的首階證明草稿 [推導，未嚴格化]

$W=h_\alpha-R$ 可寫成 $W=c_W+\sum_M\omega_M\,F_M(\theta)$，$F_M=\dfrac{1-\cos M\theta}{1-\cos\theta}$，
$\omega_M=\tfrac12\Delta^2_m\delta_m\big|_{m=M-1}$，$\delta_m=\Gamma_m(\alpha)-\sqrt{\Gamma_m(p)\Gamma_m(q)}$。
首階（$b\to0$，去掉公因子）：
$$\omega_M\;\approx\;\underbrace{\frac{12(n-M)\sinh\alpha}{n}}_{\text{三次部分}}\;-\;\underbrace{2n(1-e^{-\alpha})^2e^{-M\alpha}}_{\text{幾何部分}} .$$
三次部分的核 $\approx\dfrac{6n\sinh\alpha}{1-\cos\theta}$；幾何部分的核有封閉形式，絕對值 $\le\dfrac{4n\,e^{-\alpha}(1-e^{-\alpha})}{1-\cos\theta}$。
而 $6\sinh\alpha\ge4e^{-\alpha}(1-e^{-\alpha})$ 恆成立。所以首階上 $W>0$，不需要任何凸性判準。

要變成嚴格證明，需要對所有 $n,M,\alpha,b$ 給出 $\omega_M$ 的嚴格下界（三次部分的下界減幾何部分的上界），
也就是對 $\sqrt{\Gamma_m(p)\Gamma_m(q)}$ 關於 $m$ 的二階差分做雙邊估計。$\Gamma_m=2\sum_{j}(n-m-j)B_j$ 的線性結構是可用的工具。
