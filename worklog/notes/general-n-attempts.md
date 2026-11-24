# 一般 $n$ 的 (★★)：結構性證明的嘗試

記號：$s=e^u$，$\ell_u(x)=-\tfrac12\log(\cosh u-x)$，$h_u=\Lambda_0(u)+\sum_{m\ge1}\gamma_m(u)T_m(x)$ 為 Hermite 內插。
(★★)：$\ell_{(u+v)/2}(x)\ge\tfrac12(\Lambda_0(u)+\Lambda_0(v))+\sum_m\sqrt{\gamma_m(u)\gamma_m(v)}\,T_m(x)$。
等價說法（$W\ge0$）：沿反對角線 $u=a+b$、$v=a-b$，右邊在 $b=0$ 取最大。

## 已得到的結構 [已推導]

1. **係數是節點資料的離散 Fourier 變換。** 內插多項式可寫成
   $h_s(\theta)=\frac1n\sum_j g_s(\theta_j)\Phi_n(\theta-\theta_j)+\frac1n\sum_{l}\Delta_l\cos l\theta+\kappa\,\Phi_n(\theta)$，
   $\Phi_n$ 為 Fejér 核，$\theta_j=2\pi j/n$。即「在全部 $n$ 個單位根上的 Hermite–Fejér 內插，再減去一個以 $\theta=0$ 為中心的 Fejér 核」。
   $n$ 奇時：$n\gamma_l=(n-l)I_l+\Delta_l$，$\Delta_l(u)=\dfrac{\sinh((\frac n2-l)u)}{\sinh(\frac n2u)}$，
   $I_l=\Delta_1-\int_{|u|}^\infty\dfrac{\cosh((\frac n2-1)w)-\cosh((\frac n2-l)w)}{\sinh(\frac n2w)}\,dw$。
2. **$\Delta_l$ 對數凹**（$l<n/2$）：$(\log\sinh cu)''=-c^2/\sinh^2(cu)$ 對 $c$ 的單調性。
3. **無窮小形式。** $W$ 的 $b^2$ 係數是
   $w(x)=-\Lambda_0''(a)-\sum_m\gamma_m(\log\gamma_m)''(a)\,T_m(x)$，各係數數值上非負。
4. **單位對角處的精確結構（E18）。** $a=0$、$n$ 奇時，$w$ 的 Chebyshev 係數之比是四面體數：
   $$w(\theta)\;\propto\;\tfrac12\sum_{|m|\le n-2}\binom{n+1-|m|}{3}e^{im\theta}.$$
   （$n=5$：$10,10,4,1$；$n=7$：$28,35,20,10,4,1$。）$n$ 偶時係數也是有理數（$n=4$：$22,19,6,1$；$n=6$：$73,85,44,19,6,1$）。
   這表示 $s=1$ 處有封閉形式。

## 已排除的想法

| 想法 | 結果 |
| --- | --- |
| 用 $\cosh$ 的 Laplace 表示，把 (★★) 加強成對 $\cosh a'=\frac{\cosh u+\cosh v}2$ 的敘述 | 為假（$n=3$ 即有反例）。$\cosh\frac{u+v}2$ 與算術平均的差距是必要的 |
| 正定核 $\kappa_m(u,v)=\int E_m(t)e^{-t(\cosh u+\cosh v)/2}d\mu$（對角線正確） | 常數項方向錯誤 |
| 以 $u+v$ 為變數的核 $\gamma_m(\frac{u+v}2)$ | 不是正定核（$\gamma_m$ 對數凹，不是指數凸）；最小跡補全在 $n\ge4$ 不夠（E7） |
| 以 $u-v$ 為變數（$\Delta_l$ 是 Bochner 正定函數） | 對角線為常數，不符 |
| 冪級數表示 $c_m(s)=\sum\lambda_{mk}s^k$ | $\lambda_{mk}$ 有負值（$n=3$ 時是模 3 的特徵） |
| 無窮次數的摺疊級數證書 | 對角線接近 1 時發散 |
| 複參數 $\zeta$ 的調和延拓加 Phragmén–Lindelöf | $\gamma_m(a+\zeta)$ 在定義域內有極點與零點 |
| 把 $Z_\beta$ 寫成 $\mathbb E\prod_j\varphi_\xi(t_j)$（de Finetti 型），由 Hölder 直接得結論 | $n=3,\beta=1$ 已不存在這種實的正表示 |
| 成對 Cauchy–Schwarz 迭代 | $n\ge4$ 為假（E12） |
| 由無窮小形式推出有限形式（$(g-R)/b^2$ 對 $b$ 單調） | 不單調（E18） |
| Aczél 型反向 Cauchy–Schwarz | 方向不夠強 |

## 目前的判斷

沒有找到結構性的證明。唯一新的具體線索是 $s=1$ 處的封閉形式。
