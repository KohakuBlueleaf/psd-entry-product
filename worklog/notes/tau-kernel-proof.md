# 完整證明的草稿：τ-核 [文字證明；E51 小計算支持；Lean 形式化進行中]

記號同 `docs/THEORY.md`。$\chi_m(x)=e^{mx}k_m(x)$，對 $x$ 遞增（Lean `chi_mono`），$\chi_m(0^+)=0$，$\chi_m(\infty)=1$。
$\Pi_x(\theta)=\tfrac12k_0(x)+\sum_{m=1}^{n-2}k_m(x)\cos m\theta\le\tfrac12\mathcal P_x(\theta)$（核恆等式，Lean `kern_identity`）。

## 核

對 $0\le p\le q$ 定義（並對稱延拓）
$$K_m(p,q)=\Gamma_m(q)+\tfrac12\int_p^qk_m(x)\,e^{-m(q-x)/2}\,dx\qquad(1\le m\le n-2).$$

**(a) 對角線**：$K_m(p,p)=\Gamma_m(p)$。

**(b) 半正定**：分部積分得
$$K_m(p,q)=\frac1m\int_0^\infty\chi_m'(\tau)\,e^{-m\max(p,\tau)/2}\,e^{-m\max(q,\tau)/2}\,d\tau ,$$
$\chi_m'\ge0$，所以 $K_m$ 是秩一半正定核 $\phi_\tau(p)\phi_\tau(q)$（$\phi_\tau(p)=e^{-m\max(p,\tau)/2}$）的正混合。
（驗算：$p\le q$ 時右邊 $=\frac1m\bigl[\chi(p)e^{-m\alpha}+e^{-mq/2}\int_p^q\chi'e^{-m\tau/2}+\int_q^\infty\chi'e^{-m\tau}\bigr]$，
後兩項分部積分後 $\chi(p)$、$\chi(q)$ 的邊界項全部相消，剩下 $\Gamma_m(q)+\frac12\int_p^q\chi e^{-m\tau/2}e^{-mq/2}$。）

**(c) 對不等式**：對 $0\le p\le q$、所有 $\theta$，$\alpha=\frac{p+q}2$，
$$-\log|1-e^{-\alpha}e^{i\theta}|\ \ge\ \tfrac12\bigl(\Gamma_0(p)+\Gamma_0(q)\bigr)+\sum_{m=1}^{n-2}K_m(p,q)\cos m\theta .$$
證明：左邊 $=\int_\alpha^\infty\tfrac12(\mathcal P_w-1)\,dw$。
- $w\ge q$：$\tfrac12\mathcal P_w\ge\Pi_w$。
- $\alpha\le w\le q$：令 $x=2w-q\in[p,q]$，$s=w-x=q-w\ge0$。$\Pi_x\le\tfrac12\mathcal P_x$ 且 Poisson 核為正，所以
  $\tfrac12\mathcal P_w=\tfrac12P_s*\mathcal P_x\ge P_s*\Pi_x=\tfrac12k_0(x)+\sum_mk_m(x)e^{-ms}\cos m\theta$。
積分，第二段換元 $x=2w-q$（$dw=dx/2$）：
$$\int_\alpha^q\Bigl[\tfrac12(k_0(2w-q)-1)+\sum_mk_m(2w-q)e^{-m(q-w)}\cos m\theta\Bigr]dw
=\tfrac12\bigl(\Gamma_0(p)-\Gamma_0(q)\bigr)+\sum_m\tfrac12\!\int_p^q\!k_m(x)e^{-m(q-x)/2}dx\,\cos m\theta ,$$
加上第一段的 $\Gamma_0(q)+\sum_m\Gamma_m(q)\cos m\theta$ 即得。常數項恰為 $\tfrac12(\Gamma_0(p)+\Gamma_0(q))$。
缺口的顯式形式：$E_q(\theta)+\tfrac14\int_p^q\bigl(P_{(q-x)/2}*\rho_n(x)\mathrm{Fej}_n\mathcal P_x\bigr)(\theta)\,dx\ge0$。

## 主定理

$a_{ij}=\sqrt{d_id_j}\,c_{ij}$，$d_i=e^{-p_i}$。(c) 由調和函數的最小值原理推到 $|c|\le1$。於是
$$\sum_{i\ne j}-\log|1-a_{ij}|\ \ge\ (n-1)\sum_i\Gamma_0(p_i)+\sum_m\Bigl[\sum_{i,j}K_m(p_i,p_j)\operatorname{Re}c_{ij}^m-\sum_i\Gamma_m(p_i)\Bigr]
\ \ge\ \sum_i\Bigl[(n-1)\Gamma_0(p_i)-\sum_m\Gamma_m(p_i)\Bigr]=-\sum_i\log F_n(d_i),$$
第二個不等號用 (b) 與 Schur 乘積定理（$[K_m(p_i,p_j)]\circ C^{\circ m}\succeq0$），最後是總和恆等式（Lean `total_Gam`）。

與幾何平均核的差別：只在對角線上要求秩一；非對角元 $K_m\le\sqrt{\Gamma_m(p)\Gamma_m(q)}$。Star、(H_in)、(QC) 都不再需要。
