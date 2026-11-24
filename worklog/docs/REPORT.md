# 現況報告

日期：2026-11-25。問題敘述見 `PROBLEM.md`，形式敘述是 `Statement.MainTheorem`（`../Statement.lean`）。

## 結論

主定理
$$\prod_{i,j}|1-a_{ij}|\le\prod_i|1-a_{ii}^{\,n}|\qquad(A\succeq0,\ A\in\mathbb C^{n\times n})$$
目前的狀態：

| 範圍 | 狀態 |
| --- | --- |
| $n\le3$ | 在 Lean 中證完（`MatrixIneq.mainTheorem_le_three`） |
| 所有 $n$，對角元全相等 | 在 Lean 中證完（`MatrixIneq.mainTheorem_const_diag`；單位對角：`prod_offdiag_le_pow_of_unit_diag`） |
| 一般 $n$ | 在 Lean 中化約為一條**不含 $\theta$** 的數列凸性敘述 `QC n`（`MatrixIneq.mainTheorem_of_qc`） |
| `QC n` | 未證；$n\le80$ 的小計算無例外（`../notes/qc-route.md`） |

全部 Lean 檔案沒有 `sorry`，只依賴 `propext`、`Classical.choice`、`Quot.sound`。

## 剩下的敘述

Lean 中已證的鏈（全部無 `sorry`）：
$$\texttt{QC n}\ \Rightarrow\ \texttt{HIn n}\ \Rightarrow\ \texttt{Star n}\quad(n\ge3),\qquad(\forall n\ge3,\ \texttt{QC n})\ \Rightarrow\ \texttt{Statement.MainTheorem}.$$

對 $w>0$、$0\le m\le n-2$：$k_m(w)=\dfrac{\sinh((n-m)w)-(n-m)\sinh w}{\cosh nw-1}$，$\Gamma_m(p)=\int_p^\infty k_m$（$m\ge1$）。
對 $0<p<q$ 令 $\alpha=\frac{p+q}2$，
$$u_0=k_0(p),\quad u_m=k_m(p)\sqrt{\frac{\Gamma_m(q)}{\Gamma_m(p)}}\ (1\le m\le n-2),\quad u_m=0\ (m\ge n-1),$$
$$a_0=2(\sinh\alpha-u_0\cosh\alpha+u_1),\qquad a_m=u_{m-1}+u_{m+1}-2\cosh\alpha\,u_m\ (m\ge1).$$

**QC$(n)$**：對所有 $0<p<q$，數列 $(a_m)_{m\ge0}$ 是凸的（$a_j-2a_{j+1}+a_{j+2}\ge0$）。

它是 $n$ 條關於 $(p,q)$ 的不等式，不含角度變數。意義：$-\partial_p$（缺口）除以 Poisson 核後是低階 Fejér 核的正混合。
各步：

- **Star**（`Fejer.lean`）：$-\log|1-e^{-\alpha}e^{i\theta}|\ge\tfrac12(\Gamma_0(p)+\Gamma_0(q))+\sum_m\sqrt{\Gamma_m(p)\Gamma_m(q)}\cos m\theta$。
- **HIn**（`HIn.lean`）：$p<q$ 時 $\tfrac12k_0(p)+\sum_mu_m\cos m\theta\le\tfrac12\mathcal P_\alpha(\theta)$。缺口對較小的參數單調，$p=q$ 時為已證的等對角情形。
- **QC**（`QC.lean`）：上式乘以 $2(\cosh\alpha-\cos\theta)$ 後是次數 $n-1$ 的餘弦多項式，係數為 $a_m$；凸則由 Fejér 判準非負。

## 證明的結構

1. **約化形式**（`Reduced.lean`）。$|1-t^n|=|1-t|(1+t+\dots+t^{n-1})$，所以只需證
   $\prod_{i\ne j}|1-a_{ij}|\le\prod_iF_n(a_{ii})$，$F_n(t)=\sum_{k<n}t^k$。
2. **證書 ⟹ 約化形式**（`Certificate.lean`）。寫 $a_{ij}=\sqrt{d_id_j}\,c_{ij}$。若對每一對有
   $-\log|1-\sqrt{st}\,z|\ge\tfrac12(c_0(s)+c_0(t))+\sum_m\sqrt{c_m(s)c_m(t)}\mathrm{Re}\,z^m$ 於 $|z|=1$，
   則由最大模原理推到閉圓盤，由 Schur 乘積定理處理交叉項（係數矩陣 $[\sqrt{c_m(d_i)c_m(d_j)}]$ 為秩一半正定），
   再用恆等式 $(n-1)c_0-\sum_mc_m=-\log F_n$ 得結論。
3. **Fejér 證書**（`Kernel.lean`、`Fejer.lean`）。取 $c_m(e^{-p})=\Gamma_m(p)$。這是 $-\log|1-se^{i\theta}|$
   在非平凡 $n$ 次單位根處二重內插的餘弦多項式的係數。已證：核非負、可積、總和恆等式、延拓到所有 $s\ge0$、
   $s,t$ 分居 1 兩側時化約回 $p,q\ge0$。
4. **Star**。這是把第 2 步的假設用第 3 步的係數寫出來。$p=q$ 時它由誤差公式
   $g_s-h_s=\tfrac12\mathrm{Fej}_n(\theta)\int_p^\infty\rho_n(w)\mathcal P_w(\theta)\,dw\ge0$ 得到（已在 Lean：`EqualDiag.lean` 的 `star_diag`）。
5. **Star ⟸ HIn ⟸ QC**（`HIn.lean`、`QC.lean`）。見上一節。

## 證據與已知結構

- Star 的數值：$n=4..40$，多組 $(p,q)$，最高 220 位精度，無反例。
- (QC) 的數值：$n\le80$，$p\in[10^{-4},3]$，$q-p\in[10^{-5},12]$，約 400 組，無例外；最緊的是指標 $j=n-2$（等價於危險率之比 $r_2/r_3$ 的單調性）。
- 先前的非凸性（$n\ge16$）來自 Poisson 型的部分；(QC) 的 $\alpha$-扭轉把它精確消去。
- 單調性形式 (Mono)：令 $p=\alpha-b$、$q=\alpha+b$，缺口對 $b$ 的導數是係數非負的餘弦多項式 $D_{p,q}(\theta)$；
  Star 等價於由 $D\ge0$ 推出。$D$ 的最小值在 $\theta=\pi$，相對餘量約 $2.3/n^2$。
- Fejér 凸性判準對 $n\le15$ 成立，$n\ge16$ 失效，與原帖「$n\le15$ 已知」吻合；失效原因已解析地解釋
  （係數是「三次式部分」減「幾何部分」，後者在指標 0 的折角使數列不凸，但作為函數仍有約三倍餘量）。
- 首階（對 $e^{-n\alpha}$）有精確到 5–6 位的顯式公式，並有不依賴凸性的首階證明草稿。
- SDP：在整族對角線上最佳化所有正定核，最優解近乎秩一，印證「係數取幾何平均」是這個框架裡本質上唯一的形式。

## 已排除的路線（都有數值反例或論證）

行列式路線的非交換推廣；只靠多重次調和最大值原理的秩一化約；把一般矩陣表成秩一矩陣的調和平均（$n\ge4$）；
成對 Cauchy–Schwarz 迭代（$n\ge4$）；以 $\cosh$ 的算術平均為參數的證書；線性（不含平方根）的對證書；
單項式係數的證書族；在 Fejér 混合表示下取幾何平均；由無窮小形式直接推出有限形式。
細節分別在 `../notes/findings-round2.md`、`general-n-attempts.md`、`mono-asymptotics.md`。

## 文獻

三輪搜尋（`../notes/literature.md`、`literature-2.md`、`literature-3.md`）沒有找到這個不等式的出處，也沒有找到能直接給出 Star 或 (QC) 的定理。
秩一、等半徑的情形見 Ounaïes, arXiv:2601.10411（Alexander 猜想）。
框架（不同半徑上的 Delsarte–Yudin 界、秩一係數核）見 Miezaki–Tagami (2012)；等半徑情形對應 Cohn–Kumar (2007)，
但這裡的封閉形式使等半徑情形不需要引用它。

## 檔案索引

| 路徑 | 內容 |
| --- | --- |
| `../README.md` | 專案結構與 Lean 檔案一覽 |
| `EXPLORATION.md` | 探索過程、實驗清單 |
| `../notes/certificate-proof.md` | 證書方法的推導 |
| `../notes/closed-form.md` | Fejér 證書的封閉形式、(Mono) |
| `../notes/mono-asymptotics.md` | 漸近結構、$n=15$ 門檻、首階證明草稿 |
| `../notes/structure-gap.md` | $n\le3$ 與一般 $n$ 的差距 |
| `../notes/qc-route.md` | (QC) 的推導、無窮小形式、還需要的引理 |
| `THEORY.md` | 定理關係圖與逐輪的文字推理（4.3i–4.3n 為最新） |
| `../experiments/` | 實驗腳本 E0–E50（只作為猜想的檢驗） |
