# 探索計畫

目標：找到 `PROBLEM.md`（同目錄）中不等式的證明，並在 Lean 4 中形式化 `Statement.MainTheorem`。

本文件記錄：問題的等價改寫、目前已確立的事實、數值實驗得到的結構性猜想、各條探索路線與第一步任務。
狀態標記：

- **[已證]** 有完整的紙筆論證（尚未形式化）。
- **[依賴文獻]** 論證完整，但引用了尚未逐字核對的文獻定理。
- **[猜想·數值支持]** 只有數值證據，沒有證明。
- **[想法]** 尚未檢驗。

## 1. 記號與等價改寫

$A=(a_{ij})\succeq 0$，寫成 Gram 矩陣 $a_{ij}=\langle v_i,v_j\rangle$。記

$$F_n(t)=1+t+\dots+t^{n-1},\qquad d_i=a_{ii}\ge 0 .$$

**(R) 約化形式 [已證等價]。** 因為 $|1-t^n|=|1-t|\,F_n(t)$（$t\ge0$），原不等式對所有 PSD 矩陣成立，等價於

$$\prod_{i\ne j}|1-a_{ij}|\;\le\;\prod_{i}F_n(a_{ii})\qquad\text{對所有 PSD } A .$$

（有 $a_{ii}=1$ 時原式是 $0\le0$，而 (R) 仍有內容；由 $A+\varepsilon I$ 取極限得到。）(R) 把對角線的奇異性消掉了，
是比較好用的形式。單位對角時它是 $\prod_{i\ne j}|1-a_{ij}|\le n^n$。

**(S) 冪級數形式 [已證等價，限 $a_{ii}<1$]。** 令 $s_k=\sum_{i,j}a_{ij}^k=\bigl\|\sum_i v_i^{\otimes k}\bigr\|^2\ge0$（Schur 乘積定理），
$t_k=\sum_i a_{ii}^k$。取對數後原式等價於

$$\sum_{k\ge1}\frac{s_k}{k}\;\ge\;\sum_{m\ge1}\frac{t_{nm}}{m}.$$

注意逐項比較行不通：對 PSD 矩陣恆有 $s_k\le n\,t_k$，方向相反。不等式本質上是跨次數的。
最低階的資訊：若 $s_1=\dots=s_{n-1}=0$，則所有 $v_i$ 落在同一條複直線上且是同一向量乘上 $n$ 次單位根，此時 $s_n=n\,t_n$ 取等。

**(E) 能量形式。** $-\log|1-\langle z,w\rangle|=\operatorname{Re}\sum_k \langle z,w\rangle^k/k$ 是一個正定核。
(R) 是說：$n$ 個點的對數能量 $\sum_{i\ne j}-\log|1-\langle v_i,v_j\rangle|$ 有下界 $-\sum_i\log F_n(\|v_i\|^2)$。
單位向量時 $|1-\langle z,w\rangle|^{1/2}$ 是複球面上的 Korányi 距離，問題變成 Fekete 點問題。

**等號情形。** $a_{ij}=r^2\omega^{i-j}$（秩一、等模、$n$ 次單位根）。數值上只要對角線不全相等就有嚴格的餘量（見 E3）。

## 2. 目前已確立的事實

1. **[已證] $n=2$。** $|1-b|^2\le(1+\sqrt{ac})^2\le(1+a)(1+c)$。
2. **[已證] 秩一且所有 $|x_i|<1$。** $a_{ij}=x_i\bar x_j$。Cauchy 行列式給出
   $\det\bigl[\tfrac1{1-x_i\bar x_j}\bigr]=|\Delta(x)|^2/\prod_{i,j}(1-x_i\bar x_j)$。
   又 $\tfrac1{1-z}=F_n(z)\cdot\tfrac1{1-z^n}$，所以這個矩陣是 $G\circ K$，其中 $G=[F_n(x_i\bar x_j)]=VV^*$（$V$ 為 Vandermonde，
   $\det G=|\Delta|^2$），$K=[\tfrac1{1-x_i^n\bar x_j^n}]\succeq0$。Oppenheim 不等式 $\det(G\circ K)\ge\det G\cdot\prod_iK_{ii}$ 即得結論。
3. **[已證] 秩一且所有 $|x_i|>1$。** 代換 $y_i=1/\bar x_i$ 化為上一條。
4. **[已證] 對角線單調性。** 若 $d\le d'$（逐項），則 $A+\operatorname{diag}(d'-d)$ 仍為 PSD 且非對角元不變。
   所以 $M(d):=\sup\{\prod_{i\ne j}|1-a_{ij}|:\operatorname{diag}A=d\}$ 對每個 $d_i$ 單調不減。
5. **[依賴文獻] 等對角 $a_{ii}=\rho$（任意 $\rho>0$，任意秩）。** 寫 $a_{ij}=\rho c_{ij}$，$|c_{ij}|\le1$。
   - $g_\rho(z)=-\log|1-\rho z|$ 在單位圓盤上是上調和函數，在圓周上是 $t=\cos\theta$ 的絕對單調函數。
   - Cohn–Kumar (2007) 對圓周上正 $n$ 邊形給出 Hermite 內插多項式 $h(\theta)=\sum_{m=0}^{n-1}c_m\cos m\theta$，
     滿足 $h\le g_\rho$、在 $\theta=2\pi k/n$（$k\ne0$）相切、且 $c_m\ge0$（$m\ge1$）。
   - 調和延拓 $h(z)=\sum c_m\operatorname{Re}z^m$；由最小值原理 $h\le g_\rho$ 在整個閉圓盤成立。
   - Schur 乘積定理給 $\sum_{i,j}\operatorname{Re}c_{ij}^m\ge0$，所以
     $\sum_{i\ne j}g_\rho(c_{ij})\ge n(n-1)c_0-n\sum_{m\ge1}c_m=-n\log F_n(\rho)$。
   - 數值上（E2）對 $n\in\{2,\dots,6,8,12\}$、$\rho\in\{0.3,0.9,1,1.7\}$，LP 最優值與目標一致。
   - 待辦：核對 Cohn–Kumar 原文中係數非負的敘述確實涵蓋這裡用到的形式。
6. **帖子給的事實（未重證）。** 實矩陣、秩一（含 $|x_i|$ 跨越 1 的混合情形）、$n\le15$。
7. **文獻檢索。** 用英文與中文關鍵詞搜尋，沒有找到這個不等式或它的證明來源。

## 3. 數值實驗得到的結構性猜想

腳本在 `../experiments/`，執行方式見 `../README.md`。

| 編號 | 檔案 | 內容 | 結果 |
| --- | --- | --- | --- |
| E0 | `e0_sanity.py` | 主不等式隨機檢驗，$n\le7$ | 28 萬組無反例 |
| E1 | `e1_cauchy_det.py` | 猜想 CD 隨機檢驗，$n\le7$ | 每個 $n$ 2 萬組無反例 |
| E1b | `e1b_cauchy_det_adversarial.py` | 猜想 CD 對抗式搜尋，$n\le6$ | 最小值收斂到 0（秩一），未低於 0 |
| E2 | `e2_lp_certificate.py` | 等對角 LP 證書 | LP 界等於目標值 |
| E3 | `e3_maximizer_rank.py` | 固定對角線求最大值點 | 最大值點全部是秩一 |
| E4 | `e4_unit_det.py` | 猜想 U 分區檢驗 | 單位對角成立；其他對角線大量反例 |
| E5 | `e5_critical_census.py` | 固定對角線的臨界點普查，$n=3..6$ | 所有局部最大值是秩一。搜尋到的臨界點也全是秩一，但這不代表高秩臨界點不存在（見下方更正） |
| E6 | `e6_sdp_certificate.py` | 不等對角的調和 SDP 對偶證書 | $n=3$ 緊；$n\ge4$ 不緊（差 $10^{-3}$ 量級），但仍遠高於定理要求的界 |
| E8 | `e8_cp_map_form.py` | CD 的完全正映射形式，非交換推廣 | 交換時成立；非交換時為假 |
| E9 | `e9_sdp_vs_target.py` | 調和 SDP 界是否總 $\ge$ 定理的界，$n=4..7$ | 全部成立（餘量為正） |
| E10 | `e10_weighted_rank_one.py` | 球面平均後的逐點加權秩一不等式 $(W_r)$ | $r=1,2$ 成立；$r\ge3$ 為假 |
| E11 | `e11_holder_integral.py` | 積分版廣義 Hölder，$\beta\in\{-\tfrac14,\tfrac12,1,2,4\}$ | 全部成立 |
| E12 | `e12_pairwise_cs.py` | 成對 Cauchy–Schwarz $M(s,t,h)^2\le M(s,s,h)M(t,t,h)$ | $n=3$ 成立；$n\ge4$ 為假 |
| E13, E13b, E13c | `e13*_gm_certificate*.py` | 雙參數不等式 (★★)，$n\le16$，含 60 位精度 | **無反例** |
| E14, E14b | `e14*_*.py` | (★★) 的多項式形式 $W\ge0$ 與係數的凹性 | 全部成立，最小值在 $x=-1$ |
| E15 | `e15_large_n.py` | (★★) 與 $W\ge0$，$n=12..40$，90 位精度 | 全部成立，相對餘量約 $2/n^2$ |
| E16–E18 | `e16`–`e18` | $n=4$ 顯式化、無窮小形式 | 見 `notes/n4.md`、`notes/general-n-attempts.md` |
| E19 | `e19_kernel_sdp.py` | 整族對角線上最優正定核 | 最優核近乎秩一；確認幾何平均形式 |
| E20 | `e20_closed_form.py` | Fejér 證書的封閉形式與 (★★) | 公式精確；(★★) 到 $n=16$ 成立 |
| E21–E28 | `e21`–`e28` | (Mono)、Fejér 判準門檻、漸近公式、其他證書形式 | 見 `notes/closed-form.md`、`notes/mono-asymptotics.md` |
| E7 | `e7_reduction_to_equal.py` | 每對用 $\tau_{ij}=\sqrt{d_id_j}$ 的等對角證書 | $n=3$ 可行；$n\ge4$ 餘量為負，照原樣不可用。$c_0(e^u)$ 為凹 |

**猜想 R1 [猜想·數值支持]（秩一化約）。** 對任意固定的對角線 $d$，$\prod_{i\ne j}|1-a_{ij}|$ 在
$\{A\succeq0,\ \operatorname{diag}A=d\}$ 上的最大值在秩一矩陣取到。
E3 對 $n=3,\dots,7$、對角線全小於 1、全等於 1、跨越 1 的 16 組資料都是如此。
若成立，主定理化為秩一情形。

**猜想 CD [猜想·數值支持]（Cauchy 行列式不等式）。** 對 $a_{ii}<1$ 的 PSD 矩陣，

$$\det\Bigl[\frac1{1-a_{ij}}\Bigr]\cdot\prod_{i,j}|1-a_{ij}|\;\le\;\det\bigl[F_n(a_{ij})\bigr],$$

秩一時是等式（Cauchy 行列式公式）。$n=2$ 時它恰好是 $|b|^2\le ac$，已證。
配合恆成立的 Oppenheim 不等式 $\det[\tfrac1{1-a_{ij}}]\ge\det[F_n(a_{ij})]\cdot\prod_i\tfrac1{1-a_{ii}^n}$，立刻得到 $a_{ii}<1$ 時的主定理：

$$\prod_i\frac1{1-a_{ii}^n}\;\le\;\frac{\det[1/(1-a_{ij})]}{\det[F_n(a_{ij})]}\;\le\;\frac1{\prod_{i,j}|1-a_{ij}|}.$$

Fock 空間的說法：令 $k_v$ 為 Drury–Arveson 核函數，$\xi=k_{v_1}\wedge\dots\wedge k_{v_n}$，$P_{<n}$ 為到次數小於 $n$ 部分的投影，
則 CD 是 $\|\Lambda^n(P_{<n})\xi\|^2/\|\xi\|^2\ge\prod_{i,j}|1-\langle v_i,v_j\rangle|$。

**猜想 U [猜想·數值支持]（單位對角）。** $a_{ii}=1$ 時 $\prod_{i\ne j}|1-a_{ij}|\le\det[F_n(a_{ij})]$。
再用 Hadamard 不等式 $\det[F_n(a_{ij})]\le n^n$ 得到單位對角情形的另一個證明。此式對非單位對角不成立（E4）。

**觀察（E5 與更正）。** 數值搜尋找到的臨界點全是秩一，但秩 $\ge2$ 的臨界點確實存在（例：實正單形），它們是鞍點。
R1 需要二階或整體論證。最大值點的 KKT 條件見 `../notes/routeA.md`：存在實對角 $\Lambda$ 使
$Z=N-\Lambda\succeq0$、$Z\bar A=0$，其中 $N_{ij}=1/(1-a_{ij})$（$i\ne j$）。R1 等價於最大值點處 $\ker Z$ 為一維。
局部最大值不唯一（$n\ge4$ 不等對角時有多個秩一局部最大值）。

**形式化現況。** `MatrixIneq/Fejer.lean`：`mainTheorem_of_star : (∀ n ≥ 3, Star n) → Statement.MainTheorem`，無 `sorry`。`Star n` 就是用積分定義的係數寫出的 (★★)。主定理在 Lean 裡只剩這一條實分析敘述。

**封閉形式。** 證書係數是顯式正核的尾積分，$k_m(w)=\frac{\sinh((n-m)w)-(n-m)\sinh w}{\cosh nw-1}$，見 `../notes/closed-form.md`。(CK) 因此不需引用文獻。

**目前的主線。** 主定理 ⟸ (CK) + (★★)，見 `../notes/certificate-proof.md`。(★★) 是一個每個 $n$ 一條的雙參數逐點不等式，數值上到 $n=16$ 無反例。

**第二輪解析探索。** 已排除的方向、可用的改寫與化約見 `../notes/findings-round2.md`。

**形式化進度。** 見 `../README.md`。已完成：約化形式、$n\le2$、Schur 正性、Oppenheim 不等式。

## 4. 探索路線

可以並行。每條路線列出：核心工具、要證的關鍵引理、第一步、風險。

### 路線 A：秩一化約（R1）＋秩一情形

主定理 = R1 + 秩一全區域。這是目前唯一能一次涵蓋所有對角線取值的路線。

- **A1 證明 R1。** 工具與想法：
  - 多重次調和函數的最大值原理。固定對角線後，$f=\sum_{i<j}2\log|1-a_{ij}|$ 是上三角元 $(a_{ij})_{i<j}$ 的多重調和函數。
    若秩 $r$ 的點 $A=WW^*$ 處存在 $T\in M_r(\mathbb C)$ 使 $WTW^*$ 為嚴格上三角，就有一個落在可行集內的複圓盤，最大值可推到其邊界。
    這給出最大值點可取 $r^2\le n(n+1)/2$。只用線性圓盤降不到秩一，需要非線性的全純形變。
  - 臨界點的二階變分：證明秩 $\ge2$ 的臨界點都不是局部最大值。對單個向量 $v_i$，$f$ 是 $v_i$ 的多重調和函數限制在球面上。
  - 對偶證書（見路線 C2）：若固定 $d$ 的 SDP 鬆弛是緊的，R1 與上界同時得到。
- **A2 秩一、$|x_i|$ 跨越 1 的混合情形。** 這時 $[\tfrac1{1-x_i\bar x_j}]$ 不定，Oppenheim 不能直接用。想法：
  - Schur–Cohn／Bezout 矩陣：$\prod_{i,j}(1-x_i\bar x_j)$ 是 $q(z)=\prod(z-x_i)$ 與其反射多項式的結式，等於 Schur–Cohn 矩陣的行列式，其符號差數出圓內外的根數。
  - 對內外兩組點分別用 Cauchy 行列式，交叉項 $|1-x_i\bar x_j|=|y_i-x_j|/|y_i|$ 是 Vandermonde 型。
  - 帖子說秩一已知，所以這一塊應該有不太難的論證。
- **第一步實驗。** E5：大量隨機起點做局部最佳化，統計是否存在秩 $\ge2$ 的局部最大值或鞍點，並記錄秩 $\ge2$ 臨界點的 Hessian 正方向。
- **風險。** R1 可能為真但難證。A2 目前沒有證明。

### 路線 B：行列式鏈（CD＋Oppenheim）

- **B1 證明 CD。** 想法：
  - 加一個點的 Schur 補歸納：$\det C_n=\det C_{n-1}\cdot\operatorname{dist}^2(k_{v_n},\operatorname{span}\{k_{v_i}\}_{i<n})$，但 $F_n$ 依賴 $n$，歸納假設要推廣成帶參數 $N\ge n$ 的版本。
    已知 $\det[F_N(a_{ij})]$ 對 $N$ 單調不減，所以 $N=n$ 是最強的情形。
  - 對稱函數：秩一時兩邊是 $|\Delta|^2\sum_\lambda|s_\lambda(x)|^2$ 與 $|\Delta|^2$。尋找高秩時的 Cauchy–Binet 展開，把差寫成非負項之和。
  - 在秩一處的二階展開：先證 CD 在秩一附近成立，並看 Hessian 的結構。
  - 完全 Pick 核的極值問題：Drury–Arveson 空間中插值問題的對偶給出 $\det C$ 的界。目前只會得到下界，需要的是上界。
- **B2 對角線 $\ge1$ 的區域。** 單位對角用猜想 U。對角線大於 1 或混合時，要找正確的行列式敘述（Pick 型不定矩陣）。
- **第一步。** 用高精度（mpmath）在 $n=3$ 把 CD 的對抗式搜尋做紮實；用符號計算把 $n=3$、秩二的 CD 寫成多項式不等式，嘗試 SOS 分解。
- **風險。** 只涵蓋 $a_{ii}<1$（與單位對角），其他區域要另外處理。優點是若成立，證明短，而且容易形式化。

### 路線 C：線性規劃／半定規劃證書

- **C1 等對角。** 見第 2 節第 5 條。任務：核對文獻，或直接給出 $h$ 的顯式係數並證明非負。
- **C2 不等對角（多物種能量）。** 位勢 $g_{ij}(z)=-\log|1-\rho_i\rho_jz|$ 依賴點對。證書形如
  $h_{ij}(z)=\sum_m C_m[i,j]\operatorname{Re}z^m$，要求每個 $m\ge1$ 的係數矩陣 $C_m\succeq0$、圓周上 $h_{ij}\le g_{ij}$。
  對應的原問題鬆弛：一族圓周上的機率測度 $\mu_{ij}$，要求每個 $m\ge1$ 的 Fourier 係數矩陣 $[\hat\mu_{ij}(m)]\succeq0$。
- **第一步實驗。** E6：對 $n=3,4$ 的幾組不等對角，數值求解這個 SDP（需要安裝 SDP 求解器），看鬆弛值是否等於秩一最大值。
  若相等，這條路線同時證明 R1；若不等，C2 放棄，並且說明調和證書不夠。
- **工具。** Delsarte–Yudin 線性規劃界、Cohn–Kumar 普適最優性、Schoenberg／Christensen–Ressel 對 Hilbert 球面上正定函數的刻畫
  （$\sum c_{pq}z^p\bar z^q$，$c_{pq}\ge0$），混合項 $z^p\bar z^q$ 提供比調和證書更大的證書空間。

### 路線 D：冪級數、Fock 空間與對稱函數

- 直接攻 (S)。把 $\prod_{i,j}(1-a_{ij})^{-1}=\exp\sum_k s_k/k$ 展開成對非負整數矩陣 $M$ 的求和 $\sum_M\prod a_{ij}^{m_{ij}}$，
  右邊對應 $M=n\cdot\operatorname{diag}$ 的項。秩一時這是 RSK／Cauchy 恆等式。
- 核的比較：$\mathcal K(V,W)=\prod_{i,j}(1-\langle v_i,w_j\rangle)^{-1}$ 是構形空間上的正定核。尋找它的正交分解，使對角線上的值明顯大於目標。
- 表示論：$(\mathrm{GL}_n,\mathrm{GL}_d)$ Howe 對偶、$\mathbb Z/n$ 的同型分解（單位根結構）。
- 風險：容易停在形式改寫。適合當作路線 B 的工具庫。

### 路線 E：機率與積分表示

- CUE 平均：秩一且 $|x_i|<1$ 時 $\prod_{i,j}(1-x_i\bar x_j)^{-1}=\mathbb E_{U}\bigl|\prod_i\det(1-x_iU)^{-1}\bigr|^2$。尋找一般 Gram 矩陣的類比。
- 複 Gauss 向量 $\xi_i=\langle v_i,Z\rangle$，$\mathbb E\,\xi_i^k\bar\xi_j^{\,l}=\delta_{kl}k!\,a_{ij}^k$；積和式不等式（Lieb、Marcus）。
- 風險：推測性最高。

### 路線 F：文獻考古

- 找出帖子說的「經典結論」（候選：圓周上 Fekete 點 $\prod_{i<j}|u_i-u_j|\le n^{n/2}$；Oppenheim；Cauchy 行列式）。
- 找已知證明的來源。目前搜尋無結果，可再試：Drury–Arveson 核的行列式不等式、複球面上的普適最優構形、Korányi 距離的 Fekete 點。

## 5. 建議的優先順序

1. **A1（E5）與 C2（E6）先做實驗**。兩者都在檢驗 R1 的機制，成本低，結果決定路線 A 與 C 的走向。
2. **B1 同時進行**。CD 是一個乾淨的獨立猜想，$n=3$ 的符號計算可以很快給出訊號。
3. **A2 與 C1 是補洞工作**，結論應該為真，需要的是寫出完整論證。
4. **D、E 當作工具庫**，在 A、B 卡住時取用。
5. **F 持續低成本進行**。

決策點：E5、E6 與 B1 的 $n=3$ 結果出來後，選定主證明路線，再開始寫 Lean 的引理骨架。

## 6. 形式化的準備

Mathlib（v4.36.0）已有：Schur 乘積定理（`Matrix.PosSemidef.hadamard`）、Vandermonde 行列式（`Matrix.det_vandermonde`）、Schur 補。

快速搜尋沒有找到：Cauchy 行列式公式、Oppenheim 不等式、PSD 矩陣的 Hadamard 行列式不等式。走路線 B 的話這三項要自己證。

走路線 C 的話需要：調和函數最小值原理（圓盤上）、Hermite 內插誤差公式、Chebyshev 係數非負的證明。

## 7. 工作約定

- 每條路線的進展寫在 `../notes/<路線>.md`，結論用本文件開頭的狀態標記。
- 實驗腳本放 `experiments/`，檔名 `e<編號>_<主題>.py`，檔頭寫明檢驗的敘述。
- 新的猜想先做對抗式數值搜尋再投入證明。
- 本文件的第 2、3 節是共用的事實清單，有更新就改這裡。
