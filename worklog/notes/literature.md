# Literature search: ∏_{i,j}|1 − a_ij| ≤ ∏_i |1 − a_ii^n| for PSD A

Date of search: 2026-11-24. Tools: web search (US-only index, snippet quality poor for Chinese sources and for forum threads) and direct download/reading of arXiv PDFs (Cohn–Kumar, Miezaki–Tagami, Borodachov et al., Gaál et al., headers of a few others).

Legend: **[READ]** = I downloaded the source and read the quoted/paraphrased passage. **[SNIPPET]** = only a search-result snippet or abstract; not verified.

Bottom line up front: **the inequality itself (or its unit-diagonal / rank-one / different-radii special cases) was not found anywhere** (Tieba, Zhihu, MO, MSE, arXiv, journals, as far as the search index reaches). The most useful findings are (i) the exact statements in Cohn–Kumar (item H) and (ii) the Miezaki–Tagami linear-programming theorem for points on *concentric spheres with weights*, whose structure matches the two-parameter inequality you reduced to (item C).

---

## A. The inequality itself / its source — NOTHING FOUND

Queries tried (all returned only generic Hadamard / Oppenheim / Schur material):
- `positive semidefinite matrix inequality \prod |1 - a_{ij}| \le \prod |1 - a_{ii}^n|`
- `"\prod_{i,j}" "1-a_{ij}" positive semidefinite Hermitian ... "a_{ii}^n"`
- `半正定矩阵 乘积不等式 ∏|1-a_ij| ≤ ∏|1-a_ii^n| 数学吧`
- `贴吧 数学吧 半正定 Hermite 矩阵 证明 ... n≤15 实矩阵成立`
- `知乎 半正定矩阵 元素 1-a_ij 连乘 不等式 推广 单位根 等号`
- `mathoverflow inequality product over i,j of |1 - a_ij| positive semidefinite ... Fekete points roots of unity`
- `math.stackexchange inequality \prod_{i\ne j} |1 - x_i \bar{x}_j| points in unit disc maximum Cauchy determinant Oppenheim`
- `product \prod_{i\neq j} |1 - <v_i,v_j>| \le n^n unit vectors complex Hilbert space`
- `Gram matrix unit vectors \prod_{i<j}|1-<x_i,x_j>| maximum n^{n/2} complex sphere Fekete problem Heisenberg group Korányi` (extended mode)
- `"positive semidefinite" matrix "product of" |1 - a_ij| over all entries ... unit root equality mathoverflow` (extended mode)
- `sum over entries of PSD matrix \sum_{i,j}\log|1-a_{ij}| entrywise function ... positive definite kernel`
- `determinant of Hadamard inverse matrix [1/(1-a_ij)] ... Oppenheim Szegő kernel`

Near-misses that are only background (all [SNIPPET]):
- Lin–Sinnamon, "Revisiting a sharpened version of Hadamard's determinant inequality", arXiv:2007.13155 — Hadamard sharpening for PSD matrices; unrelated product form.
- Khare, "Sharp nonzero lower bounds for the Schur product theorem", arXiv:1910.03537 — lower bounds for M∘N.
- "Oppenheim–Schur inequalities for causal products", arXiv:2602.21056.
- Sra, "Positive definite functions of noncommuting contractions, Hua–Bellman matrices, and a new distance metric", arXiv:2112.00056 [READ abstract only]: studies positive definiteness of [det(I − A_i* A_j)^{-α}]. For 1×1 contractions this is the family (1 − z_i z̄_j)^{-α}, the Szegő/Drury–Arveson-type kernels in the disc. Background for item E only.
- Hua's determinant inequality |det(I − A*B)|² ≥ det(I − A*A) det(I − B*B) (Hua 1955; Marcus; Xu–Xu–Zhang) — [SNIPPET]. Note it is the n=1 block statement of "the Szegő kernel is positive", i.e. 1 − |φ_B(z)|² ≥ 0; does not give the product over all pairs.

Verdict: no source for the problem. Hypothesis (mine): the "classical result" is Fekete's/Hadamard's bound for the Vandermonde on the unit circle (see B), and the "modern tool" is the Cohn–Kumar / Yudin LP method (see C, H).

---

## B. The "classical result" being generalised

Observation [my own derivation, not a citation]: for rank one, A = (u_i ū_j) with |u_i|=1, ∏_{i≠j}|1 − u_i ū_j| = ∏_{i<j}|u_i − u_j|², and the theorem reads ∏_{i<j}|u_i−u_j|² ≤ n^n. This is exactly Fekete's bound for the circle / Hadamard's inequality for the Vandermonde matrix [u_i^{k}] (|det|² ≤ n^n since entries have modulus 1). So the theorem is a "Gram matrix / Hadamard–Fischer–type" extension of the Vandermonde discriminant bound, with |u_i − u_j| = |1 − u_i ū_j| replaced by |1 − ⟨v_i,v_j⟩|.

Sources:
- Fekete points of the closed unit disc/circle: n-th roots of unity are an n-point Fekete set with δ_n = n^{1/(n−1)} — [SNIPPET] (search result from Saff/Totik-style potential theory notes, arXiv:1010.3760 "Logarithmic Potential Theory with Applications to Approximation Theory", Saff; not opened).
- Hadamard maximal determinant survey, arXiv:2104.06756: for entries in the complex unit disc |det M| ≤ n^{n/2} [SNIPPET].
- Erdős–Herzog–Piranian problem (max ∏|z_i−z_j| over sets of diameter 2): Sothanaphan arXiv:2512.14251 and Cambie et al. arXiv:2603.07088 [SNIPPET]. Relevance: a cautionary tale that regular polygons are NOT optimal for the diameter-normalised problem (even n, improvement factor 1+O(1/n²)), whereas on the circle itself they are. Only background.
- Real unit vectors: [my observation] for real v_i, |1−⟨v_i,v_j⟩| = |v_i−v_j|²/2, so ∏_{i≠j}|1−⟨v_i,v_j⟩| = 2^{-n(n−1)} ∏_{i<j}|v_i−v_j|⁴. AM–GM with Σ_{i<j}|v_i−v_j|² = n² − |Σv_i|² ≤ n² gives ∏_{i<j}|v_i−v_j|² ≤ (2n/(n−1))^{n(n−1)/2}, hence ∏_{i≠j}|1−⟨v_i,v_j⟩| ≤ (n/(n−1))^{n(n−1)} ≈ e^n ≤ n^n. So the real unit-diagonal case is elementary with lots of room (the complex case has no such one-liner known to me, since |1−⟨v_i,v_j⟩| is not controlled by a squared distance). The real unequal-diagonal case is not covered by this one-liner.

---

## C. Minimal energy on circles/spheres of different radii; multi-species; weighted; LP bounds with several radii

### C1. Miezaki–Tagami, "On Euclidean designs and potential energy", Electron. J. Combin. 19 (2012), #P2. [READ]
URL: https://www.combinatorics.org/ojs/index.php/eljc/article/download/v19i1p2/pdf
This is the closest framework to the reduction you derived. Theorem 2 (quoted from the paper, notation: X ⊂ R^d∖{0} finite, w: X→R weights, Q_j Gegenbauer polynomials of S^{d−1} normalised Q_j(1)=dim Harm_j, RX the set of radii occurring):

> Let f : R_{>0}² × [−1,1] → R, g_0 : R_{>0}² → R, and g_{ij} : R_{>0} → R. If h(r,s,t) = g_0(r,s) + Σ_{i,j≥1} g_{ij}(r) g_{ij}(s) Q_j(t) satisfies f(r,s,t) ≥ h(r,s,t) for r,s ∈ RX, t ∈ [−1,1], then
> PE_f(X,w) ≥ Σ_{x,y∈X} w(x)w(y) g_0(‖x‖,‖y‖) − Σ_{x∈X} w(x)² h(‖x‖,‖x‖,1),
> with equality iff f = h at all (‖x‖,‖y‖,x̂·ŷ), x≠y, and Σ_{x,y} w(x)w(y) g_{ij}(‖x‖)g_{ij}(‖y‖)Q_j(x̂·ŷ) = 0 for all i,j ≥ 1.
(Here PE_f(X,w) = Σ_{x≠y} w(x)w(y) f(‖x‖,‖y‖, x̂·ŷ).)

Judgement: **suggests the method / is the general theorem behind your reduction.** Your two-parameter inequality −log|1−√(st)e^{iθ}| ≥ (c_0(s)+c_0(t))/2 + Σ√(c_m(s)c_m(t)) cos mθ is exactly the hypothesis f ≥ h of Theorem 2 with d=2 (Q_j = Chebyshev), g_0(r,s) = (c_0(r²)+c_0(s²))/2, g_j(r) = √c_j(r²), f(r,s,t) = −log|1 − rs e^{iθ}|. The PSD-ness of the remaining term (Σ_{x,y} g_j(r_x)g_j(r_y)cos j(θ_x−θ_y) = |Σ_x g_j(r_x)e^{ijθ_x}|² ≥ 0) is the same Schur/rank-one argument. The paper does not treat logarithmic/radial-product potentials or prove any inequality of your type; it only gives the framework and applications to a-codes on concentric spheres (Cor. 4.1, Thm 5). Note: [my remark] the equality condition in Theorem 2 is *not* automatic when radii differ (the sums |Σ_x g_j(r_x) e^{ijθ_x}|² need not vanish for polygon phases), so with unequal radii this method gives a lower bound that is generally not attained; whether it is as strong as needed is exactly your two-parameter inequality plus the diagonal term bookkeeping.

### C2. Cohn–Kumar, unequal charges remark. [READ] (see H below, Section 4 of the paper)
After Proposition 4.1: "One can easily generalize Proposition 4.1 to deal with the case of unequally charged particles (this was pointed out in Theorem 1 of [Y])", with charges c_i of common sign and energy Σ_{i≠j} c_i c_j f(|x_i−x_j|²): energy ≥ (Σc_i)² α_0 − (Σc_i²) h(1) (the exponent on c_i in the last term is garbled in the PDF text extraction; it is c_i² by the same proof). Also: "We know of few beautiful configurations with unequal charges and none for which linear programming bounds are sharp, but they may well exist." Judgement: **background**: charges multiply f, they are not radii, so it does not cover ρ_i-dependent kernels.

### C3. Borodachov–Boyvalenkov–Dragnev–Hardin–Saff–Stoyanova, "Energy bounds for weighted spherical codes and designs via linear programming", arXiv:2403.07457 [READ statement of Thm 2.1]
URL: https://arxiv.org/abs/2403.07457
Theorem 2.1: for weights W=(w_i), Σw_i=1, E_h(C,W)=Σ_{i≠j} w_i w_j h(x_i·x_j) ≥ f_0 − f(1)Σ w_i² whenever f = Σ f_ℓ P_ℓ^{(n)} has f_ℓ ≥ 0 (ℓ≥1 ... in their class L_h) and f ≤ h on [−1,1); equality needs h = f at the occurring inner products and f_ℓ M_ℓ(C,W) = 0 where M_ℓ are the weighted moments. Potentials: absolutely monotone, incl. −log[2(1−t)]. Judgement: **background** (weights, not radii); confirms the weighted-LP form with Σw_i² h(1) as diagonal correction.

### C4. Other hits [SNIPPET]
- Yudin 1993 (original unequal-charge version), cited in Cohn–Kumar as [Y]; not opened.
- Gaál–Nagy–Nagy-Csiha–Révész, "Minimal energy point systems on the unit circle and the real line", SIAM J. Math. Anal. (2020), arXiv:1911.12195 [READ abstract+intro]: n electrons on the circle in the field of n−1 pairs of protons of charge +1/2 at points a_k ∈ D and a_k* = 1/ā_k; all critical points of the discrete log energy are global minima and are the solutions of B(e^{iτ_j}) = e^{iδ} for a Blaschke product B (uses Semmler–Wegert; refines Simanek, "An electrostatic interpretation of the zeros of paraorthogonal polynomials on the unit circle", arXiv:1501.05672). Judgement: **suggests a method / partial overlap**: this is the "external field from interior points + reflected points" energy, i.e. the energy of u_j against fixed ρ_k u_k-type charges; it solves the *conditional* problem (circle points, fixed interior charges) but not the joint problem and not different-radius mobile charges. I did not check how it specialises to the kernel |1−z w̄|.
- Mixed-radii / "Euclidean design" energy: Delsarte-type LP for concentric spheres also in Bannai–Bannai–Hirao-type literature; not opened.

Queries tried for C: `linear programming bounds energy points on circles of different radii weighted points logarithmic energy two-component product bound regular polygon`; `chessboard estimate reflection positivity Coulomb gas ... different radii` (see F); `maximum product of distances points in disc with prescribed moduli ...`; `Green function unit disc energy N points maximize product |1 - z_i \bar z_j| image charges Fekete Blaschke Coulomb gas disc`. Nothing on "multi-species log energy with product-form bound ∏φ(ρ_i)" found.

[My remark] −Σ_{i≠j} log|1 − z_i z̄_j| = −Σ log|z_i − 1/z̄_j| − Σ log|z_j|: the energy of charges z_i against the *image* charges 1/z̄_j (Green's-function/Neumann-image energy minus the direct term). No paper found that treats exactly this "image-charge-only" energy.

---

## D. Universal optimality / LP bounds on complex spheres, CR sphere, Korányi; positive definite functions on complex spheres

Nothing found on Korányi distance, Heisenberg group, or CR-sphere Fekete/energy problems (queries: `Korányi distance sphere C^d maximal product of pairwise distances Fekete points |1-<z,w>| energy minimization CR sphere`; extended-mode Gram-matrix/Korányi/Heisenberg query).

Relevant background:
- Roy–Suda, "Complex spherical designs and codes", J. Combin. Des. 22 (2014); arXiv:1104.4692 [READ header/abstract; contents show Section 2 "Polynomials of the unit sphere", Section 5 "LP Bounds"]. Sets up Delsarte LP on the unit sphere of C^d with the U(d)-invariant kernels in two variables, which are expansions in *disc (Zernike-type) polynomials* R_{p,q}^{(d−2)}(⟨x,y⟩). Judgement: **background / possibly the right setting for the unit-diagonal complex case beyond the circle**, because the function −log|1−⟨x,y⟩| on the complex sphere is a U(d)-invariant kernel; the positivity of disc-polynomial coefficients is what an LP certificate needs. Not opened beyond the header: I did not verify how LP bounds for energy (Yudin-type) are phrased there.
- Massa–Peron–Porcu, "Positive definite functions on complex spheres and their walks through dimensions", SIGMA 13 (2017), 088, arXiv:1704.01237 [READ abstract]. Disk polynomials, Montée/Descente operators. Background; the Schoenberg-type characterisation on complex spheres is due to Menegatto (1994/1995) and Menegatto–Peron (JMAA 2001), Christensen–Ressel (Math. Z. 1982) for the Hilbert sphere [SNIPPET: via Barbosa–Menegatto and Guella–Menegatto–Peron abstracts; I did not open the original papers]. Statement as relayed: a continuous kernel f(⟨z,w⟩) on the unit sphere of C^d is positive definite iff f(ζ) = Σ_{p,q≥0} a_{p,q} R_{p,q}^{(d−2)}(ζ) with a_{p,q} ≥ 0 (disc polynomial expansion).
- Cohn–Kumar Section 8 [READ]: Theorem 8.2 covers *projective* spaces (real, complex, quaternionic, octonionic) for potentials absolutely monotone in cos d(x,y), i.e. functions of |⟨x,y⟩|², not of ⟨x,y⟩ itself. Hence it does not cover the complex-sphere kernel −log|1−⟨x,y⟩|, which depends on the phase of ⟨x,y⟩. (Section 8 introduction: "generalize Theorem 1.2 to all compact, connected two-point homogeneous spaces".)
- Brauchart/Dragnev/Saff-type "Riesz and Green energy on projective spaces", arXiv:2204.04015 [SNIPPET]: log kernel strictly positive definite on CP^d, asymptotic energy bounds only.
- Kao–Yu, "Semidefinite programming bounds for complex spherical codes", arXiv:2204.04108 [SNIPPET].

Judgement: D gives the *framework* for a possible multi-dimensional LP proof of the unit-diagonal case (n^n bound for unit vectors of any dimension), but I found no paper that carries out a log-energy LP on the complex sphere.

---

## E. Determinant/product inequalities for Drury–Arveson / Szegő-kernel Gram matrices, Pick kernels

Queries: `Drury-Arveson kernel Gram matrix determinant inequality product |1-<z_i,z_j>| unit ball points maximal product`; `Hua's inequality ...`; `determinant of Hadamard inverse matrix [1/(1 - a_ij)] ...`. Nothing relevant found beyond:
- Hua's inequality and Hua–Bellman matrices (see A): [SNIPPET]/[READ abstract of arXiv:2112.00056].
- Cauchy determinant det[1/(1 − x_i ȳ_j)] = ∏_{i<j}(x_i−x_j)(ȳ_j... )/∏(1−x_i ȳ_j) — classical, no source needed; your rank-one route (Cauchy + Oppenheim) is standard.
- Oppenheim's inequality det(A∘B) ≥ det A ∏ b_ii: Czech. Math. J. 59 (2009), dml.cz/bitstream/handle/10338.dmlcz/140473/CzechMathJ_59-2009-1_14.pdf [SNIPPET].
- Hartz–Shalit / Pick kernel surveys (arXiv:2204.01559 "An invitation to the Drury–Arveson space") [SNIPPET]: no determinant bounds of this type.
No inequality "det[1/(1−a_ij)] vs ∏(1−a_ij)" found in the literature.

---

## F. Chessboard estimates / reflection positivity / Hölder-type inequalities; Dyson-type constant terms with one parameter per variable

- Chessboard estimates: Fröhlich–Israel–Lieb–Simon, Commun. Math. Phys. 62 (1978) 1–34 (projecteuclid link from search) and Friedli–Velenik, *Statistical Mechanics of Lattice Systems*, Ch. 10 (unige.ch/~velenik/smbook/Reflection_Positivity.pdf) [SNIPPET]. The chessboard estimate is the lemma ⟨∏_x f_x⟩ ≤ ∏_x ⟨∏_{y} f_x(θ_y-translate)⟩^{1/N} (a generalised Hölder inequality over reflections). Nothing found that applies it to log-energies of points on circles of different radii; the requirement that the interaction be reflection positive is strict and I found no check that −log|1−ρ_iρ_j u_i ū_j| qualifies. Judgement: **only background / speculative**.
- Constant-term identities: Dyson's conjecture with unequal exponents a_i is classical: CT ∏_{i≠j}(1 − x_i/x_j)^{a_i} = (a_1+…+a_n)!/(a_1!⋯a_n!) (Dyson 1962; Gunson, Wilson 1962); Zeilberger–Bressoud (q-case, 1985); Kadell's extensions (Károlyi–Lascoux–Warnaar 2015); Habsieger–Kadell q-Morris [SNIPPET: see https://www.combinatorics.org/ojs/index.php/eljc/article/download/v18i2p2/pdf, https://arxiv.org/pdf/0706.1009, https://arxiv.org/pdf/1911.12479]. The searches found no identity with a *per-variable parameter inside the factor* of the form ∏_{i≠j}(1 − t_i t_j y_i/y_j). [My remark] E_u ∏_{i≠j}(1−ρ_iρ_j u_i ū_j) is a "Cauchy-kernel / Macdonald-type" average; it only bounds the max from below, so it would not prove the inequality.

Queries tried: `chessboard estimate reflection positivity Coulomb gas logarithmic energy on circle unit disc product inequality Hölder points on circles of different radii`; `Dyson constant term identity different parameters each variable \prod_{i\neq j}(1 - t_j x_i/x_j)^{\beta} q-Dyson Macdonald unequal parameters`.

---

## G. Turán power-sum inequalities, weighted ℓ² form, Σ|p_k|²/k

Queries: `Turán power sum inequality \sum |p_k(x)|^2/k points in unit disc lower bound logarithm \sum log(1-|x_i|^{2n}) Fekete circle`. Found only generic Turán power-sum theory [SNIPPET]: Encyclopaedia of Math "Turán theory" (encyclopediaofmath.org/wiki/Turan_theory), Montgomery *Ten Lectures* Ch. 5, Tao/Bogomolny-type arXiv:0704.1879 "Lower bounds in some power sum problems". None states a Σ_k |p_k|²/k lower bound or relates it to Fekete points. [My remark] the identity −log∏_{i≠j}|1−x_i x̄_j| = Σ_{k≥1}(|p_k|² − Σ_i|x_i|^{2k})/k is elementary; the claimed inequality in power-sum form (item 5 of your list) appears to be new relative to the literature I could access.

---

## H. What exactly Cohn–Kumar prove — precise statements [READ, full text of arXiv:math/0607446]

Citation: H. Cohn, A. Kumar, "Universally optimal distribution of points on spheres", J. Amer. Math. Soc. 20 (2007), 99–148. arXiv: https://arxiv.org/abs/math/0607446 (PDF https://arxiv.org/pdf/math/0607446). Page numbers below are the JAMS page numbers.

Setting: potential f: (0,4]→R of squared Euclidean distance; they define a(t) = f(2−2t), "absolutely monotonic on [−1,1) because f is completely monotonic on (0,4]" (§5, p. 121). So everything below is stated for a absolutely monotonic in t = ⟨x,y⟩.

1. **Table 1, p. 102**: n=2, N points, M = N−1, inner products cos(2πj/N) (1 ≤ j ≤ N/2), name "N-gon". **Definition 1.1 (p. 102)**: sharp configuration = m inner products between distinct points and spherical (2m−1)-design. For the N-gon, m = ⌊N/2⌋ and it is an (N−1)-design, N−1 ≥ 2m−1 in all cases.

2. **Theorem 1.2 (p. 101)**: f completely monotonic on (0,4], C a sharp configuration (or the 600-cell), C′ any N-point subset: Σ_{x≠y∈C′} f(|x−y|²) ≥ Σ_{x≠y∈C} f(|x−y|²); strict complete monotonicity gives uniqueness.

3. **Proposition 2.2 (p. 110)** (Hermite interpolation of an absolutely monotonic function): with distinct nodes t_1..t_m ∈ [a,b], multiplicities k_i, p the Hermite interpolant, if f is absolutely monotonic on (a,b) then (f(t) − p(t))/∏(t−t_i)^{k_i} is again absolutely monotonic (strictly if f is). Proof by Q(f,g1g2)=Q(Q(f,g1),g2) and the Taylor/Rolle remainder Lemma 2.1: f(t) − p(t) = f^{(D)}(ξ)/D! ∏(t−t_i)^{k_i}. "Of course the hypothesis that t_1..t_m lie in [a,b] is crucial."

4. **Proposition 4.1 (p. 119) — the LP bound including the constant term**: f any function; h a polynomial with h(t) ≤ f(2−2t) for all t ∈ [−1,1) and h = Σ_{i=0}^d α_i C_i^{n/2−1}(t) with α_i ≥ 0 for ALL i (including i=0). Then every N-point set on S^{n−1} has energy ≥ N²α_0 − N h(1). Proof (p. 120): energy ≥ Σ_{x≠y} h(⟨x,y⟩) = −N h(1) + Σ_i α_i Σ_{x,y} C_i(⟨x,y⟩), and Σ_{x,y}C_i ≥ 0 by positive definiteness, with the i=0 term equal to N²α_0. Sharpness condition stated on p. 121: h(t) = f(2−2t) at every inner product t occurring between distinct points of C, and Σ_{x,y∈C} C_i(⟨x,y⟩) = 0 whenever α_i > 0 and i > 0 (automatic if C is a spherical deg(h)-design). So **the constant term α_0 is covered** (it is the term giving N²α_0). Unequal charges version p. 121 (see C2). Analogue for projective spaces: Proposition 8.3 (p. 132), same statement with f(t) and absolutely monotonic f on [−1,1).

5. **Section 5, Lemma 5.1 and Lemma 5.3 (pp. 121–122)** for the generic auxiliary function; **Section 6 (pp. 123–126)** for sharp configurations. Let t_1<…<t_m be the inner products between distinct points of C and h = H(a, F²) the Hermite interpolant of a(t) = f(2−2t) to order 2 at each t_i, where F(t) = ∏(t−t_i). Then:
   - **Lemma 6.1 (p. 124)**: h(t) ≤ a(t) for all t ∈ [−1,1). Proof: Lemma 2.1 gives a(t) − h(t) = a^{(2m)}(ξ)/(2m)! · ∏(t−t_i)² ≥ 0 (uses only a^{(2m)} ≥ 0 on [−1,1), nodes in [−1,1)).
   - **Positive definiteness of h**: shown via "conductivity": Definition 5.2 (p. 122): g with roots in [−1,1) is *conductive* if H(a,g) is positive definite (nonnegative ultraspherical coefficients, constant term included, since positive definite = all coefficients ≥ 0, p. 113) for every absolutely monotonic a on [−1,1); strictly conductive analogously. **Lemma 5.3 (p. 122)**: g_1,g_2 conductive and g_1 positive definite ⇒ g_1g_2 conductive (via H(a,g_1g_2) = H(a,g_1) + g_1 H(Q(a,g_1),g_2), Proposition 2.2, and closure of positive definite functions under products). Linear factors ℓ_r(t)=t−r are conductive because H(a,ℓ_r) = a(r) ≥ 0. **Lemma 6.2 (p. 124)**: F is (strictly) positive definite, using the (2m−1)-design property. **Lemma 6.3 (p. 125)**: F = p_m + α p_{m−1} for monic orthogonal polynomials p_i of the measure (1−t)(1−t²)^{(n−3)/2}dt; **Theorem 3.1 (p. 114)**: partial products ∏_{i≤j}(t−t_i) are positive definite for j<m. Conclude F and F² are conductive (p. 125), so h = H(a,F²) is positive definite.
   - Sharpness (p. 124): C a (2m−1)-design ⇒ Σ_{x,y}C_i(⟨x,y⟩)=0 for 0<i≤deg h = 2m−1, and h = a at all t_i, so the bound in Prop. 4.1 is attained. Equal to the energy of C, including the constant term.

6. **Caveats relevant to using it for the circle (n=2):**
   - The paper says (p. 112): "We always assume λ ≥ 0 (equivalently, n ≥ 2), because the one-dimensional case is trivial..." with λ = n/2−1. For n=2, λ=0, and C_i^0 as normalised in the paper (C_0=1, C_1 = 2λt) degenerates; the Chebyshev case must be read as the limit (C_i^λ/λ → (2/i)T_i), i.e. cos(iθ) up to positive scaling. The paper never discusses λ=0 explicitly and gives no separate argument for the N-gon beyond Table 1 and Appendix A ("Uniqueness of the N-gon is trivial", p. 145). The ingredients (Theorem 3.1, Lemmas 3.3, 3.5–3.8 on orthogonal polynomials for signed measures; Jacobi weight (1−t)(1−t²)^{-1/2}) are stated for general α, so I expect they hold, but **I did not verify the λ=0 case line by line**.
   - Hypothesis on a: all derivatives a^{(k)} ≥ 0 on [−1,1) — for a(t) = −log|1 − s e^{iθ}| = −½ log(1+s²−2st) this holds for every s>0, s ≠ 1 (a^{(k)}(t) = (k−1)!(2s)^{k−1}·s/(1+s²−2st)^k > 0 for t ≤ 1; note (1+s²)/(2s) ≥ 1). For s=1 it fails only at t=1, which is outside [−1,1). [My computation.] Note that it is NOT convex-decreasing in θ for s<1 near θ=0, so Fejes Tóth–type "convex decreasing function of arc length" results do not apply, whereas Cohn–Kumar does.
   - The theorem for the polygon requires *equal* weights/radii. With different radii the Hermite interpolant depends on s and the cross-term −log|1−√(st)e^{iθ}| is not a function of t=cos θ times a single s; that is exactly the two-parameter inequality in the brief and is NOT covered by Cohn–Kumar (the unequal-charge remark covers products c_ic_j f, not radii-dependent f).
   - Follow-up: Cohn–Kumar–Miller–Radchenko–Viazovska, Ann. of Math. 196 (2022), arXiv:1902.05438 (universal optimality of E8, Leech) — [SNIPPET]; background only, uses a Fourier-interpolation approach instead of LP polynomials.

---

## Most promising leads (≤ 5)

1. **Cohn–Kumar, JAMS 20 (2007)**, https://arxiv.org/abs/math/0607446: Prop. 4.1 (+8.3), Lemma 6.1, Prop. 2.2, Lemma 5.3, §6: exactly what you rely on; constant term covered; the only gap is the n=2 (λ=0) normalisation, not spelled out in the paper.
2. **Miezaki–Tagami, EJC 19 (2012) P2**, https://www.combinatorics.org/ojs/index.php/eljc/article/download/v19i1p2/pdf: Theorem 2 is a Delsarte–Yudin LP bound for weighted points on concentric spheres with kernel h(r,s,t) = g_0(r,s) + Σ g_j(r)g_j(s)Q_j(t); your two-parameter inequality is precisely its hypothesis f ≥ h. Good for citing the framework and for seeing how they handle equality conditions with several radii.
3. **Borodachov–Boyvalenkov–Dragnev–Hardin–Saff–Stoyanova**, https://arxiv.org/abs/2403.07457: weighted LP bound with Σw_i² diagonal correction; absolutely monotone potentials including log; framework to extend to weights ~ g_j(r_x).
4. **Roy–Suda, Complex spherical designs and codes**, https://arxiv.org/abs/1104.4692 (+ Massa–Peron–Porcu https://arxiv.org/abs/1704.01237 for disc polynomials): the natural setting for an LP proof of the unit-diagonal complex-sphere case (n^n bound for arbitrary-dimension unit vectors); need disc-polynomial coefficients of −log|1−ζ| to be ≥ 0 after suitable Hermite-type interpolation (not found in the literature).
5. **Gaál–Nagy–Nagy-Csiha–Révész**, https://arxiv.org/abs/1911.12195: circle points in the field of interior charges + reflected charges; Blaschke-product critical-point/minimum structure; relevant to a "conditional" version where the radii are fixed and only phases vary.

Not found: any source stating the inequality or its special cases; the Tieba post; any Korányi/Heisenberg/CR-sphere log-energy result.
