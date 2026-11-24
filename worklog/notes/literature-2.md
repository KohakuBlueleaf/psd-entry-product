# Literature search, round 2: positivity criteria and LP certificates for the two-radius inequality

Date of search: 2026-11-24. Tools: web search (US-only index, summaries are thin) and direct download plus `pdftotext` of arXiv/author PDFs. Several publisher and mirror sites (core.ac.uk, boris.unibe.ch, emis.univie.ac.at, Cambridge, Springer) blocked automated download, so many classical items are **[SNIPPET]** only.

Legend. **[READ]** = I downloaded the source and read the quoted passage. **[SNIPPET]** = only a search-result summary or abstract, not verified. **[OWN]** = my own derivation or remark, not from a source; check it before relying on it. **[MEMORY]** = classical fact I recall, not re-verified in this session.

Notation for the inequality being proved, as in the brief: D(θ) = d_0 + Σ_{m=1}^{n-2} d_m cos mθ ≥ 0, with d_m ≥ 0 and d_{m}=0 for m ≥ n−1.

**Bottom line.** I found no source that states, or implies, the two-radius inequality, and none for a positivity criterion covering "(cubic-polynomial-coefficient kernel) − (Poisson kernel)". What the literature does offer:

1. The Pólya/Fejér criterion is, in the circle setting, not merely a sufficient condition but the natural one-parameter family: Pólya-type criteria for higher-dimensional spaces (Gneiting, Zastavnyi, Beatson–zu Castell–Xu) are *stronger* hypotheses and add nothing in dimension one. The sharper tools for sequences are Vietoris/Belov (which need monotone coefficients and positivity of *all* partial sums, so they do not apply to Fejér-type truncated kernels) and exact tools (Fejér–Riesz/Toeplitz SDP, Sturm).
2. The Cohn–Kumar/Miezaki–Tagami/BBDHSS framework matches your reduction, but nobody has written the two-radius log-kernel case.
3. Nothing in Lorentzian polynomials, real stability, Prékopa–Leindler or FKG is aimed at a signed-cosine-sum inequality of this type. They give the log-concavity input (d_m ≥ 0) and no more.

---

## 1. Positivity criteria for cosine sums beyond convexity

### 1.0 Exact reformulation used to state all tests [OWN, verified by hand]

Put c(0) = d_0, c(±m) = d_m/2 (1 ≤ m ≤ n−2), c(m) = 0 for |m| ≥ n−1, so D(θ) = Σ_{m∈Z} c(m) e^{imθ}. Define the centred second differences
  e_j := c(j−1) − 2c(j) + c(j+1),  j ≥ 1.
Because c has finite support (Σ_{m∈Z} (δ²c)(m) = 0), summation by parts gives the exact identity
  (1 − cos θ) · D(θ) = Σ_{j=1}^{n−1} e_j (1 − cos jθ).
Checks: c(m) = (J−|m|)_+ gives e_J = 1 and all other e_j = 0, i.e. the Fejér kernel (1−cos Jθ)/(1−cosθ). Also D(0) = Σ_j j² e_j.
- **Fejér/Pólya criterion** = "all e_j ≥ 0, 1 ≤ j ≤ n−1". This is what you already tested (holds for n ≤ 15, fails from n = 16).
- Every other test below is a way of handling a few negative e_j (presumably near j ≈ n−2, n−1, where the Poisson part has no truncation) against the positive mass. The identity says precisely: D ≥ 0 ⇔ the cosine polynomial Σ e_j cos jθ is ≤ Σ e_j everywhere.

### 1.1 Fejér / Young / Kolmogorov / Pólya (convex sequences)

- Statement for the circle, [READ] in Gneiting, "Strictly and non-strictly positive definite functions on spheres", Bernoulli 19 (2013) 1327–1349, arXiv:1111.7077, https://arxiv.org/pdf/1111.7077, Theorem 4 (attributed to Wood 1995, Gneiting 1998b, Beatson–zu Castell–Xu 2011): ψ continuous, nonincreasing, convex on [0,π], ψ(0)=1, ∫_0^π ψ ≥ 0 ⇒ ψ has nonnegative cosine coefficients.
  Note this is the *dual* direction: convex function of θ ⇒ nonnegative coefficients. It is the tool that could give d_m ≥ 0, not D ≥ 0. Our direction (convex coefficient sequence ⇒ nonnegative function) is the classical Fejér theorem [MEMORY], identity in 1.0.
- Judgement: **gives the baseline criterion**; already exhausted by the n ≥ 16 failure.

### 1.2 Vietoris, Askey–Steinig, Brown–Hewitt, Belov, Koumandos, Kwong, Alzer–Kwong

- Askey–Steinig, "Some positive trigonometric sums", Trans. AMS 187 (1974) 295–307, https://doi.org/10.1090/S0002-9947-1974-0338481-3 [SNIPPET].
- Vietoris (1958), via [READ] Sangal–Swaminathan, arXiv:1705.03759, https://arxiv.org/pdf/1705.03759, Theorem 1.1: a_0 ≥ a_1 ≥ … ≥ a_n > 0 and 2k a_{2k} ≤ (2k−1) a_{2k−1} (k ≥ 1) ⇒ Σ_{k=0}^n a_k cos kθ > 0 and Σ a_k sin kθ > 0 on (0,π), for every n.
- **Belov (1995)**, as quoted in the same paper (Lemma 1.1) [READ]: for a decreasing sequence of positive numbers, the condition
    Σ_{k=1}^{N} (−1)^{k−1} k a_k ≥ 0 for all N ≥ 2, a_1 > 0
  is necessary and sufficient for Σ_{k=1}^n a_k sin kθ > 0 on (0,π) for all n, and the same condition implies Σ_{k=0}^n a_k cos kθ > 0 on (0,π) for all n (sufficient only for cosines).
- Brown–Hewitt extension, Brown–Wang–Wilson (S_n^β with β_0 = 0.308443…), Brown–Wang survey: [READ] K. Wang, "A survey of my joint research with Gavin Brown", https://secure.maths.usyd.edu.au/u/donaldc/gbrown/wang.pdf. Includes Theorem 6 there: β ≥ β_0, a_k nonincreasing, k^β a_k ≥ (k+1)^β a_{k+1} ⇒ Σ a_k cos kθ ≥ 0. Brown–Wang–Wilson prove Σ cos(kθ)k^{−β} bounds via Sturm.
- Koumandos, "Positive trigonometric sums and applications", Ann. Math. Inform. 33 (2006) 77–91, https://ami.uni-eszterhazy.hu/uploads/papers/finalpdf/AMI_33_from77to91.pdf [downloaded; I read only the structure and statements of Theorems 3.1, 4.1; they are variants of the above with specific Γ-ratio coefficients].
- Kwong, "Improved Vietoris sine inequalities for non-monotone, non-decaying coefficients", arXiv:1504.06705 [READ abstract/intro]; Alzer–Kwong NYJM 26 (2020) [SNIPPET].

How to test numerically on your sequence: with a_k = d_k (a_0 = d_0, weight 1 as in D = d_0 + Σ d_k cos kθ): check (i) d_0 ≥ d_1 ≥ … ≥ d_{n−2} ≥ 0, (ii) S_N := Σ_{k=1}^{N} (−1)^{k−1} k d_k ≥ 0 for every N ≥ 2 (including N beyond n−2, where it is constant).

**Likely verdict (by hand, [OWN]):** these will fail on the Fejér part of your kernel. For the pure Fejér coefficients d_k = J−k one gets S_2 = d_1 − 2d_2 = 3 − J < 0 for J > 3. The hypotheses demand positivity of *every partial sum*, which is a much stronger conclusion than needed. Kwong states (arXiv:1402.6778, below) that "without the monotonicity assumption, few general results are known". Judgement: **background; probably not applicable** (monotone-coefficient theory for untruncated tails, not truncated polynomial kernels).

### 1.3 Cesàro (C,δ) kernels and "higher-order convex" mixtures

- Positivity of Cesàro (C,δ) kernels for δ ≥ 1 in the cosine case (Fejér, Kogbetliantz 1924; in Gegenbauer form: nonnegative iff δ ≥ 2λ+1, so δ ≥ 1 for λ→0): [SNIPPET], via R. Askey, "Positive Cesàro means of numerical series" (typeset.io listing, not downloadable) and arXiv:1912.07533 https://arxiv.org/pdf/1912.07533, arXiv:math/0312526 https://arxiv.org/pdf/math/0312526. The δ ≥ 1 threshold for cosines is my inference from the Gegenbauer statement [OWN].
- Relevance: the kernels m ↦ binom(N−m+δ−1, δ)_+ have *polynomial-of-degree-δ coefficients* (δ = 1: the Fejér coefficients N−m). So "a kernel with cubic-polynomial coefficients" is a Cesàro-type kernel. If your cubic is a nonnegative combination of such (C,δ) coefficient families, δ ≥ 1, each positive, then the polynomial part is positive without being convex-in-the-Fejér-sense mixture. Test: expand the cubic P(n−m) in the basis binom(N−m+δ−1, δ), δ = 1,2,3, plus shifts N, and check coefficient signs. The subtraction of the Poisson part is then the only obstruction.
- Judgement: **gives a usable criterion for the leading term; does not by itself handle "− Poisson"**.

### 1.4 Equivalence with positive definiteness of the piecewise-linear (or spline) interpolant; Pólya-type and Turán results

- Schep's theorem (piecewise linear function with integer nodes: positive definite on R ⇔ its restriction to Z is positive definite) and Zastavnyi's generalisation, Math. Notes 107 (2020) 959–971, https://link.springer.com/article/10.1134/S0001434620050272 [SNIPPET]. In our language: Fourier transform of the piecewise-linear interpolant of c(·) is sinc² × D(θ), so "PD interpolant" ⇔ D ≥ 0, and convexity of c is the Pólya sufficient condition. [OWN, from the standard identity.]
- **Poisson-summation test [OWN]:** if ψ is any even function on R with ψ(m) = c(m) at integers (not nec. piecewise linear) and ψ̂ ≥ 0, then D(θ) = Σ_k ψ̂(θ + 2πk) ≥ 0. Your d_m are given by closed formulas that continue analytically in m (the k_m(w) are explicit in m), so one can look for a smooth PD extension, e.g. cubic-spline interpolant or analytic continuation times a cutoff. Zastavnyi–Trigub, "Positive-definite splines of special form", Sb. Math. 193 (2002) 1771–1800, https://mathnet.ru/eng/sm699 [SNIPPET: abstract only] is the source for positive-definite even splines supported on [−1,1] that are polynomials on [0,1] (e-splines, A-splines).
- Gneiting, "Criteria of Pólya type for radial positive definite functions", Proc. AMS 129 (2001) 2309–2318, https://www.ams.org/journals/proc/2001-129-08/S0002-9939-01-05839-7/ [SNIPPET]; and Gneiting, "Radial positive definite functions generated by Euclid's hat", J. Multivariate Anal. 69 (1999) 88–119 [SNIPPET]. Those criteria assume derivative convexity conditions (e.g. −φ'(√t) convex ⇒ PD on R³, [READ] in Gneiting 2013, Thm 5). They are *stronger* hypotheses than Pólya's in dimension one (e.g. (1−t)_+^τ: Pólya needs τ ≥ 1, the R³-criterion needs τ ≥ 2). So they give **no new test in dimension 1**.
- Ehm–Gneiting–Richards, "Convolution roots of radial positive definite functions with compact support", Trans. AMS 356 (2004) 4655–4685, https://www.ams.org/tran/2004-356-11/S0002-9947-04-03502-0/ [SNIPPET]. Positive result: nonnegative radial PD functions with compact support have radial half-support convolution roots; negative result in R² for the spherical correlation function; includes Turán-problem bounds. Relevance: a convolution root φ = ψ*ψ means ψ̂² = φ̂ ≥ 0, i.e. a Fejér–Riesz-type factorisation. **Background only.**
- Jaming–Matolcsi–Révész, Kolountzakis–Révész, Kolountzakis–Lev–Matolcsi (arXiv:2510.10172): Turán/Delsarte duality for PD functions with given support [SNIPPET]. My search did not find a Pólya-type criterion in these. **Background only.**
- Otten–Nguyen–Watts, arXiv:2608.04836 (Bernstein operators preserve PD on S¹; reduces to nonnegativity of cosine coefficients via explicit formula and a two-regime argument) [READ abstract/intro]: an example of how a recent proof of cosine-coefficient positivity is organised; no transferable criterion.

### 1.5 Exact tests (for numerics and as proof-by-computation templates)

- **Fejér–Riesz / Toeplitz-PSD certificate** [SNIPPET: arXiv:math/0503133, arXiv:1811.06005, https://arxiv.org/pdf/1811.06005; B. Dumitrescu, *Positive Trigonometric Polynomials and Signal Processing Applications*, Springer 2007]. D ≥ 0 on [0,2π] ⇔ D = |Q(e^{iθ})|², deg Q ≤ n−2 ⇔ there is a Hermitian PSD (n−1)×(n−1) matrix G with Σ_i G_{i,i+k} = c(k) for |k| ≤ n−2. Exact; gives a certificate you can inspect for patterns (rank, sparsity) as n grows. Judgement: **usable exact test**; possibly the way to find the analytic factorisation.
- **Sturm procedure**, M. K. Kwong, "Nonnegative trigonometric polynomials, Sturm's theorem, and symbolic computation", arXiv:1402.6778, https://arxiv.org/pdf/1402.6778 [READ intro]: rigorous nonnegativity proof for any rational trigonometric polynomial on an interval; used to close finitely many small-n cases when an asymptotic argument works for large n. Kwong's remark (verbatim idea): the usual general criteria need monotone coefficients; without monotonicity few general results exist. Judgement: **usable for finite n ranges** (e.g. handle n ≤ N_0 once an analytic argument covers n ≥ N_0).

### 1.6 "Convex minus geometric" specifically

Searched for: Pólya-type results for φ(t) − c e^{−at}; Poisson-kernel subtraction from Fejér/Cesàro kernels; "Fejér–Poisson" comparison. **Nothing found.** The closest are the Brown–Wang–Wilson sums (k^{−β} coefficients, i.e. algebraic not geometric tails) and Kwong's non-monotone Vietoris extensions. Own suggestion [OWN]: since the geometric part is explicit (Poisson kernel 1/(cosh α − cos θ) up to normalisation) and the polynomial part is a closed form in cos θ, sin nθ, cos nθ, the problem is a calculus problem for one explicit trigonometric function; the e_j identity of 1.0 localises exactly where convexity fails.

---

## 2. Geometric means / interpolation of LP (Delsarte–Yudin) certificates; two-radius, multi-shell, weighted configurations

- **Miezaki–Tagami**, "On Euclidean designs and potential energy", Electron. J. Combin. 19(1) (2012) P2, https://www.combinatorics.org/ojs/index.php/eljc/article/download/v19i1p2/pdf, arXiv:1109.2226 https://arxiv.org/abs/1109.2226. [READ in round 1, Theorem 2 quoted there.] Same framework as your reduction (kernel g_0(r,s) + Σ g_{ij}(r)g_{ij}(s)Q_j(t) ≤ f). **Not re-read this round; nothing new found about its citations**: the search tool does not return citation counts, and I found no paper that applies their Theorem 2 to a logarithmic or radial-product potential. Judgement: **suggests the method**, no result.
- **Borodachov–Boyvalenkov–Dragnev–Hardin–Saff–Stoyanova**, "Energy bounds for weighted spherical codes and designs via linear programming", arXiv:2403.07457, https://arxiv.org/abs/2403.07457 [READ in round 1]. This round I grepped its introduction [READ]: it states that weighted designs and "Euclidean designs on several concentric spheres were first considered in [30]", where [30] = A. Neumaier and J. J. Seidel, "Discrete measures for spherical designs, eutactic stars and lattices", Indag. Math. (Proc.) 91 (1988) 321–334, and refers to Bannai–Bannai, "A survey on spherical designs and algebraic combinatorics on spheres", Europ. J. Combin. 30 (2009) 1392–1425 (comprehensive survey) [both SNIPPET/bibliography only]. Weights there are independent of the Gegenbauer index ℓ; your certificate has ℓ-dependent weights g_m(r) = √Γ_m(p), which is the rank-one coefficient structure of Miezaki–Tagami. Judgement: **background**.
- **Cohn–Kumar**, JAMS 20 (2007), arXiv:math/0607446, https://arxiv.org/abs/math/0607446 [READ round 1: Prop. 2.2, Lemma 5.3, §6 conductivity]. The structural point relevant now: for a *single* radius the certificate is the Hermite interpolant H(a, F²), which here is your h_s. Your two-radius inequality has the form g_σ(θ) ≥ [Hermite-interpolant data at p and q combined by geometric means]; since g_σ ≥ h_σ is Cohn–Kumar and h_σ has coefficients Γ_m((p+q)/2) ≥ √(Γ_m(p)Γ_m(q)) (log-concavity), the required inequality is equivalent to
    ε_σ(θ) := g_σ − h_σ  ≥  Σ_m [Γ_m(σ-radius) − √(Γ_m(p)Γ_m(q))] cos mθ  (+ constant-term bookkeeping),
  i.e. a *nonnegative-coefficient* cosine sum must stay below the Fejér × Poisson-mixture error. [OWN restatement; it follows directly from your formulas.] Alternative PSD kernels with the right diagonal, [OWN]: K_m(p,q) = Γ_m(max(p,q)) = ∫ k_m(w)1[w≥p]1[w≥q]dw and K_m(p,q) = ∫_0^∞ √(k_m(v+p)k_m(v+q)) dv are also PSD with diagonal Γ_m(p). Both are coefficientwise ≤ √(Γ_m(p)Γ_m(q)) (Cauchy–Schwarz), so they weaken the certificate in the direction the cosine sign allows only if the corresponding cos mθ terms are ≥ 0, so they do not obviously help.
  The Hankel kernel Γ_m((p+q)/2) is PSD only if Γ_m is completely monotone; here k_m(0)=0 and k_m increases first, so it is not. This is the reason geometric means (rank one) are needed. [OWN, from the formulas in the brief.]
- **Yudin 1993** (original unequal-charge/LP energy, cited in Cohn–Kumar) [SNIPPET]; **Bilyk–Glazyrin–Matzke–Park–Vlasiuk**, "Energy on spheres and discreteness of minimizing measures", arXiv:1908.10354, https://arxiv.org/abs/1908.10354, and "Optimal measures for p-frame energies on spheres", arXiv:1908.00885, https://arxiv.org/abs/1908.00885 [SNIPPET: abstracts]. Relevance: LP/positive-definite methods for measures (discreteness of minimisers) on spheres/projective spaces with *absolutely monotone-type* kernels; no radius variable. **Background only.**
- Cohn–Kumar–Miller–Radchenko–Viazovska, Ann. of Math. 196 (2022), arXiv:1902.05438, https://arxiv.org/abs/1902.05438 [SNIPPET]: universal optimality of E8/Leech via Fourier interpolation. **Background only** (different mechanism; no polygon/radius content).
- Explicit treatment of regular n-gons on two concentric circles for log or Riesz energy: **not found**, in Google-style queries for "concentric circles", "two radii", "Riesz energy polygons", "weights radii".
- Gaál–Nagy–Nagy-Csiha–Révész (round 1) remains the only result with *interior charges and reflected charges* log energy on the circle.

---

## 3. Hermite–Fejér interpolation at roots of unity; tail integrals, log-concavity, hazard rates

- Hermite–Fejér on the circle with n-th roots of a unimodular number: Daruis–González-Vera (2001); Berriochoa–Cachafeiro–Díaz–Martínez-Brey, "Rate of convergence of Hermite–Fejér interpolation on the unit circle", J. Appl. Math. 2013, https://doi.org/10.1155/2013/407128 [SNIPPET; PDF blocked]; ETNA 44 (2015) 140–152, https://etna.ricam.oeaw.ac.at/vol.44.2015/pp140-152.dir/pp140-152.pdf [SNIPPET]; Bahadur–Varun, arXiv:2202.13161, https://arxiv.org/pdf/2202.13161 [READ abstract/intro: Jacobi-projected nodes, higher order; no kernel/positivity formula]. These give convergence and error constants for analytic f. **No source found for the Fejér-kernel × Poisson-mixture error representation, nor for positivity/log-concavity of the Hermite–Fejér Chebyshev coefficients in the radius.** Judgement: **background only**; your representation g_s − h_s = ½ Fejér_n ∫_p^∞ ρ_n P_w dw appears to be new relative to what I could reach.
- Log-concavity of tail integrals and monotone hazard rate: Prékopa (1973) preservation of log-concavity under convolution/marginalisation [SNIPPET via arXiv:2512.07768 https://arxiv.org/pdf/2512.07768]; classical fact [MEMORY]: if k is log-concave on R then Γ(p) = ∫_p^∞ k is log-concave and the hazard rate k/Γ is nondecreasing (e.g. Bagnoli–Bergstrom, "Log-concave probability and its applications", Econom. Theory 26 (2005) 445–469 [MEMORY, not opened]). An integral inequality for log-concave functions tied to failure rates: Cambridge note at https://www.cambridge.org/core/product/8889FE47D318F8F343C75111A7B6AA27/core-reader [SNIPPET; third proof via Prékopa–Leindler]. This is the natural source for your "d_m ≥ 0 from log-concavity of Γ_m": Prékopa–Leindler with λ = 1/2 and f = k_m 1_{[p,∞)}, g = k_m 1_{[q,∞)}, h = k_m 1_{[(p+q)/2,∞)} gives Γ_m((p+q)/2) ≥ √(Γ_m(p)Γ_m(q)) whenever k_m is log-concave [OWN, standard]. Judgement: **gives d_m ≥ 0 (already have)**; nothing beyond.
- Lerch transcendent / incomplete beta: not pursued beyond search; no hit.

---

## 4. Total positivity, variation diminishing, FKG-type tools

- Karlin, *Total Positivity* Vol. I (Stanford 1968) [MEMORY]: the kernel e^{xy} is TP (extended); K(x,y) = 1_{y≤x} is TP; variation-diminishing property. [SNIPPET] confirmation via arXiv:1908.04667 https://arxiv.org/pdf/1908.04667. [OWN] sinh(xy) = Σ (xy)^{2k+1}/(2k+1)! is a positive combination of x^{2k+1}y^{2k+1}, so TP on x,y > 0 by Cauchy–Binet with generalized Vandermonde minors; so sinh((n−m)w) is TP in the pair (n−m, w). The numerator of k_m is a *difference* sinh((n−m)w) − (n−m) sinh w, so TP is not inherited; I found no literature on TP of such a difference. Judgement: **background only**.
- Khare, "Multiply positive functions, critical exponent phenomena, and the Jain–Karlin–Schoenberg kernel", arXiv:2008.05121, https://pdf.arxiv.org/pdf/2008.05121 [SNIPPET]. Background for TP of power-type kernels.
- Karlin–Rinott, "Classes of orderings of measures and related correlation inequalities I", J. Multivariate Anal. 10 (1980) 467–498 [SNIPPET: MTP2 preserved under marginalisation and composition]; Ahlswede–Daykin four-functions theorem [SNIPPET: Encyclopedia of Math https://encyclopediaofmath.org/wiki/Correlation_inequalities]; Richards, higher-order FKG (alternating sums), Ann. Probab. 2004, https://projecteuclid.org/download/pdfview_1/euclid.aop/1084884860 [SNIPPET]. These produce *same-sign* correlation inequalities. Your needed inequality has signed coefficients cos mθ and sum over m, with a monotone-in-m ratio Γ_m(q)/Γ_m(p) (TP2 structure) but the multiplier cos mθ is oscillating, so there is no monotone test function to correlate with. **No direct application found; background only.**
- Geometric means of PD sequences: the scalar statement "√(a_k b_k) is the Fourier sequence of a positive function when a, b are" is false in general (Hadamard geometric mean preserves positivity only under extra structure). The matrix/operator version (Ando's G(M,N)∘G(M,N) ≤ M∘N; Feng–Tonge, "geometric means and Hadamard product", https://www.personal.kent.edu/~bfeng/publication/geomatric%20means%20and%20Hadamard%20product.pdf; Audenaert et al., arXiv:2107.09459 https://arxiv.org/pdf/2107.09459) [SNIPPET] controls Hadamard products of matrix geometric means, not cosine sums with phase. **Background only.**

---

## 5. Reverse / Lorentzian Cauchy–Schwarz; Lorentzian polynomials; real stability

- Aczél (1956) inequality, Popoviciu, Bellman, reverses (Vasić–Pečarić, Tian, Wu; recent Miao–Dragomir 2025 refinements; operator versions Kaleibary–Furuichi, arXiv:1707.07147 https://arxiv.org/pdf/1707.07147, arXiv:2001.05088 https://arxiv.org/pdf/2001.05088) [SNIPPET]. These are for sums of positive numbers with a "Lorentzian" quadratic form a_1² − Σ a_i². Your sum Σ √(Γ_m(p)Γ_m(q)) cos mθ is not of that form unless one groups cos mθ > 0 and < 0 terms, which is θ-dependent. **No fit found.**
- Brändén–Huh, "Lorentzian polynomials", Ann. of Math. 192 (2020) 821–891, arXiv:1902.03719, https://arxiv.org/abs/1902.03719 [SNIPPET]. Class closed under products; log-concavity of coefficient sequences (ultra log-concave) for M-matrix characteristic polynomials. No PSD matrix product inequality of our kind found. **Background only.**
- Real stability: Borcea–Brändén; Marcus–Spielman–Srivastava, arXiv:1306.3969 https://arxiv.org/pdf/1306.3969, arXiv:1304.4132 https://arxiv.org/pdf/1304.4132 [SNIPPET]: det(Σ z_iA_i) is real stable for PSD A_i. The mechanism gives real-rootedness of expected characteristic polynomials and capacity inequalities (permanents), none of which is a lower bound for ∏|1−a_ij|. **Background only.**

---

## 6. Entrywise/Hadamard functions of PSD matrices; Schur polynomials

- **Belton–Guillot–Khare–Putinar**, "Matrix positivity preservers in fixed dimension. I", Adv. Math. 298 (2016), arXiv:1504.07674, https://arxiv.org/pdf/1504.07674 [READ Theorems 1.1, 1.6 and intro]. Statement relevant to you: Theorem 1.6. For M ≥ N, scalars c_0,…,c_{N−1} > 0, and every nonzero A ∈ P_N(D(0,ρ)) (PSD N×N, entries in the closed disc, complex allowed),
    inf_{v ∈ K(A)^⊥∖0} v*(Σ_{j<N} c_j A^{∘j}) v / v* A^{∘M} v ≥ C(c; z^M; N, ρ)^{−1},
  with C explicit (Theorem 1.1 formula via binomials and Schur polynomials) and sharp, attained already on *positive rank-one* matrices. Relevance: a sharp comparison of low Hadamard powers against a high one in exactly the dimension N = number of points, proved with Schur polynomials. Caveats: (i) the direction is "low powers dominate a high power" (upper bound for 1ᵀA^{∘M}1), the opposite of the lower bound needed for Σ_k (1/k) 1ᵀA^{∘k}1; (ii) the extremal matrices are positive rank one, not roots-of-unity phases. Judgement: **background / possibly a technique source** (Schur-polynomial inequalities with fixed N).
- Khare, "Smooth entrywise positivity preservers, a Horn–Loewner master theorem, and symmetric function identities", arXiv:1809.01823, https://arxiv.org/pdf/1809.01823; BGKP Part II (positive definiteness and strict monotonicity of Schur function ratios) arXiv:2310.18020, https://arxiv.org/abs/2310.18020; Khare, *Matrix Analysis and Entrywise Positivity Preservers*, Cambridge Univ. Press 2022 [all SNIPPET]. Background for Schur-ratio monotonicity.
- **Cauchy identity route [OWN, standard]:** for rank one, A = u u*, u ∈ D^n: ∏_{i,j}(1 − u_i ū_j)^{−1} = Σ_λ |s_λ(u)|² (Cauchy identity; [SNIPPET] confirmation via arXiv:2202.11175 and Macdonald). The conjectured bound is then Σ_λ |s_λ(u)|² ≥ ∏_i (1 − |u_i|^{2n})^{−1} (rank-one case). Equality case: u_i = ρ ω^i, because s_λ at n-th roots of unity is ±1 or 0, and vanishes unless the n-core of λ is empty (Littlewood; [SNIPPET] arXiv:2212.07343 https://arxiv.org/pdf/2212.07343, arXiv:2109.11310 https://arxiv.org/pdf/2109.11310; ±1/0 values: Littlewood–Richardson 1934), which reproduces (1−ρ^{2n})^{−n}. Equivalent form via Cauchy's determinant: ∏_{i,j}(1−u_iū_j) = ∏_{i<j}|u_i−u_j|² / det[1/(1−u_iū_j)], so the claim is ∏_{i<j}|u_i−u_j|² ≤ det[1/(1−u_iū_j)] · ∏(1−|u_i|^{2n}). No source for either form found.
- Angarone–Soskin, "Generalized diagonals in positive semi-definite matrices", arXiv:2409.06907, https://arxiv.org/pdf/2409.06907 [READ abstract/intro]: complete description of inequalities |x_{1,ς(1)}…x_{n,ς(n)}| ≤ |x_{1,τ(1)}…x_{n,τ(n)}| between permutation products of entries of PSD matrices, via a partial order on S_n. Different object (products over permutations, not over all entries; no 1−a). **Background only.**
- Khare, "Sharp nonzero lower bounds for the Schur product theorem", arXiv:1910.03537 [SNIPPET]: lower bounds for M∘N; and Sra, arXiv:2112.00056 (Hua–Bellman matrices) [READ abstract round 1]: nothing about ∏(1−a_ij).

---

## 7. Which "modern tool" would a proof use?

No source states the matrix inequality, so this is an assessment, not a finding.

- Closest existing machinery for the rank-one/unit-diagonal case: Cohn–Kumar LP (Hermite interpolation, conductivity), plus Miezaki–Tagami for radii. This is the route you are on. The remaining unproved step is exactly the two-radius inequality.
- Alternative machinery visible in the literature: **Schur-function generating series** (Cauchy identity + Littlewood vanishing at roots of unity, Item 6): it reproduces the equality case cleanly and turns the claim into a lower bound of Σ_λ |s_λ(u)|² for u ∈ D^n. Positivity-preserver technology (BGKP) is the only place I found sharp Schur-polynomial inequalities in fixed dimension N, but they bound the wrong direction.
- Not supported by anything found: free probability, optimal transport, Drury–Arveson/von Neumann inequality (Hartz–Shalit survey arXiv:2204.01559 [SNIPPET] has no determinant bound of this kind), real stability, Lorentzian polynomials.

---

## Most promising leads (≤ 6)

1. **Exact identity (1−cosθ)D(θ) = Σ_j e_j(1−cos jθ)** (Section 1.0, [OWN]) combined with the **Fejér–Riesz/Toeplitz SDP certificate** (https://arxiv.org/pdf/1811.06005; Dumitrescu 2007) and the **Sturm procedure** (Kwong, https://arxiv.org/pdf/1402.6778): finds where convexity fails, gives an inspectable certificate, and closes finite-n ranges.
2. **Cesàro (C,δ) kernels / Pólya via smooth PD extension** (Askey; arXiv:1912.07533; Poisson-summation test of 1.4; Zastavnyi–Trigub https://mathnet.ru/eng/sm699): a criterion that fits the cubic-polynomial leading term; test cubic basis expansion and spline PD extensions.
3. **Cohn–Kumar** https://arxiv.org/abs/math/0607446 with the reformulation ε_σ ≥ Σ δ_m cos mθ (Section 2): reduces the two-radius inequality to "Fejér×Poisson error dominates a nonnegative-coefficient cosine sum".
4. **Miezaki–Tagami** https://www.combinatorics.org/ojs/index.php/eljc/article/download/v19i1p2/pdf and **BBDHSS** https://arxiv.org/abs/2403.07457: the correct frameworks to cite and to model the equality-case bookkeeping.
5. **Belton–Guillot–Khare–Putinar** https://arxiv.org/pdf/1504.07674 (Thm 1.1/1.6, Schur-polynomial sharp Hadamard-power inequalities in fixed N) plus the **Cauchy-identity/Littlewood roots-of-unity** reformulation of Item 6: the only alternative-route material; direction mismatch noted.
6. **Prékopa–Leindler / log-concave tail** (https://www.cambridge.org/core/product/8889FE47D318F8F343C75111A7B6AA27/core-reader): supplies d_m ≥ 0 rigorously; nothing beyond.

Explicitly negative: Vietoris/Askey–Steinig/Belov/Brown–Hewitt/Koumandos criteria fail already on pure Fejér-type coefficients (S_2 = 3−J); Gneiting/Zastavnyi Pólya-type criteria add nothing in dimension one; no source on two-radius log-energy polygons; none on Lorentzian/real-stable approaches to this inequality.
