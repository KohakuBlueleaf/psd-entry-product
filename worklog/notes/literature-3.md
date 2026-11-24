# Literature search, round 3: Beurling–Selberg extremals, positivity criteria, the inequality in other guises, multi-radius LP

Date: 2026-11-25. Tools: web search (US index, thin snippets) and direct download + `pdftotext` of arXiv papers.
Legend: **[READ]** = I downloaded the paper and read the quoted passage. **[SNIPPET]** = search snippet or abstract only. **[OWN]** = my derivation or remark, not in a source; check before use. **[MEMORY]** = recalled, not verified now.
Not repeated here: Delsarte–Yudin, Cohn–Kumar, Miezaki–Tagami, Oppenheim, Schur product basics, and everything in literature.md / literature-2.md.

## Bottom line

1. **Angle 3 gave the one genuinely new and relevant find.** Ounaïes, arXiv:2601.10411 (Jan 2026), proves the **rank-one case of an additive version of our inequality, with unequal moduli**. It is a short Cauchy–Schwarz/Blaschke-product proof in the Hardy space. It also proves Alexander's conjecture on Cassels' inequality, i.e. the rank-one, equal-radius, off-diagonal version of our inequality (Schur 1918 for ρ = 1). Details and an honest assessment are in §3.1. Both statements are explained there; the key point is that the unequal-diagonal case is NOT reached by it.
2. **Beurling–Selberg (angle 1):** the periodic extremal problem for log|1−e(x)| (our p = 0) is solved in L¹(Lebesgue) (Carneiro–Vaaler III, Thm 1.4). The theory has explicit Fourier coefficients of the extremal minorant/majorant for Gaussians (theta functions; CLV Thm 4) and a version for general measures ϑ on the circle (Carneiro–Littmann, Thm 27/29). I found **no result on how extremals depend on the parameter other than "integrate the parameter", none on geometric means of coefficients at two parameters.** Our h_p is not the Lebesgue-L¹-extremal minorant (it interpolates at Z∖{0}, not at Z or Z+½); see §1.4.
3. Angle 2 and angle 4: nothing new that applies (details below).
4. Chinese sources / MO / MSE: nothing found for the inequality text.

---

## 1. Beurling–Selberg / Holt–Vaaler / Carneiro–Vaaler–Littmann

Searched: Carneiro–Vaaler II, III; Carneiro–Littmann–Vaaler (CLV); Carneiro–Littmann (de Branges); Littmann (Laguerre–Pólya interpolation, quadrature, Bessel zeros). Read in full text: CV III, CLV, Carneiro–Littmann 1406.5456 (periodic section §8).

### 1.1 Carneiro–Vaaler, "Some extremal functions in Fourier analysis, III", Constr. Approx. 31 (2010) 259–288, arXiv:0809.4053 [READ intro, §6]
- **Theorem 1.4** (periodic log case, p = 0 of our problem). For N ≥ 0 there is a unique real trigonometric polynomial v_N of degree ≤ N such that for every trigonometric polynomial ṽ of degree ≤ N,
  ∫_{R/Z} |log|1−e(x)| − ṽ(x)| dx ≥ 4G/((2N+2)π), G = Catalan's constant, equality iff ṽ = v_N.
  v_N is given explicitly in their §6 (eq. (6.26)–(6.28)), v_N = −k_μ(N;·) for μ = their Haar-type measure (1.21).
- Method: Poisson summation applied to x ↦ e^{−λ|x|} and to the one-sided kernel K(λ,x), then integrate the parameter λ against a measure μ (§6, Theorem 6.2). The log case is the Stieltjes/Haar-type measure.
- This is **best (two-sided) L¹ approximation**, not one-sided, because −log|1−e(x)| → +∞ at x = 0 (no polynomial majorant, and the minorant problem is not what Thm 1.4 solves).
- Carneiro–Vaaler II, Trans. AMS 362 (2010) 5803–5843, arXiv:0809.4050 [downloaded, only skimmed; MEMORY for the journal]: extremal **majorants** of exponential type for even functions of the form ∫(e^{−λ|x|} − 1) dν(λ), including log|x|, |x|^α.

### 1.2 Carneiro–Littmann–Vaaler, "Gaussian subordination for the Beurling–Selberg extremal problem", Trans. AMS 365 (2013) 3493–3534, arXiv:1008.4969 [READ Part I, Theorems 1–6]
For G_λ(x) = e^{−πλx²}:
- **Thm 2/3.** Let F be real entire of exponential type ≤ 2π. If F ≤ G_λ then ∫F ≤ λ^{−1/2} θ₂(0, iλ^{−1}), equality iff F = L_λ (interpolates G_λ and G_λ' on Z+½). If F ≥ G_λ then ∫F ≥ λ^{−1/2} θ₃(0, iλ^{−1}), equality iff F = M_λ (interpolates value and derivative on Z).
- **Thm 4 (explicit Fourier transforms; this is the closest formula to our Γ_m).** For |t| ≤ 1:
  L̂_λ(t) = (1−|t|) θ₁(t, iλ) − (2π)^{−1} λ sgn(t) ∂θ₁/∂t (t, iλ),
  M̂_λ(t) = (1−|t|) θ₃(t, iλ) − (2π)^{−1} λ sgn(t) ∂θ₃/∂t (t, iλ).
  I.e. "(Fejér weight)·(periodised transform) + derivative correction".
- **Thm 5/6 (periodic, Lebesgue measure on R/Z).** For degree ≤ N: ℓ_{λ,N}(x) ≤ θ₃(x, iλ^{−1}) ≤ m_{λ,N}(x), ℓ_{λ,N}, m_{λ,N} are the unique extremal minorant/majorant; ∫q ≤ θ₂(0,iλ^{−1})(N+1)² resp. ∫r ≥ θ₃(0,iλ^{−1})(N+1)² (their (1.25),(1.27), as I read them, the displayed constants carry λ-dependent normalisations; check before quoting).
- **Gaussian subordination.** Part II of the paper: for G(x) = ∫ e^{−πλx²} dν(λ) (ν ≥ 0, suitable integrability) the extremal minorant/majorant is the same integral of the L_λ / M_λ, because the interpolation nodes do not depend on λ. Applications listed in the abstract include log(x²+α²), log((x²+α²)/(x²+β²)), |x|^α, |x|^{2n}log|x|.
- Parameter dependence in the literature = "integrate the parameter against a positive measure". Nothing on monotonicity/log-concavity/PSD-ness of the extremal operators in λ was found (searched; snippet-level for II).

### 1.3 Carneiro–Littmann, "Extremal functions in de Branges and Euclidean spaces", arXiv:1406.5456 (Adv. Math. 260 (2014) [MEMORY]) [READ §8]
This is the only source with **extremal trigonometric polynomials for a general even probability measure ϑ on R/Z** (not only Lebesgue).
- Setting: f_λ(θ) = cosh(λ(θ−⌊θ⌋−½))/sinh(λ/2) = Σ_j e^{−λ|θ+j|} (1-periodic). φ_{n+1} = (n+1)-th orthonormal polynomial on the unit circle for ϑ, K_n its CD kernel, A_{n+1}, B_{n+1} the associated real-trigonometric polynomials built from φ_{n+1}, φ*_{n+1} (their (8.8)–(8.10)), 𝒜_{n+1}, ℬ_{n+1} their zero sets (n+1 points each; ℬ contains 0).
- **Theorem 27.** (i) If ℓ ∈ Λ_n (trig. polys of degree ≤ n) and ℓ ≤ f_λ, then ∫ℓ dϑ ≤ Σ_{ξ∈𝒜_{n+1}} f_λ(ξ)/K_n(e(ξ),e(ξ)); there is a unique ℓ_ϑ(n,λ,·) ∈ Λ_n with ℓ ≤ f_λ and equality, and it interpolates f_λ **and f_λ'** at 𝒜_{n+1}. (ii) majorant analogue with ℬ_{n+1}, 2n+1 conditions because f_λ is not differentiable at 0.
- **Theorem 29** integrates λ against a positive measure ς: h_ς(θ) = ∫(f_λ(θ) − f_λ(½)) dς(λ). Minorant case needs ∫λ e^{−aλ} dς < ∞ (all a>0); majorant needs ∫λ/(1+λ) dς < ∞. Same node sets.
- Lemma 28 / proof of Thm 27 use the Laguerre–Pólya interpolation scheme of their §2 and a Gauss-type quadrature (their Corollary 26) ∫ℓ dϑ = Σ ℓ(ξ)/K_n(ξ,ξ) for ℓ ∈ Λ_n, ξ ∈ 𝒜_{n+1}.

### 1.4 What this says about our h_p [mostly OWN; use as hypotheses, not facts]
1. **g_p is exactly a periodised −½log(x²+a²).** With x = θ/2π, a = p/2π: ĝ_p(m) = e^{−p|m|}/(2|m|) (m ≠ 0), which is the Fourier transform of −½log(x²+a²) up to normalisation sampled at m (the Poisson-summation identity Π_j((x+j)²+a²) ∝ cosh 2πa − cos 2πx). So g_p is in the periodised range of CLV Gaussian subordination: e^{−p√y}/√y = ∫_0^∞ e^{−sy} (πs)^{−1/2} e^{−p²/4s} ds is completely monotone in y = m². **It is NOT a positive mixture of periodised exponentials for p > 0** (e^{−p√y}/√y fails the Stieltjes sign condition: the imaginary part on y = −u+i0 is −cos(p√u)/√u, which changes sign). For p = 0, 1/√y is Stieltjes, which is why CV III/CL (exponential subordination) cover p = 0 only.
2. **Relation of h_p to the Hermite interpolant at all n-th roots.** Let H_p be the even cosine polynomial of degree ≤ n−1 that interpolates value and derivative of g_p at all n-th roots of unity including θ = 0 (n conditions, n coefficients). Then h_p = H_p − κ_p · Fejér_n with κ_p chosen to cancel cos((n−1)θ), because Fejér_n vanishes doubly at the nontrivial nodes (uniqueness of the degree n−2 interpolant). In the scaling limit H_p becomes the CLV majorant M_λ-type function (nodes Z incl. 0), and the k_m formula's "−(n−m) sinh w" term is the −κ·Fejér correction (limit: k(t,v) = (sinh((1−t)v) − (1−t)v)/(cosh v − 1)). So h_p is **not** the Lebesgue-L¹-extremal minorant (that interpolates on Z+½-type nodes for Lebesgue measure, by Thm 27 with ϑ = dθ); it is a one-sided approximant interpolating at Z∖{0}.
3. **Possible reading as an L¹(ϑ)-extremal minorant [hypothesis, not checked].** For dϑ = (1−cos θ) dθ/2π (a probability measure) the n-point rule (1/n)Σ_{k≠0}(1−cos θ_k) ℓ(θ_k) is exact on Λ_{n−2}, because (1−cos θ)ℓ has degree ≤ n−1 and the term k = 0 vanishes. So the nontrivial n-th roots are a Gauss-type node set for ϑ, and Theorem 27 with 𝒜 = this set would say: h_p (p = 0, where Thm 29 applies) maximises ∫ℓ(1−cos θ) dθ/2π = ℓ_0 − ℓ_1 among degree-(n−2) minorants. I did not verify that this node set is the zero set of A_{n−1} for this ϑ (it should be a paraorthogonal-polynomial zero set; plausible but unchecked). If true: a clean extremal characterisation of the Cohn–Kumar p = 0 certificate, but it does not by itself touch the two-parameter inequality.
4. **No result found about coefficients of extremals at two parameters.** No statement of the type Γ_m((p+q)/2) ≥ √(Γ_m(p)Γ_m(q)) or any PSD/log-concavity property in the parameter, for Gaussian- or exponential-subordination extremals. Assessment: the CLV/CL machinery gives (a) existence/uniqueness, (b) explicit transforms via θ-functions (Thm 4), (c) linearity in the mixing measure. Explicit transform L̂/M̂ in Thm 4 could replace the k_m(w) formulas for a Gaussian-mixture proof of positivity of coefficients, but they give no handle on the geometric-mean inequality. **Applies as background; unlikely to close the gap.**

### 1.5 Other items
- Littmann, "Quadrature and extremal bandlimited functions", SIAM J. Math. Anal. (2012?) [SNIPPET; PDF at https://www.ndsu.edu/pubweb/~littmann/research/quadrature2012.pdf]; "L¹-approximation to Laplace transforms of signed measures" (https://www.ndsu.edu/pubweb/~littmann/research/JAT-FL-v3.pdf) [SNIPPET]: Gauss-type quadrature with nodes at zeros of Laguerre–Pólya (de Branges) functions; signed measures. Relevant only if one wants the interpolation nodes to be a general Laguerre–Pólya zero set.
- Carneiro–Littmann, "Extremal functions in de Branges and Euclidean spaces II", arXiv:1508.02436 [SNIPPET]: Gaussian subordination in de Branges spaces.
- Holt–Vaaler (Duke 83 (1996)) [MEMORY]: signum function in homogeneous de Branges spaces; Carneiro–Chandee–Littmann–Milinovich, arXiv:1406.5462 (Crelle 725 (2017)) [SNIPPET]: uses log(4+x²)-type extremal majorants/minorants inside RKHS arguments. Not periodic.

---

## 2. Positivity of cosine polynomials beyond convex coefficients

Searched: Koumandos–Ruscheweyh, Alzer–Koumandos, "convex minus geometric", "Pólya criterion on Z_n", "positive definite functions on finite cyclic group convex".
- Koumandos–Ruscheweyh, "Positive Gegenbauer polynomial sums and applications to starlike functions", Constr. Approx. 23 (2006) [SNIPPET]; Koumandos–Lamprecht (ρ = 1/4 case of the trigonometric-sum conjecture); Ma, "A proof of the Koumandos–Ruscheweyh conjecture", arXiv:2610.02285 [SNIPPET, preprint]. These concern sums Σ k^{−β}-type or Gegenbauer coefficients with monotone decay. **Not applicable** (same verdict as Vietoris/Belov in literature-2: monotone-coefficient theory, fails on Fejér-type truncated kernels).
- **Pólya on Z_n:** I found no statement of a Pólya-type criterion for finite cyclic groups, beyond the identity (1−cos θ)D(θ) = Σ e_j(1−cos jθ) already derived in literature-2 §1.0 (which is the discrete Pólya criterion). arXiv:1110.2437 (Beatson–zu Castell, Pólya criterion for spheres) and Gneiting arXiv:1111.7077 were already covered. arXiv:2503.06908 (positive definite functions on finite abelian groups; lower bound on second-largest value) [SNIPPET] has no convexity criterion.
- "Convex minus geometric": nothing found (as in literature-2 §1.6).
- Assessment: **nothing applicable.** The exact tools (Fejér–Riesz/Toeplitz SDP, Sturm) from literature-2 remain the only usable ones.

---

## 3. The matrix inequality in other guises

### 3.1 FOUND: Ounaïes, "A proof of Alexander's conjecture on an inequality of Cassels", arXiv:2601.10411 (v2, 22 Jan 2026) [READ in full; conjugates confirmed against the arXiv HTML version, the PDF text extraction drops the bars]

**Statements** (conjugates restored):
- Classical Schur inequality (Schur 1918, Math. Z. 1, 377–402): z_1..z_n in the closed unit disc ⇒ ∏_{j≠k} |1 − z̄_j z_k| ≤ n^n, equality iff the z_j are the vertices of a regular n-gon on the circle.
- Cassels (1966) proved the ρ>1 analogue under a restriction on ρ, Alexander (Amer. Math. Monthly 79 (1972) 883–884) conjectured it without restriction.
- **Theorem 2 (Alexander's conjecture).** ρ > 1, |z_j| ≤ ρ ⇒ ∏_{j≠k} |1 − z̄_j z_k| ≤ (ρ^{2n} − 1)^n (ρ² − 1)^{−n}, equality iff z_j are the vertices of a regular n-gon on |z| = ρ.
- **Theorem 3 (the useful one).** z_1..z_n ∈ D (open unit disc), Λ = (−1)^n ∏ z_j. Then
  Σ_{j,k} 1/(1 − z̄_j z_k) ≥ n²/(1 − |Λ|²),
  equality iff the z_j are the n roots of zⁿ + Λ. Corollary 4: for |ω_j| = 1, a ∈ (0,1): Σ_{j,k} 1/(1 − a ω̄_j ω_k) ≥ n²/(1 − aⁿ), equality iff regular n-gon.
- **Proof of Theorem 3 (a certificate in Hardy space).** f(z) = Σ_j 1/(1−z̄_j z) = Σ_j k_{z_j}(z) (Szegő kernels), B(z) = ∏ (z−z_j)/(1−z̄_j z) the finite Blaschke product. Then (a) ‖f‖²_{H²} = Σ_{j,k} 1/(1−z̄_j z_k); (b) with g = 1 − ΛB (conjugation convention as in their (14)–(16); the PDF text lost the bars), ⟨f,g⟩ = n because B(z_j) = 0 and f(0) = n; (c) ‖g‖² = 1 − |Λ|² since |B| = 1 on the circle and B(0) = Λ; Cauchy–Schwarz gives n² ≤ (1−|Λ|²)Σ. Equality iff f = c g, which forces e_m(z) = 0 for 1 ≤ m ≤ n−1 (their (18)–(19)).
  In matrix language: with K = (1/(1−z̄_jz_k)), 1ᵀK1 ≥ n²/(1ᵀK⁻¹1) and 1ᵀK⁻¹1 = min{‖g‖² : g(z_j) = 1} ≤ ‖1−Λ̄B‖² = 1 − |Λ|².
- **Proof of Theorem 2 (monotonicity).** Maximum modulus in each z_k (the off-diagonal product is ∏_{j<k}|1−z̄_jz_k|², holomorphic in z_k) reduces to |z_j| = ρ; then with z_j = ρω_j and g_ω(a) = n log(1−aⁿ) − Σ_{j,k} log|a − ω̄_jω_k|, a·g_ω'(a) = Σ_{j,k} 1/(1−aω̄_jω_k) − n²/(1−aⁿ) ≥ 0 exactly by Corollary 4, g_ω(0) = 0, so g_ω(ρ^{−2}) ≥ 0.
- Also cited: Dubickas, "Maximal values of symmetric functions in distances between points", Math. Inequal. Appl. 23 (2020) 329–339 [SNIPPET]: for z_j = ρω_j, ∏_{j≠k}|1−z̄_jz_k| = ρ^{n(n−1)} ∏_{j<k}((ρ−ρ^{−1})² + |ω_j−ω_k|²); conjectures that all elementary symmetric functions of {|ω_j−ω_k|²} are maximised by the regular n-gon (proved for degrees 1–4); this would imply Alexander's conjecture.

**How it relates to our inequality.**
1. **Our equal-diagonal rank-one case is exactly Theorem 2/Corollary 4 with ρ<1 in place of ρ>1**, up to the diagonal factor (1−ρ²)^n. (Theorem 2 as stated is for ρ>1. For radius r<1 put a = r² and G(a) = Σ_{j,k} log|1−aω_jω̄_k| − n log(1−aⁿ): a·G'(a) = n²/(1−aⁿ) − Σ_{j,k} 1/(1−aω_jω̄_k) ≤ 0 by Corollary 4 and G(0) = 0, so G ≤ 0. [OWN, one line from their argument.]) For correlation matrices (ρ→1) our inequality becomes ∏_{i≠j}|1 − a_ij| ≤ n^n, the PSD (any rank) extension of Schur's bound. Whether Schur's n^n bound for PSD matrices of rank > 1 appears in the literature, I did not find. [The team's Lean proof covers constant diagonal, all ranks.]
2. **Multi-radius structure.** Theorem 3 is an inequality with **unequal moduli** r_j = |z_j| and an exact equality case. The kernel is rank one in the radius variable at each frequency m: (r_j r_k)^m cos(m(θ_j−θ_k)), the same geometric-mean structure as √(Γ_m(p)Γ_m(q)), with weights 1 instead of 1/m. This is the cleanest "pair inequality across radii with rank-one coefficients" I found in angle 4 as well, and the certificate is Cauchy–Schwarz with an inner function rather than LP/Hermite interpolation.
3. **But it does not imply our inequality for unequal diagonals.** Scaling A ↦ tA and integrating, ∫_0^1 (S(tA)−n²)/t dt = Σ_m (1/m) 1ᵀA^{∘m}1 =: L(A), where S(A) = Σ 1/(1−a_ij). Theorem 3 (if extended to PSD A with |Λ|² replaced by P = ∏ a_ii) gives L(A) ≥ −n log(1−P). Our target is L(A) ≥ −Σ_i log(1−a_ii^n). By convexity of s ↦ −log(1−e^s), −Σ log(1−x_i) ≥ −n log(1−(∏x_i)^{1/n}) with equality iff all x_i are equal, so Theorem 3 is weaker than needed, with equality only for constant diagonal. **Same verdict for the pointwise-in-t derivative form:** D: S(A) ≥ n² + nΣ_i a_ii^n/(1−a_ii^n) FAILS numerically for rank-one A with unequal moduli (145 failures in 300 000 random trials, n = 2..4; worst ratio 0.9994, e.g. n=4, diag ≈ (.76,.92,.98,.55)), although the original inequality holds at those A (log LHS −4.619 ≤ log RHS −4.292). [OWN numerics.] So a uniform-dilation monotonicity argument cannot work for unequal diagonals; one needs a different path or the integrated form.
4. **Numerical observation [OWN]:** the PSD (any rank, complex) extension of Theorem 3, S(A) = Σ_{ij} 1/(1−a_ij) ≥ n²/(1 − ∏_i a_ii), held in 200 000 random trials (n = 2..5, rank 1..n) and in BFGS minimisation for n ≤ 6 and ranks 1, 2, n (infimum of S(1−P)/n² = 1, approached only in the trivial limit a_ii → 0). No proof known to me; the Hardy-space proof is specific to rank one (needs the Blaschke product). A proof in the Drury–Arveson space for A = Gram(v_i) would require a function g with g(v_i)=1 and ‖g‖² ≤ 1 − ∏‖v_i‖², which I could not produce. If true, it is a natural intermediate statement.
5. **Possible use:** (a) a short independent proof of the constant-diagonal rank-one case; (b) as a template for a *weighted* certificate: Cauchy–Schwarz with a test function g satisfying g(z_j) = c_j (weights depending on r_j) in place of c_j ≡ 1, aimed at the unequal-radius case; (c) the equality structure (roots of zⁿ+Λ, i.e. regular n-gon, and unequal moduli excluded) matches our conjectured equality case.

### 3.2 Other guises searched
- **Lin–Zhang (via Marcus/Hua) [SNIPPET]:** for any n×n A with the same singular values as a contraction, ∏(1−r_k) ≤ |det(I−A)| ≤ ∏(1+r_k) (majorization + Weyl). This is the engine behind the rank-one case via Weyl's majorant theorem (as you noted); no extension to ∏_{ij}.
- **Hadamard powers:** Johnston–Sababheh, arXiv:2610.12063 (Oct 2026) [READ abstract/intro]: superadditivity (X+Y)^{⊙p} ⪰ X^{⊙p}+Y^{⊙p} for PSD entrywise-nonnegative X,Y when p ∈ N or p > size−2 (Fitzgerald–Horn / Guillot–Khare–Rajaratnam), used to prove ‖v^p‖‖w^p‖ − ⟨v^p,w^p⟩ ≤ ‖v‖^p‖w‖^p − ⟨v,w⟩^p. Different object; **not applicable**.
- Vybíral, M∘M ≥ (1/n) d dᵀ for correlation matrices; Khare, arXiv:1910.03537 (sharpness) [SNIPPET]: lower bounds for Hadamard squares, no log kernel; **not applicable**.
- **Projective/complex-sphere log energy:** Etayo–Arce (S³), Åhag–Czyż projective logarithmic potentials arXiv:1908.00933, Anderson–Dostert (Riesz/Green energy on projective spaces) arXiv:2204.04015, Dragnev–Musin note that simplex and cross-polytope are the only known log-energy minimisers for all d [all SNIPPET]. None treats −log|1−⟨x,y⟩|. **Nothing found.**
- **Polynomial-with-zeros-in-the-disc guise:** Mahler measure/discriminant searches returned only Schur/Cassels (above), Mordell's discriminant inequality (different) [SNIPPET]. The Szegő-strong-limit and model-space guises returned nothing specific.
- **Cauchy-determinant guise:** Yamada, "Oppenheim–Schur's inequality and RKHS", arXiv:2402.16228 [READ abstract, Lemma 5.1]: RKHS proof of Oppenheim–Schur with the identity det A = reciprocal of min norms; Lemma 5.1 compares ∏(a_ij) − ∏(a_ij − 1) for a_ij ≥ 1. Same Hilbert-space technique as Ounaïes (minimal norm interpolation), different inequality. **Technique background only.**
- **Chinese sources / MO / MSE:** queries in Chinese and English for "半正定", "∏|1-a_ij|", "∏|1-a_ii^n|", MO/MSE phrasing returned only Hadamard/Oppenheim material; no thread found. (Search index is US-only; Tieba/Zhihu are effectively not reached.)

---

## 4. Multi-radius LP / weighted designs / "Delsarte on the disc"

Searched again with: BDHSS universal lower bounds, Levenshtein framework, concentric circles / two radii / rotated polygons for log energy, Euclidean designs.
- Boyvalenkov–Dragnev–Hardin–Saff–Stoyanova, "Universal upper and lower bounds on energy of spherical designs", arXiv:1509.07837; "Universal lower bounds for potential energy of spherical codes", Constr. Approx. 44 (2016) 385–415 (https://link.springer.com/10.1007/s00365-016-9327-5); "Next levels universal bounds for spherical codes" arXiv:1906.03062; "Energy bounds for codes in polynomial metric spaces", arXiv:1804.07462 [all SNIPPET; identification of the arXiv numbers from the search list]; Borodachov et al. arXiv:2403.07457 and arXiv:2211.00092 (sharp codes attain ULB) [SNIPPET beyond the already-read statement]. All are single-sphere LP bounds (Levenshtein polynomials, quadrature), or weighted but with ℓ-independent weights. **No pair inequality with geometric-mean coefficients across radii.**
- Bannai et al., "On Euclidean t-designs", arXiv:1512.02981; Kyoto tight Euclidean 5-designs note [SNIPPET]: classification/construction on concentric spheres; **not energy inequalities**.
- Miezaki–Tagami (round 1) remains the only multi-shell energy statement; its positive-definiteness condition is on the matrix-valued kernel in (r,s), and the product (rank-one) choice is the natural one. **No one has applied it to log kernels.**
- Assessment: **nothing new applies.** The one multi-radius certificate in the literature that I found with rank-one structure is Ounaïes' Theorem 3 (§3.1), for the Hardy kernel rather than the log kernel.

---

## Most promising leads

1. **Ounaïes, arXiv:2601.10411, Theorem 3** (Σ1/(1−z̄_jz_k) ≥ n²/(1−|Λ|²), equality at roots of zⁿ+Λ) with its Cauchy–Schwarz/Blaschke certificate: unequal moduli, exact equality case, rank-one-in-radius structure. Derived consequences: reproves the equal-diagonal case; weaker than needed for unequal diagonals (convexity gap); the derivative form D fails numerically, so any proof must use a non-uniform path or a weighted test function g(z_j)=c_j.
2. **PSD extension of Theorem 3** (S(A) ≥ n²/(1−∏a_ii)) numerically true; a Drury–Arveson/Gram proof would be a clean new lemma, even though it is not sufficient by itself.
3. **CLV Theorem 4 formulas** (explicit θ-function transforms of Hermite interpolants at Z or Z+½) and **h_p = H_p − κ·Fejér_n** (§1.4): can supply a Gaussian-mixture proof of d_m ≥ 0 and a cleaner scaling-limit statement.
4. **Carneiro–Littmann Thm 27/29** for general measures ϑ: possible extremal characterisation of h_0 with dϑ = (1−cos θ)dθ/2π (unchecked).
5. Negative: no literature on parameter-dependence of extremals, geometric means of coefficients, Pólya on Z_n, convex-minus-geometric, projective log-energy, Chinese/MO threads.
