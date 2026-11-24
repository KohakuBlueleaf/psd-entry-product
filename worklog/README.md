# Work log

Everything here is the record of how the proof was found. None of it is needed to read or check the final
proof (`docs/PROOF.md`, `MatrixIneq/`). The notes were written while working, mostly in Traditional Chinese,
and are kept as they were; statements in them about what is "open" or "the main target" describe the state
at the time of writing.

| Path | Contents |
| --- | --- |
| `docs/THEORY.md` | Running map of theorems, reductions and written reasoning, round by round. |
| `docs/REPORT.md` | Status report written just before the final proof was found. |
| `docs/EXPLORATION.md` | Initial exploration plan and list of experiments. |
| `notes/` | One file per route. `tau-kernel-proof.md` is the first draft of the final proof; `qc-route.md` is the last route before it. |
| `experiments/` | Small numerical experiments `e<k>_<topic>.py` (mpmath/numpy). They were used only to test conjectures, never as part of a proof. |

## Routes, in order, and what each one gave

1. **Determinant route (rank one).** `∏|1 - z_i z̄_j|` is a ratio of Gram determinants, and the rank-one case
   follows from Weyl's majorant theorem. The noncommutative analogue for higher rank fails.
2. **Small cases.** `n ≤ 3` by an elementary argument (Lean: `Exploration/Three.lean`), using Oppenheim's
   inequality (`Exploration/Oppenheim.lean`).
3. **Certificate method.** Lower bounds for `-log|1 - a_ij|` by harmonic polynomials with positive
   semidefinite coefficient kernels, plus the Schur product theorem. With the interpolation ("Fejér")
   certificate this proves the case of constant diagonal for every `n`
   (Lean: `Exploration/EqualDiag.lean`), including `∏_{i≠j}|1 - a_ij| ≤ n^n` for correlation matrices.
4. **Geometric-mean kernel.** Taking `√(Γ_m(p)Γ_m(q))` off the diagonal reduces the theorem to one
   two-parameter inequality, `Star n` (Lean: `Exploration/Star.lean`). It is numerically true for
   `n ≤ 40` but we did not prove it. Reductions found on the way, all formalized:
   - `HIn n → Star n`: the gap is monotone in the smaller parameter (`Exploration/HIn.lean`);
   - `QC n → HIn n`: after multiplying by `cosh α - cos θ` the statement becomes convexity of an explicit
     sequence, with no angle variable (`Exploration/QC.lean`). `QC n` is numerically true for `n ≤ 80`.
   The classical convexity criterion works for these statements exactly up to `n = 15`.
5. **Probabilistic structure and the final kernel.** `χ_m = e^{mw}k_m` is a distribution function. Writing
   `Γ_m(p) = E e^{-m·max(p,τ)}/m` suggested the kernel `E e^{-m(max(p,τ)+max(q,τ))/2}/m`, which is positive
   semidefinite by construction and for which the pair inequality follows from the equal-diagonal case by
   Poisson smoothing. This is the proof in `docs/PROOF.md`.

Ruled out along the way (details in `notes/` and `docs/THEORY.md`): reduction to rank one by a
plurisubharmonic hull argument; harmonic representability for `n ≥ 4`; pairwise Cauchy–Schwarz for `n ≥ 4`;
min-type kernels with the wrong constant term; geometric means taken in the Fejér-mixture representation;
an instantaneous version of the arithmetic-mean kernel; a Lorentzian (one positive eigenvalue) structure
of the gap kernel; interval-arithmetic verification for fixed `n` (abandoned as not a proof of the
general case).

Three literature searches (`notes/literature*.md`) found no source for the inequality. The closest
published result is Ounaïes, arXiv:2601.10411 (rank one, equal radii).
