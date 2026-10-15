# Lean proof requirements — revised Task--06 decision

**Mandatory new Lean proofs for the present qualified 25 mathematical results:** no missing declaration is demonstrated by the two reviews. This is a scope-limited audit finding, not a proof of completeness of every potential formalization.

Task--06 already contains the bilinear and projection lemmas previously suggested, including `dot_bilinear_symmetric`, `projL_idem`, `projS_idem`, projection image/kernel equivalences and `dot_split`. These are not open tasks. See `LEAN_PROOF_DECISION.md` for the exact optional theorem candidates and their intended hypotheses and proof strategies.

**Optional, contingent on claiming a new formal unary theorem:**

1. `TriplePath.unary_numer_ne_neg_denom`: every admissible unary triple has numerator different from minus the embedded positive denominator, i.e. value `-1` is impossible. The present manuscript uses this only as a clearly identified informal deduction.
2. An exact-image theorem for the unary triple representation into `FracQ`: representability iff the fraction differs from `0` and `-1`. This requires full constructive witness construction for negative integer numerators and should not be stated as kernel-proved before compilation and axiom audit.
3. A separately named general finite-arity comparison `b≤c`, or a stand-alone ordered-arity isomorphism, only if the paper is upgraded to claim a distinct theorem instead of the existing iterations/transfer lemmas.

**Not mandatory for this paper:** unconditional Cauchy completeness, MP/LPO/WLPO, unrestricted suprema, alternative omega limits, and hypothetical geometric interpretations. The existing claims are qualified precisely to avoid assuming these.

**Source:** `7e12641454b9d2e387eee0c034d02f834836829c2e7d2926da5e8f63554b0b7e` (Lean 4.28.0). If any optional theorem is added, recompute the fingerprint and rerun release verification before modifying the paper's formal-proof status.

## Decision following the second ChatGPT and Claude reviews

Both reviewed the long-form text in the scope of its existing principal theorems. Their M1–M6/B1–B6 findings concern exposition, representative bounds, quantifiers and delivery metadata rather than a demonstrated missing Lean proof. **No new Lean proof is required to sustain the 25 main results as qualified.** The informal unary `-1` exclusion is not promoted to a formally checked theorem; a kernel-verified exact-image characterization would be a separately specified future extension. See `SECOND_REVIEW_RESOLUTION.md`.
