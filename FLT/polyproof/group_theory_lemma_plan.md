Plan for formalizing `group_theory_lemma` (Torsion.lean)

Goal
----
Prove: if for every d | n, |torsionBy ℤ A d| = d^r, then torsionBy ℤ A n ≃+ (ZMod n)^r.

Sketch
------
1. Reduce to primary decomposition: use `equiv_directSum_of_isTorsion` to write torsion as ⨁_p (⊕_{i=1..m_p} ℤ/(p^{a_{p,i}})).
2. For each prime p | n, compare |A[p]| = p^r with `Module.natCard_eq_pow_finrank` to deduce the number of p-primary summands equals r.
3. Use the hypothesis for higher prime-powers to force each a_{p,i} = v_p(n).
4. Reassemble via CRT to get (Z/nZ)^r.

Mathlib lemmas referenced (search and import as needed)
- `equiv_directSum_of_isTorsion`
- `Module.natCard_eq_pow_finrank`
- `Submodule.torsionBy_isInternal` / CRT decomposition helpers
- `Int.quotientSpanNatEquivZMod` / CRT equivalences

Next steps
----------
- Implement prime-power lemma: if for all k, |torsionBy p^k| = p^{k r}, then the p-primary decomposition has r summands each of exponent v_p(n).
- Formalize step-by-step in FLT/FLT/EllipticCurve/Torsion.lean (near `group_theory_lemma`).

I will start by adding this plan and pushing a branch; next I can add a draft Lean file with the prime-case lemma.
