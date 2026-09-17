# Consecutive powerful nonsquares

Development toward a Lean formalization for JSP-000301 / Erdős problem 365.
Verification is pending until the complete build and axiom audit pass.

The intended contribution is a construction parameterized by **any** pair of
consecutive positive powerful nonsquares. From a seed `n`, the Pell orbit starts
at `(x,y)=(1,1)` and sends

```
x ↦ (2n+1)x + 2(n+1)y
y ↦ 2nx + (2n+1)y
```

It preserves `n*x² + 1 = (n+1)*y²`. Both resulting integers are powerful
and remain nonsquares. The sequence `a(k)=n*x(k)²` strictly increases and obeys
`a(k+1) ≤ (4n+3)²*a(k)` and `a(k) ≤ n*((4n+3)²)^k`.
In particular every `B ≥ n` has a new pair starting in
`(B, (4n+3)²*B]`. The explicit Golomb seed gives constant `2368866241`.

This formalizes classical mathematics, not a new discovery. Golomb's seed and
Walker's infinitude result retain their original credit. Prior submissions for
this problem include many finite certificates and PR #412's infinite family.
This package focuses on the general seed theorem and its quantitative bounds;
it does not claim first formalization, the unresolved polylogarithmic counting
upper bound, or prize eligibility. AI assistance was used in development.

Sources:

- https://www.erdosproblems.com/365
- https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0301-0400.md#JSP-000301
- https://doi.org/10.1080/00150517.1976.12430562
- https://github.com/TheJustinSunPrize/awards/pull/412

Reproduction (Lean 4.33.1; exact Mathlib revision in `lakefile.toml`):

```sh
lake update
lake exe cache get
lake build
lake env lean Audit.lean
```
