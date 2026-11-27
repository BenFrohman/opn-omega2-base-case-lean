# Odd Perfect Numbers: ω(N) = 2 Base Case

[![Lean CI](https://github.com/BenFrohman/opn-omega2-base-case-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/BenFrohman/opn-omega2-base-case-lean/actions/workflows/lean.yml)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
[![ORCID](https://img.shields.io/badge/ORCID-0009--0006--7068--3718-brightgreen.svg)](https://orcid.org/0009-0006-7068-3718)

**Status:** Machine-checked formalization of the elementary base case of Steuerwald’s theorem: there is no odd perfect number of the form \(p^2 q\) for distinct odd primes \(p, q\). The proof is sorry-free. Existence of an odd perfect number remains open.

**Author:** Benjamin Stanley Frohman ([ORCID: 0009-0006-7068-3718](https://orcid.org/0009-0006-7068-3718))

Copyright (c) 2026 Benjamin Stanley Frohman. Apache-2.0.

## Claim delimitation

This repository formalizes that \(\sigma(p^2 q) \ne 2 p^2 q\) for distinct odd primes \(p, q\). It is the simplest case of Euler form with a single ordinary prime of exponent 2. It does **not** resolve the existence of an odd perfect number.

## Steuerwald clarification

Steuerwald's 1937 theorem is not an induction building from the \(\omega = 2\) case. It assumes \(N = p^\alpha q_1^2 \cdots q_k^2\) for any \(k \ge 1\) and derives a direct contradiction from the 3-adic valuation: each \(\Phi_3(q_i) = 1 + q_i + q_i^2\) contributes a factor of 3 to \(\sigma(N)\), while the special prime power contributes none.

## Reproduce

```bash
git clone https://github.com/BenFrohman/opn-omega2-base-case-lean.git
cd opn-omega2-base-case-lean
lake exe cache get
lake build
```

Axioms are the standard three: `propext`, `Classical.choice`, `Quot.sound`.

Existence of an odd perfect number remains open.
