# Odd Perfect Numbers — ω(N) = 2 Base Case of Steuerwald

[![Lean CI](https://github.com/BenFrohman/opn-omega2-base-case-lean/actions/workflows/lean-ci.yml/badge.svg)](https://github.com/BenFrohman/opn-omega2-base-case-lean/actions/workflows/lean-ci.yml)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
[![ORCID](https://img.shields.io/badge/ORCID-0009--0006--7068--3718-brightgreen.svg)](https://orcid.org/0009-0006-7068-3718)

Lean 4 + Mathlib formalization of the elementary base case: there is no odd perfect number of the form \(p^2 q\) with distinct odd primes \(p, q\).

**Author**: Benjamin Stanley Frohman  
**ORCID**: [0009-0006-7068-3718](https://orcid.org/0009-0006-7068-3718)  
**License**: Apache-2.0  
**Copyright**: (c) 2026 Benjamin Stanley Frohman

## Claim
**Machine-checked formalization of the ω(N)=2 base case of Steuerwald’s theorem; existence of an odd perfect number remains open.**

## What is formalized
- Abundancy-index bound showing \(I(p^2 q) \le 26/15 < 2\)
- 2-adic valuation case analysis ruling out the two candidate forms for \(q\)

## Reproduce
```bash
lake exe cache get
lake update
lake build
```

## Status
See [docs/STATUS.md](docs/STATUS.md).

## License
Apache License 2.0. Copyright (c) 2026 Benjamin Stanley Frohman.
See [LICENSE](LICENSE).
