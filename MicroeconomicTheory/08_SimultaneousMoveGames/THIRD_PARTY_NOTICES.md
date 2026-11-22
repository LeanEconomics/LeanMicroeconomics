# Third-party notices

Original code and documentation are released under Apache 2.0; see `LICENSE`.
Lean, Mathlib and their dependencies retain their upstream licenses.

The verifier and its tests are copied from LeanEconomics/DynamicProgramming,
commit `d39805f553dfb9619271b32bbf858d3162ca7e4e`,
`RecursiveMethods/DeterministicDP/scripts/`, under Apache 2.0. Copyright and
attribution belong to their original contributors. The Lake configuration, dependency
pins and CI conventions follow the same repository.

This project depends, through Lake requirements and without copying, on MWG Chapter 7
(`MWGNoncooperativeGames`, path `../07_NoncooperativeGames`), MWG Chapter 3
(`MWGClassicalDemand`, path `../03_ClassicalDemand`), MWG Chapter 5 (`MWGProduction`, path
`../05_Production`; Farkas' lemma and Stiemke's alternative) and LeanEconomics
(`https://github.com/LeanEconomics/LeanEconomics`, pinned to `04decca`; Brouwer's and
Kakutani's fixed-point theorems), each under its own license.

Andreu Mas-Colell, Michael D. Whinston and Jerry R. Green, *Microeconomic Theory*, Oxford
University Press, 1995, ISBN 978-0-19-507340-9, is cited by printed page and result. Its text
and figures are not distributed. The local scan is excluded from version control.

Original formalization is developed with Claude Code under the user's direction;
mathematical coverage and verification status are recorded separately.
