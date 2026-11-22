# Third-party notices

Original code and documentation are released under Apache 2.0; see `LICENSE`.
Lean, Mathlib and their dependencies retain their upstream licenses.

The verifier and its tests are copied from LeanEconomics/DynamicProgramming,
commit `d39805f553dfb9619271b32bbf858d3162ca7e4e`,
`RecursiveMethods/DeterministicDP/scripts/`, under Apache 2.0. Copyright and
attribution belong to their original contributors. The Lake configuration, dependency
pins and CI conventions follow the same repository.

This project depends (Lake `path` requirement) on the MWG chapter project
`MWGGeneralEquilibriumExamples` (Chapter 15) of this repository and, through it, on MWG
Chapters 10, 5, 3 and 2, the Kreps chapter projects they require, and LeanEconomics
(pinned `04deccaf63`; this chapter imports its `DynamicProgramming` modules: the Bellman
operator, Blackwell's conditions and the principle of optimality). Their results are
imported, not copied; their notices apply to them.

Andreu Mas-Colell, Michael D. Whinston and Jerry R. Green, *Microeconomic Theory*, Oxford
University Press, 1995, ISBN 978-0-19-507340-9, is cited by printed page and result. Its text
and figures are not distributed. The local scan is excluded from version control.

Original formalization is developed with Claude Code under the user's direction;
mathematical coverage and verification status are recorded separately.
