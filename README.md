# Spectra of Graphs: Lean 4 Formalization
Formalizing Brouwer & Haemer's *Spectra of Graphs* in Lean 4 Mathlib. Begining with the core chapters on spectral graph theory (found in Ch. 1-4), and hopefully formalizing the special topics chapters (Ch. 4-15)

**STATUS: WIP** - Finished core pre-requisite definitions (Basic.lean) and working on theorems from Chapter 1. Not production ready yet.

##Progress
- [X] Prerequisite linear algebra
- [ ] Chapter 1: Graph Spectrum
- [ ] Chapter 2: Linear Algebra
- [ ] Chapter 3: Eigenvalues and Eigenvectors of Graphs
- [ ] Chapter 4: The Second-Largest Eigenvalue

##Building
Requires Lean 4.32.1, Mathlib v4.32.1.
```bash
lake build
```
##Why this project
I do not have a strong background in formal methods, but do have a strong background in graph theory. My goal with this project is to (1) become proficient in Lean 4 and formalization techniques, (2) become more familiar with formal methods, and (3) identify the gaps between the written language in proofs and the formalization in Lean. I believe that the future of mathmaticians will be in developing methods of auditing machine-generated proofs, and I intend to learn how to do that effectively.
