# Sharp entropy superadditivity for rotating four-charge STU black holes

This repository proves the analytic inequality requested by Cvetič, Gibbons, Lü and Pope after equation (6.25) in their 2018 paper. The target is the outer-horizon entropy of the asymptotically flat, four-dimensional, ungauged STU family with four independent electric charges. Their equations (3.75) and (3.77) supply the physical mass, angular momentum, charges and entropy. [Original question and equations](https://arxiv.org/abs/1806.11134)

## Theorem

Take any two admissible states $X,Y$, measured in the same normalization. Add their ADM masses, signed axial angular momenta and four electric charges componentwise. The resulting state is admissible and obeys

$$
S_+(X+Y)\ge S_+(X)+S_+(Y)+8\pi m_Xm_Y .
$$

For a state with ADM mass $M$ and charges $Q_i$, the seed $m$ is the unique nonnegative solution of

$$
\sum_{i=1}^{4}\sqrt{m^2+16Q_i^2}=4M.
$$

The result allows arbitrary charge ratios and spin signs. It includes the continuous boundary of the entropy function. When either input has a positive seed, the state at the summed data can be realized in the original boost parameterization. The area version has coefficient $32\pi$ in units $G=c=\hbar=k_{\rm B}=1$. Any two positive-mass Schwarzschild inputs attain equality, so the coefficient $8\pi$ is optimal.

This comparison concerns stationary states at fixed total conserved quantities. A time-dependent merger can radiate energy and angular momentum. The four-electric-charge hypothesis is material. Section 6.4 of the source gives a dyonic Kaluza–Klein counterexample to unrestricted superadditivity. [Physical interpretation and scope](https://doi.org/10.1103/PhysRevD.98.106015)

## Proof

The sum of the two input energy vectors need not share a single Kerr seed across the four charge slots. At fixed total mass and fixed individual charges, the common-seed equilibrium maximizes each of the two quantities $L$ and $R$ entering $S_+=2\pi(L+\sqrt{R^2-J^2})$. Pairing slots in the pooled vector yields positive cross terms of at least $2m_Xm_Y$ in each of $L$ and $R$. Cauchy–Schwarz carries the second gain through the rotation term. This establishes the inequality throughout the family. [Five-page proof](paper/STU_Horizon_Entropy.pdf) · [LaTeX source](paper/STU_Horizon_Entropy.tex)

| Result | Lean declaration in `STUHorizons` |
| --- | --- |
| Unique physical seed | `exists_unique_seed` |
| Equilibrium maximizes both sectors | `sectors_maximize` |
| Lower bound for both cross terms | `pooled_gain` |
| Summed data are admissible | `merged_sectors` |
| Sharp entropy bound and ordinary superadditivity | `entropy_gap`, `four_charge_superadditivity` |
| Identity with equation (3.77) and inverse parameterization | `boost_formula`, `exists_boost_of_admissible` |
| The theorem on the published parameterization | `boost_superadditivity`, `realized_entropy_gap` |
| Area inequality | `horizon_area_gap` |
| Attainment and optimality of the coefficient | `schwarzschild_equality`, `optimal_gap_coefficient` |

## Verify in Lean

The project pins Lean 4.34.1 and mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`. With a Lean toolchain manager and Git installed, run the following from the repository root. The first setup retrieves dependencies. The commands also work in a PowerShell terminal.

```sh
lake exe cache get Mathlib.Tactic Mathlib.Analysis.SpecialFunctions.Arsinh Mathlib.Topology.Order.IntermediateValue
lake build
lake env lean Verify.lean
lake env leanchecker --verbose STUHorizons
```

The Lean source establishes the real-variable inequality from the published stationary entropy formula. It also derives that formula in the physical-data coordinates from the boost parameterization. The physical identification of the formula as horizon area divided by four comes from the cited gravitational solution. The axiom audit lists only standard Lean foundations. [Formal proof](STUHorizons.lean) · [Audit declarations](Verify.lean) · [Verification transcript](verification.txt)

## Sources and account antecedents

- Cvetič, Gibbons, Lü and Pope give the physical parameters and entropy in equations (3.75)–(3.80), and pose the four-charge analytic problem in §6.2. The earlier Cvetič–Youm paper constructs the rotating solution in a duality frame. [2018 paper](https://doi.org/10.1103/PhysRevD.98.106015) · [1996 paper](https://doi.org/10.1103/PhysRevD.54.2612)
- The account manuscript `Horizon_Heat_Counterexample.pdf` and its companion `HorizonHeat.lean` track which charges are held fixed when a mass parameter changes. `Scale_Perspective.pdf` (*Empty strips in rotated triangular lattices*) chooses a scale shared by every layer. In this proof the analogous common parameter is the unique $m$ for all four slots.
- The OpenAI Kerr–Newman–Penrose preprint specifies the conserved angular momentum including the electromagnetic contribution. This motivated stating the addition law on physical data before introducing the auxiliary seed. [OpenAI repository](https://github.com/openai/math/tree/main/preprints/The-Kerr-Newman-Penrose-Inequality-for-Axisymmetric-Electrovacuum-Exteriors-October-5-2026)
- Alpöge’s November 2026 RH/Dirichlet note tracks the cost of individual steps and uses Cauchy–Schwarz in its checklist. That suggested retaining the cross terms at each stage. The horizon proof is independent of the number-theory claims. [Author’s note, p. 4](https://alpo.ge/remark.pdf)
