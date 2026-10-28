# Erdős Problem 835: the case where k + 1 is composite (Lean 4)

Formal proofs, against [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
commit `5a2fb85045c86e4a184b15ce7531ba199a3c4580`, of these statements in
`FormalConjectures/ErdosProblems/835.lean`:

| Repository statement | Proof in `Erdos835Proof.lean` |
|---|---|
| `Erdos835.johnson_chromaticNumber_composite` | `Erdos835Proof.johnson_chromaticNumber_composite` |
| `Erdos835.property_iff_chromaticNumber` | `Erdos835Proof.property_iff_chromaticNumber` |
| `Erdos835.johnson_chromaticNumber_odd` | `Erdos835Proof.johnson_chromaticNumber_odd` |
| `Erdos835.johnsonGraph_18_9_chromaticNumber` | `Erdos835Proof.johnsonGraph_18_9_chromaticNumber` |

The file ends with `example : type_of% Erdos835.X := Erdos835Proof.X` for each row, so the
types are checked to be exactly the repository statements.

The theorem is due to Ma and Tang
([MT25](https://github.com/QuanyuTang/erdos-problem-835/blob/main/On_Problem_835.pdf)).
This is a formalization; it claims no new mathematics. The case where k + 1 is prime, and so
Erdős Problem 835 itself, remains open.

The proof was written with AI assistance (Claude, Anthropic) and checked by the Lean kernel.

## Check it

```sh
lake exe cache get
lake --wfail build
lake env lean CheckAxioms.lean   # every theorem: [propext, Classical.choice, Quot.sound]
```

Lean `v4.33.1`, Mathlib as pinned by formal-conjectures at the commit above.
