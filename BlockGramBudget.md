# Block Gram budgets for discounted squared residuals

Let a step have a gain (g) and an injection (p(v-z^	op c)^2), where the
feature vector (z) and target (v) are observed during the step and the
decoder (c) may be selected later. For a list of steps, the reference budget
starts at zero and applies these affine updates in order.

## Contract

`FastGramBudget.merge_blocks` gives the exact affine map of a block.
Its gain is the product of the step gains. For each input position the
injection is carried by just the gains strictly after that position, as in
`suffix_weight`. Nonnegative gains and squared residuals permit separate
upper bounds on these coefficients.

For any finite sets of writes and feature coordinates,
`FastGramBudget.readerEnergy` defines the direct sum of weighted squared
residuals. `weighted_gram` identifies the sufficient statistics as the
feature Gram, target/feature cross moment and target square sum. The
identity applies to all decoders, including a decoder chosen after the
statistics were accumulated. The empty index sets and zero gains are
allowed. The least-squares optimization problem does not occur in the
contract.

## Roundoff contract

`path_roundoff` bounds the algebraic deviation along a path of
multiplicative perturbations. `signed_roundoff` bounds cancellation by
the sum of absolute monomial masses. `absolute_row_mass` lets a shared
row envelope bound that mass. `certified_reader` adds the residual,
stored-state and final evaluation allowances.

Dropping the absolute allowance is unsound for a binary floating-point
evaluation. In binary64 the expression (v^2-2v+1) can round to zero
for (v=1+2^{-27}), although the exact residual squared is (2^{-54}).
The formal contracts concern real algebra. A concrete kernel still has
to justify the perturbation bounds for its operations and any additive
underflow allowance.

## Verification

```sh
lake exe cache get
lake --wfail build
scripts/audit.sh
```

The audit lists the kernel dependencies of each theorem with
`#print axioms`. The toolchain and Mathlib revision are pinned by
`lean-toolchain` and `lakefile.toml`.
