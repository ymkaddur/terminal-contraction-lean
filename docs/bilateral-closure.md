# Bilateral dynamics with moving readers

Let a state be a matrix S and let its recorded value be SB. At the next step the state is FSG + U and the readers are C. The matrices may be rectangular. The write U is given. If GC = BM then the next value is F(SB)M + UC. Matrix associativity proves this over a semiring, with arbitrary reader widths at consecutive steps. Induction gives the time-dependent statement `moving_readout`.

For a candidate M over a ring, the exact discrepancy is FS(GC − BM). A factorization of the discrepancy into t independent directions costs up to t extra reader columns before taking the output projection. With an induced norm, its magnitude is at most the product of the norms of F, S and GC − BM. Those norms require independent bounds. An exact right factorization alone gives no floating-point roundoff certificate.

### Necessity and exceptional cases

Over a field, for arbitrary S, the sandwich FSD vanishes identically exactly when the left or right factor vanishes. A single-entry S tests any two nonzero entries of F and D. For a decoder of arbitrary form, take P to be the span of the old readers and Q to be the span of the pulled-back next readers. If Q contains a vector outside P, there is a linear functional vanishing on P but nonzero there. Multiplying that functional by a vector outside the kernel of F gives two indistinguishable old states with different outputs. Thus Q ⊆ P is necessary when F is nonzero. This includes singular nonzero F. Restricted admissible states require testing the differences within each actual observation fiber.

The rational examples include a right factor mapping the second reader line into the first, a hidden coordinate, and a zero left factor. Full column rank is needed for uniqueness of transfer coordinates. The evolution identity holds with redundant readers.

### The price of missing directions

Write d = dim((Q+P)/P) and r = rank(F). The extra reader space has minimum dimension d by quotient projection and lifting. Over a finite field of order q, the exact response alphabet on a fixed old-readout fiber has size q to the power rd. Choose bases of the extra directions and the output image. In these coordinates F has a right inverse J. The coordinate map L on the input kills B and satisfies LC = I on the new independent readers. For every r by d matrix T, the state JTL vanishes on B and realizes response T. An arbitrary encoder and decoder therefore need at least one message per T. Sending T attains the bound. For a nonzero old value, translate the witness family by any state in its fiber. In the original output coordinates reconstruct by the known left-image and reader-basis maps. Those maps and access to the original data have a cost.

`hit_response` and `residual_message_bound` prove the fixed-fiber argument for explicit split coordinates. The dimension results in the same module establish the missing-reader count. No timing assumptions enter the proof.

### Reproduction

Run `lake build` and `bash scripts/audit.sh`. The module is `BilateralCertificates`. Related background includes the minimal invariant observation spaces in [constrained linear lumping](https://arxiv.org/abs/2004.11961).
