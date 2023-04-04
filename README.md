# README
This code is complementary to the paper "Vectorized and Parallel Computation of Large Smooth-Degree Isogenies using Precedence-Constrained Scheduling" accepted to TCHES and includes two implementations. The first implementation in the folder `multi-core` corresponds to the implementation described in Section 3. The second implementation in the folder `AVX-512 with multi-core` corresponds to the implementation described in Section 4.

## "Multi-core" implementation
Three implementations are provided for multi-core processors with two, three, and four cores. All of them include the optimization in Section 3. The optimizations are mainly in the file `/src/sidh.c`. The execution times of this implementation are shown in the row "This work ($\ast$)" for $4^{186}$-isogeny and "This work" for $3^{239}$-isogeny. To compile and execute, run the following commands:

```bash
 $ make
 $ ./sidhP751/test_SIDH
 $ ./sikeP751/test_SIKE
```

## "AVX-512 with multi-core" implementation
This implementation includes all optimizations listed in Section 4 and 3.2, namely the modified PCP, the modified PCS, and the efficient synchronization handling. The optimizations are mainly in the file `/src/sidh.c`. The execution times of this implementation are shown in the row "4 cores, This work, AVX, PCS". To compile and execute, you need a processor that supports AVX-512 and then run the following commands:

```bash
 $ make
 $ ./sike
```

To benchmark SIKEp751 protocol, you need to modify `/src/main.c` by uncommenting `test_sike()` and then recompile.