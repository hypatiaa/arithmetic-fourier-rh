# A coupling chosen from the three-tooth Vernier denominators

28 November 2026. Exact SageMath 10.9 tests on Nucleus and a written analytic deduction.

**At every integer cutoff from 2 through 100,000,000, the local coupling left fewer than $\sqrt X$ rows in both character gradings.** The exact maximum of its unmatched count divided by $\sqrt X$ was $8/\sqrt{73}$ untwisted and $6/\sqrt{85}$ under $\chi_4$. Two implementations checked this finite claim. For arbitrarily large $X$, the argument below proves an unconditional logarithmic saving. The square-root estimate at unbounded cutoffs remains open.

## The geometry fixes the matrix before the signs are read

Use squarefree $X/2<q\le X$ with $(q,6)=1$. On a complete denominator row the three teeth contribute $(f(q),0,f(q))$, with $f=\mu$ or $f=\mu\chi_4$. All counts here refer to one flank; the full signed endpoint is $2V_f(X)$. The distinguished left-flank fraction at spin one is $a_q/q$, $a_q=(q-1)/2$. Its unsigned Farey determinant with $a_r/r$ is $|a_qr-a_rq|=|r-q|/2$. The right flank gives the same distance. The fractions select which complete rows may interact. Their individual arrows are not required to cancel. [Pinned three-tooth identity](https://github.com/hypatiaa/FVLT/blob/26fe071f3a73cdc8581bee6e33b7c013c928ab96/Lean/projects/farey-character-bridge/ThreeToothVernierBridge.lean#L437)

Set $H=\lfloor\sqrt X\rfloor$. For $i=(q-1)/2$ and $j=(r-1)/2$, use the integer weight
$$
K_H(q,r)=\binom{2H}{H+j-i},
$$
with value zero outside the binomial range. The choice of a binomial kernel and of radius $H$ is part of this experiment. Form $B_f$ by taking the positive rows and negative columns in this one matrix. Twisting changes the grading, while the locations and weights of all candidate edges stay fixed. Let $P,N$ be the two grade counts, $Q=P+N$, and let $U_f=Q-2\operatorname{rank}B_f$. The Dirac theorem identifies $U_f$ with the nullity and gives $|V_f|=|P-N|\le U_f$ (finite linear algebra works in either real-sign grading). [Replayed rank identity](https://github.com/hypatiaa/FVLT/blob/ba94084eafa8c22e693f4ae8160190d0c04e2ee6/Lean/projects/farey-character-bridge/VernierPairingDirac.lean#L553)

### Why the rank computation is exact

$K_H(i,j)$ counts paths of $2H$ time steps from $i$ to $j+H$, with spatial increments zero or one. In a minor with ordered row and column indices, intersecting families cancel by exchanging tails at their first meeting. Disjoint paths retain their order. If $|i_k-j_k|\le H$ for every aligned pair, a disjoint family exists: at time $t$ take the floor of the linear interpolation between $i_k$ and $j_k+H$. The slopes are between zero and one, and adjacent interpolants are separated by at least one throughout. The minor is therefore positive. If a permutation matches all selected vertices, uncrossing an inverted pair preserves both distance bounds. This produces the ordered matching. A nonzero minor in turn requires a matching by its determinant expansion. Thus the rank equals the **maximum number of disjoint opposite-sign pairs** at determinant distance at most $H$. [Gessel and Viennot on path determinants](https://doi.org/10.1016/0001-8708(85)90121-5)

The sweep compares the earliest available positive and negative index. If they are too far apart, the earlier one can never pair with a later member of the other class. If they can pair, a maximum matching can include that edge: replace a single incident edge, or uncross the two incident edges if both are in use. This proves optimality by induction. Exact rational ranks in Sage checked this implementation in 1,224 cases. Another 1,983 integer minors verified the positivity criterion, including zeros.

## Where locality costs rows

| $X$ | Signed $V$ | Untwisted $U$ | Signed $V_4$ | Twisted $U_4$ | Unmatched using pairs valid in both |
|---:|---:|---:|---:|---:|---:|
| 40 | −3 | 3 | −1 | 1 | 3 |
| 720 | −11 | 11 | 3 | 3 | 11 |
| 1,000 | −6 | 6 | 0 | 0 | 6 |
| 100,000 | −60 | 60 | −60 | 60 | 98 |
| 1,000,000 | 86 | 86 | 222 | 494 | 580 |
| 10,000,000 | 708 | 708 | 376 | 376 | 926 |
| 30,922,618 | −1,909 | 1,909 | −1,023 | 1,023 | 1,909 |
| 49,098,878 | 475 | 475 | −2,997 | 2,997 | 2,997 |
| 100,000,000 | 726 | 726 | 550 | 3,100 | 4,476 |

The last column additionally requires both denominators in a pair to agree modulo four. This is necessary and sufficient for an ordinary opposite-sign pair to survive $\chi_4$. The optimal counts then add over the two residue classes. The two certified maxima in the introduction apply to the separately graded matrices. [Exact checkpoints and interval certificates](geometry.json)

At $10^8$, $H=10,000$, so a partner can be at most 20,000 away in its denominator. Among the twisted rows in $[59,829,053,99,999,995]$ there are **6,107,381 negative rows**. The expanded interval, clipped to the band, contains only **6,106,106 positive rows**. At least **1,275 negatives** must remain unmatched in any permitted matching. The greedy matching attains that lower bound. The band has 550 more positives than negatives, so it leaves $550+2(1,275)=3,100$ rows in total. At this particular cutoff the smallest determinant radius that matches the entire minority is **14,207**.

The first extra loss is visible much earlier. At $X=115$ the twisted band sums to zero, yet three positive rows in $[59,67]$ can reach only two negative rows. Two rows survive at $H=10$, and radius 12 clears them. Untwisted, the first excess occurs at $X=1,417$: the signed sum is −1, but the radius-37 coupling leaves three rows. At radius 38 it leaves one. At $X=10^6$, 136 twisted negative rows necessarily remain on the minority side, explaining $494=222+2(136)$.

Fixing the radius at one already fails in a provable way. Every eligible squarefree $q\equiv23\bmod150$ is isolated: $q-2$ is divisible by 3 and $q+2$ by 25. The squarefree integers in this coprime progression have positive density by squarefree inclusion-exclusion. Their band count is linear in $X$. At $10^8$ the radius-one counts are 8,285,592 unmatched untwisted and 8,283,590 twisted. Enlarging the radius changes the asymptotic question.

## How every cutoff was certified

For a range $a\le X\le b$, construct one disjoint matching on the larger denominator interval $(a/2,b]$, at radius $\lfloor\sqrt a\rfloor$. A matched pair $q<r$ survives in precisely the cutoffs $r\le X<2q$, intersected with $[a,b]$. Counting these pairs by their entry and exit cutoffs certifies an upper bound for the optimal unmatched count at every integer in the range. Restriction only deletes edges; every surviving edge meets the allowed radius. Splitting only the ranges whose certificates might exceed the current maximum produces 72 ranges untwisted and 94 twisted.

The second implementation rebuilt the signs with an odd Euler sieve, constructed disjoint pairs with a chronological FIFO queue, and independently counted eligible rows by prefix sums. It verified an upper bound of $64/73$ for $U^2/X$ and $36/85$ for $U_4^2/X$ at all 99,999,999 cutoffs per character by integer cross-multiplication. Direct Sage Möbius sums gave $V(73)=-8$ and $V_4(85)=6$. These force the matching lower bounds at the two witnesses, so both ratios are exact maxima. [Coverage data](coverage.json) · [Independent verification](independent.json)

## What holds for arbitrarily large cutoffs

**For each grading, and even for one matching required to work for both, the number of unmatched rows is $O(X/(\log X)^{1/200})$ with this radius.** Here is a deduction from the short-interval theorem of Matomäki and Radziwiłł. It applies to every sufficiently large cutoff.

Extend each $f$ by zero on multiples of 2 or 3. Both $f_1(n)=\mu(n)\mathbf1_{(n,6)=1}$ and $f_4(n)=f_1(n)\chi_4(n)$ are real multiplicative functions bounded by one. Their long averages are $O_A((\log X)^{-A})$ for each fixed $A$ by Davenport's Möbius estimate applied to the finite Fourier expansion of the fixed periodic weight. [Davenport](https://academic.oup.com/qjmath/article-abstract/os-8/1/313/1564796)

Take $h=H$ and partition the band into blocks of $h$ consecutive integers, trying all $h$ starting offsets. Inside any full block every two active rows are within determinant radius $H$. Pair opposite signs in that block, leaving $|S_f(t,h)|$, where $S_f(t,h)=\sum_{t<n\le t+h}f(n)$. The two partial end blocks cost at most $2h$. Averaging over the offsets and taking the best gives
$$
U_f(X)\le 2h+\frac1h\sum_{\lfloor X/2\rfloor\le t\le X-h}|S_f(t,h)|.
$$
Matomäki–Radziwiłł, Theorem 1, with $\delta=(\log h)^{-1/200}$, bounds the deviation of the short average from the long one by $O((\log h)^{-1/200})$ outside $O(X(\log h)^{-1/100})$ exceptional starts. The half-open endpoint convention costs $O(1/h)$ in the average. Bounding each exceptional average by one and putting $h=\lfloor\sqrt X\rfloor$ proves the claim. For simultaneous pairs, in a full block let $A,B$ be the ordinary sums in residue classes 1 and 3 modulo four. Pair inside each class. The residual $|A|+|B|=\max(|S_1|,|S_4|)\le |S_1|+|S_4|$ satisfies the same offset-averaged estimate. [Matomäki and Radziwiłł, Theorem 1](https://annals.math.princeton.edu/wp-content/uploads/annals-v183-n3-p06-p.pdf#page=2)

**The remaining estimate.** Take the smaller grade $T$. For a subset $S\subseteq T$, let $N_H(S)$ be the available opposite rows within radius $H$. The matching deficiency theorem gives
$$
U_f(X)=|V_f(X)|+2\max_{S\subseteq T}\bigl(|S|-|N_H(S)|\bigr).
$$
Consequently both the global imbalance and the worst local shortage need $O_\varepsilon(X^{1/2+\varepsilon})$ control. The explicit interval above certifies the entire local shortage at $10^8$ under the twist. The short-interval estimate bounds an average of absolute block imbalances at logarithmic scale. It leaves both the uniform square-root estimate and the untwisted RH implication's hypothesis open.

## Reproduce

With a Sage Python environment, Cython, and a C compiler, run the following in this directory. The first command checks small rational matrix ranks and computes individual optimal matchings. The second produces the interval certificates. The third checks the full finite claim using a separate sieve and matching implementation. The path argument and asymptotic deduction above are written proofs. These new claims have not been formalized in Lean.

~~~sh
python test_sage.py
python cover_sage.py
python verify_coverage.py
~~~
