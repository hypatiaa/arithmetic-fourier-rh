# The mean square of a prime-phase polynomial and the Riemann Hypothesis

**saphir** (GitHub: `hypatiaa`) · simplified edition v0.1.1 · 23 November 2026

Attach a unit phase to each prime, and multiply those phases according to the factorisation of an integer. For each fixed positive modulus $B$, this gives a Möbius-weighted polynomial $D_{X,B}$ whose mean-square size can be computed exactly. The Riemann Hypothesis is equivalent to that mean square growing as $O_{B,\delta}(X^{1+\delta})$ for every $\delta > 0$.

The mean square is

$$
\|D_{X,B}\|^2 \;=\; \sum_{\substack{r \le X\\ (r,B)=1}} j(r)\, S_B\!\left(\lfloor X/r \rfloor\right)^2,
\qquad
j(r) = \prod_{p \mid r}\Bigl(1 - \frac{1}{p^2}\Bigr),
\qquad
S_B(t) = \sum_{\substack{k \le t\\ (k,B)=1}} \frac{M(t/k)}{k},
$$

where $M(t) = \sum_{n \le t} \mu(n)$ is the Mertens function. Lean 4, checked against Mathlib's own definitions, verifies both this identity and the equivalence with RH.

---

## 1. Why a mean square can carry the Riemann Hypothesis

Write $\mathscr E_B(X)$ for the right-hand side above. Four short steps do all the work.

**The energy controls the scalar.** At $r = 1$ the weight is $j(1) = 1$, so the first term of the sum is exactly $S_B(X)^2$. Every other term is non-negative. Hence

$$S_B(X)^2 \le \mathscr E_B(X).$$

**The scalar controls the energy.** If $|S_B(t)| \le A\,t^{\theta}$ for some $\theta > \tfrac12$, then each term is at most $A^2 (X/r)^{2\theta}$, and since $0 \le j(r) \le 1$,

$$\mathscr E_B(X) \le A^2 \sum_{r \ge 1} r^{-2\theta}\, X^{2\theta} = A^2\,\zeta(2\theta)\, X^{2\theta}.$$

So $S_B(n) \ll n^{1/2+\varepsilon}$ for every $\varepsilon$ exactly when $\mathscr E_B(X) \ll X^{1+\delta}$ for every $\delta$.

**The scalar is the Mertens function in disguise.** Put $g_B(k) = 1/k$ when $\gcd(k,B) = 1$ and $0$ otherwise, and $h_B(k) = \mu(k)\,g_B(k)$. Since $g_B$ is completely multiplicative, $g_B * h_B$ is the identity for Dirichlet convolution. That gives an exact two-way inversion:

$$S_B(n) = \sum_{k \le n} g_B(k)\, M(\lfloor n/k \rfloor), \qquad M(n) = \sum_{k \le n} h_B(k)\, S_B(\lfloor n/k \rfloor).$$

Both kernels are bounded by $1/k$, so a power bound passes through either sum unchanged: $M(n) = O(n^\theta) \iff S_B(n) = O(n^\theta)$ for every $\theta > 0$.

**The classical step.** By Littlewood (1912), RH holds exactly when $M(x) = O(x^{1/2+\varepsilon})$ for every $\varepsilon > 0$.

Putting the four together:

$$\text{RH} \iff M \ll x^{1/2+\varepsilon} \iff S_B \ll n^{1/2+\varepsilon} \iff \mathscr E_B(X) \ll X^{1+\delta} \iff \|D_{X,B}\|^2 \ll X^{1+\delta}.$$

That is why a question about the norm of a polynomial carries the full content of RH. One sign is even enough: a lower bound $\sigma S_B(n) \ge -C_\varepsilon n^{1/2+\varepsilon}$ for a single fixed sign $\sigma = \pm 1$ is also equivalent to RH. That direction uses Landau's positivity theorem.

## 2. The construction, one prime at a time

### Phases and the Möbius lift

Give each prime $p$ a phase $z_p = e^{i\theta_p}$, and set $Z(n) = \prod_p z_p^{v_p(n)}$. The Möbius lift of $N$ factors over its prime powers:

$$A_N = \sum_{d \mid N} \mu(N/d)\, Z(d) = \prod_{p^a \parallel N} z_p^{a-1}(z_p - 1).$$

For example, $A_6 = (z_2 - 1)(z_3 - 1)$ and $A_{12} = z_2\,(z_2-1)(z_3-1) = z_2 A_6$. Multiplying by one more factor of two rotates the existing lift by the prime-two phase.

On the slice $\theta_p = \tau \log p$ one gets $Z(n) = n^{i\tau}$. The Dirichlet series on a vertical line is one view of the instrument.

### The polynomial

Fix a modulus $B \ge 1$ and a cutoff $X$. Sum the Möbius lifts of the integers $n \le X$ coprime to $B$, with an inclusion–exclusion window $w_{X,B}(n) = \sum_{b \mid \operatorname{rad} B} \mu(b)\,\mathbf 1_{n \le X/b}$:

$$D_{X,B} = \sum_{\substack{n \le X\\(n,B)=1}} w_{X,B}(n)\, A_n = \sum_{\substack{d \le X\\(d,B)=1}} M(X/d)\, Z(d).$$

For $B = 91 = 7 \cdot 13$ the window is $\mathbf 1_{X/7 < n \le X} - \mathbf 1_{X/91 < n \le X/13}$. The second form says the coefficient of each phase monomial $Z(d)$ is a Mertens value.

### The measure, starting from one example

Let each phase $z_p$ be random, with the Poisson law of radius $1/p$ on the circle. The only fact needed is that the average of $z_p^a\,\overline{z_p^{\,b}}$ is $p^{-|a-b|}$.

Take $d = 6$ and $e = 12$. Then $Z(6)\,\overline{Z(12)} = z_2 z_3 \cdot \overline{z_2^2 z_3} = \overline{z_2}$. The common prime-three phase cancels, and one conjugate prime-two phase remains. Its mean is $1/2$. That is

$$\langle Z(6), Z(12) \rangle = \tfrac12 = \frac{\gcd(6,12)^2}{6 \cdot 12}.$$

The same calculation, prime by prime, gives the general formula

$$\langle Z(d), Z(e) \rangle = \frac{\gcd(d,e)^2}{d\,e}.$$

### An orthogonal basis, and the identity

For each prime power, set $\varphi_{p,0} = 1$ and $\varphi_{p,a} = z_p^a - p^{-1} z_p^{a-1}$ for $a \ge 1$. Put $\Psi_r = \prod_{p^a \parallel r} \varphi_{p,a}$. These are orthogonal, with $\|\Psi_r\|^2 = j(r)$. Each monomial expands as $Z(n) = \sum_{r \mid n} (r/n)\, \Psi_r$.

Substitute into $D_{X,B}$ and collect: the coefficient of $\Psi_r$ is $S_B(\lfloor X/r \rfloor)$. By orthogonality,

$$\|D_{X,B}\|^2 = \sum_{\substack{r \le X\\(r,B)=1}} j(r)\, S_B(\lfloor X/r \rfloor)^2,$$

which is the identity on the first page.

## 3. What is verified

Everything in §1 and §2 is proved in Lean 4 against Mathlib. The proofs compile with no `sorry` and use only the three standard axioms.
- The ζ function and `RiemannHypothesis` are Mathlib's own definitions.
- The construction is formalised for every $B \ge 1$: the Poisson product measure, the Gram formula, the orthogonal basis, and the identity.
- The inversion and the RH criteria hold for every $B$.

The proofs were checked in several independent ways.
- **Kernel replay:** every declaration was replayed through Lean's kernel twice, once by our own checker and once by Lean's official `leanchecker`.
- **Statement pins:** a separate file restates each headline result using only plain Mathlib definitions written from scratch, and proves each restatement from the repository's theorem. If any definition in the repository meant something other than its name says, that file would not compile.

The verification record in the repository gives the details and hashes.

## 4. What this is not

- **It is not a proof of RH.** Every result is an identity or an equivalence. Bounding $\|D_{X,B}\|^2$ by $X^{1+\delta}$ for one fixed $B$ and every $\delta$ is exactly as hard as RH.
- **Not everything here is new.**
  - The Gram formula $\gcd(d,e)^2/(de)$ is the $\alpha = 1$ case of the Poisson-integral representation of GCD sums. That goes back to Hedenmalm–Lindqvist–Seip and Lindqvist–Seip, and was developed by Hilberdink and by Aistleitner–Berkes–Seip (2015).
  - The Mertens and Landau criteria are classical.
- **What is new** is the use of that measure for the Möbius-weighted polynomial $D_{X,B}$, the collapse of its mean square onto the single scalar $S_B$, and a machine-checked proof of the whole chain, from a single prime phase to the RH criterion.

## Credits

- **saphir:** the construction (prime phases, the Möbius lift and window, the Poisson measure, the basis $\Psi_r$, the scalar $S_B$ and its inverse, the energy identity), and the direction of the work.
- **Codex:** wrote the main Lean formalisation, and gave the editorial review this edition follows (open with the theorem; lead with the energy squeeze and the worked examples).
- **Gemini:** formalised the measure modules and wrote the full edition.
- **Claude:** compilation checks, statement review, prior-art search, and this simplified edition.
- **Astra:** analytical and editorial review.

## References

- J. E. Littlewood, *C. R. Acad. Sci. Paris* **154** (1912), 263–266.
- E. Landau, *Math. Ann.* **61** (1905), 527–550.
- C. Aistleitner, I. Berkes, K. Seip, *GCD sums from Poisson integrals and systems of dilated functions*, *J. Eur. Math. Soc.* **17** (2015), 1517–1546.
- The full edition (v0.3.3) has the complete references, proofs, and the formal statement list.
