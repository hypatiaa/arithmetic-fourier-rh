# Coherent Arithmetic Fourier Energy, Coprime Möbius Inversion, and Formalized Equivalences for the Riemann Hypothesis in Lean 4

**Author:** saphir (GitHub: `hypatiaa`)  
**Date:** 2026-11-23  
**Version:** v0.3.3.1  
**2020 Mathematics Subject Classification:** Primary 11M26; Secondary 11N37, 68V20.  
**Keywords:** Riemann Hypothesis, Möbius function, Mertens function, arithmetic Fourier transform, Poisson measure, orthogonal polynomials, formal verification, Lean 4, Mathlib.

---

## Abstract

We attach a unit phase to each prime and multiply those phases according to the factorization of an integer. For each fixed integer modulus $B \ge 1$, this defines a Möbius-weighted trigonometric polynomial $D_{X,B}$ whose mean-square size under the product Poisson measure $\nu$ (radius $1/p$ at each prime $p$) can be computed explicitly:
$$\|D_{X,B}\|_\nu^2 = \sum_{\substack{r \le X \\ (r,B)=1}} j(r)\, S_B(\lfloor X/r \rfloor)^2, \qquad j(r) = \prod_{p \mid r} \left(1 - \frac{1}{p^2}\right), \qquad S_B(t) = \sum_{\substack{k \le t \\ (k,B)=1}} \frac{M(t/k)}{k},$$
where $M(t) = \sum_{1 \le n \le t} \mu(n)$ is the Mertens function. The Riemann Hypothesis is equivalent to $\|D_{X,B}\|_\nu^2 = O_{B,\delta}(X^{1+\delta})$ for every $\delta > 0$, to two-sided and one-sided bounds on $S_B$, and in scaled form to zero-free half-planes $\operatorname{Re} s > a$ ($\tfrac{1}{2} \le a < 1$). Lean 4, checked against Mathlib's own definitions, verifies both this energy identity ($B \ge 1$) and its equivalence with RH for every fixed modulus (Section 6 records the kernel replay, statement reviews, and checksums). Every result is an equivalence or an identity: no unconditional square-root growth bound for $S_B$, $D_{X,B}$, or $M$ is proved.

---

## 1. Why a Mean Square Can Carry the Riemann Hypothesis

Write $\mathscr{E}_B(X)$ for the right-hand side of the mean-square identity in the Abstract. Four short steps explain why bounding this single sum of squares captures the full content of the Riemann Hypothesis (RH).

**The energy controls the scalar.** At $r = 1$ the weight is $j(1) = 1$, so the first term of the sum is $S_B(X)^2$. Every other term is non-negative, giving $S_B(X)^2 \le \mathscr{E}_B(X)$.

**The scalar controls the energy.** If $|S_B(t)| \le A\, t^\theta$ for some $\theta > \tfrac{1}{2}$, then each term is at most $A^2 (X/r)^{2\theta}$, and since $0 \le j(r) \le 1$,
$$\mathscr{E}_B(X) \le A^2 \sum_{r \ge 1} r^{-2\theta}\, X^{2\theta} = A^2\, \zeta(2\theta)\, X^{2\theta}.$$
Hence $S_B(n) \ll_\varepsilon n^{1/2+\varepsilon}$ for every $\varepsilon > 0$ holds if and only if $\mathscr{E}_B(X) \ll_\delta X^{1+\delta}$ for every $\delta > 0$.

**The scalar is the Mertens function in disguise.** Put $g_B(k) = 1/k$ when $\gcd(k, B) = 1$ and $0$ otherwise, and $h_B(k) = \mu(k)\, g_B(k)$. Because $g_B$ is completely multiplicative, $g_B * h_B = \delta_1$ under Dirichlet convolution, yielding the exact two-way inversion
$$S_B(n) = \sum_{k=1}^n g_B(k)\, M(\lfloor n/k \rfloor), \qquad M(n) = \sum_{k=1}^n h_B(k)\, S_B(\lfloor n/k \rfloor).$$
Both kernels satisfy $|g_B(k)|, |h_B(k)| \le 1/k$, so any power bound passes through either sum unchanged: $M(n) = O(n^\theta) \iff S_B(n) = O(n^\theta)$ for every $\theta > 0$.

**The classical step.** By Littlewood [1912], RH holds if and only if $M(x) = O_\varepsilon(x^{1/2+\varepsilon})$ for every $\varepsilon > 0$ [Titchmarsh 1986; Montgomery–Vaughan 2007]. Putting the four steps together gives
$$\mathrm{RH} \iff M \ll_\varepsilon x^{1/2+\varepsilon} \iff S_B \ll_\varepsilon n^{1/2+\varepsilon} \iff \mathscr{E}_B(X) \ll_\delta X^{1+\delta} \iff \|D_{X,B}\|_\nu^2 \ll_\delta X^{1+\delta}.$$
That is why a question about the norm of a trigonometric polynomial carries the full content of RH. One sign is already enough: using the coprime Dirichlet factor $L(g_B, s)$ and Landau's positivity theorem [Landau 1905; Mertens 1897], a lower bound $\sigma S_B(n) \ge -C_\varepsilon n^{1/2+\varepsilon}$ for either fixed sign $\sigma \in \{1, -1\}$ is also equivalent to RH, and shifting the exponent $a \in [\tfrac{1}{2}, 1)$ covers zero-free half-planes $\operatorname{Re} s > a$. Originating in `saphir`'s arithmetic Fourier instrument (October 2026), the construction and all equivalences are formalized in Lean 4 against Mathlib [de Moura–Ullrich 2021; mathlib Community 2020].

### Main Results and Epistemic Scope

To maintain strict transparency between machine-verified proofs, classical analytic derivations, conditional statements, and open problems, every claim in this paper is assigned to one of four explicit categories:

1. **Formalized and kernel-checked in Lean 4 (Sections 2–5):**
   - *Exact coprime inversion and power-bound transfer (`v2.6.4`, Sections 3–5):* For every $B \in \mathbb{N}$, $g_B * h_B = \delta_1$, yielding the mutual inversion identities relating $M(n)$ and $S_B(n)$, and the equivalence $M(n) = O(n^\theta) \iff S_B(n) = O(n^\theta)$ for all $\theta > 0$.
   - *Two-sided energy squeeze and half-plane equivalences (`v2.6.4`, Sections 3 and 5):* Defining the energy sum $\mathscr{E}_B(X) := \sum_{r \le X,\, (r,B)=1} j(r)\, S_B(\lfloor X/r \rfloor)^2$, we have $S_B(X)^2 \le \mathscr{E}_B(X) \le A^2 \zeta(2\theta) X^{2\theta}$ whenever $|S_B(k)| \le A k^\theta$ ($\theta > \tfrac{1}{2}$). Consequently, for every $B \in \mathbb{N}$ and $\tfrac{1}{2} \le a < 1$, $\zeta(s) \neq 0$ on $\operatorname{Re} s > a$ if and only if $S_B(n) = O_\varepsilon(n^{a+\varepsilon})$ for all $\varepsilon > 0$, if and only if $\mathscr{E}_B(X) = O_\varepsilon(X^{2a+\varepsilon})$ for all $\varepsilon > 0$. At $a = \tfrac{1}{2}$, $\mathrm{RH} \iff \forall \delta > 0,\ \mathscr{E}_B(X) = O_\delta(X^{1+\delta})$.
   - *Coprime Euler factor and one-sided criteria (`v2.6.4`, Sections 4–5):* The Dirichlet series $L(g_B, s)$ and $L(h_B, s)$ are holomorphic on $\operatorname{Re} s > 0$ and satisfy $L(g_B, s) L(h_B, s) = 1$, with $\sum_{n \ge 1} (g_B * \mu)(n)\, n^{-s} = L(g_B, s)/\zeta(s)$ for $\operatorname{Re} s > 1$. Combining this non-vanishing factor with a formalized Landau Mellin-extension theorem gives one-sided RH and zero-free strip criteria for $\sigma S_B(n) \ge -C_\varepsilon n^{a+\varepsilon}$ ($\sigma \in \{1, -1\}$). At $B = 0$, these statements specialize verbatim to the classical Mertens criteria.
   - *Poisson-measure diagonalization and $L^2(\nu)$ RH bridges for $B \ge 1$ (Section 2):* Construction of the product Poisson probability measure $\nu = \bigotimes_p \nu_p$, inclusion–exclusion recombination for $D_{X,B}$, Gram identity $\langle Z(d), Z(e)\rangle_\nu = \gcd(d,e)^2/(de)$, orthogonal family $\{\Psi_r\}$, Parseval identity $\mathscr{E}_B(X) = \|D_{X,B}\|_\nu^2$, and the resulting measure-norm RH and fixed-strip criteria for all $B \ge 1$.
2. **Analytic prose remark and finite rational controls (Section 2):**
   - The Hilbert-space observation that $\overline{z_p} - p^{-1}$ has squared norm $1 - p^{-2} > 0$ while being orthogonal to all $Z(n)$ (showing the closed span of $\{\Psi_r\}$ is strictly smaller than $L^2(\Omega, \nu)$) is given analytically in prose; and Proposition 2.5 is independently corroborated at $B = 91$ by `9,291` exact rational-arithmetic checks across `578` configurations up to $X = 1000$.
3. **Conditional theorems separated from the unconditional dictionary (`Remark 5.5`):**
   - Auxiliary modules in the same Lean artifact connect long-rank power savings to $S_B$ under an explicit hypothesis `ZetaDensityPremise` modeling Ingham's zero-density estimate [Ingham 1940]. The principal equivalences in Sections 3–5 are independent of that premise.
4. **Open mathematical problem:**
   - **The RH-scale growth estimate remains open.** Every equivalence places $\mathrm{RH}$ (or a zero-free half-plane) on one side and a polynomial growth estimate on the other. Obtaining $\mathscr{E}_B(X) \ll_\delta X^{1+\delta}$ or $S_B(n) \ll_\varepsilon n^{1/2+\varepsilon}$ remains completely open.

### Organization of the Paper

Section 1 explains the four-step equivalence chain and fixes epistemic scope. Section 2 develops the prime-phasor lifts, worked examples, inclusion–exclusion window, Poisson Hilbert space $L^2(\Omega, \nu)$, and Parseval identity connecting $\|D_{X,B}\|_\nu^2$ to $\mathscr{E}_B(X)$. Section 3 presents the formalized definitions, finite Dirichlet-convolution inversion, and the two-sided energy squeeze in Lean 4. Section 4 isolates the coprime Dirichlet factor $L(g_B, s)$ and its reciprocal. Section 5 states and explains the proof architecture for the two-sided and one-sided half-plane and RH equivalences, explicitly separating conditional zero-density results. Section 6 records the scope of formal verification. Section 7 compares the construction and Lean 4 formalization with related analytic and formalization prior art. Section 8 discusses scope, limitations, and open problems.

---

## 2. Prime-Phasor Construction and Coherent Energy

> **Epistemic Status of Section 2.** Proposition 2.2 (`D_eq_mertens_sum`), Example 2.3 (`sievingWindow_91`), Definition 2.4 (`poissonMeasure`, `primeTorusMeasure`, `Psi`), and all three parts of Proposition 2.5 (`innerNu_Z`, `innerNu_Psi`, `Z_eq_sum_Psi`, `D_eq_sum_Psi`, `norm_sq_D_eq_energy`) are **formalized and strictly kernel-replayed in Lean 4** in the `CoherentEnergyMeasure` module for every integer $B \ge 1$ and natural $X \ge 1$, and bridged to the Section 5 RH and half-plane equivalences of `v2.6.4` via `CoherentEnergyRHBridge`. In the Lean formalization, $X$ is a natural number ($X \in \mathbb{N}$, $X \ge 1$); the real-$X$ statement of Proposition 2.5(3) follows immediately because for integers $n, b \ge 1$ one has $n \le X/b \iff nb \le \lfloor X \rfloor \iff n \le \lfloor \lfloor X \rfloor / b \rfloor$, so $D_{X,B} = D_{\lfloor X \rfloor, B}$ and $\mathscr{E}_B(X) = \mathscr{E}_B(\lfloor X \rfloor)$. These results are also corroborated up to $X = 1000$ by the finite rational-arithmetic suite of Section 2.4. The prose observation after Proposition 2.5 showing that the ambient space $L^2(\Omega, \nu)$ strictly contains the closed span of $\{\Psi_r\}$ remains an unformalized analytic remark.

### 2.1 Prime Phasors and Divisor Lifts

Let $\mathcal{P}$ denote the set of rational primes and $\mathbb{T} = \mathbb{R}/2\pi\mathbb{Z}$. Let $\Omega = \mathbb{T}^{\mathcal{P}}$ be the compact torus parametrized by phase tuples $\boldsymbol{\theta} = (\theta_p)_{p \in \mathcal{P}}$, with unit coordinate phasors $z_p(\boldsymbol{\theta}) = e^{i\theta_p}$.

**Definition 2.1 (Multiplicative phasor lift and Möbius lift).**  
For each positive integer $n \ge 1$, define the multiplicative character on $\Omega$ by
$$Z(n) = Z(n; \mathbf{z}) := \prod_{p \in \mathcal{P}} z_p^{v_p(n)},$$
where $v_p(n)$ is the $p$-adic valuation of $n$ (with $Z(1) = 1$). For $N \ge 1$, define the *divisor lift* $L_N(\mathbf{z})$ and the *Möbius lift* $A_N(\mathbf{z})$ by
$$L_N(\mathbf{z}) := \sum_{d \mid N} Z(d) = \prod_{p^a \parallel N} \left(1 + z_p + \dots + z_p^a\right),$$
$$A_N(\mathbf{z}) := \sum_{d \mid N} \mu(N/d)\, Z(d) = \prod_{p^a \parallel N} z_p^{a-1}(z_p - 1),$$
where $p^a \parallel N$ indicates $a = v_p(N) \ge 1$ and empty products equal $1$. For example, $A_6(\mathbf{z}) = (z_2 - 1)(z_3 - 1)$ and $A_{12}(\mathbf{z}) = z_2 (z_2 - 1)(z_3 - 1) = z_2 A_6(\mathbf{z})$: multiplying by one more factor of $2$ rotates the existing lift by the prime-two phase. On the logarithmic slice $\theta_p = \tau \log p$ ($\tau \in \mathbb{R}$), one gets $Z(n) = n^{i\tau}$, so a Dirichlet series on a vertical line is one view of the instrument.

### 2.2 Inclusion–Exclusion Sieving Window

Fix an integer modulus $B \ge 1$, let $R = \mathrm{rad}(B) := \prod_{p \mid B} p$ be its squarefree radical (with $R = 1$ if $B = 1$), and define the inclusion–exclusion window on $\mathbb{N}_{\ge 1}$ by
$$w_{X,B}(n) := \sum_{b \mid R} \mu(b)\, \mathbf{1}_{n \le X/b} \qquad (X \ge 1).$$
Consider the coprime Möbius-lift sum
$$D_{X,B}(\mathbf{z}) := \sum_{\substack{n \le X \\ (n,B)=1}} w_{X,B}(n)\, A_n(\mathbf{z}).$$

**Proposition 2.2 (Reduction of $D_{X,B}$ to standard Mertens coefficients).**  
*For every real $X \ge 1$ and integer $B \ge 1$,*
$$D_{X,B}(\mathbf{z}) = \sum_{\substack{d \le X \\ (d,B)=1}} M(X/d)\, Z(d), \qquad \text{where } M(t) := \sum_{1 \le n \le t} \mu(n).$$

*Proof.* Substituting $A_n(\mathbf{z}) = \sum_{d \mid n} \mu(n/d) Z(d)$ and writing $n = dm$, the condition $(dm, B) = 1$ holds if and only if $(d, B) = 1$ and $(m, B) = 1$ (equivalently $(m, R) = 1$). Reordering the finite sum yields
$$D_{X,B}(\mathbf{z}) = \sum_{\substack{d \le X \\ (d,B)=1}} c_{X,B}(d)\, Z(d), \qquad c_{X,B}(d) := \sum_{\substack{m \le X/d \\ (m,R)=1}} \mu(m)\, w_{X,B}(dm).$$
Note that $w_{X,B}(n) = 0$ for $n > X$ because each term $\mathbf{1}_{n \le X/b}$ vanishes there. Expanding $w_{X,B}(dm)$ gives
$$c_{X,B}(d) = \sum_{b \mid R} \mu(b) \sum_{\substack{m \le X/(bd) \\ (m,R)=1}} \mu(m) = \sum_{b \mid R} \sum_{\substack{m \le X/(bd) \\ (m,R)=1}} \mu(bm),$$
since $b \mid R$ and $(m, R) = 1$ imply $(b, m) = 1$ and hence $\mu(b)\mu(m) = \mu(bm)$. Now set $k = bm$. Every $k \ge 1$ with $\mu(k) \neq 0$ is squarefree, so $v_p(k) \in \{0, 1\}$ for each $p \mid R$; consequently, such a $k$ decomposes uniquely as $k = bm$ with $b = \gcd(k, R) \mid R$ and $(m, R) = 1$. Conversely, if $p^2 \mid k$ for some $p \mid R$, then $\mu(k) = 0$ and $k$ admits no such decomposition. Summing over all $k \le X/d$ therefore gives $c_{X,B}(d) = \sum_{k \le X/d} \mu(k) = M(X/d)$. $\square$

**Example 2.3 (The modulus $B = 91$).**  
For $B = 91 = 7 \cdot 13$, we have $R = 91$ and
$$w_{X,91}(n) = \mathbf{1}_{n \le X} - \mathbf{1}_{n \le X/7} - \mathbf{1}_{n \le X/13} + \mathbf{1}_{n \le X/91} = \mathbf{1}_{X/7 < n \le X} - \mathbf{1}_{X/91 < n \le X/13}.$$
With $M_{91}(t) := \sum_{n \le t,\, (n,91)=1} \mu(n)$, the proof of Proposition 2.2 reads explicitly as
$$c_{X,91}(d) = M_{91}\!\left(\frac{X}{d}\right) - M_{91}\!\left(\frac{X}{7d}\right) - M_{91}\!\left(\frac{X}{13d}\right) + M_{91}\!\left(\frac{X}{91d}\right) = M\!\left(\frac{X}{d}\right).$$

### 2.3 Product Poisson Measure and Orthogonal Energy Diagonalization

**Definition 2.4 (Product Poisson measure and orthogonal system).**  
For $\rho \in [0, 1)$, let $\mathcal{P}_\rho(\theta) := \frac{1 - \rho^2}{1 - 2\rho\cos\theta + \rho^2} = \sum_{m \in \mathbb{Z}} \rho^{|m|} e^{im\theta}$ be the normalized Poisson kernel on $\mathbb{T}$. Endow each coordinate $p \in \mathcal{P}$ with the probability measure $d\nu_p(\theta_p) := \mathcal{P}_{1/p}(\theta_p)\,\frac{d\theta_p}{2\pi}$, and let $\nu := \bigotimes_{p \in \mathcal{P}} \nu_p$ on $\Omega$, with inner product $\langle F, G \rangle_\nu := \int_\Omega F \overline{G}\, d\nu$. Define the local prime-power functions
$$\varphi_{p,0}(z_p) := 1, \qquad \varphi_{p,a}(z_p) := z_p^a - p^{-1} z_p^{a-1} \quad (a \ge 1),$$
and the global product functions
$$\Psi_r(\mathbf{z}) := \prod_{p^a \parallel r} \varphi_{p,a}(z_p) \qquad (r \ge 1), \qquad j(r) := \prod_{p \mid r} \left(1 - p^{-2}\right),$$
with $\Psi_1 = 1$ and $j(1) = 1$.

**Worked Example ($\langle Z(6), Z(12)\rangle_\nu = \tfrac{1}{2}$).**  
Because the normalized Poisson kernel $\mathcal{P}_{1/p}(\theta) = \sum_{m \in \mathbb{Z}} p^{-|m|} e^{im\theta}$ gives coordinate moments $\mathbb{E}_{\nu_p}[z_p^a \overline{z_p^b}] = p^{-|a-b|}$, product independence reduces every Gram inner product prime by prime. Take $d = 6 = 2 \cdot 3$ and $e = 12 = 2^2 \cdot 3$. Then
$$Z(6)\,\overline{Z(12)} = (z_2 z_3)\,\overline{(z_2^2 z_3)} = \overline{z_2}, \qquad \langle Z(6), Z(12) \rangle_\nu = \mathbb{E}_{\nu_2}[\overline{z_2}] = \frac{1}{2} = \frac{\gcd(6, 12)^2}{6 \cdot 12}.$$
The common prime-three phase cancels ($\mathbb{E}_{\nu_3}[z_3\overline{z_3}] = 1$), leaving one conjugate prime-two phase whose mean is $1/2$.

**Proposition 2.5 (Orthogonality and coherent-energy diagonalization).**  
*In the Hilbert space $L^2(\Omega, \nu)$:*
1. *For all integers $d, e \ge 1$,*
   $$\langle Z(d), Z(e) \rangle_\nu = \frac{\gcd(d, e)^2}{de}.$$
2. *The family $\{\Psi_r\}_{r \ge 1}$ is orthogonal, with*
   $$\langle \Psi_r, \Psi_s \rangle_\nu = \mathbf{1}_{r=s}\, j(r),$$
   *and spans the $Z(n)$ via the exact triangular expansion*
   $$Z(n) = \sum_{r \mid n} \frac{r}{n}\, \Psi_r \qquad (n \ge 1).$$
3. *For every real $X \ge 1$ and integer $B \ge 1$, defining*
   $$S_B(t) := \sum_{\substack{k \le t \\ (k,B)=1}} \frac{M(t/k)}{k} \qquad (t \ge 0),$$
   *we have the orthogonal expansion and Parseval identity*
   $$D_{X,B} = \sum_{\substack{r \le X \\ (r,B)=1}} S_B(\lfloor X/r \rfloor)\, \Psi_r, \qquad \mathscr{E}_B(X) := \|D_{X,B}\|_\nu^2 = \sum_{\substack{r \le X \\ (r,B)=1}} j(r)\, S_B(\lfloor X/r \rfloor)^2.$$

*Proof.*  
(1) Since $\mathcal{P}_{1/p}(\theta) = \sum_{m \in \mathbb{Z}} p^{-|m|} e^{im\theta}$ converges uniformly on $\mathbb{T}$, $\mathbb{E}_{\nu_p}[z_p^a \overline{z_p^b}] = \int_{\mathbb{T}} e^{i(a-b)\theta_p} \mathcal{P}_{1/p}(\theta_p)\,\frac{d\theta_p}{2\pi} = p^{-|a-b|}$ for all $a, b \in \mathbb{Z}$. Because $Z(d)\overline{Z(e)}$ depends on finitely many coordinates under the product measure $\nu$,
$$\langle Z(d), Z(e) \rangle_\nu = \prod_{p \mid de} p^{-|v_p(d) - v_p(e)|}.$$
Using the valuation identity $|v_p(d) - v_p(e)| = v_p(d) + v_p(e) - 2\min(v_p(d), v_p(e)) = v_p(de) - 2v_p(\gcd(d, e))$ yields $\langle Z(d), Z(e) \rangle_\nu = \gcd(d, e)^2 / (de)$.

(2) For a fixed prime $p$, we compute $\langle \varphi_{p,a}, \varphi_{p,b} \rangle_{\nu_p}$. Clearly $\langle \varphi_{p,0}, \varphi_{p,0} \rangle_{\nu_p} = 1$. If $a \ge 1$ and $b = 0$, then $\langle z_p^a - p^{-1} z_p^{a-1}, 1 \rangle_{\nu_p} = p^{-a} - p^{-1} p^{-(a-1)} = 0$. If $a > b \ge 1$, then $a - b \ge 1$ and $a - 1 - b \ge 0$, so
$$\langle \varphi_{p,a}, \varphi_{p,b} \rangle_{\nu_p} = p^{-(a-b)} - p^{-1} p^{-(a-b+1)} - p^{-1} p^{-(a-1-b)} + p^{-2} p^{-(a-b)} = 0;$$
by conjugate symmetry, the inner product also vanishes when $b > a$. Finally, when $a = b \ge 1$,
$$\langle \varphi_{p,a}, \varphi_{p,a} \rangle_{\nu_p} = 1 - p^{-2} - p^{-2} + p^{-2} = 1 - p^{-2}.$$
Because $\Psi_r = \prod_{p \in \mathcal{P}} \varphi_{p, v_p(r)}$ is a finite product (since $\varphi_{p,0} = 1$), product-measure integration gives
$$\langle \Psi_r, \Psi_s \rangle_\nu = \prod_{p \mid rs} \langle \varphi_{p, v_p(r)}, \varphi_{p, v_p(s)} \rangle_{\nu_p} = \mathbf{1}_{r=s} \prod_{p \mid r} (1 - p^{-2}) = \mathbf{1}_{r=s}\, j(r).$$
Next, for any prime $p$ and integer $a \ge 0$, telescoping yields
$$\sum_{c=0}^{a} \frac{p^c}{p^a}\, \varphi_{p,c}(z_p) = p^{-a} + \sum_{c=1}^{a} p^{-(a-c)} \bigl(z_p^c - p^{-1} z_p^{c-1}\bigr) = p^{-a} + \sum_{c=1}^{a} \bigl(p^{c-a} z_p^c - p^{(c-1)-a} z_p^{c-1}\bigr) = z_p^a.$$
Taking the product over $p^a \parallel n$ and expanding over tuples $(c_p)_{p \mid n}$ with $0 \le c_p \le v_p(n)$, corresponding bijectively to divisors $r = \prod_{p \mid n} p^{c_p} \mid n$, gives $Z(n) = \sum_{r \mid n} (r/n)\Psi_r$.

(3) Substituting $Z(d) = \sum_{r \mid d} (r/d)\Psi_r$ into Proposition 2.2 and setting $d = rk$ (so $(d,B) = 1 \iff (r,B) = 1 \text{ and } (k,B) = 1$), we obtain
$$D_{X,B} = \sum_{\substack{r \le X \\ (r,B)=1}} \Psi_r \sum_{\substack{k \le X/r \\ (k,B)=1}} \frac{M(X/(rk))}{k}.$$
For real $X \ge 1$ and integers $r, k \ge 1$, the elementary floor identity $\lfloor X/(rk) \rfloor = \lfloor \lfloor X/r \rfloor / k \rfloor$ together with $M(t) = M(\lfloor t \rfloor)$ implies that the inner sum equals $S_B(\lfloor X/r \rfloor)$. Orthogonality of $\{\Psi_r\}_{r \ge 1}$ in $L^2(\Omega, \nu)$ then gives $\mathscr{E}_B(X) = \|D_{X,B}\|_\nu^2 = \sum_{r \le X,\, (r,B)=1} j(r)\, S_B(\lfloor X/r \rfloor)^2$. $\square$

The triangular expansions above identify the closed span of the modes with the closed span of the analytic monomials $Z(n)$. The ambient space is larger. Fix a prime $p$ and put $\rho=1/p$. The function $\overline{z_p}-\rho$ has squared norm $1-\rho^2>0$, yet its inner product with $z_p^k$ equals $\rho^{k+1}-\rho\,\rho^k=0$ for every $k\ge0$. Independence gives orthogonality to every $Z(n)$. The energy identity uses only the finite expansion of $D_{X,B}$.

*Literature credit for the Poisson Gram kernel:* In the harmonic-analysis and GCD-matrix literature—in the lineage of Hedenmalm–Lindqvist–Seip [1997] and Lindqvist–Seip [1998], developed for zeta $\Omega$-results by Hilberdink [2009], and crystallized by Aistleitner–Berkes–Seip [2015]—quadratic forms with entries $\gcd(n_k, n_\ell)^{2\alpha}/(n_k n_\ell)^\alpha$ ($0 < \alpha \le 1$) are realized as Poisson integrals on the infinite-dimensional polydisc evaluated at radial parameters $(p^{-\alpha})$. At $\alpha = 1$, that Poisson integral inner product is precisely Proposition 2.5(1), $\langle Z(d), Z(e)\rangle_\nu = \gcd(d, e)^2 / (de)$ (see Section 7.1 for a direct comparison).

### 2.4 Finite Rational-Arithmetic Checks

**Remark 2.6 (Exact finite controls for $B = 91$).**  
At $B=91$, exact rational arithmetic reproduced 9,291 checks across 578 projection configurations. Full polynomial reconstruction was checked at $X=1,\ldots,160$ and at $200,216,343,512,729,1000$. Direct comparison of the full Gram quadratic form with the scalar sum of squares was checked at $X=1,\ldots,40$, $125$, and $216$. The general identity follows from Proposition 2.5 (now formalized and kernel-checked for every $B \ge 1$ in `CoherentEnergyMeasure`, with `sievingWindow_91` checked specifically at $B = 91$).

---

## 3. Formalized Algebraic Inversion and Coherent-Energy Squeeze

From this section through Section 5, the principal formal results are stated in mathematical notation from the comment-scrubbed, kernel-checked Lean 4 release *Arithmetic Fourier and Compensated Trace in Lean* (`v2.6.4`), with `CoherentEnergyRHBridge` verifying exact definitional concordance (`mertens_eq_M`, `scalarS_eq_S`, `jWeight_eq_j`) between Section 2's measure-side functions and `v2.6.4`. Throughout, $\mathbb{N} = \{0, 1, 2, \dots\}$ and natural division $n / k$ denotes $\lfloor n / k \rfloor$.

### 3.1 Formal Definitions in Lean 4

**Definition 3.1 (Arithmetic weights, scalar $S_B$, and coherent energy).**  
For $B \in \mathbb{N}$, define real-valued arithmetic functions $g_B, h_B : \mathbb{N} \to \mathbb{R}$ by
$$g_B(k) := \begin{cases} 1/k & \text{if } \gcd(k, B) = 1, \\ 0 & \text{otherwise}, \end{cases} \qquad h_B(k) := g_B(k)\, \mu(k),$$
with Dirichlet convolution $(u * v)(n) = \sum_{ab = n} u(a)v(b)$ and unit $\delta_1$. Set
$$M(n) := \sum_{1 \le j \le n} \mu(j), \qquad S_B(n) := \sum_{1 \le j \le n} (g_B * \mu)(j) \qquad (n \in \mathbb{N}).$$
For $F : \mathbb{N} \to \mathbb{R}$ and $\theta \in \mathbb{R}$, write
$$\mathcal{B}(F, \theta) \quad :\Longleftrightarrow \quad \exists C \ge 0,\ \forall n \ge 1,\ |F(n)| \le C\, n^\theta.$$
On the energy side, set $j(r) := \prod_{p \in \mathrm{primeFactors}(r)} (1 - p^{-2})$ (so $j(0) = j(1) = 1$), $\mathcal{I}(B, X) := \{r \in [1, X] \cap \mathbb{N} : \gcd(r, B) = 1\}$, and for any sequence $S : \mathbb{N} \to \mathbb{R}$,
$$\mathrm{energy}(S, B, X) := \sum_{r \in \mathcal{I}(B, X)} j(r)\, S(\lfloor X/r \rfloor)^2, \qquad \mathrm{pSeries}(p) := \sum_{r=0}^{\infty} r^{-p},$$
where $0^{-p} = 0$ in Mathlib so $\mathrm{pSeries}(2\theta) = \zeta(2\theta)$ for $\theta > \tfrac{1}{2}$. When $S = S_B$, we write $\mathscr{E}_B(X) := \mathrm{energy}(S_B, B, X)$.

**Remark 3.2 (Edge moduli $B = 0$ and $B = 1$).**  
Because $\gcd(k, 0) = k$, the Lean condition `Nat.Coprime k 0` holds if and only if $k = 1$. Hence at $B = 0$:
$$g_0 = h_0 = \delta_1, \qquad S_0(n) = M(n), \qquad \mathcal{I}(0, X) = \{1\} \quad (X \ge 1), \qquad \mathscr{E}_0(X) = M(X)^2.$$
Thus the $B = 0$ specialization recovers the classical Mertens theory verbatim inside the same formal statements, even though the inclusion–exclusion window $w_{X,B}$ of Section 2 uses $B \ge 1$. At $B = 1$, every $k \ge 1$ is coprime to $1$, so $g_1(k) = 1/k$ for all $k \ge 1$ and $S_1(n) = \sum_{k=1}^n M(\lfloor n/k \rfloor)/k$.

### 3.2 Exact Coprime Inversion and Power-Bound Equivalence

**Theorem 3.3 (Exact finite inversion for all $B \in \mathbb{N}$).**  
*For every $B \in \mathbb{N}$ and every $n \in \mathbb{N}$:*
1. $g_B * h_B = \delta_1$ *in the ring of real-valued arithmetic functions.*
2. $S_B(n) = \sum_{k=1}^{n} g_B(k)\, M(\lfloor n/k \rfloor)$.
3. $M(n) = \sum_{k=1}^{n} h_B(k)\, S_B(\lfloor n/k \rfloor)$.

*Lean proof idea.* Because $g_B$ is completely multiplicative, twisting by $g_B$ distributes over Dirichlet convolution: $(g_B \cdot u) * (g_B \cdot v) = g_B \cdot (u * v)$. Taking $u = 1$ (constant arithmetic function $\zeta_{\mathrm{arith}}$) and $v = \mu$ uses Mathlib's identity $\zeta_{\mathrm{arith}} * \mu = \delta_1$, giving $g_B * h_B = g_B \cdot \delta_1 = \delta_1$ since $g_B(1) = 1$. Applying Mathlib's hyperbola summatory identity `sum_Ioc_mul_eq_sum_sum` directly proves `S_from_M`, and multiplying $h_B * (g_B * \mu) = (h_B * g_B) * \mu = \mu$ yields `M_from_S`. $\square$

**Theorem 3.4 (Mutual power-bound transfer).**  
*Let $B \in \mathbb{N}$ and $\theta > 0$.*
1. *For any sequences $F, G, w : \mathbb{N} \to \mathbb{R}$ satisfying $|w(k)| \le 1/k$ for all $k \in \mathbb{N}$ and $G(n) = \sum_{k=1}^n w(k) F(\lfloor n/k \rfloor)$, if $\mathcal{B}(F, \theta)$ holds with constant $A \ge 0$, then $\mathcal{B}(G, \theta)$ holds with constant $A \sum_{k=1}^{\infty} k^{-(1+\theta)}$.*
2. $\mathcal{B}(M, \theta) \iff \mathcal{B}(S_B, \theta)$.
3. *In particular, $M(n) = O_\varepsilon(n^{1/2+\varepsilon})$ for all $\varepsilon > 0$ if and only if $S_B(n) = O_\varepsilon(n^{1/2+\varepsilon})$ for all $\varepsilon > 0$.*

*Lean proof idea.* Both $|g_B(k)| \le 1/k$ and $|h_B(k)| \le 1/k$ hold pointwise. Since $\lfloor n/k \rfloor \le n/k$ and $1+\theta > 1$, the $p$-series $\sum_{k=1}^{\infty} k^{-(1+\theta)}$ converges and bounds the transferred sum by $A n^\theta \sum_{k=1}^{\infty} k^{-(1+\theta)}$. $\square$

### 3.3 The Two-Sided Energy Squeeze

**Proposition 3.5 (Energy squeeze).**  
*For every $B \in \mathbb{N}$, every $r \in \mathbb{N}$, and every sequence $S : \mathbb{N} \to \mathbb{R}$:*
1. $0 \le j(r) \le 1$ *and* $j(1) = 1$.
2. *For every $X \ge 1$,* $S(X)^2 \le \mathrm{energy}(S, B, X)$.
3. *If $\theta > \tfrac{1}{2}$, $A \ge 0$, and $|S(k)| \le A k^\theta$ for all $k \ge 1$, then for every $X \in \mathbb{N}$,*
   $$\mathrm{energy}(S, B, X) \le A^2\, \mathrm{pSeries}(2\theta)\, X^{2\theta}.$$
4. *Combining the lower and upper bounds at $\theta = \tfrac{1}{2} + \varepsilon$ ($\delta = 2\varepsilon$),*
   $$\Bigl(\forall \varepsilon > 0,\ \mathcal{B}(S, \tfrac{1}{2}+\varepsilon)\Bigr) \iff \Bigl(\forall \delta > 0,\ \mathcal{B}(\mathrm{energy}(S, B, \cdot), 1+\delta)\Bigr).$$

Note that no arithmetic structure on $S$ is used in Proposition 3.5: the inequality holds for an arbitrary real sequence $S : \mathbb{N} \to \mathbb{R}$.

---

## 4. The Coprime Euler Factor and Dirichlet-Series Factorization

While Theorem 3.4 already suffices to transfer two-sided growth bounds between $M$ and $S_B$, one-sided growth bounds on $S_B$ cannot be pushed through the oscillating Möbius inverse $M = h_B * S_B$ without losing sign control. Instead, the Lean formalization passes directly to the Dirichlet series of the increments of $S_B$ and isolates the coprime weight factor on $\operatorname{Re} s > 0$.

**Theorem 4.1 (Holomorphic non-vanishing factor and Dirichlet factorization).**  
*For $B \in \mathbb{N}$ and $s \in \mathbb{C}$, define*
$$L(g_B, s) := \sum_{n=1}^{\infty} \frac{g_B(n)}{n^s}, \qquad L(h_B, s) := \sum_{n=1}^{\infty} \frac{h_B(n)}{n^s}.$$
*Then:*
1. *Both $L(g_B, \cdot)$ and $L(h_B, \cdot)$ have abscissa of absolute convergence $\le 0$, hence converge absolutely and define holomorphic functions on $\{s \in \mathbb{C} : \operatorname{Re} s > 0\}$.*
2. *For every $s \in \mathbb{C}$ with $\operatorname{Re} s > 0$,*
   $$L(g_B, s)\, L(h_B, s) = 1, \qquad \text{and in particular } L(g_B, s) \neq 0.$$
3. *For every $s \in \mathbb{C}$ with $\operatorname{Re} s > 1$, the Dirichlet series of $(g_B * \mu)$ converges absolutely and equals*
   $$\sum_{n=1}^{\infty} \frac{(g_B * \mu)(n)}{n^s} = \frac{L(g_B, s)}{\zeta(s)}.$$

**Remark 4.2 (Uniformity in $B$ vs. the classical Euler product).**  
When $B \ge 1$, absolute convergence on $\operatorname{Re} s > 0$ gives the familiar Euler-product formula
$$L(g_B, s) = \prod_{p \nmid B} \left(1 - p^{-(s+1)}\right)^{-1} = \zeta(s+1) \prod_{p \mid B} \left(1 - p^{-(s+1)}\right),$$
and when $B = 0$, $L(g_0, s) = 1$. The Lean proof avoids splitting cases on $B = 0$ versus $B \ge 1$ and avoids constructing infinite Euler products altogether: because $|g_B(k)| \le 1/k$ and $|h_B(k)| \le 1/k$, both $L$-series converge absolutely on $\operatorname{Re} s > 0$, so Dirichlet multiplication (`LSeries_convolution'`) converts $g_B * h_B = \delta_1$ directly into $L(g_B, s) L(h_B, s) = 1$. Thus the factor $L(g_B, \cdot)$ neither introduces zeros nor cancels any zero of $\zeta$ anywhere in the half-plane $\operatorname{Re} s > 0$.

---

## 5. Half-Plane and Riemann Hypothesis Equivalences

All criteria in this section use Mathlib's `riemannZeta` and `RiemannHypothesis`.

### 5.1 Two-Sided Half-Plane and Energy Criteria

**Theorem 5.1 (Zero-free half-plane equivalences).**  
*Let $B \in \mathbb{N}$ and $\tfrac{1}{2} \le a < 1$. The following statements are equivalent:*
1. $\zeta(s) \neq 0$ *for all $s \in \mathbb{C}$ with $\operatorname{Re} s > a$.*
2. *For every $\varepsilon > 0$, $\mathcal{B}(S_B, a + \varepsilon)$ holds.*
3. *For every $\varepsilon > 0$, $\mathcal{B}(\mathscr{E}_B, 2a + \varepsilon)$ holds.*

Setting $a = \tfrac{1}{2}$ yields the Riemann Hypothesis equivalence for the coherent energy:

**Theorem 5.2 (Mertens and coherent-energy criteria for RH).**  
*Let $B \in \mathbb{N}$. Each of the following is equivalent to `RiemannHypothesis`:*
1. *The classical Mertens cancellation condition: for every $\varepsilon > 0$, $M(x) = O(x^{1/2+\varepsilon})$ as $x \to \infty$.*
2. *For every $\delta > 0$, there exists $C_\delta \ge 0$ such that for all $X \in \mathbb{N}$ with $X \ge 1$,*
   $$\mathscr{E}_B(X) \le C_\delta\, X^{1+\delta}.$$
3. *For any fixed $z_0 \in \mathbb{C}$ with $\operatorname{Re} z_0 > \tfrac{1}{2}$, the coherent energy bound (2) is also equivalent to the critical-line Euler-residual condition `ZetaLineEulerResidual` $z_0$.*
4. *Moreover, for every integer modulus $B \ge 1$, the measure-norm condition $\forall \delta > 0,\ \exists C_\delta \ge 0,\ \forall X \ge 1,\ \|D_{X,B}\|_\nu^2 \le C_\delta X^{1+\delta}$ (`coherent_energy_measure_growth_iff_RH`) is equivalent to `RiemannHypothesis`, and the corresponding fixed-strip bound $\|D_{X,B}\|_\nu^2 \le C_\varepsilon X^{2a+\varepsilon}$ (`fixed_strip_iff_coherent_energy_measure_power`) is equivalent to $\zeta(s) \neq 0$ on $\operatorname{Re} s > a$ for $\tfrac{1}{2} \le a < 1$.*

Here `ZetaLineEulerResidual` $z_0$ asserts that for every complex $z$ with $\operatorname{Re} z > \tfrac{1}{2}$, the compensated explicit-formula trace residual `traceResidual` in the `v2.6.4` Lean library—formed by the prime-power and real-place test integrals minus the pole terms at $\pm\tfrac{1}{2}$ and the spectral sum restricted to critical-line zeros `StripZetaZero 0` ($\operatorname{Re} \rho = \tfrac{1}{2}$) weighted by analytic multiplicity—converges to $0$ as the mollifier level $n \to \infty$. Note that `Re` notation matches Mathlib's `s.re`.

### 5.2 One-Sided Criteria

**Theorem 5.3 (One-sided half-plane and RH criteria).**  
*Let $B \in \mathbb{N}$ and fix a sign $\sigma \in \{1, -1\}$.*
1. *Let $0 \le a < 1$ and $C \ge 0$. If $\sigma S_B(n) \ge -C n^a$ for all sufficiently large $n \in \mathbb{N}$, then $\zeta(s) \neq 0$ for all $s \in \mathbb{C}$ with $\operatorname{Re} s > a$.*
2. *For every $\tfrac{1}{2} \le a < 1$,*
   $$\bigl(\forall s \in \mathbb{C},\ \operatorname{Re} s > a \implies \zeta(s) \neq 0\bigr) \iff \Bigl(\forall \varepsilon > 0,\ \exists C \ge 0,\ \forall^{\infty} n \in \mathbb{N},\ \sigma S_B(n) \ge -C n^{a+\varepsilon}\Bigr).$$
3. *In particular, taking $a = \tfrac{1}{2}$,*
   $$\mathrm{RiemannHypothesis} \iff \Bigl(\forall \varepsilon > 0,\ \exists C \ge 0,\ \forall^{\infty} n \in \mathbb{N},\ \sigma S_B(n) \ge -C n^{1/2+\varepsilon}\Bigr).$$

Note the contrast between the two criteria: `coherent_energy_growth_iff_RH` controls a sum of squares $\mathscr{E}_B(X) = \sum j(r) S_B(\lfloor X/r \rfloor)^2$, which automatically bounds both signs of $S_B$ via $S_B(X)^2 \le \mathscr{E}_B(X)$, whereas `rh_iff_one_sided_fourier_scalar` requires only a one-sided bound (either an upper bound $\sigma = -1$ or a lower bound $\sigma = +1$) on $S_B(n)$ itself.

### 5.3 Proof Architecture of the Equivalence Theorems

The Lean proofs combine three standard analytic mechanisms without any zero-density input:

1. *Zero-free half-plane $\implies$ two-sided bound:* Assuming $\zeta(s) \neq 0$ on $\operatorname{Re} s > a$ ($\tfrac{1}{2} \le a < 1$), $1/\zeta(s)$ is holomorphic there and satisfies polynomial-height bounds on narrower strips $\operatorname{Re} s \ge b > a$. Applying a smoothed Perron ramp integral with parameter $h = X^{-1}$ (in `mertens_power_bound_of_strip`) or $h = X^{-1/2}$ (in `mertens_power_bound_of_RH`) gives $M(n) = O_\varepsilon(n^{a+\varepsilon})$, which transfers to $S_B$ via `M_power_bound_iff_S` and to $\mathscr{E}_B$ via `energy_upper`.
2. *One-sided bound $\implies$ zero-free half-plane:* Define the step function $\widetilde{S}_B(x) := S_B(\lfloor x \rfloor)$. By partial summation and Theorem 4.1, for $\operatorname{Re} s > 1$,
   $$\int_1^\infty \widetilde{S}_B(x)\, x^{-(s+1)}\, dx = \frac{L(g_B, s)}{s\, \zeta(s)}.$$
   Since $S_B(n) = O(n)$, a one-sided eventual lower bound $\sigma S_B(n) \ge -C n^a$ extends to a global shifted positivity bound $\sigma \widetilde{S}_B(x) x^{-a} + K \ge 0$ for all $x > 1$. Write $R(s)$ for the analytic continuation of $(s-1)\zeta(s)$, with $R(1)=1$. Along the positive real axis $R$ is nonzero. The analytic reciprocal of zeta there is $(s-1)/R(s)$, with value zero at $1$. Thus $L(g_B,s)(s-1)/R(s)$ supplies the real-axis germ used in Landau’s Mellin-extension theorem. The resulting function $A$ is analytic on $\{s \in \mathbb{C} : \operatorname{Re} s > a\}$ and agrees with $L(g_B, s)/\zeta(s)$ on $\operatorname{Re} s > 1$. By analytic continuation on $\{s : \operatorname{Re} s > a\}$,
   $$R(s)\, A(s) = (s - 1)\, L(g_B, s) \qquad (\operatorname{Re} s > a).$$
   Since $L(g_B, s) \neq 0$ for $\operatorname{Re} s > 0$ (Theorem 4.1), no zero of $\zeta(s)$ can occur in $\operatorname{Re} s > a$ ($a \ge 0$).
3. *Completing the equivalences:* A two-sided bound $|S_B(n)| \le C n^{a+\varepsilon}$ trivially implies the corresponding one-sided bound, and for $\zeta$, having no zeros in $\operatorname{Re} s > \tfrac{1}{2}$ is equivalent to Mathlib's `RiemannHypothesis` via the functional equation.

### 5.4 Separation from Conditional Zero-Density Modules

**Remark 5.5 (Conditional rank-strip results).**  
Two auxiliary rank-strip theorems connect uniform long-rank power savings to the scalar under an explicit zero-density premise modeling Ingham’s estimate [Ingham 1940]. The proofs of Theorems 5.1–5.3 are independent of this premise.

---

## 6. Formal verification

### 6.1 Kernel replay and provenance

All formal modules were compiled against Lean 4.35.0 (commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`) and Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`, and replayed by an independent Lean 4.35.0 kernel checker (`--run`, `fullDependencyReplay := false`, `g1Excluded := true`). Every replay completed with `verdict: PASS`, zero partial or unsafe constants, and axiom dependencies strictly contained in `{propext, Classical.choice, Quot.sound}`:

| Formal Module | Audited Constants | Compile Time | Replay Time | Partial / Unsafe | Scope |
|---|---:|---:|---:|---:|---|
| `v2.6.4` (`Verified`) | `3,325` | `293.54 s` | `1,527.82 s` | `0` / `0` | Comment-scrubbed release (`1,074` theorems across `335` fragments): coprime inversion, squeeze, Euler factor, RH & fixed-strip criteria (`B : ℕ`), `ZetaLineEulerResidual`, conditional rank-strip extension |
| `CoherentEnergyMeasure` | `168` | `8.48 s` | `28.05 s` | `0` / `0` | Product Poisson measure $\nu$, inclusion–exclusion window ($B \ge 1$, plus $B = 91$), Gram kernel, orthogonal family $\Psi_r$, Parseval diagonalization $\|D_{X,B}\|_\nu^2 = \mathscr{E}_B(X)$ |
| `CoherentEnergyRHBridge` | `9` | `1.77 s` | `6.97 s` | `0` / `0` | Definitional concordance (`M`, `S`, `j`) with `v2.6.4` and $L^2(\nu)$-energy RH & fixed-strip equivalences ($B \ge 1$) |

Within `v2.6.4` (inheriting the provenance structure documented in `v2.6.3`), the October 2026 arithmetic-Fourier core (coprime inversion, growth transfer, coherent-energy bounds, coprime Euler factor, two-sided strip growth, Mertens converse, and one-sided RH criteria, together with the arithmetic Fourier shell) is cleanly separated from the conditional zero-density rank-strip extension (depending on `ZetaDensityPremise`) and auxiliary compensated-trace modules (Archimedean cutoff, compensated geometry, strip evaluation witnesses, spectral tail, relative resolvent, and scaled cutoff).

### 6.2 Statement review

By direct line inspection and replay cross-check, independent statement reviews verify that the principal equivalences in `v2.6.4` (Sections 3–5) and the definitions and headline statements of `CoherentEnergyMeasure` and `CoherentEnergyRHBridge` (against Proposition 2.5 and the RH and fixed-strip equivalences, for $B \ge 1$ and natural $X \ge 1$, review of 2026-11-23) match their mathematical statements and hypotheses, including the explicit $B \ge 1$ vs. $B = 0$ modulus boundary and exact equality `S_0(n) = M(n)`. Internal helper lemmas (`168 + 9` constants) in the measure and bridge modules, as well as auxiliary `v2.6.4` modules beyond the principal equivalences, remain covered by strict kernel replay only. Replay and statement review answer distinct questions: kernel replay verifies proof-term validity under Lean's trusted kernel, while statement review verifies mathematical meaning against the source definitions.

### 6.3 Shipped Edition Checksums (SHA-256)

Checksums below identify the companion files shipped directly in this `v0.3.3` writeup package:

- **Reader guide** (`README.md`, `8,816` B): `91246b12f0a1e592f0199eafaa20221255dc99bb6bed12e62ffb3687223b3f78`
- **Edition changelog** (`CHANGELOG_v0_3_2_to_v0_3_3.md`, `2,713` B): `5cf9dc25ac95d8010008a207a98bf8f2ed93973c949234e0dc18ec37c2aeaf98`
- **Edition verifier** (`verify_v0_3_3.py`, `22,516` B): `03c8db30008f6817fb2065ab65cd4964d2bdd309199721aaaa40116678649660`

The accompanying `SHA256SUMS.txt` manifest records the final digests of all six package items, including the three reading editions. External Lean-release, kernel-replay, and October 2026 finite-control digests are pinned in the edition verifier and summarized in the reader guide.

## 7. Prior Art and Related Work

To place both the mathematical construction and its Lean 4 formalization cleanly in the surrounding literature, we separate what was already known from what this paper and companion artifact contribute.

### 7.1 Analytic Prior Art: GCD Sums and Infinite-Polydisc Poisson Integrals

The covariance kernel underlying Proposition 2.5(1) is classical in the theory of GCD matrices and Dirichlet-series Hilbert spaces. Hedenmalm, Lindqvist, and Seip [1997] introduced the Hilbert space $\mathscr{H}^2$ of Dirichlet series via the Bohr lift to the infinite-dimensional polydisc, Lindqvist and Seip [1998] analyzed associated GCD quadratic forms, and Hilberdink [2009] linked spectral norms of arithmetic GCD matrices to $\Omega$-bounds for $\zeta(s)$. Building on this line of work, Aistleitner, Berkes, and Seip [2015] identified general GCD sums as Poisson integrals on the infinite polydisc evaluated at radial weights $(p^{-\alpha})$:
$$\sum_{k,\ell=1}^N \frac{\gcd(n_k, n_\ell)^{2\alpha}}{(n_k n_\ell)^\alpha} \quad (0 < \alpha \le 1) \qquad \longleftrightarrow \qquad \text{Proposition 2.5(1) at } \alpha = 1:\ \langle Z(d), Z(e) \rangle_\nu = \frac{\gcd(d, e)^2}{de}.$$

Against that backdrop, the contribution developed here enters after the $\alpha = 1$ Poisson kernel is fixed:
1. **Coprime Möbius-lift polynomial:** Combining the prime-phasor monomials $Z(n)$ with the Möbius lift $A_n$ and the inclusion–exclusion sieving window $w_{X,B}$ ($B \ge 1$) produces the finite trigonometric polynomial $D_{X,B}(\mathbf{z}) = \sum_{n \le X,\, (n,B)=1} w_{X,B}(n) A_n(\mathbf{z})$, whose monomial coefficients collapse exactly to the standard Mertens coefficients $M(X/d)$ (Proposition 2.2).
2. **Gram–Schmidt diagonalization:** Applying explicit prime-power Gram–Schmidt modes $\Psi_r = \prod_{p^a \parallel r} (z_p^a - p^{-1} z_p^{a-1})$ with orthogonal norms $\langle \Psi_r, \Psi_s\rangle_\nu = \mathbf{1}_{r=s} j(r)$ ($j(r) = \prod_{p \mid r}(1 - p^{-2})$) collapses the $L^2(\nu)$ squared norm directly to the coherent energy $\mathscr{E}_B(X) = \|D_{X,B}\|_\nu^2 = \sum_{r \le X,\, (r,B)=1} j(r)\, S_B(\lfloor X/r\rfloor)^2$ (Proposition 2.5).
3. **Equivalences for RH and zero-free strips:** Coupling Proposition 2.5 with the exact coprime Dirichlet inversion $g_B * h_B = \delta_1$ and non-vanishing Euler factor $L(g_B, s)$ establishes bidirectional two-sided and Landau-type one-sided equivalences with $\mathrm{RH}$ and zero-free half-planes across every fixed modulus $B$ (Theorems 5.1–5.3 and `CoherentEnergyRHBridge`).

### 7.2 Formalization Prior Art in Lean 4

In Lean 4 and Mathlib, foundational definitions of $\zeta(s)$, Dirichlet $L$-functions, and `RiemannHypothesis` were formalized by Loeffler and Stoll [2025]. Several Lean projects investigate alternative RH formulations: Gomes and Kontorovich (`AlexKontorovich/Lean-RH`) formalized a Dirichlet-$\eta$ equivalence, and `KXKXKXK/riemann-hypothesis-lean` formalizes critical-strip and zero-counting equivalences. Closer to the Mertens lineage, Mathlib4 Pull Request `#46101` (`leanprover-community/mathlib4#46101`, opened 16 November 2026 and closed unmerged on 17 November 2026 under Mathlib's AI-use policy) formalized specifically the **one-way forward implication** `RiemannHypothesis.of_mertens_isBigO` ($M(x) = O_\varepsilon(x^{1/2+\varepsilon}) \implies \mathrm{RH}$), without the converse direction, without general coprime moduli $B$ or $S_B$, and without one-sided Landau-type criteria.

To our knowledge—based on public GitHub and arXiv searches as of November 2026, which establish only what was located and cannot prove global non-existence—no prior machine-checked formalization covers the bidirectional Mertens equivalence (`mertens_cancellation_iff_RH`), Landau-type one-sided criteria (`rh_iff_one_sided_fourier_scalar`), the general-modulus coprime inversion $(g_B, h_B)$ and scalar $S_B$, or the end-to-end Poisson-measure energy equivalence (`coherent_energy_measure_growth_iff_RH`, which has passed strict kernel replay and independent statement review of its definitions and headline statements on 2026-11-23, while internal helper lemmas are covered by kernel replay).

## 8. Scope, Limitations, and Open Directions

1. **A verified equivalence dictionary, not a proof of RH.**  
   Every main theorem in Sections 3–5 proves an "if and only if" (or conditional implication) between $\mathrm{RH}$ / a zero-free half-plane and a growth bound on $S_B$ or $\mathscr{E}_B$. Obtaining an unconditional estimate $\mathscr{E}_B(X) \ll_\delta X^{1+\delta}$ or $\sigma S_B(n) \ge -C_\varepsilon n^{1/2+\varepsilon}$ is as hard as proving the Riemann Hypothesis itself.
2. **Relation to classical literature.**  
   In analytic content, the two-sided and one-sided criteria belong to the classical lineage of Mertens [1897], Landau [1905], and Littlewood [1912], while the infinite-polydisc Poisson covariance stands in the GCD-sum lineage culminating in Aistleitner–Berkes–Seip [2015] (Section 7). This work combines that Poisson covariance with the coprime Möbius lift $D_{X,B}$, orthogonal system $\{\Psi_r\}$, energy reduction $\mathscr{E}_B(X)$, and a unified, kernel-replayed Lean 4 formalization over Mathlib.
3. **Open formalization and computational directions.**  
   - Formalize the analytic closed-span complement example ($\overline{z_p} - p^{-1} \perp Z(n)$ in $L^2(\Omega, \nu)$) noted after Proposition 2.5.
   - Extend independent statement review beyond the principal equivalences of `v2.6.4` and the headline statements of `CoherentEnergyMeasure` / `CoherentEnergyRHBridge` to auxiliary compensated-trace modules and internal helper lemmas.
   - Implement the interactive arithmetic-energy viewer extension left open in the October 2026 specification.

---

## Acknowledgments and Contributions

`saphir` originated the arithmetic Fourier construction documented in Section 2—the prime-phasor lifts $Z(n)$ and $A_N$, the inclusion–exclusion window $w_{X,B}$, the product Poisson measure $\nu$, the orthogonal system $\{\Psi_r\}$, the scalar $S_B$, its exact Möbius inverse, and the coherent-energy diagonalization—and directed the October 2026 finite rational verification suite (run under `saphir`'s direction). Under `saphir`'s direction: **Codex** authored the core Lean 4 formalization (coprime inversion, energy bounds, Euler factor, RH and zero-free strip equivalences, and compensated-trace development); **Claude Fable** performed independent compilation and the initial statement audit; **Claude Opus** produced the `v0.1` manuscript draft, the `v2.6.2`/`v2.6.3` renames and comment pass, the `v0.2.1` edition audit, the prior-art literature review (identifying Aistleitner–Berkes–Seip [2015] and Mathlib4 PR `#46101`), the `v0.3.1` independent statement review of `v2.6.4`, `CoherentEnergyMeasure`, and `CoherentEnergyRHBridge`, and the simplified companion edition (`v0.1`) whose opening and Section 1 are adapted here; **ChatGPT 6.2 (Astra/Sol)** contributed analytical reviews, mathematical design notes on the Fourier-shell and dyadic constructions, and the editorial reviews followed by the simplified edition and this revision (opening with the theorem, leading with the energy squeeze and the worked examples), as well as review of the prior-art comparison and publication scope; and **Gemini** prepared the comment-scrubbed `v2.6.4` assembly and kernel replay, formalized and replayed `CoherentEnergyMeasure` and `CoherentEnergyRHBridge`, and authored the `v0.2`, `v0.3`, `v0.3.1`, `v0.3.2`, and `v0.3.3` writeup revisions. Responsibility for verifying mathematical correctness beyond the scope described in Section 6 remains human; no external peer review is implied.

---

## References

1. F. Mertens, *Über eine zahlentheoretische Funktion*, Sitzungsber. Akad. Wiss. Wien IIa **106** (1897), 761–830.
2. E. Landau, *Über einen Satz von Tschebyschef*, Math. Ann. **61** (1905), 527–550.
3. J. E. Littlewood, *Quelques conséquences de l'hypothèse que la fonction $\zeta(s)$ de Riemann n'a pas de zéros dans le demi-plan $\mathcal{R}(s) > 1/2$*, C. R. Acad. Sci. Paris **154** (1912), 263–266.
4. A. E. Ingham, *On the estimation of $N(\sigma, T)$*, Quart. J. Math. Oxford Ser. **11** (1940), 201–202. doi:10.1093/qmath/os-11.1.201.
5. E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., revised by D. R. Heath-Brown, Clarendon Press, Oxford, 1986.
6. H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I. Classical Theory*, Cambridge Studies in Advanced Mathematics, Vol. 97, Cambridge University Press, Cambridge, 2007.
7. The mathlib Community, *The Lean Mathematical Library*, in Proc. 9th ACM SIGPLAN Int. Conf. on Certified Programs and Proofs (CPP 2020), ACM, 2020, pp. 367–381. doi:10.1145/3372885.3373824.
8. L. de Moura and S. Ullrich, *The Lean 4 Theorem Prover and Programming Language*, in *Automated Deduction – CADE 28*, Lecture Notes in Computer Science, Vol. 12699, Springer, Cham, 2021, pp. 625–635. doi:10.1007/978-3-030-79876-5_37.
9. H. Hedenmalm, P. Lindqvist, and K. Seip, *A Hilbert space of Dirichlet series and systems of dilated functions in $L^2(0,1)$*, Duke Math. J. **86** (1997), no. 1, 1–37 (arXiv:math/9512211).
10. P. Lindqvist and K. Seip, *Note on some greatest common divisor matrices*, Acta Arith. **84** (1998), 149–154.
11. T. Hilberdink, *An arithmetical mapping and applications to $\Omega$-results for the Riemann zeta function*, Acta Arith. **139** (2009), 341–367.
12. C. Aistleitner, I. Berkes, and K. Seip, *GCD sums from Poisson integrals and systems of dilated functions*, J. Eur. Math. Soc. (JEMS) **17** (2015), no. 6, 1517–1546. doi:10.4171/JEMS/537 (arXiv:1210.0741).
13. D. Loeffler and M. Stoll, *Formalizing zeta and $L$-functions in Lean*, Ann. Formalized Math. **1** (2025), 43–56, doi:10.46298/afm.15328 (arXiv:2503.00959).
14. B. Gomes and A. Kontorovich, *Lean-RH* (Lean 4 formalization of Riemann Hypothesis formulations including Dirichlet-$\eta$ equivalences), GitHub repository `AlexKontorovich/Lean-RH`.
15. `KXKXKXK/riemann-hypothesis-lean` (Lean 4 formalization of critical-strip and zero-counting Riemann Hypothesis equivalences), GitHub repository.
16. Mathlib4 Pull Request `#46101` (`leanprover-community/mathlib4#46101`, opened 16 Nov 2026; closed unmerged 17 Nov 2026 under Mathlib's AI-use policy), proving `RiemannHypothesis.of_mertens_isBigO`.
