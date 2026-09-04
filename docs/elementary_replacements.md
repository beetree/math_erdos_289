# Erdős 289: elementary replacements for the two remaining deep inputs

**Status.** This is a new mathematical replacement argument, with independent internal audits of the covering lemma, the signed correction fibers, their simultaneous separation, and the downstream estimates. It has not yet been translated into Lean. The existing compilation and axiom reports are those reported by the project maintainer, on Lean and Mathlib v4.34.0-rc2.

The conclusion of this investigation is stronger than merely narrowing the two external statements:

- The CFHMPSV structure input can be replaced by a finite weighted Fourier argument and the divisor bound. The original summand budget is preserved.
- The Bourgain–Garaev input can be avoided by allowing correction pairs on either side of $qm$, widening the multiplier range by a factor $q^{o(1)}$, and choosing compatible orientations by finite counting.
- The second change bypasses inverse equidistribution altogether, so this proof path also has no use for the Erdős–Turán axiom.

The already discharged Liu–Sawhney, Mertens, and divisor-bound statements suffice as literature inputs. The additional arguments below are to be proved as finite or asymptotic lemmas, not installed as replacement axioms. Neither the general Bourgain–Garaev theorem nor the general CFP structure theorem is proved here.

All estimates and cardinality comparisons below take place in the real numbers, with natural cardinalities coerced to reals. Integer divisions are used only when exact divisibility has been established. An integer is *strictly $q$-powersmooth* if every prime power dividing it is strictly smaller than $q$; for integral $q$ this is the existing powersmooth predicate at cutoff $q-1$.

## 1. Elementary inverse covering with a prescribed summand budget

This uses the same finite Fourier-product mechanism as Martin's Lemmas 10–11, but replaces his restricted-factor divisor estimate by the already proved uniform divisor bound and introduces weights to enforce a smaller subset size. The weighted argument is given in full below; it is not being assumed as a published theorem. [Martin, *Denser Egyptian fractions*, Lemmas 10–11](https://www.math.ubc.ca/~gerg/papers/downloads/DrEF.pdf).

### Lemma C1: finite divisor dispersion

Let $q\ge2$ be an integer, let $W\ge1$ be real, and let $I$ be a finite set of positive integers at most $W$, each coprime to $q$. Write $m=|I|$. Suppose $D\ge1$ satisfies

$$
\tau(n)\le D\qquad(1\le n\le Wq).
$$

For every integer $1\le h<q$ and every real $0<\Delta<1/2$,

$$
\#\left\{i\in I:
\left\|\frac{h i^{-1}}q\right\|_{\mathbb R/\mathbb Z}<\Delta
\right\}
\le (2W\Delta+1)D.
\tag{C1}
$$

The inverse is taken modulo $q$; the norm denotes distance to the nearest integer.

**Proof.** Choose the centered representative $r_i\in(-q/2,q/2]$ of $h i^{-1}$. For a counted $i$,

$$
i r_i=h+qz_i,\qquad |r_i|<\Delta q.
$$

The signed product on the left is nonzero: otherwise $h\equiv0\pmod q$. Its absolute value is below $W\Delta q$, and $z_i$ belongs to the real interval

$$
(-W\Delta-h/q,\ W\Delta-h/q).
$$

There are at most $2W\Delta+1$ integer possibilities for $z_i$. For each, $i$ is a positive divisor of the nonzero integer $|h+qz_i|\le Wq$, giving at most $D$ choices. Positive and negative products have already been counted together; no extra factor of two is required. This proof includes nonunit frequencies $h$ and does not require $q$ to be a prime power.

If $m\ge4D$, set

$$
\Delta=\frac{m}{8WD}.
\tag{C2}
$$

Since $m\le W$, we have $0<\Delta\le1/8$. Equation (C1) bounds the exceptional count by

$$
(2W\Delta+1)D=m/4+D\le m/2.
$$

Thus at least $m/2$ phases are at distance at least $\Delta$ from zero for every nonzero frequency.

### Lemma C2: finite weighted Fourier covering

Let $q\ge2$ be an integer, and let $a_i\in\mathbb Z/q\mathbb Z$, indexed by a finite set $I$ of size $m\ge1$. Suppose $0<\Delta\le1/2$ and, for every $1\le h<q$, at least $m/2$ indices satisfy $\|h a_i/q\|_{\mathbb R/\mathbb Z}\ge\Delta$. For an integer $1\le s\le m$, assume

$$
s\Delta^2\ge2\log(4q).
\tag{C3}
$$

Then every residue modulo $q$ is the sum of the $a_i$ over a subset of $I$ having at most $s$ members.

**Proof using only finite sums.** Put

$$
\lambda=\frac{s}{4m},\qquad
w(A)=\lambda^{|A|}(1-\lambda)^{m-|A|}
\quad(A\subseteq I).
$$

The weights are positive and sum to one by finite product expansion. Define

$$
F_h=\prod_{i\in I}(1-\lambda+\lambda e_q(ha_i)).
$$

Expanding this product gives

$$
F_h=\sum_{A\subseteq I}w(A)e_q\left(h\sum_{i\in A}a_i\right).
$$

For a phase $\theta$ at distance at least $\Delta$,

$$
\begin{aligned}
|1-\lambda+\lambda e(\theta)|^2
&=1-4\lambda(1-\lambda)\sin^2(\pi\theta)\\
&\le \exp(-16\lambda(1-\lambda)\Delta^2).
\end{aligned}
$$

Here $|\sin(\pi\theta)|\ge2\|\theta\|_{\mathbb R/\mathbb Z}$. Since $\lambda\le1/4$, the norm of this factor is at most $\exp(-4\lambda\Delta^2)$; every other factor has norm at most one. Therefore, for $h\ne0$,

$$
|F_h|\le \exp(-2\lambda m\Delta^2)
=\exp(-s\Delta^2/2)\le\frac1{4q}.
\tag{C4}
$$

For a residue $r$, let $W_r$ be the real total weight of subsets summing to $r$. Finite character orthogonality gives the complex identity

$$
W_r=\frac1q\sum_{h=0}^{q-1}e_q(-hr)F_h.
$$

Using $F_0=1$ and taking norms yields the real inequalities

$$
\left|W_r-\frac1q\right|
\le\frac{q-1}{4q^2},
\qquad W_r\ge\frac3{4q}.
\tag{C5}
$$

The total weight of subsets exceeding the size budget is bounded by

$$
\begin{aligned}
\sum_{|A|>s}w(A)
&\le2^{-s}\sum_{A\subseteq I}2^{|A|}w(A)\\
&=2^{-s}(1+\lambda)^m\\
&\le \exp\bigl((1/4-\log2)s\bigr)\\
&\le e^{-s/4}.
\end{aligned}
\tag{C6}
$$

Use $\log2\ge1/2$. Since $\Delta^2\le1/4$, (C3) implies $s\ge8\log(4q)$, so (C6) is at most $(4q)^{-2}\le1/(4q)$. The subsets summing to $r$ and having size at most $s$ consequently have total weight at least $1/(2q)>0$. One exists.

This needs no probability space, sampling theorem, or concentration theorem. The identities are expansions over a finite powerset.

### Theorem C3: finite inverse-covering criterion

Under the hypotheses of Lemma C1, suppose $m\ge4D$ and $1\le s\le m$. Then

$$
\boxed{\quad
\frac{s m^2}{64W^2D^2}\ge2\log(4q)
\quad\Longrightarrow\quad
\forall r\ \exists A\subseteq I:
|A|\le s,\quad \sum_{i\in A}i^{-1}=r\pmod q.
\quad}
\tag{C7}
$$

Apply Lemma C2 with (C2).

### Corollary C4: stronger replacement for the existing Lemma 3

For every fixed $0<\varepsilon<1$ and fixed $C\ge1$, there exists $q_0$ such that, for every integer $q\ge q_0$ and every

$$
I\subseteq[1,Cq^\varepsilon]\cap\mathbb N,\qquad
(i,q)=1\ (i\in I),\qquad |I|\ge q^{7\varepsilon/8},
$$

every residue modulo $q$ is a sum of inverses of at most

$$
s=\lfloor q^{\varepsilon/2}\rfloor
$$

distinct members of $I$.

**Proof.** The discharged divisor estimate implies, for sufficiently large $q$,

$$
\tau(n)\le q^{\varepsilon/32}
\qquad(1\le n\le Cq^{1+\varepsilon}).
\tag{C8}
$$

To derive the uniformity in $n$, apply the eventual divisor bound at exponent $\varepsilon/[64(1+\varepsilon)]$. Above its threshold use $n^\eta\le C^\eta q^{\varepsilon/64}$; below it absorb the maximum of the finitely many divisor counts. This proves (C8) after enlarging $q_0$.

Take $W=Cq^\varepsilon$ and $D=q^{\varepsilon/32}$ in (C7). For large $q$, $m\ge4D$, $1\le s\le m$, and $s\ge q^{\varepsilon/2}/2$. Hence

$$
\frac{s m^2}{64W^2D^2}
\ge \frac{q^{3\varepsilon/16}}{128C^2}
>2\log(4q).
\tag{C9}
$$

This proves the corollary. The original Lemma 3 is the case $C=2$ with its additional lower-endpoint restriction. The correction construction below uses $C=8$. Both keep the original summand budget. In particular, the CFP theorem and the GAP argument are unnecessary for either version.

## 2. Signed correction fibers without inverse equidistribution

Fix $0<\varepsilon<1$, and write $M=q^\varepsilon$. Define the finite divisor envelope

$$
V(q)=\max_{1\le n\le\lceil25q^{1+\varepsilon}\rceil}\tau(n),
\qquad
E(q)=V(q)^2\log q,\qquad
R(q)=\frac{q^\varepsilon}{E(q)}.
\tag{F1}
$$

We use these definitions only for sufficiently large $q\ge4$. The divisor bound implies $V(q)=q^{o(1)}$ and $E(q)=q^{o(1)}$. In particular, $R(q)=q^{\varepsilon-o(1)}$ tends to infinity. The logarithm in $E(q)$ avoids needing a separate proof that $V(q)$ tends to infinity.

### Lemma F1: many individually valid signed pairs

For all sufficiently large prime powers $q=p^a$, one can find at least

$$
N_q\ge\frac{M}{8V(q)}
\tag{F2}
$$

distinct integers $m$, each with a chosen sign $\sigma_m\in\{-1,+1\}$, such that

$$
R(q)\le m\le8M,\qquad p\nmid m,
\qquad qm+\sigma_m\text{ is strictly }q\text{-powersmooth}.
\tag{F3}
$$

The pair $\{qm,qm+\sigma_m\}$ is either $[y-1,y]$ or $[y,y+1]$ for some positive multiple $y$ of $4$. Within a fixed fiber $q$, the chosen pairs have distinct such multiples $y$. The largest prime power dividing either endpoint is exactly $q$.

The lemma does not yet assert compatibility between different fibers; Lemma F2 supplies that.

**Step 1: the initial parameters.** Let

$$
\mathcal T_q=\{t\in[M,2M]\cap\mathbb N:(t,2p)=1\}.
$$

Elementary coprime counting gives $|\mathcal T_q|\ge M/3-O(1)$ uniformly in $p$; when $p=2$ the density is $1/2$. Take $q$ sufficiently large that $q>8M$.

**Step 2: complementary inverses remove the condition $p\mid m$.**

If $q=2^a\ge4$, take $1\le r<q$ with $rt\equiv1\pmod q$, and define

$$
m_+=\frac{rt-1}{q},\qquad m_-=t-m_+.
$$

Then

$$
rt=qm_++1,\qquad
(q-r)t=qm_--1,\qquad
m_++m_-=t.
\tag{F4}
$$

Both multipliers are positive and less than $2M$ for sufficiently large $q$. Since $t$ is odd, exactly one is odd. Choose that multiplier and its corresponding pair. Its endpoint $qm$ is a multiple of $4$.

If $p$ is odd, take $1\le r<q$ with $4rt\equiv-1\pmod q$, and define

$$
m_+=\frac{4rt+1}{q},\qquad m_-=4t-m_+.
$$

Then

$$
4rt=qm_+-1,\qquad
4(q-r)t=qm_-+1,\qquad
m_++m_-=4t.
\tag{F5}
$$

Both multipliers are positive and below $8M$. Because $p\nmid4t$, they cannot both be divisible by $p$. Choose a multiplier not divisible by $p$. Its neighboring endpoint $qm+\sigma_m$ is a multiple of $4$.

Fix a deterministic choice if both odd-prime alternatives are admissible. No distribution of $r$ in an interval is asserted or needed: its entire canonical range $1\le r<q$ is used.

**Step 3: discard unsuitable $t$.** Put

$$
\eta=\varepsilon/10000,\qquad T=q^{\varepsilon-\eta}.
$$

First discard $t$ with a prime factor exceeding $T$. The union bound and Mertens give

$$
\#\{\text{these }t\}
\le2M\sum_{T<\ell\le2M,\ \ell\ {\rm prime}}\frac1\ell
=\left(2\log\frac{\varepsilon}{\varepsilon-\eta}+o(1)\right)M
<M/1000
\tag{F6}
$$

for all sufficiently large $q$.

Every chosen neighbor has the form $ft$ or $4ft$, with $1\le f<q$, and is at most $8qM$. Suppose a prime power $u=\ell^b\ge q$ divides that neighbor. If $\ell\nmid4t$, then $u\mid f$, impossible since $f<q\le u$. Therefore $\ell\mid4t$, so $\ell\le T$ for a surviving $t$; also $\ell\ne p$ because the neighbor is $\pm1$ modulo $q$.

There are $O_\varepsilon(T\log q)$ possible powers $u$ with base at most $T$ and $q\le u\le8qM$. For each $u$ and each sign, the congruence

$$
qm\equiv\pm1\pmod u
$$

has at most one solution in $1\le m\le8M$, since $(q,u)=1$ and $8M<q\le u$. For a fixed signed multiplier, every corresponding $t$ divides $qm\pm1$, giving at most $V(q)$ choices. The total loss from these large powers is consequently

$$
O_\varepsilon(TV(q)\log q)=o(M).
\tag{F7}
$$

**Threshold detail:** for (F7), use the divisor bound strongly enough that $V(q)\le q^{\eta/4}$ and $\log q\le q^{\eta/4}$ eventually. The coarser exponent $\varepsilon/32$ used for covering alone is not sufficient here. These stronger estimates follow from the same discharged divisor theorem.

Finally discard chosen multipliers below $R(q)$. For each $m$ there are at most $2V(q)$ possible preimages $t$, accounting for both signs. Thus this loss is at most

$$
2(R(q)+1)V(q)
=\frac{2M}{V(q)\log q}+2V(q)=o(M).
\tag{F8}
$$

The remaining number of $t$ is at least $M/4$. Since each multiplier has at most $2V(q)$ preimages, there are at least $M/(8V(q))$ distinct multipliers. Choose one pair for each. This proves (F2)–(F3).

**Step 4: the multiple-of-four locations and the labels.** Call the multiple $y$ of $4$ associated to a pair its *slot*. In the even case $y=qm$; in the odd case $y=qm\pm1$ is the smooth neighbor. Two distinct multipliers in an even fiber give distinct slots. Equality of slots for two distinct multipliers in an odd fiber would force $q\mid2$, impossible for large odd $q$. Hence slots are distinct within each fiber.

Since $m<q$ and $p\nmid m$, the largest prime power dividing $qm$ is exactly $q$. The other endpoint is strictly $q$-powersmooth. Therefore the largest prime power occurring in either endpoint is exactly the fiber label $q$.

### Lemma F2: simultaneous nonadjacency for a finite set of fibers

There exists an integer $L_0$ such that for every integer $L\ge L_0$ and every integer upper cutoff $H\ge L$, one can thin the fibers of Lemma F1 for all prime powers $L<q\le H$ simultaneously so that

$$
|I_q|\ge q^{7\varepsilon/8},
\tag{F9}
$$

and every retained pair, over every such $q$, is distinct and nonadjacent to every other retained pair.

**Finite counting proof.** Enlarge $L_0$ until

$$
N_q\ge q^{15\varepsilon/16},
\qquad
N_q/4\ge q^{7\varepsilon/8}.
\tag{F10}
$$

These follow from (F2) and $V(q)=q^{o(1)}$.

Only finitely many slots occur for labels $q\le H$. Consider all equally weighted assignments of a bit to each slot. A bit chooses either the left pair $[y-1,y]$ or the right pair $[y,y+1]$. Retain a candidate if it agrees with its slot's bit.

For a fixed fiber, its $N_q$ slots are distinct. Let $B_q$ be the number retained. Expanding a product over these bits gives the finite average identity

$$
\mathbb E[2^{-B_q}]=(3/4)^{N_q}.
$$

Therefore

$$
\Pr(B_q<N_q/4)
\le 2^{N_q/4}(3/4)^{N_q}
<(9/10)^{N_q}.
\tag{F11}
$$

The last strict inequality follows from $2^{1/4}<6/5$. The symbols $\Pr$ and $\mathbb E$ here mean cardinality divided by the size of a finite bit cube and its normalized finite sum; no measure-theoretic or infinite probability construction is needed.

Choose $L_0$ still larger so that, for every integer $q>L_0$,

$$
(9/10)^{q^{15\varepsilon/16}}\le\frac1{2q^2}.
$$

A union bound over the finitely many labels has total failure probability at most

$$
\frac12\sum_{q=L+1}^{H}\frac1{q^2}
\le\frac12\sum_{q=L+1}^{H}\frac1{q(q-1)}
<\frac1{2L}<1.
\tag{F12}
$$

Thus a single assignment retains at least $N_q/4$ candidates in every fiber.

At distinct slots $y<z$, both multiples of $4$, the earlier pair ends at most at $y+1$ and the later starts at least at $z-1\ge y+3$. Hence there is an omitted integer between them. At a common slot only the chosen orientation survives. Two different fiber labels cannot supply that same oriented pair, because its largest prime-power divisor would have to equal both labels. Within a fiber slots were already distinct. This proves all separation and distinctness claims.

### Replacement for displays (2.1)–(2.2)

Delete the requirement that the inverse lie in $[3q/10,7q/20]$ and delete the four equidistribution counts. The substitute is the explicit chain

$$
|\mathcal T_q|\ge M/3-O(1)
\ \longrightarrow\
\#\{\text{surviving }t\}\ge M/4
\ \longrightarrow\
N_q\ge M/(8V(q))
\ \longrightarrow\
|I_q|\ge N_q/4\ge q^{7\varepsilon/8}.
\tag{F13}
$$

The resulting multipliers satisfy $R(q)\le m\le8q^\varepsilon$ and have a sign attached. Applying Corollary C4 with $C=8$ gives the same budget $\lfloor q^{\varepsilon/2}\rfloor$ for covering residues.

The original universal equidistribution proposition is not proved by this construction. Its use has been removed.

## 3. The enlarged possible endpoint set is still sparse enough

For a fixed cutoff $L$, define the deterministic superset

$$
\mathcal P^*=
\bigcup_{\substack{q>L\\q\ {\rm prime\ power}}}
\ \bigcup_{\substack{m\in\mathbb N\\R(q)\le m\le8q^\varepsilon}}
\{qm-1,qm,qm+1\}.
\tag{D1}
$$

It is independent of all subsequent choices of fibers or orientations.

### Lemma D1: density zero

$$
|\mathcal P^*\cap[1,X]|=o(X).
\tag{D2}
$$

**Proof.** Fix any $0<\zeta<\varepsilon$. Eventually $E(q)\le q^\zeta$. Exceptional bounded labels contribute only finitely many endpoints. For the remaining labels, an endpoint at most $X$ implies

$$
q^{1+\varepsilon-\zeta}\le qm\le X+1,
\qquad
q\le Z=(X+1)^{1/(1+\varepsilon-\zeta)}.
$$

Put $Y=X^{1/(1+\varepsilon)}$. Labels $q\le Y$ contribute

$$
O\left(\sum_{q\le Y,\ q\ {\rm prime\ power}}q^\varepsilon\right)
=O(X/\log X).
$$

Use the same elementary prime-power counting estimate already used in the manuscript. For $Y<q\le Z$, bound the possible multipliers by $(X+1)/q+1$. Their endpoint contribution is at most

$$
3(X+1)\sum_{\substack{Y<q\le Z\\q\ {\rm prime\ power}}}\frac1q+3Z.
$$

For prime labels, Mertens gives the limit

$$
\sum_{Y<p\le Z}\frac1p
=\log\frac{1+\varepsilon}{1+\varepsilon-\zeta}+o(1).
$$

Higher prime powers contribute $o(1)$, since

$$
\sum_{\substack{p^a>Y\\a\ge2}}p^{-a}=O(Y^{-1/2}).
$$

For the last estimate, split bases at $\sqrt Y$: each geometric tail for $p\le\sqrt Y$ is at most $2/Y$, and the tails for $p>\sqrt Y$ sum to at most $2\sum_{n>\sqrt Y}n^{-2}$. Finally $Z=o(X)$ because $\zeta<\varepsilon$. It follows that

$$
\limsup_{X\to\infty}\frac{|\mathcal P^*\cap[1,X]|}{X}
\le3\log\frac{1+\varepsilon}{1+\varepsilon-\zeta}.
$$

Let $\zeta$ decrease to zero. This proves (D2). Equivalently, given $\kappa>0$, first choose $\zeta$ making the displayed constant less than $\kappa/2$, and then choose $X$ large enough for the remaining errors. No uniformity in $\zeta$ is required.

The old rate $O(X/\log X)$ must therefore be replaced by $o(X)$ for this larger set. Every later use only needs density zero.

## 4. Rewritten descent and downstream displays

Keep the assembly parameters

$$
\varepsilon=1/10,\qquad
s(q)=\lfloor q^{1/20}\rfloor,\qquad
Q=\lfloor k^{4/5}\rfloor.
$$

The auxiliary pairs can still be chosen on the original grid with starts divisible by four and both endpoints $(q/2)$-powersmooth. Their supply constant remains

$$
1/4-\log(11/10)>0.
$$

Delete neighborhoods of the enlarged $\mathcal P^*$ before choosing them. Lemma D1 makes this deletion $o(q^{11/10})$. Earlier auxiliary endpoints contribute only $O(q^{21/20})=o(q^{11/10})$, just as before. Thus the existing auxiliary construction and its predetermined stage count survive.

After $H$ is known, choose the compatible fibers for $L<q\le H$ by Lemma F2. The auxiliary families and core were protected against all of $\mathcal P^*$, so their validity is independent of this finite choice.

For a selected sign $\sigma\in\{-1,+1\}$, use the pair mass

$$
w_\sigma(qm)=\frac1{qm}+\frac1{qm+\sigma}.
$$

In the rationals with denominators coprime to $p$,

$$
q\,w_\sigma(qm)
=\frac1m+\frac q{qm+\sigma}
\equiv m^{-1}\pmod q.
\tag{D3}
$$

Thus the same inverse-subset congruence cancels the complete current $p$-power. Every introduced prime power is strictly below $q$: this holds for $m$ because $m<q$, for its neighbor by (F3), and for auxiliary endpoints by their existing powersmoothness condition. Strictly below $q$ is sufficient; the stronger cutoff $q/2$ is unnecessary for actual correction neighbors.

**Mass correction for minus pairs.** For $qm\ge2$,

$$
w_{-1}(qm)\le\frac3{qm},
\qquad
w_{+1}(qm)\le\frac2{qm}\le\frac3{qm}.
$$

By $m\ge q^\varepsilon/E(q)$ and $E(q)=q^{o(1)}$, enlarge $L$ until $E(q)\le q^{1/40}$ for all $q>L$. A full stage of exactly $s(q)$ pairs, including auxiliary padding, then costs at most

$$
3s(q)E(q)q^{-11/10}
\le3q^{-41/40}.
\tag{D4}
$$

Consequently the replacement for the total-mass estimate is

$$
3\sum_{n>L}n^{-41/40}
\le120L^{-1/40}.
\tag{D5}
$$

Choose $L$ so that this is below $\delta/16$, where the manuscript keeps $\delta=1/1000$.

The remaining changed and unchanged estimates are:

| Quantity | Revised estimate |
|---|---|
| Possible correction endpoint set | $|\mathcal P^*\cap[1,X]|=o(X)$ |
| Auxiliary endpoint set | $|\mathcal F^*\cap[1,X]|=O(X^{21/22})$ |
| Protected union $\mathcal U=\mathcal P^*\cup\mathcal F^*$ | $|\mathcal U\cap[1,X]|=o(X)$ |
| Deleted core parameters | $o(Q)$ for fixed $K,B$ |
| Predetermined correction count | $C_H\le H^{21/20}=O(k^{21/25})$ |
| Largest correction or auxiliary endpoint | $\le8H^{11/10}+1=O(k^{22/25})=o(k)$ |
| Whole correction mass | $\le120L^{-1/40}$ |

The core definitions $K=\operatorname{lcm}(1,\ldots,L)$, $B=4^{j_0}$, $H=KBQ+2$ stay as before, with a possibly enlarged constant $L$. Density zero of $\mathcal U$ is enough to delete only $o(Q)$ core parameters; $K,B$ are fixed before $Q$ tends to infinity.

The main pairs, their spacing-three grid, the ten near bands, the far band $[4k,20k]$, and their interpolation are unchanged. All correction endpoints still lie below the first main band for sufficiently large $k$. The exact count remains

$$
(k-R-C_H)+R+C_H=k.
$$

The final intervals still have two or three members, are nonadjacent, and have endpoints at most $20k$. No change to the terminal statement or its interval conventions is needed.

## 5. Statements of faithfulness and dependency changes

### Covering lemma

The exact original sparse-covering statement can be retained and proved from Lemmas C1–C2. For the new correction construction, use Corollary C4 with $C=8$: the input is a finite set of positive integers at most $8q^\varepsilon$, each a unit modulo $q$, with cardinality at least $q^{7\varepsilon/8}$. The conclusion is an actual subset, not a multiset, of cardinality at most $\lfloor q^{\varepsilon/2}\rfloor$, whose inverses sum to the prescribed residue modulo the full modulus $q$.

The weighted powerset proof includes distinctness and the size restriction directly. It covers nonunit frequencies and composite moduli. It neither assumes nor proves the general GAP structural assertion.

### Correction fibers

The revised quantifier order, with $L_0,L,H$ natural numbers, is

$$
\forall\,0<\varepsilon<1\
\exists L_0\
\forall L\ge L_0\
\forall H\ge L\
\exists (I_q,\sigma_q)_{L<q\le H,\ q\ {\rm prime\ power}}.
$$

Each set has cardinality at least $q^{7\varepsilon/8}$; its multipliers lie in $[q^\varepsilon/E(q),8q^\varepsilon]$, are coprime to the underlying prime, and have a chosen neighboring denominator $qm+\sigma_q(m)$ with every prime-power divisor strictly below $q$. All associated two-integer intervals are simultaneously distinct and nonadjacent.

The intervals are the ordered endpoints $\min(qm,qm+\sigma_q(m))$ and $\max(qm,qm+\sigma_q(m))$. The global slot assignment proves the required omitted-integer gap, not merely disjointness. For different slots $y<z$, the bounds $b\le y+1$ and $a'\ge z-1\ge y+3$ imply $b+1<a'$.

Only a finite family through $H$ is asserted. This is sufficient because the terminal theorem constructs intervals separately for each $k$, and its $H$ is finite. The auxiliary families and core use the deterministic superset (D1), so they can be chosen before the compatible fibers.

The construction does not retain the old requirement $4\mid qm$ for every correction pair, the old interval $[q^\varepsilon,2q^\varepsilon]$ for every multiplier, or the cutoff $q/2$ for each correction neighbor. Their roles are replaced explicitly by the slot proof, the lower bound involving $E(q)$, and strict descent below $q$.

### External assumptions

No new literature axiom is proposed. Prove the finite weighted Fourier lemma, the finite orientation lemma, and the endpoint-density lemma as theorems using the already proved divisor and Mertens inputs and ordinary finite mathematics.

The audited external-axioms module and the audited interval-statement file can remain byte-identical. Existing declarations of unused axioms do not make a theorem depend on them. What must change is the actual proof path and its dependency report.

After the new arguments are formalized, the expected dependencies are:

| Former input | Role in this replacement |
|---|---|
| Liu–Sawhney | Retained through the reported proved bridge |
| Mertens second theorem | Retained through the reported proved bridge |
| Divisor bound | Retained through the reported proved bridge |
| CFHMPSV structure | Unused; not proved by this argument |
| Bourgain–Garaev | Unused; not proved by this argument |
| Erdős–Turán | Unused in this proof path |

On the maintainer's reported status of the three retained bridges, completing this rewrite would leave only the standard Lean axioms in the terminal theorem's report. That is an expectation to verify with the actual compiled theorem, not a claim about a build performed here.

## 6. Answers to the proposed alternatives

**Does Lemma 1 need equidistribution?** The old parametrization used it to force a canonical inverse into a fixed narrow interval. The correction mechanism itself needs large compatible fibers with small enough mass and descending prime powers. Lemmas F1–F2 supply those directly. The old four counts should be removed, not relabeled as consequences of dispersion.

**Can Martin-style dispersion supply the old counts directly?** Dispersion away from zero alone does not force occupancy of one prescribed interval. Its useful role here is subset-sum covering, where Lemmas C1–C2 make that implication explicit. For the fibers, complementary signs avoid the interval question.

**Are products of a bounded number of primes required?** No. The global divisor envelope handles arbitrary positive multipliers. Only the elementary large-prime-factor deletion of the auxiliary parameter $t$ is used.

**Must the summand budget increase?** No. Corollary C4 preserves $\lfloor q^{\varepsilon/2}\rfloor$. More generally, with $|I|\ge X^\theta$ and $s\asymp X^\sigma$, the same argument works when $\sigma+2\theta-2>0$, in the polynomial range for $q$ relative to $X$. At $\theta=7/8$, the original $\sigma=1/2$ has room to spare.

**Would smaller-modulus cancellation suffice?** Cancelling modulo $p$ alone lowers the maximal denominator power from $p^a$ to at most $p^{a-1}$ and therefore preserves strict descent. But this does not solve the prime-label case $q=p$. The elementary full-modulus covering above makes this additional alteration unnecessary.

## 7. Classical Kloosterman fallback, if preserving one-sided fibers is preferred

A separate audited route replaces BG by the classical complete Kloosterman bound, while changing the assembly parameters and both pair-packing arguments. It is not needed for the elementary route above.

For a unit $a\bmod U$, the classical bound is

$$
\left|\sum_{x\in(\mathbb Z/U\mathbb Z)^\times}
e_U(ax^{-1}+bx)\right|\le\tau(U)\sqrt U
\qquad\text{for every }b.
$$

It is recorded, together with its incomplete-sum consequence, in the introduction to [Bourgain–Garaev, *Kloosterman sums in residue rings*, printed page 2](https://arxiv.org/pdf/1309.1124). Finite Fourier completion gives the explicit bound

$$
|\operatorname{inversePrefix}(U,N,a)|
\le\tau(U)\sqrt U(2+\log U),\qquad 0\le N<U.
$$

Take $\varepsilon=101/200$, $Q=\lfloor k^{663/1000}\rfloor$, and split at $p=q^{1/200}$. For smaller $p$, all necessary reduced moduli are at most $4q^{201/200}$, and completion gives $q^{201/400+o(1)}=o(q^{101/200})$. For larger $p$, use completion for the base modulus $4q$ and bound the specific bad event directly by

$$
(M/p+2)\max_{n\le3qM}\tau(n)=o(M).
$$

This proves the required tested counts, not arbitrary-interval equidistribution modulo $4pq$ for large $p$.

To make the larger $\varepsilon$ fit, replace the fixed grids by the elementary packing bound: among $A$ consecutive integers with $B$ forbidden, one can select at least $(A-2B-1)/3$ nonadjacent pairs of allowed consecutive integers. A good run of length $r$ supplies $\lfloor(r+1)/3\rfloor$ pairs, proving the bound.

With $\alpha=663/1000$, the resulting main-pair density

$$
g=\frac{1-2\log(1/\alpha)}3
$$

satisfies $17g>1$ and $18g>1$. Use the far band $[3k,20k]$ and eighteen near dyadic bands $[k/2^{18},k]$, discarding finitely many pairs at their boundaries. Far mass is at most $2/3$, below the interpolation target, and near mass exceeds one. Auxiliary packing has positive density $(1-2\log(301/200))/3$. Finally

$$
\alpha(1+\varepsilon)=199563/200000<1.
$$

Thus this fallback also preserves the terminal endpoint bound $20k$, but retains a research-level classical Kloosterman obligation. The fully elementary fiber rewrite avoids that obligation and keeps the original assembly exponents.

## 8. Recommended implementation sequence

1. Prove Lemmas C1–C2 and Corollary C4, first with $C=2$. This removes the CFP dependency without altering the old fibers or downstream estimates.
2. Generalize that same corollary to $C=8$; only the fixed upper-bound constant changes.
3. Prove the complementary identities, sieve deletions, and distinct-slot claims in Lemma F1.
4. Prove Lemma F2 using a finite bit cube, its product-average identity, and the telescoping union bound.
5. Prove Lemma D1, replace the universal endpoint set, and adjust the mass estimate to (D5).
6. Instantiate the finite compatible fibers after $H$ is chosen, use the signed congruence (D3), and rerun the terminal dependency report.

This is a replacement of substantial internal lemmas, not a textual deletion of axiom names. The new finite lemmas and their integration must be checked by the kernel before the revised candidate can be described as having no literature axioms.
