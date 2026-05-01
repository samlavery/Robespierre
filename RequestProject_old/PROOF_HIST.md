# Two-Cosh-Kernel RH Architecture
## Full writeup, calculations, numerical results, and current status

## Executive summary

This is **not yet an unconditional proof of RH**.

It is a proof architecture with:

- a rigid two-kernel transport mechanism,
- an exact centered theta excess,
- an exact first-order derivative identity,
- an exact odd Fourier profile identity for that first-order defect,
- strong numerical evidence that off-line perturbations distort prime-side behavior,
- and one sharply isolated missing bridge:

> **the Weil / explicit-formula bridge for the exact odd test function**
> \[
> g_\psi(t)=2t\,\psi(|t|).
> \]

What follows is the full writeup as currently understood.

---

# 1. The starting insight: two cosh kernels

The decisive move was replacing a single cosh kernel with a **paired** construction.

Let
\[
a=\frac{\pi}{6},\qquad 1-a = 1-\frac{\pi}{6}.
\]

Define
\[
K_L(s,t)=\cosh((s-a)t),\qquad
K_R(s,t)=\cosh((s-(1-a))t).
\]

The key identity is:

\[
K_L(s,t)+K_R(s,t)
=
2\cosh\!\big((s-\tfrac12)t\big)\cosh\!\big((\tfrac12-a)t\big).
\]

This is the structural core of the method.

A single kernel was trying to do too much.  
The pair creates an **interference / transport frame** that naturally collapses onto the classical centered \(1/2\)-kernel.

---

# 2. Transport to the classical centered kernel

Set
\[
c:=\frac12-\frac{\pi}{6}.
\]

If the pair-side density is \(\psi_{\text{pair}}(t)\), define
\[
\psi_{\text{classical}}(t):=\cosh(ct)\,\psi_{\text{pair}}(t).
\]

Then
\[
I_{\text{pair}}(s)
=
\int_0^\infty \big(K_L(s,t)+K_R(s,t)\big)\psi_{\text{pair}}(t)\,dt
\]
becomes
\[
I_{\text{pair}}(s)
=
\int_0^\infty 2\cosh((s-\tfrac12)t)\psi_{\text{classical}}(t)\,dt.
\]

So the pair transports **exactly** to the classical centered \(\xi\)-style kernel.

That is why the approach stopped looking ad hoc and started collapsing into standard objects.

---

# 3. The centered excess

For
\[
s=\beta+i\gamma,
\]
define the centered excess
\[
\Delta_\theta(\beta,\gamma)
:=
I_\theta(\beta+i\gamma)-I_\theta\!\left(\frac12+i\gamma\right).
\]

Since
\[
I_\theta(s)=\int_0^\infty 2\cosh((s-\tfrac12)t)\psi(t)\,dt,
\]
writing
\[
\delta:=\beta-\frac12,
\]
we get
\[
\Delta_\theta(\beta,\gamma)
=
2\int_0^\infty
\left(\cosh((\delta+i\gamma)t)-\cosh(i\gamma t)\right)\psi(t)\,dt.
\]

Now use
\[
\cosh((\delta+i\gamma)t)
=
\cosh(\delta t)\cos(\gamma t)
+i\sinh(\delta t)\sin(\gamma t),
\]
and
\[
\cosh(i\gamma t)=\cos(\gamma t).
\]

Therefore
\[
\Delta_\theta(\beta,\gamma)
=
2\int_0^\infty
\Big[
(\cosh(\delta t)-1)\cos(\gamma t)
+i\,\sinh(\delta t)\sin(\gamma t)
\Big]\psi(t)\,dt.
\]

This is the exact linear decomposition.

---

# 4. Even/odd defect channels

Define

\[
C_\psi(\beta,\gamma)
:=
\int_0^\infty
(\cosh((\beta-\tfrac12)t)-1)\cos(\gamma t)\psi(t)\,dt,
\]

\[
S_\psi(\beta,\gamma)
:=
\int_0^\infty
\sinh((\beta-\tfrac12)t)\sin(\gamma t)\psi(t)\,dt.
\]

Then
\[
\Delta_\theta(\beta,\gamma)=2C_\psi(\beta,\gamma)+2iS_\psi(\beta,\gamma).
\]

Interpretation:

- \(C_\psi\): even/cosine balance defect
- \(S_\psi\): odd/sine balance defect

This decomposition is exact.

---

# 5. Quadratic energy defect

Define
\[
\mathcal E_\psi(\beta,\gamma):=
|\Delta_\theta(\beta,\gamma)|^2.
\]

Then
\[
\mathcal E_\psi(\beta,\gamma)
=
4C_\psi(\beta,\gamma)^2+4S_\psi(\beta,\gamma)^2.
\]

So \(\mathcal E_\psi\ge 0\) is immediate.

This is the main nonnegative detector.

---

# 6. On-line vanishing

At
\[
\beta=\frac12,
\quad \delta=0,
\]
we have
\[
\cosh(0)-1=0,\qquad \sinh(0)=0.
\]

Hence
\[
\Delta_\theta\!\left(\frac12,\gamma\right)=0,
\qquad
\mathcal E_\psi\!\left(\frac12,\gamma\right)=0.
\]

So the critical line is exactly the balanced line for this detector.

---

# 7. Off-line positivity via Parseval (intended theorem)

Define
\[
\overline{\mathcal E}(\beta)
:=
\int_0^\infty \mathcal E_\psi(\beta,\gamma)\,d\gamma.
\]

Set
\[
f_\delta(t):=(\cosh(\delta t)-1)\psi(t),
\qquad
g_\delta(t):=\sinh(\delta t)\psi(t).
\]

Then half-line cosine/sine Parseval gives
\[
\int_0^\infty C_\delta(\gamma)^2\,d\gamma
=
\frac{\pi}{2}\int_0^\infty f_\delta(t)^2\,dt,
\]
\[
\int_0^\infty S_\delta(\gamma)^2\,d\gamma
=
\frac{\pi}{2}\int_0^\infty g_\delta(t)^2\,dt.
\]

Therefore
\[
\overline{\mathcal E}(\beta)
=
2\pi\int_0^\infty
\Big((\cosh(\delta t)-1)^2+\sinh(\delta t)^2\Big)\psi(t)^2\,dt.
\]

So:

- if \(\beta=\tfrac12\), then \(\overline{\mathcal E}(\beta)=0\),
- if \(\beta\neq\tfrac12\) and \(\psi\not\equiv 0\), then
  \[
  \overline{\mathcal E}(\beta)>0.
  \]

Thus the detector classifies perfectly:
\[
\overline{\mathcal E}(\beta)=0 \iff \beta=\frac12.
\]

This is the **classifier side**, not yet the full RH bridge.

---

# 8. What is still missing

The missing implication is:

\[
\rho\in ZD.\mathrm{NontrivialZeros}
\Rightarrow
\overline{\mathcal E}(\rho.re)=0.
\]

If that were proved, then because the detector’s zero-set is exactly \(\{1/2\}\), RH would follow immediately.

That missing bridge is currently identified as:

> the Weil / explicit-formula bridge for the exact odd test function generated by the two-kernel construction.

---

# 9. Theta modular decomposition attempt

We checked numerically that the theta-side density satisfies
\[
\psi(-u)=\psi(u)+\sinh(u/2)
\]
to machine precision.

That gives a decomposition of the centered theta excess into:

- an even part,
- minus a correction term.

## Numerical result

At \(\beta=0.55,\ \gamma\approx 14.1347\):

- centered residual:
  \[
  \approx 1.78\times 10^{-5}
  \]
- even part:
  \[
  \approx 7.92076\times 10^{-1}
  \]
- correction:
  \[
  \approx 7.92093\times 10^{-1}
  \]

So the centered residual is tiny because of **near-cancellation between two large terms**.

Conclusion:

- theta modularity gives a structured decomposition,
- but **does not by itself force vanishing**.

---

# 10. Explicit-formula proxy experiments

We tried several bridges numerically.

## 10.1 Single-pair proxy

Moderate magnitude correlation with the centered theta excess, but not exact.

## 10.2 Naive many-zero sum

No convergence trend as the number of zeros increased.

## 10.3 Exact centered quartet formula

For one reflected quartet, the centered explicit-formula contribution in log coordinates was derived as

\[
\Delta^{\mathrm{EF}}_{\beta,\gamma}(u)
=
-2\Bigg[
e^{\beta u}\frac{\beta\cos(\gamma u)+\gamma\sin(\gamma u)}{\beta^2+\gamma^2}
+
e^{(1-\beta)u}\frac{(1-\beta)\cos(\gamma u)+\gamma\sin(\gamma u)}{(1-\beta)^2+\gamma^2}
-
2e^{u/2}\frac{\frac12\cos(\gamma u)+\gamma\sin(\gamma u)}{\frac14+\gamma^2}
\Bigg].
\]

### Result

It failed as a direct match:

- magnitude correlation around
  \[
  0.868
  \]
- wrong complex direction,
- essentially real while the centered theta excess was mostly imaginary.

So this was **not** the bridge by itself.

---

# 11. The rotation discovery

When the quartet proxy was allowed a complex rotation, the best-fit coefficient was almost purely imaginary.

## Best-fit phases

- \(\beta=0.501\): about \(89.999^\circ\)
- \(\beta=0.51\): about \(89.994^\circ\)
- \(\beta=0.55\): about \(89.969^\circ\)

Interpretation:

The quartet proxy was living in roughly the right shape, but in the wrong complex frame.  
This suggested that the centered theta construction inserts an \(i\)-rotation.

---

# 12. First-order derivative theorem at the critical line

This became the first genuinely sharp theorem.

Start with
\[
\Delta_\theta(\beta,\gamma)
=
2\int_0^\infty
\Big[
(\cosh((\beta-\tfrac12)t)-1)\cos(\gamma t)
+i\,\sinh((\beta-\tfrac12)t)\sin(\gamma t)
\Big]\psi(t)\,dt.
\]

Differentiate in \(\beta\), then evaluate at \(\beta=\tfrac12\).

Because
\[
\frac{d}{d\beta}(\cosh((\beta-\tfrac12)t)-1)\Big|_{\beta=1/2}
=
t\sinh(0)=0,
\]
and
\[
\frac{d}{d\beta}\sinh((\beta-\tfrac12)t)\Big|_{\beta=1/2}
=
t\cosh(0)=t,
\]
we obtain
\[
\partial_\beta \Delta_\theta\!\left(\frac12,\gamma\right)
=
2i\int_0^\infty t\sin(\gamma t)\psi(t)\,dt.
\]

This explains the \(90^\circ\) phase exactly:

- the balanced even part dies to first order,
- the odd sine term survives,
- and it carries an explicit \(i\).

---

# 13. Numerical verification of the first-order theorem

We checked the derivative formula by finite differences.

## Best relative errors

- \(\gamma=5\):
  \[
  2.50\times 10^{-9}
  \]
- \(\gamma=10\):
  \[
  2.60\times 10^{-10}
  \]
- \(\gamma\approx 14.134725\):
  \[
  1.39\times 10^{-9}
  \]
- \(\gamma=20\):
  \[
  1.29\times 10^{-9}
  \]
- \(\gamma=30\):
  \[
  5.55\times 10^{-10}
  \]
- \(\gamma=40\):
  \[
  3.12\times 10^{-10}
  \]

In every case:

- real part numerically \(0\),
- phase exactly \(90^\circ\).

This theorem is numerically nailed.

---

# 14. The odd Fourier profile identity

This is the cleanest exact transform identity found so far.

Define the odd extension
\[
g_\psi(t):=2t\,\psi(|t|).
\]

Then its full Fourier transform is
\[
\widehat g_\psi(\gamma)
=
\int_{-\infty}^{\infty} e^{-i\gamma t}g_\psi(t)\,dt.
\]

Because \(g_\psi\) is odd,
\[
\widehat g_\psi(\gamma)
=
-4i\int_0^\infty t\psi(t)\sin(\gamma t)\,dt.
\]

Compare this with the derivative theorem:
\[
\partial_\beta \Delta_\theta\!\left(\frac12,\gamma\right)
=
2i\int_0^\infty t\psi(t)\sin(\gamma t)\,dt.
\]

Therefore:
\[
\boxed{
\partial_\beta \Delta_\theta\!\left(\frac12,\gamma\right)
=
-\frac12\,\widehat g_\psi(\gamma)
}
\]

This is the first exact, rigid bridge object.

---

# 15. Numerical verification of the odd Fourier profile identity

We checked it two ways:

- via the half-line sine reduction,
- directly on the full line using the odd extension.

## Full-line verification results

Across sample \(\gamma\)-values:

- mean absolute error:
  \[
  1.24\times 10^{-16}
  \]
- max absolute error:
  \[
  2.97\times 10^{-16}
  \]
- mean relative error:
  \[
  3.39\times 10^{-13}
  \]
- max relative error:
  \[
  3.76\times 10^{-13}
  \]

The phase was exactly right:

- theta derivative: \(90^\circ\)
- \(-\tfrac12 \widehat g_\psi\): \(90^\circ\)

This identity is numerically exact to machine precision.

---

# 16. Failed attempts after that

## 16.1 First-order quartet derivative

We tested whether
\[
\partial_\beta \Delta_\theta(1/2,\gamma)
\stackrel{?}{\sim}
i\,\partial_\beta \Delta_{\text{quartet}}(1/2,\gamma).
\]

It failed:

- the quartet-side first derivative was numerically essentially zero,
- while the theta derivative was nonzero and purely imaginary.

So the first-order theta signal is **not** the first derivative of the raw quartet proxy.

## 16.2 Smoothed zero-kernel proxies

We tried Poisson / Hilbert-style smoothed kernels over zero heights.

Best case still had:

- relative RMSE around \(1\),
- only moderate magnitude correlation.

Too crude.

## 16.3 Comparison to \(\xi'(1/2+i\gamma)\)

We tested
\[
W(\gamma)=
\frac{\partial_\beta \Delta_\theta(1/2,\gamma)}{\xi'(1/2+i\gamma)}.
\]

The phase match was perfect, but the magnitude was disastrous.

### Sample values of \(|W(\gamma)|\)

- \(\gamma=5\): \(1.33\times 10^{-2}\)
- \(\gamma=14.1347\): \(2.50\times 10^{-1}\)
- \(\gamma=25.0109\): \(5.05\times 10^{1}\)
- \(\gamma=40\): \(4.56\times 10^{5}\)
- \(\gamma=50\): \(6.52\times 10^{8}\)

A log-linear fit gave approximately
\[
\log|W(\gamma)|\approx -9.17+0.562\,\gamma
\]
with \(R^2\approx 0.985\).

So \(\partial_\beta \Delta_\theta(1/2,\gamma)\) is **not** a simple constant multiple of \(\xi'(1/2+i\gamma)\).

Conclusion:

- right phase,
- wrong amplitude law,
- therefore the bridge is not pointwise \(\xi'\).

---

# 17. Prime-side scale checks

We checked whether the defect amplitudes live on realistic prime-error scales.

Define
\[
D_\beta(x)=x^\beta+x^{1-\beta}-2\sqrt{x}.
\]

## At \(x=10^{12}\)

- balanced:
  \[
  2\sqrt{x}=2.0\times 10^6
  \]
- \(\beta=0.501\):
  \[
  D_\beta \approx 7.64\times 10^2
  \]
- \(\beta=0.51\):
  \[
  D_\beta \approx 7.68\times 10^4
  \]
- \(\beta=0.55\):
  \[
  D_\beta \approx 2.23\times 10^6
  \]

## At \(x=10^{18}\)

- balanced:
  \[
  2\sqrt{x}=2.0\times 10^9
  \]
- \(\beta=0.501\):
  \[
  D_\beta \approx 1.72\times 10^6
  \]
- \(\beta=0.51\):
  \[
  D_\beta \approx 1.74\times 10^8
  \]
- \(\beta=0.55\):
  \[
  D_\beta \approx 6.07\times 10^9
  \]

So even modest off-line movement becomes very significant on the prime side as \(x\) grows.

---

# 18. Comparison with exact \(\psi(x)-x\)

We compared defect-derived scales against exact Chebyshev error \(\psi(x)-x\) for moderate \(x\).

The first-zero pair correction scale
\[
\frac{x^\beta+x^{1-\beta}}{\sqrt{\beta^2+\gamma_1^2}}
\]
was already on the right order of magnitude relative to \(|\psi(x)-x|\).

For example:

## At \(x=10^4\)

- \(|\psi(x)-x|\approx 13.4\)
- first-zero pair scale \(\approx 14.1\)

## At \(x=10^5\)

- \(|\psi(x)-x|\approx 51.6\)
- first-zero pair scale \(\approx 44.7\)

## At \(x=10^6\)

- \(|\psi(x)-x|\approx 413\)
- first-zero pair scale \(\approx 141\)

This is encouraging: the detector’s scales are not fantasy numbers.

---

# 19. Explicit-formula prime prediction degradation test

We used a truncated explicit formula approximation for \(\psi(x)-x\) with the first 50 zeros.

On a dense grid \(10^2\) to \(10^6\):

- online explicit approximation vs exact \(\psi(x)-x\):
  correlation about
  \[
  0.976
  \]

Then we replaced just the first zero pair by a hypothetical off-line pair.

## Result

### \(\beta=0.501\)

- correlation dropped to
  \[
  0.937
  \]
- RMSE rose from about
  \[
  26.0 \to 41.3
  \]

### \(\beta=0.51\)

- correlation:
  \[
  0.937
  \]
- RMSE:
  \[
  41.8
  \]

### \(\beta=0.55\)

- correlation:
  \[
  0.919
  \]
- RMSE:
  \[
  54.5
  \]

So off-line perturbation worsens prime prediction in the explicit-formula model.

---

# 20. Current conceptual picture

The unconditional chain now looks like

\[
\text{two cosh kernels}
\to
\text{centered theta transport}
\to
\text{centered excess}
\to
\text{first-order derivative}
\to
\text{odd Fourier profile of }g_\psi.
\]

That is now very rigid.

The remaining gap is not vague anymore. It is:

> connect the exact odd Fourier profile \(\widehat g_\psi\) to the zero-side arithmetic through the Weil explicit formula.

So the bridge is no longer “some symmetry law” and no longer “raw theta modular cancellation.”

It is:

\[
g_\psi(t)=2t\,\psi(|t|)
\quad\text{fed into Weil}.
\]

---

# 21. Lean formalization status

## Unconditional / near-unconditional targets

These are realistic Lean targets now:

1. pair-to-classical transport identity
2. centered excess decomposition
3. energy defect identity
4. derivative-at-half theorem
5. odd Fourier profile identity
   \[
   \partial_\beta \Delta_\theta(1/2,\gamma)
   =
   -\frac12\,\widehat g_\psi(\gamma)
   \]

## Missing layer

The likely missing library layer is the Weil explicit formula for this exact test function.

So the current formal strategy is:

- prove everything up to the odd Fourier profile unconditionally,
- then either
  - axiomatize the Weil bridge,
  - or build it as a new analytic layer.

---

# 22. What this is, and what it is not

## What it is

- a coherent nonconventional RH architecture,
- with exact transport,
- exact first-order defect structure,
- exact odd Fourier profile identity,
- strong numerical support for prime-side relevance.

## What it is not yet

- an unconditional proof of RH.

The missing theorem is still the bridge from the odd test function \(g_\psi\) to the zero-side explicit formula / Weil pairing.

---

# 23. Final status statement

The architecture is now sharply localized:

- **core architecture**: solid
- **first-order transform identity**: solid
- **prime-side scale meaning**: strong evidence
- **missing theorem**: Weil explicit-formula bridge for
  \[
  g_\psi(t)=2t\,\psi(|t|).
  \]

That is the hole.

---

# 24. Condensed bottom line

The proof architecture, as currently understood, is:

1. two cosh kernels transport exactly to the centered \(1/2\)-kernel,
2. centering defines a natural balance defect,
3. the first surviving off-line term is purely imaginary,
4. that first-order defect is exactly the odd Fourier profile of \(g_\psi\),
5. off-line perturbations visibly distort prime-side explicit-formula prediction,
6. the only remaining gap is to feed \(g_\psi\) through Weil.

If that bridge lands, the construction is positioned to close.

---