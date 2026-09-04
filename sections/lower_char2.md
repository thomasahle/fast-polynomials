
## Theorem

Let \(F=\mathbf F_Q\) be any finite field of characteristic \(2\) with

$$
Q\ge 2n,
\qquad n>1.
$$

In the strict straight-line model used above, no polynomial family with \(2n\) scalar parameters and at most \(n\) multiplication gates can have the property that evaluation at every \(2n\) distinct points is a bijection.

No assumption on the degree or leading coefficient of the output polynomial is needed.

---

## 1. Normal form for an \(n\)-multiplication circuit

Let the multiplication outputs be \(G_1,\dots,G_n\). Because additions and multiplication by fixed field constants are free, the circuit can be written as

$$
G_i=
\left(
\alpha_i x+\sum_{j<i}p_{ij}G_j+u_i
\right)
\left(
\beta_i x+\sum_{j<i}q_{ij}G_j+v_i
\right),
$$

and

$$
f=
\gamma x+\sum_{j=1}^n r_jG_j+w.
$$

Here all the Greek letters and \(p_{ij},q_{ij},r_j\) are fixed elements of \(F\), while

$$
u_1,v_1,\dots,u_n,v_n,w
$$

are affine-linear forms in the \(2n\) parameters.

Thus all parameter dependence enters through \(2n+1\) scalar “slots.”

If the linear parts of these \(2n+1\) affine forms have rank less than \(2n\), then two distinct parameter tuples give exactly the same slots, hence exactly the same polynomial. Therefore the rank must be \(2n\).

We may consequently identify parameter space with an affine hyperplane

$$
H\subset F^{2n+1}.
$$

Write a point of slot space as

$$
\mathbf z=(u,v,\mathbf s),
$$

where \(u=u_1,\ v=v_1\), and

$$
\mathbf s=(u_2,v_2,\dots,u_n,v_n,w)\in F^{2n-1}.
$$

Let the equation of \(H\) be

$$
\ell_u u+\ell_vv+\ell(\mathbf s)=h.
$$

---

## 2. The first gate cannot be scalar

The first gate is

$$
G_1=(\alpha x+u)(\beta x+v),
\qquad
\alpha=\alpha_1,\quad \beta=\beta_1.
$$

Suppose first that

$$
\alpha=\beta=0.
$$

Then \(G_1=uv\) is a scalar, independent of \(x\).

For every later factor and for the output, let \(\lambda_j\) be the fixed coefficient with which \(G_1\) occurs. Since \(G_1\) is scalar, it can be absorbed into the corresponding scalar slot:

$$
\widetilde s_j=s_j+\lambda_j uv.
$$

After making this replacement, the entire output polynomial depends only on the \(2n-1\) quantities

$$
\widetilde{\mathbf s}\in F^{2n-1}.
$$

But \(H\) has \(Q^{2n}\) points, while \(F^{2n-1}\) has only \(Q^{2n-1}\) points. Hence two distinct points of \(H\) give the same \(\widetilde{\mathbf s}\), and therefore the same polynomial.

So at least one of \(\alpha,\beta\) is nonzero.

---

## 3. Two transformations of the slot space

Set

$$
\sigma=\alpha v+\beta u.
$$

Then

$$
G_1=\alpha\beta x^2+\sigma x+uv.
$$

For every slot in \(\mathbf s\), define:

* \(\lambda_j\): the coefficient of \(G_1\) in the corresponding later factor or in the output;
* \(\varepsilon_j\): the coefficient of \(x\) in that same factor or output.

Collect these into vectors

$$
\lambda,\varepsilon\in F^{2n-1}.
$$

### A gauge transformation

For \(t\in F\), define

$$
\mathcal G_t(u,v,\mathbf s)
=
\left(
u+\alpha t,\,
v+\beta t,\,
\mathbf s+\lambda d_t
\right),
$$

where

$$
d_t=\sigma t+\alpha\beta t^2.
$$

Indeed,

$$
(\alpha x+u+\alpha t)(\beta x+v+\beta t)
=
G_1+d_t.
$$

The coefficient of \(x\) does not change because the two cross-terms cancel in characteristic \(2\).

The later slot corrections \(\lambda d_t\) cancel this scalar change in every later factor and in the output. Therefore

$$
f_{\mathcal G_t(\mathbf z)}(x)=f_{\mathbf z}(x).
$$

Thus \(\mathcal G_t\) preserves the output polynomial exactly.

### Translation of the variable

For \(c\in F\), define

$$
\mathcal T_c(u,v,\mathbf s)
=
\left(
u+\alpha c,\,
v+\beta c,\,
\mathbf s+\varepsilon c
\right).
$$

A direct induction through the circuit gives

$$
G_i^{\,\mathcal T_c(\mathbf z)}(x)
=
G_i^{\,\mathbf z}(x+c)
$$

for every gate \(i\), and hence

$$
f_{\mathcal T_c(\mathbf z)}(x)
=
f_{\mathbf z}(x+c).
$$

---

## 4. The hyperplane must be transverse to the gauge orbits

Define three scalars

$$
A=\ell_u\alpha+\ell_v\beta,
\qquad
B=\ell(\lambda),
\qquad
E=\ell(\varepsilon).
$$

For \(\mathbf z\in H\),

$$
\begin{aligned}
&\ell_u(u+\alpha t)+\ell_v(v+\beta t)
+\ell(\mathbf s+\lambda d_t)-h\\
&\qquad
=t\left(A+B\sigma+B\alpha\beta t\right).
\end{aligned}
$$

Therefore \(\mathcal G_t(\mathbf z)\in H\) precisely when

$$
t\left(A+B\sigma+B\alpha\beta t\right)=0.
$$

If there were a nonzero solution \(t\), then \(\mathbf z\) and \(\mathcal G_t(\mathbf z)\) would be two distinct points of \(H\) producing the same polynomial.

We claim that injectivity therefore forces

$$
B=0,\qquad A\ne0.
$$

Indeed:

* If \(B=0=A\), every \(t\) preserves \(H\), immediately giving collisions.
* Suppose \(B\ne0\).

  The affine-linear function \(\sigma\) is nonconstant on \(H\). Otherwise its linear part would be proportional to the defining linear form of \(H\). Since \(\sigma\) has no \(\mathbf s\)-coordinates, that would force \(B=0\), a contradiction.

  If \(\alpha\beta\ne0\), choose \(\mathbf z\in H\) with

  $$
  A+B\sigma\ne0
  $$

  and take

  $$
  t=\frac{A+B\sigma}{B\alpha\beta}\ne0.
  $$

  If \(\alpha\beta=0\), choose \(\mathbf z\in H\) with

  $$
  A+B\sigma=0.
  $$

  Then every \(t\) preserves \(H\).

Both cases give a collision. Hence necessarily

$$
\boxed{B=0,\quad A\ne0.}
$$

---

## 5. Projecting translation back onto the parameter hyperplane

Fix \(c\ne0\). Put

$$
t_c=\frac{A+E}{A}\,c
$$

and define

$$
\widehat{\mathcal T}_c
=
\mathcal G_{t_c}\circ\mathcal T_c.
$$

Because \(B=0\), the change in the equation of \(H\) is

$$
(A+E)c+At_c=0.
$$

Thus

$$
\widehat{\mathcal T}_c(H)=H.
$$

Moreover,

$$
f_{\widehat{\mathcal T}_c(\mathbf z)}(x)
=
f_{\mathbf z}(x+c).
$$

We now count the fixed points of \(\widehat{\mathcal T}_c\).

### If \(E\ne0\)

The first two slots change by

$$
\left(
\alpha\frac{E}{A}c,\,
\beta\frac{E}{A}c
\right).
$$

Since \(c\ne0\), \(E\ne0\), and at least one of \(\alpha,\beta\) is nonzero, there are no fixed points:

$$
\left|\operatorname{Fix}(\widehat{\mathcal T}_c)\right|=0.
$$

### If \(E=0\)

Then \(t_c=c\), so the first two slots return to their original values. The remaining slots change by

$$
c\left[
\varepsilon+\lambda(\sigma+\alpha\beta c)
\right].
$$

Hence a point is fixed precisely when

$$
\varepsilon+\lambda(\sigma+\alpha\beta c)=0.
$$

There are now three possibilities.

1. If \(\lambda=0=\varepsilon\), every point is fixed:

   $$
   \left|\operatorname{Fix}(\widehat{\mathcal T}_c)\right|
   =Q^{2n}.
   $$

2. If the vector equation is inconsistent, there are no fixed points.

3. If \(\lambda\ne0\) and

   $$
   \varepsilon=\kappa\lambda
   $$

   for some \(\kappa\in F\), then the fixed locus is

   $$
   \sigma=\kappa+\alpha\beta c.
   $$

   Since \(A\ne0\), the function \(\sigma\) is nonconstant on \(H\). Therefore each of its fibers has \(Q^{2n-1}\) points:

   $$
   \left|\operatorname{Fix}(\widehat{\mathcal T}_c)\right|
   =Q^{2n-1}.
   $$

Thus in all cases,

$$
\boxed{
\left|\operatorname{Fix}(\widehat{\mathcal T}_c)\right|
\in
\left\{0,Q^{2n-1},Q^{2n}\right\}.
}
$$

---

## 6. Evaluation at points paired by translation

Because \(Q\ge2n\), translation by \(c\ne0\) has at least \(n\) distinct two-element orbits. Choose

$$
r_1,\dots,r_n
$$

such that the \(2n\) elements

$$
r_1,r_1+c,\dots,r_n,r_n+c
$$

are distinct.

Let

$$
X=(r_1,r_1+c,\dots,r_n,r_n+c).
$$

Write

$$
\Phi_X(\mathbf z)
=
\bigl(
f_{\mathbf z}(r_1),
f_{\mathbf z}(r_1+c),
\dots,
f_{\mathbf z}(r_n),
f_{\mathbf z}(r_n+c)
\bigr).
$$

Let \(\pi\) be the permutation of \(F^{2n}\) which swaps the two entries in every pair. From

$$
f_{\widehat{\mathcal T}_c(\mathbf z)}(x)
=
f_{\mathbf z}(x+c)
$$

we get

$$
\Phi_X\circ\widehat{\mathcal T}_c
=
\pi\circ\Phi_X.
$$

If \(\Phi_X\) were a bijection, then \(\widehat{\mathcal T}_c\) and \(\pi\) would be conjugate permutations. They would therefore have the same number of fixed points.

But a vector is fixed by \(\pi\) precisely when the entries in every pair are equal. Hence

$$
\left|\operatorname{Fix}(\pi)\right|=Q^n.
$$

On the other hand, we proved

$$
\left|\operatorname{Fix}(\widehat{\mathcal T}_c)\right|
\in
\{0,Q^{2n-1},Q^{2n}\}.
$$

For \(n>1\),

$$
Q^n\notin\{0,Q^{2n-1},Q^{2n}\}.
$$

This is the required contradiction.

---

## Conclusion

For every finite field \(F\) of characteristic \(2\) with \(|F|\ge2n\),

$$
\boxed{\text{there is no }(2n,n)\text{ construction when }n>1.}
$$

The proof is independent of the output degree and does not assume that the polynomial is monic.

The case \(n=1\) is exceptional and does exist:

$$
f_{a,b}(x)=ax+b
$$

uses one multiplication and is bijective on evaluations at any two distinct points.
