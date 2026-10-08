module

/-
Fix $(\beta,h,s)\in\cK\times[0,1]$. For $t\ge0$, let $\mathsf H_t$ be the heat semigroup, i.e. \[ (\mathsf H_t\varphi)(x)\coloneqq\E\varphi(x+\sqrt t\,Z) . \] Then, it holds that \begin{equation}\label{eq:genH} \partial _t (\mathsf H_t\varphi)(x) = \frac{1}{2} \mathsf H_t (\partial ^2 \varphi)(x) . \end{equation} For the upper interval, introduce the tilted heat semigroup \begin{equation} (\mathsf T_t\varphi)(x) \coloneqq e^{-t/2} \frac{\bigl(\mathsf H_t (\varphi \cdot \cosh )\bigr)(x)}{\cosh(x)}. \label{eq:tiltedsemigroup} \end{equation} Differentiation under the Gaussian integral shows that its generator is $\frac12\partial_{xx}+\tanh(x)\partial_x$. For each $u\in[0,1]$, let $X_{s,u}$ denote a random variable whose law is specified by \begin{equation} \E\varphi(X_{s,u}) \coloneqq \begin{cases} \bigl(\mathsf H_{\beta^2(1-s)q+s\beta^2u}\varphi\bigr)(h), &0\le u\le q,\\[1mm] \bigl(\mathsf H_{\beta^2q} (\mathsf T_{s\beta^2(u-q)}\varphi)\bigr)(h), &q\le u\le1. \end{cases} \label{eq:localfieldlaw} \end{equation} In particular, \begin{equation}\label{eq:Xsq} X_{s,q}\stackrel{\mathrm d}=h+\beta\sqrt q\,Z. \end{equation} For $0\le u\le1$ and $x\in\mathbb R$, define \begin{equation} \Psi(u,x) \coloneqq \E\log\cosh\left( x+\beta\sqrt{s(q-u)_+}\,Z \right) +\frac{s\beta^2}{2}\bigl(1-\max\{u,q\}\bigr), \qquad Z\sim N(0,1), \label{eq:Psi-explicit} \end{equation} where $(a)_+\coloneqq\max\{a,0\}$. Equivalently, \[ \Psi(u,x) = \begin{cases} (\mathsf H_{s\beta^2(q-u)}\log\cosh)(x) +\dfrac{s\beta^2}{2}(1-q), &0\le u\le q,\\[2mm] \log\cosh(x)+\dfrac{s\beta^2}{2}(1-u), &q\le u\le1. \end{cases} \] Differentiating \eqref{eq:Psi-explicit} in $x$ gives \begin{equation} \partial_x\Psi(u,x) = \E\tanh\left( x+\beta\sqrt{s(q-u)_+}\,Z \right) = \begin{cases} (\mathsf H_{s\beta^2(q-u)}\tanh)(x), &0\le u\le q,\\ \tanh(x),&q\le u\le1. \end{cases} \label{eq:Psi-x} \end{equation} The replica-symmetric free energy for $H_{N,s}$ along the path is \begin{align} P_s^*& \coloneqq\log2+ \E\Psi(0,h+\beta\sqrt{(1-s)q}\,Z) -\frac{s\beta^2}{2}\int_q^1u\,\dd u \label{eq:scalartrial}\\ &= \log2+\E\log\cosh(h+\beta\sqrt q\,Z) +\frac{s\beta^2}{4}(1-q)^2, \label{eq:RSpathvalue} \end{align} where we have used the semigroup property and $\beta^2(1-s)q+s\beta^2q=\beta^2q$. \begin{proposition} \label{prop:pathRS} The function $g_s$ defined by \begin{equation} g_s(u)\coloneqq\E\bigl[(\partial_x\Psi(u,X_{s,u}))^2\bigr] \label{eq:gs-def} \end{equation} satisfies \begin{equation} g_s(u)-u \begin{cases} >0,&0\le u<q,\\ =0,&u=q,\\ <0,&q<u\le1. \end{cases} \label{eq:ATsign} \end{equation} Moreover, there are constants $c_{\cK},\varepsilon_{\cK}>0$ such that \begin{equation} |g_s(u)-u|\ge c_{\cK}|u-q| \qquad\text{whenever }|u-q|\le\varepsilon_{\cK}. \label{eq:linearATsign} \end{equation} \end{proposition}
\begin{proof}
Throughout the proof, write
[
a\coloneqq s\beta^2.
]
We also recall the definitions
[
q=\E\tanh^2(h+\beta\sqrt q,Z),
\qquad
\alpha=\beta^2\E\sech^4(h+\beta\sqrt q,Z),
]
and the standing assumption on $\cK$ that
[
\alpha<1.
]

First consider $u=q$. By \eqref{eq:Psi-x},
[
\partial_x\Psi(q,x)=\tanh(x),
]
while \eqref{eq:Xsq} gives
[
X_{s,q}\stackrel{\mathrm d}=h+\beta\sqrt q,Z.
]
Consequently,
[
g_s(q)
======

# \E\tanh^2(X_{s,q})

# \E\tanh^2(h+\beta\sqrt q,Z)

q.
\tag{1}
]

We next consider the interval $0\le u<q$.

Set
[
r(u)\coloneqq a(q-u),
\qquad
\tau(u)\coloneqq\beta^2(1-s)q+a u.
]
Then
[
r'(u)=-a,
\qquad
\tau'(u)=a,
]
and, by \eqref{eq:localfieldlaw},
[
\E\varphi(X_{s,u})
==================

(\mathsf H_{\tau(u)}\varphi)(h).
\tag{2}
]
Thus, for every smooth $\varphi$ with bounded derivatives,
[
\frac{\dd}{\dd u}\E\varphi(X_{s,u})
===================================

\frac{a}{2}
(\mathsf H_{\tau(u)}\varphi'')(h)
=================================

\frac{a}{2}\E\varphi''(X_{s,u}).
\tag{3}
]
Here we used \eqref{eq:genH} and $\tau'(u)=a$.

Define
[
F_u(x)\coloneqq
(\mathsf H_{r(u)}\tanh)(x).
]
By \eqref{eq:Psi-x},
[
g_s(u)=\E[F_u(X_{s,u})^2].
\tag{4}
]
Moreover, differentiating $F_u$ with respect to $u$ and using
\eqref{eq:genH},
[
\partial_uF_u(x)
================

r'(u)\frac12
\mathsf H_{r(u)}(\partial_x^2\tanh)(x)
======================================

-\frac a2 F_u''(x).
\tag{5}
]
Since the derivatives of $\tanh$ are bounded, all differentiations above
and below are justified by differentiation under the Gaussian integral.

Differentiating \eqref{eq:4} and using \eqref{eq:3} with
$\varphi=F_u^2$, we obtain
\begin{align*}
g_s'(u)
&=
\E\bigl[2F_u(X_{s,u})\partial_uF_u(X_{s,u})\bigr]
+\frac a2\E\bigl[(F_u^2)''(X_{s,u})\bigr]\
&=
-a\E\bigl[F_u(X_{s,u})F_u''(X_{s,u})\bigr]
+\frac a2
\E\bigl[(F_u^2)''(X_{s,u})\bigr].
\end{align*}
Since
[
(F_u^2)''
=========

2(F_u')^2+2F_uF_u'',
]
the terms containing $F_uF_u''$ cancel, and hence
[
g_s'(u)
=======

a,\E\bigl[(F_u'(X_{s,u}))^2\bigr].
\tag{6}
]
The heat semigroup commutes with spatial differentiation, so
[
F_u'
====

# \mathsf H_{r(u)}(\partial_x\tanh)

\mathsf H_{r(u)}(\sech^2).
]
Therefore
[
g_s'(u)
=======

a\E\left[
\left{
\mathsf H_{r(u)}(\sech^2)(X_{s,u})
\right}^2
\right].
\tag{7}
]

For every $x\in\mathbb R$, Jensen's inequality gives
[
\left{
\mathsf H_{r(u)}(\sech^2)(x)
\right}^2
\le
\mathsf H_{r(u)}(\sech^4)(x).
]
Using \eqref{eq:2},
\begin{align*}
g_s'(u)
&\le
a,\E\left[
\mathsf H_{r(u)}(\sech^4)(X_{s,u})
\right]\
&=
a,
\bigl(
\mathsf H_{\tau(u)}
\mathsf H_{r(u)}
(\sech^4)
\bigr)(h).
\end{align*}
Now
\begin{align*}
\tau(u)+r(u)
&=
\beta^2(1-s)q
+s\beta^2u
+s\beta^2(q-u)\
&=
\beta^2q.
\end{align*}
Hence, by the semigroup property,
\begin{align*}
g_s'(u)
&\le
a,(\mathsf H_{\beta^2q}\sech^4)(h)\
&=
s\beta^2
\E\sech^4(h+\beta\sqrt q,Z)\
&=
s\alpha.
\tag{8}
\end{align*}

Integrating \eqref{eq:8} from $u$ to $q$ and using \eqref{eq:1},
[
q-g_s(u)
========

# g_s(q)-g_s(u)

\int_u^qg_s'(v),\dd v
\le
s\alpha(q-u).
]
It follows that
\begin{align}
g_s(u)-u
&=
(q-u)-(q-g_s(u))\notag\
&\ge
(1-s\alpha)(q-u).
\tag{9}\label{eq:leftstrict-detailed}
\end{align}
Since $0\le s\le1$ and $\alpha<1$,
[
1-s\alpha\ge1-\alpha>0.
]
Thus
[
g_s(u)-u>0,
\qquad 0\le u<q.
\tag{10}
]

We now turn to the interval $q\le u\le1$.

It is useful first to record the generator of the tilted heat semigroup
explicitly. Let
[
\mathcal L\varphi
\coloneqq
\frac12\varphi''+\tanh(x)\varphi'.
\tag{11}
]
From \eqref{eq:tiltedsemigroup},
[
(\mathsf T_t\varphi)(x)
=======================

e^{-t/2}
\frac{\mathsf H_t(\varphi\cosh)(x)}{\cosh(x)}.
]
Differentiating in $t$,
\begin{align*}
\partial_t(\mathsf T_t\varphi)(x)
&=
-\frac12(\mathsf T_t\varphi)(x)
+
\frac{e^{-t/2}}{2\cosh(x)}
\mathsf H_t\bigl((\varphi\cosh)''\bigr)(x).
\end{align*}
Since
[
(\varphi\cosh)''
================

\varphi''\cosh
+2\varphi'\sinh
+\varphi\cosh,
]
the last $\varphi\cosh$ term cancels the term
$-\frac12\mathsf T_t\varphi$. Therefore
\begin{align*}
\partial_t(\mathsf T_t\varphi)(x)
&=
\frac{e^{-t/2}}{\cosh(x)}
\mathsf H_t
\left(
\frac12\varphi''\cosh+\varphi'\sinh
\right)(x)\
&=
\mathsf T_t
\left(
\frac12\varphi''+\tanh,\varphi'
\right)(x)\
&=
\mathsf T_t(\mathcal L\varphi)(x).
\tag{12}
\end{align*}

For $u\ge q$, \eqref{eq:localfieldlaw} becomes
[
\E\varphi(X_{s,u})
==================

\bigl(
\mathsf H_{\beta^2q}
\mathsf T_{a(u-q)}\varphi
\bigr)(h).
\tag{13}
]
Differentiating \eqref{eq:13} in $u$ and using \eqref{eq:12},
\begin{align}
\frac{\dd}{\dd u}\E\varphi(X_{s,u})
&=
a,
\bigl(
\mathsf H_{\beta^2q}
\mathsf T_{a(u-q)}
(\mathcal L\varphi)
\bigr)(h)\notag\
&=
a,\E[(\mathcal L\varphi)(X_{s,u})].
\tag{14}
\end{align}

On this interval,
[
\partial_x\Psi(u,x)=\tanh(x),
]
and hence
[
g_s(u)=\E\tanh^2(X_{s,u}).
\tag{15}
]
Set
[
\phi(x)\coloneqq\tanh^2(x).
]
Then
[
\phi'(x)=2\tanh(x)\sech^2(x),
]
and
[
\frac12\phi''(x)
================

\sech^4(x)
-2\tanh^2(x)\sech^2(x).
]
Consequently,
\begin{align*}
(\mathcal L\phi)(x)
&=
\frac12\phi''(x)+\tanh(x)\phi'(x)\
&=
\sech^4(x)
-2\tanh^2(x)\sech^2(x)
+2\tanh^2(x)\sech^2(x)\
&=
\sech^4(x).
\tag{16}
\end{align*}
Applying \eqref{eq:14} to $\phi=\tanh^2$ yields the particularly simple
identity
\begin{equation}
g_s'(u)
=======

a,\E\sech^4(X_{s,u}),
\qquad q\le u\le1.
\tag{17}\label{eq:gs-upper-derivative-detailed}
\end{equation}
At $u=q$,
[
X_{s,q}\stackrel{\mathrm d}=h+\beta\sqrt q,Z,
]
so
\begin{align}
g_s'(q)
&=
a,\E\sech^4(h+\beta\sqrt q,Z)\notag\
&=
s\alpha
<
1.
\tag{18}\label{eq:gsprimeq-detailed}
\end{align}

Suppose first that
[
a(1-q)=s\beta^2(1-q)>1.
]
By Lemma~\ref{lem:uppercomparison},
[
g_s'(u)\le s\alpha<1,
\qquad q\le u\le1.
]
Thus, for every $u>q$,
\begin{align*}
g_s(u)-g_s(q)
&=
\int_q^u g_s'(v),\dd v\
&<
u-q.
\end{align*}
Since $g_s(q)=q$, this gives
[
g_s(u)<u,
\qquad q<u\le1.
\tag{19}
]

It remains to consider
[
a(1-q)\le1.
\tag{20}
]
Since
[
\sech^4(x)\le\sech^2(x)
=1-\tanh^2(x),
]
\eqref{eq:gs-upper-derivative-detailed} and \eqref{eq:15} imply
\begin{align}
g_s'(u)
&\le
a,\E\sech^2(X_{s,u})\notag\
&=
a\left(
1-\E\tanh^2(X_{s,u})
\right)\notag\
&=
a(1-g_s(u)).
\tag{21}\label{eq:gderivative-detailed}
\end{align}

Define
[
f(u)\coloneqq g_s(u)-u.
]
Then $f(q)=0$, and \eqref{eq:gderivative-detailed} gives
\begin{align*}
f'(u)
&=
g_s'(u)-1\
&\le
a(1-g_s(u))-1\
&=
-af(u)+a(1-u)-1.
\end{align*}
Hence
\begin{equation}
f'(u)+af(u)
\le
a(1-u)-1.
\tag{22}
\end{equation}
Multiplication by the integrating factor $e^{a(u-q)}$ gives
[
\frac{\dd}{\dd u}
\left(
e^{a(u-q)}f(u)
\right)
\le
e^{a(u-q)}\bigl(a(1-u)-1\bigr).
\tag{23}
]
For every $u>q$, \eqref{eq:20} implies
[
a(1-u)-1
<
a(1-q)-1
\le0
]
when $a>0$. If $a=0$, the right-hand side of \eqref{eq:23} equals
$-1$, so it is again strictly negative. Therefore, integrating
\eqref{eq:23} from $q$ to $u>q$ and using $f(q)=0$,
[
e^{a(u-q)}f(u)
\le
\int_q^u
e^{a(v-q)}
\bigl(a(1-v)-1\bigr),\dd v
<0.
]
Thus
[
g_s(u)-u=f(u)<0,
\qquad q<u\le1.
\tag{24}
]
Together with \eqref{eq:10}, \eqref{eq:1}, and \eqref{eq:19}, this proves
\eqref{eq:ATsign}.

It remains to establish the uniform linear estimate
\eqref{eq:linearATsign}.

By compactness of $\cK$ and the strict AT condition, define
[
\alpha_{\cK}
\coloneqq
\sup_{(\beta,h)\in\cK}\alpha(\beta,h)
<1,
\qquad
\delta_{\cK}
\coloneqq
1-\alpha_{\cK}>0.
\tag{25}
]
For $u<q$, \eqref{eq:leftstrict-detailed} immediately gives
\begin{align*}
g_s(u)-u
&\ge
(1-s\alpha)(q-u)\
&\ge
\delta_{\cK}(q-u).
\tag{26}
\end{align*}
Thus the desired linear estimate already holds uniformly on the entire
lower interval.

For completeness, we give an explicit uniform argument on the upper
side. Set
[
\psi(x)\coloneqq\sech^4(x).
]
By \eqref{eq:gs-upper-derivative-detailed},
[
g_s'(u)=a,\E\psi(X_{s,u}).
]
Applying \eqref{eq:14} once more,
[
g_s''(u)
========

a^2\E[(\mathcal L\psi)(X_{s,u})],
\qquad u>q.
\tag{27}
]
A direct computation gives
[
\psi'(x)
========

-4\sech^4(x)\tanh(x),
]
and
[
\frac12\psi''(x)
================

8\sech^4(x)\tanh^2(x)
-2\sech^6(x).
]
Therefore
\begin{align*}
(\mathcal L\psi)(x)
&=
\frac12\psi''(x)+\tanh(x)\psi'(x)\
&=
4\sech^4(x)\tanh^2(x)
-2\sech^6(x).
\tag{28}
\end{align*}
In particular, there is a universal constant $C_0<\infty$, for example
$C_0=6$, such that
[
|\mathcal L\psi|_\infty\le C_0.
\tag{29}
]

Let
[
B_{\cK}\coloneqq
\sup{|\beta|:(\beta,h)\in\cK}<\infty
]
and set
[
C_{\cK}\coloneqq C_0(1+B_{\cK}^4).
]
Since $a=s\beta^2$ and $0\le s\le1$, \eqref{eq:27} gives the uniform
bound
[
|g_s''(u)|
\le
C_{\cK},
\qquad q<u\le1.
\tag{30}
]
Consequently, for $u\ge q$,
[
|g_s'(u)-g_s'(q)|
\le
C_{\cK}(u-q).
\tag{31}
]
By \eqref{eq:gsprimeq-detailed} and \eqref{eq:25},
[
g_s'(q)
=======

s\alpha
\le
\alpha_{\cK}
============

1-\delta_{\cK}.
\tag{32}
]
Choose
[
\varepsilon_{\cK}
\coloneqq
\min\left{
1,\frac{\delta_{\cK}}{2C_{\cK}}
\right}.
\tag{33}
]
Then, whenever
[
q\le u\le1,
\qquad
u-q\le\varepsilon_{\cK},
]
\eqref{eq:31} and \eqref{eq:32} imply
[
g_s'(u)
\le
1-\frac{\delta_{\cK}}2.
\tag{34}
]
Therefore
\begin{align*}
u-g_s(u)
&=
\int_q^u(1-g_s'(v)),\dd v\
&\ge
\frac{\delta_{\cK}}2(u-q).
\tag{35}
\end{align*}

Combining \eqref{eq:26} and \eqref{eq:35}, and setting
[
c_{\cK}\coloneqq\frac{\delta_{\cK}}2>0,
]
we obtain
[
|g_s(u)-u|
\ge
c_{\cK}|u-q|
]
whenever
[
u\in[0,1],
\qquad
|u-q|\le\varepsilon_{\cK}.
]
This proves \eqref{eq:linearATsign}.
\end{proof}

-/

public import Lemmas.AT.Definitions
public import Lemmas.AT.Interpolation
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.MeasureTheory.Group.IntegralConvolution
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Lemmas.SpinGlass.GaussianIntegrationByParts

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter
open scoped MeasureTheory NNReal Topology

set_option autoImplicit false

namespace SpinGlass.AT

noncomputable def propertySech (x : ℝ) : ℝ := (Real.cosh x)⁻¹

private lemma propertySech_pos (x : ℝ) : 0 < propertySech x := by
  exact inv_pos.mpr (Real.cosh_pos x)

private lemma propertySech_le_one (x : ℝ) : propertySech x ≤ 1 := by
  exact inv_le_one_of_one_le₀ (Real.one_le_cosh x)

private lemma property_abs_sech_le_one (x : ℝ) : |propertySech x| ≤ 1 := by
  rw [abs_of_pos (propertySech_pos x)]
  exact propertySech_le_one x

private lemma property_abs_tanh_le_one (x : ℝ) : |Real.tanh x| ≤ 1 :=
  (Real.abs_tanh_lt_one x).le

private lemma property_tanh_sq_add_sech_sq (x : ℝ) :
    Real.tanh x ^ 2 + propertySech x ^ 2 = 1 := by
  unfold propertySech
  rw [Real.tanh_eq_sinh_div_cosh]
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  simp only [div_pow, inv_pow]
  field_simp [hc]
  nlinarith [Real.cosh_sq_sub_sinh_sq x]

private lemma property_continuous_tanh : Continuous (fun x : ℝ => Real.tanh x) := by
  simp_rw [Real.tanh_eq_sinh_div_cosh]
  exact Real.continuous_sinh.div₀ Real.continuous_cosh
    (fun x => (Real.cosh_pos x).ne')

private lemma property_continuous_sech : Continuous propertySech := by
  unfold propertySech
  exact Real.continuous_cosh.inv₀ fun x => (Real.cosh_pos x).ne'

private lemma property_tanh_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.tanh y) (propertySech x ^ 2) x := by
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  rw [show (fun y : ℝ => Real.tanh y) = fun y => Real.sinh y / Real.cosh y by
    funext y
    exact Real.tanh_eq_sinh_div_cosh y]
  apply ((Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc).congr_deriv
  unfold propertySech
  simp only [inv_pow]
  field_simp [hc]
  nlinarith [Real.cosh_sq_sub_sinh_sq x]

private lemma property_integrable_tanh_affine (a b : ℝ) :
    Integrable (fun z : ℝ => Real.tanh (a + b * z)) (gaussianReal 0 1) := by
  apply Integrable.of_bound (C := 1)
  · exact (property_continuous_tanh.comp (by fun_prop)).aestronglyMeasurable
  · filter_upwards [] with z
    simpa [Real.norm_eq_abs] using property_abs_tanh_le_one (a + b * z)

private lemma property_integrable_sech_sq_affine (a b : ℝ) :
    Integrable (fun z : ℝ => propertySech (a + b * z) ^ 2)
      (gaussianReal 0 1) := by
  apply Integrable.of_bound (C := 1)
  · exact ((property_continuous_sech.comp (by fun_prop)).pow 2).aestronglyMeasurable
  · filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (property_abs_sech_le_one _)

private lemma property_standardGaussianExpectation_const (c : ℝ) :
    standardGaussianExpectation (fun _ : ℝ => c) = c := by
  simp [standardGaussianExpectation]

/-- At the replica-symmetric breakpoint, the scalar order parameter equals
the fixed point. -/
theorem scalarOrderParameterCorrect_at_rsQ {β h : ℝ}
    (hβ : 0 < β) (s : ℝ) :
    scalarOrderParameterCorrect β h s (rsQ β h) = rsQ β h := by
  have hq0 : 0 ≤ rsQ β h := (rsQ_mem_Icc β h).1
  have hsqrt : Real.sqrt (β ^ 2 * ((1 - s) * rsQ β h + s * rsQ β h)) =
      β * Real.sqrt (rsQ β h) := by
    rw [show (1 - s) * rsQ β h + s * rsQ β h = rsQ β h by ring]
    rw [Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq_eq_abs, abs_of_pos hβ]
  have hinner (x : ℝ) : scalarPsiX β (rsQ β h) s (rsQ β h) x =
      Real.tanh x := by
    unfold scalarPsiX
    simp [standardGaussianExpectation]
  unfold scalarOrderParameterCorrect scalarOrderParameter localFieldExpectation
  simp only [if_pos le_rfl, hinner, heatSemigroup, hsqrt]
  exact (rsQ_fixedPoint β h).symm

noncomputable def propertySech3 (x : ℝ) : ℝ := propertySech x ^ 3

private noncomputable def propertySechSecond (x : ℝ) : ℝ :=
  propertySech x * (Real.tanh x ^ 2 - propertySech x ^ 2)

private lemma property_sech_hasDerivAt (x : ℝ) :
    HasDerivAt propertySech (-propertySech x * Real.tanh x) x := by
  unfold propertySech
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  apply ((Real.hasDerivAt_cosh x).inv hc).congr_deriv
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [hc]

private lemma property_sechDeriv_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y => -propertySech y * Real.tanh y)
      (propertySechSecond x) x := by
  have hs := property_sech_hasDerivAt x
  have ht := property_tanh_hasDerivAt x
  apply (hs.neg.mul ht).congr_deriv
  unfold propertySechSecond
  simp only [Pi.neg_apply]
  ring

private lemma property_sech3_hasDerivAt (x : ℝ) :
    HasDerivAt propertySech3 (-3 * propertySech3 x * Real.tanh x) x := by
  unfold propertySech3
  apply ((property_sech_hasDerivAt x).pow 3).congr_deriv
  norm_num
  ring

private noncomputable def propertySech3Second (x : ℝ) : ℝ :=
  9 * propertySech3 x * Real.tanh x ^ 2 -
    3 * propertySech3 x * propertySech x ^ 2

private lemma property_sech3Deriv_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y => -3 * propertySech3 y * Real.tanh y)
      (propertySech3Second x) x := by
  have hs := (property_sech3_hasDerivAt x).const_mul (-3)
  have ht := property_tanh_hasDerivAt x
  apply (hs.mul ht).congr_deriv
  unfold propertySech3Second
  ring

private lemma property_abs_sech3_le_one (x : ℝ) : |propertySech3 x| ≤ 1 := by
  unfold propertySech3
  rw [abs_pow]
  exact pow_le_one₀ (abs_nonneg _) (property_abs_sech_le_one x)

private lemma property_sechDeriv_abs_le_one (x : ℝ) :
    |-propertySech x * Real.tanh x| ≤ 1 := by
  rw [abs_mul, abs_neg]
  calc
    |propertySech x| * |Real.tanh x| ≤ 1 * 1 := by
      gcongr
      · exact property_abs_sech_le_one x
      · exact property_abs_tanh_le_one x
    _ = 1 := by norm_num

private lemma property_sechSecond_abs_le_two (x : ℝ) :
    |propertySechSecond x| ≤ 2 := by
  unfold propertySechSecond
  calc
    |propertySech x * (Real.tanh x ^ 2 - propertySech x ^ 2)| ≤
        |propertySech x| * (|Real.tanh x| ^ 2 + |propertySech x| ^ 2) := by
          rw [abs_mul]
          gcongr
          calc
            |Real.tanh x ^ 2 - propertySech x ^ 2| ≤
                |Real.tanh x ^ 2| + |propertySech x ^ 2| := abs_sub _ _
            _ = |Real.tanh x| ^ 2 + |propertySech x| ^ 2 := by rw [abs_pow, abs_pow]
    _ ≤ 1 * (1 ^ 2 + 1 ^ 2) := by
      gcongr
      · exact property_abs_sech_le_one x
      · exact property_abs_tanh_le_one x
      · exact property_abs_sech_le_one x
    _ = 2 := by norm_num

private lemma property_sech3Deriv_abs_le_three (x : ℝ) :
    |-3 * propertySech3 x * Real.tanh x| ≤ 3 := by
  rw [abs_mul, abs_mul, abs_neg]
  norm_num
  calc
    3 * |propertySech3 x| * |Real.tanh x| ≤ 3 * 1 * 1 := by
      gcongr
      · exact property_abs_sech3_le_one x
      · exact property_abs_tanh_le_one x
    _ = 3 := by norm_num

private lemma property_sech3Second_abs_le_twelve (x : ℝ) :
    |propertySech3Second x| ≤ 12 := by
  unfold propertySech3Second
  calc
    |9 * propertySech3 x * Real.tanh x ^ 2 -
        3 * propertySech3 x * propertySech x ^ 2| ≤
        |9 * propertySech3 x * Real.tanh x ^ 2| +
          |3 * propertySech3 x * propertySech x ^ 2| := abs_sub _ _
    _ ≤ 9 * 1 * 1 ^ 2 + 3 * 1 * 1 ^ 2 := by
      simp only [abs_mul, abs_pow]
      gcongr <;> norm_num
      · exact property_abs_sech3_le_one x
      · exact property_abs_tanh_le_one x
      · exact property_abs_sech3_le_one x
      · exact property_abs_sech_le_one x
    _ = 12 := by norm_num

private lemma property_integrable_sech_affine (a b : ℝ) :
    Integrable (fun z : ℝ => propertySech (a + b * z)) (gaussianReal 0 1) := by
  apply Integrable.of_bound (C := 1)
  · exact (property_continuous_sech.comp (by fun_prop)).aestronglyMeasurable
  · filter_upwards [] with z
    simpa [Real.norm_eq_abs] using property_abs_sech_le_one (a + b * z)

private lemma property_integrable_sechDeriv_affine (a b : ℝ) :
    Integrable (fun z : ℝ => -propertySech (a + b * z) *
      Real.tanh (a + b * z)) (gaussianReal 0 1) := by
  apply Integrable.of_bound (C := 1)
  · have harg : Continuous (fun z : ℝ => a + b * z) :=
      continuous_const.add (continuous_const.mul continuous_id)
    exact (((property_continuous_sech.comp harg).neg.mul
      (property_continuous_tanh.comp harg))).aestronglyMeasurable
  · filter_upwards [] with z
    simpa [Real.norm_eq_abs] using property_sechDeriv_abs_le_one (a + b * z)

private lemma property_integrable_sechSecond_affine (a b : ℝ) :
    Integrable (fun z : ℝ => propertySechSecond (a + b * z))
      (gaussianReal 0 1) := by
  apply Integrable.of_bound (C := 2)
  · apply Continuous.aestronglyMeasurable
    unfold propertySechSecond
    exact (property_continuous_sech.comp (by fun_prop)).mul
      (((property_continuous_tanh.comp (by fun_prop)).pow 2).sub
        ((property_continuous_sech.comp (by fun_prop)).pow 2))
  · filter_upwards [] with z
    simpa [Real.norm_eq_abs] using property_sechSecond_abs_le_two (a + b * z)

private lemma property_integrable_sech3_affine (a b : ℝ) :
    Integrable (fun z : ℝ => propertySech3 (a + b * z)) (gaussianReal 0 1) := by
  apply Integrable.of_bound (C := 1)
  · exact ((property_continuous_sech.comp (by fun_prop)).pow 3).aestronglyMeasurable
  · filter_upwards [] with z
    simpa [Real.norm_eq_abs] using property_abs_sech3_le_one (a + b * z)

private lemma property_integrable_sech3Deriv_affine (a b : ℝ) :
    Integrable (fun z : ℝ => -3 * propertySech3 (a + b * z) *
      Real.tanh (a + b * z)) (gaussianReal 0 1) := by
  apply Integrable.of_bound (C := 3)
  · have harg : Continuous (fun z : ℝ => a + b * z) :=
      continuous_const.add (continuous_const.mul continuous_id)
    exact (((continuous_const.mul
      ((property_continuous_sech.comp harg).pow 3)).mul
      (property_continuous_tanh.comp harg))).aestronglyMeasurable
  · filter_upwards [] with z
    simpa [Real.norm_eq_abs] using property_sech3Deriv_abs_le_three (a + b * z)

private lemma property_integrable_sech3Second_affine (a b : ℝ) :
    Integrable (fun z : ℝ => propertySech3Second (a + b * z))
      (gaussianReal 0 1) := by
  apply Integrable.of_bound (C := 12)
  · apply Continuous.aestronglyMeasurable
    unfold propertySech3Second propertySech3
    have harg : Continuous (fun z : ℝ => a + b * z) :=
      continuous_const.add (continuous_const.mul continuous_id)
    exact (((continuous_const.mul ((property_continuous_sech.comp harg).pow 3)).mul
      ((property_continuous_tanh.comp harg).pow 2)).sub
      ((continuous_const.mul ((property_continuous_sech.comp harg).pow 3)).mul
        ((property_continuous_sech.comp harg).pow 2)))
  · filter_upwards [] with z
    simpa [Real.norm_eq_abs] using property_sech3Second_abs_le_twelve (a + b * z)

noncomputable def propertySmoothSech (r x : ℝ) : ℝ :=
  standardGaussianExpectation (fun z => propertySech (x + Real.sqrt r * z))

noncomputable def propertySmoothSech3 (r x : ℝ) : ℝ :=
  standardGaussianExpectation (fun z => propertySech3 (x + Real.sqrt r * z))

private lemma property_sechDeriv_comp_deriv (a b z : ℝ) :
    deriv (fun y => -propertySech (a + b * y) * Real.tanh (a + b * y)) z =
      b * propertySechSecond (a + b * z) := by
  have harg : HasDerivAt (fun y : ℝ => a + b * y) b z := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id z).const_mul b).const_add a
  simpa [Function.comp_def, mul_comm] using
    ((property_sechDeriv_hasDerivAt (a + b * z)).comp z harg).deriv

private lemma property_sech3Deriv_comp_deriv (a b z : ℝ) :
    deriv (fun y => -3 * propertySech3 (a + b * y) *
      Real.tanh (a + b * y)) z = b * propertySech3Second (a + b * z) := by
  have harg : HasDerivAt (fun y : ℝ => a + b * y) b z := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id z).const_mul b).const_add a
  simpa [Function.comp_def, mul_comm] using
    ((property_sech3Deriv_hasDerivAt (a + b * z)).comp z harg).deriv

private lemma property_contDiff_sech : ContDiff ℝ ⊤ propertySech := by
  unfold propertySech
  exact Real.contDiff_cosh.inv fun x => (Real.cosh_pos x).ne'

private lemma property_contDiff_tanh : ContDiff ℝ ⊤ (fun x : ℝ => Real.tanh x) := by
  simp_rw [Real.tanh_eq_sinh_div_cosh]
  exact Real.contDiff_sinh.div Real.contDiff_cosh
    (fun x => (Real.cosh_pos x).ne')

private lemma property_sechDeriv_comp_moderate (a b : ℝ) :
    HasModerateGrowth
      (fun z => -propertySech (a + b * z) * Real.tanh (a + b * z)) := by
  refine ⟨3 * (1 + |b|), 0, by positivity, ?_, ?_⟩
  · intro z
    simpa only [pow_zero, mul_one] using
      (show |-propertySech (a + b * z) * Real.tanh (a + b * z)| ≤
          3 * (1 + |b|) by
        have hz := property_sechDeriv_abs_le_one (a + b * z)
        have hb := abs_nonneg b
        nlinarith)
  · intro z
    rw [property_sechDeriv_comp_deriv]
    simpa only [pow_zero, mul_one] using
      (show |b * propertySechSecond (a + b * z)| ≤ 3 * (1 + |b|) by
        rw [abs_mul]
        have hs := property_sechSecond_abs_le_two (a + b * z)
        have hb := abs_nonneg b
        nlinarith [mul_le_mul_of_nonneg_left hs hb])

private lemma property_sech3Deriv_comp_moderate (a b : ℝ) :
    HasModerateGrowth
      (fun z => -3 * propertySech3 (a + b * z) * Real.tanh (a + b * z)) := by
  refine ⟨16 * (1 + |b|), 0, by positivity, ?_, ?_⟩
  · intro z
    simpa only [pow_zero, mul_one] using
      (show |-3 * propertySech3 (a + b * z) * Real.tanh (a + b * z)| ≤
          16 * (1 + |b|) by
        have hz := property_sech3Deriv_abs_le_three (a + b * z)
        have hb := abs_nonneg b
        nlinarith)
  · intro z
    rw [property_sech3Deriv_comp_deriv]
    simpa only [pow_zero, mul_one] using
      (show |b * propertySech3Second (a + b * z)| ≤ 16 * (1 + |b|) by
        rw [abs_mul]
        have hs := property_sech3Second_abs_le_twelve (a + b * z)
        have hb := abs_nonneg b
        nlinarith [mul_le_mul_of_nonneg_left hs hb])

private lemma property_smoothSech_hasDerivAt_r_raw {r x : ℝ} (hr : 0 < r) :
    HasDerivAt (fun t => propertySmoothSech t x)
      (standardGaussianExpectation (fun z =>
        (-propertySech (x + Real.sqrt r * z) *
          Real.tanh (x + Real.sqrt r * z)) *
            (1 / (2 * Real.sqrt r) * z))) r := by
  unfold propertySmoothSech standardGaussianExpectation
  let F : ℝ → ℝ → ℝ := fun t z => propertySech (x + Real.sqrt t * z)
  let F' : ℝ → ℝ → ℝ := fun t z =>
    (-propertySech (x + Real.sqrt t * z) * Real.tanh (x + Real.sqrt t * z)) *
      (1 / (2 * Real.sqrt t) * z)
  let c : ℝ := Real.sqrt (r / 2)
  have hhalf : 0 < r / 2 := by linarith
  have hc : 0 < c := Real.sqrt_pos.2 hhalf
  have hboundInt : Integrable (fun z : ℝ => c⁻¹ * |z|) (gaussianReal 0 1) := by
    have hz : Integrable (fun z : ℝ => |z|) (gaussianReal 0 1) := by
      simpa using integrable_abs_pow_gaussianReal_centered (1 : ℝ≥0) 1
    exact hz.const_mul c⁻¹
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (F := F) (F' := F') (x₀ := r)
    (s := Set.Ioi (r / 2)) (bound := fun z => c⁻¹ * |z|)
    (Ioi_mem_nhds (by linarith))
    (Filter.Eventually.of_forall fun t =>
      (property_continuous_sech.comp
        (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable)
    (by simpa [F] using property_integrable_sech_affine x (Real.sqrt r))
    (by
      apply Continuous.aestronglyMeasurable
      dsimp [F']
      have harg : Continuous (fun z : ℝ => x + Real.sqrt r * z) :=
        continuous_const.add (continuous_const.mul continuous_id)
      exact (((property_continuous_sech.comp harg).neg.mul
        (property_continuous_tanh.comp harg)).mul
          ((continuous_const : Continuous (fun _ : ℝ => 1 / (2 * Real.sqrt r))).mul
            continuous_id)))
    (by
      filter_upwards [] with z
      intro t ht
      have htpos : 0 < t := lt_trans hhalf ht
      have hroot : 0 < Real.sqrt t := Real.sqrt_pos.2 htpos
      have hrootle : c ≤ Real.sqrt t := Real.sqrt_le_sqrt ht.le
      have hinv : (Real.sqrt t)⁻¹ ≤ c⁻¹ := (inv_le_inv₀ hroot hc).2 hrootle
      have hcoef : |1 / (2 * Real.sqrt t)| ≤ c⁻¹ := by
        rw [abs_of_pos (by positivity : 0 < 1 / (2 * Real.sqrt t))]
        calc
          1 / (2 * Real.sqrt t) ≤ (Real.sqrt t)⁻¹ := by
            rw [one_div]
            exact (inv_le_inv₀ (by positivity) hroot).2 (by nlinarith)
          _ ≤ c⁻¹ := hinv
      dsimp [F']
      calc
        |(-propertySech (x + Real.sqrt t * z) * Real.tanh (x + Real.sqrt t * z)) *
            (1 / (2 * Real.sqrt t) * z)| =
            |-propertySech (x + Real.sqrt t * z) * Real.tanh (x + Real.sqrt t * z)| *
              |1 / (2 * Real.sqrt t)| * |z| := by simp only [abs_mul]; ring
        _ ≤ c⁻¹ * |z| := by
          have hp :
              |-propertySech (x + Real.sqrt t * z) * Real.tanh (x + Real.sqrt t * z)| *
                  |1 / (2 * Real.sqrt t)| ≤ c⁻¹ := by
            calc
              _ ≤ 1 * c⁻¹ := mul_le_mul (property_sechDeriv_abs_le_one _) hcoef
                (abs_nonneg _) (by norm_num)
              _ = c⁻¹ := one_mul _
          exact mul_le_mul_of_nonneg_right hp (abs_nonneg z))
    hboundInt
    (by
      filter_upwards [] with z
      intro t ht
      have htpos : 0 < t := lt_trans hhalf ht
      have hsqrt := Real.hasDerivAt_sqrt htpos.ne'
      have harg : HasDerivAt (fun t => x + Real.sqrt t * z)
          (1 / (2 * Real.sqrt t) * z) t := (hsqrt.mul_const z).const_add x
      simpa [F, F', Function.comp_def] using
        (property_sech_hasDerivAt _).comp t harg)
  simpa [F, F'] using h.2

private lemma property_smoothSech_hasDerivAt_r {r x : ℝ} (hr : 0 < r) :
    HasDerivAt (fun t => propertySmoothSech t x)
      ((1 / 2) * standardGaussianExpectation (fun z =>
        propertySechSecond (x + Real.sqrt r * z))) r := by
  apply (property_smoothSech_hasDerivAt_r_raw (x := x) hr).congr_deriv
  unfold standardGaussianExpectation
  let F : ℝ → ℝ := fun z =>
    -propertySech (x + Real.sqrt r * z) * Real.tanh (x + Real.sqrt r * z)
  have hcont : ContDiff ℝ 1 F := by
    exact ((property_contDiff_sech.neg.mul property_contDiff_tanh).of_le (by norm_num)).comp
      (by fun_prop)
  have hibp := gaussianReal_integration_by_parts (v := (1 : ℝ≥0)) one_ne_zero
    hcont (property_sechDeriv_comp_moderate x (Real.sqrt r))
  have hderiv : deriv F = fun z => Real.sqrt r *
      propertySechSecond (x + Real.sqrt r * z) := by
    funext z
    exact property_sechDeriv_comp_deriv x (Real.sqrt r) z
  rw [hderiv] at hibp
  simp only [NNReal.coe_one, one_mul] at hibp
  have hsqrt : Real.sqrt r ≠ 0 := (Real.sqrt_pos.2 hr).ne'
  calc
    ∫ z, F z * (1 / (2 * Real.sqrt r) * z) ∂gaussianReal 0 1 =
        (1 / (2 * Real.sqrt r)) * ∫ z, z * F z ∂gaussianReal 0 1 := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards [] with z
          ring
    _ = (1 / (2 * Real.sqrt r)) *
        ∫ z, Real.sqrt r * propertySechSecond (x + Real.sqrt r * z)
          ∂gaussianReal 0 1 := by rw [hibp]
    _ = (1 / 2) * ∫ z, propertySechSecond (x + Real.sqrt r * z)
          ∂gaussianReal 0 1 := by
          rw [integral_const_mul]
          field_simp [hsqrt]

private lemma property_smoothSech3_hasDerivAt_r_raw {r x : ℝ} (hr : 0 < r) :
    HasDerivAt (fun t => propertySmoothSech3 t x)
      (standardGaussianExpectation (fun z =>
        (-3 * propertySech3 (x + Real.sqrt r * z) *
          Real.tanh (x + Real.sqrt r * z)) *
            (1 / (2 * Real.sqrt r) * z))) r := by
  unfold propertySmoothSech3 standardGaussianExpectation
  let F : ℝ → ℝ → ℝ := fun t z => propertySech3 (x + Real.sqrt t * z)
  let F' : ℝ → ℝ → ℝ := fun t z =>
    (-3 * propertySech3 (x + Real.sqrt t * z) *
      Real.tanh (x + Real.sqrt t * z)) * (1 / (2 * Real.sqrt t) * z)
  let c : ℝ := Real.sqrt (r / 2)
  have hhalf : 0 < r / 2 := by linarith
  have hc : 0 < c := Real.sqrt_pos.2 hhalf
  have hboundInt : Integrable (fun z : ℝ => (3 * c⁻¹) * |z|)
      (gaussianReal 0 1) := by
    have hz : Integrable (fun z : ℝ => |z|) (gaussianReal 0 1) := by
      simpa using integrable_abs_pow_gaussianReal_centered (1 : ℝ≥0) 1
    exact hz.const_mul (3 * c⁻¹)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (F := F) (F' := F') (x₀ := r)
    (s := Set.Ioi (r / 2)) (bound := fun z => (3 * c⁻¹) * |z|)
    (Ioi_mem_nhds (by linarith))
    (Filter.Eventually.of_forall fun t =>
      ((property_continuous_sech.comp
        (continuous_const.add (continuous_const.mul continuous_id))).pow 3)
          |>.aestronglyMeasurable)
    (by simpa [F] using property_integrable_sech3_affine x (Real.sqrt r))
    (by
      apply Continuous.aestronglyMeasurable
      dsimp [F']
      have harg : Continuous (fun z : ℝ => x + Real.sqrt r * z) :=
        continuous_const.add (continuous_const.mul continuous_id)
      exact (((continuous_const.mul ((property_continuous_sech.comp harg).pow 3)).mul
        (property_continuous_tanh.comp harg)).mul
          ((continuous_const : Continuous (fun _ : ℝ => 1 / (2 * Real.sqrt r))).mul
            continuous_id)))
    (by
      filter_upwards [] with z
      intro t ht
      have htpos : 0 < t := lt_trans hhalf ht
      have hroot : 0 < Real.sqrt t := Real.sqrt_pos.2 htpos
      have hrootle : c ≤ Real.sqrt t := Real.sqrt_le_sqrt ht.le
      have hinv : (Real.sqrt t)⁻¹ ≤ c⁻¹ := (inv_le_inv₀ hroot hc).2 hrootle
      have hcoef : |1 / (2 * Real.sqrt t)| ≤ c⁻¹ := by
        rw [abs_of_pos (by positivity : 0 < 1 / (2 * Real.sqrt t))]
        calc
          1 / (2 * Real.sqrt t) ≤ (Real.sqrt t)⁻¹ := by
            rw [one_div]
            exact (inv_le_inv₀ (by positivity) hroot).2 (by nlinarith)
          _ ≤ c⁻¹ := hinv
      dsimp [F']
      calc
        |(-3 * propertySech3 (x + Real.sqrt t * z) *
              Real.tanh (x + Real.sqrt t * z)) *
            (1 / (2 * Real.sqrt t) * z)| =
            |-3 * propertySech3 (x + Real.sqrt t * z) *
              Real.tanh (x + Real.sqrt t * z)| *
              |1 / (2 * Real.sqrt t)| * |z| := by simp only [abs_mul]; ring
        _ ≤ (3 * c⁻¹) * |z| := by
          have hp : |-3 * propertySech3 (x + Real.sqrt t * z) *
                Real.tanh (x + Real.sqrt t * z)| *
                |1 / (2 * Real.sqrt t)| ≤ 3 * c⁻¹ := by
            exact mul_le_mul (property_sech3Deriv_abs_le_three _) hcoef
              (abs_nonneg _) (by norm_num)
          exact mul_le_mul_of_nonneg_right hp (abs_nonneg z))
    hboundInt
    (by
      filter_upwards [] with z
      intro t ht
      have htpos : 0 < t := lt_trans hhalf ht
      have hsqrt := Real.hasDerivAt_sqrt htpos.ne'
      have harg : HasDerivAt (fun t => x + Real.sqrt t * z)
          (1 / (2 * Real.sqrt t) * z) t := (hsqrt.mul_const z).const_add x
      simpa [F, F', Function.comp_def] using
        (property_sech3_hasDerivAt _).comp t harg)
  simpa [F, F'] using h.2

private lemma property_smoothSech3_hasDerivAt_r {r x : ℝ} (hr : 0 < r) :
    HasDerivAt (fun t => propertySmoothSech3 t x)
      ((1 / 2) * standardGaussianExpectation (fun z =>
        propertySech3Second (x + Real.sqrt r * z))) r := by
  apply (property_smoothSech3_hasDerivAt_r_raw (x := x) hr).congr_deriv
  unfold standardGaussianExpectation
  let F : ℝ → ℝ := fun z =>
    -3 * propertySech3 (x + Real.sqrt r * z) * Real.tanh (x + Real.sqrt r * z)
  have hcont : ContDiff ℝ 1 F := by
    exact (((contDiff_const.mul (property_contDiff_sech.pow 3)).mul property_contDiff_tanh)
      |>.of_le (by norm_num)).comp (by fun_prop)
  have hibp := gaussianReal_integration_by_parts (v := (1 : ℝ≥0)) one_ne_zero
    hcont (property_sech3Deriv_comp_moderate x (Real.sqrt r))
  have hderiv : deriv F = fun z => Real.sqrt r *
      propertySech3Second (x + Real.sqrt r * z) := by
    funext z
    exact property_sech3Deriv_comp_deriv x (Real.sqrt r) z
  rw [hderiv] at hibp
  simp only [NNReal.coe_one, one_mul] at hibp
  have hsqrt : Real.sqrt r ≠ 0 := (Real.sqrt_pos.2 hr).ne'
  calc
    ∫ z, F z * (1 / (2 * Real.sqrt r) * z) ∂gaussianReal 0 1 =
        (1 / (2 * Real.sqrt r)) * ∫ z, z * F z ∂gaussianReal 0 1 := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards [] with z
          ring
    _ = (1 / (2 * Real.sqrt r)) *
        ∫ z, Real.sqrt r * propertySech3Second (x + Real.sqrt r * z)
          ∂gaussianReal 0 1 := by rw [hibp]
    _ = (1 / 2) * ∫ z, propertySech3Second (x + Real.sqrt r * z)
          ∂gaussianReal 0 1 := by
          rw [integral_const_mul]
          field_simp [hsqrt]

private lemma property_smoothSech3Second_abs_le_twelve (r x : ℝ) :
    |standardGaussianExpectation (fun z =>
      propertySech3Second (x + Real.sqrt r * z))| ≤ 12 := by
  unfold standardGaussianExpectation
  calc
    |∫ z, propertySech3Second (x + Real.sqrt r * z) ∂gaussianReal 0 1| ≤
        ∫ z, |propertySech3Second (x + Real.sqrt r * z)| ∂gaussianReal 0 1 :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _z : ℝ, (12 : ℝ) ∂gaussianReal 0 1 := by
      exact integral_mono (property_integrable_sech3Second_affine x (Real.sqrt r)).abs
        (integrable_const 12) fun z => property_sech3Second_abs_le_twelve _
    _ = 12 := by simp

private lemma property_continuous_sech3Second : Continuous propertySech3Second := by
  unfold propertySech3Second propertySech3
  exact (((continuous_const.mul (property_continuous_sech.pow 3)).mul
    (property_continuous_tanh.pow 2)).sub
    ((continuous_const.mul (property_continuous_sech.pow 3)).mul
      (property_continuous_sech.pow 2)))

private lemma property_continuous_smoothSech3Second (r : ℝ) :
    Continuous (fun x => standardGaussianExpectation (fun z =>
      propertySech3Second (x + Real.sqrt r * z))) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  unfold standardGaussianExpectation
  have hmeas : ∀ᶠ x in nhds x₀,
      AEStronglyMeasurable (fun z =>
        propertySech3Second (x + Real.sqrt r * z)) (gaussianReal 0 1) :=
    Filter.Eventually.of_forall fun x =>
      (property_continuous_sech3Second.comp (by fun_prop)).aestronglyMeasurable
  have hbound : ∀ᶠ x in nhds x₀, ∀ᵐ z ∂gaussianReal 0 1,
      ‖propertySech3Second (x + Real.sqrt r * z)‖ ≤ (12 : ℝ) := by
    exact Filter.Eventually.of_forall fun x => ae_of_all _ fun z => by
      simpa [Real.norm_eq_abs] using property_sech3Second_abs_le_twelve
        (x + Real.sqrt r * z)
  have hlim : ∀ᵐ z ∂gaussianReal 0 1,
      Tendsto (fun x => propertySech3Second (x + Real.sqrt r * z)) (nhds x₀)
        (nhds (propertySech3Second (x₀ + Real.sqrt r * z))) := by
    exact ae_of_all _ fun z =>
      (property_continuous_sech3Second.comp (by fun_prop)).continuousAt.tendsto
  exact tendsto_integral_filter_of_dominated_convergence
    (l := nhds x₀)
    (F := fun x z => propertySech3Second (x + Real.sqrt r * z))
    (f := fun z => propertySech3Second (x₀ + Real.sqrt r * z))
    (bound := fun _ => (12 : ℝ)) hmeas hbound (integrable_const 12) hlim

private lemma property_smoothSech_hasDerivAt_x (r x : ℝ) :
    HasDerivAt (propertySmoothSech r)
      (standardGaussianExpectation (fun z =>
        -propertySech (x + Real.sqrt r * z) *
          Real.tanh (x + Real.sqrt r * z))) x := by
  unfold propertySmoothSech standardGaussianExpectation
  let F : ℝ → ℝ → ℝ := fun y z => propertySech (y + Real.sqrt r * z)
  let F' : ℝ → ℝ → ℝ := fun y z =>
    -propertySech (y + Real.sqrt r * z) * Real.tanh (y + Real.sqrt r * z)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (F := F) (F' := F') (x₀ := x)
    (s := Set.univ) (bound := fun _ => (1 : ℝ))
    (by simp)
    (Filter.Eventually.of_forall fun y =>
      (property_continuous_sech.comp
        (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable)
    (by simpa [F] using property_integrable_sech_affine x (Real.sqrt r))
    (by
      have harg : Continuous (fun z : ℝ => x + Real.sqrt r * z) :=
        continuous_const.add (continuous_const.mul continuous_id)
      exact ((property_continuous_sech.comp harg).neg.mul
        (property_continuous_tanh.comp harg)).aestronglyMeasurable)
    (by
      filter_upwards [] with z
      intro y _
      simpa [F', Real.norm_eq_abs] using
        property_sechDeriv_abs_le_one (y + Real.sqrt r * z))
    (integrable_const 1)
    (by
      filter_upwards [] with z
      intro y _
      simpa [F, F', Function.comp_def] using
        (property_sech_hasDerivAt _).comp y
          ((hasDerivAt_id y).add_const (Real.sqrt r * z)))
  simpa [F, F'] using h.2

private lemma property_smoothSech3_hasDerivAt_x (r x : ℝ) :
    HasDerivAt (propertySmoothSech3 r)
      (standardGaussianExpectation (fun z =>
        -3 * propertySech3 (x + Real.sqrt r * z) *
          Real.tanh (x + Real.sqrt r * z))) x := by
  unfold propertySmoothSech3 standardGaussianExpectation
  let F : ℝ → ℝ → ℝ := fun y z => propertySech3 (y + Real.sqrt r * z)
  let F' : ℝ → ℝ → ℝ := fun y z =>
    -3 * propertySech3 (y + Real.sqrt r * z) * Real.tanh (y + Real.sqrt r * z)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (F := F) (F' := F') (x₀ := x)
    (s := Set.univ) (bound := fun _ => (3 : ℝ))
    (by simp)
    (Filter.Eventually.of_forall fun y =>
      ((property_continuous_sech.comp
        (continuous_const.add (continuous_const.mul continuous_id))).pow 3)
        |>.aestronglyMeasurable)
    (by simpa [F] using property_integrable_sech3_affine x (Real.sqrt r))
    (by
      have harg : Continuous (fun z : ℝ => x + Real.sqrt r * z) :=
        continuous_const.add (continuous_const.mul continuous_id)
      exact ((continuous_const.mul ((property_continuous_sech.comp harg).pow 3)).mul
        (property_continuous_tanh.comp harg)).aestronglyMeasurable)
    (by
      filter_upwards [] with z
      intro y _
      simpa [F', Real.norm_eq_abs] using
        property_sech3Deriv_abs_le_three (y + Real.sqrt r * z))
    (integrable_const 3)
    (by
      filter_upwards [] with z
      intro y _
      simpa [F, F', Function.comp_def] using
        (property_sech3_hasDerivAt _).comp y
          ((hasDerivAt_id y).add_const (Real.sqrt r * z)))
  simpa [F, F'] using h.2

private lemma property_continuous_smoothSech (r : ℝ) :
    Continuous (propertySmoothSech r) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (property_smoothSech_hasDerivAt_x r x).continuousAt

private lemma property_continuous_smoothSech3 (r : ℝ) :
    Continuous (propertySmoothSech3 r) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (property_smoothSech3_hasDerivAt_x r x).continuousAt

private lemma property_smoothSech_nonneg (r x : ℝ) :
    0 ≤ propertySmoothSech r x := by
  unfold propertySmoothSech standardGaussianExpectation
  exact integral_nonneg fun z => (propertySech_pos _).le

private lemma property_smoothSech3_nonneg (r x : ℝ) :
    0 ≤ propertySmoothSech3 r x := by
  unfold propertySmoothSech3 standardGaussianExpectation
  exact integral_nonneg fun z => pow_nonneg (propertySech_pos _).le 3

private lemma property_smoothSech_le_one (r x : ℝ) :
    propertySmoothSech r x ≤ 1 := by
  unfold propertySmoothSech standardGaussianExpectation
  calc
    (∫ z, propertySech (x + Real.sqrt r * z) ∂gaussianReal 0 1) ≤
        ∫ _z : ℝ, (1 : ℝ) ∂gaussianReal 0 1 := by
          exact integral_mono (property_integrable_sech_affine x (Real.sqrt r))
            (integrable_const 1) fun z => propertySech_le_one _
    _ = 1 := by simp

private lemma property_smoothSech3_le_one (r x : ℝ) :
    propertySmoothSech3 r x ≤ 1 := by
  unfold propertySmoothSech3 standardGaussianExpectation
  calc
    (∫ z, propertySech3 (x + Real.sqrt r * z) ∂gaussianReal 0 1) ≤
        ∫ _z : ℝ, (1 : ℝ) ∂gaussianReal 0 1 := by
          exact integral_mono (property_integrable_sech3_affine x (Real.sqrt r))
            (integrable_const 1) fun z => by
              rw [show propertySech3 (x + Real.sqrt r * z) =
                propertySech (x + Real.sqrt r * z) ^ 3 by rfl]
              exact pow_le_one₀ (propertySech_pos _).le (propertySech_le_one _)
    _ = 1 := by simp

noncomputable def propertyTiltedTanhSq (r x : ℝ) : ℝ :=
  1 - Real.exp (-r / 2) * propertySech x * propertySmoothSech r x

noncomputable def propertyTiltedSech4 (r x : ℝ) : ℝ :=
  Real.exp (-r / 2) * propertySech x * propertySmoothSech3 r x

private noncomputable def propertyTiltedSech4TimeDerivative (r x : ℝ) : ℝ :=
  ((-1 / 2) * Real.exp (-r / 2) * propertySech x) * propertySmoothSech3 r x +
    (Real.exp (-r / 2) * propertySech x) *
      ((1 / 2) * standardGaussianExpectation (fun z =>
        propertySech3Second (x + Real.sqrt r * z)))

private lemma property_tiltedSech4_hasDerivAt_r {r x : ℝ} (hr : 0 < r) :
    HasDerivAt (fun t => propertyTiltedSech4 t x)
      (propertyTiltedSech4TimeDerivative r x) r := by
  have he : HasDerivAt (fun t : ℝ => Real.exp (-t / 2))
      ((-1 / 2) * Real.exp (-r / 2)) r := by
    have hinner : HasDerivAt (fun t : ℝ => -t / 2) (-1 / 2) r := by
      rw [show (fun t : ℝ => -t / 2) = fun t => (-1 / 2) * t by
        funext t
        ring]
      simpa using (hasDerivAt_id r).const_mul (-1 / 2)
    simpa only [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_exp (-r / 2)).comp r hinner
  have hs := property_smoothSech3_hasDerivAt_r (x := x) hr
  exact ((he.mul_const (propertySech x)).mul hs).congr_deriv (by
    unfold propertyTiltedSech4TimeDerivative
    ring)

private lemma property_tiltedSech4TimeDerivative_abs_le_seven
    {r : ℝ} (hr : 0 ≤ r) (x : ℝ) :
    |propertyTiltedSech4TimeDerivative r x| ≤ 7 := by
  have he : Real.exp (-r / 2) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have he0 : 0 ≤ Real.exp (-r / 2) := (Real.exp_pos _).le
  have hsech0 : 0 ≤ propertySech x := (propertySech_pos x).le
  have hsmooth0 : 0 ≤ propertySmoothSech3 r x := property_smoothSech3_nonneg r x
  have hfirst :
      |((-1 / 2) * Real.exp (-r / 2) * propertySech x) *
        propertySmoothSech3 r x| ≤ 1 / 2 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg he0,
      abs_of_nonneg hsech0, abs_of_nonneg hsmooth0]
    norm_num
    have hprod : Real.exp (-r / 2) * propertySech x *
        propertySmoothSech3 r x ≤ 1 := by
      calc
        Real.exp (-r / 2) * propertySech x * propertySmoothSech3 r x ≤
            1 * propertySech x * propertySmoothSech3 r x := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right he hsech0) hsmooth0
        _ ≤ 1 * 1 * propertySmoothSech3 r x := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (propertySech_le_one x) (by norm_num)) hsmooth0
        _ ≤ 1 * 1 * 1 := by
          exact mul_le_mul_of_nonneg_left (property_smoothSech3_le_one r x) (by norm_num)
        _ = 1 := by norm_num
    nlinarith
  have hsecond :
      |(Real.exp (-r / 2) * propertySech x) *
        ((1 / 2) * standardGaussianExpectation (fun z =>
          propertySech3Second (x + Real.sqrt r * z)))| ≤ 6 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg he0, abs_of_nonneg hsech0]
    norm_num
    have hprod : Real.exp (-r / 2) * propertySech x ≤ 1 := by
      calc
        Real.exp (-r / 2) * propertySech x ≤ 1 * propertySech x :=
          mul_le_mul_of_nonneg_right he hsech0
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left (propertySech_le_one x) (by norm_num)
        _ = 1 := by norm_num
    have hinner := property_smoothSech3Second_abs_le_twelve r x
    nlinarith [mul_le_mul hprod hinner (abs_nonneg _) (by positivity : 0 ≤ (1 : ℝ))]
  unfold propertyTiltedSech4TimeDerivative
  exact (abs_add_le _ _).trans (by linarith)

private lemma property_continuous_tiltedSech4TimeDerivative (r : ℝ) :
    Continuous (propertyTiltedSech4TimeDerivative r) := by
  unfold propertyTiltedSech4TimeDerivative
  exact (((continuous_const.mul property_continuous_sech).mul
    (property_continuous_smoothSech3 r)).add
      ((continuous_const.mul property_continuous_sech).mul
        (continuous_const.mul (property_continuous_smoothSech3Second r))))

private lemma property_tiltedSech4_nonneg {r : ℝ} (_hr : 0 ≤ r) (x : ℝ) :
    0 ≤ propertyTiltedSech4 r x := by
  unfold propertyTiltedSech4
  exact mul_nonneg
    (mul_nonneg (Real.exp_pos _).le (propertySech_pos x).le)
    (property_smoothSech3_nonneg r x)

private lemma property_tiltedSech4_le_one {r : ℝ} (hr : 0 ≤ r) (x : ℝ) :
    propertyTiltedSech4 r x ≤ 1 := by
  have he : Real.exp (-r / 2) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  unfold propertyTiltedSech4
  calc
    Real.exp (-r / 2) * propertySech x * propertySmoothSech3 r x ≤
        1 * 1 * 1 := by
          have h₁ : Real.exp (-r / 2) * propertySech x ≤ 1 * 1 := by
            calc
              _ ≤ 1 * propertySech x :=
                mul_le_mul_of_nonneg_right he (propertySech_pos x).le
              _ ≤ 1 * 1 :=
                mul_le_mul_of_nonneg_left (propertySech_le_one x) (by norm_num)
          calc
            _ ≤ (1 * 1) * propertySmoothSech3 r x :=
              mul_le_mul_of_nonneg_right h₁ (property_smoothSech3_nonneg r x)
            _ ≤ (1 * 1) * 1 :=
              mul_le_mul_of_nonneg_left (property_smoothSech3_le_one r x) (by norm_num)
    _ = 1 := by norm_num

private lemma property_tiltedTanhSq_mem_Icc {r : ℝ} (hr : 0 ≤ r) (x : ℝ) :
    propertyTiltedTanhSq r x ∈ Set.Icc (0 : ℝ) 1 := by
  have he : Real.exp (-r / 2) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hp : 0 ≤ Real.exp (-r / 2) * propertySech x * propertySmoothSech r x := by
    exact mul_nonneg
      (mul_nonneg (Real.exp_pos _).le (propertySech_pos x).le)
      (property_smoothSech_nonneg r x)
  have hp1 : Real.exp (-r / 2) * propertySech x * propertySmoothSech r x ≤ 1 := by
    have h₁ : Real.exp (-r / 2) * propertySech x ≤ 1 * 1 := by
      calc
        _ ≤ 1 * propertySech x :=
          mul_le_mul_of_nonneg_right he (propertySech_pos x).le
        _ ≤ 1 * 1 :=
          mul_le_mul_of_nonneg_left (propertySech_le_one x) (by norm_num)
    calc
      _ ≤ (1 * 1) * propertySmoothSech r x :=
        mul_le_mul_of_nonneg_right h₁ (property_smoothSech_nonneg r x)
      _ ≤ (1 * 1) * 1 :=
        mul_le_mul_of_nonneg_left (property_smoothSech_le_one r x) (by norm_num)
      _ = 1 := by norm_num
  unfold propertyTiltedTanhSq
  constructor <;> linarith

private lemma property_smoothSechSecond_identity (r x : ℝ) :
    standardGaussianExpectation (fun z =>
      propertySechSecond (x + Real.sqrt r * z)) =
      propertySmoothSech r x - 2 * propertySmoothSech3 r x := by
  have hpoint (z : ℝ) : propertySechSecond (x + Real.sqrt r * z) =
      propertySech (x + Real.sqrt r * z) -
        2 * propertySech3 (x + Real.sqrt r * z) := by
    have hid := property_tanh_sq_add_sech_sq (x + Real.sqrt r * z)
    unfold propertySechSecond propertySech3
    linear_combination propertySech (x + Real.sqrt r * z) * hid
  change (∫ z, propertySechSecond (x + Real.sqrt r * z) ∂gaussianReal 0 1) =
    (∫ z, propertySech (x + Real.sqrt r * z) ∂gaussianReal 0 1) -
      2 * ∫ z, propertySech3 (x + Real.sqrt r * z) ∂gaussianReal 0 1
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  rw [integral_sub (property_integrable_sech_affine x (Real.sqrt r))
    ((property_integrable_sech3_affine x (Real.sqrt r)).const_mul 2)]
  rw [integral_const_mul]

private lemma property_tiltedTanhSq_hasDerivAt_r {r x : ℝ} (hr : 0 < r) :
    HasDerivAt (fun t => propertyTiltedTanhSq t x)
      (propertyTiltedSech4 r x) r := by
  have he : HasDerivAt (fun t : ℝ => Real.exp (-t / 2))
      ((-1 / 2) * Real.exp (-r / 2)) r := by
    have hinner : HasDerivAt (fun t : ℝ => -t / 2) (-1 / 2) r := by
      rw [show (fun t : ℝ => -t / 2) = fun t => (-1 / 2) * t by
        funext t
        ring]
      simpa using (hasDerivAt_id r).const_mul (-1 / 2)
    simpa only [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_exp (-r / 2)).comp r hinner
  have hs := property_smoothSech_hasDerivAt_r (x := x) hr
  apply ((he.mul_const (propertySech x)).mul hs).neg.const_add 1 |>.congr_deriv
  rw [property_smoothSechSecond_identity r x]
  unfold propertyTiltedSech4
  ring

private lemma property_integrable_cosh_mul_gaussian (c : ℝ) :
    Integrable (fun z : ℝ => Real.cosh (c * z)) (gaussianReal 0 1) := by
  simp_rw [Real.cosh_eq]
  apply Integrable.div_const
  apply Integrable.add
  · exact integrable_exp_mul_gaussianReal c
  · simpa only [neg_mul] using integrable_exp_mul_gaussianReal (-c)

private lemma property_standardGaussianExpectation_cosh (r x : ℝ) (hr : 0 ≤ r) :
    standardGaussianExpectation (fun z => Real.cosh (x + Real.sqrt r * z)) =
      Real.exp (r / 2) * Real.cosh x := by
  have hexp (c : ℝ) : standardGaussianExpectation (fun z => Real.exp (c * z)) =
      Real.exp (c ^ 2 / 2) := by
    change ProbabilityTheory.mgf id (gaussianReal 0 1) c = Real.exp (c ^ 2 / 2)
    rw [congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) c]
    congr 1
    norm_num
  have hcosh : standardGaussianExpectation
      (fun z => Real.cosh (Real.sqrt r * z)) = Real.exp (r / 2) := by
    unfold standardGaussianExpectation
    simp_rw [Real.cosh_eq]
    rw [integral_div, integral_add
      (integrable_exp_mul_gaussianReal (Real.sqrt r))
      (by simpa only [neg_mul] using integrable_exp_mul_gaussianReal (-Real.sqrt r))]
    rw [show (∫ z, Real.exp (Real.sqrt r * z) ∂gaussianReal 0 1) =
        Real.exp ((Real.sqrt r) ^ 2 / 2) by exact hexp _]
    rw [show (∫ z, Real.exp (-(Real.sqrt r * z)) ∂gaussianReal 0 1) =
        Real.exp ((-Real.sqrt r) ^ 2 / 2) by
          simpa only [standardGaussianExpectation, neg_mul] using hexp (-Real.sqrt r)]
    rw [show (-Real.sqrt r) ^ 2 = (Real.sqrt r) ^ 2 by ring,
      Real.sq_sqrt hr]
    ring
  have hsinhInt : Integrable (fun z : ℝ => Real.sinh (Real.sqrt r * z))
      (gaussianReal 0 1) := by
    simp_rw [Real.sinh_eq]
    exact ((integrable_exp_mul_gaussianReal (Real.sqrt r)).sub
      (by simpa only [neg_mul] using
        integrable_exp_mul_gaussianReal (-Real.sqrt r))).div_const 2
  have hsinh : standardGaussianExpectation
      (fun z => Real.sinh (Real.sqrt r * z)) = 0 := by
    unfold standardGaussianExpectation
    simp_rw [Real.sinh_eq]
    rw [integral_div, integral_sub
      (integrable_exp_mul_gaussianReal (Real.sqrt r))
      (by simpa only [neg_mul] using integrable_exp_mul_gaussianReal (-Real.sqrt r))]
    rw [show (∫ z, Real.exp (Real.sqrt r * z) ∂gaussianReal 0 1) =
        Real.exp ((Real.sqrt r) ^ 2 / 2) by exact hexp _]
    rw [show (∫ z, Real.exp (-(Real.sqrt r * z)) ∂gaussianReal 0 1) =
        Real.exp ((-Real.sqrt r) ^ 2 / 2) by
          simpa only [standardGaussianExpectation, neg_mul] using hexp (-Real.sqrt r)]
    rw [show (-Real.sqrt r) ^ 2 = (Real.sqrt r) ^ 2 by ring]
    ring
  unfold standardGaussianExpectation at hcosh hsinh ⊢
  rw [show (fun z => Real.cosh (x + Real.sqrt r * z)) =
      fun z => Real.cosh x * Real.cosh (Real.sqrt r * z) +
        Real.sinh x * Real.sinh (Real.sqrt r * z) by
          funext z
          exact Real.cosh_add x (Real.sqrt r * z)]
  rw [integral_add
    ((property_integrable_cosh_mul_gaussian (Real.sqrt r)).const_mul (Real.cosh x))
    (hsinhInt.const_mul (Real.sinh x)), integral_const_mul, integral_const_mul,
    hcosh, hsinh]
  ring

private lemma property_tanh_sq_mul_cosh (x : ℝ) :
    Real.tanh x ^ 2 * Real.cosh x = Real.cosh x - propertySech x := by
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  unfold propertySech
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [hc]
  nlinarith [Real.cosh_sq_sub_sinh_sq x]

private lemma property_sech_four_mul_cosh (x : ℝ) :
    propertySech x ^ 4 * Real.cosh x = propertySech3 x := by
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  change (Real.cosh x)⁻¹ ^ 4 * Real.cosh x = (Real.cosh x)⁻¹ ^ 3
  field_simp [hc]

private lemma tiltedHeatSemigroup_tanh_sq_eq {r : ℝ} (hr : 0 ≤ r) (x : ℝ) :
    tiltedHeatSemigroup r (fun y => Real.tanh y ^ 2) x =
      propertyTiltedTanhSq r x := by
  have hcosh : standardGaussianExpectation
      (fun z => Real.cosh (x + Real.sqrt r * z)) =
      Real.exp (r / 2) * Real.cosh x :=
    property_standardGaussianExpectation_cosh r x hr
  unfold tiltedHeatSemigroup heatSemigroup propertyTiltedTanhSq propertySmoothSech
  unfold standardGaussianExpectation at hcosh ⊢
  rw [show (fun z => Real.tanh (x + Real.sqrt r * z) ^ 2 *
      Real.cosh (x + Real.sqrt r * z)) =
      fun z => Real.cosh (x + Real.sqrt r * z) -
        propertySech (x + Real.sqrt r * z) by
          funext z
          exact property_tanh_sq_mul_cosh _]
  rw [integral_sub]
  · rw [hcosh]
    unfold propertySech
    field_simp [(Real.cosh_pos x).ne', (Real.exp_pos (r / 2)).ne']
    have heq : Real.exp (-(r / 2)) * Real.exp (r / 2) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    rw [mul_sub, ← mul_assoc, heq, one_mul]
  · have hi : Integrable (fun z : ℝ => Real.cosh (x + Real.sqrt r * z))
        (gaussianReal 0 1) := by
      have hsinhInt : Integrable (fun z : ℝ => Real.sinh (Real.sqrt r * z))
          (gaussianReal 0 1) := by
        simp_rw [Real.sinh_eq]
        exact ((integrable_exp_mul_gaussianReal (Real.sqrt r)).sub
          (by simpa only [neg_mul] using
            integrable_exp_mul_gaussianReal (-Real.sqrt r))).div_const 2
      rw [show (fun z : ℝ => Real.cosh (x + Real.sqrt r * z)) =
          (fun z : ℝ => Real.cosh x * Real.cosh (Real.sqrt r * z)) +
            fun z : ℝ => Real.sinh x * Real.sinh (Real.sqrt r * z) by
        funext z
        exact Real.cosh_add x (Real.sqrt r * z)]
      exact ((property_integrable_cosh_mul_gaussian (Real.sqrt r)).const_mul
        (Real.cosh x)).add (hsinhInt.const_mul (Real.sinh x))
    exact hi
  · exact property_integrable_sech_affine x (Real.sqrt r)

private lemma tiltedHeatSemigroup_sech_four_eq {r : ℝ} (_hr : 0 ≤ r) (x : ℝ) :
    tiltedHeatSemigroup r (fun y => propertySech y ^ 4) x =
      propertyTiltedSech4 r x := by
  unfold tiltedHeatSemigroup heatSemigroup propertyTiltedSech4 propertySmoothSech3
  unfold standardGaussianExpectation
  rw [show (fun z => propertySech (x + Real.sqrt r * z) ^ 4 *
      Real.cosh (x + Real.sqrt r * z)) =
      fun z => propertySech3 (x + Real.sqrt r * z) by
        funext z
        exact property_sech_four_mul_cosh _]
  unfold propertySech
  ring

noncomputable def propertyUpperG (β h q s u : ℝ) : ℝ :=
  heatSemigroup (β ^ 2 * q)
    (propertyTiltedTanhSq (s * β ^ 2 * (u - q))) h

noncomputable def propertyUpperSech4Expectation
    (β h q s u : ℝ) : ℝ :=
  heatSemigroup (β ^ 2 * q)
    (propertyTiltedSech4 (s * β ^ 2 * (u - q))) h

private noncomputable def propertyUpperSech4TimeExpectation
    (β h q s u : ℝ) : ℝ :=
  heatSemigroup (β ^ 2 * q)
    (propertyTiltedSech4TimeDerivative (s * β ^ 2 * (u - q))) h

private lemma propertyUpperSech4Expectation_hasDerivAt
    {β h q s u : ℝ} (hβ : 0 < β) (hs : 0 < s) (hu : q < u) :
    HasDerivAt (propertyUpperSech4Expectation β h q s)
      (s * β ^ 2 * propertyUpperSech4TimeExpectation β h q s u) u := by
  let a : ℝ := s * β ^ 2
  have ha : 0 < a := mul_pos hs (sq_pos_of_pos hβ)
  let b : ℝ := Real.sqrt (β ^ 2 * q)
  unfold propertyUpperSech4Expectation propertyUpperSech4TimeExpectation
    heatSemigroup standardGaussianExpectation
  let F : ℝ → ℝ → ℝ := fun t z =>
    propertyTiltedSech4 (a * (t - q)) (h + b * z)
  let F' : ℝ → ℝ → ℝ := fun t z =>
    a * propertyTiltedSech4TimeDerivative (a * (t - q)) (h + b * z)
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (F := F) (F' := F') (x₀ := u)
    (s := Set.Ioi q) (bound := fun _ => 7 * a)
    (Ioi_mem_nhds hu)
    (Filter.Eventually.of_forall fun t =>
      ((((continuous_const.mul property_continuous_sech).mul
          (property_continuous_smoothSech3 (a * (t - q)))).comp
        (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable))
    (by
      have hr : 0 ≤ a * (u - q) := mul_nonneg ha.le (sub_nonneg.mpr hu.le)
      apply Integrable.of_bound (C := 1)
      · exact ((((continuous_const.mul property_continuous_sech).mul
          (property_continuous_smoothSech3 (a * (u - q)))).comp
            (continuous_const.add (continuous_const.mul continuous_id)))
              |>.aestronglyMeasurable)
      · filter_upwards [] with z
        rw [Real.norm_eq_abs]
        dsimp [F]
        unfold propertyTiltedSech4
        have he : Real.exp (-(a * (u - q)) / 2) ≤ 1 := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (by linarith)
        have hnonneg : 0 ≤ Real.exp (-(a * (u - q)) / 2) *
            propertySech (h + b * z) *
              propertySmoothSech3 (a * (u - q)) (h + b * z) := by
          exact mul_nonneg
            (mul_nonneg (Real.exp_pos _).le (propertySech_pos _).le)
            (property_smoothSech3_nonneg _ _)
        rw [abs_of_nonneg hnonneg]
        calc
          Real.exp (-(a * (u - q)) / 2) * propertySech (h + b * z) *
              propertySmoothSech3 (a * (u - q)) (h + b * z) ≤
              1 * propertySech (h + b * z) *
              propertySmoothSech3 (a * (u - q)) (h + b * z) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right he (propertySech_pos _).le)
              (property_smoothSech3_nonneg _ _)
          _ ≤ 1 * 1 * propertySmoothSech3 (a * (u - q)) (h + b * z) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (propertySech_le_one _) (by norm_num))
              (property_smoothSech3_nonneg _ _)
          _ ≤ 1 * 1 * 1 := by
            exact mul_le_mul_of_nonneg_left (property_smoothSech3_le_one _ _)
              (by norm_num)
          _ = 1 := by norm_num)
    (by
      exact (continuous_const.mul
        ((property_continuous_tiltedSech4TimeDerivative (a * (u - q))).comp
          (continuous_const.add (continuous_const.mul continuous_id)))).aestronglyMeasurable)
    (by
      filter_upwards [] with z
      intro t ht
      have hr : 0 ≤ a * (t - q) := mul_nonneg ha.le (sub_nonneg.mpr ht.le)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ha.le]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left
        (property_tiltedSech4TimeDerivative_abs_le_seven hr _) ha.le)
    (integrable_const (7 * a))
    (by
      filter_upwards [] with z
      intro t ht
      have hr : 0 < a * (t - q) := mul_pos ha (sub_pos.mpr ht)
      have hinner : HasDerivAt (fun v : ℝ => a * (v - q)) a t := by
        simpa only [id_eq, mul_one] using
          ((hasDerivAt_id t).sub_const q).const_mul a
      change HasDerivAt
        (fun v => propertyTiltedSech4 (a * (v - q)) (h + b * z))
        (a * propertyTiltedSech4TimeDerivative (a * (t - q)) (h + b * z)) t
      apply ((property_tiltedSech4_hasDerivAt_r (x := h + b * z) hr).comp
        t hinner).congr_deriv
      ring)
  have h := hderiv.2
  dsimp only [F, F'] at h
  rw [integral_const_mul] at h
  simpa only [a, b] using h

private lemma propertyUpperSech4TimeExpectation_abs_le_seven
    {β h q s u : ℝ} (hs : 0 ≤ s) (hu : q ≤ u) :
    |propertyUpperSech4TimeExpectation β h q s u| ≤ 7 := by
  let r : ℝ := s * β ^ 2 * (u - q)
  have hr : 0 ≤ r := mul_nonneg (mul_nonneg hs (sq_nonneg β)) (sub_nonneg.mpr hu)
  unfold propertyUpperSech4TimeExpectation heatSemigroup standardGaussianExpectation
  calc
    |∫ z, propertyTiltedSech4TimeDerivative r
        (h + Real.sqrt (β ^ 2 * q) * z) ∂gaussianReal 0 1| ≤
        ∫ z, |propertyTiltedSech4TimeDerivative r
          (h + Real.sqrt (β ^ 2 * q) * z)| ∂gaussianReal 0 1 :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _z : ℝ, (7 : ℝ) ∂gaussianReal 0 1 := by
      apply integral_mono
      · have hi : Integrable (fun z => propertyTiltedSech4TimeDerivative r
            (h + Real.sqrt (β ^ 2 * q) * z)) (gaussianReal 0 1) := by
          apply Integrable.of_bound (C := 7)
          · exact ((property_continuous_tiltedSech4TimeDerivative r).comp
              (by fun_prop)).aestronglyMeasurable
          · filter_upwards [] with z
            simpa [Real.norm_eq_abs] using
              property_tiltedSech4TimeDerivative_abs_le_seven hr
                (h + Real.sqrt (β ^ 2 * q) * z)
        exact hi.abs
      · exact integrable_const 7
      · intro z
        exact property_tiltedSech4TimeDerivative_abs_le_seven hr _
    _ = 7 := by simp

private lemma scalarOrderParameterCorrect_eq_propertyUpperG
    {β h s u : ℝ} (hs : 0 ≤ s) (hu : rsQ β h < u) :
    scalarOrderParameterCorrect β h s u =
      propertyUpperG β h (rsQ β h) s u := by
  have hnot : ¬u ≤ rsQ β h := not_le_of_gt hu
  have hmax : max (rsQ β h - u) 0 = 0 := max_eq_right (sub_nonpos.mpr hu.le)
  have hpsi (x : ℝ) : scalarPsiX β (rsQ β h) s u x = Real.tanh x := by
    unfold scalarPsiX
    rw [hmax]
    simp [standardGaussianExpectation]
  unfold scalarOrderParameterCorrect scalarOrderParameter localFieldExpectation
    propertyUpperG
  simp only [if_neg hnot, hpsi]
  congr 2
  funext x
  exact tiltedHeatSemigroup_tanh_sq_eq
    (mul_nonneg (mul_nonneg hs (sq_nonneg β)) (sub_nonneg.mpr hu.le)) x

private lemma property_continuous_tiltedTanhSq (r : ℝ) :
    Continuous (propertyTiltedTanhSq r) := by
  unfold propertyTiltedTanhSq
  exact continuous_const.sub
    ((continuous_const.mul property_continuous_sech).mul
      (property_continuous_smoothSech r))

private lemma property_continuous_tiltedSech4 (r : ℝ) :
    Continuous (propertyTiltedSech4 r) := by
  unfold propertyTiltedSech4
  exact (continuous_const.mul property_continuous_sech).mul
    (property_continuous_smoothSech3 r)

private lemma property_integrable_tiltedTanhSq_affine
    {r : ℝ} (hr : 0 ≤ r) (a b : ℝ) :
    Integrable (fun z => propertyTiltedTanhSq r (a + b * z))
      (gaussianReal 0 1) := by
  apply Integrable.of_bound (C := 1)
  · exact ((property_continuous_tiltedTanhSq r).comp
      (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable
  · filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (property_tiltedTanhSq_mem_Icc hr _).1]
    exact (property_tiltedTanhSq_mem_Icc hr _).2

private lemma property_integrable_tiltedSech4_affine
    {r : ℝ} (hr : 0 ≤ r) (a b : ℝ) :
    Integrable (fun z => propertyTiltedSech4 r (a + b * z))
      (gaussianReal 0 1) := by
  apply Integrable.of_bound (C := 1)
  · exact ((property_continuous_tiltedSech4 r).comp
      (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable
  · filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (property_tiltedSech4_nonneg hr _)]
    exact property_tiltedSech4_le_one hr _

private lemma propertyUpperG_hasDerivAt
    {β h q s u : ℝ} (hβ : 0 < β) (hs : 0 < s) (hu : q < u) :
    HasDerivAt (propertyUpperG β h q s)
      (s * β ^ 2 * propertyUpperSech4Expectation β h q s u) u := by
  let a : ℝ := s * β ^ 2
  have ha : 0 < a := mul_pos hs (sq_pos_of_pos hβ)
  let b : ℝ := Real.sqrt (β ^ 2 * q)
  unfold propertyUpperG propertyUpperSech4Expectation heatSemigroup
  unfold standardGaussianExpectation
  let F : ℝ → ℝ → ℝ := fun t z =>
    propertyTiltedTanhSq (a * (t - q)) (h + b * z)
  let F' : ℝ → ℝ → ℝ := fun t z =>
    a * propertyTiltedSech4 (a * (t - q)) (h + b * z)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (F := F) (F' := F') (x₀ := u)
    (s := Set.Ioi q) (bound := fun _ => a)
    (Ioi_mem_nhds hu)
    (Filter.Eventually.of_forall fun t =>
      ((property_continuous_tiltedTanhSq (a * (t - q))).comp
        (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable)
    (by
      have hr : 0 ≤ a * (u - q) := mul_nonneg ha.le (sub_nonneg.mpr hu.le)
      simpa [F] using property_integrable_tiltedTanhSq_affine hr h b)
    (by
      exact (continuous_const.mul
        ((property_continuous_tiltedSech4 (a * (u - q))).comp
          (continuous_const.add (continuous_const.mul continuous_id)))).aestronglyMeasurable)
    (by
      filter_upwards [] with z
      intro t ht
      have hr : 0 ≤ a * (t - q) := mul_nonneg ha.le (sub_nonneg.mpr ht.le)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ha.le
        (property_tiltedSech4_nonneg hr _))]
      exact (mul_le_mul_of_nonneg_left (property_tiltedSech4_le_one hr _) ha.le).trans_eq
        (mul_one a))
    (integrable_const a)
    (by
      filter_upwards [] with z
      intro t ht
      have hr : 0 < a * (t - q) := mul_pos ha (sub_pos.mpr ht)
      have hinner : HasDerivAt (fun v : ℝ => a * (v - q)) a t := by
        simpa only [id_eq, mul_one] using
          ((hasDerivAt_id t).sub_const q).const_mul a
      change HasDerivAt
        (fun v => propertyTiltedTanhSq (a * (v - q)) (h + b * z))
        (a * propertyTiltedSech4 (a * (t - q)) (h + b * z)) t
      apply ((property_tiltedTanhSq_hasDerivAt_r (x := h + b * z) hr).comp
        t hinner).congr_deriv
      ring)
  have hderiv := h.2
  dsimp only [F, F'] at hderiv
  rw [integral_const_mul] at hderiv
  simpa only [a, b] using hderiv

/-- On the upper branch, differentiation gives the tilted expectation of
the fourth power of `sech`. -/
theorem scalarOrderParameterCorrect_upper_derivative
    {β h s u : ℝ} (hβ : 0 < β) (hs : 0 < s) (hu : rsQ β h < u) :
    HasDerivAt (propertyUpperG β h (rsQ β h) s)
      (s * β ^ 2 * propertyUpperSech4Expectation β h (rsQ β h) s u) u :=
  propertyUpperG_hasDerivAt hβ hs hu

private noncomputable def propertyTanhSecond (x : ℝ) : ℝ :=
  -2 * Real.tanh x * propertySech x ^ 2

private lemma property_sechSq_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y => propertySech y ^ 2) (propertyTanhSecond x) x := by
  apply ((property_sech_hasDerivAt x).pow 2).congr_deriv
  unfold propertyTanhSecond
  norm_num
  ring

private lemma property_abs_sech_sq_le_one (x : ℝ) :
    |propertySech x ^ 2| ≤ 1 := by
  rw [abs_pow]
  exact pow_le_one₀ (abs_nonneg _) (property_abs_sech_le_one x)

private lemma property_tanhSecond_abs_le_two (x : ℝ) :
    |propertyTanhSecond x| ≤ 2 := by
  unfold propertyTanhSecond
  rw [abs_mul, abs_mul, abs_neg, abs_pow]
  norm_num
  calc
    2 * |Real.tanh x| * propertySech x ^ 2 ≤ 2 * 1 * 1 ^ 2 := by
      gcongr
      · exact property_abs_tanh_le_one x
      · exact (propertySech_pos x).le
      · exact propertySech_le_one x
    _ = 2 := by norm_num

private lemma property_integrable_tanhSecond_affine (a b : ℝ) :
    Integrable (fun z : ℝ => propertyTanhSecond (a + b * z))
      (gaussianReal 0 1) := by
  apply Integrable.of_bound (C := 2)
  · apply Continuous.aestronglyMeasurable
    unfold propertyTanhSecond
    have harg : Continuous (fun z : ℝ => a + b * z) :=
      continuous_const.add (continuous_const.mul continuous_id)
    exact (continuous_const.mul (property_continuous_tanh.comp harg)).mul
      ((property_continuous_sech.comp harg).pow 2)
  · filter_upwards [] with z
    simpa [Real.norm_eq_abs] using property_tanhSecond_abs_le_two (a + b * z)

private noncomputable def propertySmoothTanh (r x : ℝ) : ℝ :=
  standardGaussianExpectation (fun z => Real.tanh (x + Real.sqrt r * z))

private noncomputable def propertySmoothSech2 (r x : ℝ) : ℝ :=
  standardGaussianExpectation (fun z => propertySech (x + Real.sqrt r * z) ^ 2)

private noncomputable def propertySmoothTanhSecond (r x : ℝ) : ℝ :=
  standardGaussianExpectation (fun z => propertyTanhSecond (x + Real.sqrt r * z))

private lemma property_smoothTanh_hasDerivAt_x (r x : ℝ) :
    HasDerivAt (propertySmoothTanh r) (propertySmoothSech2 r x) x := by
  unfold propertySmoothTanh propertySmoothSech2 standardGaussianExpectation
  let F : ℝ → ℝ → ℝ := fun y z => Real.tanh (y + Real.sqrt r * z)
  let F' : ℝ → ℝ → ℝ := fun y z => propertySech (y + Real.sqrt r * z) ^ 2
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (F := F) (F' := F') (x₀ := x)
    (s := Set.univ) (bound := fun _ => (1 : ℝ))
    (by simp)
    (Filter.Eventually.of_forall fun y =>
      (property_continuous_tanh.comp
        (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable)
    (by simpa [F] using property_integrable_tanh_affine x (Real.sqrt r))
    (by
      exact ((property_continuous_sech.comp
        (continuous_const.add (continuous_const.mul continuous_id))).pow 2)
        |>.aestronglyMeasurable)
    (by
      filter_upwards [] with z
      intro y _
      simpa [F', Real.norm_eq_abs] using
        property_abs_sech_sq_le_one (y + Real.sqrt r * z))
    (integrable_const 1)
    (by
      filter_upwards [] with z
      intro y _
      simpa [F, F', Function.comp_def] using
        (property_tanh_hasDerivAt _).comp y
          ((hasDerivAt_id y).add_const (Real.sqrt r * z)))
  simpa [F, F'] using h.2

private lemma property_smoothSech2_hasDerivAt_x (r x : ℝ) :
    HasDerivAt (propertySmoothSech2 r) (propertySmoothTanhSecond r x) x := by
  unfold propertySmoothSech2 propertySmoothTanhSecond standardGaussianExpectation
  let F : ℝ → ℝ → ℝ := fun y z => propertySech (y + Real.sqrt r * z) ^ 2
  let F' : ℝ → ℝ → ℝ := fun y z => propertyTanhSecond (y + Real.sqrt r * z)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (F := F) (F' := F') (x₀ := x)
    (s := Set.univ) (bound := fun _ => (2 : ℝ))
    (by simp)
    (Filter.Eventually.of_forall fun y =>
      ((property_continuous_sech.comp
        (continuous_const.add (continuous_const.mul continuous_id))).pow 2)
        |>.aestronglyMeasurable)
    (by simpa [F] using property_integrable_sech_sq_affine x (Real.sqrt r))
    (by
      apply Continuous.aestronglyMeasurable
      change Continuous (fun z : ℝ => propertyTanhSecond (x + Real.sqrt r * z))
      unfold propertyTanhSecond
      have harg : Continuous (fun z : ℝ => x + Real.sqrt r * z) :=
        continuous_const.add (continuous_const.mul continuous_id)
      exact (continuous_const.mul (property_continuous_tanh.comp harg)).mul
        ((property_continuous_sech.comp harg).pow 2))
    (by
      filter_upwards [] with z
      intro y _
      simpa [F', Real.norm_eq_abs] using
        property_tanhSecond_abs_le_two (y + Real.sqrt r * z))
    (integrable_const 2)
    (by
      filter_upwards [] with z
      intro y _
      simpa [F, F', Function.comp_def] using
        (property_sechSq_hasDerivAt _).comp y
          ((hasDerivAt_id y).add_const (Real.sqrt r * z)))
  simpa [F, F'] using h.2

private lemma property_continuous_smoothTanh (r : ℝ) :
    Continuous (propertySmoothTanh r) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (property_smoothTanh_hasDerivAt_x r x).continuousAt

private lemma property_continuous_smoothSech2 (r : ℝ) :
    Continuous (propertySmoothSech2 r) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (property_smoothSech2_hasDerivAt_x r x).continuousAt

private lemma property_smoothTanh_abs_le_one (r x : ℝ) :
    |propertySmoothTanh r x| ≤ 1 := by
  unfold propertySmoothTanh standardGaussianExpectation
  calc
    |∫ z, Real.tanh (x + Real.sqrt r * z) ∂gaussianReal 0 1| ≤
        ∫ z, |Real.tanh (x + Real.sqrt r * z)| ∂gaussianReal 0 1 :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _z : ℝ, (1 : ℝ) ∂gaussianReal 0 1 := by
      exact integral_mono (property_integrable_tanh_affine x (Real.sqrt r)).abs
        (integrable_const 1) fun z => property_abs_tanh_le_one _
    _ = 1 := by simp

private lemma property_smoothSech2_mem_Icc (r x : ℝ) :
    propertySmoothSech2 r x ∈ Set.Icc (0 : ℝ) 1 := by
  unfold propertySmoothSech2 standardGaussianExpectation
  constructor
  · exact integral_nonneg fun z => sq_nonneg _
  · calc
      (∫ z, propertySech (x + Real.sqrt r * z) ^ 2 ∂gaussianReal 0 1) ≤
          ∫ _z : ℝ, (1 : ℝ) ∂gaussianReal 0 1 := by
        exact integral_mono (property_integrable_sech_sq_affine x (Real.sqrt r))
          (integrable_const 1) fun z => by
            have h := propertySech_le_one (x + Real.sqrt r * z)
            nlinarith [sq_nonneg (propertySech (x + Real.sqrt r * z)),
              propertySech_pos (x + Real.sqrt r * z)]
      _ = 1 := by simp

private lemma property_smoothTanhSecond_abs_le_two (r x : ℝ) :
    |propertySmoothTanhSecond r x| ≤ 2 := by
  unfold propertySmoothTanhSecond standardGaussianExpectation
  calc
    |∫ z, propertyTanhSecond (x + Real.sqrt r * z) ∂gaussianReal 0 1| ≤
        ∫ z, |propertyTanhSecond (x + Real.sqrt r * z)| ∂gaussianReal 0 1 :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _z : ℝ, (2 : ℝ) ∂gaussianReal 0 1 := by
      exact integral_mono (property_integrable_tanhSecond_affine x (Real.sqrt r)).abs
        (integrable_const 2) fun z => property_tanhSecond_abs_le_two _
    _ = 2 := by simp

private lemma property_sechSq_comp_deriv (a b z : ℝ) :
    deriv (fun y => propertySech (a + b * y) ^ 2) z =
      b * propertyTanhSecond (a + b * z) := by
  have harg : HasDerivAt (fun y : ℝ => a + b * y) b z := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id z).const_mul b).const_add a
  simpa [Function.comp_def, mul_comm] using
    ((property_sechSq_hasDerivAt (a + b * z)).comp z harg).deriv

private lemma property_sechSq_comp_moderate (a b : ℝ) :
    HasModerateGrowth (fun z => propertySech (a + b * z) ^ 2) := by
  refine ⟨3 * (1 + |b|), 0, by positivity, ?_, ?_⟩
  · intro z
    simpa only [pow_zero, mul_one] using
      (show |propertySech (a + b * z) ^ 2| ≤ 3 * (1 + |b|) by
        have hz := property_abs_sech_sq_le_one (a + b * z)
        have hb := abs_nonneg b
        nlinarith)
  · intro z
    rw [property_sechSq_comp_deriv, abs_mul]
    simpa only [pow_zero, mul_one] using
      (show |b| * |propertyTanhSecond (a + b * z)| ≤ 3 * (1 + |b|) by
        have hz := property_tanhSecond_abs_le_two (a + b * z)
        have hb := abs_nonneg b
        nlinarith [mul_le_mul_of_nonneg_left hz hb])

private lemma property_smoothTanh_hasDerivAt_r_raw {r x : ℝ} (hr : 0 < r) :
    HasDerivAt (fun t => propertySmoothTanh t x)
      (standardGaussianExpectation (fun z =>
        propertySech (x + Real.sqrt r * z) ^ 2 *
          (1 / (2 * Real.sqrt r) * z))) r := by
  unfold propertySmoothTanh standardGaussianExpectation
  let F : ℝ → ℝ → ℝ := fun t z => Real.tanh (x + Real.sqrt t * z)
  let F' : ℝ → ℝ → ℝ := fun t z =>
    propertySech (x + Real.sqrt t * z) ^ 2 * (1 / (2 * Real.sqrt t) * z)
  let c : ℝ := Real.sqrt (r / 2)
  have hhalf : 0 < r / 2 := by linarith
  have hc : 0 < c := Real.sqrt_pos.2 hhalf
  have hboundInt : Integrable (fun z : ℝ => c⁻¹ * |z|) (gaussianReal 0 1) := by
    have hz : Integrable (fun z : ℝ => |z|) (gaussianReal 0 1) := by
      simpa using integrable_abs_pow_gaussianReal_centered (1 : ℝ≥0) 1
    exact hz.const_mul c⁻¹
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (F := F) (F' := F') (x₀ := r)
    (s := Set.Ioi (r / 2)) (bound := fun z => c⁻¹ * |z|)
    (Ioi_mem_nhds (by linarith))
    (Filter.Eventually.of_forall fun t =>
      (property_continuous_tanh.comp
        (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable)
    (by simpa [F] using property_integrable_tanh_affine x (Real.sqrt r))
    (by
      apply Continuous.aestronglyMeasurable
      have harg : Continuous (fun z : ℝ => x + Real.sqrt r * z) :=
        continuous_const.add (continuous_const.mul continuous_id)
      exact ((property_continuous_sech.comp harg).pow 2).mul
        ((continuous_const : Continuous (fun _ : ℝ => 1 / (2 * Real.sqrt r))).mul
          continuous_id))
    (by
      filter_upwards [] with z
      intro t ht
      have htpos : 0 < t := lt_trans hhalf ht
      have hroot : 0 < Real.sqrt t := Real.sqrt_pos.2 htpos
      have hrootle : c ≤ Real.sqrt t := Real.sqrt_le_sqrt ht.le
      have hinv : (Real.sqrt t)⁻¹ ≤ c⁻¹ := (inv_le_inv₀ hroot hc).2 hrootle
      have hcoef : |1 / (2 * Real.sqrt t)| ≤ c⁻¹ := by
        rw [abs_of_pos (by positivity : 0 < 1 / (2 * Real.sqrt t))]
        calc
          1 / (2 * Real.sqrt t) ≤ (Real.sqrt t)⁻¹ := by
            rw [one_div]
            exact (inv_le_inv₀ (by positivity) hroot).2 (by nlinarith)
          _ ≤ c⁻¹ := hinv
      dsimp [F']
      simp only [abs_mul]
      have hp : |propertySech (x + Real.sqrt t * z) ^ 2| *
          |1 / (2 * Real.sqrt t)| ≤ c⁻¹ := by
        calc
          _ ≤ 1 * c⁻¹ := mul_le_mul (property_abs_sech_sq_le_one _) hcoef
            (abs_nonneg _) (by norm_num)
          _ = c⁻¹ := one_mul _
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right hp (abs_nonneg z))
    hboundInt
    (by
      filter_upwards [] with z
      intro t ht
      have htpos : 0 < t := lt_trans hhalf ht
      have harg : HasDerivAt (fun t => x + Real.sqrt t * z)
          (1 / (2 * Real.sqrt t) * z) t :=
        ((Real.hasDerivAt_sqrt htpos.ne').mul_const z).const_add x
      simpa [F, F', Function.comp_def] using
        (property_tanh_hasDerivAt _).comp t harg)
  simpa [F, F'] using h.2

private lemma property_smoothTanh_hasDerivAt_r {r x : ℝ} (hr : 0 < r) :
    HasDerivAt (fun t => propertySmoothTanh t x)
      ((1 / 2) * propertySmoothTanhSecond r x) r := by
  apply (property_smoothTanh_hasDerivAt_r_raw (x := x) hr).congr_deriv
  unfold propertySmoothTanhSecond standardGaussianExpectation
  let F : ℝ → ℝ := fun z => propertySech (x + Real.sqrt r * z) ^ 2
  have hcont : ContDiff ℝ 1 F := by
    exact ((property_contDiff_sech.pow 2).of_le (by norm_num)).comp (by fun_prop)
  have hibp := gaussianReal_integration_by_parts (v := (1 : ℝ≥0)) one_ne_zero
    hcont (property_sechSq_comp_moderate x (Real.sqrt r))
  have hderiv : deriv F = fun z => Real.sqrt r *
      propertyTanhSecond (x + Real.sqrt r * z) := by
    funext z
    exact property_sechSq_comp_deriv x (Real.sqrt r) z
  rw [hderiv] at hibp
  simp only [NNReal.coe_one, one_mul] at hibp
  have hsqrt : Real.sqrt r ≠ 0 := (Real.sqrt_pos.2 hr).ne'
  calc
    ∫ z, F z * (1 / (2 * Real.sqrt r) * z) ∂gaussianReal 0 1 =
        (1 / (2 * Real.sqrt r)) * ∫ z, z * F z ∂gaussianReal 0 1 := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards [] with z
          ring
    _ = (1 / (2 * Real.sqrt r)) *
        ∫ z, Real.sqrt r * propertyTanhSecond (x + Real.sqrt r * z)
          ∂gaussianReal 0 1 := by rw [hibp]
    _ = (1 / 2) * ∫ z, propertyTanhSecond (x + Real.sqrt r * z)
          ∂gaussianReal 0 1 := by
          rw [integral_const_mul]
          field_simp [hsqrt]

private lemma property_continuous_smoothTanhSecond (r : ℝ) :
    Continuous (propertySmoothTanhSecond r) := by
  unfold propertySmoothTanhSecond standardGaussianExpectation
  rw [continuous_iff_continuousAt]
  intro x
  have hmeas : ∀ᶠ y in 𝓝 x,
      AEStronglyMeasurable (fun z => propertyTanhSecond (y + Real.sqrt r * z))
        (gaussianReal 0 1) := by
    exact Filter.Eventually.of_forall fun y =>
      (by
        apply Continuous.aestronglyMeasurable
        unfold propertyTanhSecond
        have harg : Continuous (fun z : ℝ => y + Real.sqrt r * z) :=
          continuous_const.add (continuous_const.mul continuous_id)
        exact (continuous_const.mul (property_continuous_tanh.comp harg)).mul
          ((property_continuous_sech.comp harg).pow 2))
  have hbound : ∀ᶠ y in 𝓝 x, ∀ᵐ z ∂gaussianReal 0 1,
      ‖propertyTanhSecond (y + Real.sqrt r * z)‖ ≤ (2 : ℝ) := by
    exact Filter.Eventually.of_forall fun y => ae_of_all _ fun z => by
      simpa [Real.norm_eq_abs] using
        property_tanhSecond_abs_le_two (y + Real.sqrt r * z)
  have hlim : ∀ᵐ z ∂gaussianReal 0 1,
      Tendsto (fun y => propertyTanhSecond (y + Real.sqrt r * z)) (𝓝 x)
        (𝓝 (propertyTanhSecond (x + Real.sqrt r * z))) := by
    exact ae_of_all _ fun z => by
      apply ContinuousAt.tendsto
      unfold propertyTanhSecond
      have harg : Continuous (fun y : ℝ => y + Real.sqrt r * z) :=
        continuous_id.add continuous_const
      exact ((continuous_const.mul (property_continuous_tanh.comp harg)).mul
        ((property_continuous_sech.comp harg).pow 2)).continuousAt
  exact tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝 x) (F := fun y z => propertyTanhSecond (y + Real.sqrt r * z))
    (f := fun z => propertyTanhSecond (x + Real.sqrt r * z))
    (bound := fun _ => (2 : ℝ)) hmeas hbound (integrable_const 2) hlim

private lemma property_smoothTanh_deriv (r x : ℝ) :
    deriv (propertySmoothTanh r) x = propertySmoothSech2 r x :=
  (property_smoothTanh_hasDerivAt_x r x).deriv

private lemma property_smoothSech2_deriv (r x : ℝ) :
    deriv (propertySmoothSech2 r) x = propertySmoothTanhSecond r x :=
  (property_smoothSech2_hasDerivAt_x r x).deriv

private lemma property_contDiff_smoothTanh (r : ℝ) :
    ContDiff ℝ 1 (propertySmoothTanh r) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (property_smoothTanh_hasDerivAt_x r x).differentiableAt, ?_⟩
  rw [show deriv (propertySmoothTanh r) = propertySmoothSech2 r by
    funext x
    exact property_smoothTanh_deriv r x]
  exact property_continuous_smoothSech2 r

private lemma property_contDiff_smoothSech2 (r : ℝ) :
    ContDiff ℝ 1 (propertySmoothSech2 r) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (property_smoothSech2_hasDerivAt_x r x).differentiableAt, ?_⟩
  rw [show deriv (propertySmoothSech2 r) = propertySmoothTanhSecond r by
    funext x
    exact property_smoothSech2_deriv r x]
  exact property_continuous_smoothTanhSecond r

private lemma property_smooth_pair_deriv (r a b z : ℝ) :
    deriv (fun y => 2 * propertySmoothTanh r (a + b * y) *
      propertySmoothSech2 r (a + b * y)) z =
      2 * b * (propertySmoothSech2 r (a + b * z) ^ 2 +
        propertySmoothTanh r (a + b * z) *
          propertySmoothTanhSecond r (a + b * z)) := by
  have harg : HasDerivAt (fun y : ℝ => a + b * y) b z := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id z).const_mul b).const_add a
  have hT := (property_smoothTanh_hasDerivAt_x r (a + b * z)).comp z harg
  have hTx := (property_smoothSech2_hasDerivAt_x r (a + b * z)).comp z harg
  have hd := (hT.const_mul 2).mul hTx
  exact (hd.congr_deriv (by simp only [Function.comp_apply]; ring)).deriv

private lemma property_smooth_pair_moderate (r a b : ℝ) :
    HasModerateGrowth (fun z => 2 * propertySmoothTanh r (a + b * z) *
      propertySmoothSech2 r (a + b * z)) := by
  refine ⟨9 * (1 + |b|), 0, by positivity, ?_, ?_⟩
  · intro z
    simpa only [pow_zero, mul_one] using
      (show |2 * propertySmoothTanh r (a + b * z) *
          propertySmoothSech2 r (a + b * z)| ≤ 9 * (1 + |b|) by
        rw [abs_mul, abs_mul]
        norm_num
        have hT := property_smoothTanh_abs_le_one r (a + b * z)
        have hTx := (property_smoothSech2_mem_Icc r (a + b * z)).2
        have hTx0 := (property_smoothSech2_mem_Icc r (a + b * z)).1
        rw [abs_of_nonneg hTx0]
        calc
          2 * |propertySmoothTanh r (a + b * z)| *
              propertySmoothSech2 r (a + b * z) ≤ 2 * 1 * 1 := by
            gcongr
          _ ≤ 9 * (1 + |b|) := by nlinarith [abs_nonneg b])
  · intro z
    rw [property_smooth_pair_deriv]
    have hT := property_smoothTanh_abs_le_one r (a + b * z)
    have hTx := (property_smoothSech2_mem_Icc r (a + b * z)).2
    have hTx0 := (property_smoothSech2_mem_Icc r (a + b * z)).1
    have hTxx := property_smoothTanhSecond_abs_le_two r (a + b * z)
    have hinside :
        |propertySmoothSech2 r (a + b * z) ^ 2 +
          propertySmoothTanh r (a + b * z) *
            propertySmoothTanhSecond r (a + b * z)| ≤ 3 := by
      calc
        _ ≤ |propertySmoothSech2 r (a + b * z) ^ 2| +
            |propertySmoothTanh r (a + b * z) *
              propertySmoothTanhSecond r (a + b * z)| := abs_add_le _ _
        _ = propertySmoothSech2 r (a + b * z) ^ 2 +
            |propertySmoothTanh r (a + b * z)| *
              |propertySmoothTanhSecond r (a + b * z)| := by
              rw [abs_of_nonneg (sq_nonneg _), abs_mul]
        _ ≤ 1 ^ 2 + 1 * 2 := by
          gcongr
        _ = 3 := by norm_num
    simpa only [pow_zero, mul_one] using
      (show |2 * b * (propertySmoothSech2 r (a + b * z) ^ 2 +
          propertySmoothTanh r (a + b * z) *
            propertySmoothTanhSecond r (a + b * z))| ≤ 9 * (1 + |b|) by
        rw [abs_mul, abs_mul]
        norm_num
        calc
          2 * |b| * |propertySmoothSech2 r (a + b * z) ^ 2 +
              propertySmoothTanh r (a + b * z) *
                propertySmoothTanhSecond r (a + b * z)| ≤
              2 * |b| * 3 := mul_le_mul_of_nonneg_left hinside
                (mul_nonneg (by norm_num) (abs_nonneg b))
          _ ≤ 9 * (1 + |b|) := by nlinarith [abs_nonneg b])

private lemma property_gaussian_pair_ibp (r a b : ℝ) :
    (∫ z, z * (2 * propertySmoothTanh r (a + b * z) *
      propertySmoothSech2 r (a + b * z)) ∂gaussianReal 0 1) =
      2 * b * ∫ z, propertySmoothSech2 r (a + b * z) ^ 2 +
        propertySmoothTanh r (a + b * z) *
          propertySmoothTanhSecond r (a + b * z) ∂gaussianReal 0 1 := by
  let F : ℝ → ℝ := fun z => 2 * propertySmoothTanh r (a + b * z) *
    propertySmoothSech2 r (a + b * z)
  have hcont : ContDiff ℝ 1 F := by
    exact ((contDiff_const.mul ((property_contDiff_smoothTanh r).comp (by fun_prop))).mul
      ((property_contDiff_smoothSech2 r).comp (by fun_prop))).of_le (by norm_num)
  have hibp := gaussianReal_integration_by_parts (v := (1 : ℝ≥0)) one_ne_zero
    hcont (property_smooth_pair_moderate r a b)
  have hderiv : deriv F = fun z => 2 * b *
      (propertySmoothSech2 r (a + b * z) ^ 2 +
        propertySmoothTanh r (a + b * z) *
          propertySmoothTanhSecond r (a + b * z)) := by
    funext z
    exact property_smooth_pair_deriv r a b z
  rw [hderiv] at hibp
  simp only [NNReal.coe_one, one_mul] at hibp
  rw [integral_const_mul] at hibp
  exact hibp

private noncomputable def propertyLowerVariance (β q s u : ℝ) : ℝ :=
  β ^ 2 * ((1 - s) * q + s * u)

private noncomputable def propertyLowerRemainder (β q s u : ℝ) : ℝ :=
  s * β ^ 2 * (q - u)

private noncomputable def propertyLowerInner
    (β h q s u z₀ : ℝ) : ℝ :=
  propertySmoothTanh (propertyLowerRemainder β q s u)
    (h + Real.sqrt (propertyLowerVariance β q s u) * z₀)

private noncomputable def propertyLowerG (β h q s u : ℝ) : ℝ :=
  standardGaussianExpectation (fun z₀ => propertyLowerInner β h q s u z₀ ^ 2)

private noncomputable def propertyLowerDerivativeCore
    (β h q s u : ℝ) : ℝ :=
  standardGaussianExpectation (fun z₀ =>
    propertySmoothSech2 (propertyLowerRemainder β q s u)
      (h + Real.sqrt (propertyLowerVariance β q s u) * z₀) ^ 2)

private lemma scalarOrderParameterCorrect_eq_propertyLowerG
    {β h s u : ℝ} (hβ : 0 < β) (hs : 0 ≤ s) (hu : u ≤ rsQ β h) :
    scalarOrderParameterCorrect β h s u =
      propertyLowerG β h (rsQ β h) s u := by
  have hmax : max (rsQ β h - u) 0 = rsQ β h - u :=
    max_eq_left (sub_nonneg.mpr hu)
  have hsarg : 0 ≤ s * (rsQ β h - u) := mul_nonneg hs (sub_nonneg.mpr hu)
  have hsqrt : Real.sqrt (s * β ^ 2 * (rsQ β h - u)) =
      β * Real.sqrt (s * (rsQ β h - u)) := by
    rw [show s * β ^ 2 * (rsQ β h - u) =
        β ^ 2 * (s * (rsQ β h - u)) by ring]
    rw [Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq_eq_abs, abs_of_pos hβ]
  have hpsi (x : ℝ) : scalarPsiX β (rsQ β h) s u x =
      propertySmoothTanh (propertyLowerRemainder β (rsQ β h) s u) x := by
    unfold scalarPsiX propertySmoothTanh propertyLowerRemainder
    rw [hmax, hsqrt]
  unfold scalarOrderParameterCorrect scalarOrderParameter localFieldExpectation
    propertyLowerG propertyLowerInner
  simp only [if_pos hu, heatSemigroup, hpsi]
  rfl

private lemma property_gaussian_sechSq_ibp {r x : ℝ} (_hr : 0 < r) :
    (∫ z, z * propertySech (x + Real.sqrt r * z) ^ 2 ∂gaussianReal 0 1) =
      Real.sqrt r * propertySmoothTanhSecond r x := by
  let F : ℝ → ℝ := fun z => propertySech (x + Real.sqrt r * z) ^ 2
  have hcont : ContDiff ℝ 1 F := by
    exact ((property_contDiff_sech.pow 2).of_le (by norm_num)).comp (by fun_prop)
  have hibp := gaussianReal_integration_by_parts (v := (1 : ℝ≥0)) one_ne_zero
    hcont (property_sechSq_comp_moderate x (Real.sqrt r))
  have hderiv : deriv F = fun z => Real.sqrt r *
      propertyTanhSecond (x + Real.sqrt r * z) := by
    funext z
    exact property_sechSq_comp_deriv x (Real.sqrt r) z
  rw [hderiv] at hibp
  simp only [NNReal.coe_one, one_mul] at hibp
  unfold propertySmoothTanhSecond standardGaussianExpectation
  rw [integral_const_mul] at hibp
  exact hibp

private lemma propertyLowerInner_hasDerivAt
    {β h q s u z₀ : ℝ} (hβ : 0 < β) (hq : 0 < q)
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hu0 : 0 < u) (huq : u < q) :
    HasDerivAt (fun t => propertyLowerInner β h q s t z₀)
      (-s * β ^ 2 / 2 *
          propertySmoothTanhSecond (propertyLowerRemainder β q s u)
            (h + Real.sqrt (propertyLowerVariance β q s u) * z₀) +
        s * β ^ 2 / (2 * Real.sqrt (propertyLowerVariance β q s u)) * z₀ *
          propertySmoothSech2 (propertyLowerRemainder β q s u)
            (h + Real.sqrt (propertyLowerVariance β q s u) * z₀)) u := by
  let a : ℝ := s * β ^ 2
  have ha : 0 < a := mul_pos hs0 (sq_pos_of_pos hβ)
  let τ : ℝ → ℝ := fun t => propertyLowerVariance β q s t
  let r : ℝ → ℝ := fun t => propertyLowerRemainder β q s t
  let x : ℝ → ℝ := fun t => h + Real.sqrt (τ t) * z₀
  have hregion : Set.Ioo (u / 2) ((u + q) / 2) ∈ 𝓝 u := by
    exact Ioo_mem_nhds (by linarith) (by linarith)
  have hτpos (t : ℝ) (ht : t ∈ Set.Ioo (u / 2) ((u + q) / 2)) : 0 < τ t := by
    have ht0 : 0 < t := lt_trans (by linarith : 0 < u / 2) ht.1
    have h1s : 0 ≤ 1 - s := sub_nonneg.mpr hs1
    have hbase : 0 < (1 - s) * q + s * t :=
      add_pos_of_nonneg_of_pos (mul_nonneg h1s hq.le) (mul_pos hs0 ht0)
    unfold τ propertyLowerVariance
    exact mul_pos (sq_pos_of_pos hβ) hbase
  have hrpos (t : ℝ) (ht : t ∈ Set.Ioo (u / 2) ((u + q) / 2)) : 0 < r t := by
    have htq : t < q := by linarith [ht.2]
    unfold r propertyLowerRemainder
    exact mul_pos ha (sub_pos.mpr htq)
  let cτ : ℝ := Real.sqrt (β ^ 2 * (s * (u / 2)))
  let cr : ℝ := Real.sqrt (a * ((q - u) / 2))
  have hcτarg : 0 < β ^ 2 * (s * (u / 2)) := by positivity
  have hcrarg : 0 < a * ((q - u) / 2) := mul_pos ha (by linarith)
  have hcτ : 0 < cτ := Real.sqrt_pos.2 hcτarg
  have hcr : 0 < cr := Real.sqrt_pos.2 hcrarg
  let bound : ℝ → ℝ := fun z =>
    a * cτ⁻¹ * |z₀| + a * cr⁻¹ * |z|
  have hboundInt : Integrable bound (gaussianReal 0 1) := by
    have hz : Integrable (fun z : ℝ => |z|) (gaussianReal 0 1) := by
      simpa using integrable_abs_pow_gaussianReal_centered (1 : ℝ≥0) 1
    exact (integrable_const (a * cτ⁻¹ * |z₀|)).add
      (hz.const_mul (a * cr⁻¹))
  unfold propertyLowerInner propertySmoothTanh standardGaussianExpectation
  let F : ℝ → ℝ → ℝ := fun t z => Real.tanh (x t + Real.sqrt (r t) * z)
  let F' : ℝ → ℝ → ℝ := fun t z =>
    propertySech (x t + Real.sqrt (r t) * z) ^ 2 *
      (a / (2 * Real.sqrt (τ t)) * z₀ - a / (2 * Real.sqrt (r t)) * z)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (F := F) (F' := F') (x₀ := u)
    (s := Set.Ioo (u / 2) ((u + q) / 2)) (bound := bound)
    hregion
    (Filter.Eventually.of_forall fun t =>
      (property_continuous_tanh.comp (by fun_prop)).aestronglyMeasurable)
    (by
      simpa [F, x] using
        property_integrable_tanh_affine (x u) (Real.sqrt (r u)))
    (by
      apply Continuous.aestronglyMeasurable
      dsimp [F']
      have harg : Continuous (fun z : ℝ => x u + Real.sqrt (r u) * z) := by
        fun_prop
      exact ((property_continuous_sech.comp harg).pow 2).mul
        (continuous_const.sub (continuous_const.mul continuous_id)))
    (by
      filter_upwards [] with z
      intro t ht
      have hτt := hτpos t ht
      have hrt := hrpos t ht
      have hτlower : β ^ 2 * (s * (u / 2)) ≤ τ t := by
        unfold τ propertyLowerVariance
        have h1s : 0 ≤ (1 - s) * q := mul_nonneg (sub_nonneg.mpr hs1) hq.le
        have hst : s * (u / 2) ≤ s * t := mul_le_mul_of_nonneg_left ht.1.le hs0.le
        nlinarith [sq_nonneg β, mul_nonneg (sq_nonneg β) h1s,
          mul_le_mul_of_nonneg_left hst (sq_nonneg β)]
      have hrlower : a * ((q - u) / 2) ≤ r t := by
        unfold r propertyLowerRemainder
        have : (q - u) / 2 ≤ q - t := by linarith [ht.2]
        exact mul_le_mul_of_nonneg_left this ha.le
      have hsqrtτ : cτ ≤ Real.sqrt (τ t) := Real.sqrt_le_sqrt hτlower
      have hsqrtr : cr ≤ Real.sqrt (r t) := Real.sqrt_le_sqrt hrlower
      have hcoefτ : |a / (2 * Real.sqrt (τ t))| ≤ a * cτ⁻¹ := by
        rw [abs_of_pos (div_pos ha (by positivity))]
        have hi := (inv_le_inv₀ (Real.sqrt_pos.2 hτt) hcτ).2 hsqrtτ
        calc
          a / (2 * Real.sqrt (τ t)) ≤ a * (Real.sqrt (τ t))⁻¹ := by
            rw [div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_left
              ((inv_le_inv₀ (by positivity : 0 < 2 * Real.sqrt (τ t))
                (Real.sqrt_pos.2 hτt)).2 (by nlinarith)) ha.le
          _ ≤ a * cτ⁻¹ := mul_le_mul_of_nonneg_left hi ha.le
      have hcoefr : |a / (2 * Real.sqrt (r t))| ≤ a * cr⁻¹ := by
        rw [abs_of_pos (div_pos ha (by positivity))]
        have hi := (inv_le_inv₀ (Real.sqrt_pos.2 hrt) hcr).2 hsqrtr
        calc
          a / (2 * Real.sqrt (r t)) ≤ a * (Real.sqrt (r t))⁻¹ := by
            rw [div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_left
              ((inv_le_inv₀ (by positivity : 0 < 2 * Real.sqrt (r t))
                (Real.sqrt_pos.2 hrt)).2 (by nlinarith)) ha.le
          _ ≤ a * cr⁻¹ := mul_le_mul_of_nonneg_left hi ha.le
      dsimp [F', bound]
      rw [abs_mul]
      have hinside :
          |a / (2 * Real.sqrt (τ t)) * z₀ -
            a / (2 * Real.sqrt (r t)) * z| ≤
            |a / (2 * Real.sqrt (τ t))| * |z₀| +
              |a / (2 * Real.sqrt (r t))| * |z| := by
        simpa only [abs_mul] using
          abs_sub (a / (2 * Real.sqrt (τ t)) * z₀)
            (a / (2 * Real.sqrt (r t)) * z)
      calc
        |propertySech (x t + Real.sqrt (r t) * z) ^ 2| *
            |a / (2 * Real.sqrt (τ t)) * z₀ -
              a / (2 * Real.sqrt (r t)) * z| ≤
            1 * |a / (2 * Real.sqrt (τ t)) * z₀ -
              a / (2 * Real.sqrt (r t)) * z| :=
                mul_le_mul_of_nonneg_right (property_abs_sech_sq_le_one _) (abs_nonneg _)
        _ ≤ 1 * (|a / (2 * Real.sqrt (τ t))| * |z₀| +
              |a / (2 * Real.sqrt (r t))| * |z|) :=
                mul_le_mul_of_nonneg_left hinside (by norm_num)
        _ ≤ a * cτ⁻¹ * |z₀| + a * cr⁻¹ * |z| := by
          simp only [one_mul]
          exact add_le_add
            (mul_le_mul_of_nonneg_right hcoefτ (abs_nonneg z₀))
            (mul_le_mul_of_nonneg_right hcoefr (abs_nonneg z)))
    hboundInt
    (by
      filter_upwards [] with z
      intro t ht
      have hτt := hτpos t ht
      have hrt := hrpos t ht
      have hτderiv : HasDerivAt τ a t := by
        change HasDerivAt (fun v : ℝ => β ^ 2 * ((1 - s) * q + s * v)) a t
        have hd : HasDerivAt (fun v : ℝ => β ^ 2 * ((1 - s) * q + s * v))
            (β ^ 2 * s) t := by
          simpa only [Pi.add_apply, id_eq, zero_add, mul_one] using
            (((hasDerivAt_const t ((1 - s) * q)).add
              ((hasDerivAt_id t).const_mul s)).const_mul (β ^ 2))
        apply hd.congr_deriv
        unfold a
        ring
      have hrderiv : HasDerivAt r (-a) t := by
        change HasDerivAt (fun v : ℝ => s * β ^ 2 * (q - v)) (-a) t
        have hd : HasDerivAt (fun v : ℝ => s * β ^ 2 * (q - v))
            (-(s * β ^ 2)) t := by
          simpa only [Pi.sub_apply, id_eq, zero_sub, mul_one, mul_neg] using
            (((hasDerivAt_const t q).sub (hasDerivAt_id t)).const_mul
              (s * β ^ 2))
        apply hd.congr_deriv
        rfl
      have hxderiv : HasDerivAt x
          (a / (2 * Real.sqrt (τ t)) * z₀) t := by
        unfold x
        apply ((((Real.hasDerivAt_sqrt hτt.ne').comp t hτderiv).mul_const z₀).const_add h)
          |>.congr_deriv
        ring
      have hsqrtrderiv : HasDerivAt (fun v => Real.sqrt (r v))
          (-a / (2 * Real.sqrt (r t))) t := by
        apply ((Real.hasDerivAt_sqrt hrt.ne').comp t hrderiv).congr_deriv
        ring
      have harg : HasDerivAt (fun v => x v + Real.sqrt (r v) * z)
          (a / (2 * Real.sqrt (τ t)) * z₀ -
            a / (2 * Real.sqrt (r t)) * z) t := by
        apply (hxderiv.add (hsqrtrderiv.mul_const z)).congr_deriv
        ring
      simpa [F, F', Function.comp_def] using
        (property_tanh_hasDerivAt _).comp t harg)
  have hraw := hd.2
  dsimp only [F, F'] at hraw
  have hibp := property_gaussian_sechSq_ibp (r := r u) (x := x u) (hrpos u
    ⟨by linarith, by linarith⟩)
  have hsqru : Real.sqrt (r u) ≠ 0 := (Real.sqrt_pos.2
    (hrpos u ⟨by linarith, by linarith⟩)).ne'
  have hsechInt := property_integrable_sech_sq_affine (x u) (Real.sqrt (r u))
  have hzsechInt : Integrable (fun z => z * propertySech (x u + Real.sqrt (r u) * z) ^ 2)
      (gaussianReal 0 1) := by
    have hzabs : Integrable (fun z : ℝ => |z|) (gaussianReal 0 1) := by
      simpa using integrable_abs_pow_gaussianReal_centered (1 : ℝ≥0) 1
    apply Integrable.mono' hzabs
    · exact (continuous_id.mul
        ((property_continuous_sech.comp (by fun_prop)).pow 2)).aestronglyMeasurable
    · filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_mul]
      calc
        |z| * |propertySech (x u + Real.sqrt (r u) * z) ^ 2| ≤ |z| * 1 :=
          mul_le_mul_of_nonneg_left (property_abs_sech_sq_le_one _) (abs_nonneg z)
        _ = ‖z‖ := by rw [Real.norm_eq_abs, mul_one]
  have hcalc :
      (∫ z, propertySech (x u + Real.sqrt (r u) * z) ^ 2 *
        (a / (2 * Real.sqrt (τ u)) * z₀ -
          a / (2 * Real.sqrt (r u)) * z) ∂gaussianReal 0 1) =
        -a / 2 * propertySmoothTanhSecond (r u) (x u) +
          a / (2 * Real.sqrt (τ u)) * z₀ * propertySmoothSech2 (r u) (x u) := by
    rw [show (fun z => propertySech (x u + Real.sqrt (r u) * z) ^ 2 *
        (a / (2 * Real.sqrt (τ u)) * z₀ - a / (2 * Real.sqrt (r u)) * z)) =
      fun z => (a / (2 * Real.sqrt (τ u)) * z₀) *
          propertySech (x u + Real.sqrt (r u) * z) ^ 2 -
        (a / (2 * Real.sqrt (r u))) *
          (z * propertySech (x u + Real.sqrt (r u) * z) ^ 2) by
            funext z
            ring]
    rw [integral_sub (hsechInt.const_mul _) (hzsechInt.const_mul _),
      integral_const_mul, integral_const_mul, hibp]
    unfold propertySmoothSech2 standardGaussianExpectation
    field_simp [hsqru]
    ring
  rw [hcalc] at hraw
  simpa [a, τ, r, x, propertyLowerVariance, propertyLowerRemainder] using hraw

private lemma propertyLowerG_hasDerivAt
    {β h q s u : ℝ} (hβ : 0 < β) (hq : 0 < q)
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hu0 : 0 < u) (huq : u < q) :
    HasDerivAt (propertyLowerG β h q s)
      (s * β ^ 2 * propertyLowerDerivativeCore β h q s u) u := by
  let a : ℝ := s * β ^ 2
  let τ : ℝ → ℝ := fun t => propertyLowerVariance β q s t
  let r : ℝ → ℝ := fun t => propertyLowerRemainder β q s t
  let x : ℝ → ℝ → ℝ := fun t z₀ => h + Real.sqrt (τ t) * z₀
  have ha : 0 < a := mul_pos hs0 (sq_pos_of_pos hβ)
  have hregion : Set.Ioo (u / 2) ((u + q) / 2) ∈ nhds u := by
    exact Ioo_mem_nhds (by linarith) (by linarith)
  have hregionmem : u ∈ Set.Ioo (u / 2) ((u + q) / 2) := by
    constructor <;> linarith
  have hτpos : ∀ t ∈ Set.Ioo (u / 2) ((u + q) / 2), 0 < τ t := by
    intro t ht
    unfold τ propertyLowerVariance
    have h1s : 0 ≤ (1 - s) * q := mul_nonneg (sub_nonneg.mpr hs1) hq.le
    have hst : 0 < s * t := mul_pos hs0 (lt_trans (by linarith) ht.1)
    exact mul_pos (sq_pos_of_pos hβ) (by positivity)
  let cτ : ℝ := Real.sqrt (β ^ 2 * (s * (u / 2)))
  have hcτarg : 0 < β ^ 2 * (s * (u / 2)) := by positivity
  have hcτ : 0 < cτ := Real.sqrt_pos.2 hcτarg
  let bound : ℝ → ℝ := fun z => 4 * a + 2 * (a * cτ⁻¹) * |z|
  have hboundInt : Integrable bound (gaussianReal 0 1) := by
    have hz : Integrable (fun z : ℝ => |z|) (gaussianReal 0 1) := by
      simpa using integrable_abs_pow_gaussianReal_centered (1 : ℝ≥0) 1
    exact (integrable_const (4 * a)).add (hz.const_mul (2 * (a * cτ⁻¹)))
  unfold propertyLowerG standardGaussianExpectation
  let F : ℝ → ℝ → ℝ := fun t z₀ => propertyLowerInner β h q s t z₀ ^ 2
  let F' : ℝ → ℝ → ℝ := fun t z₀ =>
    2 * propertyLowerInner β h q s t z₀ *
      (-a / 2 * propertySmoothTanhSecond (r t) (x t z₀) +
        a / (2 * Real.sqrt (τ t)) * z₀ * propertySmoothSech2 (r t) (x t z₀))
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (F := F) (F' := F') (x₀ := u)
    (s := Set.Ioo (u / 2) ((u + q) / 2)) (bound := bound)
    hregion
    (Filter.Eventually.of_forall fun t => by
      dsimp [F]
      exact (property_continuous_smoothTanh (r t) |>.comp (by fun_prop) |>.pow 2)
        |>.aestronglyMeasurable)
    (by
      apply Integrable.of_bound (C := 1)
      · exact (property_continuous_smoothTanh (r u) |>.comp (by fun_prop) |>.pow 2)
          |>.aestronglyMeasurable
      · filter_upwards [] with z₀
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_one₀ (abs_nonneg _) (property_smoothTanh_abs_le_one _ _))
    (by
      apply Continuous.aestronglyMeasurable
      dsimp [F']
      exact (continuous_const.mul (property_continuous_smoothTanh (r u) |>.comp (by fun_prop))).mul
        ((continuous_const.mul (property_continuous_smoothTanhSecond (r u) |>.comp
            (by fun_prop))).add
          (((continuous_const.mul continuous_id).mul
            (property_continuous_smoothSech2 (r u) |>.comp (by fun_prop))))))
    (by
      filter_upwards [] with z₀
      intro t ht
      have hτt := hτpos t ht
      have hτlower : β ^ 2 * (s * (u / 2)) ≤ τ t := by
        unfold τ propertyLowerVariance
        have h1s : 0 ≤ (1 - s) * q := mul_nonneg (sub_nonneg.mpr hs1) hq.le
        have hst : s * (u / 2) ≤ s * t := mul_le_mul_of_nonneg_left ht.1.le hs0.le
        nlinarith [sq_nonneg β, mul_nonneg (sq_nonneg β) h1s,
          mul_le_mul_of_nonneg_left hst (sq_nonneg β)]
      have hsqrtτ : cτ ≤ Real.sqrt (τ t) := Real.sqrt_le_sqrt hτlower
      have hcoef : |a / (2 * Real.sqrt (τ t))| ≤ a * cτ⁻¹ := by
        rw [abs_of_pos (div_pos ha (by positivity))]
        have hi := (inv_le_inv₀ (Real.sqrt_pos.2 hτt) hcτ).2 hsqrtτ
        calc
          a / (2 * Real.sqrt (τ t)) ≤ a * (Real.sqrt (τ t))⁻¹ := by
            rw [div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_left
              ((inv_le_inv₀ (by positivity : 0 < 2 * Real.sqrt (τ t))
                (Real.sqrt_pos.2 hτt)).2 (by nlinarith)) ha.le
          _ ≤ a * cτ⁻¹ := mul_le_mul_of_nonneg_left hi ha.le
      dsimp [F', bound]
      rw [abs_mul, abs_mul]
      have hT := property_smoothTanh_abs_le_one (r t) (x t z₀)
      have hTxx := property_smoothTanhSecond_abs_le_two (r t) (x t z₀)
      have hTx := property_smoothSech2_mem_Icc (r t) (x t z₀)
      have hins :
          |-a / 2 * propertySmoothTanhSecond (r t) (x t z₀) +
              a / (2 * Real.sqrt (τ t)) * z₀ *
                propertySmoothSech2 (r t) (x t z₀)| ≤
            2 * a + a * cτ⁻¹ * |z₀| := by
        have hfirst : |-a / 2 * propertySmoothTanhSecond (r t) (x t z₀)| ≤ a := by
          rw [abs_mul]
          have ha2 : |-a / 2| = a / 2 := by
            have hneg : -a / 2 < 0 := by linarith
            rw [abs_of_neg hneg]
            ring
          rw [ha2]
          nlinarith
        have hsecond :
            |a / (2 * Real.sqrt (τ t)) * z₀ *
                propertySmoothSech2 (r t) (x t z₀)| ≤
              a * cτ⁻¹ * |z₀| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hTx.1]
          have hzcoef : |a / (2 * Real.sqrt (τ t))| * |z₀| ≤
              (a * cτ⁻¹) * |z₀| :=
            mul_le_mul_of_nonneg_right hcoef (abs_nonneg z₀)
          calc
            |a / (2 * Real.sqrt (τ t))| * |z₀| *
                propertySmoothSech2 (r t) (x t z₀) ≤
                (a * cτ⁻¹ * |z₀|) *
                  propertySmoothSech2 (r t) (x t z₀) :=
                    mul_le_mul_of_nonneg_right hzcoef hTx.1
            _ ≤ (a * cτ⁻¹ * |z₀|) * 1 := by
              exact mul_le_mul_of_nonneg_left hTx.2
                (mul_nonneg (mul_nonneg ha.le (inv_nonneg.mpr hcτ.le)) (abs_nonneg z₀))
            _ = a * cτ⁻¹ * |z₀| := by ring
        calc
          _ ≤ |-a / 2 * propertySmoothTanhSecond (r t) (x t z₀)| +
              |a / (2 * Real.sqrt (τ t)) * z₀ *
                propertySmoothSech2 (r t) (x t z₀)| := abs_add_le _ _
          _ ≤ a + a * cτ⁻¹ * |z₀| := add_le_add hfirst hsecond
          _ ≤ 2 * a + a * cτ⁻¹ * |z₀| := by linarith
      calc
        |2| * |propertyLowerInner β h q s t z₀| *
            |-a / 2 * propertySmoothTanhSecond (r t) (x t z₀) +
              a / (2 * Real.sqrt (τ t)) * z₀ *
                propertySmoothSech2 (r t) (x t z₀)| ≤
            2 * 1 * (2 * a + a * cτ⁻¹ * |z₀|) := by
              have hInner : |propertyLowerInner β h q s t z₀| ≤ 1 := by
                simpa [propertyLowerInner, x, r, τ] using hT
              rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
              have htwo : 2 * |propertyLowerInner β h q s t z₀| ≤ 2 * 1 :=
                mul_le_mul_of_nonneg_left hInner (by norm_num)
              exact mul_le_mul htwo hins (abs_nonneg _)
                (by positivity)
        _ = 4 * a + 2 * (a * cτ⁻¹ * |z₀|) := by ring
        _ = 4 * a + 2 * (a * cτ⁻¹) * |z₀| := by ring)
    hboundInt
    (by
      filter_upwards [] with z₀
      intro t ht
      have hi := propertyLowerInner_hasDerivAt (h := h) hβ hq hs0 hs1
        (lt_trans (by linarith) ht.1) (lt_trans ht.2 (by linarith)) (z₀ := z₀)
      have hi' : HasDerivAt (fun v => propertyLowerInner β h q s v z₀)
          (-a / 2 * propertySmoothTanhSecond (r t) (x t z₀) +
            a / (2 * Real.sqrt (τ t)) * z₀ *
              propertySmoothSech2 (r t) (x t z₀)) t := by
        simpa [a, r, x, τ, propertyLowerRemainder, propertyLowerVariance] using hi
      change HasDerivAt (fun v => propertyLowerInner β h q s v z₀ ^ 2)
        (2 * propertyLowerInner β h q s t z₀ *
          (-a / 2 * propertySmoothTanhSecond (r t) (x t z₀) +
            a / (2 * Real.sqrt (τ t)) * z₀ *
              propertySmoothSech2 (r t) (x t z₀))) t
      have hout : HasDerivAt
          ((fun v => propertyLowerInner β h q s v z₀) *
            (fun v => propertyLowerInner β h q s v z₀))
          (2 * propertyLowerInner β h q s t z₀ *
            (-a / 2 * propertySmoothTanhSecond (r t) (x t z₀) +
              a / (2 * Real.sqrt (τ t)) * z₀ *
                propertySmoothSech2 (r t) (x t z₀))) t := by
        apply (hi'.mul hi').congr_deriv
        ring
      convert hout using 1
      funext v
      simp only [Pi.mul_apply, pow_two])
  have hraw := hd.2
  dsimp only [F, F'] at hraw
  have hτu : 0 < τ u := hτpos u hregionmem
  have hsqrtτu : Real.sqrt (τ u) ≠ 0 := (Real.sqrt_pos.2 hτu).ne'
  have hibp := property_gaussian_pair_ibp (r u) h (Real.sqrt (τ u))
  have hcalc :
      (∫ z₀, 2 * propertyLowerInner β h q s u z₀ *
        (-a / 2 * propertySmoothTanhSecond (r u) (x u z₀) +
          a / (2 * Real.sqrt (τ u)) * z₀ *
            propertySmoothSech2 (r u) (x u z₀)) ∂gaussianReal 0 1) =
        a * propertyLowerDerivativeCore β h q s u := by
    unfold propertyLowerInner propertyLowerDerivativeCore standardGaussianExpectation
    change (∫ z₀, 2 * propertySmoothTanh (r u) (x u z₀) *
        (-a / 2 * propertySmoothTanhSecond (r u) (x u z₀) +
          a / (2 * Real.sqrt (τ u)) * z₀ * propertySmoothSech2 (r u) (x u z₀))
        ∂gaussianReal 0 1) =
      a * ∫ z₀, propertySmoothSech2 (r u) (x u z₀) ^ 2
        ∂gaussianReal 0 1
    dsimp only [x] at hibp ⊢
    have hTx2Int : Integrable (fun z =>
        propertySmoothSech2 (r u) (h + Real.sqrt (τ u) * z) ^ 2)
        (gaussianReal 0 1) := by
      apply Integrable.of_bound (C := 1)
      · exact ((property_continuous_smoothSech2 (r u) |>.comp (by fun_prop)).pow 2)
          |>.aestronglyMeasurable
      · filter_upwards [] with z
        rw [Real.norm_eq_abs, abs_pow]
        have hz := property_smoothSech2_mem_Icc (r u) (h + Real.sqrt (τ u) * z)
        exact pow_le_one₀ (abs_nonneg _) (by rw [abs_of_nonneg hz.1]; exact hz.2)
    have hTTxxInt : Integrable (fun z =>
        propertySmoothTanh (r u) (h + Real.sqrt (τ u) * z) *
          propertySmoothTanhSecond (r u) (h + Real.sqrt (τ u) * z))
        (gaussianReal 0 1) := by
      apply Integrable.of_bound (C := 2)
      · exact ((property_continuous_smoothTanh (r u) |>.comp (by fun_prop)).mul
          (property_continuous_smoothTanhSecond (r u) |>.comp (by fun_prop)))
          |>.aestronglyMeasurable
      · filter_upwards [] with z
        rw [Real.norm_eq_abs, abs_mul]
        exact (mul_le_mul (property_smoothTanh_abs_le_one _ _)
          (property_smoothTanhSecond_abs_le_two _ _) (abs_nonneg _) (by norm_num)).trans_eq
            (by norm_num)
    rw [integral_add hTx2Int hTTxxInt] at hibp
    rw [show (fun z₀ => 2 * propertySmoothTanh (r u) (x u z₀) *
          (-a / 2 * propertySmoothTanhSecond (r u) (x u z₀) +
            a / (2 * Real.sqrt (τ u)) * z₀ * propertySmoothSech2 (r u) (x u z₀))) =
        fun z₀ => -a * (propertySmoothTanh (r u) (x u z₀) *
            propertySmoothTanhSecond (r u) (x u z₀)) +
          a / (2 * Real.sqrt (τ u)) *
            (z₀ * (2 * propertySmoothTanh (r u) (x u z₀) *
              propertySmoothSech2 (r u) (x u z₀))) by funext z₀; ring]
    rw [integral_add, integral_const_mul, integral_const_mul, hibp]
    · field_simp [hsqrtτu]
      ring
    · exact hTTxxInt.const_mul (-a)
    · have hz : Integrable (fun z : ℝ => |z|) (gaussianReal 0 1) := by
        simpa using integrable_abs_pow_gaussianReal_centered (1 : ℝ≥0) 1
      have hpair : Integrable (fun z => z *
          (2 * propertySmoothTanh (r u) (x u z) *
            propertySmoothSech2 (r u) (x u z))) (gaussianReal 0 1) := by
        apply (hz.const_mul 2).mono'
        · exact (continuous_id.mul
            ((continuous_const.mul
              (property_continuous_smoothTanh (r u) |>.comp (by fun_prop))).mul
              (property_continuous_smoothSech2 (r u) |>.comp (by fun_prop))))
            |>.aestronglyMeasurable
        · filter_upwards [] with z
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
          have hT := property_smoothTanh_abs_le_one (r u) (x u z)
          have hTx := property_smoothSech2_mem_Icc (r u) (x u z)
          rw [abs_of_nonneg hTx.1]
          simp only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          have hprod : 2 * |propertySmoothTanh (r u) (x u z)| *
              propertySmoothSech2 (r u) (x u z) ≤ 2 := by
            calc
              2 * |propertySmoothTanh (r u) (x u z)| *
                  propertySmoothSech2 (r u) (x u z) ≤ 2 * 1 * 1 := by
                    exact mul_le_mul
                      (mul_le_mul_of_nonneg_left hT (by norm_num)) hTx.2 hTx.1 (by norm_num)
              _ = 2 := by norm_num
          calc
            |z| * (2 * |propertySmoothTanh (r u) (x u z)| *
                propertySmoothSech2 (r u) (x u z)) ≤ |z| * 2 :=
                  mul_le_mul_of_nonneg_left hprod (abs_nonneg z)
            _ = 2 * |z| := by ring
      exact hpair.const_mul _
  rw [hcalc] at hraw
  simpa [a] using hraw

private lemma property_smoothSech2_sq_le_smoothSech4 (r x : ℝ) :
    propertySmoothSech2 r x ^ 2 ≤
      standardGaussianExpectation (fun z => propertySech (x + Real.sqrt r * z) ^ 4) := by
  let X : ℝ → ℝ := fun z => propertySech (x + Real.sqrt r * z) ^ 2
  have hXmem : MemLp X 2 (gaussianReal 0 1) := by
    apply memLp_of_bounded (a := 0) (b := 1)
    · exact ae_of_all _ fun z =>
        ⟨sq_nonneg _, (le_abs_self _).trans (property_abs_sech_sq_le_one _)⟩
    · exact ((property_continuous_sech.comp (by fun_prop)).pow 2).aestronglyMeasurable
  have hv := variance_nonneg X (gaussianReal 0 1)
  rw [variance_eq_sub hXmem] at hv
  have heq : (∫ z, X z ^ 2 ∂gaussianReal 0 1) =
      ∫ z, propertySech (x + Real.sqrt r * z) ^ 4 ∂gaussianReal 0 1 := by
    apply integral_congr_ae
    filter_upwards [] with z
    dsimp [X]
    ring
  unfold propertySmoothSech2 standardGaussianExpectation
  change (∫ z, X z ∂gaussianReal 0 1) ^ 2 ≤
    ∫ z, propertySech (x + Real.sqrt r * z) ^ 4 ∂gaussianReal 0 1
  rw [← heq]
  simp only [Pi.pow_apply] at hv
  linarith

private lemma property_gaussian_convolution_sech4 (h a b c : ℝ)
    (hc : c ^ 2 = a ^ 2 + b ^ 2) :
    (∫ x, ∫ y, propertySech (h + a * x + b * y) ^ 4 ∂gaussianReal 0 1
      ∂gaussianReal 0 1) =
      ∫ z, propertySech (h + c * z) ^ 4 ∂gaussianReal 0 1 := by
  let va : ℝ≥0 := NNReal.mk (a ^ 2) (sq_nonneg a) * 1
  let vb : ℝ≥0 := NNReal.mk (b ^ 2) (sq_nonneg b) * 1
  let vc : ℝ≥0 := NNReal.mk (c ^ 2) (sq_nonneg c) * 1
  have hma : Measure.map (fun x : ℝ => a * x) (gaussianReal 0 1) =
      gaussianReal 0 va := by
    simpa [va] using (gaussianReal_map_const_mul (μ := 0) (v := (1 : ℝ≥0)) a)
  have hmb : Measure.map (fun x : ℝ => b * x) (gaussianReal 0 1) =
      gaussianReal 0 vb := by
    simpa [vb] using (gaussianReal_map_const_mul (μ := 0) (v := (1 : ℝ≥0)) b)
  have hmc : Measure.map (fun x : ℝ => c * x) (gaussianReal 0 1) =
      gaussianReal 0 vc := by
    simpa [vc] using (gaussianReal_map_const_mul (μ := 0) (v := (1 : ℝ≥0)) c)
  have hv : va + vb = vc := by
    apply NNReal.eq
    simp [va, vb, vc, hc]
  have hf : Integrable (fun z : ℝ => propertySech (h + z) ^ 4)
      (gaussianReal 0 va ∗ gaussianReal 0 vb) := by
    rw [gaussianReal_conv_gaussianReal, hv, zero_add]
    apply Integrable.of_bound (C := 1)
    · exact ((property_continuous_sech.comp (by fun_prop)).pow 4).aestronglyMeasurable
    · filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (property_abs_sech_le_one _)
  have hprod : Integrable (fun p : ℝ × ℝ =>
      propertySech (h + (p.1 + p.2)) ^ 4)
      ((gaussianReal 0 va).prod (gaussianReal 0 vb)) := by
    rw [Measure.conv] at hf
    exact (integrable_map_measure hf.1 (by fun_prop)).mp hf
  have houter : AEStronglyMeasurable
      (fun x : ℝ => ∫ y, propertySech (h + (x + y)) ^ 4 ∂gaussianReal 0 vb)
      (gaussianReal 0 va) := hprod.integral_prod_left.1
  have hinner (x : ℝ) :
      (∫ y, propertySech (h + a * x + b * y) ^ 4 ∂gaussianReal 0 1) =
        ∫ y, propertySech (h + a * x + y) ^ 4 ∂gaussianReal 0 vb := by
    have hm : AEStronglyMeasurable (fun y : ℝ => propertySech (h + a * x + y) ^ 4)
        (Measure.map (fun y : ℝ => b * y) (gaussianReal 0 1)) :=
      ((property_continuous_sech.comp (by fun_prop)).pow 4).aestronglyMeasurable
    rw [← hmb, integral_map (by fun_prop) hm]
  have houter_map :
      (∫ x, ∫ y, propertySech (h + a * x + y) ^ 4 ∂gaussianReal 0 vb
        ∂gaussianReal 0 1) =
        ∫ x, ∫ y, propertySech (h + x + y) ^ 4 ∂gaussianReal 0 vb
          ∂gaussianReal 0 va := by
    have hm : AEStronglyMeasurable
        (fun x : ℝ => ∫ y, propertySech (h + (x + y)) ^ 4 ∂gaussianReal 0 vb)
        (Measure.map (fun x : ℝ => a * x) (gaussianReal 0 1)) := by
      simpa [hma] using houter
    rw [← hma]
    simpa only [add_assoc] using (integral_map (by fun_prop) hm).symm
  calc
    (∫ x, ∫ y, propertySech (h + a * x + b * y) ^ 4 ∂gaussianReal 0 1
        ∂gaussianReal 0 1) =
        ∫ x, ∫ y, propertySech (h + x + y) ^ 4 ∂gaussianReal 0 vb
          ∂gaussianReal 0 va := by
            rw [integral_congr_ae (Filter.Eventually.of_forall hinner)]
            exact houter_map
    _ = ∫ z, propertySech (h + z) ^ 4
          ∂(gaussianReal 0 va ∗ gaussianReal 0 vb) := by
            simpa only [add_assoc] using (integral_conv hf).symm
    _ = ∫ z, propertySech (h + z) ^ 4 ∂gaussianReal 0 vc := by
          rw [gaussianReal_conv_gaussianReal, hv, zero_add]
    _ = ∫ z, propertySech (h + c * z) ^ 4 ∂gaussianReal 0 1 := by
          rw [← hmc, integral_map (by fun_prop)]
          exact ((property_continuous_sech.comp (by fun_prop)).pow 4).aestronglyMeasurable

private noncomputable def propertySmoothSech4 (r x : ℝ) : ℝ :=
  standardGaussianExpectation (fun z => propertySech (x + Real.sqrt r * z) ^ 4)

private lemma property_continuous_smoothSech4 (r : ℝ) :
    Continuous (propertySmoothSech4 r) := by
  rw [continuous_iff_continuousAt]
  intro x
  unfold propertySmoothSech4 standardGaussianExpectation
  have hmeas : ∀ᶠ y in nhds x,
      AEStronglyMeasurable (fun z => propertySech (y + Real.sqrt r * z) ^ 4)
        (gaussianReal 0 1) :=
    Filter.Eventually.of_forall fun y =>
      ((property_continuous_sech.comp (by fun_prop)).pow 4).aestronglyMeasurable
  have hbound : ∀ᶠ y in nhds x, ∀ᵐ z ∂gaussianReal 0 1,
      ‖propertySech (y + Real.sqrt r * z) ^ 4‖ ≤ (1 : ℝ) := by
    exact Filter.Eventually.of_forall fun y => ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (property_abs_sech_le_one _)
  have hlim : ∀ᵐ z ∂gaussianReal 0 1,
      Tendsto (fun y => propertySech (y + Real.sqrt r * z) ^ 4) (nhds x)
        (nhds (propertySech (x + Real.sqrt r * z) ^ 4)) := by
    exact ae_of_all _ fun z =>
      (((property_continuous_sech.comp (by fun_prop)).pow 4).continuousAt.tendsto)
  exact tendsto_integral_filter_of_dominated_convergence
    (l := nhds x) (F := fun y z => propertySech (y + Real.sqrt r * z) ^ 4)
    (f := fun z => propertySech (x + Real.sqrt r * z) ^ 4)
    (bound := fun _ => (1 : ℝ)) hmeas hbound (integrable_const 1) hlim

private lemma property_smoothSech4_mem_Icc (r x : ℝ) :
    propertySmoothSech4 r x ∈ Set.Icc (0 : ℝ) 1 := by
  unfold propertySmoothSech4 standardGaussianExpectation
  constructor
  · exact integral_nonneg fun z => pow_nonneg (propertySech_pos _).le 4
  · calc
      (∫ z, propertySech (x + Real.sqrt r * z) ^ 4 ∂gaussianReal 0 1) ≤
          ∫ _z : ℝ, (1 : ℝ) ∂gaussianReal 0 1 := by
            apply integral_mono
            · apply Integrable.of_bound (C := 1)
              · exact ((property_continuous_sech.comp (by fun_prop)).pow 4)
                  |>.aestronglyMeasurable
              · filter_upwards [] with z
                rw [Real.norm_eq_abs, abs_pow]
                exact pow_le_one₀ (abs_nonneg _) (property_abs_sech_le_one _)
            · exact integrable_const 1
            · intro z
              have hp : |propertySech (x + Real.sqrt r * z) ^ 4| ≤ 1 := by
                rw [abs_pow]
                exact pow_le_one₀ (abs_nonneg _) (property_abs_sech_le_one _)
              exact (le_abs_self _).trans hp
      _ = 1 := by simp

private lemma propertyLowerDerivativeCore_le_baseSech4
    {β h q s u : ℝ} (hβ : 0 < β) (hq : 0 < q)
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hu0 : 0 < u) (huq : u < q) :
    propertyLowerDerivativeCore β h q s u ≤
      standardGaussianExpectation (fun z =>
        propertySech (h + β * Real.sqrt q * z) ^ 4) := by
  let τ : ℝ := propertyLowerVariance β q s u
  let r : ℝ := propertyLowerRemainder β q s u
  have hτ0 : 0 ≤ τ := by
    unfold τ propertyLowerVariance
    exact mul_nonneg (sq_nonneg β)
      (add_nonneg (mul_nonneg (sub_nonneg.mpr hs1) hq.le)
        (mul_nonneg hs0.le hu0.le))
  have hr0 : 0 ≤ r := by
    unfold r propertyLowerRemainder
    exact mul_nonneg (mul_nonneg hs0.le (sq_nonneg β)) (by linarith)
  have hsquares : (β * Real.sqrt q) ^ 2 =
      (Real.sqrt τ) ^ 2 + (Real.sqrt r) ^ 2 := by
    rw [Real.sq_sqrt hτ0, Real.sq_sqrt hr0]
    unfold τ r propertyLowerVariance propertyLowerRemainder
    nlinarith [Real.sq_sqrt hq.le]
  have houterInt : Integrable (fun z₀ =>
      propertySmoothSech4 r (h + Real.sqrt τ * z₀)) (gaussianReal 0 1) := by
    apply Integrable.of_bound (C := 1)
    · exact (property_continuous_smoothSech4 r |>.comp (by fun_prop)).aestronglyMeasurable
    · filter_upwards [] with z₀
      rw [Real.norm_eq_abs, abs_of_nonneg (property_smoothSech4_mem_Icc _ _).1]
      exact (property_smoothSech4_mem_Icc _ _).2
  unfold propertyLowerDerivativeCore standardGaussianExpectation
  change (∫ z₀, propertySmoothSech2 r (h + Real.sqrt τ * z₀) ^ 2
      ∂gaussianReal 0 1) ≤
    ∫ z, propertySech (h + β * Real.sqrt q * z) ^ 4 ∂gaussianReal 0 1
  calc
    (∫ z₀, propertySmoothSech2 r (h + Real.sqrt τ * z₀) ^ 2
        ∂gaussianReal 0 1) ≤
        ∫ z₀, propertySmoothSech4 r (h + Real.sqrt τ * z₀)
          ∂gaussianReal 0 1 := by
            apply integral_mono_of_nonneg
            · exact ae_of_all _ fun z₀ => sq_nonneg _
            · exact houterInt
            · exact ae_of_all _ fun z₀ =>
                property_smoothSech2_sq_le_smoothSech4 r
                  (h + Real.sqrt τ * z₀)
    _ = ∫ z, propertySech (h + β * Real.sqrt q * z) ^ 4
          ∂gaussianReal 0 1 := by
            unfold propertySmoothSech4 standardGaussianExpectation
            exact property_gaussian_convolution_sech4 h (Real.sqrt τ) (Real.sqrt r)
              (β * Real.sqrt q) hsquares

private theorem scalarOrderParameterCorrect_lower_derivative_le_pathAT
    {β h s u : ℝ} (hβ : 0 < β) (hh : 0 < h)
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hu0 : 0 < u) (huq : u < rsQ β h) :
    HasDerivAt (scalarOrderParameterCorrect β h s)
      (s * β ^ 2 * propertyLowerDerivativeCore β h (rsQ β h) s u) u ∧
    s * β ^ 2 * propertyLowerDerivativeCore β h (rsQ β h) s u ≤
      s * atParameter β h := by
  have hq := rsQ_pos hβ hh
  have hderiv := propertyLowerG_hasDerivAt (h := h) hβ hq hs0 hs1 hu0 huq
  have heq := scalarOrderParameterCorrect_eq_propertyLowerG (h := h) hβ hs0.le huq.le
  have hderiv' : HasDerivAt (scalarOrderParameterCorrect β h s)
      (s * β ^ 2 * propertyLowerDerivativeCore β h (rsQ β h) s u) u := by
    apply hderiv.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds huq] with v hv
    exact scalarOrderParameterCorrect_eq_propertyLowerG hβ hs0.le hv.le
  refine ⟨hderiv', ?_⟩
  have hcore := propertyLowerDerivativeCore_le_baseSech4 (h := h) hβ hq hs0 hs1 hu0 huq
  rw [atParameter_eq_beta_sq_mul_gaussian_sech_fourth hβ hh]
  change s * β ^ 2 * propertyLowerDerivativeCore β h (rsQ β h) s u ≤
    s * (β ^ 2 * standardGaussianExpectation (fun z =>
      propertySech (h + β * Real.sqrt (rsQ β h) * z) ^ 4))
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hcore (sq_nonneg β)) hs0.le

private lemma property_continuous_smoothSech_time (x : ℝ) :
    Continuous (fun r => propertySmoothSech r x) := by
  rw [continuous_iff_continuousAt]
  intro r₀
  unfold propertySmoothSech standardGaussianExpectation
  have hmeas : ∀ᶠ r in nhds r₀,
      AEStronglyMeasurable (fun z => propertySech (x + Real.sqrt r * z))
        (gaussianReal 0 1) :=
    Filter.Eventually.of_forall fun r =>
      (property_continuous_sech.comp (by fun_prop)).aestronglyMeasurable
  have hbound : ∀ᶠ r in nhds r₀, ∀ᵐ z ∂gaussianReal 0 1,
      ‖propertySech (x + Real.sqrt r * z)‖ ≤ (1 : ℝ) := by
    exact Filter.Eventually.of_forall fun r => ae_of_all _ fun z => by
      simpa [Real.norm_eq_abs] using property_abs_sech_le_one (x + Real.sqrt r * z)
  have hlim : ∀ᵐ z ∂gaussianReal 0 1,
      Tendsto (fun r => propertySech (x + Real.sqrt r * z)) (nhds r₀)
        (nhds (propertySech (x + Real.sqrt r₀ * z))) := by
    exact ae_of_all _ fun z =>
      (property_continuous_sech.comp (by fun_prop)).continuousAt.tendsto
  exact tendsto_integral_filter_of_dominated_convergence
    (l := nhds r₀) (F := fun r z => propertySech (x + Real.sqrt r * z))
    (f := fun z => propertySech (x + Real.sqrt r₀ * z))
    (bound := fun _ => (1 : ℝ)) hmeas hbound (integrable_const 1) hlim

private lemma property_continuous_smoothSech3_time (x : ℝ) :
    Continuous (fun r => propertySmoothSech3 r x) := by
  rw [continuous_iff_continuousAt]
  intro r₀
  unfold propertySmoothSech3 standardGaussianExpectation
  have hmeas : ∀ᶠ r in nhds r₀,
      AEStronglyMeasurable (fun z => propertySech3 (x + Real.sqrt r * z))
        (gaussianReal 0 1) :=
    Filter.Eventually.of_forall fun r =>
      ((property_continuous_sech.comp (by fun_prop)).pow 3).aestronglyMeasurable
  have hbound : ∀ᶠ r in nhds r₀, ∀ᵐ z ∂gaussianReal 0 1,
      ‖propertySech3 (x + Real.sqrt r * z)‖ ≤ (1 : ℝ) := by
    exact Filter.Eventually.of_forall fun r => ae_of_all _ fun z => by
      simpa [Real.norm_eq_abs] using property_abs_sech3_le_one (x + Real.sqrt r * z)
  have hlim : ∀ᵐ z ∂gaussianReal 0 1,
      Tendsto (fun r => propertySech3 (x + Real.sqrt r * z)) (nhds r₀)
        (nhds (propertySech3 (x + Real.sqrt r₀ * z))) := by
    exact ae_of_all _ fun z =>
      ((property_continuous_sech.pow 3).comp (by fun_prop)).continuousAt.tendsto
  exact tendsto_integral_filter_of_dominated_convergence
    (l := nhds r₀) (F := fun r z => propertySech3 (x + Real.sqrt r * z))
    (f := fun z => propertySech3 (x + Real.sqrt r₀ * z))
    (bound := fun _ => (1 : ℝ)) hmeas hbound (integrable_const 1) hlim

private lemma property_continuous_tiltedTanhSq_time (x : ℝ) :
    Continuous (fun r => propertyTiltedTanhSq r x) := by
  unfold propertyTiltedTanhSq
  exact continuous_const.sub
    (((Real.continuous_exp.comp (by fun_prop)).mul continuous_const).mul
      (property_continuous_smoothSech_time x))

private lemma property_continuous_tiltedSech4_time (x : ℝ) :
    Continuous (fun r => propertyTiltedSech4 r x) := by
  unfold propertyTiltedSech4
  exact ((Real.continuous_exp.comp (by fun_prop)).mul continuous_const).mul
    (property_continuous_smoothSech3_time x)

private lemma property_continuous_upperSech4Expectation (β h q s : ℝ) :
    Continuous (propertyUpperSech4Expectation β h q s) := by
  rw [continuous_iff_continuousAt]
  intro u₀
  unfold propertyUpperSech4Expectation heatSemigroup standardGaussianExpectation
  let C : ℝ := Real.exp (-(s * β ^ 2 * (u₀ - q)) / 2) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hexp : ∀ᶠ u in nhds u₀,
      Real.exp (-(s * β ^ 2 * (u - q)) / 2) < C := by
    have ht : Tendsto (fun u : ℝ => Real.exp (-(s * β ^ 2 * (u - q)) / 2))
        (nhds u₀) (nhds (Real.exp (-(s * β ^ 2 * (u₀ - q)) / 2))) :=
      (Real.continuous_exp.comp (by fun_prop)).continuousAt.tendsto
    exact ht.eventually (Iio_mem_nhds (by dsimp [C]; linarith))
  have hmeas : ∀ᶠ u in nhds u₀,
      AEStronglyMeasurable
        (fun z => propertyTiltedSech4 (s * β ^ 2 * (u - q))
          (h + Real.sqrt (β ^ 2 * q) * z)) (gaussianReal 0 1) :=
    Filter.Eventually.of_forall fun u =>
      (property_continuous_tiltedSech4 _ |>.comp (by fun_prop)).aestronglyMeasurable
  have hbound : ∀ᶠ u in nhds u₀, ∀ᵐ z ∂gaussianReal 0 1,
      ‖propertyTiltedSech4 (s * β ^ 2 * (u - q))
        (h + Real.sqrt (β ^ 2 * q) * z)‖ ≤ C := by
    filter_upwards [hexp] with u hu
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs]
      unfold propertyTiltedSech4
      have hnonneg : 0 ≤ Real.exp (-(s * β ^ 2 * (u - q)) / 2) *
          propertySech (h + Real.sqrt (β ^ 2 * q) * z) *
          propertySmoothSech3 (s * β ^ 2 * (u - q))
            (h + Real.sqrt (β ^ 2 * q) * z) := by
        exact mul_nonneg
          (mul_nonneg (Real.exp_pos _).le (propertySech_pos _).le)
          (property_smoothSech3_nonneg _ _)
      rw [abs_of_nonneg hnonneg]
      calc
        _ ≤ Real.exp (-(s * β ^ 2 * (u - q)) / 2) * 1 * 1 := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (propertySech_le_one _) (Real.exp_pos _).le)
            (property_smoothSech3_le_one _ _) (property_smoothSech3_nonneg _ _)
            (mul_nonneg (Real.exp_pos _).le (by norm_num))
        _ ≤ C := by simpa using hu.le
  have hlim : ∀ᵐ z ∂gaussianReal 0 1,
      Tendsto
        (fun u => propertyTiltedSech4 (s * β ^ 2 * (u - q))
          (h + Real.sqrt (β ^ 2 * q) * z)) (nhds u₀)
        (nhds (propertyTiltedSech4 (s * β ^ 2 * (u₀ - q))
          (h + Real.sqrt (β ^ 2 * q) * z))) := by
    exact ae_of_all _ fun z =>
      (property_continuous_tiltedSech4_time _ |>.comp (by fun_prop)).continuousAt.tendsto
  exact tendsto_integral_filter_of_dominated_convergence
    (l := nhds u₀)
    (F := fun u z => propertyTiltedSech4 (s * β ^ 2 * (u - q))
      (h + Real.sqrt (β ^ 2 * q) * z))
    (f := fun z => propertyTiltedSech4 (s * β ^ 2 * (u₀ - q))
      (h + Real.sqrt (β ^ 2 * q) * z))
    (bound := fun _ => C) hmeas hbound (integrable_const C) hlim

private lemma property_continuous_upperG (β h q s : ℝ) :
    Continuous (propertyUpperG β h q s) := by
  rw [continuous_iff_continuousAt]
  intro u₀
  unfold propertyUpperG heatSemigroup standardGaussianExpectation
  let C : ℝ := Real.exp (-(s * β ^ 2 * (u₀ - q)) / 2) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hexp : ∀ᶠ u in nhds u₀,
      Real.exp (-(s * β ^ 2 * (u - q)) / 2) < C := by
    have ht : Tendsto (fun u : ℝ => Real.exp (-(s * β ^ 2 * (u - q)) / 2))
        (nhds u₀) (nhds (Real.exp (-(s * β ^ 2 * (u₀ - q)) / 2))) :=
      (Real.continuous_exp.comp (by fun_prop)).continuousAt.tendsto
    exact ht.eventually (Iio_mem_nhds (by dsimp [C]; linarith))
  have hmeas : ∀ᶠ u in nhds u₀,
      AEStronglyMeasurable
        (fun z => propertyTiltedTanhSq (s * β ^ 2 * (u - q))
          (h + Real.sqrt (β ^ 2 * q) * z)) (gaussianReal 0 1) :=
    Filter.Eventually.of_forall fun u =>
      (property_continuous_tiltedTanhSq _ |>.comp (by fun_prop)).aestronglyMeasurable
  have hbound : ∀ᶠ u in nhds u₀, ∀ᵐ z ∂gaussianReal 0 1,
      ‖propertyTiltedTanhSq (s * β ^ 2 * (u - q))
        (h + Real.sqrt (β ^ 2 * q) * z)‖ ≤ 1 + C := by
    filter_upwards [hexp] with u hu
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs]
      unfold propertyTiltedTanhSq
      have hp : 0 ≤ Real.exp (-(s * β ^ 2 * (u - q)) / 2) *
          propertySech (h + Real.sqrt (β ^ 2 * q) * z) *
          propertySmoothSech (s * β ^ 2 * (u - q))
            (h + Real.sqrt (β ^ 2 * q) * z) := by
        exact mul_nonneg
          (mul_nonneg (Real.exp_pos _).le (propertySech_pos _).le)
          (property_smoothSech_nonneg _ _)
      have hpC : Real.exp (-(s * β ^ 2 * (u - q)) / 2) *
          propertySech (h + Real.sqrt (β ^ 2 * q) * z) *
          propertySmoothSech (s * β ^ 2 * (u - q))
            (h + Real.sqrt (β ^ 2 * q) * z) ≤ C := by
        calc
          _ ≤ Real.exp (-(s * β ^ 2 * (u - q)) / 2) * 1 * 1 := by
            exact mul_le_mul
              (mul_le_mul_of_nonneg_left (propertySech_le_one _) (Real.exp_pos _).le)
              (property_smoothSech_le_one _ _) (property_smoothSech_nonneg _ _)
              (mul_nonneg (Real.exp_pos _).le (by norm_num))
          _ ≤ C := by simpa using hu.le
      exact (abs_sub (1 : ℝ) _).trans (by
        rw [abs_of_nonneg hp]
        nlinarith)
  have hlim : ∀ᵐ z ∂gaussianReal 0 1,
      Tendsto
        (fun u => propertyTiltedTanhSq (s * β ^ 2 * (u - q))
          (h + Real.sqrt (β ^ 2 * q) * z)) (nhds u₀)
        (nhds (propertyTiltedTanhSq (s * β ^ 2 * (u₀ - q))
          (h + Real.sqrt (β ^ 2 * q) * z))) := by
    exact ae_of_all _ fun z =>
      (property_continuous_tiltedTanhSq_time _ |>.comp (by fun_prop)).continuousAt.tendsto
  exact tendsto_integral_filter_of_dominated_convergence
    (l := nhds u₀)
    (F := fun u z => propertyTiltedTanhSq (s * β ^ 2 * (u - q))
      (h + Real.sqrt (β ^ 2 * q) * z))
    (f := fun z => propertyTiltedTanhSq (s * β ^ 2 * (u₀ - q))
      (h + Real.sqrt (β ^ 2 * q) * z))
    (bound := fun _ => 1 + C) hmeas hbound (integrable_const (1 + C)) hlim

private lemma property_continuous_lowerInner_time (β h q s z₀ : ℝ) :
    Continuous (fun u => propertyLowerInner β h q s u z₀) := by
  unfold propertyLowerInner propertySmoothTanh standardGaussianExpectation
  rw [continuous_iff_continuousAt]
  intro u₀
  have hmeas : ∀ᶠ u in nhds u₀,
      AEStronglyMeasurable (fun z => Real.tanh
        (h + Real.sqrt (propertyLowerVariance β q s u) * z₀ +
          Real.sqrt (propertyLowerRemainder β q s u) * z))
        (gaussianReal 0 1) :=
    Filter.Eventually.of_forall fun u =>
      (property_continuous_tanh.comp (by fun_prop)).aestronglyMeasurable
  have hbound : ∀ᶠ u in nhds u₀, ∀ᵐ z ∂gaussianReal 0 1,
      ‖Real.tanh (h + Real.sqrt (propertyLowerVariance β q s u) * z₀ +
        Real.sqrt (propertyLowerRemainder β q s u) * z)‖ ≤ (1 : ℝ) := by
    exact Filter.Eventually.of_forall fun u => ae_of_all _ fun z => by
      simpa [Real.norm_eq_abs] using property_abs_tanh_le_one
        (h + Real.sqrt (propertyLowerVariance β q s u) * z₀ +
          Real.sqrt (propertyLowerRemainder β q s u) * z)
  have hlim : ∀ᵐ z ∂gaussianReal 0 1,
      Tendsto (fun u => Real.tanh
        (h + Real.sqrt (propertyLowerVariance β q s u) * z₀ +
          Real.sqrt (propertyLowerRemainder β q s u) * z)) (nhds u₀)
        (nhds (Real.tanh
          (h + Real.sqrt (propertyLowerVariance β q s u₀) * z₀ +
            Real.sqrt (propertyLowerRemainder β q s u₀) * z))) := by
    exact ae_of_all _ fun z =>
      (property_continuous_tanh.comp (by
        unfold propertyLowerVariance propertyLowerRemainder
        fun_prop)).continuousAt.tendsto
  exact tendsto_integral_filter_of_dominated_convergence
    (l := nhds u₀)
    (F := fun u z => Real.tanh
      (h + Real.sqrt (propertyLowerVariance β q s u) * z₀ +
        Real.sqrt (propertyLowerRemainder β q s u) * z))
    (f := fun z => Real.tanh
      (h + Real.sqrt (propertyLowerVariance β q s u₀) * z₀ +
        Real.sqrt (propertyLowerRemainder β q s u₀) * z))
    (bound := fun _ => (1 : ℝ)) hmeas hbound (integrable_const 1) hlim

private lemma property_continuous_lowerG (β h q s : ℝ) :
    Continuous (propertyLowerG β h q s) := by
  rw [continuous_iff_continuousAt]
  intro u₀
  unfold propertyLowerG standardGaussianExpectation
  have hmeas : ∀ᶠ u in nhds u₀,
      AEStronglyMeasurable (fun z₀ => propertyLowerInner β h q s u z₀ ^ 2)
        (gaussianReal 0 1) :=
    Filter.Eventually.of_forall fun u => by
      apply Continuous.aestronglyMeasurable
      unfold propertyLowerInner
      exact (property_continuous_smoothTanh _ |>.comp (by fun_prop)).pow 2
  have hbound : ∀ᶠ u in nhds u₀, ∀ᵐ z₀ ∂gaussianReal 0 1,
      ‖propertyLowerInner β h q s u z₀ ^ 2‖ ≤ (1 : ℝ) := by
    exact Filter.Eventually.of_forall fun u => ae_of_all _ fun z₀ => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (by
        unfold propertyLowerInner
        exact property_smoothTanh_abs_le_one _ _)
  have hlim : ∀ᵐ z₀ ∂gaussianReal 0 1,
      Tendsto (fun u => propertyLowerInner β h q s u z₀ ^ 2) (nhds u₀)
        (nhds (propertyLowerInner β h q s u₀ z₀ ^ 2)) := by
    exact ae_of_all _ fun z₀ =>
      ((property_continuous_lowerInner_time β h q s z₀).pow 2).continuousAt.tendsto
  exact tendsto_integral_filter_of_dominated_convergence
    (l := nhds u₀) (F := fun u z₀ => propertyLowerInner β h q s u z₀ ^ 2)
    (f := fun z₀ => propertyLowerInner β h q s u₀ z₀ ^ 2)
    (bound := fun _ => (1 : ℝ)) hmeas hbound (integrable_const 1) hlim

private lemma property_smoothSech3_le_smoothSech (r x : ℝ) :
    propertySmoothSech3 r x ≤ propertySmoothSech r x := by
  unfold propertySmoothSech3 propertySmoothSech standardGaussianExpectation propertySech3
  apply integral_mono (property_integrable_sech3_affine x (Real.sqrt r))
    (property_integrable_sech_affine x (Real.sqrt r))
  intro z
  have hp := propertySech_pos (x + Real.sqrt r * z)
  have h1 := propertySech_le_one (x + Real.sqrt r * z)
  let y := propertySech (x + Real.sqrt r * z)
  have hy2 : y ^ 2 ≤ 1 := by nlinarith [sq_nonneg (y - 1)]
  change y ^ 3 ≤ y
  calc
    y ^ 3 = y * y ^ 2 := by ring
    _ ≤ y * 1 := mul_le_mul_of_nonneg_left hy2 hp.le
    _ = y := by ring

private lemma property_tiltedSech4_le_one_sub_tiltedTanhSq
    {r x : ℝ} (_hr : 0 ≤ r) :
    propertyTiltedSech4 r x ≤ 1 - propertyTiltedTanhSq r x := by
  unfold propertyTiltedSech4 propertyTiltedTanhSq
  rw [sub_sub_cancel]
  exact mul_le_mul_of_nonneg_left (property_smoothSech3_le_smoothSech r x)
    (mul_nonneg (Real.exp_pos _).le (propertySech_pos x).le)

private lemma propertyUpperSech4Expectation_le_one_sub_upperG
    {β h q s u : ℝ} (hs : 0 ≤ s) (hu : q ≤ u) :
    propertyUpperSech4Expectation β h q s u ≤ 1 - propertyUpperG β h q s u := by
  let r : ℝ := s * β ^ 2 * (u - q)
  have hr : 0 ≤ r := mul_nonneg (mul_nonneg hs (sq_nonneg β)) (sub_nonneg.mpr hu)
  have hleft := property_integrable_tiltedSech4_affine hr h (Real.sqrt (β ^ 2 * q))
  have hright := property_integrable_tiltedTanhSq_affine hr h (Real.sqrt (β ^ 2 * q))
  unfold propertyUpperSech4Expectation propertyUpperG heatSemigroup
    standardGaussianExpectation
  change (∫ z, propertyTiltedSech4 r (h + Real.sqrt (β ^ 2 * q) * z)
      ∂gaussianReal 0 1) ≤
    1 - ∫ z, propertyTiltedTanhSq r (h + Real.sqrt (β ^ 2 * q) * z)
      ∂gaussianReal 0 1
  have hone : (∫ _z : ℝ, (1 : ℝ) ∂gaussianReal 0 1) = 1 := by simp
  rw [← hone, ← integral_sub (integrable_const 1) hright]
  exact integral_mono hleft ((integrable_const 1).sub hright) fun z =>
    property_tiltedSech4_le_one_sub_tiltedTanhSq hr

private lemma propertyUpperSech4Expectation_eq_localField
    {β h q s u : ℝ} (hs : 0 ≤ s) (hu : q < u) :
    propertyUpperSech4Expectation β h q s u =
      localFieldExpectation β h q s u (fun x => (Real.cosh x)⁻¹ ^ 4) := by
  have hnot : ¬u ≤ q := not_le_of_gt hu
  have hr : 0 ≤ s * β ^ 2 * (u - q) :=
    mul_nonneg (mul_nonneg hs (sq_nonneg β)) (sub_nonneg.mpr hu.le)
  unfold propertyUpperSech4Expectation localFieldExpectation
  rw [if_neg hnot]
  congr 2
  funext x
  change propertyTiltedSech4 (s * β ^ 2 * (u - q)) x =
    tiltedHeatSemigroup (s * β ^ 2 * (u - q))
      (fun y => propertySech y ^ 4) x
  exact (tiltedHeatSemigroup_sech_four_eq hr x).symm

private lemma propertyUpperG_at_breakpoint
    {β h q s : ℝ} (hβ : 0 < β) (hq : q = rsQ β h) :
    propertyUpperG β h q s q = q := by
  subst q
  have hzero (x : ℝ) : propertyTiltedTanhSq 0 x = Real.tanh x ^ 2 := by
    have hsmooth : propertySmoothSech 0 x = propertySech x := by
      unfold propertySmoothSech standardGaussianExpectation
      simp
    unfold propertyTiltedTanhSq
    rw [hsmooth]
    simp only [neg_zero, zero_div, Real.exp_zero, one_mul]
    nlinarith [property_tanh_sq_add_sech_sq x]
  unfold propertyUpperG heatSemigroup
  simp only [sub_self, mul_zero, hzero]
  have hsqrt : Real.sqrt (β ^ 2 * rsQ β h) =
      β * Real.sqrt (rsQ β h) := by
    rw [Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq_eq_abs, abs_of_pos hβ]
  unfold standardGaussianExpectation
  rw [hsqrt]
  exact (rsQ_fixedPoint β h).symm

private lemma propertyLowerG_at_breakpoint
    {β h q s : ℝ} (hβ : 0 < β) (_hh : 0 < h)
    (hs : 0 ≤ s) (hq : q = rsQ β h) :
    propertyLowerG β h q s q = q := by
  subst q
  rw [← scalarOrderParameterCorrect_eq_propertyLowerG (h := h) hβ hs le_rfl]
  exact scalarOrderParameterCorrect_at_rsQ hβ s

private lemma scalarOrderParameterCorrect_zero_path
    {β h u : ℝ} (hβ : 0 < β) (_hh : 0 < h) :
    scalarOrderParameterCorrect β h 0 u = rsQ β h := by
  by_cases hu : u ≤ rsQ β h
  · rw [scalarOrderParameterCorrect_eq_propertyLowerG (h := h) hβ (by norm_num) hu]
    have hinner (z₀ : ℝ) : propertyLowerInner β h (rsQ β h) 0 u z₀ =
        Real.tanh (h + Real.sqrt (β ^ 2 * rsQ β h) * z₀) := by
      unfold propertyLowerInner propertyLowerRemainder propertyLowerVariance
        propertySmoothTanh standardGaussianExpectation
      simp
    unfold propertyLowerG standardGaussianExpectation
    apply Eq.trans (integral_congr_ae (ae_of_all _ fun z₀ => by rw [hinner z₀]))
    have hsqrt : Real.sqrt (β ^ 2 * rsQ β h) =
        β * Real.sqrt (rsQ β h) := by
      rw [Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq_eq_abs, abs_of_pos hβ]
    rw [hsqrt]
    exact (rsQ_fixedPoint β h).symm
  · have hu' : rsQ β h < u := lt_of_not_ge hu
    rw [scalarOrderParameterCorrect_eq_propertyUpperG (h := h) (by norm_num) hu']
    have hupper : propertyUpperG β h (rsQ β h) 0 u =
        propertyUpperG β h (rsQ β h) 0 (rsQ β h) := by
      unfold propertyUpperG
      simp only [zero_mul]
    rw [hupper]
    exact propertyUpperG_at_breakpoint hβ rfl

private lemma property_atParameter_nonneg {β h : ℝ} (hβ : 0 < β) (hh : 0 < h) :
    0 ≤ atParameter β h := by
  rw [atParameter_eq_beta_sq_mul_gaussian_sech_fourth hβ hh]
  exact mul_nonneg (sq_nonneg β) (integral_nonneg fun z => pow_nonneg (inv_nonneg.mpr
    (Real.cosh_pos _).le) 4)

private lemma propertyLowerG_increment_le_pathAT
    {β h s u : ℝ} (hβ : 0 < β) (hh : 0 < h)
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hu0 : 0 ≤ u) (huq : u < rsQ β h) :
    propertyLowerG β h (rsQ β h) s (rsQ β h) -
        propertyLowerG β h (rsQ β h) s u ≤
      s * atParameter β h * (rsQ β h - u) := by
  let f := propertyLowerG β h (rsQ β h) s
  have hcont : ContinuousOn f (Set.Icc u (rsQ β h)) :=
    (property_continuous_lowerG β h (rsQ β h) s).continuousOn
  have hdiff : DifferentiableOn ℝ f (Set.Ioo u (rsQ β h)) := by
    intro v hv
    exact (propertyLowerG_hasDerivAt (h := h) hβ (rsQ_pos hβ hh) hs0 hs1
      (lt_of_le_of_lt hu0 hv.1) hv.2).differentiableAt.differentiableWithinAt
  obtain ⟨v, hv, hvSlope⟩ := exists_deriv_eq_slope f huq hcont hdiff
  have hvBound := (scalarOrderParameterCorrect_lower_derivative_le_pathAT
    hβ hh hs0 hs1 (lt_of_le_of_lt hu0 hv.1) hv.2).2
  have hvDeriv := (propertyLowerG_hasDerivAt (h := h) hβ (rsQ_pos hβ hh)
    hs0 hs1 (lt_of_le_of_lt hu0 hv.1) hv.2).deriv
  have hratio :
      (f (rsQ β h) - f u) / (rsQ β h - u) ≤ s * atParameter β h := by
    rw [← hvSlope, hvDeriv]
    exact hvBound
  exact (div_le_iff₀ (sub_pos.mpr huq)).mp hratio

private lemma propertyUpperSech4Expectation_at_breakpoint
    {β h s : ℝ} (hβ : 0 < β) (hh : 0 < h) :
    β ^ 2 * propertyUpperSech4Expectation β h (rsQ β h) s (rsQ β h) =
      atParameter β h := by
  have hzero (x : ℝ) : propertyTiltedSech4 0 x = propertySech x ^ 4 := by
    have hsmooth : propertySmoothSech3 0 x = propertySech3 x := by
      unfold propertySmoothSech3 standardGaussianExpectation
      simp
    unfold propertyTiltedSech4
    rw [hsmooth]
    simp only [neg_zero, zero_div, Real.exp_zero, one_mul]
    unfold propertySech3
    ring
  have hsqrt : Real.sqrt (β ^ 2 * rsQ β h) =
      β * Real.sqrt (rsQ β h) := by
    rw [Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq_eq_abs, abs_of_pos hβ]
  rw [atParameter_eq_beta_sq_mul_gaussian_sech_fourth hβ hh]
  unfold propertyUpperSech4Expectation heatSemigroup standardGaussianExpectation
  simp only [sub_self, mul_zero, hzero, hsqrt]
  rfl

private lemma propertyUpperSech4Expectation_increment_abs_le
    {β h q s u : ℝ} (hβ : 0 < β) (hs : 0 < s) (hu : q < u) :
    |propertyUpperSech4Expectation β h q s u -
        propertyUpperSech4Expectation β h q s q| ≤
      7 * (s * β ^ 2) * (u - q) := by
  let f := propertyUpperSech4Expectation β h q s
  let a : ℝ := s * β ^ 2
  have ha : 0 < a := mul_pos hs (sq_pos_of_pos hβ)
  have hcont : ContinuousOn f (Set.Icc q u) :=
    (property_continuous_upperSech4Expectation β h q s).continuousOn
  have hdiff : DifferentiableOn ℝ f (Set.Ioo q u) := by
    intro v hv
    exact (propertyUpperSech4Expectation_hasDerivAt (h := h) hβ hs hv.1)
      |>.differentiableAt.differentiableWithinAt
  obtain ⟨v, hv, hvSlope⟩ := exists_deriv_eq_slope f hu hcont hdiff
  have hvDeriv :=
    (propertyUpperSech4Expectation_hasDerivAt (h := h) hβ hs hv.1).deriv
  have hvTime := propertyUpperSech4TimeExpectation_abs_le_seven
    (β := β) (h := h) (q := q) (s := s) (u := v) hs.le hv.1.le
  have hratio : |(f u - f q) / (u - q)| ≤ 7 * a := by
    rw [← hvSlope, hvDeriv, abs_mul, abs_of_pos ha]
    exact mul_le_mul_of_nonneg_left hvTime ha.le |>.trans_eq (by ring)
  rw [abs_div, abs_of_pos (sub_pos.mpr hu)] at hratio
  have hmul := (div_le_iff₀ (sub_pos.mpr hu)).mp hratio
  simpa only [f, a, mul_assoc] using hmul

private lemma propertyUpperG_derivative_le_pathAT_large
    {β h s u : ℝ} (hβ : 0 < β) (hh : 0 < h)
    (hs0 : 0 < s) (hs1 : s ≤ 1)
    (huq : rsQ β h < u) (hu1 : u ≤ 1)
    (hlarge : 1 < s * β ^ 2 * (1 - rsQ β h)) :
    s * β ^ 2 * propertyUpperSech4Expectation β h (rsQ β h) s u ≤
      s * atParameter β h := by
  have hcomp := upperComparison hβ hh ⟨hs0.le, hs1⟩ ⟨huq.le, hu1⟩ hlarge
  rw [← propertyUpperSech4Expectation_eq_localField hs0.le huq] at hcomp
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hcomp hs0.le

private lemma propertyUpperG_derivative_le_drift
    {β h q s u : ℝ} (_hβ : 0 < β) (hs0 : 0 < s) (hu : q < u) :
    s * β ^ 2 * propertyUpperSech4Expectation β h q s u ≤
      (s * β ^ 2) * (1 - propertyUpperG β h q s u) := by
  exact mul_le_mul_of_nonneg_left
    (propertyUpperSech4Expectation_le_one_sub_upperG hs0.le hu.le)
    (mul_nonneg hs0.le (sq_nonneg β))

private lemma propertyUpperG_increment_lt_large
    {β h s u : ℝ} (hβ : 0 < β) (hh : 0 < h)
    (hs0 : 0 < s) (hs1 : s ≤ 1)
    (huq : rsQ β h < u) (hu1 : u ≤ 1)
    (hlarge : 1 < s * β ^ 2 * (1 - rsQ β h))
    (hAT : atParameter β h < 1) :
    propertyUpperG β h (rsQ β h) s u < u := by
  let q := rsQ β h
  let f := propertyUpperG β h q s
  have hcont : ContinuousOn f (Set.Icc q u) :=
    (property_continuous_upperG β h q s).continuousOn
  have hdiff : DifferentiableOn ℝ f (Set.Ioo q u) := by
    intro v hv
    exact (propertyUpperG_hasDerivAt hβ hs0 hv.1).differentiableAt.differentiableWithinAt
  obtain ⟨v, hv, hvSlope⟩ := exists_deriv_eq_slope f huq hcont hdiff
  have hvDeriv := (propertyUpperG_hasDerivAt (h := h) hβ hs0 hv.1).deriv
  have hvBound := propertyUpperG_derivative_le_pathAT_large hβ hh hs0 hs1 hv.1
    (le_trans hv.2.le hu1) hlarge
  have hsAT : s * atParameter β h < 1 := by
    have hnonneg := property_atParameter_nonneg hβ hh
    nlinarith [mul_le_mul_of_nonneg_right hs1 hnonneg]
  have hratio : (f u - f q) / (u - q) < 1 := by
    rw [← hvSlope, hvDeriv]
    exact lt_of_le_of_lt hvBound hsAT
  have hslope : f u - f q < u - q :=
    (div_lt_one (sub_pos.mpr huq)).mp hratio
  have hfq : f q = q := propertyUpperG_at_breakpoint hβ rfl
  dsimp [f, q] at hfq ⊢
  linarith

private lemma propertyUpperG_lt_small
    {β h s u : ℝ} (hβ : 0 < β) (_hh : 0 < h)
    (hs0 : 0 < s) (huq : rsQ β h < u)
    (hsmall : s * β ^ 2 * (1 - rsQ β h) ≤ 1) :
    propertyUpperG β h (rsQ β h) s u < u := by
  let q : ℝ := rsQ β h
  let a : ℝ := s * β ^ 2
  let g : ℝ → ℝ := propertyUpperG β h q s
  let subq : ℝ → ℝ := id - fun _ => q
  let linear : ℝ → ℝ := (fun y => a * y) ∘ subq
  let expo : ℝ → ℝ := fun v => Real.exp (linear v)
  let diff : ℝ → ℝ := g - id
  let F : ℝ → ℝ := expo * diff
  have ha : 0 < a := mul_pos hs0 (sq_pos_of_pos hβ)
  have hcont : ContinuousOn F (Set.Icc q u) := by
    have hexpoCont : Continuous expo := by
      dsimp [expo, linear, subq]
      fun_prop
    have hdiffCont : Continuous diff := by
      dsimp [diff, g]
      exact (property_continuous_upperG β h q s).sub continuous_id
    exact (hexpoCont.mul hdiffCont).continuousOn
  have hdiff : DifferentiableOn ℝ F (Set.Ioo q u) := by
    intro v hv
    have hg := propertyUpperG_hasDerivAt (h := h) hβ hs0 hv.1
    have hsub : HasDerivAt subq 1 v := by
      exact (hasDerivAt_id v).sub_const q
    have hlinear : HasDerivAt linear a v := by
      exact (hasDerivAt_const_mul (x := subq v) a).comp v hsub |>.congr_deriv (by ring)
    have hexpo : HasDerivAt expo (Real.exp (linear v) * a) v := hlinear.exp
    have hdiff' : HasDerivAt diff
        (s * β ^ 2 * propertyUpperSech4Expectation β h q s v - 1) v := by
      exact hg.sub (hasDerivAt_id v)
    exact (hexpo.mul hdiff').differentiableAt.differentiableWithinAt
  obtain ⟨v, hv, hvSlope⟩ := exists_deriv_eq_slope F huq hcont hdiff
  have hg := propertyUpperG_hasDerivAt (h := h) hβ hs0 hv.1
  have hsub : HasDerivAt subq 1 v := by
    exact (hasDerivAt_id v).sub_const q
  have hlinear : HasDerivAt linear a v := by
    exact (hasDerivAt_const_mul (x := subq v) a).comp v hsub |>.congr_deriv (by ring)
  have hexpo : HasDerivAt expo (Real.exp (linear v) * a) v := hlinear.exp
  have hdiff' : HasDerivAt diff
      (s * β ^ 2 * propertyUpperSech4Expectation β h q s v - 1) v := by
    exact hg.sub (hasDerivAt_id v)
  have hFderiv := (hexpo.mul hdiff').deriv
  have hFderivEq : deriv F v = Real.exp (a * (v - q)) *
      (a * (g v - v) +
        s * β ^ 2 * propertyUpperSech4Expectation β h q s v - 1) := by
    rw [hFderiv]
    dsimp [F, expo, linear, subq, diff]
    ring
  have hgBound := propertyUpperG_derivative_le_drift (h := h) hβ hs0 hv.1
  have hforce : a * (1 - v) - 1 < 0 := by
    have hav : a * (1 - v) < a * (1 - q) := by
      exact mul_lt_mul_of_pos_left (by linarith [hv.1]) ha
    dsimp [a, q] at hav ⊢
    linarith
  have hinside : a * (g v - v) +
      s * β ^ 2 * propertyUpperSech4Expectation β h q s v - 1 < 0 := by
    dsimp [a, g]
    have := hgBound
    nlinarith [hforce]
  have hderivNeg : deriv F v < 0 := by
    rw [hFderivEq]
    exact mul_neg_of_pos_of_neg (Real.exp_pos _) hinside
  have hratio : (F u - F q) / (u - q) < 0 := by
    rw [← hvSlope]
    exact hderivNeg
  have hFu : F u < F q := by
    have hden := sub_pos.mpr huq
    rcases div_neg_iff.mp hratio with hbad | hgood
    · linarith [hbad.2]
    · linarith [hgood.1]
  have hgq : g q = q := propertyUpperG_at_breakpoint hβ rfl
  have hexpPos := Real.exp_pos (a * (u - q))
  have hprod : Real.exp (a * (u - q)) * (g u - u) < 0 := by
    simpa [F, expo, linear, subq, diff, hgq] using hFu
  have hgu : g u - u < 0 := by
    rcases (mul_neg_iff.mp hprod) with hgood | hbad
    · exact hgood.2
    · linarith
  dsimp [g, q] at hgu ⊢
  linarith

private lemma propertyUpperG_local_gap {K : Set (ℝ × ℝ)}
    (data : UniformATData K) {β h s u : ℝ}
    (hp : (β, h) ∈ K) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (huq : rsQ β h < u)
    (hnear : u - rsQ β h ≤
      data.gap / (14 * (1 + data.βmax ^ 4))) :
    data.gap / 2 * (u - rsQ β h) ≤
      u - propertyUpperG β h (rsQ β h) s u := by
  let q : ℝ := rsQ β h
  let a : ℝ := s * β ^ 2
  let f : ℝ → ℝ := propertyUpperG β h q s
  have hβ : 0 < β := by simpa using data.β_pos (β, h) hp
  have hh : 0 < h := by simpa using data.h_pos (β, h) hp
  have ha : 0 < a := mul_pos hs0 (sq_pos_of_pos hβ)
  have hcont : ContinuousOn f (Set.Icc q u) :=
    (property_continuous_upperG β h q s).continuousOn
  have hdiff : DifferentiableOn ℝ f (Set.Ioo q u) := by
    intro v hv
    exact (propertyUpperG_hasDerivAt (h := h) hβ hs0 hv.1)
      |>.differentiableAt.differentiableWithinAt
  obtain ⟨v, hv, hvSlope⟩ := exists_deriv_eq_slope f huq hcont hdiff
  have hvDeriv := (propertyUpperG_hasDerivAt (h := h) hβ hs0 hv.1).deriv
  have hcore := propertyUpperSech4Expectation_increment_abs_le
    (h := h) hβ hs0 hv.1
  have hcoreUpper :
      propertyUpperSech4Expectation β h q s v ≤
        propertyUpperSech4Expectation β h q s q + 7 * a * (v - q) := by
    have hle := le_abs_self
      (propertyUpperSech4Expectation β h q s v -
        propertyUpperSech4Expectation β h q s q)
    change |propertyUpperSech4Expectation β h q s v -
      propertyUpperSech4Expectation β h q s q| ≤ 7 * a * (v - q) at hcore
    linarith
  have hqcore := propertyUpperSech4Expectation_at_breakpoint
    (s := s) hβ hh
  have hβle : β ≤ data.βmax := by simpa using data.β_bound (β, h) hp
  have hβsq : β ^ 2 ≤ data.βmax ^ 2 := by nlinarith [data.βmax_pos]
  have hale : a ≤ data.βmax ^ 2 := by
    dsimp [a]
    calc
      s * β ^ 2 ≤ 1 * β ^ 2 := mul_le_mul_of_nonneg_right hs1 (sq_nonneg β)
      _ ≤ data.βmax ^ 2 := by simpa using hβsq
  have haSq : a ^ 2 ≤ data.βmax ^ 4 := by
    have hmul := mul_self_le_mul_self ha.le hale
    nlinarith
  have hden : 0 < 14 * (1 + data.βmax ^ 4) := by positivity
  have hnearMul : (u - q) * (14 * (1 + data.βmax ^ 4)) ≤ data.gap := by
    apply (le_div_iff₀ hden).mp
    simpa [q] using hnear
  have hvNonneg : 0 ≤ v - q := sub_nonneg.mpr hv.1.le
  have huNonneg : 0 ≤ u - q := sub_nonneg.mpr huq.le
  have hvu : v - q ≤ u - q := by linarith [hv.2]
  have haSqMul : a ^ 2 * (v - q) ≤ data.βmax ^ 4 * (u - q) := by
    calc
      a ^ 2 * (v - q) ≤ data.βmax ^ 4 * (v - q) :=
        mul_le_mul_of_nonneg_right haSq hvNonneg
      _ ≤ data.βmax ^ 4 * (u - q) :=
        mul_le_mul_of_nonneg_left hvu (by positivity)
  have herror : 7 * a ^ 2 * (v - q) ≤ data.gap / 2 := by
    have hβfour : 0 ≤ data.βmax ^ 4 := by positivity
    have hC : 7 * data.βmax ^ 4 * (u - q) ≤
        7 * (1 + data.βmax ^ 4) * (u - q) := by
      nlinarith [huNonneg]
    have hfirst : 7 * a ^ 2 * (v - q) ≤
        7 * data.βmax ^ 4 * (u - q) := by nlinarith
    nlinarith [hnearMul]
  have hAT : atParameter β h ≤ 1 - data.gap := by
    simpa using data.strictAT (β, h) hp
  have hAT0 := property_atParameter_nonneg hβ hh
  have hsAT : s * atParameter β h ≤ 1 - data.gap := by
    have hsle := mul_le_mul_of_nonneg_right hs1 hAT0
    rw [one_mul] at hsle
    exact hsle.trans hAT
  have hderivBound : deriv f v ≤ 1 - data.gap / 2 := by
    rw [hvDeriv]
    have hendpoint : a * propertyUpperSech4Expectation β h q s q =
        s * atParameter β h := by
      dsimp [a, q]
      calc
        s * β ^ 2 * propertyUpperSech4Expectation β h (rsQ β h) s (rsQ β h) =
            s * (β ^ 2 * propertyUpperSech4Expectation β h
              (rsQ β h) s (rsQ β h)) := by ring
        _ = s * atParameter β h := by rw [hqcore]
    change a * propertyUpperSech4Expectation β h q s v ≤ 1 - data.gap / 2
    calc
      a * propertyUpperSech4Expectation β h q s v ≤
          a * (propertyUpperSech4Expectation β h q s q + 7 * a * (v - q)) :=
        mul_le_mul_of_nonneg_left hcoreUpper ha.le
      _ = a * propertyUpperSech4Expectation β h q s q +
          7 * a ^ 2 * (v - q) := by ring
      _ = s * atParameter β h + 7 * a ^ 2 * (v - q) := by rw [hendpoint]
      _ ≤ 1 - data.gap / 2 := by linarith
  have hratio : (f u - f q) / (u - q) ≤ 1 - data.gap / 2 := by
    rw [← hvSlope]
    exact hderivBound
  have hslope := (div_le_iff₀ (sub_pos.mpr huq)).mp hratio
  have hfq : f q = q := propertyUpperG_at_breakpoint hβ rfl
  dsimp [f, q] at hfq ⊢
  nlinarith

/-- The scalar order parameter crosses the diagonal exactly once, at the
replica-symmetric fixed point. -/
theorem scalarOrderParameterCorrect_sign {K : Set (ℝ × ℝ)}
    (data : UniformATData K) {β h s : ℝ}
    (hp : (β, h) ∈ K) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (∀ u ∈ Set.Ico (0 : ℝ) (rsQ β h),
      0 < scalarOrderParameterCorrect β h s u - u) ∧
    scalarOrderParameterCorrect β h s (rsQ β h) - rsQ β h = 0 ∧
    (∀ u ∈ Set.Ioc (rsQ β h) 1,
      scalarOrderParameterCorrect β h s u - u < 0) := by
  have hβ : 0 < β := by simpa using data.β_pos (β, h) hp
  have hh : 0 < h := by simpa using data.h_pos (β, h) hp
  have hAT : atParameter β h ≤ 1 - data.gap := by
    simpa using data.strictAT (β, h) hp
  have hATlt : atParameter β h < 1 := by linarith [data.gap_pos]
  constructor
  · intro u hu
    by_cases hsZero : s = 0
    · rw [hsZero, scalarOrderParameterCorrect_zero_path hβ hh]
      linarith [hu.2]
    · have hs0 : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hsZero)
      have hinc := propertyLowerG_increment_le_pathAT hβ hh hs0 hs.2 hu.1 hu.2
      have hleft := scalarOrderParameterCorrect_eq_propertyLowerG
        (h := h) hβ hs.1 hu.2.le
      have hq := propertyLowerG_at_breakpoint hβ hh hs.1 rfl
      have hnonneg := property_atParameter_nonneg hβ hh
      have hsAT : s * atParameter β h ≤ 1 - data.gap := by
        have hsle := mul_le_mul_of_nonneg_right hs.2 hnonneg
        rw [one_mul] at hsle
        exact hsle.trans hAT
      have hmul := mul_le_mul_of_nonneg_right hsAT (sub_nonneg.mpr hu.2.le)
      rw [hq] at hinc
      rw [hleft]
      nlinarith [mul_pos data.gap_pos (sub_pos.mpr hu.2)]
  · constructor
    · rw [scalarOrderParameterCorrect_at_rsQ hβ]
      ring
    · intro u hu
      by_cases hsZero : s = 0
      · rw [hsZero, scalarOrderParameterCorrect_zero_path hβ hh]
        linarith [hu.1]
      · have hs0 : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hsZero)
        have hupper := scalarOrderParameterCorrect_eq_propertyUpperG
          (h := h) hs.1 hu.1
        rw [hupper]
        by_cases hlarge : 1 < s * β ^ 2 * (1 - rsQ β h)
        · exact sub_neg.mpr
            (propertyUpperG_increment_lt_large hβ hh hs0 hs.2 hu.1 hu.2 hlarge hATlt)
        · exact sub_neg.mpr
            (propertyUpperG_lt_small hβ hh hs0 hu.1 (le_of_not_gt hlarge))

/-- Uniform linear separation from the diagonal near the replica-symmetric
fixed point. The constants depend only on `UniformATData K`. -/
theorem scalarOrderParameterCorrect_linear_separation {K : Set (ℝ × ℝ)}
    (data : UniformATData K) :
    ∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧
      ∀ {β h s u : ℝ}, (β, h) ∈ K → s ∈ Set.Icc (0 : ℝ) 1 →
        u ∈ Set.Icc (0 : ℝ) 1 →
        |u - rsQ β h| ≤ ε →
        c * |u - rsQ β h| ≤ |scalarOrderParameterCorrect β h s u - u| := by
  refine ⟨data.gap / 2,
    data.gap / (14 * (1 + data.βmax ^ 4)), by linarith [data.gap_pos],
    div_pos data.gap_pos (by positivity), ?_⟩
  intro β h s u hp hs hu hnear
  have hβ : 0 < β := by simpa using data.β_pos (β, h) hp
  have hh : 0 < h := by simpa using data.h_pos (β, h) hp
  have hAT : atParameter β h ≤ 1 - data.gap := by
    simpa using data.strictAT (β, h) hp
  have hAT0 := property_atParameter_nonneg hβ hh
  have hgap_le_one : data.gap ≤ 1 := by linarith
  have hc_le_one : data.gap / 2 ≤ 1 := by linarith
  by_cases hsZero : s = 0
  · rw [hsZero, scalarOrderParameterCorrect_zero_path hβ hh]
    have hmul := mul_le_mul_of_nonneg_right hc_le_one
      (abs_nonneg (u - rsQ β h))
    simpa [abs_sub_comm] using hmul
  have hs0 : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hsZero)
  by_cases huq : u < rsQ β h
  · have hinc := propertyLowerG_increment_le_pathAT hβ hh hs0 hs.2 hu.1 huq
    have hq := propertyLowerG_at_breakpoint hβ hh hs.1 rfl
    have hsAT : s * atParameter β h ≤ 1 - data.gap := by
      have hsle := mul_le_mul_of_nonneg_right hs.2 hAT0
      rw [one_mul] at hsle
      exact hsle.trans hAT
    have hmul := mul_le_mul_of_nonneg_right hsAT (sub_nonneg.mpr huq.le)
    rw [hq] at hinc
    have hlower : data.gap * (rsQ β h - u) ≤
        propertyLowerG β h (rsQ β h) s u - u := by
      nlinarith
    have hleft := scalarOrderParameterCorrect_eq_propertyLowerG
      (h := h) hβ hs.1 huq.le
    have hmap : data.gap * (rsQ β h - u) ≤
        scalarOrderParameterCorrect β h s u - u := by
      rw [hleft]
      exact hlower
    have hmap0 : 0 ≤ scalarOrderParameterCorrect β h s u - u := by
      have hpos := mul_pos data.gap_pos (sub_pos.mpr huq)
      linarith
    rw [abs_of_nonpos (sub_nonpos.mpr huq.le), abs_of_nonneg hmap0]
    nlinarith
  by_cases hqu : rsQ β h < u
  · have hnear' : u - rsQ β h ≤
        data.gap / (14 * (1 + data.βmax ^ 4)) := by
      rw [← abs_of_pos (sub_pos.mpr hqu)]
      exact hnear
    have hlocal := propertyUpperG_local_gap data hp hs0 hs.2 hqu hnear'
    have hupper := scalarOrderParameterCorrect_eq_propertyUpperG
      (h := h) hs.1 hqu
    have hmap : data.gap / 2 * (u - rsQ β h) ≤
        u - scalarOrderParameterCorrect β h s u := by
      rw [hupper]
      exact hlocal
    have hmap0 : scalarOrderParameterCorrect β h s u - u ≤ 0 := by
      have hpos := mul_pos (by linarith [data.gap_pos] : 0 < data.gap / 2)
        (sub_pos.mpr hqu)
      linarith
    rw [abs_of_pos (sub_pos.mpr hqu), abs_of_nonpos hmap0]
    linarith
  · have hueq : u = rsQ β h :=
      le_antisymm (le_of_not_gt hqu) (le_of_not_gt huq)
    subst u
    simp [scalarOrderParameterCorrect_at_rsQ hβ]


/-!
## Global separation of the scalar order parameter from the diagonal

`scalarOrderParameterCorrect_linear_separation` is a purely local statement.
The results below upgrade it to a *global* linear separation on the whole
overlap range `[0,1]`, with a constant depending only on `UniformATData K`.
-/

private lemma property_gap_le_one {K : Set (ℝ × ℝ)} (data : UniformATData K)
    {β h : ℝ} (hp : (β, h) ∈ K) : data.gap ≤ 1 := by
  have hβ : 0 < β := by simpa using data.β_pos (β, h) hp
  have hh : 0 < h := by simpa using data.h_pos (β, h) hp
  have hAT : atParameter β h ≤ 1 - data.gap := by
    simpa using data.strictAT (β, h) hp
  have h0 := property_atParameter_nonneg hβ hh
  linarith

/-- On the whole lower branch `0 ≤ u < q` the scalar order parameter is
separated from the diagonal linearly, with the uniform constant `gap`. -/
private lemma scalarOrderParameterCorrect_lower_global_gap {K : Set (ℝ × ℝ)}
    (data : UniformATData K) {β h s u : ℝ}
    (hp : (β, h) ∈ K) (hs : s ∈ Set.Icc (0 : ℝ) 1) (hu0 : 0 ≤ u)
    (huq : u < rsQ β h) :
    data.gap * (rsQ β h - u) ≤ scalarOrderParameterCorrect β h s u - u := by
  have hβ : 0 < β := by simpa using data.β_pos (β, h) hp
  have hh : 0 < h := by simpa using data.h_pos (β, h) hp
  have hAT : atParameter β h ≤ 1 - data.gap := by
    simpa using data.strictAT (β, h) hp
  have hAT0 := property_atParameter_nonneg hβ hh
  have hgap1 : data.gap ≤ 1 := property_gap_le_one data hp
  by_cases hsZero : s = 0
  · rw [hsZero, scalarOrderParameterCorrect_zero_path hβ hh]
    nlinarith [sub_pos.mpr huq]
  · have hs0 : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hsZero)
    have hinc := propertyLowerG_increment_le_pathAT hβ hh hs0 hs.2 hu0 huq
    have hq := propertyLowerG_at_breakpoint hβ hh hs.1 rfl
    have hsAT : s * atParameter β h ≤ 1 - data.gap := by
      have hsle := mul_le_mul_of_nonneg_right hs.2 hAT0
      rw [one_mul] at hsle
      exact hsle.trans hAT
    have hmul := mul_le_mul_of_nonneg_right hsAT (sub_nonneg.mpr huq.le)
    rw [hq] at hinc
    rw [scalarOrderParameterCorrect_eq_propertyLowerG (h := h) hβ hs.1 huq.le]
    nlinarith

/-- The exponentially reweighted defect used on the upper branch. -/
private noncomputable def propertyUpperExpo (β h s v : ℝ) : ℝ :=
  Real.exp (s * β ^ 2 * (v - rsQ β h)) *
    (propertyUpperG β h (rsQ β h) s v - v)

private lemma property_continuous_upperExpo (β h s : ℝ) :
    Continuous (propertyUpperExpo β h s) := by
  unfold propertyUpperExpo
  exact (Real.continuous_exp.comp (by fun_prop)).mul
    ((property_continuous_upperG β h (rsQ β h) s).sub continuous_id)

private lemma propertyUpperExpo_hasDerivAt {β h s v : ℝ}
    (hβ : 0 < β) (hs0 : 0 < s) (hv : rsQ β h < v) :
    HasDerivAt (propertyUpperExpo β h s)
      (Real.exp (s * β ^ 2 * (v - rsQ β h)) *
        (s * β ^ 2 * (propertyUpperG β h (rsQ β h) s v - v) +
          (s * β ^ 2 * propertyUpperSech4Expectation β h (rsQ β h) s v - 1))) v := by
  have hlin : HasDerivAt (fun y : ℝ => s * β ^ 2 * (y - rsQ β h)) (s * β ^ 2) v := by
    simpa using ((hasDerivAt_id v).sub_const (rsQ β h)).const_mul (s * β ^ 2)
  have hexp := hlin.exp
  have hg := propertyUpperG_hasDerivAt (h := h) hβ hs0 hv
  have hdiff : HasDerivAt (fun y : ℝ => propertyUpperG β h (rsQ β h) s y - y)
      (s * β ^ 2 * propertyUpperSech4Expectation β h (rsQ β h) s v - 1) v :=
    hg.sub (hasDerivAt_id v)
  unfold propertyUpperExpo
  exact (hexp.mul hdiff).congr_deriv (by ring)

private lemma propertyUpperExpo_deriv_le {β h s v : ℝ}
    (hβ : 0 < β) (hs0 : 0 < s) (hv : rsQ β h < v) :
    deriv (propertyUpperExpo β h s) v ≤
      Real.exp (s * β ^ 2 * (v - rsQ β h)) * (s * β ^ 2 * (1 - v) - 1) := by
  rw [(propertyUpperExpo_hasDerivAt hβ hs0 hv).deriv]
  have hE4 := propertyUpperSech4Expectation_le_one_sub_upperG (β := β) (h := h)
    (q := rsQ β h) (s := s) hs0.le hv.le
  have ha : 0 < s * β ^ 2 := mul_pos hs0 (pow_pos hβ 2)
  have hbr : s * β ^ 2 * (propertyUpperG β h (rsQ β h) s v - v) +
      (s * β ^ 2 * propertyUpperSech4Expectation β h (rsQ β h) s v - 1) ≤
      s * β ^ 2 * (1 - v) - 1 := by nlinarith
  exact mul_le_mul_of_nonneg_left hbr (Real.exp_pos _).le

/-- In the subcritical regime `s β² (1-q) ≤ 1` the reweighted defect has a
derivative bounded by the linear expression `s β² (1-v) - 1 ≤ 0`. -/
private lemma propertyUpperExpo_deriv_le_linear {β h s v : ℝ}
    (hβ : 0 < β) (hs0 : 0 < s) (hv : rsQ β h < v)
    (hsmall : s * β ^ 2 * (1 - rsQ β h) ≤ 1) :
    deriv (propertyUpperExpo β h s) v ≤ s * β ^ 2 * (1 - v) - 1 := by
  have ha : 0 < s * β ^ 2 := mul_pos hs0 (pow_pos hβ 2)
  have hx : 0 ≤ s * β ^ 2 * (v - rsQ β h) :=
    mul_nonneg ha.le (by linarith)
  have hexp1 : 1 ≤ Real.exp (s * β ^ 2 * (v - rsQ β h)) := Real.one_le_exp hx
  have hneg : s * β ^ 2 * (1 - v) - 1 ≤ 0 := by nlinarith
  have hmain := propertyUpperExpo_deriv_le hβ hs0 hv
  nlinarith

/-- Subcritical upper branch: a quadratic separation from the diagonal,
valid on the whole range `q < u ≤ 1`. -/
private lemma propertyUpperG_global_gap_small {β h s u : ℝ}
    (hβ : 0 < β) (hh : 0 < h) (hs0 : 0 < s)
    (huq : rsQ β h < u) (hu1 : u ≤ 1)
    (hsmall : s * β ^ 2 * (1 - rsQ β h) ≤ 1) :
    (u - rsQ β h) ^ 2 / 24 ≤ u - propertyUpperG β h (rsQ β h) s u := by
  have hq0 : 0 < rsQ β h := rsQ_pos hβ hh
  have hq1 : rsQ β h < 1 := rsQ_lt_one hβ hh
  have ha : 0 < s * β ^ 2 := mul_pos hs0 (pow_pos hβ 2)
  have hFq : propertyUpperExpo β h s (rsQ β h) = 0 := by
    unfold propertyUpperExpo
    rw [propertyUpperG_at_breakpoint hβ rfl]
    simp
  have hcont : ∀ a b : ℝ, ContinuousOn (propertyUpperExpo β h s) (Set.Icc a b) :=
    fun a b => (property_continuous_upperExpo β h s).continuousOn
  have hdiffon : ∀ a b : ℝ, rsQ β h ≤ a →
      DifferentiableOn ℝ (propertyUpperExpo β h s) (Set.Ioo a b) := by
    intro a b hab v hv
    exact (propertyUpperExpo_hasDerivAt hβ hs0
      (lt_of_le_of_lt hab hv.1)).differentiableAt.differentiableWithinAt
  have hkey : propertyUpperExpo β h s u ≤ -((u - rsQ β h) ^ 2 / 8) := by
    by_cases hcase : s * β ^ 2 ≤ 1 / 2
    · obtain ⟨ξ, hξ, hslope⟩ := exists_deriv_eq_slope (propertyUpperExpo β h s)
        huq (hcont _ _) (hdiffon _ _ le_rfl)
      have hbound := propertyUpperExpo_deriv_le_linear hβ hs0 hξ.1 hsmall
      rw [hslope, hFq] at hbound
      have hden : 0 < u - rsQ β h := sub_pos.mpr huq
      have hmul := (div_le_iff₀ hden).mp
        (by simpa using hbound.trans (by nlinarith [hξ.1, hξ.2] :
          s * β ^ 2 * (1 - ξ) - 1 ≤ -(1 / 2 : ℝ)))
      nlinarith
    · have hcase' : (1 : ℝ) / 2 < s * β ^ 2 := lt_of_not_ge hcase
      set m : ℝ := (rsQ β h + u) / 2 with hm
      have hqm : rsQ β h < m := by rw [hm]; linarith
      have hmu : m < u := by rw [hm]; linarith
      have hFm : propertyUpperExpo β h s m ≤ 0 := by
        obtain ⟨ξ, hξ, hslope⟩ := exists_deriv_eq_slope (propertyUpperExpo β h s)
          hqm (hcont _ _) (hdiffon _ _ le_rfl)
        have hbound := propertyUpperExpo_deriv_le_linear hβ hs0 hξ.1 hsmall
        rw [hslope, hFq] at hbound
        have hden : 0 < m - rsQ β h := sub_pos.mpr hqm
        have hneg : s * β ^ 2 * (1 - ξ) - 1 ≤ 0 := by
          nlinarith [hξ.1, hξ.2, hmu, hu1]
        have := (div_le_iff₀ hden).mp (hbound.trans hneg)
        nlinarith
      obtain ⟨ξ, hξ, hslope⟩ := exists_deriv_eq_slope (propertyUpperExpo β h s)
        hmu (hcont _ _) (hdiffon _ _ hqm.le)
      have hbound := propertyUpperExpo_deriv_le_linear hβ hs0
        (lt_trans hqm hξ.1) hsmall
      rw [hslope] at hbound
      have hden : 0 < u - m := sub_pos.mpr hmu
      have hstep : s * β ^ 2 * (1 - ξ) - 1 ≤ -(u - rsQ β h) / 4 := by
        have h1 : s * β ^ 2 * (ξ - rsQ β h) ≥ s * β ^ 2 * (m - rsQ β h) := by
          apply mul_le_mul_of_nonneg_left _ ha.le
          linarith [hξ.1]
        have h2 : s * β ^ 2 * (m - rsQ β h) = s * β ^ 2 * ((u - rsQ β h) / 2) := by
          rw [hm]; ring
        nlinarith
      have := (div_le_iff₀ hden).mp (hbound.trans hstep)
      have hmq : u - m = (u - rsQ β h) / 2 := by rw [hm]; ring
      nlinarith
  have hEle : Real.exp (s * β ^ 2 * (u - rsQ β h)) ≤ 3 := by
    have hx : s * β ^ 2 * (u - rsQ β h) ≤ 1 := by nlinarith
    calc Real.exp (s * β ^ 2 * (u - rsQ β h)) ≤ Real.exp 1 :=
          Real.exp_le_exp.mpr hx
      _ ≤ 3 := by
          exact Real.exp_one_lt_three.le
  have hEpos : 0 < Real.exp (s * β ^ 2 * (u - rsQ β h)) := Real.exp_pos _
  have hEone : 1 ≤ Real.exp (s * β ^ 2 * (u - rsQ β h)) :=
    Real.one_le_exp (mul_nonneg ha.le (by linarith))
  unfold propertyUpperExpo at hkey
  nlinarith [sq_nonneg (u - rsQ β h)]

/-- Supercritical upper branch: a linear separation with constant `gap`. -/
private lemma propertyUpperG_global_gap_large {K : Set (ℝ × ℝ)}
    (data : UniformATData K) {β h s u : ℝ}
    (hp : (β, h) ∈ K) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (huq : rsQ β h < u) (hu1 : u ≤ 1)
    (hlarge : 1 < s * β ^ 2 * (1 - rsQ β h)) :
    data.gap * (u - rsQ β h) ≤ u - propertyUpperG β h (rsQ β h) s u := by
  have hβ : 0 < β := by simpa using data.β_pos (β, h) hp
  have hh : 0 < h := by simpa using data.h_pos (β, h) hp
  have hAT : atParameter β h ≤ 1 - data.gap := by
    simpa using data.strictAT (β, h) hp
  have hAT0 := property_atParameter_nonneg hβ hh
  have hcont : ContinuousOn (propertyUpperG β h (rsQ β h) s)
      (Set.Icc (rsQ β h) u) :=
    (property_continuous_upperG β h (rsQ β h) s).continuousOn
  have hdiff : DifferentiableOn ℝ (propertyUpperG β h (rsQ β h) s)
      (Set.Ioo (rsQ β h) u) := by
    intro v hv
    exact (propertyUpperG_hasDerivAt hβ hs0 hv.1).differentiableAt.differentiableWithinAt
  obtain ⟨ξ, hξ, hslope⟩ := exists_deriv_eq_slope (propertyUpperG β h (rsQ β h) s)
    huq hcont hdiff
  have hvDeriv := (propertyUpperG_hasDerivAt (h := h) hβ hs0 hξ.1).deriv
  have hvBound := propertyUpperG_derivative_le_pathAT_large hβ hh hs0 hs1 hξ.1
    (le_trans hξ.2.le hu1) hlarge
  have hsAT : s * atParameter β h ≤ 1 - data.gap := by
    have hsle := mul_le_mul_of_nonneg_right hs1 hAT0
    rw [one_mul] at hsle
    exact hsle.trans hAT
  have hratio : (propertyUpperG β h (rsQ β h) s u -
      propertyUpperG β h (rsQ β h) s (rsQ β h)) / (u - rsQ β h) ≤ 1 - data.gap := by
    rw [← hslope, hvDeriv]
    exact hvBound.trans hsAT
  have hden : 0 < u - rsQ β h := sub_pos.mpr huq
  have hmul := (div_le_iff₀ hden).mp hratio
  rw [propertyUpperG_at_breakpoint hβ rfl] at hmul
  linarith

/-- Upper branch, uniform quadratic separation on `q < u ≤ 1`. -/
private lemma scalarOrderParameterCorrect_upper_global_gap {K : Set (ℝ × ℝ)}
    (data : UniformATData K) {β h s u : ℝ}
    (hp : (β, h) ∈ K) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (huq : rsQ β h < u) (hu1 : u ≤ 1) :
    min data.gap (1 / 24) * (u - rsQ β h) ^ 2 ≤
      u - scalarOrderParameterCorrect β h s u := by
  have hβ : 0 < β := by simpa using data.β_pos (β, h) hp
  have hh : 0 < h := by simpa using data.h_pos (β, h) hp
  have hq0 : 0 < rsQ β h := rsQ_pos hβ hh
  have hgap1 : data.gap ≤ 1 := property_gap_le_one data hp
  have hmin1 : min data.gap (1 / 24) ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
  have hmin0 : 0 < min data.gap (1 / 24) := lt_min data.gap_pos (by norm_num)
  have hsq : (u - rsQ β h) ^ 2 ≤ u - rsQ β h := by nlinarith
  by_cases hsZero : s = 0
  · rw [hsZero, scalarOrderParameterCorrect_zero_path hβ hh]
    nlinarith
  · have hs0 : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hsZero)
    rw [scalarOrderParameterCorrect_eq_propertyUpperG (h := h) hs.1 huq]
    by_cases hlarge : 1 < s * β ^ 2 * (1 - rsQ β h)
    · have := propertyUpperG_global_gap_large data hp hs0 hs.2 huq hu1 hlarge
      nlinarith [min_le_left data.gap (1 / 24 : ℝ)]
    · have := propertyUpperG_global_gap_small hβ hh hs0 huq hu1
        (le_of_not_gt hlarge)
      nlinarith [min_le_right data.gap (1 / 24 : ℝ), sq_nonneg (u - rsQ β h)]

/-- Global linear separation of the scalar order parameter from the diagonal
on the whole overlap range `[0,1]`, with a constant depending only on
`UniformATData K`. -/
theorem scalarOrderParameterCorrect_global_separation {K : Set (ℝ × ℝ)}
    (data : UniformATData K) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {β h s u : ℝ}, (β, h) ∈ K → s ∈ Set.Icc (0 : ℝ) 1 →
        u ∈ Set.Icc (0 : ℝ) 1 →
        c * |u - rsQ β h| ≤ |scalarOrderParameterCorrect β h s u - u| := by
  obtain ⟨c₁, ε, hc₁, hε, hloc⟩ := scalarOrderParameterCorrect_linear_separation data
  refine ⟨min c₁ (min (min data.gap (1 / 24) * ε) data.gap), ?_, ?_⟩
  · exact lt_min hc₁ (lt_min (mul_pos (lt_min data.gap_pos (by norm_num)) hε)
      data.gap_pos)
  · intro β h s u hp hs hu
    by_cases hnear : |u - rsQ β h| ≤ ε
    · refine le_trans ?_ (hloc hp hs hu hnear)
      exact mul_le_mul_of_nonneg_right (min_le_left _ _) (abs_nonneg _)
    · have hfar : ε < |u - rsQ β h| := lt_of_not_ge hnear
      rcases lt_trichotomy u (rsQ β h) with hlt | heq | hgt
      · have hlow := scalarOrderParameterCorrect_lower_global_gap data hp hs hu.1 hlt
        have hpos : 0 < rsQ β h - u := sub_pos.mpr hlt
        rw [abs_of_nonpos (by linarith : u - rsQ β h ≤ 0),
          abs_of_nonneg (by nlinarith [data.gap_pos] :
            0 ≤ scalarOrderParameterCorrect β h s u - u)]
        have hle : min c₁ (min (min data.gap (1 / 24) * ε) data.gap) ≤ data.gap :=
          le_trans (min_le_right _ _) (min_le_right _ _)
        nlinarith
      · rw [heq]
        simp
      · have hup := scalarOrderParameterCorrect_upper_global_gap data hp hs hgt hu.2
        have hpos : 0 < u - rsQ β h := sub_pos.mpr hgt
        have hεlt : ε < u - rsQ β h := by
          rwa [abs_of_pos hpos] at hfar
        have hmin0 : 0 < min data.gap (1 / 24) :=
          lt_min data.gap_pos (by norm_num)
        have hnonpos : scalarOrderParameterCorrect β h s u - u ≤ 0 := by
          nlinarith
        rw [abs_of_nonneg hpos.le, abs_of_nonpos hnonpos]
        have hle : min c₁ (min (min data.gap (1 / 24) * ε) data.gap) ≤
            min data.gap (1 / 24) * ε :=
          le_trans (min_le_right _ _) (min_le_left _ _)
        nlinarith


end SpinGlass.AT
