module

/-
Fix $(\beta,h,s)\in\cK\times[0,1]$.
For $t\ge0$, let $\mathsf H_t$ be the heat semigroup, namely
\[
 (\mathsf H_t\varphi)(x)
 \coloneqq
 \E\varphi(x+\sqrt t\,Z),
 \qquad Z\sim N(0,1).
\]
For instance, if $\varphi\in C_b^2(\R)$ and $t>0$, then
\[
 \begin{aligned}
 \partial_t(\mathsf H_t\varphi)(x)
 &=
 \partial_t\int_{\R}
 \varphi(x+\sqrt t\,z)\phi(z)\,dz\\
 &=
 \frac{1}{2\sqrt t}
 \int_{\R}
 z\,\varphi'(x+\sqrt t\,z)\phi(z)\,dz.
 \end{aligned}
\]
Since $\phi'(z)=-z\phi(z)$, integration by parts in $z$ gives
\[
 \begin{aligned}
 \int_{\R}
 z\,\varphi'(x+\sqrt t\,z)\phi(z)\,dz
 &=
 -\int_{\R}
 \varphi'(x+\sqrt t\,z)\phi'(z)\,dz\\
 &=
 \sqrt t
 \int_{\R}
 \varphi''(x+\sqrt t\,z)\phi(z)\,dz.
 \end{aligned}
\]
Consequently,
\begin{equation}\label{eq:genH}
 \partial_t(\mathsf H_t\varphi)(x)
 =
 \frac12\mathsf H_t(\partial^2\varphi)(x).
\end{equation}

For the upper interval, introduce the tilted heat semigroup
\begin{equation}
 (\mathsf T_t\varphi)(x)
 \coloneqq
 e^{-t/2}
 \frac{\bigl(\mathsf H_t(\varphi\cosh)\bigr)(x)}
 {\cosh x}.
 \label{eq:tiltedsemigroup}
\end{equation}
We record explicitly its generator. Put
\[
 g_t(x)\coloneqq(\mathsf T_t\varphi)(x).
\]
Then
\[
 \mathsf H_t(\varphi\cosh)(x)
 =
 e^{t/2}\cosh(x)g_t(x).
\]
Using \eqref{eq:genH},
\[
 \begin{aligned}
 \partial_tg_t(x)
 &=
 -\frac12g_t(x)
 +
 \frac{e^{-t/2}}{2\cosh x}
 \partial_{xx}
 \mathsf H_t(\varphi\cosh)(x)\\
 &=
 -\frac12g_t(x)
 +
 \frac{1}{2\cosh x}
 \partial_{xx}\bigl(\cosh(x)g_t(x)\bigr).
 \end{aligned}
\]
Since
\[
 \begin{aligned}
 \partial_{xx}\bigl(\cosh(x)g_t(x)\bigr)
 &=
 \partial_x\bigl(
   \sinh(x)g_t(x)+\cosh(x)g_t'(x)
 \bigr)\\
 &=
 \cosh(x)g_t(x)
 +2\sinh(x)g_t'(x)
 +\cosh(x)g_t''(x),
 \end{aligned}
\]
we obtain
\[
 \partial_tg_t(x)
 =
 \frac12g_t''(x)+\tanh(x)g_t'(x).
\]
Thus the generator of $\mathsf T_t$ is
\[
 \frac12\partial_{xx}+\tanh(x)\partial_x.
\]
Equivalently,
\begin{equation}\label{eq:partialT_t}
 \partial_t(\mathsf T_t\varphi)(x)
 =
 \frac{1}{2\cosh^2x}
 \partial_x\left(
   \cosh^2x\,
   \partial_x(\mathsf T_t\varphi)(x)
 \right),
\end{equation}
because
\[
 \begin{aligned}
 \frac{1}{2\cosh^2x}
 \partial_x\left(\cosh^2x\,g_t'(x)\right)
 &=
 \frac{1}{2\cosh^2x}
 \left(
  2\cosh x\sinh x\,g_t'(x)
  +\cosh^2x\,g_t''(x)
 \right)\\
 &=
 \tanh x\,g_t'(x)+\frac12g_t''(x).
 \end{aligned}
\]

For each $u\in[0,1]$, let $X_{s,u}$ denote a random variable whose
law is specified by
\begin{equation}
 \E\varphi(X_{s,u})
 \coloneqq
 \begin{cases}
  \bigl(\mathsf H_{\beta^2(1-s)q+s\beta^2u}\varphi\bigr)(h),
      &0\le u\le q,\\[1mm]
  \bigl(\mathsf H_{\beta^2q}
      (\mathsf T_{s\beta^2(u-q)}\varphi)\bigr)(h),
      &q\le u\le1.
 \end{cases}
 \label{eq:localfieldlaw}
\end{equation}
At $u=q$, both expressions reduce to
\[
 \bigl(\mathsf H_{\beta^2q}\varphi\bigr)(h)
 =
 \E\varphi(h+\beta\sqrt q\,Z),
\]
and hence
\begin{equation}\label{eq:Xsq}
 X_{s,q}\stackrel{\mathrm d}=h+\beta\sqrt q\,Z.
\end{equation}

\begin{lemma}
\label{lem:uppercomparison}
If $s\beta^2(1-q)>1$, then
\begin{equation}
 \beta^2\E\sech^4(X_{s,u})\le\alpha,
 \qquad q\le u\le1.
 \label{eq:uppercomparison}
\end{equation}
\end{lemma}

\begin{proof}
Fix $u\in[q,1]$, and set
\[
 \sigma^2\coloneqq\beta^2q,
 \qquad
 \tau\coloneqq s\beta^2(u-q),
 \qquad
 X\coloneqq h+\sigma Z.
\]
Then $X\sim N(h,\sigma^2)$.

We first dispose of the case $q=0$. In that case the defining equation
for $q$ gives
\[
 1
 =
 \sech^2(h),
\]
and therefore $h=0$. Moreover,
\[
 \mathsf H_t(\cosh)(x)
 =
 \E\cosh(x+\sqrt t\,Z).
\]
Using
\[
 \cosh(x+y)
 =
 \cosh x\cosh y+\sinh x\sinh y,
\]
together with
\[
 \E\sinh(\sqrt t\,Z)=0,
 \qquad
 \E\cosh(\sqrt t\,Z)
 =
 \frac12\left(\E e^{\sqrt t Z}+\E e^{-\sqrt t Z}\right)
 =
 e^{t/2},
\]
we obtain
\[
 \mathsf H_t(\cosh)(x)=e^{t/2}\cosh x.
\]
Hence
\[
 \mathsf T_t1=1.
\]
Since $\mathsf T_t$ is positivity preserving and $0\le\sech^4\le1$,
\[
 0\le\mathsf T_t(\sech^4)\le1.
\]
Thus the desired comparison is immediate when $q=0$.

We may therefore assume $q>0$, so that $\sigma>0$.

By \eqref{eq:localfieldlaw},
\[
 \begin{aligned}
 \E\sech^4(X_{s,u})
 &=
 \bigl(
 \mathsf H_{\beta^2q}
   (\mathsf T_\tau\sech^4)
 \bigr)(h)\\
 &=
 \E\bigl[
   (\mathsf T_\tau\sech^4)(h+\sigma Z)
 \bigr]\\
 &=
 \E\bigl[
   (\mathsf T_\tau\sech^4)(X)
 \bigr].
 \end{aligned}
\]
Thus it is enough to prove
\begin{equation}\label{eq:upper-M-comparison}
 \E\bigl[
   (\mathsf T_\tau\sech^4)(X)
 \bigr]
 \le
 \E\sech^4(X).
\end{equation}

We next prove
\begin{equation}
 |h|<\sigma^2.
 \label{eq:h-less-sigma}
\end{equation}
Let
\[
 F(a)
 \coloneqq
 \E\sech^2(a+\sigma Z).
\]
The function $F$ is even. We also verify directly that it is
nonincreasing on $[0,\infty)$. Let
\[
 \rho_\sigma(x)
 \coloneqq
 \frac{1}{\sqrt{2\pi\sigma^2}}
 e^{-x^2/(2\sigma^2)}
\]
be the density of $N(0,\sigma^2)$ and put $f_2(x)=\sech^2x$. Then
\[
 F(a)
 =
 \int_{\R}f_2(y)\rho_\sigma(a-y)\,dy.
\]
Differentiating the convolution in the $f_2$ variable gives
\[
 F'(a)
 =
 \int_{\R}f_2'(y)\rho_\sigma(a-y)\,dy.
\]
Since $f_2$ is even, $f_2'$ is odd. Pairing $y$ and $-y$ therefore yields,
for $a\ge0$,
\[
 F'(a)
 =
 \int_0^\infty
 f_2'(y)
 \left[
   \rho_\sigma(a-y)-\rho_\sigma(a+y)
 \right]\,dy.
\]
For $a,y\ge0$,
\[
 |a-y|\le a+y,
\]
and hence, since $\rho_\sigma$ is decreasing as a function of $|x|$,
\[
 \rho_\sigma(a-y)\ge\rho_\sigma(a+y).
\]
On the other hand,
\[
 f_2'(y)
 =
 -2\sech^2(y)\tanh(y)\le0,
 \qquad y\ge0.
\]
Consequently,
\[
 F'(a)\le0,
 \qquad a\ge0.
\]

Suppose now, toward a contradiction, that $|h|\ge\sigma^2$. Since $F$
is even and nonincreasing on $[0,\infty)$,
\[
 \begin{aligned}
 1-q
 &=
 \E\sech^2(h+\sigma Z)\\
 &=
 F(|h|)\\
 &\le
 F(\sigma^2)\\
 &=
 \E\sech^2(\sigma^2+\sigma Z).
 \end{aligned}
\]
We estimate the final expectation.

Let $\varepsilon$ be a symmetric Rademacher random variable independent
of $Z$, and define
\[
 Y\coloneqq\sigma^2\varepsilon+\sigma Z.
\]
Conditional on $\varepsilon=\pm1$, the variable $Y$ has density
\[
 y\longmapsto
 \frac{1}{\sqrt{2\pi\sigma^2}}
 \exp\left(
  -\frac{(y\mp\sigma^2)^2}{2\sigma^2}
 \right).
\]
Therefore Bayes' formula gives
\[
 \frac{\P(\varepsilon=1\mid Y=y)}
 {\P(\varepsilon=-1\mid Y=y)}
 =
 \exp\left(
 -\frac{(y-\sigma^2)^2-(y+\sigma^2)^2}
 {2\sigma^2}
 \right).
\]
Since
\[
 (y-\sigma^2)^2-(y+\sigma^2)^2
 =
 -4y\sigma^2,
\]
the ratio is $e^{2y}$. Hence
\[
 \P(\varepsilon=1\mid Y=y)
 =
 \frac{e^{2y}}{1+e^{2y}},
 \qquad
 \P(\varepsilon=-1\mid Y=y)
 =
 \frac{1}{1+e^{2y}},
\]
and therefore
\[
 \E[\varepsilon\mid Y=y]
 =
 \frac{e^{2y}-1}{e^{2y}+1}
 =
 \tanh y.
\]
It follows that
\[
 \Var(\varepsilon\mid Y)
 =
 1-\bigl(\E[\varepsilon\mid Y]\bigr)^2
 =
 1-\tanh^2Y
 =
 \sech^2Y.
\]
Moreover, since $\sech^2$ is even and $Z\stackrel{\mathrm d}=-Z$,
\[
 \begin{aligned}
 \E\sech^2Y
 &=
 \frac12\E\sech^2(\sigma^2+\sigma Z)
 +
 \frac12\E\sech^2(-\sigma^2+\sigma Z)\\
 &=
 \E\sech^2(\sigma^2+\sigma Z).
 \end{aligned}
\]
Thus
\[
 \E\sech^2(\sigma^2+\sigma Z)
 =
 \E\Var(\varepsilon\mid Y).
\]

Since $\E[\varepsilon\mid Y]$ is the $L^2$-optimal estimator of
$\varepsilon$ among all measurable functions of $Y$,
\[
 \E\Var(\varepsilon\mid Y)
 =
 \E\bigl[
   (\varepsilon-\E[\varepsilon\mid Y])^2
 \bigr]
 \le
 \inf_{a\in\R}\E(\varepsilon-aY)^2.
\]
We compute this last infimum explicitly. Since
\[
 Y=\sigma^2\varepsilon+\sigma Z,
\]
independence and centering give
\[
 \E[\varepsilon Y]
 =
 \sigma^2
\]
and
\[
 \begin{aligned}
 \E Y^2
 &=
 \E(\sigma^2\varepsilon+\sigma Z)^2\\
 &=
 \sigma^4\E\varepsilon^2
 +2\sigma^3\E[\varepsilon Z]
 +\sigma^2\E Z^2\\
 &=
 \sigma^4+\sigma^2\\
 &=
 \sigma^2(1+\sigma^2).
 \end{aligned}
\]
Therefore
\[
 \begin{aligned}
 \E(\varepsilon-aY)^2
 &=
 \E\varepsilon^2
 -2a\E[\varepsilon Y]
 +a^2\E Y^2\\
 &=
 1-2a\sigma^2
 +a^2\sigma^2(1+\sigma^2).
 \end{aligned}
\]
The minimizing coefficient is
\[
 a_\star
 =
 \frac{\sigma^2}{\sigma^2(1+\sigma^2)}
 =
 \frac{1}{1+\sigma^2},
\]
and substitution gives
\[
 \begin{aligned}
 \inf_{a\in\R}\E(\varepsilon-aY)^2
 &=
 1-\frac{2\sigma^2}{1+\sigma^2}
 +\frac{\sigma^2}{1+\sigma^2}\\
 &=
 \frac{1}{1+\sigma^2}.
 \end{aligned}
\]
Consequently,
\[
 \E\sech^2(\sigma^2+\sigma Z)
 \le
 \frac{1}{1+\sigma^2}.
\]
Recalling $\sigma^2=\beta^2q$, we obtain
\[
 1-q
 \le
 \frac{1}{1+\beta^2q},
\]
or equivalently
\[
 (1-q)(1+\beta^2q)\le1.
\]
Expanding the left-hand side gives
\[
 1-q+\beta^2q(1-q)\le1,
\]
hence
\[
 q\bigl(\beta^2(1-q)-1\bigr)\le0.
\]
Since $q>0$,
\[
 \beta^2(1-q)\le1.
\]
As $s\le1$, this implies
\[
 s\beta^2(1-q)\le1,
\]
contradicting the assumption
\[
 s\beta^2(1-q)>1.
\]
This proves \eqref{eq:h-less-sigma}.

We now study the tilted semigroup. Set
\[
 f\coloneqq\sech^4,
 \qquad
 g_r\coloneqq\mathsf T_r f,
 \qquad
 M(r)\coloneqq\E g_r(X),
 \qquad 0\le r\le\tau.
\]
By \eqref{eq:tiltedsemigroup},
\[
 \begin{aligned}
 g_r(x)
 &=
 e^{-r/2}
 \frac{\mathsf H_r(f\cosh)(x)}
 {\cosh x}\\
 &=
 e^{-r/2}
 \frac{\mathsf H_r(\sech^3)(x)}
 {\cosh x}.
 \end{aligned}
\]
Let
\[
 a_r(x)\coloneqq\mathsf H_r(\sech^3)(x).
\]
Since $\sech^3$ is even and nonincreasing on $[0,\infty)$, and the
centered Gaussian density is even and nonincreasing on $[0,\infty)$,
the same convolution argument used above shows that $a_r$ is even and
nonincreasing on $[0,\infty)$. Thus
\[
 a_r'(x)\le0,
 \qquad x>0.
\]
Since
\[
 g_r(x)=e^{-r/2}a_r(x)\sech x,
\]
we can also differentiate directly:
\[
 \begin{aligned}
 g_r'(x)
 &=
 e^{-r/2}
 \left(
  a_r'(x)\sech x
  -
  a_r(x)\sech x\tanh x
 \right).
 \end{aligned}
\]
For $x>0$,
\[
 a_r'(x)\le0,
 \qquad
 a_r(x)\ge0,
 \qquad
 \sech x>0,
 \qquad
 \tanh x>0,
\]
so
\begin{equation}\label{eq:gt-decreasing}
 g_r'(x)\le0,
 \qquad x>0.
\end{equation}
Also $g_r$ is even, and therefore $g_r'$ is odd.

Let
\[
 p(x)
 \coloneqq
 \frac1\sigma
 \phi\left(\frac{x-h}{\sigma}\right)
\]
be the density of $X\sim N(h,\sigma^2)$. From
\eqref{eq:partialT_t},
\[
 \begin{aligned}
 M'(r)
 &=
 \int_{\R}
 \partial_rg_r(x)p(x)\,dx\\
 &=
 \frac12
 \int_{\R}
 \frac{1}{\cosh^2x}
 \partial_x\bigl(\cosh^2x\,g_r'(x)\bigr)
 p(x)\,dx\\
 &=
 \frac12
 \int_{\R}
 \partial_x\bigl(\cosh^2x\,g_r'(x)\bigr)
 \frac{p(x)}{\cosh^2x}\,dx.
 \end{aligned}
\]
The Gaussian decay makes the boundary term vanish, so integration by
parts gives
\[
 M'(r)
 =
 -\frac12
 \int_{\R}
 \cosh^2x\,g_r'(x)
 \partial_x\left(
  \frac{p(x)}{\cosh^2x}
 \right)\,dx.
\]
Now
\[
 p'(x)
 =
 -\frac{x-h}{\sigma^2}p(x),
\]
whereas
\[
 \partial_x(\cosh^{-2}x)
 =
 -2\tanh x\,\cosh^{-2}x.
\]
Therefore
\[
 \begin{aligned}
 \partial_x\left(
   \frac{p(x)}{\cosh^2x}
 \right)
 &=
 \frac{p'(x)}{\cosh^2x}
 -
 \frac{2\tanh x\,p(x)}{\cosh^2x}\\
 &=
 -\left(
   \frac{x-h}{\sigma^2}+2\tanh x
 \right)
 \frac{p(x)}{\cosh^2x}.
 \end{aligned}
\]
Substituting this identity into the previous display yields
\[
 \begin{aligned}
 M'(r)
 &=
 \frac12
 \int_{\R}
 g_r'(x)
 \left(
   \frac{x-h}{\sigma^2}+2\tanh x
 \right)
 p(x)\,dx\\
 &=
 \E\left[
  \left(
    \tanh X+\frac{X-h}{2\sigma^2}
  \right)
  g_r'(X)
 \right].
 \end{aligned}
\]

We now pair the contributions from $x$ and $-x$. Since $g_r'$ is odd,
\[
 M'(r)
 =
 \int_0^\infty g_r'(x)K(x)\,dx,
 \tag{\ref{eq:Mprime-detail}}\label{eq:Mprime-detail}
\]
where
\[
 \begin{aligned}
 K(x)
 &\coloneqq
 \frac1\sigma
 \phi\left(\frac{x-h}{\sigma}\right)
 \left(
   \tanh x+\frac{x-h}{2\sigma^2}
 \right)\\
 &\quad+
 \frac1\sigma
 \phi\left(\frac{-x-h}{\sigma}\right)
 \left(
   \tanh x+\frac{x+h}{2\sigma^2}
 \right).
 \end{aligned}
\]
Indeed, the contribution from the negative half-line is
\[
 \begin{aligned}
 &\int_{-\infty}^0
 g_r'(x)
 \left(
   \tanh x+\frac{x-h}{2\sigma^2}
 \right)p(x)\,dx\\
 &\qquad=
 \int_0^\infty
 g_r'(-x)
 \left(
  \tanh(-x)+\frac{-x-h}{2\sigma^2}
 \right)p(-x)\,dx\\
 &\qquad=
 \int_0^\infty
 g_r'(x)
 \left(
   \tanh x+\frac{x+h}{2\sigma^2}
 \right)p(-x)\,dx.
 \end{aligned}
\]

It remains to determine the sign of $K(x)$. Write
\[
 A
 \coloneqq
 \phi\left(\frac{x-h}{\sigma}\right),
 \qquad
 B
 \coloneqq
 \phi\left(\frac{-x-h}{\sigma}\right).
\]
Then
\[
 \begin{aligned}
 \sigma K(x)
 &=
 A\left(
   \tanh x+\frac{x}{2\sigma^2}
   -\frac{h}{2\sigma^2}
 \right)\\
 &\quad+
 B\left(
   \tanh x+\frac{x}{2\sigma^2}
   +\frac{h}{2\sigma^2}
 \right)\\
 &=
 (A+B)
 \left(
   \tanh x+\frac{x}{2\sigma^2}
 \right)
 +
 \frac{h}{2\sigma^2}(B-A).
 \end{aligned}
\]
Furthermore,
\[
 \begin{aligned}
 \frac BA
 &=
 \exp\left(
  -\frac{(-x-h)^2-(x-h)^2}{2\sigma^2}
 \right)\\
 &=
 \exp\left(-\frac{2hx}{\sigma^2}\right).
 \end{aligned}
\]
Hence
\[
 \begin{aligned}
 \frac{B-A}{A+B}
 &=
 \frac{e^{-2hx/\sigma^2}-1}
 {e^{-2hx/\sigma^2}+1}\\
 &=
 -\tanh\left(\frac{hx}{\sigma^2}\right).
 \end{aligned}
\]
Consequently,
\begin{equation}\label{eq:Kidentity}
 \frac{\sigma K(x)}{A+B}
 =
 \tanh x+\frac{x}{2\sigma^2}
 -
 \frac{h}{2\sigma^2}
 \tanh\left(\frac{hx}{\sigma^2}\right).
\end{equation}
Since
\[
 h\tanh\left(\frac{hx}{\sigma^2}\right)
 =
 |h|\tanh\left(\frac{|h|x}{\sigma^2}\right),
\]
and \eqref{eq:h-less-sigma} gives
\[
 0\le\frac{|h|}{\sigma^2}<1,
\]
we have, for $x>0$,
\[
 0\le
 \frac{|h|x}{\sigma^2}
 <x.
\]
Since $\tanh$ is increasing,
\[
 \tanh\left(\frac{|h|x}{\sigma^2}\right)
 \le
 \tanh x.
\]
Therefore \eqref{eq:Kidentity} implies
\[
 \begin{aligned}
 \frac{\sigma K(x)}{A+B}
 &\ge
 \tanh x+\frac{x}{2\sigma^2}
 -
 \frac{|h|}{2\sigma^2}\tanh x\\
 &=
 \left(
   1-\frac{|h|}{2\sigma^2}
 \right)\tanh x
 +
 \frac{x}{2\sigma^2}.
 \end{aligned}
\]
For $x>0$, both $\tanh x$ and $x$ are positive, while
\[
 1-\frac{|h|}{2\sigma^2}
 >
 \frac12.
\]
Thus
\[
 K(x)>0,
 \qquad x>0.
\]

Combining this with \eqref{eq:gt-decreasing} and
\eqref{eq:Mprime-detail}, we conclude that
\[
 M'(r)\le0,
 \qquad 0\le r\le\tau.
\]
Hence
\[
 M(\tau)\le M(0).
\]
Since
\[
 M(\tau)
 =
 \E\bigl[
   (\mathsf T_\tau\sech^4)(X)
 \bigr]
 =
 \E\sech^4(X_{s,u}),
\]
whereas
\[
 M(0)
 =
 \E\sech^4(X)
 =
 \E\sech^4(h+\beta\sqrt q\,Z),
\]
we obtain
\[
 \E\sech^4(X_{s,u})
 \le
 \E\sech^4(h+\beta\sqrt q\,Z).
\]
Multiplying by $\beta^2$ and using the definition of $\alpha$ gives
\[
 \beta^2\E\sech^4(X_{s,u})
 \le
 \beta^2\E\sech^4(h+\beta\sqrt q\,Z)
 =
 \alpha.
\]
This proves \eqref{eq:uppercomparison}.
\end{proof}
-/

public import Lemmas.AT.Definitions
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Lemmas.SpinGlass.GaussianIntegrationByParts

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped MeasureTheory NNReal

private lemma integral_eq_integral_Ioi_add_neg {f : ℝ → ℝ} (hf : Integrable f) :
    ∫ x, f x = ∫ x in Set.Ioi (0 : ℝ), (f x + f (-x)) := by
  have hsplit := setIntegral_union (f := f)
    (Set.Iic_disjoint_Ioi (a := (0 : ℝ)) (b := 0) le_rfl)
    measurableSet_Ioi hf.integrableOn hf.integrableOn
  rw [Set.Iic_union_Ioi, setIntegral_univ] at hsplit
  have hneg : ∫ x in Set.Ioi (0 : ℝ), f (-x) = ∫ x in Set.Iic 0, f x := by
    simpa using integral_comp_neg_Ioi (0 : ℝ) f
  calc
    ∫ x, f x = (∫ x in Set.Iic 0, f x) + ∫ x in Set.Ioi 0, f x := hsplit
    _ = (∫ x in Set.Ioi 0, f (-x)) + ∫ x in Set.Ioi 0, f x := by rw [hneg]
    _ = ∫ x in Set.Ioi 0, (f (-x) + f x) :=
      (integral_add hf.comp_neg.integrableOn hf.integrableOn).symm
    _ = ∫ x in Set.Ioi 0, (f x + f (-x)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring

namespace SpinGlass.AT

private noncomputable def sech (x : ℝ) : ℝ := (Real.cosh x)⁻¹
private noncomputable def sech3 (x : ℝ) : ℝ := sech x ^ 3
private noncomputable def sech4 (x : ℝ) : ℝ := sech x ^ 4

private lemma sech_pos (x : ℝ) : 0 < sech x := by
  exact inv_pos.mpr (Real.cosh_pos x)

private lemma sech_le_one (x : ℝ) : sech x ≤ 1 := by
  exact inv_le_one_of_one_le₀ (Real.one_le_cosh x)

private lemma abs_sech_le_one (x : ℝ) : |sech x| ≤ 1 := by
  rw [abs_of_pos (sech_pos x)]
  exact sech_le_one x

private lemma abs_tanh_le_one (x : ℝ) : |Real.tanh x| ≤ 1 :=
  (Real.abs_tanh_lt_one x).le

private lemma sech3_hasDerivAt (x : ℝ) : HasDerivAt sech3
    (-3 * sech3 x * Real.tanh x) x := by
  unfold sech3 sech
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  apply (((Real.hasDerivAt_cosh x).inv hc).pow 3).congr_deriv
  rw [Real.tanh_eq_sinh_div_cosh]
  norm_num only [Nat.cast_ofNat, Nat.reduceSub]
  simp only [Pi.inv_apply, inv_pow]
  field_simp [hc]

private lemma continuous_sech3 : Continuous sech3 := by
  unfold sech3 sech
  exact (Real.continuous_cosh.inv₀ fun x => (Real.cosh_pos x).ne').pow 3

private lemma continuous_tanh : Continuous (fun x : ℝ => Real.tanh x) := by
  simp_rw [Real.tanh_eq_sinh_div_cosh]
  exact Real.continuous_sinh.div₀ Real.continuous_cosh
    (fun x => (Real.cosh_pos x).ne')

private lemma sech3_abs_le_one (x : ℝ) : |sech3 x| ≤ 1 := by
  unfold sech3
  rw [abs_pow]
  exact pow_le_one₀ (abs_nonneg _) (abs_sech_le_one x)

private lemma sech3Deriv_abs_le_three (x : ℝ) :
    |-3 * sech3 x * Real.tanh x| ≤ 3 := by
  rw [abs_mul, abs_mul, abs_neg]
  norm_num
  calc
    3 * |sech3 x| * |Real.tanh x| ≤ 3 * 1 * 1 := by
      gcongr
      · exact sech3_abs_le_one x
      · exact abs_tanh_le_one x
    _ = 3 := by norm_num

private lemma integrable_sech3_affine (a b : ℝ) :
    Integrable (fun z : ℝ => sech3 (a + b * z)) (gaussianReal 0 1) := by
  apply Integrable.of_bound (C := 1)
  · exact (continuous_sech3.comp
      (continuous_const.add (continuous_const.mul continuous_id)))
      |>.aestronglyMeasurable
  · filter_upwards [] with z
    simpa [Real.norm_eq_abs] using sech3_abs_le_one (a + b * z)

private lemma integrable_sech3Deriv_affine (a b : ℝ) :
    Integrable (fun z : ℝ => -3 * sech3 (a + b * z) *
      Real.tanh (a + b * z)) (gaussianReal 0 1) := by
  apply Integrable.of_bound (C := 3)
  · exact ((continuous_const.mul (continuous_sech3.comp
      (continuous_const.add (continuous_const.mul continuous_id)))).mul
      (continuous_tanh.comp
        (continuous_const.add (continuous_const.mul continuous_id))))
      |>.aestronglyMeasurable
  · filter_upwards [] with z
    simpa [Real.norm_eq_abs] using sech3Deriv_abs_le_three (a + b * z)

private noncomputable def smoothSech3 (r x : ℝ) : ℝ :=
  standardGaussianExpectation (fun z => sech3 (x + Real.sqrt r * z))

private lemma smoothSech3_hasDerivAt_x (r x : ℝ) :
    HasDerivAt (smoothSech3 r)
      (standardGaussianExpectation (fun z =>
        -3 * sech3 (x + Real.sqrt r * z) *
          Real.tanh (x + Real.sqrt r * z))) x := by
  unfold smoothSech3 standardGaussianExpectation
  let F : ℝ → ℝ → ℝ := fun y z => sech3 (y + Real.sqrt r * z)
  let F' : ℝ → ℝ → ℝ := fun y z =>
    -3 * sech3 (y + Real.sqrt r * z) * Real.tanh (y + Real.sqrt r * z)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (F := F) (F' := F') (x₀ := x)
    (s := Set.univ) (bound := fun _ => (3 : ℝ))
    (by simp)
    (Filter.Eventually.of_forall fun y => by
      exact (continuous_sech3.comp
        (continuous_const.add (continuous_const.mul continuous_id)))
        |>.aestronglyMeasurable)
    (by simpa [F] using integrable_sech3_affine x (Real.sqrt r))
    (by
      exact ((continuous_const.mul (continuous_sech3.comp
        (continuous_const.add (continuous_const.mul continuous_id)))).mul
        (continuous_tanh.comp
          (continuous_const.add (continuous_const.mul continuous_id))))
        |>.aestronglyMeasurable)
    (by
      filter_upwards [] with z
      intro y _
      simpa [F', Real.norm_eq_abs] using
        sech3Deriv_abs_le_three (y + Real.sqrt r * z))
    (integrable_const 3)
    (by
      filter_upwards [] with z
      intro y _
      simpa [F, F', Function.comp_def] using
        (sech3_hasDerivAt _).comp y
          ((hasDerivAt_id y).add_const (Real.sqrt r * z)))
  simpa [F, F'] using h.2

private lemma tanh_hasDerivAt (x : ℝ) : HasDerivAt (fun x : ℝ => Real.tanh x)
    (sech x ^ 2) x := by
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  rw [show (fun x : ℝ => Real.tanh x) = fun x => Real.sinh x / Real.cosh x by
    funext y
    exact Real.tanh_eq_sinh_div_cosh y]
  apply ((Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc).congr_deriv
  unfold sech
  simp only [Pi.inv_apply, inv_pow]
  field_simp [hc]
  nlinarith [Real.cosh_sq_sub_sinh_sq x]

private noncomputable def sech3Second (x : ℝ) : ℝ :=
  9 * sech3 x * Real.tanh x ^ 2 - 3 * sech3 x * sech x ^ 2

private lemma sech3Deriv_hasDerivAt (x : ℝ) :
    HasDerivAt (fun x => -3 * sech3 x * Real.tanh x) (sech3Second x) x := by
  have h := ((sech3_hasDerivAt x).const_mul (-3)).mul (tanh_hasDerivAt x)
  apply h.congr_deriv
  unfold sech3Second
  ring

private lemma sech3Second_abs_le_twelve (x : ℝ) : |sech3Second x| ≤ 12 := by
  have hs3 : |sech3 x| ≤ 1 := sech3_abs_le_one x
  have ht : |Real.tanh x| ≤ 1 := abs_tanh_le_one x
  have hs : |sech x| ≤ 1 := abs_sech_le_one x
  unfold sech3Second
  calc
    |9 * sech3 x * Real.tanh x ^ 2 - 3 * sech3 x * sech x ^ 2|
        ≤ |9 * sech3 x * Real.tanh x ^ 2| + |3 * sech3 x * sech x ^ 2| :=
      abs_sub _ _
    _ ≤ 9 * 1 * 1 ^ 2 + 3 * 1 * 1 ^ 2 := by
      simp only [abs_mul, abs_pow]
      gcongr <;> norm_num
    _ = 12 := by norm_num

private lemma integrable_sech3Second_affine (a b : ℝ) :
    Integrable (fun z : ℝ => sech3Second (a + b * z)) (gaussianReal 0 1) := by
  apply Integrable.of_bound (C := 12)
  · apply Continuous.aestronglyMeasurable
    unfold sech3Second
    exact (((continuous_const.mul (continuous_sech3.comp (by fun_prop))).mul
      ((continuous_tanh.comp (by fun_prop)).pow 2)).sub
      ((continuous_const.mul (continuous_sech3.comp (by fun_prop))).mul
        (((Real.continuous_cosh.comp (by fun_prop)).inv₀
          (fun z => (Real.cosh_pos _).ne')).pow 2)))
  · filter_upwards [] with z
    simpa [Real.norm_eq_abs] using sech3Second_abs_le_twelve (a + b * z)

private lemma smoothSech3_first_hasDerivAt_x (r x : ℝ) :
    HasDerivAt
      (fun y => standardGaussianExpectation (fun z =>
        -3 * sech3 (y + Real.sqrt r * z) *
          Real.tanh (y + Real.sqrt r * z)))
      (standardGaussianExpectation (fun z =>
        sech3Second (x + Real.sqrt r * z))) x := by
  unfold standardGaussianExpectation
  let F : ℝ → ℝ → ℝ := fun y z =>
    -3 * sech3 (y + Real.sqrt r * z) * Real.tanh (y + Real.sqrt r * z)
  let F' : ℝ → ℝ → ℝ := fun y z => sech3Second (y + Real.sqrt r * z)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (F := F) (F' := F') (x₀ := x)
    (s := Set.univ) (bound := fun _ => (12 : ℝ))
    (by simp)
    (Filter.Eventually.of_forall fun y => by
      exact ((continuous_const.mul (continuous_sech3.comp (by fun_prop))).mul
        (continuous_tanh.comp (by fun_prop))).aestronglyMeasurable)
    (by simpa [F] using integrable_sech3Deriv_affine x (Real.sqrt r))
    (by
      apply Continuous.aestronglyMeasurable
      unfold F' sech3Second
      exact (((continuous_const.mul (continuous_sech3.comp (by fun_prop))).mul
        ((continuous_tanh.comp (by fun_prop)).pow 2)).sub
        ((continuous_const.mul (continuous_sech3.comp (by fun_prop))).mul
          (((Real.continuous_cosh.comp (by fun_prop)).inv₀
            (fun z => (Real.cosh_pos _).ne')).pow 2))))
    (by
      filter_upwards [] with z
      intro y _
      simpa [F', Real.norm_eq_abs] using
        sech3Second_abs_le_twelve (y + Real.sqrt r * z))
    (integrable_const 12)
    (by
      filter_upwards [] with z
      intro y _
      simpa [F, F', Function.comp_def] using
        (sech3Deriv_hasDerivAt _).comp y
          ((hasDerivAt_id y).add_const (Real.sqrt r * z)))
  simpa [F, F'] using h.2

private lemma smoothSech3_hasDerivAt_x_twice (r x : ℝ) :
    HasDerivAt (deriv (smoothSech3 r))
      (standardGaussianExpectation (fun z =>
        sech3Second (x + Real.sqrt r * z))) x := by
  have h₁ := smoothSech3_hasDerivAt_x r
  have heq : deriv (smoothSech3 r) = fun y => standardGaussianExpectation (fun z =>
      -3 * sech3 (y + Real.sqrt r * z) *
        Real.tanh (y + Real.sqrt r * z)) := by
    funext y
    exact (h₁ y).deriv
  rw [heq]
  exact smoothSech3_first_hasDerivAt_x r x

private lemma contDiff_sech : ContDiff ℝ ⊤ sech := by
  unfold sech
  exact Real.contDiff_cosh.inv (fun x => (Real.cosh_pos x).ne')

private lemma contDiff_sech3 : ContDiff ℝ ⊤ sech3 := by
  unfold sech3
  exact contDiff_sech.pow 3

private lemma contDiff_tanh : ContDiff ℝ ⊤ (fun x : ℝ => Real.tanh x) := by
  simp_rw [Real.tanh_eq_sinh_div_cosh]
  exact Real.contDiff_sinh.div Real.contDiff_cosh
    (fun x => (Real.cosh_pos x).ne')

private lemma contDiff_sech3Deriv :
    ContDiff ℝ ⊤ (fun x => -3 * sech3 x * Real.tanh x) := by
  exact (contDiff_const.mul contDiff_sech3).mul contDiff_tanh

private lemma sech3Deriv_comp_deriv (a b z : ℝ) :
    deriv (fun y => -3 * sech3 (a + b * y) * Real.tanh (a + b * y)) z =
      b * sech3Second (a + b * z) := by
  have harg : HasDerivAt (fun y : ℝ => a + b * y) b z := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id z).const_mul b).const_add a
  simpa [Function.comp_def, mul_comm] using
    ((sech3Deriv_hasDerivAt (a + b * z)).comp z harg).deriv

private lemma sech3Deriv_comp_moderate (a b : ℝ) :
    HasModerateGrowth
      (fun z => -3 * sech3 (a + b * z) * Real.tanh (a + b * z)) := by
  refine ⟨16 * (1 + |b|), 0, by positivity, ?_, ?_⟩
  · intro z
    simpa only [pow_zero, mul_one] using
      (show |-3 * sech3 (a + b * z) * Real.tanh (a + b * z)| ≤
          16 * (1 + |b|) by
        have h := sech3Deriv_abs_le_three (a + b * z)
        have hb : 0 ≤ |b| := abs_nonneg b
        nlinarith)
  · intro z
    rw [sech3Deriv_comp_deriv]
    simpa only [pow_zero, mul_one] using
      (show |b * sech3Second (a + b * z)| ≤ 16 * (1 + |b|) by
        rw [abs_mul]
        have hs := sech3Second_abs_le_twelve (a + b * z)
        have hb : 0 ≤ |b| := abs_nonneg b
        nlinarith [mul_le_mul_of_nonneg_left hs hb])

private lemma smoothSech3_hasDerivAt_r_raw {r x : ℝ} (hr : 0 < r) :
    HasDerivAt (fun t => smoothSech3 t x)
      (standardGaussianExpectation (fun z =>
        (-3 * sech3 (x + Real.sqrt r * z) *
          Real.tanh (x + Real.sqrt r * z)) *
            (1 / (2 * Real.sqrt r) * z))) r := by
  unfold smoothSech3 standardGaussianExpectation
  let F : ℝ → ℝ → ℝ := fun t z => sech3 (x + Real.sqrt t * z)
  let F' : ℝ → ℝ → ℝ := fun t z =>
    (-3 * sech3 (x + Real.sqrt t * z) *
      Real.tanh (x + Real.sqrt t * z)) * (1 / (2 * Real.sqrt t) * z)
  let c : ℝ := Real.sqrt (r / 2)
  have hhalf : 0 < r / 2 := by linarith
  have hc : 0 < c := Real.sqrt_pos.2 hhalf
  have hboundInt : Integrable (fun z : ℝ => 3 * c⁻¹ * |z|)
      (gaussianReal 0 1) := by
    have hz : Integrable (fun z : ℝ => |z|) (gaussianReal 0 1) := by
      simpa using integrable_abs_pow_gaussianReal_centered (1 : ℝ≥0) 1
    exact hz.const_mul (3 * c⁻¹)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (F := F) (F' := F') (x₀ := r)
    (s := Set.Ioi (r / 2)) (bound := fun z => 3 * c⁻¹ * |z|)
    (Ioi_mem_nhds (by linarith))
    (Filter.Eventually.of_forall fun t =>
      (continuous_sech3.comp
        (continuous_const.add
          ((Real.continuous_sqrt.comp continuous_const).mul continuous_id)))
        |>.aestronglyMeasurable)
    (by simpa [F] using integrable_sech3_affine x (Real.sqrt r))
    (by
      apply Continuous.aestronglyMeasurable
      dsimp [F']
      exact (((continuous_const.mul (continuous_sech3.comp (by fun_prop))).mul
        (continuous_tanh.comp (by fun_prop))).mul
          (continuous_const.mul continuous_id)))
    (by
      filter_upwards [] with z
      intro t ht
      have htpos : 0 < t := lt_trans hhalf ht
      have hroot : 0 < Real.sqrt t := Real.sqrt_pos.2 htpos
      have hrootle : c ≤ Real.sqrt t := Real.sqrt_le_sqrt ht.le
      have hinv : (Real.sqrt t)⁻¹ ≤ c⁻¹ :=
        (inv_le_inv₀ hroot hc).2 hrootle
      have hcoef : |1 / (2 * Real.sqrt t)| ≤ c⁻¹ := by
        rw [abs_of_pos (by positivity : 0 < 1 / (2 * Real.sqrt t))]
        calc
          1 / (2 * Real.sqrt t) ≤ (Real.sqrt t)⁻¹ := by
            rw [one_div]
            exact (inv_le_inv₀ (by positivity) hroot).2 (by nlinarith)
          _ ≤ c⁻¹ := hinv
      dsimp [F']
      calc
        |(-3 * sech3 (x + Real.sqrt t * z) * Real.tanh (x + Real.sqrt t * z)) *
            (1 / (2 * Real.sqrt t) * z)|
            = |-3 * sech3 (x + Real.sqrt t * z) * Real.tanh (x + Real.sqrt t * z)| *
                |1 / (2 * Real.sqrt t)| * |z| := by
                  simp only [abs_mul]
                  ring
        _
            ≤ 3 * c⁻¹ * |z| := by
              have hp :
                  |-3 * sech3 (x + Real.sqrt t * z) * Real.tanh (x + Real.sqrt t * z)| *
                      |1 / (2 * Real.sqrt t)| ≤ 3 * c⁻¹ :=
                mul_le_mul (sech3Deriv_abs_le_three _) hcoef
                  (abs_nonneg _) (by norm_num)
              exact mul_le_mul_of_nonneg_right hp (abs_nonneg z))
    hboundInt
    (by
      filter_upwards [] with z
      intro t ht
      have htpos : 0 < t := lt_trans hhalf ht
      have hsqrt := Real.hasDerivAt_sqrt htpos.ne'
      have harg : HasDerivAt (fun t => x + Real.sqrt t * z)
          (1 / (2 * Real.sqrt t) * z) t := by
        exact (hsqrt.mul_const z).const_add x
      simpa [F, F', Function.comp_def] using
        (sech3_hasDerivAt _).comp t harg)
  simpa [F, F'] using h.2

private lemma smoothSech3_hasDerivAt_r {r x : ℝ} (hr : 0 < r) :
    HasDerivAt (fun t => smoothSech3 t x)
      ((1 / 2) * standardGaussianExpectation (fun z =>
        sech3Second (x + Real.sqrt r * z))) r := by
  apply (smoothSech3_hasDerivAt_r_raw (x := x) hr).congr_deriv
  unfold standardGaussianExpectation
  let F : ℝ → ℝ := fun z =>
    -3 * sech3 (x + Real.sqrt r * z) * Real.tanh (x + Real.sqrt r * z)
  have hcont : ContDiff ℝ 1 F := by
    exact (contDiff_sech3Deriv.of_le (by norm_num)).comp (by fun_prop)
  have hibp := gaussianReal_integration_by_parts (v := (1 : ℝ≥0)) one_ne_zero
    hcont (sech3Deriv_comp_moderate x (Real.sqrt r))
  have hderiv : deriv F = fun z => Real.sqrt r * sech3Second
      (x + Real.sqrt r * z) := by
    funext z
    exact sech3Deriv_comp_deriv x (Real.sqrt r) z
  rw [hderiv] at hibp
  simp only [NNReal.coe_one, one_mul] at hibp
  have hsqrt : Real.sqrt r ≠ 0 := (Real.sqrt_pos.2 hr).ne'
  calc
    ∫ z, F z * (1 / (2 * Real.sqrt r) * z) ∂gaussianReal 0 1
        = (1 / (2 * Real.sqrt r)) * ∫ z, z * F z ∂gaussianReal 0 1 := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards [] with z
          ring
    _ = (1 / (2 * Real.sqrt r)) *
          ∫ z, Real.sqrt r * sech3Second (x + Real.sqrt r * z)
            ∂gaussianReal 0 1 := by rw [hibp]
    _ = (1 / 2) * ∫ z, sech3Second (x + Real.sqrt r * z)
          ∂gaussianReal 0 1 := by
          rw [integral_const_mul]
          field_simp [hsqrt]

private lemma sech_neg (x : ℝ) : sech (-x) = sech x := by
  unfold sech
  rw [Real.cosh_neg]

private lemma sech3_neg (x : ℝ) : sech3 (-x) = sech3 x := by
  unfold sech3
  rw [sech_neg]

private lemma sech3Deriv_neg (x : ℝ) :
    -3 * sech3 (-x) * Real.tanh (-x) =
      -(-3 * sech3 x * Real.tanh x) := by
  rw [sech3_neg, Real.tanh_neg]
  ring

private lemma integral_comp_neg_standard (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ z, f (-z) ∂gaussianReal 0 1) = ∫ z, f z ∂gaussianReal 0 1 := by
  have hmap : Measure.map (fun z : ℝ => -z) (gaussianReal 0 1) =
      gaussianReal 0 1 := by simpa using gaussianReal_map_neg (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
  calc
    (∫ z, f (-z) ∂gaussianReal 0 1) =
        ∫ z, f z ∂Measure.map (fun z : ℝ => -z) (gaussianReal 0 1) := by
          rw [integral_map (by fun_prop) hf.aestronglyMeasurable]
    _ = ∫ z, f z ∂gaussianReal 0 1 := by rw [hmap]

private lemma smoothSech3_neg (r x : ℝ) : smoothSech3 r (-x) = smoothSech3 r x := by
  unfold smoothSech3 standardGaussianExpectation
  calc
    ∫ z, sech3 (-x + Real.sqrt r * z) ∂gaussianReal 0 1 =
        ∫ z, sech3 (x + Real.sqrt r * (-z)) ∂gaussianReal 0 1 := by
          apply integral_congr_ae
          filter_upwards [] with z
          calc
            sech3 (-x + Real.sqrt r * z) =
                sech3 (-(x + Real.sqrt r * (-z))) := by congr 1 <;> ring
            _ = sech3 (x + Real.sqrt r * (-z)) := sech3_neg _
    _ = ∫ z, sech3 (x + Real.sqrt r * z) ∂gaussianReal 0 1 := by
      simpa using integral_comp_neg_standard
        (fun z => sech3 (x + Real.sqrt r * z))
        (continuous_sech3.comp (by fun_prop))

private lemma smoothSech3_first_neg (r x : ℝ) :
    standardGaussianExpectation (fun z =>
      -3 * sech3 (-x + Real.sqrt r * z) *
        Real.tanh (-x + Real.sqrt r * z)) =
      -standardGaussianExpectation (fun z =>
        -3 * sech3 (x + Real.sqrt r * z) *
          Real.tanh (x + Real.sqrt r * z)) := by
  unfold standardGaussianExpectation
  calc
    ∫ z, -3 * sech3 (-x + Real.sqrt r * z) *
        Real.tanh (-x + Real.sqrt r * z) ∂gaussianReal 0 1 =
        ∫ z, -(-3 * sech3 (x + Real.sqrt r * (-z)) *
          Real.tanh (x + Real.sqrt r * (-z))) ∂gaussianReal 0 1 := by
            apply integral_congr_ae
            filter_upwards [] with z
            calc
              -3 * sech3 (-x + Real.sqrt r * z) *
                  Real.tanh (-x + Real.sqrt r * z) =
                  -3 * sech3 (-(x + Real.sqrt r * (-z))) *
                    Real.tanh (-(x + Real.sqrt r * (-z))) := by
                      congr 2 <;> ring
              _ = -(-3 * sech3 (x + Real.sqrt r * (-z)) *
                    Real.tanh (x + Real.sqrt r * (-z))) := sech3Deriv_neg _
    _ = -∫ z, -3 * sech3 (x + Real.sqrt r * z) *
          Real.tanh (x + Real.sqrt r * z) ∂gaussianReal 0 1 := by
      rw [integral_neg]
      congr 1
      simpa using integral_comp_neg_standard
        (fun z => -3 * sech3 (x + Real.sqrt r * z) *
          Real.tanh (x + Real.sqrt r * z))
        (((continuous_const.mul (continuous_sech3.comp (by fun_prop))).mul
          (continuous_tanh.comp (by fun_prop))))

private lemma standard_affine_integral_eq_gaussian
    {r : ℝ} (hr : 0 ≤ r) (x : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ z, f (x + Real.sqrt r * z) ∂gaussianReal 0 1) =
      ∫ y, f y ∂gaussianReal x ⟨r, hr⟩ := by
  let v : ℝ≥0 := ⟨r, hr⟩
  have hmul : Measure.map (fun z : ℝ => Real.sqrt r * z) (gaussianReal 0 1) =
      gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul]
    simp only [mul_zero]
    apply congrArg (gaussianReal 0)
    apply NNReal.eq
    simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one, mul_one]
    exact Real.sq_sqrt hr
  have hadd : Measure.map (fun y : ℝ => x + y) (gaussianReal 0 v) =
      gaussianReal x v := by
    simpa using gaussianReal_map_const_add (μ := (0 : ℝ)) (v := v) x
  have hmap : Measure.map (fun z : ℝ => x + Real.sqrt r * z)
      (gaussianReal 0 1) = gaussianReal x v := by
    calc
      Measure.map (fun z : ℝ => x + Real.sqrt r * z) (gaussianReal 0 1) =
          Measure.map (fun y : ℝ => x + y)
            (Measure.map (fun z : ℝ => Real.sqrt r * z) (gaussianReal 0 1)) := by
              simpa [Function.comp_def] using
                (Measure.map_map
                  (μ := gaussianReal 0 1)
                  (g := fun y : ℝ => x + y)
                  (f := fun z : ℝ => Real.sqrt r * z)
                  (by fun_prop) (by fun_prop)).symm
      _ = Measure.map (fun y : ℝ => x + y) (gaussianReal 0 v) := by rw [hmul]
      _ = gaussianReal x v := hadd
  calc
    (∫ z, f (x + Real.sqrt r * z) ∂gaussianReal 0 1) =
        ∫ y, f y ∂Measure.map (fun z : ℝ => x + Real.sqrt r * z)
          (gaussianReal 0 1) := by
            rw [integral_map (by fun_prop) hf.aestronglyMeasurable]
    _ = ∫ y, f y ∂gaussianReal x ⟨r, hr⟩ := by rw [hmap]

private lemma gaussianPDFReal_neg_le_self {v : ℝ≥0} (hv : v ≠ 0)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    gaussianPDFReal x v (-y) ≤ gaussianPDFReal x v y := by
  rw [gaussianPDFReal, gaussianPDFReal]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hvpos : 0 < (v : ℝ) := by
    exact_mod_cast (bot_lt_iff_ne_bot.mpr hv)
  apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ 2 * (v : ℝ))
  nlinarith [sq_nonneg (y - x), sq_nonneg (y + x)]

private lemma smoothSech3_first_nonpos {r x : ℝ} (hr : 0 ≤ r) (hx : 0 ≤ x) :
    standardGaussianExpectation (fun z =>
      -3 * sech3 (x + Real.sqrt r * z) *
        Real.tanh (x + Real.sqrt r * z)) ≤ 0 := by
  by_cases hr0 : r = 0
  · subst r
    simp only [Real.sqrt_zero, zero_mul, add_zero, standardGaussianExpectation,
      integral_const, probReal_univ, one_smul]
    have ht : 0 ≤ Real.tanh x := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_nonneg ((Real.sinh_nonneg_iff).2 hx) (Real.cosh_pos x).le
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num)
        (pow_nonneg (sech_pos x).le 3)) ht
  let v : ℝ≥0 := ⟨r, hr⟩
  have hvpos : 0 < v := by
    change 0 < r
    exact lt_of_le_of_ne hr (Ne.symm hr0)
  have hv : v ≠ 0 := hvpos.ne'
  let D : ℝ → ℝ := fun y => -3 * sech3 y * Real.tanh y
  have hshift : standardGaussianExpectation (fun z => D (x + Real.sqrt r * z)) =
      ∫ y, D y ∂gaussianReal x v := by
    unfold standardGaussianExpectation
    simpa [v] using standard_affine_integral_eq_gaussian hr x
      ((continuous_const.mul continuous_sech3).mul continuous_tanh)
  rw [hshift, integral_gaussianReal_eq_integral_smul hv]
  have hvol : Integrable (fun y => gaussianPDFReal x v y * D y) := by
    apply Integrable.mono' ((integrable_gaussianPDFReal x v).const_mul 3)
    · exact ((measurable_gaussianPDFReal x v).mul
        ((continuous_const.mul continuous_sech3).mul continuous_tanh).measurable)
        |>.aestronglyMeasurable
    · filter_upwards [] with y
      have hp := gaussianPDFReal_nonneg x v y
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp]
      dsimp [D]
      calc
        gaussianPDFReal x v y *
            |-3 * sech3 y * Real.tanh y| ≤
            gaussianPDFReal x v y * 3 :=
          mul_le_mul_of_nonneg_left (sech3Deriv_abs_le_three y) hp
        _ = 3 * gaussianPDFReal x v y := by ring
  simp only [smul_eq_mul]
  rw [integral_eq_integral_Ioi_add_neg hvol]
  apply integral_nonpos_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hy0 : 0 ≤ y := hy.le
  have hD : D y ≤ 0 := by
    have ht : 0 ≤ Real.tanh y := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_nonneg ((Real.sinh_nonneg_iff).2 hy0) (Real.cosh_pos y).le
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num)
        (pow_nonneg (sech_pos y).le 3)) ht
  have hp := gaussianPDFReal_neg_le_self hv hx hy0
  change gaussianPDFReal x v y * D y + gaussianPDFReal x v (-y) * D (-y) ≤ 0
  have hDneg : D (-y) = -D y := by
    exact sech3Deriv_neg y
  rw [hDneg]
  nlinarith [mul_nonpos_of_nonpos_of_nonneg hD (sub_nonneg.mpr hp)]

private noncomputable def smoothSech3First (r x : ℝ) : ℝ :=
  standardGaussianExpectation (fun z =>
    -3 * sech3 (x + Real.sqrt r * z) *
      Real.tanh (x + Real.sqrt r * z))

private noncomputable def smoothSech3Second (r x : ℝ) : ℝ :=
  standardGaussianExpectation (fun z => sech3Second (x + Real.sqrt r * z))

private lemma smoothSech3_nonneg (r x : ℝ) : 0 ≤ smoothSech3 r x := by
  unfold smoothSech3 standardGaussianExpectation
  apply integral_nonneg
  intro z
  exact pow_nonneg (sech_pos _).le 3

private lemma abs_smoothSech3_le_one (r x : ℝ) : |smoothSech3 r x| ≤ 1 := by
  rw [abs_of_nonneg (smoothSech3_nonneg r x)]
  unfold smoothSech3 standardGaussianExpectation
  calc
    (∫ z, sech3 (x + Real.sqrt r * z) ∂gaussianReal 0 1) ≤
        ∫ _z : ℝ, (1 : ℝ) ∂gaussianReal 0 1 := by
          apply integral_mono (integrable_sech3_affine x (Real.sqrt r)) (integrable_const 1)
          intro z
          exact le_trans (le_abs_self _) (sech3_abs_le_one _)
    _ = 1 := by simp

private lemma abs_smoothSech3First_le_three (r x : ℝ) :
    |smoothSech3First r x| ≤ 3 := by
  unfold smoothSech3First standardGaussianExpectation
  calc
    |∫ z, -3 * sech3 (x + Real.sqrt r * z) *
        Real.tanh (x + Real.sqrt r * z) ∂gaussianReal 0 1| ≤
        ∫ z, |-3 * sech3 (x + Real.sqrt r * z) *
          Real.tanh (x + Real.sqrt r * z)| ∂gaussianReal 0 1 :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _z : ℝ, (3 : ℝ) ∂gaussianReal 0 1 := by
      apply integral_mono
      · exact (integrable_sech3Deriv_affine x (Real.sqrt r)).abs
      · exact integrable_const 3
      · intro z
        exact sech3Deriv_abs_le_three _
    _ = 3 := by simp

private lemma abs_smoothSech3Second_le_twelve (r x : ℝ) :
    |smoothSech3Second r x| ≤ 12 := by
  unfold smoothSech3Second standardGaussianExpectation
  calc
    |∫ z, sech3Second (x + Real.sqrt r * z) ∂gaussianReal 0 1| ≤
        ∫ z, |sech3Second (x + Real.sqrt r * z)| ∂gaussianReal 0 1 :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _z : ℝ, (12 : ℝ) ∂gaussianReal 0 1 := by
      apply integral_mono
      · exact (integrable_sech3Second_affine x (Real.sqrt r)).abs
      · exact integrable_const 12
      · intro z
        exact sech3Second_abs_le_twelve _
    _ = 12 := by simp

private lemma sech_hasDerivAt (x : ℝ) :
    HasDerivAt sech (-sech x * Real.tanh x) x := by
  unfold sech
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  apply ((Real.hasDerivAt_cosh x).inv hc).congr_deriv
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [hc]

private lemma tanh_sq_add_sech_sq (x : ℝ) :
    Real.tanh x ^ 2 + sech x ^ 2 = 1 := by
  unfold sech
  rw [Real.tanh_eq_sinh_div_cosh]
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  simp only [div_pow, inv_pow]
  field_simp [hc]
  nlinarith [Real.cosh_sq_sub_sinh_sq x]

private noncomputable def tiltedSech4Value (r x : ℝ) : ℝ :=
  Real.exp (-r / 2) * smoothSech3 r x * sech x

private noncomputable def tiltedSech4First (r x : ℝ) : ℝ :=
  Real.exp (-r / 2) * sech x *
    (smoothSech3First r x - smoothSech3 r x * Real.tanh x)

private noncomputable def tiltedSech4Second (r x : ℝ) : ℝ :=
  Real.exp (-r / 2) * sech x *
    (smoothSech3Second r x - 2 * smoothSech3First r x * Real.tanh x +
      smoothSech3 r x * (Real.tanh x ^ 2 - sech x ^ 2))

private lemma tiltedSech4Value_hasDerivAt_x (r x : ℝ) :
    HasDerivAt (tiltedSech4Value r) (tiltedSech4First r x) x := by
  have ha : HasDerivAt (smoothSech3 r) (smoothSech3First r x) x := by
    simpa [smoothSech3First] using smoothSech3_hasDerivAt_x r x
  have hs := sech_hasDerivAt x
  unfold tiltedSech4Value tiltedSech4First
  apply ((ha.const_mul (Real.exp (-r / 2))).mul hs).congr_deriv
  ring

private lemma tiltedSech4First_hasDerivAt_x (r x : ℝ) :
    HasDerivAt (tiltedSech4First r) (tiltedSech4Second r x) x := by
  have ha : HasDerivAt (smoothSech3 r) (smoothSech3First r x) x := by
    simpa [smoothSech3First] using smoothSech3_hasDerivAt_x r x
  have ha₁ : HasDerivAt (smoothSech3First r) (smoothSech3Second r x) x := by
    change HasDerivAt
      (fun y => standardGaussianExpectation (fun z =>
        -3 * sech3 (y + Real.sqrt r * z) * Real.tanh (y + Real.sqrt r * z)))
      (standardGaussianExpectation (fun z => sech3Second (x + Real.sqrt r * z))) x
    exact smoothSech3_first_hasDerivAt_x r x
  have hs := sech_hasDerivAt x
  have ht := tanh_hasDerivAt x
  unfold tiltedSech4First tiltedSech4Second
  have hbracket := ha₁.sub (ha.mul ht)
  apply ((hs.const_mul (Real.exp (-r / 2))).mul hbracket).congr_deriv
  simp only [Pi.sub_apply, Pi.mul_apply]
  ring

private lemma tiltedSech4_generator (r x : ℝ) :
    (1 / 2) * tiltedSech4Second r x +
        Real.tanh x * tiltedSech4First r x =
      (1 / 2) * Real.exp (-r / 2) * sech x *
        (smoothSech3Second r x - smoothSech3 r x) := by
  have hid := tanh_sq_add_sech_sq x
  have ht : Real.tanh x ^ 2 = 1 - sech x ^ 2 := by linarith
  unfold tiltedSech4Second tiltedSech4First
  linear_combination
    -(Real.exp (-r / 2) * sech x * smoothSech3 r x / 2) * hid

private lemma tiltedSech4Value_hasDerivAt_r {r x : ℝ} (hr : 0 < r) :
    HasDerivAt (fun t => tiltedSech4Value t x)
      ((1 / 2) * Real.exp (-r / 2) * sech x *
        (smoothSech3Second r x - smoothSech3 r x)) r := by
  have he : HasDerivAt (fun t : ℝ => Real.exp (-t / 2))
      ((-1 / 2) * Real.exp (-r / 2)) r := by
    have hinner : HasDerivAt (fun t : ℝ => -t / 2) (-1 / 2) r := by
      rw [show (fun t : ℝ => -t / 2) = fun t => (-1 / 2) * t by
        funext t
        ring]
      simpa using (hasDerivAt_id r).const_mul (-1 / 2)
    simpa only [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_exp (-r / 2)).comp r hinner
  have ha := smoothSech3_hasDerivAt_r (x := x) hr
  unfold tiltedSech4Value smoothSech3Second
  apply ((he.mul ha).mul_const (sech x)).congr_deriv
  ring

private lemma tiltedSech4First_nonpos {r x : ℝ} (hr : 0 ≤ r) (hx : 0 ≤ x) :
    tiltedSech4First r x ≤ 0 := by
  have ha₁ : smoothSech3First r x ≤ 0 :=
    smoothSech3_first_nonpos hr hx
  have ha : 0 ≤ smoothSech3 r x := smoothSech3_nonneg r x
  have ht : 0 ≤ Real.tanh x := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg ((Real.sinh_nonneg_iff).2 hx) (Real.cosh_pos x).le
  unfold tiltedSech4First
  exact mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (Real.exp_pos _).le (sech_pos x).le)
    (by linarith [mul_nonneg ha ht])

private lemma tiltedSech4First_neg (r x : ℝ) :
    tiltedSech4First r (-x) = -tiltedSech4First r x := by
  unfold tiltedSech4First smoothSech3First
  rw [sech_neg, Real.tanh_neg, smoothSech3_neg, smoothSech3_first_neg]
  ring

private lemma continuous_smoothSech3 (r : ℝ) : Continuous (smoothSech3 r) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (smoothSech3_hasDerivAt_x r x).continuousAt

private lemma continuous_smoothSech3First (r : ℝ) : Continuous (smoothSech3First r) := by
  rw [continuous_iff_continuousAt]
  intro x
  change ContinuousAt
    (fun y => standardGaussianExpectation (fun z =>
      -3 * sech3 (y + Real.sqrt r * z) * Real.tanh (y + Real.sqrt r * z))) x
  exact (smoothSech3_first_hasDerivAt_x r x).continuousAt

private lemma continuous_smoothSech3Second (r : ℝ) : Continuous (smoothSech3Second r) := by
  unfold smoothSech3Second standardGaussianExpectation
  rw [continuous_iff_continuousAt]
  intro x
  have hmeas : ∀ᶠ y in nhds x,
      AEStronglyMeasurable (fun z => sech3Second (y + Real.sqrt r * z))
        (gaussianReal 0 1) := by
    exact Filter.Eventually.of_forall fun y =>
      (by
        apply Continuous.aestronglyMeasurable
        unfold sech3Second
        exact (((continuous_const.mul (continuous_sech3.comp (by fun_prop))).mul
          ((continuous_tanh.comp (by fun_prop)).pow 2)).sub
          ((continuous_const.mul (continuous_sech3.comp (by fun_prop))).mul
            (((Real.continuous_cosh.comp (by fun_prop)).inv₀
              (fun z => (Real.cosh_pos _).ne')).pow 2))))
  have hbound : ∀ᶠ y in nhds x, ∀ᵐ z ∂gaussianReal 0 1,
      ‖sech3Second (y + Real.sqrt r * z)‖ ≤ (12 : ℝ) := by
    exact Filter.Eventually.of_forall fun y => ae_of_all _ fun z => by
      simpa [Real.norm_eq_abs] using sech3Second_abs_le_twelve (y + Real.sqrt r * z)
  have hlim : ∀ᵐ z ∂gaussianReal 0 1,
      Filter.Tendsto (fun y => sech3Second (y + Real.sqrt r * z)) (nhds x)
        (nhds (sech3Second (x + Real.sqrt r * z))) := by
    exact ae_of_all _ fun z => by
      apply ContinuousAt.tendsto
      unfold sech3Second
      exact (((continuous_const.mul (continuous_sech3.comp (by fun_prop))).mul
        ((continuous_tanh.comp (by fun_prop)).pow 2)).sub
        ((continuous_const.mul (continuous_sech3.comp (by fun_prop))).mul
          (((Real.continuous_cosh.comp (by fun_prop)).inv₀
            (fun y => (Real.cosh_pos _).ne')).pow 2))).continuousAt
  exact tendsto_integral_filter_of_dominated_convergence
    (l := nhds x) (F := fun y z => sech3Second (y + Real.sqrt r * z))
    (f := fun z => sech3Second (x + Real.sqrt r * z))
    (bound := fun _ => (12 : ℝ)) hmeas hbound (integrable_const 12) hlim

private lemma continuous_tiltedSech4Value (r : ℝ) : Continuous (tiltedSech4Value r) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (tiltedSech4Value_hasDerivAt_x r x).continuousAt

private lemma continuous_tiltedSech4First (r : ℝ) : Continuous (tiltedSech4First r) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (tiltedSech4First_hasDerivAt_x r x).continuousAt

private lemma continuous_sech : Continuous sech := contDiff_sech.continuous

private lemma continuous_tiltedSech4Second (r : ℝ) : Continuous (tiltedSech4Second r) := by
  unfold tiltedSech4Second
  exact ((continuous_const.mul continuous_sech).mul
    (((continuous_smoothSech3Second r).sub
      ((continuous_const.mul (continuous_smoothSech3First r)).mul continuous_tanh)).add
      ((continuous_smoothSech3 r).mul
        ((continuous_tanh.pow 2).sub (continuous_sech.pow 2)))))

private lemma abs_tiltedSech4Value_le_one {r x : ℝ} (hr : 0 ≤ r) :
    |tiltedSech4Value r x| ≤ 1 := by
  unfold tiltedSech4Value
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (sech_pos _)]
  have he : Real.exp (-r / 2) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  calc
    Real.exp (-r / 2) * |smoothSech3 r x| * sech x ≤ 1 * 1 * 1 := by
      have h₁ : Real.exp (-r / 2) * |smoothSech3 r x| ≤ 1 * 1 :=
        mul_le_mul he (abs_smoothSech3_le_one r x) (abs_nonneg _) (by norm_num)
      exact mul_le_mul h₁ (sech_le_one x) (sech_pos x).le (by norm_num)
    _ = 1 := by norm_num

private lemma abs_tiltedSech4First_le_four {r x : ℝ} (hr : 0 ≤ r) :
    |tiltedSech4First r x| ≤ 4 := by
  unfold tiltedSech4First
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (sech_pos _)]
  have he : Real.exp (-r / 2) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hb : |smoothSech3First r x - smoothSech3 r x * Real.tanh x| ≤ 4 := by
    calc
      |smoothSech3First r x - smoothSech3 r x * Real.tanh x| ≤
          |smoothSech3First r x| + |smoothSech3 r x| * |Real.tanh x| := by
            simpa [abs_mul] using abs_sub (smoothSech3First r x)
              (smoothSech3 r x * Real.tanh x)
      _ ≤ 3 + 1 * 1 := by
        gcongr
        · exact abs_smoothSech3First_le_three r x
        · exact abs_smoothSech3_le_one r x
        · exact abs_tanh_le_one x
      _ = 4 := by norm_num
  calc
    Real.exp (-r / 2) * sech x *
        |smoothSech3First r x - smoothSech3 r x * Real.tanh x| ≤
        1 * 1 * 4 := by
          have h₁ : Real.exp (-r / 2) * sech x ≤ 1 * 1 :=
            mul_le_mul he (sech_le_one x) (sech_pos x).le (by norm_num)
          exact mul_le_mul h₁ hb (abs_nonneg _) (by norm_num)
    _ = 4 := by norm_num

private lemma abs_tiltedSech4Second_le_twenty {r x : ℝ} (hr : 0 ≤ r) :
    |tiltedSech4Second r x| ≤ 20 := by
  unfold tiltedSech4Second
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (sech_pos _)]
  have he : Real.exp (-r / 2) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hinside : |smoothSech3Second r x -
      2 * smoothSech3First r x * Real.tanh x +
      smoothSech3 r x * (Real.tanh x ^ 2 - sech x ^ 2)| ≤ 20 := by
    calc
      |smoothSech3Second r x - 2 * smoothSech3First r x * Real.tanh x +
          smoothSech3 r x * (Real.tanh x ^ 2 - sech x ^ 2)| ≤
          |smoothSech3Second r x| + 2 * |smoothSech3First r x| * |Real.tanh x| +
            |smoothSech3 r x| * (|Real.tanh x| ^ 2 + |sech x| ^ 2) := by
              calc
                _ ≤ |smoothSech3Second r x -
                    2 * smoothSech3First r x * Real.tanh x| +
                    |smoothSech3 r x * (Real.tanh x ^ 2 - sech x ^ 2)| :=
                  abs_add_le _ _
                _ ≤ (|smoothSech3Second r x| +
                    |2 * smoothSech3First r x * Real.tanh x|) +
                    |smoothSech3 r x| * |Real.tanh x ^ 2 - sech x ^ 2| := by
                      gcongr
                      · exact abs_sub _ _
                      · rw [abs_mul]
                _ ≤ _ := by
                  rw [abs_mul, abs_mul,
                    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
                  gcongr
                  calc
                    |Real.tanh x ^ 2 - sech x ^ 2| =
                        |Real.tanh x ^ 2 + -(sech x ^ 2)| := by ring
                    _ ≤ |Real.tanh x ^ 2| + |-(sech x ^ 2)| := abs_add_le _ _
                    _ = |Real.tanh x| ^ 2 + |sech x| ^ 2 := by
                      rw [abs_neg, abs_pow, abs_pow]
      _ ≤ 12 + 2 * 3 * 1 + 1 * (1 ^ 2 + 1 ^ 2) := by
        gcongr
        · exact abs_smoothSech3Second_le_twelve r x
        · exact abs_smoothSech3First_le_three r x
        · exact abs_tanh_le_one x
        · exact abs_smoothSech3_le_one r x
        · exact abs_tanh_le_one x
        · exact abs_sech_le_one x
      _ = 20 := by norm_num
  calc
    Real.exp (-r / 2) * sech x *
        |smoothSech3Second r x - 2 * smoothSech3First r x * Real.tanh x +
          smoothSech3 r x * (Real.tanh x ^ 2 - sech x ^ 2)| ≤
        1 * 1 * 20 := by
          have h₁ : Real.exp (-r / 2) * sech x ≤ 1 * 1 :=
            mul_le_mul he (sech_le_one x) (sech_pos x).le (by norm_num)
          exact mul_le_mul h₁ hinside (abs_nonneg _) (by norm_num)
    _ = 20 := by norm_num

private lemma tiltedSech4First_deriv (r x : ℝ) :
    deriv (tiltedSech4First r) x = tiltedSech4Second r x :=
  (tiltedSech4First_hasDerivAt_x r x).deriv

private lemma contDiff_tiltedSech4First (r : ℝ) :
    ContDiff ℝ 1 (tiltedSech4First r) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (tiltedSech4First_hasDerivAt_x r x).differentiableAt, ?_⟩
  have heq : deriv (tiltedSech4First r) = tiltedSech4Second r := by
    funext x
    exact tiltedSech4First_deriv r x
  rw [heq]
  exact continuous_tiltedSech4Second r

private lemma tiltedSech4First_shift_moderate {r : ℝ} (hr : 0 ≤ r) (h : ℝ) :
    HasModerateGrowth (fun y => tiltedSech4First r (h + y)) := by
  refine ⟨21, 0, by norm_num, ?_, ?_⟩
  · intro y
    simpa using (abs_tiltedSech4First_le_four (x := h + y) hr).trans (by norm_num)
  · intro y
    have hderiv : deriv (fun y => tiltedSech4First r (h + y)) y =
        tiltedSech4Second r (h + y) := by
      simpa [Function.comp_def] using
        ((tiltedSech4First_hasDerivAt_x r (h + y)).comp y
          ((hasDerivAt_id y).const_add h)).deriv
    rw [hderiv]
    simpa using (abs_tiltedSech4Second_le_twenty (x := h + y) hr).trans (by norm_num)

private lemma continuous_smoothSech3_time (x : ℝ) :
    Continuous (fun r => smoothSech3 r x) := by
  unfold smoothSech3 standardGaussianExpectation
  rw [continuous_iff_continuousAt]
  intro r₀
  have hmeas : ∀ᶠ r in nhds r₀,
      AEStronglyMeasurable (fun z => sech3 (x + Real.sqrt r * z))
        (gaussianReal 0 1) := by
    exact Filter.Eventually.of_forall fun r =>
      (continuous_sech3.comp (by fun_prop)).aestronglyMeasurable
  have hbound : ∀ᶠ r in nhds r₀, ∀ᵐ z ∂gaussianReal 0 1,
      ‖sech3 (x + Real.sqrt r * z)‖ ≤ (1 : ℝ) := by
    exact Filter.Eventually.of_forall fun r => ae_of_all _ fun z => by
      simpa [Real.norm_eq_abs] using sech3_abs_le_one (x + Real.sqrt r * z)
  have hlim : ∀ᵐ z ∂gaussianReal 0 1,
      Filter.Tendsto (fun r => sech3 (x + Real.sqrt r * z)) (nhds r₀)
        (nhds (sech3 (x + Real.sqrt r₀ * z))) := by
    exact ae_of_all _ fun z =>
      (continuous_sech3.comp (by fun_prop)).continuousAt.tendsto
  exact tendsto_integral_filter_of_dominated_convergence
    (l := nhds r₀) (F := fun r z => sech3 (x + Real.sqrt r * z))
    (f := fun z => sech3 (x + Real.sqrt r₀ * z))
    (bound := fun _ => (1 : ℝ)) hmeas hbound (integrable_const 1) hlim

private lemma continuous_tiltedSech4Value_time (x : ℝ) :
    Continuous (fun r => tiltedSech4Value r x) := by
  unfold tiltedSech4Value
  exact ((Real.continuous_exp.comp (by fun_prop)).mul
    (continuous_smoothSech3_time x)).mul continuous_const

private lemma abs_tiltedSech4Value_le_exp (r x : ℝ) :
    |tiltedSech4Value r x| ≤ Real.exp (-r / 2) := by
  unfold tiltedSech4Value
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (sech_pos _)]
  have h₁ : |smoothSech3 r x| * sech x ≤ 1 * 1 :=
    mul_le_mul (abs_smoothSech3_le_one r x) (sech_le_one x)
      (sech_pos x).le (by norm_num)
  simpa [mul_assoc] using
    mul_le_mul_of_nonneg_left h₁ (Real.exp_pos (-r / 2)).le

private noncomputable def tiltedSech4Average (v : ℝ≥0) (h r : ℝ) : ℝ :=
  ∫ x, tiltedSech4Value r x ∂gaussianReal h v

private lemma continuous_tiltedSech4Average (v : ℝ≥0) (h : ℝ) :
    Continuous (tiltedSech4Average v h) := by
  rw [continuous_iff_continuousAt]
  intro r₀
  unfold tiltedSech4Average
  let C : ℝ := Real.exp (-r₀ / 2) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hexp : ∀ᶠ r in nhds r₀, Real.exp (-r / 2) < C := by
    have ht : Filter.Tendsto (fun r : ℝ => Real.exp (-r / 2)) (nhds r₀)
        (nhds (Real.exp (-r₀ / 2))) := by
      exact (Real.continuous_exp.comp (by fun_prop :
        Continuous fun r : ℝ => -r / 2)).continuousAt.tendsto
    exact ht.eventually (Iio_mem_nhds (by dsimp [C]; linarith))
  have hmeas : ∀ᶠ r in nhds r₀,
      AEStronglyMeasurable (tiltedSech4Value r) (gaussianReal h v) := by
    exact Filter.Eventually.of_forall fun r =>
      (continuous_tiltedSech4Value r).aestronglyMeasurable
  have hbound : ∀ᶠ r in nhds r₀, ∀ᵐ x ∂gaussianReal h v,
      ‖tiltedSech4Value r x‖ ≤ C := by
    filter_upwards [hexp] with r hr
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]
      exact (abs_tiltedSech4Value_le_exp r x).trans hr.le
  have hlim : ∀ᵐ x ∂gaussianReal h v,
      Filter.Tendsto (fun r => tiltedSech4Value r x) (nhds r₀)
        (nhds (tiltedSech4Value r₀ x)) := by
    exact ae_of_all _ fun x => (continuous_tiltedSech4Value_time x).continuousAt.tendsto
  exact tendsto_integral_filter_of_dominated_convergence
    (l := nhds r₀) (F := fun r x => tiltedSech4Value r x)
    (f := tiltedSech4Value r₀) (bound := fun _ => C)
    hmeas hbound (integrable_const C) hlim

private lemma tiltedSech4Average_hasDerivAt {v : ℝ≥0} {h r : ℝ} (hr : 0 < r) :
    HasDerivAt (tiltedSech4Average v h)
      (∫ x, (1 / 2) * Real.exp (-r / 2) * sech x *
        (smoothSech3Second r x - smoothSech3 r x) ∂gaussianReal h v) r := by
  unfold tiltedSech4Average
  let F : ℝ → ℝ → ℝ := fun t x => tiltedSech4Value t x
  let F' : ℝ → ℝ → ℝ := fun t x =>
    (1 / 2) * Real.exp (-t / 2) * sech x *
      (smoothSech3Second t x - smoothSech3 t x)
  have hhalf : 0 < r / 2 := by linarith
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal h v) (F := F) (F' := F') (x₀ := r)
    (s := Set.Ioi (r / 2)) (bound := fun _ => (7 : ℝ))
    (Ioi_mem_nhds (by linarith))
    (Filter.Eventually.of_forall fun t =>
      (continuous_tiltedSech4Value t).aestronglyMeasurable)
    (by
      apply Integrable.of_bound (C := 1)
      · exact (continuous_tiltedSech4Value r).aestronglyMeasurable
      · filter_upwards [] with x
        simpa [Real.norm_eq_abs] using abs_tiltedSech4Value_le_one (x := x) hr.le)
    (by
      apply Continuous.aestronglyMeasurable
      dsimp [F']
      exact ((((continuous_const.mul continuous_const).mul continuous_sech).mul
        ((continuous_smoothSech3Second r).sub (continuous_smoothSech3 r)))))
    (by
      filter_upwards [] with x
      intro t ht
      have ht0 : 0 ≤ t := (lt_trans hhalf ht).le
      dsimp [F']
      rw [abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
        abs_of_pos (Real.exp_pos _), abs_of_pos (sech_pos _)]
      have he : Real.exp (-t / 2) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by linarith)
      have hd : |smoothSech3Second t x - smoothSech3 t x| ≤ 13 := by
        calc
          _ ≤ |smoothSech3Second t x| + |smoothSech3 t x| := abs_sub _ _
          _ ≤ 12 + 1 := by
            gcongr
            · exact abs_smoothSech3Second_le_twelve t x
            · exact abs_smoothSech3_le_one t x
          _ = 13 := by norm_num
      have hp : (1 / 2) * Real.exp (-t / 2) * sech x ≤ (1 / 2) * 1 * 1 := by
        have h₁ : (1 / 2) * Real.exp (-t / 2) ≤ (1 / 2) * 1 :=
          mul_le_mul_of_nonneg_left he (by norm_num)
        exact mul_le_mul h₁ (sech_le_one x) (sech_pos x).le (by norm_num)
      calc
        (1 / 2) * Real.exp (-t / 2) * sech x *
            |smoothSech3Second t x - smoothSech3 t x| ≤
            ((1 : ℝ) / 2 * 1 * 1) * 13 := by
              exact mul_le_mul hp hd (abs_nonneg _)
                (by norm_num)
        _ ≤ 7 := by norm_num)
    (integrable_const 7)
    (by
      filter_upwards [] with x
      intro t ht
      exact tiltedSech4Value_hasDerivAt_r (x := x) (lt_trans hhalf ht))
  simpa [F, F'] using h.2

private lemma tiltedSech4Average_deriv_generator {v : ℝ≥0} {h r : ℝ} (hr : 0 < r) :
    HasDerivAt (tiltedSech4Average v h)
      (∫ x, (1 / 2) * tiltedSech4Second r x +
        Real.tanh x * tiltedSech4First r x ∂gaussianReal h v) r := by
  apply (tiltedSech4Average_hasDerivAt (v := v) (h := h) hr).congr_deriv
  apply integral_congr_ae
  filter_upwards [] with x
  exact (tiltedSech4_generator r x).symm

private lemma gaussian_shift_integral (v : ℝ≥0) (h : ℝ) {f : ℝ → ℝ}
    (hf : Continuous f) :
    (∫ y, f (h + y) ∂gaussianReal 0 v) = ∫ x, f x ∂gaussianReal h v := by
  have hmap : Measure.map (fun y : ℝ => h + y) (gaussianReal 0 v) = gaussianReal h v := by
    simpa using gaussianReal_map_const_add (μ := 0) (v := v) h
  calc
    (∫ y, f (h + y) ∂gaussianReal 0 v) =
        ∫ x, f x ∂Measure.map (fun y : ℝ => h + y) (gaussianReal 0 v) := by
          rw [integral_map (by fun_prop) hf.aestronglyMeasurable]
    _ = ∫ x, f x ∂gaussianReal h v := by rw [hmap]

private lemma tiltedSech4_gaussian_ibp {v : ℝ≥0} (hv : v ≠ 0) {h r : ℝ} (hr : 0 ≤ r) :
    (∫ x, (x - h) * tiltedSech4First r x ∂gaussianReal h v) =
      (v : ℝ) * ∫ x, tiltedSech4Second r x ∂gaussianReal h v := by
  let F : ℝ → ℝ := fun y => tiltedSech4First r (h + y)
  have hcont : ContDiff ℝ 1 F :=
    (contDiff_tiltedSech4First r).comp (by fun_prop)
  have hmod : HasModerateGrowth F := tiltedSech4First_shift_moderate hr h
  have hibp := gaussianReal_integration_by_parts (v := v) hv hcont hmod
  have hderiv : deriv F = fun y => tiltedSech4Second r (h + y) := by
    funext y
    simpa [F, Function.comp_def] using
      ((tiltedSech4First_hasDerivAt_x r (h + y)).comp y
        ((hasDerivAt_id y).const_add h)).deriv
  rw [hderiv] at hibp
  have hleft := gaussian_shift_integral v h
    (f := fun x => (x - h) * tiltedSech4First r x)
    ((continuous_id.sub continuous_const).mul (continuous_tiltedSech4First r))
  have hright := gaussian_shift_integral v h
    (f := tiltedSech4Second r) (continuous_tiltedSech4Second r)
  rw [← hleft, ← hright]
  simpa [F, mul_assoc] using hibp

private lemma integrable_tiltedSech4Second (v : ℝ≥0) (h r : ℝ) (hr : 0 ≤ r) :
    Integrable (tiltedSech4Second r) (gaussianReal h v) := by
  apply Integrable.of_bound (C := 20)
  · exact (continuous_tiltedSech4Second r).aestronglyMeasurable
  · filter_upwards [] with x
    simpa [Real.norm_eq_abs] using abs_tiltedSech4Second_le_twenty (x := x) hr

private lemma integrable_tanh_mul_tiltedSech4First
    (v : ℝ≥0) (h r : ℝ) (hr : 0 ≤ r) :
    Integrable (fun x => Real.tanh x * tiltedSech4First r x) (gaussianReal h v) := by
  apply Integrable.of_bound (C := 4)
  · exact ((((Real.contDiff_sinh (n := (0 : WithTop ℕ∞))).continuous.div
        (Real.contDiff_cosh (n := (0 : WithTop ℕ∞))).continuous
        (fun x => (Real.cosh_pos x).ne')).congr
          (fun x => (Real.tanh_eq_sinh_div_cosh x).symm)).mul
      (continuous_tiltedSech4First r)).aestronglyMeasurable
  · filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |Real.tanh x| * |tiltedSech4First r x| ≤ 1 * 4 :=
        mul_le_mul (abs_tanh_le_one x)
          (abs_tiltedSech4First_le_four (x := x) hr) (abs_nonneg _) (by norm_num)
      _ = 4 := by norm_num

private lemma integrable_centered_mul_tiltedSech4First
    {v : ℝ≥0} (hv : v ≠ 0) (h r : ℝ) (hr : 0 ≤ r) :
    Integrable (fun x => (x - h) * tiltedSech4First r x) (gaussianReal h v) := by
  let F : ℝ → ℝ := fun y => tiltedSech4First r (h + y)
  have hFcont : ContDiff ℝ 1 F :=
    (contDiff_tiltedSech4First r).comp (by fun_prop)
  have hFderiv : deriv F = fun y => tiltedSech4Second r (h + y) := by
    funext y
    simpa [F, Function.comp_def] using
      ((tiltedSech4First_hasDerivAt_x r (h + y)).comp y
        ((hasDerivAt_id y).const_add h)).deriv
  have hpair : Integrable (fun y => y * F y) (gaussianReal 0 v) :=
    ((tiltedSech4First_shift_moderate hr h).integrable_pair
      hFcont.continuous.aestronglyMeasurable
      (by rw [hFderiv]; exact
        ((continuous_tiltedSech4Second r).comp (by fun_prop)).aestronglyMeasurable)).1
  have hcont : Continuous (fun x => (x - h) * tiltedSech4First r x) :=
    (continuous_id.sub continuous_const).mul (continuous_tiltedSech4First r)
  have hmap : Measure.map (fun y : ℝ => h + y) (gaussianReal 0 v) = gaussianReal h v := by
    simpa using gaussianReal_map_const_add (μ := 0) (v := v) h
  rw [← hmap, integrable_map_measure hcont.aestronglyMeasurable (by fun_prop)]
  refine hpair.congr (ae_of_all _ fun y => ?_)
  dsimp [F, Function.comp_def]
  ring

private lemma tiltedSech4Average_deriv_drift {v : ℝ≥0} (hv : v ≠ 0)
    {h r : ℝ} (hr : 0 < r) :
    HasDerivAt (tiltedSech4Average v h)
      (∫ x, (Real.tanh x + (x - h) / (2 * (v : ℝ))) * tiltedSech4First r x
        ∂gaussianReal h v) r := by
  have hvR : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  have hsecond := integrable_tiltedSech4Second v h r hr.le
  have htanh := integrable_tanh_mul_tiltedSech4First v h r hr.le
  have hcenter := integrable_centered_mul_tiltedSech4First hv h r hr.le
  apply (tiltedSech4Average_deriv_generator (v := v) (h := h) hr).congr_deriv
  rw [integral_add (hsecond.const_mul (1 / 2)) htanh, integral_const_mul]
  have hscaled : Integrable
      (fun x => (2 * (v : ℝ))⁻¹ * ((x - h) * tiltedSech4First r x))
      (gaussianReal h v) := hcenter.const_mul _
  rw [show (∫ x, (Real.tanh x + (x - h) / (2 * (v : ℝ))) *
      tiltedSech4First r x ∂gaussianReal h v) =
      (∫ x, Real.tanh x * tiltedSech4First r x ∂gaussianReal h v) +
      ∫ x, (2 * (v : ℝ))⁻¹ * ((x - h) * tiltedSech4First r x)
        ∂gaussianReal h v by
    rw [← integral_add htanh hscaled]
    apply integral_congr_ae
    filter_upwards [] with x
    field_simp
    <;> ring]
  rw [integral_const_mul]
  have hibp := tiltedSech4_gaussian_ibp hv (h := h) hr.le
  rw [hibp]
  field_simp
  ring

private lemma hasDerivAt_tanh (x : ℝ) :
    HasDerivAt Real.tanh (sech x ^ 2) x := by
  rw [show Real.tanh = fun y => Real.sinh y / Real.cosh y by
    funext y
    exact Real.tanh_eq_sinh_div_cosh y]
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x)
    (Real.cosh_pos x).ne'
  apply h.congr_deriv
  unfold sech
  rw [show Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x =
    Real.cosh x ^ 2 - Real.sinh x ^ 2 by ring]
  rw [Real.cosh_sq_sub_sinh_sq]
  field_simp

private lemma tanh_le_self {x : ℝ} (hx : 0 ≤ x) : Real.tanh x ≤ x := by
  let f : ℝ → ℝ := fun y => y - Real.tanh y
  have hfcont : Continuous f := continuous_id.sub continuous_tanh
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (D := Set.Ici 0) (convex_Ici 0) hfcont.continuousOn
    · intro y hy
      exact ((hasDerivAt_id y).sub (hasDerivAt_tanh y)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [show deriv f y = 1 - sech y ^ 2 by
        exact ((hasDerivAt_id y).sub (hasDerivAt_tanh y)).deriv]
      nlinarith [sech_pos y, sech_le_one y]
  have h := hmono (by simp) hx hx
  simpa [f] using h

private lemma tanh_monotone : Monotone Real.tanh := by
  have hmono : MonotoneOn Real.tanh Set.univ := by
    apply monotoneOn_of_deriv_nonneg (D := Set.univ) convex_univ
      continuous_tanh.continuousOn
    · intro x hx
      exact (hasDerivAt_tanh x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hasDerivAt_tanh x).deriv]
      positivity
  intro x y hxy
  exact hmono (by simp) (by simp) hxy

private lemma gaussianPDFReal_diff_sum_ratio {v : ℝ≥0} (hv : v ≠ 0)
    (h x : ℝ) :
    (gaussianPDFReal h v x - gaussianPDFReal h v (-x)) /
        (gaussianPDFReal h v x + gaussianPDFReal h v (-x)) =
      Real.tanh (h * x / (v : ℝ)) := by
  have hvR : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  rw [div_eq_iff (add_pos (gaussianPDFReal_pos h v x hv)
    (gaussianPDFReal_pos h v (-x) hv)).ne']
  rw [Real.tanh_eq, div_mul_eq_mul_div,
    eq_div_iff (add_pos (Real.exp_pos _) (Real.exp_pos _)).ne']
  have hcross :
      Real.exp (-((x - h) ^ 2) / (2 * (v : ℝ))) *
          Real.exp (-(h * x / (v : ℝ))) =
        Real.exp (-((-x - h) ^ 2) / (2 * (v : ℝ))) *
          Real.exp (h * x / (v : ℝ)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp
    ring
  unfold gaussianPDFReal
  linear_combination 2 * (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * hcross

private lemma tiltedSech4_drift_pair_nonpos {v : ℝ≥0} (hv : v ≠ 0)
    {h r x : ℝ} (hr : 0 ≤ r) (hh : 0 ≤ h) (hhv : h < (v : ℝ)) (hx : 0 ≤ x) :
    gaussianPDFReal h v x *
          ((Real.tanh x + (x - h) / (2 * (v : ℝ))) * tiltedSech4First r x) +
        gaussianPDFReal h v (-x) *
          ((Real.tanh (-x) + (-x - h) / (2 * (v : ℝ))) * tiltedSech4First r (-x)) ≤ 0 := by
  let A := gaussianPDFReal h v x
  let B := gaussianPDFReal h v (-x)
  let a := h * x / (v : ℝ)
  have hvpos : 0 < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hsum : 0 < A + B := add_pos (gaussianPDFReal_pos h v x hv)
    (gaussianPDFReal_pos h v (-x) hv)
  have hratio : A - B = (A + B) * Real.tanh a := by
    calc
      A - B = Real.tanh a * (A + B) := by
        apply (div_eq_iff hsum.ne').mp
        simpa [A, B, a] using gaussianPDFReal_diff_sum_ratio hv h x
      _ = (A + B) * Real.tanh a := by ring
  have ha : 0 ≤ a := div_nonneg (mul_nonneg hh hx) hvpos.le
  have hcoef : 0 ≤ h / (2 * (v : ℝ)) := div_nonneg hh (by positivity)
  have ha_le_x : a ≤ x := by
    dsimp [a]
    apply (div_le_iff₀ hvpos).2
    nlinarith
  have htanh_mono : Real.tanh a ≤ Real.tanh x := tanh_monotone ha_le_x
  have htanh_a_nonneg : 0 ≤ Real.tanh a := by
    rw [Real.tanh_eq_sinh_div_cosh]
    positivity
  have htanh_x : 0 ≤ Real.tanh x := by
    rw [Real.tanh_eq_sinh_div_cosh]
    positivity
  have hcoef_le_one : h / (2 * (v : ℝ)) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (v : ℝ))).2
    nlinarith
  have hmul : h / (2 * (v : ℝ)) * Real.tanh a ≤ Real.tanh x := by
    simpa using mul_le_mul hcoef_le_one htanh_mono htanh_a_nonneg (by norm_num : (0 : ℝ) ≤ 1)
  have hinside : 0 ≤ Real.tanh x + x / (2 * (v : ℝ)) -
      h / (2 * (v : ℝ)) * Real.tanh a := by
    have hxterm : 0 ≤ x / (2 * (v : ℝ)) := div_nonneg hx (by positivity)
    linarith
  have hbracket : 0 ≤
      A * (Real.tanh x + (x - h) / (2 * (v : ℝ))) +
        B * (Real.tanh x + (x + h) / (2 * (v : ℝ))) := by
    rw [show A * (Real.tanh x + (x - h) / (2 * (v : ℝ))) +
          B * (Real.tanh x + (x + h) / (2 * (v : ℝ))) =
        (A + B) * (Real.tanh x + x / (2 * (v : ℝ))) -
          h / (2 * (v : ℝ)) * (A - B) by
        field_simp
        ring,
      hratio]
    rw [show (A + B) * (Real.tanh x + x / (2 * (v : ℝ))) -
          h / (2 * (v : ℝ)) * ((A + B) * Real.tanh a) =
        (A + B) * (Real.tanh x + x / (2 * (v : ℝ)) -
          h / (2 * (v : ℝ)) * Real.tanh a) by ring]
    exact mul_nonneg hsum.le hinside
  have hg : tiltedSech4First r x ≤ 0 := tiltedSech4First_nonpos hr hx
  rw [tiltedSech4First_neg, Real.tanh_neg]
  change A * ((Real.tanh x + (x - h) / (2 * (v : ℝ))) *
      tiltedSech4First r x) +
    B * ((-Real.tanh x + (-x - h) / (2 * (v : ℝ))) *
      -tiltedSech4First r x) ≤ 0
  rw [show A * ((Real.tanh x + (x - h) / (2 * (v : ℝ))) *
        tiltedSech4First r x) +
      B * ((-Real.tanh x + (-x - h) / (2 * (v : ℝ))) *
        -tiltedSech4First r x) =
    (A * (Real.tanh x + (x - h) / (2 * (v : ℝ))) +
      B * (Real.tanh x + (x + h) / (2 * (v : ℝ)))) *
        tiltedSech4First r x by ring]
  exact mul_nonpos_of_nonneg_of_nonpos hbracket hg

private lemma tiltedSech4_drift_integral_nonpos {v : ℝ≥0} (hv : v ≠ 0)
    {h r : ℝ} (hr : 0 ≤ r) (hh : 0 ≤ h) (hhv : h < (v : ℝ)) :
    (∫ x, (Real.tanh x + (x - h) / (2 * (v : ℝ))) * tiltedSech4First r x
      ∂gaussianReal h v) ≤ 0 := by
  let b : ℝ → ℝ := fun x =>
    (Real.tanh x + (x - h) / (2 * (v : ℝ))) * tiltedSech4First r x
  have htanh := integrable_tanh_mul_tiltedSech4First v h r hr
  have hcenter := integrable_centered_mul_tiltedSech4First hv h r hr
  have hscaled : Integrable
      (fun x => (2 * (v : ℝ))⁻¹ * ((x - h) * tiltedSech4First r x))
      (gaussianReal h v) := hcenter.const_mul _
  have hb : Integrable b (gaussianReal h v) := by
    refine (htanh.add hscaled).congr (ae_of_all _ fun x => ?_)
    dsimp [b]
    field_simp
  have hbvol : Integrable (fun x => gaussianPDFReal h v x * b x) := by
    rw [gaussianReal_of_var_ne_zero h hv] at hb
    have hs := (integrable_withDensity_iff_integrable_smul'
      (measurable_gaussianPDF h v) (ae_of_all _ fun x => gaussianPDF_lt_top)).mp hb
    simpa [toReal_gaussianPDF, smul_eq_mul] using hs
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  rw [integral_eq_integral_Ioi_add_neg hbvol]
  apply integral_nonpos_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact tiltedSech4_drift_pair_nonpos hv hr hh hhv hx.le

private lemma tiltedSech4Average_deriv_nonpos {v : ℝ≥0} (hv : v ≠ 0)
    {h r : ℝ} (hr : 0 < r) (hh : 0 ≤ h) (hhv : h < (v : ℝ)) :
    deriv (tiltedSech4Average v h) r ≤ 0 := by
  rw [(tiltedSech4Average_deriv_drift hv hr).deriv]
  exact tiltedSech4_drift_integral_nonpos hv hr.le hh hhv

private lemma tiltedSech4Average_antitone {v : ℝ≥0} (hv : v ≠ 0)
    {h : ℝ} (hh : 0 ≤ h) (hhv : h < (v : ℝ)) :
    AntitoneOn (tiltedSech4Average v h) (Set.Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (D := Set.Ici 0) (convex_Ici 0)
    (continuous_tiltedSech4Average v h).continuousOn
  · intro r hr
    have hrpos : 0 < r := by simpa using hr
    exact (tiltedSech4Average_deriv_drift hv hrpos).differentiableAt.differentiableWithinAt
  · intro r hr
    have hrpos : 0 < r := by simpa using hr
    exact tiltedSech4Average_deriv_nonpos hv hrpos hh hhv

private lemma smoothSech3_zero (x : ℝ) : smoothSech3 0 x = sech3 x := by
  unfold smoothSech3 standardGaussianExpectation
  simp

private lemma tiltedSech4Value_zero (x : ℝ) : tiltedSech4Value 0 x = sech4 x := by
  unfold tiltedSech4Value sech4
  rw [smoothSech3_zero]
  simp [sech3]
  ring

private lemma tiltedSech4Average_le_zero {v : ℝ≥0} (hv : v ≠ 0)
    {h r : ℝ} (hr : 0 ≤ r) (hh : 0 ≤ h) (hhv : h < (v : ℝ)) :
    tiltedSech4Average v h r ≤ ∫ x, sech4 x ∂gaussianReal h v := by
  have hanti := tiltedSech4Average_antitone hv hh hhv
  calc
    tiltedSech4Average v h r ≤ tiltedSech4Average v h 0 :=
      hanti (by simp) hr hr
    _ = ∫ x, sech4 x ∂gaussianReal h v := by
      unfold tiltedSech4Average
      apply integral_congr_ae
      filter_upwards [] with x
      exact tiltedSech4Value_zero x

private noncomputable def sech2 (x : ℝ) : ℝ := sech x ^ 2

private noncomputable def sech2Deriv (x : ℝ) : ℝ :=
  -2 * sech2 x * Real.tanh x

private lemma sech2_hasDerivAt (x : ℝ) : HasDerivAt sech2 (sech2Deriv x) x := by
  apply ((sech_hasDerivAt x).pow 2).congr_deriv
  unfold sech2Deriv sech2
  norm_num
  ring

private lemma continuous_sech2 : Continuous sech2 := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (sech2_hasDerivAt x).continuousAt

private lemma sech2_abs_le_one (x : ℝ) : |sech2 x| ≤ 1 := by
  unfold sech2
  rw [abs_pow]
  exact pow_le_one₀ (abs_nonneg _) (abs_sech_le_one x)

private lemma sech2Deriv_abs_le_two (x : ℝ) : |sech2Deriv x| ≤ 2 := by
  unfold sech2Deriv
  rw [abs_mul, abs_mul, abs_neg]
  norm_num
  calc
    2 * |sech2 x| * |Real.tanh x| ≤ 2 * 1 * 1 := by
      gcongr
      · exact sech2_abs_le_one x
      · exact abs_tanh_le_one x
    _ = 2 := by norm_num

private lemma continuous_sech2Deriv : Continuous sech2Deriv := by
  unfold sech2Deriv
  exact (continuous_const.mul continuous_sech2).mul continuous_tanh

private noncomputable def gaussianSech2 (v : ℝ≥0) (a : ℝ) : ℝ :=
  standardGaussianExpectation (fun z => sech2 (a + Real.sqrt (v : ℝ) * z))

private lemma gaussianSech2_hasDerivAt (v : ℝ≥0) (a : ℝ) :
    HasDerivAt (gaussianSech2 v)
      (standardGaussianExpectation (fun z =>
        sech2Deriv (a + Real.sqrt (v : ℝ) * z))) a := by
  unfold gaussianSech2 standardGaussianExpectation
  let F : ℝ → ℝ → ℝ := fun b z => sech2 (b + Real.sqrt (v : ℝ) * z)
  let F' : ℝ → ℝ → ℝ := fun b z => sech2Deriv (b + Real.sqrt (v : ℝ) * z)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (F := F) (F' := F') (x₀ := a)
    (s := Set.univ) (bound := fun _ => (2 : ℝ)) (by simp)
    (Filter.Eventually.of_forall fun b =>
      (continuous_sech2.comp (by fun_prop)).aestronglyMeasurable)
    (by
      apply Integrable.of_bound (C := 1)
      · exact (continuous_sech2.comp (by fun_prop)).aestronglyMeasurable
      · filter_upwards [] with z
        simpa [F, Real.norm_eq_abs] using
          sech2_abs_le_one (a + Real.sqrt (v : ℝ) * z))
    (by
      dsimp [F', sech2Deriv]
      exact ((continuous_const.mul (continuous_sech2.comp (by fun_prop))).mul
        (continuous_tanh.comp (by fun_prop))).aestronglyMeasurable)
    (by
      filter_upwards [] with z
      intro b hb
      simpa [F', Real.norm_eq_abs] using
        sech2Deriv_abs_le_two (b + Real.sqrt (v : ℝ) * z))
    (integrable_const 2)
    (by
      filter_upwards [] with z
      intro b hb
      simpa [F, F', Function.comp_def] using
        (sech2_hasDerivAt _).comp b
          ((hasDerivAt_id b).add_const (Real.sqrt (v : ℝ) * z)))
  simpa [F, F'] using h.2

private lemma continuous_gaussianSech2 (v : ℝ≥0) : Continuous (gaussianSech2 v) := by
  rw [continuous_iff_continuousAt]
  intro a
  exact (gaussianSech2_hasDerivAt v a).continuousAt

private lemma gaussianSech2_deriv_nonpos {v : ℝ≥0} (hv : v ≠ 0)
    {a : ℝ} (ha : 0 ≤ a) : deriv (gaussianSech2 v) a ≤ 0 := by
  rw [(gaussianSech2_hasDerivAt v a).deriv]
  unfold standardGaussianExpectation
  have hshift :
      (∫ z, sech2Deriv (a + Real.sqrt (v : ℝ) * z) ∂gaussianReal 0 1) =
        ∫ y, sech2Deriv y ∂gaussianReal a v := by
    have h := standard_affine_integral_eq_gaussian
      (show 0 ≤ (v : ℝ) from v.2) a continuous_sech2Deriv
    have hvEq : (⟨(v : ℝ), v.2⟩ : ℝ≥0) = v := NNReal.eq rfl
    simpa [hvEq] using h
  rw [hshift, integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  have hvol : Integrable (fun y => gaussianPDFReal a v y * sech2Deriv y) := by
    apply Integrable.mono' ((integrable_gaussianPDFReal a v).const_mul 2)
    · exact ((measurable_gaussianPDFReal a v).mul
        ((continuous_const.mul continuous_sech2).mul continuous_tanh).measurable)
        |>.aestronglyMeasurable
    · filter_upwards [] with y
      have hp := gaussianPDFReal_nonneg a v y
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp]
      calc
        gaussianPDFReal a v y * |sech2Deriv y| ≤ gaussianPDFReal a v y * 2 :=
          mul_le_mul_of_nonneg_left (sech2Deriv_abs_le_two y) hp
        _ = 2 * gaussianPDFReal a v y := by ring
  rw [integral_eq_integral_Ioi_add_neg hvol]
  apply integral_nonpos_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hy0 : 0 ≤ y := hy.le
  have hD : sech2Deriv y ≤ 0 := by
    unfold sech2Deriv
    have ht : 0 ≤ Real.tanh y := by
      rw [Real.tanh_eq_sinh_div_cosh]
      positivity
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg _)) ht
  have hp := gaussianPDFReal_neg_le_self hv ha hy0
  change gaussianPDFReal a v y * sech2Deriv y +
    gaussianPDFReal a v (-y) * sech2Deriv (-y) ≤ 0
  have hDneg : sech2Deriv (-y) = -sech2Deriv y := by
    unfold sech2Deriv sech2
    rw [sech_neg, Real.tanh_neg]
    ring
  rw [hDneg]
  nlinarith [mul_nonpos_of_nonpos_of_nonneg hD (sub_nonneg.mpr hp)]

private lemma gaussianSech2_antitone {v : ℝ≥0} (hv : v ≠ 0) :
    AntitoneOn (gaussianSech2 v) (Set.Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (D := Set.Ici 0) (convex_Ici 0)
    (continuous_gaussianSech2 v).continuousOn
  · intro a ha
    exact (gaussianSech2_hasDerivAt v a).differentiableAt.differentiableWithinAt
  · intro a ha
    have ha0 : 0 < a := by simpa using ha
    exact gaussianSech2_deriv_nonpos hv ha0.le

private lemma gaussianSech2_eq_integral (v : ℝ≥0) (a : ℝ) :
    gaussianSech2 v a = ∫ x, sech2 x ∂gaussianReal a v := by
  unfold gaussianSech2 standardGaussianExpectation
  have h := standard_affine_integral_eq_gaussian
    (show 0 ≤ (v : ℝ) from v.2) a continuous_sech2
  have hvEq : (⟨(v : ℝ), v.2⟩ : ℝ≥0) = v := NNReal.eq rfl
  simpa [hvEq] using h

private lemma integrable_tanh_gaussian (v : ℝ≥0) (h : ℝ) :
    Integrable Real.tanh (gaussianReal h v) := by
  apply Integrable.of_bound (C := 1)
  · exact continuous_tanh.aestronglyMeasurable
  · filter_upwards [] with x
    simpa [Real.norm_eq_abs] using abs_tanh_le_one x

private lemma integrable_tanh_sq_gaussian (v : ℝ≥0) (h : ℝ) :
    Integrable (fun x => Real.tanh x ^ 2) (gaussianReal h v) := by
  apply Integrable.of_bound (C := 1)
  · exact (continuous_tanh.pow 2).aestronglyMeasurable
  · filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (abs_tanh_le_one x)

private lemma nishimori_tanh_identity {v : ℝ≥0} (hv : v ≠ 0) :
    (∫ x, Real.tanh x ∂gaussianReal (v : ℝ) v) =
      ∫ x, Real.tanh x ^ 2 ∂gaussianReal (v : ℝ) v := by
  have hvol₁ : Integrable
      (fun x => gaussianPDFReal (v : ℝ) v x * Real.tanh x) := by
    apply Integrable.mono' (integrable_gaussianPDFReal (v : ℝ) v)
    · exact ((measurable_gaussianPDFReal (v : ℝ) v).mul
        continuous_tanh.measurable).aestronglyMeasurable
    · filter_upwards [] with x
      have hp := gaussianPDFReal_nonneg (v : ℝ) v x
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp]
      exact mul_le_of_le_one_right hp (abs_tanh_le_one x)
  have hvol₂ : Integrable
      (fun x => gaussianPDFReal (v : ℝ) v x * Real.tanh x ^ 2) := by
    apply Integrable.mono' (integrable_gaussianPDFReal (v : ℝ) v)
    · exact ((measurable_gaussianPDFReal (v : ℝ) v).mul
        (continuous_tanh.pow 2).measurable).aestronglyMeasurable
    · filter_upwards [] with x
      have hp := gaussianPDFReal_nonneg (v : ℝ) v x
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp, abs_pow]
      exact mul_le_of_le_one_right hp
        (pow_le_one₀ (abs_nonneg _) (abs_tanh_le_one x))
  rw [integral_gaussianReal_eq_integral_smul hv,
    integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  rw [integral_eq_integral_Ioi_add_neg hvol₁,
    integral_eq_integral_Ioi_add_neg hvol₂]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hvR : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  have hratio := gaussianPDFReal_diff_sum_ratio hv (v : ℝ) x
  have harg : (v : ℝ) * x / (v : ℝ) = x := by field_simp
  rw [harg] at hratio
  have hsum : 0 < gaussianPDFReal (v : ℝ) v x +
      gaussianPDFReal (v : ℝ) v (-x) :=
    add_pos (gaussianPDFReal_pos (v : ℝ) v x hv)
      (gaussianPDFReal_pos (v : ℝ) v (-x) hv)
  have hdiff : gaussianPDFReal (v : ℝ) v x -
      gaussianPDFReal (v : ℝ) v (-x) =
      (gaussianPDFReal (v : ℝ) v x + gaussianPDFReal (v : ℝ) v (-x)) *
        Real.tanh x := by
    calc
      _ = Real.tanh x * (gaussianPDFReal (v : ℝ) v x +
          gaussianPDFReal (v : ℝ) v (-x)) :=
        (div_eq_iff hsum.ne').mp hratio
      _ = _ := by ring
  rw [Real.tanh_neg]
  linear_combination hdiff * Real.tanh x

private lemma sech2_add_tanh_sq (x : ℝ) : sech2 x + Real.tanh x ^ 2 = 1 := by
  unfold sech2 sech
  rw [Real.tanh_eq_sinh_div_cosh]
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  field_simp [hc]
  nlinarith [Real.cosh_sq_sub_sinh_sq x]

private lemma tanh_shift_moderate (v : ℝ) :
    HasModerateGrowth (fun y => Real.tanh (v + y)) := by
  refine ⟨1, 0, by norm_num, ?_, ?_⟩
  · intro y
    simpa using (abs_tanh_le_one (v + y)).trans_eq (by norm_num)
  · intro y
    have hderiv : deriv (fun y => Real.tanh (v + y)) y = sech2 (v + y) := by
      simpa [Function.comp_def, sech2] using
        ((hasDerivAt_tanh (v + y)).comp y ((hasDerivAt_id y).const_add v)).deriv
    rw [hderiv]
    unfold sech2
    rw [abs_of_pos (sq_pos_of_pos (sech_pos (v + y)))]
    exact (pow_le_one₀ (sech_pos _).le (sech_le_one _)).trans_eq (by norm_num)

private lemma gaussian_tanh_ibp {v : ℝ≥0} (hv : v ≠ 0) :
    (∫ x, (x - (v : ℝ)) * Real.tanh x ∂gaussianReal (v : ℝ) v) =
      (v : ℝ) * ∫ x, sech2 x ∂gaussianReal (v : ℝ) v := by
  let F : ℝ → ℝ := fun y => Real.tanh ((v : ℝ) + y)
  have haff : ContDiff ℝ ⊤ (fun y : ℝ => (v : ℝ) + y) :=
    contDiff_const.add contDiff_id
  have hcont : ContDiff ℝ 1 F :=
    (contDiff_tanh.comp haff).of_le (by simp)
  have hibp := gaussianReal_integration_by_parts hv hcont (tanh_shift_moderate (v : ℝ))
  have hderiv : deriv F = fun y => sech2 ((v : ℝ) + y) := by
    funext y
    simpa [F, Function.comp_def, sech2] using
      ((hasDerivAt_tanh ((v : ℝ) + y)).comp y
        ((hasDerivAt_id y).const_add (v : ℝ))).deriv
  rw [hderiv] at hibp
  have hleft := gaussian_shift_integral v (v : ℝ)
    (f := fun x => (x - (v : ℝ)) * Real.tanh x)
    ((continuous_id.sub continuous_const).mul continuous_tanh)
  have hright := gaussian_shift_integral v (v : ℝ)
    (f := sech2) continuous_sech2
  rw [← hleft, ← hright]
  simpa [F] using hibp

private lemma gaussian_sq_moment (v : ℝ≥0) :
    (∫ x, x ^ 2 ∂gaussianReal (v : ℝ) v) = (v : ℝ) + (v : ℝ) ^ 2 := by
  have h := variance_eq_sub (memLp_id_gaussianReal (μ := (v : ℝ)) (v := v) 2)
  have hvar : Var[id; gaussianReal (v : ℝ) v] = (v : ℝ) := by
    simpa using (variance_fun_id_gaussianReal (μ := (v : ℝ)) (v := v))
  rw [hvar] at h
  simp only [Pi.pow_apply, id_eq, integral_id_gaussianReal] at h
  nlinarith

private lemma gaussian_sech2_integral_eq_one_sub_tanh_sq (v : ℝ≥0) (h : ℝ) :
    (∫ x, sech2 x ∂gaussianReal h v) =
      1 - ∫ x, Real.tanh x ^ 2 ∂gaussianReal h v := by
  have hs : Integrable sech2 (gaussianReal h v) := by
    apply Integrable.of_bound (C := 1)
    · exact continuous_sech2.aestronglyMeasurable
    · filter_upwards [] with x
      simpa [Real.norm_eq_abs] using sech2_abs_le_one x
  have ht := integrable_tanh_sq_gaussian v h
  have hsum := integral_add hs ht
  have hone : (∫ x, sech2 x + Real.tanh x ^ 2 ∂gaussianReal h v) = 1 := by
    calc
      _ = ∫ _x : ℝ, (1 : ℝ) ∂gaussianReal h v := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact sech2_add_tanh_sq x
      _ = 1 := by simp
  rw [hone] at hsum
  linarith

private lemma integrable_id_mul_tanh_gaussian (v : ℝ≥0) (h : ℝ) :
    Integrable (fun x => x * Real.tanh x) (gaussianReal h v) := by
  have hx : Integrable (fun x : ℝ => x) (gaussianReal h v) :=
    (memLp_id_gaussianReal (μ := h) (v := v) 1).integrable (by simp)
  exact hx.mul_bdd continuous_tanh.aestronglyMeasurable
    (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using abs_tanh_le_one x)

private lemma gaussian_xtanh_moment {v : ℝ≥0} (hv : v ≠ 0) :
    (∫ x, x * Real.tanh x ∂gaussianReal (v : ℝ) v) = (v : ℝ) := by
  have hxt := integrable_id_mul_tanh_gaussian v (v : ℝ)
  have ht := integrable_tanh_gaussian v (v : ℝ)
  have hcenter : Integrable
      (fun x => (x - (v : ℝ)) * Real.tanh x) (gaussianReal (v : ℝ) v) := by
    refine (hxt.sub (ht.const_mul (v : ℝ))).congr (ae_of_all _ fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  have hdecomp :
      (∫ x, x * Real.tanh x ∂gaussianReal (v : ℝ) v) =
        (∫ x, (x - (v : ℝ)) * Real.tanh x ∂gaussianReal (v : ℝ) v) +
          (v : ℝ) * ∫ x, Real.tanh x ∂gaussianReal (v : ℝ) v := by
    rw [← integral_const_mul]
    rw [← integral_add hcenter (ht.const_mul (v : ℝ))]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  rw [hdecomp, gaussian_tanh_ibp hv, nishimori_tanh_identity hv,
    gaussian_sech2_integral_eq_one_sub_tanh_sq]
  ring

private lemma gaussianSech2_diagonal_bound {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianSech2 v (v : ℝ) ≤ 1 / (1 + (v : ℝ)) := by
  have hvpos : 0 < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  let c : ℝ := 1 / (1 + (v : ℝ))
  let Q : ℝ := ∫ x, Real.tanh x ^ 2 ∂gaussianReal (v : ℝ) v
  have ht2 := integrable_tanh_sq_gaussian v (v : ℝ)
  have hxt := integrable_id_mul_tanh_gaussian v (v : ℝ)
  have hx2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal (v : ℝ) v) :=
    (memLp_id_gaussianReal (μ := (v : ℝ)) (v := v) 2).integrable_sq
  have hexpanded :
      (∫ x, (Real.tanh x - c * x) ^ 2 ∂gaussianReal (v : ℝ) v) =
        Q - 2 * c * (∫ x, x * Real.tanh x ∂gaussianReal (v : ℝ) v) +
          c ^ 2 * ∫ x, x ^ 2 ∂gaussianReal (v : ℝ) v := by
    have hmid : Integrable (fun x => (2 * c) * (x * Real.tanh x))
        (gaussianReal (v : ℝ) v) := hxt.const_mul _
    have hlast : Integrable (fun x => c ^ 2 * x ^ 2)
        (gaussianReal (v : ℝ) v) := hx2.const_mul _
    calc
      (∫ x, (Real.tanh x - c * x) ^ 2 ∂gaussianReal (v : ℝ) v) =
          ∫ x, Real.tanh x ^ 2 - (2 * c) * (x * Real.tanh x) +
            c ^ 2 * x ^ 2 ∂gaussianReal (v : ℝ) v := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ =
          (∫ x, Real.tanh x ^ 2 ∂gaussianReal (v : ℝ) v) -
            (∫ x, (2 * c) * (x * Real.tanh x) ∂gaussianReal (v : ℝ) v) +
              ∫ x, c ^ 2 * x ^ 2 ∂gaussianReal (v : ℝ) v := by
        calc
          (∫ x, Real.tanh x ^ 2 - (2 * c) * (x * Real.tanh x) +
              c ^ 2 * x ^ 2 ∂gaussianReal (v : ℝ) v) =
              (∫ x, Real.tanh x ^ 2 - (2 * c) * (x * Real.tanh x)
                ∂gaussianReal (v : ℝ) v) +
                ∫ x, c ^ 2 * x ^ 2 ∂gaussianReal (v : ℝ) v :=
            integral_add (ht2.sub hmid) hlast
          _ = _ := by rw [integral_sub ht2 hmid]
      _ = _ := by
        rw [integral_const_mul, integral_const_mul]
  have hnonneg : 0 ≤ ∫ x, (Real.tanh x - c * x) ^ 2
      ∂gaussianReal (v : ℝ) v := by
    apply integral_nonneg
    intro x
    exact sq_nonneg _
  rw [hexpanded, gaussian_xtanh_moment hv, gaussian_sq_moment] at hnonneg
  have hQ : (v : ℝ) / (1 + (v : ℝ)) ≤ Q := by
    dsimp [c] at hnonneg
    field_simp at hnonneg
    apply (div_le_iff₀ (by linarith : 0 < 1 + (v : ℝ))).2
    nlinarith
  rw [gaussianSech2_eq_integral,
    gaussian_sech2_integral_eq_one_sub_tanh_sq]
  change 1 - Q ≤ 1 / (1 + (v : ℝ))
  have hid : 1 - (v : ℝ) / (1 + (v : ℝ)) = 1 / (1 + (v : ℝ)) := by
    field_simp
    ring
  linarith

private lemma field_lt_beta_sq_mul_rsQ {β h s : ℝ}
    (hβ : 0 < β) (hh : 0 < h) (hs : s ≤ 1)
    (hlarge : 1 < s * β ^ 2 * (1 - rsQ β h)) :
    h < β ^ 2 * rsQ β h := by
  let q : ℝ := rsQ β h
  have hqpos : 0 < q := by
    exact rsQ_pos hβ hh
  have hqle : q ≤ 1 := by
    exact (rsQ_mem_Icc β h).2
  have hrnonneg : 0 ≤ β ^ 2 * q :=
    mul_nonneg (sq_nonneg β) hqpos.le
  have hrpos : 0 < β ^ 2 * q :=
    mul_pos (sq_pos_of_pos hβ) hqpos
  let v : ℝ≥0 := ⟨β ^ 2 * q, hrnonneg⟩
  have hvpos : 0 < v := by
    change 0 < β ^ 2 * q
    exact hrpos
  have hv : v ≠ 0 := hvpos.ne'
  have hsqrt : Real.sqrt (β ^ 2 * q) = β * Real.sqrt q := by
    rw [Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq_eq_abs, abs_of_pos hβ]
  have hqgauss :
      q = ∫ x, Real.tanh x ^ 2 ∂gaussianReal h v := by
    have hfp := rsQ_eq_gaussian_tanh_sq (β := β) hh
    have haffine := standard_affine_integral_eq_gaussian
      hrnonneg h (continuous_tanh.pow 2)
    calc
      q = ∫ z, Real.tanh (h + β * Real.sqrt q * z) ^ 2
          ∂gaussianReal 0 1 := by
        simpa [q, standardGaussianExpectation] using hfp
      _ = ∫ x, Real.tanh x ^ 2 ∂gaussianReal h v := by
        simpa only [hsqrt, Pi.pow_apply, v] using haffine
  have hsech : gaussianSech2 v h = 1 - q := by
    rw [gaussianSech2_eq_integral,
      gaussian_sech2_integral_eq_one_sub_tanh_sq, ← hqgauss]
  by_contra hnot
  have hrh : (v : ℝ) ≤ h := by
    change β ^ 2 * q ≤ h
    exact le_of_not_gt hnot
  have hmon : gaussianSech2 v h ≤ gaussianSech2 v (v : ℝ) :=
    (gaussianSech2_antitone hv) (by simp) hh.le hrh
  have hsech_le : 1 - q ≤ 1 / (1 + (v : ℝ)) := by
    rw [← hsech]
    exact hmon.trans (gaussianSech2_diagonal_bound hv)
  have hdenpos : 0 < 1 + (v : ℝ) := by positivity
  have hproduct : (1 - q) * (1 + (v : ℝ)) ≤ 1 :=
    (le_div_iff₀ hdenpos).mp hsech_le
  have hvcoe : (v : ℝ) = β ^ 2 * q := rfl
  rw [hvcoe] at hproduct
  have hbasic : β ^ 2 * (1 - q) ≤ 1 := by
    nlinarith
  have hbasic_nonneg : 0 ≤ β ^ 2 * (1 - q) :=
    mul_nonneg (sq_nonneg β) (sub_nonneg.mpr hqle)
  have hsbound : s * (β ^ 2 * (1 - q)) ≤ β ^ 2 * (1 - q) :=
    by simpa only [one_mul] using mul_le_mul_of_nonneg_right hs hbasic_nonneg
  change 1 < s * β ^ 2 * (1 - q) at hlarge
  nlinarith

private lemma continuous_sech4 : Continuous sech4 := by
  unfold sech4
  exact continuous_sech.pow 4

private lemma tiltedHeatSemigroup_sech4_eq (r x : ℝ) :
    tiltedHeatSemigroup r sech4 x = tiltedSech4Value r x := by
  have hpoint : (fun y => sech4 y * Real.cosh y) = sech3 := by
    funext y
    unfold sech4 sech3 sech
    have hc : Real.cosh y ≠ 0 := (Real.cosh_pos y).ne'
    field_simp [hc]
  unfold tiltedHeatSemigroup heatSemigroup tiltedSech4Value smoothSech3
  rw [hpoint]
  unfold sech
  rw [div_eq_mul_inv]

private lemma heatSemigroup_tiltedSech4_eq_average
    (v : ℝ≥0) (h r : ℝ) :
    heatSemigroup (v : ℝ) (tiltedHeatSemigroup r sech4) h =
      tiltedSech4Average v h r := by
  have hfun : tiltedHeatSemigroup r sech4 = tiltedSech4Value r := by
    funext x
    exact tiltedHeatSemigroup_sech4_eq r x
  rw [hfun]
  unfold heatSemigroup standardGaussianExpectation tiltedSech4Average
  let hvnonneg : 0 ≤ (v : ℝ) := v.2
  have hgauss := standard_affine_integral_eq_gaussian hvnonneg h
    (continuous_tiltedSech4Value r)
  have hvsub : (⟨(v : ℝ), hvnonneg⟩ : ℝ≥0) = v := by
    apply NNReal.eq
    rfl
  rw [hvsub] at hgauss
  exact hgauss

private lemma heatSemigroup_sech4_eq_integral (v : ℝ≥0) (h : ℝ) :
    heatSemigroup (v : ℝ) sech4 h =
      ∫ x, sech4 x ∂gaussianReal h v := by
  unfold heatSemigroup standardGaussianExpectation
  let hvnonneg : 0 ≤ (v : ℝ) := v.2
  have hgauss := standard_affine_integral_eq_gaussian hvnonneg h continuous_sech4
  have hvsub : (⟨(v : ℝ), hvnonneg⟩ : ℝ≥0) = v := by
    apply NNReal.eq
    rfl
  rw [hvsub] at hgauss
  exact hgauss

private lemma tiltedSech4Average_zero (v : ℝ≥0) (h : ℝ) :
    tiltedSech4Average v h 0 = ∫ x, sech4 x ∂gaussianReal h v := by
  unfold tiltedSech4Average
  apply integral_congr_ae
  filter_upwards [] with x
  exact tiltedSech4Value_zero x

private lemma atParameter_eq_beta_sq_mul_gaussian_sech4
    {β h : ℝ} (hβ : 0 < β) (hh : 0 < h) :
    let q := rsQ β h
    let v : ℝ≥0 := ⟨β ^ 2 * q,
      mul_nonneg (sq_nonneg β) (rsQ_mem_Icc β h).1⟩
    atParameter β h = β ^ 2 * ∫ x, sech4 x ∂gaussianReal h v := by
  let q : ℝ := rsQ β h
  have hqnonneg : 0 ≤ q := (rsQ_mem_Icc β h).1
  let v : ℝ≥0 := ⟨β ^ 2 * q, mul_nonneg (sq_nonneg β) hqnonneg⟩
  have hsqrt : Real.sqrt (β ^ 2 * q) = β * Real.sqrt q := by
    rw [Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq_eq_abs, abs_of_pos hβ]
  have haffine := standard_affine_integral_eq_gaussian
    (mul_nonneg (sq_nonneg β) hqnonneg) h continuous_sech4
  rw [atParameter_eq_beta_sq_mul_gaussian_sech_fourth hβ hh]
  congr 1
  unfold standardGaussianExpectation
  simpa only [sech4, sech, q, hsqrt, v] using haffine

/-- Above the replica-symmetric breakpoint, the interpolated fourth local-field
moment is bounded by the Almeida-Thouless parameter. -/
theorem upperComparison {β h s u : ℝ}
    (hβ : 0 < β) (hh : 0 < h) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hu : u ∈ Set.Icc (rsQ β h) 1)
    (hlarge : 1 < s * β ^ 2 * (1 - rsQ β h)) :
    β ^ 2 * localFieldExpectation β h (rsQ β h) s u
      (fun x => (Real.cosh x)⁻¹ ^ 4) ≤ atParameter β h := by
  let q : ℝ := rsQ β h
  have hqnonneg : 0 ≤ q := (rsQ_mem_Icc β h).1
  let v : ℝ≥0 := ⟨β ^ 2 * q, mul_nonneg (sq_nonneg β) hqnonneg⟩
  let r : ℝ := s * β ^ 2 * (u - q)
  have hvpos : 0 < v := by
    change 0 < β ^ 2 * q
    exact mul_pos (sq_pos_of_pos hβ) (rsQ_pos hβ hh)
  have hv : v ≠ 0 := hvpos.ne'
  have hr : 0 ≤ r := by
    exact mul_nonneg (mul_nonneg hs.1 (sq_nonneg β))
      (sub_nonneg.mpr hu.1)
  have hhv : h < (v : ℝ) := by
    change h < β ^ 2 * q
    exact field_lt_beta_sq_mul_rsQ hβ hh hs.2 hlarge
  have hlocal :
      localFieldExpectation β h q s u sech4 =
        tiltedSech4Average v h r := by
    unfold localFieldExpectation
    by_cases huq : u ≤ q
    · have hueq : u = q := le_antisymm huq hu.1
      subst u
      rw [if_pos le_rfl]
      have hvariance : β ^ 2 * ((1 - s) * q + s * q) = (v : ℝ) := by
        change β ^ 2 * ((1 - s) * q + s * q) = β ^ 2 * q
        ring
      have hrzero : r = 0 := by
        dsimp [r]
        ring
      rw [hvariance, heatSemigroup_sech4_eq_integral, hrzero,
        tiltedSech4Average_zero]
    · rw [if_neg huq]
      have hvariance : β ^ 2 * q = (v : ℝ) := rfl
      rw [hvariance]
      exact heatSemigroup_tiltedSech4_eq_average v h r
  change β ^ 2 * localFieldExpectation β h q s u sech4 ≤ atParameter β h
  rw [hlocal, atParameter_eq_beta_sq_mul_gaussian_sech4 hβ hh]
  exact mul_le_mul_of_nonneg_left
    (tiltedSech4Average_le_zero hv hr hh.le hhv) (sq_nonneg β)

end SpinGlass.AT
