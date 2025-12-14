#import "@preview/ctheorems:1.1.3": *
#show: thmrules.with(qed-symbol: $square.filled$)

#set par(
  first-line-indent: 1em,
  leading: 0.8em,
  linebreaks: "simple",
)
#set align(left)

#set page(
  margin: 1.5cm,
  // footer-descent: 20%,
)

#set text(
  font: "TeX Gyre Pagella",
  size: 12pt,
)
#show math.equation: set text(font: "TeX Gyre Pagella Math")
#show raw: set text(font: "TeX Gyre Pagella Math")

#show link: set text(fill: gray)
#show link: underline

#set align(left)

#set heading(numbering: "1.1")

#set page(footer: context [
  #let elems = query(
    selector(heading).before(here()),
  )
  #let subsection = elems.last().body
  #let num = counter(heading).display(elems.last().numbering)

  // #text(num, size: 8pt)
  // #text(subsection, size: 8pt)
  #h(1fr)
  #text(
    counter(page).display(
      "1",
      // both: true,
    ),
    size: 8pt,
  )
])




#let remark = thmbox(
  "remark",
  "Remark",
  stroke: none,
  inset: (top: 0.4em, left: .5em, right: .5em, bottom: 0.6em),
  base_level: 1,
  padding: (top: 0pt, bottom: -4pt),
)


#let proof = thmproof(
  "proof",
  text(
    smallcaps("Proof"),
    // highlight("Proof", fill: white, stroke: black, top-edge: "cap-height", extent: 3pt),
    style: "oblique",
    weight: "regular",
  ),
  inset: (top: 0em, left: 2.8em, right: 1.4em),
  separator: [#h(0.1em). #h(0.2em)],
  // bodyfmt: body => [
  //   #set align(left)
  //   #body
  // ],
  breakable: true,
)

#let solution = thmproof(
  "solution",
  text(
    // "Solution",
    smallcaps("Solution"),
    style: "oblique",
    // weight: "bold",
    // fill: rgb("#6c71c4"),
  ),
  namefmt: name => text(smallcaps([#name]), size: 10pt),
  inset: (top: 0.5em, left: 1em, right: 1.4em, bottom: .5em),
  separator: [#h(0.1em). #h(0.2em)],
  fill: rgb("#f2f2f2"),
  // bodyfmt: body => [
  //   #set align(left)
  //   #body
  // ],
  breakable: true,
)


#let hard = text(fill: red, $star.filled$)



= Some Exercises in Real Analysis

== (Sequences)
1. Prove the following sequential limits: $ a) lim_(n -> infinity) (sin(n))/n = 0, quad b) lim_(n -> infinity) (n!)/(n^n) = 0, quad c) lim_(n->infinity) (1 + 2 + dots.c + n)^2/n^4 = 1/4. $
Try proving in multiple ways ($N-epsilon$, squeeze theorem, etc).\
_(Hint (for b)): how many times does $n$ appear in "$n!$"? How about "$n^n$"?)_

2. The following sequences are defined recursively. Prove that each converges, and find the limiting value in each case.$ a) quad & x_1 := sqrt(2), x_(n + 1) := sqrt(2 + x_n) "for" n >= 1 \
   b)quad & x_1 = 2, x_(n + 1) := 1/2 (x_n + 2/(x_n)) \
  c) quad & x_1 := 1, x_2 := 2, x_(n + 1) := 1/2 (x_n + x_(n - 1)) \
  d) quad & x_1 = 1, x_(n + 1) = sin(x_n) $_(Hint: if $lim_n x_n = L,$ then what is $lim_n x_(n - 1)$?)_

3. Prove that, for $b in RR$ with $b > 0$, $x_n := n/(b^n)$ converges to $0$ if $b > 1$ and properly diverges to $+infinity$ if $b <= 1$.
4. Prove that $ x_n := 1 + 1/(2^2) + dots.c + 1/(n^2) := sum_(k=0)^n 1/(k^2) $ converges (don't try to find the limiting value).

5. Let $x_1 in RR$ be nonzero, and define inductively $x_(n+ 1) := x_n + 1/(x_n)$. Prove that $ lim_(n -> infinity) x_n = cases(
    +infinity quad & x_1 > 0,
    - infinity quad & x_1 < 0
  ). $

6. Let ${x_n} subset RR$ converge to $x in RR$, with $x_n > 0$ for all $n$. Prove that both the sequence of _arithmetic means_ $ y_n := 1/n (x_1 + dots.c + x_n) $ and the sequence of _geometric means_ $ z_n := (x_1 x_2 dots.c x_n)^(1\/n) $ converge to $x$.
== (Functional Limits/Continuity)

1. #hard Let $f : RR -> RR$ satisfy the following:\
  i. $f(x + y) = f(x) + f(y)$, for all $x, y in RR$,\
  ii. $f$ continuous at $0$\
  iii. $f(1) = 1$\
Prove that $f$ must be the identity function, i.e. $f(x) = x$ for all $x in RR$.\ _(Hint: begin by showing $f$ must be continuous everywhere in $RR$, and use this to prove the claim for $x in QQ$. Conclude by a density argument.)_

2. [Recall that a set $X subset RR$ is said to be _open_ if for every $x in X$, there exists an $epsilon > 0$ such that $(x - epsilon, x + epsilon) subset X$ (i.e., if a point is in $X$, so are all of its "neighboring" points for a sufficiently small neighborhood), and that a set $Y subset RR$ is said to be _closed_ if its complement $Y^C = RR \\ X$ is open.] \ Let $f : RR -> RR$ be continuous. Prove that $X := {x in RR | f(x) = 0}$ is a closed subset of $RR$.\ _(Bonus #hard: what can you say about the set $Y := {x : a <= f(x) < b}$ for some real numbers $a < b$? Can you find continuous functions $f$ such that $Y$ open, closed, both, and neither?)_

3. Compute the following functional limits using only the $epsilon$-$delta$/$epsilon$-$M$ definition:
$
  a) quad & lim_(x -> 1^+) (x/(x - 1)) \
  b) quad & lim_(x -> infinity) (sqrt(x + 1)/(x)) \
  c) quad & lim_(x -> infinity) (sqrt(x) -x)/(sqrt(x) + x)
$
4. Let $f : RR_+ -> RR$, where $RR_+ := {x in RR | x >= 0}$. Prove that, for some real number $L$, $ lim_(x -> infinity) f(x) = L <=> lim_(x -> 0^+) f(1/x) = L. $
5. We say a function $f : RR -> RR$ is _Lipschitz continuous_ if there exists a constant $K > 0$ such that $ abs(f(x) - f(y)) <= K abs(x - y), quad forall x, y in RR. $ Prove that if $f$ Lipschitz continuous, it is also _uniformly_ continuous. Can you find an example of a continuous function that isn't Lipschitz continuous?\ _(Bonus: prove that if $f : [a, b] -> RR$ is differentiable with continuous derivative, then $f$ is Lipschitz on $[a, b]$)_

6. Prove using the $delta$-$epsilon$ definition that the following functions are continuous on $RR$: $ a) thin f(x) := 1/(1 + x^2), quad b) thin f(x) := sqrt(x^2 + 1). $

7. #hard Let $f : RR_+ -> RR$ be continuous and bounded. Show that for any $T in RR$, there exists a sequence ${x_n} subset RR_+$ such that $lim_(n->infinity) x_n = + infinity$ and  $ lim_(n -> infinity) [f(x_n + T) - f(x_n)] = 0. $\ _(Hint: this one's very hard )_ // TODO

8. Let $f : [0, 1] -> RR$ be continuous, with $f(0) = 0 = f(1)$. Show that there must exist a $c in [0, 1/2]$ such that $f(c) = f(c + 1/2)$. \ _(Hint: don't reinvent the wheel; turn what you have into a wheel)_

9. Let $f : [0, 1] -> RR$ continuous, and suppose that for every $x in [0, 1]$, there exists a $y in [0, 1]$ such that $ abs(f(y)) <= 1/2 abs(f(x)). $ Prove that there exists a $c in [0, 1]$ such that $f(c) = 0$.

10. Prove that the function $ f(x) = cases(sin(1/x) quad & x eq.not 0, 0 & x = 0) $ is _not_ continuous at $x = 0$, using the sequential criterion for convergence.

11.
#pagebreak()
= Some Useful Inequalities to Remember
- *Triangle inequality:* $abs(x + y) <= abs(x) + abs(y), quad forall x, y in RR.$
  #proof[If $x$ or $y$ equals 0, or $x + y = 0$, this is clear If $x, y$ both positive, the claim holds with equality. If both negative, then since for any negative number $z < 0$ we have $abs(z) = - z$, we find that $abs(x + y) = - (x + y)$ on one side, and $abs(x) + abs(y) = -x + - y$ on the other, so equality also holds in this case. Finally, if one of $x, y$ negative and the other positive, wlog $x < 0$ and $y > 0$, then $ abs(x + y) = cases(
      y + x = abs(y) - abs(x) <= abs(y) + abs(x) quad & "if" y > abs(x),
      - y - x - abs(x) - abs(y) <= abs(y) + abs(x) quad & "if" y < abs(x)
    ) , $ proving the claim.
  ]
- *Reverse Triangle Inequality*: $abs(abs(x) - abs(y)) <= abs(x - y)$
#proof()[
  By the triangle inequality, we have both bounds $ abs(x) = abs(x -y + y) <= abs(x - y) + abs(y), quad abs(y) <= abs(x - y) + abs(x), $ from which, subtracting from both sides, $ - abs(x - y) <= abs(x) - abs(y) <= abs(x - y) => abs(abs(x) - abs(y)) <= abs(x - y). $
]
- *AM-GM Inequality (basic)*: $sqrt(a b) <= (a + b)/2, a, b in RR$ with $a, b >= 0$. #proof[
    Remark that $ #stack(spacing: 1em, $(a - b)^2 = a^2 - 2 a b + b^2$, $(a + b)^2 = a^2 + 2 a b + b^2$) #rotate(180deg, $cases("", "", "")$) => (a - b)^2 = (a + b)^2 - 4 a b. $ But also, $(a - b)^2 >= 0$, so this implies $ 0 <= (a + b)^2 - 4 a b => 4 a b <= (a + b)^2, $ which gives the claimed inequality upon taking square roots of both sides and dividing by two.
  ]

- *AM-GM Inequality (extended):* $(a_1 dots.c a_n)^(1\/n) <= (a_1 + dots.c + a_n)/n$, where $a_i in RR$ with $a_i >= 0$.
#pagebreak()
= Solutions

== Sequences

#solution("1")[
  $a)$ Remember that $abs(sin(x)) <= 1$ for all $x in RR$, thus $ 0 <= abs(sin(n)/n) <= 1/n. $ Since $1/n$ converges to zero, then by the squeeze theorem, so does $sin(n)/n$. \
  $b)$ We can write $ 0 <= (n!)/(n^n) & = (n dot (n - 1) dots.c (1))/(underbrace(n dots. n, n "times")) = underbrace(n/n, = 1) dot.c underbrace((n -1)/n, <= 1) dot underbrace((n - 2)/n, <= 1) dots.c (1)/n <= 1/n, $ so again $(n!)/(n^n)$ converges to zero by squeeze theorem.\
  $c)$ Remember that $1 + 2 + dots.c + n = ((n)(n+1))/2$, so that the sequence may be written $ (( 1 + 2 + dots.c + n)^2)/(n^4) = ((n)(n+1))^2/(4 n^4) = (n^2 (n^2 + 2 n + 1))/(4 n^4) \
  = (n^4 + 2 n^3 + n^2)/(4 n^4) = 1/4 + 1/(2 n) + 1/(4 n^2) -> 1/4. $
]

#solution("2")[
  $a)$ We prove $x_n$ is monotonically increasing and bounded from above, from which case convergence follows by the monotone convergence theorem. We prove both by induction. For increasing, the base case is clear, for $x_2 = sqrt(2 + sqrt(2)) > sqrt(2) = x_1$. Supposing this inequality holds for some $n$, i.e., $x_(n) >= x_(n - 1)$, we find that $ x_(n + 1) = sqrt(2 + x_n) >=^"induct" sqrt(2 + x_(n - 1)) =^"by def." x_n, $ so we have monotone increasing indeed. For boundedness, we claim $x_n <= 2$ for all $n >= 1$. The base case, for $n = 1$, is clear. Supposing $x_(n - 1) <= 2$, then $ x_n = sqrt(2 + x_(n-1)) <=^"induct" sqrt(2 + 2) = 2, $ so we indeed have boundedness of the whole sequence. Thus, we know $x_n$ converges; let $L$ be its limit. But then, we also know that $x_n = sqrt(2 + x_(n - 1))$, thus $ L = lim_(n) x_n = lim_n sqrt(2 + x_(n - 1)) =^(#stack("cnty of", "sqrt")) sqrt(2 + L). $ Squaring both sides, this means $ L^2 = L + 2, $ which one can solve to find two solutions, $L = 2$ and $L = -1$. But $x_n$ is a strictly positive, increasing sequence, so it can't have a negative limit, and thus we conclude $L = 2$.\
  $b)$ // TODO
  $c)$ // TODO
  $d)$ // TODO
]
#solution("3")[
  // TODO
]

#solution("4")[
  We will employ the Cauchy criterion to prove convergence. Let $epsilon > 0$ and fix $m > n >= N$ for some $N$ to be determined later. Then, $ abs(x_m - x_n) & = (1 + 1/(2^2) + dots.c + 1/m^2) - (1 + 1/2^2 + dots.c + 1/n^2) \
                 & =1/(n + 1)^2 +1/(n + 2)^2 + dots.c + 1/m^2 \
                 & <= 1/((n + 1) n) + 1/((n + 1) (n + 2)) + dots.c + 1/(m (m -1)) \
                 & = (1/n - 1/(n + 1)) + (1/(n + 1) - 1/(n + 2)) + dots.c + (1/m + 1/(m - 1)) \
                 & = 1/n - 1/m <= 1/N, $ so taking $N >= 1/epsilon$ will work to prove convergence.
  #remark[
    When I originally did this question, I immediately upper-bounded the second line by $(m - n)/((n + 1)^2) <= (m - n) epsilon$, which is _not_ good enough to prove the desired result.
  ]
]


#solution("5")[ // TODO
]

#solution("6")[
  We first prove for $y_n$. Let $epsilon > 0$. Since $x_n$ converges to $x$, there exists some $N_1$ such that $ n >= N_1 => abs(x_n - x) < epsilon/2 quad "(i)". $ Next, since $x_n$ convergent it must be bounded (check!) so there exists some $M > 0$ such that $abs(x_n - x) <= M$ for all $n in NN$. Finally, the sequence $1/n$ is convergent, so there exists an $N_2$ such that $ n >= N_2 => 1/n < epsilon/(2 M N_1). quad "(ii)" $ Let $N := max(N_1, N_2)$. Then, for $n >= N$, we can split our sequence as follows: $ abs(y_n - x) & = abs(x_1 + dots.c + x_N_1 + x_(N_1 + 1) + dots.c + x_n - n x)/n \
  & <= 1/n sum_(i=1)^(N_1) abs(x_i - x) + 1/n sum_(i=N_1 + 1)^n abs(x_i -x) \
  & <= underbrace(epsilon/(2 M N_1), "(ii)") dot underbrace(M N_1, "boundedness") + underbrace((n - (N_1 + 1))/n epsilon/2, "(i)") \
  & = (1 + underbrace((n - (N_1 + 1))/n, <= 1)) epsilon/2 \
  & <= 2 epsilon/2 = epsilon, $ which proves the claimed convergence.
]
== (Functional Limits/Continuity)

#solution(
  "1",
)[ We follow the hint. First, we show $f$ continuous everywhere. Before that, we note that $f(0) = 0$, for $ f(0) = f(0 + 0) = f(0) + f(0) => f(0) = 0, $ just by using the definition. Fix now $epsilon > 0$, and let $delta > 0$ such that $abs(x) < delta => abs(f(x) - f(0)) = abs(f(x)) < epsilon$, appealing to the assumed continuity of $f$ at $0$. Then, for any $x, y in RR$ with $abs(x - y) < delta$, we find $ abs(f(x) - f(y)) =^"definition" abs(f(x - y)) < epsilon, $ using the continuity assumption at the origin _(in particular, we have uniform convergence)_. \ Next, we prove the result for $q in QQ$. First, remark that for any positive integer $n$ and any $x in RR$, we have that $ f(n x) = f((n - 1) x + x) = f((n - 1)x) + f(x), $ but we can repeat this work for $f((n - 1) x)$, and we deduce that $f(n x) = n f(x)$. By similar reasoning, we can deduce that $f(n x) = n f(x)$ for any negative integer as well. For $q in QQ$, we can write $ q = a/b, $ where $a, b in ZZ$. From the previous line of reasoning, we see thus that $ f(a/b) = a dot f(1/b). $ But also, $ 1 = f(1) = f(b dot 1/b) = b f(1/b) => f(1/b) = 1/b, $ from which we conclude $ f(q) = f(a/b) = a/b = q $ indeed. This proves the conclusion for all rational numbers. Now, for any $x in RR$, let ${q_n}$ be a sequence of rational numbers converging to $x$, which must exist by the density of $QQ$ in $RR$. Then, by the continuity of $f$ we proved above, $ lim_n f(q_n) = f(x) $ on the one hand, but also, since $q_n in QQ$ for each $NN$, $ lim_n f(q_n) = lim_n q_n = x, $ from which we conclude $f(x) = x$ for all $x in RR$, as we aimed to show.
]

#solution("2")[
  We will equivalently show that $X^c = {f(x) eq.not 0}$ is open. Let $x in X^c$, and assume wlog that $f(x) > 0$ (if $f(x) < 0$, repeat the proof with $-f$ instead of $f$), and let $epsilon := f(x)/2$, which is strictly positive since $f(x) eq.not 0$. Since $f$ continuous, in particular, at $x$, there exists a $delta > 0$ such that if $abs(y - x) < delta$, then $abs(f(y) - f(x)) < epsilon$. But this means, for such $y$, $ abs(f(y) - f(x)) < epsilon & => (-f(x))/2 < f(y) - f(x) < f(x)/2 \
                             & =>f(x)/2 < f(y) < (3f(x))/2, $ which, since $f(x) > 0$, in particular implies that if $abs(y - x) < delta$, then $f(y) > 0$. This means that all such $y in X^c$ as well, i.e. $(x - delta, x + delta) subset X^c$, which is exactly the definition of openness. Thus, $X^c$ open and so $X$ closed.
]

#solution("3")[
  $a)$ We claim the given limit diverges properly to $+infinity$. Let $M > 0$, and let $delta := 1/M > 0$. Then, if $x$ is such that $0 < x - 1 < delta$, then in particular $x > 1$ and $1/(x - 1) > 1/(delta)$, from which we conclude $ x/(x - 1) > 1/(delta) = M, $ which proves the claim.

  $b)$ We claim the given limit is 0. Fix $epsilon > 0$. Note that if the function in question was just $sqrt(x)/(x)$, our job would be far easier, for this simplifies to $1/sqrt(x)$, so just taking $M := 1/epsilon^2$ would do the trick. So, inspired by this work, we can rewrite the function in question: $ f(x) := sqrt(x + 1)/x = sqrt(x)/x dot sqrt(x + 1)/sqrt(x) = 1/sqrt(x) sqrt(1 + 1/x). $ In particular, we've put all the $x$ dependence into denominators, which should always be a goal when proving something goes to zero. Let now $x > M$ with $M := 2/epsilon^2$, assuming without loss of generality that $epsilon < 1$ #footnote([This is wlog since what really matters in limit proofs is small $epsilon$; if you don't like this, you can instead take $ M = max(2/epsilon^2, 1), $  then in particular $1/M < 1$ and $1/sqrt(M) < (epsilon)/sqrt(2)$, then the proof follows identically.])  then $ f(x) < 1/sqrt(M) sqrt(1 + 1/M) = epsilon/sqrt(2) sqrt(1 + epsilon^2) < (epsilon)/sqrt(2) sqrt(2) = epsilon, $ so the proof follows.

  $c)$ Whenever you see ugly functions like this, you should always simplify (in the sense of getting rid of as many $x$'s as possible) before attempting anything. We see that: $ f(x) := (sqrt(x) - x)/(sqrt(x) + x) & = (- sqrt(x) + x + 2 sqrt(x))/(sqrt(x) + x) = -1 + 2 sqrt(x)/(sqrt(x) + x) = -1 + 2/(1 + sqrt(x)). $ In particular, we can see from here that $lim_(x -> infinity) f(x) = -1$; for $epsilon > 0$ (and less than $1$, wlog), let $M := (2/epsilon - 1)^2$, then for $x> M$, $ abs(f(x) - (-1)) & = 2/(1 + sqrt(x)) < 2/(1 + sqrt(M)) = epsilon, $ as we needed to show.
]

#solution(
  "4",
)[ Assume the first direction. Let $epsilon > 0$. By definition, there exists $M > 0$ such that $x > M$ implies $abs(f(x) - L) < epsilon$. Taking $delta := 1/M$, then, this implies that for all $y$ such that $0 < 1/y < 1/delta$, (viewing $x$ as $1/y$) we have $abs(f(1/y) - L) < epsilon$, which $lim_(x -> 0^+) f(1/x) = L$. The inverse implication is very similar.
]

#solution("5")[
  Let $epsilon > 0$ and let $delta := epsilon/K$. Then, $abs(x - y) < delta$ implies $abs(f(x) - f(y)) <= K abs(x - y) < K/K epsilon = epsilon$, so $f$ continuous (uniformly). The classic example of a non-Lipschitz but continuous function is $f(x) := x^2$ on $RR$; to see this, it suffices to take $y = 0$. Then, we see that $ abs(f(x) - f(y)) = x^2, $ so any Lipschitz constant would have to be proportional to $x$, which contradicts the uniformity definition.
]

#solution("6")[
  $a)$ Fix $epsilon > 0$, $x in RR$ and let $y$ such that $abs(x - y) < delta$, with $delta$ to be chosen. Note that this implies $y in (x - delta, x + delta)$, so $abs(y) <= abs(x) + delta$. Then: $ abs(f(x) - f(y)) & = abs(1/(1 + x^2) - 1/(1 + y^2)) \
                   & = abs(y^2 - x^2)/((1 + x^2) (1 + y^2)) \
                   & = (abs((y - x)(y + x)))/((1 + x^2)(1 + y^2)) \
                   & <= abs(y - x) abs(y + x) \
                   & < delta (abs(y) + abs(x)) < delta (delta + 2 abs(x)). $ If $x = 0$, then we can just take $delta = sqrt(epsilon)$. Else, $abs(x) > 0$, so that with the choice $ delta := delta(x, epsilon) = min{2 abs(x), epsilon/(4 abs(x))} > 0, $ we have that $delta < 2 abs(x)$ and $delta < epsilon/(4 abs(x))$, so that continuing our work above we get $ abs(f(x) - f(y)) < delta (delta + 2 abs(x)) < epsilon/(4 abs(x)) (4 abs(x)) = epsilon, $ as needed.

  $b)$ Let $epsilon > 0, x in RR$ and $y in RR$ such that $abs(x -y) < delta$ with $delta > 0$ to be chosen. By the reverse triangle inequality, $ abs(f(x) - f(y)) & = abs(sqrt(x^2 + 1) - sqrt(y^2 + 1)) <= sqrt(abs(x^2 - y^2)) = sqrt(abs(x - y)) sqrt(abs(x + y)) <= delta^(1/2) sqrt(2 abs(x) + delta). $ So, if $x = 0$, $delta = epsilon$ will work. Else, we can take $ delta := min{2 abs(x), (epsilon^2)/(4 abs(x))} > 0, $ then continuing form our work above, $ abs(f(x) - f(y)) <= delta^(1/2) sqrt(2 abs(x) + delta) <= delta^(1/2) 2 abs(x)^(1/2) < epsilon, $ as we needed to show.
]

#solution(
  "7",
)[ This is tricky. One way you can interpret the result is that, if $f$ a continuous and bounded function, then it must be "eventually periodic" with arbitrary period $T$; i.e., we can find some properly diverging sequence of ${x_n}$ such that $f(x_n + T) - f(x_n)$ converges to zero. \ With this interpretation, we fix $T in RR\\{0}$ (if $T = 0$ we're done) and let $g(x) := f(x + T) - f(x)$ for convenience. Consider the following three possibilities:\ (i) $f$ is identically zero outside of some bounded set, or $f$ decays to zero as $abs(x) -> infinity$, i.e. $lim_(x -> + infinity) f(x) = 0$; in either case, we can take $x_n := n$ and conclude (why?).  \ \ (ii) $g$ changes sign infinitely often for sufficiently large $x$, i.e. for all $n in NN$, there exists a $y_n > n$ such that $g(y_n) > 0 (< 0)$ iff $g(n) < 0 (> 0)$. In this case, we can construct an unbounded, increasing sequence ${y_n} subset RR$ such that ${g(y_n)}$ alternates sign, i.e. if $g(y_1) > 0$, then $g(y_2) < 0$, $g(y_3) > 0$, etc. Since $f$ continuous, then by the intermediate value theorem, then we can find a sequence ${x_n}$ such that: \ - $x_n in (y_n, y_(n + 1))$ for each $n in NN$ \ - $g(x_n) = 0$ for all $n in NN$ \ Moreover, this first condition implies $lim_n x_n >= lim_n y_n = infinity$, so ${x_n}$ also diverges to infinity. The second condition moreover gives that $f(x_n + T) - f(x_n) = 0$ identically, so the claim is proven. \ \ (iii) Finally, if neither of the two previous conditions are satisfied, then we know $g$ must eventually be strictly positive or negative, i.e. there must exist some sufficiently large $M > 0$ such that $x >= M => g(x) > 0$ or $g(x) < 0$ (indeed, if we couldn't find such an $M$, two cases would be possible: either $g$ identically zero beyond some sufficiently large value of $x$, in which case we enter case (i), or $g$ alternates sign infinitely often for large $x$, in which case we are in case (ii)). \ Suppose first $g(x) > 0$ for $x >= M$. This implies $f(x + T) > f(x)$; if $T > 0$, we can inductively argue then that $f(x + n T) > f(x)$ for all $n in NN$. So, if we define the sequence $x_n := M + (n - 1) T$, we conclude that $f(x_n) > f(x_(n - 1))$ for all $n in NN$. But then, ${f(x_n)}$ a bounded (by assumption, $f$ bounded) sequence which monotonically increases, so by the Monotone Convergence Theorem, we know $lim_(n) f(x_n)$ exists. In particular, this implies $ lim_n [f(x_n + T) - f(x_n)] = lim_(n) f(x_(n + 1)) - lim_n f(x_n) = 0, $ using our definition of $x_n$, which implies $x_(n + 1) = x_n + T$; so, we are done in this case. If on the other hand $T < 0$, then we similarly define $x_n := M - (n - 1) T$, and conclude similarly. Finally, if instead $g(x) < 0$ for $x >= M$, the same sequence gives rise to a monotonically decreasing sequence, and the conclusion is the same.
]

#solution(
  "8",
)[ Let $g(x) := f(x) - f(x + 1/2)$ for $x in [0, 1/2]$. Then, $g(0) = - f(1/2)$ and $g(1/2) = f(1/2)$; in particular, $g$ must change sign on the interval $[0, 1/2]$, for $g(0) = - g(1/2)$. Thus, there must exist a $c$ for which $g(c) = 0$, which, unravelling the definition of $g$, proves the assertion.
]

#solution(
  "9",
)[Let $x_1 in [0, 1]$ arbitrary. Let $x_2 in [0, 1]$ such that $abs(f(x_2)) <= 1/2 abs(f(x_1))$, which exists by hypothesis. Repeat this inductively, defining a sequence of ${x_n} subset [0, 1]$ such that $abs(f(x_(n+1))) <= 1/2 abs(f(x_n))$ for each $n >= 1$. In particular, ${x_n}$ a bounded sequence of real numbers, and thus by the Bolzano-Weierstrauss Theorem, there exists a point $c in [0, 1]$ and a subsequence ${x_n_k} subset {x_n}$ such that $x_n_k$ converges to $c$. By continuity, $f(x_n_k)$ converges to $f(c).$ In addition, we see that, applying the hypothesis inductively, $ abs(f(x_n)) <= 1/2 abs(f(x_(n-1))) <= (1/2)^2 abs(f(x_(n - 2))) <= dots.c <= (1/2)^(n - 1) abs(f(x_1)). $ Applying this bound to the subsequence, we conclude $ abs(f(x_n_k)) <= (1/2)^(n_k - 1) abs(f(x_1)), $ and, taking limits on both sides, we find $ abs(f(c)) <= abs(f(x_1)) lim_k (1/2)^(n_k - 1) = 0, $ hence $f(c) = 0$, as we aimed to find.]

#solution(
  "10",
)[To disprove continuity, we need to create a sequence ${x_n}$ that converges to zero, but for which $f(x_n)$ does not converge to $f(0) = 0$. Graphically, one can see that $sin(1/x)$ oscillates increasing wildly near the origin; one expects $sin(1/x)$ to hit 1, for instance, infinitely often as $x -> 0$. Concretely, consider the sequence $ x_n := 1/(pi/2 + 2pi n). $ One sees that $lim_n x_n =0$ (check), but since $x_n > 0$ for all $n$, $ f(x_n) = sin(pi/2 + 2pi n) = 1 $ for all $n$. So, $lim_n f(x_n) = 1 eq.not 0 = f(0)$, so $f$ cannot be continuous at zero. _(In fact, we for any $y in [-1, 1]$, we can take a sequence of the form $ x_n := 1/(c + 2 pi n) $ with $c := arcsin(y)$; then $lim_n f(x_n) = y$.)_]
