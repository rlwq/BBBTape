# Формулы

## Машина

Программы $P$ — термы грамматики

$$
P ::= \varepsilon \mid {<}P \mid {>}P \mid {*}P \mid [P]\,P
$$

Машина $m = (t, p)$: лента $t$ и оставшаяся программа $p$.
Начальная машина программы $p$: $\mathrm{init}(p) = (\mathrm{blank}, p)$.

Шаг:

$$
\begin{aligned}
\mathrm{step}(t, \varepsilon) &= (t, \varepsilon) \\
\mathrm{step}(t, {<}p) &= (\mathrm{moveL}\,t,\ p) \\
\mathrm{step}(t, {>}p) &= (\mathrm{moveR}\,t,\ p) \\
\mathrm{step}(t, {*}p) &= (\mathrm{flip}\,t,\ p) \\
\mathrm{step}(t, [b]\,p) &=
  \begin{cases}
    (t,\ b \mathbin{+\!\!+} [b]\,p) & \text{если } t.\mathrm{head} = 1 \\
    (t,\ p) & \text{иначе}
  \end{cases}
\end{aligned}
$$

$\mathrm{run}_n = \mathrm{step}^n$.

## Остановка

$$
\begin{aligned}
\mathrm{halted}(m) &\iff m.\mathrm{program} = \varepsilon \\
\mathrm{halts}(m) &\iff \exists n,\ \mathrm{halted}(\mathrm{run}_n\, m) \\
\mathrm{haltsIn}(m, k) &\iff \mathrm{halted}(\mathrm{run}_k\, m) \land \forall j < k,\ \lnot\,\mathrm{halted}(\mathrm{run}_j\, m)
\end{aligned}
$$

## Busy Beaver

$E_n$ — все программы длины $n$ (`Program.enumerate n`).

$$
\mathrm{BB}(n) = s \iff
\big(\exists p \in E_n,\ \mathrm{haltsIn}(\mathrm{init}\,p, s)\big) \land
\big(\forall p \in E_n,\ \forall k,\ \mathrm{haltsIn}(\mathrm{init}\,p, k) \to k \le s\big)
$$

## Децайдеры

Децайдер $d : \mathrm{Machine} \to \{\mathrm{halts}, \mathrm{nonhalts}, \mathrm{unknown}\}$ с условиями корректности:

$$
d(m) = \mathrm{halts} \to \mathrm{halts}(m), \qquad
d(m) = \mathrm{nonhalts} \to \lnot\,\mathrm{halts}(m)
$$

Моноид $(\mathrm{Decider},\ {<|>},\ \mathbf{0})$, где $\mathbf{0}(m) = \mathrm{unknown}$:

$$
(d_1 <|> d_2)(m) =
\begin{cases}
  d_2(m) & \text{если } d_1(m) = \mathrm{unknown} \\
  d_1(m) & \text{иначе}
\end{cases}
$$

$$
\mathbf{0} <|> d = d, \qquad d <|> \mathbf{0} = d, \qquad
(a <|> b) <|> c = a <|> (b <|> c)
$$

## Результаты

$$
\forall p \in E_0,\ \mathrm{halts}(\mathrm{init}\,p), \qquad
\forall p \in E_1,\ \mathrm{halts}(\mathrm{init}\,p)
$$
