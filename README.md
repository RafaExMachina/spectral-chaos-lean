# Formalização em Lean dos resultados sobre densidade espectral de potência de sinais gerados por um sistema caótico linear por partes

Este projeto usa **Lean 4** e **Mathlib** para formalizar, verificar e certificar matematicamente resultados obtidos no artigo:

> **Rafael Alves da Costa; Marcio Eisencraft.**  
> *Spectral characteristics of a general piecewise linear chaotic signal generator.*  
> **Communications in Nonlinear Science and Numerical Simulation**, v. 72, p. 441–448, 2019.  
> DOI: https://doi.org/10.1016/j.cnsns.2019.01.002

O objetivo não é apenas reproduzir numericamente as fórmulas do artigo. A proposta é transformar parte da derivação matemática em **teoremas formais verificados pelo kernel do Lean**, de modo que cada transformação algébrica, argumento de convergência e manipulação de séries seja checada automaticamente.

---

## 1. Objetivo geral

O artigo estuda uma família geral de mapas caóticos lineares por partes e deriva expressões fechadas para a sequência de autocorrelação (ACS) e para a densidade espectral de potência (PSD) dos sinais gerados.

Nesta formalização, o foco inicial foi verificar formalmente a passagem entre os resultados centrais:

$$
R(k+1)=\psi R(k),
$$

$$
R(k)=\frac{1}{3}\psi^{|k|},
$$

e

$$
P(\omega)=\frac{1-\psi^2}{3\left(1-2\psi\cos(\omega)+\psi^2\right)}.
$$

No artigo, essas relações correspondem às equações **(17)**, **(18)** e **(19)**.

Além disso, foi formalizado um caso particular apresentado no artigo para \(r=3\), no qual

$$
\psi(\alpha)=\frac{1-2\alpha-\alpha^2}{2},
$$

e, para

$$
\alpha=\sqrt{2}-1,
$$

tem-se \(\psi=0\), o que conduz a um **espectro branco**.

---

## 2. Por que usar Lean?

Em uma demonstração matemática tradicional, os passos são validados por inspeção humana. Em Lean, cada etapa precisa ser expressa de maneira suficientemente precisa para que o kernel consiga verificar o termo de prova correspondente.

Isso oferece algumas vantagens importantes:

- elimina passos algébricos implícitos;
- torna explícitas hipóteses como \(|\psi|<1\);
- força a verificação da convergência das séries utilizadas;
- separa resultados auxiliares em lemas reutilizáveis;
- permite verificar simbolicamente identidades envolvendo números reais e complexos;
- fornece um artefato formal reprodutível complementar à demonstração publicada.

O Lean não substitui o raciocínio matemático do artigo. Ele atua como uma camada adicional de **verificação formal**.

---

## 3. Visão geral da formalização

O fluxo formalizado pode ser resumido assim:

```mermaid
flowchart TD
    A[Recorrência da autocorrelação<br/>R(k+1) = ψ R(k)]
    B[Forma fechada para k ≥ 0<br/>R(k) = 1/3 · ψ^k]
    C[Extensão bilateral<br/>R(k) = 1/3 · ψ^|k|]
    D[Definição da DTFT bilateral<br/>Σ R(k)e^(-ikω)]
    E[Convergência absoluta<br/>|ψ| < 1]
    F[Pareamento dos termos +n e -n]
    G[Série real de cossenos]
    H[Série geométrica complexa]
    I[Fórmula fechada da soma trigonométrica]
    J[PSD fechada<br/>(1-ψ²)/(3(1-2ψ cosω+ψ²))]

    A --> B
    B --> C
    C --> D
    D --> E
    E --> F
    F --> G
    H --> I
    I --> G
    G --> J
```

Também foi verificado o caso particular:

```mermaid
flowchart LR
    A[α = √2 - 1]
    B[ψ(α) = 0]
    C[P(ω) = 1/3]
    D[Espectro branco]

    A --> B --> C --> D
```

---

## 4. Estrutura matemática usada

### 4.1 Parâmetro espectral \(\psi\)

No artigo,

$$
\psi=\frac{1}{4}\sum_{j=1}^{r}\beta_j(\alpha_j-\alpha_{j-1})^2.
$$

Esse parâmetro controla diretamente a sequência de autocorrelação e a forma do espectro.

Na formalização atual, a derivação geral dessa expressão a partir de todos os segmentos do mapa ainda não foi formalizada integralmente. O trabalho atual concentra-se principalmente nas consequências matemáticas de \(\psi\) e na passagem ACS \(\rightarrow\) PSD.

---

### 4.2 Caso particular com \(r=3\)

Para o caso discutido no artigo,

$$
\psi(\alpha)=\frac{1-2\alpha-\alpha^2}{2}.
$$

Em Lean:

```lean
def psi3 (α : ℝ) : ℝ :=
  (1 - 2 * α - α ^ 2) / 2
```

Foi demonstrado formalmente:

```lean
theorem psi_zero_at_sqrt2_sub_one :
    psi3 (Real.sqrt 2 - 1) = 0 := by
  have hsqrt :
      (Real.sqrt (2 : ℝ)) ^ 2 = 2 := by
    norm_num
  unfold psi3
  nlinarith
```

Portanto,

$$
\psi(\sqrt{2}-1)=0.
$$

---

## 5. Formalização da PSD

A forma fechada da PSD usada no projeto é:

```lean

def PSD (ψ ω : ℝ) : ℝ :=
  (1 - ψ ^ 2) /
    (3 * (1 - 2 * Real.cos ω * ψ + ψ ^ 2))
```

Isto representa

$$
P(\omega)=\frac{1-\psi^2}{3(1-2\psi\cos\omega+\psi^2)}.
$$

Foi demonstrado, por exemplo, que \(\psi=0\) produz uma PSD constante:

```lean

theorem white_spectrum (ω : ℝ) :
    PSD 0 ω = (1 : ℝ) / 3 := by
  norm_num [PSD]
```

E combinando o resultado com \(\alpha=\sqrt2-1\):

```lean

theorem r3_white_spectrum (ω : ℝ) :
    PSD (psi3 (Real.sqrt 2 - 1)) ω =
      (1 : ℝ) / 3 := by
  rw [psi_zero_at_sqrt2_sub_one]
  exact white_spectrum ω
```

Logo,

$$
P(\omega)=\frac13\quad\forall\omega,
$$

formalizando o resultado de espectro branco desse caso particular.

---

## 6. Da recorrência à forma fechada da autocorrelação

Partindo das hipóteses

$$
R(0)=\frac13
$$

e

$$
R(k+1)=\psi R(k),
$$

foi usado o princípio de indução do Lean para provar:

$$
R(k)=\frac13\psi^k,
\qquad k\in\mathbb N.
$$

O teorema formal é:

```lean

theorem autocorrelation_closed_form
    (ψ : ℝ)
    (R : ℕ → ℝ)
    (h0 : R 0 = (1 : ℝ) / 3)
    (hrec : ∀ k : ℕ, R (k + 1) = ψ * R k) :
    ∀ k : ℕ, R k = ((1 : ℝ) / 3) * ψ ^ k := by
  intro k
  induction k with
  | zero =>
      simpa using h0
  | succ k ih =>
      calc
        R (Nat.succ k) = ψ * R k := by
          simpa [Nat.succ_eq_add_one] using hrec k
        _ = ψ * (((1 : ℝ) / 3) * ψ ^ k) := by
          rw [ih]
        _ = ((1 : ℝ) / 3) * ψ ^ (Nat.succ k) := by
          rw [pow_succ]
          ring
```

---

## 7. Extensão bilateral da autocorrelação

Para representar a equação (18) sobre os inteiros, foi definida:

```lean

def autocorrZ (ψ : ℝ) (k : ℤ) : ℝ :=
  (1 : ℝ) / 3 * ψ ^ k.natAbs
```

Assim,

$$
R(k)=\frac13\psi^{|k|}.
$$

A simetria da autocorrelação também foi verificada formalmente:

```lean

theorem autocorrZ_even
    (ψ : ℝ)
    (k : ℤ) :
    autocorrZ ψ (-k) = autocorrZ ψ k := by
  unfold autocorrZ
  simp
```

Portanto,

$$
\boxed{R(-k)=R(k)}.
$$

Essa propriedade é essencial para converter a DTFT bilateral em uma série envolvendo apenas cossenos.

---

## 8. Definição formal da DTFT

O termo individual da DTFT foi definido como:

```lean

def dtftTerm
    (ψ ω : ℝ)
    (k : ℤ) : ℂ :=
  (autocorrZ ψ k : ℂ) *
    Complex.exp
      (-Complex.I *
        (((k : ℝ) * ω : ℝ) : ℂ))
```

A DTFT bilateral é então:

```lean

def psdDTFT
    (ψ ω : ℝ) : ℂ :=
  ∑' k : ℤ, dtftTerm ψ ω k
```

que corresponde diretamente a

$$
P(\omega)
=
\sum_{k\in\mathbb Z}
R(k)e^{-ik\omega}.
$$

O termo central também foi verificado:

$$
T(0)=R(0)=\frac13.
$$

---

## 9. Série geométrica complexa

Para calcular a soma infinita, foi utilizado o número complexo

$$
q=\psi e^{i\omega}.
$$

Sob a hipótese

$$
|\psi|<1,
$$

tem-se

$$
|q|<1,
$$

e portanto a série geométrica converge:

$$
\sum_{n=0}^{\infty}q^n
=
\frac{1}{1-q}.
$$

A formalização usa resultados da Mathlib para séries geométricas em espaços normados.

Também foi provado:

$$
\operatorname{Re}
\left[(\psi e^{i\omega})^n\right]
=
\psi^n\cos(n\omega).
$$

Esse resultado permite converter a série geométrica complexa em uma soma trigonométrica real.

---

## 10. Soma trigonométrica geométrica

Foi formalmente demonstrado:

$$
\boxed{
\sum_{n=0}^{\infty}
\psi^n\cos(n\omega)
=
\frac{1-\psi\cos\omega}
{1-2\psi\cos\omega+\psi^2}
}
$$

para \(|\psi|<1\).

Em seguida, separando o termo \(n=0\), foi obtida a cauda:

$$
\boxed{
\sum_{n=1}^{\infty}
\psi^n\cos(n\omega)
=
\frac{\psi\cos\omega-\psi^2}
{1-2\psi\cos\omega+\psi^2}
}.
$$

Essa é a identidade central usada para transformar a série da PSD em sua forma racional fechada.

---

## 11. Convergência absoluta da DTFT

A formalização não apenas manipula a `tsum`; ela também verifica que a série bilateral é somável.

Para cada termo,

$$
\left|
\frac13\psi^{|k|}e^{-ik\omega}
\right|
=
\frac13|\psi|^{|k|},
$$

pois

$$
|e^{-ik\omega}|=1.
$$

Como \(|\psi|<1\), a série geométrica bilateral correspondente converge. Isso foi usado para provar em Lean que

```lean
Summable (fun k : ℤ => dtftTerm ψ ω k)
```

sob a hipótese \(|\psi|<1\).

---

## 12. Pareamento das frequências positivas e negativas

A fórmula de Euler foi formalizada na forma

$$
e^{-ix}+e^{ix}=2\cos x.
$$

Em seguida, demonstrou-se que

$$
T(n)+T(-n)
=
\frac23\psi^n\cos(n\omega).
$$

Em Lean:

```lean

theorem dtftTerm_pair
    (ψ ω : ℝ)
    (n : ℕ) :
    dtftTerm ψ ω (n : ℤ) +
        dtftTerm ψ ω (-(n : ℤ))
      =
    (((2 : ℝ) / 3 *
        ψ ^ n *
        Real.cos ((n : ℝ) * ω) : ℝ) : ℂ) := by
  ...
```

Esse é o passo que transforma a DTFT bilateral em

$$
P(\omega)
=
\frac13
+
\frac23
\sum_{n=1}^{\infty}
\psi^n\cos(n\omega).
$$

---

## 13. Série real equivalente à DTFT

Foi definida a representação real:

```lean

def psdSeries (ψ ω : ℝ) : ℝ :=
  (1 : ℝ) / 3 *
    (
      1 +
      2 *
        ∑' n : ℕ,
          ψ ^ (n + 1) *
            Real.cos (((n + 1 : ℕ) : ℝ) * ω)
    )
```

E foi demonstrado formalmente que

$$
\boxed{
\operatorname{psdDTFT}(\psi,\omega)
=
\operatorname{psdSeries}(\psi,\omega)
}.
$$

---

## 14. Forma fechada da PSD

A partir da soma trigonométrica, foi provado:

```lean

theorem psd_closed_form
    (ψ ω : ℝ)
    (hψ : |ψ| < 1) :
    psdSeries ψ ω = PSD ψ ω := by
  exact
    psd_closed_form_of_cosine_tsum
      ψ
      ω
      hψ
      (cosine_geometric_tail_tsum ψ ω hψ)
```

Assim,

$$
\boxed{
P(\omega)=
\frac{1-\psi^2}
{3(1-2\psi\cos\omega+\psi^2)}
}.
$$

---

## 15. Teorema principal

O resultado final conecta diretamente a DTFT bilateral da equação (18) à expressão fechada da equação (19):

```lean

/--
Teorema principal da formalização espectral.

Para |ψ| < 1, a DTFT bilateral da autocorrelação

    R(k) = (1/3) ψ^|k|

é exatamente

    P(ω) =
      (1 - ψ²) /
      (3 (1 - 2 ψ cos(ω) + ψ²)).
-/
theorem dtft_eq_psd
    (ψ ω : ℝ)
    (hψ : |ψ| < 1) :
    psdDTFT ψ ω = (PSD ψ ω : ℂ) := by
  rw [psdDTFT_eq_psdSeries ψ ω hψ]
  rw [psd_closed_form ψ ω hψ]
```

Matematicamente, o Lean certifica:

$$
\boxed{
\sum_{k\in\mathbb Z}
\frac13\psi^{|k|}e^{-ik\omega}
=
\frac{1-\psi^2}
{3\left(1-2\psi\cos\omega+\psi^2\right)}
}
\qquad |\psi|<1.
$$

Esse resultado formaliza a passagem entre as equações **(18)** e **(19)** do artigo.

---

## 16. Resultados formalizados até o momento

| Resultado | Situação |
|---|---|
| \(\psi(\sqrt2-1)=0\) para o caso \(r=3\) | ✅ Provado em Lean |
| \(\psi=0\Rightarrow P(\omega)=1/3\) | ✅ Provado em Lean |
| Caso \(r=3\), \(\alpha=\sqrt2-1\Rightarrow\) espectro branco | ✅ Provado em Lean |
| \(R(k+1)=\psi R(k)\Rightarrow R(k)=\frac13\psi^k\) | ✅ Provado em Lean |
| Simetria \(R(-k)=R(k)\) | ✅ Provado em Lean |
| Convergência da série geométrica complexa | ✅ Provado em Lean |
| \(\operatorname{Re}[(\psi e^{i\omega})^n]=\psi^n\cos(n\omega)\) | ✅ Provado em Lean |
| Soma trigonométrica geométrica | ✅ Provado em Lean |
| Convergência absoluta da DTFT bilateral | ✅ Provado em Lean |
| Pareamento \(T(n)+T(-n)\) | ✅ Provado em Lean |
| DTFT bilateral = série real de cossenos | ✅ Provado em Lean |
| Série real = PSD fechada | ✅ Provado em Lean |
| DTFT bilateral = equação (19) | ✅ Provado em Lean |
| Derivação completa do mapa da eq. (1) até a recorrência da eq. (17) | ⏳ Trabalho futuro |
| Prova formal completa da densidade invariante uniforme | ⏳ Trabalho futuro |
| Formalização integral das equações (1)–(17) | ⏳ Trabalho futuro |

---

## 17. O que esta formalização prova — e o que ainda não prova

### Formalizado

O projeto já verifica formalmente uma parte substancial da derivação espectral, em particular:

$$
\boxed{
R(k+1)=\psi R(k)
\Longrightarrow
R(k)=\frac13\psi^{|k|}
\Longrightarrow
\operatorname{DTFT}\{R\}
=
\frac{1-\psi^2}
{3(1-2\psi\cos\omega+\psi^2)}
}.
$$

Também é formalizado um dos casos de espectro branco discutidos no artigo.

### Ainda não formalizado integralmente

A formalização atual **não deve ser interpretada como uma prova Lean de todo o artigo**.

Ainda resta formalizar, entre outros pontos:

1. a própria família geral de mapas lineares por partes da equação (1);
2. a iteração \(s(n+1)=f(s(n))\);
3. a densidade invariante uniforme;
4. a expressão integral da autocorrelação;
5. a decomposição de \(f^k\) em \(r^k\) segmentos;
6. a derivação formal das equações (11)–(16);
7. a obtenção de
 $$
   R(k+1)=\psi R(k)
$$
   diretamente a partir da estrutura do mapa.

Esse conjunto constitui a continuação natural do projeto.

---

## 18. Possível direção para formalização completa do artigo

Uma estratégia incremental é:

```mermaid
flowchart TD
    A[Eq. 1<br/>Definir o mapa linear por partes]
    B[Eq. 2<br/>Sistema dinâmico discreto]
    C[Eq. 4<br/>Densidade invariante uniforme]
    D[Eq. 7<br/>Autocorrelação como integral]
    E[Eq. 8<br/>Segmentos de f^k]
    F[Eq. 10<br/>Integral em cada segmento]
    G[Eq. 11<br/>Expressão de R(k)]
    H[Eqs. 12–16<br/>Refinamento dos segmentos]
    I[Eq. 17<br/>R(k+1)=ψR(k)]
    J[Eq. 18<br/>R(k)=1/3 ψ^|k|]
    K[Eq. 19<br/>PSD fechada]

    A --> B --> C --> D --> E --> F --> G --> H --> I --> J --> K
```

A parte **I → J → K** já está substancialmente formalizada neste projeto.

---

## 19. Como executar

### Requisitos

- Lean 4;
- Lake;
- Mathlib;
- VS Code com a extensão **Lean 4** recomendada.

Dentro da raiz do projeto:

```bash
lake build
```

Ou abra a pasta no VS Code:

```bash
code .
```

Abra o arquivo principal de formalização, por exemplo:

```text
SpectralChaos.lean
```

O painel **Lean Infoview** mostra os objetivos ainda pendentes.

Quando uma prova é aceita, o resultado esperado é:

```text
Goals accomplished!
```

ou

```text
No goals
```

Warnings do linter sobre espaçamento ou estilo não significam falhas matemáticas da prova.

---

## 20. Filosofia do projeto

O objetivo deste repositório não é reescrever o artigo em Lean palavra por palavra. A abordagem adotada é transformar resultados matematicamente relevantes em uma cadeia de teoremas formais pequenos e verificáveis.

O princípio usado foi:

> **resultado científico publicado → enunciado formal → lemas auxiliares → prova Lean → verificação pelo kernel**

Isso permite localizar com precisão quais hipóteses são necessárias e quais partes da derivação ainda dependem de resultados previamente assumidos.

---

## 21. Referência principal

```bibtex
@article{CostaEisencraft2019,
  author  = {Costa, Rafael Alves da and Eisencraft, Marcio},
  title   = {Spectral characteristics of a general piecewise linear chaotic signal generator},
  journal = {Communications in Nonlinear Science and Numerical Simulation},
  volume  = {72},
  pages   = {441--448},
  year    = {2019},
  doi     = {10.1016/j.cnsns.2019.01.002}
}
```

**Referência:**

R. A. da Costa and M. Eisencraft, “Spectral characteristics of a general piecewise linear chaotic signal generator,” *Communications in Nonlinear Science and Numerical Simulation*, vol. 72, pp. 441–448, 2019. DOI: 10.1016/j.cnsns.2019.01.002.

---

## 22. Status

**Estado atual:** prova formal da relação entre a autocorrelação geométrica e a expressão fechada da PSD concluída.

Teorema principal verificado:

$$
\boxed{
\sum_{k\in\mathbb Z}
\frac13\psi^{|k|}e^{-ik\omega}
=
\frac{1-\psi^2}
{3(1-2\psi\cos\omega+\psi^2)}
},
\qquad |\psi|<1.
$$

A próxima etapa natural é formalizar a derivação de \(R(k+1)=\psi R(k)\) diretamente a partir da família geral de mapas lineares por partes descrita no artigo.
