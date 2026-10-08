import Mathlib

noncomputable section

/--
ψ para o caso r = 3 considerado no artigo.
-/
def psi3 (α : ℝ) : ℝ :=
  (1 - 2 * α - α ^ 2) / 2

/--
Para α = √2 - 1, ψ = 0.
-/
theorem psi_zero_at_sqrt2_sub_one :
    psi3 (Real.sqrt 2 - 1) = 0 := by
  have hsqrt :
      (Real.sqrt (2 : ℝ)) ^ 2 = 2 := by
    norm_num
  unfold psi3
  nlinarith

/--
PSD dada pela equação (19) do artigo.
-/
def PSD (ψ ω : ℝ) : ℝ :=
  (1 - ψ ^ 2) /
    (3 * (1 - 2 * Real.cos ω * ψ + ψ ^ 2))


/--
Se ψ = 0, a PSD é constante para toda frequência.
-/
theorem white_spectrum (ω : ℝ) :
    PSD 0 ω = (1 : ℝ) / 3 := by
  norm_num [PSD]

/--
Para α = √2 - 1, o caso r = 3 apresenta espectro branco.
-/
theorem r3_white_spectrum (ω : ℝ) :
    PSD (psi3 (Real.sqrt 2 - 1)) ω =
      (1 : ℝ) / 3 := by
  rw [psi_zero_at_sqrt2_sub_one]
  exact white_spectrum ω

/--
Se R(0) = 1/3 e R(k+1) = ψ R(k),
então R(k) = (1/3) ψ^k.

Corresponde à passagem da equação (17)
para a equação (18) do artigo.
-/
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
/--
Denominador da expressão fechada da PSD.
-/
def psdDen (ψ ω : ℝ) : ℝ :=
  1 - 2 * ψ * Real.cos ω + ψ ^ 2


/--
Para |ψ| < 1, o denominador da PSD nunca é zero.
-/
theorem psdDen_ne_zero
    (ψ ω : ℝ)
    (hψ : |ψ| < 1) :
    psdDen ψ ω ≠ 0 := by

  have hψ2 : ψ ^ 2 < 1 := by
    exact (sq_lt_one_iff_abs_lt_one ψ).2 hψ

  intro hzero

  have htrig :
      Real.sin ω ^ 2 + Real.cos ω ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq ω

  have hsum :
      (ψ - Real.cos ω) ^ 2 +
        Real.sin ω ^ 2 = 0 := by
    unfold psdDen at hzero
    nlinarith

  have hdiff_sq :
      (ψ - Real.cos ω) ^ 2 = 0 := by
    have h1 :
        0 ≤ (ψ - Real.cos ω) ^ 2 :=
      sq_nonneg _
    have h2 :
        0 ≤ Real.sin ω ^ 2 :=
      sq_nonneg _
    nlinarith

  have hsin_sq :
      Real.sin ω ^ 2 = 0 := by
    have h1 :
        0 ≤ (ψ - Real.cos ω) ^ 2 :=
      sq_nonneg _
    have h2 :
        0 ≤ Real.sin ω ^ 2 :=
      sq_nonneg _
    nlinarith

  have hψcos :
      ψ = Real.cos ω := by
    nlinarith

  have hsin :
      Real.sin ω = 0 := by
    nlinarith

  nlinarith
/--
PSD escrita a partir da autocorrelação

R(k) = (1/3) ψ^|k|.

A soma bilateral da DTFT é reduzida,
pela simetria, a uma soma sobre os naturais.
-/
def psdSeries (ψ ω : ℝ) : ℝ :=
  (1 : ℝ) / 3 *
    (
      1 +
      2 *
        ∑' n : ℕ,
          ψ ^ (n + 1) *
            Real.cos (((n + 1 : ℕ) : ℝ) * ω)
    )

/--
Se a série trigonométrica geométrica possui
a forma fechada esperada, então a PSD é
exatamente a expressão da equação (19).
-/
theorem psd_closed_form_of_cosine_tsum
    (ψ ω : ℝ)
    (hψ : |ψ| < 1)
    (htail :
      (∑' n : ℕ,
          ψ ^ (n + 1) *
            Real.cos (((n + 1 : ℕ) : ℝ) * ω))
        =
      (ψ * Real.cos ω - ψ ^ 2) /
        psdDen ψ ω) :
    psdSeries ψ ω = PSD ψ ω := by

  have hden :
      psdDen ψ ω ≠ 0 :=
    psdDen_ne_zero ψ ω hψ

  unfold psdSeries

  rw [htail]

  unfold PSD
  unfold psdDen at *

  field_simp [hden] <;> ring

/--
O número complexo ψ exp(iω) tem norma menor que 1
sempre que |ψ| < 1.
-/
theorem complex_ratio_norm_lt_one
    (ψ ω : ℝ)
    (hψ : |ψ| < 1) :
    ‖(ψ : ℂ) * Complex.exp ((ω : ℂ) * Complex.I)‖ < 1 := by

  rw [norm_mul]

  have hexp :
      ‖Complex.exp ((ω : ℂ) * Complex.I)‖ = 1 := by
    simpa using Complex.norm_exp_ofReal_mul_I ω

  rw [hexp]

  simp only [mul_one, Complex.norm_real]

  exact hψ

/--
Série geométrica complexa usada na derivação da PSD.
-/
theorem complex_geometric_psd
    (ψ ω : ℝ)
    (hψ : |ψ| < 1) :
    (∑' n : ℕ,
      (((ψ : ℂ) *
        Complex.exp ((ω : ℂ) * Complex.I)) ^ n))
      =
    (1 -
      ((ψ : ℂ) *
        Complex.exp ((ω : ℂ) * Complex.I)))⁻¹ := by

  have hnorm :
      ‖(ψ : ℂ) *
        Complex.exp ((ω : ℂ) * Complex.I)‖ < 1 :=
    complex_ratio_norm_lt_one ψ ω hψ

  exact tsum_geometric_of_norm_lt_one hnorm

/--
Parte real das potências de ψ exp(iω).

Implementa:
Re[(ψ e^(iω))^n] = ψ^n cos(nω).
-/
theorem complex_power_re
    (ψ ω : ℝ)
    (n : ℕ) :
    ((((ψ : ℂ) *
        Complex.exp ((ω : ℂ) * Complex.I)) ^ n).re)
      =
    ψ ^ n * Real.cos ((n : ℝ) * ω) := by

  rw [mul_pow]

  rw [← Complex.exp_nat_mul]

  have harg :
      (n : ℂ) * ((ω : ℂ) * Complex.I)
        =
      ((((n : ℝ) * ω : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring

  rw [harg]

  have hpow :
      ((ψ : ℂ) ^ n) =
        ((ψ ^ n : ℝ) : ℂ) := by
    simpa using
      (map_pow Complex.ofRealHom ψ n).symm

  rw [hpow]

  rw [Complex.re_ofReal_mul]

  rw [Complex.exp_ofReal_mul_I_re]

/--
Soma trigonométrica geométrica:

∑ ψ^n cos(nω)
=
(1 - ψ cos ω) /
(1 - 2 ψ cos ω + ψ²),

para |ψ| < 1.
-/
theorem cosine_geometric_tsum
    (ψ ω : ℝ)
    (hψ : |ψ| < 1) :
    (∑' n : ℕ,
        ψ ^ n * Real.cos ((n : ℝ) * ω))
      =
    (1 - ψ * Real.cos ω) /
      psdDen ψ ω := by

  let q : ℂ :=
    (ψ : ℂ) *
      Complex.exp ((ω : ℂ) * Complex.I)

  have hnorm :
      ‖q‖ < 1 := by
    dsimp [q]
    exact complex_ratio_norm_lt_one ψ ω hψ

  have hsum :
      Summable (fun n : ℕ => q ^ n) := by
    exact summable_geometric_of_norm_lt_one hnorm

  have hgeom :
      (∑' n : ℕ, q ^ n) =
        (1 - q)⁻¹ := by
    exact tsum_geometric_of_norm_lt_one hnorm

  have hreal :
      (∑' n : ℕ,
          ψ ^ n *
            Real.cos ((n : ℝ) * ω))
        =
      ((1 - q)⁻¹).re := by
    rw [← hgeom]
    rw [Complex.re_tsum hsum]
    apply tsum_congr
    intro n
    dsimp [q]
    exact (complex_power_re ψ ω n).symm

  have hre :
      (1 - q).re =
        1 - ψ * Real.cos ω := by
    dsimp [q]
    simp

  have him :
      (1 - q).im =
        -(ψ * Real.sin ω) := by
    dsimp [q]
    simp

  have hnormsq :
      Complex.normSq (1 - q) =
        psdDen ψ ω := by
    rw [Complex.normSq_apply]
    rw [hre, him]

    unfold psdDen

    have htrig :
        Real.sin ω ^ 2 +
          Real.cos ω ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq ω

    nlinarith

  rw [hreal]
  rw [Complex.inv_re]
  rw [hre, hnormsq]

/--
Versão deslocada da soma trigonométrica geométrica:

∑_{n=0}^∞ ψ^(n+1) cos((n+1)ω)
=
(ψ cos ω - ψ²) /
(1 - 2 ψ cos ω + ψ²),

para |ψ| < 1.
-/
theorem cosine_geometric_tail_tsum
    (ψ ω : ℝ)
    (hψ : |ψ| < 1) :
    (∑' n : ℕ,
        ψ ^ (n + 1) *
          Real.cos (((n + 1 : ℕ) : ℝ) * ω))
      =
    (ψ * Real.cos ω - ψ ^ 2) /
      psdDen ψ ω := by

  let q : ℂ :=
    (ψ : ℂ) *
      Complex.exp ((ω : ℂ) * Complex.I)

  have hnorm :
      ‖q‖ < 1 := by
    dsimp [q]
    exact complex_ratio_norm_lt_one ψ ω hψ

  have hsumComplex :
      Summable (fun n : ℕ => q ^ n) := by
    exact summable_geometric_of_norm_lt_one hnorm

  have hsumRe :
      Summable (fun n : ℕ => (q ^ n).re) := by
    exact
      (Complex.hasSum_re hsumComplex.hasSum).summable

  have hsumCos :
      Summable
        (fun n : ℕ =>
          ψ ^ n *
            Real.cos ((n : ℝ) * ω)) := by
    refine hsumRe.congr ?_
    intro n
    dsimp [q]
    exact complex_power_re ψ ω n

  have hsplit :
      (∑' n : ℕ,
          ψ ^ n *
            Real.cos ((n : ℝ) * ω))
        =
      1 +
        (∑' n : ℕ,
          ψ ^ (n + 1) *
            Real.cos (((n + 1 : ℕ) : ℝ) * ω)) := by
    simpa using hsumCos.tsum_eq_zero_add

  calc
    (∑' n : ℕ,
        ψ ^ (n + 1) *
          Real.cos (((n + 1 : ℕ) : ℝ) * ω))
        =
      (∑' n : ℕ,
          ψ ^ n *
            Real.cos ((n : ℝ) * ω)) - 1 := by
      linarith [hsplit]

    _ =
      (1 - ψ * Real.cos ω) /
          psdDen ψ ω - 1 := by
      rw [cosine_geometric_tsum ψ ω hψ]

    _ =
      (ψ * Real.cos ω - ψ ^ 2) /
        psdDen ψ ω := by
      have hden :
          psdDen ψ ω ≠ 0 :=
        psdDen_ne_zero ψ ω hψ

      field_simp [hden]
      unfold psdDen
      ring

/--
Forma fechada da densidade espectral de potência.

Para |ψ| < 1,

P(ω) =
(1 - ψ²) /
(3 (1 - 2 ψ cos(ω) + ψ²)).
-/
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

/--
Autocorrelação bilateral correspondente à equação (18).
-/
def autocorrZ (ψ : ℝ) (k : ℤ) : ℝ :=
  (1 : ℝ) / 3 * ψ ^ k.natAbs

theorem autocorrZ_even
    (ψ : ℝ)
    (k : ℤ) :
    autocorrZ ψ (-k) = autocorrZ ψ k := by
  unfold autocorrZ
  simp

/--
Um termo da DTFT bilateral da autocorrelação.

term(k) = R(k) exp(-i k ω)
-/
def dtftTerm
    (ψ ω : ℝ)
    (k : ℤ) : ℂ :=
  (autocorrZ ψ k : ℂ) *
    Complex.exp
      (-Complex.I *
        (((k : ℝ) * ω : ℝ) : ℂ))


/--
PSD definida literalmente como a DTFT bilateral
da sequência de autocorrelação.
-/
def psdDTFT
    (ψ ω : ℝ) : ℂ :=
  ∑' k : ℤ, dtftTerm ψ ω k


/--
O termo k = 0 da DTFT é R(0) = 1/3.
-/
theorem dtftTerm_zero
    (ψ ω : ℝ) :
    dtftTerm ψ ω 0 = (1 : ℂ) / 3 := by
  simp [dtftTerm, autocorrZ]

/--
Identidade de Euler usada para combinar
as frequências positivas e negativas:

exp(-ix) + exp(ix) = 2 cos(x).
-/
theorem exp_neg_I_add_exp_I
    (x : ℝ) :
    Complex.exp (-Complex.I * (x : ℂ)) +
        Complex.exp (Complex.I * (x : ℂ))
      =
    ((2 * Real.cos x : ℝ) : ℂ) := by

  have hneg :
      -Complex.I * (x : ℂ)
        =
      (((-x : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring

  have hpos :
      Complex.I * (x : ℂ)
        =
      ((x : ℂ) * Complex.I) := by
    ring

  rw [hneg, hpos]

  rw [Complex.exp_ofReal_mul_I]
  rw [Complex.exp_ofReal_mul_I]

  simp [Real.cos_neg, Real.sin_neg]

  ring

/--
Os termos +n e -n da DTFT se combinam
em um termo real envolvendo cosseno:

term(n) + term(-n) = (2/3) ψ^n cos(nω).
-/
theorem dtftTerm_pair
    (ψ ω : ℝ)
    (n : ℕ) :
    dtftTerm ψ ω (n : ℤ) +
        dtftTerm ψ ω (-(n : ℤ))
      =
    (((2 : ℝ) / 3 *
        ψ ^ n *
        Real.cos ((n : ℝ) * ω) : ℝ) : ℂ) := by

  have hterm_pos :
      dtftTerm ψ ω (n : ℤ)
        =
      ((((1 : ℝ) / 3) * ψ ^ n : ℝ) : ℂ) *
        Complex.exp
          (-Complex.I *
            ((((n : ℝ) * ω : ℝ) : ℂ))) := by
    unfold dtftTerm autocorrZ
    simp

  have hterm_neg :
      dtftTerm ψ ω (-(n : ℤ))
        =
      ((((1 : ℝ) / 3) * ψ ^ n : ℝ) : ℂ) *
        Complex.exp
          (Complex.I *
            ((((n : ℝ) * ω : ℝ) : ℂ))) := by
    unfold dtftTerm autocorrZ

    have habs :
        (-(n : ℤ)).natAbs = n := by
      simp

    rw [habs]

    congr 1

    apply congrArg Complex.exp

    push_cast
    ring

  rw [hterm_pos, hterm_neg]

  rw [← mul_add]

  rw [exp_neg_I_add_exp_I ((n : ℝ) * ω)]

  push_cast

  ring
