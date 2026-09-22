import Mathlib

open Matrix
open scoped BigOperators

set_option maxHeartbeats 4000000

/-!
  FHB-2 · why the RZZ/RX brickwork is **not** a matchgate circuit.

  `AwareLiquid/The-Fuxi-Hypercube-Math` describes FHB-2 as a "nearest-neighbor
  RZZ/RX brickwork … a matchgate (free-fermion) circuit whose ⟨Xⱼ⟩ / ⟨XⱼXₖ⟩
  references are exactly computable in O(n²·d) via Majorana covariance
  evolution".  That holds for `RZZ` but **not** for `RX` on an interior line.

  Under the Jordan–Wigner mapping (indices from 1)

      γ_{2l−1} = (∏_{i<l} Z_i) X_l ,      γ_{2l} = (∏_{i<l} Z_i) Y_l ,

  the single-qubit generators have these Majorana degrees:

      Z_l = −i γ_{2l−1} γ_{2l}              degree 2      Gaussian
      X_1 =    γ_1                           degree 1      Gaussian after a (2n+1) extension
      X_l = −i γ_1 γ_2 … γ_{2l−1}            degree 2l−1   NOT Gaussian for l ≥ 2

  The covariance route is valid exactly when every generator is at most
  quadratic; a cubic generator puts `X_2` outside `span{1, γ_μ, γ_μγ_ν}`, so the
  `O(n²·d)` claim fails.  Replacing `RX` by `RZ` repairs it — `RZ` is quadratic
  on every line.

  Witnesses below are explicit 4×4 complex matrices for `n = 2`.
-/

namespace FHB2Matchgate

/-- The four Jordan–Wigner Majoranas on two qubits:
`γ₁ = X⊗1`, `γ₂ = Y⊗1`, `γ₃ = Z⊗X`, `γ₄ = Z⊗Y`. -/
def g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ
  | 0 => !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]
  | 1 => !![0, 0, -Complex.I, 0; 0, 0, 0, -Complex.I; Complex.I, 0, 0, 0; 0, Complex.I, 0, 0]
  | 2 => !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, -1; 0, 0, -1, 0]
  | 3 => !![0, -Complex.I, 0, 0; Complex.I, 0, 0, 0; 0, 0, 0, Complex.I; 0, 0, -Complex.I, 0]

/-- `X` on the second qubit. -/
def X2 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]

/-- `Z` on the second qubit. -/
def Z2 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1]

/-- The Majoranas anticommute and square to one: `{γ_μ, γ_ν} = 2 δ_{μν}`. -/
theorem clifford (μ ν : Fin 4) :
    g μ * g ν + g ν * g μ = (if μ = ν then (2 : ℂ) else 0) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  fin_cases μ <;> fin_cases ν <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [g, Complex.ext_iff, Complex.I_mul_I] <;> norm_num

/-- **The falsification witness.**  On two qubits `X_2` is a *cubic* Majorana
monomial `−i γ₁γ₂γ₃`, hence not a Gaussian (matchgate) generator. -/
theorem X2_cubic : X2 = -Complex.I • (g 0 * g 1 * g 2) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [X2, g, Complex.I_mul_I]

/-- `Z_2` is a *quadratic* Majorana monomial `−i γ₃γ₄` — a genuine matchgate
generator. -/
theorem Z2_quadratic : Z2 = -Complex.I • (g 2 * g 3) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Z2, g, Complex.I_mul_I]

/-- `Z` on the first qubit. -/
def Z1 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]

/-- `Z_1 Z_2` is a **quartic** Majorana monomial — so `RZZ`, whose generator it
is, is *not* a matchgate generator either.  The two-qubit matchgate generator is
`X_l X_{l+1} = −i γ_{2l} γ_{2l+1}` (quadratic), not `Z_l Z_{l+1}`. -/
theorem ZZ_quartic : Z1 * Z2 = -(g 0 * g 1 * g 2 * g 3) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Z1, Z2, g, Complex.I_mul_I]

/-- The RZZ generator moves a Majorana into a **cubic** monomial:
`γ₁ · (Z₁Z₂) = −γ₂γ₃γ₄`.  Conjugating `γ₁` by `exp(−iθ Z₁Z₂/2)` therefore
produces a cubic component, so the adjoint action is not linear and the
covariance-matrix route does not apply. -/
theorem ZZ_conj_cubic : g 0 * (Z1 * Z2) = -(g 1 * g 2 * g 3) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Z1, Z2, g, Complex.I_mul_I]

end FHB2Matchgate
