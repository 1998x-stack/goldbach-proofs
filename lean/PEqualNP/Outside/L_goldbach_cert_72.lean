import Mathlib

/-!
SPDX-License-Identifier: Apache-2.0

For modulus 72, the units are paired by a shift of 36. The half-period
cancellation strategy and conversion to powers are adapted from
longchangzheng's Goldbach PR #587 (modulus 128), commit
dde70f03511fe3cf64b61288bbeeff453a9487c3. Here the finite unit-set
identity is certified independently for modulus 72.
-/

theorem PEqualNP.Outside.L_goldbach_cert_72 :
    ∀ a:ℕ, Nat.Coprime a 72 → (∑ b ∈ (Finset.range 72).filter (fun b => Nat.Coprime b 72), Complex.exp (((2*Real.pi*(a:ℝ)*b/72:ℝ):ℂ)*Complex.I))/(24:ℂ)=(0:ℂ)/24 := by
  intro a ha
  let t : ℂ := 2 * (Real.pi : ℂ) * Complex.I * ((a : ℂ) / 72)
  let z : ℂ := Complex.exp t
  have hz : IsPrimitiveRoot z 72 := by
    simpa [z, t] using Complex.isPrimitiveRoot_exp_of_coprime a 72 (by decide) ha
  have hterm (b : ℕ) :
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / 72 : ℝ) : ℂ) * Complex.I) = z ^ b := by
    change _ = Complex.exp t ^ b
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    dsimp [t]
    ring
  have hhalf : z ^ 36 = -1 := by
    have hsquare : (z ^ 36) ^ 2 = 1 := by
      rw [← pow_mul]
      exact hz.pow_eq_one
    exact (sq_eq_one_iff.mp hsquare).resolve_left
      (hz.pow_ne_one_of_pos_of_lt (by decide) (by decide))
  let U : Finset ℕ := (Finset.range 72).filter (fun b => Nat.Coprime b 72)
  let L : Finset ℕ := (Finset.range 36).filter (fun b => Nat.Coprime b 72)
  let H : Finset ℕ := L.image (fun b => b + 36)
  have hsplit : U = L ∪ H := by decide
  have hdisj : Disjoint L H := by decide
  have hsum : (∑ b ∈ H, z ^ b) = -(∑ b ∈ L, z ^ b) := by
    dsimp only [H]
    rw [Finset.sum_image]
    · rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro b hb
      rw [pow_add, hhalf]
      ring
    · intro x hx y hy hxy
      exact Nat.add_right_cancel hxy
  have hzero : (∑ b ∈ U, z ^ b) = 0 := by
    rw [hsplit, Finset.sum_union hdisj, hsum]
    ring
  simp_rw [hterm]
  exact congrArg (fun x : ℂ => x / 24) hzero
