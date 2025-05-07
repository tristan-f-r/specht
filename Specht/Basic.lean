import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Star.Basic

abbrev Word := List (ℕ × ℕ)

universe u

namespace Word

variable {α : Type u} [Mul α] [One α] [Pow α ℕ]

def apply (W : Word) (A B : α) : α := (W.map (fun ⟨n, m⟩ ↦ A^n * B^m)).prod

@[simp] theorem apply_nil {A B : α} : Word.apply [] A B = 1 := rfl
@[simp] theorem apply_cons {W : Word} {nm : ℕ × ℕ} {A B : α} :
    Word.apply (nm :: W) A B = A^nm.1 * B ^ nm.2 * Word.apply W A B := rfl

-- We follow the "degree" convention from Wikipedia instead of the one in Matrix Analysis, since
-- our abbrev of `Word` is on `List` and `List.length` is confusing.
def degree (W : Word) : ℕ := (W.map (fun ⟨n, m⟩ ↦ n + m)).sum

end Word

namespace Specht

variable {α : Type u} [CommRing α] [StarRing α] {k : Type u} [Fintype k] [DecidableEq k]

/-- If matrices `A` and `B` are similar, then `tr(AA*) = tr(BB*)`.
From Theorem 2.2.2 of Matrix Analysis. -/
lemma similar_star_tr {A B : Matrix k k α} {U : Matrix.unitaryGroup k α}
    (hABU : U * B * star U = A) :
    (star A * A).trace = (star B * B).trace := by
  rw [← hABU, Matrix.star_mul, Matrix.star_mul, unitary.coe_star, star_star,
    ← Matrix.trace_mul_cycle, mul_assoc, mul_assoc (U * B), unitary.star_mul_self_of_mem U.prop,
    mul_one, mul_assoc, ← mul_assoc (star U.val), unitary.star_mul_self_of_mem U.prop, one_mul]

/-- From Matrix Analysis, (presumably) 2.2.5 -/
lemma word_similar_star {A B : Matrix k k α} {U : Matrix.unitaryGroup k α} (W : Word)
    (hABU : U * B * star U = A) : W.apply A (star A) = U * W.apply B (star B) * star U := by
  rw [← hABU, Matrix.star_mul, Matrix.star_mul, ← mul_assoc, unitary.coe_star,
    star_star, Word.apply]
  have := fun (M : Matrix k k α) ↦ Units.conj_pow (Units.mk U.val (U⁻¹).val (by simp) (by simp)) M
  conv at this in _ = _ => dsimp only [← Units.inv_eq_val_inv, Matrix.UnitaryGroup.inv_apply]
  conv in (U.val * B * star U.val)^_ => rw [this]
  conv in (U * star B * star U.val)^_ => rw [this]
  conv in _ * _ * _ * _ =>
    rw [mul_assoc, mul_assoc _ _ (star U.val), ← mul_assoc (star U.val),
      unitary.star_mul_self_of_mem U.prop, one_mul, ← mul_assoc]
  induction W with
  | nil =>
    symm
    rw [Word.apply_nil, mul_one, List.map_nil, List.prod_nil, Matrix.mul_eq_one_comm,
      unitary.star_mul_self_of_mem U.prop]
  | cons nm w hw =>
    rw [List.map_cons, List.prod_cons, Word.apply_cons, hw, mul_assoc,
      mul_assoc (U.val) _ (star U.val), ← mul_assoc (star U.val) (U.val),
      unitary.star_mul_self_of_mem U.prop, one_mul]
    group

theorem specht (A B : Matrix k k α) :
    (∃ U : Matrix.unitaryGroup k α, U * B * star U = A) ↔
      ∀ W : Word, (W.apply A (star A)).trace = (W.apply B (star B)).trace := by
  refine ⟨fun ⟨U, hABU⟩ W ↦ ?_, fun h ↦ ?_⟩
  · have ht := word_similar_star W hABU
    rw [← one_mul (W.apply B _), ← unitary.star_mul_self_of_mem U.prop, ← Matrix.trace_mul_cycle]
    congr
  · sorry -- Theorem 63 in Linear Algebra and Geometry: A Second Course

end Specht
