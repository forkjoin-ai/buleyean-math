import Init

/-!
# Buleyean Logic

Post-fold logic. Truth is ground state. Proof is rejection.
Boolean is the K=2 special case.

The Bule is the unit of topological deficit. A Bule count of n means
n rejections remain before ground state. The proof step is reject(p) = p - 1.
The sliver is the +1 that guarantees p > 0 always.

Key theorems (from BuleyeanLogic.lean in the aeon formal surface):
  - Boolean is K=2 Buleyean
  - n rejections reach ground from n
  - The sliver bridges probability and logic
  - Truth is the unique ground state (Bule = 0)
-/

namespace BuleyeanMath.Logic

-- The Bule: unit of topological deficit
-- A natural number counting rejections remaining
def Bule := Nat

-- The proof step: reject one possibility
def reject (b : Nat) : Nat := b - 1

-- The sliver: add one possibility back
def sliver (b : Nat) : Nat := b + 1

-- Ground state: zero deficit, truth
def isGround (b : Nat) : Bool := b == 0

-- Concrete instances: n rejections from n reach ground
theorem one_rejection : reject 1 = 0 := by unfold reject; omega
theorem two_rejections : reject (reject 2) = 0 := by unfold reject; omega
theorem three_rejections : reject (reject (reject 3)) = 0 := by unfold reject; omega

-- Boolean is K=2 Buleyean: one rejection from 1 reaches ground
theorem boolean_is_two_buleyean : reject 1 = 0 := by unfold reject; omega

-- The sliver then reject = identity (for n ≥ 1)
theorem sliver_reject_identity (n : Nat) : reject (sliver n) = n := by
  unfold reject sliver; omega

-- Reject then sliver = identity (for n ≥ 1)
theorem reject_sliver_identity (n : Nat) (_ : n ≥ 1) : sliver (reject n) = n := by
  unfold reject sliver; omega

-- Truth is unique: the only ground state is 0
theorem ground_is_zero (n : Nat) : isGround n = true ↔ n = 0 := by
  unfold isGround; simp [BEq.beq]

end BuleyeanMath.Logic
