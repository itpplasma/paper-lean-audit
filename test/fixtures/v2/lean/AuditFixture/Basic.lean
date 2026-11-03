module

@[expose] public section

namespace AuditFixture

/-- A natural number is even if it is twice another one. -/
def IsEven (n : Nat) : Prop := ∃ k, n = 2 * k

/-- Doubling, written with the project notation `𝔡(n)`. -/
def double (n : Nat) : Nat := 2 * n

@[inherit_doc] notation:max "𝔡(" n ")" => double n

/-- A helper predicate that the paper never names. -/
def IsDoubled (n : Nat) : Prop := ∃ k, n = 𝔡(k)

theorem double_isEven (k : Nat) : IsEven (𝔡(k)) := by
  exact ⟨k, rfl⟩

end AuditFixture
