module

public import AuditFixture.Basic

@[expose] public section

namespace AuditFixture

/-- An unmapped helper that routes through `double_isEven`. -/
theorem isEven_of_isDoubled {n : Nat} (h : IsDoubled n) : IsEven n := by
  obtain ⟨k, rfl⟩ := h
  exact double_isEven k

/-- The sum of two even numbers is even. The hypothesis `hc` is never used. -/
theorem even_add (m n c : Nat) (hm : IsEven m) (hn : IsDoubled n) (hc : 0 < c) :
    IsEven (m + n) := by
  obtain ⟨a, rfl⟩ := hm
  have hb : IsEven n := isEven_of_isDoubled hn
  obtain ⟨b, rfl⟩ := hb
  refine ⟨a + b, ?_⟩
  rw [Nat.mul_add]

end AuditFixture
