/-! Deterministic value and an associated counter. Concrete routines compose
counters according to the scalar-operation convention. This value/count type
itself permits arbitrary values with count zero; it is not an instruction
language that enforces execution costs. -/
set_option autoImplicit false
namespace DPCut

structure Arithmetic (α : Type) where
  value : α
  steps : Nat

end DPCut
