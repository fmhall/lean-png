/-!
# Shared Test Helpers

Common utilities used across all test modules.
-/

namespace PngTest

/-- Assert a condition, throwing an error with the given message on failure. -/
def check (cond : Bool) (msg : String) : IO Unit :=
  if cond then pure ()
  else throw (.userError s!"FAIL: {msg}")

end PngTest
