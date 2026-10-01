import Mathlib

/-!
# Exact integer arithmetic for the 1024-point witness

Each signed weighted entry is enclosed
above by one integer unit at denominator `2^64`. The generated block
proofs check these arithmetic definitions using kernel reduction.
-/

namespace ToeplitzSOS.Negative.Witness

/-- The floor weights of (22), indexed from zero. -/
def weight (j : ℕ) : ℤ := (2^43 * (j + 1) / (128^2 + (j + 1)^2)^2 : ℕ)

/-- The real speed, equal to one or two on the 1024 witness indices. -/
def radius (i : ℕ) : ℤ := (i / 512 + 1 : ℕ)

/-- The positive integer imaginary speed, one through 256. -/
def frequency (i : ℕ) : ℤ := (i / 2 % 256 + 1 : ℕ)

/-- The two conjugate signs, with the positive sign first. -/
def sign (i : ℕ) : ℤ := if i % 2 = 0 then 1 else -1

/-- The signed real coefficient of each witness point. -/
def coefficient (i : ℕ) : ℤ := sign i * weight (i / 2 % 256)

/-- The positive rational kernel denominator `A₀` at a witness pair. -/
def denomA (i j : ℕ) : ℤ :=
  (radius i + radius j)^2 + (sign i * frequency i - sign j * frequency j)^2

/-- The positive rational kernel denominator `C₀` at a witness pair. -/
def denomC (i j : ℕ) : ℤ := 4 * radius i * radius j

/-- Numerator of the signed weighted tangent entry over `A₀² C₀²`. -/
def entryNumerator (i j : ℕ) : ℤ :=
  2 * coefficient i * coefficient j *
    (2 * (denomC i j)^2 + (denomA i j)^2 - denomA i j * denomC i j)

/-- Positive denominator of the signed weighted tangent entry. -/
def entryDenominator (i j : ℕ) : ℤ := (denomA i j)^2 * (denomC i j)^2

/-- Directed upper enclosure, in units of `2^-64`. -/
def upperEntry (i j : ℕ) : ℤ :=
  (2^64 * entryNumerator i j) / entryDenominator i j + 1

/-- Sixteen consecutive rows of the full entrywise directed enclosure. -/
def upperBlock (b : ℕ) : ℤ :=
  ((List.range 16).map (fun k =>
    ((List.range 1024).map (upperEntry (16 * b + k))).sum)).sum

/-- All 64 blocks cover exactly the 1024² signed weighted tangent entries. -/
def fullUpper : ℤ := ∑ b ∈ Finset.range 64, upperBlock b

end ToeplitzSOS.Negative.Witness
