import ToeplitzSOS.Certificates.Generated.N3
import ToeplitzSOS.Certificates.Generated.N4
import ToeplitzSOS.Certificates.Generated.N5
import ToeplitzSOS.Certificates.Generated.N6
import ToeplitzSOS.Certificates.Generated.N7
import ToeplitzSOS.Certificates.Generated.N8
import ToeplitzSOS.Certificates.Generated.N9
import ToeplitzSOS.Certificates.Generated.N10
import ToeplitzSOS.Certificates.Generated.N11
import ToeplitzSOS.Certificates.Generated.N12
import ToeplitzSOS.Certificates.Generated.N13
import ToeplitzSOS.Certificates.Generated.N14
import ToeplitzSOS.Certificates.Generated.N15
import ToeplitzSOS.Certificates.Generated.N16
import ToeplitzSOS.Certificates.Generated.N17
import ToeplitzSOS.Certificates.Generated.N18
import ToeplitzSOS.Certificates.Generated.N19
import ToeplitzSOS.Certificates.Generated.N20

/-! # Positive certificates for every order from 2 through 20

Each fixed-order identity is checked by the Lean kernel. The theorem below
collects the certificates for the original real Toeplitz polynomial.
-/

namespace ToeplitzSOS

/-- The kernel-checked fixed-order certificates, `2 ≤ n ≤ 20`, as one statement. -/
theorem toeplitzBW_isSumSq_of_le_20 (n : ℕ) (h2 : 2 ≤ n) (h20 : n ≤ 20) :
    IsSumSqHomQuad (toeplitzBW n) := by
  interval_cases n
  · exact toeplitzBW_two_isSumSq
  · exact toeplitzBW_isSumSq_n3
  · exact toeplitzBW_isSumSq_n4
  · exact toeplitzBW_isSumSq_n5
  · exact toeplitzBW_isSumSq_n6
  · exact toeplitzBW_isSumSq_n7
  · exact toeplitzBW_isSumSq_n8
  · exact toeplitzBW_isSumSq_n9
  · exact toeplitzBW_isSumSq_n10
  · exact toeplitzBW_isSumSq_n11
  · exact toeplitzBW_isSumSq_n12
  · exact toeplitzBW_isSumSq_n13
  · exact toeplitzBW_isSumSq_n14
  · exact toeplitzBW_isSumSq_n15
  · exact toeplitzBW_isSumSq_n16
  · exact toeplitzBW_isSumSq_n17
  · exact toeplitzBW_isSumSq_n18
  · exact toeplitzBW_isSumSq_n19
  · exact toeplitzBW_isSumSq_n20

end ToeplitzSOS
