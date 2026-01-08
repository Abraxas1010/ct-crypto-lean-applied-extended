import HeytingLean.Crypto.Information.PrivacyAmplification
import HeytingLean.Crypto.QKD.BB84.ProbabilisticSecurity

/-!
# BB84 key extraction (interface-first)

This is a placeholder wiring layer for privacy amplification. It is intentionally
lightweight: it depends on a packaged Leftover Hash Lemma rather than proving it.
-/

namespace HeytingLean.Crypto.QKD.BB84

open HeytingLean.Crypto.Information.PrivacyAmplification

/-- A BB84 key extraction record: raw key, and a plan to hash it to a final key. -/
structure BB84KeyExtraction (D R S : Type*) where
  rawKeyDist : D → ℝ
  plan : PrivacyAmplificationPlan D R S

end HeytingLean.Crypto.QKD.BB84
