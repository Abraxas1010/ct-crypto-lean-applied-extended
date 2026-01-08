import HeytingLean.Crypto.Information.PrivacyAmplification.LeftoverHashLemma

/-!
# Privacy amplification (interface-first)

This file provides a minimal "wiring layer" around the packaged Leftover Hash Lemma.
It does not attempt to implement a full QKD privacy amplification pipeline.
-/

namespace HeytingLean.Crypto.Information.PrivacyAmplification

open HeytingLean.Crypto.Information.Hashing

/-- A privacy amplification plan: choose a hash seed and apply it to the raw key. -/
structure PrivacyAmplificationPlan (D R S : Type*) where
  H : HashFamily D R S
  seed : S

end HeytingLean.Crypto.Information.PrivacyAmplification
