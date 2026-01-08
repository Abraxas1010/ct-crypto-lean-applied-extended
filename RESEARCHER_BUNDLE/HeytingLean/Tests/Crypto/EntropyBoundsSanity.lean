import HeytingLean.Crypto.Information.Entropy
import HeytingLean.Crypto.SecurityBounds
import HeytingLean.Crypto.QKD.BB84.ProbabilisticSecurity

/-!
# Entropy/security-bounds sanity checks

Compile-time checks for the interface-first entropy + ε-security bookkeeping layer.
-/

namespace HeytingLean.Tests.Crypto.EntropyBoundsSanity

open HeytingLean.Crypto.Information.Entropy
open HeytingLean.Crypto.SecurityBounds
open HeytingLean.Crypto.QKD.BB84

#check MinEntropySpace
#check SmoothMinEntropy
#check ConditionalMinEntropy
#check EpsilonSecure
#check FiniteKeyBound
#check BB84FiniteKeySecurity

end HeytingLean.Tests.Crypto.EntropyBoundsSanity

