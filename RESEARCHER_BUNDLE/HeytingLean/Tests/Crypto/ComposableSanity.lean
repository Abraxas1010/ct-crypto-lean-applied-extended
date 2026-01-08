import HeytingLean.Crypto.Composable
import HeytingLean.Crypto.QKD.BB84.UCsecurity

namespace HeytingLean.Tests.Crypto.ComposableSanity

open HeytingLean.Crypto.Composable
open HeytingLean.Crypto.Composable.Instances

#check IdealFunctionality
#check Protocol
#check Simulator
#check UCSecure
#check CompositionKit

-- BB84 UC reduction scaffold exists and implies UC security given a reduction.
#check HeytingLean.Crypto.QKD.BB84.BB84UCReduction
#check HeytingLean.Crypto.QKD.BB84.bb84_uc_secure

end HeytingLean.Tests.Crypto.ComposableSanity

