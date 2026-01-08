import HeytingLean.Crypto.QKD.E91

/-!
# E91 sanity checks

Compile-time checks for the toy E91 CT instantiation.
-/

namespace HeytingLean.Tests.Crypto.E91Sanity

open HeytingLean.Crypto.QKD.E91

#check E91State
#check attrKey
#check attrTest
#check copyAll
#check e91TaskCT
#check e91Superinfo
#check e91_secure
#check intercept_impossible

end HeytingLean.Tests.Crypto.E91Sanity

