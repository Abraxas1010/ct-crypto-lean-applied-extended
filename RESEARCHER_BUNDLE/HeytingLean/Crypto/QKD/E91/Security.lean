import HeytingLean.Crypto.ConstructiveHardness.Security
import HeytingLean.Crypto.QKD.E91.Eavesdropping

/-!
# E91 security (toy, Constructor-Theoretic)

This file applies the generic no-cloning ⇒ eavesdropping-impossible theorem to
the toy E91 superinformation medium.
-/

namespace HeytingLean
namespace Crypto
namespace QKD
namespace E91

open HeytingLean.Constructor.CT
open HeytingLean.Crypto.ConstructiveHardness

theorem e91_secure : SecureAgainstEavesdropping E91Substrate e91TaskCT e91Superinfo :=
  superinfo_secure_against_eavesdropping e91TaskCT e91Superinfo

theorem intercept_impossible :
    e91TaskCT.impossible interceptStrategy.intercept := by
  have hsec : SecureAgainstEavesdropping E91Substrate e91TaskCT e91Superinfo := e91_secure
  refine hsec interceptStrategy ?_
  intro hPossible
  simpa [e91Superinfo] using (intercept_requires_copyAll hPossible)

end E91
end QKD
end Crypto
end HeytingLean

