import HeytingLean.Crypto.QKD.E91.DI.CHSH.CHSHInequality
import HeytingLean.Crypto.QKD.E91.DI.Tsirelson.Achievability
import HeytingLean.Crypto.QKD.E91.DI.Security.CHSHSecurity

/-!
# E91 Device-Independent Layer (CHSH/Tsirelson umbrella)

This layer refines the toy CT-native E91 story by adding:
- CHSH inequality for local hidden-variable models (`|S| ≤ 2`);
- Tsirelson bound for vector strategies (`|S| ≤ 2√2`) and an explicit achiever;
- the logical bridge: `|S| > 2` implies no LHV model can induce the correlator.

Quantitative secrecy bounds from CHSH violation remain future work.
-/

namespace HeytingLean.Crypto.QKD.E91.DI

-- Intentionally empty: importing the modules is the API.

end HeytingLean.Crypto.QKD.E91.DI

