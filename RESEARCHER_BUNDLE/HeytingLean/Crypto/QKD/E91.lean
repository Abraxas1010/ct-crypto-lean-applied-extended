import HeytingLean.Crypto.QKD.E91.States
import HeytingLean.Crypto.QKD.E91.Tasks
import HeytingLean.Crypto.QKD.E91.Constructors
import HeytingLean.Crypto.QKD.E91.Superinfo
import HeytingLean.Crypto.QKD.E91.Eavesdropping
import HeytingLean.Crypto.QKD.E91.Security

/-!
# E91 Quantum Key Distribution (toy umbrella)

This is an interface-first, CT-native E91 *placeholder* that:
- provides a non-trivial `TaskCT` and `SuperinformationMedium` instance;
- supports the project’s generic security theorem.

Device-independent E91 via CHSH/Tsirelson is a future refinement layered on top.
-/

namespace HeytingLean.Crypto.QKD.E91

-- Intentionally empty: importing the modules is the API.

end HeytingLean.Crypto.QKD.E91

