# CT Crypto: Concept to Lean Mapping

| CT Concept | Lean Definition | File |
|------------|-----------------|------|
| Physical Modality | `PhysicalModality` | `ConstructiveHardness/PhysicalModality.lean` |
| Soundness (`Phi P -> P`) | `PhysicalModality.sound` | `ConstructiveHardness/PhysicalModality.lean` |
| CT Task | `Task sigma` | `Constructor/CT/Core.lean` |
| Constructor | `TaskCT.Ctor` | `Constructor/CT/TaskExistence.lean` |
| Task Possible | `TaskCT.possible` | `Constructor/CT/TaskExistence.lean` |
| Task Impossible | `TaskCT.impossible` | `Constructor/CT/TaskExistence.lean` |
| Serial Composition | `Task.seq` | `Constructor/CT/Core.lean` |
| Parallel Composition | `Task.par` | `Constructor/CT/Core.lean` |
| Multi-round (serial) | `Task.seqPow` | `Constructor/CT/MultiRound.lean` |
| Multi-round (parallel) | `Task.parPow` | `Constructor/CT/MultiRound.lean` |
| Information Variable | `InfoVariable` | `Constructor/CT/InformationSound.lean` |
| Superinformation Medium | `SuperinformationMedium` | `Constructor/CT/InformationSound.lean` |
| No-Cloning | `M.no_copyXY` | `Constructor/CT/InformationSound.lean` |
| Empirical Model | `EmpiricalModel` | `LoF/CryptoSheaf/Quantum/EmpiricalModel.lean` |
| Global Section | `HasGlobalSection` | `LoF/CryptoSheaf/Quantum/EmpiricalModel.lean` |
| Contextuality | `NoGlobalSection` | `LoF/CryptoSheaf/Quantum/EmpiricalModel.lean` |
| Eavesdropping Strategy | `EavesdroppingStrategy` | `ConstructiveHardness/Security.lean` |
| Security | `SecureAgainstEavesdropping` | `ConstructiveHardness/Security.lean` |
| BB84 (QKD) | `HeytingLean.Crypto.QKD.BB84` | `Crypto/QKD/BB84.lean` |
| BB84 Security | `bb84_secure` | `Crypto/QKD/BB84/Security.lean` |
| BB84 No-cloning witness | `copyAll_impossible` | `Crypto/QKD/BB84/Constructors.lean` |
| BB84 QBER | `KeyComparison.qberReal` | `Crypto/QKD/BB84/ErrorRate/QBER.lean` |
| BB84 intercept-resend | `expectedQBER_eq_rate_div_4` | `Crypto/QKD/BB84/ErrorRate/InterceptResend.lean` |
| BB84 threshold | `securityThreshold` | `Crypto/QKD/BB84/ErrorRate/Threshold.lean` |
| BB84 multi-round reduction | `bb84_attackSeqPow_impossible` | `Crypto/QKD/BB84/MultiRound.lean` |
| E91 (toy) | `HeytingLean.Crypto.QKD.E91` | `Crypto/QKD/E91.lean` |
| E91 security | `e91_secure` | `Crypto/QKD/E91/Security.lean` |
