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
| Information Variable | `InfoVariable` | `Constructor/CT/InformationSound.lean` |
| Superinformation Medium | `SuperinformationMedium` | `Constructor/CT/InformationSound.lean` |
| No-Cloning | `M.no_copyXY` | `Constructor/CT/InformationSound.lean` |
| Empirical Model | `EmpiricalModel` | `LoF/CryptoSheaf/Quantum/EmpiricalModel.lean` |
| Global Section | `HasGlobalSection` | `LoF/CryptoSheaf/Quantum/EmpiricalModel.lean` |
| Contextuality | `NoGlobalSection` | `LoF/CryptoSheaf/Quantum/EmpiricalModel.lean` |
| Eavesdropping Strategy | `EavesdroppingStrategy` | `ConstructiveHardness/Security.lean` |
| Security | `SecureAgainstEavesdropping` | `ConstructiveHardness/Security.lean` |
