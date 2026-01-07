// CT Crypto proof declarations data
window.CT_CRYPTO_PROOFS = {
  items: [
    // Physical Modality layer
    { name: "PhysicalModality", kind: "structure", family: "Modality", path: "HeytingLean/Crypto/ConstructiveHardness/PhysicalModality.lean", line: 38, snippet: "Sound modality: Φ P → P", pos: {x:0.15, y:0.85}, pos3: {x:-0.8, y:0.7, z:0.2} },
    { name: "PhysicalModality.not_toFun_of_not", kind: "lemma", family: "Modality", path: "HeytingLean/Crypto/ConstructiveHardness/PhysicalModality.lean", line: 47, snippet: "¬P → ¬Φ P (core polarity)", pos: {x:0.22, y:0.78}, pos3: {x:-0.6, y:0.6, z:0.3} },

    // Contextuality layer
    { name: "EmpiricalModel", kind: "structure", family: "Contextuality", path: "HeytingLean/LoF/CryptoSheaf/Quantum/EmpiricalModel.lean", line: 21, snippet: "Empirical model with possibilistic supports", pos: {x:0.12, y:0.55}, pos3: {x:-0.9, y:0.1, z:-0.3} },
    { name: "HasGlobalSection", kind: "def", family: "Contextuality", path: "HeytingLean/LoF/CryptoSheaf/Quantum/EmpiricalModel.lean", line: 30, snippet: "Global section existence predicate", pos: {x:0.18, y:0.50}, pos3: {x:-0.7, y:0.0, z:-0.2} },
    { name: "NoGlobalSection", kind: "def", family: "Contextuality", path: "HeytingLean/LoF/CryptoSheaf/Quantum/EmpiricalModel.lean", line: 37, snippet: "KS-style obstruction: ¬HasGlobalSection", pos: {x:0.25, y:0.52}, pos3: {x:-0.5, y:0.05, z:-0.1} },
    { name: "triangleModel", kind: "def", family: "Contextuality", path: "HeytingLean/LoF/CryptoSheaf/Quantum/EmpiricalModel.lean", line: 270, snippet: "Triangle parity model (a=b, b=c, a≠c)", pos: {x:0.08, y:0.42}, pos3: {x:-1.0, y:-0.2, z:-0.4} },
    { name: "triangle_no_global", kind: "theorem", family: "Contextuality", path: "HeytingLean/LoF/CryptoSheaf/Quantum/EmpiricalModel.lean", line: 281, snippet: "Triangle has no global section", pos: {x:0.15, y:0.38}, pos3: {x:-0.85, y:-0.3, z:-0.3} },

    // Bridge layer
    { name: "contextuality_implies_not_globalSectionTask", kind: "theorem", family: "Bridge", path: "HeytingLean/Crypto/ConstructiveHardness/ContextualityPhysical.lean", line: 31, snippet: "NoGlobalSection → ¬GlobalSectionTask", pos: {x:0.35, y:0.65}, pos3: {x:-0.2, y:0.4, z:0.1} },
    { name: "contextuality_implies_physImpossible", kind: "theorem", family: "Bridge", path: "HeytingLean/Crypto/ConstructiveHardness/ContextualityPhysical.lean", line: 41, snippet: "NoGlobalSection → ¬Φ(HasGlobalSection)", pos: {x:0.40, y:0.70}, pos3: {x:-0.1, y:0.5, z:0.2} },
    { name: "triangle_physImpossible", kind: "theorem", family: "Bridge", path: "HeytingLean/Crypto/ConstructiveHardness/ContextualityPhysical.lean", line: 56, snippet: "Concrete witness: triangle is phys-impossible", pos: {x:0.32, y:0.58}, pos3: {x:-0.3, y:0.25, z:0.0} },

    // Task layer
    { name: "Task", kind: "structure", family: "Task", path: "HeytingLean/Constructor/CT/Core.lean", line: 52, snippet: "CT task: list of input/output arc pairs", pos: {x:0.55, y:0.80}, pos3: {x:0.3, y:0.65, z:0.5} },
    { name: "Variable", kind: "structure", family: "Task", path: "HeytingLean/Constructor/CT/Core.lean", line: 39, snippet: "CT variable: pairwise disjoint attributes", pos: {x:0.60, y:0.85}, pos3: {x:0.4, y:0.75, z:0.6} },
    { name: "TaskCT", kind: "structure", family: "Task", path: "HeytingLean/Constructor/CT/TaskExistence.lean", line: 24, snippet: "Constructor existence interface", pos: {x:0.58, y:0.72}, pos3: {x:0.35, y:0.55, z:0.4} },
    { name: "TaskCT.possible", kind: "def", family: "Task", path: "HeytingLean/Constructor/CT/TaskExistence.lean", line: 50, snippet: "possible T := ∃ c, implements c T", pos: {x:0.65, y:0.68}, pos3: {x:0.5, y:0.45, z:0.35} },
    { name: "TaskCT.impossible", kind: "def", family: "Task", path: "HeytingLean/Constructor/CT/TaskExistence.lean", line: 54, snippet: "impossible T := ¬possible T", pos: {x:0.68, y:0.65}, pos3: {x:0.55, y:0.4, z:0.3} },
    { name: "TaskCT.possible_seq", kind: "theorem", family: "Task", path: "HeytingLean/Constructor/CT/TaskExistence.lean", line: 57, snippet: "Serial composition preserves possibility", pos: {x:0.72, y:0.70}, pos3: {x:0.65, y:0.5, z:0.4} },
    { name: "TaskCT.possible_par", kind: "theorem", family: "Task", path: "HeytingLean/Constructor/CT/TaskExistence.lean", line: 65, snippet: "Parallel composition preserves possibility", pos: {x:0.75, y:0.75}, pos3: {x:0.7, y:0.6, z:0.5} },

    // Information layer
    { name: "InfoVariable", kind: "structure", family: "Information", path: "HeytingLean/Constructor/CT/InformationSound.lean", line: 27, snippet: "Info variable with perm/copy tasks", pos: {x:0.70, y:0.50}, pos3: {x:0.6, y:0.1, z:0.2} },
    { name: "SuperinformationMedium", kind: "structure", family: "Information", path: "HeytingLean/Constructor/CT/InformationSound.lean", line: 58, snippet: "X,Y clonable; XY not clonable", pos: {x:0.75, y:0.45}, pos3: {x:0.7, y:0.0, z:0.1} },
    { name: "SuperinformationMedium.no_cloning_union", kind: "theorem", family: "Information", path: "HeytingLean/Constructor/CT/InformationSound.lean", line: 77, snippet: "CT.impossible M.copyXY", pos: {x:0.78, y:0.40}, pos3: {x:0.75, y:-0.1, z:0.0} },

    // QubitLike example
    { name: "compBasis", kind: "def", family: "QubitLike", path: "HeytingLean/Constructor/CT/Examples/QubitLike.lean", line: 29, snippet: "Computational basis {(ff,ff),(tt,tt)}", pos: {x:0.50, y:0.25}, pos3: {x:0.2, y:-0.5, z:-0.3} },
    { name: "diagBasis", kind: "def", family: "QubitLike", path: "HeytingLean/Constructor/CT/Examples/QubitLike.lean", line: 33, snippet: "Diagonal basis {(ff,tt),(tt,ff)}", pos: {x:0.55, y:0.22}, pos3: {x:0.3, y:-0.55, z:-0.35} },
    { name: "QubitCtor", kind: "inductive", family: "QubitLike", path: "HeytingLean/Constructor/CT/Examples/QubitLike.lean", line: 112, snippet: "Constructors: comp, diag, seq, par", pos: {x:0.52, y:0.30}, pos3: {x:0.25, y:-0.4, z:-0.2} },
    { name: "qubitLikeTaskCT", kind: "def", family: "QubitLike", path: "HeytingLean/Constructor/CT/Examples/QubitLike.lean", line: 161, snippet: "TaskCT instance for qubit-like model", pos: {x:0.58, y:0.28}, pos3: {x:0.35, y:-0.45, z:-0.25} },
    { name: "not_implements_copyUnion", kind: "lemma", family: "QubitLike", path: "HeytingLean/Constructor/CT/Examples/QubitLike.lean", line: 152, snippet: "copyUnion is impossible (no constructor)", pos: {x:0.62, y:0.20}, pos3: {x:0.45, y:-0.6, z:-0.4} },
    { name: "qubitLikeSuperinfo", kind: "def", family: "QubitLike", path: "HeytingLean/Constructor/CT/Examples/QubitLike.lean", line: 234, snippet: "Concrete superinformation witness", pos: {x:0.65, y:0.18}, pos3: {x:0.5, y:-0.65, z:-0.45} },

    // Security layer
    { name: "EavesdroppingStrategy", kind: "structure", family: "Security", path: "HeytingLean/Crypto/ConstructiveHardness/Security.lean", line: 23, snippet: "Abstract eavesdropping task model", pos: {x:0.85, y:0.55}, pos3: {x:0.9, y:0.15, z:-0.1} },
    { name: "SecureAgainstEavesdropping", kind: "def", family: "Security", path: "HeytingLean/Crypto/ConstructiveHardness/Security.lean", line: 33, snippet: "Security predicate for superinfo media", pos: {x:0.88, y:0.50}, pos3: {x:0.95, y:0.05, z:-0.2} },
    { name: "superinfo_secure_against_eavesdropping", kind: "theorem", family: "Security", path: "HeytingLean/Crypto/ConstructiveHardness/Security.lean", line: 41, snippet: "MAIN: no-cloning → secure", pos: {x:0.90, y:0.45}, pos3: {x:1.0, y:-0.05, z:-0.3} },

    // Composition layer
    { name: "TaskSpec", kind: "structure", family: "Composition", path: "HeytingLean/Crypto/ConstructiveHardness/TaskSpec.lean", line: 30, snippet: "Task → Prop bridge", pos: {x:0.82, y:0.35}, pos3: {x:0.85, y:-0.25, z:-0.15} },
    { name: "TaskSpec.toPhysicalModality", kind: "def", family: "Composition", path: "HeytingLean/Crypto/ConstructiveHardness/TaskSpec.lean", line: 42, snippet: "Induced physical modality from TaskSpec", pos: {x:0.85, y:0.30}, pos3: {x:0.9, y:-0.35, z:-0.25} },
    { name: "contextuality_implies_task_impossible", kind: "theorem", family: "Composition", path: "HeytingLean/Crypto/ConstructiveHardness/TaskSpec.lean", line: 64, snippet: "Unifies contextuality with task impossibility", pos: {x:0.80, y:0.25}, pos3: {x:0.8, y:-0.45, z:-0.35} },
    { name: "impossible_seq_of_impossible", kind: "theorem", family: "Composition", path: "HeytingLean/Crypto/ConstructiveHardness/Composition.lean", line: 33, snippet: "Serial decomposition (classical)", pos: {x:0.92, y:0.32}, pos3: {x:1.0, y:-0.3, z:-0.2} },
    { name: "composed_security", kind: "theorem", family: "Composition", path: "HeytingLean/Crypto/ConstructiveHardness/Composition.lean", line: 53, snippet: "Compositional transfer (axiom-free!)", pos: {x:0.95, y:0.28}, pos3: {x:1.05, y:-0.4, z:-0.3} }
  ],
  edges: [
    // Modality -> Bridge
    [0, 8], [1, 8], [1, 9],
    // Contextuality -> Bridge
    [4, 7], [5, 6], [6, 9],
    // Bridge -> Security
    [8, 9], [9, 28],
    // Task -> Information
    [12, 17], [13, 14], [14, 18], [15, 18],
    // Information -> Security
    [18, 19], [19, 28],
    // QubitLike -> Information
    [24, 25], [25, 18],
    // Security -> Composition
    [28, 34], [27, 28],
    // Composition internal
    [30, 31], [31, 32], [33, 34]
  ]
};
