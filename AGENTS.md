# Repository Guidelines

## Project Structure & Module Organization

This is a Lean 4 project for formalizing cryptographic protocols and UC-style security proofs. Main source files live under `LeanCryptoProtocols/`.

- `LeanCryptoProtocols/UC/`: current UC framework, including machines, controller-driven execution, ideal worlds, security definitions, and UC functionalities.
- `LeanCryptoProtocols/Assumptions/`: cryptographic assumptions such as DDH.
- `LeanCryptoProtocols/CaseStudy/`: protocol proof case studies, currently including `SMCEasyUC`.
- `LeanCryptoProtocols/Circuit/`: Boolean circuit components and examples.
- `LeanCryptoProtocols/GMW/`: older transitional code; do not treat it as the current UC mainline unless a task explicitly targets it.
- `blueprint/`: leanblueprint documentation and proof plans.

## Build, Test, and Development Commands

Run commands from the repository root:

```bash
lake build
```

Builds the full Lean library.

```bash
lake build LeanCryptoProtocols.UC.Core
lake build LeanCryptoProtocols.UC.Controller
lake build LeanCryptoProtocols.CaseStudy.SMCEasyUC.DHKE
```

Build focused modules while developing.

```bash
rg -n "\baxiom\b|\bsorry\b|\badmit\b" LeanCryptoProtocols
```

Checks for proof placeholders. Only approved abstraction-layer axioms, such as PPT closure interfaces, should remain.

## Coding Style & Naming Conventions

Use Lean 4 with `lakefile.toml` settings. Keep `relaxedAutoImplicit = false` compatible code. Use two-space indentation in tactic/proof blocks where practical.

Naming conventions:

- Types, structures, inductives, namespaces: `CamelCase`
- Definitions, theorems, fields, helpers: `snake_case`
- Keep UC terms stable: `Machine`, `Protocol`, `Message`, `Envelope`, `ExecutionSetup`, `IdealFunctionality`.

Comments should be concise and audit-relevant. Existing Chinese comments and TODO markers should be preserved unless the corresponding code is removed.

## Testing Guidelines

There is no separate test framework; Lean compilation is the primary check. For each change, build the smallest affected module first, then run `lake build` when the change touches shared UC definitions or public interfaces.

Case-study changes should also build their certificate/audit entry modules, for example:

```bash
lake build LeanCryptoProtocols.CaseStudy.SMCEasyUC.Certificate
```

## Commit & Pull Request Guidelines

Recent commits use short imperative summaries, for example `add blueprint` or `fix some warnings in IdealWorld.lean`. Follow that style: keep the first line concise and mention the affected subsystem.

Pull requests should include:

- A short description of the modeling or proof change.
- The exact `lake build ...` commands run.
- Any remaining axioms, warnings, or intentionally unfinished proof obligations.
- For UC framework changes, note whether old modules such as `Composition.lean` or `GMW/` were intentionally left untouched.

## Agent-Specific Instructions

Prefer `rg` for search. Use `apply_patch` for manual edits. Do not revert unrelated user changes. Keep changes scoped to the requested modules, especially in proof case studies.
