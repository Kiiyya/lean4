(In the following, use `sysctl -n hw.logicalcpu` instead of `nproc` on macOS)

## Building

To build Lean you should use `make -j$(nproc) -C build/release`.

The build uses `ccache`, and in a sandbox `ccache` may complain about read-only file systems.
Use `CCACHE_READONLY` and `CCACHE_TEMPDIR` instead of disabling ccache completely.

### Garbage-collected Nix store paths

On NixOS the CMake caches pin absolute `/nix/store/...` paths for `gmp`, `libuv` and `openssl`.
A `nix-collect-garbage` run deletes those store paths while the caches keep pointing at them, so
the next configure-triggering change (e.g. checking out a revision with a different `stage0/`)
fails with `fatal error: 'gmp.h' file not found` or `clang: error: no such file or directory:
'/nix/store/...-gmp-with-cxx-6.3.0/lib/libgmp.so'`.

Only the caches are stale; the environment's `CMAKE_PREFIX_PATH` still lists live paths. Drop the
pinned entries so the next configure re-detects them, then build as usual:

```bash
script/refresh-cmake-deps.sh stage0/src build/release/stage0
script/refresh-cmake-deps.sh src        build/release/stage1
script/refresh-cmake-deps.sh src        build/release/stage2  # only if stage2 is configured
```

Note the differing source directory: stage0 configures from `stage0/src`, the later stages from
`src`. This only rewrites cache entries; it does not delete build outputs.

## Running Tests

See `tests/README.md` for full documentation. Quick reference:

```bash
# Full test suite (use after builds to verify correctness)
CTEST_PARALLEL_LEVEL="$(nproc)" CTEST_OUTPUT_ON_FAILURE=1 \
make -C build/release -j "$(nproc)" test

# Specific test by name (supports regex via ctest -R; double-quote special chars like |)
CTEST_PARALLEL_LEVEL="$(nproc)" CTEST_OUTPUT_ON_FAILURE=1 \
make -C build/release -j "$(nproc)" test ARGS="-R 'grind_ematch'"

# Multiple tests matching a pattern
CTEST_PARALLEL_LEVEL="$(nproc)" CTEST_OUTPUT_ON_FAILURE=1 \
make -C build/release -j "$(nproc)" test ARGS="-R 'treemap|phashmap'"

# Rerun only previously failed tests
CTEST_PARALLEL_LEVEL="$(nproc)" CTEST_OUTPUT_ON_FAILURE=1 \
make -C build/release -j "$(nproc)" test ARGS='--rerun-failed'

# Run a test manually without ctest (test pile: pass filename relative to the pile dir)
tests/with_stage1_test_env.sh tests/elab_bench/run_bench.sh cbv_decide.lean
tests/with_stage1_test_env.sh tests/elab/run_test.sh grind_indexmap.lean

# Build Lake and run a Lake test (pass directory name relative to `tests/lake`)
tests/lake/run_test.sh tests/ltar
```

## Benchmark vs Test Problem Sizes

Benchmarks are also run as tests. Use the `TEST_BENCH` environment variable (unset in tests, set to `1` in benchmarks) to scale problem sizes:

- In `compile_bench` `.init.sh` files: check `$TEST_BENCH` and set `TEST_ARGS` accordingly
- In `elab_bench` Lean files: use `(← IO.getEnv "TEST_BENCH") == some "1"` to switch between small (test) and large (bench) inputs

See `tests/README.md` for the full benchmark writing guide.

## New features

When asked to implement new features:
* begin by reviewing existing relevant code and tests
* write comprehensive tests first (expecting that these will initially fail)
* and then iterate on the implementation until the tests pass.

## Comments

Inline comments should be concise. Use them for important, non-obvious facts about the code at hand. Avoid comments that:

- restate the code, repeat a type signature, or describe a general API contract;
- document old behavior, rejected alternatives, or the history of the change (that belongs in the PR body or commit message);
- explain API usage that belongs with the API definition instead of this call site.

Rewrite a stale comment instead of adding a new one beside it. If a fact applies generally, document it at the definition.

## Success Criteria

*Never* report success on a task unless you have verified both a clean build without errors, and that the relevant tests pass.

## Build System Safety

**NEVER manually delete build directories** (build/, stage0/, stage1/, etc.) even when builds fail.
- ONLY use the project's documented build command: `make -j$(nproc) -C build/release`
- If a build is broken, ask the user before attempting any manual cleanup

## stage0 Is a Copy of src

**Never manually edit files under `stage0/`.** The `stage0/` directory is a snapshot of `src/` produced by `make update-stage0`. To change anything in stage0 (CMakeLists.txt, C++ source, etc.), edit the corresponding file in `src/` and let `update-stage0` propagate it.

## LSP and IDE Diagnostics

After rebuilding, LSP diagnostics may be stale until the user interacts with files. Trust command-line test results over IDE diagnostics.

## Update prompting when the user is frustrated

If the user expresses frustration with you, stop and ask them to help update this `.claude/CLAUDE.md` file with missing guidance.

## Creating pull requests

Follow the commit convention in `doc/dev/commit_convention.md`.

**Title format:** `<type>: <subject>` where type is one of: `feat`, `fix`, `doc`, `style`, `refactor`, `test`, `chore`, `perf`.
Subject should use imperative present tense ("add" not "added"), no capitalization, no trailing period.

**Body format:** The first paragraph must start with "This PR". This paragraph is automatically incorporated into release notes, so keep it short, focus on user-side impact, and avoid implementation-specific wording. Save the implementation details for a follow-up paragraph. Use imperative present tense. Do NOT use markdown headings (`## Summary`, `## Test plan`, etc.) in PR bodies.

**Line wrapping:** Do NOT hard-wrap lines in commit messages or PR descriptions. Write each paragraph as a single line and let display tools (GitHub, `git log`, terminals) soft-wrap. Bullet lists are still fine; just keep each `* item` body on one line.

Example:
```
feat: add optional binder limit to `mkPatternFromTheorem`

This PR adds a `num?` parameter to `mkPatternFromTheorem` to control how many leading quantifiers are stripped when creating a pattern.
```

**Changelog labels:** Add one `changelog-*` label to categorize the PR for release notes:
- `changelog-language` - Language features and metaprograms
- `changelog-tactics` - User facing tactics
- `changelog-server` - Language server, widgets, and IDE extensions
- `changelog-pp` - Pretty printing
- `changelog-library` - Library
- `changelog-compiler` - Compiler, runtime, and FFI
- `changelog-lake` - Lake
- `changelog-doc` - Documentation
- `changelog-ffi` - FFI changes
- `changelog-other` - Other changes
- `changelog-no` - Do not include this PR in the release changelog

If you're unsure which label applies, it's fine to omit the label and let reviewers add it.

## Module System for `src/` Files

Files in `src/Lean/`, `src/Std/`, and `src/lake/Lake/` must have both `module` and `prelude` (CI enforces `^prelude$` on its own line). With `prelude`, nothing is auto-imported — you must explicitly import `Init.*` modules for standard library features. Check existing files in the same directory for the pattern, e.g.:

```lean
module

prelude
import Init.While  -- needed for while/repeat
import Init.Data.String.TakeDrop  -- needed for String.startsWith
public import Lean.Compiler.NameMangling  -- public if types are used in public signatures
```

Files outside these directories (e.g. `tests/`, `script/`) use just `module`.

## Copyright Headers

New files require a copyright header. To get the year right, always run `date +%Y` rather than relying on memory. The copyright holder should be the author or their current employer — check other recent files by the same author in the repository to determine the correct entity (e.g., "Lean FRO, LLC", "Amazon.com, Inc. or its affiliates").

Test files (in `tests/`) do not need copyright headers.

## Test Module Docstrings

Every test `.lean` file must include a module docstring (`/-! ... -/`) briefly explaining what the file tests. For regression tests, reference the issue (e.g. `#13599`). Place the docstring after the `import` block, if any.

## Rebasing vs PR base

When asked to "rebase a PR onto X", **only change the local branch base** — never change the PR's `--base` target on GitHub unless explicitly told to.

Common Lean4 case: rebasing onto `nightly-with-mathlib` is done to get a mathlib-tested snapshot for CI; the PR still targets `master`.

## Semantic highlighting fork (Kiiyya)

This repo is Max's fork of Lean. Each `releases/vX.Y.Z` branch is the corresponding upstream `leanprover/releases/vX.Y.Z` branch plus **exactly one commit** on top, titled `fork: semantic highlighting + nix toolchain package`, which contains:

- the semantic highlighting patch: extra `SemanticTokenType`/`SemanticTokenModifier` constructors in `src/Lean/Data/Lsp/LanguageFeatures.lean` and the corresponding emitter changes in `src/Lean/Server/FileWorker/SemanticHighlighting.lean`;
- `packages.<system>.default` in `flake.nix`, calling `nix/package.nix` with `version = "X.Y.Z-kiiya"` (`X.Y.Z` = `LEAN_VERSION_*` in `src/CMakeLists.txt`), which builds this fork as a single elan-style toolchain (see the `elan-nix` repo for the consumer side);
- `nix/mimalloc.patch`, which rewrites the `FetchContent_Declare(mimalloc ...)` block in the top-level `CMakeLists.txt` to point at the mimalloc source vendored by `nix/package.nix` (`mimalloc-src`), so the build works offline;
- this section of `.claude/CLAUDE.md`.

Keep it one commit. Never stack cherry-picks of older fork history on top; take the diff of the previous release's fork commit and re-apply it.

### Porting the fork to a new upstream release

1. `git fetch leanprover --tags` and base on the release *branch* tip, not the tag: `git checkout -b releases/vX.Y.Z leanprover/releases/vX.Y.Z` (the branch may carry backports after the tag).
2. Apply the previous release's fork commit as a single change: `git cherry-pick -n <prev fork commit>` (`-n` keeps it uncommitted). Resolve conflicts in the two highlighting files if upstream touched them.
3. Check what the packaging depends on and adapt:
   - `grep -n -A12 'if(USE_MIMALLOC)' CMakeLists.txt` — regenerate `nix/mimalloc.patch` so its context matches (only `GIT_REPOSITORY`/`GIT_BRANCH`/`GIT_TAG`/comment lines and the `SOURCE_DIR` value are removed; `SOURCE_DIR` becomes `"MIMALLOC-SRC"`). Generate it with a real `diff -u`, never by hand, and verify with `patch --dry-run -p1 < nix/mimalloc.patch`.
   - Set `mimalloc-src.tag` in `nix/package.nix` to the `GIT_TAG` above and get the hash with `nix store prefetch-file --json --unpack https://github.com/microsoft/mimalloc/archive/refs/tags/<tag>.tar.gz`.
   - `grep -n 'mimalloc/src/mimalloc' stage0/src/CMakeLists.txt src/CMakeLists.txt src/runtime/CMakeLists.txt` — the `postPatch` in `nix/package.nix` substitutes this path; if upstream renames it, update `pattern` there.
   - `grep -n 'find_package' src/CMakeLists.txt` — add/remove `buildInputs` in `nix/package.nix` accordingly (e.g. `openssl` became required in 4.32).
   - Bump `version` in `flake.nix` to `X.Y.Z-kiiya`.
4. Verify with `nix build .#default -L` (≈15–20 min) and `./result/bin/lean --version` (must print `X.Y.Z-kiiya`).
5. Commit everything as one commit (`fork: semantic highlighting + nix toolchain package`), including the `flake.lock` bump if one was needed. Do not push; Max pushes to `Kiiyya`.

Known per-version differences seen so far: 4.30 used `ExternalProject_Add`; 4.32/4.33 use `FetchContent_Declare` with mimalloc `v2.2.3`; 4.34 adds `GIT_BRANCH dev3` and mimalloc `v3.4.4`.
