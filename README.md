


- Install landrun as per their instructions
- and comparator




# dLean

dLean is a Lean 4 library for differential dynamic logic. This repository also contains small
proof problems that can be given to coding agents and checked independently with Lean Comparator.

The benchmark harness supports:

- OpenAI Codex CLI
- Anthropic Claude Code
- a manually produced `Solution.lean`

The agent receives the selected challenge and the reusable dLean library. The harness never copies
the `dLean/Examples/` directory into the sandbox.

## Build dLean

The project currently uses Lean `v4.34.0-rc2` and the matching Mathlib release.

Install [elan](https://github.com/leanprover/elan), then run:

```sh
git clone YOUR_DLEAN_REPOSITORY_URL
cd dLean
lake update
lake exe cache get
lake build
```

`lake exe cache get` downloads precompiled Mathlib artifacts. It is optional, but building without
the cache takes considerably longer.

## Benchmark prerequisites

The complete automated runner is currently intended for Linux because the Comparator stage uses a
systemd user unit. Install:

- Bash, Git, `timeout`, and standard GNU command-line tools
- systemd with a working user manager (`systemd-run --user`)
- Lean Comparator and a real Landrun executable
- at least one supported agent CLI

The harness itself does not invoke Bubblewrap. Codex and Claude use their own native sandbox
interfaces. On Linux, both native implementations currently use Bubblewrap internally, and Claude
also requires `socat`. On macOS, they use Seatbelt instead.

### Codex CLI

Install Codex using the [official Codex CLI instructions](https://learn.chatgpt.com/docs/codex/cli):

```sh
curl -fsSL https://chatgpt.com/codex/install.sh | sh
codex login
```

The runner uses the documented non-interactive `codex exec` interface and a native permission
profile. The profile grants write access only to the generated agent workspace, read access to the
shared Lean package cache, minimal runtime files, and the installed Codex runtime itself, and no
command network access. The Codex runtime access is read-only and is required because Codex
re-executes its native binary when it starts sandboxed commands. The active Lean toolchain selected
by `lean-toolchain` is also resolved before launch and exposed read-only; its `bin` directory is put
on the agent command path. If the standard Codex `lean4` and `lean-proof` skills are installed,
their exact directories are exposed read-only as well. The run is ephemeral, ignores personal
configuration and execution-policy rules, never asks for approval, and also disables Codex's
separate hosted web-search tool. The Codex controller can still contact the model API. Use a current
Codex CLI with permission-profile support. See the
[Codex non-interactive mode documentation](https://learn.chatgpt.com/docs/non-interactive-mode)
and [permission-profile documentation](https://learn.chatgpt.com/docs/permissions).

### Claude Code

Install Claude Code using the
[official getting-started instructions](https://code.claude.com/docs/en/getting-started):

```sh
curl -fsSL https://claude.ai/install.sh | bash
claude
```

Complete authentication in the interactive command, then exit it. The harness uses `claude -p`
with stream-JSON output, no session persistence, and restricted mode. It enables Claude's command
sandbox with an empty strict network allowlist, denies reading the original dLean checkout except
for the generated agent workspace and shared Lean package cache, disables unsandboxed retries, and
fails instead of falling back if the sandbox is unavailable. The harness does not wrap Claude in
Bubblewrap. Restricted mode requires Claude Code 2.1.248 or newer; check with:

```sh
claude --version
```

See the official [Claude Code CLI reference](https://code.claude.com/docs/en/cli-usage) and
[sandbox documentation](https://code.claude.com/docs/en/sandboxing).

### Lean Comparator

Clone Lean Comparator separately and follow that repository's installation instructions. Its
`lean4export` dependency must support the same Lean version as dLean. In the Comparator checkout,
build both required executables:

```sh
lake build lean4export comparator
```

Install a real Landrun executable. Do not use Comparator's `fake-landrun.sh` for agent-generated or
otherwise untrusted code: the fake script is a development shim, not a security boundary.

Point the benchmark harness to the tools:

```sh
export COMPARATOR_ROOT=/absolute/path/to/comparator
export COMPARATOR_LANDRUN=/absolute/path/to/landrun
```

By default, `COMPARATOR_ROOT` resolves these paths:

```text
$COMPARATOR_ROOT/.lake/build/bin/comparator
$COMPARATOR_ROOT/.lake/packages/lean4export/.lake/build/bin/lean4export
```

If your layout differs, set `COMPARATOR_BIN` and `COMPARATOR_LEAN4EXPORT` explicitly.

## Run a benchmark

List the available problems:

```sh
agentic/prove.sh list
```

Run Codex and judge its result:

```sh
agentic/prove.sh run BouncingBall codex
```

Run Claude Code and judge its result:

```sh
agentic/prove.sh run BouncingBall claude
```

Choose a model or impose a shorter wall-clock limit when needed:

```sh
agentic/prove.sh run VectorBraking codex \
  --model MODEL_NAME \
  --timeout 1800

agentic/prove.sh run QdLCars claude \
  --model MODEL_NAME \
  --timeout 1800 \
  --max-turns 80
```

Omit `--model` to use the CLI's configured default. The default timeout is 3600 seconds and the
default Claude turn limit is 100.

Each run is written to a new directory under `benchmark-results/`:

```text
benchmark-results/TIMESTAMP-PROBLEM-AGENT/
├── trusted/              # isolated judge project built before the agent starts
├── agent/                # small agent workspace and resulting Solution.lean
├── agent-output.jsonl    # machine-readable CLI event stream
├── agent-stderr.log
└── result.txt            # agent and Comparator exit codes
```

The command returns a nonzero exit code if the agent fails or Comparator rejects the solution.
`result.txt` records both exit codes and the solution path.

Useful run options:

```text
--model MODEL
--timeout SECONDS
--max-turns NUMBER        Claude Code only
--output DIRECTORY
--skip-judge              development only
--unsafe-no-systemd       development only
```

Use `agentic/prove.sh help` for the complete command summary.

## Run the stages separately

Prepare the exact project that an agent will receive:

```sh
agentic/prove.sh prepare BouncingBall /tmp/bouncing-ball-sandbox
(cd /tmp/bouncing-ball-sandbox && lake env lean Solution.lean)
```

The prepared directory is a standalone Git repository for the dLean source snapshot. Its
`.lake/packages` is a link to the dependency cache in the trusted dLean checkout, so Mathlib is not
copied for every problem or run. Edit only `Solution.lean`.

Run Codex in that prepared project:

```sh
agentic/prove.sh agent codex /tmp/bouncing-ball-sandbox
```

Or run Claude Code:

```sh
agentic/prove.sh agent claude /tmp/bouncing-ball-sandbox \
  --timeout 1800 \
  --max-turns 80
```

The `agent` command accepts `--model`, `--timeout`, and `--max-turns`, and uses the same native
sandbox configuration as the combined `run` command. It writes the event stream and diagnostic
output to `agent-output.jsonl` and `agent-stderr.log` inside the prepared directory. The resulting
proof remains in `Solution.lean`.

The proof-task instructions are maintained in `agentic/AGENTS.md`. During preparation, the harness
copies that file to both `AGENTS.md` and `CLAUDE.md` in the generated workspace so Codex and Claude
receive the same instructions.

Finally, judge the solution. The harness creates a new trusted project and copies only
`Solution.lean` into it:

```sh
agentic/prove.sh judge BouncingBall /absolute/path/to/Solution.lean
```

For the example above, the complete separate-stage workflow is:

```sh
agentic/prove.sh prepare BouncingBall /tmp/bouncing-ball-sandbox
agentic/prove.sh agent codex /tmp/bouncing-ball-sandbox
agentic/prove.sh judge BouncingBall /tmp/bouncing-ball-sandbox/Solution.lean
```

An optional third positional argument selects where the judge project is retained:

```sh
agentic/prove.sh judge BouncingBall solution.lean /tmp/comparator-judge
```

## What the agent can see

For every run, the harness copies only:

- `dLean/Core/`
- `dLean/Tactic/`
- `dLean.lean`
- the selected `Challenge.lean`, also copied initially to `Solution.lean`
- the selected `config.json`
- the Lake manifest, project configuration, and Lean toolchain file
- a link to the trusted dependency packages from `.lake/packages`; native agent sandboxes expose
  the link target read-only
- the active Lean toolchain selected by `lean-toolchain`, exposed read-only
- `.agents/skills/dlean-prover/SKILL.md`, copied from `agentic/skills/dlean-prover/`
- for Codex, the installed `lean4` and `lean-proof` skill directories, when present, exposed
  read-only

It deliberately does not copy:

- `dLean/Examples/`
- this repository's `.git/`
- this repository's `.lake/build/` or compiled dLean/example artifacts
- local Codex memories/session logs or Claude project-history directories

The trusted challenge is compiled before the agent runs. The agent workspace is a separate clean
copy with read-only sandbox access to the dependency packages. Afterward, only the agent's
`Solution.lean` is copied back to the untouched trusted judge project. Thus the judge does not reuse
artifacts compiled by the agent.

## Security model and limitations

The harness combines several layers:

1. It creates a minimal, sanitized project instead of copying the whole repository.
2. It configures Codex's native permission profile or Claude's native restricted sandbox. The
   generated agent project is writable, the shared dependency cache is read-only, the original
   dLean checkout is unavailable, and tool commands have no network access. Codex additionally
   receives read-only access to its own resolved installation package so its sandbox can launch.
   Both agents receive read-only access to the active Lean toolchain. Codex additionally receives
   read-only access to the exact `lean4` and `lean-proof` skill directories when they are installed;
   other Codex data, including memories and session logs, remains unavailable.
3. It runs Comparator through Landrun and, by default, a transient systemd user unit with
   Unix-domain sockets disabled.

The Codex or Claude controller process still requires network connectivity to contact its model API.
Commands and child processes launched as agent tools have network access disabled: Codex uses an
explicit network-off permission profile, while Claude uses a strict empty domain allowlist with
unsandboxed retries disabled.

Native sandbox policy is enforced by the installed agent CLI and the operating system. The harness
fails if the requested Claude sandbox is unavailable; an obsolete Codex CLI should reject the
permission-profile options instead of running the task. Organization-managed agent configuration
may impose additional restrictions or reject the requested settings.

This convenience harness is still not a complete hostile-code containment system. For
publication-quality or adversarial evaluations, run it from a dedicated unprivileged OS account,
container, or virtual machine that contains no private proofs or unrelated credentials. Keep
Comparator and Landrun outside the agent workspace.

If reference `Proof.lean` files are committed to a public repository or remain in its public Git
history, local sandboxing cannot make them secret: an agent may already know them or retrieve them
over the network. Keep reference proofs in a separate private repository or an unpublished private
branch, and publish only challenges plus configuration when benchmark secrecy matters.

The `--unsafe-no-systemd` switch removes one Comparator isolation layer and should only be used for
local debugging. The script refuses `fake-landrun.sh` for judging.

## Reproducibility

Every generated project includes `benchmark-metadata.txt` with:

- the problem name
- the Lean toolchain
- a SHA-256 fingerprint of the copied dLean source and project files
- the source repository commit and dirty-worktree flag, when available

For comparable experiments, also record the agent CLI version, the exact model identifier, timeout,
turn limit, Comparator commit, Landrun version, and the revisions in `lake-manifest.json`. The event
stream is retained in `agent-output.jsonl` for later usage and timing analysis.

## Add a benchmark problem

Create a directory under `dLean/Examples/` containing:

```text
dLean/Examples/MyProblem/
├── Challenge.lean
├── config.json
└── Proof.lean            # optional private reference proof
```

The challenge file contains the definitions, statement, and a placeholder proof. For example:

```lean
import dLean

def answer : Nat := 42

theorem answer_is_42 : answer = 42 := by
  sorry
```

Configure Comparator to compare the theorem in `Solution` with the trusted theorem in `Challenge`:

```json
{
  "challenge_module": "Challenge",
  "solution_module": "Solution",
  "theorem_names": ["answer_is_42"],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
  "enable_nanoda": false
}
```

Use the exact configuration schema supported by your Lean Comparator version. Confirm the new
problem before involving an agent:

```sh
agentic/prove.sh prepare MyProblem /tmp/my-problem
```

## Troubleshooting

`set COMPARATOR_ROOT or COMPARATOR_BIN`

: Export `COMPARATOR_ROOT`, or explicitly export both `COMPARATOR_BIN` and
  `COMPARATOR_LEAN4EXPORT`.

Comparator or `lean4export` fails after a Lean upgrade

: Update Comparator and its `lean4export` dependency to versions compatible with the Lean version
  in `lean-toolchain`, then rebuild both executables.

`systemd-run --user` cannot connect to the user manager

: Run the benchmark in a login session with a working systemd user manager. The
  `--unsafe-no-systemd` fallback removes this hardening and is intended only for trusted debugging.

Claude reports that `--restricted` is unknown

: Upgrade Claude Code to version 2.1.248 or newer.

Claude reports that its sandbox is unavailable

: Install the platform prerequisites required by Claude Code. On Linux, its native sandbox
  currently requires Bubblewrap and `socat`; on macOS it uses Seatbelt. The harness intentionally
  does not provide an unsandboxed fallback.

The dependency cache is missing

: Run `lake update && lake exe cache get` in the dLean checkout. The harness links this shared cache
  into each generated project, grants agents read-only sandbox access to it, and never copies the
  full Mathlib tree per run.
