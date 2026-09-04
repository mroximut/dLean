#!/usr/bin/env bash

set -Eeuo pipefail

readonly SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
readonly REPO_ROOT="$(cd -- "$SCRIPT_DIR/.." && pwd)"
readonly EXAMPLES_DIR="$REPO_ROOT/dLean/Examples"

die() {
  echo "error: $*" >&2
  exit 1
}

note() {
  echo "==> $*" >&2
}

usage() {
  sed -n '18,62p' "$0" | sed -n 's/^# \{0,1\}//p'
}

# dLean proof-agent benchmark harness
#
# Usage:
#   agentic/prove.sh list
#   agentic/prove.sh prepare PROBLEM [OUTPUT_DIRECTORY]
#   agentic/prove.sh agent AGENT SANDBOX [OPTIONS]
#   agentic/prove.sh judge PROBLEM SOLUTION_FILE [OUTPUT_DIRECTORY]
#   agentic/prove.sh run PROBLEM AGENT [OPTIONS]
#
# Agents:
#   codex
#   claude
#
# Agent options:
#   --model MODEL             Select the agent model.
#   --timeout SECONDS         Stop the agent after this many seconds (default: 3600).
#   --max-turns NUMBER        Claude Code turn limit (default: 100).
#
# Additional run options:
#   --output DIRECTORY        Store the complete run in this directory.
#   --skip-judge              Run the agent but do not invoke Comparator.
#   --unsafe-no-systemd       Invoke Comparator without the documented systemd wrapper.
#
# Comparator environment:
#   COMPARATOR_ROOT           Comparator checkout containing .lake/build/bin/comparator.
#   COMPARATOR_BIN            Explicit Comparator executable; overrides COMPARATOR_ROOT.
#   COMPARATOR_LEAN4EXPORT    lean4export executable compatible with this Lean toolchain.
#   COMPARATOR_LANDRUN        Real landrun executable. The fake shim is rejected by default.
#
# Other environment:
#   CODEX_BIN=codex
#   CLAUDE_BIN=claude
#   ELAN_BIN=elan
#       Override agent and toolchain executables.

require_command() {
  command -v "$1" >/dev/null 2>&1 || die "required command not found: $1"
}

resolve_executable() {
  local value="$1"
  if [[ "$value" == */* ]]; then
    [[ -x "$value" ]] || die "not executable: $value"
    realpath "$value"
  else
    command -v "$value" || die "executable not found: $value"
  fi
}

problem_dir() {
  local problem="$1"
  [[ "$problem" =~ ^[A-Za-z0-9_-]+$ ]] || die "invalid problem name: $problem"
  local dir="$EXAMPLES_DIR/$problem"
  [[ -d "$dir" ]] || die "unknown problem '$problem'; run '$0 list'"
  printf '%s\n' "$dir"
}

list_problems() {
  local dir
  for dir in "$EXAMPLES_DIR"/*; do
    [[ -d "$dir" && -f "$dir/config.json" ]] || continue
    if [[ -f "$dir/Challenge.lean" ]]; then
      basename "$dir"
    fi
  done
}

write_project_lakefile() {
  local destination="$1"
  cp "$REPO_ROOT/lakefile.toml" "$destination/lakefile.toml"
  cat >> "$destination/lakefile.toml" <<'EOF'

[[lean_lib]]
name = "Challenge"

[[lean_lib]]
name = "Solution"
EOF
}

write_agent_instructions() {
  local destination="$1"
  local instructions="$SCRIPT_DIR/AGENTS.md"
  [[ -f "$instructions" ]] || die "missing benchmark agent instructions: $instructions"
  cp "$instructions" "$destination/AGENTS.md"
  cp "$destination/AGENTS.md" "$destination/CLAUDE.md"
}

copy_dlean_skill() {
  local destination="$1"
  local skill="$SCRIPT_DIR/skills/dlean-prover"
  [[ -f "$skill/SKILL.md" ]] || die "missing dLean prover skill: $skill/SKILL.md"
  mkdir -p "$destination/.agents/skills"
  cp -a "$skill" "$destination/.agents/skills/dlean-prover"
}

write_workspace_gitignore() {
  local destination="$1"
  cat > "$destination/.gitignore" <<'EOF'
/.lake
/.tmp
/agent-output.jsonl
/agent-stderr.log
EOF
}

link_packages() {
  local destination="$1"
  [[ -d "$REPO_ROOT/.lake/packages/mathlib" ]] ||
    die "missing trusted dependency cache; run 'lake update && lake exe cache get' in $REPO_ROOT"
  note "Linking the shared, trusted dependency package cache"
  mkdir -p "$destination/.lake"
  ln -s "$REPO_ROOT/.lake/packages" "$destination/.lake/packages"
}

source_fingerprint() {
  (
    cd "$REPO_ROOT"
    find dLean/Core dLean/Tactic -type f -name '*.lean' -print0
    printf '%s\0' dLean.lean lakefile.toml lake-manifest.json lean-toolchain \
      agentic/AGENTS.md agentic/skills/dlean-prover/SKILL.md
  ) | sort -z | while IFS= read -r -d '' path; do
    sha256sum "$REPO_ROOT/$path"
  done | sha256sum | cut -d ' ' -f 1
}

create_project() {
  local problem="$1"
  local destination="$2"
  local initialize_git="${3:-0}"
  local dir challenge
  dir="$(problem_dir "$problem")"
  challenge="$dir/Challenge.lean"
  [[ -f "$challenge" ]] || die "missing Challenge.lean in $dir"

  [[ ! -e "$destination" ]] || die "output already exists: $destination"
  mkdir -p "$destination/dLean"
  cp -a "$REPO_ROOT/dLean/Core" "$destination/dLean/Core"
  cp -a "$REPO_ROOT/dLean/Tactic" "$destination/dLean/Tactic"
  cp "$REPO_ROOT/dLean.lean" "$destination/dLean.lean"
  cp "$REPO_ROOT/lean-toolchain" "$destination/lean-toolchain"
  cp "$REPO_ROOT/lake-manifest.json" "$destination/lake-manifest.json"
  cp "$dir/config.json" "$destination/config.json"
  cp "$challenge" "$destination/Challenge.lean"
  cp "$challenge" "$destination/Solution.lean"
  write_project_lakefile "$destination"
  write_agent_instructions "$destination"
  copy_dlean_skill "$destination"
  write_workspace_gitignore "$destination"
  link_packages "$destination"

  {
    echo "problem=$problem"
    echo "source_fingerprint=$(source_fingerprint)"
    echo "lean_toolchain=$(tr -d '\r\n' < "$REPO_ROOT/lean-toolchain")"
    if git -C "$REPO_ROOT" rev-parse --verify HEAD >/dev/null 2>&1; then
      echo "git_commit=$(git -C "$REPO_ROOT" rev-parse HEAD)"
      if [[ -n "$(git -C "$REPO_ROOT" status --porcelain)" ]]; then
        echo "git_dirty=true"
      else
        echo "git_dirty=false"
      fi
    fi
  } > "$destination/benchmark-metadata.txt"

  note "Building the trusted challenge snapshot"
  (cd "$destination" && lake build Challenge)

  if [[ "$initialize_git" == "1" ]]; then
    init_agent_git "$destination"
  fi
}

create_agent_project() {
  local source="$1"
  local destination="$2"
  [[ ! -e "$destination" ]] || die "output already exists: $destination"
  mkdir -p "$destination/dLean" "$destination/.lake/packages"
  cp -a "$source/dLean/Core" "$destination/dLean/Core"
  cp -a "$source/dLean/Tactic" "$destination/dLean/Tactic"
  cp "$source/dLean.lean" "$destination/dLean.lean"
  cp "$source/Challenge.lean" "$destination/Challenge.lean"
  cp "$source/Solution.lean" "$destination/Solution.lean"
  cp "$source/config.json" "$destination/config.json"
  cp "$source/lakefile.toml" "$destination/lakefile.toml"
  cp "$source/lake-manifest.json" "$destination/lake-manifest.json"
  cp "$source/lean-toolchain" "$destination/lean-toolchain"
  cp "$source/AGENTS.md" "$destination/AGENTS.md"
  cp "$source/CLAUDE.md" "$destination/CLAUDE.md"
  cp -a "$source/.agents" "$destination/.agents"
  cp "$source/.gitignore" "$destination/.gitignore"
  cp "$source/benchmark-metadata.txt" "$destination/benchmark-metadata.txt"
  cp -a --reflink=auto "$source/.lake/build" "$destination/.lake/build"
}

init_agent_git() {
  local destination="$1"
  [[ ! -e "$destination/.git" ]] || die "refusing to replace existing Git data in $destination"
  git -C "$destination" init -q
  git -C "$destination" add .agents AGENTS.md CLAUDE.md Challenge.lean Solution.lean config.json \
    dLean dLean.lean lakefile.toml lake-manifest.json lean-toolchain \
    benchmark-metadata.txt .gitignore
  git -C "$destination" -c user.name='dLean Benchmark' \
    -c user.email='benchmark@example.invalid' commit -qm 'Initial sanitized benchmark'
}

agent_prompt() {
  cat <<'EOF'
Complete the Lean proof task described in AGENTS.md. Work autonomously on Solution.lean, inspect the
local dLean library as needed, and repeatedly run `lake env lean Solution.lean` while developing the
proof. Do not stop at a plan or explanation: leave the completed proof in Solution.lean.
EOF
}

run_agent() {
  local workspace="$1"
  local packages="$2"
  local agent="$3"
  local model="$4"
  local timeout_seconds="$5"
  local max_turns="$6"
  local stdout_file="$7"
  local stderr_file="$8"
  local prompt agent_cwd claude_settings codex_filesystem codex_shell_environment
  local codex_skill_permissions=""
  local elan_bin toolchain_lake toolchain_bin toolchain_root sandbox_path
  prompt="$(agent_prompt)"
  agent_cwd="$workspace"
  packages="$(realpath "$packages")"
  elan_bin="$(resolve_executable "${ELAN_BIN:-elan}")"
  toolchain_lake="$(cd "$workspace" && "$elan_bin" which lake)" ||
    die "could not resolve the Lean toolchain for $workspace"
  toolchain_lake="$(realpath "$toolchain_lake")"
  [[ -x "$toolchain_lake" ]] || die "resolved lake executable is not usable: $toolchain_lake"
  toolchain_bin="$(dirname "$toolchain_lake")"
  toolchain_root="$(dirname "$toolchain_bin")"
  sandbox_path="$toolchain_bin:/usr/local/bin:/usr/bin:/bin"
  [[ "$packages" != *'"'* && "$packages" != *'\\'* && "$packages" != *$'\n'* ]] ||
    die "dependency path cannot be encoded safely: $packages"
  [[ "$workspace" != *'"'* && "$workspace" != *'\\'* && "$workspace" != *$'\n'* ]] ||
    die "workspace path cannot be encoded safely: $workspace"
  [[ "$REPO_ROOT" != *'"'* && "$REPO_ROOT" != *'\\'* && "$REPO_ROOT" != *$'\n'* ]] ||
    die "repository path cannot be encoded safely: $REPO_ROOT"
  [[ "$HOME" != *'"'* && "$HOME" != *'\\'* && "$HOME" != *$'\n'* ]] ||
    die "home path cannot be encoded safely: $HOME"
  [[ "$toolchain_root" != *'"'* && "$toolchain_root" != *'\\'* &&
      "$toolchain_root" != *$'\n'* ]] ||
    die "Lean toolchain path cannot be encoded safely: $toolchain_root"
  local skill_path
  for skill_path in "$HOME/.codex/skills/lean4" "$HOME/.codex/skills/lean-proof"; do
    [[ -d "$skill_path" ]] || continue
    skill_path="$(realpath "$skill_path")"
    [[ "$skill_path" != *'"'* && "$skill_path" != *'\\'* && "$skill_path" != *$'\n'* ]] ||
      die "Codex skill path cannot be encoded safely: $skill_path"
    codex_skill_permissions+=",\"$skill_path\"=\"read\""
  done
  mkdir -p "$workspace/.tmp"
  if [[ -L "$workspace/.lake/packages" ]]; then
    unlink "$workspace/.lake/packages"
  elif [[ -d "$workspace/.lake/packages" ]]; then
    rmdir "$workspace/.lake/packages" ||
      die "refusing to replace nonempty dependency directory: $workspace/.lake/packages"
  else
    die "missing dependency link: $workspace/.lake/packages"
  fi
  ln -s "$packages" "$workspace/.lake/packages"

  printf -v claude_settings \
    '{"sandbox":{"enabled":true,"failIfUnavailable":true,"allowUnsandboxedCommands":false,"filesystem":{"denyRead":["%s","%s/.codex/memories","%s/.codex/sessions","%s/.claude/projects"],"allowRead":["%s","%s","%s"]},"network":{"allowedDomains":[],"strictAllowlist":true}}}' \
    "$REPO_ROOT" "$HOME" "$HOME" "$HOME" "$workspace" "$packages" "$toolchain_root"

  local -a command
  case "$agent" in
    codex)
      local codex_bin codex_entry codex_runtime
      codex_bin="$(resolve_executable "${CODEX_BIN:-codex}")"
      codex_entry="$(realpath "$codex_bin")"
      case "$codex_entry" in
        */node_modules/@openai/codex/bin/codex.js)
          codex_runtime="${codex_entry%/bin/codex.js}"
          ;;
        *)
          codex_runtime="$codex_entry"
          ;;
      esac
      [[ "$codex_runtime" != *'"'* && "$codex_runtime" != *'\\'* &&
          "$codex_runtime" != *$'\n'* ]] ||
        die "Codex runtime path cannot be encoded safely: $codex_runtime"
      printf -v codex_filesystem \
        'permissions.dlean-benchmark.filesystem={":minimal"="read","%s"="write","%s"="read","%s"="read","%s"="read"%s}' \
        "$workspace" "$packages" "$codex_runtime" "$toolchain_root" "$codex_skill_permissions"
      printf -v codex_shell_environment \
        'shell_environment_policy={inherit="core",set={PATH="%s"},ignore_default_excludes=false}' \
        "$sandbox_path"
      command=(
        "$codex_bin"
        --ask-for-approval never
        exec
        --ephemeral
        --json
        --skip-git-repo-check
        --ignore-user-config
        --ignore-rules
        --config 'default_permissions="dlean-benchmark"'
        --config "$codex_filesystem"
        --config "$codex_shell_environment"
        --config 'permissions.dlean-benchmark.network.enabled=false'
        --config 'web_search="disabled"'
        -C "$agent_cwd"
      )
      [[ -n "$model" ]] && command+=(--model "$model")
      command+=("$prompt")
      ;;
    claude)
      local claude_bin
      claude_bin="$(resolve_executable "${CLAUDE_BIN:-claude}")"
      command=(
        "$claude_bin"
        --restricted
        --settings "$claude_settings"
        --tools Bash,Edit,Read,Write,Glob,Grep
        --allowedTools Bash,Edit,Read,Write,Glob,Grep
        --disallowedTools 'mcp__*'
        --permission-mode dontAsk
        --no-session-persistence
        --max-turns "$max_turns"
        --print
        --verbose
        --output-format stream-json
      )
      [[ -n "$model" ]] && command+=(--model "$model")
      command+=("$prompt")
      ;;
    *)
      die "unknown agent '$agent'; expected codex or claude"
      ;;
  esac

  note "Running $agent in $workspace"
  set +e
  TMPDIR="$workspace/.tmp" timeout --signal=TERM --kill-after=30 "$timeout_seconds" \
    bash -c 'cd "$1" && shift && exec "$@"' benchmark-agent "$workspace" "${command[@]}" \
    > >(tee "$stdout_file") 2> >(tee "$stderr_file" >&2)
  local status=$?
  set -e
  return "$status"
}

comparator_paths() {
  local comparator_bin="${COMPARATOR_BIN:-}"
  local lean4export="${COMPARATOR_LEAN4EXPORT:-}"
  local landrun="${COMPARATOR_LANDRUN:-landrun}"

  if [[ -z "$comparator_bin" && -n "${COMPARATOR_ROOT:-}" ]]; then
    comparator_bin="$COMPARATOR_ROOT/.lake/build/bin/comparator"
  fi
  if [[ -z "$lean4export" && -n "${COMPARATOR_ROOT:-}" ]]; then
    lean4export="$COMPARATOR_ROOT/.lake/packages/lean4export/.lake/build/bin/lean4export"
  fi

  [[ -n "$comparator_bin" ]] || die "set COMPARATOR_ROOT or COMPARATOR_BIN"
  [[ -n "$lean4export" ]] || die "set COMPARATOR_ROOT or COMPARATOR_LEAN4EXPORT"
  comparator_bin="$(resolve_executable "$comparator_bin")"
  lean4export="$(resolve_executable "$lean4export")"
  landrun="$(resolve_executable "$landrun")"

  [[ "$landrun" != *fake-landrun.sh ]] || die "refusing fake-landrun.sh for an untrusted solution"
  printf '%s\n%s\n%s\n' "$comparator_bin" "$lean4export" "$landrun"
}

run_comparator() {
  local judge_dir="$1"
  local use_systemd="$2"
  local -a paths
  mapfile -t paths < <(comparator_paths)
  local comparator_bin="${paths[0]}"
  local lean4export="${paths[1]}"
  local landrun="${paths[2]}"

  note "Judging Solution.lean with Lean Comparator"
  if [[ "$use_systemd" == "1" ]]; then
    require_command systemd-run
    systemd-run \
      --user \
      --wait \
      --pipe \
      --collect \
      --quiet \
      --property=RestrictAddressFamilies=~AF_UNIX \
      --working-directory="$judge_dir" \
      --setenv=PATH="$PATH" \
      --setenv=COMPARATOR_LANDRUN="$landrun" \
      --setenv=COMPARATOR_LEAN4EXPORT="$lean4export" \
      -- \
      lake env "$comparator_bin" config.json
  else
    echo "WARNING: invoking Comparator without the documented systemd hardening" >&2
    (
      cd "$judge_dir"
      COMPARATOR_LANDRUN="$landrun" \
        COMPARATOR_LEAN4EXPORT="$lean4export" \
        lake env "$comparator_bin" config.json
    )
  fi
}

prepare_command() {
  [[ $# -ge 1 && $# -le 2 ]] || die "usage: $0 prepare PROBLEM [OUTPUT_DIRECTORY]"
  local problem="$1"
  local destination="${2:-$(pwd)/${problem}-sandbox}"
  destination="$(realpath -m "$destination")"
  create_project "$problem" "$destination" 1
  echo "$destination"
}

agent_command() {
  [[ $# -ge 2 ]] || die "usage: $0 agent AGENT SANDBOX [OPTIONS]"
  local agent="$1"
  local workspace="$2"
  shift 2

  local model=""
  local timeout_seconds=3600
  local max_turns=100
  while [[ $# -gt 0 ]]; do
    case "$1" in
      --model)
        [[ $# -ge 2 ]] || die "--model requires a value"
        model="$2"
        shift 2
        ;;
      --timeout)
        [[ $# -ge 2 && "$2" =~ ^[1-9][0-9]*$ ]] || die "--timeout requires positive seconds"
        timeout_seconds="$2"
        shift 2
        ;;
      --max-turns)
        [[ $# -ge 2 && "$2" =~ ^[1-9][0-9]*$ ]] || die "--max-turns requires a positive number"
        max_turns="$2"
        shift 2
        ;;
      *)
        die "unknown option: $1"
        ;;
    esac
  done

  [[ "$agent" == "codex" || "$agent" == "claude" ]] ||
    die "unknown agent '$agent'; expected codex or claude"
  workspace="$(realpath "$workspace")"
  local required
  for required in .agents/skills/dlean-prover/SKILL.md AGENTS.md Challenge.lean Solution.lean \
      config.json lakefile.toml \
      lake-manifest.json lean-toolchain dLean/Core dLean/Tactic .lake/packages; do
    [[ -e "$workspace/$required" || -L "$workspace/$required" ]] ||
      die "not a prepared benchmark sandbox; missing $workspace/$required"
  done
  require_command timeout
  require_command tee

  local agent_status=0
  run_agent "$workspace" "$REPO_ROOT/.lake/packages" "$agent" "$model" "$timeout_seconds" \
    "$max_turns" "$workspace/agent-output.jsonl" "$workspace/agent-stderr.log" \
    || agent_status=$?

  echo
  echo "Agent workspace: $workspace"
  echo "Agent exit code: $agent_status"
  echo "Solution: $workspace/Solution.lean"
  return "$agent_status"
}

judge_command() {
  [[ $# -ge 2 && $# -le 4 ]] || \
    die "usage: $0 judge PROBLEM SOLUTION_FILE [OUTPUT_DIRECTORY] [--unsafe-no-systemd]"
  local problem="$1"
  local solution="$2"
  shift 2
  local destination=""
  local use_systemd=1
  while [[ $# -gt 0 ]]; do
    case "$1" in
      --unsafe-no-systemd) use_systemd=0 ;;
      *)
        [[ -z "$destination" ]] || die "unexpected argument: $1"
        destination="$1"
        ;;
    esac
    shift
  done
  [[ -f "$solution" ]] || die "solution file not found: $solution"
  if [[ -z "$destination" ]]; then
    local temporary_root
    temporary_root="$(mktemp -d "${TMPDIR:-/tmp}/dlean-judge.XXXXXX")"
    destination="$temporary_root/project"
  fi
  destination="$(realpath -m "$destination")"
  create_project "$problem" "$destination" 0
  cp "$solution" "$destination/Solution.lean"
  run_comparator "$destination" "$use_systemd"
  echo "$destination"
}

run_command() {
  [[ $# -ge 2 ]] || die "usage: $0 run PROBLEM AGENT [OPTIONS]"
  local problem="$1"
  local agent="$2"
  shift 2

  local model=""
  local timeout_seconds=3600
  local max_turns=100
  local output=""
  local skip_judge=0
  local use_systemd=1

  while [[ $# -gt 0 ]]; do
    case "$1" in
      --model)
        [[ $# -ge 2 ]] || die "--model requires a value"
        model="$2"
        shift 2
        ;;
      --timeout)
        [[ $# -ge 2 && "$2" =~ ^[1-9][0-9]*$ ]] || die "--timeout requires positive seconds"
        timeout_seconds="$2"
        shift 2
        ;;
      --max-turns)
        [[ $# -ge 2 && "$2" =~ ^[1-9][0-9]*$ ]] || die "--max-turns requires a positive number"
        max_turns="$2"
        shift 2
        ;;
      --output)
        [[ $# -ge 2 ]] || die "--output requires a directory"
        output="$2"
        shift 2
        ;;
      --skip-judge)
        skip_judge=1
        shift
        ;;
      --unsafe-no-systemd)
        use_systemd=0
        shift
        ;;
      *)
        die "unknown option: $1"
        ;;
    esac
  done

  [[ "$agent" == "codex" || "$agent" == "claude" ]] || \
    die "unknown agent '$agent'; expected codex or claude"
  require_command timeout
  require_command tee

  if [[ -z "$output" ]]; then
    local stamp
    stamp="$(date -u +%Y%m%dT%H%M%SZ)"
    output="$REPO_ROOT/benchmark-results/${stamp}-${problem}-${agent}"
  fi
  output="$(realpath -m "$output")"
  [[ ! -e "$output" ]] || die "output already exists: $output"
  mkdir -p "$output"

  local trusted="$output/trusted"
  local agent_dir="$output/agent"
  local judge_dir="$trusted"
  create_project "$problem" "$trusted" 0
  create_agent_project "$trusted" "$agent_dir"
  init_agent_git "$agent_dir"

  local agent_status=0
  run_agent "$agent_dir" "$trusted/.lake/packages" "$agent" "$model" "$timeout_seconds" \
    "$max_turns" "$output/agent-output.jsonl" "$output/agent-stderr.log" \
    || agent_status=$?

  local comparator_status="skipped"
  if [[ "$skip_judge" == "0" ]]; then
    cp "$agent_dir/Solution.lean" "$judge_dir/Solution.lean"
    comparator_status=0
    run_comparator "$judge_dir" "$use_systemd" || comparator_status=$?
  fi

  {
    echo "problem=$problem"
    echo "agent=$agent"
    echo "model=${model:-default}"
    echo "agent_exit_code=$agent_status"
    echo "comparator_exit_code=$comparator_status"
    echo "solution=$agent_dir/Solution.lean"
  } > "$output/result.txt"

  echo
  echo "Run directory: $output"
  echo "Agent exit code: $agent_status"
  echo "Comparator exit code: $comparator_status"

  if [[ "$skip_judge" == "0" && "$comparator_status" != "0" ]]; then
    return "$comparator_status"
  fi
  return "$agent_status"
}

main() {
  local command="${1:-help}"
  [[ $# -eq 0 ]] || shift
  case "$command" in
    list) list_problems ;;
    prepare) prepare_command "$@" ;;
    agent) agent_command "$@" ;;
    judge) judge_command "$@" ;;
    run) run_command "$@" ;;
    help|-h|--help) usage ;;
    *) die "unknown command '$command'; run '$0 help'" ;;
  esac
}

main "$@"
