# dLean

dLean is a shallow embedding of [differential dynamic logic (dL)](https://doi.org/10.1007/978-3-319-63588-0) in Lean 4 for verifying cyber-physical systems. It represents hybrid programs—nondeterministic programs combining discrete and continuous dynamics—as ordinary monadic Lean programs that can be verified using Lean's `mvcgen` framework. This approach scales from scalar systems to vector-valued dynamics and QdL-style multi-agent models while reusing Lean and Mathlib's existing infrastructure. Because LLMs are effective at constructing Lean proofs, dLean proofs are also well suited to LLM-based automation at scale.

## Hybrid programs

A hybrid program combines discrete control with continuous physical evolution. Consider a bouncing ball with height x and vertical velocity v. Let g > 0 denote gravitational constant, c is the coefficient of restitution applied at each bounce, and r ≥ 0 models aerodynamic drag. When the ball reaches the ground (x = 0), the controller reverses and scales its velocity by assigning v := -c * v. Between bounces, the ball follows one of two ODEs: `up` describes upward motion (v ≥ 0), while `down` describes downward motion (v ≤ 0).

First, we define the upward ODE `{ x' = v, v' = -g - r*v^2 }` 
with its domain constraint `(x >= 0 & v >= 0)`, and likewise the downward ODE
`{ x' = v, v' = -g + r*v^2 }` with the domain `(x >= 0 & v <= 0)`.

```lean
def up (g r : ℝ) : ℝ × ℝ → ℝ × ℝ
  | (_x, v) => (v, -g - r * v ^ 2)

def updom : ℝ × ℝ → Prop
  | (x, v) => 0 ≤ x ∧ 0 ≤ v

def down (g r : ℝ) : ℝ × ℝ → ℝ × ℝ
  | (_x, v) => (v, -g + r * v ^ 2)

def downdom : ℝ × ℝ → Prop
  | (x, v) => 0 ≤ x ∧ v ≤ 0
```

The return type of the hybrid program that we will define will be `SetM ℝ`. It is an ordinary set of real numbers represented by its membership predicate. The `SetM` monad's bind operation provides sequential composition: every possible result of one program is passed to the next program, and all possible outputs are collected into a single set. The bouncing-ball hybrid program can therefore be written using Lean's `do` notation as follows:

```lean
def prog (g c r x v : ℝ) : SetM ℝ := do
  let mut (x, v) := (x, v)
  let n ← choose ℕ
  for _ in [:n] do
    if x = 0 then
      v := -c * v
    (x, v) ← (evolve (up g r) updom ∪
                evolve (down g r) downdom) (x, v)
  return x
```

The program nondeterministically chooses a `n : Nat` and executes the loop exactly `n` times. `evolve (up g r) updom ∪ evolve (down g r) downdom` is a nondeterministic choice between upward and downward motion. In either branch, `evolve` follows any valid trajectory of the selected ODE from the current `(x, v)` for an arbitrary nonnegative duration, requires its domain condition to hold throughout, and returns the reached position and velocity pair.

The corresponding Lean safety statement says that every result position `x_res` of the ball is between the ground and the initial height bound is as follows:

```lean
theorem aerodynamic_quantum_safe :
    ∀ g H c r x v,
      (x ≤ H ∧ v = 0 ∧ 0 ≤ x) ∧ (0 < g ∧ c ≤ 1 ∧ 0 ≤ c ∧ 0 ≤ r) →
        ∀ x_res ∈ SetM.run (prog g c r x v), 0 ≤ x_res ∧ x_res ≤ H := sorry
```

The safety theorem corresponds to the following dL formula:

```text
  (x<=H & v=0 & x>=0) &
  (g>0 & 1>=c&c>=0 & r>=0)
 ->
  [
    {
      {?x=0; v:=-c*v;  ++  ?x!=0;}
      {{x'=v,v'=-g-r*v^2&x>=0&v>=0} ++ {x'=v,v'=-g+r*v^2&x>=0&v<=0}}
    }*
  ] (0<=x&x<=H)
```

Quantifying over every member of the resulting set corresponds to the box modality: the postcondition must hold after every possible execution.

To prove the safety theorem, a loop invariant is supplied to `mvcgen`, which decomposes the monadic program and generates the required verification conditions. Continuous evolution is handled by applying theorems that represent the dL proof rules: `dI` proves differential invariants, `dC` introduces differential cuts, and `dW` derives consequences of the evolution domain.

The automatic differentiation tactics discharge the analytic side of these rules and the remaining arithmetic is proved using Lean and Mathlib.

State spaces beyond real-valued variables require almost no additional machinery: vectors are supported directly by Mathlib, while QdL-style collections of objects are represented as ordinary Lean functions from object identifiers to their values.

## Install and build

```sh
git clone REPOSITORY_URL
cd dLean
lake update
lake exe cache get
lake build
```

## Proof automation

The benchmark harness in `agentic/prove.sh` prepares a workspace, runs Codex or Claude Code (the Claude integration has not been tested), and checks the generated `Solution.lean` independently with Lean Comparator. Reference `Proof.lean` files are not copied into the workspace.

Judging requires Lean Comparator and lean4export compatible with dLean's Lean toolchain, and Landrun on a Linux system that supports its sandbox. Clone comparator and build with:

```sh
lake build lean4export comparator
```

Back in the dLean repository, configure the executable locations:

```sh
export COMPARATOR_ROOT=/absolute/path/to/comparator
export COMPARATOR_LANDRUN=/absolute/path/to/landrun
```

`PROBLEM` is a relative or absolute directory path containing `Challenge.lean` and `config.json`, for example:

```text
dLean/Examples/BouncingBall/
  Challenge.lean
  config.json
```

Run the complete workflow from the repository root:

```sh
agentic/prove.sh run dLean/Examples/BouncingBall codex --model gpt-6-astra
```

The stages can also be run separately:

```sh
agentic/prove.sh prepare dLean/Examples/BouncingBall ./BouncingBall-sandbox
agentic/prove.sh agent codex ./BouncingBall-sandbox
agentic/prove.sh judge dLean/Examples/BouncingBall ./BouncingBall-sandbox/Solution.lean
```

Run `agentic/prove.sh help` for more information.
