# 🚀 Turing Machine Quick Start Guide

Get up and running with the world's first fractal Turing machine in **5 minutes**.

## ⚡ Super Quick Start

```bash
# 1. Clone the repo
git clone https://github.com/FractalDevTeam/Principia-Fractalis.git
cd Principia-Fractalis

# 2. Build (first time: ~15 min, subsequent: ~30 sec)
lake build PF.TuringEncoding

# 3. You're done! ✅
```

## 🎮 Try It Out

### Option 1: Interactive REPL

```bash
lake env lean
```

Then in the Lean REPL:

```lean
import PF.TuringEncoding
open PrincipiaTractalis

-- Check out the increment machine
#check tmUnaryIncrement

-- See its structure
#print tmUnaryIncrement

-- Try the all-ones checker
#check tmAllOnes
```

### Option 2: VSCode Extension

1. Install [Lean 4 VSCode extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)
2. Open `PF/TuringEncoding.lean`
3. Navigate to example machines (lines 1737-1797)
4. Hover over definitions to see their types!

### Option 3: Command Line Verification

```bash
# Verify a specific theorem
lake env lean --run PF/TuringEncoding.lean -c "example : alpha_P ≠ alpha_NP := alpha_separation"

# Check build status
lake build --verbose

# Run full verification
lake build
```

## 📝 Your First Turing Machine

Create a new file `MyMachine.lean`:

```lean
import PF.TuringEncoding

namespace MyFirstTM
open PrincipiaTractalis

/-- A simple machine that accepts strings of all 0s -/
def tmAllZeros : TuringMachine where
  num_states := 3
  initial_state := 0
  accept_state := 1
  reject_state := 2
  transition := fun state sym =>
    match state, sym with
    | 0, 0 => some (0, 0, Move.right)  -- Keep scanning 0s
    | 0, 2 => some (1, 2, Move.stay)   -- Hit blank: accept!
    | 0, 1 => some (2, 1, Move.stay)   -- Found a 1: reject!
    | _, _ => none                      -- Halt
  h_initial := by norm_num
  h_accept := by norm_num
  h_reject := by norm_num

-- Test it!
example : tmAllZeros.accepts [0,0,0] 10 := by
  sorry  -- Computational proof (needs eval tactics)

end MyFirstTM
```

Build it:

```bash
lake build MyMachine
```

## 🔍 Understanding the Code

### Key Components

1. **TMConfig** - Current machine state
   ```lean
   { state := 0, tape := [1,1,1], head := 0 }
   ```

2. **TuringMachine** - Machine specification
   ```lean
   { num_states := 2
     initial_state := 0
     accept_state := 1
     transition := ... }
   ```

3. **Move** - Head direction
   ```lean
   Move.left | Move.right | Move.stay
   ```

### Running a Machine

```lean
-- Create initial config
let config := tm.initialConfig [1,1,1]

-- Run for 10 steps
let (final_config, steps_taken) := config.runSteps tm 10

-- Check if accepted
let accepted := final_config.isAccepting tm
```

## 🎯 Common Tasks

### Task 1: Check if a machine accepts an input

```lean
def test_input := [1, 0, 1]
def max_steps := 100

#check tmAllOnes.accepts test_input max_steps
-- Returns: Prop (proposition to be proven)
```

### Task 2: Encode a configuration

```lean
def my_config : TMConfig := {
  state := 2
  tape := [1, 0, 1, 2]
  head := 1
}

#check encodeConfig my_config
-- Returns: ℕ (natural number encoding)
```

### Task 3: Prove encoding is injective

```lean
example (c1 c2 : TMConfig) : 
  encodeConfig c1 = encodeConfig c2 → c1 = c2 :=
encodeConfig_injective c1 c2
```

## 🐛 Troubleshooting

### Build fails with "unknown package"

```bash
# Update dependencies
lake update

# Clean and rebuild
lake clean
lake build
```

### "Module not found" error

Make sure you're in the project root:

```bash
cd Principia_Fractalis_FINAL_SUBMISSION_2025-11-18
lake build
```

### Slow build times

First build takes ~15 minutes (compiling Mathlib). Subsequent builds are fast (~30 sec).

```bash
# Use cache if available
lake exe cache get
```

### VSCode doesn't recognize Lean files

1. Check Lean 4 extension is installed
2. Open command palette (Ctrl+Shift+P)
3. Run: "Lean 4: Restart Server"

## 📚 Next Steps

1. **Read the documentation**: [Full API Docs](docs/API.md)
2. **Try examples**: Check out `PF/TuringEncoding.lean` lines 1737-1797
3. **Build your own**: Follow the patterns in example machines
4. **Explore theorems**: See what's proven in lines 217-244
5. **Understand the math**: Read [TURING_MACHINE_README.md](TURING_MACHINE_README.md)

## 💡 Pro Tips

1. **Use `#check`** to see types of definitions
2. **Use `#print`** to see full definitions
3. **Hover in VSCode** to see documentation
4. **Use `sorry`** as placeholder while developing
5. **Run `lake build`** frequently to catch errors early

## 🎓 Learning Resources

- [Lean 4 Manual](https://leanprover.github.io/lean4/doc/)
- [Mathlib Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
- [Principia Fractalis Book](docs/book/) (814 pages)

## 🤝 Get Help

- **Issues**: [GitHub Issues](https://github.com/FractalDevTeam/Principia-Fractalis/issues)
- **Discussions**: [GitHub Discussions](https://github.com/FractalDevTeam/Principia-Fractalis/discussions)
- **Chat**: [Lean Zulip](https://leanprover.zulipchat.com/)

---

**Need help?** Open an issue or start a discussion!

**Found a bug?** We'd love to hear about it!

**Built something cool?** Share it with the community!

---

<p align="center">
  <strong>Happy Computing! 🎉</strong>
</p>
