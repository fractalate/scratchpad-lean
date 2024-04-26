# Lean Prover Scratchpad

On Debian 12, I had success installing Lean via `elan`:

```
sudo apt-get install elan curl git
elan default leanprover/lean4:stable
```

This will install `elan` and Lean 4. Check your version with the command `lean --version`.

To bootstrap a new project, you can use the following commands:

```bash
mkdir my_project
cd my_project
lake init my_project math
lake build
```

To test something basic with Lean, create a simple test proof in the file named `MyProject.lean`:

```lean
theorem one_equals_one : 1 = 1 := by
  rfl
```

Build the project to test the proof.

```bash
lake build
```

The output will be blank if the proof is valid. To test an invalid proof, try the following invalid revision of the previous proof:

```lean
theorem one_equals_one : 1 = 2 := by
  rfl
```

You will see errors when attempting to build since the proof is not valid.

### Notes

* `lake init my_project math` is opinionated about project structure and version management.
  - It will create a project structure for you with several source files.
  - It will create a git repository in the initialized project. This might be confusing if you are already in a repository. Simply delete the `.git` directory it creates if you require additional flexibility.
  - With `math` included at the end of the command, you will get `mathlib` by default. This also sets the nature of your project to be a library, instead of an application that you run.
