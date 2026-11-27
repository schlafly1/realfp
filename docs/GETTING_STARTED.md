# Getting started with realfp (from nothing installed)

This guide takes you from a computer with nothing installed to running realfp's
examples and proving your first theorem of your own. It assumes no knowledge of
Lean. You will type a few commands into a terminal; each one is given exactly.

If you only want to learn Lean itself, see [Learning Lean](#learning-lean) at
the end. This guide only covers what you need to get realfp running.

**Contents**

1. [What you will install, and why](#1-what-you-will-install-and-why)
2. [Choose your path](#2-choose-your-path)
3. [Windows 11 (through WSL)](#3-windows-11-through-wsl)
4. [Linux](#4-linux)
5. [macOS](#5-macos)
6. [Get realfp and run the examples](#6-get-realfp-and-run-the-examples)
7. [Open the examples in VS Code and see the goals](#7-open-the-examples-in-vs-code-and-see-the-goals)
8. [Your first theorem in your own project](#8-your-first-theorem-in-your-own-project)
9. [No install at all: GitHub Codespaces](#9-no-install-at-all-github-codespaces)
10. [Troubleshooting](#10-troubleshooting)
11. [Learning Lean](#learning-lean)

> realfp is public: <https://github.com/schlafly1/realfp>. Downloading it needs no
> GitHub account; only the optional Codespaces route (§9) needs one.

---

## 1. What you will install, and why

| Piece | What it is | Size |
|---|---|---|
| **Git** and **curl** | download tools | small |
| **elan** | Lean's installer; it fetches the right Lean version automatically | small |
| **Lean 4.36.0** | the theorem prover (elan installs it the first time it is needed) | ≈ 3 GB |
| **A C compiler** (`gcc` or `clang`) | realfp compiles a small, fast C library for its interval arithmetic | ≈ 0.2–1 GB |
| **Mathlib** (prebuilt) | Lean's mathematics library, downloaded ready-made by `lake exe cache get` | ≈ 5 GB |
| **VS Code** + **Lean 4 extension** | the editor where you see proofs and goals | ≈ 0.5 GB |

Plan for **about 12 GB of free disk space** for realfp and its examples, plus
about 7 GB more for each separate project of your own (each project gets its own
copy of Mathlib). **8 GB of RAM** is enough for the examples; 16 GB is
comfortable.

**Why a C compiler?** realfp's speed comes from small C routines that use the
processor's rounding modes. They are compiled on your machine the first time you
build. Lean ships its own copy of `clang`, but without the C library headers that
these routines need (`math.h`, `fenv.h`, …), so a normal system C compiler is
required: `gcc` on Linux and in WSL, Apple's `clang` on macOS. This is needed even
if you only use the default, kernel-checked mode: the tactics search for
certificates using the C routines, and only the final check runs in Lean's kernel.

**Which processor?** Nothing to choose. On x86-64 processors that have AVX-512
(for example AMD Zen 4/5, many Intel Xeons) realfp uses it; on everything else
(most Intel laptops, Apple Silicon, ARM) it automatically uses a portable version.
Both give bit-identical results, and the theorems are the same either way.

## 2. Choose your path

| You have | Recommended path | Tested? |
|---|---|---|
| Windows 11 (or 10) | **WSL** (Linux inside Windows), §3, then §6–8 | yes |
| Linux (Ubuntu, Debian, Fedora, …) | §4, then §6–8 | yes (Ubuntu 24.04) |
| macOS (Apple Silicon or Intel) | §5, then §6–8 | **not tested** |
| Only a web browser | GitHub Codespaces, §9 | container tested; Codespaces itself not tested |

**Why not native Windows?** It does not work reliably yet. On our Windows 11 test
machine, realfp's C code compiled natively (with
[llvm-mingw](https://github.com/mstorsjo/llvm-mingw)), but Windows' **Smart App
Control** blocked Lean from loading the freshly compiled library (`error loading
library … .dll: 4551`). Smart App Control cannot be switched back on once it is
turned off, so we do not ask you to turn it off. WSL avoids the problem entirely,
and is also much faster for Lean (no antivirus scanning of thousands of files).
If you try native Windows anyway, see [Native Windows](#native-windows-experimental).

---

## 3. Windows 11 (through WSL)

WSL ("Windows Subsystem for Linux") runs a real Ubuntu Linux inside Windows. You
install it once; afterwards you follow the Linux instructions.

**3.1 Install WSL and Ubuntu.** Open **PowerShell as administrator** (Start menu →
type `PowerShell` → right-click → *Run as administrator*) and run:

```powershell
wsl --install -d Ubuntu
```

Restart Windows when asked. After the restart an Ubuntu window opens and asks you
to choose a Linux user name and password (they are separate from your Windows
login; remember the password, `sudo` will ask for it). If you already have WSL,
`wsl -l -v` lists your distributions; any recent Ubuntu works.

**3.2 Open Ubuntu.** From now on, "the terminal" means the **Ubuntu** app (Start
menu → *Ubuntu*). Work in your Linux home folder (`~`), not under `/mnt/c/...`:
Lean is many times slower on the Windows side of the file system.

**3.3 Continue with [§4 Linux](#4-linux)** inside the Ubuntu terminal.

**3.4 VS Code for WSL.** Install VS Code on **Windows** from
<https://code.visualstudio.com/>. Then, in VS Code, install the extension **WSL**
(by Microsoft). Later, in §6–7, you start VS Code *from the Ubuntu terminal* with
`code .`; VS Code then runs inside Linux, and you install the **Lean 4**
extension there (VS Code offers "Install in WSL: Ubuntu").

*Tested:* Windows 11 with WSL 2 + Ubuntu 24.04 on a 16-core AMD Ryzen 9 9950X
(32 threads, 30 GB available to WSL): downloading Lean and Mathlib took about
4 minutes, building realfp and an example about 75 seconds.

## 4. Linux

These commands are for Ubuntu/Debian (and Ubuntu in WSL). Fedora users: replace
the `apt` line with `sudo dnf install -y git curl gcc`.

**4.1 Install Git, curl and a C compiler:**

```bash
sudo apt update
sudo apt install -y git curl build-essential
```

(`build-essential` is the C compiler `gcc` plus `make` and the C library headers.)

**4.2 Install elan (Lean's installer):**

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
source ~/.profile
```

`--default-toolchain none` means "don't install any Lean yet": the right version
(4.36.0) is installed automatically the first time you use it inside realfp.
Check with `elan --version`. If `elan` is "not found", close the terminal and
open a new one.

**4.3 VS Code** (optional on a server, recommended on a desktop): install from
<https://code.visualstudio.com/>, then add the **Lean 4** extension
(Extensions panel → search "Lean 4" → the one by *leanprover*). The extension can
also install elan for you; either way is fine.

Continue with [§6](#6-get-realfp-and-run-the-examples).

*Tested:* a fresh, minimal Ubuntu 24.04 with nothing installed, 8 CPU cores,
15 GB RAM: `apt install` of Git and curl 15 s, `build-essential` 25 s, elan 1 s.

## 5. macOS

> **Not tested.** We have not run these steps on a Mac. They follow the standard
> Lean instructions, and realfp's C code was adjusted to compile with `clang`
> (checked on Linux), but please report any problem.

**5.1 Install Apple's command line tools** (Git and the `clang` C compiler).
Open *Terminal* (Applications → Utilities) and run:

```bash
xcode-select --install
```

and click *Install* in the window that appears.

**5.2 Install elan:**

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
source ~/.profile 2>/dev/null; source ~/.zprofile 2>/dev/null; export PATH="$HOME/.elan/bin:$PATH"
```

**5.3 VS Code:** install from <https://code.visualstudio.com/> and add the
**Lean 4** extension.

On Apple Silicon (M1–M4) realfp automatically uses its portable C routines; on
Intel Macs it checks whether the processor has AVX-512 (most do not) and chooses
accordingly.

Continue with [§6](#6-get-realfp-and-run-the-examples).

---

## 6. Get realfp and run the examples

All commands in this section are typed in the terminal (Ubuntu on Windows).

**6.1 Download realfp:**

```bash
cd ~
git clone https://github.com/schlafly1/realfp
```

No sign-in is needed. If Git asks for a user name or password, check the address
for typos.

**6.2 Download Lean and the prebuilt Mathlib.** The examples live in the
`RealFPMathlib` folder; always work from there:

```bash
cd ~/realfp/RealFPMathlib
lake exe cache get
```

The first time, this installs Lean 4.36.0 (about 1 minute) and then downloads and
unpacks about 9,000 prebuilt Mathlib files. It should end with a
line like `Decompressed 9117 file(s)` (or "Already decompressed …"). It must **not** start
compiling Mathlib itself; if you see thousands of lines like
`Built Mathlib.…`, press Ctrl-C and see [Troubleshooting](#10-troubleshooting).

**6.3 Build realfp and one example:**

```bash
lake build RealFPMathlib.Examples.Constants
```

This compiles realfp's C routines and its Lean files (a few hundred), then the
example. Expect **1–3 minutes** on a recent machine (longer on a laptop). Yellow
`warning:` lines are normal; the last line should be
`Build completed successfully`.

**6.4 Run an example and see its output:**

```bash
lake lean RealFPMathlib/Examples/Constants.lean
```

No output (or only warnings) means every theorem in the file was proved. To see
something, look at the file: it proves π, e, √2 and the golden ratio to 30
decimals. The polished examples are listed in [EXAMPLES.md](EXAMPLES.md).

**6.5 (Optional) Build all examples and the axiom audit:**

```bash
lake build
```

On our 8-core test machine this took about 3 more minutes after step 6.3. The
last lines report the axiom audit: every library theorem uses only Lean's three
standard axioms.

*Tested times* (fresh Ubuntu 24.04, 8 cores, 15 GB): clone 1 s, `lake exe cache
get` 68 s (including the Lean download), step 6.3 87 s, step 6.4 5 s, step 6.5
173 s. Disk used: 3.1 GB for Lean (`~/.elan`), 7.4 GB for `~/realfp`.

## 7. Open the examples in VS Code and see the goals

**7.1 Open the right folder.** Open the folder `realfp/RealFPMathlib` — not the
top-level `realfp` folder. (The top level is realfp's Mathlib-free core; in it,
`import RealFPMathlib` cannot find Mathlib.)

- Linux/macOS: `cd ~/realfp/RealFPMathlib && code .` or *File → Open Folder…*
- Windows (WSL): in the Ubuntu terminal, `cd ~/realfp/RealFPMathlib && code .`
  (the first time, VS Code installs its WSL helper; then install the Lean 4
  extension "in WSL: Ubuntu" when offered).

**7.2 Open an example**, e.g. `RealFPMathlib/Examples/Constants.lean`. The Lean
extension starts Lean on the file. An orange bar at the left edge means "still
checking"; it disappears when the file is done (a few seconds, because step 6.3
already built everything).

**7.3 See the goals.** The **Lean Infoview** panel opens on the right (if not:
press Ctrl+Shift+Enter, or on a Mac Cmd+Shift+Enter, or click the ∀ menu → *Toggle
Infoview*). Put the cursor just *before* `realfp` in a proof: the Infoview shows
the goal, the statement still to be proved. Put it just *after* `realfp`: "No
goals" means the tactic proved it. Errors are underlined in red and explained in
the Infoview and in the *Problems* panel.

**7.4 Try a change.** Edit a number in a statement so that it becomes false, for
example change `3.14159265358979323846264338327951` to
`3.14159265358979323846264338327949` (now false). After a moment `realfp` fails
with a red error showing the enclosure it computed for π,
`[3.141592653589793238462643383279503, …]`, and the bound it could not prove.
Undo with Ctrl+Z.

If a file says something like "imports are out of date, restart file", click
*Restart File* (or run `lake build` in the terminal first).

## 8. Your first theorem in your own project

Do your own work in a separate project that *depends on* realfp, rather than
inside the realfp folder.

**8.1 Make a project folder** next to `realfp`, and give it the same Lean version:

```bash
mkdir -p ~/myfirst && cd ~/myfirst
cp ~/realfp/RealFPMathlib/lean-toolchain .
```

(`lean-toolchain` contains one line, `leanprover/lean4:v4.36.0`. Your project
**must** use the same Lean version as realfp and Mathlib.)

**8.2 Create the project description `lakefile.toml`** with this content (use VS
Code, or any text editor):

```toml
name = "myfirst"
defaultTargets = ["MyFirst"]

[[require]]
name = "realfp_mathlib"
path = "../realfp/RealFPMathlib"

[[lean_lib]]
name = "MyFirst"
```

This uses your local copy of realfp from §6. Mathlib (`v4.36.0`) comes with it;
do not add Mathlib separately (a different Mathlib version would not match).
Alternatively, without a local copy, let Lake download realfp from GitHub:

```toml
[[require]]
name = "realfp_mathlib"
git = "https://github.com/schlafly1/realfp"
rev = "v0.1.1"
subDir = "RealFPMathlib"
```

`rev = "v0.1.1"` pins the release v0.1.1; use a newer release tag to upgrade, or
`"main"` for the latest development version.

**8.3 Write your first theorem** in a new file `MyFirst.lean` in the same folder:

```lean
import RealFPMathlib

-- My first realfp theorem: e^x stays below 1 + x + x^2 on [0, 1].
theorem my_first : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 1 + x + x ^ 2 := by
  realfp

#print axioms my_first
```

**8.4 Download Mathlib for the project and build it:**

```bash
cd ~/myfirst
lake exe cache get
lake build
```

The output should include

```
info: MyFirst.lean:7:0: 'my_first' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully
```

meaning the theorem is proved and checked by Lean's kernel, with only the
standard axioms. Now open the folder in VS Code (`code .`) and experiment: change
the interval, the function or the bound. The [tutorial](TUTORIAL.md) explains what
`realfp` can prove, its options, and the other tactics; the
[examples](EXAMPLES.md) are good models to copy.

*Tested:* §8 with the path form on the fresh Ubuntu machine: `lake exe cache get`
56 s, `lake build` 9 s (realfp was already built in §6). The Git form (which also
builds realfp inside the project) took 175 s for both commands together, with
Mathlib's download already in the local cache.

---

## 9. No install at all: GitHub Codespaces

[GitHub Codespaces](https://github.com/features/codespaces) runs VS Code in your
browser on a cloud machine. realfp includes a configuration
(`.devcontainer/`) that installs everything above automatically.

1. Sign in to GitHub, open <https://github.com/schlafly1/realfp>, click the green
   **Code** button → **Codespaces** → **Create codespace on main**.
2. Wait while it sets up (it runs `lake exe cache get` and builds realfp and one
   example; expect 5–15 minutes the first time). You can watch the progress in
   the terminal panel.
3. In the file explorer open `RealFPMathlib/RealFPMathlib/Examples/Constants.lean`.
   To get the Infoview working with Mathlib, open the `RealFPMathlib` folder as
   the workspace: *File → Open Folder…* → `/workspaces/realfp/RealFPMathlib`.

Costs: personal GitHub accounts get a free monthly allowance (currently 120
core-hours and 15 GB-months of storage). realfp's configuration asks for a
4-core machine (so about 30 free hours a month) and uses about 12 GB of disk, so
**stop the codespace when you finish and delete it when you no longer need it**
(github.com/codespaces). Any GitHub account can create a codespace from the
public repository.

*Tested:* the container was built with Docker (18 s) and its setup command run on a
fresh copy of the repository on an 8-core machine: 2.6 minutes for the Mathlib
download plus building realfp and one example. Creating an actual codespace on
GitHub was **not tested**.

**Other online options.**
- [live.lean-lang.org](https://live.lean-lang.org) runs Lean and Mathlib in the
  browser with nothing to install, which is ideal for learning Lean, but it
  cannot load extra libraries such as realfp.
- Gitpod Classic was shut down in 2025; its successor (Ona) can use the same
  `.devcontainer/` configuration, but we have not tried it.

---

## 10. Troubleshooting

**`lake: command not found` / `elan: command not found`.** Close and reopen the
terminal, or run `source ~/.profile` (macOS: `source ~/.zprofile`), or
`export PATH="$HOME/.elan/bin:$PATH"`.

**"realfp needs a C compiler …" or `could not execute external process 'cc'`.**
No C compiler is installed. Ubuntu/Debian/WSL: `sudo apt install -y
build-essential`; Fedora: `sudo dnf install -y gcc`; macOS: `xcode-select
--install`. Then run the build again. To use a particular compiler, set
`CC`, e.g. `export CC=clang`.

**The cache does not download, or Lake starts building Mathlib from source**
(thousands of `Built Mathlib.…` lines, taking hours). Press Ctrl-C, then:
- Make sure you are in the right folder (`~/realfp/RealFPMathlib`, or your own
  project) and that its `lean-toolchain` says `leanprover/lean4:v4.36.0`.
- Run `lake exe cache get` again; it resumes. `lake exe cache get!` (with `!`)
  forces a fresh download of everything.
- On a network with a proxy or firewall, the download servers may be blocked;
  try another network.

**Toolchain or version mismatch** (errors such as "failed to read file … .olean,
invalid header", "unknown package", or Mathlib names that do not exist). Your
project's `lean-toolchain` must be exactly the one in
`realfp/RealFPMathlib/lean-toolchain`, and you must not require a different
Mathlib version yourself. Fix `lean-toolchain`, then run `lake update` and
`lake exe cache get` in the project folder. Do not create the project with
`lake new … math`: that picks the newest Mathlib, which realfp does not use yet.

**Out of memory** (the build is killed, "Killed", or the machine freezes). Lean
uses up to a few GB per file and builds several files at once. Close other
programs and limit the parallelism: `LEAN_NUM_THREADS=2 lake build`. On WSL,
Windows gives Linux only half of your RAM by default; to give it more, create
`C:\Users\<you>\.wslconfig` containing

```
[wsl2]
memory=12GB
```

then run `wsl --shutdown` in PowerShell and reopen Ubuntu.

**Slow on Windows; antivirus.** Keep your projects inside WSL's Linux folders
(`~/…`), not under `/mnt/c/…`: Windows Defender then does not scan every one of
Mathlib's files, and file access is many times faster. If you must work on the
Windows side, add your project folder and `%USERPROFILE%\.elan` as Defender
exclusions (Windows Security → Virus & threat protection → Manage settings →
Exclusions).

**Long paths on Windows** ("Filename too long" from Git, or files that cannot be
created). Mathlib has deep folder names. In WSL this does not happen. On the
Windows side, enable long paths: in PowerShell as administrator,
`New-ItemProperty -Path HKLM:\SYSTEM\CurrentControlSet\Control\FileSystem -Name LongPathsEnabled -Value 1 -PropertyType DWORD -Force`,
then `git config --global core.longpaths true`, and use a short base folder such
as `C:\lean`.

**`Could not find native implementation of external declaration`** (from
`#eval`) or a message from `realfp` about missing compiled code. You ran plain
`lean`. Use the editor, `lake build`, or `lake lean File.lean`, which load
realfp's compiled C routines.

**"Illegal instruction" crash.** The compiled code uses AVX-512 but the processor
does not have it (for example, a build copied from another machine). Force the
portable version and rebuild: `export IV64_BACKEND=rnerr`, delete the folder
`.lake/build/c` of realfp (in `~/realfp`, or in
`.lake/packages/realfp_mathlib` of your project), and run `lake build` again.

**VS Code shows "imports are out of date" or never finishes.** Run `lake build`
in the terminal first, then *Restart File* (∀ menu → *Server* → *Restart File*).
Make sure you opened the `RealFPMathlib` folder (or your project folder), not the
top-level `realfp` folder.

### Native Windows (experimental)

Not recommended (see §2). What we found on Windows 11: elan and Lean install
natively (with Git for Windows), and `lake exe cache get` works. realfp's C code
needs a MinGW C compiler; with [llvm-mingw](https://github.com/mstorsjo/llvm-mingw)
on the `PATH` (it provides `cc`) the C code compiles. Loading the compiled
library then failed with `error loading library … .dll: 4551` because **Smart
App Control** blocked it (Windows Security → App & browser control → Smart App
Control). On a machine where Smart App Control is off (it is off on many
machines, e.g. after an upgrade from Windows 10), native Windows may work; this is
untested. Use WSL instead if you can.

### Optional: GPU many-box proofs

You do not need a GPU for realfp. If you have an NVIDIA GPU with CUDA, the opt-in
`interval_grid` tactic and its `realfp-grid` search tool can prove some bounds that need
billions of boxes. Without a GPU, they run on all your CPU cores. See [GPU.md](GPU.md).

---

## Learning Lean

realfp's tactics do the numerical work, but you will want to read and write Lean
statements. Good free resources:

- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
  — the standard introduction for mathematicians, with exercises.
- [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4)
  — a gentle, in-browser first contact with proofs in Lean.
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)
  — the logic and the language in depth.
- [Lean documentation](https://lean-lang.org/documentation/) and the
  [Lean community website](https://leanprover-community.github.io/), including
  how to find things in Mathlib (Loogle, Mathlib docs).
- The [Lean Zulip chat](https://leanprover.zulipchat.com/), where beginners'
  questions are welcome (stream "new members").

Then continue with realfp's [tutorial](TUTORIAL.md) and [examples](EXAMPLES.md).
