# Instructions for Claude Code: set up and check this formalisation

**You are reading this because someone handed you a directory containing an
Isabelle/HOL formalisation and asked you to get it running.** Work through the
modules below in order. Each one starts with a check, so it is safe to run them
all even if some of the work is already done.

Your goal, stated once: **make `isabelle build -d . -e Lemmon_Fitch` succeed in
this directory.** That single command processes the entire development from
Isabelle's plain `HOL` image and regenerates the Haskell and SML exports. When
it exits 0, everything in the accompanying note (`SUMMARY.pdf`) has been
machine-checked on this machine.

Two facts that save time:

* **This project needs no Archive of Formal Proofs.** It uses only `HOL` and
  `HOL-Library`, both of which ship with Isabelle. Do not install the AFP.
* **The exact version matters: Isabelle2025-2.** Other versions may fail to
  process these sources. Do not substitute a newer or older release without
  saying so plainly to the user.

---

## Module 0 — Assess what is already there

Run these and keep the answers; later modules branch on them.

```bash
uname -s                      # Linux / Darwin / (MINGW* means Windows)
which isabelle || echo "no isabelle on PATH"
isabelle version 2>/dev/null || echo "cannot run isabelle"
df -h .                       # need ~6 GB free for Isabelle + heaps
nproc 2>/dev/null || sysctl -n hw.ncpu   # build is parallel; 4+ cores helps
```

Also look for an installation that is present but not on `PATH`:

```bash
ls -d ~/Isabelle* /opt/Isabelle* /usr/local/Isabelle* \
      ~/Desktop/Isabelle* "/Applications/Isabelle2025-2.app" 2>/dev/null
```

Decide which case you are in:

| Case | What you found | Go to |
|---|---|---|
| A | `isabelle version` prints `Isabelle2025-2` | Module 2 |
| B | An `Isabelle2025-2` directory exists but is not on `PATH` | Module 1.4 |
| C | Isabelle is installed but a **different** version | Module 1, and read 1.5 first |
| D | No Isabelle at all | Module 1 |

---

## Module 1 — Install Isabelle 2025-2

### 1.1 Get the download URL (do this first, do not guess)

The canonical layout is
`https://isabelle.in.tum.de/dist/Isabelle2025-2_linux.tar.gz` for Linux,
`…_macos.tar.gz` for macOS, and `Isabelle2025-2.exe` for Windows. **Check that
the URL actually resolves before downloading**, and if it does not, get the
correct link from the release page rather than inventing one:

```bash
curl -fsIL -o /dev/null -w '%{http_code}\n' \
     https://isabelle.in.tum.de/dist/Isabelle2025-2_linux.tar.gz
```

`200` means good. The request is redirected to a mirror on the way, which is
normal and which `curl -fL` follows for you. If you get anything else, open
`https://isabelle.in.tum.de/` and find the Isabelle2025-2 download for this
platform. Tell the user what you found; if only a different
version is available, stop and ask rather than installing it.

### 1.2 Linux

```bash
cd ~                                  # or wherever the user prefers
curl -fL -o isabelle.tar.gz https://isabelle.in.tum.de/dist/Isabelle2025-2_linux.tar.gz
tar -xzf isabelle.tar.gz              # creates ~/Isabelle2025-2
rm isabelle.tar.gz
~/Isabelle2025-2/bin/isabelle version
```

If the extracted directory has a different name, use the name that actually
appeared — do not assume.

### 1.3 macOS

The macOS download may be a `.dmg` (drag `Isabelle2025-2.app` to
`/Applications`) or a `.tar.gz` (extract as in 1.2). Either way the executable
ends up at one of:

```
/Applications/Isabelle2025-2.app/Isabelle/bin/isabelle
~/Isabelle2025-2/bin/isabelle
```

On Apple silicon the first launch may be slow while macOS verifies the
binaries. If Gatekeeper blocks it, the user must approve it in System Settings
→ Privacy & Security; you cannot do this for them, so ask.

### 1.4 Put `isabelle` on PATH

Substitute the real installation directory:

```bash
echo 'export PATH="$HOME/Isabelle2025-2/bin:$PATH"' >> ~/.bashrc   # or ~/.zshrc
export PATH="$HOME/Isabelle2025-2/bin:$PATH"
isabelle version                      # must print Isabelle2025-2
```

If you would rather not edit shell config, you can skip this and use the full
path to the executable in every later command. Say which you did.

### 1.5 If a different Isabelle is already installed

Isabelle versions coexist happily — they keep separate state under
`~/.isabelle/Isabelle2025-2/`. **Install 2025-2 alongside the existing one**
rather than removing anything, and be explicit about which `isabelle` binary
each later command uses. Getting this wrong is the single most common cause of
confusing failures here: a command that runs the wrong binary will report
errors that look like problems with the proofs.

### 1.6 Windows

Prefer WSL: install Ubuntu from the Microsoft Store, then follow the Linux
instructions inside it and keep this project directory inside the WSL
filesystem (not under `/mnt/c/`, which is slow). The native Windows installer
also works; if the user chooses it, run the commands below from the Cygwin
terminal that Isabelle provides.

---

## Module 2 — Check the whole development

From **this directory** (the one containing `Lemmon_Fitch.thy` and `ROOT`):

```bash
isabelle build -d . -e Lemmon_Fitch
```

Expect **five to ten minutes** on a modern four-core machine and exit code 0.
It is normal for it to look idle for a minute at a time; some single proofs are
slow. The last lines should read:

```
Finished Lemmon_Fitch (0:06:10 elapsed time, ...)
Exporting Lemmon_Fitch ...
```

Two things to check afterwards, and report both:

```bash
git status --porcelain generated 2>/dev/null   # if this is a git checkout
```

The `-e` flag rewrites `generated/haskell/LemmonFitch.hs`,
`generated/haskell/Str_Literal.hs` and `generated/sml.ML`. They should come out
**byte-for-byte identical** to what shipped. If they differ, say so — it means
this Isabelle is producing different code than the one the results were
recorded with, and that is worth knowing before trusting anything else.

**If the first build is much slower than ten minutes**, Isabelle is probably
building the `HOL` image from scratch because the distribution did not ship it
prebuilt. That is a one-off cost of roughly twenty minutes; let it finish.

---

## Module 3 — Read the proofs interactively

```bash
isabelle jedit -d . -n -l HOL Lemmon_Fitch.thy
```

The `-l HOL` and `-n` are deliberate and should not be "simplified away":
together they make every project theory open as editable source rather than
loading a prebuilt project heap. Opening the cap this way pulls in all 49
theories; the Prover IDE will take several minutes to process them, showing
progress in the Theories panel.

To read one theory without waiting for the rest, open it directly, e.g.
`isabelle jedit -d . -n -l HOL LF_HLW_Construct.thy`.

Suggested reading order for someone who wants the results rather than the
machinery:

1. `SUMMARY.pdf` — the covering note.
2. `LF_HLW_Construct.thy` — the construction theorem, `hlPaperCorrect_toFitch`
   at the end.
3. `LF_HLW_Theorem10.thy` — the three impossibility results.
4. `PROJECT_GOALS.md` — what is proved, what is not, and why.

---

## Module 4 — Optional: the differential test against the handwritten checker

This compiles the Isabelle-generated Haskell kernel and the original
handwritten checker and compares their verdicts line by line. It needs GHC and
two libraries; on Debian or Ubuntu:

```bash
sudo apt-get install ghc libghc-aeson-dev libghc-split-dev
```

Then, from this directory:

```bash
ghc --make -O1 -igenerated/haskell \
    -ireference/lemmon-checker-main/src -idifferential \
    -outputdir differential/build -o differential/diff \
    differential/Differential.hs
./differential/diff
```

Recorded results, for comparison, are in `differential/RESULT.txt` and the
other `RESULT.*` files: 9,874 comparisons with 0 disagreements. See
`differential/README.md` for the other harnesses (rejection messages, the
supplied regression suite, the public API).

**If GHC is not available, skip this module.** It is a cross-check on the
generated code, not part of the formal result, and Module 2 is what verifies
the theorems.

---

## Module 5 — Optional: rebuild the papers

```bash
pdflatex lemmon-fitch.tex && pdflatex lemmon-fitch.tex && pdflatex lemmon-fitch.tex
pdflatex SUMMARY.tex && pdflatex SUMMARY.tex
```

Standard LaTeX only — AMS bundle, `geometry`, `array`, `listings`, `booktabs`.
Three passes for the manuscript because of cross-references.

---

## Troubleshooting

| Symptom | Likely cause and fix |
|---|---|
| `isabelle: command not found` | PATH not set; Module 1.4, or use the full path to the binary. |
| Errors in theories that look like syntax errors | Wrong Isabelle version. Check `isabelle version` prints `Isabelle2025-2`. |
| `Bad session root` / `Unknown session` | You are not in the directory containing `ROOT`. `cd` there. |
| Build dies with an out-of-memory error | Give it more heap: `isabelle build -o ML_system_64 -d . -e Lemmon_Fitch`, and close other applications. 8 GB RAM is comfortable. |
| Build appears hung | Some individual proofs take a minute or more. Wait ten minutes before concluding anything; `isabelle build -v` shows per-theory progress. |
| jEdit opens but nothing processes | The Theories panel has to be given focus; also confirm you passed `-l HOL`. |
| Exports differ after `-e` | Report it rather than working around it. See Module 2. |

## What not to do

* Do not install the AFP; nothing here needs it.
* Do not build or select a `Lemmon_Fitch` heap for interactive work — `-n -l HOL`
  is intentional.
* Do not "fix" a proof that fails. If something fails to process on a correct
  Isabelle2025-2, that is a finding: record the exact error and which theory and
  line it came from, and report it. These sources are checked to build clean, so
  a failure means either a version mismatch or something worth telling the
  authors about.
