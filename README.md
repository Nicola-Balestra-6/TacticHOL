# TacticHOL

TacticHOL is an automated tactical prover for HOL Light. It learns
from an instrumented copy of the library, which records successful
tactic applications together with the goals they acted on; from these
steps it predicts, using features of the terms involved, which tactic a
human would apply and which theorems to give it as arguments, and
explores the candidates by Monte Carlo tree search. In the evaluation,
theorems are attempted in library order, each using only the material
that precedes it. For theorems that remain unproved after search, an
intermediate-lemma mechanism asks a large language model for lemmas
that could split the proof: candidates that could not have been stated
at that point of the library are rejected before any search, and the
surviving ones are tried in turn, each starting a fresh search that
must prove both the lemma and the original goal from it, until one
succeeds. Every proof found is rebuilt by the kernel of HOL Light
before it is counted.

This directory is the whole repository. It lives inside a HOL Light
tree, as `<hol-light>/TacticHOL/`, and reads the HOL Light sources from
there.

## Layout

    lib/tactichol.ml        entry point for interactive use
    lib/                    recorder, tactic execution, argument instantiation
    lib/mcts/               feature index, prediction, search, evaluation runner
    lib/lemma_channel/      the intermediate-lemma channel, stage by stage
    lib/replay_kernel.ml    kernel replay of the proofs found
    lib/grammar/            tactic lexer, parser, printer, argument abstraction (dune)
    lib/rewrite/            instrumentation of the library sources (dune)
    hol_min/                the minimal HOL Light session used for recording
    bin/                    the dune executables of the pipeline
    scripts/build_corpus.sh builds the corpus from the HOL Light sources
    scripts/add_theory.sh   registers a new theory for the corpus
    scripts/recording/      instrumentation and recording, one session per theory
    scripts/dataset/        chronological index, merge, export
    scripts/lemma_channel/  the model call, the join, and the channel's own README
    repl/                   one file per run: load it in a fresh REPL, then start the run
    examples/               a proof built as a chain of calls to the prover
    data/                   built by build_corpus.sh, not in the repository

## Requirements

- HOL Light at commit `157c99b7` of https://github.com/jrh13/hol-light
  (release 3.1.0 plus the support for Camlp5 8.03.06; none of the files
  that `hol.ml` loads differs from the release), built in its root
  directory with `make switch-5`, `eval $(opam env)` and `make`, as its
  README says. This creates a local opam switch with OCaml 5.2.0 and
  Camlp5 8.03.06 and produces `pa_j.cmo` and `hol.sh`. The scripts run
  HOL Light through `hol.sh` and use the opam switch of the HOL Light
  root, or the one named by the environment variable `TT_OPAM_SWITCH`.
- The recording sessions use the minimal HOL Light session of
  `hol_min/hol_min.ml`, which loads the kernel, `bool`, `drule` and
  `tactics` and nothing after them.
- In that switch, `opam install dune yojson menhir` (reference
  versions: dune 3.20.2, yojson 3.0.0, menhir 20250912). `dune build`
  in this directory names anything missing.
- Python 3, for the dataset scripts and the model call.

## 1. Build the corpus

    ./scripts/build_corpus.sh

Nine steps, from the HOL Light sources: the library is rewritten into
`z_lib/` with every tactic wrapped in a recording function; the
chronological index of the theorems is built by loading the library in
order; each instrumented theory is loaded in a fresh minimal session,
which records every successful tactic application with the goal it
acted on; the recordings are merged, the tactic arguments are
abstracted into placeholders, and the four files the prover reads at
start-up are exported to `data/chrono/`. The script stops if a corpus
is already there; `--rebuild` copies it aside first. Times measured on
one machine (the rebuild, about 16 minutes) are indicative.

The theories are listed in four places, on purpose with different
counts (which theories are instrumented, which are recorded, which are
merged, and which are loaded for the index); the script reports what
the lists imply and stops when a recording would be skipped in
silence. `scripts/add_theory.sh` edits the four lists together.

The first session after a build activates the whole corpus and saves
the policy state in `data/chrono/policy_state.snapshot`, about 270 MB:
about 20 minutes once, then about 20 seconds at every later start. The
snapshot is checked against the corpus it was built from and rebuilt
when they differ. Neither the corpus nor the snapshot is in the
repository.

## 2. Use the prover

In a HOL Light session launched from this directory:

    #use "lib/tactichol.ml";;
    let LEMMA = tactichol `!m n. m + n = n + m`;;

`tactichol : term -> thm` searches for a proof of the term and, when
one is found, lets `prove` build the theorem, so that the result is a
theorem of the kernel; it fails when no proof is found within
`tactichol_budget` seconds (60 by default). The root directory is taken
from the environment variable `TACTICHOL_ROOT` when set, and from the
launch directory otherwise.

This entry point activates the whole corpus: a goal is attempted with
every recorded step and every library theorem, which is the opposite of
the regime of the evaluation below, where each theorem is attempted
with only what precedes it. The activation cannot be undone in the same
session, so no chronological run can share a REPL with it.

`examples/cauchy_schwarz.ml` proves the Cauchy-Schwarz inequality in
two dimensions as a chain of three calls to `tactichol` and one manual
composition.

## 3. Reproduce the evaluation

Each file of `repl/` sets up one run: loaded in a fresh HOL Light
session launched from this directory, it loads what the run needs,
sets its parameters, checks them, and prints the call that starts the
run. It starts nothing itself.

    repl/eval_search_30s.ml        search over the library, 30 s per theorem
    repl/eval_search_atp_30s.ml    the same, with the ATP channel
    repl/eval_search_atp_60s.ml    the same, with the ATP channel and 60 s
    repl/replay_kernel_search.ml   kernel replay of the proofs of a search run
    repl/lemma_search_30s.ml       leaf search of the lemma channel, 30 s per search
    repl/lemma_search_60s.ml       the same, with 60 s

The search runs go through the library in chronological order: before
each theorem the prover activates only the recorded steps and the
theorems that precede it. The three search runs process the theorems
in batches and resume from their output file, so an interrupted run
continues from a fresh session; the leaf searches never overwrite
their output and resume only by hand, as their files explain. The
kernel replay reads the proofs a search run wrote
and asks the kernel to build every theorem; a proof counts only if the
kernel accepts it. One run per session: the activation of the corpus
only moves forward.

## 4. The intermediate-lemma channel

`scripts/lemma_channel/README.md` describes the channel stage by
stage: export of the goals the search left unproved, the call to the
model, the typing gate, the chronological filter, the leaf search, the
restated-goal check, the assembly of the proofs and their kernel
replay. The model is reached through an API with a key the user
provides in the environment; the key never appears in a file of the
repository.

## 5. Extend the library

A new theory is a file `<name>.ml` in the HOL Light root, opening with
`needs "<last theory of the chain>.ml";;` like every library file,
since the recording sessions are minimal and rely on that line. Then:

    ./scripts/add_theory.sh <name>
    ./scripts/build_corpus.sh --rebuild

The first registers the theory in the four lists and checks the
`needs` line, telling the exact line to add if it is missing; the
second rebuilds the corpus with it, and the next session rebuilds the
policy snapshot. Theorems in the form `prove(tm, tac)` get their proof
steps recorded; other forms still enter the index as premises. Write
one theorem per `;;` at top level: theorems declared together between
two `;;`, as inside a module, get their relative order in the index
from the session and not from the source, and only the one such case
of the HOL Light library is corrected (`scripts/dataset/fix_chrono_index.py`).

## 6. Known limits

- Recorded steps whose tactic contains `SUBGOAL_THEN`, or an anonymous
  function `fun ... ->`, are dropped from the dataset by
  `scripts/dataset/prepare_chrono_data.py`: the proofs assembled by the
  lemma channel have the first form, so extending the library with them
  records them but does not learn from them.
- The library is instrumented at the level of the individual tactics:
  a step is always the application of one tactic. A proof whose tactic
  the rewriter does not parse, as one passing an anonymous function to
  a tactical, is left as it is and yields no step; the tactics inside a
  `let` binding within a tactic yield no step either.
- The policy activation never rolls back within a session. Every run,
  and the interactive entry point, needs a fresh REPL.
- The prover forks a child process for each tactic application, with a
  wall-clock limit per tactic and per search: the outcome of a search
  at the edge of its budget depends on the load of the machine.

## License

See `LICENSE`.
