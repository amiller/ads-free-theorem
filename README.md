# Authenticated Data Structures, for Free

Formalizing Atkey's 2016 claim that the security of authenticated data structures follows from parametricity alone, using internal parametricity in Cubical Agda ([agda-bridges](https://music-impl.pages.gitlabpages.inria.fr/agda-music-graded/agda-bridges.html)).

## The result

A program polymorphic over an "auth kit" interface (monad `m`, wrapper `au`, operations `ret`/`bind`/`auth`/`unauth`) must produce the same pure value regardless of which kit implements it. The type signature *is* the security argument.

**Theorem (purity):** For any lawful kit satisfying monad left-identity and auth roundtrip:
```
f kit x ≡ ret (f IdKit x)
```

**Corollary (agreement):** Any two lawful kits (e.g. Prover, Verifier) produce the same underlying value.

## Files

| File | Description |
|------|-------------|
| `agda/AuthFreeThm.agda` | Main result: ADS security via parametricity (388 lines, no sorry) |
| `agda/TinyFreeThms.agda` | Warm-up: identity and Church bool free theorems |
| `agda/Noninterference.agda` | Noninterference from parametricity (total relation trick) |
| `agda-check` | Script to typecheck via Docker |
| `notes/paper-outline.md` | ICFP pearl paper outline |

## Background

- Miller, Hicks, Katz, Shi — [Authenticated Data Structures, as a Library](https://dl.acm.org/doi/10.1145/2535838.2535851) (POPL 2014)
- Atkey — [From Parametricity to Conservation Laws, via Noether's Theorem](https://dl.acm.org/doi/10.1145/2535838.2535867) (POPL 2014)
- Atkey — [Authenticated Data Structures, Generically](https://bentnib.org/posts/2016-04-12-authenticated-data-structures-as-a-library.html) (2016 blog post) — the claim we formalize
- Cagne, Lamiaux, Moeneclaey — [agda-bridges](https://music-impl.pages.gitlabpages.inria.fr/agda-music-graded/agda-bridges.html) — internal parametricity for Cubical Agda

## Development setup

These files require a patched version of Agda with bridge types (internal parametricity). The setup uses Docker to build and run the compiler.

### Prerequisites

- Docker
- ~4GB disk for the Haskell build cache

### 1. Get the compiler source

```bash
git clone https://music-impl.pages.gitlabpages.inria.fr/agda-music-graded/agda-bridges.git ~/agda-bridges-src
cd ~/agda-bridges-src
git checkout bridges-with-2.6.4
```

Two patches are needed in `~/agda-bridges-src` to handle `primMHComp` ordering:

**`src/full/Agda/TypeChecking/Rules/Record.hs:466`** — add `whenDefined` guard for mhocom generation

**`src/full/Agda/TypeChecking/Primitive/Cubical.hs:171-173`** — fall back to standard hcomp when `primMHComp` not yet bound

### 2. Build the compiler

```bash
docker run --rm \
  -v agda-bridges-stack-cache:/root/.stack \
  -v agda-bridges-stack-work:/agda/.stack-work \
  -v ~/agda-bridges-src:/agda \
  -w /agda haskell:9.8.1-slim bash -c '
    sed -i "s|deb.debian.org|archive.debian.org|g" /etc/apt/sources.list
    sed -i "/security.debian.org/d" /etc/apt/sources.list
    sed -i "/buster-updates/d" /etc/apt/sources.list
    apt-get update -qq && apt-get install -y -qq libgmp-dev zlib1g-dev libncurses5-dev gcc make >/dev/null 2>&1
    cp stack-9.8.1.yaml stack.yaml && stack install --system-ghc --fast 2>&1'
```

Full build takes ~20 min; incremental ~2 min. Exit code 42 at the end is expected.

### 3. Get the libraries

```bash
# Cubical Agda library
git clone https://github.com/agda/cubical.git deps/cubical
cd deps/cubical && git checkout a10e25a8 && cd ../..

# bridgy-lib (ROTT framework)
# Copy from agda-bridges distribution or clone separately
git clone <bridgy-lib-repo> deps/bridgy-lib
```

Then copy (or symlink) the `agda/*.agda` files from this repo into `deps/bridgy-lib/Bridgy/Examples/`.

### 4. Typecheck

```bash
./agda-check                          # defaults to AuthFreeThm.agda
./agda-check agda/TinyFreeThms.agda   # or specify a file
```

### Gotcha: `--bridges` flag is infective

The `--bridges` flag propagates to all imports. The prim library (`HCompU.agda`, `Glue.agda`) must be pre-compiled *without* `--bridges` first, or you get a cryptic error about `Σ` and Erased Cubical Agda. The `agda-check` script handles this automatically on first run.
