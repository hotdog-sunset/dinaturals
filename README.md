# Agda formalization for the APLAS 2026 submission "Dinaturals Compose, Up-to Loops"

This file contains the Agda formalization files for the APLAS 2026 submission "Dinaturals Compose, Up-to Loops".

## How to run this

### Option 1

1. Install [Nix](https://nixos.org/download/), and enable [flakes](https://nixos.wiki/wiki/Flakes). Tested with Nix 2.34.6.
2. Run `nix develop`. This puts you in a `bash` shell with a working Agda installation with all libraries installed.
3. Run `nix build`. This `--safe`ly typechecks the entire formalization and builds browsable HTML files.

### Option 2

1. Install [Agda](https://agda.readthedocs.io/en/latest/getting-started/installation.html) `v2.8` manually.
2. Install the [`agda-categories`](https://github.com/agda/agda-categories) library `v0.3.0`.
3. Install the [`agda-stdlib`](https://github.com/agda/agda-stdlib) library `v2.3`.
4. Run `agda --html --html-dir=html/ --highlight-occurrences --safe All.agda +RTS -M16G`.
5. Browse the formalization, starting from the `All.agda` file.

## Description

The file `All.agda` groups all formalization files for batch typechecking/inspection. Typecheck the code by running Agda in Safe Mode:
```bash
$ agda --safe ./All.agda +RTS -M16G  # Recommended flags for Agda.
```

The flake output `agda-html` can be used to typecheck and build the HTML for the `All.agda` file (the above flags are already active):

```bash
$ nix build '.#agda-html' # This typechecks and creates a browsable HTML output.
$ xdg-open html/All.html  # Open html/All.html in your browser.
```

## Files structure

A description of each file can be read in [All.agda](All.agda). Each of the theorems in the paper links to a single formalization file.

## Requirements

- `agda` 2.8
- `agda-categories` 0.2.0
- `agda-stdlib` 2.3
