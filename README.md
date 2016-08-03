# Mechanization of a noninterference proof for a toy imperative language with small-step semantics in Coq.

Author: Aslan Askarov

- An (in-progress) description of the proof architecture is available in [DESCRIPTION.md](DESCRIPTION.md).
- The standard TINI theorem is at the bottom of `TINI.v`.
- The workhorse noninterference reasoning is in `NIBridge.v`.

## Usage
Invoke `make` to compile everything.


## Notes
- The proof scripts use CPDT tactics. It assumes existence of the file `CpdtTactics.v` in `lib/cpdt/`; they are not included in the repository.
- The proof uses `LibTactics` and software foundation tactics `SfLib.v`;
  these and other small libraries are included for convenience in `lib/`.
- Comments and suggestions on how to improve these scripts are welcome.


## ChangeLog

### 2016-08-03: More simplifications.
### Added
- PROOFSTRUCTURE.md is a placeholder for the high-level description of the proof.

### Changed
- Simplified the definition of Bridge relation.

### 2016-07-29: Adequacy and Standard TINI
#### Added
- Indexed multi-step relation
- Adequacy theorem for the indexed multi-step relation
- Preservation for bridge relation
- The proof of Standard TINI via adequacy and NI for bridge

### 2016-07-27: Simplifying proof structure and porting to 8.5
#### Added
- Added `_CoqProject` file and a better `Makefile`
- Including an updated version of `LibTactics` that compiles in 8.5

#### Changes
- Simplifying the way the bridge relation is formulated, reducing the overall size of the codebase.
- More automation.

### 2016-07-10: update to the next version of Cpdt tactics.

### 2015-04-04: initial version of the proof.
