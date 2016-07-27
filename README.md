# Mechanization of a noninterference proof for a toy imperative language with small-step semantics in Coq.

Author: Aslan Askarov

The main NI theorem is in `NIBridge.v`

## Usage
Invoke `make` to compile everything.


## Notes
- The proof scripts use CPDT tactics. It assumes existence of the file `CpdtTactics.v` in `lib/cpdt/`; they are not included in the repository.
- The proof uses `LibTactics` and software foundation tactics `SfLib.v`;
  these and other small libraries are included for convenience in `lib/`.
- Comments and suggestions on how to improve these scripts are welcome.


## ChangeLog

### 2016-07-27: Simplifying proof structure and porting to 8.5
#### Added
- Added `_CoqProject` file and a better `Makefile`
- Including an updated version of `LibTactics` that compiles in 8.5

#### Changes
- Simplifying the way the bridge relation is formulated, reducing the overall size of the codebase.
- More automation.

### 2016-07-10: update to the next version of Cpdt tactics.

### 2015-04-04: initial version of the proof.
