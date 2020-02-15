# Mechanization of a noninterference proof via a type system for a simple imperative language with a small-step semantics in Coq.

Author: Aslan Askarov

- Coq version: 8.7
- An (in-progress) description of the [proof architecture](#Proof Architecture) is below.
- The standard TINI theorem is at the bottom of `TINI.v`.
- The workhorse noninterference reasoning is in `NIBridge.v`.

## Usage
Run `make` to compile everything.


## Notes
- The proof scripts use CPDT tactics; they are included in `lib/cpdt`.
- The proof uses `LibTactics` and software foundation tactics `SfLib.v`;
  these and other small libraries are included for convenience in `lib/`.
- Comments and suggestions on how to improve these scripts are welcome.
- For a version of this proof technique applied to a dynamic monitor, see this repository https://github.com/Crowton/DynamicNoninterference

---
## Proof Architecture

A more thorough description of the proof technique, including some introduction
and background, is available in [infoflow-basics.pdf](infoflow-basics.pdf).

### The language and the semantics.
Our language is the standard imperative language, given by the following grammar

    e := n | x | e + e
    c := skip | x := e | c; c | if e then c else c | while e do c | stop

#### Semantics

__Memory__ is a partial function from variable names to values. Variable _x_ has
value _v_ in memory _m_, when `m x = Some v`.


Semantics is a mixed-step semantics. For expressions, we use a big-step
evaluation relation `eval m e v` that means expression _e_ evaluates to value
_v_ in memory _m_. Semantics for commands is given as a relation `step cfg
cfg'`, also written as  _cfg_ ⇒ _cfg'_  that relates two configurations.
A __configuration__ is a pair of a command and a memory, often expressed using
notation 〈_c_,_m_〉.

Reachability in zero or many steps, denoted as cfg ⇒\* cfg',
is defined later in module [Bridge.v](Bridge.v).
The same module also defines reachability in at most n steps with the
corresponding notation cfg ⇒/+ n +/ cfg'.

#### Security environment
We assume two security levels _Low_ and _High_ that form a simple two-point
lattice, with a _flowsto_ relation ⊑, such that for all ℓ we have ℓ ⊑ ℓ, and _Low_ ⊑ _High_, but
not _High ⊑ Low_.

A __security environment__ is a partial function Γ mapping variable names to security levels.
Variable _x_ has security level ℓ in Γ when `Γ x = Some ℓ`.

#### Well-formedness
A memory _m_ is well formed w.r.t. a security environment Γ when _dom_ (_m_) = _dom_ (Γ); this is formalized as `wf_mem m Γ`.


#### Low-equivalence

Two memories _m_ and _s_ are low-equivalent w.r.t. an environment Γ, when
they each are well-formed w.r.t. Γ and they agree on the values of all low variables.
This is denoted using relation `state_low_eq Γ m s`. Low-equivalence is formally
defined in the module [LowEq.v](LowEq.v).


### Type system

The type system is a standard information flow type system, in the style of Volpano Smith Irvine, aka Denning-style enforcement.
Notation `-{ Γ, pc ⊢ c}-` means that program _c_ is well-typed
in the security environment Γ given the program counter label _pc_.
The typing rules are standard, and are formalized in the module [Types.v](Types.v).


#### Preservation
The preservation theorem is standard. The following statement of the preservation
theorem is an excerpt from [WellFormedness.v](WellFormedness.v).

    Theorem preservation:
      forall Γ c m c' m' pc,
      -{ Γ, pc ⊢ c}- ->
     〈c, m 〉 ⇒ 〈c', m' 〉->
      wf_mem m Γ ->
      wf_mem m' Γ /\ ( c' <> STOP -> -{Γ, pc ⊢ c'}- ).


### Noninterference

Top-level noninterference is the standard termination-insensitive
noninterference. To prove NI we extend our semantics with with so-called _events_ — the resulting event semantics is  an augmentation of the original semantics. We also introduce bridge steps, that
are the key tool in the proof. We show that each of these extensions is
adequate w.r.t. the original small-step transition relation in the module [Adequacy.v](Adequacy.v).

#### Event semantics

We distinguish between two kinds of events:
_low assignments_, and _empty events_ that correspond to all other steps. Events
are propagated through sequential composition.

We say that an event step is a low step if it produces a low event, and is a high step otherwise.

The event semantics is defined in the module [Augmented.v](Augmented.v).

#### Bridge relation

Bridge relation is the key workhorse relation. Say that configuration *cfg*
bridges to configuration *cfg'* when *cfg'* is the first configuration reachable
from *cfg* after a low assignment or a *cfg'* is a terminal configuration. Bridge
relation is defined in terms of the event semantics. Bridge relations are
indexed by the number of intermediate steps, which is needed in order to apply
the strong induction principle in the noninterference for bridge steps.


We use notation `cfg ↷(Γ, ev, n) cfg'` to denote that configuration _cfg_
"bridges" to configuration _cfg'_ producing event _ev_ with _n_ intermediate high steps.
The following rules provide the idea behind the bridge relation; see the formal definition
in the module [Bridge.v](Bridge.v) for details.

    low_event_step Γ ℓ evt cfg cfg'
    ____________________________________  [bridge_low_num]
    cfg ↷(Γ, evt, 0) cfg'



    high_event_step Γ ℓ evt cfg 〈STOP,m〉
    ____________________________________  [bridge_stop_num]
    cfg ↷(Γ, evt, 0) 〈STOP,m〉



    high_event_step Γ ℓ evt cfg cfg'
    is_not_stop cfg'  
    cfg' ↷(Γ, evt'', n) cfg''
    ____________________________________  [bridge_trans_num]
    cfg ↷(Γ, evt'', n+1) cfg''


### Noninterference for bridge steps.

The following is an excerpt from
[NIBridge.v](NIBridge.v), where the last four lines in the definition encode the postconditions.


    Definition NI_idx (n: nat): Prop :=
      forall Γ pc c,
      -{ Γ, pc ⊢ c }- ->
      forall m s ev1 ev2 c2 d2 m2 s2 n',
        state_low_eq Γ m s ->
        〈c, m〉 ↷ ( Γ, ev1, n ) 〈c2, m2〉->
        〈c, s〉 ↷ ( Γ, ev2, n') 〈d2, s2〉->      
              state_low_eq Γ m2 s2 /\
              c2 = d2 /\
              (low_event Γ Low ev1 <-> low_event Γ Low ev2) /\
              (low_event Γ Low ev1 -> ev1 = ev2).

    Theorem ni_bridge_num:
        forall n, NI_idx (n).


This theorem is proved using an outer strong induction on _n_, with inner inductions on the typing
derivation. In the outer base case (_n_ = 0) the only possible cases are skip, assignment, and sequential composition. In the outer inductive case the only possibly cases
are sequential composition, if, and while commands.


### Adequacy and relating to standard NI

We relate noninterference for the bridge relation to standard noninterference via
[adequacy](Adequacy.v) of the bridge relation. The final connection is made in the
module [NI.v](NI.v).

    (** Standard termination-insensitive noninterference *)

    Theorem TINI:
      forall Γ c m s m_end s_end pc,
        -{ Γ, pc ⊢ c }- ->
          state_low_eq Γ m s ->
            〈c, m 〉 ⇒* 〈STOP, m_end 〉 ->
            〈c, s 〉 ⇒* 〈STOP, s_end 〉 ->
                state_low_eq Γ m_end s_end.


---



## ChangeLog

### 2016-08-03: More simplifications.
### Added
- High-level description of the proof architecture.

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
