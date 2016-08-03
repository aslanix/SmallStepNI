# Proof Architecture

## The language and the semantics.
Our language is the standard imperative language, given by the following grammar

    e := n | x | e + e
    c := skip | x := e | c; c | if e then c else c | while e do c | stop

### Semantics

__Memory__ is a partial function from variable names to values. Variable _x_ has
value _v_ in memory _m_, when `m x = Some v`.


Semantics is a mixed-step semantics. For expressions, we use a big-step
evaluation relation `eval m e v` that means expression _e_ evaluates to value
_v_ in memory _m_. Semantics for commands is given as a relation `step cfg
cfg'`, also written as  _cfg_ ⇒ _cfg'_  that relates two configurations.
A __configuration__ is a pair of a command and a memory, often expressed using
notation 〈_c_,_m_〉.

### Security environment
We assume two security levels _Low_ and _High_ that form a simple two-point
lattice, with a _flowsto_ relation ⊑, such that for all ℓ we have ℓ ⊑ ℓ, and _Low_ ⊑ _High_, but
not _High ⊑ Low_.

A __security environment__ is a partial function Γ mapping variable names to security levels.
Variable _x_ has security level ℓ in Γ when `Γ x = Some ℓ`.

### Well-formedness
A memory _m_ is well formed w.r.t. a security environment Γ when they _dom_ (_m_) = _dom_ (Γ).


### Low-equivalence

Two memories _m_ and _s_ are low-equivalent w.r.t. an environment Γ, when
they each are well-formed w.r.t. Γ and they agree on the values of all low variables.


## Type system

Our type system is a standard information flow type system, in the style of Volpano Smith Irvine (aka Denning-style enforcement). We use notation `-{ Γ, pc ⊢ c}-` to denote that program _c_ is well-typed
in security environment Γ given the program counter label _pc_.


## Noninterference

Top-level noninterference is the standard termination-insensitive
noninterference. To prove NI we define event semantics, that is
an augmentation of the original semantics, and introduce bridge steps, that
are the key tool in the proof. We show that each of these extensions are
adequate w.r.t. the original small-step transition relation.

### Event semantics

Event semantics is a semantics that extends the original one with so-called
_event_.  In the current setting, we distinguish between two kinds of events:
_low assignments_, and _empty events_ that correspond to all other steps. Events
are propagated through sequential composition.

We say that an event step is a low step if it produces a low event, and is a high step otherwise.

### Bridge relation

Bridge relation is the key workhorse relation. Say that configuration *cfg*
bridges to configuration *cfg'* when *cfg'* is the first configuration reachable
from *cfg* that is either a low assignment or program termination. Bridge
relation is defined in terms of the event semantics. Bridge relations are indexed by the number of
intermediate steps, which is needed in order to apply the strong induction principle in the
noninterference for bridge steps.

## Noninterference for bridge steps.

TBA

## Adequacy

TBA
