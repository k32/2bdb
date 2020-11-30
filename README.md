# LibTx

[![builds.sr.ht status](https://builds.sr.ht/~k32/libtx.svg)](https://builds.sr.ht/~k32/libtx?)

LibTx is a collection of theorems about distributed databases proven
from the first principles. A far-fetched goal of this project is to
create a formally verified transaction engine for OLTP databases,
similar to [mnesia](http://erlang.org/doc/man/mnesia.html). Note that
this library does not implement a storage engine and distributed
message queue.

## How proofs in this repo work

Logic of `libtx` is written in Gallina language (the specification
language of Coq). Effects are simulated using a library called `SLOT`
(developed in-house) that allows to model nondeterministic I/O. `SLOT`
allows to verify all possible executions of the program and extract a
Coq proofs, that are mostly free of axioms (we only rely on the
excluded triple in some places).

Since formal proofs are only as useful as their assumptions (garbage
in -- garbage out), a lot of effort went into keeping the number of
assumptions to the minimum. Generally speaking, there are two levels
of assumptions in SLOT:

 - core definitions that describe the behavior of a concurrent
   distributed system doing I/O in general

 - I/O handler models that describe behavior of specific 3rd party
   services, such as network, message queues, disk, etc.

### Core definitions

(Note on terminology: internally we call I/O operations "trace
elements" or "TE" for short, and sequences of I/O operations are
called "traces")

Below you can find the full list of core assumptions made by `SLOT`:

1) [StateSpace](https://git.sr.ht/~k32/libtx/tree/master/theories/SLOT/Hoare.v)
    class allows to define non-deterministic side effects of the I/O operation:

   ```coq
   Class StateSpace (S TE : Type) :=
     { chain_rule : S -> S -> TE -> Prop;
     }.
   ```

2) [LongStep](https://git.sr.ht/~k32/libtx/tree/master/theories/SLOT/Hoare.v)
    inductive datatype defines side effects of multiple I/O operations executed
    sequentially:

   ```coq
   Inductive LongStep : S -> T -> S -> Prop :=
   | ls_nil : forall s,
       LongStep s [] s
   | ls_cons : forall s s' s'' te trace,
       chain_rule s s' te ->
       LongStep s' trace  s'' ->
       LongStep s (te :: trace) s''.
   ```

3) [HoareTriple](https://git.sr.ht/~k32/libtx/tree/master/theories/SLOT/Hoare.v)
    is a type that introduces Hoare logic of I/O operations:

   ```coq
   Definition HoareTriple (pre : S -> Prop) (trace : T) (post : S -> Prop) :=
     forall s s',
       LongStep s trace s' ->
       pre s -> post s'.
    ```

4) [TraceInvariant](https://git.sr.ht/~k32/libtx/tree/master/theories/SLOT/Hoare.v)
    is an inductive datatype that is used to describe invariants of the system:

    ```coq
    Inductive TraceInvariant (prop : S -> Prop) : T -> Prop :=
    | inv_nil : TraceInvariant prop []
    | inv_cons : forall te t,
        {{prop}} [te] {{prop}} ->
        TraceInvariant prop t ->
        TraceInvariant prop (te :: t).
    ```

5) [Interleaving](https://git.sr.ht/~k32/libtx/tree/master/theories/SLOT/Ensemble.v)
   is an inductive datatype that describes all possible ways to execute a concurrent
   system of two processes

    ```coq
    Inductive Interleaving : list TE -> list TE -> TraceEnsemble :=
    | ilv_cons_l : forall te t1 t2 t,
        Interleaving t1 t2 t ->
        Interleaving (te :: t1) t2 (te :: t)
    | ilv_cons_r : forall te t1 t2 t,
        Interleaving t1 t2 t ->
        Interleaving t1 (te :: t2) (te :: t)
    | ilv_nil : Interleaving [] [] [].
    ```

### I/O handler models

(Currently they are largely WIP)
