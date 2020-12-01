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
in — garbage out), a lot of effort went into keeping the number of
assumptions to the minimum. Generally speaking, there are three levels
of assumptions in SLOT:

 - Core definitions that describe side effects of I/O operations in
   general. These are considered fundamental to SLOT

 - Definitions describing behavior of concurrent and distributed
   systems

 - I/O handler models that describe behavior of specific 3rd party
   services, such as network, message queues, disk, etc. These
   definitions are domain-specific

### Core definitions

(Note on terminology: internally we call I/O operations "trace
elements" or "TE" for short, and sequences of I/O operations are
called "traces")

Below you can find the full list of core assumptions made by `SLOT`:

1) [StateSpace](https://git.sr.ht/~k32/libtx/tree/master/theories/SLOT/Hoare.v)
    class allows to define non-deterministic side effects of the I/O operation:

   ```coq
   Class StateSpace (S TE : Type) :=
     { state_transition : S -> S -> TE -> Prop;
     }.
   ```

   ![](https://git.sr.ht/~k32/libtx/blob/master/doc/state_space.png)

2) [ReachableByTrace](https://git.sr.ht/~k32/libtx/tree/master/theories/SLOT/Hoare.v)
    inductive datatype defines side effects of multiple I/O operations executed
    sequentially:

   ```coq
   Inductive ReachableByTrace : S -> T -> S -> Prop :=
   | rbt_nil : forall s,
       ReachableByTrace s [] s
   | rbt_cons : forall s s' s'' te trace,
       state_transition s s' te ->
       ReachableByTrace s' trace  s'' ->
       ReachableByTrace s (te :: trace) s''.
   ```

   ![](https://git.sr.ht/~k32/libtx/blob/master/doc/long_step.png)

3) [HoareTriple](https://git.sr.ht/~k32/libtx/tree/master/theories/SLOT/Hoare.v)
    is a type that introduces Hoare logic of I/O operations:

   ```coq
   Definition HoareTriple (pre : S -> Prop) (trace : T) (post : S -> Prop) :=
     forall s s',
       ReachableByTrace s trace s' ->
       pre s -> post s'.
    ```

   ![](https://git.sr.ht/~k32/libtx/blob/master/doc/hoare.png)

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

### Definitions describing concurrent systems

1) [Interleaving](https://git.sr.ht/~k32/libtx/tree/master/theories/SLOT/Ensemble.v)
   is an inductive datatype that describes all possible ways to execute a concurrent
   system of two processes (without sudden deaths):

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

    (It allows nesting, so it can be used to define a system with however many processes)

### I/O handler models

(Currently they are largely WIP)
