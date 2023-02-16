# Artifact: Dependent Merges and First-Class Environments

- Title of the submitted paper: **Dependent Merges and First-Class Environments**

## Overview: What does the artifact comprise?

This artifact contains the mechanical formalization of the calculi associated with the paper Dependent Merges and First-Class Environments. All of the metatheory has been formalized in Coq theorem prover. We provide a docker image. Artifact can either be compiled in the pre-built docker image with all the dependencies installed or it could be built from the scratch.

We claim the functional, reusable, and available badges.

## For authors claiming a functional or reusable badge: What are claims about the artifact’s functionality to be evaluated by the committee?

All of the metatheory and theorems stated in paper can be found in the artifact.

There are two directories in the artifact: the `calculus` directory contains the definition and proofs of the main calculus; and the `extension` directory contains the definition and proofs of the extension with fixpoints (discussed in the Appendix). 

The structures of these two directories are almost the same. For `extension`, the system is extended with fixpoints in `Language.v`. All the metatheory does not require significant changes for this extension. The proof structure and correspondence mentioned below are applied for both `calculus` and `extension`.

### Proof Structure
- `Language.v` contains the definitions of the calculi.
- `Infra.v` contains some helper relations for proofs.
- `SubDis.v` contains properties of the subtyping and disjointness.
- `Determinism.v` contains the proofs of the determinism property.
- `TypeSafety.v` contains the proofs of the progress and type preservation properties.
- `Encoding.v` contains the proofs of the well-typed encoding of lambda_i.

### Correspondence between paper and Coq proofs

| Paper                 | File          | Name in Coq                                                  |
| --------------------- | ------------- | ------------------------------------------------------------ |
| Lemma 2               | SubDis.v      | 1. dis_sym; 2. dis_and; 3. dis_dom; 4. dis_rcd; 5. dis_arr; 6. dis_super |
| Lemma 4               | Determinism.v | disjoint_val_consistent                                      |
| Lemma 5               | Determinism.v | value_closed                                                 |
| Lemma 6               | Determinism.v | casting_unique                                               |
| Theorem 7             | Determinism.v | gen_step_unique                                              |
| Corollary 8           | Determinism.v | step_unique                                                  |
| Lemma 9               | TypeSafety.v  | casting_progress                                             |
| Lemma 10              | TypeSafety.v  | casting_trans                                                |
| Lemma 11              | TypeSafety.v  | consistent_after_casting                                     |
| Lemma 12              | TypeSafety.v  | casting_preservation                                         |
| Theorem 13            | TypeSafety.v  | gen_progress                                                 |
| Theorem 14            | TypeSafety.v  | gen_preservation                                             |
| Corollary 15          | TypeSafety.v  | progress                                                     |
| Corollary 16          | TypeSafety.v  | preservation                                                 |
| Corollary 17          | TypeSafety.v  | gen_type_safety                                              |
| Corollary 18          | TypeSafety.v  | type_safety                                                  |
| Theorem 20            | Encoding.v    | encoding_complete                                            |
| Theorem 22 (Appendix) | SubDis.v      | algo_dis_eqv                                                 |


## For authors claiming a reusable badge: What are the authors' claims about the artifact's reusability to be evaluated by the committee?

This Coq proof artifact is also reusable: any extension or alteration to the system can be easily done with our provided Coq scripts, and after possible adjustments, all the proofs can be reused for the formalization of the extended or altered system.

## For authors claiming an available badge

We agree to publish under a Creative Commons license on DARTS.


## Artifact Requirements

Our Coq proofs are verified in **Coq 8.13.1** and **Coq 8.16.0**. We rely on two Coq libraries: [`LibTactics.v`](http://gallium.inria.fr/~fpottier/ssphs/LibTactics.html) (which is included in the directories `calculus` and `extension`) and [`metalib`](https://github.com/plclub/metalib) in our proofs.

## Getting Started

We provide two alternatives to run the artifact:
1. Docker Image, or
2. Build From Scratch

### 1) Docker Image
This is the easiest way to run the artifact. We provide a docker image with all the dependencies installed in it.

This section explains how to pull the docker image of artifact from docker repo and use it. Run the following commands one by one in terminal:

1. `$ docker pull confartifact/ecoop2023`
2. `$ docker run -it confartifact/ecoop2023`

Note: Please note that **$** symbol appearing in the beginning is not a part of the command.

The artifact is located in the directory: `/home/coq/ecoop2023`. There are two folders in the artifact, with make file in each:
- `calculus` contains the definition and proofs of the main calculus;
- `extension` contains the definition and proofs of the extension with fixpoints (discussed in the Appendix). 

Go to each folder and run make:
#### calculus:
1. `$ cd /home/coq/ecoop2023/calculus`
2. `$ make`
#### extension:
1. `$ cd /home/coq/ecoop2023/extension`
2. `$ make`

This completes the evaluation of artifact following docker image.

### 2) Build from Scratch
This section explains how to build the artifact from scratch.

#### Prerequisites

1. Install **Coq 8.13.1** or **Coq 8.16.0**. The recommended way to install Coq is via `OPAM`. Refer to [here](https://coq.inria.fr/opam/www/using.html) for detailed steps. Or one could download the pre-built packages for Windows and MacOS via [here](https://github.com/coq/coq/releases/tag/V8.13.1) (8.13.1) or [here](https://github.com/coq/coq/releases/tag/V8.16.0) (8.16.0). Choose a suitable installer according to your platform.
2. Make sure `Coq` is installed (type `coqc` in the terminal, if you see "command not found" this means you have not properly installed Coq), then install `Metalib`:
   1. Open terminal
   2. `git clone https://github.com/plclub/metalib`
   3. `cd metalib/Metalib`
   4. `make install`

#### Build and Compile the Proofs

1. Enter either `calculus` or `extension` directory.
2. Please make sure to run the command `$ eval $(opam env)` before running make if you installed the Coq via opam.
3. Type `make` in the terminal to build and compile the proofs.
