CertiCrypt
====================================================================

Abstract
--------------------------------------------------------------------

As cryptographic proofs have become essentially unverifiable,
cryptographers have argued in favor of developing techniques that help
taming the complexity of their proofs. Game-based techniques provide a
popular approach in which proofs are structured as sequences of games,
and in which proof steps establish the validity of transitions between
successive games. Code-based techniques form an instance of this
approach that takes a code-centric view of games, and that relies on
programming language theory to justify proof steps. While code-based
techniques contribute to formalize the security statements precisely
and to carry out proofs systematically, typical proofs are so long and
involved that formal verification is necessary to achieve a high
degree of confidence. We present CertiCrypt, a framework that enables
the machine-checked construction and verification of code-based
proofs. CertiCrypt is built upon the general-purpose proof assistant
Coq, and draws on many areas, including probability, complexity,
algebra, and semantics of programming languages. CertiCrypt provides
certified tools to reason about the equivalence of probabilistic
programs, including a relational Hoare logic, a theory of
observational equivalence, verified program transformations, and
game-based techniques such as reasoning about failure events. The
usefulness of CertiCrypt is demonstrated through classical examples,
including a proof of semantic security of OAEP (with a bound that
improves upon the bound proved by Bellare and Rogaway), and a proof of
existential unforgeability of FDH signatures. Our work provides a
first yet significant step towards Halevi's ambitious programme of
providing tool support for cryptographic proofs.


Compilation
--------------------------------------------------------------------

This version of the development must be compiled with the latest
stable release of Coq 8.3, which can be downloaded from

    https://github.com/coq/coq/tree/v8.3

Some examples require SSReflect version 1.3 (pl4), which can be
downloaded from

    http://ssr.msr-inria.inria.fr/FTP/

To compile the source using GNU make, just launch

    $> make

from the top level folder (where this README file is located). The Coq
compiler (`coqc`) should be in your PATH for this to work. Depending on
your computer, and on whether you are using the native or the bytecode
version of the Coq compiler, this can take some time (expect 20
minutes for the main development in a native compiler). You will be
able to see the progress in your terminal.


Interactive interpretation
--------------------------------------------------------------------

If you want to use the coq interpreter interactively to explore the
development, e.g. by using CoqIDE of ProofGeneral, you should first
add the directories ALEA/, Lib/, and Semantics/ to the coqtop
loadpath.  An easy way to do this is to create a text file named
.coqrc in your home folder containing:

    Add LoadPath "<certicrypt>/Lib".
    Add LoadPath "<certicrypt>/ALEA".
    Add LoadPath "<certicrypt>/Semantics".

Where `<certicrypt>` stands for the absolute path to the top level
folder of the certicrypt development.

Contents
--------------------------------------------------------------------

+ `ALEA/`
  C. Paulin and P. Audebaud's library for the probability monad.

+ `Lib/`
  Extensions to the standard library of Coq.

+ `Semantics/`
  - Definition of the pWhile language and its semantics.

  - Probabilistic Relational Hoare Logic and theory of observational
    equivalence.

  - Functors for dataflow analyses and optimizations.

  - Tactics for game transformations, and for proving PPT and lossless.

  - Proof of the fundamental lemma of game-playing and implementation of
    a syntactic criterion to apply it.

+ `Examples/`
  - `ElGamal/`
    Proof of semantic security of ElGamal encryption.

  - `FDH/`
    Proof of existential unforgeability of the FDH signature scheme
    (original bound).

  - `FDHcoron/`
    Proof of existential unforgeability of the FDH signature scheme
    (Coron's optimal bound.)

  - `HElGamal/`
    Proof of semantic security of Hashed ElGamal encryption in the
    Standard Model.
  
  - `HElGamal_ROM/`
    Proof of semantic security of Hashed ElGamal encryption in the
    Random Oracle Model.

  - `IBE/`
    Proof of IND-ID-CPA security of Boneh-Franklin BasicIdent scheme.

  - `OAEP/`
    Proof of semantic security of the OAEP padding scheme.

  - `OAEP-CCA/`
    Proof of IND-CCA security of the OAEP padding scheme.

  - `Switching/`
    Proof of the PRP/PRF switching lemma.
