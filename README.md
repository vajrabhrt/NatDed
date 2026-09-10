# Build instructions 

```lean 
git clone https://github.com/vajrabhrt/NatDed.git
cd NatDed
lake exe cache get
lake build
```

# Natural Deduction

Natural Deduction, introduced by Gerhard Gentzen in the 1930s, is a fundamental framework for logic proofs, with a very rich history. One of the fundamental results is the weak normalization theorem, proved (but not published until much later) by Gentzen himself in 1933. The first published proof was by Dag Prawitz in 1965. This fundamental result is presented in most introductory texts on proof theory.

But (as far as I could determine), the proofs fall in one of the following categories:
1. Present a proof for the fragment with only implies (and perhaps conjunction), and sketch the modifications needed for the full fragment.
2. Present a proof of strong normalization for much richer systems like System F, and obtain weak normalization as a corollary.
3. Present the original elaborate proofs for full propositional (or first-order logic) with all the connectives, which involve notions like cut-segments and hard-to-parse rules for which cut to reduce next. (The textbook by Troelstra and Schwichtenberg contains essentially such proofs. The recent textbook by Mancosu, Galvan and Zach contains an excellent, very detailed proof of the weak normalization theorem, but they too follow the original proofs.)

This is an attempt at producing a short proof of weak normalization for intuitionistic propositional logic with all the connectives, where all the key transformations are "inductive". We define the contraction relation, and extend that to a one-step reduction which is tailored to our normalization strategy. Defining the one-step reduction (extracted from presentation by Mancosu, Galvan and Zach) is our main contribution.

This repository contains a formalisation of our proof in Lean. It currently has a proof of the weak normalization for NJ, (propositional) intuitionistic logic.

We hope to extend it for (propositional) classical logic, and then to first-order logic.
