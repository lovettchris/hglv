# Preface

Formal proof assistants are software tools designed to help their users carry out computer-checked
proofs in a logical calculus. We usually call them _proof assistants_, or _interactive theorem
provers_, but a mischievous student coined the phase “proof-preventing beasts,” and dictation
software occasionally misunderstands “theorem prover” as “fear improver.” Consider yourself warned.

**Rigorous and Formal Proofs** Interactive theorem proving has its own terminology, already starting
with the notion of “proof.” A _formal proof_ is a logical argument expressed in a logical formalism.
In this context, “formal” means “logical” or “logic-based.” Logicians—the mathematicians of
logics—carried out formal proofs on papers decades before the advent of computers, but nowadays
formal proofs are almost always carried out using a proof assistant.

In contrast, an _informal proof_ is what a mathematician would normally call a proof. These are
often carried out in \\(\LaTeX\\) or on a blackboard, and are also called “pen-and-paper proofs.” The level
of detail can vary a lot, and phrases such as “it is obvious that,” “clearly,” and “without loss of
generality” move some of the proof burden onto the reader. A rigorous proof is a very detailed
informal proof.

The main strength of proof assistants is that they help develop highly trustworthy, unambiguous
proofs of mathematical statements, using a precise logic. They can be used to prove arbitrarily
advanced results, and not only toy examples or logic puzzles. Formal proofs also help students
understand what constitutes a valid definition or a valid proof. To quote [Scott
Aaronson](https://www.scottaaronson.com/teaching.pdf):

> I still remember having to grade hundreds of exams where the students started out by assuming what
had to be proved, or filled page after page with gibberish in the hope that, somewhere in the mess,
they might accidentally have said something correct.

When we develop a new theory, formal proofs can help us explore it. They are useful when we
generalize, refactor, or otherwise modify an existing proof, in much the same way as a compiler
helps us develop correct programs. They give a high level of trustworthiness that makes it easier
for others to review the proof. In addition, formal proofs can form the basis of verified
computational tools (e.g., verified computer algebra systems).

**Success Stories** There have been a number of success stories in mathematics and computer science.
Three landmark results in the formalization of mathematics have been the proof of the [four-color
theorem](../bib.md#8) by Gonthier et al., the proof of the
[odd-order theorem](../bib.md#9) by Gonthier et al., and the proof of
the [Kepler conjecture](../bib.md#12) by Hales et al.. The earliest work in this
area was carried out by Nicolaas de Bruijn and his colleagues starting in the 1960s in a system
called [AUTOMATH](https://www.win.tue.nl/automath/).

Today, few mathematicians use proof assistants, but this is slowly changing. For example, 29
participants of the [Lean Together 2019 meeting in
Amsterdam](https://lean-forward.github.io/lean-together/2019/index.html), about formalization of
mathematics, self-identified as mathematicians.

Most users of proof assistants today are computer scientists. A few companies, including
[AMD](../bib.md#32) and [Intel](../bib.md#13), have been using proof assistants to verify their
designs. In academia, some of the milestones are the verifications of the operating system kernels
[seL4](../bib.md#16) and [CertiKOS](../bib.md#11) and the development of the verified compilers
[CompCert](../bib.md#19), [JinjaThreads](../bib.md#23), and [CakeML](../bib.md#18).

**Proof Assistants** There are dozens of proof assistants in development or use across the world. A
list of the main ones follows, classified by logical foundations:

- set theory: Isabelle/ZF, Metamath, Mizar;
- simple type theory: HOL4, HOL Light, Isabelle/HOL;
- dependent type theory: Agda, Coq, Lean, Matita, PVS;
- Lisp-like first-order logic: ACL2.

For a history of proof assistants and interactive theorem proving, we refer to Harrison, Urban, and
Wiedijk’s [highly informative chapter](../bib.md#14).

**Lean** Lean is a new proof assistant developed primarily by Leonardo de Moura (Microsoft Research)
since 2012. Its mathematical library, [mathlib](https://arxiv.org/pdf/1910.09336.pdf), was
originally developed under the leadership of Jeremy Avigad (Carnegie Mellon University) but is now
maintained and further extended by an [active users’ community](../bib.md#24).

We will use Lean community version 4, mathlib4, and a few extensions collected in a small library
called [LoVelib](https://github.com/blanchette/logical_verification_2021/raw/main/lean/lovelib.lean).
Although it is still a research project, with some rough edges, there are several reasons why Lean
is a suitable vehicle to teach interactive theorem proving:

- It has a highly expressive, and highly interesting, logic based on the calculus of inductive
  constructions, a dependent type theory.
- It is extended with classical axioms and quotient types, making it convenient to verify
  mathematics.
- It includes a convenient metaprogramming framework, which can be used to program custom proof
  automation.
- It includes a modern user interface via a [Visual Studio Code
  plugin](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4).
- It has highly readable, fairly complete documentation.
- It is open source and cross-platform.

Lean’s core library includes only basic algebraic definitions. More setup and proof automation are
found in mathlib. It is more than a mathematical library; it provides a lot of basic automation on
top of Lean’s core library that one would expect from a modern proof assistant.

**This Guide** This guide is a companion to the MSc-level course Logical Verification (LoVe) taught
at the Vrije Universiteit Amsterdam. Our primary aim is to teach interactive theorem proving. Lean
is the vehicle, not an end of itself. As such, this guide is not designed to be a comprehensive Lean
tutorial—for this, we recommend [Theorem Proving in Lean](../bib.md#1).
The guide is also no substitute for attending class or doing the exercises and homework.
Theorem proving is not for spectators; it can only be learned by doing.

Specifically, our goal is that you

- learn fundamental theory and techniques in interactive theorem proving;
- learn how to use logic as a precise language for modeling systems and stating properties about them;
- familiarize yourselves with some areas in which proof assistants are successfully applied, such as
  functional programming, the semantics of imperative programming languages, and mathematics;
- develop some practical skills you can apply on a larger project (as a hobby, for an MSc or PhD, or in industry);
- reach a point where you feel ready to move to another proof assistant and apply what you have learned;
- get to understand the domain well enough to start reading relevant scientific papers published at
  international conferences such as Certified Programs and Proofs (CPP) and Interactive Theorem
  Proving (ITP) or in journals such as the _Journal of Automated Reasoning_ (JAR).

Equipped with a good knowledge of Lean, you will find it easy to move to another proof assistant
based on dependent type theory, such as Agda or Coq, or to a system based on simple type theory,
such as HOL4 or Isabelle/HOL

We assume that you are familiar with typed functional programming, as embodied in the languages
Haskell, OCaml, and Standard ML. If you do not see that the term `g (f a b)` applies the (curried)
function `f` to two arguments `a` and `b` and passes the result to the function `g`, or that `λ n => n + 1` is
the function that maps `n` to `n + 1`, we strongly recommend that you start by studying a tutorial, such
as the first chapters of the online tutorial [Learn You a Haskell for Great Good!](../bib.md#22).
You can stop reading once you have reached the end of the section titled “Lambdas.”

An important characteristic of this guide, which it shares with [Knuth’s \\(\TeX\\) book](../bib.md#17),
is that it does not always tell the truth. To simplify the exposition, simple but
false claims are made about Lean. Some of these statements are rectified in later
chapters. Like Knuth, we feel that _“this technique of deliberate lying will actually
make it easier for you to learn the ideas. Once you understand a simple but false
rule, it will not be hard to supplement that rule with its exceptions.”_

The Lean files accompanying this guide can be found in the [public repository](https://github.com/leanprover/HitchikersGuide).
The files’ naming scheme follows this guide’s chapters; thus, `06_monads_demo`.
lean is the main file associated with Chapter 6 (“Monads”), which is demonstrated
in class, `06_monads_exercise_sheet.lean` is the exercise sheet, and `06_monads_homework_sheet.lean`
is the homework sheet.

We have a huge debt to the authors of [Theorem Proving in Lean](../bib.md#1)
and [Concrete Semantics: With Isabelle/HOL](../bib.md#27),
who have taught us Lean and programming language semantics. Many of their ideas appear in this guide.

We thank Robert Lewis and Assia Mahboubi for their useful comments on this guide’s organization and
focus. We thank Kiran Gopinathan and Ilya Sergey for sharing the anecdote reported in footnote 3 of
Chapter 1 and letting us share it further. We thank Daniel Fabian for designing the first
tablet-optimized version of this guide. Finally, we thank Chris Bailey, Kevin Buzzard, Wan Fokkink,
Robert Lewis, Antonius Danny Reyes, Robert Schütz, Patrick Thomas, Huub Vromen, and Wijnand van
Woerkom for reporting typos and some more serious errors they found in earlier editions of this
guide. Should you find some mistakes in this text, please let us know.

**Special Symbols** In this guide, we assume that you will be using [Visual Studio
Code](https://code.visualstudio.com/Download) and its [Lean 4
extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4) to edit .lean
files. Visual Studio Code lets us enter Unicode symbols by entering backslash \ followed by an ASCII
identifier. For example, →, λ, or ∀  can be entered by typing `\r`, `\la`, or `\all` and pressing the tab key
or the space bar. We will freely use these notations. For reference, we provide a list of the main
non-ASCII symbols that are used in the guide and, for each, one of its ASCII representations. By
hovering over a symbol in Visual Studio Code while holding the control or command key pressed, you
will see the different ways in which it can be entered.

| symbol | abbreviation | symbol | abbreviation | symbol | abbreviation |
|--------|--------------|--------|--------------|--------|--------------|
| ¬      |  \not        | ∧      | \and         | ∨      | \or          |
| →      |  \r          | ←      | \l           | ↔      | \lr          |
| ∃      |  \ex         | ∀      | \fo          | ∑      | \S           |
| ≤      | \\<=          | ≥      | \\>=          |  ≠     |  \neq        |
| ≈      | \\~~          | ×      | \x           | ⊕      | \oplus       |
| ◦      |  \circ       | ∅      | \em          | ∪      |  \union      |
| ∩      |  \intersect  | ∈      | \in          |  ⇃ | \downleftharpoon  |
| ◯     | \bigcirc     | ↦      | \mapsto      | ⇒      |  \\=>        |
| ⟹     | \\==>         | ⟦      | \\[[          |  ⟧      |  \\]]        |
| ℕ      | \N           | ℤ      | \Z           | ℚ     |  \Q          |
| ℝ      | \R           | α      | \a           | β      |  \b          |
| γ       | \g          | δ      | \de          | ε      |  \e          |
|  λ     | \la          |  σ     | \s           | ₀      |  \0          |
|  ₁     | \1           | ₂      | \2           | ₃      |  \3          |
| ₄      | \4           | ₅      | \5           | ₆      |  \6          |
| ₇      | \7           | ₈      | \8           | ₉      |  \9          |
