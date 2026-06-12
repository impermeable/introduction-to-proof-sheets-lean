import WaterproofGenre
import Verbose.English.All


open WaterproofGenre
open Verbose.NameLess

#doc (WaterproofGenre) "Conjunction" =>

::::multilean

Welcome to the exercise sheets for Bewijzen in de Wiskunde.
These sheets are designed to accompany the textbook Infinite Descent into Mathematics and are intended to help you learn the concepts through the use of Waterproof.

Whenever you have a question about a mathematical concept, refer to the textbook. If you have a question about how to use Waterproof, first check these sheets. If you are still unsure, ask your teacher.

Waterproof is a language developed to construct and verify mathematical proofs using a computer. You write your proofs in the input fields, and the system checks their correctness and provides feedback on any mistakes.

These sheets include examples from the textbook as well as additional original examples. Exercises and examples taken directly from the textbook are named accordingly. For instance, the example below is named `1.1.1`, which corresponds to Example 1.1.1 in the textbook.

Waterproof is designed to help you learn write mathematical proofs on paper. This means we purposefully do not include all recommended exercises from the course in Waterproof exercise sheets. Some examples are not in the book and are marked as "extra", and just meant to explain Waterproof syntax.

Below is Example 1.1.1.
In the textbook, this proof is presented step by step to show how assumptions and goals change throughout the process.
Waterproof provides an overview of the current goal on the right side of the screen, under "We need to show" line.
The goal shown will update dynamically based on the position of your cursor in the proof.

Use the example below to explore how the goal changes by clicking in the proof and moving your cursor up and down. The specific proof techniques used in this example will be explained in later sections.

```lean
Example "1.1.1"
  Given: (a b c : ℤ)
  Assume: (_ : c ∣ b) (_ : b ∣ a)
  Conclusion: c ∣ a
Proof:
  Since c ∣ b we get n such that b = c * n
  Since b ∣ a we get m such that a = b * m
  Let's prove that n * m works
  Since b = c * n and a = b * m we conclude that a = c * (n * m)
QED
```
::::

To prove conjunctions we first type `Let's first prove that [left proposition]`, after which we demonstrate that the left proposition is true using a subproof. Then we type `Let's now prove that [right proposition]`, and demonstrate that the right proposition is true using another subproof.
These subproofs begin with a bullet point, using `·` as bullet symbols.
We conclude each subproof by typing `We conclude by hypothesis`, since each of the propositions `p`, `q` and `r` is included in our assumptions.

The bullet symbol `·` can be inserted by typing `\.` and then pressing space or tab. Similarly, the `∧` symbol can be inserted by typing `\and`. You'll see more special symbols appear throughout the sheets, and each of those can be inserted using a combination that starts with `\`. To see how to write a specific symbol, open the Waterproof menu on the left, then the "Symbols" panel, and hover over a symbol.

```lean
Example "1.1.8"
  Given: (p q r : Prop)
  Assume: (_ : p) (_ : q) (_ : r)
  Conclusion: (p ∧ q) ∧ r
Proof:
  Let's first prove that p ∧ q
  · Let's first prove that p
    · We conclude by hypothesis
    Let's now prove that q
    · We conclude by hypothesis
  Let's now prove that r
  · We conclude by hypothesis
QED
```

Below is how to assume conjunctions (Strategy 1.1.10) in Waterproof.
The line `Since p ∧ q we get that p and q` uses the assumed conjunction to derive and add two new propositions, `p` and `q`, to your assumptions.
This line works not only with conjunctions, it can be used more generally to derive new propositions.
For example, `Since A1, A2 and A3 we get that B1 and B2` checks if propositions B1 and B2 follow in one step from A1, A2 and A3.

Writing `Since p and q we conclude that q ∧ p` works similarly, it derives propositions in one step.
The difference is that after `conclude that` we should write the statement we want to show, and it finishes the current goal.
Here we use this phrase instead of writing `Let's first prove that q` and then `Let's now prove that p`, since the goal follows in one step.

```lean
Example "1.1.11"
  Given: (p q : Prop)
  Assume: (_ : p ∧ q)
  Conclusion: q ∧ p
Proof:
  Since p ∧ q we get that p and q
  Since p and q we conclude that q ∧ p
QED
```

::::multilean

Use the techniques shown in these examples to finish the following exercises.

```lean
Exercise "1.1.13"
  Given: (p q r : Prop)
  Assume: (_ : (p ∧ q) ∧ r)
  Conclusion: q
Proof:
```
:::input
```lean

```
:::
```lean
QED
```
::::

::::multilean
```lean
Exercise "1.1.14"
  Given: (p q r s : Prop)
  Assume: (_ : p) (_ : q) (_ : r) (_ : s)
  Conclusion: (p ∧ q) ∧ (r ∧ s)
Proof:
```
:::input
```lean

```
:::
```lean
QED
```
::::
