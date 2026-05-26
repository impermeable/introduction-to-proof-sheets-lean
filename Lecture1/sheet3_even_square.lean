import WaterproofGenre
import Verbose.English.All
import Bewijzen.Customlib.Integers
import Bewijzen.Customlib.Reals

open WaterproofGenre
open Verbose.NameLess

#doc (WaterproofGenre) "Even and Perfect Square" =>

Below are examples of how you can show that a certain number is even or a perfect square.
Showing `n is even` is done by proving that `n = m + m` for some `m`, as shown below.
Showing `n is square` is done by proving that `n = m * m` for some `m`, as shown below.
When typing `We compute`, Waterproof will try to verify that a numerical (in)equality, `6 = 3 + 3` or `9 = 3 * 3` in our case, is correct using basic manipulations.

```lean
Example "showing_even"
  Given:
  Assume:
  Conclusion: 6 is even
Proof:
  Let's prove that 3 works: 6 = 3 + 3
  We compute
QED
```

```lean
Example "showing_perfect_square"
  Given:
  Assume:
  Conclusion: 9 is square
Proof:
  Let's prove that 3 works
  We compute
QED
```

Using these examples, we can prove Example 1.1.22 from the book, as shown below.

```lean
Example "1.1.22"
  Given: (n : ℤ)
  Assume: (_ : n = 1 ∨ n = 2)
  Conclusion: n is even ∨ n is square
Proof:
  We discuss depending on whether n = 1 or n = 2
  · Assume that n = 1
    Let's prove that n is square
    · Let's prove that 1 works
      Since n = 1 we conclude that n = 1 * 1
  · Assume that n = 2
    Let's prove that n is even
    · Let's prove that 1 works
      Since n = 2 we conclude that n = 1 + 1
QED
```

Now do the following exercise to practice proving that a number is even or a perfect square.

::::multilean
```lean
Exercise "1.1.23"
  Given: (n : ℤ)
  Assume: (_ : n = 8 ∨ n = 9)
  Conclusion: n is even ∨ n is square
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
