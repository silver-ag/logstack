# LogStack

LogStack is a stack-based logic language. Each item on the stack is a valid sentence of propositional logic, and all conditionals work by popping one and testing whether it can be proven using the rest of the stack as assumptions.

## Instructions

| Instruction | Effect                                                                  |
|-------------|-------------------------------------------------------------------------|
| `a-zA-Z`      | push an atomic proposition corresponding to the letter                  |
| `*`           | push a contradiction                                                    |
| `%`           | push a tautology                                                        |
| `&`           | pop two propositions p and q, and push a compound proposition 'p and q' |
| `\|`          | pop two propositions p and q, and push a compound proposition 'p or q'  |
| `!`           | pop a proposition and push its negation                                 |
| `^`           | pop two propositions p and q and push 'p xor q'. This is syntactic sugar, under the hood it's all in terms of and, or and not |
| `:`           | pop two propositions p and q and push 'q implies p' (in that order, so "ab:" pushes a=>b) |
| `=`           | pop two propositions p and q and push 'p if and only if q' (biconditional) |
| `/`           | swap the top two items on the stack |
| `;`           | duplicate the top item on the stack |
| `$`           | pop and discard |
| `@`           | rotate the stack - pop an proposition and place it on the bottom of the stack |
| `~`           | pop a proposition and try to prove it using the rest of the stack. If it is provable, swap the top two items (not replacing the proposition popped for testing) |
| `?`           | pop a proposition and try to prove it. output the result ('yes' or 'no'). |
| `()`          | loop - before each iteration, pop a proposition and try to prove it. If it's not provable, end the loop immediately. |
| `.`           | halt the program |
| `#`           | output the state of the stack, mostly for debugging purposes |

All other characters are nops.

## Use

As it turns out, the logic part isn't that much use. A subset of the language consisting only of three atomic propositions, `%`, `/`, `$`, `@` and `()` is turing complete. However, there are a couple of useful things to remember:
- The difference between false and unprovable matters. `p?` on a stack that makes no mention of `p` outputs 'no'.
- The principle of explosion applies. If the stack implies a contradiction, all propositions are provable. This breaks the constructions below if it happens.
- the construction `%/( [if true] ab)( [if false] ab)$` acts as an if-else statement
- the construction `*( [comment] )` allows comments

## Input

In principle, input is taken as the initial state of the stack. No facility for setting it from outside the start of the program text is provided, however.

## Example

The following is a truth machine - a program which outputs an infinite stream of truthy values if its input is truthy, or outputs a single falsy value and halts oherwise.
Truthy input for this program consists of a starting stack containing a single 'p', falsy input is an empty starting stack.

```
p        *(push (another?) 'p')
(        *(pop something, initially the 'p' we just pushed, and try to prove it. If it's not provable, skip past the matching ')')
 pp?)    *(push two 'p's, then pop one of them and output whether or not it's provable - always yes. Then go back to the '(')
a?       *(push 'a' and output whether it's provable - always no, since it's not mentioned anywhere in the stack)
```
## Errors

A runtime error occurs if an attempt is made to pop from an empty stack or if an `(` with no matching `)` is encountered. There is currently no error handling, so the interpreter just crashes.
