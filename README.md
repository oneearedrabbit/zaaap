Zaaap -- A Schema-like language purely based Lambda Calculus
---

Lambda calculus is a formal system in mathematical logic for
expressing computation based on function abstraction and application
using variable binding and substitution. It is a universal model of
computation that can be used to simulate any Turing machine. It was
introduced by the mathematician Alonzo Church in the 1930s as part of
his research into the foundations of mathematics.

Zaaap implements a schema-like language based on Lambda notation and
creates a minimalistic stdlib to explore what could be done based on
three basic rules: 1) define a variable 2) define a function, and 3)
apply a function to an argument.

For pureness Zaaap's lambda functions take one and only one argument.
It could be simplified in the parser to unfold a lambda function with
multiple arguments to two or more lambdas.

As an example, here's a quicksort lambda function. All functions are
also lambda functions, which you can explore in `./examples/church.scm`:

```
(define quicksort
  (lambda (l)
    ((Z (lambda (rec)
          (lambda (l)
            ((lambda (piv)
               (((if (zerop piv))
                 l)
                ((lambda (parts)
                   ((append (rec (car parts)))
                    (rec (cdr parts))))
                 ((((partition piv) l) nil) nil))))
             (pivot l))))) l)))
```

Install
===

```
$ bundle
```

Run
===

```
$ ./bin/zaaap <filename>
```

Examples
===

- `examples/church.scm` - basic primitives like boolean logic, Church
  numbers, rational numbers, iterators, etc
- `examples/quicksort.scm` - Quick sort implementation
- `examples/fizzbuzz.scm` - Recurse-like flavour of a FizzBuzz problem
