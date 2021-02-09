; Functions are "first class citizens" (Cristopher Strachey, mid-1960s).

; DISCLAIMER: THE DRAFT BELOW IS NOT INTENDED TO BE THE PURE LAMBDA CALCULUS;
; FOR EXAMPLE, THERE ARE METHODS LIKE define AND display. NEVERTHELESS,
; HAVING ENOUGH PASSION IT'S QUITE EASY TO TRANSFORM THEM TO THE PURE FORM.
; JUST TAKE THEM AS A SORT OF APPLIED CALCULUS.

;-------------------------
; (Very) Basic I/O
(define newline
  (lambda ()
    (display "\n"))) ; display is a predefined function in my
                     ; self-written parser

;-------------------------
; Basic Combinator
; identity
(define identity
  (lambda (x) x))

; Y- and Z- combinators will be defined later

;-------------------------
; Boolean Logic
(define true
  (lambda (x)
    (lambda (y) x)))
(define false
  (lambda (x)
    (lambda (y) y)))

; Reduction of (and p q) gives true if and only if both p and q are
; equals to true, otherwise it results into false.
(define and
  (lambda (p)
    (lambda (q)
      ((p q) false))))

(define or
  (lambda (p)
    (lambda (q)
      ((p true) q))))
(define not
  (lambda (p)
    ((p false) true)))
(define xor
  (lambda (p)
    (lambda (q)
      ((p ((q false) true)) q))))
(define equal
  (lambda (p)
    (lambda (q)
      (not ((xor p) q)))))

(dispb ((equal true) false)) ; => false
(newline)
(dispb (not ((xor false) true))) ; => false
(newline)

; if selector
(define if
  (lambda (p)
    (lambda (x)
      (lambda (y)
        ((p x) y)))))

;-------------------------
; Basic unit-test
(define assert-equal
  (lambda (x)
    (lambda (y)
      (((if ((equal x) y))
        (display "OK"))
       (display "Fail!"))
      (newline))))

(dispb (((if true) false) true)) ; => false
(newline)
(dispb (((if false) false) true)) ; => true
(newline)

;-------------------------
; Basic arithmetics with natural numbers

(define zero
  (lambda (f)
    (lambda (x) x)))

; N.B. zero is false just like in many languages!

(define one
  (lambda (f)
    (lambda (x)
      (f x))))

(dispn one) ; => 1
(newline)

; Zero checking

; A numeral c is represented by a function that applies any function
; to its argument exactly n times.

; Zero predicate: say we have a function (and false), so zero
; applications of it to an argument true returns true, however if we
; apply it one or more times to the true argument, it will return false.
(define zerop
  (lambda (n)
    ((n (lambda (x) false)) true)))

(dispb (zerop zero)) ; => true
(newline)
(dispb (zerop false)) ; => true
(newline)
(dispb (zerop one)) ; => false
(newline)

(define two
  (lambda (f)
    (lambda (x)
      (f (f x)))))

(dispn two) ; => 2
(newline)

(define succ
  (lambda (c)
    (lambda (x)
      (lambda (y)
        (x ((c x) y))))))

(define three (succ two))
(define four (succ three))

; (expand three)

(dispn four) ; => 4
(newline)

(define add
  (lambda (m)
    (lambda (n)
      (lambda (f)
        (lambda (x)
          ((m f) ((n f) x)))))))

(define five ((add two) three))

(dispn five) ; => 5
(newline)
(dispn ((add two) four)) ; => 6
(newline)

; "add" can be thought of as a function taking two natural
; numbers as arguments and returning a natural number;
; since adding m to a number n can be accomplished by adding 1 m times
(define add-alt
  (lambda (m)
    (lambda (n)
      ((m succ) n))))

(dispn ((add-alt two) four)) ; => 6
(newline)

(define mul
  (lambda (c)
    (lambda (d)
      (lambda (f)
        (c (d f))))))

(dispn ((mul two) five)) ; => 10
(newline)
(dispn ((mul zero) four)) ; => 0
(newline)

; since multiplying m and n is the same as repeating
; the add n function m times and then applying it to zero.
(define mul-alt
  (lambda (m)
    (lambda (n)
      ((m (add n)) zero))))

(dispn ((mul-alt two) five)) ; => 10
(newline)

; rather ugly definition of prev predicate, however a classic one, a
; bit later we'll define way must elegant predicate
(define pred
  (lambda (n)
    (lambda (f)
      (lambda (x)
        (((n (lambda (g)
               (lambda (h)
                 (h (g f)))))
          (lambda (u) x))
         (lambda (u) u))))))

(dispn (pred five)) ; => 4
(newline)

; having true and false definitions we can simplify prev predicate
; by using if-then-else expression. however it still looks ugly.
; we'll define a good one soon.
(define pred-alt
  (lambda (n)
    (((n
       (lambda (g)
         (lambda (k)
           (((zerop (g one))
             k)
            ((add (g k)) one)))))
      (lambda (v) zero))
     zero)))

(dispn (pred-alt five)) ; => 4
(newline)

; subtraction works in a trivial way: subtract 1 from m number n times
(define sub
  (lambda (m)
    (lambda (n)
      ((n pred) m))))

(dispn ((sub five) three)) ; => 2
(newline)

; poor man Y-combinator, call by value
(define Z
  (lambda (f)
    ((lambda (g)
       (f (lambda (x) ((g g) x))))
     (lambda (g)
       (f (lambda (x) ((g g) x)))))))

; TODO: (Y I) and (Z I)

; the real Y-combinator, call by name. Just as an example -- it won't
; work here, due to parser limitations (yeah, it's call-by-value
; parser)
(define Y
  (lambda (g)
    (lambda (x) (g (x x)))
    (lambda (x) (g (x x)))))

; we are getting close to lisp like labmdas
(define gt
  (lambda (x)
    (lambda (y)
      (((Z (lambda (rec)
             (lambda (x)
               (lambda (y)
                 (((if (zerop x))
                   false)
                  (((if (zerop y))
                    true)
                   ((rec (pred x)) (pred y)))))))) x) y))))

(dispb ((gt five) three)) ; => true
(newline)
(dispb ((gt two) four)) ; => false
(newline)

; TODO: I would like to call this function "<", but my parser sucks
(define lt
  (lambda (x)
    (lambda (y)
      (((Z (lambda (rec)
             (lambda (x)
               (lambda (y)
                 (((if (zerop y))
                   false)
                  (((if (zerop x))
                    true)
                   ((rec (pred x)) (pred y)))))))) x) y))))

(dispb ((lt five) three)) ; => false
(newline)
(dispb ((lt two) four)) ; => true
(newline)
(dispb ((lt two) two)) ; => false
(newline)

(define lte
  (lambda (x)
    (lambda (y)
      (zerop
       ((sub x) y)))))
; TODO: using the same method I can declare gt, gte, etc

(dispb ((lte four) two)) ; => false
(newline)
(dispb ((lte four) four)) ; => true
(newline)
(dispb ((lte four) five)) ; => true
(newline)

; actually, greater than must be defined as follow, since we've
; specially defined pred function in a way x-y=0, if y greater than x
(define gt-alt
  (lambda (x)
    (lambda (y)
      (not ((lte x) y)))))

(dispb ((gt-alt two) five)) ; => false
(newline)
(dispb ((gt-alt four) two)) ; => true
(newline)

(define eq
  (lambda (x)
    (lambda (y)
      (((Z (lambda (rec)
             (lambda (x)
               (lambda (y)
                 (((if (zerop x))
                   (((if (zerop y))
                     true)
                    false))
                  ((rec (pred x)) (pred y))))))) y) x))))

(dispb ((eq two) two)) ; => true
(newline)
(dispb ((eq five) two)) ; => false
(newline)

;-------------------------
; Basic unit-test
(define assert_eq
  (lambda (x)
    (lambda (y)
      (((if ((eq x) y))
        (display "OK"))
       (display "Fail!"))
      (newline))))

; Euclidean algorithm and GCD
(define modulo
  (lambda (i)
    (lambda (j)
      (((Z (lambda (rec)
             (lambda (i)
               (lambda (j)
                 (((if ((lt i) j))
                   i)
                  ((rec ((sub i) j)) j)))))) i) j))))

(define six (succ five))

(dispn ((modulo six) four)) ; => 2
(newline)

(dispn ((modulo four) six)) ; => 4
(newline)

(dispn ((modulo four) four)) ; => 0
(newline)

(define gcd
  (lambda (i)
    (lambda (j)
      (((Z (lambda (rec)
             (lambda (i)
               (lambda (j)
                 (((if (zerop j))
                   i)
                  ((gcd j) ((modulo i) j))))))) i) j))))

(dispn ((gcd four) six)) ; => 2
(newline)

;; Division — DIV a b evaluates to a pair of two numbers, a idiv b and a mod b:
;; DIV := Y (λgqab. LT a b (PAIR q a) (g (SUCC q) (SUB a b) b)) 0
;; Integer division:
;; IDIV := λab. CAR (DIV a b)
;; Modulus:
;; MOD := λab. CDR (DIV a b)
;; Exponentiation (EXP a b ≡ ab):
;; EXP := λab. b a ≡ C I

; TODO: prime numbers example from SICP, primep
; TODO: define oddp
; TODO: define evenp

;-------------------------
; Self-application and recursion
(define U
  (lambda (f)
    (f f)))

(define fact-nr
  (lambda (f)
    (lambda (n)
      (((if (zerop n))
        one)
       ((mul n) ((f f) (pred n)))))))

(dispn ((U fact-nr) four)) ; => 24
(newline)

; TODO: define SKI basis
;; K := λxy. x ≡ X (X (X X)) ≡ X′ X′ X′
;; S := λxyz. (x z) (y z) ≡ X (X (X (X X))) ≡ X K ≡ X′ (X′ X′) ≡ B (B (B W) C) (B B)
;; I := λx. x ≡ S K S ≡ S K K ≡ X X
;; X := λx. x S K — also called ι (iota)
;; X′ := λx. x K S K
;; B := λxyz. x (y z) ≡ S (K S) K
;; C := λxyz. x z y ≡ S (S (K (S (K S) K)) S) (K K)
;; W := λxy. x y y ≡ S S (K (S K K))
;; Y := λg. (λx. g (x x)) (λx. g (x x)) ≡ S (K (S I I)) (S (S (K S) K) (K (S I I)))
;; Y′ := (λxy. x y x) (λyx. y (x y x)) ≡ S S K (S (K (S S (S (S S K)))) K)
;; Θ := (λxy. y (x x y)) (λxy. y (x x y)) — called the "Turing fixed-point combinator"
;; ω := λx. x x ≡ S I I
;; Ω := ω ω
;; Ω2 := (λx. x x x) (λx. x x x)
;; A fixed point combinator is any function F for which F g ≡ g (F g) for all g; examples are Y, Y′, and Θ. Since lambda calculus functions cannot refer to themselves by name, fixed point combinators are needed to implement recursion. For example, the factorial function can be implemented using f := λgx. ISZERO x 1 (MULT x (g (PRED x))), which takes a function g and a number x; if x is not zero, it is multiplied by the result of g (PRED x). Defining FACTORIAL := Y f (or Y′ f or Θ f) means that FACTORIAL x ≡ Y f x ≡ f (Y f) x, and so f is able to recurse on itself indefinitely.


(define fact
  (lambda (n)
    ((Z (lambda (rec)
           (lambda (x)
             (((if (zerop x))
               one)
              ((mul x) (rec (pred x))))))) n)))

(dispn (fact four)) ; => 24
(newline)

(define fact-iter1 ; that's an interesting function, for example, we
                   ; can speedup this function a little by using succ
                   ; method instead of (pred counter)
  (lambda (product)
    (lambda (counter)
      (((Z (lambda (rec)
             (lambda (product)
               (lambda (counter)
                 (((if (zerop counter))
                   product)
                  ((fact-iter1 ((mul counter) product))
                   (pred counter))))))) product) counter))))

; factorial iterative
(define fact-iter
  (lambda (n)
    ((fact-iter1 one) n)))

(dispn (fact-iter four)) ; => 24
(newline)

(define fib
  (lambda (x)
    ((Z (lambda (rec)
          (lambda (x)
            (((if ((lt x) three))
              x)
             ((add (rec (pred x))) (pred (pred x))))))) x)))

(dispn (fib five)) ; => 8
(newline)

; fib iterative to test tail recursion
(define fib-iter1
  (lambda (a)
    (lambda (b)
      (lambda (count)
        ((((Z (lambda (rec)
                (lambda (a)
                  (lambda (b)
                    (lambda (count)
                      (((if ((eq count) zero))
                        b)
                       (((rec ((add a) b)) a) (pred count)))))))) a) b) count)))))

(define fib-iter
  (lambda (n)
    (((fib-iter1 one) one) n)))

(dispn (fib-iter five)) ; => 8
(newline)

;-------------------------
; Ordered Pairs
(define cons
  (lambda (p)
    (lambda (q)
      (lambda (fn)
        ((fn p) q)))))
(define car
  (lambda (p)
    (p true)))
(define cdr
  (lambda (p)
    (p false)))

(dispb (car ((cons false) true))) ; => false
(newline)

; finally, we can define a better predcessor function. the basic idea is
; to use pair (x, y), where second element is an incremented first
; element: (n-1, n), or (n, n+1)
(define F
  (lambda (x)
    ((cons
      (cdr x))
     (succ (cdr x)))))
(define pred-p
  (lambda (n)
    (car
     ((n F) ((cons zero) zero)))))

;-------------------------
; Lists
(define nil
  (lambda (x)
    true))

(define null
  (lambda (p)
    (p (lambda (x)
         (lambda (y)
           false)))))

(dispb (null ((cons one) two))) ; => false
(newline)
(dispb (null nil)) ; => true
(newline)

(define append
  (lambda (x)
    (lambda (y)
      (((Z (lambda (rec)
             (lambda (x)
               (lambda (y)
                 (((if (null x))
                   y)
                  ((cons (car x)) ((rec (cdr x)) y))))))) x) y))))

; TODO: append with recursion and inf number of params

;; GET n i a0 a1 ... an-1 =β ai:
;; GET := λni. i K (SUB n (SUCC i) K)

(dispn (car
        (cdr
         (cdr
          (cdr ; TODO: define nth function
           ((append
             ((cons three) ((cons four) ((cons five) nil))))
            ((cons two) ((cons one) nil))))))))
; (cadddr (append '(3 4 5) '(2 1))) => 2
(newline)

(dispn (car
        (cdr
         (cdr
          (cdr
           ((append
             ((cons one)
              ((cons two)
               ((cons three) nil))))
            ((cons four)
             ((cons five) nil))))))))
; (cadddr (append '(1 2 3) '(4 5))) => 4
(newline)

; tail recursive function
(define length
  (lambda (x)
    (((Z (lambda (rec)
            (lambda (x)
              (lambda (acc)
                (((if (null x))
                  acc)
                 ((rec (cdr x)) (succ acc))))))) x) zero)))

(dispn (length
        ((append
          ((cons two) ((cons three) ((cons four) nil))))
         ((cons one) nil)))) ; => 4
(newline)

; TODO: missing implementation of
; depth
; define zip
; define merge

;; INDEX x i — evaluates to the i-th (zero-based) element of list x, assuming that x has at least i + 1 elements:
;; INDEX := λxi. CAR (i CDR x)
;; Get the last element in a list:
;; LAST := Y (λgx. NULL x NIL (NULL (CDR x) (CAR x) (g (CDR x))))
;; Get a list without its last element:
;; TRUNCATE := Y (λgx. NULL x NIL (NULL (CDR x) NIL (PAIR (CAR x) (g (CDR x)))))
;; Reverse a list:
;; REVERSE := Y (λgal. NULL l a (g (PAIR (CAR l) a) (CDR l))) NIL
;; RANGE s e — evaluates to a list of all natural numbers from s up through e, or to NIL when s > e.
;; RANGE := λse. Y (λgc. LEQ c e (PAIR c (g (SUCC c) e)) NIL) s
;; LIST n a0 a1 ... an-1 — evaluates to a0 ... an-1 as a list
;; LIST := λn. n (λfax. f (PAIR x a)) REVERSE NIL

;-------------------------
; Rational numbers
(define make-rat
  (lambda (n)
    (lambda (d)
      ((cons n) d))))

(define numer
  (lambda (x)
    (car x)))
(define denom
  (lambda (x)
    (cdr x)))

(define add-rat
  (lambda (x)
    (lambda (y)
      ((make-rat ((add ((mul (numer x)) (denom y)))
                  ((mul (numer y)) (denom x))))
       ((mul (denom x)) (denom y))))))

(define sub-rat
  (lambda (x)
    (lambda (y)
      ((make-rat ((sub ((mul (numer x)) (denom y)))
                  ((mul (numer y)) (denom x))))
       ((mul (denom x)) (denom y))))))

(define mul-rat
  (lambda (x)
    (lambda (y)
      ((make-rat ((mul (numer x)) (numer y)))
       ((mul (denom x)) (denom y))))))

(define div-rat
  (lambda (x)
    (lambda (y)
      ((make-rat ((mul (numer x)) (denom y)))
       ((mul (denom x)) (numer y))))))

(define equal-rat
  (lambda (x)
    (lambda (y)
      ((eq ((mul (numer x)) (denom y)))
       ((mul (numer y)) (denom x))))))

(define disp-rat
  (lambda (x)
    (dispn (numer x))
    (display "/")
    (dispn (denom x))
    (newline)))

(disp-rat ((make-rat one) two)) ; => 1/2
(disp-rat ((add-rat ((make-rat one) two))
        ((make-rat three) four))) ; => 5/4

; TODO: assert-equal-rat

;-------------------------
; Syntax macros
;; (define-syntax and2
;;   (lambda (x)
;;     (syntax-case x ()
;;       ((_ x y)
;;        (syntax (if x y #f))))))
; http://www.xs4all.nl/~hipster/lib/scheme/gauche/define-syntax-primer.txt
; http://groups.google.com/group/comp.lang.lisp/msg/7893ba79443a82f8?hl=en&

; TODO: strings as lists?

;-------------------------
; Higher-order functions
(define map
  (lambda (f)
    (lambda (l)
      (((Z (lambda (rec)
             (lambda (f)
               (lambda (l)
                 (((if (null l))
                   nil)
                  ((cons (f (car l)))
                   ((rec f) (cdr l)))))))) f) l))))

;; (define each
;;   (lambda (f)
;;     (lambda (l)
;;       (((Z (lambda (rec)
;;              (lambda (f)
;;                (lambda (l)
;;                  (((if (null l))
;;                    nil)
;;                   ((lambda ()
;;                      (f (car l)) ; Q: is it allowed at all to have
;;                                   ; concurent calls?
;;                      ((rec f) (cdr l))))))))) f) l))))

;; (define (for-each1 proc lis)
;;    (cond ((null? (cdr lis))  ; one-element list?
;;           (proc (car lis)))
;;          (else
;;           (proc (car lis))
;;           (for-each1 proc (cdr lis)))))

;; APPLY := Y (λgfx. NULL x f (g (f (CAR x)) (CDR x)))
(define each
  (lambda (f)
    (lambda (l)
      (((Z (lambda (rec)
             (lambda (f)
               (lambda (l)
                 (((if (null l))
                   f)
                  ((lambda ()
                     (f (car l))
                     ((rec f) (cdr l))))))))) f) l))))

(define displ
  (lambda (x)
    (display "[ ")
    ((each
      (lambda (x)
        (dispn x)
        (display " ")))
     x)
    (display "]")))

(displ ((cons two) ((cons three) ((cons four) nil)))) ; => 2 3 4
(newline)

(displ ((map
         (lambda (x) (succ x)))
        ((cons two) ((cons three) ((cons four) nil))))) ; => 3 4 5
(newline)

;; (define-syntax let
;;   (syntax-rules ()
;;     ((let ((x v) ...) e ...)
;;      ((lambda (x ...) e ...) v ...))))

(define filter
  (lambda (p)
    (lambda (l)
      (((Z (lambda (rec)
             (lambda (p)
               (lambda (l)
                 (((if (null l))
                   nil)
                  (((if (p (car l)))
                    ((cons (car l)) ((rec p) (cdr l)))) ; TODO: let syntax
                   ((rec p) (cdr l)))))))) p) l))))

(displ
 ((filter
    (lambda (x)
      ((lte x) two)))
  ((cons one) ((cons two) ((cons three) ((cons four) nil)))))) ; => 1 2
(newline)

; locate ; http://www.aplusplus.net/bookonl/node191.html
; remove
; insert
; sum
; nth
; while ; http://www.aplusplus.net/bookonl/node194.html

;; (define nth (lambda (l n)
;;   (if (null? l) '()
;;     (if (< n 1) (car l)   ; note this is an "else if" expression
;;       (nth (cdr l) (- n 1))))))

; http://jonathan.tang.name/files/scheme_in_48/tutorial/stdlib.html
; Our Scheme is almost complete now, but it's still rather hard to
; use. At the very least, we'd like a library of standard
; list-manipulation functions that we can use to perform some common
; computations.

; Rather than using a typical Scheme implementation, defining each
; list function in terms of a recursion on lists, we'll implement two
; primitive recursion operators (fold and unfold) and then define our
; whole library based on those. This style is used by the Haskell
; Prelude (http://www.haskell.org/onlinereport/standard-prelude.html):
; it gives you more concise definitions, less room for
; error, and good practice using fold to capture iteration.

(define foldr
  (lambda (func)
    (lambda (end)
      (lambda (lst)
        ((((Z (lambda (rec)
                (lambda (func)
                  (lambda (end)
                    (lambda (lst)
                      (((if (null lst))
                        end)
                       ((func (car lst)) (((rec func) end) (cdr lst)))))))))
           func) end) lst)))))

(define foldl
  (lambda (func)
    (lambda (accum)
      (lambda (lst)
        ((((Z (lambda (rec)
                (lambda (func)
                  (lambda (accum)
                    (lambda (lst)
                      (((if (null lst))
                        accum)
                       (((rec func) ((func accum) (car lst))) (cdr lst))))))))
           func) accum) lst)))))

; aliases
; (define fold foldl)
; (define reduce fold)

; TODO: define unfold
;; (define (unfold func init pred)
;;   (if (pred init)
;;       (cons init '())
;;       (cons init (unfold func (func init) pred))))


; In academic functional programming literature, folds are often
; called catamorphisms, unfolds are often called anamorphisms, and
; the combinations of the two are often called hylomorphisms. They're
; interesting because any for-each loop can be represented as a
; catamorphism. To convert from a loop to a foldl, package up all
; mutable variables in the loop into a data structure (records work
; well for this, but you can also use an algebraic data type or a
; list). The initial state becomes the accumulator; the loop body
; becomes a function with the loop variables as its first argument
; and the iteration variable as its second; and the list becomes,
; well, the list. The result of the fold function is the new state of
; all the mutable variables.

; Similarly, every for-loop (without early exits) can be represented
; as a hylomorphism. The initialization, termination, and step
; conditions of a for-loop define an anamorphism that builds up a
; list of values for the iteration variable to take. Then, you can
; treat that as a for-each loop and use a catamorphism to break it
; down into whatever state you wish to modify.

; TODO: upgraded core functions w/ fold
;; (define (and . lst)         (fold && #t lst))
;; (define (or . lst)          (fold || #f lst))

(define sum
  (lambda (l)
    (((foldl add) zero) l)))

(dispn
 (sum ((cons four) ((cons two) ((cons three) ((cons one) nil)))))) ; => 10
(newline)

(define product
  (lambda (l)
    (((foldl mul) one) l)))

(dispn
 (product ((cons four) ((cons two) ((cons three) ((cons one) nil)))))) ; => 24
(newline)

(define reverse-alt
  (lambda (l)
    (((foldr cons) nil) l))) ; XXX: foldr?

(displ
 (reverse-alt
  ((cons four) ((cons two) ((cons three) ((cons one) nil)))))) ; => 1 3 2 4
(newline)

;; APPEND = -> k { -> l { FOLDR[CONS][l][k] } }
;; PUSH = -> x { -> l { APPEND[l][CONS[x][NIL]] } }


; It's not immediately obvious what operation to fold over the list,
; because none of the built-ins quite qualify. Instead, think back to
; fold as a representation of a foreach loop. The accumulator
; represents any state we've maintained over previous iterations of
; the loop, so we'll want it to be the maximum value we've found so
; far. That gives us our initialization value: we want to start off
; with the leftmost variable in the list (since we're doing a
; foldl). Now recall that the result of the operation becomes the new
; accumulator at each step, and we've got our function. If the
; previous value is greater, keep it. If the new value is greater, or
; they're equal, return the new value. Reverse the operation for min.

; TODO: define max, min, length, reverse w/ fold
;; (define (max first . num-list) (fold (lambda (old new) (if (> old new) old new)) first num-list))
;; (define (min first . num-list) (fold (lambda (old new) (if (< old new) old new)) first num-list))
;; (define (length lst)        (fold (lambda (x y) (+ x 1)) 0 lst))
;; (define (reverse lst)       (fold (flip cons) '() lst))


; Next, let's define the functions map and filter. Map applies a
; function to every element of a list, returning a new list with the
; transformed values:

; TODO: define map and filter w/ fold
;; (define (map func lst)      (foldr (lambda (x y) (cons (func x) y)) '() lst))
;; (define (filter pred lst)   (foldr (lambda (x y) (if (pred x) (cons x y) y)) '() lst))




;-------------------------
; Quick sort
; given list '(7 3 9 6 5 3 2 7 6) -> return sorted list

; pivot function returns the pivot - first element out of order.
; returns nil if no pivot (means list already sorted)

; partition function takes pivot, list and returns a pair of lists of the
; form '((4 3 6) (8 9 7))

; given:
; (append '(1 2) '(3 4)) --> (1 2 3 4)
; (member 1 '(3 1 2)) --> #t  (or actually, the rest of the list)


(define pivot
  (lambda (l)
    (((if (null l)) ; TODO: cond function
      nil)
     (((if (null (cdr l)))
       zero) ; TODO: need to return an atom here
      (((if ((lte (car l))
             (car (cdr l))))
        (pivot (cdr l)))
       (car l))))))

(dispn
 (pivot ((cons two) ((cons three) ((cons one) ((cons four) nil)))))) ; => 3
(newline)

(define reverse
  (lambda (l)
    ((Z (lambda (rec)
          (lambda (l)
            (((if (null l))
              nil)
             ((append (rec (cdr l))) ((cons (car l)) nil)))))) l)))

; TODO: reverse tail recursion
;; REVERSE := Y (λgal. NULL l a (g (PAIR (CAR l) a) (CDR l))) NIL


(displ
 (reverse
  ((cons two) ((cons three) ((cons one) ((cons four) nil))))))
; => 4 1 3 2
(newline)

; (partition 3 '(2 3 1 4) '() '()) => '((2 1) . (3 4))
(define partition
  (lambda (piv)
    (lambda (l)
      (lambda (p1)
        (lambda (p2)
          (((if (null l))
            ((cons (reverse p1)) (reverse p2)))
           (((if ((lt (car l)) piv))
             ((((partition piv) (cdr l)) ((cons (car l)) p1)) p2))
            ((((partition piv) (cdr l)) p1) ((cons (car l)) p2)))))))))

(displ
 (car
  ((((partition three)
     ((cons two) ((cons three) ((cons one) ((cons four) nil)))))
    nil) nil))) ; => 2 1
(displ
 (cdr
  ((((partition three)
     ((cons two) ((cons three) ((cons one) ((cons four) nil)))))
    nil) nil))) ; => 3 4

(newline)

(define quicksort
  (lambda (l)
    ((Z (lambda (rec)
          (lambda (l)
            ((lambda (piv) ; TODO: let syntax
               (((if (zerop piv)) ; TODO: compare it to 'nothing atom from pivot
                                  ; function rather then to zero
                 l)
                ((lambda (parts) ; TODO: let syntax
                   ((append (rec (car parts)))
                    (rec (cdr parts))))
                 ((((partition piv) l) nil) nil))))
             (pivot l))))) l)))

(displ
 (quicksort
  ((cons three) ((cons one) ((cons two) nil)))))
; => 1 2 3
(newline)

(define quicksort-alt
  (lambda (l)
    ((Z (lambda (rec)
          (lambda (l)
            (((if (null l))
              nil)
             ((lambda (p)
                ((lambda (xs)
                   ((append
                     ((append
                       (rec ((filter (lambda (x) ((lte x) p))) xs)))
                      ((cons p) nil)))
                    (rec ((filter (lambda (x) ((gt-alt x) p))) xs)))) (cdr l))) (car l)))))) l)))

(displ
 (quicksort-alt
  ((cons three) ((cons one) ((cons two) nil)))))
; => 1 2 3
(newline)

;; (define (quicksort lst)
;;   (cond ((or (null? lst) (= (length lst) 1)) lst) ;; if the list is empty or of length 1, return the list
;;         (else
;;          (let ((r (random (length lst))))
;;            (append (quicksort (filter (lambda (x) (< x (list-ref r lst))) lst))
;;            ;;take every term of the list with a value less than that found at index r
;;                    (append (filter (lambda (x) (= x (list-index r lst))) lst)
;;                            ;;take every term of the list with a value equal to that found at index r
;;                            (quicksort (filter (lambda (x) (> x (list-index r lst))) lst))))))))
;; ;;take every term of the list with a value less than that found at index r


;-------------------------
; Negative numbers
; http://okmij.org/ftp/Computation/lambda-calc-div-neg.txt
; TODO: positivep
; TODO: negativep
; TODO: negative numbers

;-------------------------
; TODO: define sieve_of_eratosthenese
; http://www.csse.monash.edu.au/~lloyd/tildeFP/Lambda/Examples/

;-------------------------
; Trees
; TODO: trees
; http://www.csse.monash.edu.au/~lloyd/tildeFP/Lambda/Examples/tree/

;-------------------------
; Basic I/O
; TODO: I/O

;-------------------------
; REPL
; TODO: REPL

;-------------------------
; Advanced I/O: File
; TODO: I/O: File

;-------------------------
; TODO: Combinator calculus

;-------------------------
; TODO: SKI combinator calculus
; http://en.wikipedia.org/wiki/SKI_calculus

;-------------------------
; TODO: BCKW combinator calculus
; http://en.wikipedia.org/wiki/B,C,K,W_system

;-------------------------
; TODO: Iota
; http://en.wikipedia.org/wiki/Iota_and_Jot

;-------------------------
; TODO: Memoizing recursive functions
; http://matt.might.net/articles/implementation-of-recursive-fixed-point-y-combinator-in-javascript-for-memoization/

; TODO: point-free
; http://www.haskell.org/haskellwiki/Pointfree

; TODO: Scott numerals
; Scott numerals in λ-calculus
;; some common combinators
;; let K = (\x y. x)
;; let I = (\x. x)

;; ; bools
;; let true = (\x y. x)
;; let false = (\x y. y)
;; let cond = (\b t f. b t f)

;; ; numerals
;; let zero = (K)
;; let succ = (\n x y. y n)
;; let pred = (\p. p K I)

;; ; predicates
;; let isZero = (\n. n true (K false))
;; let eq = (\m n. cond (isZero m) (isZero n) (eq (pred m) (pred n)))

;; (isZero zero)
;; (isZero (succ zero))
;; (isZero (pred zero))
;; (eq (succ zero) (succ zero))
;; (eq (succ zero) (pred (succ (succ zero))))
;; (eq zero (pred zero))
;; (eq zero (pred (succ (succ zero))))
;; (eq zero (succ (zero)))
