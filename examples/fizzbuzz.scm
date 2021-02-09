;-------------------------
; (Very) Basic I/O
(define newline
  (lambda ()
    (display "\n"))) ; display is a predefined function in my
                     ; self-written parser

;-------------------------
; Boolean Logic
(define true
  (lambda (x)
    (lambda (y) x)))
(define false
  (lambda (x)
    (lambda (y) y)))
(define or
  (lambda (p)
    (lambda (q)
      ((p true) q))))
(define not
  (lambda (p)
    ((p false) true)))

; Zero predicate: say we have a function (and false), so zero
; applications of it to an argument true returns true, however if we
; apply it one or more times to the true argument, it will return false.
(define zerop
  (lambda (n)
    ((n (lambda (x) false)) true)))

(define lte
  (lambda (x)
    (lambda (y)
      (zerop
       ((sub x) y)))))

; if selector
(define if
  (lambda (p)
    (lambda (x)
      (lambda (y)
        ((p x) y)))))

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

; subtraction works in a trivial way: subtract 1 from m number n times
(define sub
  (lambda (m)
    (lambda (n)
      ((n pred) m))))

(define succ
  (lambda (c)
    (lambda (x)
      (lambda (y)
        (x ((c x) y))))))

(define add
  (lambda (m)
    (lambda (n)
      (lambda (f)
        (lambda (x)
          ((m f) ((n f) x)))))))

(define mul
  (lambda (c)
    (lambda (d)
      (lambda (f)
        (c (d f))))))

(define one
  (lambda (f)
    (lambda (x)
      (f x))))
(define two
  (lambda (f)
    (lambda (x)
      (f (f x)))))
(define three (succ two))
(define five ((add two) three))
(define ten ((mul two) five))
(define twenty ((mul ten) two))
(define hundred ((mul twenty) five))

; poor man Y-combinator, call by value
(define Z
  (lambda (f)
    ((lambda (g)
       (f (lambda (x) ((g g) x))))
     (lambda (g)
       (f (lambda (x) ((g g) x)))))))

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
; fizzbuzz
(define fizzbuzz
  (lambda (finish)
    ((Z (lambda (rec)
          (lambda (num)
            (((if ((lte num) finish))
             ((lambda ()
                ((lambda (by_three)
                   ((lambda (by_five)
                        (((if by_three) (display "Crackle")))
                        (((if by_five) (display "Pop")))
                        (((if (not ((or by_three) by_five))) (dispn num))))
                    (zerop ((modulo num) five))))
                 (zerop ((modulo num) three)))
                (newline)
                (rec (succ num)))))))))
     one)))

;; (fizzbuzz hundred)
;; (newline)

((lambda (finish) (((lambda (f) ((lambda (g) (f (lambda (x) ((g g) x)))) (lambda (g) (f (lambda (x) ((g g) x)))))) (lambda (rec) (lambda (num) ((((lambda (p) (lambda (x) (lambda (y) ((p x) y)))) (((lambda (x) (lambda (y) ((lambda (n) ((n (lambda (x) (lambda (x) (lambda (y) y)))) (lambda (x) (lambda (y) x)))) (((lambda (m) (lambda (n) ((n (lambda (n) (lambda (f) (lambda (x) (((n (lambda (g) (lambda (h) (h (g f))))) (lambda (u) x)) (lambda (u) u)))))) m))) x) y)))) num) finish)) ((lambda () ((lambda (by_three) ((lambda (by_five) ((((lambda (p) (lambda (x) (lambda (y) ((p x) y)))) by_three) (display "Crackle"))) ((((lambda (p) (lambda (x) (lambda (y) ((p x) y)))) by_five) (display "Pop"))) ((((lambda (p) (lambda (x) (lambda (y) ((p x) y)))) ((lambda (p) ((p (lambda (x) (lambda (y) y))) (lambda (x) (lambda (y) x)))) (((lambda (p) (lambda (q) ((p (lambda (x) (lambda (y) x))) q))) by_three) by_five))) (dispn num)))) ((lambda (n) ((n (lambda (x) (lambda (x) (lambda (y) y)))) (lambda (x) (lambda (y) x)))) (((lambda (i) (lambda (j) ((((lambda (f) ((lambda (g) (f (lambda (x) ((g g) x)))) (lambda (g) (f (lambda (x) ((g g) x)))))) (lambda (rec) (lambda (i) (lambda (j) ((((lambda (p) (lambda (x) (lambda (y) ((p x) y)))) (((lambda (x) (lambda (y) ((((lambda (f) ((lambda (g) (f (lambda (x) ((g g) x)))) (lambda (g) (f (lambda (x) ((g g) x)))))) (lambda (rec) (lambda (x) (lambda (y) ((((lambda (p) (lambda (x) (lambda (y) ((p x) y)))) ((lambda (n) ((n (lambda (x) (lambda (x) (lambda (y) y)))) (lambda (x) (lambda (y) x)))) y)) (lambda (x) (lambda (y) y))) ((((lambda (p) (lambda (x) (lambda (y) ((p x) y)))) ((lambda (n) ((n (lambda (x) (lambda (x) (lambda (y) y)))) (lambda (x) (lambda (y) x)))) x)) (lambda (x) (lambda (y) x))) ((rec ((lambda (n) (lambda (f) (lambda (x) (((n (lambda (g) (lambda (h) (h (g f))))) (lambda (u) x)) (lambda (u) u))))) x)) ((lambda (n) (lambda (f) (lambda (x) (((n (lambda (g) (lambda (h) (h (g f))))) (lambda (u) x)) (lambda (u) u))))) y)))))))) x) y))) i) j)) i) ((rec (((lambda (m) (lambda (n) ((n (lambda (n) (lambda (f) (lambda (x) (((n (lambda (g) (lambda (h) (h (g f))))) (lambda (u) x)) (lambda (u) u)))))) m))) i) j)) j)))))) i) j))) num) (((lambda (m) (lambda (n) (lambda (f) (lambda (x) ((m f) ((n f) x)))))) (lambda (f) (lambda (x) (f (f x))))) ((lambda (c) (lambda (x) (lambda (y) (x ((c x) y))))) (lambda (f) (lambda (x) (f (f x)))))))))) ((lambda (n) ((n (lambda (x) (lambda (x) (lambda (y) y)))) (lambda (x) (lambda (y) x)))) (((lambda (i) (lambda (j) ((((lambda (f) ((lambda (g) (f (lambda (x) ((g g) x)))) (lambda (g) (f (lambda (x) ((g g) x)))))) (lambda (rec) (lambda (i) (lambda (j) ((((lambda (p) (lambda (x) (lambda (y) ((p x) y)))) (((lambda (x) (lambda (y) ((((lambda (f) ((lambda (g) (f (lambda (x) ((g g) x)))) (lambda (g) (f (lambda (x) ((g g) x)))))) (lambda (rec) (lambda (x) (lambda (y) ((((lambda (p) (lambda (x) (lambda (y) ((p x) y)))) ((lambda (n) ((n (lambda (x) (lambda (x) (lambda (y) y)))) (lambda (x) (lambda (y) x)))) y)) (lambda (x) (lambda (y) y))) ((((lambda (p) (lambda (x) (lambda (y) ((p x) y)))) ((lambda (n) ((n (lambda (x) (lambda (x) (lambda (y) y)))) (lambda (x) (lambda (y) x)))) x)) (lambda (x) (lambda (y) x))) ((rec ((lambda (n) (lambda (f) (lambda (x) (((n (lambda (g) (lambda (h) (h (g f))))) (lambda (u) x)) (lambda (u) u))))) x)) ((lambda (n) (lambda (f) (lambda (x) (((n (lambda (g) (lambda (h) (h (g f))))) (lambda (u) x)) (lambda (u) u))))) y)))))))) x) y))) i) j)) i) ((rec (((lambda (m) (lambda (n) ((n (lambda (n) (lambda (f) (lambda (x) (((n (lambda (g) (lambda (h) (h (g f))))) (lambda (u) x)) (lambda (u) u)))))) m))) i) j)) j)))))) i) j))) num) ((lambda (c) (lambda (x) (lambda (y) (x ((c x) y))))) (lambda (f) (lambda (x) (f (f x)))))))) ((lambda () (display "\n"))) (rec ((lambda (c) (lambda (x) (lambda (y) (x ((c x) y))))) num))))))))) (lambda (f) (lambda (x) (f x))))) (((lambda (c) (lambda (d) (lambda (f) (c (d f))))) (((lambda (c) (lambda (d) (lambda (f) (c (d f))))) (((lambda (c) (lambda (d) (lambda (f) (c (d f))))) (lambda (f) (lambda (x) (f (f x))))) (((lambda (m) (lambda (n) (lambda (f) (lambda (x) ((m f) ((n f) x)))))) (lambda (f) (lambda (x) (f (f x))))) ((lambda (c) (lambda (x) (lambda (y) (x ((c x) y))))) (lambda (f) (lambda (x) (f (f x)))))))) (lambda (f) (lambda (x) (f (f x)))))) (((lambda (m) (lambda (n) (lambda (f) (lambda (x) ((m f) ((n f) x)))))) (lambda (f) (lambda (x) (f (f x))))) ((lambda (c) (lambda (x) (lambda (y) (x ((c x) y))))) (lambda (f) (lambda (x) (f (f x))))))))

