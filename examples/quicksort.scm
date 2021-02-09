;; This buffer is for notes you don't want to save, and for Lisp evaluation.
;; If you want to create a file, visit that file with C-x C-f,
;; then enter the text in that file's own buffer.

; === CORE ===
(define nil
  (lambda (x)
    true))

(define Z
  (lambda (f)
    ((lambda (g)
       (f (lambda (x) ((g g) x))))
     (lambda (g)
       (f (lambda (x) ((g g) x)))))))

(define if
  (lambda (p)
    (lambda (x)
      (lambda (y)
        ((p x) y)))))

(define true
  (lambda (x)
    (lambda (y) x)))

(define false
  (lambda (x)
    (lambda (y) y)))

(define car
  (lambda (p)
    (p true)))

(define cdr
  (lambda (p)
    (p false)))

(define null
  (lambda (p)
    (p (lambda (x)
         (lambda (y)
           false)))))

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

; QUICKSORT

(define quicksort
  (lambda (l) (((lambda (f) ((lambda (g) (f (lambda (x) ((g g) x)))) (lambda (g) (f (lambda (x) ((g g) x)))))) (lambda (rec) (lambda (l) ((((lambda (p) (lambda (x) (lambda (y) ((p x) y)))) ((lambda (p) (p (lambda (x) (lambda (y) (lambda (x) (lambda (y) y)))))) l)) (lambda (x) (lambda (x) (lambda (y) x)))) ((lambda (p) ((lambda (xs) (((lambda (x) (lambda (y) ((((lambda (f) ((lambda (g) (f (lambda (x) ((g g) x)))) (lambda (g) (f (lambda (x) ((g g) x)))))) (lambda (rec) (lambda (x) (lambda (y) ((((lambda (p) (lambda (x) (lambda (y) ((p x) y)))) ((lambda (p) (p (lambda (x) (lambda (y) (lambda (x) (lambda (y) y)))))) x)) y) (((lambda (p) (lambda (q) (lambda (fn) ((fn p) q)))) ((lambda (p) (p (lambda (x) (lambda (y) x)))) x)) ((rec ((lambda (p) (p (lambda (x) (lambda (y) y)))) x)) y))))))) x) y))) (((lambda (x) (lambda (y) ((((lambda (f) ((lambda (g) (f (lambda (x) ((g g) x)))) (lambda (g) (f (lambda (x) ((g g) x)))))) (lambda (rec) (lambda (x) (lambda (y) ((((lambda (p) (lambda (x) (lambda (y) ((p x) y)))) ((lambda (p) (p (lambda (x) (lambda (y) (lambda (x) (lambda (y) y)))))) x)) y) (((lambda (p) (lambda (q) (lambda (fn) ((fn p) q)))) ((lambda (p) (p (lambda (x) (lambda (y) x)))) x)) ((rec ((lambda (p) (p (lambda (x) (lambda (y) y)))) x)) y))))))) x) y))) (rec (((lambda (p) (lambda (l) ((((lambda (f) ((lambda (g) (f (lambda (x) ((g g) x)))) (lambda (g) (f (lambda (x) ((g g) x)))))) (lambda (rec) (lambda (p) (lambda (l) ((((lambda (p) (lambda (x) (lambda (y) ((p x) y)))) ((lambda (p) (p (lambda (x) (lambda (y) (lambda (x) (lambda (y) y)))))) l)) (lambda (x) (lambda (x) (lambda (y) x)))) ((((lambda (p) (lambda (x) (lambda (y) ((p x) y)))) (p ((lambda (p) (p (lambda (x) (lambda (y) x)))) l))) (((lambda (p) (lambda (q) (lambda (fn) ((fn p) q)))) ((lambda (p) (p (lambda (x) (lambda (y) x)))) l)) ((rec p) ((lambda (p) (p (lambda (x) (lambda (y) y)))) l)))) ((rec p) ((lambda (p) (p (lambda (x) (lambda (y) y)))) l)))))))) p) l))) (lambda (x) (((lambda (x) (lambda (y) ((lambda (n) ((n (lambda (x) (lambda (x) (lambda (y) y)))) (lambda (x) (lambda (y) x)))) (((lambda (m) (lambda (n) ((n (lambda (n) (lambda (f) (lambda (x) (((n (lambda (g) (lambda (h) (h (g f))))) (lambda (u) x)) (lambda (u) u)))))) m))) x) y)))) x) p))) xs))) (((lambda (p) (lambda (q) (lambda (fn) ((fn p) q)))) p) (lambda (x) (lambda (x) (lambda (y) x)))))) (rec (((lambda (p) (lambda (l) ((((lambda (f) ((lambda (g) (f (lambda (x) ((g g) x)))) (lambda (g) (f (lambda (x) ((g g) x)))))) (lambda (rec) (lambda (p) (lambda (l) ((((lambda (p) (lambda (x) (lambda (y) ((p x) y)))) ((lambda (p) (p (lambda (x) (lambda (y) (lambda (x) (lambda (y) y)))))) l)) (lambda (x) (lambda (x) (lambda (y) x)))) ((((lambda (p) (lambda (x) (lambda (y) ((p x) y)))) (p ((lambda (p) (p (lambda (x) (lambda (y) x)))) l))) (((lambda (p) (lambda (q) (lambda (fn) ((fn p) q)))) ((lambda (p) (p (lambda (x) (lambda (y) x)))) l)) ((rec p) ((lambda (p) (p (lambda (x) (lambda (y) y)))) l)))) ((rec p) ((lambda (p) (p (lambda (x) (lambda (y) y)))) l)))))))) p) l))) (lambda (x) (((lambda (x) (lambda (y) ((lambda (p) ((p (lambda (x) (lambda (y) y))) (lambda (x) (lambda (y) x)))) (((lambda (x) (lambda (y) ((lambda (n) ((n (lambda (x) (lambda (x) (lambda (y) y)))) (lambda (x) (lambda (y) x)))) (((lambda (m) (lambda (n) ((n (lambda (n) (lambda (f) (lambda (x) (((n (lambda (g) (lambda (h) (h (g f))))) (lambda (u) x)) (lambda (u) u)))))) m))) x) y)))) x) y)))) x) p))) xs)))) ((lambda (p) (p (lambda (x) (lambda (y) y)))) l))) ((lambda (p) (p (lambda (x) (lambda (y) x)))) l)))))) l)))

(define test
  (lambda () (((lambda (p) (lambda (q) (lambda (fn) ((fn p) q)))) (lambda (f) (lambda (x) (f (f (f x)))))) (((lambda (p) (lambda (q) (lambda (fn) ((fn p) q)))) (lambda (f) (lambda (x) (f x)))) (((lambda (p) (lambda (q) (lambda (fn) ((fn p) q)))) (lambda (f) (lambda (x) (f (f x))))) (lambda (x) (lambda (x) (lambda (y) x))))))))

; (displ (quicksort (test)))

(displ
 ((lambda (l) (((lambda (f) ((lambda (g) (f (lambda (x) ((g g) x)))) (lambda (g) (f (lambda (x) ((g g) x)))))) (lambda (rec) (lambda (l) ((((lambda (p) (lambda (x) (lambda (y) ((p x) y)))) ((lambda (p) (p (lambda (x) (lambda (y) (lambda (x) (lambda (y) y)))))) l)) (lambda (x) (lambda (x) (lambda (y) x)))) ((lambda (p) ((lambda (xs) (((lambda (x) (lambda (y) ((((lambda (f) ((lambda (g) (f (lambda (x) ((g g) x)))) (lambda (g) (f (lambda (x) ((g g) x)))))) (lambda (rec) (lambda (x) (lambda (y) ((((lambda (p) (lambda (x) (lambda (y) ((p x) y)))) ((lambda (p) (p (lambda (x) (lambda (y) (lambda (x) (lambda (y) y)))))) x)) y) (((lambda (p) (lambda (q) (lambda (fn) ((fn p) q)))) ((lambda (p) (p (lambda (x) (lambda (y) x)))) x)) ((rec ((lambda (p) (p (lambda (x) (lambda (y) y)))) x)) y))))))) x) y))) (((lambda (x) (lambda (y) ((((lambda (f) ((lambda (g) (f (lambda (x) ((g g) x)))) (lambda (g) (f (lambda (x) ((g g) x)))))) (lambda (rec) (lambda (x) (lambda (y) ((((lambda (p) (lambda (x) (lambda (y) ((p x) y)))) ((lambda (p) (p (lambda (x) (lambda (y) (lambda (x) (lambda (y) y)))))) x)) y) (((lambda (p) (lambda (q) (lambda (fn) ((fn p) q)))) ((lambda (p) (p (lambda (x) (lambda (y) x)))) x)) ((rec ((lambda (p) (p (lambda (x) (lambda (y) y)))) x)) y))))))) x) y))) (rec (((lambda (p) (lambda (l) ((((lambda (f) ((lambda (g) (f (lambda (x) ((g g) x)))) (lambda (g) (f (lambda (x) ((g g) x)))))) (lambda (rec) (lambda (p) (lambda (l) ((((lambda (p) (lambda (x) (lambda (y) ((p x) y)))) ((lambda (p) (p (lambda (x) (lambda (y) (lambda (x) (lambda (y) y)))))) l)) (lambda (x) (lambda (x) (lambda (y) x)))) ((((lambda (p) (lambda (x) (lambda (y) ((p x) y)))) (p ((lambda (p) (p (lambda (x) (lambda (y) x)))) l))) (((lambda (p) (lambda (q) (lambda (fn) ((fn p) q)))) ((lambda (p) (p (lambda (x) (lambda (y) x)))) l)) ((rec p) ((lambda (p) (p (lambda (x) (lambda (y) y)))) l)))) ((rec p) ((lambda (p) (p (lambda (x) (lambda (y) y)))) l)))))))) p) l))) (lambda (x) (((lambda (x) (lambda (y) ((lambda (n) ((n (lambda (x) (lambda (x) (lambda (y) y)))) (lambda (x) (lambda (y) x)))) (((lambda (m) (lambda (n) ((n (lambda (n) (lambda (f) (lambda (x) (((n (lambda (g) (lambda (h) (h (g f))))) (lambda (u) x)) (lambda (u) u)))))) m))) x) y)))) x) p))) xs))) (((lambda (p) (lambda (q) (lambda (fn) ((fn p) q)))) p) (lambda (x) (lambda (x) (lambda (y) x)))))) (rec (((lambda (p) (lambda (l) ((((lambda (f) ((lambda (g) (f (lambda (x) ((g g) x)))) (lambda (g) (f (lambda (x) ((g g) x)))))) (lambda (rec) (lambda (p) (lambda (l) ((((lambda (p) (lambda (x) (lambda (y) ((p x) y)))) ((lambda (p) (p (lambda (x) (lambda (y) (lambda (x) (lambda (y) y)))))) l)) (lambda (x) (lambda (x) (lambda (y) x)))) ((((lambda (p) (lambda (x) (lambda (y) ((p x) y)))) (p ((lambda (p) (p (lambda (x) (lambda (y) x)))) l))) (((lambda (p) (lambda (q) (lambda (fn) ((fn p) q)))) ((lambda (p) (p (lambda (x) (lambda (y) x)))) l)) ((rec p) ((lambda (p) (p (lambda (x) (lambda (y) y)))) l)))) ((rec p) ((lambda (p) (p (lambda (x) (lambda (y) y)))) l)))))))) p) l))) (lambda (x) (((lambda (x) (lambda (y) ((lambda (p) ((p (lambda (x) (lambda (y) y))) (lambda (x) (lambda (y) x)))) (((lambda (x) (lambda (y) ((lambda (n) ((n (lambda (x) (lambda (x) (lambda (y) y)))) (lambda (x) (lambda (y) x)))) (((lambda (m) (lambda (n) ((n (lambda (n) (lambda (f) (lambda (x) (((n (lambda (g) (lambda (h) (h (g f))))) (lambda (u) x)) (lambda (u) u)))))) m))) x) y)))) x) y)))) x) p))) xs)))) ((lambda (p) (p (lambda (x) (lambda (y) y)))) l))) ((lambda (p) (p (lambda (x) (lambda (y) x)))) l)))))) l))

  (((lambda (p) (lambda (q) (lambda (fn) ((fn p) q)))) (lambda (f) (lambda (x) (f (f (f x)))))) (((lambda (p) (lambda (q) (lambda (fn) ((fn p) q)))) (lambda (f) (lambda (x) (f x)))) (((lambda (p) (lambda (q) (lambda (fn) ((fn p) q)))) (lambda (f) (lambda (x) (f (f x))))) (lambda (x) (lambda (x) (lambda (y) x))))))))

;; ((L (l) (((L (f) ((L (g) (f (L (x) ((g g) x)))) (L (g) (f (L (x) ((g g) x))))))
;; (L (r) (L (l) ((((L (p) (L (x) (L (y) ((p x) y)))) ((L (p) (p (L (x) (L (y) (L
;; (x) (L (y) y)))))) l)) (L (x) (L (x) (L (y) x)))) ((L (p) ((L (s) (((L (x) (L
;; (y) ((((L (f) ((L (g) (f (L (x) ((g g) x)))) (L (g) (f (L (x) ((g g) x)))))) (L
;; (r) (L (x) (L (y) ((((L (p) (L (x) (L (y) ((p x) y)))) ((L (p) (p (L (x) (L (y)
;; (L (x) (L (y) y)))))) x)) y) (((L (p) (L (q) (L (h) ((h p) q)))) ((L (p) (p (L
;; (x) (L (y) x)))) x)) ((r ((L (p) (p (L (x) (L (y) y)))) x)) y))))))) x) y)))
;; (((L (x) (L (y) ((((L (f) ((L (g) (f (L (x) ((g g) x)))) (L (g) (f (L (x) ((g g)
;; x)))))) (L (r) (L (x) (L (y) ((((L (p) (L (x) (L (y) ((p x) y)))) ((L (p) (p (L
;; (x) (L (y) (L (x) (L (y) y)))))) x)) y) (((L (p) (L (q) (L (h) ((h p) q)))) ((L
;; (p) (p (L (x) (L (y) x)))) x)) ((r ((L (p) (p (L (x) (L (y) y)))) x)) y)))))))
;; x) y))) (r (((L (p) (L (l) ((((L (f) ((L (g) (f (L (x) ((g g) x)))) (L (g) (f (L
;; (x) ((g g) x)))))) (L (r) (L (p) (L (l) ((((L (p) (L (x) (L (y) ((p x) y)))) ((L
;; (p) (p (L (x) (L (y) (L (x) (L (y) y)))))) l)) (L (x) (L (x) (L (y) x)))) ((((L
;; (p) (L (x) (L (y) ((p x) y)))) (p ((L (p) (p (L (x) (L (y) x)))) l))) (((L (p)
;; (L (q) (L (h) ((h p) q)))) ((L (p) (p (L (x) (L (y) x)))) l)) ((r p) ((L (p) (p
;; (L (x) (L (y) y)))) l)))) ((r p) ((L (p) (p (L (x) (L (y) y)))) l)))))))) p)
;; l))) (L (x) (((L (x) (L (y) ((L (n) ((n (L (x) (L (x) (L (y) y)))) (L (x) (L (y)
;; x)))) (((L (m) (L (n) ((n (L (n) (L (f) (L (x) (((n (L (g) (L (h) (h (g f)))))
;; (L (u) x)) (L (u) u)))))) m))) x) y)))) x) p))) s))) (((L (p) (L (q) (L (h) ((h
;; p) q)))) p) (L (x) (L (x) (L (y) x)))))) (r (((L (p) (L (l) ((((L (f) ((L (g) (f
;; (L (x) ((g g) x)))) (L (g) (f (L (x) ((g g) x)))))) (L (r) (L (p) (L (l) ((((L
;; (p) (L (x) (L (y) ((p x) y)))) ((L (p) (p (L (x) (L (y) (L (x) (L (y) y))))))
;; l)) (L (x) (L (x) (L (y) x)))) ((((L (p) (L (x) (L (y) ((p x) y)))) (p ((L (p)
;; (p (L (x) (L (y) x)))) l))) (((L (p) (L (q) (L (h) ((h p) q)))) ((L (p) (p (L
;; (x) (L (y) x)))) l)) ((r p) ((L (p) (p (L (x) (L (y) y)))) l)))) ((r p) ((L (p)
;; (p (L (x) (L (y) y)))) l)))))))) p) l))) (L (x) (((L (x) (L (y) ((L (p) ((p (L
;; (x) (L (y) y))) (L (x) (L (y) x)))) (((L (x) (L (y) ((L (n) ((n (L (x) (L (x) (L
;; (y) y)))) (L (x) (L (y) x)))) (((L (m) (L (n) ((n (L (n) (L (f) (L (x) (((n (L
;; (g) (L (h) (h (g f))))) (L (u) x)) (L (u) u)))))) m))) x) y)))) x) y)))) x) p)))
;; s)))) ((L (p) (p (L (x) (L (y) y)))) l))) ((L (p) (p (L (x) (L (y) x)))) l))))))
;; l))
;; (((L (p) (L (q) (L (h) ((h p) q)))) (L (f) (L (x) (f (f (f x)))))) (((L (p) (L
;; (q) (L (h) ((h p) q)))) (L (f) (L (x) (f x)))) (((L (p) (L (q) (L (h) ((h p)
;; q)))) (L (f) (L (x) (f (f x))))) (L (x) (L (x) (L (y) x)))))))
