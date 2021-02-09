require 'test_helper'

# NOTE: these tests are commented out as the idea was to use lambda
# calculus itself to run self-validation

# NOTE: this test should be focused on grammar parser instead

class BasicTest < Test::Unit::TestCase
  # def test_bool_true
  #   code = "#t"
  #   assert_equal true, lisp(code)
  # end

  # def test_bool_false
  #   code = "#f"
  #   assert_equal false, lisp(code)
  # end

  # def test_int
  #   code = "42"
  #   assert_equal 42, lisp(code)
  # end

  # def test_sum
  #   code = "(+ 1 2 3)"
  #   assert_equal 6, lisp(code)
  # end

  # def test_sub
  #   code = "(- 5 3 1)"
  #   assert_equal 1, lisp(code)
  # end

  # def test_mul
  #   code = "(* 6 7 2)"
  #   assert_equal 84, lisp(code)
  # end

  # def test_div
  #   code = "(/ 40 4 2)"
  #   assert_equal 5, lisp(code)
  # end

  # def test_eq
  #   code = "(= 6 6)"
  #   assert_equal true, lisp(code)
  # end

  # def test_define
  #   code = "(define x 10)
  #           x"
  #   assert_equal 10, lisp(code)
  # end

  # def test_define_scope
  #   code = "(define x 3)
  #           (+ x 5)"
  #   assert_equal 8, lisp(code)
  # end

  # def test_define_triple
  #   code = "(define x 3)
  #           (define y 4)
  #           (define z 5)
  #           (+ z (* x y) x)"
  #   assert_equal 20, lisp(code)
  # end

  # def test_cond_negative
  #   code = "(define x 5)
  #           (if (= 14 (* x 3))
  #              #t
  #              #f)"
  #   assert_equal false, lisp(code)
  # end

  # def test_cond_positive
  #   code = "(if (= (* 3 4) (+ 10 2))
  #              #t
  #              #f)"
  #   assert_equal true, lisp(code)
  # end

  # def test_cond_complex
  #   code = "(define x
  #             (if (= (/ 15 5) (+ 1 2))
  #               (if (= 6 (* 2 3)) 3 4)
  #               5))
  #           (* x 2)"
  #   assert_equal 6, lisp(code)
  # end

  # def test_lambda
  #   code = "((lambda (x)
  #              (+ x 2))
  #            5)"
  #   assert_equal 7, lisp(code)
  # end

  # def test_function
  #   code = "(define fn (lambda (x)
  #              (* 3 x)))
  #           (fn 5)"
  #   assert_equal 15, lisp(code)
  # end

  # def test_fact
  #   code = "(define fact (lambda (x)
  #              (if (= x 0)
  #                  1
  #                  (* (fact (- x 1))
  #                     x))))
  #           (fact 10)"
  #   assert_equal 3628800, lisp(code)
  # end

  # def test_inner_scopes
  #   code = "(define test (lambda (x)
  #              (lambda (y)
  #                (lambda (z)
  #                  (lambda (a)
  #                    (* a (+ x y z)))))))
  #           ((((test 1) 2) 3) 4)"
  #   assert_equal 24, lisp(code)
  # end

  # def test_y_combinator
  #   code = "(define Z
  #             (lambda (f)
  #               ((lambda (g)
  #                 (f (lambda (x) ((g g) x))))
  #               (lambda (g)
  #                 (f (lambda (x) ((g g) x)))))))

  #           ((Z (lambda (rec)
  #               (lambda (x)
  #                 (if (= x 0)
  #                     1
  #                     (* x (rec (- x 1)))))))
  #            6)"
  #   assert_equal 720, lisp(code)
  # end
end
