;
; Copyright © 2017 Colin Smith.
; This work is based on the Scmutils system of MIT/GNU Scheme:
; Copyright © 2002 Massachusetts Institute of Technology
;
; This is free software;  you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 3 of the License, or (at
; your option) any later version.
;
; This software is distributed in the hope that it will be useful, but
; WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
; General Public License for more details.
;
; You should have received a copy of the GNU General Public License
; along with this code; if not, see <http://www.gnu.org/licenses/>.
;

(ns sicmutils.rules
  (:require [pattern.rule :refer [ruleset rule-simplifier]
             #?@(:cljs [:include-macros true])]
            [sicmutils.complex :as c]
            [sicmutils.generic :as g]
            [sicmutils.value :as v]))

;; TODO troll for places like (: (- n 2)), where I actually need toperform a
;; computation BEFORE substitution instead of just subbing in the (+ 1 ), for
;; example.

(defn- negative-number? [x]
  (and (v/number? x)
       (g/negative? x)))

(defn- complex-number? [z]
  (and (c/complex? z)
       (not (v/nullity? (c/real-part z)))
       (not (v/nullity? (c/imag-part z)))))

(defn- imaginary-number? [z]
  (and (c/complex? z)
       (not (v/nullity? z))
       (v/nullity? (c/real-part z))))

(defn- imaginary-integer? [z]
  (and (c/complex? z)
       (not (v/nullity? z))
       (v/nullity? (c/real-part z))
       (v/integral? (c/imag-part z))))

(defn non-integer? [x]
  (not (v/integral? x)))

(defn- even-integer? [x]
  (and (v/integral? x) (v/nullity? (g/modulo x 2))))

(defn- odd-integer? [x]
  (and (v/integral? x)
       (not (v/nullity? (g/modulo x 2)))))

(defn- more-than-two? [x]
  (and (v/number? x) (> x 2)))

(defn- at-least-two? [x]
  (and (v/number? x) (>= x 2)))

(def logexp
  (ruleset
   (exp (* (:? n v/integral?) (log :x))) => (expt :x :n)

   (exp (log :x)) => :x

   (log (exp :x)) => :x

   (sqrt (exp :x)) => (exp (/ :x 2))

   (log (sqrt :x)) => (* (/ 1 2) (log :x))))

(def magsimp
  (ruleset
   (magnitude (* :x :y :ys*))
   =>
   (* (magnitude :x) (magnitude (* :y :ys*)))

   (magnitude (expt :x (:? n even-integer?)))
   =>
   (expt :x :n)
   ))

(def miscsimp
  ;; should really be one-like!
  (ruleset
   (expt :x 0) => 1

   (expt :x 1) => :x

   #_
   (let ((a (rcf:simplify a)) (b (rcf:simplify b)))
     (or (and (integer? a) (integer? b))
         (and (even-integer? b)
              (integer? (rcf:simplify (symb:* a b))))
         (and exponent-product-simplify?
              (assume! `(= (expt (expt ,x ,a) ,b)
                           (expt ,x (symb:* ,a ,b)))
                       'exponent-product))))
   (expt (expt :x :a) :b)
   =>
   (expt :x (:? #(g/* (:a %) (:b %))))

   ;; gated on ^1/2->sqrt?
   (expt :x (/ 1 2)) => (sqrt :x)

   ;; a rare, expensive luxury
   (* :fs1* :x :fs2* (expt :x :y) :fs3*)
   =>
   (* :f1* :f2* (expt :x (+ 1 :y)) :fs3*)

   ;; a rare, expensive luxury
   (* :fs1* (expt :x :y) :fs2* :x :fs3*)
   =>
   (* :f1* (expt :x (+ 1 :y)) :f2* :fs3*)

   ;; a rare, expensive luxury
   (* :fs1* (expt :x :y1) :fs2* (expt :x :y2) :fs3*)
   =>
   (* :fs1* :fs2* (expt :x (+ :y1 :y2)) :fs3*)))

(def simplify-square-roots
  (rule-simplifier
   (ruleset
    (expt (sqrt :x) (:? n even-integer?))
    => (expt :x (:? #(/ (% 'n) 2)))

    (sqrt (expt :x (:? n even-integer?)))
    => (expt :x (:? #(/ (% 'n) 2)))

    (expt (sqrt :x) (:? n odd-integer?))
    => (* (sqrt :x) (expt :x (:? #(/ (- (% 'n) 1) 2))))

    (/ :x (sqrt :x)) => (sqrt :x)

    (/ (sqrt :x) :x) => (/ 1 (sqrt :x))

    (/ (* :u* :x :v*) (sqrt :x))
    =>
    (* :u* (sqrt :x) :v*)

    (/ (* :u* (sqrt :x) :v*) :x)
    =>
    (/ (* :u* :v*) (sqrt :x))

    (/ :x (* :u* (sqrt :x) :v*))
    =>
    (/ (sqrt :x) (* :u* :v*))

    (/ (sqrt :x) (* :u* :x :v*))
    =>
    (/ 1 (* :u* (sqrt :x) :v*))

    (/ (* :p* :x :q*)
       (* :u* (sqrt :x) :v*))
    =>
    (/ (* :p* (sqrt :x) :q*)
       (* :u* :v*))

    (/ (* :p* (sqrt :x) :q*)
       (* :u* :x :v*))
    =>
    (/ (* :p* :q*)
       (* :u* (sqrt :x) :v*))

    ;; Following are the new rules we added to approach
    ;; the simplification of the time-invariant-canonical
    ;; test.

    ;; ... (sqrt a) ... (sqrt b) ... => ... (sqrt a b)
    (* :f1* (sqrt :a) :f2* (sqrt :b) :f3*)
    => (* :f1* :f2* :f3* (sqrt (* :a :b)))

    ;; (/ (* ... (sqrt a) ...)
    ;;    (* ... (sqrt b) ...)  => ... (sqrt (/ a b)) ... / ... ...
    (/ (* :f1* (sqrt :a) :f2*)
       (* :g1* (sqrt :b) :g2*))
    => (/ (* :f1* :f2* (sqrt (/ :a :b)))
          (* :g1* :g2*))
    )))

(def sqrt-expand
  (rule-simplifier
   (ruleset
    ;; "distribute the radical sign across products and quotients.
    ;; but doing this may allow equal subexpressions within the
    ;; radicals to cancel in various ways. The companion rule
    ;; sqrt-contract reassembles what remains."

    ;; Scmutils, in each of these expansions, will `assume!`
    ;; that the expressions named :x and :y are non-negative
    (sqrt (* :x :y)) => (* (sqrt :x) (sqrt :y))

    (sqrt (* :x :y :ys*)) => (* (sqrt :x) (sqrt (* :y :ys*)))

    (sqrt (/ :x :y)) => (/ (sqrt :x) (sqrt :y))

    (sqrt (/ :x :y :ys*)) => (/ (sqrt :x) (sqrt (* :y :ys*)))
    )))


(def sqrt-contract
  (rule-simplifier
   (ruleset
    ;; scmutils note: in scmutils, each of these rules checks to see whether,
    ;; after sub-simplification, x and y are equal, and if so, the opportunity
    ;; is taken to subsitute a simpler result.
    ;;
    ;; It could be that we don't need that, if there were a rule (for example)
    ;; to replace (* (sqrt x) (sqrt x)) with x. I tend to think that running the
    ;; simplifier on interior subexpressions is a dubious idea given how
    ;; much "churn" there is already waiting for the rulesets to stabilize

    ;; Scmutils, in each of these contractions, will `assume!`
    ;; that the expressions named :x and :y are non-negative
    (* :a* (sqrt :x) :b* (sqrt :y) :c*)
    => (* :a* :b* :c* (sqrt (* :x :y)))

    (/ (sqrt :x) (sqrt :y))
    => (sqrt (/ :x :y))

    (/ (* :a* (sqrt :x) :b*) (sqrt :y))
    => (* :a* :b* (sqrt (/ :x :y)))

    (/ (sqrt :x) (* :a* (sqrt :y) *b*))
    => (/ (sqrt (/ :x :y)) (* :a* :b*))

    (/ (* :a* (sqrt :x) :b*)
       (* :c* (sqrt :y) :d*))
    => (/ (* :a* :b* (sqrt (/ :x :y)))
          (* :c* :d*))
    )))

(def specfun->logexp
  (ruleset
   (sqrt :x) => (exp (* (/ 1 2) (log :x)))

   (atan :z)
   =>
   (/ (- (log (+ 1 (* (complex 0 1) :z)))
         (log (- 1 (* (complex 0 1) :z))))
      (complex 0 2))

   (asin :z)
   =>
   (* (complex 0 -1)
      (log (+ (* (complex 0 1) :z)
              (sqrt (- 1 (expt :z 2))))))

   (acos :z)
   =>
   (* (complex 0 -1)
      (log (+ :z (* (complex 0 1)
                    (sqrt (- 1 (expt :z 2)))))))

   (sinh :u) => (/ (- (exp :u) (exp (* -1 :u))) 2)

   (cosh :u) => (/ (+ (exp :u) (exp (* -1 :u))) 2)

   (expt :x (:? y non-integer?)) => (exp (* :y (log :x)))
   ))

(def logexp->specfun
  (ruleset
   (exp (* -1 (log :x))) => (expt :x -1)

   (exp (* (/ 1 2) (log :x1))) => (sqrt :x1)

   (exp (* (/ -1 2) (log :x1))) => (/ 1 (sqrt :x1))

   (exp (* (/ 3 2) (log :x1))) => (expt (sqrt :x1) 3)

   (exp (* (/ -3 2) (log :x1))) => (expt (sqrt :x1) -3)

   (exp (* :n1* (log :x) :n2*))
   =>
   (expt :x (* :n1* :n2*))
   ))



(comment
  (def log-contract
    (ruleset
     (+ :x1** (log :x2) :x3* (log :x4) :x5*)
     =>
     (+ :x1* :x3* :x5* (log (* :x2 :x4)))

     (- (log :x) (log :y))
     =>
     (log (/ :x :y))

     (+ :x1*
        (* :f1* (log :x) :f2*)
        :x2*
        (* :f3* (log :y) :f4*)
        :x3*)
     (let [s1 (rcf:simplify `(* ~@f1 ~@f2))
           s2 (rcf:simplify `(* ~@f3 ~@f4))]
       (when (exact-zero? (rcf:simplify `(- ~s1 ~s2)))
         s1))
     (+ (* (log (* :x :y)) :predicate-value)
        :x1* :x2* :x3*)
     )))

(def log-expand
  (ruleset
   (log (* :x1 :x2 :xs*))
   =>
   (+ (log :x1) (log (* :x2 :xs*)))

   (log (/ :x1 :x2))
   =>
   (- (log :x1) (log :x2))

   (log (expt :x :e))
   =>
   (* :e (log :x))
   ))

(def log-extra
  (ruleset
   (* (:? n v/integral?) :f1* (log :x) :f2*)
   =>
   (* :f1* (log (expt :x :n)) :f2*)
   ))

(def canonicalize-partials
  (rule-simplifier
   (ruleset
    ;; example: (((partial 2 1) ((partial 1 1) FF)) (up t (up x y) (down p_x p_y)))
    ;; since the partial indices in the outer derivative are lexically
    ;; greater than those of the inner, we canonicalize by swapping the
    ;; order. This is the "equality of mixed partials."
    (((partial :i*) ((partial :j*) :x)) :y*)
    #(> 0 (compare (% :i*) (% :j*)))
    (((partial :j*) ((partial :i*) :x)) :y*))))

;; TODO taken from scheme.
(def canonicalize-partials*
  (ruleset
   ;; First turn nests into products.
   ((partial :i*) ((partial :j*) :f))
   =>
   ((* (partial :i*) (partial :j*)) :f)

   ((partial :i*) ((* (partial :j*) :more*) :f))
   =>
   ((* (partial :i*) (partial :j*) :more*) :f)

   ;; Exponentiation of operators makes things hairy
   ((expt (partial :i*) :n) ((partial :j*) :f))
   =>
   ((* (expt (partial :i*) :n) (partial :j*)) :f)

   ((partial :i*) ((expt (partial :j*) :n) :f))
   =>
   ((* (partial :i*) (expt (partial :j*) :n)) :f)

   ((expt (partial :i*) :n) ((expt (partial :j*) :m) :f))
   =>
   ((* (expt (partial :i*) :n) (expt (partial :j*) :m)) :f)


   ;; Already some accumulation
   ((partial :i*) ((* (partial :j*) :more*) :f))
   =>
   ((* (partial :i*) (partial :j*) :more*) :f)

   ((expt (partial :i*) :n) ((* (partial :j*) :more*) :f))
   =>
   ((* (expt (partial :i*) :n) (partial :j*) :more*) :f)

   ((partial :i*) ((* (expt (partial :j*) (? m)) :more*) :f))
   =>
   ((* (partial :i*) (expt (partial :j*) :m) :more*) :f)

   ((expt (partial :i*) :n) ((* (expt (partial :j*) (? m)) :more*) :f))
   =>
   ((* (expt (partial :i*) :n) (expt (partial :j*) :m) :more*) :f)

   ;; Next sort products, if OK
   #_#_#_(((* :xs* (partial :i*) :ys* (partial :j*) :zs*)
           ;; TODO check that this is waht we mean with symbol
           (:? f symbol?))
          :args*)
   (let ((args (expression args)))
     (and commute-partials?
          (symb:elementary-access? i args)
          (symb:elementary-access? j args)
          (list< j i)))
   (((* :xs* (partial :j*) :ys* (partial :i*) :zs*) :f)
    :args*)
   ))

(def complex-trig
  ;; TODO: clearly more of these are needed.
  ;;
  ;; TODO check this in Clojurescript... does the 0.0 cause trouble here? EITHER
  ;; WAY go replace it above.
  (rule-simplifier
   (ruleset
    (cos (* :z (complex 0.0 1.0)))
    => (cosh :z)

    (sin (* :z (complex 0.0 1.0)))
    => (* (complex 0.0 1.0) (sinh :z))

    ;; Does this really belong here?
    ;; It works by reducing n mod 4 and then indexing into [1 i -1 -i].
    (expt (complex 0.0 1.0) (:? n v/integral?))
    => (:? #([1 '(complex 0 1) -1 '(complex 0 -1)] (mod (% 'n) 4))))))

(comment
  (define complex-rules
    (ruleset
     ( (make-rectangular (cos (? theta)) (sin (? theta)))
      none
      (exp (* +i (: theta))) )

     ( (real-part (make-rectangular (? x) (? y)))
      none
      (: x) )
     ( (imag-part (make-rectangular (? x) (? y)))
      none
      (: x) )

     ( (magnitude (make-rectangular (? x) (? y)))
      none
      (sqrt (+ (expt (: x) 2) (expt (: y) 2))) )
     ( (angle (make-rectangular (? x) (? y)))
      none
      (atan (: y) (: x)) )


     ( (real-part (make-polar (? m) (? a)))
      none
      (* (: m) (cos (: a))) )
     ( (imag-part (make-polar (? m) (? a)))
      none
      (* (: m) (sin (: a))) )

     ( (magnitude (make-polar (? m) (? a)))
      none
      (: m) )
     ( (angle (make-polar (? m) (? a)))
      none
      (: a) )
     )))

(def divide-numbers-through
  (rule-simplifier
   (ruleset
    (* 1 :factor)
    => :factor

    (* 1 :factors*)
    => (* :factors*)

    (/ (:? n v/number?) (:? d v/number?))
    => (:? #(g// (% 'n) (% 'd)))

    (/ (+ :terms*) (:? d v/number?))
    => (+ (:?? #(map (fn [n] `(~'/ ~n ~(% 'd))) (% :terms*)))))))

(comment
  (define divide-numbers-through
    (rule-system
     ( (* 1 (? factor))
      none
      (: factor) )

     ( (* 1 (?? factors))
      none
      (* (:: factors)) )

     ( (/ (? n number?) (? d number?))
      none
      (: (/ n d)) )

     ( (/ (+ (?? terms)) (? d number?))
      none
      (+ (:: (map (lambda (term) `(/ ,term ,d))
                  terms))) )

     ( (/ (* (? n number?) (?? factors)) (? d number?))
      none
      (* (: (/ n d)) (:: factors)) )

     ( (/ (* (?? factors)) (? d number?))
      none
      (* (: (n:invert d)) (:: factors)) )


     ( (/ (? n) (* (? d number?) (? factor)))
      none
      (/ (/ (: n) (: d)) (: factor)) )

     ( (/ (? n) (* (? d number?) (?? factors)))
      none
      (/ (/ (: n) (: d)) (* (:: factors))) )


     ( (/ (? n) (? d number?))
      none
      (* (: (n:invert d)) (: n)) )

     )))

(def trig->sincos
  (rule-simplifier
   (ruleset
    ;; GJS has other rules: to map cot, sec and csc to sin/cos, but
    ;; I don't think we need those since we transform those to sin/cos
    ;; in the env namespace.
    (tan :x) => (/ (sin :x) (cos :x)))))

;; note the difference in interface between rulesets and rule simplifiers.
;; rulesets return nil when they're not applicable (unless you specify a
;; custom fail continuation). Rule-simplifiers pass expressions through.

(def sincos->trig
  (rule-simplifier
   (ruleset
    ;; undoes the effect of trig->sincos
    (/ (sin :x) (cos :x))
    => (tan :x)

    (/ (sin :x) (* :d1* (cos :x) :d2*))
    => (/ (tan :x) (* :d1* :d2*))

    (/ (* :n1* (sin :x) :n1*)
       (* :d1* (cos :x) :d2*))
    => (/ (* :n1* (tan :x) :n2*)
          (* :d1* :d2*)))))

(comment
  ;;;; trigonometry

;;; the following rules are used to convert all trig expressions to
;;; ones involving only sin and cos functions, and to make 1-arg atan
;;; into 2-arg atan.

  (define trig->sincos
    (rule-system

     ( (tan (? x)) none (/ (sin (: x)) (cos (: x))) )

     ( (cot (? x)) none (/ (cos (: x)) (sin (: x))) )

     ( (sec (? x)) none (/ 1 (cos (: x))) )

     ( (csc (? x)) none (/ 1 (sin (: x))) )

     ( (atan (/ (? y) (? x))) none (atan (: y) (: x)) )

     ( (atan (? y)) none (atan (: y) 1) )

     ))


;;; sometimes we want to express combinations of sin and cos in terms
;;; of other functions.

  (define sincos->trig
    (rule-system
     ( (/ (sin (? x)) (cos (? x))) none (tan (: x)) )

     ( (/ (* (?? n1) (sin (? x)) (?? n2)) (cos (? x)))
      none
      (* (:: n1) (tan (: x)) (:: n2)) )


     ( (/ (sin (? x)) (* (?? d1) (cos (? x)) (?? d2)))
      none
      (/ (tan (: x)) (* (:: d1) (:: d2))) )


     ( (/ (* (?? n1) (sin (? x)) (?? n2))
          (* (?? d1) (cos (? x)) (?? d2)))
      none
      (/ (* (:: n1) (tan (: x)) (:: n2))
         (* (:: d1) (:: d2))) )

                                        ;   ( (/ (cos (? x)) (sin (? x))) none (cot (: x)) )

                                        ;   ( (/ (* (?? n1) (cos (? x)) (?? n2)) (sin (? x)))
                                        ;     none
                                        ;     (* (:: n1) (cot (: x)) (:: n2)) )


                                        ;   ( (/ (cos (? x)) (* (?? d1) (sin (? x)) (?? d2)))
                                        ;     none
                                        ;     (/ (cot (: x)) (* (:: d1) (:: d2))) )

                                        ;   ( (/ (* (?? n1) (cos (? x)) (?? n2))
                                        ;	(* (?? d1) (sin (? x)) (?? d2)))
                                        ;     none
                                        ;     (/ (* (:: n1) (cot (: x)) (:: n2))
                                        ;	(* (:: d1) (:: d2))) )
     ))
  )

(def triginv
  (rule-simplifier
   (ruleset
    (sin (asin :x))          => :x
    (asin (sin :x))          => :x
    (sin (atan :y :x))       => (/ :y (sqrt (+ (expt :x 2) (expt :y 2))))
    (cos (atan :y :x))       => (/ :x (sqrt (+ (expt :x 2) (expt :y 2))))
    (cos (asin :t))          => (sqrt (- 1 (square :t)))
    )
   (ruleset
    (acos (cos :x))          => :x
    (atan (tan :x))          => :x
    (atan (sin :x) (cos :x)) => :x
    (atan (* :c (sin :x)) (* :c (cos :x))) => :x)))

(comment
  (define triginv
    (rule-system

     ( (atan (? y) (? x))
      (and aggressive-atan-simplify?
           (let ((ys (rcf:simplify y)) (xs (rcf:simplify x)))
             (if (equal? ys xs)
               (if (number? ys)
                 (if (negative? ys)
                   '(- (/ (* 3 :pi) 4))
                   '(/ :pi 4))
                 (let ((note `(assuming (positive? ,xs))))
                   (eq-adjoin! note 'rules 'aggressive-atan-1)
                   (note-that! note)
                   '(/ :pi 4)))
               (if (and (number? ys) (number? xs))
                 (atan ys xs)
                 (let ((s (rcf:simplify `(gcd ,ys ,xs))))
                   (if (equal? s 1)
                     #f            ;do nothing
                     (let ((note `(assuming (positive? ,s)))
                           (yv (rcf:simplify `(/ ,ys ,s)))
                           (xv (rcf:simplify `(/ ,xs ,s))))
                       (eq-adjoin! note 'rules 'aggressive-atan-2)
                       (note-that! note)
                       `(atan ,yv ,xv)))))))) )

     ( (sin (asin (? x))) none (: x) )
     ( (asin (sin (? x)))
      (and inverse-simplify?
           (let ((xs (rcf:simplify x)))
             (assume! `(= (asin (sin ,xs)) ,xs) 'asin-sin)))
      (: x) )

     ( (cos (acos (? x))) none (: x) )
     ( (acos (cos (? x)))
      (and inverse-simplify?
           (let ((xs (rcf:simplify x)))
             (assume! `(= (acos (cos ,xs)) ,xs) 'acos-cos)))
      (: x) )

     ( (tan (atan (? x))) none (: x) )
     ( (atan (tan (? x)))
      (and inverse-simplify?
           (let ((xs (rcf:simplify x)))
             (assume! `(= (atan (tan ,xs)) ,xs) 'atan-tan)))
      (: x) )

     ( (sin (acos (? x))) none (sqrt (- 1 (expt (: x) 2))) )
     ( (cos (asin (? y))) none (sqrt (- 1 (expt (: y) 2))) )
     ( (tan (asin (? y))) none (/ (: y) (sqrt (- 1 (expt (: y) 2)))) )
     ( (tan (acos (? x))) none (/ (sqrt (- 1 (expt (: x) 2))) (: x)) )

     ( (atan (sin (? x)) (cos (? x)))
      (and inverse-simplify?
           (let ((xs (rcf:simplify x)))
             (assume! `(= (atan (sin ,xs) (cos ,xs)) ,xs) `atan-sin-cos)))
      (: x) )

     ( (asin (cos (? x)))
      (and inverse-simplify?
           (let ((xs (rcf:simplify x)))
             (assume! `(= (asin (cos ,xs)) (- (* 1/2 :pi) ,xs)) 'asin-cos)))
      (- (* 1/2 :pi) (: x)) )
     ( (acos (sin (? x)))
      (and inverse-simplify?
           (let ((xs (rcf:simplify x)))
             (assume! `(= (acos (sin ,xs)) (- (* 1/2 :pi) ,xs)) 'acos-sin)))
      (- (* 1/2 :pi) (: x)) )

     ( (sin (atan (? a) (? b)))
      none
      (/ (: a) (sqrt (+ (expt (: a) 2) (expt (: b) 2)))) )

     ( (cos (atan (? a) (? b)))
      none
      (/ (: b) (sqrt (+ (expt (: a) 2) (expt (: b) 2)))) )

     )))

(comment
  ;; confirm that these all apply in numsymb, on construction.

;;; Rules when :pi is symbolic.

  (define (zero-mod-pi? x)
    (integer? (rcf:simplify (symb:/ x :pi))))

  (define (pi/2-mod-2pi? x)
    (integer?
     (rcf:simplify (symb:/ (symb:- x (symb:/ :pi 2)) (symb:* 2 :pi)))))

  (define (-pi/2-mod-2pi? x)
    (integer?
     (rcf:simplify (symb:/ (symb:+ x (symb:/ :pi 2)) (symb:* 2 :pi)))))

  (define (pi/2-mod-pi? x)
    (integer? (rcf:simplify (symb:/ (symb:- x (symb:/ :pi 2)) :pi))))

  (define (zero-mod-2pi? x)
    (integer? (rcf:simplify (symb:/ x (symb:* 2 :pi)))))

  (define (pi-mod-2pi? x)
    (integer? (rcf:simplify (symb:/ (symb:- x :pi) (symb:* 2 :pi)))))

  (define (pi/4-mod-pi? x)
    (integer? (rcf:simplify (symb:/ (symb:- x (symb:/ :pi 4)) :pi))))

  (define (-pi/4-mod-pi? x)
    (integer? (rcf:simplify (symb:/ (symb:+ x (symb:/ :pi 4)) :pi))))

  (define special-trig
    (rule-system

     ( (sin (? x zero-mod-pi?))   none  0 )
     ( (sin (? x pi/2-mod-2pi?))  none +1 )
     ( (sin (? x -pi/2-mod-2pi?)) none -1 )

     ( (cos (? x pi/2-mod-pi?))   none  0 )
     ( (cos (? x zero-mod-2pi?))  none +1 )
     ( (cos (? x pi-mod-2pi?))    none -1 )

     ( (tan (? x zero-mod-pi?))   none  0 )
     ( (tan (? x pi/4-mod-pi?))   none +1 )
     ( (tan (? x -pi/4-mod-pi?))  none -1 )

     ))
  )

(comment
  (define angular-parity
    (rule-system
     ( (cos (? n negative-number?))
      none
      (cos (: (- n))) )

     ( (cos (* (? n negative-number?) (?? x)))
      none
      (cos (* (: (- n)) (:: x))) )

     ( (cos (+ (* (? n negative-number?) (?? x)) (?? y)))
      none
      (cos (- (* (: (- n)) (:: x)) (:: y))) )

     ( (sin (? n negative-number?))
      none
      (- (sin (: (- n)))) )

     ( (sin (* (? n negative-number?) (?? x)))
      none
      (- (sin (* (: (- n)) (:: x)))) )

     ( (sin (+ (* (? n negative-number?) (?? x)) (?? y)))
      none
      (- (sin (- (* (: (- n)) (:: x)) (:: y)))) )
     )))

(comment
  (define (exact-integer>3? x)
    (and (exact-integer? x) (> x 3)))

  (define expand-multiangle
    (rule-system
     ( (sin (* 2 (? x) (?? y)))
      none
      (* 2 (sin (* (: x) (:: y))) (cos (* (: x) (:: y)))) )

     ( (cos (* 2 (? x) (?? y)))
      none
      (- (* 2 (expt (cos (* (: x) (:: y))) 2)) 1) )

     ( (sin (* 3 (? x) (?? y)))
      none
      (+ (* 3 (sin (* (: x) (:: y)))) (* -4 (expt (sin (* (: x) (:: y))) 3))) )

     ( (cos (* 3 (? x) (?? y)))
      none
      (+ (* 4 (expt (cos (* (: x) (:: y))) 3)) (* -3 (cos (* (: x) (:: y))))) )

     ( (sin (* (? n exact-integer>3?) (? f) (?? fs))) ;at least one f
      (> n 1)
      (+ (* (sin (* (: (- n 1)) (: f) (:: fs))) (cos (* (: f) (:: fs))))
         (* (cos (* (: (- n 1)) (: f) (:: fs))) (sin (* (: f) (:: fs))))) )

     ( (sin (+ (? x) (? y) (?? ys)))	;at least one y
      none
      (+ (* (sin (: x)) (cos (+ (: y) (:: ys))))
         (* (cos (: x)) (sin (+ (: y) (:: ys))))) )

     ( (cos (* (? n exact-integer>3?) (? f) (?? fs))) ;at least one f
      (> n 1)
      (- (* (cos (* (: (- n 1)) (: f) (:: fs))) (cos (* (: f) (:: fs))))
         (* (sin (* (: (- n 1)) (: f) (:: fs))) (sin (* (: f) (:: fs))))) )

     ( (cos (+ (? x) (? y) (?? ys)))	;at least one y
      none
      (- (* (cos (: x)) (cos (+ (: y) (:: ys))))
         (* (sin (: x)) (sin (+ (: y) (:: ys))))) )
     )))

(comment
  (define trig-sum-to-product
    (rule-system
     ( (+ (?? a) (sin (? x)) (?? b) (sin (? y)) (?? c) )
      none
      (+ (* 2 (sin (/ (+ (: x) (: y)) 2)) (cos (/ (- (: x) (: y)) 2))) (:: a) (:: b) (:: c)) )

     ( (+ (?? a) (sin (? x)) (?? b) (* -1 (sin (? y))) (?? c) )
      none
      (+ (* 2 (sin (/ (- (: x) (: y)) 2)) (cos (/ (+ (: x) (: y)) 2))) (:: a) (:: b) (:: c)) )

     ( (+ (?? a) (* -1 (sin (? y))) (?? b) (sin (? x)) (?? c) )
      none
      (+ (* 2 (sin (/ (- (: x) (: y)) 2)) (cos (/ (+ (: x) (: y)) 2))) (:: a) (:: b) (:: c)) )

     ( (+ (?? a) (cos (? x)) (?? b) (cos (? y)) (?? c) )
      none
      (+ (* 2 (cos (/ (+ (: x) (: y)) 2)) (cos (/ (- (: x) (: y)) 2))) (:: a) (:: b) (:: c)) )

     ( (+ (?? a) (cos (? x)) (?? b) (* -1 (cos (? y))) (?? c) )
      none
      (+ (* -2 (sin (/ (+ (: x) (: y)) 2)) (sin (/ (- (: x) (: y)) 2))) (:: a) (:: b) (:: c)) )

     ( (+ (?? a) (* -1 (cos (? y))) (?? b) (cos (? x)) (?? c) )
      none
      (+ (* -2 (sin (/ (+ (: x) (: y)) 2)) (sin (/ (- (: x) (: y)) 2))) (:: a) (:: b) (:: c)) )
     ))

  (define trig-product-to-sum
    (rule-system
     ( (* (?? u) (sin (? x)) (?? v) (sin (? y)) (?? w))
      none
      (* 1/2 (- (cos (- (: x) (: y))) (cos (+ (: x) (: y)))) (:: u) (:: v) (:: w)) )

     ( (* (?? u) (cos (? x)) (?? v) (cos (? y)) (?? w))
      none
      (* 1/2 (+ (cos (- (: x) (: y))) (cos (+ (: x) (: y)))) (:: u) (:: v) (:: w)) )

     ( (* (?? u) (sin (? x)) (?? v) (cos (? y)) (?? w))
      none
      (* 1/2 (+ (sin (+ (: x) (: y))) (sin (- (: x) (: y)))) (:: u) (:: v) (:: w)) )

     ( (* (?? u) (cos (? y)) (?? v) (sin (? x)) (?? w))
      none
      (* 1/2 (+ (sin (+ (: x) (: y))) (sin (- (: x) (: y)))) (:: u) (:: v) (:: w)) )
     )))

(comment
  (define contract-expt-trig
    (rule-system
     ( (expt (sin (? x)) (? n exact-integer?))
      (> n 1)
      (* 1/2 (expt (sin (: x)) (: (- n 2))) (- 1 (cos (* 2 (: x))))))

     ( (expt (cos (? x)) (? n exact-integer?))
      (> n 1)
      (* 1/2 (expt (cos (: x)) (: (- n 2))) (+ 1 (cos (* 2 (: x))))))
     )))

(comment
  (define (sin-half-angle-formula theta)
    (let ((thetas (rcf:simplify theta)))
      (assume!
       `(non-negative?
         (+ (* 2 :pi)
            (* -1 ,thetas)
            (* 4 :pi (floor (/ ,thetas (* 4 :pi))))))
       'sin-half-angle-formula)
      `(sqrt (/ (- 1 (cos ,thetas)) 2))))

  (define (cos-half-angle-formula theta)
    (let ((thetas (rcf:simplify theta)))
      (assume!
       `(non-negative?
         (+ :pi
            ,thetas
            (* 4 :pi
               (floor (/ (- :pi ,thetas) (* 4 :pi))))))
       'cos-half-angle-formula)
      `(sqrt (/ (+ 1 (cos ,theta)) 2))))

  (define half-angle
    (rule-system
     ( (sin (* 1/2 (? x) (?? y)))
      (and half-angle-simplify?
           (sin-half-angle-formula `(* ,x ,@y))) )

     ( (sin (/ (? x) 2))
      (and half-angle-simplify?
           (sin-half-angle-formula x)) )

     ( (cos (* 1/2 (? x) (?? y)))
      (and half-angle-simplify?
           (cos-half-angle-formula `(* ,x ,@y))) )

     ( (cos (/ (? x) 2))
      (and half-angle-simplify?
           (cos-half-angle-formula x)) )
     ))
  )

(comment
  (define sin^2->cos^2
    (rule-system
     ( (expt (sin (? x)) (? n at-least-two?))
      none
      (* (expt (sin (: x)) (: (- n 2)))
         (- 1 (expt (cos (: x)) 2))) )
     ))

  (define cos^2->sin^2
    (rule-system
     ( (expt (cos (? x)) (? n at-least-two?))
      none
      (* (expt (cos (: x)) (: (- n 2)))
         (- 1 (expt (sin (: x)) 2))) )
     )))

(def sin-sq->cos-sq
  (rule-simplifier
   (ruleset
    (expt (sin :x) (:? n at-least-two?))
    => (* (expt (sin :x) (:? #(- (% 'n) 2)))
          (- 1 (expt (cos :x) 2))))))

(def ^:private split-high-degree-cosines
  (ruleset
   (* :f1* (expt (cos :x) (:? n more-than-two?)) :f2*)
   => (* (expt (cos :x) 2)
         (expt (cos :x) (:? #(- (% 'n) 2)))
         :f1*
         :f2*)

   (+ :a1* (expt (cos :x) (:? n more-than-two?)) :a2*)
   => (+ (* (expt (cos :x) 2)
            (expt (cos :x) (:? #(- (% 'n) 2))))
         :a1*
         :a2*)))

(def ^:private split-high-degree-sines
  (ruleset
   (* :f1* (expt (sin :x) (:? n more-than-two?)) :f2*)
   => (* (expt (sin :x) 2)
         (expt (sin :x) (:? #(- (% 'n) 2)))
         :f1*
         :f2*)

   (+ :a1* (expt (sin :x) (:? n more-than-two?)) :a2*)
   => (+ (* (expt (sin :x) 2)
            (expt (sin :x) (:? #(- (% 'n) 2))))
         :a1*
         :a2*)))

(def ^:private flush-obvious-ones
  (ruleset
   (+ :a1* (expt (sin :x) 2) :a2* (expt (cos :x) 2) :a3*)
   => (+ 1 :a1* :a2* :a3*))

  ;; gate on this:
  #_
  (let ((s1 (rcf:simplify `(* ,@f1 ,@f2)))
        (s2 (rcf:simplify `(* ,@f3 ,@f4))))
    (if (exact-zero? (rcf:simplify `(- ,s1 ,s2)))
      s1
      #f))

  ;; TODO figure out predicate value!
  #_#_#_
  (+ :a1*
     (* :f1* (expt (sin :x) 2) :f2*)
     :a2*
     (* :f3* (expt (cos :x) 2) :f4*)
     :a3*)
  =>
  (+ :a1* :a2* :a3* (: predicate-value))

  ;; are sines always before cosines after we poly simplify? they are in
  ;; scmutils, so we should be alert for this. in scmutils, there are a couple
  ;; of others that involve rcf:simplify, which we don't have, and we don't know
  ;; if pcf:simplify is an acceptable substitute here; and we don't have a
  ;; method for pasting the value of a predicate into a rule, so this is far
  ;; from complete.
  ;;
  ;; TODO add this ability!
  ;;
  ;; TODO I think we CAN do rcf:simplify now.
  )

(def sincos-flush-ones
  (rule-simplifier
   split-high-degree-cosines
   split-high-degree-sines
   flush-obvious-ones))

(comment
  (define sincos-random
    (rule-system

     ( (+ (?? a1) (? a) (?? a2) (expt (cos (? x)) (? n at-least-two?)) (?? a3))
      (exact-zero? (rcf:simplify `(+ ,a (expt (cos ,x) ,(- n 2)))))
      (+ (:: a1) (:: a2) (:: a3) (* (expt (sin (: x)) 2) (: a))) )

     ( (+ (?? a1) (expt (cos (? x)) (? n at-least-two?)) (?? a2) (? a) (?? a3))
      (exact-zero? (rcf:simplify `(+ ,a (expt (cos ,x) ,(- n 2)))))
      (+ (:: a1) (:: a2) (:: a3) (* (expt (sin (: x)) 2) (: a))) )

     ( (+ (?? a1) (? a) (?? a2) (expt (sin (? x)) (? n at-least-two?)) (?? a3))
      (exact-zero? (rcf:simplify `(+ ,a (expt (sin ,x) ,(- n 2)))))
      (+ (:: a1) (:: a2) (:: a3) (* (expt (cos (: x)) 2) (: a))) )

     ( (+ (?? a1) (expt (sin (? x)) (? n at-least-two?)) (?? a2) (? a) (?? a3))
      (exact-zero? (rcf:simplify `(+ ,a (expt (sin ,x) ,(- n 2)))))
      (+ (:: a1) (:: a2) (:: a3) (* (expt (cos (: x)) 2) (: a))) )

     ( (+ (?? a1)
          (? a)
          (?? a2)
          (* (?? b1) (expt (cos (? x)) (? n at-least-two?)) (?? b2))
          (?? a3))
      (exact-zero? (rcf:simplify `(+ (* ,@b1 ,@b2 (expt (cos ,x) ,(- n 2))) ,a)))
      (+ (:: a1) (:: a2) (:: a3) (* (: a) (expt (sin (: x)) 2))) )

     ( (+ (?? a1)
          (? a)
          (?? a2)
          (* (?? b1) (expt (sin (? x)) (? n at-least-two?)) (?? b2))
          (?? a3))
      (exact-zero? (rcf:simplify `(+ (* ,@b1 ,@b2 (expt (sin ,x) ,(- n 2))) ,a)))
      (+ (:: a1) (:: a2) (:: a3) (* (: a) (expt (cos (: x)) 2))) )


     ( (+ (?? a1)
          (* (?? b1) (expt (cos (? x)) (? n at-least-two?)) (?? b2))
          (?? a2)
          (? a)
          (?? a3))
      (exact-zero? (rcf:simplify `(+ (* ,@b1 ,@b2 (expt (cos ,x) ,(- n 2))) ,a)))
      (+ (:: a1) (:: a2) (:: a3) (* (: a) (expt (sin (: x)) 2))) )

     ( (+ (?? a1)
          (* (?? b1) (expt (sin (? x)) (? n at-least-two?)) (?? b2))
          (?? a2)
          (? a)
          (?? a3))
      (exact-zero? (rcf:simplify `(+ (* ,@b1 ,@b2 (expt (sin ,x) ,(- n 2))) ,a)))
      (+ (:: a1) (:: a2) (:: a3) (* (: a) (expt (cos (: x)) 2))) )

     )))

(comment
  ;;; we can eliminate sin and cos in favor of complex exponentials

  (define sincos->exp1
    (rule-system
     ( (sin (? x))
      none
      (/ (- (exp (* +i (: x))) (exp (* -i (: x))))
         +2i) )

     ( (cos (? x))
      none
      (/ (+ (exp (* +i (: x))) (exp (* -i (: x))))
         2) )
     ))

  (define sincos->exp2
    (rule-system
     ( (sin (? x))
      none
      (/ (- (exp (* +i (: x))) (/ 1 (exp (* +i (: x)))))
         +2i) )

     ( (cos (? x))
      none
      (/ (+ (exp (* +i (: x))) (/ 1 (exp (* +i (: x)))))
         2) )
     ))

;;; under favorable conditions, we can replace the trig functions.

  (define exp->sincos
    (rule-system
     ( (exp (? c1 imaginary-number?))
      (positive? (n:imag-part c1))
      (+ (cos (: (n:imag-part c1)))
         (* +i (sin (: (n:imag-part c1))))) )

     ( (exp (? c1 imaginary-number?))
      (negative? (n:imag-part c1))
      (+ (cos (: (- (n:imag-part c1))))
         (* -i (sin (: (- (n:imag-part c1)))))) )

     ( (exp (* (? c1 imaginary-number?) (?? f)))
      (positive? (n:imag-part c1))
      (+ (cos (* (: (n:imag-part c1)) (:: f)))
         (* +i (sin (* (: (n:imag-part c1)) (:: f))))) )

     ( (exp (* (? c1 imaginary-number?) (?? f)))
      (negative? (n:imag-part c1))
      (* (exp (: (n:real-part c1)))
         (+ (cos (* (: (- (n:imag-part c1))) (:: f)))
            (* -i (sin (* (: (- (n:imag-part c1))) (:: f)))))) )

     ( (exp (? c1 complex-number?))
      (positive? (n:imag-part c1))
      (* (exp (: (n:real-part c1)))
         (+ (cos (: (n:imag-part c1)))
            (* +i (sin (: (n:imag-part c1)))))) )

     ( (exp (? c1 complex-number?))
      (negative? (n:imag-part c1))
      (* (exp (: (n:real-part c1)))
         (+ (cos (: (- (n:imag-part c1))))
            (* -i (sin (: (- (n:imag-part c1))))))) )

     ( (exp (* (? c1 complex-number?) (?? f)))
      (positive? (n:imag-part c1))
      (* (exp (: (n:real-part c1)))
         (+ (cos (* (: (n:imag-part c1)) (:: f)))
            (* +i (sin (* (: (n:imag-part c1)) (:: f)))))) )

     ( (exp (* (? c1 complex-number?) (?? f)))
      (negative? (n:imag-part c1))
      (* (exp (: (n:real-part c1)))
         (+ (cos (* (: (- (n:imag-part c1))) (:: f)))
            (* -i (sin (* (: (- (n:imag-part c1))) (:: f)))))) )
     )))

(comment
  (define exp-contract
    (rule-system
     ( (* (?? x1) (exp (? x2)) (?? x3) (exp (? x4)) (?? x5))
      none
      (* (:: x1) (:: x3) (:: x5) (exp (+ (: x2) (: x4)))) )

     ( (expt (exp (? x)) (? p)) none (exp (* (: p) (: x))) )

     ( (/ (exp (? x)) (exp (? y))) none (exp (- (: x) (: y))) )

     ( (/ (* (?? x1) (exp (? x)) (?? x2)) (exp (? y)))
      none
      (* (:: x1) (:: x2) (exp (- (: x) (: y)))) )

     ( (/ (exp (? x)) (* (?? y1) (exp (? y)) (?? y2)))
      none
      (/ (exp (- (: x) (: y))) (* (:: y1) (:: y2))) )

     ( (/ (* (?? x1) (exp (? x)) (?? x2))
          (* (?? y1) (exp (? y)) (?? y2)))
      none
      (/ (* (:: x1) (:: x2) (exp (- (: x) (: y))))
         (* (:: y1) (:: y2))) )
     ))

  (define exp-expand
    (rule-system
     ( (exp (- (? x1)))
      none
      (/ 1 (exp (: x1))) )

     ( (exp (- (? x1) (? x2)))
      none
      (/ (exp (: x1)) (exp (: x2))) )

     ( (exp (+ (? x1) (? x2) (?? xs)))
      none
      (* (exp (: x1)) (exp (+ (: x2) (:: xs)))) )

     ( (exp (* (? x imaginary-integer?) (?? factors)))
      (> (n:imag-part x) 1)
      (expt (exp (* +i (:: factors))) (: (n:imag-part x))) )

     ( (exp (* (? x imaginary-integer?) (?? factors)))
      (< (n:imag-part x) -1)
      (expt (exp (* -i (:: factors))) (: (- (n:imag-part x)))) )

     ( (exp (* (? n exact-integer?) (?? factors)))
      (> n 1)
      (expt (exp (* (:: factors))) (: n)) )

     ( (exp (* (? n exact-integer?) (?? factors)))
      (< n -1)
      (expt (exp (* -1 (:: factors))) (: (- n))) )

     ( (exp (? x complex-number?))
      none
      (* (exp (: (n:real-part x)))
         (exp (: (n:* (n:imag-part x) +i)))) )

     ( (exp (* (? x complex-number?) (?? factors)))
      none
      (* (exp (* (: (n:real-part x)) (:: factors)))
         (exp (* (: (n:* (n:imag-part x) +i)) (:: factors)))) )
     ))
  )

(defn universal-reductions
  [x]
  (triginv x))

(comment
  (define (universal-reductions exp)
    (let ((vars (variables-in exp)))
      (let ((logexp? (occurs-in? '(log exp) vars))
            (sincos? (occurs-in? '(sin cos) vars))
            (invtrig? (occurs-in? '(asin acos atan) vars))
            (sqrt? (memq 'sqrt vars))
            (mag? (memq 'magnitude vars))
            )
        (let* ((e0 (miscsimp exp))
               (e1 (if logexp? (logexp e0) e0))
               (e2 (if mag? (magsimp e1) e1))
               (e3 (if
                       (and sincos? (symbol? :pi) sin-cos-simplify?)
                     (special-trig e2)
                     e2)))
          (cond ((and sincos? invtrig?)
                 (simsqrt (triginv e3)))
                (sqrt? (simsqrt e3))
                (else e3)))))))
