;;
;; Copyright © 2017 Colin Smith.
;; This work is based on the Scmutils system of MIT/GNU Scheme:
;; Copyright © 2002 Massachusetts Institute of Technology
;;
;; This is free software;  you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3 of the License, or (at
;; your option) any later version.
;;
;; This software is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this code; if not, see <http://www.gnu.org/licenses/>.
;;

(ns sicmutils.polynomial
  (:refer-clojure :exclude [divide])
  (:require [clojure.set :as set]
            [clojure.string :as cs]
            [sicmutils.expression.analyze :as a]
            [sicmutils.expression :as x]
            [sicmutils.function :as f]
            [sicmutils.generic :as g]
            [sicmutils.numsymb :as sym]
            [sicmutils.util :as u]
            [sicmutils.value :as v]))

;; # Flat Polynomial Form, for Commutative Rings
;;
;; The namespace starts by defining monomials, then builds these into
;; polynomials with a proper type definition.
;;
;; ## Monomials
;;
;; A monomial is a single term of a polynomial. NOTE we need to clarify this vs
;; the polynomial single term with coef.
;;
;; We represent a monomial as a vector of integers representing the exponents of
;; the indeterminates over some ring. For example; we would represent x^2
;; as [2], and xy^2 as [1 2], though the indeterminates have no name.
;; Polynomials are linear combinations of the monomials. When these are formed,
;; it is important that the monomial vectors all contain the same number of
;; slots, so that 3x + 2y^2 would be represented as: 3*[1 0] + 2*[0 2].

(defn- monomial-degree
  "Compute the degree of a monomial. This is just the sum of the exponents."
  [m]
  (apply g/+ m))

;; ### Monomial Comparators
;;
;; These comparators are in the sense of Java: x.compareTo(y), so that this
;; returns 1 if x > y, -1 if x < y, and 0 if x = y.

(defn ^:no-doc lex-order
  "Lex order for monomials considers the power of x, then the power of y, etc."
  [xs ys]
  {:pre (= (count xs)
           (count ys))}
  (compare xs ys))

(defn ^:no-doc graded-lex-order [xs ys]
  {:pre (= (count xs)
           (count ys))}
  (let [xd (monomial-degree xs)
        yd (monomial-degree ys)]
    (if (= xd yd)
      (lex-order xs ys)
      (g/- xd yd))))

(defn ^:no-doc graded-reverse-lex-order [xs ys]
  {:pre (= (count xs) (count ys))}
  (let [xd (monomial-degree xs)
        yd (monomial-degree ys)]
    (if (= xd yd)
      (compare (vec (rseq ys))
               (vec (rseq xs)))
      (g/- xd yd))))

(def ^:private monomial-order
  graded-lex-order)

;; ## Polynomial Terms

;; from pcf
(def base? v/number?)

;; from fpf
(defn coeff? [x]
  (v/number? x))

(defn coeff-zero? [x]
  (and (coeff? x)
       (v/zero? x)))

;; ## Term List
;;
;; Terms are represented as pairs of [<monomial>, <coef>]. A polynomial (called
;; an `fpf` in scmutils, for Flat Polynomial Form), is a sorted list of terms.

(defn make-term
  "Takes a monomial and a coefficient and returns a polynomial term."
  [expts coef]
  [expts coef])

(defn exponents [term]
  (nth term 0 []))

(defn coefficient [term]
  (nth term 1 0))

(def ^:no-doc empty-terms
  [])

(defn constant-term? [term]
  (v/zero?
   (exponents term)))

;; ## Polynomial Type Definition
;;
;; TODO look at PowerSeries, see what we're missing.

(declare make-constant poly->str)

(deftype Polynomial [arity xs->c]
  v/Value
  (zero? [_]
    (empty? xs->c))

  (one? [_]
    (and (= (count xs->c) 1)
         (let [[term] xs->c]
           (and (v/zero? (exponents term))
                (v/one? (coefficient term))))))

  (identity? [_]
    (and (v/one? arity)
         (= (count xs->c) 1)
         (let [[[[e] c]] xs->c]
           (and (v/one? e)
                (v/one? c)))))

  (zero-like [_]
    (Polynomial. arity empty-terms))

  (one-like [_]
    (let [one (if-let [term (first xs->c)]
                (v/one-like (coefficient term))
                1)]
      (make-constant arity one)))

  (identity-like [_]
    (assert (v/one? arity)
            "identity-like unsupported on multivariate monomials!")
    (let [one (if-let [term (first xs->c)]
                (v/one-like (coefficient term))
                1)
          term (make-term [1] one)]
      (Polynomial. arity [term])))

  (exact? [_] false)
  (freeze [_] `(~'polynomial ~arity ~xs->c))
  (kind [_] ::polynomial)

  f/IArity
  (arity [_] arity)

  #?@(:clj
      [Object
       (equals [_ b]
               (and (instance? Polynomial b)
                    (and (= arity (.-arity b))
                         (= xs->c (.-xs->c b)))))

       (toString [p] (poly->str p))]

      :cljs
      [IEquiv
       (-equiv [_ b]
               (and (instance? Polynomial b)
                    (and (= arity (.-arity b))
                         (= xs->c (.-xs->c b)))))

       Object
       (toString [p] (poly->str p))

       IPrintWithWriter
       (-pr-writer [x writer _]
                   (write-all writer
                              "#object[sicmutils.structure.Polynomial \""
                              (.toString x)
                              "\"]"))]))

(defn explicit-polynomial?
  "Returns true if the supplied argument is an instance of `Polynomial`, false
  otherwise."
  [x]
  (instance? Polynomial x))

(defn polynomial? [x]
  (or (coeff? x)
      (explicit-polynomial? x)))

(defn- bare-arity [p]
  {:pre [(explicit-polynomial? p)]}
  (.-arity ^Polynomial p))

(defn- bare-terms [p]
  {:pre [(explicit-polynomial? p)]}
  (.-xs->c ^Polynomial p))

(defn terms [p]
  (if (and (coeff? p)
           (coeff-zero? p))
    []
    (bare-terms p)))

(defn- lead-term
  "Return the leading (i.e., highest degree) term of the polynomial p. The return
  value is a pair of [exponents coefficient].

  TODO this is a change, returning an explicit term always. NOTE, test."
  [p]
  (or (peek (terms p))
      [[] 0]))

(defn arity
  "TODO what's the difference between arity and degree?"
  [p]
  (if (coeff? p)
    0
    (bare-arity p)))

(defn degree
  "TODO what's the difference between arity and degree?"
  [p]
  (cond (v/zero? p) -1
        (coeff? p) 0
        :else (monomial-degree
               (exponents
                (lead-term p)))))

(defn monomial?
  "NOTE this can handle coefs now."
  [p]
  (or (coeff? p)
      (= 1 (count (terms p)))))

(defn monic?
  "Returns true if `p` is a [monic
  polynomial](https://en.wikipedia.org/wiki/Monic_polynomial), false otherwise."
  [p]
  (if (coeff? p)
    (v/one? p)
    (and (= 1 (arity p))
         (v/one? (coefficient
                  (lead-term p))))))

(defn coefficients
  "NOTE this can handle coefs now."
  [p]
  (if (coeff? p)
    [p]
    (map coefficient (terms p))))

;; String methods...

(defn- term->str [term]
  (let [expts (exponents term)
        coef  (coefficient term)]
    (str coef "*[" (cs/join "," expts) "]")))

(defn- poly->str
  ([p] (poly->str p 10))
  ([p n]
   {:pre [explicit-polynomial? p]}
   (let [terms     (bare-terms p)
         n-terms   (count terms)
         term-strs (take n (map term->str terms))
         suffix    (when (> n-terms n)
                     (str "...and " (g/- n-terms n) " more terms"))]
     (str "(" (cs/join " + " term-strs) suffix ")"))))

;; ## Constructors

(defn make-constant
  "Return a constant polynomial of the given arity."
  [arity c]
  (let [terms (if (v/zero? c)
                empty-terms
                [(make-term (into [] (repeat arity 0)) c)])]
    (->Polynomial arity terms)))

;; TODO check what this actually generates... I bet we do NOT want to generate
;; NON polynomials here, if the original does not!!

(defn make-c*xn
  "Polynomial representing c*x^n, where x is always the first indeterminate."
  [arity c n]
  (cond (<= n -1)   0
        (v/zero? n) c
        (v/zero? c) c
        :else
        (let [term (make-term (into [n] (repeat (dec arity) 0))
                              c)]
          (->Polynomial arity [term]))))

(defn- guarded-make
  [arity terms]
  (let [n (count terms)]
    (cond (zero? n) 0

          (and (= 1 n) (constant-term? (first terms)))
          (coefficient (first terms))

          :else (->Polynomial arity terms))))

(defn make
  "When called with two arguments, the first is the arity
  (number of indeterminates) of the polynomial followed by a sequence of
  exponent-coefficient pairs. Each exponent should be a vector with length equal
  to the arity, with integer exponent values. To make 4 x^2 y + 5 x y^2, an
  arity 2 polynomial (since it has two variables, x and y), we could write the
  following for xc-pairs:
   [[[2 1] 4] [[1 2] 5]]

  When called with one argument, the sequence is interpreted as a dense sequence
  of coefficients of an arity-1 (univariate) polynomial. The coefficients begin
  with the constant term and proceed to each higher power of the indeterminate.
  For example, x^2 - 1 can be constructed by (make [-1 0 1]).

  TODO note that we now return a coefficient for constant, even if they sum to a
  constant. We try hard to get OUT of poly land!

  TODO note that we have to have ALL the same arity!

  TODO ALSO check that this is bailing out correctly."
  ([dense-coefficients]
   (let [terms (map-indexed (fn [i coef]
                              (make-term [i] coef))
                            dense-coefficients)]
     (make 1 terms)))
  ([arity expts->coef]
   (if (empty? expts->coef)
     0
     (let [terms (->> (for [[expts terms] (group-by exponents expts->coef)
                            :let [coef-sum (transduce
                                            (map coefficient) g/+ terms)]
                            :when (not (v/zero? coef-sum))]
                        [expts coef-sum])
                      (sort-by exponents monomial-order)
                      (into empty-terms))]
       (guarded-make arity terms)))))

;; ## Polynomial API

(def poly:identity
  (make 1 [(make-term [1] 1)]))

(defn check-same-arity
  "TODO works now for constants, check!"
  [p q]
  (let [ap (arity p)
        aq (arity q)]
    (if (= ap aq)
      ap
      (u/arithmetic-ex "mismatched polynomial arity"))))

(defn new-variables
  "TODO NOTE: returns a sequence of `n` new polynomials of arity `n`, with the
  coefficient 1 and new indeterminates for each."
  [n]
  (map (fn [i]
         (make n [(make-term
                   (mapv (fn [j] (if (= i j) 1 0))
                         (range n))
		               1)]))
       (range n)))

(defn map-coefficients
  "Map the function f over the coefficients of p, returning a new Polynomial.

  TODO this demotes to coefficient when it needs to, and can take a bare coef."
  [f p]
  (if (coeff? p)
    (f p)
    (guarded-make (bare-arity p)
                  (into empty-terms
                        (for [[xs c] (bare-terms p)
                              :let [fc (f c)]
                              :when (not (v/zero? fc))]
                          [xs fc])))))

(defn map-exponents
  "Map the function f over the exponents of each monomial in p,
  returning a new Polynomial.

  TODO can handle bare coef now."
  [f p]
  (if (coeff? p)
    p
    (make (bare-arity p)
          (for [term (bare-terms p)]
            (make-term
             (f (exponents term))
             (coefficient term))))))

;; ## Manipulations

(defn poly:extend
  "TODO interpolate a new variable in the `n` spot by expanding all vectors."
  [p n]
  )

(defn contract [p n])
(defn contractible? [p n])

(comment
  (define (poly/contract n p)
    (if (poly/contractable? n p)
      (let ((arity (poly/arity p)))
	      (if (fix:= n 0)
	        (poly/trailing-coefficient p)
	        (let lp ((p p))
	             (cond ((poly/zero? p) p)
		                 (else
		                  (poly/adjoin (fix:- arity 1)
				                           (poly/degree p)
				                           (poly/contract (fix:- n 1)
				                                          (poly/leading-coefficient p))
				                           (lp
				                            (poly/except-leading-term arity p))))))))
      (error "Poly not contractable" n p)))

  (define (poly/contractable? n p)
    (or (base? p)
        (if (fix:= n 0)
	        (fix:= (poly/degree p) 0)
          (and (fix:< n (poly/arity p))
	             (let lp ((p p))
		                (cond ((poly/zero? p) true)
		                      ((poly/contractable?
                            (fix:- n 1)
					                  (poly/leading-coefficient p))
			                     (poly/contractable?
                            n
			                      (poly/except-leading-term (poly/arity p) p)))
		                      (else false))))))))


(defn normalize
  "Note that we can take coefs on left too..."
  [p c]
  {:pre [(polynomial? p)
         (base? c)]}
  (cond (v/zero? c) (u/arithmetic-ex (str "Divide by zero: " p c))
        (v/one? c) p
        :else
        (let [c' (g/invert c)]
          (map-coefficients #(g/* c' %) p))))

;; TODO
(defn scale [p c]
  )

;; TODO
(defn arg-shift [p c]
  )

;; ## Polynomial Arithmetic

(defn negate [p]
  (map-coefficients g/negate p))


(defn- binary-combine [l r coeff-op terms-op opname]
  (letfn [(wta []
            (u/illegal (str "Wrong type argument for " opname " : "
                            l ", " r)))]
    (if (coeff? l)
      (if (coeff? r)
        (coeff-op l r)
        (if (explicit-polynomial? r)
          (let [l-poly (make-constant (bare-arity r) l)]
            (make (bare-arity r)
                  (terms-op (bare-terms l-poly)
                            (bare-terms r))))
          (wta)))
      (if (coeff? r)
        (if (explicit-polynomial? l)
	        (let [r-poly (make-constant (bare-arity l) r)]
            (make (bare-arity l)
	                (terms-op (bare-terms l)
			                      (bare-terms r-poly))))
	        (wta))
        (if (and (explicit-polynomial? l)
		             (explicit-polynomial? r))
	        (make (check-same-arity l r)
                (terms-op (bare-terms l)
                          (bare-terms r)))
	        (wta))))))

(defn poly:+
  "Adds the polynomials p and q"
  [p q]
  (binary-combine p q g/+ concat '+))

(defn poly:-
  "Subtract the polynomial q from the polynomial p."
  [p q]
  (poly:+ p (negate q)))

(defn- mul-terms [l r]
  (for [[l-expts l-coef] l
        [r-expts r-coef] r]
    (make-term (g/+ l-expts r-expts)
               (g/* l-coef r-coef))))

(defn poly:*
  "Multiply polynomials p and q, and return the product."
  [p q]
  (binary-combine p q g/* mul-terms '*))

(defn expt
  "Raise the polynomial p to the (integer) power n."
  [p n]
  (letfn [(expt-iter [x n answer]
            (cond (zero? n) answer
                  (even? n) (recur (poly:* x x) (quot n 2) answer)
                  :else     (recur x (dec n) (poly:* x answer))))]
    (cond (coeff? p)  (g/expt p n)

          (not (explicit-polynomial? p))
          (u/illegal "Wrong type :" p)

          (not (v/native-integral? n))
          (u/illegal (str "Can only raise an FPF to an exact integer power: " p n))

          (neg? n)
          (u/illegal (str "No inverse -- FPF:EXPT:" p n))

          (v/one? p)  p
          (v/zero? p) (if (v/zero? n)
                        (u/arithmetic-ex "poly 0^0")
                        p)

          :else (expt-iter p n 1))))

;; TODO go from here! divide, then horner-eval, get those working (raise and
;; lower come along for the ride).
;;
;; then lock in to and from expressions... that covers fpf if that's all done.
;;
;; TODO oh! get accumulation going so that all this stuff actually works. That
;; will be a nice PR for itself.
;;
;; TODO implement more protocols, like IFn for SURE.
;;
;; TODO to power series, for arity == 1...
;;
;; TODO monic?
;;
;; TODO put `abs` back in! weird, it is `poly/abs`...
;;
;; TODO make proper equality method... use v/=
;;
;;
;; TODO get notes from pcf, poly/div
(defn divide
  "Divide polynomial u by v, and return the pair of [quotient, remainder]
  polynomials.

  This assumes that the coefficients are drawn from a field, and so support
  division."
  [u v]
  {:pre [(polynomial? u)
         (polynomial? v)]}
  (cond (v/zero? v) (u/illegal "internal polynomial division by zero")
        (v/zero? u) [u u]
        (v/one? v) [u (v/zero-like u)]
        :else (let [arity (check-same-arity u v)
                    [vn-exponents vn-coefficient] (lead-term v)
                    good? (fn [residues]
                            (and (not-empty residues)
                                 (every? (complement neg?) residues)))]
                (if (zero? arity)
                  [(make 0 [[[] (g/divide (coefficient (lead-term u)) vn-coefficient)]])
                   (make 0 [[[] 0]])]
                  (loop [quotient (make arity [])
                         remainder u]
                    ;; find a term in the remainder into which the
                    ;; lead term of the divisor can be divided.
                    (let [[r-exponents r-coefficient] (lead-term remainder)
                          residues (mapv g/- r-exponents vn-exponents)]
                      (if (good? residues)
                        (let [new-coefficient (g/divide r-coefficient vn-coefficient)
                              new-term (make arity [[residues new-coefficient]])]
                          (recur (poly:+ quotient new-term)
                                 (poly:- remainder (poly:* new-term v))))
                        [quotient remainder])))))))

(defn evenly-divide
  "Divides the polynomial u by the polynomial v. Throws an IllegalStateException
  if the division leaves a remainder. Otherwise returns the quotient."
  [u v]
  {:pre [(polynomial? u)
         (polynomial? v)]}
  (let [[q r] (divide u v)]
    (when-not (v/zero? r)
      (u/illegal-state
       (str "expected even division left a remainder!" u " / " v " r " r)))
    q))

(defn lower-arity
  "Given a nonzero polynomial of arity A > 1, return an equivalent polynomial
  of arity 1 whose coefficients are polynomials of arity A-1."
  [p]
  {:pre [(explicit-polynomial? p)
         (> (bare-arity p) 1)
         (not (v/zero? p))]}
  ;; XXX observation:
  ;; XXX we often create polynomials of "one lower arity"
  ;; which are EFFECTIVELY UNIVARIATE. When this happens,
  ;; we should notice.
  ;; (but univariate in which variable? is it really that
  ;; common that it's the first one?)
  (let [A (bare-arity p)]
    (->> (bare-terms p)
         (group-by #(first (exponents %)))
         (map (fn [[x cs]]
                [[x] (make (dec A) (for [[xs c] cs]
                                     [(subvec xs 1) c]))]))
         (make 1))))

(defn raise-arity
  "The opposite of lower-arity. This needs a polynomial with terms that are
  THEMSELVES coefficients."
  [p]
  {:pre [(explicit-polynomial? p)
         (= (bare-arity p) 1)]}
  (let [terms (for [[x q]  (bare-terms p)
                    [ys c] (bare-terms q)]
                [(into x ys) c])
        ltc (coefficient (lead-term p))]
    (make (inc (bare-arity ltc)) terms)))

(defn- evaluate-1
  "Evaluates a univariate polynomial p at x."
  [p x]
  (loop [xs->c (bare-terms p)
         result 0
         x**e 1
         e 0]
    (if-let [[[e'] c] (first xs->c)]
      (let [x**e' (g/* x**e (g/expt x (g/- e' e)))]
        (recur (next xs->c)
               (g/+ result (g/* c x**e'))
               x**e'
               e'))
      result)))

(defn evaluate
  "Evaluates a multivariate polynomial p at xs."
  [p xs]
  (cond (coeff? p)  p
        (empty? xs) p
        (v/zero? p) 0
        (= (arity p) 1) (evaluate-1 p (first xs))
        :else (let [L (evaluate-1 (lower-arity p) (first xs))]
                (if (polynomial? L)
                  (recur L (next xs))
                  L))))

;; Pseudo division produces only a remainder--no quotient.
;;  This can be used to generalize Euclid's algorithm for polynomials
;;  over a unique factorization domain (UFD).
;;
;; This implementation differs from Knuth's Algorithm R in that
;; Knuth's contributes to the integerizing factor, making it
;; l(v)^(m-n+1), even though no factor of l(v) is needed if a u_j is
;; zero for some n<j<m.  This matters a great deal in the
;; multivariate case.
;;
;; Sussman's code -- good for Euclid Algorithm

(defn pseudo-remainder
  "Compute the pseudo-remainder of univariate polynomials p and
  q.

  Fractions won't appear in the result; instead the divisor is multiplied by the
  leading coefficient of the dividend before quotient terms are generated so
  that division will not result in fractions. Only the remainder is returned,
  together with the integerizing factor needed to make this happen. Similar in
  spirit to Knuth's algorithm 4.6.1R, except we don't multiply the remainder
  through during gaps in the remainder. Since you don't know up front how many
  times the integerizing multiplication will be done, we also return the number
  d for which d * u = q * v + r."
  [u v]
  {:pre [(polynomial? u)
         (polynomial? v)
         (not (v/zero? v))
         (= (bare-arity u) (bare-arity v) 1)]}
  (let [a (check-same-arity u v)
        [vn-exponents vn-coefficient] (lead-term v)
        *vn (fn [p] (map-coefficients #(g/* vn-coefficient %) p))
        n (reduce g/+ vn-exponents)]
    (loop [remainder u d -1]
      (let [m (degree remainder)
            c (coefficient
               (lead-term remainder))]
        (if (< m n)
          [remainder d]
          (recur (poly:- (*vn remainder)
                         (poly:* (make-c*xn a c (g/- m n))
                                 v))
                 (inc d)))))))

(defn partial-derivative
  "The partial derivative of the polynomial with respect to the
  i-th indeterminate."
  [p i]
  (if (base? p)
    0
    (make (bare-arity p)
          (for [[xs c] (bare-terms p)
                :let [xi (xs i)]
                :when (not= 0 xi)]
            [(update xs i dec) (g/* xi c)]))))

(defn partial-derivatives
  "The sequence of partial derivatives of p with respect to each
  indeterminate"
  [p]
  (if (v/number? p)
    [0]
    (for [i (range (bare-arity p))]
      (partial-derivative p i))))

;; ## Canonicalizer

;; The operator-table represents the operations that can be understood
;; from the point of view of a polynomial over a commutative ring. The
;; functions take polynomial inputs and return polynomials.

(def ^:private operator-table
  {'+ #(reduce g/add %&)
   '- (fn [arg & args]
        (if (some? args)
          (g/sub arg (reduce g/add args))
          (g/negate arg)))
   '* #(reduce g/mul %&)
   'negate negate
   'expt g/expt
   'square #(mul % %)
   'cube #(mul % (mul % %))})

(def ^:private operators-known
  (into #{} (keys operator-table)))

(deftype PolynomialAnalyzer []
  a/ICanonicalize
  (expression-> [this expr cont]
    (a/expression-> this expr cont compare))

  (expression-> [this expr cont v-compare]
    ;; Convert an expression into Flat Polynomial canonical form. The expression
    ;; should be an unwrapped expression, i.e., not an instance of the
    ;; Literal type, nor should subexpressions contain type information. This
    ;; kind of simplification proceeds purely symbolically over the known Flat
    ;; Polynomial operations; other operations outside the arithmetic available
    ;; in polynomials over commutative rings should be factored out by an
    ;; expression analyzer before we get here. The result is a Polynomial object
    ;; representing the polynomial structure of the input over the unknowns.
    (let [expression-vars (sort v-compare (set/difference (x/variables-in expr) operators-known))
          sym->var        (zipmap expression-vars (a/new-variables this (count expression-vars)))
          expr'           (x/evaluate expr sym->var operator-table)]
      (cont expr' expression-vars)))

  (->expression [this p vars]
    ;; This is the output stage of Flat Polynomial canonical form
    ;; simplification. The input is a Polynomial object, and the output is an
    ;; expression representing the evaluation of that polynomial over the
    ;; indeterminates extracted from the expression at the start of this
    ;; process.
    (let [*    (sym/symbolic-operator '*)
          +    (sym/symbolic-operator '+)
          expt (sym/symbolic-operator 'expt)]
      (if (polynomial? p)
        (->> (bare-terms p)
             (sort-by exponents #(monomial-order %2 %1))
             (map (fn [[xs c]]
                    (->> (map (fn [exponent var]
                                (expt var exponent))
                              xs vars)
                         (reduce *)
                         (* c))))
             (reduce +))
        p)))

  (known-operation? [_ o]
    (operator-table o))

  (new-variables [_ arity]
    (for [a (range arity)]
      (make arity [[(mapv #(if (= % a) 1 0)
                          (range arity))
                    1]]))))

;; ## Generic Implementations

(defmethod g/negate [::polynomial] [a] (negate a))

(defmethod g/add [::polynomial ::polynomial] [a b] (poly:+ a b))
(defmethod g/mul [::polynomial ::polynomial] [a b] (poly:* a b))
(defmethod g/sub [::polynomial ::polynomial] [a b] (poly:- a b))

(defmethod g/exact-divide [::polynomial ::polynomial] [p q]
  (evenly-divide p q))

;; quotient, remainder... TODO search for more functions!

(defmethod g/square [::polynomial] [a] (poly:* a a))

(defmethod g/mul [::v/number ::polynomial] [c p]
  (map-coefficients #(g/* c %) p))

(defmethod g/mul [::polynomial ::v/number] [p c]
  (map-coefficients #(g/* % c) p))

(defmethod g/add [::v/number ::polynomial] [c p]
  (poly:+ (make-constant (bare-arity p) c) p))

(defmethod g/add [::polynomial ::v/number] [p c]
  (poly:+ p (make-constant (bare-arity p) c)))

(defmethod g/sub [::v/number ::polynomial] [c p]
  (poly:- (make-constant (bare-arity p) c) p))

(defmethod g/sub [::polynomial ::v/number] [p c]
  (poly:- p (make-constant (bare-arity p) c)))

(defmethod g/div [::polynomial ::v/number] [p c]
  (map-coefficients #(g/divide % c) p))

(defmethod g/expt [::polynomial ::v/native-integral] [b x] (expt b x))
