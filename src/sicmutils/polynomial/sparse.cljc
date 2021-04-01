;;
;; Copyright © 2021 Sam Ritchie.
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

(ns sicmutils.polynomial.sparse
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

;; TODO: redo everything on JUST the term arithmetic, and call this `sparse.`
