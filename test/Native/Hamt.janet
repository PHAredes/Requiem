(import ../../build/hamt :as h)
(import ../Utils/TestRunner :as test)
(import ../../src/coreTT :as c)
(import ../Utils/Generators :as gen)

(def suite (test/start-suite "Native HAMT"))

# Basic Operations

(def h0 (h/new))

(test/assert suite (= (h/len h0) 0) "New HAMT has length 0")
(test/assert suite (nil? (h/get h0 "a")) "Get on empty returns nil")

(def h1 (h/put h0 "a" 10))
(test/assert suite (= (h/len h1) 1) "Length increases after put")
(test/assert suite (= (h/get h1 "a") 10) "Can get inserted value")
(test/assert suite (= (h/len h0) 0) "Original HAMT unchanged (persistence)")
(test/assert suite (nil? (h/get h0 "a")) "Original HAMT doesn't have key")

(def h2 (h/put h1 "b" 20))
(test/assert suite (= (h/len h2) 2) "Length 2")
(test/assert suite (= (h/get h2 "a") 10) "Key 'a' preserved")
(test/assert suite (= (h/get h2 "b") 20) "Key 'b' accessible")

# Shadowing (Updates)

(def h3 (h/put h2 "a" 99))
(test/assert suite (= (h/len h3) 2) "Length constant on update")
(test/assert suite (= (h/get h3 "a") 99) "New value for 'a'")
(test/assert suite (= (h/get h2 "a") 10) "Old HAMT preserves old value")

# Keys & Table Conversion

(def ks (h/keys h2))
(test/assert suite (= (length ks) 2) "Keys array length")
(test/assert suite (not (nil? (find |(= $ "a") ks))) "Contains 'a'")
(test/assert suite (not (nil? (find |(= $ "b") ks))) "Contains 'b'")

(def t (h/to-table h2))
(test/assert suite (= (t "a") 10) "Table conversion 'a'")
(test/assert suite (= (t "b") 20) "Table conversion 'b'")

# Large Scale & Collisions

(var hl (h/new))
(def N 1000)
(for i 0 N
  (set hl (h/put hl (string i) i)))

(test/assert suite (= (h/len hl) N) "Large scale length correct")
(test/assert suite (= (h/get hl "0") 0) "First element")
(test/assert suite (= (h/get hl "500") 500) "Middle element")
(test/assert suite (= (h/get hl "999") 999) "Last element")
(test/assert suite (nil? (h/get hl "1000")) "Out of bounds nil")

# Force collisions (hash is complex to force, but large N helps coverage)
# We rely on the large dataset to trigger splitting nodes

(defn hamt/stress-semantic-values [seed rounds]
  (let [rng (gen/rng seed)]
    (var ok true)
    (var i 0)
    (while (and ok (< i rounds))
      (let [sample (gen/gen-inferable-judgment rng)]
        (try
          (c/infer (sample :ctx) (sample :term))
          ([err]
            (set ok false)
            (print "HAMT semantic-value corruption:")
            (print "  seed =" seed)
            (print "  round =" i)
            (print "  kind =" (sample :kind))
            (print "  err =" err))))
      (++ i))
    ok))

(test/assert suite
  (hamt/stress-semantic-values "3" 3000)
  "HAMT retains semantic values across GC pressure")

(test/end-suite suite)
