(import ../../build/hamt :as h)
(import ../Utils/TestRunner :as test)

(test/start-suite "Native HAMT")

# Basic Operations

(def h0 (h/new))

(test/assert (= (h/len h0) 0) "New HAMT has length 0")
(test/assert (nil? (h/get h0 "a")) "Get on empty returns nil")

(def h1 (h/put h0 "a" 10))
(test/assert (= (h/len h1) 1) "Length increases after put")
(test/assert (= (h/get h1 "a") 10) "Can get inserted value")
(test/assert (= (h/len h0) 0) "Original HAMT unchanged (persistence)")
(test/assert (nil? (h/get h0 "a")) "Original HAMT doesn't have key")

(def h2 (h/put h1 "b" 20))
(test/assert (= (h/len h2) 2) "Length 2")
(test/assert (= (h/get h2 "a") 10) "Key 'a' preserved")
(test/assert (= (h/get h2 "b") 20) "Key 'b' accessible")

# Shadowing (Updates)

(def h3 (h/put h2 "a" 99))
(test/assert (= (h/len h3) 2) "Length constant on update")
(test/assert (= (h/get h3 "a") 99) "New value for 'a'")
(test/assert (= (h/get h2 "a") 10) "Old HAMT preserves old value")

# Keys & Table Conversion

(def ks (h/keys h2))
(test/assert (= (length ks) 2) "Keys array length")
(test/assert (not (nil? (find |(= $ "a") ks))) "Contains 'a'")
(test/assert (not (nil? (find |(= $ "b") ks))) "Contains 'b'")

(def t (h/to-table h2))
(test/assert (= (t "a") 10) "Table conversion 'a'")
(test/assert (= (t "b") 20) "Table conversion 'b'")

# Large Scale & Collisions

(var hl (h/new))
(def N 1000)
(for i 0 N
  (set hl (h/put hl (string i) i)))

(test/assert (= (h/len hl) N) "Large scale length correct")
(test/assert (= (h/get hl "0") 0) "First element")
(test/assert (= (h/get hl "500") 500) "Middle element")
(test/assert (= (h/get hl "999") 999) "Last element")
(test/assert (nil? (h/get hl "1000")) "Out of bounds nil")

# Force collisions (hash is complex to force, but large N helps coverage)
# We rely on the large dataset to trigger splitting nodes

(test/end-suite)
