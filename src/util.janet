#!/usr/bin/env janet

(defn find-index [pred xs]
  (defn find-iter [i xs]
    (if (empty? xs)
      nil
      (if (pred (first xs))
        i
        (find-iter (+ i 1) (slice xs 1)))))
  (find-iter 0 xs))

(defn seq/contains? [xs x]
  (not (nil? (find-index |(= $ x) xs))))

(def exports
  {:find-index find-index
   :seq/contains? seq/contains?})
