(declare-project
  :name "context-bench"
  :description "Benchmarks for Context Data Structures")

(declare-native
  :name "timer"
  :source @["native/timer.c"])

(declare-native
  :name "hamt"
  :source @["native/hamt.c"])
