(declare-project
  :name "requiem"
  :description "Requiem: A minimal dependently-typed language core")

(declare-native
  :name "timer"
  :source @["native/timer.c"])

(declare-native
  :name "hamt"
  :source @["native/hamt.c"])
