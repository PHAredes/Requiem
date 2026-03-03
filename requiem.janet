#!/usr/bin/env janet

(import ./src/parser :as p)
(import ./src/desugar :as d)
(import ./src/elaborate :as e)

(defn decl/summary [decl]
  (match decl
    [:decl/data name _ _ ctors]
    (string "data " name " (" (length ctors) " constructor(s))")
    [:decl/func name params _ clauses]
    (string "def " name " (" (length params) " param(s), " (length clauses) " clause(s))")
    _
    (string "unknown declaration: " decl)))

(defn run/file [path]
  (def start (os/clock))
  (def src (slurp path))
  (print "Parsing " path "...")
  (def forms (p/parse/text src))
  (def interactions (length forms))
  (print "Parsed " interactions " interaction(s)")
  (def tesla (d/desugar/program forms))
  (print "Desugared to Tesla-style declarations: " (length tesla))
  (each decl tesla
    (print "  - " (decl/summary decl)))
  (def core (e/elaborate/program tesla))
  (print "Elaborated core declarations: " (length core))
  (def elapsed (- (os/clock) start))
  (printf "Done. %d interaction(s) in %.3fs" interactions elapsed))

(defn main [& args]
  (def n (length args))
  (if (zero? n)
    (do
      (print "Usage: requiem <file.requiem>")
      (os/exit 1))
    (run/file (args (- n 1)))))
