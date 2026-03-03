#!/usr/bin/env janet

(import ./src/parser :as p)
(import ./src/surface :as s)
(import ./src/elab :as e)

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
  (def lowered (s/lower/program forms))
  (print "Lowered surface declarations: " (length lowered))
  (each decl lowered
    (print "  - " (decl/summary decl)))
  (def core (e/elab/program lowered))
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
