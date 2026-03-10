#!/usr/bin/env janet

(import ./src/frontend/sexpr/parser :as p)
(import ./src/frontend/sexpr/lower :as l)
(import ./src/frontend/surface/parser :as sp)
(import ./src/elab :as e)

(defn decl/summary [decl]
  (match decl
    [:decl/data name _ _ ctors]
    (string "data " name " (" (length ctors) " constructor(s))")
    [:decl/func name params _ clauses]
    (string "def " name " (" (length params) " param(s), " (length clauses) " clause(s))")
    [:decl/record header entries]
    (string "record " header " (" (length entries) " entry(ies))")
    _
    (string "unknown declaration: " decl)))

(defn- surface-file? [path]
  (string/has-suffix? ".requiem" path))

(defn run/file-surface [path]
  (def start (os/clock))
  (def src (string (slurp path)))
  (print "Parsing (surface) " path "...")
  (def prog (sp/parse/program src))
  (def lowered (sp/lower/program prog))
  (print "Lowered declarations: " (length lowered))
  (each decl lowered
    (print "  - " (decl/summary decl)))
  (def core (e/elab/program lowered))
  (print "Elaborated core declarations: " (length core))
  (def elapsed (- (os/clock) start))
  (printf "Done. %d declaration(s) in %.3fs" (length lowered) elapsed))

(defn run/file-sexpr [path]
  (def start (os/clock))
  (def src (slurp path))
  (print "Parsing (sexpr) " path "...")
  (def forms (p/parse/text src))
  (def interactions (length forms))
  (print "Parsed " interactions " interaction(s)")
  (def lowered (l/lower/program forms))
  (print "Lowered declarations: " (length lowered))
  (each decl lowered
    (print "  - " (decl/summary decl)))
  (def core (e/elab/program lowered))
  (print "Elaborated core declarations: " (length core))
  (def elapsed (- (os/clock) start))
  (printf "Done. %d interaction(s) in %.3fs" interactions elapsed))

(defn run/file [path]
  (if (surface-file? path)
    (run/file-surface path)
    (run/file-sexpr path)))

(defn main [& args]
  (def n (length args))
  (if (zero? n)
    (do
      (print "Usage: requiem <file.requiem>")
      (os/exit 1))
    (run/file (args (- n 1)))))
