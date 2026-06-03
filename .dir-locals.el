;; Build with `dune build` first; this points Proof General / coqtop at the
;; dune output so `Require` resolves the compiled theory.
((coq-mode . ((coq-prog-args . ("-emacs" "-R" "_build/default" "NI")))))
