(lang dune 3.22)
(using rocq 0.11)

(name picinae-rocq)

(generate_opam_files true)

(source
 (github CharlesAverill/Picinae))

(authors
 "Kevin W. Hamlen <hamlen@utdallas.edu>"
 "Charles Averill <charles@utdallas.edu>"
 "Ilan Buzzetti <ixb140230@utdallas.edu>")

(maintainers
 "Kevin W. Hamlen <hamlen@utdallas.edu>"
 "Charles Averill <charles@utdallas.edu>"
 "Ilan Buzzetti <ixb140230@utdallas.edu>")

(license GPL-3.0)

(documentation https://github.com/CharlesAverill/Picinae)

(package
 (name picinae-rocq)
 (synopsis "Platform In Coq for INstruction-level Analysis of Executables")
 (description "A formal program analysis tool for stripped binary code")
 (depends
   (dune (>= 3.20.1))
   (rocq (= 9.1.1))))

(package
  (name picinae-examples)
  (synopsis "A set of example proofs using picinae-rocq")
  (depends picinae-rocq))
