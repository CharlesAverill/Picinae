(lang dune 3.20)
(using coq 0.10)

(name rocq-picinae)

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
 (name rocq-picinae)
 (synopsis "Platform In Coq for INstruction-level Analysis of Executables")
 (description "A formal program analysis tool for stripped binary code")
 (depends
   (dune (>= 3.20.1))
   (coq (= 8.19.1))))

