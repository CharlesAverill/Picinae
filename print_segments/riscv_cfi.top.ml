#require "bap";;
#require "ppx_let"
#require "bap-elf";;
#require "bap.top";;
#load_rec "elf_write.cmo";;
#load_rec "policy.cmo";;
#load_rec "extraction.cmo";;

open Core_extend
open Bap_elf
open Bap.Std
open Bap_main

module Unix = UnixLabels;;

