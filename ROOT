(* Optional batch-checking session.  Normal editing opens LF_All.thy directly
   from HOL, so no Lemmon_Fitch heap is selected and every theory stays editable. *)

session Lemmon_Fitch = HOL +
  options [document = false]
  sessions "HOL-Library"
  theories
    LF_All
  export_files (in "generated") [2] "*:code/**"
