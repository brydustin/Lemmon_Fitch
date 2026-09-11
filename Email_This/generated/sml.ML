structure Str_Literal : sig
  type int = IntInf.int
  val literal_of_asciis : int list -> string
  val asciis_of_literal : string -> int list
end = struct

open IntInf;

fun map f [] = []
  | map f (x :: xs) = f x :: map f xs; (* deliberate clone not relying on List._ structure *)

fun check_ascii k =
  if 0 <= k andalso k < 128
  then k
  else raise Fail "Non-ASCII character in literal";

val char_of_ascii = Char.chr o toInt o (fn k => k mod 128);

val ascii_of_char = check_ascii o fromInt o Char.ord;

val literal_of_asciis = String.implode o map char_of_ascii;

val asciis_of_literal = map ascii_of_char o String.explode;

end;

structure LemmonFitch : sig
  type int
  type 'a equal
  type nat
  type trm
  type fm
  type just
  type num
  type hl_term
  type hl_formula
  type 'a set
  type ('a, 'b) sum
  type fitch_rule
  type fline
  type hl_justification
  type hl_line
  type pline
  type route
  type subproof
  type fitch_item
  type deriv
  type drule
  type hl_route
  type hl_fitch_rule
  type hl_subproof
  type hl_fitch_item
  type translation_error
  type hl_derivation
  type hl_derivation_rule
  type 'a hl_finite_model
  type hl_translation_error
  val hlRuleOK : hl_line list -> hl_line -> bool
  val hlLineOK : hl_line list -> hl_line -> bool
  val fitchWF : fitch_item list -> bool
  val hlCorrect : hl_line list -> bool
  val ruleOK : pline list -> fm -> fm list -> just -> bool
  val delta : fitch_item list -> pline list
  val derivationToFitch : deriv -> fitch_item list
  val lemmonCorrect : pline list -> bool
  val toDerivation : pline list -> (translation_error, deriv) sum
  val viaTree : pline list -> (translation_error, (route * fitch_item list)) sum
  val recompute : (nat * (fm * just)) list -> pline list
  val stripDeps : pline list -> (nat * (fm * just)) list
  val hlIsPropositional : hl_formula -> bool
  val hlToNNF : hl_formula -> hl_formula
  val hlToDNF : hl_formula -> hl_formula option
  val hlConclusion : hl_line list -> hl_formula option
  val showError : translation_error -> string
  val showFitch : fitch_item list -> string list
  val scopeError : pline list -> translation_error option
  val showLemmon : pline list -> string list
  val fitchCorrect : fitch_item list -> bool
  val hlOpenPremises : hl_line list -> hl_formula list
  val fitchToLemmon : fitch_item list -> pline list
  val boxHeadError : pline list -> translation_error option
  val nestingError : pline list -> translation_error option
  val premiseError : pline list -> translation_error option
  val renumberJust : (nat -> nat) -> just -> just
  val relabel : (nat -> nat) -> pline -> pline
  val boxOrderError : pline list -> translation_error option
  val subScopeError : pline list -> translation_error option
  val hlDerivationToFitch : hl_derivation -> hl_fitch_item list
  val hlVerifiedCorrect : hl_line list -> bool
  val hlToDerivation : hl_line list -> hl_derivation option
  val hlFitchToLemmon : hl_fitch_item list -> hl_line list
  val hlFitchPremises : hl_fitch_item list -> hl_formula list
  val hlConcludesAtTop : hl_fitch_item list -> bool
  val hlFitchNestedWellFormed : hl_fitch_item list -> bool
  val hlFitchPremiseClosed : hl_fitch_item list -> bool
  val hlFitchWellFormed : hl_fitch_item list -> bool
  val hlFitchVerified : hl_fitch_item list -> bool
  val hlFitchCorrect : hl_fitch_item list -> bool
  val hlViaTree :
    hl_line list -> (hl_translation_error, (hl_route * hl_fitch_item list)) sum
  val premiseOrderError : pline list -> translation_error option
  val lemmonToFitchDirect :
    pline list -> (translation_error, (fitch_item list)) sum
  val lemmonToFitch :
    pline list -> (translation_error, (route * fitch_item list)) sum
  val fitchWellFormed : fitch_item list -> string option
  val showTranslation :
    (translation_error, (route * fitch_item list)) sum -> string list
  val dependents : pline list -> nat -> nat list
  val ruleMatches : just -> fitch_rule -> bool
  val lineMatches : fline -> pline -> bool
  val fitchImage : fitch_item list -> pline list -> bool
  val permuteProof : (nat -> nat) -> pline list -> pline list
  val noDuplication : fitch_item list -> pline list -> bool
  val sourceCovered : fitch_item list -> pline list -> bool
  val hlFiniteEval :
    'a equal ->
      'a hl_finite_model -> (string * 'a) list -> hl_formula -> bool option
  val hlLemmonToFitchDirect :
    hl_line list -> (hl_translation_error, (hl_fitch_item list)) sum
  val hlLemmonToFitch :
    hl_line list -> (hl_translation_error, (hl_route * hl_fitch_item list)) sum
  val hlFitchConclusion : hl_fitch_item list -> hl_formula option
  val lemmonToFitchChecked :
    pline list -> (translation_error, (route * fitch_item list)) sum
  val positionalImage : fitch_item list -> pline list -> bool
  val hlCanonicalDependencies : hl_line list -> bool
  val hlPaperCorrect : hl_line list -> bool
  val hlFiniteEvalClosed :
    'a equal -> 'a hl_finite_model -> hl_formula -> bool option
  val hlStripDependencies :
    hl_line list -> (int * (hl_formula * hl_justification)) list
  val hlLemmonToFitchChecked :
    hl_line list -> (hl_translation_error, (hl_route * hl_fitch_item list)) sum
  val hlRecomputeDependencies :
    (int * (hl_formula * hl_justification)) list -> hl_line list
  val hlFiniteStandardEquality : 'a equal -> 'a hl_finite_model -> bool
end = struct

datatype int = Int_of_integer of IntInf.int;

fun integer_of_int (Int_of_integer k) = k;

fun equal_inta k l = (((integer_of_int k) : IntInf.int) = (integer_of_int l));

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_int = {equal = equal_inta} : int equal;

fun less_eq_int k l = IntInf.<= (integer_of_int k, integer_of_int l);

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun less_int k l = IntInf.< (integer_of_int k, integer_of_int l);

val ord_int = {less_eq = less_eq_int, less = less_int} : int ord;

type 'a preorder = {ord_preorder : 'a ord};
val ord_preorder = #ord_preorder : 'a preorder -> 'a ord;

type 'a order = {preorder_order : 'a preorder};
val preorder_order = #preorder_order : 'a order -> 'a preorder;

val preorder_int = {ord_preorder = ord_int} : int preorder;

val order_int = {preorder_order = preorder_int} : int order;

type 'a linorder = {order_linorder : 'a order};
val order_linorder = #order_linorder : 'a linorder -> 'a order;

val linorder_int = {order_linorder = order_int} : int linorder;

datatype nat = Nat of IntInf.int;

fun integer_of_nat (Nat x) = x;

fun equal_nata m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

val equal_nat = {equal = equal_nata} : nat equal;

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

val ord_nat = {less_eq = less_eq_nat, less = less_nat} : nat ord;

val preorder_nat = {ord_preorder = ord_nat} : nat preorder;

val order_nat = {preorder_order = preorder_nat} : nat order;

val linorder_nat = {order_linorder = order_nat} : nat linorder;

fun eq A_ a b = equal A_ a b;

fun equal_lista A_ [] (x21 :: x22) = false
  | equal_lista A_ (x21 :: x22) [] = false
  | equal_lista A_ (x21 :: x22) (y21 :: y22) =
    eq A_ x21 y21 andalso equal_lista A_ x22 y22
  | equal_lista A_ [] [] = true;

fun equal_list A_ = {equal = equal_lista A_} : ('a list) equal;

datatype trm = Nm of string | Vr of string;

fun equal_trma (Nm x1) (Vr x2) = false
  | equal_trma (Vr x2) (Nm x1) = false
  | equal_trma (Vr x2) (Vr y2) = ((x2 : string) = y2)
  | equal_trma (Nm x1) (Nm y1) = ((x1 : string) = y1);

datatype fm = Atom of string * trm list | Eqf of trm * trm | Bot | Neg of fm |
  Conj of fm * fm | Disj of fm * fm | Impl of fm * fm | Iff of fm * fm |
  Uni of string * fm | Exi of string * fm;

val equal_trm = {equal = equal_trma} : trm equal;

fun equal_fma (Uni (x91, x92)) (Exi (x101, x102)) = false
  | equal_fma (Exi (x101, x102)) (Uni (x91, x92)) = false
  | equal_fma (Iff (x81, x82)) (Exi (x101, x102)) = false
  | equal_fma (Exi (x101, x102)) (Iff (x81, x82)) = false
  | equal_fma (Iff (x81, x82)) (Uni (x91, x92)) = false
  | equal_fma (Uni (x91, x92)) (Iff (x81, x82)) = false
  | equal_fma (Impl (x71, x72)) (Exi (x101, x102)) = false
  | equal_fma (Exi (x101, x102)) (Impl (x71, x72)) = false
  | equal_fma (Impl (x71, x72)) (Uni (x91, x92)) = false
  | equal_fma (Uni (x91, x92)) (Impl (x71, x72)) = false
  | equal_fma (Impl (x71, x72)) (Iff (x81, x82)) = false
  | equal_fma (Iff (x81, x82)) (Impl (x71, x72)) = false
  | equal_fma (Disj (x61, x62)) (Exi (x101, x102)) = false
  | equal_fma (Exi (x101, x102)) (Disj (x61, x62)) = false
  | equal_fma (Disj (x61, x62)) (Uni (x91, x92)) = false
  | equal_fma (Uni (x91, x92)) (Disj (x61, x62)) = false
  | equal_fma (Disj (x61, x62)) (Iff (x81, x82)) = false
  | equal_fma (Iff (x81, x82)) (Disj (x61, x62)) = false
  | equal_fma (Disj (x61, x62)) (Impl (x71, x72)) = false
  | equal_fma (Impl (x71, x72)) (Disj (x61, x62)) = false
  | equal_fma (Conj (x51, x52)) (Exi (x101, x102)) = false
  | equal_fma (Exi (x101, x102)) (Conj (x51, x52)) = false
  | equal_fma (Conj (x51, x52)) (Uni (x91, x92)) = false
  | equal_fma (Uni (x91, x92)) (Conj (x51, x52)) = false
  | equal_fma (Conj (x51, x52)) (Iff (x81, x82)) = false
  | equal_fma (Iff (x81, x82)) (Conj (x51, x52)) = false
  | equal_fma (Conj (x51, x52)) (Impl (x71, x72)) = false
  | equal_fma (Impl (x71, x72)) (Conj (x51, x52)) = false
  | equal_fma (Conj (x51, x52)) (Disj (x61, x62)) = false
  | equal_fma (Disj (x61, x62)) (Conj (x51, x52)) = false
  | equal_fma (Neg x4) (Exi (x101, x102)) = false
  | equal_fma (Exi (x101, x102)) (Neg x4) = false
  | equal_fma (Neg x4) (Uni (x91, x92)) = false
  | equal_fma (Uni (x91, x92)) (Neg x4) = false
  | equal_fma (Neg x4) (Iff (x81, x82)) = false
  | equal_fma (Iff (x81, x82)) (Neg x4) = false
  | equal_fma (Neg x4) (Impl (x71, x72)) = false
  | equal_fma (Impl (x71, x72)) (Neg x4) = false
  | equal_fma (Neg x4) (Disj (x61, x62)) = false
  | equal_fma (Disj (x61, x62)) (Neg x4) = false
  | equal_fma (Neg x4) (Conj (x51, x52)) = false
  | equal_fma (Conj (x51, x52)) (Neg x4) = false
  | equal_fma Bot (Exi (x101, x102)) = false
  | equal_fma (Exi (x101, x102)) Bot = false
  | equal_fma Bot (Uni (x91, x92)) = false
  | equal_fma (Uni (x91, x92)) Bot = false
  | equal_fma Bot (Iff (x81, x82)) = false
  | equal_fma (Iff (x81, x82)) Bot = false
  | equal_fma Bot (Impl (x71, x72)) = false
  | equal_fma (Impl (x71, x72)) Bot = false
  | equal_fma Bot (Disj (x61, x62)) = false
  | equal_fma (Disj (x61, x62)) Bot = false
  | equal_fma Bot (Conj (x51, x52)) = false
  | equal_fma (Conj (x51, x52)) Bot = false
  | equal_fma Bot (Neg x4) = false
  | equal_fma (Neg x4) Bot = false
  | equal_fma (Eqf (x21, x22)) (Exi (x101, x102)) = false
  | equal_fma (Exi (x101, x102)) (Eqf (x21, x22)) = false
  | equal_fma (Eqf (x21, x22)) (Uni (x91, x92)) = false
  | equal_fma (Uni (x91, x92)) (Eqf (x21, x22)) = false
  | equal_fma (Eqf (x21, x22)) (Iff (x81, x82)) = false
  | equal_fma (Iff (x81, x82)) (Eqf (x21, x22)) = false
  | equal_fma (Eqf (x21, x22)) (Impl (x71, x72)) = false
  | equal_fma (Impl (x71, x72)) (Eqf (x21, x22)) = false
  | equal_fma (Eqf (x21, x22)) (Disj (x61, x62)) = false
  | equal_fma (Disj (x61, x62)) (Eqf (x21, x22)) = false
  | equal_fma (Eqf (x21, x22)) (Conj (x51, x52)) = false
  | equal_fma (Conj (x51, x52)) (Eqf (x21, x22)) = false
  | equal_fma (Eqf (x21, x22)) (Neg x4) = false
  | equal_fma (Neg x4) (Eqf (x21, x22)) = false
  | equal_fma (Eqf (x21, x22)) Bot = false
  | equal_fma Bot (Eqf (x21, x22)) = false
  | equal_fma (Atom (x11, x12)) (Exi (x101, x102)) = false
  | equal_fma (Exi (x101, x102)) (Atom (x11, x12)) = false
  | equal_fma (Atom (x11, x12)) (Uni (x91, x92)) = false
  | equal_fma (Uni (x91, x92)) (Atom (x11, x12)) = false
  | equal_fma (Atom (x11, x12)) (Iff (x81, x82)) = false
  | equal_fma (Iff (x81, x82)) (Atom (x11, x12)) = false
  | equal_fma (Atom (x11, x12)) (Impl (x71, x72)) = false
  | equal_fma (Impl (x71, x72)) (Atom (x11, x12)) = false
  | equal_fma (Atom (x11, x12)) (Disj (x61, x62)) = false
  | equal_fma (Disj (x61, x62)) (Atom (x11, x12)) = false
  | equal_fma (Atom (x11, x12)) (Conj (x51, x52)) = false
  | equal_fma (Conj (x51, x52)) (Atom (x11, x12)) = false
  | equal_fma (Atom (x11, x12)) (Neg x4) = false
  | equal_fma (Neg x4) (Atom (x11, x12)) = false
  | equal_fma (Atom (x11, x12)) Bot = false
  | equal_fma Bot (Atom (x11, x12)) = false
  | equal_fma (Atom (x11, x12)) (Eqf (x21, x22)) = false
  | equal_fma (Eqf (x21, x22)) (Atom (x11, x12)) = false
  | equal_fma (Exi (x101, x102)) (Exi (y101, y102)) =
    ((x101 : string) = y101) andalso equal_fma x102 y102
  | equal_fma (Uni (x91, x92)) (Uni (y91, y92)) =
    ((x91 : string) = y91) andalso equal_fma x92 y92
  | equal_fma (Iff (x81, x82)) (Iff (y81, y82)) =
    equal_fma x81 y81 andalso equal_fma x82 y82
  | equal_fma (Impl (x71, x72)) (Impl (y71, y72)) =
    equal_fma x71 y71 andalso equal_fma x72 y72
  | equal_fma (Disj (x61, x62)) (Disj (y61, y62)) =
    equal_fma x61 y61 andalso equal_fma x62 y62
  | equal_fma (Conj (x51, x52)) (Conj (y51, y52)) =
    equal_fma x51 y51 andalso equal_fma x52 y52
  | equal_fma (Neg x4) (Neg y4) = equal_fma x4 y4
  | equal_fma (Eqf (x21, x22)) (Eqf (y21, y22)) =
    equal_trma x21 y21 andalso equal_trma x22 y22
  | equal_fma (Atom (x11, x12)) (Atom (y11, y12)) =
    ((x11 : string) = y11) andalso equal_lista equal_trm x12 y12
  | equal_fma Bot Bot = true;

val equal_fm = {equal = equal_fma} : fm equal;

datatype just = Assumption | MP of nat * nat | CP of nat * nat |
  RAA of nat * nat | DN of nat | BotI of nat * nat | AndIntro of nat * nat |
  AndElimL of nat | AndElimR of nat | OrIntroL of nat | OrIntroR of nat |
  OrElim of nat * nat * nat * nat * nat | IffIntro of nat * nat |
  IffElimL of nat | IffElimR of nat | ForallElim of nat | ForallIntro of nat |
  ExistsIntro of nat | ExistsElim of nat * nat * nat | EqIntro |
  EqElim of nat * nat | Reit of nat;

fun equal_justa (EqElim (x211, x212)) (Reit x22a) = false
  | equal_justa (Reit x22a) (EqElim (x211, x212)) = false
  | equal_justa EqIntro (Reit x22a) = false
  | equal_justa (Reit x22a) EqIntro = false
  | equal_justa EqIntro (EqElim (x211, x212)) = false
  | equal_justa (EqElim (x211, x212)) EqIntro = false
  | equal_justa (ExistsElim (x191, x192, x193)) (Reit x22a) = false
  | equal_justa (Reit x22a) (ExistsElim (x191, x192, x193)) = false
  | equal_justa (ExistsElim (x191, x192, x193)) (EqElim (x211, x212)) = false
  | equal_justa (EqElim (x211, x212)) (ExistsElim (x191, x192, x193)) = false
  | equal_justa (ExistsElim (x191, x192, x193)) EqIntro = false
  | equal_justa EqIntro (ExistsElim (x191, x192, x193)) = false
  | equal_justa (ExistsIntro x18) (Reit x22a) = false
  | equal_justa (Reit x22a) (ExistsIntro x18) = false
  | equal_justa (ExistsIntro x18) (EqElim (x211, x212)) = false
  | equal_justa (EqElim (x211, x212)) (ExistsIntro x18) = false
  | equal_justa (ExistsIntro x18) EqIntro = false
  | equal_justa EqIntro (ExistsIntro x18) = false
  | equal_justa (ExistsIntro x18) (ExistsElim (x191, x192, x193)) = false
  | equal_justa (ExistsElim (x191, x192, x193)) (ExistsIntro x18) = false
  | equal_justa (ForallIntro x17) (Reit x22a) = false
  | equal_justa (Reit x22a) (ForallIntro x17) = false
  | equal_justa (ForallIntro x17) (EqElim (x211, x212)) = false
  | equal_justa (EqElim (x211, x212)) (ForallIntro x17) = false
  | equal_justa (ForallIntro x17) EqIntro = false
  | equal_justa EqIntro (ForallIntro x17) = false
  | equal_justa (ForallIntro x17) (ExistsElim (x191, x192, x193)) = false
  | equal_justa (ExistsElim (x191, x192, x193)) (ForallIntro x17) = false
  | equal_justa (ForallIntro x17) (ExistsIntro x18) = false
  | equal_justa (ExistsIntro x18) (ForallIntro x17) = false
  | equal_justa (ForallElim x16) (Reit x22a) = false
  | equal_justa (Reit x22a) (ForallElim x16) = false
  | equal_justa (ForallElim x16) (EqElim (x211, x212)) = false
  | equal_justa (EqElim (x211, x212)) (ForallElim x16) = false
  | equal_justa (ForallElim x16) EqIntro = false
  | equal_justa EqIntro (ForallElim x16) = false
  | equal_justa (ForallElim x16) (ExistsElim (x191, x192, x193)) = false
  | equal_justa (ExistsElim (x191, x192, x193)) (ForallElim x16) = false
  | equal_justa (ForallElim x16) (ExistsIntro x18) = false
  | equal_justa (ExistsIntro x18) (ForallElim x16) = false
  | equal_justa (ForallElim x16) (ForallIntro x17) = false
  | equal_justa (ForallIntro x17) (ForallElim x16) = false
  | equal_justa (IffElimR x15) (Reit x22a) = false
  | equal_justa (Reit x22a) (IffElimR x15) = false
  | equal_justa (IffElimR x15) (EqElim (x211, x212)) = false
  | equal_justa (EqElim (x211, x212)) (IffElimR x15) = false
  | equal_justa (IffElimR x15) EqIntro = false
  | equal_justa EqIntro (IffElimR x15) = false
  | equal_justa (IffElimR x15) (ExistsElim (x191, x192, x193)) = false
  | equal_justa (ExistsElim (x191, x192, x193)) (IffElimR x15) = false
  | equal_justa (IffElimR x15) (ExistsIntro x18) = false
  | equal_justa (ExistsIntro x18) (IffElimR x15) = false
  | equal_justa (IffElimR x15) (ForallIntro x17) = false
  | equal_justa (ForallIntro x17) (IffElimR x15) = false
  | equal_justa (IffElimR x15) (ForallElim x16) = false
  | equal_justa (ForallElim x16) (IffElimR x15) = false
  | equal_justa (IffElimL x14) (Reit x22a) = false
  | equal_justa (Reit x22a) (IffElimL x14) = false
  | equal_justa (IffElimL x14) (EqElim (x211, x212)) = false
  | equal_justa (EqElim (x211, x212)) (IffElimL x14) = false
  | equal_justa (IffElimL x14) EqIntro = false
  | equal_justa EqIntro (IffElimL x14) = false
  | equal_justa (IffElimL x14) (ExistsElim (x191, x192, x193)) = false
  | equal_justa (ExistsElim (x191, x192, x193)) (IffElimL x14) = false
  | equal_justa (IffElimL x14) (ExistsIntro x18) = false
  | equal_justa (ExistsIntro x18) (IffElimL x14) = false
  | equal_justa (IffElimL x14) (ForallIntro x17) = false
  | equal_justa (ForallIntro x17) (IffElimL x14) = false
  | equal_justa (IffElimL x14) (ForallElim x16) = false
  | equal_justa (ForallElim x16) (IffElimL x14) = false
  | equal_justa (IffElimL x14) (IffElimR x15) = false
  | equal_justa (IffElimR x15) (IffElimL x14) = false
  | equal_justa (IffIntro (x131, x132)) (Reit x22a) = false
  | equal_justa (Reit x22a) (IffIntro (x131, x132)) = false
  | equal_justa (IffIntro (x131, x132)) (EqElim (x211, x212)) = false
  | equal_justa (EqElim (x211, x212)) (IffIntro (x131, x132)) = false
  | equal_justa (IffIntro (x131, x132)) EqIntro = false
  | equal_justa EqIntro (IffIntro (x131, x132)) = false
  | equal_justa (IffIntro (x131, x132)) (ExistsElim (x191, x192, x193)) = false
  | equal_justa (ExistsElim (x191, x192, x193)) (IffIntro (x131, x132)) = false
  | equal_justa (IffIntro (x131, x132)) (ExistsIntro x18) = false
  | equal_justa (ExistsIntro x18) (IffIntro (x131, x132)) = false
  | equal_justa (IffIntro (x131, x132)) (ForallIntro x17) = false
  | equal_justa (ForallIntro x17) (IffIntro (x131, x132)) = false
  | equal_justa (IffIntro (x131, x132)) (ForallElim x16) = false
  | equal_justa (ForallElim x16) (IffIntro (x131, x132)) = false
  | equal_justa (IffIntro (x131, x132)) (IffElimR x15) = false
  | equal_justa (IffElimR x15) (IffIntro (x131, x132)) = false
  | equal_justa (IffIntro (x131, x132)) (IffElimL x14) = false
  | equal_justa (IffElimL x14) (IffIntro (x131, x132)) = false
  | equal_justa (OrElim (x121, x122, x123, x124, x125)) (Reit x22a) = false
  | equal_justa (Reit x22a) (OrElim (x121, x122, x123, x124, x125)) = false
  | equal_justa (OrElim (x121, x122, x123, x124, x125)) (EqElim (x211, x212)) =
    false
  | equal_justa (EqElim (x211, x212)) (OrElim (x121, x122, x123, x124, x125)) =
    false
  | equal_justa (OrElim (x121, x122, x123, x124, x125)) EqIntro = false
  | equal_justa EqIntro (OrElim (x121, x122, x123, x124, x125)) = false
  | equal_justa (OrElim (x121, x122, x123, x124, x125))
    (ExistsElim (x191, x192, x193)) = false
  | equal_justa (ExistsElim (x191, x192, x193))
    (OrElim (x121, x122, x123, x124, x125)) = false
  | equal_justa (OrElim (x121, x122, x123, x124, x125)) (ExistsIntro x18) =
    false
  | equal_justa (ExistsIntro x18) (OrElim (x121, x122, x123, x124, x125)) =
    false
  | equal_justa (OrElim (x121, x122, x123, x124, x125)) (ForallIntro x17) =
    false
  | equal_justa (ForallIntro x17) (OrElim (x121, x122, x123, x124, x125)) =
    false
  | equal_justa (OrElim (x121, x122, x123, x124, x125)) (ForallElim x16) = false
  | equal_justa (ForallElim x16) (OrElim (x121, x122, x123, x124, x125)) = false
  | equal_justa (OrElim (x121, x122, x123, x124, x125)) (IffElimR x15) = false
  | equal_justa (IffElimR x15) (OrElim (x121, x122, x123, x124, x125)) = false
  | equal_justa (OrElim (x121, x122, x123, x124, x125)) (IffElimL x14) = false
  | equal_justa (IffElimL x14) (OrElim (x121, x122, x123, x124, x125)) = false
  | equal_justa (OrElim (x121, x122, x123, x124, x125)) (IffIntro (x131, x132))
    = false
  | equal_justa (IffIntro (x131, x132)) (OrElim (x121, x122, x123, x124, x125))
    = false
  | equal_justa (OrIntroR x11) (Reit x22a) = false
  | equal_justa (Reit x22a) (OrIntroR x11) = false
  | equal_justa (OrIntroR x11) (EqElim (x211, x212)) = false
  | equal_justa (EqElim (x211, x212)) (OrIntroR x11) = false
  | equal_justa (OrIntroR x11) EqIntro = false
  | equal_justa EqIntro (OrIntroR x11) = false
  | equal_justa (OrIntroR x11) (ExistsElim (x191, x192, x193)) = false
  | equal_justa (ExistsElim (x191, x192, x193)) (OrIntroR x11) = false
  | equal_justa (OrIntroR x11) (ExistsIntro x18) = false
  | equal_justa (ExistsIntro x18) (OrIntroR x11) = false
  | equal_justa (OrIntroR x11) (ForallIntro x17) = false
  | equal_justa (ForallIntro x17) (OrIntroR x11) = false
  | equal_justa (OrIntroR x11) (ForallElim x16) = false
  | equal_justa (ForallElim x16) (OrIntroR x11) = false
  | equal_justa (OrIntroR x11) (IffElimR x15) = false
  | equal_justa (IffElimR x15) (OrIntroR x11) = false
  | equal_justa (OrIntroR x11) (IffElimL x14) = false
  | equal_justa (IffElimL x14) (OrIntroR x11) = false
  | equal_justa (OrIntroR x11) (IffIntro (x131, x132)) = false
  | equal_justa (IffIntro (x131, x132)) (OrIntroR x11) = false
  | equal_justa (OrIntroR x11) (OrElim (x121, x122, x123, x124, x125)) = false
  | equal_justa (OrElim (x121, x122, x123, x124, x125)) (OrIntroR x11) = false
  | equal_justa (OrIntroL x10) (Reit x22a) = false
  | equal_justa (Reit x22a) (OrIntroL x10) = false
  | equal_justa (OrIntroL x10) (EqElim (x211, x212)) = false
  | equal_justa (EqElim (x211, x212)) (OrIntroL x10) = false
  | equal_justa (OrIntroL x10) EqIntro = false
  | equal_justa EqIntro (OrIntroL x10) = false
  | equal_justa (OrIntroL x10) (ExistsElim (x191, x192, x193)) = false
  | equal_justa (ExistsElim (x191, x192, x193)) (OrIntroL x10) = false
  | equal_justa (OrIntroL x10) (ExistsIntro x18) = false
  | equal_justa (ExistsIntro x18) (OrIntroL x10) = false
  | equal_justa (OrIntroL x10) (ForallIntro x17) = false
  | equal_justa (ForallIntro x17) (OrIntroL x10) = false
  | equal_justa (OrIntroL x10) (ForallElim x16) = false
  | equal_justa (ForallElim x16) (OrIntroL x10) = false
  | equal_justa (OrIntroL x10) (IffElimR x15) = false
  | equal_justa (IffElimR x15) (OrIntroL x10) = false
  | equal_justa (OrIntroL x10) (IffElimL x14) = false
  | equal_justa (IffElimL x14) (OrIntroL x10) = false
  | equal_justa (OrIntroL x10) (IffIntro (x131, x132)) = false
  | equal_justa (IffIntro (x131, x132)) (OrIntroL x10) = false
  | equal_justa (OrIntroL x10) (OrElim (x121, x122, x123, x124, x125)) = false
  | equal_justa (OrElim (x121, x122, x123, x124, x125)) (OrIntroL x10) = false
  | equal_justa (OrIntroL x10) (OrIntroR x11) = false
  | equal_justa (OrIntroR x11) (OrIntroL x10) = false
  | equal_justa (AndElimR x9) (Reit x22a) = false
  | equal_justa (Reit x22a) (AndElimR x9) = false
  | equal_justa (AndElimR x9) (EqElim (x211, x212)) = false
  | equal_justa (EqElim (x211, x212)) (AndElimR x9) = false
  | equal_justa (AndElimR x9) EqIntro = false
  | equal_justa EqIntro (AndElimR x9) = false
  | equal_justa (AndElimR x9) (ExistsElim (x191, x192, x193)) = false
  | equal_justa (ExistsElim (x191, x192, x193)) (AndElimR x9) = false
  | equal_justa (AndElimR x9) (ExistsIntro x18) = false
  | equal_justa (ExistsIntro x18) (AndElimR x9) = false
  | equal_justa (AndElimR x9) (ForallIntro x17) = false
  | equal_justa (ForallIntro x17) (AndElimR x9) = false
  | equal_justa (AndElimR x9) (ForallElim x16) = false
  | equal_justa (ForallElim x16) (AndElimR x9) = false
  | equal_justa (AndElimR x9) (IffElimR x15) = false
  | equal_justa (IffElimR x15) (AndElimR x9) = false
  | equal_justa (AndElimR x9) (IffElimL x14) = false
  | equal_justa (IffElimL x14) (AndElimR x9) = false
  | equal_justa (AndElimR x9) (IffIntro (x131, x132)) = false
  | equal_justa (IffIntro (x131, x132)) (AndElimR x9) = false
  | equal_justa (AndElimR x9) (OrElim (x121, x122, x123, x124, x125)) = false
  | equal_justa (OrElim (x121, x122, x123, x124, x125)) (AndElimR x9) = false
  | equal_justa (AndElimR x9) (OrIntroR x11) = false
  | equal_justa (OrIntroR x11) (AndElimR x9) = false
  | equal_justa (AndElimR x9) (OrIntroL x10) = false
  | equal_justa (OrIntroL x10) (AndElimR x9) = false
  | equal_justa (AndElimL x8) (Reit x22a) = false
  | equal_justa (Reit x22a) (AndElimL x8) = false
  | equal_justa (AndElimL x8) (EqElim (x211, x212)) = false
  | equal_justa (EqElim (x211, x212)) (AndElimL x8) = false
  | equal_justa (AndElimL x8) EqIntro = false
  | equal_justa EqIntro (AndElimL x8) = false
  | equal_justa (AndElimL x8) (ExistsElim (x191, x192, x193)) = false
  | equal_justa (ExistsElim (x191, x192, x193)) (AndElimL x8) = false
  | equal_justa (AndElimL x8) (ExistsIntro x18) = false
  | equal_justa (ExistsIntro x18) (AndElimL x8) = false
  | equal_justa (AndElimL x8) (ForallIntro x17) = false
  | equal_justa (ForallIntro x17) (AndElimL x8) = false
  | equal_justa (AndElimL x8) (ForallElim x16) = false
  | equal_justa (ForallElim x16) (AndElimL x8) = false
  | equal_justa (AndElimL x8) (IffElimR x15) = false
  | equal_justa (IffElimR x15) (AndElimL x8) = false
  | equal_justa (AndElimL x8) (IffElimL x14) = false
  | equal_justa (IffElimL x14) (AndElimL x8) = false
  | equal_justa (AndElimL x8) (IffIntro (x131, x132)) = false
  | equal_justa (IffIntro (x131, x132)) (AndElimL x8) = false
  | equal_justa (AndElimL x8) (OrElim (x121, x122, x123, x124, x125)) = false
  | equal_justa (OrElim (x121, x122, x123, x124, x125)) (AndElimL x8) = false
  | equal_justa (AndElimL x8) (OrIntroR x11) = false
  | equal_justa (OrIntroR x11) (AndElimL x8) = false
  | equal_justa (AndElimL x8) (OrIntroL x10) = false
  | equal_justa (OrIntroL x10) (AndElimL x8) = false
  | equal_justa (AndElimL x8) (AndElimR x9) = false
  | equal_justa (AndElimR x9) (AndElimL x8) = false
  | equal_justa (AndIntro (x71, x72)) (Reit x22a) = false
  | equal_justa (Reit x22a) (AndIntro (x71, x72)) = false
  | equal_justa (AndIntro (x71, x72)) (EqElim (x211, x212)) = false
  | equal_justa (EqElim (x211, x212)) (AndIntro (x71, x72)) = false
  | equal_justa (AndIntro (x71, x72)) EqIntro = false
  | equal_justa EqIntro (AndIntro (x71, x72)) = false
  | equal_justa (AndIntro (x71, x72)) (ExistsElim (x191, x192, x193)) = false
  | equal_justa (ExistsElim (x191, x192, x193)) (AndIntro (x71, x72)) = false
  | equal_justa (AndIntro (x71, x72)) (ExistsIntro x18) = false
  | equal_justa (ExistsIntro x18) (AndIntro (x71, x72)) = false
  | equal_justa (AndIntro (x71, x72)) (ForallIntro x17) = false
  | equal_justa (ForallIntro x17) (AndIntro (x71, x72)) = false
  | equal_justa (AndIntro (x71, x72)) (ForallElim x16) = false
  | equal_justa (ForallElim x16) (AndIntro (x71, x72)) = false
  | equal_justa (AndIntro (x71, x72)) (IffElimR x15) = false
  | equal_justa (IffElimR x15) (AndIntro (x71, x72)) = false
  | equal_justa (AndIntro (x71, x72)) (IffElimL x14) = false
  | equal_justa (IffElimL x14) (AndIntro (x71, x72)) = false
  | equal_justa (AndIntro (x71, x72)) (IffIntro (x131, x132)) = false
  | equal_justa (IffIntro (x131, x132)) (AndIntro (x71, x72)) = false
  | equal_justa (AndIntro (x71, x72)) (OrElim (x121, x122, x123, x124, x125)) =
    false
  | equal_justa (OrElim (x121, x122, x123, x124, x125)) (AndIntro (x71, x72)) =
    false
  | equal_justa (AndIntro (x71, x72)) (OrIntroR x11) = false
  | equal_justa (OrIntroR x11) (AndIntro (x71, x72)) = false
  | equal_justa (AndIntro (x71, x72)) (OrIntroL x10) = false
  | equal_justa (OrIntroL x10) (AndIntro (x71, x72)) = false
  | equal_justa (AndIntro (x71, x72)) (AndElimR x9) = false
  | equal_justa (AndElimR x9) (AndIntro (x71, x72)) = false
  | equal_justa (AndIntro (x71, x72)) (AndElimL x8) = false
  | equal_justa (AndElimL x8) (AndIntro (x71, x72)) = false
  | equal_justa (BotI (x61, x62)) (Reit x22a) = false
  | equal_justa (Reit x22a) (BotI (x61, x62)) = false
  | equal_justa (BotI (x61, x62)) (EqElim (x211, x212)) = false
  | equal_justa (EqElim (x211, x212)) (BotI (x61, x62)) = false
  | equal_justa (BotI (x61, x62)) EqIntro = false
  | equal_justa EqIntro (BotI (x61, x62)) = false
  | equal_justa (BotI (x61, x62)) (ExistsElim (x191, x192, x193)) = false
  | equal_justa (ExistsElim (x191, x192, x193)) (BotI (x61, x62)) = false
  | equal_justa (BotI (x61, x62)) (ExistsIntro x18) = false
  | equal_justa (ExistsIntro x18) (BotI (x61, x62)) = false
  | equal_justa (BotI (x61, x62)) (ForallIntro x17) = false
  | equal_justa (ForallIntro x17) (BotI (x61, x62)) = false
  | equal_justa (BotI (x61, x62)) (ForallElim x16) = false
  | equal_justa (ForallElim x16) (BotI (x61, x62)) = false
  | equal_justa (BotI (x61, x62)) (IffElimR x15) = false
  | equal_justa (IffElimR x15) (BotI (x61, x62)) = false
  | equal_justa (BotI (x61, x62)) (IffElimL x14) = false
  | equal_justa (IffElimL x14) (BotI (x61, x62)) = false
  | equal_justa (BotI (x61, x62)) (IffIntro (x131, x132)) = false
  | equal_justa (IffIntro (x131, x132)) (BotI (x61, x62)) = false
  | equal_justa (BotI (x61, x62)) (OrElim (x121, x122, x123, x124, x125)) =
    false
  | equal_justa (OrElim (x121, x122, x123, x124, x125)) (BotI (x61, x62)) =
    false
  | equal_justa (BotI (x61, x62)) (OrIntroR x11) = false
  | equal_justa (OrIntroR x11) (BotI (x61, x62)) = false
  | equal_justa (BotI (x61, x62)) (OrIntroL x10) = false
  | equal_justa (OrIntroL x10) (BotI (x61, x62)) = false
  | equal_justa (BotI (x61, x62)) (AndElimR x9) = false
  | equal_justa (AndElimR x9) (BotI (x61, x62)) = false
  | equal_justa (BotI (x61, x62)) (AndElimL x8) = false
  | equal_justa (AndElimL x8) (BotI (x61, x62)) = false
  | equal_justa (BotI (x61, x62)) (AndIntro (x71, x72)) = false
  | equal_justa (AndIntro (x71, x72)) (BotI (x61, x62)) = false
  | equal_justa (DN x5) (Reit x22a) = false
  | equal_justa (Reit x22a) (DN x5) = false
  | equal_justa (DN x5) (EqElim (x211, x212)) = false
  | equal_justa (EqElim (x211, x212)) (DN x5) = false
  | equal_justa (DN x5) EqIntro = false
  | equal_justa EqIntro (DN x5) = false
  | equal_justa (DN x5) (ExistsElim (x191, x192, x193)) = false
  | equal_justa (ExistsElim (x191, x192, x193)) (DN x5) = false
  | equal_justa (DN x5) (ExistsIntro x18) = false
  | equal_justa (ExistsIntro x18) (DN x5) = false
  | equal_justa (DN x5) (ForallIntro x17) = false
  | equal_justa (ForallIntro x17) (DN x5) = false
  | equal_justa (DN x5) (ForallElim x16) = false
  | equal_justa (ForallElim x16) (DN x5) = false
  | equal_justa (DN x5) (IffElimR x15) = false
  | equal_justa (IffElimR x15) (DN x5) = false
  | equal_justa (DN x5) (IffElimL x14) = false
  | equal_justa (IffElimL x14) (DN x5) = false
  | equal_justa (DN x5) (IffIntro (x131, x132)) = false
  | equal_justa (IffIntro (x131, x132)) (DN x5) = false
  | equal_justa (DN x5) (OrElim (x121, x122, x123, x124, x125)) = false
  | equal_justa (OrElim (x121, x122, x123, x124, x125)) (DN x5) = false
  | equal_justa (DN x5) (OrIntroR x11) = false
  | equal_justa (OrIntroR x11) (DN x5) = false
  | equal_justa (DN x5) (OrIntroL x10) = false
  | equal_justa (OrIntroL x10) (DN x5) = false
  | equal_justa (DN x5) (AndElimR x9) = false
  | equal_justa (AndElimR x9) (DN x5) = false
  | equal_justa (DN x5) (AndElimL x8) = false
  | equal_justa (AndElimL x8) (DN x5) = false
  | equal_justa (DN x5) (AndIntro (x71, x72)) = false
  | equal_justa (AndIntro (x71, x72)) (DN x5) = false
  | equal_justa (DN x5) (BotI (x61, x62)) = false
  | equal_justa (BotI (x61, x62)) (DN x5) = false
  | equal_justa (RAA (x41, x42)) (Reit x22a) = false
  | equal_justa (Reit x22a) (RAA (x41, x42)) = false
  | equal_justa (RAA (x41, x42)) (EqElim (x211, x212)) = false
  | equal_justa (EqElim (x211, x212)) (RAA (x41, x42)) = false
  | equal_justa (RAA (x41, x42)) EqIntro = false
  | equal_justa EqIntro (RAA (x41, x42)) = false
  | equal_justa (RAA (x41, x42)) (ExistsElim (x191, x192, x193)) = false
  | equal_justa (ExistsElim (x191, x192, x193)) (RAA (x41, x42)) = false
  | equal_justa (RAA (x41, x42)) (ExistsIntro x18) = false
  | equal_justa (ExistsIntro x18) (RAA (x41, x42)) = false
  | equal_justa (RAA (x41, x42)) (ForallIntro x17) = false
  | equal_justa (ForallIntro x17) (RAA (x41, x42)) = false
  | equal_justa (RAA (x41, x42)) (ForallElim x16) = false
  | equal_justa (ForallElim x16) (RAA (x41, x42)) = false
  | equal_justa (RAA (x41, x42)) (IffElimR x15) = false
  | equal_justa (IffElimR x15) (RAA (x41, x42)) = false
  | equal_justa (RAA (x41, x42)) (IffElimL x14) = false
  | equal_justa (IffElimL x14) (RAA (x41, x42)) = false
  | equal_justa (RAA (x41, x42)) (IffIntro (x131, x132)) = false
  | equal_justa (IffIntro (x131, x132)) (RAA (x41, x42)) = false
  | equal_justa (RAA (x41, x42)) (OrElim (x121, x122, x123, x124, x125)) = false
  | equal_justa (OrElim (x121, x122, x123, x124, x125)) (RAA (x41, x42)) = false
  | equal_justa (RAA (x41, x42)) (OrIntroR x11) = false
  | equal_justa (OrIntroR x11) (RAA (x41, x42)) = false
  | equal_justa (RAA (x41, x42)) (OrIntroL x10) = false
  | equal_justa (OrIntroL x10) (RAA (x41, x42)) = false
  | equal_justa (RAA (x41, x42)) (AndElimR x9) = false
  | equal_justa (AndElimR x9) (RAA (x41, x42)) = false
  | equal_justa (RAA (x41, x42)) (AndElimL x8) = false
  | equal_justa (AndElimL x8) (RAA (x41, x42)) = false
  | equal_justa (RAA (x41, x42)) (AndIntro (x71, x72)) = false
  | equal_justa (AndIntro (x71, x72)) (RAA (x41, x42)) = false
  | equal_justa (RAA (x41, x42)) (BotI (x61, x62)) = false
  | equal_justa (BotI (x61, x62)) (RAA (x41, x42)) = false
  | equal_justa (RAA (x41, x42)) (DN x5) = false
  | equal_justa (DN x5) (RAA (x41, x42)) = false
  | equal_justa (CP (x31, x32)) (Reit x22a) = false
  | equal_justa (Reit x22a) (CP (x31, x32)) = false
  | equal_justa (CP (x31, x32)) (EqElim (x211, x212)) = false
  | equal_justa (EqElim (x211, x212)) (CP (x31, x32)) = false
  | equal_justa (CP (x31, x32)) EqIntro = false
  | equal_justa EqIntro (CP (x31, x32)) = false
  | equal_justa (CP (x31, x32)) (ExistsElim (x191, x192, x193)) = false
  | equal_justa (ExistsElim (x191, x192, x193)) (CP (x31, x32)) = false
  | equal_justa (CP (x31, x32)) (ExistsIntro x18) = false
  | equal_justa (ExistsIntro x18) (CP (x31, x32)) = false
  | equal_justa (CP (x31, x32)) (ForallIntro x17) = false
  | equal_justa (ForallIntro x17) (CP (x31, x32)) = false
  | equal_justa (CP (x31, x32)) (ForallElim x16) = false
  | equal_justa (ForallElim x16) (CP (x31, x32)) = false
  | equal_justa (CP (x31, x32)) (IffElimR x15) = false
  | equal_justa (IffElimR x15) (CP (x31, x32)) = false
  | equal_justa (CP (x31, x32)) (IffElimL x14) = false
  | equal_justa (IffElimL x14) (CP (x31, x32)) = false
  | equal_justa (CP (x31, x32)) (IffIntro (x131, x132)) = false
  | equal_justa (IffIntro (x131, x132)) (CP (x31, x32)) = false
  | equal_justa (CP (x31, x32)) (OrElim (x121, x122, x123, x124, x125)) = false
  | equal_justa (OrElim (x121, x122, x123, x124, x125)) (CP (x31, x32)) = false
  | equal_justa (CP (x31, x32)) (OrIntroR x11) = false
  | equal_justa (OrIntroR x11) (CP (x31, x32)) = false
  | equal_justa (CP (x31, x32)) (OrIntroL x10) = false
  | equal_justa (OrIntroL x10) (CP (x31, x32)) = false
  | equal_justa (CP (x31, x32)) (AndElimR x9) = false
  | equal_justa (AndElimR x9) (CP (x31, x32)) = false
  | equal_justa (CP (x31, x32)) (AndElimL x8) = false
  | equal_justa (AndElimL x8) (CP (x31, x32)) = false
  | equal_justa (CP (x31, x32)) (AndIntro (x71, x72)) = false
  | equal_justa (AndIntro (x71, x72)) (CP (x31, x32)) = false
  | equal_justa (CP (x31, x32)) (BotI (x61, x62)) = false
  | equal_justa (BotI (x61, x62)) (CP (x31, x32)) = false
  | equal_justa (CP (x31, x32)) (DN x5) = false
  | equal_justa (DN x5) (CP (x31, x32)) = false
  | equal_justa (CP (x31, x32)) (RAA (x41, x42)) = false
  | equal_justa (RAA (x41, x42)) (CP (x31, x32)) = false
  | equal_justa (MP (x21, x22)) (Reit x22a) = false
  | equal_justa (Reit x22a) (MP (x21, x22)) = false
  | equal_justa (MP (x21, x22)) (EqElim (x211, x212)) = false
  | equal_justa (EqElim (x211, x212)) (MP (x21, x22)) = false
  | equal_justa (MP (x21, x22)) EqIntro = false
  | equal_justa EqIntro (MP (x21, x22)) = false
  | equal_justa (MP (x21, x22)) (ExistsElim (x191, x192, x193)) = false
  | equal_justa (ExistsElim (x191, x192, x193)) (MP (x21, x22)) = false
  | equal_justa (MP (x21, x22)) (ExistsIntro x18) = false
  | equal_justa (ExistsIntro x18) (MP (x21, x22)) = false
  | equal_justa (MP (x21, x22)) (ForallIntro x17) = false
  | equal_justa (ForallIntro x17) (MP (x21, x22)) = false
  | equal_justa (MP (x21, x22)) (ForallElim x16) = false
  | equal_justa (ForallElim x16) (MP (x21, x22)) = false
  | equal_justa (MP (x21, x22)) (IffElimR x15) = false
  | equal_justa (IffElimR x15) (MP (x21, x22)) = false
  | equal_justa (MP (x21, x22)) (IffElimL x14) = false
  | equal_justa (IffElimL x14) (MP (x21, x22)) = false
  | equal_justa (MP (x21, x22)) (IffIntro (x131, x132)) = false
  | equal_justa (IffIntro (x131, x132)) (MP (x21, x22)) = false
  | equal_justa (MP (x21, x22)) (OrElim (x121, x122, x123, x124, x125)) = false
  | equal_justa (OrElim (x121, x122, x123, x124, x125)) (MP (x21, x22)) = false
  | equal_justa (MP (x21, x22)) (OrIntroR x11) = false
  | equal_justa (OrIntroR x11) (MP (x21, x22)) = false
  | equal_justa (MP (x21, x22)) (OrIntroL x10) = false
  | equal_justa (OrIntroL x10) (MP (x21, x22)) = false
  | equal_justa (MP (x21, x22)) (AndElimR x9) = false
  | equal_justa (AndElimR x9) (MP (x21, x22)) = false
  | equal_justa (MP (x21, x22)) (AndElimL x8) = false
  | equal_justa (AndElimL x8) (MP (x21, x22)) = false
  | equal_justa (MP (x21, x22)) (AndIntro (x71, x72)) = false
  | equal_justa (AndIntro (x71, x72)) (MP (x21, x22)) = false
  | equal_justa (MP (x21, x22)) (BotI (x61, x62)) = false
  | equal_justa (BotI (x61, x62)) (MP (x21, x22)) = false
  | equal_justa (MP (x21, x22)) (DN x5) = false
  | equal_justa (DN x5) (MP (x21, x22)) = false
  | equal_justa (MP (x21, x22)) (RAA (x41, x42)) = false
  | equal_justa (RAA (x41, x42)) (MP (x21, x22)) = false
  | equal_justa (MP (x21, x22)) (CP (x31, x32)) = false
  | equal_justa (CP (x31, x32)) (MP (x21, x22)) = false
  | equal_justa Assumption (Reit x22a) = false
  | equal_justa (Reit x22a) Assumption = false
  | equal_justa Assumption (EqElim (x211, x212)) = false
  | equal_justa (EqElim (x211, x212)) Assumption = false
  | equal_justa Assumption EqIntro = false
  | equal_justa EqIntro Assumption = false
  | equal_justa Assumption (ExistsElim (x191, x192, x193)) = false
  | equal_justa (ExistsElim (x191, x192, x193)) Assumption = false
  | equal_justa Assumption (ExistsIntro x18) = false
  | equal_justa (ExistsIntro x18) Assumption = false
  | equal_justa Assumption (ForallIntro x17) = false
  | equal_justa (ForallIntro x17) Assumption = false
  | equal_justa Assumption (ForallElim x16) = false
  | equal_justa (ForallElim x16) Assumption = false
  | equal_justa Assumption (IffElimR x15) = false
  | equal_justa (IffElimR x15) Assumption = false
  | equal_justa Assumption (IffElimL x14) = false
  | equal_justa (IffElimL x14) Assumption = false
  | equal_justa Assumption (IffIntro (x131, x132)) = false
  | equal_justa (IffIntro (x131, x132)) Assumption = false
  | equal_justa Assumption (OrElim (x121, x122, x123, x124, x125)) = false
  | equal_justa (OrElim (x121, x122, x123, x124, x125)) Assumption = false
  | equal_justa Assumption (OrIntroR x11) = false
  | equal_justa (OrIntroR x11) Assumption = false
  | equal_justa Assumption (OrIntroL x10) = false
  | equal_justa (OrIntroL x10) Assumption = false
  | equal_justa Assumption (AndElimR x9) = false
  | equal_justa (AndElimR x9) Assumption = false
  | equal_justa Assumption (AndElimL x8) = false
  | equal_justa (AndElimL x8) Assumption = false
  | equal_justa Assumption (AndIntro (x71, x72)) = false
  | equal_justa (AndIntro (x71, x72)) Assumption = false
  | equal_justa Assumption (BotI (x61, x62)) = false
  | equal_justa (BotI (x61, x62)) Assumption = false
  | equal_justa Assumption (DN x5) = false
  | equal_justa (DN x5) Assumption = false
  | equal_justa Assumption (RAA (x41, x42)) = false
  | equal_justa (RAA (x41, x42)) Assumption = false
  | equal_justa Assumption (CP (x31, x32)) = false
  | equal_justa (CP (x31, x32)) Assumption = false
  | equal_justa Assumption (MP (x21, x22)) = false
  | equal_justa (MP (x21, x22)) Assumption = false
  | equal_justa (Reit x22a) (Reit y22a) = equal_nata x22a y22a
  | equal_justa (EqElim (x211, x212)) (EqElim (y211, y212)) =
    equal_nata x211 y211 andalso equal_nata x212 y212
  | equal_justa (ExistsElim (x191, x192, x193)) (ExistsElim (y191, y192, y193))
    = equal_nata x191 y191 andalso
        (equal_nata x192 y192 andalso equal_nata x193 y193)
  | equal_justa (ExistsIntro x18) (ExistsIntro y18) = equal_nata x18 y18
  | equal_justa (ForallIntro x17) (ForallIntro y17) = equal_nata x17 y17
  | equal_justa (ForallElim x16) (ForallElim y16) = equal_nata x16 y16
  | equal_justa (IffElimR x15) (IffElimR y15) = equal_nata x15 y15
  | equal_justa (IffElimL x14) (IffElimL y14) = equal_nata x14 y14
  | equal_justa (IffIntro (x131, x132)) (IffIntro (y131, y132)) =
    equal_nata x131 y131 andalso equal_nata x132 y132
  | equal_justa (OrElim (x121, x122, x123, x124, x125))
    (OrElim (y121, y122, y123, y124, y125)) =
    equal_nata x121 y121 andalso
      (equal_nata x122 y122 andalso
        (equal_nata x123 y123 andalso
          (equal_nata x124 y124 andalso equal_nata x125 y125)))
  | equal_justa (OrIntroR x11) (OrIntroR y11) = equal_nata x11 y11
  | equal_justa (OrIntroL x10) (OrIntroL y10) = equal_nata x10 y10
  | equal_justa (AndElimR x9) (AndElimR y9) = equal_nata x9 y9
  | equal_justa (AndElimL x8) (AndElimL y8) = equal_nata x8 y8
  | equal_justa (AndIntro (x71, x72)) (AndIntro (y71, y72)) =
    equal_nata x71 y71 andalso equal_nata x72 y72
  | equal_justa (BotI (x61, x62)) (BotI (y61, y62)) =
    equal_nata x61 y61 andalso equal_nata x62 y62
  | equal_justa (DN x5) (DN y5) = equal_nata x5 y5
  | equal_justa (RAA (x41, x42)) (RAA (y41, y42)) =
    equal_nata x41 y41 andalso equal_nata x42 y42
  | equal_justa (CP (x31, x32)) (CP (y31, y32)) =
    equal_nata x31 y31 andalso equal_nata x32 y32
  | equal_justa (MP (x21, x22)) (MP (y21, y22)) =
    equal_nata x21 y21 andalso equal_nata x22 y22
  | equal_justa EqIntro EqIntro = true
  | equal_justa Assumption Assumption = true;

val equal_just = {equal = equal_justa} : just equal;

val equal_literal = {equal = (fn a => fn b => ((a : string) = b))} :
  string equal;

val ord_literal =
  {less_eq = (fn a => fn b => ((a : string) <= b)),
    less = (fn a => fn b => ((a : string) < b))}
  : string ord;

val preorder_literal = {ord_preorder = ord_literal} : string preorder;

val order_literal = {preorder_order = preorder_literal} : string order;

val linorder_literal = {order_linorder = order_literal} : string linorder;

fun equal_proda A_ B_ (x1, x2) (y1, y2) = eq A_ x1 y1 andalso eq B_ x2 y2;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) equal;

datatype num = One | Bit0 of num | Bit1 of num;

val one_integera : IntInf.int = (1 : IntInf.int);

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_integer = {one = one_integera} : IntInf.int one;

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_integer = {zero = (0 : IntInf.int)} : IntInf.int zero;

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

type 'a zero_neq_one = {one_zero_neq_one : 'a one, zero_zero_neq_one : 'a zero};
val one_zero_neq_one = #one_zero_neq_one : 'a zero_neq_one -> 'a one;
val zero_zero_neq_one = #zero_zero_neq_one : 'a zero_neq_one -> 'a zero;

val zero_neq_one_integer =
  {one_zero_neq_one = one_integer, zero_zero_neq_one = zero_integer} :
  IntInf.int zero_neq_one;

datatype hl_term = HL_Var of string | HL_Const of string;

fun equal_hl_terma (HL_Var x1) (HL_Const x2) = false
  | equal_hl_terma (HL_Const x2) (HL_Var x1) = false
  | equal_hl_terma (HL_Const x2) (HL_Const y2) = ((x2 : string) = y2)
  | equal_hl_terma (HL_Var x1) (HL_Var y1) = ((x1 : string) = y1);

val equal_hl_term = {equal = equal_hl_terma} : hl_term equal;

fun equal_bool false p = not p
  | equal_bool true p = p
  | equal_bool p false = not p
  | equal_bool p true = p;

datatype hl_formula = HL_Predicate of string * hl_term list | HL_Boolean of bool
  | HL_Not of hl_formula | HL_And of hl_formula * hl_formula |
  HL_Or of hl_formula * hl_formula | HL_Implies of hl_formula * hl_formula |
  HL_Iff of hl_formula * hl_formula | HL_ForAll of string * hl_formula |
  HL_Exists of string * hl_formula;

fun equal_hl_formulaa (HL_ForAll (x81, x82)) (HL_Exists (x91, x92)) = false
  | equal_hl_formulaa (HL_Exists (x91, x92)) (HL_ForAll (x81, x82)) = false
  | equal_hl_formulaa (HL_Iff (x71, x72)) (HL_Exists (x91, x92)) = false
  | equal_hl_formulaa (HL_Exists (x91, x92)) (HL_Iff (x71, x72)) = false
  | equal_hl_formulaa (HL_Iff (x71, x72)) (HL_ForAll (x81, x82)) = false
  | equal_hl_formulaa (HL_ForAll (x81, x82)) (HL_Iff (x71, x72)) = false
  | equal_hl_formulaa (HL_Implies (x61, x62)) (HL_Exists (x91, x92)) = false
  | equal_hl_formulaa (HL_Exists (x91, x92)) (HL_Implies (x61, x62)) = false
  | equal_hl_formulaa (HL_Implies (x61, x62)) (HL_ForAll (x81, x82)) = false
  | equal_hl_formulaa (HL_ForAll (x81, x82)) (HL_Implies (x61, x62)) = false
  | equal_hl_formulaa (HL_Implies (x61, x62)) (HL_Iff (x71, x72)) = false
  | equal_hl_formulaa (HL_Iff (x71, x72)) (HL_Implies (x61, x62)) = false
  | equal_hl_formulaa (HL_Or (x51, x52)) (HL_Exists (x91, x92)) = false
  | equal_hl_formulaa (HL_Exists (x91, x92)) (HL_Or (x51, x52)) = false
  | equal_hl_formulaa (HL_Or (x51, x52)) (HL_ForAll (x81, x82)) = false
  | equal_hl_formulaa (HL_ForAll (x81, x82)) (HL_Or (x51, x52)) = false
  | equal_hl_formulaa (HL_Or (x51, x52)) (HL_Iff (x71, x72)) = false
  | equal_hl_formulaa (HL_Iff (x71, x72)) (HL_Or (x51, x52)) = false
  | equal_hl_formulaa (HL_Or (x51, x52)) (HL_Implies (x61, x62)) = false
  | equal_hl_formulaa (HL_Implies (x61, x62)) (HL_Or (x51, x52)) = false
  | equal_hl_formulaa (HL_And (x41, x42)) (HL_Exists (x91, x92)) = false
  | equal_hl_formulaa (HL_Exists (x91, x92)) (HL_And (x41, x42)) = false
  | equal_hl_formulaa (HL_And (x41, x42)) (HL_ForAll (x81, x82)) = false
  | equal_hl_formulaa (HL_ForAll (x81, x82)) (HL_And (x41, x42)) = false
  | equal_hl_formulaa (HL_And (x41, x42)) (HL_Iff (x71, x72)) = false
  | equal_hl_formulaa (HL_Iff (x71, x72)) (HL_And (x41, x42)) = false
  | equal_hl_formulaa (HL_And (x41, x42)) (HL_Implies (x61, x62)) = false
  | equal_hl_formulaa (HL_Implies (x61, x62)) (HL_And (x41, x42)) = false
  | equal_hl_formulaa (HL_And (x41, x42)) (HL_Or (x51, x52)) = false
  | equal_hl_formulaa (HL_Or (x51, x52)) (HL_And (x41, x42)) = false
  | equal_hl_formulaa (HL_Not x3) (HL_Exists (x91, x92)) = false
  | equal_hl_formulaa (HL_Exists (x91, x92)) (HL_Not x3) = false
  | equal_hl_formulaa (HL_Not x3) (HL_ForAll (x81, x82)) = false
  | equal_hl_formulaa (HL_ForAll (x81, x82)) (HL_Not x3) = false
  | equal_hl_formulaa (HL_Not x3) (HL_Iff (x71, x72)) = false
  | equal_hl_formulaa (HL_Iff (x71, x72)) (HL_Not x3) = false
  | equal_hl_formulaa (HL_Not x3) (HL_Implies (x61, x62)) = false
  | equal_hl_formulaa (HL_Implies (x61, x62)) (HL_Not x3) = false
  | equal_hl_formulaa (HL_Not x3) (HL_Or (x51, x52)) = false
  | equal_hl_formulaa (HL_Or (x51, x52)) (HL_Not x3) = false
  | equal_hl_formulaa (HL_Not x3) (HL_And (x41, x42)) = false
  | equal_hl_formulaa (HL_And (x41, x42)) (HL_Not x3) = false
  | equal_hl_formulaa (HL_Boolean x2) (HL_Exists (x91, x92)) = false
  | equal_hl_formulaa (HL_Exists (x91, x92)) (HL_Boolean x2) = false
  | equal_hl_formulaa (HL_Boolean x2) (HL_ForAll (x81, x82)) = false
  | equal_hl_formulaa (HL_ForAll (x81, x82)) (HL_Boolean x2) = false
  | equal_hl_formulaa (HL_Boolean x2) (HL_Iff (x71, x72)) = false
  | equal_hl_formulaa (HL_Iff (x71, x72)) (HL_Boolean x2) = false
  | equal_hl_formulaa (HL_Boolean x2) (HL_Implies (x61, x62)) = false
  | equal_hl_formulaa (HL_Implies (x61, x62)) (HL_Boolean x2) = false
  | equal_hl_formulaa (HL_Boolean x2) (HL_Or (x51, x52)) = false
  | equal_hl_formulaa (HL_Or (x51, x52)) (HL_Boolean x2) = false
  | equal_hl_formulaa (HL_Boolean x2) (HL_And (x41, x42)) = false
  | equal_hl_formulaa (HL_And (x41, x42)) (HL_Boolean x2) = false
  | equal_hl_formulaa (HL_Boolean x2) (HL_Not x3) = false
  | equal_hl_formulaa (HL_Not x3) (HL_Boolean x2) = false
  | equal_hl_formulaa (HL_Predicate (x11, x12)) (HL_Exists (x91, x92)) = false
  | equal_hl_formulaa (HL_Exists (x91, x92)) (HL_Predicate (x11, x12)) = false
  | equal_hl_formulaa (HL_Predicate (x11, x12)) (HL_ForAll (x81, x82)) = false
  | equal_hl_formulaa (HL_ForAll (x81, x82)) (HL_Predicate (x11, x12)) = false
  | equal_hl_formulaa (HL_Predicate (x11, x12)) (HL_Iff (x71, x72)) = false
  | equal_hl_formulaa (HL_Iff (x71, x72)) (HL_Predicate (x11, x12)) = false
  | equal_hl_formulaa (HL_Predicate (x11, x12)) (HL_Implies (x61, x62)) = false
  | equal_hl_formulaa (HL_Implies (x61, x62)) (HL_Predicate (x11, x12)) = false
  | equal_hl_formulaa (HL_Predicate (x11, x12)) (HL_Or (x51, x52)) = false
  | equal_hl_formulaa (HL_Or (x51, x52)) (HL_Predicate (x11, x12)) = false
  | equal_hl_formulaa (HL_Predicate (x11, x12)) (HL_And (x41, x42)) = false
  | equal_hl_formulaa (HL_And (x41, x42)) (HL_Predicate (x11, x12)) = false
  | equal_hl_formulaa (HL_Predicate (x11, x12)) (HL_Not x3) = false
  | equal_hl_formulaa (HL_Not x3) (HL_Predicate (x11, x12)) = false
  | equal_hl_formulaa (HL_Predicate (x11, x12)) (HL_Boolean x2) = false
  | equal_hl_formulaa (HL_Boolean x2) (HL_Predicate (x11, x12)) = false
  | equal_hl_formulaa (HL_Exists (x91, x92)) (HL_Exists (y91, y92)) =
    ((x91 : string) = y91) andalso equal_hl_formulaa x92 y92
  | equal_hl_formulaa (HL_ForAll (x81, x82)) (HL_ForAll (y81, y82)) =
    ((x81 : string) = y81) andalso equal_hl_formulaa x82 y82
  | equal_hl_formulaa (HL_Iff (x71, x72)) (HL_Iff (y71, y72)) =
    equal_hl_formulaa x71 y71 andalso equal_hl_formulaa x72 y72
  | equal_hl_formulaa (HL_Implies (x61, x62)) (HL_Implies (y61, y62)) =
    equal_hl_formulaa x61 y61 andalso equal_hl_formulaa x62 y62
  | equal_hl_formulaa (HL_Or (x51, x52)) (HL_Or (y51, y52)) =
    equal_hl_formulaa x51 y51 andalso equal_hl_formulaa x52 y52
  | equal_hl_formulaa (HL_And (x41, x42)) (HL_And (y41, y42)) =
    equal_hl_formulaa x41 y41 andalso equal_hl_formulaa x42 y42
  | equal_hl_formulaa (HL_Not x3) (HL_Not y3) = equal_hl_formulaa x3 y3
  | equal_hl_formulaa (HL_Boolean x2) (HL_Boolean y2) = equal_bool x2 y2
  | equal_hl_formulaa (HL_Predicate (x11, x12)) (HL_Predicate (y11, y12)) =
    ((x11 : string) = y11) andalso equal_lista equal_hl_term x12 y12;

val equal_hl_formula = {equal = equal_hl_formulaa} : hl_formula equal;

datatype 'a set = Set of 'a list | Coset of 'a list;

datatype char = Chara of bool * bool * bool * bool * bool * bool * bool * bool;

datatype ('a, 'b) sum = Inl of 'a | Inr of 'b;

datatype fitch_rule = FPremise | FAssume | FMP of nat * nat | FCP of (nat * nat)
  | FRAA of (nat * nat) | FDN of nat | FBotI of nat * nat |
  FAndIntro of nat * nat | FAndElimL of nat | FAndElimR of nat |
  FOrIntroL of nat | FOrIntroR of nat |
  FOrElim of nat * (nat * nat) * (nat * nat) | FIffIntro of nat * nat |
  FIffElimL of nat | FIffElimR of nat | FForallElim of nat | FForallIntro of nat
  | FExistsIntro of nat | FExistsElim of nat * (nat * nat) | FEqIntro |
  FEqElim of nat * nat | FReit of nat;

datatype fline = FL of nat * fm * fitch_rule * nat list;

datatype hl_justification = HL_Assumption | HL_MP of int * int |
  HL_MT of int * int | HL_DN of int | HL_CP of int * int |
  HL_AndIntro of int * int | HL_AndElim of int | HL_OrIntro of int |
  HL_OrElim of int * int * int * int * int | HL_RAA of int * int |
  HL_ForallElim of int | HL_ExistsIntro of int | HL_ForallIntro of int |
  HL_ExistsElim of int * int * int | HL_EqIntro | HL_EqElim of int * int |
  HL_LEM | HL_PropTaut of int list | HL_IffIntro of int * int |
  HL_IffElim of int * int | HL_QN of int;

datatype hl_line =
  HL_ProofLine of int * hl_formula * hl_justification * int set;

datatype pline = ProofLine of nat * fm * just * nat set;

datatype route = Direct | ViaTree;

datatype subproof = Subproof of nat * fm * fitch_item list
and fitch_item = FLine of nat * fm * fitch_rule | FSub of subproof;

datatype deriv = Deriv of fm * drule
and drule = DAssume of nat | DPremise of nat | DMP of deriv * deriv |
  DCP of nat * fm * deriv | DRAA of nat * fm * deriv | DDN of deriv |
  DBotI of deriv * deriv | DAndIntro of deriv * deriv | DAndElimL of deriv |
  DAndElimR of deriv | DOrIntroL of deriv | DOrIntroR of deriv |
  DOrElim of deriv * nat * fm * deriv * nat * fm * deriv |
  DIffIntro of deriv * deriv | DIffElimL of deriv | DIffElimR of deriv |
  DForallElim of deriv | DForallIntro of deriv | DExistsIntro of deriv |
  DExistsElim of deriv * nat * fm * deriv | DEqIntro | DEqElim of deriv * deriv
  | DReit of deriv;

datatype hl_route = HL_DirectRoute | HL_ViaTreeRoute;

datatype hl_fitch_rule = HL_FPremise | HL_FAssume | HL_FMP of int * int |
  HL_FMT of int * int | HL_FDN of int | HL_FCP of (int * int) |
  HL_FAndI of int * int | HL_FAndE of int | HL_FOrI of int |
  HL_FOrE of int * (int * int) * (int * int) | HL_FRAA of (int * int) |
  HL_FForallE of int | HL_FForallI of int | HL_FExistsI of int |
  HL_FExistsE of int * (int * int) | HL_FEqI | HL_FEqE of int * int | HL_FLEM |
  HL_FPropTaut of int list | HL_FIffI of int * int | HL_FIffE of int * int |
  HL_FQN of int | HL_FReit of int;

datatype hl_subproof = HL_Subproof of int * hl_formula * hl_fitch_item list
and hl_fitch_item = HL_FLine of int * hl_formula * hl_fitch_rule |
  HL_FSub of hl_subproof;

datatype translation_error = NotNested of nat * nat * nat list |
  OutOfScope of nat * nat * nat | PremiseInBox of nat * nat |
  PremiseLate of nat * nat | BoxReversed of nat * nat |
  AssumptionReused of nat * nat * nat | NotCorrect of nat;

datatype hl_derivation = HL_Derivation of hl_formula * hl_derivation_rule
and hl_derivation_rule = HL_DAssume of int | HL_DPremise of int |
  HL_DMP of hl_derivation * hl_derivation |
  HL_DMT of hl_derivation * hl_derivation | HL_DDN of hl_derivation |
  HL_DCP of int * hl_formula * hl_derivation |
  HL_DAndI of hl_derivation * hl_derivation | HL_DAndE of hl_derivation |
  HL_DOrI of hl_derivation |
  HL_DOrE of
    hl_derivation * int * hl_formula * hl_derivation * int * hl_formula *
      hl_derivation
  | HL_DRAA of int * hl_formula * hl_derivation | HL_DForallE of hl_derivation |
  HL_DForallI of hl_derivation | HL_DExistsI of hl_derivation |
  HL_DExistsE of hl_derivation * int * hl_formula * hl_derivation | HL_DEqI |
  HL_DEqE of hl_derivation * hl_derivation | HL_DLEM |
  HL_DPropTaut of hl_derivation list | HL_DIffI of hl_derivation * hl_derivation
  | HL_DIffE of hl_derivation * hl_derivation | HL_DQN of hl_derivation;

datatype 'a hl_finite_model =
  HL_FiniteModel of
    'a list * (string * 'a) list * ((string * nat) * ('a list) list) list;

datatype hl_translation_error = HL_NotNested of int * int * int list |
  HL_OutOfScope of int * int * int | HL_UnknownAssumption of int * int |
  HL_MissingLine of int | HL_EigenInScope of int * string * int |
  HL_PremiseInBox of int * int | HL_PremiseLate of int * int |
  HL_BoxReversed of int * int | HL_AssumptionReused of int * int * int |
  HL_SourceNotVerified of int | HL_TargetNotVerified;

fun id x = (fn xa => xa) x;

fun plus_nat m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

val one_nat : nat = Nat (1 : IntInf.int);

fun suc n = plus_nat n one_nat;

fun upt i j = (if less_nat i j then i :: upt (suc i) j else []);

fun zip [] ys = []
  | zip xs [] = []
  | zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys;

fun list_all p [] = true
  | list_all p (x :: xs) = p x andalso list_all p xs;

fun ball (Set xs) p = list_all p xs;

fun max A_ a b = (if less_eq A_ a b then b else a);

fun minus_nat m n =
  Nat (max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

val zero_nat : nat = Nat (0 : IntInf.int);

fun drop n [] = []
  | drop n (x :: xs) =
    (if equal_nata n zero_nat then x :: xs else drop (minus_nat n one_nat) xs);

fun find uu [] = NONE
  | find p (x :: xs) = (if p x then SOME x else find p xs);

fun fold f [] s = s
  | fold f (x :: xs) s = fold f xs (f x s);

fun null [] = true
  | null (x :: xs) = false;

fun last (x :: xs) = (if null xs then x else last xs);

fun maps f [] = []
  | maps f (x :: xs) = f x @ maps f xs;

fun take n [] = []
  | take n (x :: xs) =
    (if equal_nata n zero_nat then [] else x :: take (minus_nat n one_nat) xs);

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun image f (Set xs) = Set (map f xs);

fun foldl f a [] = a
  | foldl f a (x :: xs) = foldl f (f a x) xs;

fun foldr f [] = id
  | foldr f (x :: xs) = f x o foldr f xs;

fun map_of A_ [] k = NONE
  | map_of A_ ((l, v) :: ps) k = (if eq A_ l k then SOME v else map_of A_ ps k);

fun filtera p [] = []
  | filtera p (x :: xs) = (if p x then x :: filtera p xs else filtera p xs);

fun filter p (Set xs) = Set (filtera p xs);

fun removeAll A_ x [] = []
  | removeAll A_ x (y :: xs) =
    (if eq A_ x y then removeAll A_ x xs else y :: removeAll A_ x xs);

fun membera A_ [] y = false
  | membera A_ (x :: xs) y = eq A_ x y orelse membera A_ xs y;

fun inserta A_ x xs = (if membera A_ xs x then xs else x :: xs);

fun insert A_ x (Set xs) = Set (inserta A_ x xs)
  | insert A_ x (Coset xs) = Coset (removeAll A_ x xs);

fun member A_ x (Set xs) = membera A_ xs x
  | member A_ x (Coset xs) = not (membera A_ xs x);

fun remove A_ x (Set xs) = Set (removeAll A_ x xs)
  | remove A_ x (Coset xs) = Coset (inserta A_ x xs);

fun fun_upd A_ f a b = (fn x => (if eq A_ x a then b else f x));

fun tl [] = []
  | tl (x21 :: x22) = x22;

fun list_ex p [] = false
  | list_ex p (x :: xs) = p x orelse list_ex p xs;

fun product [] uu = []
  | product (x :: xs) ys = map (fn a => (x, a)) ys @ product xs ys;

fun remdups A_ [] = []
  | remdups A_ (x :: xs) =
    (if membera A_ xs x then remdups A_ xs else x :: remdups A_ xs);

fun rn_t a b (Nm c) = Nm (if ((c : string) = a) then b else c)
  | rn_t a b (Vr y) = Vr y;

fun rn a b (Atom (p, ts)) = Atom (p, map (rn_t a b) ts)
  | rn a b (Eqf (t, u)) = Eqf (rn_t a b t, rn_t a b u)
  | rn a b Bot = Bot
  | rn a b (Neg p) = Neg (rn a b p)
  | rn a b (Conj (p, q)) = Conj (rn a b p, rn a b q)
  | rn a b (Disj (p, q)) = Disj (rn a b p, rn a b q)
  | rn a b (Impl (p, q)) = Impl (rn a b p, rn a b q)
  | rn a b (Iff (p, q)) = Iff (rn a b p, rn a b q)
  | rn a b (Uni (y, p)) = Uni (y, rn a b p)
  | rn a b (Exi (y, p)) = Exi (y, rn a b p);

fun cat ss = foldr (fn a => fn b => a ^ b) ss "";

fun of_bool A_ false = zero (zero_zero_neq_one A_)
  | of_bool A_ true = one (one_zero_neq_one A_);

fun integer_of_char (Chara (b0, b1, b2, b3, b4, b5, b6, b7)) =
  IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (of_bool
                        zero_neq_one_integer
                        b7, (2 : IntInf.int)), of_bool zero_neq_one_integer
         b6), (2 : IntInf.int)), of_bool zero_neq_one_integer
                                   b5), (2 : IntInf.int)), of_bool
                     zero_neq_one_integer
                     b4), (2 : IntInf.int)), of_bool zero_neq_one_integer
       b3), (2 : IntInf.int)), of_bool zero_neq_one_integer
                                 b2), (2 : IntInf.int)), of_bool
                   zero_neq_one_integer
                   b1), (2 : IntInf.int)), of_bool zero_neq_one_integer b0);

fun implode cs = Str_Literal.literal_of_asciis (map integer_of_char cs);

fun replicate n x =
  (if equal_nata n zero_nat then []
    else x :: replicate (minus_nat n one_nat) x);

fun freshIdx base k =
  implode
    (replicate (plus_nat base k)
      (Chara (true, true, false, false, false, true, true, false)));

fun names_t (Nm a) = [a]
  | names_t (Vr uu) = [];

fun names (Atom (uu, ts)) = maps names_t ts
  | names (Eqf (t, u)) = names_t t @ names_t u
  | names Bot = []
  | names (Neg p) = names p
  | names (Conj (p, q)) = names p @ names q
  | names (Disj (p, q)) = names p @ names q
  | names (Impl (p, q)) = names p @ names q
  | names (Iff (p, q)) = names p @ names q
  | names (Uni (uv, p)) = names p
  | names (Exi (uw, p)) = names p;

fun arbitrary_in a ps =
  list_all (fn p => not (membera equal_literal (names p) a)) ps;

fun subDerivs (DAssume k1) = []
  | subDerivs (DPremise k1) = []
  | subDerivs (DMP (d1, d2)) = [d1, d2]
  | subDerivs (DCP (k1, g1, d1)) = [d1]
  | subDerivs (DRAA (k1, g1, d1)) = [d1]
  | subDerivs (DDN d1) = [d1]
  | subDerivs (DBotI (d1, d2)) = [d1, d2]
  | subDerivs (DAndIntro (d1, d2)) = [d1, d2]
  | subDerivs (DAndElimL d1) = [d1]
  | subDerivs (DAndElimR d1) = [d1]
  | subDerivs (DOrIntroL d1) = [d1]
  | subDerivs (DOrIntroR d1) = [d1]
  | subDerivs (DOrElim (d1, k1, g1, d2, k2, g2, d3)) = [d1, d2, d3]
  | subDerivs (DIffIntro (d1, d2)) = [d1, d2]
  | subDerivs (DIffElimL d1) = [d1]
  | subDerivs (DIffElimR d1) = [d1]
  | subDerivs (DForallElim d1) = [d1]
  | subDerivs (DForallIntro d1) = [d1]
  | subDerivs (DExistsIntro d1) = [d1]
  | subDerivs (DExistsElim (d1, k1, g1, d2)) = [d1, d2]
  | subDerivs DEqIntro = []
  | subDerivs (DEqElim (d1, d2)) = [d1, d2]
  | subDerivs (DReit d1) = [d1];

fun fst (x1, x2) = x1;

fun openAsms (Deriv (phi, DAssume n)) = [(n, phi)]
  | openAsms (Deriv (phi, DPremise n)) = [(n, phi)]
  | openAsms (Deriv (phi, DCP (a, fa, d))) =
    filtera (fn nf => not (equal_nata (fst nf) a)) (openAsms d)
  | openAsms (Deriv (phi, DRAA (a, fa, d))) =
    filtera (fn nf => not (equal_nata (fst nf) a)) (openAsms d)
  | openAsms (Deriv (phi, DOrElim (d0, a1, f1, d1, a2, f2, d2))) =
    openAsms d0 @
      filtera (fn nf => not (equal_nata (fst nf) a1)) (openAsms d1) @
        filtera (fn nf => not (equal_nata (fst nf) a2)) (openAsms d2)
  | openAsms (Deriv (phi, DExistsElim (d0, a, f, d1))) =
    openAsms d0 @ filtera (fn nf => not (equal_nata (fst nf) a)) (openAsms d1)
  | openAsms (Deriv (phi, DMP (v, va))) =
    maps openAsms (subDerivs (DMP (v, va)))
  | openAsms (Deriv (phi, DDN v)) = maps openAsms (subDerivs (DDN v))
  | openAsms (Deriv (phi, DBotI (v, va))) =
    maps openAsms (subDerivs (DBotI (v, va)))
  | openAsms (Deriv (phi, DAndIntro (v, va))) =
    maps openAsms (subDerivs (DAndIntro (v, va)))
  | openAsms (Deriv (phi, DAndElimL v)) =
    maps openAsms (subDerivs (DAndElimL v))
  | openAsms (Deriv (phi, DAndElimR v)) =
    maps openAsms (subDerivs (DAndElimR v))
  | openAsms (Deriv (phi, DOrIntroL v)) =
    maps openAsms (subDerivs (DOrIntroL v))
  | openAsms (Deriv (phi, DOrIntroR v)) =
    maps openAsms (subDerivs (DOrIntroR v))
  | openAsms (Deriv (phi, DIffIntro (v, va))) =
    maps openAsms (subDerivs (DIffIntro (v, va)))
  | openAsms (Deriv (phi, DIffElimL v)) =
    maps openAsms (subDerivs (DIffElimL v))
  | openAsms (Deriv (phi, DIffElimR v)) =
    maps openAsms (subDerivs (DIffElimR v))
  | openAsms (Deriv (phi, DForallElim v)) =
    maps openAsms (subDerivs (DForallElim v))
  | openAsms (Deriv (phi, DForallIntro v)) =
    maps openAsms (subDerivs (DForallIntro v))
  | openAsms (Deriv (phi, DExistsIntro v)) =
    maps openAsms (subDerivs (DExistsIntro v))
  | openAsms (Deriv (phi, DEqIntro)) = maps openAsms (subDerivs DEqIntro)
  | openAsms (Deriv (phi, DEqElim (v, va))) =
    maps openAsms (subDerivs (DEqElim (v, va)))
  | openAsms (Deriv (phi, DReit v)) = maps openAsms (subDerivs (DReit v));

fun snd (x1, x2) = x2;

fun inst_t x a (Nm b) = Nm b
  | inst_t x a (Vr y) = (if ((x : string) = y) then Nm a else Vr y);

fun inst x a (Atom (p, ts)) = Atom (p, map (inst_t x a) ts)
  | inst x a (Eqf (t, u)) = Eqf (inst_t x a t, inst_t x a u)
  | inst x a Bot = Bot
  | inst x a (Neg p) = Neg (inst x a p)
  | inst x a (Conj (p, q)) = Conj (inst x a p, inst x a q)
  | inst x a (Disj (p, q)) = Disj (inst x a p, inst x a q)
  | inst x a (Impl (p, q)) = Impl (inst x a p, inst x a q)
  | inst x a (Iff (p, q)) = Iff (inst x a p, inst x a q)
  | inst x a (Uni (y, p)) =
    Uni (y, (if ((x : string) = y) then p else inst x a p))
  | inst x a (Exi (y, p)) =
    Exi (y, (if ((x : string) = y) then p else inst x a p));

fun fvs_t (Nm uu) = []
  | fvs_t (Vr x) = [x];

fun fvs (Atom (uu, ts)) = maps fvs_t ts
  | fvs (Eqf (t, u)) = fvs_t t @ fvs_t u
  | fvs Bot = []
  | fvs (Neg p) = fvs p
  | fvs (Conj (p, q)) = fvs p @ fvs q
  | fvs (Disj (p, q)) = fvs p @ fvs q
  | fvs (Impl (p, q)) = fvs p @ fvs q
  | fvs (Iff (p, q)) = fvs p @ fvs q
  | fvs (Uni (x, p)) = removeAll equal_literal x (fvs p)
  | fvs (Exi (x, p)) = removeAll equal_literal x (fvs p);

fun instWitnesses x p q =
  (if membera equal_literal (fvs p) x
    then filtera (fn a => equal_fma (inst x a p) q) (names q) else []);

fun witnessOf ex f psi asa =
  (case ex of Atom (_, _) => NONE | Eqf (_, _) => NONE | Bot => NONE
    | Neg _ => NONE | Conj (_, _) => NONE | Disj (_, _) => NONE
    | Impl (_, _) => NONE | Iff (_, _) => NONE | Uni (_, _) => NONE
    | Exi (x, p) =>
      (case filtera
              (fn b =>
                not (membera equal_literal (names p) b) andalso
                  (not (membera equal_literal (names psi) b) andalso
                    arbitrary_in b asa))
              (instWitnesses x p f)
        of [] => NONE | b :: _ => SOME b));

fun envFms g = map (snd o snd) g;

fun map_filter f [] = []
  | map_filter f (x :: xs) =
    (case f x of NONE => map_filter f xs | SOME y => y :: map_filter f xs);

fun exRepair g ex f psi a d0 d1 =
  (case witnessOf ex f psi
          (map snd (openAsms d0) @
            map_filter
              (fn x =>
                (if not (equal_nata (fst x) a) then SOME (snd x) else NONE))
              (openAsms d1))
    of NONE => NONE
    | SOME b => (if arbitrary_in b (envFms g) then NONE else SOME b));

fun rnD a b (Deriv (phi, DAssume k1)) = Deriv (rn a b phi, DAssume k1)
  | rnD a b (Deriv (phi, DPremise k1)) = Deriv (rn a b phi, DPremise k1)
  | rnD a b (Deriv (phi, DMP (d1, d2))) =
    Deriv (rn a b phi, DMP (rnD a b d1, rnD a b d2))
  | rnD a b (Deriv (phi, DCP (k1, g1, d1))) =
    Deriv (rn a b phi, DCP (k1, rn a b g1, rnD a b d1))
  | rnD a b (Deriv (phi, DRAA (k1, g1, d1))) =
    Deriv (rn a b phi, DRAA (k1, rn a b g1, rnD a b d1))
  | rnD a b (Deriv (phi, DDN d1)) = Deriv (rn a b phi, DDN (rnD a b d1))
  | rnD a b (Deriv (phi, DBotI (d1, d2))) =
    Deriv (rn a b phi, DBotI (rnD a b d1, rnD a b d2))
  | rnD a b (Deriv (phi, DAndIntro (d1, d2))) =
    Deriv (rn a b phi, DAndIntro (rnD a b d1, rnD a b d2))
  | rnD a b (Deriv (phi, DAndElimL d1)) =
    Deriv (rn a b phi, DAndElimL (rnD a b d1))
  | rnD a b (Deriv (phi, DAndElimR d1)) =
    Deriv (rn a b phi, DAndElimR (rnD a b d1))
  | rnD a b (Deriv (phi, DOrIntroL d1)) =
    Deriv (rn a b phi, DOrIntroL (rnD a b d1))
  | rnD a b (Deriv (phi, DOrIntroR d1)) =
    Deriv (rn a b phi, DOrIntroR (rnD a b d1))
  | rnD a b (Deriv (phi, DOrElim (d1, k1, g1, d2, k2, g2, d3))) =
    Deriv (rn a b phi,
            DOrElim
              (rnD a b d1, k1, rn a b g1, rnD a b d2, k2, rn a b g2,
                rnD a b d3))
  | rnD a b (Deriv (phi, DIffIntro (d1, d2))) =
    Deriv (rn a b phi, DIffIntro (rnD a b d1, rnD a b d2))
  | rnD a b (Deriv (phi, DIffElimL d1)) =
    Deriv (rn a b phi, DIffElimL (rnD a b d1))
  | rnD a b (Deriv (phi, DIffElimR d1)) =
    Deriv (rn a b phi, DIffElimR (rnD a b d1))
  | rnD a b (Deriv (phi, DForallElim d1)) =
    Deriv (rn a b phi, DForallElim (rnD a b d1))
  | rnD a b (Deriv (phi, DForallIntro d1)) =
    Deriv (rn a b phi, DForallIntro (rnD a b d1))
  | rnD a b (Deriv (phi, DExistsIntro d1)) =
    Deriv (rn a b phi, DExistsIntro (rnD a b d1))
  | rnD a b (Deriv (phi, DExistsElim (d1, k1, g1, d2))) =
    Deriv (rn a b phi, DExistsElim (rnD a b d1, k1, rn a b g1, rnD a b d2))
  | rnD a b (Deriv (phi, DEqIntro)) = Deriv (rn a b phi, DEqIntro)
  | rnD a b (Deriv (phi, DEqElim (d1, d2))) =
    Deriv (rn a b phi, DEqElim (rnD a b d1, rnD a b d2))
  | rnD a b (Deriv (phi, DReit d1)) = Deriv (rn a b phi, DReit (rnD a b d1));

fun exD base cnt g ex f psi a d0 d1 =
  (case exRepair g ex f psi a d0 d1 of NONE => d1
    | SOME b => rnD b (freshIdx base cnt) d1);

fun exF base cnt g ex f psi a d0 d1 =
  (case exRepair g ex f psi a d0 d1 of NONE => f
    | SOME b => rn b (freshIdx base cnt) f);

fun superset A_ xs = list_all (membera A_ xs);

fun map_option f NONE = NONE
  | map_option f (SOME x2) = SOME (f x2);

fun formula (ProofLine (x1, x2, x3, x4)) = x2;

fun lineNumber (ProofLine (x1, x2, x3, x4)) = x1;

fun lookupLine [] n = NONE
  | lookupLine (l :: ls) n =
    (if equal_nata (lineNumber l) n then SOME l else lookupLine ls n);

fun fmAt p n = map_option formula (lookupLine p n);

fun dForm (Deriv (x1, x2)) = x1;

fun endsAt body asmLine c =
  (if null body then equal_nata asmLine c
    else (case last body of FLine (n, _, _) => equal_nata n c
           | FSub _ => false));

fun closeSub asmLine psi body c nxt =
  (if endsAt body asmLine c then (body, (c, nxt))
    else (body @ [FLine (nxt, psi, FReit c)], (nxt, suc nxt)));

fun envLine g a =
  (case find (fn e => equal_nata (fst e) a) g of NONE => zero_nat
    | SOME e => fst (snd e));

fun eigenOf x p d =
  (case filtera
          (fn a =>
            not (membera equal_literal (names p) a) andalso
              arbitrary_in a (map snd (openAsms d)))
          (instWitnesses x p (dForm d))
    of [] => NONE | a :: _ => SOME a);

fun uniRepair g phi d =
  (case phi of Atom (_, _) => NONE | Eqf (_, _) => NONE | Bot => NONE
    | Neg _ => NONE | Conj (_, _) => NONE | Disj (_, _) => NONE
    | Impl (_, _) => NONE | Iff (_, _) => NONE
    | Uni (x, p) =>
      (case eigenOf x p d of NONE => NONE
        | SOME a => (if arbitrary_in a (envFms g) then NONE else SOME a))
    | Exi (_, _) => NONE);

fun uniCnt cnt g phi d =
  (case uniRepair g phi d of NONE => cnt | SOME _ => suc cnt);

fun exCnt cnt g ex f psi a d0 d1 =
  (case exRepair g ex f psi a d0 d1 of NONE => cnt | SOME _ => suc cnt);

fun uniD base cnt g phi d =
  (case uniRepair g phi d of NONE => d | SOME a => rnD a (freshIdx base cnt) d);

fun emit base g nx cnt (Deriv (phi, DAssume a)) = ([], (envLine g a, (nx, cnt)))
  | emit base g nx cnt (Deriv (phi, DPremise a)) =
    ([], (envLine g a, (nx, cnt)))
  | emit base g nx cnt (Deriv (phi, DMP (d1, d2))) =
    let
      val (i1, (c1, (nx1, cnt1))) = emit base g nx cnt d1;
      val (i2, (c2, (nx2, cnt2))) = emit base g nx1 cnt1 d2;
    in
      (i1 @ i2 @ [FLine (nx2, phi, FMP (c1, c2))], (nx2, (suc nx2, cnt2)))
    end
  | emit base g nx cnt (Deriv (phi, DCP (a, fa, d1))) =
    let
      val (b1, (cc1, (nx1, cnt1))) =
        emit base ((a, (nx, fa)) :: g) (suc nx) cnt d1;
      val (b1a, (l1, nx2)) = closeSub nx (dForm d1) b1 cc1 nx1;
    in
      ([FSub (Subproof (nx, fa, b1a)), FLine (nx2, phi, FCP (nx, l1))],
        (nx2, (suc nx2, cnt1)))
    end
  | emit base g nx cnt (Deriv (phi, DRAA (a, fa, d1))) =
    let
      val (b1, (cc1, (nx1, cnt1))) =
        emit base ((a, (nx, fa)) :: g) (suc nx) cnt d1;
      val (b1a, (l1, nx2)) = closeSub nx (dForm d1) b1 cc1 nx1;
    in
      ([FSub (Subproof (nx, fa, b1a)), FLine (nx2, phi, FRAA (nx, l1))],
        (nx2, (suc nx2, cnt1)))
    end
  | emit base g nx cnt (Deriv (phi, DDN d1)) =
    let
      val (i1, (c1, (nx1, cnt1))) = emit base g nx cnt d1;
    in
      (i1 @ [FLine (nx1, phi, FDN c1)], (nx1, (suc nx1, cnt1)))
    end
  | emit base g nx cnt (Deriv (phi, DBotI (d1, d2))) =
    let
      val (i1, (c1, (nx1, cnt1))) = emit base g nx cnt d1;
      val (i2, (c2, (nx2, cnt2))) = emit base g nx1 cnt1 d2;
    in
      (i1 @ i2 @ [FLine (nx2, phi, FBotI (c1, c2))], (nx2, (suc nx2, cnt2)))
    end
  | emit base g nx cnt (Deriv (phi, DAndIntro (d1, d2))) =
    let
      val (i1, (c1, (nx1, cnt1))) = emit base g nx cnt d1;
      val (i2, (c2, (nx2, cnt2))) = emit base g nx1 cnt1 d2;
    in
      (i1 @ i2 @ [FLine (nx2, phi, FAndIntro (c1, c2))], (nx2, (suc nx2, cnt2)))
    end
  | emit base g nx cnt (Deriv (phi, DAndElimL d1)) =
    let
      val (i1, (c1, (nx1, cnt1))) = emit base g nx cnt d1;
    in
      (i1 @ [FLine (nx1, phi, FAndElimL c1)], (nx1, (suc nx1, cnt1)))
    end
  | emit base g nx cnt (Deriv (phi, DAndElimR d1)) =
    let
      val (i1, (c1, (nx1, cnt1))) = emit base g nx cnt d1;
    in
      (i1 @ [FLine (nx1, phi, FAndElimR c1)], (nx1, (suc nx1, cnt1)))
    end
  | emit base g nx cnt (Deriv (phi, DOrIntroL d1)) =
    let
      val (i1, (c1, (nx1, cnt1))) = emit base g nx cnt d1;
    in
      (i1 @ [FLine (nx1, phi, FOrIntroL c1)], (nx1, (suc nx1, cnt1)))
    end
  | emit base g nx cnt (Deriv (phi, DOrIntroR d1)) =
    let
      val (i1, (c1, (nx1, cnt1))) = emit base g nx cnt d1;
    in
      (i1 @ [FLine (nx1, phi, FOrIntroR c1)], (nx1, (suc nx1, cnt1)))
    end
  | emit base g nx cnt (Deriv (phi, DOrElim (d0, a1, f1, d1, a2, f2, d2))) =
    let
      val (i0, (c0, (nx0, cnt0))) = emit base g nx cnt d0;
      val (b1, (cc1, (nx1, cnt1))) =
        emit base ((a1, (nx0, f1)) :: g) (suc nx0) cnt0 d1;
      val (b1a, (l1, nx1a)) = closeSub nx0 (dForm d1) b1 cc1 nx1;
      val (b2, (cc2, (nx2, cnt2))) =
        emit base ((a2, (nx1a, f2)) :: g) (suc nx1a) cnt1 d2;
      val (b2a, (l2, nx2a)) = closeSub nx1a (dForm d2) b2 cc2 nx2;
    in
      (i0 @ [FSub (Subproof (nx0, f1, b1a)), FSub (Subproof (nx1a, f2, b2a)),
              FLine (nx2a, phi, FOrElim (c0, (nx0, l1), (nx1a, l2)))],
        (nx2a, (suc nx2a, cnt2)))
    end
  | emit base g nx cnt (Deriv (phi, DIffIntro (d1, d2))) =
    let
      val (i1, (c1, (nx1, cnt1))) = emit base g nx cnt d1;
      val (i2, (c2, (nx2, cnt2))) = emit base g nx1 cnt1 d2;
    in
      (i1 @ i2 @ [FLine (nx2, phi, FIffIntro (c1, c2))], (nx2, (suc nx2, cnt2)))
    end
  | emit base g nx cnt (Deriv (phi, DIffElimL d1)) =
    let
      val (i1, (c1, (nx1, cnt1))) = emit base g nx cnt d1;
    in
      (i1 @ [FLine (nx1, phi, FIffElimL c1)], (nx1, (suc nx1, cnt1)))
    end
  | emit base g nx cnt (Deriv (phi, DIffElimR d1)) =
    let
      val (i1, (c1, (nx1, cnt1))) = emit base g nx cnt d1;
    in
      (i1 @ [FLine (nx1, phi, FIffElimR c1)], (nx1, (suc nx1, cnt1)))
    end
  | emit base g nx cnt (Deriv (phi, DForallElim d1)) =
    let
      val (i1, (c1, (nx1, cnt1))) = emit base g nx cnt d1;
    in
      (i1 @ [FLine (nx1, phi, FForallElim c1)], (nx1, (suc nx1, cnt1)))
    end
  | emit base g nx cnt (Deriv (phi, DForallIntro d1)) =
    let
      val (i1, (c1, (nx1, cnt1))) =
        emit base g nx (uniCnt cnt g phi d1) (uniD base cnt g phi d1);
    in
      (i1 @ [FLine (nx1, phi, FForallIntro c1)], (nx1, (suc nx1, cnt1)))
    end
  | emit base g nx cnt (Deriv (phi, DExistsIntro d1)) =
    let
      val (i1, (c1, (nx1, cnt1))) = emit base g nx cnt d1;
    in
      (i1 @ [FLine (nx1, phi, FExistsIntro c1)], (nx1, (suc nx1, cnt1)))
    end
  | emit base g nx cnt (Deriv (phi, DExistsElim (d0, a, f, d1))) =
    let
      val (i0, (c0, (nx0, cnt0))) = emit base g nx cnt d0;
      val fa = exF base cnt0 g (dForm d0) f phi a d0 d1;
      val (b1, (cc1, (nx1, cnt1))) =
        emit base ((a, (nx0, fa)) :: g) (suc nx0)
          (exCnt cnt0 g (dForm d0) f phi a d0 d1)
          (exD base cnt0 g (dForm d0) f phi a d0 d1);
      val (b1a, (l1, nx2)) = closeSub nx0 phi b1 cc1 nx1;
    in
      (i0 @ [FSub (Subproof (nx0, fa, b1a)),
              FLine (nx2, phi, FExistsElim (c0, (nx0, l1)))],
        (nx2, (suc nx2, cnt1)))
    end
  | emit base g nx cnt (Deriv (phi, DEqIntro)) =
    ([FLine (nx, phi, FEqIntro)], (nx, (suc nx, cnt)))
  | emit base g nx cnt (Deriv (phi, DEqElim (d1, d2))) =
    let
      val (i1, (c1, (nx1, cnt1))) = emit base g nx cnt d1;
      val (i2, (c2, (nx2, cnt2))) = emit base g nx1 cnt1 d2;
    in
      (i1 @ i2 @ [FLine (nx2, phi, FEqElim (c1, c2))], (nx2, (suc nx2, cnt2)))
    end
  | emit base g nx cnt (Deriv (phi, DReit d1)) =
    let
      val (i1, (c1, (nx1, cnt1))) = emit base g nx cnt d1;
    in
      (i1 @ [FLine (nx1, phi, FReit c1)], (nx1, (suc nx1, cnt1)))
    end;

fun dropWhile p [] = []
  | dropWhile p (x :: xs) = (if p x then dropWhile p xs else x :: xs);

fun enumerate n [] = []
  | enumerate n (x :: xs) = (n, x) :: enumerate (suc n) xs;

fun takeWhile p [] = []
  | takeWhile p (x :: xs) = (if p x then x :: takeWhile p xs else []);

fun is_none NONE = true
  | is_none (SOME x) = false;

fun flNum (FL (x1, x2, x3, x4)) = x1;

fun findFL [] n = NONE
  | findFL (fl :: fls) n =
    (if equal_nata (flNum fl) n then SOME fl else findFL fls n);

fun length_tailrec [] n = n
  | length_tailrec (x :: xs) n = length_tailrec xs (suc n);

fun size_lista xs = length_tailrec xs zero_nat;

fun bit_cut_integer k =
  (if ((k : IntInf.int) = (0 : IntInf.int)) then ((0 : IntInf.int), false)
    else let
           val (r, s) =
             IntInf.divMod (IntInf.abs k, IntInf.abs (2 : IntInf.int));
         in
           ((if IntInf.< ((0 : IntInf.int), k) then r
              else IntInf.- (IntInf.~ r, s)),
             ((s : IntInf.int) = (1 : IntInf.int)))
         end);

fun char_of_integer k = let
                          val (q0, b0) = bit_cut_integer k;
                          val (q1, b1) = bit_cut_integer q0;
                          val (q2, b2) = bit_cut_integer q1;
                          val (q3, b3) = bit_cut_integer q2;
                          val (q4, b4) = bit_cut_integer q3;
                          val (q5, b5) = bit_cut_integer q4;
                          val (q6, b6) = bit_cut_integer q5;
                          val (_, a) = bit_cut_integer q6;
                        in
                          Chara (b0, b1, b2, b3, b4, b5, b6, a)
                        end;

fun explode s = map char_of_integer (Str_Literal.asciis_of_literal s);

fun nlen a = size_lista (explode a);

fun hlJustification (HL_ProofLine (x1, x2, x3, x4)) = x3;

fun hlLineNumber (HL_ProofLine (x1, x2, x3, x4)) = x1;

fun hlCitedLines HL_Assumption = []
  | hlCitedLines (HL_MP (m, n)) = [m, n]
  | hlCitedLines (HL_MT (m, n)) = [m, n]
  | hlCitedLines (HL_DN m) = [m]
  | hlCitedLines (HL_CP (m, n)) = [m, n]
  | hlCitedLines (HL_AndIntro (m, n)) = [m, n]
  | hlCitedLines (HL_AndElim m) = [m]
  | hlCitedLines (HL_OrIntro m) = [m]
  | hlCitedLines (HL_OrElim (d, a1, c1, a2, c2)) = [d, a1, c1, a2, c2]
  | hlCitedLines (HL_RAA (a, c)) = [a, c]
  | hlCitedLines (HL_ForallElim m) = [m]
  | hlCitedLines (HL_ExistsIntro m) = [m]
  | hlCitedLines (HL_ForallIntro m) = [m]
  | hlCitedLines (HL_ExistsElim (m, a, c)) = [m, a, c]
  | hlCitedLines HL_EqIntro = []
  | hlCitedLines (HL_EqElim (m, n)) = [m, n]
  | hlCitedLines HL_LEM = []
  | hlCitedLines (HL_PropTaut ms) = ms
  | hlCitedLines (HL_IffIntro (m, n)) = [m, n]
  | hlCitedLines (HL_IffElim (m, n)) = [m, n]
  | hlCitedLines (HL_QN m) = [m];

fun hlStructureOK p l =
  equal_nata
    (size_lista
      (filtera (fn k => equal_inta (hlLineNumber k) (hlLineNumber l)) p))
    one_nat andalso
    list_all (fn m => less_int m (hlLineNumber l))
      (hlCitedLines (hlJustification l));

fun equal_hl_justification (HL_IffElim (x201, x202)) (HL_QN x21a) = false
  | equal_hl_justification (HL_QN x21a) (HL_IffElim (x201, x202)) = false
  | equal_hl_justification (HL_IffIntro (x191, x192)) (HL_QN x21a) = false
  | equal_hl_justification (HL_QN x21a) (HL_IffIntro (x191, x192)) = false
  | equal_hl_justification (HL_IffIntro (x191, x192)) (HL_IffElim (x201, x202))
    = false
  | equal_hl_justification (HL_IffElim (x201, x202)) (HL_IffIntro (x191, x192))
    = false
  | equal_hl_justification (HL_PropTaut x18) (HL_QN x21a) = false
  | equal_hl_justification (HL_QN x21a) (HL_PropTaut x18) = false
  | equal_hl_justification (HL_PropTaut x18) (HL_IffElim (x201, x202)) = false
  | equal_hl_justification (HL_IffElim (x201, x202)) (HL_PropTaut x18) = false
  | equal_hl_justification (HL_PropTaut x18) (HL_IffIntro (x191, x192)) = false
  | equal_hl_justification (HL_IffIntro (x191, x192)) (HL_PropTaut x18) = false
  | equal_hl_justification HL_LEM (HL_QN x21a) = false
  | equal_hl_justification (HL_QN x21a) HL_LEM = false
  | equal_hl_justification HL_LEM (HL_IffElim (x201, x202)) = false
  | equal_hl_justification (HL_IffElim (x201, x202)) HL_LEM = false
  | equal_hl_justification HL_LEM (HL_IffIntro (x191, x192)) = false
  | equal_hl_justification (HL_IffIntro (x191, x192)) HL_LEM = false
  | equal_hl_justification HL_LEM (HL_PropTaut x18) = false
  | equal_hl_justification (HL_PropTaut x18) HL_LEM = false
  | equal_hl_justification (HL_EqElim (x161, x162)) (HL_QN x21a) = false
  | equal_hl_justification (HL_QN x21a) (HL_EqElim (x161, x162)) = false
  | equal_hl_justification (HL_EqElim (x161, x162)) (HL_IffElim (x201, x202)) =
    false
  | equal_hl_justification (HL_IffElim (x201, x202)) (HL_EqElim (x161, x162)) =
    false
  | equal_hl_justification (HL_EqElim (x161, x162)) (HL_IffIntro (x191, x192)) =
    false
  | equal_hl_justification (HL_IffIntro (x191, x192)) (HL_EqElim (x161, x162)) =
    false
  | equal_hl_justification (HL_EqElim (x161, x162)) (HL_PropTaut x18) = false
  | equal_hl_justification (HL_PropTaut x18) (HL_EqElim (x161, x162)) = false
  | equal_hl_justification (HL_EqElim (x161, x162)) HL_LEM = false
  | equal_hl_justification HL_LEM (HL_EqElim (x161, x162)) = false
  | equal_hl_justification HL_EqIntro (HL_QN x21a) = false
  | equal_hl_justification (HL_QN x21a) HL_EqIntro = false
  | equal_hl_justification HL_EqIntro (HL_IffElim (x201, x202)) = false
  | equal_hl_justification (HL_IffElim (x201, x202)) HL_EqIntro = false
  | equal_hl_justification HL_EqIntro (HL_IffIntro (x191, x192)) = false
  | equal_hl_justification (HL_IffIntro (x191, x192)) HL_EqIntro = false
  | equal_hl_justification HL_EqIntro (HL_PropTaut x18) = false
  | equal_hl_justification (HL_PropTaut x18) HL_EqIntro = false
  | equal_hl_justification HL_EqIntro HL_LEM = false
  | equal_hl_justification HL_LEM HL_EqIntro = false
  | equal_hl_justification HL_EqIntro (HL_EqElim (x161, x162)) = false
  | equal_hl_justification (HL_EqElim (x161, x162)) HL_EqIntro = false
  | equal_hl_justification (HL_ExistsElim (x141, x142, x143)) (HL_QN x21a) =
    false
  | equal_hl_justification (HL_QN x21a) (HL_ExistsElim (x141, x142, x143)) =
    false
  | equal_hl_justification (HL_ExistsElim (x141, x142, x143))
    (HL_IffElim (x201, x202)) = false
  | equal_hl_justification (HL_IffElim (x201, x202))
    (HL_ExistsElim (x141, x142, x143)) = false
  | equal_hl_justification (HL_ExistsElim (x141, x142, x143))
    (HL_IffIntro (x191, x192)) = false
  | equal_hl_justification (HL_IffIntro (x191, x192))
    (HL_ExistsElim (x141, x142, x143)) = false
  | equal_hl_justification (HL_ExistsElim (x141, x142, x143)) (HL_PropTaut x18)
    = false
  | equal_hl_justification (HL_PropTaut x18) (HL_ExistsElim (x141, x142, x143))
    = false
  | equal_hl_justification (HL_ExistsElim (x141, x142, x143)) HL_LEM = false
  | equal_hl_justification HL_LEM (HL_ExistsElim (x141, x142, x143)) = false
  | equal_hl_justification (HL_ExistsElim (x141, x142, x143))
    (HL_EqElim (x161, x162)) = false
  | equal_hl_justification (HL_EqElim (x161, x162))
    (HL_ExistsElim (x141, x142, x143)) = false
  | equal_hl_justification (HL_ExistsElim (x141, x142, x143)) HL_EqIntro = false
  | equal_hl_justification HL_EqIntro (HL_ExistsElim (x141, x142, x143)) = false
  | equal_hl_justification (HL_ForallIntro x13) (HL_QN x21a) = false
  | equal_hl_justification (HL_QN x21a) (HL_ForallIntro x13) = false
  | equal_hl_justification (HL_ForallIntro x13) (HL_IffElim (x201, x202)) =
    false
  | equal_hl_justification (HL_IffElim (x201, x202)) (HL_ForallIntro x13) =
    false
  | equal_hl_justification (HL_ForallIntro x13) (HL_IffIntro (x191, x192)) =
    false
  | equal_hl_justification (HL_IffIntro (x191, x192)) (HL_ForallIntro x13) =
    false
  | equal_hl_justification (HL_ForallIntro x13) (HL_PropTaut x18) = false
  | equal_hl_justification (HL_PropTaut x18) (HL_ForallIntro x13) = false
  | equal_hl_justification (HL_ForallIntro x13) HL_LEM = false
  | equal_hl_justification HL_LEM (HL_ForallIntro x13) = false
  | equal_hl_justification (HL_ForallIntro x13) (HL_EqElim (x161, x162)) = false
  | equal_hl_justification (HL_EqElim (x161, x162)) (HL_ForallIntro x13) = false
  | equal_hl_justification (HL_ForallIntro x13) HL_EqIntro = false
  | equal_hl_justification HL_EqIntro (HL_ForallIntro x13) = false
  | equal_hl_justification (HL_ForallIntro x13)
    (HL_ExistsElim (x141, x142, x143)) = false
  | equal_hl_justification (HL_ExistsElim (x141, x142, x143))
    (HL_ForallIntro x13) = false
  | equal_hl_justification (HL_ExistsIntro x12) (HL_QN x21a) = false
  | equal_hl_justification (HL_QN x21a) (HL_ExistsIntro x12) = false
  | equal_hl_justification (HL_ExistsIntro x12) (HL_IffElim (x201, x202)) =
    false
  | equal_hl_justification (HL_IffElim (x201, x202)) (HL_ExistsIntro x12) =
    false
  | equal_hl_justification (HL_ExistsIntro x12) (HL_IffIntro (x191, x192)) =
    false
  | equal_hl_justification (HL_IffIntro (x191, x192)) (HL_ExistsIntro x12) =
    false
  | equal_hl_justification (HL_ExistsIntro x12) (HL_PropTaut x18) = false
  | equal_hl_justification (HL_PropTaut x18) (HL_ExistsIntro x12) = false
  | equal_hl_justification (HL_ExistsIntro x12) HL_LEM = false
  | equal_hl_justification HL_LEM (HL_ExistsIntro x12) = false
  | equal_hl_justification (HL_ExistsIntro x12) (HL_EqElim (x161, x162)) = false
  | equal_hl_justification (HL_EqElim (x161, x162)) (HL_ExistsIntro x12) = false
  | equal_hl_justification (HL_ExistsIntro x12) HL_EqIntro = false
  | equal_hl_justification HL_EqIntro (HL_ExistsIntro x12) = false
  | equal_hl_justification (HL_ExistsIntro x12)
    (HL_ExistsElim (x141, x142, x143)) = false
  | equal_hl_justification (HL_ExistsElim (x141, x142, x143))
    (HL_ExistsIntro x12) = false
  | equal_hl_justification (HL_ExistsIntro x12) (HL_ForallIntro x13) = false
  | equal_hl_justification (HL_ForallIntro x13) (HL_ExistsIntro x12) = false
  | equal_hl_justification (HL_ForallElim x11) (HL_QN x21a) = false
  | equal_hl_justification (HL_QN x21a) (HL_ForallElim x11) = false
  | equal_hl_justification (HL_ForallElim x11) (HL_IffElim (x201, x202)) = false
  | equal_hl_justification (HL_IffElim (x201, x202)) (HL_ForallElim x11) = false
  | equal_hl_justification (HL_ForallElim x11) (HL_IffIntro (x191, x192)) =
    false
  | equal_hl_justification (HL_IffIntro (x191, x192)) (HL_ForallElim x11) =
    false
  | equal_hl_justification (HL_ForallElim x11) (HL_PropTaut x18) = false
  | equal_hl_justification (HL_PropTaut x18) (HL_ForallElim x11) = false
  | equal_hl_justification (HL_ForallElim x11) HL_LEM = false
  | equal_hl_justification HL_LEM (HL_ForallElim x11) = false
  | equal_hl_justification (HL_ForallElim x11) (HL_EqElim (x161, x162)) = false
  | equal_hl_justification (HL_EqElim (x161, x162)) (HL_ForallElim x11) = false
  | equal_hl_justification (HL_ForallElim x11) HL_EqIntro = false
  | equal_hl_justification HL_EqIntro (HL_ForallElim x11) = false
  | equal_hl_justification (HL_ForallElim x11)
    (HL_ExistsElim (x141, x142, x143)) = false
  | equal_hl_justification (HL_ExistsElim (x141, x142, x143))
    (HL_ForallElim x11) = false
  | equal_hl_justification (HL_ForallElim x11) (HL_ForallIntro x13) = false
  | equal_hl_justification (HL_ForallIntro x13) (HL_ForallElim x11) = false
  | equal_hl_justification (HL_ForallElim x11) (HL_ExistsIntro x12) = false
  | equal_hl_justification (HL_ExistsIntro x12) (HL_ForallElim x11) = false
  | equal_hl_justification (HL_RAA (x101, x102)) (HL_QN x21a) = false
  | equal_hl_justification (HL_QN x21a) (HL_RAA (x101, x102)) = false
  | equal_hl_justification (HL_RAA (x101, x102)) (HL_IffElim (x201, x202)) =
    false
  | equal_hl_justification (HL_IffElim (x201, x202)) (HL_RAA (x101, x102)) =
    false
  | equal_hl_justification (HL_RAA (x101, x102)) (HL_IffIntro (x191, x192)) =
    false
  | equal_hl_justification (HL_IffIntro (x191, x192)) (HL_RAA (x101, x102)) =
    false
  | equal_hl_justification (HL_RAA (x101, x102)) (HL_PropTaut x18) = false
  | equal_hl_justification (HL_PropTaut x18) (HL_RAA (x101, x102)) = false
  | equal_hl_justification (HL_RAA (x101, x102)) HL_LEM = false
  | equal_hl_justification HL_LEM (HL_RAA (x101, x102)) = false
  | equal_hl_justification (HL_RAA (x101, x102)) (HL_EqElim (x161, x162)) =
    false
  | equal_hl_justification (HL_EqElim (x161, x162)) (HL_RAA (x101, x102)) =
    false
  | equal_hl_justification (HL_RAA (x101, x102)) HL_EqIntro = false
  | equal_hl_justification HL_EqIntro (HL_RAA (x101, x102)) = false
  | equal_hl_justification (HL_RAA (x101, x102))
    (HL_ExistsElim (x141, x142, x143)) = false
  | equal_hl_justification (HL_ExistsElim (x141, x142, x143))
    (HL_RAA (x101, x102)) = false
  | equal_hl_justification (HL_RAA (x101, x102)) (HL_ForallIntro x13) = false
  | equal_hl_justification (HL_ForallIntro x13) (HL_RAA (x101, x102)) = false
  | equal_hl_justification (HL_RAA (x101, x102)) (HL_ExistsIntro x12) = false
  | equal_hl_justification (HL_ExistsIntro x12) (HL_RAA (x101, x102)) = false
  | equal_hl_justification (HL_RAA (x101, x102)) (HL_ForallElim x11) = false
  | equal_hl_justification (HL_ForallElim x11) (HL_RAA (x101, x102)) = false
  | equal_hl_justification (HL_OrElim (x91, x92, x93, x94, x95)) (HL_QN x21a) =
    false
  | equal_hl_justification (HL_QN x21a) (HL_OrElim (x91, x92, x93, x94, x95)) =
    false
  | equal_hl_justification (HL_OrElim (x91, x92, x93, x94, x95))
    (HL_IffElim (x201, x202)) = false
  | equal_hl_justification (HL_IffElim (x201, x202))
    (HL_OrElim (x91, x92, x93, x94, x95)) = false
  | equal_hl_justification (HL_OrElim (x91, x92, x93, x94, x95))
    (HL_IffIntro (x191, x192)) = false
  | equal_hl_justification (HL_IffIntro (x191, x192))
    (HL_OrElim (x91, x92, x93, x94, x95)) = false
  | equal_hl_justification (HL_OrElim (x91, x92, x93, x94, x95))
    (HL_PropTaut x18) = false
  | equal_hl_justification (HL_PropTaut x18)
    (HL_OrElim (x91, x92, x93, x94, x95)) = false
  | equal_hl_justification (HL_OrElim (x91, x92, x93, x94, x95)) HL_LEM = false
  | equal_hl_justification HL_LEM (HL_OrElim (x91, x92, x93, x94, x95)) = false
  | equal_hl_justification (HL_OrElim (x91, x92, x93, x94, x95))
    (HL_EqElim (x161, x162)) = false
  | equal_hl_justification (HL_EqElim (x161, x162))
    (HL_OrElim (x91, x92, x93, x94, x95)) = false
  | equal_hl_justification (HL_OrElim (x91, x92, x93, x94, x95)) HL_EqIntro =
    false
  | equal_hl_justification HL_EqIntro (HL_OrElim (x91, x92, x93, x94, x95)) =
    false
  | equal_hl_justification (HL_OrElim (x91, x92, x93, x94, x95))
    (HL_ExistsElim (x141, x142, x143)) = false
  | equal_hl_justification (HL_ExistsElim (x141, x142, x143))
    (HL_OrElim (x91, x92, x93, x94, x95)) = false
  | equal_hl_justification (HL_OrElim (x91, x92, x93, x94, x95))
    (HL_ForallIntro x13) = false
  | equal_hl_justification (HL_ForallIntro x13)
    (HL_OrElim (x91, x92, x93, x94, x95)) = false
  | equal_hl_justification (HL_OrElim (x91, x92, x93, x94, x95))
    (HL_ExistsIntro x12) = false
  | equal_hl_justification (HL_ExistsIntro x12)
    (HL_OrElim (x91, x92, x93, x94, x95)) = false
  | equal_hl_justification (HL_OrElim (x91, x92, x93, x94, x95))
    (HL_ForallElim x11) = false
  | equal_hl_justification (HL_ForallElim x11)
    (HL_OrElim (x91, x92, x93, x94, x95)) = false
  | equal_hl_justification (HL_OrElim (x91, x92, x93, x94, x95))
    (HL_RAA (x101, x102)) = false
  | equal_hl_justification (HL_RAA (x101, x102))
    (HL_OrElim (x91, x92, x93, x94, x95)) = false
  | equal_hl_justification (HL_OrIntro x8) (HL_QN x21a) = false
  | equal_hl_justification (HL_QN x21a) (HL_OrIntro x8) = false
  | equal_hl_justification (HL_OrIntro x8) (HL_IffElim (x201, x202)) = false
  | equal_hl_justification (HL_IffElim (x201, x202)) (HL_OrIntro x8) = false
  | equal_hl_justification (HL_OrIntro x8) (HL_IffIntro (x191, x192)) = false
  | equal_hl_justification (HL_IffIntro (x191, x192)) (HL_OrIntro x8) = false
  | equal_hl_justification (HL_OrIntro x8) (HL_PropTaut x18) = false
  | equal_hl_justification (HL_PropTaut x18) (HL_OrIntro x8) = false
  | equal_hl_justification (HL_OrIntro x8) HL_LEM = false
  | equal_hl_justification HL_LEM (HL_OrIntro x8) = false
  | equal_hl_justification (HL_OrIntro x8) (HL_EqElim (x161, x162)) = false
  | equal_hl_justification (HL_EqElim (x161, x162)) (HL_OrIntro x8) = false
  | equal_hl_justification (HL_OrIntro x8) HL_EqIntro = false
  | equal_hl_justification HL_EqIntro (HL_OrIntro x8) = false
  | equal_hl_justification (HL_OrIntro x8) (HL_ExistsElim (x141, x142, x143)) =
    false
  | equal_hl_justification (HL_ExistsElim (x141, x142, x143)) (HL_OrIntro x8) =
    false
  | equal_hl_justification (HL_OrIntro x8) (HL_ForallIntro x13) = false
  | equal_hl_justification (HL_ForallIntro x13) (HL_OrIntro x8) = false
  | equal_hl_justification (HL_OrIntro x8) (HL_ExistsIntro x12) = false
  | equal_hl_justification (HL_ExistsIntro x12) (HL_OrIntro x8) = false
  | equal_hl_justification (HL_OrIntro x8) (HL_ForallElim x11) = false
  | equal_hl_justification (HL_ForallElim x11) (HL_OrIntro x8) = false
  | equal_hl_justification (HL_OrIntro x8) (HL_RAA (x101, x102)) = false
  | equal_hl_justification (HL_RAA (x101, x102)) (HL_OrIntro x8) = false
  | equal_hl_justification (HL_OrIntro x8) (HL_OrElim (x91, x92, x93, x94, x95))
    = false
  | equal_hl_justification (HL_OrElim (x91, x92, x93, x94, x95)) (HL_OrIntro x8)
    = false
  | equal_hl_justification (HL_AndElim x7) (HL_QN x21a) = false
  | equal_hl_justification (HL_QN x21a) (HL_AndElim x7) = false
  | equal_hl_justification (HL_AndElim x7) (HL_IffElim (x201, x202)) = false
  | equal_hl_justification (HL_IffElim (x201, x202)) (HL_AndElim x7) = false
  | equal_hl_justification (HL_AndElim x7) (HL_IffIntro (x191, x192)) = false
  | equal_hl_justification (HL_IffIntro (x191, x192)) (HL_AndElim x7) = false
  | equal_hl_justification (HL_AndElim x7) (HL_PropTaut x18) = false
  | equal_hl_justification (HL_PropTaut x18) (HL_AndElim x7) = false
  | equal_hl_justification (HL_AndElim x7) HL_LEM = false
  | equal_hl_justification HL_LEM (HL_AndElim x7) = false
  | equal_hl_justification (HL_AndElim x7) (HL_EqElim (x161, x162)) = false
  | equal_hl_justification (HL_EqElim (x161, x162)) (HL_AndElim x7) = false
  | equal_hl_justification (HL_AndElim x7) HL_EqIntro = false
  | equal_hl_justification HL_EqIntro (HL_AndElim x7) = false
  | equal_hl_justification (HL_AndElim x7) (HL_ExistsElim (x141, x142, x143)) =
    false
  | equal_hl_justification (HL_ExistsElim (x141, x142, x143)) (HL_AndElim x7) =
    false
  | equal_hl_justification (HL_AndElim x7) (HL_ForallIntro x13) = false
  | equal_hl_justification (HL_ForallIntro x13) (HL_AndElim x7) = false
  | equal_hl_justification (HL_AndElim x7) (HL_ExistsIntro x12) = false
  | equal_hl_justification (HL_ExistsIntro x12) (HL_AndElim x7) = false
  | equal_hl_justification (HL_AndElim x7) (HL_ForallElim x11) = false
  | equal_hl_justification (HL_ForallElim x11) (HL_AndElim x7) = false
  | equal_hl_justification (HL_AndElim x7) (HL_RAA (x101, x102)) = false
  | equal_hl_justification (HL_RAA (x101, x102)) (HL_AndElim x7) = false
  | equal_hl_justification (HL_AndElim x7) (HL_OrElim (x91, x92, x93, x94, x95))
    = false
  | equal_hl_justification (HL_OrElim (x91, x92, x93, x94, x95)) (HL_AndElim x7)
    = false
  | equal_hl_justification (HL_AndElim x7) (HL_OrIntro x8) = false
  | equal_hl_justification (HL_OrIntro x8) (HL_AndElim x7) = false
  | equal_hl_justification (HL_AndIntro (x61, x62)) (HL_QN x21a) = false
  | equal_hl_justification (HL_QN x21a) (HL_AndIntro (x61, x62)) = false
  | equal_hl_justification (HL_AndIntro (x61, x62)) (HL_IffElim (x201, x202)) =
    false
  | equal_hl_justification (HL_IffElim (x201, x202)) (HL_AndIntro (x61, x62)) =
    false
  | equal_hl_justification (HL_AndIntro (x61, x62)) (HL_IffIntro (x191, x192)) =
    false
  | equal_hl_justification (HL_IffIntro (x191, x192)) (HL_AndIntro (x61, x62)) =
    false
  | equal_hl_justification (HL_AndIntro (x61, x62)) (HL_PropTaut x18) = false
  | equal_hl_justification (HL_PropTaut x18) (HL_AndIntro (x61, x62)) = false
  | equal_hl_justification (HL_AndIntro (x61, x62)) HL_LEM = false
  | equal_hl_justification HL_LEM (HL_AndIntro (x61, x62)) = false
  | equal_hl_justification (HL_AndIntro (x61, x62)) (HL_EqElim (x161, x162)) =
    false
  | equal_hl_justification (HL_EqElim (x161, x162)) (HL_AndIntro (x61, x62)) =
    false
  | equal_hl_justification (HL_AndIntro (x61, x62)) HL_EqIntro = false
  | equal_hl_justification HL_EqIntro (HL_AndIntro (x61, x62)) = false
  | equal_hl_justification (HL_AndIntro (x61, x62))
    (HL_ExistsElim (x141, x142, x143)) = false
  | equal_hl_justification (HL_ExistsElim (x141, x142, x143))
    (HL_AndIntro (x61, x62)) = false
  | equal_hl_justification (HL_AndIntro (x61, x62)) (HL_ForallIntro x13) = false
  | equal_hl_justification (HL_ForallIntro x13) (HL_AndIntro (x61, x62)) = false
  | equal_hl_justification (HL_AndIntro (x61, x62)) (HL_ExistsIntro x12) = false
  | equal_hl_justification (HL_ExistsIntro x12) (HL_AndIntro (x61, x62)) = false
  | equal_hl_justification (HL_AndIntro (x61, x62)) (HL_ForallElim x11) = false
  | equal_hl_justification (HL_ForallElim x11) (HL_AndIntro (x61, x62)) = false
  | equal_hl_justification (HL_AndIntro (x61, x62)) (HL_RAA (x101, x102)) =
    false
  | equal_hl_justification (HL_RAA (x101, x102)) (HL_AndIntro (x61, x62)) =
    false
  | equal_hl_justification (HL_AndIntro (x61, x62))
    (HL_OrElim (x91, x92, x93, x94, x95)) = false
  | equal_hl_justification (HL_OrElim (x91, x92, x93, x94, x95))
    (HL_AndIntro (x61, x62)) = false
  | equal_hl_justification (HL_AndIntro (x61, x62)) (HL_OrIntro x8) = false
  | equal_hl_justification (HL_OrIntro x8) (HL_AndIntro (x61, x62)) = false
  | equal_hl_justification (HL_AndIntro (x61, x62)) (HL_AndElim x7) = false
  | equal_hl_justification (HL_AndElim x7) (HL_AndIntro (x61, x62)) = false
  | equal_hl_justification (HL_CP (x51, x52)) (HL_QN x21a) = false
  | equal_hl_justification (HL_QN x21a) (HL_CP (x51, x52)) = false
  | equal_hl_justification (HL_CP (x51, x52)) (HL_IffElim (x201, x202)) = false
  | equal_hl_justification (HL_IffElim (x201, x202)) (HL_CP (x51, x52)) = false
  | equal_hl_justification (HL_CP (x51, x52)) (HL_IffIntro (x191, x192)) = false
  | equal_hl_justification (HL_IffIntro (x191, x192)) (HL_CP (x51, x52)) = false
  | equal_hl_justification (HL_CP (x51, x52)) (HL_PropTaut x18) = false
  | equal_hl_justification (HL_PropTaut x18) (HL_CP (x51, x52)) = false
  | equal_hl_justification (HL_CP (x51, x52)) HL_LEM = false
  | equal_hl_justification HL_LEM (HL_CP (x51, x52)) = false
  | equal_hl_justification (HL_CP (x51, x52)) (HL_EqElim (x161, x162)) = false
  | equal_hl_justification (HL_EqElim (x161, x162)) (HL_CP (x51, x52)) = false
  | equal_hl_justification (HL_CP (x51, x52)) HL_EqIntro = false
  | equal_hl_justification HL_EqIntro (HL_CP (x51, x52)) = false
  | equal_hl_justification (HL_CP (x51, x52)) (HL_ExistsElim (x141, x142, x143))
    = false
  | equal_hl_justification (HL_ExistsElim (x141, x142, x143)) (HL_CP (x51, x52))
    = false
  | equal_hl_justification (HL_CP (x51, x52)) (HL_ForallIntro x13) = false
  | equal_hl_justification (HL_ForallIntro x13) (HL_CP (x51, x52)) = false
  | equal_hl_justification (HL_CP (x51, x52)) (HL_ExistsIntro x12) = false
  | equal_hl_justification (HL_ExistsIntro x12) (HL_CP (x51, x52)) = false
  | equal_hl_justification (HL_CP (x51, x52)) (HL_ForallElim x11) = false
  | equal_hl_justification (HL_ForallElim x11) (HL_CP (x51, x52)) = false
  | equal_hl_justification (HL_CP (x51, x52)) (HL_RAA (x101, x102)) = false
  | equal_hl_justification (HL_RAA (x101, x102)) (HL_CP (x51, x52)) = false
  | equal_hl_justification (HL_CP (x51, x52))
    (HL_OrElim (x91, x92, x93, x94, x95)) = false
  | equal_hl_justification (HL_OrElim (x91, x92, x93, x94, x95))
    (HL_CP (x51, x52)) = false
  | equal_hl_justification (HL_CP (x51, x52)) (HL_OrIntro x8) = false
  | equal_hl_justification (HL_OrIntro x8) (HL_CP (x51, x52)) = false
  | equal_hl_justification (HL_CP (x51, x52)) (HL_AndElim x7) = false
  | equal_hl_justification (HL_AndElim x7) (HL_CP (x51, x52)) = false
  | equal_hl_justification (HL_CP (x51, x52)) (HL_AndIntro (x61, x62)) = false
  | equal_hl_justification (HL_AndIntro (x61, x62)) (HL_CP (x51, x52)) = false
  | equal_hl_justification (HL_DN x4) (HL_QN x21a) = false
  | equal_hl_justification (HL_QN x21a) (HL_DN x4) = false
  | equal_hl_justification (HL_DN x4) (HL_IffElim (x201, x202)) = false
  | equal_hl_justification (HL_IffElim (x201, x202)) (HL_DN x4) = false
  | equal_hl_justification (HL_DN x4) (HL_IffIntro (x191, x192)) = false
  | equal_hl_justification (HL_IffIntro (x191, x192)) (HL_DN x4) = false
  | equal_hl_justification (HL_DN x4) (HL_PropTaut x18) = false
  | equal_hl_justification (HL_PropTaut x18) (HL_DN x4) = false
  | equal_hl_justification (HL_DN x4) HL_LEM = false
  | equal_hl_justification HL_LEM (HL_DN x4) = false
  | equal_hl_justification (HL_DN x4) (HL_EqElim (x161, x162)) = false
  | equal_hl_justification (HL_EqElim (x161, x162)) (HL_DN x4) = false
  | equal_hl_justification (HL_DN x4) HL_EqIntro = false
  | equal_hl_justification HL_EqIntro (HL_DN x4) = false
  | equal_hl_justification (HL_DN x4) (HL_ExistsElim (x141, x142, x143)) = false
  | equal_hl_justification (HL_ExistsElim (x141, x142, x143)) (HL_DN x4) = false
  | equal_hl_justification (HL_DN x4) (HL_ForallIntro x13) = false
  | equal_hl_justification (HL_ForallIntro x13) (HL_DN x4) = false
  | equal_hl_justification (HL_DN x4) (HL_ExistsIntro x12) = false
  | equal_hl_justification (HL_ExistsIntro x12) (HL_DN x4) = false
  | equal_hl_justification (HL_DN x4) (HL_ForallElim x11) = false
  | equal_hl_justification (HL_ForallElim x11) (HL_DN x4) = false
  | equal_hl_justification (HL_DN x4) (HL_RAA (x101, x102)) = false
  | equal_hl_justification (HL_RAA (x101, x102)) (HL_DN x4) = false
  | equal_hl_justification (HL_DN x4) (HL_OrElim (x91, x92, x93, x94, x95)) =
    false
  | equal_hl_justification (HL_OrElim (x91, x92, x93, x94, x95)) (HL_DN x4) =
    false
  | equal_hl_justification (HL_DN x4) (HL_OrIntro x8) = false
  | equal_hl_justification (HL_OrIntro x8) (HL_DN x4) = false
  | equal_hl_justification (HL_DN x4) (HL_AndElim x7) = false
  | equal_hl_justification (HL_AndElim x7) (HL_DN x4) = false
  | equal_hl_justification (HL_DN x4) (HL_AndIntro (x61, x62)) = false
  | equal_hl_justification (HL_AndIntro (x61, x62)) (HL_DN x4) = false
  | equal_hl_justification (HL_DN x4) (HL_CP (x51, x52)) = false
  | equal_hl_justification (HL_CP (x51, x52)) (HL_DN x4) = false
  | equal_hl_justification (HL_MT (x31, x32)) (HL_QN x21a) = false
  | equal_hl_justification (HL_QN x21a) (HL_MT (x31, x32)) = false
  | equal_hl_justification (HL_MT (x31, x32)) (HL_IffElim (x201, x202)) = false
  | equal_hl_justification (HL_IffElim (x201, x202)) (HL_MT (x31, x32)) = false
  | equal_hl_justification (HL_MT (x31, x32)) (HL_IffIntro (x191, x192)) = false
  | equal_hl_justification (HL_IffIntro (x191, x192)) (HL_MT (x31, x32)) = false
  | equal_hl_justification (HL_MT (x31, x32)) (HL_PropTaut x18) = false
  | equal_hl_justification (HL_PropTaut x18) (HL_MT (x31, x32)) = false
  | equal_hl_justification (HL_MT (x31, x32)) HL_LEM = false
  | equal_hl_justification HL_LEM (HL_MT (x31, x32)) = false
  | equal_hl_justification (HL_MT (x31, x32)) (HL_EqElim (x161, x162)) = false
  | equal_hl_justification (HL_EqElim (x161, x162)) (HL_MT (x31, x32)) = false
  | equal_hl_justification (HL_MT (x31, x32)) HL_EqIntro = false
  | equal_hl_justification HL_EqIntro (HL_MT (x31, x32)) = false
  | equal_hl_justification (HL_MT (x31, x32)) (HL_ExistsElim (x141, x142, x143))
    = false
  | equal_hl_justification (HL_ExistsElim (x141, x142, x143)) (HL_MT (x31, x32))
    = false
  | equal_hl_justification (HL_MT (x31, x32)) (HL_ForallIntro x13) = false
  | equal_hl_justification (HL_ForallIntro x13) (HL_MT (x31, x32)) = false
  | equal_hl_justification (HL_MT (x31, x32)) (HL_ExistsIntro x12) = false
  | equal_hl_justification (HL_ExistsIntro x12) (HL_MT (x31, x32)) = false
  | equal_hl_justification (HL_MT (x31, x32)) (HL_ForallElim x11) = false
  | equal_hl_justification (HL_ForallElim x11) (HL_MT (x31, x32)) = false
  | equal_hl_justification (HL_MT (x31, x32)) (HL_RAA (x101, x102)) = false
  | equal_hl_justification (HL_RAA (x101, x102)) (HL_MT (x31, x32)) = false
  | equal_hl_justification (HL_MT (x31, x32))
    (HL_OrElim (x91, x92, x93, x94, x95)) = false
  | equal_hl_justification (HL_OrElim (x91, x92, x93, x94, x95))
    (HL_MT (x31, x32)) = false
  | equal_hl_justification (HL_MT (x31, x32)) (HL_OrIntro x8) = false
  | equal_hl_justification (HL_OrIntro x8) (HL_MT (x31, x32)) = false
  | equal_hl_justification (HL_MT (x31, x32)) (HL_AndElim x7) = false
  | equal_hl_justification (HL_AndElim x7) (HL_MT (x31, x32)) = false
  | equal_hl_justification (HL_MT (x31, x32)) (HL_AndIntro (x61, x62)) = false
  | equal_hl_justification (HL_AndIntro (x61, x62)) (HL_MT (x31, x32)) = false
  | equal_hl_justification (HL_MT (x31, x32)) (HL_CP (x51, x52)) = false
  | equal_hl_justification (HL_CP (x51, x52)) (HL_MT (x31, x32)) = false
  | equal_hl_justification (HL_MT (x31, x32)) (HL_DN x4) = false
  | equal_hl_justification (HL_DN x4) (HL_MT (x31, x32)) = false
  | equal_hl_justification (HL_MP (x21, x22)) (HL_QN x21a) = false
  | equal_hl_justification (HL_QN x21a) (HL_MP (x21, x22)) = false
  | equal_hl_justification (HL_MP (x21, x22)) (HL_IffElim (x201, x202)) = false
  | equal_hl_justification (HL_IffElim (x201, x202)) (HL_MP (x21, x22)) = false
  | equal_hl_justification (HL_MP (x21, x22)) (HL_IffIntro (x191, x192)) = false
  | equal_hl_justification (HL_IffIntro (x191, x192)) (HL_MP (x21, x22)) = false
  | equal_hl_justification (HL_MP (x21, x22)) (HL_PropTaut x18) = false
  | equal_hl_justification (HL_PropTaut x18) (HL_MP (x21, x22)) = false
  | equal_hl_justification (HL_MP (x21, x22)) HL_LEM = false
  | equal_hl_justification HL_LEM (HL_MP (x21, x22)) = false
  | equal_hl_justification (HL_MP (x21, x22)) (HL_EqElim (x161, x162)) = false
  | equal_hl_justification (HL_EqElim (x161, x162)) (HL_MP (x21, x22)) = false
  | equal_hl_justification (HL_MP (x21, x22)) HL_EqIntro = false
  | equal_hl_justification HL_EqIntro (HL_MP (x21, x22)) = false
  | equal_hl_justification (HL_MP (x21, x22)) (HL_ExistsElim (x141, x142, x143))
    = false
  | equal_hl_justification (HL_ExistsElim (x141, x142, x143)) (HL_MP (x21, x22))
    = false
  | equal_hl_justification (HL_MP (x21, x22)) (HL_ForallIntro x13) = false
  | equal_hl_justification (HL_ForallIntro x13) (HL_MP (x21, x22)) = false
  | equal_hl_justification (HL_MP (x21, x22)) (HL_ExistsIntro x12) = false
  | equal_hl_justification (HL_ExistsIntro x12) (HL_MP (x21, x22)) = false
  | equal_hl_justification (HL_MP (x21, x22)) (HL_ForallElim x11) = false
  | equal_hl_justification (HL_ForallElim x11) (HL_MP (x21, x22)) = false
  | equal_hl_justification (HL_MP (x21, x22)) (HL_RAA (x101, x102)) = false
  | equal_hl_justification (HL_RAA (x101, x102)) (HL_MP (x21, x22)) = false
  | equal_hl_justification (HL_MP (x21, x22))
    (HL_OrElim (x91, x92, x93, x94, x95)) = false
  | equal_hl_justification (HL_OrElim (x91, x92, x93, x94, x95))
    (HL_MP (x21, x22)) = false
  | equal_hl_justification (HL_MP (x21, x22)) (HL_OrIntro x8) = false
  | equal_hl_justification (HL_OrIntro x8) (HL_MP (x21, x22)) = false
  | equal_hl_justification (HL_MP (x21, x22)) (HL_AndElim x7) = false
  | equal_hl_justification (HL_AndElim x7) (HL_MP (x21, x22)) = false
  | equal_hl_justification (HL_MP (x21, x22)) (HL_AndIntro (x61, x62)) = false
  | equal_hl_justification (HL_AndIntro (x61, x62)) (HL_MP (x21, x22)) = false
  | equal_hl_justification (HL_MP (x21, x22)) (HL_CP (x51, x52)) = false
  | equal_hl_justification (HL_CP (x51, x52)) (HL_MP (x21, x22)) = false
  | equal_hl_justification (HL_MP (x21, x22)) (HL_DN x4) = false
  | equal_hl_justification (HL_DN x4) (HL_MP (x21, x22)) = false
  | equal_hl_justification (HL_MP (x21, x22)) (HL_MT (x31, x32)) = false
  | equal_hl_justification (HL_MT (x31, x32)) (HL_MP (x21, x22)) = false
  | equal_hl_justification HL_Assumption (HL_QN x21a) = false
  | equal_hl_justification (HL_QN x21a) HL_Assumption = false
  | equal_hl_justification HL_Assumption (HL_IffElim (x201, x202)) = false
  | equal_hl_justification (HL_IffElim (x201, x202)) HL_Assumption = false
  | equal_hl_justification HL_Assumption (HL_IffIntro (x191, x192)) = false
  | equal_hl_justification (HL_IffIntro (x191, x192)) HL_Assumption = false
  | equal_hl_justification HL_Assumption (HL_PropTaut x18) = false
  | equal_hl_justification (HL_PropTaut x18) HL_Assumption = false
  | equal_hl_justification HL_Assumption HL_LEM = false
  | equal_hl_justification HL_LEM HL_Assumption = false
  | equal_hl_justification HL_Assumption (HL_EqElim (x161, x162)) = false
  | equal_hl_justification (HL_EqElim (x161, x162)) HL_Assumption = false
  | equal_hl_justification HL_Assumption HL_EqIntro = false
  | equal_hl_justification HL_EqIntro HL_Assumption = false
  | equal_hl_justification HL_Assumption (HL_ExistsElim (x141, x142, x143)) =
    false
  | equal_hl_justification (HL_ExistsElim (x141, x142, x143)) HL_Assumption =
    false
  | equal_hl_justification HL_Assumption (HL_ForallIntro x13) = false
  | equal_hl_justification (HL_ForallIntro x13) HL_Assumption = false
  | equal_hl_justification HL_Assumption (HL_ExistsIntro x12) = false
  | equal_hl_justification (HL_ExistsIntro x12) HL_Assumption = false
  | equal_hl_justification HL_Assumption (HL_ForallElim x11) = false
  | equal_hl_justification (HL_ForallElim x11) HL_Assumption = false
  | equal_hl_justification HL_Assumption (HL_RAA (x101, x102)) = false
  | equal_hl_justification (HL_RAA (x101, x102)) HL_Assumption = false
  | equal_hl_justification HL_Assumption (HL_OrElim (x91, x92, x93, x94, x95)) =
    false
  | equal_hl_justification (HL_OrElim (x91, x92, x93, x94, x95)) HL_Assumption =
    false
  | equal_hl_justification HL_Assumption (HL_OrIntro x8) = false
  | equal_hl_justification (HL_OrIntro x8) HL_Assumption = false
  | equal_hl_justification HL_Assumption (HL_AndElim x7) = false
  | equal_hl_justification (HL_AndElim x7) HL_Assumption = false
  | equal_hl_justification HL_Assumption (HL_AndIntro (x61, x62)) = false
  | equal_hl_justification (HL_AndIntro (x61, x62)) HL_Assumption = false
  | equal_hl_justification HL_Assumption (HL_CP (x51, x52)) = false
  | equal_hl_justification (HL_CP (x51, x52)) HL_Assumption = false
  | equal_hl_justification HL_Assumption (HL_DN x4) = false
  | equal_hl_justification (HL_DN x4) HL_Assumption = false
  | equal_hl_justification HL_Assumption (HL_MT (x31, x32)) = false
  | equal_hl_justification (HL_MT (x31, x32)) HL_Assumption = false
  | equal_hl_justification HL_Assumption (HL_MP (x21, x22)) = false
  | equal_hl_justification (HL_MP (x21, x22)) HL_Assumption = false
  | equal_hl_justification (HL_QN x21a) (HL_QN y21a) = equal_inta x21a y21a
  | equal_hl_justification (HL_IffElim (x201, x202)) (HL_IffElim (y201, y202)) =
    equal_inta x201 y201 andalso equal_inta x202 y202
  | equal_hl_justification (HL_IffIntro (x191, x192)) (HL_IffIntro (y191, y192))
    = equal_inta x191 y191 andalso equal_inta x192 y192
  | equal_hl_justification (HL_PropTaut x18) (HL_PropTaut y18) =
    equal_lista equal_int x18 y18
  | equal_hl_justification (HL_EqElim (x161, x162)) (HL_EqElim (y161, y162)) =
    equal_inta x161 y161 andalso equal_inta x162 y162
  | equal_hl_justification (HL_ExistsElim (x141, x142, x143))
    (HL_ExistsElim (y141, y142, y143)) =
    equal_inta x141 y141 andalso
      (equal_inta x142 y142 andalso equal_inta x143 y143)
  | equal_hl_justification (HL_ForallIntro x13) (HL_ForallIntro y13) =
    equal_inta x13 y13
  | equal_hl_justification (HL_ExistsIntro x12) (HL_ExistsIntro y12) =
    equal_inta x12 y12
  | equal_hl_justification (HL_ForallElim x11) (HL_ForallElim y11) =
    equal_inta x11 y11
  | equal_hl_justification (HL_RAA (x101, x102)) (HL_RAA (y101, y102)) =
    equal_inta x101 y101 andalso equal_inta x102 y102
  | equal_hl_justification (HL_OrElim (x91, x92, x93, x94, x95))
    (HL_OrElim (y91, y92, y93, y94, y95)) =
    equal_inta x91 y91 andalso
      (equal_inta x92 y92 andalso
        (equal_inta x93 y93 andalso
          (equal_inta x94 y94 andalso equal_inta x95 y95)))
  | equal_hl_justification (HL_OrIntro x8) (HL_OrIntro y8) = equal_inta x8 y8
  | equal_hl_justification (HL_AndElim x7) (HL_AndElim y7) = equal_inta x7 y7
  | equal_hl_justification (HL_AndIntro (x61, x62)) (HL_AndIntro (y61, y62)) =
    equal_inta x61 y61 andalso equal_inta x62 y62
  | equal_hl_justification (HL_CP (x51, x52)) (HL_CP (y51, y52)) =
    equal_inta x51 y51 andalso equal_inta x52 y52
  | equal_hl_justification (HL_DN x4) (HL_DN y4) = equal_inta x4 y4
  | equal_hl_justification (HL_MT (x31, x32)) (HL_MT (y31, y32)) =
    equal_inta x31 y31 andalso equal_inta x32 y32
  | equal_hl_justification (HL_MP (x21, x22)) (HL_MP (y21, y22)) =
    equal_inta x21 y21 andalso equal_inta x22 y22
  | equal_hl_justification HL_LEM HL_LEM = true
  | equal_hl_justification HL_EqIntro HL_EqIntro = true
  | equal_hl_justification HL_Assumption HL_Assumption = true;

fun hlQuantifierNegationForms (HL_Not (HL_ForAll (x, p))) =
  HL_Not (HL_ForAll (x, p)) ::
    map (fn a => HL_Exists (x, a)) (hlQuantifierNegationForms (HL_Not p))
  | hlQuantifierNegationForms (HL_Not (HL_Exists (x, p))) =
    HL_Not (HL_Exists (x, p)) ::
      map (fn a => HL_ForAll (x, a)) (hlQuantifierNegationForms (HL_Not p))
  | hlQuantifierNegationForms (HL_ForAll (x, p)) =
    map (fn a => HL_ForAll (x, a)) (hlQuantifierNegationForms p)
  | hlQuantifierNegationForms (HL_Exists (x, p)) =
    map (fn a => HL_Exists (x, a)) (hlQuantifierNegationForms p)
  | hlQuantifierNegationForms (HL_Predicate (v, va)) = [HL_Predicate (v, va)]
  | hlQuantifierNegationForms (HL_Boolean v) = [HL_Boolean v]
  | hlQuantifierNegationForms (HL_Not (HL_Predicate (va, vb))) =
    [HL_Not (HL_Predicate (va, vb))]
  | hlQuantifierNegationForms (HL_Not (HL_Boolean va)) =
    [HL_Not (HL_Boolean va)]
  | hlQuantifierNegationForms (HL_Not (HL_Not va)) = [HL_Not (HL_Not va)]
  | hlQuantifierNegationForms (HL_Not (HL_And (va, vb))) =
    [HL_Not (HL_And (va, vb))]
  | hlQuantifierNegationForms (HL_Not (HL_Or (va, vb))) =
    [HL_Not (HL_Or (va, vb))]
  | hlQuantifierNegationForms (HL_Not (HL_Implies (va, vb))) =
    [HL_Not (HL_Implies (va, vb))]
  | hlQuantifierNegationForms (HL_Not (HL_Iff (va, vb))) =
    [HL_Not (HL_Iff (va, vb))]
  | hlQuantifierNegationForms (HL_And (v, va)) = [HL_And (v, va)]
  | hlQuantifierNegationForms (HL_Or (v, va)) = [HL_Or (v, va)]
  | hlQuantifierNegationForms (HL_Implies (v, va)) = [HL_Implies (v, va)]
  | hlQuantifierNegationForms (HL_Iff (v, va)) = [HL_Iff (v, va)];

fun hlQuantifierNegationReachable p q =
  (case p of HL_Predicate (_, _) => false | HL_Boolean _ => false
    | HL_Not _ => membera equal_hl_formula (hlQuantifierNegationForms p) q
    | HL_And (_, _) => false | HL_Or (_, _) => false
    | HL_Implies (_, _) => false | HL_Iff (_, _) => false
    | HL_ForAll (_, _) => false | HL_Exists (_, _) => false);

fun hlQuantifierNegationEquivalent p q =
  hlQuantifierNegationReachable p q orelse hlQuantifierNegationReachable q p;

fun hlTermEqualUpToConstantReplacement a b (HL_Var x) (HL_Var y) =
  ((x : string) = y)
  | hlTermEqualUpToConstantReplacement a b (HL_Const c) (HL_Const d) =
    ((c : string) = a) andalso ((d : string) = b) orelse ((c : string) = d)
  | hlTermEqualUpToConstantReplacement a b (HL_Const v) (HL_Var va) = false
  | hlTermEqualUpToConstantReplacement a b (HL_Var va) (HL_Const v) = false;

fun list_all2 p [] ys = null ys
  | list_all2 p xs [] = null xs
  | list_all2 p (x :: xs) (y :: ys) = p x y andalso list_all2 p xs ys;

fun hlEqualUpToConstantReplacement a b p q =
  (case p
    of HL_Predicate (pa, ts) =>
      (case q
        of HL_Predicate (qa, us) =>
          ((pa : string) = qa) andalso
            list_all2 (hlTermEqualUpToConstantReplacement a b) ts us
        | HL_Boolean _ => false | HL_Not _ => false | HL_And (_, _) => false
        | HL_Or (_, _) => false | HL_Implies (_, _) => false
        | HL_Iff (_, _) => false | HL_ForAll (_, _) => false
        | HL_Exists (_, _) => false)
    | HL_Boolean c =>
      (case q of HL_Predicate (_, _) => false | HL_Boolean aa => equal_bool c aa
        | HL_Not _ => false | HL_And (_, _) => false | HL_Or (_, _) => false
        | HL_Implies (_, _) => false | HL_Iff (_, _) => false
        | HL_ForAll (_, _) => false | HL_Exists (_, _) => false)
    | HL_Not r =>
      (case q of HL_Predicate (_, _) => false | HL_Boolean _ => false
        | HL_Not c => hlEqualUpToConstantReplacement a b r c
        | HL_And (_, _) => false | HL_Or (_, _) => false
        | HL_Implies (_, _) => false | HL_Iff (_, _) => false
        | HL_ForAll (_, _) => false | HL_Exists (_, _) => false)
    | HL_And (r, s) =>
      (case q of HL_Predicate (_, _) => false | HL_Boolean _ => false
        | HL_Not _ => false
        | HL_And (u, v) =>
          hlEqualUpToConstantReplacement a b r u andalso
            hlEqualUpToConstantReplacement a b s v
        | HL_Or (_, _) => false | HL_Implies (_, _) => false
        | HL_Iff (_, _) => false | HL_ForAll (_, _) => false
        | HL_Exists (_, _) => false)
    | HL_Or (r, s) =>
      (case q of HL_Predicate (_, _) => false | HL_Boolean _ => false
        | HL_Not _ => false | HL_And (_, _) => false
        | HL_Or (u, v) =>
          hlEqualUpToConstantReplacement a b r u andalso
            hlEqualUpToConstantReplacement a b s v
        | HL_Implies (_, _) => false | HL_Iff (_, _) => false
        | HL_ForAll (_, _) => false | HL_Exists (_, _) => false)
    | HL_Implies (r, s) =>
      (case q of HL_Predicate (_, _) => false | HL_Boolean _ => false
        | HL_Not _ => false | HL_And (_, _) => false | HL_Or (_, _) => false
        | HL_Implies (u, v) =>
          hlEqualUpToConstantReplacement a b r u andalso
            hlEqualUpToConstantReplacement a b s v
        | HL_Iff (_, _) => false | HL_ForAll (_, _) => false
        | HL_Exists (_, _) => false)
    | HL_Iff (r, s) =>
      (case q of HL_Predicate (_, _) => false | HL_Boolean _ => false
        | HL_Not _ => false | HL_And (_, _) => false | HL_Or (_, _) => false
        | HL_Implies (_, _) => false
        | HL_Iff (u, v) =>
          hlEqualUpToConstantReplacement a b r u andalso
            hlEqualUpToConstantReplacement a b s v
        | HL_ForAll (_, _) => false | HL_Exists (_, _) => false)
    | HL_ForAll (x, r) =>
      (case q of HL_Predicate (_, _) => false | HL_Boolean _ => false
        | HL_Not _ => false | HL_And (_, _) => false | HL_Or (_, _) => false
        | HL_Implies (_, _) => false | HL_Iff (_, _) => false
        | HL_ForAll (y, s) =>
          ((x : string) = y) andalso hlEqualUpToConstantReplacement a b r s
        | HL_Exists (_, _) => false)
    | HL_Exists (x, r) =>
      (case q of HL_Predicate (_, _) => false | HL_Boolean _ => false
        | HL_Not _ => false | HL_And (_, _) => false | HL_Or (_, _) => false
        | HL_Implies (_, _) => false | HL_Iff (_, _) => false
        | HL_ForAll (_, _) => false
        | HL_Exists (y, s) =>
          ((x : string) = y) andalso hlEqualUpToConstantReplacement a b r s));

fun equal_option A_ NONE (SOME x2) = false
  | equal_option A_ (SOME x2) NONE = false
  | equal_option A_ (SOME x2) (SOME y2) = eq A_ x2 y2
  | equal_option A_ NONE NONE = true;

fun insort_key B_ f x [] = [x]
  | insort_key B_ f x (y :: ys) =
    (if less_eq ((ord_preorder o preorder_order o order_linorder) B_) (f x)
          (f y)
      then x :: y :: ys else y :: insort_key B_ f x ys);

fun sort_key B_ f xs = foldr (insort_key B_ f) xs [];

fun sorted_list_of_set (A1_, A2_) (Set xs) =
  sort_key A2_ (fn x => x) (remdups A1_ xs);

fun sup_set A_ (Set xs) a = fold (insert A_) xs a
  | sup_set A_ (Coset xs) a = Coset (filtera (fn x => not (member A_ x a)) xs);

val bot_set : 'a set = Set [];

fun sup_seta A_ (Set xs) = fold (sup_set A_) xs bot_set;

fun hlConstantsInTerm (HL_Var uu) = bot_set
  | hlConstantsInTerm (HL_Const a) = insert equal_literal a bot_set;

fun hlConstantsInFormula (HL_Predicate (uu, ts)) =
  sup_seta equal_literal (image hlConstantsInTerm (Set ts))
  | hlConstantsInFormula (HL_Boolean uv) = bot_set
  | hlConstantsInFormula (HL_Not p) = hlConstantsInFormula p
  | hlConstantsInFormula (HL_And (p, q)) =
    sup_set equal_literal (hlConstantsInFormula p) (hlConstantsInFormula q)
  | hlConstantsInFormula (HL_Or (p, q)) =
    sup_set equal_literal (hlConstantsInFormula p) (hlConstantsInFormula q)
  | hlConstantsInFormula (HL_Implies (p, q)) =
    sup_set equal_literal (hlConstantsInFormula p) (hlConstantsInFormula q)
  | hlConstantsInFormula (HL_Iff (p, q)) =
    sup_set equal_literal (hlConstantsInFormula p) (hlConstantsInFormula q)
  | hlConstantsInFormula (HL_ForAll (uw, p)) = hlConstantsInFormula p
  | hlConstantsInFormula (HL_Exists (ux, p)) = hlConstantsInFormula p;

fun hlSubstituteTerm x t (HL_Var y) =
  (if ((x : string) = y) then t else HL_Var y)
  | hlSubstituteTerm x t (HL_Const a) = HL_Const a;

fun hlSubstituteFree x t (HL_Predicate (p, ts)) =
  HL_Predicate (p, map (hlSubstituteTerm x t) ts)
  | hlSubstituteFree x t (HL_Boolean b) = HL_Boolean b
  | hlSubstituteFree x t (HL_Not p) = HL_Not (hlSubstituteFree x t p)
  | hlSubstituteFree x t (HL_And (p, q)) =
    HL_And (hlSubstituteFree x t p, hlSubstituteFree x t q)
  | hlSubstituteFree x t (HL_Or (p, q)) =
    HL_Or (hlSubstituteFree x t p, hlSubstituteFree x t q)
  | hlSubstituteFree x t (HL_Implies (p, q)) =
    HL_Implies (hlSubstituteFree x t p, hlSubstituteFree x t q)
  | hlSubstituteFree x t (HL_Iff (p, q)) =
    HL_Iff (hlSubstituteFree x t p, hlSubstituteFree x t q)
  | hlSubstituteFree x t (HL_ForAll (y, p)) =
    HL_ForAll (y, (if ((x : string) = y) then p else hlSubstituteFree x t p))
  | hlSubstituteFree x t (HL_Exists (y, p)) =
    HL_Exists (y, (if ((x : string) = y) then p else hlSubstituteFree x t p));

fun hlVariablesInTerm (HL_Var x) = insert equal_literal x bot_set
  | hlVariablesInTerm (HL_Const uu) = bot_set;

fun hlFreeVariables (HL_Predicate (uu, ts)) =
  sup_seta equal_literal (image hlVariablesInTerm (Set ts))
  | hlFreeVariables (HL_Boolean uv) = bot_set
  | hlFreeVariables (HL_Not p) = hlFreeVariables p
  | hlFreeVariables (HL_And (p, q)) =
    sup_set equal_literal (hlFreeVariables p) (hlFreeVariables q)
  | hlFreeVariables (HL_Or (p, q)) =
    sup_set equal_literal (hlFreeVariables p) (hlFreeVariables q)
  | hlFreeVariables (HL_Implies (p, q)) =
    sup_set equal_literal (hlFreeVariables p) (hlFreeVariables q)
  | hlFreeVariables (HL_Iff (p, q)) =
    sup_set equal_literal (hlFreeVariables p) (hlFreeVariables q)
  | hlFreeVariables (HL_ForAll (x, p)) =
    remove equal_literal x (hlFreeVariables p)
  | hlFreeVariables (HL_Exists (x, p)) =
    remove equal_literal x (hlFreeVariables p);

fun hlWitnessLists [] p q = (if equal_hl_formulaa p q then [[]] else [])
  | hlWitnessLists (x :: xs) p q =
    (if not (member equal_literal x (hlFreeVariables p))
      then map (fn a => "" :: a) (hlWitnessLists xs p q)
      else maps (fn a =>
                  map (fn b => a :: b)
                    (hlWitnessLists xs (hlSubstituteFree x (HL_Const a) p) q))
             (sorted_list_of_set (equal_literal, linorder_literal)
               (hlConstantsInFormula q)));

fun hlInferWitnessConstsK xs p k q =
  let
    val candidates = hlWitnessLists (take k xs) p q;
  in
    (if null candidates then NONE else SOME (last candidates))
  end;

fun hlEliminationCount source destination =
  let
    val k = minus_nat (size_lista source) (size_lista destination);
  in
    (if less_eq_nat (size_lista destination) (size_lista source) andalso
          equal_lista equal_literal (drop k source) destination
      then SOME k else NONE)
  end;

fun hlPropositionalValue v (HL_Boolean b) = b
  | hlPropositionalValue v (HL_Not p) = not (hlPropositionalValue v p)
  | hlPropositionalValue v (HL_And (p, q)) =
    hlPropositionalValue v p andalso hlPropositionalValue v q
  | hlPropositionalValue v (HL_Or (p, q)) =
    hlPropositionalValue v p orelse hlPropositionalValue v q
  | hlPropositionalValue v (HL_Implies (p, q)) =
    (if hlPropositionalValue v p then hlPropositionalValue v q else true)
  | hlPropositionalValue v (HL_Iff (p, q)) =
    equal_bool (hlPropositionalValue v p) (hlPropositionalValue v q)
  | hlPropositionalValue v (HL_Predicate (va, vb)) = v (HL_Predicate (va, vb))
  | hlPropositionalValue v (HL_ForAll (va, vb)) = v (HL_ForAll (va, vb))
  | hlPropositionalValue v (HL_Exists (va, vb)) = v (HL_Exists (va, vb));

fun hlPropositionalAtoms (HL_Predicate (p, ts)) = [HL_Predicate (p, ts)]
  | hlPropositionalAtoms (HL_Boolean uu) = []
  | hlPropositionalAtoms (HL_Not p) = hlPropositionalAtoms p
  | hlPropositionalAtoms (HL_And (p, q)) =
    hlPropositionalAtoms p @ hlPropositionalAtoms q
  | hlPropositionalAtoms (HL_Or (p, q)) =
    hlPropositionalAtoms p @ hlPropositionalAtoms q
  | hlPropositionalAtoms (HL_Implies (p, q)) =
    hlPropositionalAtoms p @ hlPropositionalAtoms q
  | hlPropositionalAtoms (HL_Iff (p, q)) =
    hlPropositionalAtoms p @ hlPropositionalAtoms q
  | hlPropositionalAtoms (HL_ForAll (v, va)) = [HL_ForAll (v, va)]
  | hlPropositionalAtoms (HL_Exists (v, va)) = [HL_Exists (v, va)];

fun hlValuations [] = [(fn _ => false)]
  | hlValuations (p :: ps) =
    map (fn v => fun_upd equal_hl_formula v p false) (hlValuations ps) @
      map (fn v => fun_upd equal_hl_formula v p true) (hlValuations ps);

fun hlPropositionalConsequence premises conclusion =
  let
    val atoms =
      remdups equal_hl_formula
        (maps hlPropositionalAtoms (conclusion :: premises));
  in
    list_all
      (fn v =>
        (if list_all (hlPropositionalValue v) premises
          then hlPropositionalValue v conclusion else true))
      (hlValuations atoms)
  end;

fun hlEqualityFormula (HL_Predicate (p, [t, u])) =
  (if ((p : string) = "=") then SOME (t, u) else NONE)
  | hlEqualityFormula (HL_Predicate (v, [])) = NONE
  | hlEqualityFormula (HL_Predicate (v, [vb])) = NONE
  | hlEqualityFormula (HL_Predicate (v, vb :: vd :: vf :: vg)) = NONE
  | hlEqualityFormula (HL_Boolean v) = NONE
  | hlEqualityFormula (HL_Not v) = NONE
  | hlEqualityFormula (HL_And (v, va)) = NONE
  | hlEqualityFormula (HL_Or (v, va)) = NONE
  | hlEqualityFormula (HL_Implies (v, va)) = NONE
  | hlEqualityFormula (HL_Iff (v, va)) = NONE
  | hlEqualityFormula (HL_ForAll (v, va)) = NONE
  | hlEqualityFormula (HL_Exists (v, va)) = NONE;

fun hlCollectForalls (HL_ForAll (x, p)) = let
    val (xs, a) = hlCollectForalls p;
  in
    (x :: xs, a)
  end
  | hlCollectForalls (HL_Predicate (v, va)) = ([], HL_Predicate (v, va))
  | hlCollectForalls (HL_Boolean v) = ([], HL_Boolean v)
  | hlCollectForalls (HL_Not v) = ([], HL_Not v)
  | hlCollectForalls (HL_And (v, va)) = ([], HL_And (v, va))
  | hlCollectForalls (HL_Or (v, va)) = ([], HL_Or (v, va))
  | hlCollectForalls (HL_Implies (v, va)) = ([], HL_Implies (v, va))
  | hlCollectForalls (HL_Iff (v, va)) = ([], HL_Iff (v, va))
  | hlCollectForalls (HL_Exists (v, va)) = ([], HL_Exists (v, va));

fun hlCollectExists (HL_Exists (x, p)) = let
   val (xs, a) = hlCollectExists p;
 in
   (x :: xs, a)
 end
  | hlCollectExists (HL_Predicate (v, va)) = ([], HL_Predicate (v, va))
  | hlCollectExists (HL_Boolean v) = ([], HL_Boolean v)
  | hlCollectExists (HL_Not v) = ([], HL_Not v)
  | hlCollectExists (HL_And (v, va)) = ([], HL_And (v, va))
  | hlCollectExists (HL_Or (v, va)) = ([], HL_Or (v, va))
  | hlCollectExists (HL_Implies (v, va)) = ([], HL_Implies (v, va))
  | hlCollectExists (HL_Iff (v, va)) = ([], HL_Iff (v, va))
  | hlCollectExists (HL_ForAll (v, va)) = ([], HL_ForAll (v, va));

fun hlPrefixExists xs p = foldr (fn a => fn b => HL_Exists (a, b)) xs p;

fun hlReplaceConstantInTerm a x (HL_Const b) =
  (if ((a : string) = b) then HL_Var x else HL_Const b)
  | hlReplaceConstantInTerm a x (HL_Var y) = HL_Var y;

fun hlAbstractConstantFree a x (HL_Predicate (p, ts)) =
  SOME (HL_Predicate (p, map (hlReplaceConstantInTerm a x) ts))
  | hlAbstractConstantFree a x (HL_Boolean b) = SOME (HL_Boolean b)
  | hlAbstractConstantFree a x (HL_Not p) =
    map_option HL_Not (hlAbstractConstantFree a x p)
  | hlAbstractConstantFree a x (HL_And (p, q)) =
    (case (hlAbstractConstantFree a x p, hlAbstractConstantFree a x q)
      of (NONE, _) => NONE | (SOME _, NONE) => NONE
      | (SOME r, SOME s) => SOME (HL_And (r, s)))
  | hlAbstractConstantFree a x (HL_Or (p, q)) =
    (case (hlAbstractConstantFree a x p, hlAbstractConstantFree a x q)
      of (NONE, _) => NONE | (SOME _, NONE) => NONE
      | (SOME r, SOME s) => SOME (HL_Or (r, s)))
  | hlAbstractConstantFree a x (HL_Implies (p, q)) =
    (case (hlAbstractConstantFree a x p, hlAbstractConstantFree a x q)
      of (NONE, _) => NONE | (SOME _, NONE) => NONE
      | (SOME r, SOME s) => SOME (HL_Implies (r, s)))
  | hlAbstractConstantFree a x (HL_Iff (p, q)) =
    (case (hlAbstractConstantFree a x p, hlAbstractConstantFree a x q)
      of (NONE, _) => NONE | (SOME _, NONE) => NONE
      | (SOME r, SOME s) => SOME (HL_Iff (r, s)))
  | hlAbstractConstantFree a x (HL_ForAll (y, p)) =
    (if ((y : string) = x) then NONE
      else map_option (fn aa => HL_ForAll (y, aa))
             (hlAbstractConstantFree a x p))
  | hlAbstractConstantFree a x (HL_Exists (y, p)) =
    (if ((y : string) = x) then NONE
      else map_option (fn aa => HL_Exists (y, aa))
             (hlAbstractConstantFree a x p));

fun hlAbstractMany [] p = SOME p
  | hlAbstractMany ((x, a) :: ps) p =
    (case hlAbstractConstantFree a x p of NONE => NONE
      | SOME aa => hlAbstractMany ps aa);

fun less_eq_set A_ (Set xs) b = list_all (fn x => member A_ x b) xs
  | less_eq_set A_ a (Coset ys) = list_all (fn y => not (member A_ y a)) ys
  | less_eq_set A_ (Coset []) (Set []) = false;

fun equal_set A_ a b = less_eq_set A_ a b andalso less_eq_set A_ b a;

fun hlFormula (HL_ProofLine (x1, x2, x3, x4)) = x2;

fun hlReferencedConstants p g =
  sup_seta equal_literal
    (image hlConstantsInFormula
      (image hlFormula
        (Set (filtera (fn l => member equal_int (hlLineNumber l) g) p))));

fun hlAssumptionConstants p g =
  sup_seta equal_literal
    (image hlConstantsInFormula
      (image hlFormula
        (Set (filtera
               (fn l =>
                 member equal_int (hlLineNumber l) g andalso
                   equal_hl_justification (hlJustification l) HL_Assumption)
               p))));

fun hlReferences (HL_ProofLine (x1, x2, x3, x4)) = x4;

fun hlLookupLine [] n = NONE
  | hlLookupLine (l :: ls) n =
    (if equal_inta (hlLineNumber l) n then SOME l else hlLookupLine ls n);

fun hlReferencesAt p n = map_option hlReferences (hlLookupLine p n);

fun hlMapFilter f [] = []
  | hlMapFilter f (x :: xs) =
    (case f x of NONE => hlMapFilter f xs | SOME y => y :: hlMapFilter f xs);

fun hlReferenceUnion p ns =
  sup_seta equal_int (Set (hlMapFilter (hlReferencesAt p) ns));

fun hlExcludedMiddle p =
  (case p of HL_Predicate (_, _) => false | HL_Boolean _ => false
    | HL_Not _ => false | HL_And (_, _) => false
    | HL_Or (HL_Predicate (_, _), HL_Predicate (_, _)) => false
    | HL_Or (HL_Predicate (_, _), HL_Boolean _) => false
    | HL_Or (HL_Predicate (literal, lista), HL_Not a) =>
      equal_hl_formulaa (HL_Predicate (literal, lista)) a
    | HL_Or (HL_Predicate (_, _), HL_And (_, _)) => false
    | HL_Or (HL_Predicate (_, _), HL_Or (_, _)) => false
    | HL_Or (HL_Predicate (_, _), HL_Implies (_, _)) => false
    | HL_Or (HL_Predicate (_, _), HL_Iff (_, _)) => false
    | HL_Or (HL_Predicate (_, _), HL_ForAll (_, _)) => false
    | HL_Or (HL_Predicate (_, _), HL_Exists (_, _)) => false
    | HL_Or (HL_Boolean _, HL_Predicate (_, _)) => false
    | HL_Or (HL_Boolean _, HL_Boolean _) => false
    | HL_Or (HL_Boolean boola, HL_Not a) =>
      equal_hl_formulaa (HL_Boolean boola) a
    | HL_Or (HL_Boolean _, HL_And (_, _)) => false
    | HL_Or (HL_Boolean _, HL_Or (_, _)) => false
    | HL_Or (HL_Boolean _, HL_Implies (_, _)) => false
    | HL_Or (HL_Boolean _, HL_Iff (_, _)) => false
    | HL_Or (HL_Boolean _, HL_ForAll (_, _)) => false
    | HL_Or (HL_Boolean _, HL_Exists (_, _)) => false
    | HL_Or (HL_Not hl_formula, HL_Predicate (literal, lista)) =>
      equal_hl_formulaa hl_formula (HL_Predicate (literal, lista))
    | HL_Or (HL_Not hl_formula, HL_Boolean boola) =>
      equal_hl_formulaa hl_formula (HL_Boolean boola)
    | HL_Or (HL_Not hl_formula, HL_Not a) =>
      equal_hl_formulaa (HL_Not hl_formula) a
    | HL_Or (HL_Not hl_formula, HL_And (hl_formula1, hl_formula2)) =>
      equal_hl_formulaa hl_formula (HL_And (hl_formula1, hl_formula2))
    | HL_Or (HL_Not hl_formula, HL_Or (hl_formula1, hl_formula2)) =>
      equal_hl_formulaa hl_formula (HL_Or (hl_formula1, hl_formula2))
    | HL_Or (HL_Not hl_formula, HL_Implies (hl_formula1, hl_formula2)) =>
      equal_hl_formulaa hl_formula (HL_Implies (hl_formula1, hl_formula2))
    | HL_Or (HL_Not hl_formula, HL_Iff (hl_formula1, hl_formula2)) =>
      equal_hl_formulaa hl_formula (HL_Iff (hl_formula1, hl_formula2))
    | HL_Or (HL_Not hl_formula, HL_ForAll (literal, hl_formulaa)) =>
      equal_hl_formulaa hl_formula (HL_ForAll (literal, hl_formulaa))
    | HL_Or (HL_Not hl_formula, HL_Exists (literal, hl_formulaa)) =>
      equal_hl_formulaa hl_formula (HL_Exists (literal, hl_formulaa))
    | HL_Or (HL_And (_, _), HL_Predicate (_, _)) => false
    | HL_Or (HL_And (_, _), HL_Boolean _) => false
    | HL_Or (HL_And (hl_formula1, hl_formula2), HL_Not a) =>
      equal_hl_formulaa (HL_And (hl_formula1, hl_formula2)) a
    | HL_Or (HL_And (_, _), HL_And (_, _)) => false
    | HL_Or (HL_And (_, _), HL_Or (_, _)) => false
    | HL_Or (HL_And (_, _), HL_Implies (_, _)) => false
    | HL_Or (HL_And (_, _), HL_Iff (_, _)) => false
    | HL_Or (HL_And (_, _), HL_ForAll (_, _)) => false
    | HL_Or (HL_And (_, _), HL_Exists (_, _)) => false
    | HL_Or (HL_Or (_, _), HL_Predicate (_, _)) => false
    | HL_Or (HL_Or (_, _), HL_Boolean _) => false
    | HL_Or (HL_Or (hl_formula1, hl_formula2), HL_Not a) =>
      equal_hl_formulaa (HL_Or (hl_formula1, hl_formula2)) a
    | HL_Or (HL_Or (_, _), HL_And (_, _)) => false
    | HL_Or (HL_Or (_, _), HL_Or (_, _)) => false
    | HL_Or (HL_Or (_, _), HL_Implies (_, _)) => false
    | HL_Or (HL_Or (_, _), HL_Iff (_, _)) => false
    | HL_Or (HL_Or (_, _), HL_ForAll (_, _)) => false
    | HL_Or (HL_Or (_, _), HL_Exists (_, _)) => false
    | HL_Or (HL_Implies (_, _), HL_Predicate (_, _)) => false
    | HL_Or (HL_Implies (_, _), HL_Boolean _) => false
    | HL_Or (HL_Implies (hl_formula1, hl_formula2), HL_Not a) =>
      equal_hl_formulaa (HL_Implies (hl_formula1, hl_formula2)) a
    | HL_Or (HL_Implies (_, _), HL_And (_, _)) => false
    | HL_Or (HL_Implies (_, _), HL_Or (_, _)) => false
    | HL_Or (HL_Implies (_, _), HL_Implies (_, _)) => false
    | HL_Or (HL_Implies (_, _), HL_Iff (_, _)) => false
    | HL_Or (HL_Implies (_, _), HL_ForAll (_, _)) => false
    | HL_Or (HL_Implies (_, _), HL_Exists (_, _)) => false
    | HL_Or (HL_Iff (_, _), HL_Predicate (_, _)) => false
    | HL_Or (HL_Iff (_, _), HL_Boolean _) => false
    | HL_Or (HL_Iff (hl_formula1, hl_formula2), HL_Not a) =>
      equal_hl_formulaa (HL_Iff (hl_formula1, hl_formula2)) a
    | HL_Or (HL_Iff (_, _), HL_And (_, _)) => false
    | HL_Or (HL_Iff (_, _), HL_Or (_, _)) => false
    | HL_Or (HL_Iff (_, _), HL_Implies (_, _)) => false
    | HL_Or (HL_Iff (_, _), HL_Iff (_, _)) => false
    | HL_Or (HL_Iff (_, _), HL_ForAll (_, _)) => false
    | HL_Or (HL_Iff (_, _), HL_Exists (_, _)) => false
    | HL_Or (HL_ForAll (_, _), HL_Predicate (_, _)) => false
    | HL_Or (HL_ForAll (_, _), HL_Boolean _) => false
    | HL_Or (HL_ForAll (literal, hl_formula), HL_Not a) =>
      equal_hl_formulaa (HL_ForAll (literal, hl_formula)) a
    | HL_Or (HL_ForAll (_, _), HL_And (_, _)) => false
    | HL_Or (HL_ForAll (_, _), HL_Or (_, _)) => false
    | HL_Or (HL_ForAll (_, _), HL_Implies (_, _)) => false
    | HL_Or (HL_ForAll (_, _), HL_Iff (_, _)) => false
    | HL_Or (HL_ForAll (_, _), HL_ForAll (_, _)) => false
    | HL_Or (HL_ForAll (_, _), HL_Exists (_, _)) => false
    | HL_Or (HL_Exists (_, _), HL_Predicate (_, _)) => false
    | HL_Or (HL_Exists (_, _), HL_Boolean _) => false
    | HL_Or (HL_Exists (literal, hl_formula), HL_Not a) =>
      equal_hl_formulaa (HL_Exists (literal, hl_formula)) a
    | HL_Or (HL_Exists (_, _), HL_And (_, _)) => false
    | HL_Or (HL_Exists (_, _), HL_Or (_, _)) => false
    | HL_Or (HL_Exists (_, _), HL_Implies (_, _)) => false
    | HL_Or (HL_Exists (_, _), HL_Iff (_, _)) => false
    | HL_Or (HL_Exists (_, _), HL_ForAll (_, _)) => false
    | HL_Or (HL_Exists (_, _), HL_Exists (_, _)) => false
    | HL_Implies (_, _) => false | HL_Iff (_, _) => false
    | HL_ForAll (_, _) => false | HL_Exists (_, _) => false);

fun hlContradiction p =
  (case p of HL_Predicate (_, _) => false | HL_Boolean _ => false
    | HL_Not _ => false
    | HL_And (HL_Predicate (_, _), HL_Predicate (_, _)) => false
    | HL_And (HL_Predicate (_, _), HL_Boolean _) => false
    | HL_And (HL_Predicate (literal, lista), HL_Not a) =>
      equal_hl_formulaa (HL_Predicate (literal, lista)) a
    | HL_And (HL_Predicate (_, _), HL_And (_, _)) => false
    | HL_And (HL_Predicate (_, _), HL_Or (_, _)) => false
    | HL_And (HL_Predicate (_, _), HL_Implies (_, _)) => false
    | HL_And (HL_Predicate (_, _), HL_Iff (_, _)) => false
    | HL_And (HL_Predicate (_, _), HL_ForAll (_, _)) => false
    | HL_And (HL_Predicate (_, _), HL_Exists (_, _)) => false
    | HL_And (HL_Boolean _, HL_Predicate (_, _)) => false
    | HL_And (HL_Boolean _, HL_Boolean _) => false
    | HL_And (HL_Boolean boola, HL_Not a) =>
      equal_hl_formulaa (HL_Boolean boola) a
    | HL_And (HL_Boolean _, HL_And (_, _)) => false
    | HL_And (HL_Boolean _, HL_Or (_, _)) => false
    | HL_And (HL_Boolean _, HL_Implies (_, _)) => false
    | HL_And (HL_Boolean _, HL_Iff (_, _)) => false
    | HL_And (HL_Boolean _, HL_ForAll (_, _)) => false
    | HL_And (HL_Boolean _, HL_Exists (_, _)) => false
    | HL_And (HL_Not hl_formula, HL_Predicate (literal, lista)) =>
      equal_hl_formulaa hl_formula (HL_Predicate (literal, lista))
    | HL_And (HL_Not hl_formula, HL_Boolean boola) =>
      equal_hl_formulaa hl_formula (HL_Boolean boola)
    | HL_And (HL_Not hl_formula, HL_Not a) =>
      equal_hl_formulaa (HL_Not hl_formula) a
    | HL_And (HL_Not hl_formula, HL_And (hl_formula1, hl_formula2)) =>
      equal_hl_formulaa hl_formula (HL_And (hl_formula1, hl_formula2))
    | HL_And (HL_Not hl_formula, HL_Or (hl_formula1, hl_formula2)) =>
      equal_hl_formulaa hl_formula (HL_Or (hl_formula1, hl_formula2))
    | HL_And (HL_Not hl_formula, HL_Implies (hl_formula1, hl_formula2)) =>
      equal_hl_formulaa hl_formula (HL_Implies (hl_formula1, hl_formula2))
    | HL_And (HL_Not hl_formula, HL_Iff (hl_formula1, hl_formula2)) =>
      equal_hl_formulaa hl_formula (HL_Iff (hl_formula1, hl_formula2))
    | HL_And (HL_Not hl_formula, HL_ForAll (literal, hl_formulaa)) =>
      equal_hl_formulaa hl_formula (HL_ForAll (literal, hl_formulaa))
    | HL_And (HL_Not hl_formula, HL_Exists (literal, hl_formulaa)) =>
      equal_hl_formulaa hl_formula (HL_Exists (literal, hl_formulaa))
    | HL_And (HL_And (_, _), HL_Predicate (_, _)) => false
    | HL_And (HL_And (_, _), HL_Boolean _) => false
    | HL_And (HL_And (hl_formula1, hl_formula2), HL_Not a) =>
      equal_hl_formulaa (HL_And (hl_formula1, hl_formula2)) a
    | HL_And (HL_And (_, _), HL_And (_, _)) => false
    | HL_And (HL_And (_, _), HL_Or (_, _)) => false
    | HL_And (HL_And (_, _), HL_Implies (_, _)) => false
    | HL_And (HL_And (_, _), HL_Iff (_, _)) => false
    | HL_And (HL_And (_, _), HL_ForAll (_, _)) => false
    | HL_And (HL_And (_, _), HL_Exists (_, _)) => false
    | HL_And (HL_Or (_, _), HL_Predicate (_, _)) => false
    | HL_And (HL_Or (_, _), HL_Boolean _) => false
    | HL_And (HL_Or (hl_formula1, hl_formula2), HL_Not a) =>
      equal_hl_formulaa (HL_Or (hl_formula1, hl_formula2)) a
    | HL_And (HL_Or (_, _), HL_And (_, _)) => false
    | HL_And (HL_Or (_, _), HL_Or (_, _)) => false
    | HL_And (HL_Or (_, _), HL_Implies (_, _)) => false
    | HL_And (HL_Or (_, _), HL_Iff (_, _)) => false
    | HL_And (HL_Or (_, _), HL_ForAll (_, _)) => false
    | HL_And (HL_Or (_, _), HL_Exists (_, _)) => false
    | HL_And (HL_Implies (_, _), HL_Predicate (_, _)) => false
    | HL_And (HL_Implies (_, _), HL_Boolean _) => false
    | HL_And (HL_Implies (hl_formula1, hl_formula2), HL_Not a) =>
      equal_hl_formulaa (HL_Implies (hl_formula1, hl_formula2)) a
    | HL_And (HL_Implies (_, _), HL_And (_, _)) => false
    | HL_And (HL_Implies (_, _), HL_Or (_, _)) => false
    | HL_And (HL_Implies (_, _), HL_Implies (_, _)) => false
    | HL_And (HL_Implies (_, _), HL_Iff (_, _)) => false
    | HL_And (HL_Implies (_, _), HL_ForAll (_, _)) => false
    | HL_And (HL_Implies (_, _), HL_Exists (_, _)) => false
    | HL_And (HL_Iff (_, _), HL_Predicate (_, _)) => false
    | HL_And (HL_Iff (_, _), HL_Boolean _) => false
    | HL_And (HL_Iff (hl_formula1, hl_formula2), HL_Not a) =>
      equal_hl_formulaa (HL_Iff (hl_formula1, hl_formula2)) a
    | HL_And (HL_Iff (_, _), HL_And (_, _)) => false
    | HL_And (HL_Iff (_, _), HL_Or (_, _)) => false
    | HL_And (HL_Iff (_, _), HL_Implies (_, _)) => false
    | HL_And (HL_Iff (_, _), HL_Iff (_, _)) => false
    | HL_And (HL_Iff (_, _), HL_ForAll (_, _)) => false
    | HL_And (HL_Iff (_, _), HL_Exists (_, _)) => false
    | HL_And (HL_ForAll (_, _), HL_Predicate (_, _)) => false
    | HL_And (HL_ForAll (_, _), HL_Boolean _) => false
    | HL_And (HL_ForAll (literal, hl_formula), HL_Not a) =>
      equal_hl_formulaa (HL_ForAll (literal, hl_formula)) a
    | HL_And (HL_ForAll (_, _), HL_And (_, _)) => false
    | HL_And (HL_ForAll (_, _), HL_Or (_, _)) => false
    | HL_And (HL_ForAll (_, _), HL_Implies (_, _)) => false
    | HL_And (HL_ForAll (_, _), HL_Iff (_, _)) => false
    | HL_And (HL_ForAll (_, _), HL_ForAll (_, _)) => false
    | HL_And (HL_ForAll (_, _), HL_Exists (_, _)) => false
    | HL_And (HL_Exists (_, _), HL_Predicate (_, _)) => false
    | HL_And (HL_Exists (_, _), HL_Boolean _) => false
    | HL_And (HL_Exists (literal, hl_formula), HL_Not a) =>
      equal_hl_formulaa (HL_Exists (literal, hl_formula)) a
    | HL_And (HL_Exists (_, _), HL_And (_, _)) => false
    | HL_And (HL_Exists (_, _), HL_Or (_, _)) => false
    | HL_And (HL_Exists (_, _), HL_Implies (_, _)) => false
    | HL_And (HL_Exists (_, _), HL_Iff (_, _)) => false
    | HL_And (HL_Exists (_, _), HL_ForAll (_, _)) => false
    | HL_And (HL_Exists (_, _), HL_Exists (_, _)) => false
    | HL_Or (_, _) => false | HL_Implies (_, _) => false
    | HL_Iff (_, _) => false | HL_ForAll (_, _) => false
    | HL_Exists (_, _) => false);

fun hlFormulaAt p n = map_option hlFormula (hlLookupLine p n);

fun hlRuleOK p l =
  let
    val phi = hlFormula l;
    val g = hlReferences l;
  in
    (case hlJustification l
      of HL_Assumption =>
        equal_set equal_int g (insert equal_int (hlLineNumber l) bot_set)
      | HL_MP (m, n) =>
        (case (hlLookupLine p m, hlLookupLine p n) of (NONE, _) => false
          | (SOME _, NONE) => false
          | (SOME lm, SOME ln) =>
            (case hlFormula lm of HL_Predicate (_, _) => false
              | HL_Boolean _ => false | HL_Not _ => false
              | HL_And (_, _) => false | HL_Or (_, _) => false
              | HL_Implies (pa, q) =>
                equal_hl_formulaa (hlFormula ln) pa andalso
                  (equal_hl_formulaa phi q andalso
                    equal_set equal_int g
                      (sup_set equal_int (hlReferences lm) (hlReferences ln)))
              | HL_Iff (_, _) => false | HL_ForAll (_, _) => false
              | HL_Exists (_, _) => false))
      | HL_MT (m, n) =>
        (case (hlLookupLine p m, (hlLookupLine p n, phi)) of (NONE, _) => false
          | (SOME _, (NONE, _)) => false
          | (SOME _, (SOME _, HL_Predicate (_, _))) => false
          | (SOME _, (SOME _, HL_Boolean _)) => false
          | (SOME lm, (SOME ln, HL_Not pa)) =>
            (case (hlFormula lm, hlFormula ln)
              of (HL_Predicate (_, _), _) => false | (HL_Boolean _, _) => false
              | (HL_Not _, _) => false | (HL_And (_, _), _) => false
              | (HL_Or (_, _), _) => false
              | (HL_Implies (_, _), HL_Predicate (_, _)) => false
              | (HL_Implies (_, _), HL_Boolean _) => false
              | (HL_Implies (q, r), HL_Not s) =>
                equal_hl_formulaa pa q andalso
                  (equal_hl_formulaa r s andalso
                    equal_set equal_int g
                      (sup_set equal_int (hlReferences lm) (hlReferences ln)))
              | (HL_Implies (_, _), HL_And (_, _)) => false
              | (HL_Implies (_, _), HL_Or (_, _)) => false
              | (HL_Implies (_, _), HL_Implies (_, _)) => false
              | (HL_Implies (_, _), HL_Iff (_, _)) => false
              | (HL_Implies (_, _), HL_ForAll (_, _)) => false
              | (HL_Implies (_, _), HL_Exists (_, _)) => false
              | (HL_Iff (_, _), _) => false | (HL_ForAll (_, _), _) => false
              | (HL_Exists (_, _), _) => false)
          | (SOME _, (SOME _, HL_And (_, _))) => false
          | (SOME _, (SOME _, HL_Or (_, _))) => false
          | (SOME _, (SOME _, HL_Implies (_, _))) => false
          | (SOME _, (SOME _, HL_Iff (_, _))) => false
          | (SOME _, (SOME _, HL_ForAll (_, _))) => false
          | (SOME _, (SOME _, HL_Exists (_, _))) => false)
      | HL_DN m =>
        (case hlLookupLine p m of NONE => false
          | SOME lm =>
            (equal_hl_formulaa (hlFormula lm) (HL_Not (HL_Not phi)) orelse
              equal_hl_formulaa phi (HL_Not (HL_Not (hlFormula lm)))) andalso
              equal_set equal_int g (hlReferences lm))
      | HL_CP (a, c) =>
        (case (hlLookupLine p a, hlLookupLine p c) of (NONE, _) => false
          | (SOME _, NONE) => false
          | (SOME la, SOME lc) =>
            equal_hl_justification (hlJustification la) HL_Assumption andalso
              (equal_hl_formulaa phi
                 (HL_Implies (hlFormula la, hlFormula lc)) andalso
                equal_set equal_int g
                  (remove equal_int (hlLineNumber la) (hlReferences lc))))
      | HL_AndIntro (m, n) =>
        (case (hlLookupLine p m, hlLookupLine p n) of (NONE, _) => false
          | (SOME _, NONE) => false
          | (SOME lm, SOME ln) =>
            (equal_hl_formulaa phi (HL_And (hlFormula lm, hlFormula ln)) orelse
              equal_hl_formulaa phi
                (HL_And (hlFormula ln, hlFormula lm))) andalso
              equal_set equal_int g
                (sup_set equal_int (hlReferences lm) (hlReferences ln)))
      | HL_AndElim m =>
        (case hlLookupLine p m of NONE => false
          | SOME lm =>
            (case hlFormula lm of HL_Predicate (_, _) => false
              | HL_Boolean _ => false | HL_Not _ => false
              | HL_And (pa, q) =>
                (equal_hl_formulaa phi pa orelse
                  equal_hl_formulaa phi q) andalso
                  equal_set equal_int g (hlReferences lm)
              | HL_Or (_, _) => false | HL_Implies (_, _) => false
              | HL_Iff (_, _) => false | HL_ForAll (_, _) => false
              | HL_Exists (_, _) => false))
      | HL_OrIntro m =>
        (case (hlLookupLine p m, phi) of (NONE, _) => false
          | (SOME _, HL_Predicate (_, _)) => false
          | (SOME _, HL_Boolean _) => false | (SOME _, HL_Not _) => false
          | (SOME _, HL_And (_, _)) => false
          | (SOME lm, HL_Or (pa, q)) =>
            (equal_hl_formulaa (hlFormula lm) pa orelse
              equal_hl_formulaa (hlFormula lm) q) andalso
              equal_set equal_int g (hlReferences lm)
          | (SOME _, HL_Implies (_, _)) => false
          | (SOME _, HL_Iff (_, _)) => false
          | (SOME _, HL_ForAll (_, _)) => false
          | (SOME _, HL_Exists (_, _)) => false)
      | HL_OrElim (d, a1, c1, a2, c2) =>
        (case (hlLookupLine p d,
                (hlLookupLine p a1,
                  (hlLookupLine p c1, (hlLookupLine p a2, hlLookupLine p c2))))
          of (NONE, _) => false | (SOME _, (NONE, _)) => false
          | (SOME _, (SOME _, (NONE, _))) => false
          | (SOME _, (SOME _, (SOME _, (NONE, _)))) => false
          | (SOME _, (SOME _, (SOME _, (SOME _, NONE)))) => false
          | (SOME ld, (SOME la1, (SOME lc1, (SOME la2, SOME lc2)))) =>
            equal_hl_justification (hlJustification la1) HL_Assumption andalso
              (equal_hl_justification (hlJustification la2)
                 HL_Assumption andalso
                (equal_hl_formulaa (hlFormula lc1) phi andalso
                  (equal_hl_formulaa (hlFormula lc2) phi andalso
                    ((case hlFormula ld of HL_Predicate (_, _) => false
                       | HL_Boolean _ => false | HL_Not _ => false
                       | HL_And (_, _) => false
                       | HL_Or (pa, q) =>
                         equal_hl_formulaa (hlFormula la1) pa andalso
                           equal_hl_formulaa (hlFormula la2) q orelse
                           equal_hl_formulaa (hlFormula la1) q andalso
                             equal_hl_formulaa (hlFormula la2) pa
                       | HL_Implies (_, _) => false | HL_Iff (_, _) => false
                       | HL_ForAll (_, _) => false
                       | HL_Exists (_, _) => false) andalso
                      equal_set equal_int g
                        (sup_set equal_int
                          (sup_set equal_int (hlReferences ld)
                            (remove equal_int (hlLineNumber la1)
                              (hlReferences lc1)))
                          (remove equal_int (hlLineNumber la2)
                            (hlReferences lc2))))))))
      | HL_RAA (a, c) =>
        (case (hlLookupLine p a, hlLookupLine p c) of (NONE, _) => false
          | (SOME _, NONE) => false
          | (SOME la, SOME lc) =>
            equal_hl_justification (hlJustification la) HL_Assumption andalso
              (equal_hl_formulaa phi (HL_Not (hlFormula la)) andalso
                (hlContradiction (hlFormula lc) andalso
                  equal_set equal_int g
                    (remove equal_int (hlLineNumber la) (hlReferences lc)))))
      | HL_ForallElim m =>
        (case hlLookupLine p m of NONE => false
          | SOME lm =>
            let
              val (sourceVars, sourceCore) = hlCollectForalls (hlFormula lm);
              val (targetVars, targetCore) = hlCollectForalls phi;
            in
              (case hlEliminationCount sourceVars targetVars of NONE => false
                | SOME k =>
                  not (is_none
                        (hlInferWitnessConstsK sourceVars sourceCore k
                          targetCore)) andalso
                    equal_set equal_int g (hlReferences lm))
            end)
      | HL_ExistsIntro m =>
        (case hlLookupLine p m of NONE => false
          | SOME lm =>
            let
              val (xs, core) = hlCollectExists phi;
            in
              not (null xs) andalso
                (list_ex
                   (fn k =>
                     not (is_none
                           (hlInferWitnessConstsK xs
                             (hlPrefixExists (drop k xs) core) k
                             (hlFormula lm))))
                   (upt zero_nat (suc (size_lista xs))) andalso
                  equal_set equal_int g (hlReferences lm))
            end)
      | HL_ForallIntro m =>
        (case hlLookupLine p m of NONE => false
          | SOME lm =>
            let
              val (xs, core) = hlCollectForalls phi;
            in
              not (null xs) andalso
                (case hlInferWitnessConstsK xs core (size_lista xs)
                        (hlFormula lm)
                  of NONE => false
                  | SOME cs =>
                    let
                      val pairs =
                        filtera (fn xc => not (((snd xc) : string) = ""))
                          (zip xs cs);
                    in
                      equal_option equal_hl_formula
                        (hlAbstractMany pairs (hlFormula lm))
                        (SOME core) andalso
                        (ball (image snd (Set pairs))
                           (fn c =>
                             not (member equal_literal c
                                   (hlAssumptionConstants p
                                     (hlReferences lm)))) andalso
                          equal_set equal_int g (hlReferences lm))
                    end)
            end)
      | HL_ExistsElim (m, a, c) =>
        (case (hlLookupLine p m, (hlLookupLine p a, hlLookupLine p c))
          of (NONE, _) => false | (SOME _, (NONE, _)) => false
          | (SOME _, (SOME _, NONE)) => false
          | (SOME lm, (SOME la, SOME lc)) =>
            let
              val (sourceVars, sourceCore) = hlCollectExists (hlFormula lm);
              val (targetVars, _) = hlCollectExists (hlFormula la);
              val delta = remove equal_int (hlLineNumber la) (hlReferences lc);
            in
              not (null sourceVars) andalso
                (equal_hl_justification (hlJustification la)
                   HL_Assumption andalso
                  (case hlEliminationCount sourceVars targetVars
                    of NONE => false
                    | SOME k =>
                      let
                        val template = hlPrefixExists targetVars sourceCore;
                      in
                        (case hlInferWitnessConstsK sourceVars template k
                                (hlFormula la)
                          of NONE => false
                          | SOME cs =>
                            let
                              val pairs =
                                filtera
                                  (fn xc => not (((snd xc) : string) = ""))
                                  (zip (take k sourceVars) cs);
                            in
                              equal_option equal_hl_formula
                                (hlAbstractMany pairs (hlFormula la))
                                (SOME template) andalso
                                (ball (image snd (Set pairs))
                                   (fn w =>
                                     not (member equal_literal w
   (hlConstantsInFormula (hlFormula lc))) andalso
                                       not
 (member equal_literal w (hlReferencedConstants p delta))) andalso
                                  (equal_hl_formulaa phi (hlFormula lc) andalso
                                    equal_set equal_int g
                                      (sup_set equal_int (hlReferences lm)
delta)))
                            end)
                      end))
            end)
      | HL_EqIntro =>
        (case phi of HL_Predicate (_, []) => false
          | HL_Predicate (_, HL_Var _ :: _) => false
          | HL_Predicate (_, [HL_Const _]) => false
          | HL_Predicate (_, HL_Const _ :: HL_Var _ :: _) => false
          | HL_Predicate (e, [HL_Const a, HL_Const b]) =>
            ((e : string) = "=") andalso
              (((a : string) = b) andalso equal_set equal_int g bot_set)
          | HL_Predicate (_, HL_Const _ :: HL_Const _ :: _ :: _) => false
          | HL_Boolean _ => false | HL_Not _ => false | HL_And (_, _) => false
          | HL_Or (_, _) => false | HL_Implies (_, _) => false
          | HL_Iff (_, _) => false | HL_ForAll (_, _) => false
          | HL_Exists (_, _) => false)
      | HL_EqElim (m, n) =>
        (case (hlLookupLine p m, hlLookupLine p n) of (NONE, _) => false
          | (SOME _, NONE) => false
          | (SOME lm, SOME ln) =>
            (case hlEqualityFormula (hlFormula ln) of NONE => false
              | SOME (HL_Var _, _) => false
              | SOME (HL_Const _, HL_Var _) => false
              | SOME (HL_Const a, HL_Const b) =>
                hlEqualUpToConstantReplacement a b (hlFormula lm) phi andalso
                  equal_set equal_int g
                    (sup_set equal_int (hlReferences lm) (hlReferences ln))))
      | HL_LEM => hlExcludedMiddle phi
      | HL_PropTaut ms =>
        list_all (fn m => not (is_none (hlLookupLine p m))) ms andalso
          (hlPropositionalConsequence (hlMapFilter (hlFormulaAt p) ms)
             phi andalso
            equal_set equal_int g (hlReferenceUnion p ms))
      | HL_IffIntro (m, n) =>
        (case (hlLookupLine p m, (hlLookupLine p n, phi)) of (NONE, _) => false
          | (SOME _, (NONE, _)) => false
          | (SOME _, (SOME _, HL_Predicate (_, _))) => false
          | (SOME _, (SOME _, HL_Boolean _)) => false
          | (SOME _, (SOME _, HL_Not _)) => false
          | (SOME _, (SOME _, HL_And (_, _))) => false
          | (SOME _, (SOME _, HL_Or (_, _))) => false
          | (SOME _, (SOME _, HL_Implies (_, _))) => false
          | (SOME lm, (SOME ln, HL_Iff (u, v))) =>
            (case (hlFormula lm, hlFormula ln)
              of (HL_Predicate (_, _), _) => false | (HL_Boolean _, _) => false
              | (HL_Not _, _) => false | (HL_And (_, _), _) => false
              | (HL_Or (_, _), _) => false
              | (HL_Implies (_, _), HL_Predicate (_, _)) => false
              | (HL_Implies (_, _), HL_Boolean _) => false
              | (HL_Implies (_, _), HL_Not _) => false
              | (HL_Implies (_, _), HL_And (_, _)) => false
              | (HL_Implies (_, _), HL_Or (_, _)) => false
              | (HL_Implies (pa, q), HL_Implies (r, s)) =>
                equal_hl_formulaa pa s andalso
                  (equal_hl_formulaa q r andalso
                    ((equal_hl_formulaa u pa andalso
                        equal_hl_formulaa v q orelse
                       equal_hl_formulaa u q andalso
                         equal_hl_formulaa v pa) andalso
                      equal_set equal_int g
                        (sup_set equal_int (hlReferences lm)
                          (hlReferences ln))))
              | (HL_Implies (_, _), HL_Iff (_, _)) => false
              | (HL_Implies (_, _), HL_ForAll (_, _)) => false
              | (HL_Implies (_, _), HL_Exists (_, _)) => false
              | (HL_Iff (_, _), _) => false | (HL_ForAll (_, _), _) => false
              | (HL_Exists (_, _), _) => false)
          | (SOME _, (SOME _, HL_ForAll (_, _))) => false
          | (SOME _, (SOME _, HL_Exists (_, _))) => false)
      | HL_IffElim (m, n) =>
        (case (hlLookupLine p m, hlLookupLine p n) of (NONE, _) => false
          | (SOME _, NONE) => false
          | (SOME lm, SOME ln) =>
            (case hlFormula lm of HL_Predicate (_, _) => false
              | HL_Boolean _ => false | HL_Not _ => false
              | HL_And (_, _) => false | HL_Or (_, _) => false
              | HL_Implies (_, _) => false
              | HL_Iff (pa, q) =>
                (equal_hl_formulaa (hlFormula ln) pa andalso
                   equal_hl_formulaa phi q orelse
                  equal_hl_formulaa (hlFormula ln) q andalso
                    equal_hl_formulaa phi pa) andalso
                  equal_set equal_int g
                    (sup_set equal_int (hlReferences lm) (hlReferences ln))
              | HL_ForAll (_, _) => false | HL_Exists (_, _) => false))
      | HL_QN m =>
        (case hlLookupLine p m of NONE => false
          | SOME lm =>
            hlQuantifierNegationEquivalent (hlFormula lm) phi andalso
              equal_set equal_int g (hlReferences lm)))
  end;

fun hlLineOK p l = hlStructureOK p l andalso hlRuleOK p l;

fun eqsub_t a b (Nm c) (Nm d) =
  ((c : string) = d) orelse ((c : string) = a) andalso ((d : string) = b)
  | eqsub_t a b (Vr x) (Vr y) = ((x : string) = y)
  | eqsub_t a b (Vr v) (Nm va) = false
  | eqsub_t a b (Nm va) (Vr v) = false;

fun eqsub a b (Atom (p, ts)) (Atom (q, us)) =
  ((p : string) = q) andalso list_all2 (eqsub_t a b) ts us
  | eqsub a b (Eqf (ta, ua)) (Eqf (t, u)) =
    eqsub_t a b ta t andalso eqsub_t a b ua u
  | eqsub a b Bot Bot = true
  | eqsub a b (Neg pa) (Neg p) = eqsub a b pa p
  | eqsub a b (Conj (pa, qa)) (Conj (p, q)) =
    eqsub a b pa p andalso eqsub a b qa q
  | eqsub a b (Disj (pa, qa)) (Disj (p, q)) =
    eqsub a b pa p andalso eqsub a b qa q
  | eqsub a b (Impl (pa, qa)) (Impl (p, q)) =
    eqsub a b pa p andalso eqsub a b qa q
  | eqsub a b (Iff (pa, qa)) (Iff (p, q)) =
    eqsub a b pa p andalso eqsub a b qa q
  | eqsub a b (Uni (x, pa)) (Uni (y, p)) =
    ((x : string) = y) andalso eqsub a b pa p
  | eqsub a b (Exi (x, pa)) (Exi (y, p)) =
    ((x : string) = y) andalso eqsub a b pa p
  | eqsub a b (Eqf (v, va)) (Atom (vb, vc)) = false
  | eqsub a b (Eqf (v, va)) Bot = false
  | eqsub a b (Eqf (v, va)) (Neg vb) = false
  | eqsub a b (Eqf (v, va)) (Conj (vb, vc)) = false
  | eqsub a b (Eqf (v, va)) (Disj (vb, vc)) = false
  | eqsub a b (Eqf (v, va)) (Impl (vb, vc)) = false
  | eqsub a b (Eqf (v, va)) (Iff (vb, vc)) = false
  | eqsub a b (Eqf (v, va)) (Uni (vb, vc)) = false
  | eqsub a b (Eqf (v, va)) (Exi (vb, vc)) = false
  | eqsub a b Bot (Atom (v, va)) = false
  | eqsub a b Bot (Eqf (v, va)) = false
  | eqsub a b Bot (Neg v) = false
  | eqsub a b Bot (Conj (v, va)) = false
  | eqsub a b Bot (Disj (v, va)) = false
  | eqsub a b Bot (Impl (v, va)) = false
  | eqsub a b Bot (Iff (v, va)) = false
  | eqsub a b Bot (Uni (v, va)) = false
  | eqsub a b Bot (Exi (v, va)) = false
  | eqsub a b (Neg v) (Atom (va, vb)) = false
  | eqsub a b (Neg v) (Eqf (va, vb)) = false
  | eqsub a b (Neg v) Bot = false
  | eqsub a b (Neg v) (Conj (va, vb)) = false
  | eqsub a b (Neg v) (Disj (va, vb)) = false
  | eqsub a b (Neg v) (Impl (va, vb)) = false
  | eqsub a b (Neg v) (Iff (va, vb)) = false
  | eqsub a b (Neg v) (Uni (va, vb)) = false
  | eqsub a b (Neg v) (Exi (va, vb)) = false
  | eqsub a b (Conj (v, va)) (Atom (vb, vc)) = false
  | eqsub a b (Conj (v, va)) (Eqf (vb, vc)) = false
  | eqsub a b (Conj (v, va)) Bot = false
  | eqsub a b (Conj (v, va)) (Neg vb) = false
  | eqsub a b (Conj (v, va)) (Disj (vb, vc)) = false
  | eqsub a b (Conj (v, va)) (Impl (vb, vc)) = false
  | eqsub a b (Conj (v, va)) (Iff (vb, vc)) = false
  | eqsub a b (Conj (v, va)) (Uni (vb, vc)) = false
  | eqsub a b (Conj (v, va)) (Exi (vb, vc)) = false
  | eqsub a b (Disj (v, va)) (Atom (vb, vc)) = false
  | eqsub a b (Disj (v, va)) (Eqf (vb, vc)) = false
  | eqsub a b (Disj (v, va)) Bot = false
  | eqsub a b (Disj (v, va)) (Neg vb) = false
  | eqsub a b (Disj (v, va)) (Conj (vb, vc)) = false
  | eqsub a b (Disj (v, va)) (Impl (vb, vc)) = false
  | eqsub a b (Disj (v, va)) (Iff (vb, vc)) = false
  | eqsub a b (Disj (v, va)) (Uni (vb, vc)) = false
  | eqsub a b (Disj (v, va)) (Exi (vb, vc)) = false
  | eqsub a b (Impl (v, va)) (Atom (vb, vc)) = false
  | eqsub a b (Impl (v, va)) (Eqf (vb, vc)) = false
  | eqsub a b (Impl (v, va)) Bot = false
  | eqsub a b (Impl (v, va)) (Neg vb) = false
  | eqsub a b (Impl (v, va)) (Conj (vb, vc)) = false
  | eqsub a b (Impl (v, va)) (Disj (vb, vc)) = false
  | eqsub a b (Impl (v, va)) (Iff (vb, vc)) = false
  | eqsub a b (Impl (v, va)) (Uni (vb, vc)) = false
  | eqsub a b (Impl (v, va)) (Exi (vb, vc)) = false
  | eqsub a b (Iff (v, va)) (Atom (vb, vc)) = false
  | eqsub a b (Iff (v, va)) (Eqf (vb, vc)) = false
  | eqsub a b (Iff (v, va)) Bot = false
  | eqsub a b (Iff (v, va)) (Neg vb) = false
  | eqsub a b (Iff (v, va)) (Conj (vb, vc)) = false
  | eqsub a b (Iff (v, va)) (Disj (vb, vc)) = false
  | eqsub a b (Iff (v, va)) (Impl (vb, vc)) = false
  | eqsub a b (Iff (v, va)) (Uni (vb, vc)) = false
  | eqsub a b (Iff (v, va)) (Exi (vb, vc)) = false
  | eqsub a b (Uni (v, va)) (Atom (vb, vc)) = false
  | eqsub a b (Uni (v, va)) (Eqf (vb, vc)) = false
  | eqsub a b (Uni (v, va)) Bot = false
  | eqsub a b (Uni (v, va)) (Neg vb) = false
  | eqsub a b (Uni (v, va)) (Conj (vb, vc)) = false
  | eqsub a b (Uni (v, va)) (Disj (vb, vc)) = false
  | eqsub a b (Uni (v, va)) (Impl (vb, vc)) = false
  | eqsub a b (Uni (v, va)) (Iff (vb, vc)) = false
  | eqsub a b (Uni (v, va)) (Exi (vb, vc)) = false
  | eqsub a b (Exi (v, va)) (Atom (vb, vc)) = false
  | eqsub a b (Exi (v, va)) (Eqf (vb, vc)) = false
  | eqsub a b (Exi (v, va)) Bot = false
  | eqsub a b (Exi (v, va)) (Neg vb) = false
  | eqsub a b (Exi (v, va)) (Conj (vb, vc)) = false
  | eqsub a b (Exi (v, va)) (Disj (vb, vc)) = false
  | eqsub a b (Exi (v, va)) (Impl (vb, vc)) = false
  | eqsub a b (Exi (v, va)) (Iff (vb, vc)) = false
  | eqsub a b (Exi (v, va)) (Uni (vb, vc)) = false
  | eqsub a b (Atom (vb, vc)) (Eqf (v, va)) = false
  | eqsub a b (Atom (v, va)) Bot = false
  | eqsub a b (Atom (va, vb)) (Neg v) = false
  | eqsub a b (Atom (vb, vc)) (Conj (v, va)) = false
  | eqsub a b (Atom (vb, vc)) (Disj (v, va)) = false
  | eqsub a b (Atom (vb, vc)) (Impl (v, va)) = false
  | eqsub a b (Atom (vb, vc)) (Iff (v, va)) = false
  | eqsub a b (Atom (vb, vc)) (Uni (v, va)) = false
  | eqsub a b (Atom (vb, vc)) (Exi (v, va)) = false;

fun genOK x p psi asa =
  (if membera equal_literal (fvs p) x
    then list_ex
           (fn a =>
             not (membera equal_literal (names p) a) andalso arbitrary_in a asa)
           (instWitnesses x p psi)
    else equal_fma psi p);

fun witOK x p psi phi asa =
  (if membera equal_literal (fvs p) x
    then list_ex
           (fn b =>
             not (membera equal_literal (names p) b) andalso
               (not (membera equal_literal (names phi) b) andalso
                 arbitrary_in b asa))
           (instWitnesses x p psi)
    else equal_fma psi p);

fun equal_char (Chara (x1, x2, x3, x4, x5, x6, x7, x8))
  (Chara (y1, y2, y3, y4, y5, y6, y7, y8)) =
  equal_bool x1 y1 andalso
    (equal_bool x2 y2 andalso
      (equal_bool x3 y3 andalso
        (equal_bool x4 y4 andalso
          (equal_bool x5 y5 andalso
            (equal_bool x6 y6 andalso
              (equal_bool x7 y7 andalso equal_bool x8 y8))))));

fun dispLen [] = zero_nat
  | dispLen (c :: cs) =
    (if equal_char c
          (Chara (false, false, true, true, true, false, true, false))
      then suc (dispLen
                 (tl (dropWhile
                       (fn x =>
                         not (equal_char x
                               (Chara
                                 (false, true, true, true, true, true, false,
                                   false))))
                       cs)))
      else suc (dispLen cs));

fun dispWidth s = dispLen (explode s);

fun padTo n s =
  s ^ implode
        (replicate (minus_nat n (dispWidth s))
          (Chara (false, false, false, false, false, true, false, false)));

fun sepBy s ss =
  (case ss of [] => "" | t :: ts => t ^ cat (map (fn a => s ^ a) ts));

fun isaSym s =
  implode
    [Chara (false, false, true, true, true, false, true, false),
      Chara (false, false, true, true, true, true, false, false)] ^
    s ^
    ">";

val symEx : string = isaSym "exists";

val symOr : string = isaSym "or";

fun sorted_wrt p [] = true
  | sorted_wrt p (x :: ys) = list_all (p x) ys andalso sorted_wrt p ys;

fun equal_fitch_rule (FEqElim (x221, x222)) (FReit x23) = false
  | equal_fitch_rule (FReit x23) (FEqElim (x221, x222)) = false
  | equal_fitch_rule FEqIntro (FReit x23) = false
  | equal_fitch_rule (FReit x23) FEqIntro = false
  | equal_fitch_rule FEqIntro (FEqElim (x221, x222)) = false
  | equal_fitch_rule (FEqElim (x221, x222)) FEqIntro = false
  | equal_fitch_rule (FExistsElim (x201, x202)) (FReit x23) = false
  | equal_fitch_rule (FReit x23) (FExistsElim (x201, x202)) = false
  | equal_fitch_rule (FExistsElim (x201, x202)) (FEqElim (x221, x222)) = false
  | equal_fitch_rule (FEqElim (x221, x222)) (FExistsElim (x201, x202)) = false
  | equal_fitch_rule (FExistsElim (x201, x202)) FEqIntro = false
  | equal_fitch_rule FEqIntro (FExistsElim (x201, x202)) = false
  | equal_fitch_rule (FExistsIntro x19) (FReit x23) = false
  | equal_fitch_rule (FReit x23) (FExistsIntro x19) = false
  | equal_fitch_rule (FExistsIntro x19) (FEqElim (x221, x222)) = false
  | equal_fitch_rule (FEqElim (x221, x222)) (FExistsIntro x19) = false
  | equal_fitch_rule (FExistsIntro x19) FEqIntro = false
  | equal_fitch_rule FEqIntro (FExistsIntro x19) = false
  | equal_fitch_rule (FExistsIntro x19) (FExistsElim (x201, x202)) = false
  | equal_fitch_rule (FExistsElim (x201, x202)) (FExistsIntro x19) = false
  | equal_fitch_rule (FForallIntro x18) (FReit x23) = false
  | equal_fitch_rule (FReit x23) (FForallIntro x18) = false
  | equal_fitch_rule (FForallIntro x18) (FEqElim (x221, x222)) = false
  | equal_fitch_rule (FEqElim (x221, x222)) (FForallIntro x18) = false
  | equal_fitch_rule (FForallIntro x18) FEqIntro = false
  | equal_fitch_rule FEqIntro (FForallIntro x18) = false
  | equal_fitch_rule (FForallIntro x18) (FExistsElim (x201, x202)) = false
  | equal_fitch_rule (FExistsElim (x201, x202)) (FForallIntro x18) = false
  | equal_fitch_rule (FForallIntro x18) (FExistsIntro x19) = false
  | equal_fitch_rule (FExistsIntro x19) (FForallIntro x18) = false
  | equal_fitch_rule (FForallElim x17) (FReit x23) = false
  | equal_fitch_rule (FReit x23) (FForallElim x17) = false
  | equal_fitch_rule (FForallElim x17) (FEqElim (x221, x222)) = false
  | equal_fitch_rule (FEqElim (x221, x222)) (FForallElim x17) = false
  | equal_fitch_rule (FForallElim x17) FEqIntro = false
  | equal_fitch_rule FEqIntro (FForallElim x17) = false
  | equal_fitch_rule (FForallElim x17) (FExistsElim (x201, x202)) = false
  | equal_fitch_rule (FExistsElim (x201, x202)) (FForallElim x17) = false
  | equal_fitch_rule (FForallElim x17) (FExistsIntro x19) = false
  | equal_fitch_rule (FExistsIntro x19) (FForallElim x17) = false
  | equal_fitch_rule (FForallElim x17) (FForallIntro x18) = false
  | equal_fitch_rule (FForallIntro x18) (FForallElim x17) = false
  | equal_fitch_rule (FIffElimR x16) (FReit x23) = false
  | equal_fitch_rule (FReit x23) (FIffElimR x16) = false
  | equal_fitch_rule (FIffElimR x16) (FEqElim (x221, x222)) = false
  | equal_fitch_rule (FEqElim (x221, x222)) (FIffElimR x16) = false
  | equal_fitch_rule (FIffElimR x16) FEqIntro = false
  | equal_fitch_rule FEqIntro (FIffElimR x16) = false
  | equal_fitch_rule (FIffElimR x16) (FExistsElim (x201, x202)) = false
  | equal_fitch_rule (FExistsElim (x201, x202)) (FIffElimR x16) = false
  | equal_fitch_rule (FIffElimR x16) (FExistsIntro x19) = false
  | equal_fitch_rule (FExistsIntro x19) (FIffElimR x16) = false
  | equal_fitch_rule (FIffElimR x16) (FForallIntro x18) = false
  | equal_fitch_rule (FForallIntro x18) (FIffElimR x16) = false
  | equal_fitch_rule (FIffElimR x16) (FForallElim x17) = false
  | equal_fitch_rule (FForallElim x17) (FIffElimR x16) = false
  | equal_fitch_rule (FIffElimL x15) (FReit x23) = false
  | equal_fitch_rule (FReit x23) (FIffElimL x15) = false
  | equal_fitch_rule (FIffElimL x15) (FEqElim (x221, x222)) = false
  | equal_fitch_rule (FEqElim (x221, x222)) (FIffElimL x15) = false
  | equal_fitch_rule (FIffElimL x15) FEqIntro = false
  | equal_fitch_rule FEqIntro (FIffElimL x15) = false
  | equal_fitch_rule (FIffElimL x15) (FExistsElim (x201, x202)) = false
  | equal_fitch_rule (FExistsElim (x201, x202)) (FIffElimL x15) = false
  | equal_fitch_rule (FIffElimL x15) (FExistsIntro x19) = false
  | equal_fitch_rule (FExistsIntro x19) (FIffElimL x15) = false
  | equal_fitch_rule (FIffElimL x15) (FForallIntro x18) = false
  | equal_fitch_rule (FForallIntro x18) (FIffElimL x15) = false
  | equal_fitch_rule (FIffElimL x15) (FForallElim x17) = false
  | equal_fitch_rule (FForallElim x17) (FIffElimL x15) = false
  | equal_fitch_rule (FIffElimL x15) (FIffElimR x16) = false
  | equal_fitch_rule (FIffElimR x16) (FIffElimL x15) = false
  | equal_fitch_rule (FIffIntro (x141, x142)) (FReit x23) = false
  | equal_fitch_rule (FReit x23) (FIffIntro (x141, x142)) = false
  | equal_fitch_rule (FIffIntro (x141, x142)) (FEqElim (x221, x222)) = false
  | equal_fitch_rule (FEqElim (x221, x222)) (FIffIntro (x141, x142)) = false
  | equal_fitch_rule (FIffIntro (x141, x142)) FEqIntro = false
  | equal_fitch_rule FEqIntro (FIffIntro (x141, x142)) = false
  | equal_fitch_rule (FIffIntro (x141, x142)) (FExistsElim (x201, x202)) = false
  | equal_fitch_rule (FExistsElim (x201, x202)) (FIffIntro (x141, x142)) = false
  | equal_fitch_rule (FIffIntro (x141, x142)) (FExistsIntro x19) = false
  | equal_fitch_rule (FExistsIntro x19) (FIffIntro (x141, x142)) = false
  | equal_fitch_rule (FIffIntro (x141, x142)) (FForallIntro x18) = false
  | equal_fitch_rule (FForallIntro x18) (FIffIntro (x141, x142)) = false
  | equal_fitch_rule (FIffIntro (x141, x142)) (FForallElim x17) = false
  | equal_fitch_rule (FForallElim x17) (FIffIntro (x141, x142)) = false
  | equal_fitch_rule (FIffIntro (x141, x142)) (FIffElimR x16) = false
  | equal_fitch_rule (FIffElimR x16) (FIffIntro (x141, x142)) = false
  | equal_fitch_rule (FIffIntro (x141, x142)) (FIffElimL x15) = false
  | equal_fitch_rule (FIffElimL x15) (FIffIntro (x141, x142)) = false
  | equal_fitch_rule (FOrElim (x131, x132, x133)) (FReit x23) = false
  | equal_fitch_rule (FReit x23) (FOrElim (x131, x132, x133)) = false
  | equal_fitch_rule (FOrElim (x131, x132, x133)) (FEqElim (x221, x222)) = false
  | equal_fitch_rule (FEqElim (x221, x222)) (FOrElim (x131, x132, x133)) = false
  | equal_fitch_rule (FOrElim (x131, x132, x133)) FEqIntro = false
  | equal_fitch_rule FEqIntro (FOrElim (x131, x132, x133)) = false
  | equal_fitch_rule (FOrElim (x131, x132, x133)) (FExistsElim (x201, x202)) =
    false
  | equal_fitch_rule (FExistsElim (x201, x202)) (FOrElim (x131, x132, x133)) =
    false
  | equal_fitch_rule (FOrElim (x131, x132, x133)) (FExistsIntro x19) = false
  | equal_fitch_rule (FExistsIntro x19) (FOrElim (x131, x132, x133)) = false
  | equal_fitch_rule (FOrElim (x131, x132, x133)) (FForallIntro x18) = false
  | equal_fitch_rule (FForallIntro x18) (FOrElim (x131, x132, x133)) = false
  | equal_fitch_rule (FOrElim (x131, x132, x133)) (FForallElim x17) = false
  | equal_fitch_rule (FForallElim x17) (FOrElim (x131, x132, x133)) = false
  | equal_fitch_rule (FOrElim (x131, x132, x133)) (FIffElimR x16) = false
  | equal_fitch_rule (FIffElimR x16) (FOrElim (x131, x132, x133)) = false
  | equal_fitch_rule (FOrElim (x131, x132, x133)) (FIffElimL x15) = false
  | equal_fitch_rule (FIffElimL x15) (FOrElim (x131, x132, x133)) = false
  | equal_fitch_rule (FOrElim (x131, x132, x133)) (FIffIntro (x141, x142)) =
    false
  | equal_fitch_rule (FIffIntro (x141, x142)) (FOrElim (x131, x132, x133)) =
    false
  | equal_fitch_rule (FOrIntroR x12) (FReit x23) = false
  | equal_fitch_rule (FReit x23) (FOrIntroR x12) = false
  | equal_fitch_rule (FOrIntroR x12) (FEqElim (x221, x222)) = false
  | equal_fitch_rule (FEqElim (x221, x222)) (FOrIntroR x12) = false
  | equal_fitch_rule (FOrIntroR x12) FEqIntro = false
  | equal_fitch_rule FEqIntro (FOrIntroR x12) = false
  | equal_fitch_rule (FOrIntroR x12) (FExistsElim (x201, x202)) = false
  | equal_fitch_rule (FExistsElim (x201, x202)) (FOrIntroR x12) = false
  | equal_fitch_rule (FOrIntroR x12) (FExistsIntro x19) = false
  | equal_fitch_rule (FExistsIntro x19) (FOrIntroR x12) = false
  | equal_fitch_rule (FOrIntroR x12) (FForallIntro x18) = false
  | equal_fitch_rule (FForallIntro x18) (FOrIntroR x12) = false
  | equal_fitch_rule (FOrIntroR x12) (FForallElim x17) = false
  | equal_fitch_rule (FForallElim x17) (FOrIntroR x12) = false
  | equal_fitch_rule (FOrIntroR x12) (FIffElimR x16) = false
  | equal_fitch_rule (FIffElimR x16) (FOrIntroR x12) = false
  | equal_fitch_rule (FOrIntroR x12) (FIffElimL x15) = false
  | equal_fitch_rule (FIffElimL x15) (FOrIntroR x12) = false
  | equal_fitch_rule (FOrIntroR x12) (FIffIntro (x141, x142)) = false
  | equal_fitch_rule (FIffIntro (x141, x142)) (FOrIntroR x12) = false
  | equal_fitch_rule (FOrIntroR x12) (FOrElim (x131, x132, x133)) = false
  | equal_fitch_rule (FOrElim (x131, x132, x133)) (FOrIntroR x12) = false
  | equal_fitch_rule (FOrIntroL x11) (FReit x23) = false
  | equal_fitch_rule (FReit x23) (FOrIntroL x11) = false
  | equal_fitch_rule (FOrIntroL x11) (FEqElim (x221, x222)) = false
  | equal_fitch_rule (FEqElim (x221, x222)) (FOrIntroL x11) = false
  | equal_fitch_rule (FOrIntroL x11) FEqIntro = false
  | equal_fitch_rule FEqIntro (FOrIntroL x11) = false
  | equal_fitch_rule (FOrIntroL x11) (FExistsElim (x201, x202)) = false
  | equal_fitch_rule (FExistsElim (x201, x202)) (FOrIntroL x11) = false
  | equal_fitch_rule (FOrIntroL x11) (FExistsIntro x19) = false
  | equal_fitch_rule (FExistsIntro x19) (FOrIntroL x11) = false
  | equal_fitch_rule (FOrIntroL x11) (FForallIntro x18) = false
  | equal_fitch_rule (FForallIntro x18) (FOrIntroL x11) = false
  | equal_fitch_rule (FOrIntroL x11) (FForallElim x17) = false
  | equal_fitch_rule (FForallElim x17) (FOrIntroL x11) = false
  | equal_fitch_rule (FOrIntroL x11) (FIffElimR x16) = false
  | equal_fitch_rule (FIffElimR x16) (FOrIntroL x11) = false
  | equal_fitch_rule (FOrIntroL x11) (FIffElimL x15) = false
  | equal_fitch_rule (FIffElimL x15) (FOrIntroL x11) = false
  | equal_fitch_rule (FOrIntroL x11) (FIffIntro (x141, x142)) = false
  | equal_fitch_rule (FIffIntro (x141, x142)) (FOrIntroL x11) = false
  | equal_fitch_rule (FOrIntroL x11) (FOrElim (x131, x132, x133)) = false
  | equal_fitch_rule (FOrElim (x131, x132, x133)) (FOrIntroL x11) = false
  | equal_fitch_rule (FOrIntroL x11) (FOrIntroR x12) = false
  | equal_fitch_rule (FOrIntroR x12) (FOrIntroL x11) = false
  | equal_fitch_rule (FAndElimR x10) (FReit x23) = false
  | equal_fitch_rule (FReit x23) (FAndElimR x10) = false
  | equal_fitch_rule (FAndElimR x10) (FEqElim (x221, x222)) = false
  | equal_fitch_rule (FEqElim (x221, x222)) (FAndElimR x10) = false
  | equal_fitch_rule (FAndElimR x10) FEqIntro = false
  | equal_fitch_rule FEqIntro (FAndElimR x10) = false
  | equal_fitch_rule (FAndElimR x10) (FExistsElim (x201, x202)) = false
  | equal_fitch_rule (FExistsElim (x201, x202)) (FAndElimR x10) = false
  | equal_fitch_rule (FAndElimR x10) (FExistsIntro x19) = false
  | equal_fitch_rule (FExistsIntro x19) (FAndElimR x10) = false
  | equal_fitch_rule (FAndElimR x10) (FForallIntro x18) = false
  | equal_fitch_rule (FForallIntro x18) (FAndElimR x10) = false
  | equal_fitch_rule (FAndElimR x10) (FForallElim x17) = false
  | equal_fitch_rule (FForallElim x17) (FAndElimR x10) = false
  | equal_fitch_rule (FAndElimR x10) (FIffElimR x16) = false
  | equal_fitch_rule (FIffElimR x16) (FAndElimR x10) = false
  | equal_fitch_rule (FAndElimR x10) (FIffElimL x15) = false
  | equal_fitch_rule (FIffElimL x15) (FAndElimR x10) = false
  | equal_fitch_rule (FAndElimR x10) (FIffIntro (x141, x142)) = false
  | equal_fitch_rule (FIffIntro (x141, x142)) (FAndElimR x10) = false
  | equal_fitch_rule (FAndElimR x10) (FOrElim (x131, x132, x133)) = false
  | equal_fitch_rule (FOrElim (x131, x132, x133)) (FAndElimR x10) = false
  | equal_fitch_rule (FAndElimR x10) (FOrIntroR x12) = false
  | equal_fitch_rule (FOrIntroR x12) (FAndElimR x10) = false
  | equal_fitch_rule (FAndElimR x10) (FOrIntroL x11) = false
  | equal_fitch_rule (FOrIntroL x11) (FAndElimR x10) = false
  | equal_fitch_rule (FAndElimL x9) (FReit x23) = false
  | equal_fitch_rule (FReit x23) (FAndElimL x9) = false
  | equal_fitch_rule (FAndElimL x9) (FEqElim (x221, x222)) = false
  | equal_fitch_rule (FEqElim (x221, x222)) (FAndElimL x9) = false
  | equal_fitch_rule (FAndElimL x9) FEqIntro = false
  | equal_fitch_rule FEqIntro (FAndElimL x9) = false
  | equal_fitch_rule (FAndElimL x9) (FExistsElim (x201, x202)) = false
  | equal_fitch_rule (FExistsElim (x201, x202)) (FAndElimL x9) = false
  | equal_fitch_rule (FAndElimL x9) (FExistsIntro x19) = false
  | equal_fitch_rule (FExistsIntro x19) (FAndElimL x9) = false
  | equal_fitch_rule (FAndElimL x9) (FForallIntro x18) = false
  | equal_fitch_rule (FForallIntro x18) (FAndElimL x9) = false
  | equal_fitch_rule (FAndElimL x9) (FForallElim x17) = false
  | equal_fitch_rule (FForallElim x17) (FAndElimL x9) = false
  | equal_fitch_rule (FAndElimL x9) (FIffElimR x16) = false
  | equal_fitch_rule (FIffElimR x16) (FAndElimL x9) = false
  | equal_fitch_rule (FAndElimL x9) (FIffElimL x15) = false
  | equal_fitch_rule (FIffElimL x15) (FAndElimL x9) = false
  | equal_fitch_rule (FAndElimL x9) (FIffIntro (x141, x142)) = false
  | equal_fitch_rule (FIffIntro (x141, x142)) (FAndElimL x9) = false
  | equal_fitch_rule (FAndElimL x9) (FOrElim (x131, x132, x133)) = false
  | equal_fitch_rule (FOrElim (x131, x132, x133)) (FAndElimL x9) = false
  | equal_fitch_rule (FAndElimL x9) (FOrIntroR x12) = false
  | equal_fitch_rule (FOrIntroR x12) (FAndElimL x9) = false
  | equal_fitch_rule (FAndElimL x9) (FOrIntroL x11) = false
  | equal_fitch_rule (FOrIntroL x11) (FAndElimL x9) = false
  | equal_fitch_rule (FAndElimL x9) (FAndElimR x10) = false
  | equal_fitch_rule (FAndElimR x10) (FAndElimL x9) = false
  | equal_fitch_rule (FAndIntro (x81, x82)) (FReit x23) = false
  | equal_fitch_rule (FReit x23) (FAndIntro (x81, x82)) = false
  | equal_fitch_rule (FAndIntro (x81, x82)) (FEqElim (x221, x222)) = false
  | equal_fitch_rule (FEqElim (x221, x222)) (FAndIntro (x81, x82)) = false
  | equal_fitch_rule (FAndIntro (x81, x82)) FEqIntro = false
  | equal_fitch_rule FEqIntro (FAndIntro (x81, x82)) = false
  | equal_fitch_rule (FAndIntro (x81, x82)) (FExistsElim (x201, x202)) = false
  | equal_fitch_rule (FExistsElim (x201, x202)) (FAndIntro (x81, x82)) = false
  | equal_fitch_rule (FAndIntro (x81, x82)) (FExistsIntro x19) = false
  | equal_fitch_rule (FExistsIntro x19) (FAndIntro (x81, x82)) = false
  | equal_fitch_rule (FAndIntro (x81, x82)) (FForallIntro x18) = false
  | equal_fitch_rule (FForallIntro x18) (FAndIntro (x81, x82)) = false
  | equal_fitch_rule (FAndIntro (x81, x82)) (FForallElim x17) = false
  | equal_fitch_rule (FForallElim x17) (FAndIntro (x81, x82)) = false
  | equal_fitch_rule (FAndIntro (x81, x82)) (FIffElimR x16) = false
  | equal_fitch_rule (FIffElimR x16) (FAndIntro (x81, x82)) = false
  | equal_fitch_rule (FAndIntro (x81, x82)) (FIffElimL x15) = false
  | equal_fitch_rule (FIffElimL x15) (FAndIntro (x81, x82)) = false
  | equal_fitch_rule (FAndIntro (x81, x82)) (FIffIntro (x141, x142)) = false
  | equal_fitch_rule (FIffIntro (x141, x142)) (FAndIntro (x81, x82)) = false
  | equal_fitch_rule (FAndIntro (x81, x82)) (FOrElim (x131, x132, x133)) = false
  | equal_fitch_rule (FOrElim (x131, x132, x133)) (FAndIntro (x81, x82)) = false
  | equal_fitch_rule (FAndIntro (x81, x82)) (FOrIntroR x12) = false
  | equal_fitch_rule (FOrIntroR x12) (FAndIntro (x81, x82)) = false
  | equal_fitch_rule (FAndIntro (x81, x82)) (FOrIntroL x11) = false
  | equal_fitch_rule (FOrIntroL x11) (FAndIntro (x81, x82)) = false
  | equal_fitch_rule (FAndIntro (x81, x82)) (FAndElimR x10) = false
  | equal_fitch_rule (FAndElimR x10) (FAndIntro (x81, x82)) = false
  | equal_fitch_rule (FAndIntro (x81, x82)) (FAndElimL x9) = false
  | equal_fitch_rule (FAndElimL x9) (FAndIntro (x81, x82)) = false
  | equal_fitch_rule (FBotI (x71, x72)) (FReit x23) = false
  | equal_fitch_rule (FReit x23) (FBotI (x71, x72)) = false
  | equal_fitch_rule (FBotI (x71, x72)) (FEqElim (x221, x222)) = false
  | equal_fitch_rule (FEqElim (x221, x222)) (FBotI (x71, x72)) = false
  | equal_fitch_rule (FBotI (x71, x72)) FEqIntro = false
  | equal_fitch_rule FEqIntro (FBotI (x71, x72)) = false
  | equal_fitch_rule (FBotI (x71, x72)) (FExistsElim (x201, x202)) = false
  | equal_fitch_rule (FExistsElim (x201, x202)) (FBotI (x71, x72)) = false
  | equal_fitch_rule (FBotI (x71, x72)) (FExistsIntro x19) = false
  | equal_fitch_rule (FExistsIntro x19) (FBotI (x71, x72)) = false
  | equal_fitch_rule (FBotI (x71, x72)) (FForallIntro x18) = false
  | equal_fitch_rule (FForallIntro x18) (FBotI (x71, x72)) = false
  | equal_fitch_rule (FBotI (x71, x72)) (FForallElim x17) = false
  | equal_fitch_rule (FForallElim x17) (FBotI (x71, x72)) = false
  | equal_fitch_rule (FBotI (x71, x72)) (FIffElimR x16) = false
  | equal_fitch_rule (FIffElimR x16) (FBotI (x71, x72)) = false
  | equal_fitch_rule (FBotI (x71, x72)) (FIffElimL x15) = false
  | equal_fitch_rule (FIffElimL x15) (FBotI (x71, x72)) = false
  | equal_fitch_rule (FBotI (x71, x72)) (FIffIntro (x141, x142)) = false
  | equal_fitch_rule (FIffIntro (x141, x142)) (FBotI (x71, x72)) = false
  | equal_fitch_rule (FBotI (x71, x72)) (FOrElim (x131, x132, x133)) = false
  | equal_fitch_rule (FOrElim (x131, x132, x133)) (FBotI (x71, x72)) = false
  | equal_fitch_rule (FBotI (x71, x72)) (FOrIntroR x12) = false
  | equal_fitch_rule (FOrIntroR x12) (FBotI (x71, x72)) = false
  | equal_fitch_rule (FBotI (x71, x72)) (FOrIntroL x11) = false
  | equal_fitch_rule (FOrIntroL x11) (FBotI (x71, x72)) = false
  | equal_fitch_rule (FBotI (x71, x72)) (FAndElimR x10) = false
  | equal_fitch_rule (FAndElimR x10) (FBotI (x71, x72)) = false
  | equal_fitch_rule (FBotI (x71, x72)) (FAndElimL x9) = false
  | equal_fitch_rule (FAndElimL x9) (FBotI (x71, x72)) = false
  | equal_fitch_rule (FBotI (x71, x72)) (FAndIntro (x81, x82)) = false
  | equal_fitch_rule (FAndIntro (x81, x82)) (FBotI (x71, x72)) = false
  | equal_fitch_rule (FDN x6) (FReit x23) = false
  | equal_fitch_rule (FReit x23) (FDN x6) = false
  | equal_fitch_rule (FDN x6) (FEqElim (x221, x222)) = false
  | equal_fitch_rule (FEqElim (x221, x222)) (FDN x6) = false
  | equal_fitch_rule (FDN x6) FEqIntro = false
  | equal_fitch_rule FEqIntro (FDN x6) = false
  | equal_fitch_rule (FDN x6) (FExistsElim (x201, x202)) = false
  | equal_fitch_rule (FExistsElim (x201, x202)) (FDN x6) = false
  | equal_fitch_rule (FDN x6) (FExistsIntro x19) = false
  | equal_fitch_rule (FExistsIntro x19) (FDN x6) = false
  | equal_fitch_rule (FDN x6) (FForallIntro x18) = false
  | equal_fitch_rule (FForallIntro x18) (FDN x6) = false
  | equal_fitch_rule (FDN x6) (FForallElim x17) = false
  | equal_fitch_rule (FForallElim x17) (FDN x6) = false
  | equal_fitch_rule (FDN x6) (FIffElimR x16) = false
  | equal_fitch_rule (FIffElimR x16) (FDN x6) = false
  | equal_fitch_rule (FDN x6) (FIffElimL x15) = false
  | equal_fitch_rule (FIffElimL x15) (FDN x6) = false
  | equal_fitch_rule (FDN x6) (FIffIntro (x141, x142)) = false
  | equal_fitch_rule (FIffIntro (x141, x142)) (FDN x6) = false
  | equal_fitch_rule (FDN x6) (FOrElim (x131, x132, x133)) = false
  | equal_fitch_rule (FOrElim (x131, x132, x133)) (FDN x6) = false
  | equal_fitch_rule (FDN x6) (FOrIntroR x12) = false
  | equal_fitch_rule (FOrIntroR x12) (FDN x6) = false
  | equal_fitch_rule (FDN x6) (FOrIntroL x11) = false
  | equal_fitch_rule (FOrIntroL x11) (FDN x6) = false
  | equal_fitch_rule (FDN x6) (FAndElimR x10) = false
  | equal_fitch_rule (FAndElimR x10) (FDN x6) = false
  | equal_fitch_rule (FDN x6) (FAndElimL x9) = false
  | equal_fitch_rule (FAndElimL x9) (FDN x6) = false
  | equal_fitch_rule (FDN x6) (FAndIntro (x81, x82)) = false
  | equal_fitch_rule (FAndIntro (x81, x82)) (FDN x6) = false
  | equal_fitch_rule (FDN x6) (FBotI (x71, x72)) = false
  | equal_fitch_rule (FBotI (x71, x72)) (FDN x6) = false
  | equal_fitch_rule (FRAA x5) (FReit x23) = false
  | equal_fitch_rule (FReit x23) (FRAA x5) = false
  | equal_fitch_rule (FRAA x5) (FEqElim (x221, x222)) = false
  | equal_fitch_rule (FEqElim (x221, x222)) (FRAA x5) = false
  | equal_fitch_rule (FRAA x5) FEqIntro = false
  | equal_fitch_rule FEqIntro (FRAA x5) = false
  | equal_fitch_rule (FRAA x5) (FExistsElim (x201, x202)) = false
  | equal_fitch_rule (FExistsElim (x201, x202)) (FRAA x5) = false
  | equal_fitch_rule (FRAA x5) (FExistsIntro x19) = false
  | equal_fitch_rule (FExistsIntro x19) (FRAA x5) = false
  | equal_fitch_rule (FRAA x5) (FForallIntro x18) = false
  | equal_fitch_rule (FForallIntro x18) (FRAA x5) = false
  | equal_fitch_rule (FRAA x5) (FForallElim x17) = false
  | equal_fitch_rule (FForallElim x17) (FRAA x5) = false
  | equal_fitch_rule (FRAA x5) (FIffElimR x16) = false
  | equal_fitch_rule (FIffElimR x16) (FRAA x5) = false
  | equal_fitch_rule (FRAA x5) (FIffElimL x15) = false
  | equal_fitch_rule (FIffElimL x15) (FRAA x5) = false
  | equal_fitch_rule (FRAA x5) (FIffIntro (x141, x142)) = false
  | equal_fitch_rule (FIffIntro (x141, x142)) (FRAA x5) = false
  | equal_fitch_rule (FRAA x5) (FOrElim (x131, x132, x133)) = false
  | equal_fitch_rule (FOrElim (x131, x132, x133)) (FRAA x5) = false
  | equal_fitch_rule (FRAA x5) (FOrIntroR x12) = false
  | equal_fitch_rule (FOrIntroR x12) (FRAA x5) = false
  | equal_fitch_rule (FRAA x5) (FOrIntroL x11) = false
  | equal_fitch_rule (FOrIntroL x11) (FRAA x5) = false
  | equal_fitch_rule (FRAA x5) (FAndElimR x10) = false
  | equal_fitch_rule (FAndElimR x10) (FRAA x5) = false
  | equal_fitch_rule (FRAA x5) (FAndElimL x9) = false
  | equal_fitch_rule (FAndElimL x9) (FRAA x5) = false
  | equal_fitch_rule (FRAA x5) (FAndIntro (x81, x82)) = false
  | equal_fitch_rule (FAndIntro (x81, x82)) (FRAA x5) = false
  | equal_fitch_rule (FRAA x5) (FBotI (x71, x72)) = false
  | equal_fitch_rule (FBotI (x71, x72)) (FRAA x5) = false
  | equal_fitch_rule (FRAA x5) (FDN x6) = false
  | equal_fitch_rule (FDN x6) (FRAA x5) = false
  | equal_fitch_rule (FCP x4) (FReit x23) = false
  | equal_fitch_rule (FReit x23) (FCP x4) = false
  | equal_fitch_rule (FCP x4) (FEqElim (x221, x222)) = false
  | equal_fitch_rule (FEqElim (x221, x222)) (FCP x4) = false
  | equal_fitch_rule (FCP x4) FEqIntro = false
  | equal_fitch_rule FEqIntro (FCP x4) = false
  | equal_fitch_rule (FCP x4) (FExistsElim (x201, x202)) = false
  | equal_fitch_rule (FExistsElim (x201, x202)) (FCP x4) = false
  | equal_fitch_rule (FCP x4) (FExistsIntro x19) = false
  | equal_fitch_rule (FExistsIntro x19) (FCP x4) = false
  | equal_fitch_rule (FCP x4) (FForallIntro x18) = false
  | equal_fitch_rule (FForallIntro x18) (FCP x4) = false
  | equal_fitch_rule (FCP x4) (FForallElim x17) = false
  | equal_fitch_rule (FForallElim x17) (FCP x4) = false
  | equal_fitch_rule (FCP x4) (FIffElimR x16) = false
  | equal_fitch_rule (FIffElimR x16) (FCP x4) = false
  | equal_fitch_rule (FCP x4) (FIffElimL x15) = false
  | equal_fitch_rule (FIffElimL x15) (FCP x4) = false
  | equal_fitch_rule (FCP x4) (FIffIntro (x141, x142)) = false
  | equal_fitch_rule (FIffIntro (x141, x142)) (FCP x4) = false
  | equal_fitch_rule (FCP x4) (FOrElim (x131, x132, x133)) = false
  | equal_fitch_rule (FOrElim (x131, x132, x133)) (FCP x4) = false
  | equal_fitch_rule (FCP x4) (FOrIntroR x12) = false
  | equal_fitch_rule (FOrIntroR x12) (FCP x4) = false
  | equal_fitch_rule (FCP x4) (FOrIntroL x11) = false
  | equal_fitch_rule (FOrIntroL x11) (FCP x4) = false
  | equal_fitch_rule (FCP x4) (FAndElimR x10) = false
  | equal_fitch_rule (FAndElimR x10) (FCP x4) = false
  | equal_fitch_rule (FCP x4) (FAndElimL x9) = false
  | equal_fitch_rule (FAndElimL x9) (FCP x4) = false
  | equal_fitch_rule (FCP x4) (FAndIntro (x81, x82)) = false
  | equal_fitch_rule (FAndIntro (x81, x82)) (FCP x4) = false
  | equal_fitch_rule (FCP x4) (FBotI (x71, x72)) = false
  | equal_fitch_rule (FBotI (x71, x72)) (FCP x4) = false
  | equal_fitch_rule (FCP x4) (FDN x6) = false
  | equal_fitch_rule (FDN x6) (FCP x4) = false
  | equal_fitch_rule (FCP x4) (FRAA x5) = false
  | equal_fitch_rule (FRAA x5) (FCP x4) = false
  | equal_fitch_rule (FMP (x31, x32)) (FReit x23) = false
  | equal_fitch_rule (FReit x23) (FMP (x31, x32)) = false
  | equal_fitch_rule (FMP (x31, x32)) (FEqElim (x221, x222)) = false
  | equal_fitch_rule (FEqElim (x221, x222)) (FMP (x31, x32)) = false
  | equal_fitch_rule (FMP (x31, x32)) FEqIntro = false
  | equal_fitch_rule FEqIntro (FMP (x31, x32)) = false
  | equal_fitch_rule (FMP (x31, x32)) (FExistsElim (x201, x202)) = false
  | equal_fitch_rule (FExistsElim (x201, x202)) (FMP (x31, x32)) = false
  | equal_fitch_rule (FMP (x31, x32)) (FExistsIntro x19) = false
  | equal_fitch_rule (FExistsIntro x19) (FMP (x31, x32)) = false
  | equal_fitch_rule (FMP (x31, x32)) (FForallIntro x18) = false
  | equal_fitch_rule (FForallIntro x18) (FMP (x31, x32)) = false
  | equal_fitch_rule (FMP (x31, x32)) (FForallElim x17) = false
  | equal_fitch_rule (FForallElim x17) (FMP (x31, x32)) = false
  | equal_fitch_rule (FMP (x31, x32)) (FIffElimR x16) = false
  | equal_fitch_rule (FIffElimR x16) (FMP (x31, x32)) = false
  | equal_fitch_rule (FMP (x31, x32)) (FIffElimL x15) = false
  | equal_fitch_rule (FIffElimL x15) (FMP (x31, x32)) = false
  | equal_fitch_rule (FMP (x31, x32)) (FIffIntro (x141, x142)) = false
  | equal_fitch_rule (FIffIntro (x141, x142)) (FMP (x31, x32)) = false
  | equal_fitch_rule (FMP (x31, x32)) (FOrElim (x131, x132, x133)) = false
  | equal_fitch_rule (FOrElim (x131, x132, x133)) (FMP (x31, x32)) = false
  | equal_fitch_rule (FMP (x31, x32)) (FOrIntroR x12) = false
  | equal_fitch_rule (FOrIntroR x12) (FMP (x31, x32)) = false
  | equal_fitch_rule (FMP (x31, x32)) (FOrIntroL x11) = false
  | equal_fitch_rule (FOrIntroL x11) (FMP (x31, x32)) = false
  | equal_fitch_rule (FMP (x31, x32)) (FAndElimR x10) = false
  | equal_fitch_rule (FAndElimR x10) (FMP (x31, x32)) = false
  | equal_fitch_rule (FMP (x31, x32)) (FAndElimL x9) = false
  | equal_fitch_rule (FAndElimL x9) (FMP (x31, x32)) = false
  | equal_fitch_rule (FMP (x31, x32)) (FAndIntro (x81, x82)) = false
  | equal_fitch_rule (FAndIntro (x81, x82)) (FMP (x31, x32)) = false
  | equal_fitch_rule (FMP (x31, x32)) (FBotI (x71, x72)) = false
  | equal_fitch_rule (FBotI (x71, x72)) (FMP (x31, x32)) = false
  | equal_fitch_rule (FMP (x31, x32)) (FDN x6) = false
  | equal_fitch_rule (FDN x6) (FMP (x31, x32)) = false
  | equal_fitch_rule (FMP (x31, x32)) (FRAA x5) = false
  | equal_fitch_rule (FRAA x5) (FMP (x31, x32)) = false
  | equal_fitch_rule (FMP (x31, x32)) (FCP x4) = false
  | equal_fitch_rule (FCP x4) (FMP (x31, x32)) = false
  | equal_fitch_rule FAssume (FReit x23) = false
  | equal_fitch_rule (FReit x23) FAssume = false
  | equal_fitch_rule FAssume (FEqElim (x221, x222)) = false
  | equal_fitch_rule (FEqElim (x221, x222)) FAssume = false
  | equal_fitch_rule FAssume FEqIntro = false
  | equal_fitch_rule FEqIntro FAssume = false
  | equal_fitch_rule FAssume (FExistsElim (x201, x202)) = false
  | equal_fitch_rule (FExistsElim (x201, x202)) FAssume = false
  | equal_fitch_rule FAssume (FExistsIntro x19) = false
  | equal_fitch_rule (FExistsIntro x19) FAssume = false
  | equal_fitch_rule FAssume (FForallIntro x18) = false
  | equal_fitch_rule (FForallIntro x18) FAssume = false
  | equal_fitch_rule FAssume (FForallElim x17) = false
  | equal_fitch_rule (FForallElim x17) FAssume = false
  | equal_fitch_rule FAssume (FIffElimR x16) = false
  | equal_fitch_rule (FIffElimR x16) FAssume = false
  | equal_fitch_rule FAssume (FIffElimL x15) = false
  | equal_fitch_rule (FIffElimL x15) FAssume = false
  | equal_fitch_rule FAssume (FIffIntro (x141, x142)) = false
  | equal_fitch_rule (FIffIntro (x141, x142)) FAssume = false
  | equal_fitch_rule FAssume (FOrElim (x131, x132, x133)) = false
  | equal_fitch_rule (FOrElim (x131, x132, x133)) FAssume = false
  | equal_fitch_rule FAssume (FOrIntroR x12) = false
  | equal_fitch_rule (FOrIntroR x12) FAssume = false
  | equal_fitch_rule FAssume (FOrIntroL x11) = false
  | equal_fitch_rule (FOrIntroL x11) FAssume = false
  | equal_fitch_rule FAssume (FAndElimR x10) = false
  | equal_fitch_rule (FAndElimR x10) FAssume = false
  | equal_fitch_rule FAssume (FAndElimL x9) = false
  | equal_fitch_rule (FAndElimL x9) FAssume = false
  | equal_fitch_rule FAssume (FAndIntro (x81, x82)) = false
  | equal_fitch_rule (FAndIntro (x81, x82)) FAssume = false
  | equal_fitch_rule FAssume (FBotI (x71, x72)) = false
  | equal_fitch_rule (FBotI (x71, x72)) FAssume = false
  | equal_fitch_rule FAssume (FDN x6) = false
  | equal_fitch_rule (FDN x6) FAssume = false
  | equal_fitch_rule FAssume (FRAA x5) = false
  | equal_fitch_rule (FRAA x5) FAssume = false
  | equal_fitch_rule FAssume (FCP x4) = false
  | equal_fitch_rule (FCP x4) FAssume = false
  | equal_fitch_rule FAssume (FMP (x31, x32)) = false
  | equal_fitch_rule (FMP (x31, x32)) FAssume = false
  | equal_fitch_rule FPremise (FReit x23) = false
  | equal_fitch_rule (FReit x23) FPremise = false
  | equal_fitch_rule FPremise (FEqElim (x221, x222)) = false
  | equal_fitch_rule (FEqElim (x221, x222)) FPremise = false
  | equal_fitch_rule FPremise FEqIntro = false
  | equal_fitch_rule FEqIntro FPremise = false
  | equal_fitch_rule FPremise (FExistsElim (x201, x202)) = false
  | equal_fitch_rule (FExistsElim (x201, x202)) FPremise = false
  | equal_fitch_rule FPremise (FExistsIntro x19) = false
  | equal_fitch_rule (FExistsIntro x19) FPremise = false
  | equal_fitch_rule FPremise (FForallIntro x18) = false
  | equal_fitch_rule (FForallIntro x18) FPremise = false
  | equal_fitch_rule FPremise (FForallElim x17) = false
  | equal_fitch_rule (FForallElim x17) FPremise = false
  | equal_fitch_rule FPremise (FIffElimR x16) = false
  | equal_fitch_rule (FIffElimR x16) FPremise = false
  | equal_fitch_rule FPremise (FIffElimL x15) = false
  | equal_fitch_rule (FIffElimL x15) FPremise = false
  | equal_fitch_rule FPremise (FIffIntro (x141, x142)) = false
  | equal_fitch_rule (FIffIntro (x141, x142)) FPremise = false
  | equal_fitch_rule FPremise (FOrElim (x131, x132, x133)) = false
  | equal_fitch_rule (FOrElim (x131, x132, x133)) FPremise = false
  | equal_fitch_rule FPremise (FOrIntroR x12) = false
  | equal_fitch_rule (FOrIntroR x12) FPremise = false
  | equal_fitch_rule FPremise (FOrIntroL x11) = false
  | equal_fitch_rule (FOrIntroL x11) FPremise = false
  | equal_fitch_rule FPremise (FAndElimR x10) = false
  | equal_fitch_rule (FAndElimR x10) FPremise = false
  | equal_fitch_rule FPremise (FAndElimL x9) = false
  | equal_fitch_rule (FAndElimL x9) FPremise = false
  | equal_fitch_rule FPremise (FAndIntro (x81, x82)) = false
  | equal_fitch_rule (FAndIntro (x81, x82)) FPremise = false
  | equal_fitch_rule FPremise (FBotI (x71, x72)) = false
  | equal_fitch_rule (FBotI (x71, x72)) FPremise = false
  | equal_fitch_rule FPremise (FDN x6) = false
  | equal_fitch_rule (FDN x6) FPremise = false
  | equal_fitch_rule FPremise (FRAA x5) = false
  | equal_fitch_rule (FRAA x5) FPremise = false
  | equal_fitch_rule FPremise (FCP x4) = false
  | equal_fitch_rule (FCP x4) FPremise = false
  | equal_fitch_rule FPremise (FMP (x31, x32)) = false
  | equal_fitch_rule (FMP (x31, x32)) FPremise = false
  | equal_fitch_rule FPremise FAssume = false
  | equal_fitch_rule FAssume FPremise = false
  | equal_fitch_rule (FReit x23) (FReit y23) = equal_nata x23 y23
  | equal_fitch_rule (FEqElim (x221, x222)) (FEqElim (y221, y222)) =
    equal_nata x221 y221 andalso equal_nata x222 y222
  | equal_fitch_rule (FExistsElim (x201, x202)) (FExistsElim (y201, y202)) =
    equal_nata x201 y201 andalso equal_proda equal_nat equal_nat x202 y202
  | equal_fitch_rule (FExistsIntro x19) (FExistsIntro y19) = equal_nata x19 y19
  | equal_fitch_rule (FForallIntro x18) (FForallIntro y18) = equal_nata x18 y18
  | equal_fitch_rule (FForallElim x17) (FForallElim y17) = equal_nata x17 y17
  | equal_fitch_rule (FIffElimR x16) (FIffElimR y16) = equal_nata x16 y16
  | equal_fitch_rule (FIffElimL x15) (FIffElimL y15) = equal_nata x15 y15
  | equal_fitch_rule (FIffIntro (x141, x142)) (FIffIntro (y141, y142)) =
    equal_nata x141 y141 andalso equal_nata x142 y142
  | equal_fitch_rule (FOrElim (x131, x132, x133)) (FOrElim (y131, y132, y133)) =
    equal_nata x131 y131 andalso
      (equal_proda equal_nat equal_nat x132 y132 andalso
        equal_proda equal_nat equal_nat x133 y133)
  | equal_fitch_rule (FOrIntroR x12) (FOrIntroR y12) = equal_nata x12 y12
  | equal_fitch_rule (FOrIntroL x11) (FOrIntroL y11) = equal_nata x11 y11
  | equal_fitch_rule (FAndElimR x10) (FAndElimR y10) = equal_nata x10 y10
  | equal_fitch_rule (FAndElimL x9) (FAndElimL y9) = equal_nata x9 y9
  | equal_fitch_rule (FAndIntro (x81, x82)) (FAndIntro (y81, y82)) =
    equal_nata x81 y81 andalso equal_nata x82 y82
  | equal_fitch_rule (FBotI (x71, x72)) (FBotI (y71, y72)) =
    equal_nata x71 y71 andalso equal_nata x72 y72
  | equal_fitch_rule (FDN x6) (FDN y6) = equal_nata x6 y6
  | equal_fitch_rule (FRAA x5) (FRAA y5) = equal_proda equal_nat equal_nat x5 y5
  | equal_fitch_rule (FCP x4) (FCP y4) = equal_proda equal_nat equal_nat x4 y4
  | equal_fitch_rule (FMP (x31, x32)) (FMP (y31, y32)) =
    equal_nata x31 y31 andalso equal_nata x32 y32
  | equal_fitch_rule FEqIntro FEqIntro = true
  | equal_fitch_rule FAssume FAssume = true
  | equal_fitch_rule FPremise FPremise = true;

fun noAssumeLinesItem (FLine (uu, uv, r)) = not (equal_fitch_rule r FAssume)
  | noAssumeLinesItem (FSub s) = noAssumeLinesSub s
and noAssumeLinesSub (Subproof (uw, ux, body)) =
  list_all noAssumeLinesItem body;

fun lastIsLineItem (FLine (uu, uv, uw)) = true
  | lastIsLineItem (FSub s) = lastIsLineSub s
and lastIsLineSub (Subproof (ux, uy, body)) =
  list_all lastIsLineItem body andalso
    (null body orelse
      (case last body of FLine (_, _, _) => true | FSub _ => false));

fun concludesAtTop f =
  null f orelse (case last f of FLine (_, _, _) => true | FSub _ => false);

fun flRule (FL (x1, x2, x3, x4)) = x3;

fun flatItem (FLine (n, f, r)) path = [FL (n, f, r, path)]
  | flatItem (FSub s) path = flatSub s path
and flatSub (Subproof (a, fa, body)) path =
  FL (a, fa, FAssume, path @ [a]) ::
    maps (fn it => flatItem it (path @ [a])) body;

fun flatten f = maps (fn it => flatItem it []) f;

fun premisesFirst f =
  list_all (fn fl => not (equal_fitch_rule (flRule fl) FPremise))
    (dropWhile (fn fl => equal_fitch_rule (flRule fl) FPremise) (flatten f));

fun flScope (FL (x1, x2, x3, x4)) = x4;

fun fCitedLines FPremise = []
  | fCitedLines FAssume = []
  | fCitedLines (FMP (i, j)) = [i, j]
  | fCitedLines (FCP uu) = []
  | fCitedLines (FRAA uv) = []
  | fCitedLines (FDN i) = [i]
  | fCitedLines (FBotI (i, j)) = [i, j]
  | fCitedLines (FAndIntro (i, j)) = [i, j]
  | fCitedLines (FAndElimL i) = [i]
  | fCitedLines (FAndElimR i) = [i]
  | fCitedLines (FOrIntroL i) = [i]
  | fCitedLines (FOrIntroR i) = [i]
  | fCitedLines (FOrElim (d, uw, ux)) = [d]
  | fCitedLines (FIffIntro (i, j)) = [i, j]
  | fCitedLines (FIffElimL i) = [i]
  | fCitedLines (FIffElimR i) = [i]
  | fCitedLines (FForallElim i) = [i]
  | fCitedLines (FForallIntro i) = [i]
  | fCitedLines (FExistsIntro i) = [i]
  | fCitedLines (FExistsElim (m, uy)) = [m]
  | fCitedLines FEqIntro = []
  | fCitedLines (FEqElim (i, j)) = [i, j]
  | fCitedLines (FReit i) = [i];

fun fCitedSubs (FCP s) = [s]
  | fCitedSubs (FRAA s) = [s]
  | fCitedSubs (FOrElim (uu, s1, s2)) = [s1, s2]
  | fCitedSubs (FExistsElim (uv, s)) = [s]
  | fCitedSubs FPremise = []
  | fCitedSubs FAssume = []
  | fCitedSubs (FMP (v, va)) = []
  | fCitedSubs (FDN v) = []
  | fCitedSubs (FBotI (v, va)) = []
  | fCitedSubs (FAndIntro (v, va)) = []
  | fCitedSubs (FAndElimL v) = []
  | fCitedSubs (FAndElimR v) = []
  | fCitedSubs (FOrIntroL v) = []
  | fCitedSubs (FOrIntroR v) = []
  | fCitedSubs (FIffIntro (v, va)) = []
  | fCitedSubs (FIffElimL v) = []
  | fCitedSubs (FIffElimR v) = []
  | fCitedSubs (FForallElim v) = []
  | fCitedSubs (FForallIntro v) = []
  | fCitedSubs (FExistsIntro v) = []
  | fCitedSubs FEqIntro = []
  | fCitedSubs (FEqElim (v, va)) = []
  | fCitedSubs (FReit v) = [];

fun is_prefix A_ [] ys = true
  | is_prefix A_ (x :: xs) [] = false
  | is_prefix A_ (x :: xs) (y :: ys) = eq A_ x y andalso is_prefix A_ xs ys;

fun subLastLine s = flNum (last (flatSub s []));

fun subrefsItem (FLine (uu, uv, uw)) path = []
  | subrefsItem (FSub s) path = subrefsSub s path
and subrefsSub (Subproof (a, fa, body)) path =
  ((a, subLastLine (Subproof (a, fa, body))), path) ::
    maps (fn it => subrefsItem it (path @ [a])) body;

fun subrefs f = maps (fn it => subrefsItem it []) f;

fun citationOK f fl =
  list_all
    (fn m =>
      less_nat m (flNum fl) andalso
        (case findFL (flatten f) m of NONE => false
          | SOME fla => is_prefix equal_nat (flScope fla) (flScope fl)))
    (fCitedLines (flRule fl)) andalso
    list_all
      (fn (a, c) =>
        less_nat c (flNum fl) andalso
          membera
            (equal_prod (equal_prod equal_nat equal_nat) (equal_list equal_nat))
            (subrefs f) ((a, c), flScope fl))
      (fCitedSubs (flRule fl));

fun fitchWF f =
  sorted_wrt less_nat (map flNum (flatten f)) andalso
    (list_all noAssumeLinesItem f andalso
      (list_all
         (fn fl =>
           (if equal_fitch_rule (flRule fl) FPremise then null (flScope fl)
             else true))
         (flatten f) andalso
        (premisesFirst f andalso
          (list_all lastIsLineItem f andalso
            (concludesAtTop f andalso list_all (citationOK f) (flatten f))))));

fun premiseLines f =
  map_filter
    (fn x =>
      (if equal_fitch_rule (flRule x) FPremise then SOME (flNum x) else NONE))
    (flatten f);

fun scopePath f n =
  (case findFL (flatten f) n of NONE => [] | SOME a => flScope a);

fun scopeOf f n =
  sup_set equal_nat (Set (premiseLines f)) (Set (scopePath f n));

fun hlCorrect p = list_all (hlLineOK p) p;

fun depFms e g =
  map_filter
    (fn x =>
      (if member equal_nat (lineNumber x) g then SOME (formula x) else NONE))
    e;

fun depSrc e n g = depFms e g;

fun references (ProofLine (x1, x2, x3, x4)) = x4;

fun depsAt p n =
  (case lookupLine p n of NONE => bot_set | SOME a => references a);

fun citedLines Assumption = []
  | citedLines (MP (i, j)) = [i, j]
  | citedLines (CP (a, c)) = [a, c]
  | citedLines (RAA (a, c)) = [a, c]
  | citedLines (DN i) = [i]
  | citedLines (BotI (i, j)) = [i, j]
  | citedLines (AndIntro (i, j)) = [i, j]
  | citedLines (AndElimL i) = [i]
  | citedLines (AndElimR i) = [i]
  | citedLines (OrIntroL i) = [i]
  | citedLines (OrIntroR i) = [i]
  | citedLines (OrElim (d, a1, c1, a2, c2)) = [d, a1, c1, a2, c2]
  | citedLines (IffIntro (i, j)) = [i, j]
  | citedLines (IffElimL i) = [i]
  | citedLines (IffElimR i) = [i]
  | citedLines (ForallElim i) = [i]
  | citedLines (ForallIntro i) = [i]
  | citedLines (ExistsIntro i) = [i]
  | citedLines (ExistsElim (m, a, c)) = [m, a, c]
  | citedLines EqIntro = []
  | citedLines (EqElim (i, j)) = [i, j]
  | citedLines (Reit i) = [i];

fun depsOf look j self =
  (case j of Assumption => insert equal_nat self bot_set
    | MP (_, _) => sup_seta equal_nat (Set (map look (citedLines j)))
    | CP (a, c) => remove equal_nat a (look c)
    | RAA (a, c) => remove equal_nat a (look c)
    | DN _ => sup_seta equal_nat (Set (map look (citedLines j)))
    | BotI (_, _) => sup_seta equal_nat (Set (map look (citedLines j)))
    | AndIntro (_, _) => sup_seta equal_nat (Set (map look (citedLines j)))
    | AndElimL _ => sup_seta equal_nat (Set (map look (citedLines j)))
    | AndElimR _ => sup_seta equal_nat (Set (map look (citedLines j)))
    | OrIntroL _ => sup_seta equal_nat (Set (map look (citedLines j)))
    | OrIntroR _ => sup_seta equal_nat (Set (map look (citedLines j)))
    | OrElim (d, a1, c1, a2, c2) =>
      sup_set equal_nat
        (sup_set equal_nat (look d) (remove equal_nat a1 (look c1)))
        (remove equal_nat a2 (look c2))
    | IffIntro (_, _) => sup_seta equal_nat (Set (map look (citedLines j)))
    | IffElimL _ => sup_seta equal_nat (Set (map look (citedLines j)))
    | IffElimR _ => sup_seta equal_nat (Set (map look (citedLines j)))
    | ForallElim _ => sup_seta equal_nat (Set (map look (citedLines j)))
    | ForallIntro _ => sup_seta equal_nat (Set (map look (citedLines j)))
    | ExistsIntro _ => sup_seta equal_nat (Set (map look (citedLines j)))
    | ExistsElim (m, a, c) =>
      sup_set equal_nat (look m) (remove equal_nat a (look c))
    | EqIntro => bot_set
    | EqElim (_, _) => sup_seta equal_nat (Set (map look (citedLines j)))
    | Reit _ => sup_seta equal_nat (Set (map look (citedLines j))));

fun instOK x p q =
  (if membera equal_literal (fvs p) x then not (null (instWitnesses x p q))
    else equal_fma q p);

fun justification (ProofLine (x1, x2, x3, x4)) = x3;

fun justAt p n = map_option justification (lookupLine p n);

fun isAssumptionLine e a =
  equal_option equal_just (justAt e a) (SOME Assumption);

fun ruleOK e phi asa Assumption = true
  | ruleOK e phi asa (MP (i, j)) =
    (case fmAt e i of NONE => false | SOME (Atom (_, _)) => false
      | SOME (Eqf (_, _)) => false | SOME Bot => false | SOME (Neg _) => false
      | SOME (Conj (_, _)) => false | SOME (Disj (_, _)) => false
      | SOME (Impl (p, q)) =>
        equal_option equal_fm (fmAt e j) (SOME p) andalso equal_fma phi q
      | SOME (Iff (_, _)) => false | SOME (Uni (_, _)) => false
      | SOME (Exi (_, _)) => false)
  | ruleOK e phi asa (CP (a, c)) =
    isAssumptionLine e a andalso
      (case (fmAt e a, fmAt e c) of (NONE, _) => false | (SOME _, NONE) => false
        | (SOME p, SOME q) => equal_fma phi (Impl (p, q)))
  | ruleOK e phi asa (RAA (a, c)) =
    isAssumptionLine e a andalso
      (equal_option equal_fm (fmAt e c) (SOME Bot) andalso
        (case fmAt e a of NONE => false | SOME p => equal_fma phi (Neg p)))
  | ruleOK e phi asa (DN i) =
    equal_option equal_fm (fmAt e i) (SOME (Neg (Neg phi)))
  | ruleOK e phi asa (BotI (i, j)) =
    equal_fma phi Bot andalso
      (case fmAt e i of NONE => false
        | SOME p => equal_option equal_fm (fmAt e j) (SOME (Neg p)))
  | ruleOK e phi asa (AndIntro (i, j)) =
    (case phi of Atom (_, _) => false | Eqf (_, _) => false | Bot => false
      | Neg _ => false
      | Conj (p, q) =>
        equal_option equal_fm (fmAt e i) (SOME p) andalso
          equal_option equal_fm (fmAt e j) (SOME q)
      | Disj (_, _) => false | Impl (_, _) => false | Iff (_, _) => false
      | Uni (_, _) => false | Exi (_, _) => false)
  | ruleOK e phi asa (AndElimL i) =
    (case fmAt e i of NONE => false | SOME (Atom (_, _)) => false
      | SOME (Eqf (_, _)) => false | SOME Bot => false | SOME (Neg _) => false
      | SOME (Conj (p, _)) => equal_fma phi p | SOME (Disj (_, _)) => false
      | SOME (Impl (_, _)) => false | SOME (Iff (_, _)) => false
      | SOME (Uni (_, _)) => false | SOME (Exi (_, _)) => false)
  | ruleOK e phi asa (AndElimR i) =
    (case fmAt e i of NONE => false | SOME (Atom (_, _)) => false
      | SOME (Eqf (_, _)) => false | SOME Bot => false | SOME (Neg _) => false
      | SOME (Conj (_, a)) => equal_fma phi a | SOME (Disj (_, _)) => false
      | SOME (Impl (_, _)) => false | SOME (Iff (_, _)) => false
      | SOME (Uni (_, _)) => false | SOME (Exi (_, _)) => false)
  | ruleOK e phi asa (OrIntroL i) =
    (case phi of Atom (_, _) => false | Eqf (_, _) => false | Bot => false
      | Neg _ => false | Conj (_, _) => false
      | Disj (p, _) => equal_option equal_fm (fmAt e i) (SOME p)
      | Impl (_, _) => false | Iff (_, _) => false | Uni (_, _) => false
      | Exi (_, _) => false)
  | ruleOK e phi asa (OrIntroR i) =
    (case phi of Atom (_, _) => false | Eqf (_, _) => false | Bot => false
      | Neg _ => false | Conj (_, _) => false
      | Disj (_, q) => equal_option equal_fm (fmAt e i) (SOME q)
      | Impl (_, _) => false | Iff (_, _) => false | Uni (_, _) => false
      | Exi (_, _) => false)
  | ruleOK e phi asa (OrElim (d, a1, c1, a2, c2)) =
    isAssumptionLine e a1 andalso
      (isAssumptionLine e a2 andalso
        (equal_option equal_fm (fmAt e c1) (SOME phi) andalso
          (equal_option equal_fm (fmAt e c2) (SOME phi) andalso
            (case fmAt e d of NONE => false | SOME (Atom (_, _)) => false
              | SOME (Eqf (_, _)) => false | SOME Bot => false
              | SOME (Neg _) => false | SOME (Conj (_, _)) => false
              | SOME (Disj (p, q)) =>
                equal_option equal_fm (fmAt e a1) (SOME p) andalso
                  equal_option equal_fm (fmAt e a2) (SOME q)
              | SOME (Impl (_, _)) => false | SOME (Iff (_, _)) => false
              | SOME (Uni (_, _)) => false | SOME (Exi (_, _)) => false))))
  | ruleOK e phi asa (IffIntro (i, j)) =
    (case phi of Atom (_, _) => false | Eqf (_, _) => false | Bot => false
      | Neg _ => false | Conj (_, _) => false | Disj (_, _) => false
      | Impl (_, _) => false
      | Iff (p, q) =>
        equal_option equal_fm (fmAt e i) (SOME (Impl (p, q))) andalso
          equal_option equal_fm (fmAt e j) (SOME (Impl (q, p)))
      | Uni (_, _) => false | Exi (_, _) => false)
  | ruleOK e phi asa (IffElimL i) =
    (case phi of Atom (_, _) => false | Eqf (_, _) => false | Bot => false
      | Neg _ => false | Conj (_, _) => false | Disj (_, _) => false
      | Impl (p, q) => equal_option equal_fm (fmAt e i) (SOME (Iff (p, q)))
      | Iff (_, _) => false | Uni (_, _) => false | Exi (_, _) => false)
  | ruleOK e phi asa (IffElimR i) =
    (case phi of Atom (_, _) => false | Eqf (_, _) => false | Bot => false
      | Neg _ => false | Conj (_, _) => false | Disj (_, _) => false
      | Impl (q, p) => equal_option equal_fm (fmAt e i) (SOME (Iff (p, q)))
      | Iff (_, _) => false | Uni (_, _) => false | Exi (_, _) => false)
  | ruleOK e phi asa (ForallElim i) =
    (case fmAt e i of NONE => false | SOME (Atom (_, _)) => false
      | SOME (Eqf (_, _)) => false | SOME Bot => false | SOME (Neg _) => false
      | SOME (Conj (_, _)) => false | SOME (Disj (_, _)) => false
      | SOME (Impl (_, _)) => false | SOME (Iff (_, _)) => false
      | SOME (Uni (x, p)) => instOK x p phi | SOME (Exi (_, _)) => false)
  | ruleOK e phi asa (ForallIntro i) =
    (case (phi, fmAt e i) of (Atom (_, _), _) => false
      | (Eqf (_, _), _) => false | (Bot, _) => false | (Neg _, _) => false
      | (Conj (_, _), _) => false | (Disj (_, _), _) => false
      | (Impl (_, _), _) => false | (Iff (_, _), _) => false
      | (Uni (_, _), NONE) => false
      | (Uni (x, p), SOME psi) => genOK x p psi asa | (Exi (_, _), _) => false)
  | ruleOK e phi asa (ExistsIntro i) =
    (case (phi, fmAt e i) of (Atom (_, _), _) => false
      | (Eqf (_, _), _) => false | (Bot, _) => false | (Neg _, _) => false
      | (Conj (_, _), _) => false | (Disj (_, _), _) => false
      | (Impl (_, _), _) => false | (Iff (_, _), _) => false
      | (Uni (_, _), _) => false | (Exi (_, _), NONE) => false
      | (Exi (x, p), SOME a) => instOK x p a)
  | ruleOK e phi asa (ExistsElim (m, a, c)) =
    isAssumptionLine e a andalso
      (equal_option equal_fm (fmAt e c) (SOME phi) andalso
        (case (fmAt e m, fmAt e a) of (NONE, _) => false
          | (SOME (Atom (_, _)), _) => false | (SOME (Eqf (_, _)), _) => false
          | (SOME Bot, _) => false | (SOME (Neg _), _) => false
          | (SOME (Conj (_, _)), _) => false | (SOME (Disj (_, _)), _) => false
          | (SOME (Impl (_, _)), _) => false | (SOME (Iff (_, _)), _) => false
          | (SOME (Uni (_, _)), _) => false | (SOME (Exi (_, _)), NONE) => false
          | (SOME (Exi (x, p)), SOME psi) => witOK x p psi phi asa))
  | ruleOK e phi asa EqIntro =
    (case phi of Atom (_, _) => false | Eqf (Nm a, Nm b) => ((a : string) = b)
      | Eqf (Nm _, Vr _) => false | Eqf (Vr _, _) => false | Bot => false
      | Neg _ => false | Conj (_, _) => false | Disj (_, _) => false
      | Impl (_, _) => false | Iff (_, _) => false | Uni (_, _) => false
      | Exi (_, _) => false)
  | ruleOK e phi asa (EqElim (i, j)) =
    (case fmAt e i of NONE => false | SOME (Atom (_, _)) => false
      | SOME (Eqf (Nm a, Nm b)) =>
        (case fmAt e j of NONE => false | SOME psi => eqsub a b psi phi)
      | SOME (Eqf (Nm _, Vr _)) => false | SOME (Eqf (Vr _, _)) => false
      | SOME Bot => false | SOME (Neg _) => false | SOME (Conj (_, _)) => false
      | SOME (Disj (_, _)) => false | SOME (Impl (_, _)) => false
      | SOME (Iff (_, _)) => false | SOME (Uni (_, _)) => false
      | SOME (Exi (_, _)) => false)
  | ruleOK e phi asa (Reit i) = equal_option equal_fm (fmAt e i) (SOME phi);

fun showTrm (Nm a) = a
  | showTrm (Vr x) = x;

val symNot : string = isaSym "not";

val symImp : string = isaSym "longrightarrow";

val symIff : string = isaSym "longleftrightarrow";

val symBot : string = isaSym "bottom";

val symAnd : string = isaSym "and";

val symAll : string = isaSym "forall";

fun showFm (Atom (p, [])) = p
  | showFm (Atom (p, v :: va)) =
    p ^ "(" ^ sepBy "," (map showTrm (v :: va)) ^ ")"
  | showFm (Eqf (s, t)) = showTrm s ^ " = " ^ showTrm t
  | showFm Bot = symBot
  | showFm (Neg Bot) = isaSym "top"
  | showFm (Neg (Atom (v, va))) = symNot ^ showFm (Atom (v, va))
  | showFm (Neg (Eqf (v, va))) = symNot ^ showFm (Eqf (v, va))
  | showFm (Neg (Neg v)) = symNot ^ showFm (Neg v)
  | showFm (Neg (Conj (v, va))) = symNot ^ showFm (Conj (v, va))
  | showFm (Neg (Disj (v, va))) = symNot ^ showFm (Disj (v, va))
  | showFm (Neg (Impl (v, va))) = symNot ^ showFm (Impl (v, va))
  | showFm (Neg (Iff (v, va))) = symNot ^ showFm (Iff (v, va))
  | showFm (Neg (Uni (v, va))) = symNot ^ showFm (Uni (v, va))
  | showFm (Neg (Exi (v, va))) = symNot ^ showFm (Exi (v, va))
  | showFm (Conj (p, q)) = "(" ^ showFm p ^ " " ^ symAnd ^ " " ^ showFm q ^ ")"
  | showFm (Disj (p, q)) = "(" ^ showFm p ^ " " ^ symOr ^ " " ^ showFm q ^ ")"
  | showFm (Impl (p, q)) = "(" ^ showFm p ^ " " ^ symImp ^ " " ^ showFm q ^ ")"
  | showFm (Iff (p, q)) = "(" ^ showFm p ^ " " ^ symIff ^ " " ^ showFm q ^ ")"
  | showFm (Uni (x, p)) = symAll ^ x ^ ". " ^ showFm p
  | showFm (Exi (x, p)) = symEx ^ x ^ ". " ^ showFm p;

fun toLemmonRule FPremise = Assumption
  | toLemmonRule FAssume = Assumption
  | toLemmonRule (FMP (i, j)) = MP (i, j)
  | toLemmonRule (FCP (a, c)) = CP (a, c)
  | toLemmonRule (FRAA (a, c)) = RAA (a, c)
  | toLemmonRule (FDN i) = DN i
  | toLemmonRule (FBotI (i, j)) = BotI (i, j)
  | toLemmonRule (FAndIntro (i, j)) = AndIntro (i, j)
  | toLemmonRule (FAndElimL i) = AndElimL i
  | toLemmonRule (FAndElimR i) = AndElimR i
  | toLemmonRule (FOrIntroL i) = OrIntroL i
  | toLemmonRule (FOrIntroR i) = OrIntroR i
  | toLemmonRule (FOrElim (d, (a1, c1), (a2, c2))) = OrElim (d, a1, c1, a2, c2)
  | toLemmonRule (FIffIntro (i, j)) = IffIntro (i, j)
  | toLemmonRule (FIffElimL i) = IffElimL i
  | toLemmonRule (FIffElimR i) = IffElimR i
  | toLemmonRule (FForallElim i) = ForallElim i
  | toLemmonRule (FForallIntro i) = ForallIntro i
  | toLemmonRule (FExistsIntro i) = ExistsIntro i
  | toLemmonRule (FExistsElim (m, (a, c))) = ExistsElim (m, a, c)
  | toLemmonRule FEqIntro = EqIntro
  | toLemmonRule (FEqElim (i, j)) = EqElim (i, j)
  | toLemmonRule (FReit i) = Reit i;

fun flFm (FL (x1, x2, x3, x4)) = x2;

fun deltaAux acc [] = acc
  | deltaAux acc (fl :: fls) =
    deltaAux
      (acc @
        [ProofLine
           (flNum fl, flFm fl, toLemmonRule (flRule fl),
             depsOf (depsAt acc) (toLemmonRule (flRule fl)) (flNum fl))])
      fls;

fun delta f = deltaAux [] (flatten f);

fun scopeSrc f e n g = depFms e (scopeOf f n);

fun dischargePairs (CP (a, c)) = [(a, c)]
  | dischargePairs (RAA (a, c)) = [(a, c)]
  | dischargePairs (OrElim (d, a1, c1, a2, c2)) = [(a1, c1), (a2, c2)]
  | dischargePairs (ExistsElim (m, a, c)) = [(a, c)]
  | dischargePairs Assumption = []
  | dischargePairs (MP (v, va)) = []
  | dischargePairs (DN v) = []
  | dischargePairs (BotI (v, va)) = []
  | dischargePairs (AndIntro (v, va)) = []
  | dischargePairs (AndElimL v) = []
  | dischargePairs (AndElimR v) = []
  | dischargePairs (OrIntroL v) = []
  | dischargePairs (OrIntroR v) = []
  | dischargePairs (IffIntro (v, va)) = []
  | dischargePairs (IffElimL v) = []
  | dischargePairs (IffElimR v) = []
  | dischargePairs (ForallElim v) = []
  | dischargePairs (ForallIntro v) = []
  | dischargePairs (ExistsIntro v) = []
  | dischargePairs EqIntro = []
  | dischargePairs (EqElim (v, va)) = []
  | dischargePairs (Reit v) = [];

fun boxesOf p = maps (fn l => dischargePairs (justification l)) p;

fun boxPath p m =
  sort_key linorder_nat (fn x => x)
    (map_filter
      (fn x =>
        (if less_eq_nat (fst x) m andalso less_eq_nat m (snd x)
          then SOME (fst x) else NONE))
      (boxesOf p));

fun maxlen used = foldr (fn a => fn n => max ord_nat n (nlen a)) used zero_nat;

fun apsnd f (x, y) = (x, f y);

fun divmod_integer k l =
  (if ((k : IntInf.int) = (0 : IntInf.int))
    then ((0 : IntInf.int), (0 : IntInf.int))
    else (if IntInf.< ((0 : IntInf.int), l)
           then (if IntInf.< ((0 : IntInf.int), k)
                  then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                  else let
                         val (r, s) =
                           IntInf.divMod (IntInf.abs k, IntInf.abs l);
                       in
                         (if ((s : IntInf.int) = (0 : IntInf.int))
                           then (IntInf.~ r, (0 : IntInf.int))
                           else (IntInf.- (IntInf.~ r, (1 : IntInf.int)),
                                  IntInf.- (l, s)))
                       end)
           else (if ((l : IntInf.int) = (0 : IntInf.int))
                  then ((0 : IntInf.int), k)
                  else apsnd IntInf.~
                         (if IntInf.< (k, (0 : IntInf.int))
                           then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                           else let
                                  val (r, s) =
                                    IntInf.divMod (IntInf.abs k, IntInf.abs l);
                                in
                                  (if ((s : IntInf.int) = (0 : IntInf.int))
                                    then (IntInf.~ r, (0 : IntInf.int))
                                    else (IntInf.- (IntInf.~
              r, (1 : IntInf.int)),
   IntInf.- (IntInf.~ l, s)))
                                end))));

fun modulo_integer k l = snd (divmod_integer k l);

fun modulo_nat m n = Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));

fun divide_integer k l = fst (divmod_integer k l);

fun divide_nat m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));

fun char_of_nat x = (char_of_integer o integer_of_nat) x;

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

fun digitsAux v =
  (if equal_nata v zero_nat then []
    else digitsAux
           (divide_nat (suc (minus_nat v one_nat))
             (nat_of_integer (10 : IntInf.int))) @
           [char_of_nat
              (plus_nat (nat_of_integer (48 : IntInf.int))
                (modulo_nat (suc (minus_nat v one_nat))
                  (nat_of_integer (10 : IntInf.int))))]);

fun showNat n = (if equal_nata n zero_nat then "0" else implode (digitsAux n));

fun premEnv d =
  map (fn ke => (fst (snd ke), (suc (fst ke), snd (snd ke))))
    (enumerate zero_nat
      (sort_key linorder_nat fst
        (remdups (equal_prod equal_nat equal_fm) (openAsms d))));

fun dischargedAssumps p = map fst (boxesOf p);

fun unfoldD k p n =
  (if equal_nata k zero_nat then NONE
    else (case lookupLine p n of NONE => NONE
           | SOME l =>
             (case justification l
               of Assumption =>
                 SOME (Deriv
                        (formula l,
                          (if membera equal_nat (dischargedAssumps p) n
                            then DAssume n else DPremise n)))
               | MP (i, j) =>
                 (case (unfoldD (minus_nat k one_nat) p i,
                         unfoldD (minus_nat k one_nat) p j)
                   of (NONE, _) => NONE | (SOME _, NONE) => NONE
                   | (SOME e0, SOME e1) =>
                     SOME (Deriv (formula l, DMP (e0, e1))))
               | CP (a, c) =>
                 (case (fmAt p a, unfoldD (minus_nat k one_nat) p c)
                   of (NONE, _) => NONE | (SOME _, NONE) => NONE
                   | (SOME g0, SOME e1) =>
                     SOME (Deriv (formula l, DCP (a, g0, e1))))
               | RAA (a, c) =>
                 (case (fmAt p a, unfoldD (minus_nat k one_nat) p c)
                   of (NONE, _) => NONE | (SOME _, NONE) => NONE
                   | (SOME g0, SOME e1) =>
                     SOME (Deriv (formula l, DRAA (a, g0, e1))))
               | DN i =>
                 (case unfoldD (minus_nat k one_nat) p i of NONE => NONE
                   | SOME e0 => SOME (Deriv (formula l, DDN e0)))
               | BotI (i, j) =>
                 (case (unfoldD (minus_nat k one_nat) p i,
                         unfoldD (minus_nat k one_nat) p j)
                   of (NONE, _) => NONE | (SOME _, NONE) => NONE
                   | (SOME e0, SOME e1) =>
                     SOME (Deriv (formula l, DBotI (e0, e1))))
               | AndIntro (i, j) =>
                 (case (unfoldD (minus_nat k one_nat) p i,
                         unfoldD (minus_nat k one_nat) p j)
                   of (NONE, _) => NONE | (SOME _, NONE) => NONE
                   | (SOME e0, SOME e1) =>
                     SOME (Deriv (formula l, DAndIntro (e0, e1))))
               | AndElimL i =>
                 (case unfoldD (minus_nat k one_nat) p i of NONE => NONE
                   | SOME e0 => SOME (Deriv (formula l, DAndElimL e0)))
               | AndElimR i =>
                 (case unfoldD (minus_nat k one_nat) p i of NONE => NONE
                   | SOME e0 => SOME (Deriv (formula l, DAndElimR e0)))
               | OrIntroL i =>
                 (case unfoldD (minus_nat k one_nat) p i of NONE => NONE
                   | SOME e0 => SOME (Deriv (formula l, DOrIntroL e0)))
               | OrIntroR i =>
                 (case unfoldD (minus_nat k one_nat) p i of NONE => NONE
                   | SOME e0 => SOME (Deriv (formula l, DOrIntroR e0)))
               | OrElim (d, a1, c1, a2, c2) =>
                 (case (unfoldD (minus_nat k one_nat) p d,
                         (fmAt p a1,
                           (unfoldD (minus_nat k one_nat) p c1,
                             (fmAt p a2, unfoldD (minus_nat k one_nat) p c2))))
                   of (NONE, _) => NONE | (SOME _, (NONE, _)) => NONE
                   | (SOME _, (SOME _, (NONE, _))) => NONE
                   | (SOME _, (SOME _, (SOME _, (NONE, _)))) => NONE
                   | (SOME _, (SOME _, (SOME _, (SOME _, NONE)))) => NONE
                   | (SOME e0, (SOME g1, (SOME e2, (SOME g3, SOME e4)))) =>
                     SOME (Deriv
                            (formula l, DOrElim (e0, a1, g1, e2, a2, g3, e4))))
               | IffIntro (i, j) =>
                 (case (unfoldD (minus_nat k one_nat) p i,
                         unfoldD (minus_nat k one_nat) p j)
                   of (NONE, _) => NONE | (SOME _, NONE) => NONE
                   | (SOME e0, SOME e1) =>
                     SOME (Deriv (formula l, DIffIntro (e0, e1))))
               | IffElimL i =>
                 (case unfoldD (minus_nat k one_nat) p i of NONE => NONE
                   | SOME e0 => SOME (Deriv (formula l, DIffElimL e0)))
               | IffElimR i =>
                 (case unfoldD (minus_nat k one_nat) p i of NONE => NONE
                   | SOME e0 => SOME (Deriv (formula l, DIffElimR e0)))
               | ForallElim i =>
                 (case unfoldD (minus_nat k one_nat) p i of NONE => NONE
                   | SOME e0 => SOME (Deriv (formula l, DForallElim e0)))
               | ForallIntro i =>
                 (case unfoldD (minus_nat k one_nat) p i of NONE => NONE
                   | SOME e0 => SOME (Deriv (formula l, DForallIntro e0)))
               | ExistsIntro i =>
                 (case unfoldD (minus_nat k one_nat) p i of NONE => NONE
                   | SOME e0 => SOME (Deriv (formula l, DExistsIntro e0)))
               | ExistsElim (m, a, c) =>
                 (case (unfoldD (minus_nat k one_nat) p m,
                         (fmAt p a, unfoldD (minus_nat k one_nat) p c))
                   of (NONE, _) => NONE | (SOME _, (NONE, _)) => NONE
                   | (SOME _, (SOME _, NONE)) => NONE
                   | (SOME e0, (SOME g1, SOME e2)) =>
                     SOME (Deriv (formula l, DExistsElim (e0, a, g1, e2))))
               | EqIntro => SOME (Deriv (formula l, DEqIntro))
               | EqElim (i, j) =>
                 (case (unfoldD (minus_nat k one_nat) p i,
                         unfoldD (minus_nat k one_nat) p j)
                   of (NONE, _) => NONE | (SOME _, NONE) => NONE
                   | (SOME e0, SOME e1) =>
                     SOME (Deriv (formula l, DEqElim (e0, e1))))
               | Reit i =>
                 (case unfoldD (minus_nat k one_nat) p i of NONE => NONE
                   | SOME e0 => SOME (Deriv (formula l, DReit e0))))));

fun ruleFms (DAssume k1) = []
  | ruleFms (DPremise k1) = []
  | ruleFms (DMP (d1, d2)) = []
  | ruleFms (DCP (k1, g1, d1)) = [g1]
  | ruleFms (DRAA (k1, g1, d1)) = [g1]
  | ruleFms (DDN d1) = []
  | ruleFms (DBotI (d1, d2)) = []
  | ruleFms (DAndIntro (d1, d2)) = []
  | ruleFms (DAndElimL d1) = []
  | ruleFms (DAndElimR d1) = []
  | ruleFms (DOrIntroL d1) = []
  | ruleFms (DOrIntroR d1) = []
  | ruleFms (DOrElim (d1, k1, g1, d2, k2, g2, d3)) = [g1, g2]
  | ruleFms (DIffIntro (d1, d2)) = []
  | ruleFms (DIffElimL d1) = []
  | ruleFms (DIffElimR d1) = []
  | ruleFms (DForallElim d1) = []
  | ruleFms (DForallIntro d1) = []
  | ruleFms (DExistsIntro d1) = []
  | ruleFms (DExistsElim (d1, k1, g1, d2)) = [g1]
  | ruleFms DEqIntro = []
  | ruleFms (DEqElim (d1, d2)) = []
  | ruleFms (DReit d1) = [];

fun namesD (Deriv (phi, r)) =
  names phi @ maps names (ruleFms r) @ maps namesD (subDerivs r);

fun premLines g = map (fn e => FLine (fst (snd e), snd (snd e), FPremise)) g;

fun derivationToFitch d =
  let
    val g = premEnv d;
    val base = suc (maxlen (namesD d));
    val (items, (_, (_, _))) = emit base g (suc (size_lista g)) zero_nat d;
  in
    premLines g @ items
  end;

fun lineOK_gen a e l =
  let
    val g = depsOf (depsAt e) (justification l) (lineNumber l);
  in
    equal_set equal_nat (references l) g andalso
      (list_all (fn m => not (is_none (lookupLine e m)))
         (citedLines (justification l)) andalso
        ruleOK e (formula l) (a e (lineNumber l) g) (justification l))
  end;

fun checkFrom_gen a e [] = true
  | checkFrom_gen a e (l :: ls) =
    lineOK_gen a e l andalso checkFrom_gen a (e @ [l]) ls;

fun lemmonCorrect p =
  sorted_wrt less_nat (map lineNumber p) andalso checkFrom_gen depSrc [] p;

fun rootLine p = (if null p then zero_nat else lineNumber (last p));

fun toDerivation p =
  (if null p orelse not (lemmonCorrect p) then Inl (NotCorrect zero_nat)
    else (case unfoldD (suc (rootLine p)) p (rootLine p)
           of NONE => Inl (NotCorrect (rootLine p)) | SOME a => Inr a));

fun viaTree p =
  (case toDerivation p of Inl a => Inl a
    | Inr d => Inr (ViaTree, derivationToFitch d));

fun recomputeAux acc [] = acc
  | recomputeAux acc ((n, (f, j)) :: ls) =
    recomputeAux (acc @ [ProofLine (n, f, j, depsOf (depsAt acc) j n)]) ls;

fun recompute x = recomputeAux [] x;

fun stripDeps p = map (fn l => (lineNumber l, (formula l, justification l))) p;

fun subLevel p ac = removeAll equal_nat (fst ac) (boxPath p (fst ac));

fun hlIsPropositional (HL_Predicate (p, ts)) = null ts
  | hlIsPropositional (HL_Boolean b) = true
  | hlIsPropositional (HL_Not p) = hlIsPropositional p
  | hlIsPropositional (HL_And (p, q)) =
    hlIsPropositional p andalso hlIsPropositional q
  | hlIsPropositional (HL_Or (p, q)) =
    hlIsPropositional p andalso hlIsPropositional q
  | hlIsPropositional (HL_Implies (p, q)) =
    hlIsPropositional p andalso hlIsPropositional q
  | hlIsPropositional (HL_Iff (p, q)) =
    hlIsPropositional p andalso hlIsPropositional q
  | hlIsPropositional (HL_ForAll (x, p)) = false
  | hlIsPropositional (HL_Exists (x, p)) = false;

fun hlLiteralFormula (p, true) = HL_Predicate (p, [])
  | hlLiteralFormula (p, false) = HL_Not (HL_Predicate (p, []));

fun hlDisjoin ps =
  (case ps of [] => HL_Boolean false
    | a :: b => foldl (fn aa => fn ba => HL_Or (aa, ba)) a b);

fun hlConjoin ps =
  (case ps of [] => HL_Boolean true
    | a :: b => foldl (fn aa => fn ba => HL_And (aa, ba)) a b);

fun hlClausesFormula clauses =
  hlDisjoin (map (hlConjoin o map hlLiteralFormula) clauses);

fun hlDNFClauses (HL_Boolean true) = SOME [[]]
  | hlDNFClauses (HL_Boolean false) = SOME []
  | hlDNFClauses (HL_Or (p, q)) =
    (case (hlDNFClauses p, hlDNFClauses q) of (NONE, _) => NONE
      | (SOME _, NONE) => NONE | (SOME ps, SOME qs) => SOME (ps @ qs))
  | hlDNFClauses (HL_And (p, q)) =
    (case (hlDNFClauses p, hlDNFClauses q) of (NONE, _) => NONE
      | (SOME _, NONE) => NONE
      | (SOME ps, SOME qs) => SOME (maps (fn r => map (fn a => r @ a) qs) ps))
  | hlDNFClauses (HL_Predicate (p, [])) = SOME [[(p, true)]]
  | hlDNFClauses (HL_Not (HL_Predicate (p, []))) = SOME [[(p, false)]]
  | hlDNFClauses (HL_Predicate (v, vb :: vc)) = NONE
  | hlDNFClauses (HL_Not (HL_Predicate (va, vc :: vd))) = NONE
  | hlDNFClauses (HL_Not (HL_Boolean va)) = NONE
  | hlDNFClauses (HL_Not (HL_Not va)) = NONE
  | hlDNFClauses (HL_Not (HL_And (va, vb))) = NONE
  | hlDNFClauses (HL_Not (HL_Or (va, vb))) = NONE
  | hlDNFClauses (HL_Not (HL_Implies (va, vb))) = NONE
  | hlDNFClauses (HL_Not (HL_Iff (va, vb))) = NONE
  | hlDNFClauses (HL_Not (HL_ForAll (va, vb))) = NONE
  | hlDNFClauses (HL_Not (HL_Exists (va, vb))) = NONE
  | hlDNFClauses (HL_Implies (v, va)) = NONE
  | hlDNFClauses (HL_Iff (v, va)) = NONE
  | hlDNFClauses (HL_ForAll (v, va)) = NONE
  | hlDNFClauses (HL_Exists (v, va)) = NONE;

fun hlEliminateImplications (HL_Predicate (p, ts)) = HL_Predicate (p, ts)
  | hlEliminateImplications (HL_Boolean b) = HL_Boolean b
  | hlEliminateImplications (HL_Not p) = HL_Not (hlEliminateImplications p)
  | hlEliminateImplications (HL_And (p, q)) =
    HL_And (hlEliminateImplications p, hlEliminateImplications q)
  | hlEliminateImplications (HL_Or (p, q)) =
    HL_Or (hlEliminateImplications p, hlEliminateImplications q)
  | hlEliminateImplications (HL_Implies (p, q)) =
    HL_Or (HL_Not (hlEliminateImplications p), hlEliminateImplications q)
  | hlEliminateImplications (HL_Iff (p, q)) =
    let
      val pa = hlEliminateImplications p;
      val qa = hlEliminateImplications q;
    in
      HL_And (HL_Or (HL_Not pa, qa), HL_Or (HL_Not qa, pa))
    end
  | hlEliminateImplications (HL_ForAll (x, p)) =
    HL_ForAll (x, hlEliminateImplications p)
  | hlEliminateImplications (HL_Exists (x, p)) =
    HL_Exists (x, hlEliminateImplications p);

fun hlPushNegations (HL_Not (HL_Not p)) = hlPushNegations p
  | hlPushNegations (HL_Not (HL_And (p, q))) =
    HL_Or (hlPushNegations (HL_Not p), hlPushNegations (HL_Not q))
  | hlPushNegations (HL_Not (HL_Or (p, q))) =
    HL_And (hlPushNegations (HL_Not p), hlPushNegations (HL_Not q))
  | hlPushNegations (HL_Not (HL_Boolean b)) = HL_Boolean (not b)
  | hlPushNegations (HL_Not (HL_ForAll (x, p))) =
    HL_Exists (x, hlPushNegations (HL_Not p))
  | hlPushNegations (HL_Not (HL_Exists (x, p))) =
    HL_ForAll (x, hlPushNegations (HL_Not p))
  | hlPushNegations (HL_Not (HL_Predicate (v, va))) =
    HL_Not (HL_Predicate (v, va))
  | hlPushNegations (HL_Not (HL_Implies (v, va))) = HL_Not (HL_Implies (v, va))
  | hlPushNegations (HL_Not (HL_Iff (v, va))) = HL_Not (HL_Iff (v, va))
  | hlPushNegations (HL_And (p, q)) =
    HL_And (hlPushNegations p, hlPushNegations q)
  | hlPushNegations (HL_Or (p, q)) =
    HL_Or (hlPushNegations p, hlPushNegations q)
  | hlPushNegations (HL_ForAll (x, p)) = HL_ForAll (x, hlPushNegations p)
  | hlPushNegations (HL_Exists (x, p)) = HL_Exists (x, hlPushNegations p)
  | hlPushNegations (HL_Predicate (v, va)) = HL_Predicate (v, va)
  | hlPushNegations (HL_Boolean v) = HL_Boolean v
  | hlPushNegations (HL_Implies (v, va)) = HL_Implies (v, va)
  | hlPushNegations (HL_Iff (v, va)) = HL_Iff (v, va);

fun hlToNNF p = hlPushNegations (hlEliminateImplications p);

fun hlToDNF p =
  (if hlIsPropositional p
    then map_option hlClausesFormula (hlDNFClauses (hlToNNF p)) else NONE);

fun showNats ns = sepBy "," (map showNat ns);

fun showDeps g = showNats (sorted_list_of_set (equal_nat, linorder_nat) g);

fun showJust Assumption = "A"
  | showJust (MP (i, j)) = showNats [i, j] ^ " MP"
  | showJust (CP (a, c)) = showNats [a, c] ^ " CP"
  | showJust (RAA (a, c)) = showNats [a, c] ^ " RAA"
  | showJust (DN i) = showNat i ^ " DN"
  | showJust (BotI (i, j)) = showNats [i, j] ^ " " ^ symBot ^ "I"
  | showJust (AndIntro (i, j)) = showNats [i, j] ^ " " ^ symAnd ^ "I"
  | showJust (AndElimL i) = showNat i ^ " " ^ symAnd ^ "E"
  | showJust (AndElimR i) = showNat i ^ " " ^ symAnd ^ "E"
  | showJust (OrIntroL i) = showNat i ^ " " ^ symOr ^ "I"
  | showJust (OrIntroR i) = showNat i ^ " " ^ symOr ^ "I"
  | showJust (OrElim (d, a1, c1, a2, c2)) =
    showNats [d, a1, c1, a2, c2] ^ " " ^ symOr ^ "E"
  | showJust (IffIntro (i, j)) = showNats [i, j] ^ " " ^ symIff ^ "I"
  | showJust (IffElimL i) = showNat i ^ " " ^ symIff ^ "E"
  | showJust (IffElimR i) = showNat i ^ " " ^ symIff ^ "E"
  | showJust (ForallElim i) = showNat i ^ " " ^ symAll ^ "E"
  | showJust (ForallIntro i) = showNat i ^ " " ^ symAll ^ "I"
  | showJust (ExistsIntro i) = showNat i ^ " " ^ symEx ^ "I"
  | showJust (ExistsElim (m, a, c)) = showNats [m, a, c] ^ " " ^ symEx ^ "E"
  | showJust EqIntro = "=I"
  | showJust (EqElim (i, j)) = showNats [i, j] ^ " =E"
  | showJust (Reit i) = showNat i ^ " R";

fun firstDiff [] ys = zero_nat
  | firstDiff (x :: xs) [] = x
  | firstDiff (x :: xs) (y :: ys) =
    (if equal_nata x y then firstDiff xs ys else x);

fun hlConclusion p = (if null p then NONE else SOME (hlFormula (last p)));

fun showError (NotNested (n, a, bs)) =
  "line " ^ showNat n ^ " discharges " ^ showNat a ^
    " while the box(es) opened at " ^
    showNats bs ^
    " are still open"
  | showError (OutOfScope (n, m, b)) =
    "line " ^ showNat n ^ " cites " ^ showNat m ^ ", which the box opened at " ^
      showNat b ^
      " has closed over"
  | showError (PremiseInBox (n, b)) =
    "premise " ^ showNat n ^ " is written inside the box opened at " ^ showNat b
  | showError (PremiseLate (n, m)) =
    "premise " ^ showNat n ^ " is written after line " ^ showNat m ^
      ", which is not a premise"
  | showError (BoxReversed (a, c)) =
    "the assumption at line " ^ showNat a ^ " is discharged from line " ^
      showNat c ^
      ", which precedes it"
  | showError (AssumptionReused (a, ca, c)) =
    "the assumption at line " ^ showNat a ^ " is discharged both at line " ^
      showNat ca ^
      " and at line " ^
      showNat c ^
      ", so two subproofs would have to open together"
  | showError (NotCorrect n) =
    "the source is not a correct Lemmon proof (line " ^ showNat n ^ ")";

fun showFRule FPremise = "Premise"
  | showFRule FAssume = "Assume"
  | showFRule (FMP (i, j)) = "MP " ^ showNats [i, j]
  | showFRule (FCP (a, c)) = "CP " ^ showNat a ^ "-" ^ showNat c
  | showFRule (FRAA (a, c)) = "RAA " ^ showNat a ^ "-" ^ showNat c
  | showFRule (FDN i) = "DN " ^ showNat i
  | showFRule (FBotI (i, j)) = symBot ^ "I " ^ showNats [i, j]
  | showFRule (FAndIntro (i, j)) = symAnd ^ "I " ^ showNats [i, j]
  | showFRule (FAndElimL i) = symAnd ^ "E " ^ showNat i
  | showFRule (FAndElimR i) = symAnd ^ "E " ^ showNat i
  | showFRule (FOrIntroL i) = symOr ^ "I " ^ showNat i
  | showFRule (FOrIntroR i) = symOr ^ "I " ^ showNat i
  | showFRule (FOrElim (d, (a1, c1), (a2, c2))) =
    symOr ^ "E " ^ showNat d ^ ", " ^ showNat a1 ^ "-" ^ showNat c1 ^ ", " ^
      showNat a2 ^
      "-" ^
      showNat c2
  | showFRule (FIffIntro (i, j)) = symIff ^ "I " ^ showNats [i, j]
  | showFRule (FIffElimL i) = symIff ^ "E " ^ showNat i
  | showFRule (FIffElimR i) = symIff ^ "E " ^ showNat i
  | showFRule (FForallElim i) = symAll ^ "E " ^ showNat i
  | showFRule (FForallIntro i) = symAll ^ "I " ^ showNat i
  | showFRule (FExistsIntro i) = symEx ^ "I " ^ showNat i
  | showFRule (FExistsElim (m, (a, c))) =
    symEx ^ "E " ^ showNat m ^ ", " ^ showNat a ^ "-" ^ showNat c
  | showFRule FEqIntro = "=I"
  | showFRule (FEqElim (i, j)) = "=E " ^ showNats [i, j]
  | showFRule (FReit i) = "R " ^ showNat i;

fun showFitchLine fl =
  padTo (nat_of_integer (5 : IntInf.int)) (showNat (flNum fl)) ^
    padTo (nat_of_integer (36 : IntInf.int))
      (cat (replicate (size_lista (flScope fl)) "| ") ^ showFm (flFm fl)) ^
    showFRule (flRule fl);

fun showFitch f = map showFitchLine (flatten f);

fun showRoute Direct = "-- positional"
  | showRoute ViaTree = "-- via a derivation tree";

fun size_list x [] = zero_nat
  | size_list x (x21 :: x22) =
    plus_nat (plus_nat (x x21) (size_list x x22)) (suc zero_nat);

fun toFitchRule Assumption = FPremise
  | toFitchRule (MP (i, j)) = FMP (i, j)
  | toFitchRule (CP (a, c)) = FCP (a, c)
  | toFitchRule (RAA (a, c)) = FRAA (a, c)
  | toFitchRule (DN i) = FDN i
  | toFitchRule (BotI (i, j)) = FBotI (i, j)
  | toFitchRule (AndIntro (i, j)) = FAndIntro (i, j)
  | toFitchRule (AndElimL i) = FAndElimL i
  | toFitchRule (AndElimR i) = FAndElimR i
  | toFitchRule (OrIntroL i) = FOrIntroL i
  | toFitchRule (OrIntroR i) = FOrIntroR i
  | toFitchRule (OrElim (d, a1, c1, a2, c2)) = FOrElim (d, (a1, c1), (a2, c2))
  | toFitchRule (IffIntro (i, j)) = FIffIntro (i, j)
  | toFitchRule (IffElimL i) = FIffElimL i
  | toFitchRule (IffElimR i) = FIffElimR i
  | toFitchRule (ForallElim i) = FForallElim i
  | toFitchRule (ForallIntro i) = FForallIntro i
  | toFitchRule (ExistsIntro i) = FExistsIntro i
  | toFitchRule (ExistsElim (m, a, c)) = FExistsElim (m, (a, c))
  | toFitchRule EqIntro = FEqIntro
  | toFitchRule (EqElim (i, j)) = FEqElim (i, j)
  | toFitchRule (Reit i) = FReit i;

fun buildItems boxes [] = []
  | buildItems boxes (l :: ls) =
    (case find (fn ac => equal_nata (fst ac) (lineNumber l)) boxes
      of NONE =>
        FLine (lineNumber l, formula l, toFitchRule (justification l)) ::
          buildItems boxes ls
      | SOME ac =>
        FSub (Subproof
               (lineNumber l, formula l,
                 buildItems boxes
                   (takeWhile (fn la => less_eq_nat (lineNumber la) (snd ac))
                     ls))) ::
          buildItems boxes
            (dropWhile (fn la => less_eq_nat (lineNumber la) (snd ac)) ls));

fun badCitations p =
  maps (fn l =>
         map_filter
           (fn x =>
             (if not (is_prefix equal_nat (boxPath p x)
                       (boxPath p (lineNumber l)))
               then SOME (lineNumber l, x) else NONE))
           (fCitedLines (toFitchRule (justification l))))
    p;

fun scopeError p =
  (case badCitations p of [] => NONE
    | (n, m) :: _ =>
      SOME (OutOfScope (n, m, firstDiff (boxPath p m) (boxPath p n))));

fun showLemmonLine l =
  padTo (nat_of_integer (10 : IntInf.int)) (showDeps (references l)) ^
    padTo (nat_of_integer (6 : IntInf.int))
      ("(" ^ showNat (lineNumber l) ^ ")") ^
    padTo (nat_of_integer (32 : IntInf.int)) (showFm (formula l)) ^
    showJust (justification l);

fun showLemmon p = map showLemmonLine p;

fun fitchCorrect f = fitchWF f andalso checkFrom_gen (scopeSrc f) [] (delta f);

fun overlapping ac b =
  less_nat (fst ac) (fst b) andalso
    (less_eq_nat (fst b) (snd ac) andalso less_nat (snd ac) (snd b));

fun hlOpenPremises p =
  (if null p then []
    else map_filter
           (fn x =>
             (if member equal_int (hlLineNumber x)
                   (hlReferences (last p)) andalso
                   equal_hl_justification (hlJustification x) HL_Assumption
               then SOME (hlFormula x) else NONE))
           p);

fun fitchToLemmon f = delta f;

fun boxHeadError p =
  (case filtera
          (fn x =>
            equal_nata (fst (fst x)) (fst (snd x)) andalso
              not (equal_nata (snd (fst x)) (snd (snd x))))
          (product (boxesOf p) (boxesOf p))
    of [] => NONE
    | x :: _ =>
      SOME (AssumptionReused (fst (fst x), snd (fst x), snd (snd x))));

fun dischargerOf p ac =
  (case find (fn l =>
               membera (equal_prod equal_nat equal_nat)
                 (dischargePairs (justification l)) ac)
          p
    of NONE => zero_nat | SOME a => lineNumber a);

fun nestingError p =
  (case filtera (fn ac => list_ex (overlapping ac) (boxesOf p)) (boxesOf p)
    of [] => NONE
    | ac :: _ =>
      SOME (NotNested
             (dischargerOf p ac, fst ac,
               map_filter
                 (fn x => (if overlapping ac x then SOME (fst x) else NONE))
                 (boxesOf p))));

fun premiseError p =
  (case filtera
          (fn l =>
            equal_justa (justification l) Assumption andalso
              (not (membera equal_nat (dischargedAssumps p)
                     (lineNumber l)) andalso
                not (null (boxPath p (lineNumber l)))))
          p
    of [] => NONE
    | l :: _ =>
      SOME (PremiseInBox (lineNumber l, last (boxPath p (lineNumber l)))));

fun hlRuleOKG src p l =
  let
    val phi = hlFormula l;
    val g = hlReferences l;
  in
    (case hlJustification l
      of HL_Assumption =>
        equal_set equal_int g (insert equal_int (hlLineNumber l) bot_set)
      | HL_MP (m, n) =>
        (case (hlLookupLine p m, hlLookupLine p n) of (NONE, _) => false
          | (SOME _, NONE) => false
          | (SOME lm, SOME ln) =>
            (case hlFormula lm of HL_Predicate (_, _) => false
              | HL_Boolean _ => false | HL_Not _ => false
              | HL_And (_, _) => false | HL_Or (_, _) => false
              | HL_Implies (pa, q) =>
                equal_hl_formulaa (hlFormula ln) pa andalso
                  (equal_hl_formulaa phi q andalso
                    equal_set equal_int g
                      (sup_set equal_int (hlReferences lm) (hlReferences ln)))
              | HL_Iff (_, _) => false | HL_ForAll (_, _) => false
              | HL_Exists (_, _) => false))
      | HL_MT (m, n) =>
        (case (hlLookupLine p m, (hlLookupLine p n, phi)) of (NONE, _) => false
          | (SOME _, (NONE, _)) => false
          | (SOME _, (SOME _, HL_Predicate (_, _))) => false
          | (SOME _, (SOME _, HL_Boolean _)) => false
          | (SOME lm, (SOME ln, HL_Not pa)) =>
            (case (hlFormula lm, hlFormula ln)
              of (HL_Predicate (_, _), _) => false | (HL_Boolean _, _) => false
              | (HL_Not _, _) => false | (HL_And (_, _), _) => false
              | (HL_Or (_, _), _) => false
              | (HL_Implies (_, _), HL_Predicate (_, _)) => false
              | (HL_Implies (_, _), HL_Boolean _) => false
              | (HL_Implies (q, r), HL_Not s) =>
                equal_hl_formulaa pa q andalso
                  (equal_hl_formulaa r s andalso
                    equal_set equal_int g
                      (sup_set equal_int (hlReferences lm) (hlReferences ln)))
              | (HL_Implies (_, _), HL_And (_, _)) => false
              | (HL_Implies (_, _), HL_Or (_, _)) => false
              | (HL_Implies (_, _), HL_Implies (_, _)) => false
              | (HL_Implies (_, _), HL_Iff (_, _)) => false
              | (HL_Implies (_, _), HL_ForAll (_, _)) => false
              | (HL_Implies (_, _), HL_Exists (_, _)) => false
              | (HL_Iff (_, _), _) => false | (HL_ForAll (_, _), _) => false
              | (HL_Exists (_, _), _) => false)
          | (SOME _, (SOME _, HL_And (_, _))) => false
          | (SOME _, (SOME _, HL_Or (_, _))) => false
          | (SOME _, (SOME _, HL_Implies (_, _))) => false
          | (SOME _, (SOME _, HL_Iff (_, _))) => false
          | (SOME _, (SOME _, HL_ForAll (_, _))) => false
          | (SOME _, (SOME _, HL_Exists (_, _))) => false)
      | HL_DN m =>
        (case hlLookupLine p m of NONE => false
          | SOME lm =>
            (equal_hl_formulaa (hlFormula lm) (HL_Not (HL_Not phi)) orelse
              equal_hl_formulaa phi (HL_Not (HL_Not (hlFormula lm)))) andalso
              equal_set equal_int g (hlReferences lm))
      | HL_CP (a, c) =>
        (case (hlLookupLine p a, hlLookupLine p c) of (NONE, _) => false
          | (SOME _, NONE) => false
          | (SOME la, SOME lc) =>
            equal_hl_justification (hlJustification la) HL_Assumption andalso
              (equal_hl_formulaa phi
                 (HL_Implies (hlFormula la, hlFormula lc)) andalso
                equal_set equal_int g
                  (remove equal_int (hlLineNumber la) (hlReferences lc))))
      | HL_AndIntro (m, n) =>
        (case (hlLookupLine p m, hlLookupLine p n) of (NONE, _) => false
          | (SOME _, NONE) => false
          | (SOME lm, SOME ln) =>
            (equal_hl_formulaa phi (HL_And (hlFormula lm, hlFormula ln)) orelse
              equal_hl_formulaa phi
                (HL_And (hlFormula ln, hlFormula lm))) andalso
              equal_set equal_int g
                (sup_set equal_int (hlReferences lm) (hlReferences ln)))
      | HL_AndElim m =>
        (case hlLookupLine p m of NONE => false
          | SOME lm =>
            (case hlFormula lm of HL_Predicate (_, _) => false
              | HL_Boolean _ => false | HL_Not _ => false
              | HL_And (pa, q) =>
                (equal_hl_formulaa phi pa orelse
                  equal_hl_formulaa phi q) andalso
                  equal_set equal_int g (hlReferences lm)
              | HL_Or (_, _) => false | HL_Implies (_, _) => false
              | HL_Iff (_, _) => false | HL_ForAll (_, _) => false
              | HL_Exists (_, _) => false))
      | HL_OrIntro m =>
        (case (hlLookupLine p m, phi) of (NONE, _) => false
          | (SOME _, HL_Predicate (_, _)) => false
          | (SOME _, HL_Boolean _) => false | (SOME _, HL_Not _) => false
          | (SOME _, HL_And (_, _)) => false
          | (SOME lm, HL_Or (pa, q)) =>
            (equal_hl_formulaa (hlFormula lm) pa orelse
              equal_hl_formulaa (hlFormula lm) q) andalso
              equal_set equal_int g (hlReferences lm)
          | (SOME _, HL_Implies (_, _)) => false
          | (SOME _, HL_Iff (_, _)) => false
          | (SOME _, HL_ForAll (_, _)) => false
          | (SOME _, HL_Exists (_, _)) => false)
      | HL_OrElim (d, a1, c1, a2, c2) =>
        (case (hlLookupLine p d,
                (hlLookupLine p a1,
                  (hlLookupLine p c1, (hlLookupLine p a2, hlLookupLine p c2))))
          of (NONE, _) => false | (SOME _, (NONE, _)) => false
          | (SOME _, (SOME _, (NONE, _))) => false
          | (SOME _, (SOME _, (SOME _, (NONE, _)))) => false
          | (SOME _, (SOME _, (SOME _, (SOME _, NONE)))) => false
          | (SOME ld, (SOME la1, (SOME lc1, (SOME la2, SOME lc2)))) =>
            equal_hl_justification (hlJustification la1) HL_Assumption andalso
              (equal_hl_justification (hlJustification la2)
                 HL_Assumption andalso
                (equal_hl_formulaa (hlFormula lc1) phi andalso
                  (equal_hl_formulaa (hlFormula lc2) phi andalso
                    ((case hlFormula ld of HL_Predicate (_, _) => false
                       | HL_Boolean _ => false | HL_Not _ => false
                       | HL_And (_, _) => false
                       | HL_Or (pa, q) =>
                         equal_hl_formulaa (hlFormula la1) pa andalso
                           equal_hl_formulaa (hlFormula la2) q orelse
                           equal_hl_formulaa (hlFormula la1) q andalso
                             equal_hl_formulaa (hlFormula la2) pa
                       | HL_Implies (_, _) => false | HL_Iff (_, _) => false
                       | HL_ForAll (_, _) => false
                       | HL_Exists (_, _) => false) andalso
                      equal_set equal_int g
                        (sup_set equal_int
                          (sup_set equal_int (hlReferences ld)
                            (remove equal_int (hlLineNumber la1)
                              (hlReferences lc1)))
                          (remove equal_int (hlLineNumber la2)
                            (hlReferences lc2))))))))
      | HL_RAA (a, c) =>
        (case (hlLookupLine p a, hlLookupLine p c) of (NONE, _) => false
          | (SOME _, NONE) => false
          | (SOME la, SOME lc) =>
            equal_hl_justification (hlJustification la) HL_Assumption andalso
              (equal_hl_formulaa phi (HL_Not (hlFormula la)) andalso
                (hlContradiction (hlFormula lc) andalso
                  equal_set equal_int g
                    (remove equal_int (hlLineNumber la) (hlReferences lc)))))
      | HL_ForallElim m =>
        (case hlLookupLine p m of NONE => false
          | SOME lm =>
            let
              val (sourceVars, sourceCore) = hlCollectForalls (hlFormula lm);
              val (targetVars, targetCore) = hlCollectForalls phi;
            in
              (case hlEliminationCount sourceVars targetVars of NONE => false
                | SOME k =>
                  not (is_none
                        (hlInferWitnessConstsK sourceVars sourceCore k
                          targetCore)) andalso
                    equal_set equal_int g (hlReferences lm))
            end)
      | HL_ExistsIntro m =>
        (case hlLookupLine p m of NONE => false
          | SOME lm =>
            let
              val (xs, core) = hlCollectExists phi;
            in
              not (null xs) andalso
                (list_ex
                   (fn k =>
                     not (is_none
                           (hlInferWitnessConstsK xs
                             (hlPrefixExists (drop k xs) core) k
                             (hlFormula lm))))
                   (upt zero_nat (suc (size_lista xs))) andalso
                  equal_set equal_int g (hlReferences lm))
            end)
      | HL_ForallIntro m =>
        (case hlLookupLine p m of NONE => false
          | SOME lm =>
            let
              val (xs, core) = hlCollectForalls phi;
            in
              not (null xs) andalso
                (case hlInferWitnessConstsK xs core (size_lista xs)
                        (hlFormula lm)
                  of NONE => false
                  | SOME cs =>
                    let
                      val pairs =
                        filtera (fn xc => not (((snd xc) : string) = ""))
                          (zip xs cs);
                    in
                      equal_option equal_hl_formula
                        (hlAbstractMany pairs (hlFormula lm))
                        (SOME core) andalso
                        (ball (image snd (Set pairs))
                           (fn c =>
                             not (member equal_literal c
                                   (hlAssumptionConstants p
                                     (src p (hlLineNumber l) g)))) andalso
                          equal_set equal_int g (hlReferences lm))
                    end)
            end)
      | HL_ExistsElim (m, a, c) =>
        (case (hlLookupLine p m, (hlLookupLine p a, hlLookupLine p c))
          of (NONE, _) => false | (SOME _, (NONE, _)) => false
          | (SOME _, (SOME _, NONE)) => false
          | (SOME lm, (SOME la, SOME lc)) =>
            let
              val (sourceVars, sourceCore) = hlCollectExists (hlFormula lm);
              val (targetVars, _) = hlCollectExists (hlFormula la);
              val delta = remove equal_int (hlLineNumber la) (hlReferences lc);
              val deltaSrc =
                remove equal_int (hlLineNumber la)
                  (src p (hlLineNumber lc) (hlReferences lc));
            in
              not (null sourceVars) andalso
                (equal_hl_justification (hlJustification la)
                   HL_Assumption andalso
                  (case hlEliminationCount sourceVars targetVars
                    of NONE => false
                    | SOME k =>
                      let
                        val template = hlPrefixExists targetVars sourceCore;
                      in
                        (case hlInferWitnessConstsK sourceVars template k
                                (hlFormula la)
                          of NONE => false
                          | SOME cs =>
                            let
                              val pairs =
                                filtera
                                  (fn xc => not (((snd xc) : string) = ""))
                                  (zip (take k sourceVars) cs);
                            in
                              equal_option equal_hl_formula
                                (hlAbstractMany pairs (hlFormula la))
                                (SOME template) andalso
                                (ball (image snd (Set pairs))
                                   (fn w =>
                                     not (member equal_literal w
   (hlConstantsInFormula (hlFormula lc))) andalso
                                       not
 (member equal_literal w (hlReferencedConstants p deltaSrc))) andalso
                                  (equal_hl_formulaa phi (hlFormula lc) andalso
                                    equal_set equal_int g
                                      (sup_set equal_int (hlReferences lm)
delta)))
                            end)
                      end))
            end)
      | HL_EqIntro =>
        (case phi of HL_Predicate (_, []) => false
          | HL_Predicate (_, HL_Var _ :: _) => false
          | HL_Predicate (_, [HL_Const _]) => false
          | HL_Predicate (_, HL_Const _ :: HL_Var _ :: _) => false
          | HL_Predicate (e, [HL_Const a, HL_Const b]) =>
            ((e : string) = "=") andalso
              (((a : string) = b) andalso equal_set equal_int g bot_set)
          | HL_Predicate (_, HL_Const _ :: HL_Const _ :: _ :: _) => false
          | HL_Boolean _ => false | HL_Not _ => false | HL_And (_, _) => false
          | HL_Or (_, _) => false | HL_Implies (_, _) => false
          | HL_Iff (_, _) => false | HL_ForAll (_, _) => false
          | HL_Exists (_, _) => false)
      | HL_EqElim (m, n) =>
        (case (hlLookupLine p m, hlLookupLine p n) of (NONE, _) => false
          | (SOME _, NONE) => false
          | (SOME lm, SOME ln) =>
            (case hlEqualityFormula (hlFormula ln) of NONE => false
              | SOME (HL_Var _, _) => false
              | SOME (HL_Const _, HL_Var _) => false
              | SOME (HL_Const a, HL_Const b) =>
                hlEqualUpToConstantReplacement a b (hlFormula lm) phi andalso
                  equal_set equal_int g
                    (sup_set equal_int (hlReferences lm) (hlReferences ln))))
      | HL_LEM => hlExcludedMiddle phi
      | HL_PropTaut ms =>
        list_all (fn m => not (is_none (hlLookupLine p m))) ms andalso
          (hlPropositionalConsequence (hlMapFilter (hlFormulaAt p) ms)
             phi andalso
            equal_set equal_int g (hlReferenceUnion p ms))
      | HL_IffIntro (m, n) =>
        (case (hlLookupLine p m, (hlLookupLine p n, phi)) of (NONE, _) => false
          | (SOME _, (NONE, _)) => false
          | (SOME _, (SOME _, HL_Predicate (_, _))) => false
          | (SOME _, (SOME _, HL_Boolean _)) => false
          | (SOME _, (SOME _, HL_Not _)) => false
          | (SOME _, (SOME _, HL_And (_, _))) => false
          | (SOME _, (SOME _, HL_Or (_, _))) => false
          | (SOME _, (SOME _, HL_Implies (_, _))) => false
          | (SOME lm, (SOME ln, HL_Iff (u, v))) =>
            (case (hlFormula lm, hlFormula ln)
              of (HL_Predicate (_, _), _) => false | (HL_Boolean _, _) => false
              | (HL_Not _, _) => false | (HL_And (_, _), _) => false
              | (HL_Or (_, _), _) => false
              | (HL_Implies (_, _), HL_Predicate (_, _)) => false
              | (HL_Implies (_, _), HL_Boolean _) => false
              | (HL_Implies (_, _), HL_Not _) => false
              | (HL_Implies (_, _), HL_And (_, _)) => false
              | (HL_Implies (_, _), HL_Or (_, _)) => false
              | (HL_Implies (pa, q), HL_Implies (r, s)) =>
                equal_hl_formulaa pa s andalso
                  (equal_hl_formulaa q r andalso
                    ((equal_hl_formulaa u pa andalso
                        equal_hl_formulaa v q orelse
                       equal_hl_formulaa u q andalso
                         equal_hl_formulaa v pa) andalso
                      equal_set equal_int g
                        (sup_set equal_int (hlReferences lm)
                          (hlReferences ln))))
              | (HL_Implies (_, _), HL_Iff (_, _)) => false
              | (HL_Implies (_, _), HL_ForAll (_, _)) => false
              | (HL_Implies (_, _), HL_Exists (_, _)) => false
              | (HL_Iff (_, _), _) => false | (HL_ForAll (_, _), _) => false
              | (HL_Exists (_, _), _) => false)
          | (SOME _, (SOME _, HL_ForAll (_, _))) => false
          | (SOME _, (SOME _, HL_Exists (_, _))) => false)
      | HL_IffElim (m, n) =>
        (case (hlLookupLine p m, hlLookupLine p n) of (NONE, _) => false
          | (SOME _, NONE) => false
          | (SOME lm, SOME ln) =>
            (case hlFormula lm of HL_Predicate (_, _) => false
              | HL_Boolean _ => false | HL_Not _ => false
              | HL_And (_, _) => false | HL_Or (_, _) => false
              | HL_Implies (_, _) => false
              | HL_Iff (pa, q) =>
                (equal_hl_formulaa (hlFormula ln) pa andalso
                   equal_hl_formulaa phi q orelse
                  equal_hl_formulaa (hlFormula ln) q andalso
                    equal_hl_formulaa phi pa) andalso
                  equal_set equal_int g
                    (sup_set equal_int (hlReferences lm) (hlReferences ln))
              | HL_ForAll (_, _) => false | HL_Exists (_, _) => false))
      | HL_QN m =>
        (case hlLookupLine p m of NONE => false
          | SOME lm =>
            hlQuantifierNegationEquivalent (hlFormula lm) phi andalso
              equal_set equal_int g (hlReferences lm)))
  end;

fun hlLineOKG src p l = hlStructureOK p l andalso hlRuleOKG src p l;

fun renumberJust r Assumption = Assumption
  | renumberJust r (MP (i0, i1)) = MP (r i0, r i1)
  | renumberJust r (CP (i0, i1)) = CP (r i0, r i1)
  | renumberJust r (RAA (i0, i1)) = RAA (r i0, r i1)
  | renumberJust r (DN i0) = DN (r i0)
  | renumberJust r (BotI (i0, i1)) = BotI (r i0, r i1)
  | renumberJust r (AndIntro (i0, i1)) = AndIntro (r i0, r i1)
  | renumberJust r (AndElimL i0) = AndElimL (r i0)
  | renumberJust r (AndElimR i0) = AndElimR (r i0)
  | renumberJust r (OrIntroL i0) = OrIntroL (r i0)
  | renumberJust r (OrIntroR i0) = OrIntroR (r i0)
  | renumberJust r (OrElim (i0, i1, i2, i3, i4)) =
    OrElim (r i0, r i1, r i2, r i3, r i4)
  | renumberJust r (IffIntro (i0, i1)) = IffIntro (r i0, r i1)
  | renumberJust r (IffElimL i0) = IffElimL (r i0)
  | renumberJust r (IffElimR i0) = IffElimR (r i0)
  | renumberJust r (ForallElim i0) = ForallElim (r i0)
  | renumberJust r (ForallIntro i0) = ForallIntro (r i0)
  | renumberJust r (ExistsIntro i0) = ExistsIntro (r i0)
  | renumberJust r (ExistsElim (i0, i1, i2)) = ExistsElim (r i0, r i1, r i2)
  | renumberJust r EqIntro = EqIntro
  | renumberJust r (EqElim (i0, i1)) = EqElim (r i0, r i1)
  | renumberJust r (Reit i0) = Reit (r i0);

fun relabel r l =
  ProofLine
    (r (lineNumber l), formula l, renumberJust r (justification l),
      image r (references l));

fun boxOrderError p =
  (case filtera (fn ac => less_nat (snd ac) (fst ac)) (boxesOf p) of [] => NONE
    | ac :: _ => SOME (BoxReversed (fst ac, snd ac)));

fun isPremiseLine p l =
  equal_justa (justification l) Assumption andalso
    not (membera equal_nat (dischargedAssumps p) (lineNumber l));

fun badSubCitations p =
  maps (fn l =>
         map_filter
           (fn x =>
             (if not (equal_lista equal_nat (boxPath p (lineNumber l))
                       (subLevel p x))
               then SOME (lineNumber l, (snd x, fst x)) else NONE))
           (dischargePairs (justification l)))
    p;

fun subScopeError p =
  (case badSubCitations p of [] => NONE
    | (n, (c, a)) :: _ => SOME (OutOfScope (n, c, a)));

val zero_int : int = Int_of_integer (0 : IntInf.int);

fun hlCanonicalOrder p =
  list_all (less_int zero_int) (map hlLineNumber p) andalso
    sorted_wrt less_int (map hlLineNumber p);

fun hlDischargePairs (HL_CP (a, c)) = [(a, c)]
  | hlDischargePairs (HL_RAA (a, c)) = [(a, c)]
  | hlDischargePairs (HL_OrElim (d, a1, c1, a2, c2)) = [(a1, c1), (a2, c2)]
  | hlDischargePairs (HL_ExistsElim (m, a, c)) = [(a, c)]
  | hlDischargePairs HL_Assumption = []
  | hlDischargePairs (HL_MP (v, va)) = []
  | hlDischargePairs (HL_MT (v, va)) = []
  | hlDischargePairs (HL_DN v) = []
  | hlDischargePairs (HL_AndIntro (v, va)) = []
  | hlDischargePairs (HL_AndElim v) = []
  | hlDischargePairs (HL_OrIntro v) = []
  | hlDischargePairs (HL_ForallElim v) = []
  | hlDischargePairs (HL_ExistsIntro v) = []
  | hlDischargePairs (HL_ForallIntro v) = []
  | hlDischargePairs HL_EqIntro = []
  | hlDischargePairs (HL_EqElim (v, va)) = []
  | hlDischargePairs HL_LEM = []
  | hlDischargePairs (HL_PropTaut v) = []
  | hlDischargePairs (HL_IffIntro (v, va)) = []
  | hlDischargePairs (HL_IffElim (v, va)) = []
  | hlDischargePairs (HL_QN v) = [];

fun hlCorrectG src p = list_all (hlLineOKG src p) p;

fun equal_hl_fitch_rule (HL_FQN x22) (HL_FReit x23) = false
  | equal_hl_fitch_rule (HL_FReit x23) (HL_FQN x22) = false
  | equal_hl_fitch_rule (HL_FIffE (x211, x212)) (HL_FReit x23) = false
  | equal_hl_fitch_rule (HL_FReit x23) (HL_FIffE (x211, x212)) = false
  | equal_hl_fitch_rule (HL_FIffE (x211, x212)) (HL_FQN x22) = false
  | equal_hl_fitch_rule (HL_FQN x22) (HL_FIffE (x211, x212)) = false
  | equal_hl_fitch_rule (HL_FIffI (x201, x202)) (HL_FReit x23) = false
  | equal_hl_fitch_rule (HL_FReit x23) (HL_FIffI (x201, x202)) = false
  | equal_hl_fitch_rule (HL_FIffI (x201, x202)) (HL_FQN x22) = false
  | equal_hl_fitch_rule (HL_FQN x22) (HL_FIffI (x201, x202)) = false
  | equal_hl_fitch_rule (HL_FIffI (x201, x202)) (HL_FIffE (x211, x212)) = false
  | equal_hl_fitch_rule (HL_FIffE (x211, x212)) (HL_FIffI (x201, x202)) = false
  | equal_hl_fitch_rule (HL_FPropTaut x19) (HL_FReit x23) = false
  | equal_hl_fitch_rule (HL_FReit x23) (HL_FPropTaut x19) = false
  | equal_hl_fitch_rule (HL_FPropTaut x19) (HL_FQN x22) = false
  | equal_hl_fitch_rule (HL_FQN x22) (HL_FPropTaut x19) = false
  | equal_hl_fitch_rule (HL_FPropTaut x19) (HL_FIffE (x211, x212)) = false
  | equal_hl_fitch_rule (HL_FIffE (x211, x212)) (HL_FPropTaut x19) = false
  | equal_hl_fitch_rule (HL_FPropTaut x19) (HL_FIffI (x201, x202)) = false
  | equal_hl_fitch_rule (HL_FIffI (x201, x202)) (HL_FPropTaut x19) = false
  | equal_hl_fitch_rule HL_FLEM (HL_FReit x23) = false
  | equal_hl_fitch_rule (HL_FReit x23) HL_FLEM = false
  | equal_hl_fitch_rule HL_FLEM (HL_FQN x22) = false
  | equal_hl_fitch_rule (HL_FQN x22) HL_FLEM = false
  | equal_hl_fitch_rule HL_FLEM (HL_FIffE (x211, x212)) = false
  | equal_hl_fitch_rule (HL_FIffE (x211, x212)) HL_FLEM = false
  | equal_hl_fitch_rule HL_FLEM (HL_FIffI (x201, x202)) = false
  | equal_hl_fitch_rule (HL_FIffI (x201, x202)) HL_FLEM = false
  | equal_hl_fitch_rule HL_FLEM (HL_FPropTaut x19) = false
  | equal_hl_fitch_rule (HL_FPropTaut x19) HL_FLEM = false
  | equal_hl_fitch_rule (HL_FEqE (x171, x172)) (HL_FReit x23) = false
  | equal_hl_fitch_rule (HL_FReit x23) (HL_FEqE (x171, x172)) = false
  | equal_hl_fitch_rule (HL_FEqE (x171, x172)) (HL_FQN x22) = false
  | equal_hl_fitch_rule (HL_FQN x22) (HL_FEqE (x171, x172)) = false
  | equal_hl_fitch_rule (HL_FEqE (x171, x172)) (HL_FIffE (x211, x212)) = false
  | equal_hl_fitch_rule (HL_FIffE (x211, x212)) (HL_FEqE (x171, x172)) = false
  | equal_hl_fitch_rule (HL_FEqE (x171, x172)) (HL_FIffI (x201, x202)) = false
  | equal_hl_fitch_rule (HL_FIffI (x201, x202)) (HL_FEqE (x171, x172)) = false
  | equal_hl_fitch_rule (HL_FEqE (x171, x172)) (HL_FPropTaut x19) = false
  | equal_hl_fitch_rule (HL_FPropTaut x19) (HL_FEqE (x171, x172)) = false
  | equal_hl_fitch_rule (HL_FEqE (x171, x172)) HL_FLEM = false
  | equal_hl_fitch_rule HL_FLEM (HL_FEqE (x171, x172)) = false
  | equal_hl_fitch_rule HL_FEqI (HL_FReit x23) = false
  | equal_hl_fitch_rule (HL_FReit x23) HL_FEqI = false
  | equal_hl_fitch_rule HL_FEqI (HL_FQN x22) = false
  | equal_hl_fitch_rule (HL_FQN x22) HL_FEqI = false
  | equal_hl_fitch_rule HL_FEqI (HL_FIffE (x211, x212)) = false
  | equal_hl_fitch_rule (HL_FIffE (x211, x212)) HL_FEqI = false
  | equal_hl_fitch_rule HL_FEqI (HL_FIffI (x201, x202)) = false
  | equal_hl_fitch_rule (HL_FIffI (x201, x202)) HL_FEqI = false
  | equal_hl_fitch_rule HL_FEqI (HL_FPropTaut x19) = false
  | equal_hl_fitch_rule (HL_FPropTaut x19) HL_FEqI = false
  | equal_hl_fitch_rule HL_FEqI HL_FLEM = false
  | equal_hl_fitch_rule HL_FLEM HL_FEqI = false
  | equal_hl_fitch_rule HL_FEqI (HL_FEqE (x171, x172)) = false
  | equal_hl_fitch_rule (HL_FEqE (x171, x172)) HL_FEqI = false
  | equal_hl_fitch_rule (HL_FExistsE (x151, x152)) (HL_FReit x23) = false
  | equal_hl_fitch_rule (HL_FReit x23) (HL_FExistsE (x151, x152)) = false
  | equal_hl_fitch_rule (HL_FExistsE (x151, x152)) (HL_FQN x22) = false
  | equal_hl_fitch_rule (HL_FQN x22) (HL_FExistsE (x151, x152)) = false
  | equal_hl_fitch_rule (HL_FExistsE (x151, x152)) (HL_FIffE (x211, x212)) =
    false
  | equal_hl_fitch_rule (HL_FIffE (x211, x212)) (HL_FExistsE (x151, x152)) =
    false
  | equal_hl_fitch_rule (HL_FExistsE (x151, x152)) (HL_FIffI (x201, x202)) =
    false
  | equal_hl_fitch_rule (HL_FIffI (x201, x202)) (HL_FExistsE (x151, x152)) =
    false
  | equal_hl_fitch_rule (HL_FExistsE (x151, x152)) (HL_FPropTaut x19) = false
  | equal_hl_fitch_rule (HL_FPropTaut x19) (HL_FExistsE (x151, x152)) = false
  | equal_hl_fitch_rule (HL_FExistsE (x151, x152)) HL_FLEM = false
  | equal_hl_fitch_rule HL_FLEM (HL_FExistsE (x151, x152)) = false
  | equal_hl_fitch_rule (HL_FExistsE (x151, x152)) (HL_FEqE (x171, x172)) =
    false
  | equal_hl_fitch_rule (HL_FEqE (x171, x172)) (HL_FExistsE (x151, x152)) =
    false
  | equal_hl_fitch_rule (HL_FExistsE (x151, x152)) HL_FEqI = false
  | equal_hl_fitch_rule HL_FEqI (HL_FExistsE (x151, x152)) = false
  | equal_hl_fitch_rule (HL_FExistsI x14) (HL_FReit x23) = false
  | equal_hl_fitch_rule (HL_FReit x23) (HL_FExistsI x14) = false
  | equal_hl_fitch_rule (HL_FExistsI x14) (HL_FQN x22) = false
  | equal_hl_fitch_rule (HL_FQN x22) (HL_FExistsI x14) = false
  | equal_hl_fitch_rule (HL_FExistsI x14) (HL_FIffE (x211, x212)) = false
  | equal_hl_fitch_rule (HL_FIffE (x211, x212)) (HL_FExistsI x14) = false
  | equal_hl_fitch_rule (HL_FExistsI x14) (HL_FIffI (x201, x202)) = false
  | equal_hl_fitch_rule (HL_FIffI (x201, x202)) (HL_FExistsI x14) = false
  | equal_hl_fitch_rule (HL_FExistsI x14) (HL_FPropTaut x19) = false
  | equal_hl_fitch_rule (HL_FPropTaut x19) (HL_FExistsI x14) = false
  | equal_hl_fitch_rule (HL_FExistsI x14) HL_FLEM = false
  | equal_hl_fitch_rule HL_FLEM (HL_FExistsI x14) = false
  | equal_hl_fitch_rule (HL_FExistsI x14) (HL_FEqE (x171, x172)) = false
  | equal_hl_fitch_rule (HL_FEqE (x171, x172)) (HL_FExistsI x14) = false
  | equal_hl_fitch_rule (HL_FExistsI x14) HL_FEqI = false
  | equal_hl_fitch_rule HL_FEqI (HL_FExistsI x14) = false
  | equal_hl_fitch_rule (HL_FExistsI x14) (HL_FExistsE (x151, x152)) = false
  | equal_hl_fitch_rule (HL_FExistsE (x151, x152)) (HL_FExistsI x14) = false
  | equal_hl_fitch_rule (HL_FForallI x13) (HL_FReit x23) = false
  | equal_hl_fitch_rule (HL_FReit x23) (HL_FForallI x13) = false
  | equal_hl_fitch_rule (HL_FForallI x13) (HL_FQN x22) = false
  | equal_hl_fitch_rule (HL_FQN x22) (HL_FForallI x13) = false
  | equal_hl_fitch_rule (HL_FForallI x13) (HL_FIffE (x211, x212)) = false
  | equal_hl_fitch_rule (HL_FIffE (x211, x212)) (HL_FForallI x13) = false
  | equal_hl_fitch_rule (HL_FForallI x13) (HL_FIffI (x201, x202)) = false
  | equal_hl_fitch_rule (HL_FIffI (x201, x202)) (HL_FForallI x13) = false
  | equal_hl_fitch_rule (HL_FForallI x13) (HL_FPropTaut x19) = false
  | equal_hl_fitch_rule (HL_FPropTaut x19) (HL_FForallI x13) = false
  | equal_hl_fitch_rule (HL_FForallI x13) HL_FLEM = false
  | equal_hl_fitch_rule HL_FLEM (HL_FForallI x13) = false
  | equal_hl_fitch_rule (HL_FForallI x13) (HL_FEqE (x171, x172)) = false
  | equal_hl_fitch_rule (HL_FEqE (x171, x172)) (HL_FForallI x13) = false
  | equal_hl_fitch_rule (HL_FForallI x13) HL_FEqI = false
  | equal_hl_fitch_rule HL_FEqI (HL_FForallI x13) = false
  | equal_hl_fitch_rule (HL_FForallI x13) (HL_FExistsE (x151, x152)) = false
  | equal_hl_fitch_rule (HL_FExistsE (x151, x152)) (HL_FForallI x13) = false
  | equal_hl_fitch_rule (HL_FForallI x13) (HL_FExistsI x14) = false
  | equal_hl_fitch_rule (HL_FExistsI x14) (HL_FForallI x13) = false
  | equal_hl_fitch_rule (HL_FForallE x12) (HL_FReit x23) = false
  | equal_hl_fitch_rule (HL_FReit x23) (HL_FForallE x12) = false
  | equal_hl_fitch_rule (HL_FForallE x12) (HL_FQN x22) = false
  | equal_hl_fitch_rule (HL_FQN x22) (HL_FForallE x12) = false
  | equal_hl_fitch_rule (HL_FForallE x12) (HL_FIffE (x211, x212)) = false
  | equal_hl_fitch_rule (HL_FIffE (x211, x212)) (HL_FForallE x12) = false
  | equal_hl_fitch_rule (HL_FForallE x12) (HL_FIffI (x201, x202)) = false
  | equal_hl_fitch_rule (HL_FIffI (x201, x202)) (HL_FForallE x12) = false
  | equal_hl_fitch_rule (HL_FForallE x12) (HL_FPropTaut x19) = false
  | equal_hl_fitch_rule (HL_FPropTaut x19) (HL_FForallE x12) = false
  | equal_hl_fitch_rule (HL_FForallE x12) HL_FLEM = false
  | equal_hl_fitch_rule HL_FLEM (HL_FForallE x12) = false
  | equal_hl_fitch_rule (HL_FForallE x12) (HL_FEqE (x171, x172)) = false
  | equal_hl_fitch_rule (HL_FEqE (x171, x172)) (HL_FForallE x12) = false
  | equal_hl_fitch_rule (HL_FForallE x12) HL_FEqI = false
  | equal_hl_fitch_rule HL_FEqI (HL_FForallE x12) = false
  | equal_hl_fitch_rule (HL_FForallE x12) (HL_FExistsE (x151, x152)) = false
  | equal_hl_fitch_rule (HL_FExistsE (x151, x152)) (HL_FForallE x12) = false
  | equal_hl_fitch_rule (HL_FForallE x12) (HL_FExistsI x14) = false
  | equal_hl_fitch_rule (HL_FExistsI x14) (HL_FForallE x12) = false
  | equal_hl_fitch_rule (HL_FForallE x12) (HL_FForallI x13) = false
  | equal_hl_fitch_rule (HL_FForallI x13) (HL_FForallE x12) = false
  | equal_hl_fitch_rule (HL_FRAA x11) (HL_FReit x23) = false
  | equal_hl_fitch_rule (HL_FReit x23) (HL_FRAA x11) = false
  | equal_hl_fitch_rule (HL_FRAA x11) (HL_FQN x22) = false
  | equal_hl_fitch_rule (HL_FQN x22) (HL_FRAA x11) = false
  | equal_hl_fitch_rule (HL_FRAA x11) (HL_FIffE (x211, x212)) = false
  | equal_hl_fitch_rule (HL_FIffE (x211, x212)) (HL_FRAA x11) = false
  | equal_hl_fitch_rule (HL_FRAA x11) (HL_FIffI (x201, x202)) = false
  | equal_hl_fitch_rule (HL_FIffI (x201, x202)) (HL_FRAA x11) = false
  | equal_hl_fitch_rule (HL_FRAA x11) (HL_FPropTaut x19) = false
  | equal_hl_fitch_rule (HL_FPropTaut x19) (HL_FRAA x11) = false
  | equal_hl_fitch_rule (HL_FRAA x11) HL_FLEM = false
  | equal_hl_fitch_rule HL_FLEM (HL_FRAA x11) = false
  | equal_hl_fitch_rule (HL_FRAA x11) (HL_FEqE (x171, x172)) = false
  | equal_hl_fitch_rule (HL_FEqE (x171, x172)) (HL_FRAA x11) = false
  | equal_hl_fitch_rule (HL_FRAA x11) HL_FEqI = false
  | equal_hl_fitch_rule HL_FEqI (HL_FRAA x11) = false
  | equal_hl_fitch_rule (HL_FRAA x11) (HL_FExistsE (x151, x152)) = false
  | equal_hl_fitch_rule (HL_FExistsE (x151, x152)) (HL_FRAA x11) = false
  | equal_hl_fitch_rule (HL_FRAA x11) (HL_FExistsI x14) = false
  | equal_hl_fitch_rule (HL_FExistsI x14) (HL_FRAA x11) = false
  | equal_hl_fitch_rule (HL_FRAA x11) (HL_FForallI x13) = false
  | equal_hl_fitch_rule (HL_FForallI x13) (HL_FRAA x11) = false
  | equal_hl_fitch_rule (HL_FRAA x11) (HL_FForallE x12) = false
  | equal_hl_fitch_rule (HL_FForallE x12) (HL_FRAA x11) = false
  | equal_hl_fitch_rule (HL_FOrE (x101, x102, x103)) (HL_FReit x23) = false
  | equal_hl_fitch_rule (HL_FReit x23) (HL_FOrE (x101, x102, x103)) = false
  | equal_hl_fitch_rule (HL_FOrE (x101, x102, x103)) (HL_FQN x22) = false
  | equal_hl_fitch_rule (HL_FQN x22) (HL_FOrE (x101, x102, x103)) = false
  | equal_hl_fitch_rule (HL_FOrE (x101, x102, x103)) (HL_FIffE (x211, x212)) =
    false
  | equal_hl_fitch_rule (HL_FIffE (x211, x212)) (HL_FOrE (x101, x102, x103)) =
    false
  | equal_hl_fitch_rule (HL_FOrE (x101, x102, x103)) (HL_FIffI (x201, x202)) =
    false
  | equal_hl_fitch_rule (HL_FIffI (x201, x202)) (HL_FOrE (x101, x102, x103)) =
    false
  | equal_hl_fitch_rule (HL_FOrE (x101, x102, x103)) (HL_FPropTaut x19) = false
  | equal_hl_fitch_rule (HL_FPropTaut x19) (HL_FOrE (x101, x102, x103)) = false
  | equal_hl_fitch_rule (HL_FOrE (x101, x102, x103)) HL_FLEM = false
  | equal_hl_fitch_rule HL_FLEM (HL_FOrE (x101, x102, x103)) = false
  | equal_hl_fitch_rule (HL_FOrE (x101, x102, x103)) (HL_FEqE (x171, x172)) =
    false
  | equal_hl_fitch_rule (HL_FEqE (x171, x172)) (HL_FOrE (x101, x102, x103)) =
    false
  | equal_hl_fitch_rule (HL_FOrE (x101, x102, x103)) HL_FEqI = false
  | equal_hl_fitch_rule HL_FEqI (HL_FOrE (x101, x102, x103)) = false
  | equal_hl_fitch_rule (HL_FOrE (x101, x102, x103)) (HL_FExistsE (x151, x152))
    = false
  | equal_hl_fitch_rule (HL_FExistsE (x151, x152)) (HL_FOrE (x101, x102, x103))
    = false
  | equal_hl_fitch_rule (HL_FOrE (x101, x102, x103)) (HL_FExistsI x14) = false
  | equal_hl_fitch_rule (HL_FExistsI x14) (HL_FOrE (x101, x102, x103)) = false
  | equal_hl_fitch_rule (HL_FOrE (x101, x102, x103)) (HL_FForallI x13) = false
  | equal_hl_fitch_rule (HL_FForallI x13) (HL_FOrE (x101, x102, x103)) = false
  | equal_hl_fitch_rule (HL_FOrE (x101, x102, x103)) (HL_FForallE x12) = false
  | equal_hl_fitch_rule (HL_FForallE x12) (HL_FOrE (x101, x102, x103)) = false
  | equal_hl_fitch_rule (HL_FOrE (x101, x102, x103)) (HL_FRAA x11) = false
  | equal_hl_fitch_rule (HL_FRAA x11) (HL_FOrE (x101, x102, x103)) = false
  | equal_hl_fitch_rule (HL_FOrI x9) (HL_FReit x23) = false
  | equal_hl_fitch_rule (HL_FReit x23) (HL_FOrI x9) = false
  | equal_hl_fitch_rule (HL_FOrI x9) (HL_FQN x22) = false
  | equal_hl_fitch_rule (HL_FQN x22) (HL_FOrI x9) = false
  | equal_hl_fitch_rule (HL_FOrI x9) (HL_FIffE (x211, x212)) = false
  | equal_hl_fitch_rule (HL_FIffE (x211, x212)) (HL_FOrI x9) = false
  | equal_hl_fitch_rule (HL_FOrI x9) (HL_FIffI (x201, x202)) = false
  | equal_hl_fitch_rule (HL_FIffI (x201, x202)) (HL_FOrI x9) = false
  | equal_hl_fitch_rule (HL_FOrI x9) (HL_FPropTaut x19) = false
  | equal_hl_fitch_rule (HL_FPropTaut x19) (HL_FOrI x9) = false
  | equal_hl_fitch_rule (HL_FOrI x9) HL_FLEM = false
  | equal_hl_fitch_rule HL_FLEM (HL_FOrI x9) = false
  | equal_hl_fitch_rule (HL_FOrI x9) (HL_FEqE (x171, x172)) = false
  | equal_hl_fitch_rule (HL_FEqE (x171, x172)) (HL_FOrI x9) = false
  | equal_hl_fitch_rule (HL_FOrI x9) HL_FEqI = false
  | equal_hl_fitch_rule HL_FEqI (HL_FOrI x9) = false
  | equal_hl_fitch_rule (HL_FOrI x9) (HL_FExistsE (x151, x152)) = false
  | equal_hl_fitch_rule (HL_FExistsE (x151, x152)) (HL_FOrI x9) = false
  | equal_hl_fitch_rule (HL_FOrI x9) (HL_FExistsI x14) = false
  | equal_hl_fitch_rule (HL_FExistsI x14) (HL_FOrI x9) = false
  | equal_hl_fitch_rule (HL_FOrI x9) (HL_FForallI x13) = false
  | equal_hl_fitch_rule (HL_FForallI x13) (HL_FOrI x9) = false
  | equal_hl_fitch_rule (HL_FOrI x9) (HL_FForallE x12) = false
  | equal_hl_fitch_rule (HL_FForallE x12) (HL_FOrI x9) = false
  | equal_hl_fitch_rule (HL_FOrI x9) (HL_FRAA x11) = false
  | equal_hl_fitch_rule (HL_FRAA x11) (HL_FOrI x9) = false
  | equal_hl_fitch_rule (HL_FOrI x9) (HL_FOrE (x101, x102, x103)) = false
  | equal_hl_fitch_rule (HL_FOrE (x101, x102, x103)) (HL_FOrI x9) = false
  | equal_hl_fitch_rule (HL_FAndE x8) (HL_FReit x23) = false
  | equal_hl_fitch_rule (HL_FReit x23) (HL_FAndE x8) = false
  | equal_hl_fitch_rule (HL_FAndE x8) (HL_FQN x22) = false
  | equal_hl_fitch_rule (HL_FQN x22) (HL_FAndE x8) = false
  | equal_hl_fitch_rule (HL_FAndE x8) (HL_FIffE (x211, x212)) = false
  | equal_hl_fitch_rule (HL_FIffE (x211, x212)) (HL_FAndE x8) = false
  | equal_hl_fitch_rule (HL_FAndE x8) (HL_FIffI (x201, x202)) = false
  | equal_hl_fitch_rule (HL_FIffI (x201, x202)) (HL_FAndE x8) = false
  | equal_hl_fitch_rule (HL_FAndE x8) (HL_FPropTaut x19) = false
  | equal_hl_fitch_rule (HL_FPropTaut x19) (HL_FAndE x8) = false
  | equal_hl_fitch_rule (HL_FAndE x8) HL_FLEM = false
  | equal_hl_fitch_rule HL_FLEM (HL_FAndE x8) = false
  | equal_hl_fitch_rule (HL_FAndE x8) (HL_FEqE (x171, x172)) = false
  | equal_hl_fitch_rule (HL_FEqE (x171, x172)) (HL_FAndE x8) = false
  | equal_hl_fitch_rule (HL_FAndE x8) HL_FEqI = false
  | equal_hl_fitch_rule HL_FEqI (HL_FAndE x8) = false
  | equal_hl_fitch_rule (HL_FAndE x8) (HL_FExistsE (x151, x152)) = false
  | equal_hl_fitch_rule (HL_FExistsE (x151, x152)) (HL_FAndE x8) = false
  | equal_hl_fitch_rule (HL_FAndE x8) (HL_FExistsI x14) = false
  | equal_hl_fitch_rule (HL_FExistsI x14) (HL_FAndE x8) = false
  | equal_hl_fitch_rule (HL_FAndE x8) (HL_FForallI x13) = false
  | equal_hl_fitch_rule (HL_FForallI x13) (HL_FAndE x8) = false
  | equal_hl_fitch_rule (HL_FAndE x8) (HL_FForallE x12) = false
  | equal_hl_fitch_rule (HL_FForallE x12) (HL_FAndE x8) = false
  | equal_hl_fitch_rule (HL_FAndE x8) (HL_FRAA x11) = false
  | equal_hl_fitch_rule (HL_FRAA x11) (HL_FAndE x8) = false
  | equal_hl_fitch_rule (HL_FAndE x8) (HL_FOrE (x101, x102, x103)) = false
  | equal_hl_fitch_rule (HL_FOrE (x101, x102, x103)) (HL_FAndE x8) = false
  | equal_hl_fitch_rule (HL_FAndE x8) (HL_FOrI x9) = false
  | equal_hl_fitch_rule (HL_FOrI x9) (HL_FAndE x8) = false
  | equal_hl_fitch_rule (HL_FAndI (x71, x72)) (HL_FReit x23) = false
  | equal_hl_fitch_rule (HL_FReit x23) (HL_FAndI (x71, x72)) = false
  | equal_hl_fitch_rule (HL_FAndI (x71, x72)) (HL_FQN x22) = false
  | equal_hl_fitch_rule (HL_FQN x22) (HL_FAndI (x71, x72)) = false
  | equal_hl_fitch_rule (HL_FAndI (x71, x72)) (HL_FIffE (x211, x212)) = false
  | equal_hl_fitch_rule (HL_FIffE (x211, x212)) (HL_FAndI (x71, x72)) = false
  | equal_hl_fitch_rule (HL_FAndI (x71, x72)) (HL_FIffI (x201, x202)) = false
  | equal_hl_fitch_rule (HL_FIffI (x201, x202)) (HL_FAndI (x71, x72)) = false
  | equal_hl_fitch_rule (HL_FAndI (x71, x72)) (HL_FPropTaut x19) = false
  | equal_hl_fitch_rule (HL_FPropTaut x19) (HL_FAndI (x71, x72)) = false
  | equal_hl_fitch_rule (HL_FAndI (x71, x72)) HL_FLEM = false
  | equal_hl_fitch_rule HL_FLEM (HL_FAndI (x71, x72)) = false
  | equal_hl_fitch_rule (HL_FAndI (x71, x72)) (HL_FEqE (x171, x172)) = false
  | equal_hl_fitch_rule (HL_FEqE (x171, x172)) (HL_FAndI (x71, x72)) = false
  | equal_hl_fitch_rule (HL_FAndI (x71, x72)) HL_FEqI = false
  | equal_hl_fitch_rule HL_FEqI (HL_FAndI (x71, x72)) = false
  | equal_hl_fitch_rule (HL_FAndI (x71, x72)) (HL_FExistsE (x151, x152)) = false
  | equal_hl_fitch_rule (HL_FExistsE (x151, x152)) (HL_FAndI (x71, x72)) = false
  | equal_hl_fitch_rule (HL_FAndI (x71, x72)) (HL_FExistsI x14) = false
  | equal_hl_fitch_rule (HL_FExistsI x14) (HL_FAndI (x71, x72)) = false
  | equal_hl_fitch_rule (HL_FAndI (x71, x72)) (HL_FForallI x13) = false
  | equal_hl_fitch_rule (HL_FForallI x13) (HL_FAndI (x71, x72)) = false
  | equal_hl_fitch_rule (HL_FAndI (x71, x72)) (HL_FForallE x12) = false
  | equal_hl_fitch_rule (HL_FForallE x12) (HL_FAndI (x71, x72)) = false
  | equal_hl_fitch_rule (HL_FAndI (x71, x72)) (HL_FRAA x11) = false
  | equal_hl_fitch_rule (HL_FRAA x11) (HL_FAndI (x71, x72)) = false
  | equal_hl_fitch_rule (HL_FAndI (x71, x72)) (HL_FOrE (x101, x102, x103)) =
    false
  | equal_hl_fitch_rule (HL_FOrE (x101, x102, x103)) (HL_FAndI (x71, x72)) =
    false
  | equal_hl_fitch_rule (HL_FAndI (x71, x72)) (HL_FOrI x9) = false
  | equal_hl_fitch_rule (HL_FOrI x9) (HL_FAndI (x71, x72)) = false
  | equal_hl_fitch_rule (HL_FAndI (x71, x72)) (HL_FAndE x8) = false
  | equal_hl_fitch_rule (HL_FAndE x8) (HL_FAndI (x71, x72)) = false
  | equal_hl_fitch_rule (HL_FCP x6) (HL_FReit x23) = false
  | equal_hl_fitch_rule (HL_FReit x23) (HL_FCP x6) = false
  | equal_hl_fitch_rule (HL_FCP x6) (HL_FQN x22) = false
  | equal_hl_fitch_rule (HL_FQN x22) (HL_FCP x6) = false
  | equal_hl_fitch_rule (HL_FCP x6) (HL_FIffE (x211, x212)) = false
  | equal_hl_fitch_rule (HL_FIffE (x211, x212)) (HL_FCP x6) = false
  | equal_hl_fitch_rule (HL_FCP x6) (HL_FIffI (x201, x202)) = false
  | equal_hl_fitch_rule (HL_FIffI (x201, x202)) (HL_FCP x6) = false
  | equal_hl_fitch_rule (HL_FCP x6) (HL_FPropTaut x19) = false
  | equal_hl_fitch_rule (HL_FPropTaut x19) (HL_FCP x6) = false
  | equal_hl_fitch_rule (HL_FCP x6) HL_FLEM = false
  | equal_hl_fitch_rule HL_FLEM (HL_FCP x6) = false
  | equal_hl_fitch_rule (HL_FCP x6) (HL_FEqE (x171, x172)) = false
  | equal_hl_fitch_rule (HL_FEqE (x171, x172)) (HL_FCP x6) = false
  | equal_hl_fitch_rule (HL_FCP x6) HL_FEqI = false
  | equal_hl_fitch_rule HL_FEqI (HL_FCP x6) = false
  | equal_hl_fitch_rule (HL_FCP x6) (HL_FExistsE (x151, x152)) = false
  | equal_hl_fitch_rule (HL_FExistsE (x151, x152)) (HL_FCP x6) = false
  | equal_hl_fitch_rule (HL_FCP x6) (HL_FExistsI x14) = false
  | equal_hl_fitch_rule (HL_FExistsI x14) (HL_FCP x6) = false
  | equal_hl_fitch_rule (HL_FCP x6) (HL_FForallI x13) = false
  | equal_hl_fitch_rule (HL_FForallI x13) (HL_FCP x6) = false
  | equal_hl_fitch_rule (HL_FCP x6) (HL_FForallE x12) = false
  | equal_hl_fitch_rule (HL_FForallE x12) (HL_FCP x6) = false
  | equal_hl_fitch_rule (HL_FCP x6) (HL_FRAA x11) = false
  | equal_hl_fitch_rule (HL_FRAA x11) (HL_FCP x6) = false
  | equal_hl_fitch_rule (HL_FCP x6) (HL_FOrE (x101, x102, x103)) = false
  | equal_hl_fitch_rule (HL_FOrE (x101, x102, x103)) (HL_FCP x6) = false
  | equal_hl_fitch_rule (HL_FCP x6) (HL_FOrI x9) = false
  | equal_hl_fitch_rule (HL_FOrI x9) (HL_FCP x6) = false
  | equal_hl_fitch_rule (HL_FCP x6) (HL_FAndE x8) = false
  | equal_hl_fitch_rule (HL_FAndE x8) (HL_FCP x6) = false
  | equal_hl_fitch_rule (HL_FCP x6) (HL_FAndI (x71, x72)) = false
  | equal_hl_fitch_rule (HL_FAndI (x71, x72)) (HL_FCP x6) = false
  | equal_hl_fitch_rule (HL_FDN x5) (HL_FReit x23) = false
  | equal_hl_fitch_rule (HL_FReit x23) (HL_FDN x5) = false
  | equal_hl_fitch_rule (HL_FDN x5) (HL_FQN x22) = false
  | equal_hl_fitch_rule (HL_FQN x22) (HL_FDN x5) = false
  | equal_hl_fitch_rule (HL_FDN x5) (HL_FIffE (x211, x212)) = false
  | equal_hl_fitch_rule (HL_FIffE (x211, x212)) (HL_FDN x5) = false
  | equal_hl_fitch_rule (HL_FDN x5) (HL_FIffI (x201, x202)) = false
  | equal_hl_fitch_rule (HL_FIffI (x201, x202)) (HL_FDN x5) = false
  | equal_hl_fitch_rule (HL_FDN x5) (HL_FPropTaut x19) = false
  | equal_hl_fitch_rule (HL_FPropTaut x19) (HL_FDN x5) = false
  | equal_hl_fitch_rule (HL_FDN x5) HL_FLEM = false
  | equal_hl_fitch_rule HL_FLEM (HL_FDN x5) = false
  | equal_hl_fitch_rule (HL_FDN x5) (HL_FEqE (x171, x172)) = false
  | equal_hl_fitch_rule (HL_FEqE (x171, x172)) (HL_FDN x5) = false
  | equal_hl_fitch_rule (HL_FDN x5) HL_FEqI = false
  | equal_hl_fitch_rule HL_FEqI (HL_FDN x5) = false
  | equal_hl_fitch_rule (HL_FDN x5) (HL_FExistsE (x151, x152)) = false
  | equal_hl_fitch_rule (HL_FExistsE (x151, x152)) (HL_FDN x5) = false
  | equal_hl_fitch_rule (HL_FDN x5) (HL_FExistsI x14) = false
  | equal_hl_fitch_rule (HL_FExistsI x14) (HL_FDN x5) = false
  | equal_hl_fitch_rule (HL_FDN x5) (HL_FForallI x13) = false
  | equal_hl_fitch_rule (HL_FForallI x13) (HL_FDN x5) = false
  | equal_hl_fitch_rule (HL_FDN x5) (HL_FForallE x12) = false
  | equal_hl_fitch_rule (HL_FForallE x12) (HL_FDN x5) = false
  | equal_hl_fitch_rule (HL_FDN x5) (HL_FRAA x11) = false
  | equal_hl_fitch_rule (HL_FRAA x11) (HL_FDN x5) = false
  | equal_hl_fitch_rule (HL_FDN x5) (HL_FOrE (x101, x102, x103)) = false
  | equal_hl_fitch_rule (HL_FOrE (x101, x102, x103)) (HL_FDN x5) = false
  | equal_hl_fitch_rule (HL_FDN x5) (HL_FOrI x9) = false
  | equal_hl_fitch_rule (HL_FOrI x9) (HL_FDN x5) = false
  | equal_hl_fitch_rule (HL_FDN x5) (HL_FAndE x8) = false
  | equal_hl_fitch_rule (HL_FAndE x8) (HL_FDN x5) = false
  | equal_hl_fitch_rule (HL_FDN x5) (HL_FAndI (x71, x72)) = false
  | equal_hl_fitch_rule (HL_FAndI (x71, x72)) (HL_FDN x5) = false
  | equal_hl_fitch_rule (HL_FDN x5) (HL_FCP x6) = false
  | equal_hl_fitch_rule (HL_FCP x6) (HL_FDN x5) = false
  | equal_hl_fitch_rule (HL_FMT (x41, x42)) (HL_FReit x23) = false
  | equal_hl_fitch_rule (HL_FReit x23) (HL_FMT (x41, x42)) = false
  | equal_hl_fitch_rule (HL_FMT (x41, x42)) (HL_FQN x22) = false
  | equal_hl_fitch_rule (HL_FQN x22) (HL_FMT (x41, x42)) = false
  | equal_hl_fitch_rule (HL_FMT (x41, x42)) (HL_FIffE (x211, x212)) = false
  | equal_hl_fitch_rule (HL_FIffE (x211, x212)) (HL_FMT (x41, x42)) = false
  | equal_hl_fitch_rule (HL_FMT (x41, x42)) (HL_FIffI (x201, x202)) = false
  | equal_hl_fitch_rule (HL_FIffI (x201, x202)) (HL_FMT (x41, x42)) = false
  | equal_hl_fitch_rule (HL_FMT (x41, x42)) (HL_FPropTaut x19) = false
  | equal_hl_fitch_rule (HL_FPropTaut x19) (HL_FMT (x41, x42)) = false
  | equal_hl_fitch_rule (HL_FMT (x41, x42)) HL_FLEM = false
  | equal_hl_fitch_rule HL_FLEM (HL_FMT (x41, x42)) = false
  | equal_hl_fitch_rule (HL_FMT (x41, x42)) (HL_FEqE (x171, x172)) = false
  | equal_hl_fitch_rule (HL_FEqE (x171, x172)) (HL_FMT (x41, x42)) = false
  | equal_hl_fitch_rule (HL_FMT (x41, x42)) HL_FEqI = false
  | equal_hl_fitch_rule HL_FEqI (HL_FMT (x41, x42)) = false
  | equal_hl_fitch_rule (HL_FMT (x41, x42)) (HL_FExistsE (x151, x152)) = false
  | equal_hl_fitch_rule (HL_FExistsE (x151, x152)) (HL_FMT (x41, x42)) = false
  | equal_hl_fitch_rule (HL_FMT (x41, x42)) (HL_FExistsI x14) = false
  | equal_hl_fitch_rule (HL_FExistsI x14) (HL_FMT (x41, x42)) = false
  | equal_hl_fitch_rule (HL_FMT (x41, x42)) (HL_FForallI x13) = false
  | equal_hl_fitch_rule (HL_FForallI x13) (HL_FMT (x41, x42)) = false
  | equal_hl_fitch_rule (HL_FMT (x41, x42)) (HL_FForallE x12) = false
  | equal_hl_fitch_rule (HL_FForallE x12) (HL_FMT (x41, x42)) = false
  | equal_hl_fitch_rule (HL_FMT (x41, x42)) (HL_FRAA x11) = false
  | equal_hl_fitch_rule (HL_FRAA x11) (HL_FMT (x41, x42)) = false
  | equal_hl_fitch_rule (HL_FMT (x41, x42)) (HL_FOrE (x101, x102, x103)) = false
  | equal_hl_fitch_rule (HL_FOrE (x101, x102, x103)) (HL_FMT (x41, x42)) = false
  | equal_hl_fitch_rule (HL_FMT (x41, x42)) (HL_FOrI x9) = false
  | equal_hl_fitch_rule (HL_FOrI x9) (HL_FMT (x41, x42)) = false
  | equal_hl_fitch_rule (HL_FMT (x41, x42)) (HL_FAndE x8) = false
  | equal_hl_fitch_rule (HL_FAndE x8) (HL_FMT (x41, x42)) = false
  | equal_hl_fitch_rule (HL_FMT (x41, x42)) (HL_FAndI (x71, x72)) = false
  | equal_hl_fitch_rule (HL_FAndI (x71, x72)) (HL_FMT (x41, x42)) = false
  | equal_hl_fitch_rule (HL_FMT (x41, x42)) (HL_FCP x6) = false
  | equal_hl_fitch_rule (HL_FCP x6) (HL_FMT (x41, x42)) = false
  | equal_hl_fitch_rule (HL_FMT (x41, x42)) (HL_FDN x5) = false
  | equal_hl_fitch_rule (HL_FDN x5) (HL_FMT (x41, x42)) = false
  | equal_hl_fitch_rule (HL_FMP (x31, x32)) (HL_FReit x23) = false
  | equal_hl_fitch_rule (HL_FReit x23) (HL_FMP (x31, x32)) = false
  | equal_hl_fitch_rule (HL_FMP (x31, x32)) (HL_FQN x22) = false
  | equal_hl_fitch_rule (HL_FQN x22) (HL_FMP (x31, x32)) = false
  | equal_hl_fitch_rule (HL_FMP (x31, x32)) (HL_FIffE (x211, x212)) = false
  | equal_hl_fitch_rule (HL_FIffE (x211, x212)) (HL_FMP (x31, x32)) = false
  | equal_hl_fitch_rule (HL_FMP (x31, x32)) (HL_FIffI (x201, x202)) = false
  | equal_hl_fitch_rule (HL_FIffI (x201, x202)) (HL_FMP (x31, x32)) = false
  | equal_hl_fitch_rule (HL_FMP (x31, x32)) (HL_FPropTaut x19) = false
  | equal_hl_fitch_rule (HL_FPropTaut x19) (HL_FMP (x31, x32)) = false
  | equal_hl_fitch_rule (HL_FMP (x31, x32)) HL_FLEM = false
  | equal_hl_fitch_rule HL_FLEM (HL_FMP (x31, x32)) = false
  | equal_hl_fitch_rule (HL_FMP (x31, x32)) (HL_FEqE (x171, x172)) = false
  | equal_hl_fitch_rule (HL_FEqE (x171, x172)) (HL_FMP (x31, x32)) = false
  | equal_hl_fitch_rule (HL_FMP (x31, x32)) HL_FEqI = false
  | equal_hl_fitch_rule HL_FEqI (HL_FMP (x31, x32)) = false
  | equal_hl_fitch_rule (HL_FMP (x31, x32)) (HL_FExistsE (x151, x152)) = false
  | equal_hl_fitch_rule (HL_FExistsE (x151, x152)) (HL_FMP (x31, x32)) = false
  | equal_hl_fitch_rule (HL_FMP (x31, x32)) (HL_FExistsI x14) = false
  | equal_hl_fitch_rule (HL_FExistsI x14) (HL_FMP (x31, x32)) = false
  | equal_hl_fitch_rule (HL_FMP (x31, x32)) (HL_FForallI x13) = false
  | equal_hl_fitch_rule (HL_FForallI x13) (HL_FMP (x31, x32)) = false
  | equal_hl_fitch_rule (HL_FMP (x31, x32)) (HL_FForallE x12) = false
  | equal_hl_fitch_rule (HL_FForallE x12) (HL_FMP (x31, x32)) = false
  | equal_hl_fitch_rule (HL_FMP (x31, x32)) (HL_FRAA x11) = false
  | equal_hl_fitch_rule (HL_FRAA x11) (HL_FMP (x31, x32)) = false
  | equal_hl_fitch_rule (HL_FMP (x31, x32)) (HL_FOrE (x101, x102, x103)) = false
  | equal_hl_fitch_rule (HL_FOrE (x101, x102, x103)) (HL_FMP (x31, x32)) = false
  | equal_hl_fitch_rule (HL_FMP (x31, x32)) (HL_FOrI x9) = false
  | equal_hl_fitch_rule (HL_FOrI x9) (HL_FMP (x31, x32)) = false
  | equal_hl_fitch_rule (HL_FMP (x31, x32)) (HL_FAndE x8) = false
  | equal_hl_fitch_rule (HL_FAndE x8) (HL_FMP (x31, x32)) = false
  | equal_hl_fitch_rule (HL_FMP (x31, x32)) (HL_FAndI (x71, x72)) = false
  | equal_hl_fitch_rule (HL_FAndI (x71, x72)) (HL_FMP (x31, x32)) = false
  | equal_hl_fitch_rule (HL_FMP (x31, x32)) (HL_FCP x6) = false
  | equal_hl_fitch_rule (HL_FCP x6) (HL_FMP (x31, x32)) = false
  | equal_hl_fitch_rule (HL_FMP (x31, x32)) (HL_FDN x5) = false
  | equal_hl_fitch_rule (HL_FDN x5) (HL_FMP (x31, x32)) = false
  | equal_hl_fitch_rule (HL_FMP (x31, x32)) (HL_FMT (x41, x42)) = false
  | equal_hl_fitch_rule (HL_FMT (x41, x42)) (HL_FMP (x31, x32)) = false
  | equal_hl_fitch_rule HL_FAssume (HL_FReit x23) = false
  | equal_hl_fitch_rule (HL_FReit x23) HL_FAssume = false
  | equal_hl_fitch_rule HL_FAssume (HL_FQN x22) = false
  | equal_hl_fitch_rule (HL_FQN x22) HL_FAssume = false
  | equal_hl_fitch_rule HL_FAssume (HL_FIffE (x211, x212)) = false
  | equal_hl_fitch_rule (HL_FIffE (x211, x212)) HL_FAssume = false
  | equal_hl_fitch_rule HL_FAssume (HL_FIffI (x201, x202)) = false
  | equal_hl_fitch_rule (HL_FIffI (x201, x202)) HL_FAssume = false
  | equal_hl_fitch_rule HL_FAssume (HL_FPropTaut x19) = false
  | equal_hl_fitch_rule (HL_FPropTaut x19) HL_FAssume = false
  | equal_hl_fitch_rule HL_FAssume HL_FLEM = false
  | equal_hl_fitch_rule HL_FLEM HL_FAssume = false
  | equal_hl_fitch_rule HL_FAssume (HL_FEqE (x171, x172)) = false
  | equal_hl_fitch_rule (HL_FEqE (x171, x172)) HL_FAssume = false
  | equal_hl_fitch_rule HL_FAssume HL_FEqI = false
  | equal_hl_fitch_rule HL_FEqI HL_FAssume = false
  | equal_hl_fitch_rule HL_FAssume (HL_FExistsE (x151, x152)) = false
  | equal_hl_fitch_rule (HL_FExistsE (x151, x152)) HL_FAssume = false
  | equal_hl_fitch_rule HL_FAssume (HL_FExistsI x14) = false
  | equal_hl_fitch_rule (HL_FExistsI x14) HL_FAssume = false
  | equal_hl_fitch_rule HL_FAssume (HL_FForallI x13) = false
  | equal_hl_fitch_rule (HL_FForallI x13) HL_FAssume = false
  | equal_hl_fitch_rule HL_FAssume (HL_FForallE x12) = false
  | equal_hl_fitch_rule (HL_FForallE x12) HL_FAssume = false
  | equal_hl_fitch_rule HL_FAssume (HL_FRAA x11) = false
  | equal_hl_fitch_rule (HL_FRAA x11) HL_FAssume = false
  | equal_hl_fitch_rule HL_FAssume (HL_FOrE (x101, x102, x103)) = false
  | equal_hl_fitch_rule (HL_FOrE (x101, x102, x103)) HL_FAssume = false
  | equal_hl_fitch_rule HL_FAssume (HL_FOrI x9) = false
  | equal_hl_fitch_rule (HL_FOrI x9) HL_FAssume = false
  | equal_hl_fitch_rule HL_FAssume (HL_FAndE x8) = false
  | equal_hl_fitch_rule (HL_FAndE x8) HL_FAssume = false
  | equal_hl_fitch_rule HL_FAssume (HL_FAndI (x71, x72)) = false
  | equal_hl_fitch_rule (HL_FAndI (x71, x72)) HL_FAssume = false
  | equal_hl_fitch_rule HL_FAssume (HL_FCP x6) = false
  | equal_hl_fitch_rule (HL_FCP x6) HL_FAssume = false
  | equal_hl_fitch_rule HL_FAssume (HL_FDN x5) = false
  | equal_hl_fitch_rule (HL_FDN x5) HL_FAssume = false
  | equal_hl_fitch_rule HL_FAssume (HL_FMT (x41, x42)) = false
  | equal_hl_fitch_rule (HL_FMT (x41, x42)) HL_FAssume = false
  | equal_hl_fitch_rule HL_FAssume (HL_FMP (x31, x32)) = false
  | equal_hl_fitch_rule (HL_FMP (x31, x32)) HL_FAssume = false
  | equal_hl_fitch_rule HL_FPremise (HL_FReit x23) = false
  | equal_hl_fitch_rule (HL_FReit x23) HL_FPremise = false
  | equal_hl_fitch_rule HL_FPremise (HL_FQN x22) = false
  | equal_hl_fitch_rule (HL_FQN x22) HL_FPremise = false
  | equal_hl_fitch_rule HL_FPremise (HL_FIffE (x211, x212)) = false
  | equal_hl_fitch_rule (HL_FIffE (x211, x212)) HL_FPremise = false
  | equal_hl_fitch_rule HL_FPremise (HL_FIffI (x201, x202)) = false
  | equal_hl_fitch_rule (HL_FIffI (x201, x202)) HL_FPremise = false
  | equal_hl_fitch_rule HL_FPremise (HL_FPropTaut x19) = false
  | equal_hl_fitch_rule (HL_FPropTaut x19) HL_FPremise = false
  | equal_hl_fitch_rule HL_FPremise HL_FLEM = false
  | equal_hl_fitch_rule HL_FLEM HL_FPremise = false
  | equal_hl_fitch_rule HL_FPremise (HL_FEqE (x171, x172)) = false
  | equal_hl_fitch_rule (HL_FEqE (x171, x172)) HL_FPremise = false
  | equal_hl_fitch_rule HL_FPremise HL_FEqI = false
  | equal_hl_fitch_rule HL_FEqI HL_FPremise = false
  | equal_hl_fitch_rule HL_FPremise (HL_FExistsE (x151, x152)) = false
  | equal_hl_fitch_rule (HL_FExistsE (x151, x152)) HL_FPremise = false
  | equal_hl_fitch_rule HL_FPremise (HL_FExistsI x14) = false
  | equal_hl_fitch_rule (HL_FExistsI x14) HL_FPremise = false
  | equal_hl_fitch_rule HL_FPremise (HL_FForallI x13) = false
  | equal_hl_fitch_rule (HL_FForallI x13) HL_FPremise = false
  | equal_hl_fitch_rule HL_FPremise (HL_FForallE x12) = false
  | equal_hl_fitch_rule (HL_FForallE x12) HL_FPremise = false
  | equal_hl_fitch_rule HL_FPremise (HL_FRAA x11) = false
  | equal_hl_fitch_rule (HL_FRAA x11) HL_FPremise = false
  | equal_hl_fitch_rule HL_FPremise (HL_FOrE (x101, x102, x103)) = false
  | equal_hl_fitch_rule (HL_FOrE (x101, x102, x103)) HL_FPremise = false
  | equal_hl_fitch_rule HL_FPremise (HL_FOrI x9) = false
  | equal_hl_fitch_rule (HL_FOrI x9) HL_FPremise = false
  | equal_hl_fitch_rule HL_FPremise (HL_FAndE x8) = false
  | equal_hl_fitch_rule (HL_FAndE x8) HL_FPremise = false
  | equal_hl_fitch_rule HL_FPremise (HL_FAndI (x71, x72)) = false
  | equal_hl_fitch_rule (HL_FAndI (x71, x72)) HL_FPremise = false
  | equal_hl_fitch_rule HL_FPremise (HL_FCP x6) = false
  | equal_hl_fitch_rule (HL_FCP x6) HL_FPremise = false
  | equal_hl_fitch_rule HL_FPremise (HL_FDN x5) = false
  | equal_hl_fitch_rule (HL_FDN x5) HL_FPremise = false
  | equal_hl_fitch_rule HL_FPremise (HL_FMT (x41, x42)) = false
  | equal_hl_fitch_rule (HL_FMT (x41, x42)) HL_FPremise = false
  | equal_hl_fitch_rule HL_FPremise (HL_FMP (x31, x32)) = false
  | equal_hl_fitch_rule (HL_FMP (x31, x32)) HL_FPremise = false
  | equal_hl_fitch_rule HL_FPremise HL_FAssume = false
  | equal_hl_fitch_rule HL_FAssume HL_FPremise = false
  | equal_hl_fitch_rule (HL_FReit x23) (HL_FReit y23) = equal_inta x23 y23
  | equal_hl_fitch_rule (HL_FQN x22) (HL_FQN y22) = equal_inta x22 y22
  | equal_hl_fitch_rule (HL_FIffE (x211, x212)) (HL_FIffE (y211, y212)) =
    equal_inta x211 y211 andalso equal_inta x212 y212
  | equal_hl_fitch_rule (HL_FIffI (x201, x202)) (HL_FIffI (y201, y202)) =
    equal_inta x201 y201 andalso equal_inta x202 y202
  | equal_hl_fitch_rule (HL_FPropTaut x19) (HL_FPropTaut y19) =
    equal_lista equal_int x19 y19
  | equal_hl_fitch_rule (HL_FEqE (x171, x172)) (HL_FEqE (y171, y172)) =
    equal_inta x171 y171 andalso equal_inta x172 y172
  | equal_hl_fitch_rule (HL_FExistsE (x151, x152)) (HL_FExistsE (y151, y152)) =
    equal_inta x151 y151 andalso equal_proda equal_int equal_int x152 y152
  | equal_hl_fitch_rule (HL_FExistsI x14) (HL_FExistsI y14) = equal_inta x14 y14
  | equal_hl_fitch_rule (HL_FForallI x13) (HL_FForallI y13) = equal_inta x13 y13
  | equal_hl_fitch_rule (HL_FForallE x12) (HL_FForallE y12) = equal_inta x12 y12
  | equal_hl_fitch_rule (HL_FRAA x11) (HL_FRAA y11) =
    equal_proda equal_int equal_int x11 y11
  | equal_hl_fitch_rule (HL_FOrE (x101, x102, x103))
    (HL_FOrE (y101, y102, y103)) =
    equal_inta x101 y101 andalso
      (equal_proda equal_int equal_int x102 y102 andalso
        equal_proda equal_int equal_int x103 y103)
  | equal_hl_fitch_rule (HL_FOrI x9) (HL_FOrI y9) = equal_inta x9 y9
  | equal_hl_fitch_rule (HL_FAndE x8) (HL_FAndE y8) = equal_inta x8 y8
  | equal_hl_fitch_rule (HL_FAndI (x71, x72)) (HL_FAndI (y71, y72)) =
    equal_inta x71 y71 andalso equal_inta x72 y72
  | equal_hl_fitch_rule (HL_FCP x6) (HL_FCP y6) =
    equal_proda equal_int equal_int x6 y6
  | equal_hl_fitch_rule (HL_FDN x5) (HL_FDN y5) = equal_inta x5 y5
  | equal_hl_fitch_rule (HL_FMT (x41, x42)) (HL_FMT (y41, y42)) =
    equal_inta x41 y41 andalso equal_inta x42 y42
  | equal_hl_fitch_rule (HL_FMP (x31, x32)) (HL_FMP (y31, y32)) =
    equal_inta x31 y31 andalso equal_inta x32 y32
  | equal_hl_fitch_rule HL_FLEM HL_FLEM = true
  | equal_hl_fitch_rule HL_FEqI HL_FEqI = true
  | equal_hl_fitch_rule HL_FAssume HL_FAssume = true
  | equal_hl_fitch_rule HL_FPremise HL_FPremise = true;

fun hlFitchPremiseNumbers [] = []
  | hlFitchPremiseNumbers (HL_FLine (n, p, r) :: rest) =
    (if equal_hl_fitch_rule r HL_FPremise then n :: hlFitchPremiseNumbers rest
      else hlFitchPremiseNumbers rest)
  | hlFitchPremiseNumbers (HL_FSub s :: rest) = hlFitchPremiseNumbers rest;

fun hlFitchScopeRecord scope [] = []
  | hlFitchScopeRecord scope (HL_FLine (n, p, r) :: rest) =
    (n, scope) :: hlFitchScopeRecord scope rest
  | hlFitchScopeRecord scope (HL_FSub (HL_Subproof (a, p, body)) :: rest) =
    (a, insert equal_int a scope) ::
      hlFitchScopeRecord (insert equal_int a scope) body @
        hlFitchScopeRecord scope rest;

fun hlFitchScopeOf f n =
  (case map_of equal_int (hlFitchScopeRecord (Set (hlFitchPremiseNumbers f)) f)
          n
    of NONE => bot_set | SOME scope => scope);

fun hlScopeSrc f p n g = hlFitchScopeOf f n;

fun plus_int k l =
  Int_of_integer (IntInf.+ (integer_of_int k, integer_of_int l));

val one_int : int = Int_of_integer (1 : IntInf.int);

fun hlNumberPremises next [] = []
  | hlNumberPremises next ((source, phi) :: premises) =
    (source, (next, phi)) :: hlNumberPremises (plus_int next one_int) premises;

fun hlPremisesOf (HL_Derivation (phi, r)) =
  (case r of HL_DAssume _ => [] | HL_DPremise i => [(i, phi)]
    | HL_DMP (d1, d2) => hlPremisesOf d1 @ hlPremisesOf d2
    | HL_DMT (d1, d2) => hlPremisesOf d1 @ hlPremisesOf d2
    | HL_DDN a => hlPremisesOf a | HL_DCP (_, _, a) => hlPremisesOf a
    | HL_DAndI (d1, d2) => hlPremisesOf d1 @ hlPremisesOf d2
    | HL_DAndE a => hlPremisesOf a | HL_DOrI a => hlPremisesOf a
    | HL_DOrE (d0, _, _, d1, _, _, d2) =>
      hlPremisesOf d0 @ hlPremisesOf d1 @ hlPremisesOf d2
    | HL_DRAA (_, _, a) => hlPremisesOf a | HL_DForallE a => hlPremisesOf a
    | HL_DForallI a => hlPremisesOf a | HL_DExistsI a => hlPremisesOf a
    | HL_DExistsE (d0, _, _, d) => hlPremisesOf d0 @ hlPremisesOf d
    | HL_DEqI => [] | HL_DEqE (d1, d2) => hlPremisesOf d1 @ hlPremisesOf d2
    | HL_DLEM => [] | HL_DPropTaut a => maps hlPremisesOf a
    | HL_DIffI (d1, d2) => hlPremisesOf d1 @ hlPremisesOf d2
    | HL_DIffE (d1, d2) => hlPremisesOf d1 @ hlPremisesOf d2
    | HL_DQN a => hlPremisesOf a);

fun hlPremiseEnvironment d =
  hlNumberPremises one_int
    (sort_key linorder_int fst
      (remdups (equal_prod equal_int equal_hl_formula) (hlPremisesOf d)));

fun hlDerivationFormulas (HL_Derivation (phi, r)) =
  phi ::
    (case r of HL_DAssume _ => [] | HL_DPremise _ => []
      | HL_DMP (d1, d2) => hlDerivationFormulas d1 @ hlDerivationFormulas d2
      | HL_DMT (d1, d2) => hlDerivationFormulas d1 @ hlDerivationFormulas d2
      | HL_DDN a => hlDerivationFormulas a
      | HL_DCP (_, p, d) => p :: hlDerivationFormulas d
      | HL_DAndI (d1, d2) => hlDerivationFormulas d1 @ hlDerivationFormulas d2
      | HL_DAndE a => hlDerivationFormulas a
      | HL_DOrI a => hlDerivationFormulas a
      | HL_DOrE (d0, _, p1, d1, _, p2, d2) =>
        p1 :: p2 :: hlDerivationFormulas d0 @
                      hlDerivationFormulas d1 @ hlDerivationFormulas d2
      | HL_DRAA (_, p, d) => p :: hlDerivationFormulas d
      | HL_DForallE a => hlDerivationFormulas a
      | HL_DForallI a => hlDerivationFormulas a
      | HL_DExistsI a => hlDerivationFormulas a
      | HL_DExistsE (d0, _, p, d) =>
        p :: hlDerivationFormulas d0 @ hlDerivationFormulas d
      | HL_DEqI => []
      | HL_DEqE (d1, d2) => hlDerivationFormulas d1 @ hlDerivationFormulas d2
      | HL_DLEM => [] | HL_DPropTaut a => maps hlDerivationFormulas a
      | HL_DIffI (d1, d2) => hlDerivationFormulas d1 @ hlDerivationFormulas d2
      | HL_DIffE (d1, d2) => hlDerivationFormulas d1 @ hlDerivationFormulas d2
      | HL_DQN a => hlDerivationFormulas a);

fun hlPremiseFitchLines env =
  map (fn (_, (n, phi)) => HL_FLine (n, phi, HL_FPremise)) env;

fun size_hl_derivation (HL_Derivation (x11, x12)) =
  plus_nat (size_hl_derivation_rule x12) (suc zero_nat)
and size_hl_derivation_rule (HL_DAssume x21) = zero_nat
  | size_hl_derivation_rule (HL_DPremise x22) = zero_nat
  | size_hl_derivation_rule (HL_DMP (x231, x232)) =
    plus_nat (plus_nat (size_hl_derivation x231) (size_hl_derivation x232))
      (suc zero_nat)
  | size_hl_derivation_rule (HL_DMT (x241, x242)) =
    plus_nat (plus_nat (size_hl_derivation x241) (size_hl_derivation x242))
      (suc zero_nat)
  | size_hl_derivation_rule (HL_DDN x25) =
    plus_nat (size_hl_derivation x25) (suc zero_nat)
  | size_hl_derivation_rule (HL_DCP (x261, x262, x263)) =
    plus_nat (size_hl_derivation x263) (suc zero_nat)
  | size_hl_derivation_rule (HL_DAndI (x271, x272)) =
    plus_nat (plus_nat (size_hl_derivation x271) (size_hl_derivation x272))
      (suc zero_nat)
  | size_hl_derivation_rule (HL_DAndE x28) =
    plus_nat (size_hl_derivation x28) (suc zero_nat)
  | size_hl_derivation_rule (HL_DOrI x29) =
    plus_nat (size_hl_derivation x29) (suc zero_nat)
  | size_hl_derivation_rule
    (HL_DOrE (x2101, x2102, x2103, x2104, x2105, x2106, x2107)) =
    plus_nat
      (plus_nat (plus_nat (size_hl_derivation x2101) (size_hl_derivation x2104))
        (size_hl_derivation x2107))
      (suc zero_nat)
  | size_hl_derivation_rule (HL_DRAA (x2111, x2112, x2113)) =
    plus_nat (size_hl_derivation x2113) (suc zero_nat)
  | size_hl_derivation_rule (HL_DForallE x212) =
    plus_nat (size_hl_derivation x212) (suc zero_nat)
  | size_hl_derivation_rule (HL_DForallI x213) =
    plus_nat (size_hl_derivation x213) (suc zero_nat)
  | size_hl_derivation_rule (HL_DExistsI x214) =
    plus_nat (size_hl_derivation x214) (suc zero_nat)
  | size_hl_derivation_rule (HL_DExistsE (x2151, x2152, x2153, x2154)) =
    plus_nat (plus_nat (size_hl_derivation x2151) (size_hl_derivation x2154))
      (suc zero_nat)
  | size_hl_derivation_rule HL_DEqI = zero_nat
  | size_hl_derivation_rule (HL_DEqE (x2171, x2172)) =
    plus_nat (plus_nat (size_hl_derivation x2171) (size_hl_derivation x2172))
      (suc zero_nat)
  | size_hl_derivation_rule HL_DLEM = zero_nat
  | size_hl_derivation_rule (HL_DPropTaut x219) =
    plus_nat (size_list size_hl_derivation x219) (suc zero_nat)
  | size_hl_derivation_rule (HL_DIffI (x2201, x2202)) =
    plus_nat (plus_nat (size_hl_derivation x2201) (size_hl_derivation x2202))
      (suc zero_nat)
  | size_hl_derivation_rule (HL_DIffE (x2211, x2212)) =
    plus_nat (plus_nat (size_hl_derivation x2211) (size_hl_derivation x2212))
      (suc zero_nat)
  | size_hl_derivation_rule (HL_DQN x222) =
    plus_nat (size_hl_derivation x222) (suc zero_nat);

fun hlDerivationFormula (HL_Derivation (x1, x2)) = x1;

fun hlConstantsInScope scope =
  sup_seta equal_literal (image hlConstantsInFormula (Set scope));

fun minus_set A_ a (Set xs) = fold (remove A_) xs a
  | minus_set A_ a (Coset xs) = Set (filtera (fn x => member A_ x a) xs);

fun inf_set A_ a (Set xs) = Set (filtera (fn x => member A_ x a) xs)
  | inf_set A_ a (Coset xs) = fold (remove A_) xs a;

fun hlForallRepairConstants scope goal d =
  sorted_list_of_set (equal_literal, linorder_literal)
    (inf_set equal_literal
      (minus_set equal_literal (hlConstantsInFormula (hlDerivationFormula d))
        (hlConstantsInFormula goal))
      (hlConstantsInScope scope));

fun hlExistsRepairConstants scope assumption source goal =
  sorted_list_of_set (equal_literal, linorder_literal)
    (inf_set equal_literal
      (minus_set equal_literal (hlConstantsInFormula assumption)
        (sup_set equal_literal
          (hlConstantsInFormula (hlDerivationFormula source))
          (hlConstantsInFormula goal)))
      (hlConstantsInScope scope));

fun hlEmitDerivationsUsing emit next count [] = ([], ([], (next, count)))
  | hlEmitDerivationsUsing emit next count (d :: ds) =
    let
      val (items, (n, (next1, count1))) = emit next count d;
      val (more, (numbers, (next2, count2))) =
        hlEmitDerivationsUsing emit next1 count1 ds;
    in
      (items @ more, (n :: numbers, (next2, count2)))
    end;

fun hlRenameTerm old new (HL_Var x) = HL_Var x
  | hlRenameTerm old new (HL_Const a) =
    HL_Const (if ((a : string) = old) then new else a);

fun hlRenameFormula old new (HL_Predicate (p, ts)) =
  HL_Predicate (p, map (hlRenameTerm old new) ts)
  | hlRenameFormula old new (HL_Boolean b) = HL_Boolean b
  | hlRenameFormula old new (HL_Not p) = HL_Not (hlRenameFormula old new p)
  | hlRenameFormula old new (HL_And (p, q)) =
    HL_And (hlRenameFormula old new p, hlRenameFormula old new q)
  | hlRenameFormula old new (HL_Or (p, q)) =
    HL_Or (hlRenameFormula old new p, hlRenameFormula old new q)
  | hlRenameFormula old new (HL_Implies (p, q)) =
    HL_Implies (hlRenameFormula old new p, hlRenameFormula old new q)
  | hlRenameFormula old new (HL_Iff (p, q)) =
    HL_Iff (hlRenameFormula old new p, hlRenameFormula old new q)
  | hlRenameFormula old new (HL_ForAll (x, p)) =
    HL_ForAll (x, hlRenameFormula old new p)
  | hlRenameFormula old new (HL_Exists (x, p)) =
    HL_Exists (x, hlRenameFormula old new p);

fun hlRenamePairsFormula [] p = p
  | hlRenamePairsFormula ((old, new) :: pairs) p =
    hlRenamePairsFormula pairs (hlRenameFormula old new p);

fun hlRenameDerivation old new (HL_Derivation (phi, r)) =
  HL_Derivation
    (hlRenameFormula old new phi,
      (case r of HL_DAssume a => HL_DAssume a | HL_DPremise a => HL_DPremise a
        | HL_DMP (d1, d2) =>
          HL_DMP (hlRenameDerivation old new d1, hlRenameDerivation old new d2)
        | HL_DMT (d1, d2) =>
          HL_DMT (hlRenameDerivation old new d1, hlRenameDerivation old new d2)
        | HL_DDN d => HL_DDN (hlRenameDerivation old new d)
        | HL_DCP (i, p, d) =>
          HL_DCP (i, hlRenameFormula old new p, hlRenameDerivation old new d)
        | HL_DAndI (d1, d2) =>
          HL_DAndI
            (hlRenameDerivation old new d1, hlRenameDerivation old new d2)
        | HL_DAndE d => HL_DAndE (hlRenameDerivation old new d)
        | HL_DOrI d => HL_DOrI (hlRenameDerivation old new d)
        | HL_DOrE (d0, a1, p1, d1, a2, p2, d2) =>
          HL_DOrE
            (hlRenameDerivation old new d0, a1, hlRenameFormula old new p1,
              hlRenameDerivation old new d1, a2, hlRenameFormula old new p2,
              hlRenameDerivation old new d2)
        | HL_DRAA (i, p, d) =>
          HL_DRAA (i, hlRenameFormula old new p, hlRenameDerivation old new d)
        | HL_DForallE d => HL_DForallE (hlRenameDerivation old new d)
        | HL_DForallI d => HL_DForallI (hlRenameDerivation old new d)
        | HL_DExistsI d => HL_DExistsI (hlRenameDerivation old new d)
        | HL_DExistsE (d0, i, p, d) =>
          HL_DExistsE
            (hlRenameDerivation old new d0, i, hlRenameFormula old new p,
              hlRenameDerivation old new d)
        | HL_DEqI => HL_DEqI
        | HL_DEqE (d1, d2) =>
          HL_DEqE (hlRenameDerivation old new d1, hlRenameDerivation old new d2)
        | HL_DLEM => HL_DLEM
        | HL_DPropTaut ds => HL_DPropTaut (map (hlRenameDerivation old new) ds)
        | HL_DIffI (d1, d2) =>
          HL_DIffI
            (hlRenameDerivation old new d1, hlRenameDerivation old new d2)
        | HL_DIffE (d1, d2) =>
          HL_DIffE
            (hlRenameDerivation old new d1, hlRenameDerivation old new d2)
        | HL_DQN d => HL_DQN (hlRenameDerivation old new d)));

fun hlFreshIndex base k =
  implode
    (replicate (plus_nat base k)
      (Chara (true, true, false, false, false, true, true, false)));

fun hlRepairDerivation base count [] d = (count, ([], d))
  | hlRepairDerivation base count (old :: olds) d =
    let
      val new = hlFreshIndex base count;
      val da = hlRenameDerivation old new d;
      val (counta, (pairs, result)) =
        hlRepairDerivation base (suc count) olds da;
    in
      (counta, ((old, new) :: pairs, result))
    end;

fun hlEnvironmentLine [] source = zero_int
  | hlEnvironmentLine ((i, (n, p)) :: env) source =
    (if equal_inta i source then n else hlEnvironmentLine env source);

fun hlEmitDerivationFuel [] base env scope next count d =
  ([], (zero_int, (next, count)))
  | hlEmitDerivationFuel (uu :: fuel) base env scope next count
    (HL_Derivation (phi, rule)) =
    (case rule of HL_DAssume i => ([], (hlEnvironmentLine env i, (next, count)))
      | HL_DPremise i => ([], (hlEnvironmentLine env i, (next, count)))
      | HL_DMP (d1, d2) =>
        let
          val (items1, (n1, (next1, count1))) =
            hlEmitDerivationFuel fuel base env scope next count d1;
          val (items2, (n2, (next2, count2))) =
            hlEmitDerivationFuel fuel base env scope next1 count1 d2;
        in
          (items1 @ items2 @ [HL_FLine (next2, phi, HL_FMP (n1, n2))],
            (next2, (plus_int next2 one_int, count2)))
        end
      | HL_DMT (d1, d2) =>
        let
          val (items1, (n1, (next1, count1))) =
            hlEmitDerivationFuel fuel base env scope next count d1;
          val (items2, (n2, (next2, count2))) =
            hlEmitDerivationFuel fuel base env scope next1 count1 d2;
        in
          (items1 @ items2 @ [HL_FLine (next2, phi, HL_FMT (n1, n2))],
            (next2, (plus_int next2 one_int, count2)))
        end
      | HL_DDN d =>
        let
          val (items, (n, (nexta, counta))) =
            hlEmitDerivationFuel fuel base env scope next count d;
        in
          (items @ [HL_FLine (nexta, phi, HL_FDN n)],
            (nexta, (plus_int nexta one_int, counta)))
        end
      | HL_DCP (a, af, body) =>
        let
          val assumptionLine = next;
          val (bodyItems, (bodyLine, (next1, count1))) =
            hlEmitDerivationFuel fuel base ((a, (assumptionLine, af)) :: env)
              (af :: scope) (plus_int next one_int) count body;
          val needsReiteration =
            null bodyItems andalso not (equal_inta bodyLine assumptionLine);
          val closedBody =
            (if needsReiteration
              then [HL_FLine
                      (next1, hlDerivationFormula body, HL_FReit bodyLine)]
              else bodyItems);
          val lastLine = (if needsReiteration then next1 else bodyLine);
          val afterBox =
            (if needsReiteration then plus_int next1 one_int else next1);
        in
          ([HL_FSub (HL_Subproof (assumptionLine, af, closedBody)),
             HL_FLine (afterBox, phi, HL_FCP (assumptionLine, lastLine))],
            (afterBox, (plus_int afterBox one_int, count1)))
        end
      | HL_DAndI (d1, d2) =>
        let
          val (items1, (n1, (next1, count1))) =
            hlEmitDerivationFuel fuel base env scope next count d1;
          val (items2, (n2, (next2, count2))) =
            hlEmitDerivationFuel fuel base env scope next1 count1 d2;
        in
          (items1 @ items2 @ [HL_FLine (next2, phi, HL_FAndI (n1, n2))],
            (next2, (plus_int next2 one_int, count2)))
        end
      | HL_DAndE d =>
        let
          val (items, (n, (nexta, counta))) =
            hlEmitDerivationFuel fuel base env scope next count d;
        in
          (items @ [HL_FLine (nexta, phi, HL_FAndE n)],
            (nexta, (plus_int nexta one_int, counta)))
        end
      | HL_DOrI d =>
        let
          val (items, (n, (nexta, counta))) =
            hlEmitDerivationFuel fuel base env scope next count d;
        in
          (items @ [HL_FLine (nexta, phi, HL_FOrI n)],
            (nexta, (plus_int nexta one_int, counta)))
        end
      | HL_DOrE (d0, a1, f1, b1, a2, f2, b2) =>
        let
          val (items0, (n0, (next0, count0))) =
            hlEmitDerivationFuel fuel base env scope next count d0;
          val assumption1 = next0;
          val (body1, (line1, (next1, count1))) =
            hlEmitDerivationFuel fuel base ((a1, (assumption1, f1)) :: env)
              (f1 :: scope) (plus_int next0 one_int) count0 b1;
          val reiterate1 =
            null body1 andalso not (equal_inta line1 assumption1);
          val closed1 =
            (if reiterate1
              then [HL_FLine (next1, hlDerivationFormula b1, HL_FReit line1)]
              else body1);
          val last1 = (if reiterate1 then next1 else line1);
          val after1 = (if reiterate1 then plus_int next1 one_int else next1);
          val assumption2 = after1;
          val (body2, (line2, (next2, count2))) =
            hlEmitDerivationFuel fuel base ((a2, (assumption2, f2)) :: env)
              (f2 :: scope) (plus_int after1 one_int) count1 b2;
          val reiterate2 =
            null body2 andalso not (equal_inta line2 assumption2);
          val closed2 =
            (if reiterate2
              then [HL_FLine (next2, hlDerivationFormula b2, HL_FReit line2)]
              else body2);
          val last2 = (if reiterate2 then next2 else line2);
          val after2 = (if reiterate2 then plus_int next2 one_int else next2);
        in
          (items0 @
             [HL_FSub (HL_Subproof (assumption1, f1, closed1)),
               HL_FSub (HL_Subproof (assumption2, f2, closed2)),
               HL_FLine
                 (after2, phi,
                   HL_FOrE (n0, (assumption1, last1), (assumption2, last2)))],
            (after2, (plus_int after2 one_int, count2)))
        end
      | HL_DRAA (a, af, body) =>
        let
          val assumptionLine = next;
          val (bodyItems, (bodyLine, (next1, count1))) =
            hlEmitDerivationFuel fuel base ((a, (assumptionLine, af)) :: env)
              (af :: scope) (plus_int next one_int) count body;
          val needsReiteration =
            null bodyItems andalso not (equal_inta bodyLine assumptionLine);
          val closedBody =
            (if needsReiteration
              then [HL_FLine
                      (next1, hlDerivationFormula body, HL_FReit bodyLine)]
              else bodyItems);
          val lastLine = (if needsReiteration then next1 else bodyLine);
          val afterBox =
            (if needsReiteration then plus_int next1 one_int else next1);
        in
          ([HL_FSub (HL_Subproof (assumptionLine, af, closedBody)),
             HL_FLine (afterBox, phi, HL_FRAA (assumptionLine, lastLine))],
            (afterBox, (plus_int afterBox one_int, count1)))
        end
      | HL_DForallE d =>
        let
          val (items, (n, (nexta, counta))) =
            hlEmitDerivationFuel fuel base env scope next count d;
        in
          (items @ [HL_FLine (nexta, phi, HL_FForallE n)],
            (nexta, (plus_int nexta one_int, counta)))
        end
      | HL_DForallI d =>
        let
          val bad = hlForallRepairConstants scope phi d;
          val (count0, (_, repaired)) = hlRepairDerivation base count bad d;
          val (items, (n, (nexta, counta))) =
            hlEmitDerivationFuel fuel base env scope next count0 repaired;
        in
          (items @ [HL_FLine (nexta, phi, HL_FForallI n)],
            (nexta, (plus_int nexta one_int, counta)))
        end
      | HL_DExistsI d =>
        let
          val (items, (n, (nexta, counta))) =
            hlEmitDerivationFuel fuel base env scope next count d;
        in
          (items @ [HL_FLine (nexta, phi, HL_FExistsI n)],
            (nexta, (plus_int nexta one_int, counta)))
        end
      | HL_DExistsE (source, a, af, body) =>
        let
          val (sourceItems, (sourceLine, (next0, count0))) =
            hlEmitDerivationFuel fuel base env scope next count source;
          val bad = hlExistsRepairConstants scope af source phi;
          val (countR, (pairs, repairedBody)) =
            hlRepairDerivation base count0 bad body;
          val repairedAssumption = hlRenamePairsFormula pairs af;
          val assumptionLine = next0;
          val (bodyItems, (bodyLine, (next1, count1))) =
            hlEmitDerivationFuel fuel base
              ((a, (assumptionLine, repairedAssumption)) :: env)
              (repairedAssumption :: scope) (plus_int next0 one_int) countR
              repairedBody;
          val needsReiteration =
            null bodyItems andalso not (equal_inta bodyLine assumptionLine);
          val closedBody =
            (if needsReiteration
              then [HL_FLine
                      (next1, hlDerivationFormula repairedBody,
                        HL_FReit bodyLine)]
              else bodyItems);
          val lastLine = (if needsReiteration then next1 else bodyLine);
          val afterBox =
            (if needsReiteration then plus_int next1 one_int else next1);
        in
          (sourceItems @
             [HL_FSub
                (HL_Subproof (assumptionLine, repairedAssumption, closedBody)),
               HL_FLine
                 (afterBox, phi,
                   HL_FExistsE (sourceLine, (assumptionLine, lastLine)))],
            (afterBox, (plus_int afterBox one_int, count1)))
        end
      | HL_DEqI =>
        ([HL_FLine (next, phi, HL_FEqI)],
          (next, (plus_int next one_int, count)))
      | HL_DEqE (d1, d2) =>
        let
          val (items1, (n1, (next1, count1))) =
            hlEmitDerivationFuel fuel base env scope next count d1;
          val (items2, (n2, (next2, count2))) =
            hlEmitDerivationFuel fuel base env scope next1 count1 d2;
        in
          (items1 @ items2 @ [HL_FLine (next2, phi, HL_FEqE (n1, n2))],
            (next2, (plus_int next2 one_int, count2)))
        end
      | HL_DLEM =>
        ([HL_FLine (next, phi, HL_FLEM)],
          (next, (plus_int next one_int, count)))
      | HL_DPropTaut ds =>
        let
          val (items, (numbers, (nexta, counta))) =
            hlEmitDerivationsUsing (hlEmitDerivationFuel fuel base env scope)
              next count ds;
        in
          (items @ [HL_FLine (nexta, phi, HL_FPropTaut numbers)],
            (nexta, (plus_int nexta one_int, counta)))
        end
      | HL_DIffI (d1, d2) =>
        let
          val (items1, (n1, (next1, count1))) =
            hlEmitDerivationFuel fuel base env scope next count d1;
          val (items2, (n2, (next2, count2))) =
            hlEmitDerivationFuel fuel base env scope next1 count1 d2;
        in
          (items1 @ items2 @ [HL_FLine (next2, phi, HL_FIffI (n1, n2))],
            (next2, (plus_int next2 one_int, count2)))
        end
      | HL_DIffE (d1, d2) =>
        let
          val (items1, (n1, (next1, count1))) =
            hlEmitDerivationFuel fuel base env scope next count d1;
          val (items2, (n2, (next2, count2))) =
            hlEmitDerivationFuel fuel base env scope next1 count1 d2;
        in
          (items1 @ items2 @ [HL_FLine (next2, phi, HL_FIffE (n1, n2))],
            (next2, (plus_int next2 one_int, count2)))
        end
      | HL_DQN d =>
        let
          val (items, (n, (nexta, counta))) =
            hlEmitDerivationFuel fuel base env scope next count d;
        in
          (items @ [HL_FLine (nexta, phi, HL_FQN n)],
            (nexta, (plus_int nexta one_int, counta)))
        end);

fun hlEmitDerivation base env scope next count d =
  hlEmitDerivationFuel (replicate (suc (size_hl_derivation d)) ()) base env
    scope next count d;

fun int_of_nat n = Int_of_integer (integer_of_nat n);

fun hlDerivationToFitch d =
  let
    val env = hlPremiseEnvironment d;
    val premiseLines = hlPremiseFitchLines env;
    val base =
      suc (maxlen
            (sorted_list_of_set (equal_literal, linorder_literal)
              (sup_seta equal_literal
                (image hlConstantsInFormula (Set (hlDerivationFormulas d))))));
    val (body, (_, (_, _))) =
      hlEmitDerivation base env (map (fn (_, (_, phi)) => phi) env)
        (plus_int one_int (int_of_nat (size_lista env))) zero_nat d;
  in
    premiseLines @ body
  end;

fun hlClassifyAssumptions bound (HL_Derivation (phi, rule)) =
  HL_Derivation
    (phi, (case rule
            of HL_DAssume i =>
              (if member equal_int i bound then HL_DAssume i else HL_DPremise i)
            | HL_DPremise i =>
              (if member equal_int i bound then HL_DAssume i else HL_DPremise i)
            | HL_DMP (d1, d2) =>
              HL_DMP
                (hlClassifyAssumptions bound d1, hlClassifyAssumptions bound d2)
            | HL_DMT (d1, d2) =>
              HL_DMT
                (hlClassifyAssumptions bound d1, hlClassifyAssumptions bound d2)
            | HL_DDN d => HL_DDN (hlClassifyAssumptions bound d)
            | HL_DCP (i, p, d) =>
              HL_DCP (i, p, hlClassifyAssumptions (insert equal_int i bound) d)
            | HL_DAndI (d1, d2) =>
              HL_DAndI
                (hlClassifyAssumptions bound d1, hlClassifyAssumptions bound d2)
            | HL_DAndE d => HL_DAndE (hlClassifyAssumptions bound d)
            | HL_DOrI d => HL_DOrI (hlClassifyAssumptions bound d)
            | HL_DOrE (d0, a1, p1, d1, a2, p2, d2) =>
              HL_DOrE
                (hlClassifyAssumptions bound d0, a1, p1,
                  hlClassifyAssumptions (insert equal_int a1 bound) d1, a2, p2,
                  hlClassifyAssumptions (insert equal_int a2 bound) d2)
            | HL_DRAA (i, p, d) =>
              HL_DRAA (i, p, hlClassifyAssumptions (insert equal_int i bound) d)
            | HL_DForallE d => HL_DForallE (hlClassifyAssumptions bound d)
            | HL_DForallI d => HL_DForallI (hlClassifyAssumptions bound d)
            | HL_DExistsI d => HL_DExistsI (hlClassifyAssumptions bound d)
            | HL_DExistsE (d0, i, p, d) =>
              HL_DExistsE
                (hlClassifyAssumptions bound d0, i, p,
                  hlClassifyAssumptions (insert equal_int i bound) d)
            | HL_DEqI => HL_DEqI
            | HL_DEqE (d1, d2) =>
              HL_DEqE
                (hlClassifyAssumptions bound d1, hlClassifyAssumptions bound d2)
            | HL_DLEM => HL_DLEM
            | HL_DPropTaut ds =>
              HL_DPropTaut (map (hlClassifyAssumptions bound) ds)
            | HL_DIffI (d1, d2) =>
              HL_DIffI
                (hlClassifyAssumptions bound d1, hlClassifyAssumptions bound d2)
            | HL_DIffE (d1, d2) =>
              HL_DIffE
                (hlClassifyAssumptions bound d1, hlClassifyAssumptions bound d2)
            | HL_DQN d => HL_DQN (hlClassifyAssumptions bound d)));

fun hlBoxesOf p = maps (hlDischargePairs o hlJustification) p;

fun hlDischargedAssumptions p = map fst (hlBoxesOf p);

fun hlSequenceOptions [] = SOME []
  | hlSequenceOptions (NONE :: xs) = NONE
  | hlSequenceOptions (SOME x :: xs) =
    map_option (fn a => x :: a) (hlSequenceOptions xs);

fun hlUnfoldDerivation fuel p n =
  (if equal_nata fuel zero_nat then NONE
    else (case hlLookupLine p n of NONE => NONE
           | SOME l =>
             let
               val phi = hlFormula l;
               val node = (fn a => HL_Derivation (phi, a));
             in
               (case hlJustification l
                 of HL_Assumption =>
                   SOME (node (if membera equal_int (hlDischargedAssumptions p)
                                    n
                                then HL_DAssume n else HL_DPremise n))
                 | HL_MP (m, k) =>
                   (case (hlUnfoldDerivation (minus_nat fuel one_nat) p m,
                           hlUnfoldDerivation (minus_nat fuel one_nat) p k)
                     of (NONE, _) => NONE | (SOME _, NONE) => NONE
                     | (SOME d1, SOME d2) => SOME (node (HL_DMP (d1, d2))))
                 | HL_MT (m, k) =>
                   (case (hlUnfoldDerivation (minus_nat fuel one_nat) p m,
                           hlUnfoldDerivation (minus_nat fuel one_nat) p k)
                     of (NONE, _) => NONE | (SOME _, NONE) => NONE
                     | (SOME d1, SOME d2) => SOME (node (HL_DMT (d1, d2))))
                 | HL_DN m =>
                   map_option (node o HL_DDN)
                     (hlUnfoldDerivation (minus_nat fuel one_nat) p m)
                 | HL_CP (a, c) =>
                   (case (hlFormulaAt p a,
                           hlUnfoldDerivation (minus_nat fuel one_nat) p c)
                     of (NONE, _) => NONE | (SOME _, NONE) => NONE
                     | (SOME assumption, SOME body) =>
                       SOME (node (HL_DCP (a, assumption, body))))
                 | HL_AndIntro (m, k) =>
                   (case (hlUnfoldDerivation (minus_nat fuel one_nat) p m,
                           hlUnfoldDerivation (minus_nat fuel one_nat) p k)
                     of (NONE, _) => NONE | (SOME _, NONE) => NONE
                     | (SOME d1, SOME d2) => SOME (node (HL_DAndI (d1, d2))))
                 | HL_AndElim m =>
                   map_option (node o HL_DAndE)
                     (hlUnfoldDerivation (minus_nat fuel one_nat) p m)
                 | HL_OrIntro m =>
                   map_option (node o HL_DOrI)
                     (hlUnfoldDerivation (minus_nat fuel one_nat) p m)
                 | HL_OrElim (d, a1, c1, a2, c2) =>
                   (case (hlUnfoldDerivation (minus_nat fuel one_nat) p d,
                           (hlFormulaAt p a1,
                             (hlUnfoldDerivation (minus_nat fuel one_nat) p c1,
                               (hlFormulaAt p a2,
                                 hlUnfoldDerivation (minus_nat fuel one_nat) p
                                   c2))))
                     of (NONE, _) => NONE | (SOME _, (NONE, _)) => NONE
                     | (SOME _, (SOME _, (NONE, _))) => NONE
                     | (SOME _, (SOME _, (SOME _, (NONE, _)))) => NONE
                     | (SOME _, (SOME _, (SOME _, (SOME _, NONE)))) => NONE
                     | (SOME dd, (SOME f1, (SOME b1, (SOME f2, SOME b2)))) =>
                       SOME (node (HL_DOrE (dd, a1, f1, b1, a2, f2, b2))))
                 | HL_RAA (a, c) =>
                   (case (hlFormulaAt p a,
                           hlUnfoldDerivation (minus_nat fuel one_nat) p c)
                     of (NONE, _) => NONE | (SOME _, NONE) => NONE
                     | (SOME assumption, SOME body) =>
                       SOME (node (HL_DRAA (a, assumption, body))))
                 | HL_ForallElim m =>
                   map_option (node o HL_DForallE)
                     (hlUnfoldDerivation (minus_nat fuel one_nat) p m)
                 | HL_ExistsIntro m =>
                   map_option (node o HL_DExistsI)
                     (hlUnfoldDerivation (minus_nat fuel one_nat) p m)
                 | HL_ForallIntro m =>
                   map_option (node o HL_DForallI)
                     (hlUnfoldDerivation (minus_nat fuel one_nat) p m)
                 | HL_ExistsElim (m, a, c) =>
                   (case (hlUnfoldDerivation (minus_nat fuel one_nat) p m,
                           (hlFormulaAt p a,
                             hlUnfoldDerivation (minus_nat fuel one_nat) p c))
                     of (NONE, _) => NONE | (SOME _, (NONE, _)) => NONE
                     | (SOME _, (SOME _, NONE)) => NONE
                     | (SOME source, (SOME assumption, SOME body)) =>
                       SOME (node (HL_DExistsE (source, a, assumption, body))))
                 | HL_EqIntro => SOME (node HL_DEqI)
                 | HL_EqElim (m, k) =>
                   (case (hlUnfoldDerivation (minus_nat fuel one_nat) p m,
                           hlUnfoldDerivation (minus_nat fuel one_nat) p k)
                     of (NONE, _) => NONE | (SOME _, NONE) => NONE
                     | (SOME d1, SOME d2) => SOME (node (HL_DEqE (d1, d2))))
                 | HL_LEM => SOME (node HL_DLEM)
                 | HL_PropTaut ms =>
                   map_option (node o HL_DPropTaut)
                     (hlSequenceOptions
                       (map (hlUnfoldDerivation (minus_nat fuel one_nat) p) ms))
                 | HL_IffIntro (m, k) =>
                   (case (hlUnfoldDerivation (minus_nat fuel one_nat) p m,
                           hlUnfoldDerivation (minus_nat fuel one_nat) p k)
                     of (NONE, _) => NONE | (SOME _, NONE) => NONE
                     | (SOME d1, SOME d2) => SOME (node (HL_DIffI (d1, d2))))
                 | HL_IffElim (m, k) =>
                   (case (hlUnfoldDerivation (minus_nat fuel one_nat) p m,
                           hlUnfoldDerivation (minus_nat fuel one_nat) p k)
                     of (NONE, _) => NONE | (SOME _, NONE) => NONE
                     | (SOME d1, SOME d2) => SOME (node (HL_DIffE (d1, d2))))
                 | HL_QN m =>
                   map_option (node o HL_DQN)
                     (hlUnfoldDerivation (minus_nat fuel one_nat) p m))
             end));

fun hlDependencyClosed p =
  list_all
    (fn l =>
      less_eq_set equal_int (hlReferences l)
        (image hlLineNumber
          (filter
            (fn a => equal_hl_justification (hlJustification a) HL_Assumption)
            (Set p))))
    p;

fun hlVerifiedCorrect p =
  hlCorrect p andalso (hlDependencyClosed p andalso hlCanonicalOrder p);

fun hlToDerivation p =
  (if null p orelse not (hlVerifiedCorrect p) then NONE
    else map_option (hlClassifyAssumptions bot_set)
           (hlUnfoldDerivation (suc (size_lista p)) p (hlLineNumber (last p))));

fun hlFitchCitedLines HL_FPremise = []
  | hlFitchCitedLines HL_FAssume = []
  | hlFitchCitedLines (HL_FMP (m, n)) = [m, n]
  | hlFitchCitedLines (HL_FMT (m, n)) = [m, n]
  | hlFitchCitedLines (HL_FDN m) = [m]
  | hlFitchCitedLines (HL_FCP s) = []
  | hlFitchCitedLines (HL_FAndI (m, n)) = [m, n]
  | hlFitchCitedLines (HL_FAndE m) = [m]
  | hlFitchCitedLines (HL_FOrI m) = [m]
  | hlFitchCitedLines (HL_FOrE (d, s1, s2)) = [d]
  | hlFitchCitedLines (HL_FRAA s) = []
  | hlFitchCitedLines (HL_FForallE m) = [m]
  | hlFitchCitedLines (HL_FForallI m) = [m]
  | hlFitchCitedLines (HL_FExistsI m) = [m]
  | hlFitchCitedLines (HL_FExistsE (m, s)) = [m]
  | hlFitchCitedLines HL_FEqI = []
  | hlFitchCitedLines (HL_FEqE (m, n)) = [m, n]
  | hlFitchCitedLines HL_FLEM = []
  | hlFitchCitedLines (HL_FPropTaut ms) = ms
  | hlFitchCitedLines (HL_FIffI (m, n)) = [m, n]
  | hlFitchCitedLines (HL_FIffE (m, n)) = [m, n]
  | hlFitchCitedLines (HL_FQN m) = [m]
  | hlFitchCitedLines (HL_FReit m) = [m];

fun hlFitchDependenciesOf look r self =
  (case r of HL_FPremise => insert equal_int self bot_set
    | HL_FAssume => insert equal_int self bot_set
    | HL_FMP (_, _) => sup_seta equal_int (Set (map look (hlFitchCitedLines r)))
    | HL_FMT (_, _) => sup_seta equal_int (Set (map look (hlFitchCitedLines r)))
    | HL_FDN _ => sup_seta equal_int (Set (map look (hlFitchCitedLines r)))
    | HL_FCP (a, c) => remove equal_int a (look c)
    | HL_FAndI (_, _) =>
      sup_seta equal_int (Set (map look (hlFitchCitedLines r)))
    | HL_FAndE _ => sup_seta equal_int (Set (map look (hlFitchCitedLines r)))
    | HL_FOrI _ => sup_seta equal_int (Set (map look (hlFitchCitedLines r)))
    | HL_FOrE (d, (a1, c1), (a2, c2)) =>
      sup_set equal_int
        (sup_set equal_int (look d) (remove equal_int a1 (look c1)))
        (remove equal_int a2 (look c2))
    | HL_FRAA (a, c) => remove equal_int a (look c)
    | HL_FForallE _ => sup_seta equal_int (Set (map look (hlFitchCitedLines r)))
    | HL_FForallI _ => sup_seta equal_int (Set (map look (hlFitchCitedLines r)))
    | HL_FExistsI _ => sup_seta equal_int (Set (map look (hlFitchCitedLines r)))
    | HL_FExistsE (m, (a, c)) =>
      sup_set equal_int (look m) (remove equal_int a (look c))
    | HL_FEqI => sup_seta equal_int (Set (map look (hlFitchCitedLines r)))
    | HL_FEqE (_, _) =>
      sup_seta equal_int (Set (map look (hlFitchCitedLines r)))
    | HL_FLEM => sup_seta equal_int (Set (map look (hlFitchCitedLines r)))
    | HL_FPropTaut _ =>
      sup_seta equal_int (Set (map look (hlFitchCitedLines r)))
    | HL_FIffI (_, _) =>
      sup_seta equal_int (Set (map look (hlFitchCitedLines r)))
    | HL_FIffE (_, _) =>
      sup_seta equal_int (Set (map look (hlFitchCitedLines r)))
    | HL_FQN _ => sup_seta equal_int (Set (map look (hlFitchCitedLines r)))
    | HL_FReit _ => sup_seta equal_int (Set (map look (hlFitchCitedLines r))));

fun hlDependencyLookup [] n = bot_set
  | hlDependencyLookup ((m, g) :: env) n =
    (if equal_inta m n then g else hlDependencyLookup env n);

fun hlToLemmonRule HL_FPremise = HL_Assumption
  | hlToLemmonRule HL_FAssume = HL_Assumption
  | hlToLemmonRule (HL_FMP (m, n)) = HL_MP (m, n)
  | hlToLemmonRule (HL_FMT (m, n)) = HL_MT (m, n)
  | hlToLemmonRule (HL_FDN m) = HL_DN m
  | hlToLemmonRule (HL_FCP (a, c)) = HL_CP (a, c)
  | hlToLemmonRule (HL_FAndI (m, n)) = HL_AndIntro (m, n)
  | hlToLemmonRule (HL_FAndE m) = HL_AndElim m
  | hlToLemmonRule (HL_FOrI m) = HL_OrIntro m
  | hlToLemmonRule (HL_FOrE (d, (a1, c1), (a2, c2))) =
    HL_OrElim (d, a1, c1, a2, c2)
  | hlToLemmonRule (HL_FRAA (a, c)) = HL_RAA (a, c)
  | hlToLemmonRule (HL_FForallE m) = HL_ForallElim m
  | hlToLemmonRule (HL_FForallI m) = HL_ForallIntro m
  | hlToLemmonRule (HL_FExistsI m) = HL_ExistsIntro m
  | hlToLemmonRule (HL_FExistsE (m, (a, c))) = HL_ExistsElim (m, a, c)
  | hlToLemmonRule HL_FEqI = HL_EqIntro
  | hlToLemmonRule (HL_FEqE (m, n)) = HL_EqElim (m, n)
  | hlToLemmonRule HL_FLEM = HL_LEM
  | hlToLemmonRule (HL_FPropTaut ms) = HL_PropTaut ms
  | hlToLemmonRule (HL_FIffI (m, n)) = HL_IffIntro (m, n)
  | hlToLemmonRule (HL_FIffE (m, n)) = HL_IffElim (m, n)
  | hlToLemmonRule (HL_FQN m) = HL_QN m
  | hlToLemmonRule (HL_FReit m) = HL_PropTaut [m];

fun hlFitchToLemmonFrom env [] = (env, [])
  | hlFitchToLemmonFrom env ((n, (p, r)) :: ls) =
    let
      val g = hlFitchDependenciesOf (hlDependencyLookup env) r n;
      val line = HL_ProofLine (n, p, hlToLemmonRule r, g);
      val (enva, tail) = hlFitchToLemmonFrom ((n, g) :: env) ls;
    in
      (enva, line :: tail)
    end;

fun hlFlattenFitch [] = []
  | hlFlattenFitch (i :: is) = hlFlattenFitchItem i @ hlFlattenFitch is
and hlFlattenFitchItem (HL_FLine (n, p, r)) = [(n, (p, r))]
  | hlFlattenFitchItem (HL_FSub (HL_Subproof (a, p, body))) =
    (a, (p, HL_FAssume)) :: hlFlattenFitch body;

fun hlFitchToLemmon f = snd (hlFitchToLemmonFrom [] (hlFlattenFitch f));

fun hlFitchPremises [] = []
  | hlFitchPremises (HL_FLine (n, p, r) :: rest) =
    (if equal_hl_fitch_rule r HL_FPremise then p :: hlFitchPremises rest
      else hlFitchPremises rest)
  | hlFitchPremises (HL_FSub s :: rest) = hlFitchPremises rest;

fun hlFitchPremisesFirst f =
  list_all (fn (_, (_, r)) => not (equal_hl_fitch_rule r HL_FPremise))
    (dropWhile (fn (_, (_, r)) => equal_hl_fitch_rule r HL_FPremise)
      (hlFlattenFitch f));

fun hlFitchCitedSubs (HL_FCP s) = [s]
  | hlFitchCitedSubs (HL_FRAA s) = [s]
  | hlFitchCitedSubs (HL_FOrE (uu, s1, s2)) = [s1, s2]
  | hlFitchCitedSubs (HL_FExistsE (uv, s)) = [s]
  | hlFitchCitedSubs HL_FPremise = []
  | hlFitchCitedSubs HL_FAssume = []
  | hlFitchCitedSubs (HL_FMP (v, va)) = []
  | hlFitchCitedSubs (HL_FMT (v, va)) = []
  | hlFitchCitedSubs (HL_FDN v) = []
  | hlFitchCitedSubs (HL_FAndI (v, va)) = []
  | hlFitchCitedSubs (HL_FAndE v) = []
  | hlFitchCitedSubs (HL_FOrI v) = []
  | hlFitchCitedSubs (HL_FForallE v) = []
  | hlFitchCitedSubs (HL_FForallI v) = []
  | hlFitchCitedSubs (HL_FExistsI v) = []
  | hlFitchCitedSubs HL_FEqI = []
  | hlFitchCitedSubs (HL_FEqE (v, va)) = []
  | hlFitchCitedSubs HL_FLEM = []
  | hlFitchCitedSubs (HL_FPropTaut v) = []
  | hlFitchCitedSubs (HL_FIffI (v, va)) = []
  | hlFitchCitedSubs (HL_FIffE (v, va)) = []
  | hlFitchCitedSubs (HL_FQN v) = []
  | hlFitchCitedSubs (HL_FReit v) = [];

fun hlConcludesAtTop f =
  null f orelse
    (case last f of HL_FLine (_, _, _) => true | HL_FSub _ => false);

fun hlFitchLineNumbers [] = []
  | hlFitchLineNumbers (i :: is) =
    hlFitchItemLineNumbers i @ hlFitchLineNumbers is
and hlFitchItemLineNumbers (HL_FLine (n, p, r)) = [n]
  | hlFitchItemLineNumbers (HL_FSub (HL_Subproof (a, p, body))) =
    a :: hlFitchLineNumbers body;

fun hlSubLastLine (HL_Subproof (a, p, body)) =
  (if null (hlFitchLineNumbers body) then a
    else last (hlFitchLineNumbers body));

fun hlFitchNestingFrom depth visible boxes [] = true
  | hlFitchNestingFrom depth visible boxes (HL_FLine (n, p, r) :: rest) =
    not (equal_hl_fitch_rule r HL_FAssume) andalso
      ((if equal_hl_fitch_rule r HL_FPremise then equal_nata depth zero_nat
         else true) andalso
        (less_eq_set equal_int (Set (hlFitchCitedLines r)) visible andalso
          (less_eq_set (equal_prod equal_int equal_int)
             (Set (hlFitchCitedSubs r)) boxes andalso
            hlFitchNestingFrom depth (insert equal_int n visible) boxes rest)))
  | hlFitchNestingFrom depth visible boxes
    (HL_FSub (HL_Subproof (a, p, body)) :: rest) =
    hlConcludesAtTop body andalso
      (hlFitchNestingFrom (suc depth) (insert equal_int a visible) bot_set
         body andalso
        hlFitchNestingFrom depth visible
          (insert (equal_prod equal_int equal_int)
            (a, hlSubLastLine (HL_Subproof (a, p, body))) boxes)
          rest);

fun hlFitchNestedWellFormed f =
  hlFitchNestingFrom zero_nat bot_set bot_set f andalso
    (hlFitchPremisesFirst f andalso
      (list_all (less_int zero_int) (hlFitchLineNumbers f) andalso
        (sorted_wrt less_int (hlFitchLineNumbers f) andalso
          hlConcludesAtTop f)));

fun hlFitchPremiseClosed f =
  superset equal_hl_formula (hlFitchPremises f)
    (hlOpenPremises (hlFitchToLemmon f));

fun hlFitchScopeFrom depth visible [] = SOME visible
  | hlFitchScopeFrom depth visible (HL_FLine (n, p, r) :: rest) =
    (if (case r of HL_FPremise => equal_nata depth zero_nat | HL_FAssume => true
          | HL_FMP (_, _) => true | HL_FMT (_, _) => true | HL_FDN _ => true
          | HL_FCP _ => true | HL_FAndI (_, _) => true | HL_FAndE _ => true
          | HL_FOrI _ => true | HL_FOrE (_, _, _) => true | HL_FRAA _ => true
          | HL_FForallE _ => true | HL_FForallI _ => true
          | HL_FExistsI _ => true | HL_FExistsE (_, _) => true | HL_FEqI => true
          | HL_FEqE (_, _) => true | HL_FLEM => true | HL_FPropTaut _ => true
          | HL_FIffI (_, _) => true | HL_FIffE (_, _) => true | HL_FQN _ => true
          | HL_FReit _ => true) andalso
          less_eq_set equal_int (Set (hlFitchCitedLines r)) visible
      then hlFitchScopeFrom depth (insert equal_int n visible) rest else NONE)
  | hlFitchScopeFrom depth visible (HL_FSub (HL_Subproof (a, p, body)) :: rest)
    = (case hlFitchScopeFrom (suc depth) (insert equal_int a visible) body
        of NONE => NONE
        | SOME _ =>
          hlFitchScopeFrom depth
            (insert equal_int a
              (insert equal_int (hlSubLastLine (HL_Subproof (a, p, body)))
                visible))
            rest);

fun hlFitchWellFormed f = not (is_none (hlFitchScopeFrom zero_nat bot_set f));

fun hlFitchVerified f =
  hlFitchWellFormed f andalso
    (hlConcludesAtTop f andalso
      (hlFitchNestedWellFormed f andalso
        (hlFitchPremiseClosed f andalso
          hlVerifiedCorrect (hlFitchToLemmon f))));

fun hlFitchCorrect f =
  hlFitchVerified f andalso hlCorrectG (hlScopeSrc f) (hlFitchToLemmon f);

fun hlViaTree p =
  (case hlToDerivation p of NONE => Inl (HL_SourceNotVerified zero_int)
    | SOME d =>
      let
        val f = hlDerivationToFitch d;
      in
        (if hlFitchCorrect f andalso
              (superset equal_hl_formula (hlOpenPremises p)
                 (hlFitchPremises f) andalso
                equal_option equal_hl_formula (hlConclusion (hlFitchToLemmon f))
                  (hlConclusion p))
          then Inr (HL_ViaTreeRoute, f) else Inl HL_TargetNotVerified)
      end);

fun premiseOrderError p =
  let
    val rest = dropWhile (isPremiseLine p) p;
  in
    (case filtera (isPremiseLine p) rest of [] => NONE
      | l :: _ =>
        (case rest of [] => NONE
          | e :: _ => SOME (PremiseLate (lineNumber l, lineNumber e))))
  end;

fun lemmonToFitchDirect p =
  (if not (lemmonCorrect p) then Inl (NotCorrect zero_nat)
    else (case boxOrderError p
           of NONE =>
             (case boxHeadError p
               of NONE =>
                 (case nestingError p
                   of NONE =>
                     (case premiseError p
                       of NONE =>
                         (case scopeError p
                           of NONE =>
                             (case subScopeError p
                               of NONE =>
                                 (case premiseOrderError p
                                   of NONE => Inr (buildItems (boxesOf p) p)
                                   | SOME a => Inl a)
                               | SOME a => Inl a)
                           | SOME a => Inl a)
                       | SOME a => Inl a)
                   | SOME a => Inl a)
               | SOME a => Inl a)
           | SOME a => Inl a));

fun lemmonToFitch p =
  (case lemmonToFitchDirect p of Inl _ => viaTree p | Inr f => Inr (Direct, f));

fun fitchWellFormed f =
  (if not (sorted_wrt less_nat (map flNum (flatten f)))
    then SOME "line numbers are not strictly increasing"
    else (if not (list_all noAssumeLinesItem f)
           then SOME "an assumption occurs otherwise than as the head of a subproof"
           else (if not (list_all
                          (fn fl =>
                            (if equal_fitch_rule (flRule fl) FPremise
                              then null (flScope fl) else true))
                          (flatten f))
                  then SOME "a premise occurs inside a subproof"
                  else (if not (premisesFirst f)
                         then SOME "a premise occurs after a line that is not a premise"
                         else (if not (list_all lastIsLineItem f)
                                then SOME "a subproof does not end in a line"
                                else (if not (concludesAtTop f)
                                       then SOME
      "the proof does not end at the outermost level"
                                       else (if not
          (list_all (citationOK f) (flatten f))
      then SOME "a line cites something not in its scope" else NONE)))))));

fun showTranslation r =
  (case r of Inl e => ["no translation: " ^ showError e]
    | Inr (rt, f) => showRoute rt :: showFitch f);

fun dependents p a =
  map_filter
    (fn x =>
      (if member equal_nat a (references x) then SOME (lineNumber x) else NONE))
    p;

fun ruleMatches j r =
  (if equal_justa j Assumption
    then equal_fitch_rule r FPremise orelse equal_fitch_rule r FAssume
    else equal_fitch_rule r (toFitchRule j));

fun lineMatches fl l =
  equal_nata (flNum fl) (lineNumber l) andalso
    (equal_fma (flFm fl) (formula l) andalso
      ruleMatches (justification l) (flRule fl));

fun fitchImage f p =
  list_all (fn l => list_ex (fn fl => lineMatches fl l) (flatten f)) p andalso
    list_all (fn fl => list_ex (lineMatches fl) p) (flatten f);

fun hlBoxPath p m =
  sort_key linorder_int (fn x => x)
    (map_filter
      (fn x =>
        (if less_eq_int (fst x) m andalso less_eq_int m (snd x)
          then SOME (fst x) else NONE))
      (hlBoxesOf p));

fun hlIsPrefix A_ [] ys = true
  | hlIsPrefix A_ (x :: xs) [] = false
  | hlIsPrefix A_ (x :: xs) (y :: ys) = eq A_ x y andalso hlIsPrefix A_ xs ys;

fun permuteProof r p = sort_key linorder_nat lineNumber (map (relabel r) p);

fun hlOptionAll f [] = SOME true
  | hlOptionAll f (x :: xs) =
    (case f x of NONE => NONE | SOME true => hlOptionAll f xs
      | SOME false => SOME false);

fun hlOptionAny f [] = SOME false
  | hlOptionAny f (x :: xs) =
    (case f x of NONE => NONE | SOME true => SOME true
      | SOME false => hlOptionAny f xs);

fun noDuplication f p =
  fitchImage f p andalso equal_nata (size_lista (flatten f)) (size_lista p);

fun sourceCovered f p =
  list_all (fn l => list_ex (fn fl => lineMatches fl l) (flatten f)) p;

fun hlFinitePredicates (HL_FiniteModel (x1, x2, x3)) = x3;

fun hlFiniteDomain (HL_FiniteModel (x1, x2, x3)) = x1;

fun hlFiniteConstants (HL_FiniteModel (x1, x2, x3)) = x2;

fun hlFiniteEvalTerm m assignment (HL_Var x) = map_of equal_literal assignment x
  | hlFiniteEvalTerm m assignment (HL_Const a) =
    map_of equal_literal (hlFiniteConstants m) a;

fun hlFiniteEval A_ m assignment (HL_Boolean b) = SOME b
  | hlFiniteEval A_ m assignment (HL_Predicate (p, ts)) =
    (case hlSequenceOptions (map (hlFiniteEvalTerm m assignment) ts)
      of NONE => NONE
      | SOME values =>
        (case map_of (equal_prod equal_literal equal_nat) (hlFinitePredicates m)
                (p, size_lista ts)
          of NONE => NONE
          | SOME relation => SOME (membera (equal_list A_) relation values)))
  | hlFiniteEval A_ m assignment (HL_Not p) =
    map_option not (hlFiniteEval A_ m assignment p)
  | hlFiniteEval A_ m assignment (HL_And (p, q)) =
    (case (hlFiniteEval A_ m assignment p, hlFiniteEval A_ m assignment q)
      of (NONE, _) => NONE | (SOME _, NONE) => NONE
      | (SOME a, SOME b) => SOME (a andalso b))
  | hlFiniteEval A_ m assignment (HL_Or (p, q)) =
    (case (hlFiniteEval A_ m assignment p, hlFiniteEval A_ m assignment q)
      of (NONE, _) => NONE | (SOME _, NONE) => NONE
      | (SOME a, SOME b) => SOME (a orelse b))
  | hlFiniteEval A_ m assignment (HL_Implies (p, q)) =
    (case (hlFiniteEval A_ m assignment p, hlFiniteEval A_ m assignment q)
      of (NONE, _) => NONE | (SOME _, NONE) => NONE
      | (SOME a, SOME b) => SOME (if a then b else true))
  | hlFiniteEval A_ m assignment (HL_Iff (p, q)) =
    (case (hlFiniteEval A_ m assignment p, hlFiniteEval A_ m assignment q)
      of (NONE, _) => NONE | (SOME _, NONE) => NONE
      | (SOME a, SOME b) => SOME (equal_bool a b))
  | hlFiniteEval A_ m assignment (HL_ForAll (x, p)) =
    (if null (hlFiniteDomain m) then NONE
      else hlOptionAll (fn d => hlFiniteEval A_ m ((x, d) :: assignment) p)
             (hlFiniteDomain m))
  | hlFiniteEval A_ m assignment (HL_Exists (x, p)) =
    (if null (hlFiniteDomain m) then NONE
      else hlOptionAny (fn d => hlFiniteEval A_ m ((x, d) :: assignment) p)
             (hlFiniteDomain m));

fun hlFirstDifference [] ys = zero_int
  | hlFirstDifference (x :: xs) [] = x
  | hlFirstDifference (x :: xs) (y :: ys) =
    (if equal_inta x y then hlFirstDifference xs ys else x);

fun hlToFitchRule HL_Assumption = HL_FPremise
  | hlToFitchRule (HL_MP (m, n)) = HL_FMP (m, n)
  | hlToFitchRule (HL_MT (m, n)) = HL_FMT (m, n)
  | hlToFitchRule (HL_DN m) = HL_FDN m
  | hlToFitchRule (HL_CP (a, c)) = HL_FCP (a, c)
  | hlToFitchRule (HL_AndIntro (m, n)) = HL_FAndI (m, n)
  | hlToFitchRule (HL_AndElim m) = HL_FAndE m
  | hlToFitchRule (HL_OrIntro m) = HL_FOrI m
  | hlToFitchRule (HL_OrElim (d, a1, c1, a2, c2)) =
    HL_FOrE (d, (a1, c1), (a2, c2))
  | hlToFitchRule (HL_RAA (a, c)) = HL_FRAA (a, c)
  | hlToFitchRule (HL_ForallElim m) = HL_FForallE m
  | hlToFitchRule (HL_ExistsIntro m) = HL_FExistsI m
  | hlToFitchRule (HL_ForallIntro m) = HL_FForallI m
  | hlToFitchRule (HL_ExistsElim (m, a, c)) = HL_FExistsE (m, (a, c))
  | hlToFitchRule HL_EqIntro = HL_FEqI
  | hlToFitchRule (HL_EqElim (m, n)) = HL_FEqE (m, n)
  | hlToFitchRule HL_LEM = HL_FLEM
  | hlToFitchRule (HL_PropTaut ms) = HL_FPropTaut ms
  | hlToFitchRule (HL_IffIntro (m, n)) = HL_FIffI (m, n)
  | hlToFitchRule (HL_IffElim (m, n)) = HL_FIffE (m, n)
  | hlToFitchRule (HL_QN m) = HL_FQN m;

fun hlBadCitations p =
  maps (fn l =>
         map_filter
           (fn x =>
             (if not (hlIsPrefix equal_int (hlBoxPath p x)
                       (hlBoxPath p (hlLineNumber l)))
               then SOME (hlLineNumber l, x) else NONE))
           (hlFitchCitedLines (hlToFitchRule (hlJustification l))))
    p;

fun hlScopeError p =
  (case hlBadCitations p of [] => NONE
    | (n, m) :: _ =>
      SOME (HL_OutOfScope
             (n, m, hlFirstDifference (hlBoxPath p m) (hlBoxPath p n))));

fun hlSubproofLevel p ac = removeAll equal_int (fst ac) (hlBoxPath p (fst ac));

fun hlBadSubproofCitations p =
  maps (fn l =>
         map_filter
           (fn x =>
             (if not (equal_lista equal_int (hlBoxPath p (hlLineNumber l))
                       (hlSubproofLevel p x))
               then SOME (hlLineNumber l, (snd x, fst x)) else NONE))
           (hlDischargePairs (hlJustification l)))
    p;

fun hlSubproofScopeError p =
  (case hlBadSubproofCitations p of [] => NONE
    | (n, (c, a)) :: _ => SOME (HL_OutOfScope (n, c, a)));

fun hlIsPremiseLine p l =
  equal_hl_justification (hlJustification l) HL_Assumption andalso
    not (membera equal_int (hlDischargedAssumptions p) (hlLineNumber l));

fun hlPremiseOrderError p =
  let
    val rest = dropWhile (hlIsPremiseLine p) p;
  in
    (case filtera (hlIsPremiseLine p) rest of [] => NONE
      | l :: _ =>
        (case rest of [] => NONE
          | e :: _ => SOME (HL_PremiseLate (hlLineNumber l, hlLineNumber e))))
  end;

fun hlEigenScopeAssumptions p l =
  let
    val n = hlLineNumber l;
    val premises =
      map_filter
        (fn x =>
          (if hlIsPremiseLine p x andalso less_int (hlLineNumber x) n
            then SOME (hlLineNumber x) else NONE))
        p;
  in
    premises @
      (case hlJustification l of HL_Assumption => hlBoxPath p n
        | HL_MP (_, _) => hlBoxPath p n | HL_MT (_, _) => hlBoxPath p n
        | HL_DN _ => hlBoxPath p n | HL_CP (_, _) => hlBoxPath p n
        | HL_AndIntro (_, _) => hlBoxPath p n | HL_AndElim _ => hlBoxPath p n
        | HL_OrIntro _ => hlBoxPath p n
        | HL_OrElim (_, _, _, _, _) => hlBoxPath p n
        | HL_RAA (_, _) => hlBoxPath p n | HL_ForallElim _ => hlBoxPath p n
        | HL_ExistsIntro _ => hlBoxPath p n | HL_ForallIntro _ => hlBoxPath p n
        | HL_ExistsElim (_, a, c) => removeAll equal_int a (hlBoxPath p c)
        | HL_EqIntro => hlBoxPath p n | HL_EqElim (_, _) => hlBoxPath p n
        | HL_LEM => hlBoxPath p n | HL_PropTaut _ => hlBoxPath p n
        | HL_IffIntro (_, _) => hlBoxPath p n
        | HL_IffElim (_, _) => hlBoxPath p n | HL_QN _ => hlBoxPath p n)
  end;

fun hlGeneralizedConstants p (HL_ProofLine (n, goal, HL_ForallIntro m, g)) =
  (case hlLookupLine p m of NONE => []
    | SOME source =>
      sorted_list_of_set (equal_literal, linorder_literal)
        (minus_set equal_literal (hlConstantsInFormula (hlFormula source))
          (hlConstantsInFormula goal)))
  | hlGeneralizedConstants p
    (HL_ProofLine (n, goal, HL_ExistsElim (m, a, c), g)) =
    (case (hlFormulaAt p m, hlFormulaAt p a) of (NONE, _) => []
      | (SOME _, NONE) => []
      | (SOME source, SOME assumption) =>
        sorted_list_of_set (equal_literal, linorder_literal)
          (minus_set equal_literal (hlConstantsInFormula assumption)
            (sup_set equal_literal (hlConstantsInFormula source)
              (hlConstantsInFormula goal))))
  | hlGeneralizedConstants p (HL_ProofLine (v, va, HL_Assumption, vc)) = []
  | hlGeneralizedConstants p (HL_ProofLine (v, va, HL_MP (vd, ve), vc)) = []
  | hlGeneralizedConstants p (HL_ProofLine (v, va, HL_MT (vd, ve), vc)) = []
  | hlGeneralizedConstants p (HL_ProofLine (v, va, HL_DN vd, vc)) = []
  | hlGeneralizedConstants p (HL_ProofLine (v, va, HL_CP (vd, ve), vc)) = []
  | hlGeneralizedConstants p (HL_ProofLine (v, va, HL_AndIntro (vd, ve), vc)) =
    []
  | hlGeneralizedConstants p (HL_ProofLine (v, va, HL_AndElim vd, vc)) = []
  | hlGeneralizedConstants p (HL_ProofLine (v, va, HL_OrIntro vd, vc)) = []
  | hlGeneralizedConstants p
    (HL_ProofLine (v, va, HL_OrElim (vd, ve, vf, vg, vh), vc)) = []
  | hlGeneralizedConstants p (HL_ProofLine (v, va, HL_RAA (vd, ve), vc)) = []
  | hlGeneralizedConstants p (HL_ProofLine (v, va, HL_ForallElim vd, vc)) = []
  | hlGeneralizedConstants p (HL_ProofLine (v, va, HL_ExistsIntro vd, vc)) = []
  | hlGeneralizedConstants p (HL_ProofLine (v, va, HL_EqIntro, vc)) = []
  | hlGeneralizedConstants p (HL_ProofLine (v, va, HL_EqElim (vd, ve), vc)) = []
  | hlGeneralizedConstants p (HL_ProofLine (v, va, HL_LEM, vc)) = []
  | hlGeneralizedConstants p (HL_ProofLine (v, va, HL_PropTaut vd, vc)) = []
  | hlGeneralizedConstants p (HL_ProofLine (v, va, HL_IffIntro (vd, ve), vc)) =
    []
  | hlGeneralizedConstants p (HL_ProofLine (v, va, HL_IffElim (vd, ve), vc)) =
    []
  | hlGeneralizedConstants p (HL_ProofLine (v, va, HL_QN vd, vc)) = [];

fun hlEigenScopeViolations p =
  maps (fn l =>
         maps (fn a =>
                map_filter
                  (fn x =>
                    (if (case hlFormulaAt p a of NONE => false
                          | SOME assumption =>
                            member equal_literal x
                              (hlConstantsInFormula assumption))
                      then SOME (hlLineNumber l, (x, a)) else NONE))
                  (hlGeneralizedConstants p l))
           (hlEigenScopeAssumptions p l))
    p;

fun hlEigenScopeError p =
  (case hlEigenScopeViolations p of [] => NONE
    | (n, (c, a)) :: _ => SOME (HL_EigenInScope (n, c, a)));

fun hlBuildFitchItems boxes [] = []
  | hlBuildFitchItems boxes (l :: ls) =
    (case find (fn ac => equal_inta (fst ac) (hlLineNumber l)) boxes
      of NONE =>
        HL_FLine
          (hlLineNumber l, hlFormula l, hlToFitchRule (hlJustification l)) ::
          hlBuildFitchItems boxes ls
      | SOME ac =>
        HL_FSub
          (HL_Subproof
            (hlLineNumber l, hlFormula l,
              hlBuildFitchItems boxes
                (takeWhile (fn la => less_eq_int (hlLineNumber la) (snd ac))
                  ls))) ::
          hlBuildFitchItems boxes
            (dropWhile (fn la => less_eq_int (hlLineNumber la) (snd ac)) ls));

fun hlBoxOrderError p =
  (case filtera (fn ac => less_int (snd ac) (fst ac)) (hlBoxesOf p)
    of [] => NONE | ac :: _ => SOME (HL_BoxReversed (fst ac, snd ac)));

fun hlPremiseError p =
  (case filtera
          (fn l =>
            hlIsPremiseLine p l andalso
              not (null (hlBoxPath p (hlLineNumber l))))
          p
    of [] => NONE
    | l :: _ =>
      SOME (HL_PremiseInBox
             (hlLineNumber l, last (hlBoxPath p (hlLineNumber l)))));

fun hlDischargerOf p ac =
  (case find (fn l =>
               membera (equal_prod equal_int equal_int)
                 (hlDischargePairs (hlJustification l)) ac)
          p
    of NONE => zero_int | SOME a => hlLineNumber a);

fun hlOverlapping ac bd =
  less_int (fst ac) (fst bd) andalso
    (less_eq_int (fst bd) (snd ac) andalso less_int (snd ac) (snd bd));

fun hlNestingError p =
  (case filtera (fn ac => list_ex (hlOverlapping ac) (hlBoxesOf p))
          (hlBoxesOf p)
    of [] => NONE
    | ac :: _ =>
      SOME (HL_NotNested
             (hlDischargerOf p ac, fst ac,
               map_filter
                 (fn x => (if hlOverlapping ac x then SOME (fst x) else NONE))
                 (hlBoxesOf p))));

fun hlBoxHeadError p =
  (case filtera
          (fn x =>
            equal_inta (fst (fst x)) (fst (snd x)) andalso
              not (equal_inta (snd (fst x)) (snd (snd x))))
          (product (hlBoxesOf p) (hlBoxesOf p))
    of [] => NONE
    | x :: _ =>
      SOME (HL_AssumptionReused (fst (fst x), snd (fst x), snd (snd x))));

fun hlLemmonToFitchDirect p =
  (if not (hlVerifiedCorrect p) then Inl (HL_SourceNotVerified zero_int)
    else (case hlBoxOrderError p
           of NONE =>
             (case hlBoxHeadError p
               of NONE =>
                 (case hlNestingError p
                   of NONE =>
                     (case hlPremiseError p
                       of NONE =>
                         (case hlScopeError p
                           of NONE =>
                             (case hlSubproofScopeError p
                               of NONE =>
                                 (case hlPremiseOrderError p
                                   of NONE =>
                                     (case hlEigenScopeError p
                                       of NONE =>
 Inr (hlBuildFitchItems (hlBoxesOf p) p)
                                       | SOME a => Inl a)
                                   | SOME a => Inl a)
                               | SOME a => Inl a)
                           | SOME a => Inl a)
                       | SOME a => Inl a)
                   | SOME a => Inl a)
               | SOME a => Inl a)
           | SOME a => Inl a));

fun hlLemmonToFitch p =
  (case hlLemmonToFitchDirect p of Inl _ => hlViaTree p
    | Inr f => Inr (HL_DirectRoute, f));

fun hlFitchConclusion f =
  (if null (hlFlattenFitch f) then NONE
    else SOME (fst (snd (last (hlFlattenFitch f)))));

fun lemmonToFitchChecked p =
  (case lemmonToFitchDirect p of Inl _ => viaTree p
    | Inr f => (if fitchCorrect f then Inr (Direct, f) else viaTree p));

fun positionalImage f p = list_all2 lineMatches (flatten f) p;

fun hlPaperDependenciesOf look HL_Assumption self =
  insert equal_int self bot_set
  | hlPaperDependenciesOf look (HL_CP (a, c)) self = remove equal_int a (look c)
  | hlPaperDependenciesOf look (HL_RAA (a, c)) self =
    remove equal_int a (look c)
  | hlPaperDependenciesOf look (HL_OrElim (d, a1, c1, a2, c2)) self =
    sup_set equal_int
      (sup_set equal_int (look d) (remove equal_int a1 (look c1)))
      (remove equal_int a2 (look c2))
  | hlPaperDependenciesOf look (HL_ExistsElim (m, a, c)) self =
    sup_set equal_int (look m) (remove equal_int a (look c))
  | hlPaperDependenciesOf look (HL_MP (v, va)) self =
    sup_seta equal_int (Set (map look (hlCitedLines (HL_MP (v, va)))))
  | hlPaperDependenciesOf look (HL_MT (v, va)) self =
    sup_seta equal_int (Set (map look (hlCitedLines (HL_MT (v, va)))))
  | hlPaperDependenciesOf look (HL_DN v) self =
    sup_seta equal_int (Set (map look (hlCitedLines (HL_DN v))))
  | hlPaperDependenciesOf look (HL_AndIntro (v, va)) self =
    sup_seta equal_int (Set (map look (hlCitedLines (HL_AndIntro (v, va)))))
  | hlPaperDependenciesOf look (HL_AndElim v) self =
    sup_seta equal_int (Set (map look (hlCitedLines (HL_AndElim v))))
  | hlPaperDependenciesOf look (HL_OrIntro v) self =
    sup_seta equal_int (Set (map look (hlCitedLines (HL_OrIntro v))))
  | hlPaperDependenciesOf look (HL_ForallElim v) self =
    sup_seta equal_int (Set (map look (hlCitedLines (HL_ForallElim v))))
  | hlPaperDependenciesOf look (HL_ExistsIntro v) self =
    sup_seta equal_int (Set (map look (hlCitedLines (HL_ExistsIntro v))))
  | hlPaperDependenciesOf look (HL_ForallIntro v) self =
    sup_seta equal_int (Set (map look (hlCitedLines (HL_ForallIntro v))))
  | hlPaperDependenciesOf look HL_EqIntro self =
    sup_seta equal_int (Set (map look (hlCitedLines HL_EqIntro)))
  | hlPaperDependenciesOf look (HL_EqElim (v, va)) self =
    sup_seta equal_int (Set (map look (hlCitedLines (HL_EqElim (v, va)))))
  | hlPaperDependenciesOf look HL_LEM self =
    sup_seta equal_int (Set (map look (hlCitedLines HL_LEM)))
  | hlPaperDependenciesOf look (HL_PropTaut v) self =
    sup_seta equal_int (Set (map look (hlCitedLines (HL_PropTaut v))))
  | hlPaperDependenciesOf look (HL_IffIntro (v, va)) self =
    sup_seta equal_int (Set (map look (hlCitedLines (HL_IffIntro (v, va)))))
  | hlPaperDependenciesOf look (HL_IffElim (v, va)) self =
    sup_seta equal_int (Set (map look (hlCitedLines (HL_IffElim (v, va)))))
  | hlPaperDependenciesOf look (HL_QN v) self =
    sup_seta equal_int (Set (map look (hlCitedLines (HL_QN v))));

fun hlPaperDependencyAt e n =
  (case hlReferencesAt e n of NONE => bot_set | SOME g => g);

fun hlCanonicalFrom e [] = true
  | hlCanonicalFrom e (l :: ls) =
    equal_set equal_int (hlReferences l)
      (hlPaperDependenciesOf (hlPaperDependencyAt e) (hlJustification l)
        (hlLineNumber l)) andalso
      hlCanonicalFrom (e @ [l]) ls;

fun hlCanonicalDependencies p = hlCanonicalFrom [] p;

fun hlPaperCorrect p = hlVerifiedCorrect p andalso hlCanonicalDependencies p;

fun hlFiniteEvalClosed A_ m p =
  (if equal_set equal_literal (hlFreeVariables p) bot_set
    then hlFiniteEval A_ m [] p else NONE);

fun hlStripDependencies p =
  map (fn l => (hlLineNumber l, (hlFormula l, hlJustification l))) p;

fun hlLemmonToFitchChecked p =
  (case hlLemmonToFitchDirect p of Inl _ => hlViaTree p
    | Inr f =>
      (if hlFitchCorrect f andalso
            (superset equal_hl_formula (hlOpenPremises p)
               (hlFitchPremises f) andalso
              equal_option equal_hl_formula (hlConclusion (hlFitchToLemmon f))
                (hlConclusion p))
        then Inr (HL_DirectRoute, f) else hlViaTree p));

fun hlRecomputeDependenciesFrom e [] = e
  | hlRecomputeDependenciesFrom e ((n, (p, j)) :: ls) =
    hlRecomputeDependenciesFrom
      (e @ [HL_ProofLine
              (n, p, j, hlPaperDependenciesOf (hlPaperDependencyAt e) j n)])
      ls;

fun hlRecomputeDependencies x = hlRecomputeDependenciesFrom [] x;

fun hlFiniteStandardEquality A_ m =
  (case map_of (equal_prod equal_literal equal_nat) (hlFinitePredicates m)
          ("=", nat_of_integer (2 : IntInf.int))
    of NONE => false
    | SOME relation =>
      let
        val diagonal = map (fn x => [x, x]) (hlFiniteDomain m);
      in
        list_all (membera (equal_list A_) diagonal) relation andalso
          list_all (membera (equal_list A_) relation) diagonal
      end);

end; (*struct LemmonFitch*)
