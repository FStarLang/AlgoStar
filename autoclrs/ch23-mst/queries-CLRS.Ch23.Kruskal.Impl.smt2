; Z3 invocation started by F*
; F* version: 2025.12.15~dev -- commit hash: 7c9ca52b7ed12cafe329275b64719e4715f389a8
; Z3 version (according to F*): 4.13.3

(set-option :global-decls false)
(set-option :smt.mbqi false)
(set-option :auto_config false)
(set-option :produce-unsat-cores true)
(set-option :model true)
(set-option :smt.case_split 3)
(set-option :smt.relevancy 2)
(set-option :rewriter.enable_der false)
(set-option :rewriter.sort_disjunctions false)
(set-option :pi.decompose_patterns false)
(set-option :smt.arith.solver 6)
(set-option :smt.random-seed 0)


(declare-sort FString)
(declare-fun FString_constr_id (FString) Int)

(declare-sort Term)
(declare-datatypes () ((Universe 
(Univ (ulevel Int)))))
(define-fun imax ((i Int) (j Int)) Int 
(ite (<= i 0) j 
(ite (<= j 0) i 
(ite (<= i j) j i)))) 
(define-fun U_zero () Universe (Univ 0))
(define-fun U_succ ((u Universe)) Universe
(Univ (+ (ulevel u) 1)))
(declare-fun U_max (Universe Universe) Universe) 
(assert (forall ((u1 Universe) (u2 Universe)) 
(! (= (U_max u1 u2)
(Univ (imax (ulevel u1) (ulevel u2))))
:pattern ((U_max u1 u2)))))
(assert (forall ((u Universe)) (>= (ulevel u) 0)))
(declare-fun U_unif (Int) Universe)
(declare-fun U_unknown () Universe)
(declare-fun Term_constr_id (Term) Int)
(declare-sort Dummy_sort)
(declare-fun Dummy_value () Dummy_sort)
(declare-datatypes () ((Fuel 
(ZFuel) 
(SFuel (prec Fuel)))))
(declare-fun MaxIFuel () Fuel)
(declare-fun MaxFuel () Fuel)
(declare-fun PreType (Term) Term)
(declare-fun Valid (Term) Bool)
(declare-fun HasTypeFuel (Fuel Term Term) Bool)
(define-fun HasTypeZ ((x Term) (t Term)) Bool
(HasTypeFuel ZFuel x t))
(define-fun HasType ((x Term) (t Term)) Bool
(HasTypeFuel MaxIFuel x t))
(declare-fun IsTotFun (Term) Bool)

                ;;fuel irrelevance
(assert (forall ((f Fuel) (x Term) (t Term))
(! (= (HasTypeFuel (SFuel f) x t)
(HasTypeZ x t))
:pattern ((HasTypeFuel (SFuel f) x t)))))
(declare-fun NoHoist (Term Bool) Bool)
;;no-hoist
(assert (forall ((dummy Term) (b Bool))
(! (= (NoHoist dummy b) b)
:pattern ((NoHoist dummy b)))))
(define-fun  IsTyped ((x Term)) Bool
(exists ((t Term)) (HasTypeZ x t)))
(declare-fun ApplyTF (Term Fuel) Term)
(declare-fun ApplyTT (Term Term) Term)
(declare-fun Prec (Term Term) Bool)
(assert (forall ((x Term) (y Term) (z Term))
(! (implies (and (Prec x y) (Prec y z)) (Prec x z))
:pattern ((Prec x z) (Prec x y)))))
(assert (forall ((x Term) (y Term))
(implies (Prec x y)
(not (Prec y x)))))
(declare-fun Closure (Term) Term)
(declare-fun ConsTerm (Term Term) Term)
(declare-fun ConsFuel (Fuel Term) Term)
(declare-fun Tm_uvar (Int) Term)
(define-fun Reify ((x Term)) Term x)
(declare-fun Prims.precedes (Universe Universe Term Term Term Term) Term)
(declare-fun Range_const (Int) Term)
(declare-fun _mul (Int Int) Int)
(declare-fun _div (Int Int) Int)
(declare-fun _mod (Int Int) Int)
(declare-fun __uu__PartialApp () Term)
(assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))
(assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))
(assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))
(declare-fun _rmul (Real Real) Real)
(declare-fun _rdiv (Real Real) Real)
(assert (forall ((x Real) (y Real)) (! (= (_rmul x y) (* x y)) :pattern ((_rmul x y)))))
(assert (forall ((x Real) (y Real)) (! (= (_rdiv x y) (/ x y)) :pattern ((_rdiv x y)))))
(define-fun Unreachable () Bool false); <start constructor FString_const>
; Constructor
(declare-fun FString_const (Int) FString)
; Constructor distinct
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Int))
   (! (= 0 (FString_constr_id (FString_const @u0)))
    :pattern ((FString_const @u0))
    :qid constructor_distinct_FString_const))
  :named constructor_distinct_FString_const))
; Projector
(declare-fun FString_const_proj_0 (FString) Int)
; Projection inverse
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Int))
   (! (= (FString_const_proj_0 (FString_const @u0)) @u0)
    :pattern ((FString_const @u0))
    :qid projection_inverse_FString_const_proj_0))
  :named projection_inverse_FString_const_proj_0))
; Discriminator definition
(define-fun is-FString_const ((__@u0 FString)) Bool
 (and (= (FString_constr_id __@u0) 0) (= __@u0 (FString_const (FString_const_proj_0 __@u0)))))
; </end constructor FString_const>
; <start constructor Tm_type>
; Constructor
(declare-fun Tm_type (Universe) Term)
; Constructor distinct
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Universe))
   (! (= 2 (Term_constr_id (Tm_type @u0)))
    :pattern ((Tm_type @u0))
    :qid constructor_distinct_Tm_type))
  :named constructor_distinct_Tm_type))
; Projector
(declare-fun Tm_type_0 (Term) Universe)
; Projection inverse
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Universe))
   (! (= (Tm_type_0 (Tm_type @u0)) @u0) :pattern ((Tm_type @u0)) :qid projection_inverse_Tm_type_0))
  :named projection_inverse_Tm_type_0))
; Discriminator definition
(define-fun is-Tm_type ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 2) (= __@x0 (Tm_type (Tm_type_0 __@x0)))))
; </end constructor Tm_type>
; <start constructor Tm_arrow>
; Constructor
(declare-fun Tm_arrow (Int) Term)
; Constructor distinct
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Int))
   (! (= 3 (Term_constr_id (Tm_arrow @u0)))
    :pattern ((Tm_arrow @u0))
    :qid constructor_distinct_Tm_arrow))
  :named constructor_distinct_Tm_arrow))
; Projector
(declare-fun Tm_arrow_id (Term) Int)
; Projection inverse
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Int))
   (! (= (Tm_arrow_id (Tm_arrow @u0)) @u0)
    :pattern ((Tm_arrow @u0))
    :qid projection_inverse_Tm_arrow_id))
  :named projection_inverse_Tm_arrow_id))
; Discriminator definition
(define-fun is-Tm_arrow ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 3) (= __@x0 (Tm_arrow (Tm_arrow_id __@x0)))))
; </end constructor Tm_arrow>
; <start constructor Tm_unit>
; Constructor
(declare-fun Tm_unit () Term)
; Constructor distinct
;;; Fact-ids: 
(assert (! (= 6 (Term_constr_id Tm_unit)) :named constructor_distinct_Tm_unit))
; Discriminator definition
(define-fun is-Tm_unit ((__@x0 Term)) Bool (and (= (Term_constr_id __@x0) 6) (= __@x0 Tm_unit)))
; </end constructor Tm_unit>
; <start constructor BoxInt>
; Constructor
(declare-fun BoxInt (Int) Term)
; Constructor distinct
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Int))
   (! (= 7 (Term_constr_id (BoxInt @u0))) :pattern ((BoxInt @u0)) :qid constructor_distinct_BoxInt))
  :named constructor_distinct_BoxInt))
; Projector
(declare-fun BoxInt_proj_0 (Term) Int)
; Projection inverse
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Int))
   (! (= (BoxInt_proj_0 (BoxInt @u0)) @u0)
    :pattern ((BoxInt @u0))
    :qid projection_inverse_BoxInt_proj_0))
  :named projection_inverse_BoxInt_proj_0))
; Discriminator definition
(define-fun is-BoxInt ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 7) (= __@x0 (BoxInt (BoxInt_proj_0 __@x0)))))
; </end constructor BoxInt>
; <start constructor BoxBool>
; Constructor
(declare-fun BoxBool (Bool) Term)
; Constructor distinct
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Bool))
   (! (= 8 (Term_constr_id (BoxBool @u0)))
    :pattern ((BoxBool @u0))
    :qid constructor_distinct_BoxBool))
  :named constructor_distinct_BoxBool))
; Projector
(declare-fun BoxBool_proj_0 (Term) Bool)
; Projection inverse
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Bool))
   (! (= (BoxBool_proj_0 (BoxBool @u0)) @u0)
    :pattern ((BoxBool @u0))
    :qid projection_inverse_BoxBool_proj_0))
  :named projection_inverse_BoxBool_proj_0))
; Discriminator definition
(define-fun is-BoxBool ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 8) (= __@x0 (BoxBool (BoxBool_proj_0 __@x0)))))
; </end constructor BoxBool>
; <start constructor BoxString>
; Constructor
(declare-fun BoxString (FString) Term)
; Constructor distinct
;;; Fact-ids: 
(assert
 (! (forall ((@u0 FString))
   (! (= 9 (Term_constr_id (BoxString @u0)))
    :pattern ((BoxString @u0))
    :qid constructor_distinct_BoxString))
  :named constructor_distinct_BoxString))
; Projector
(declare-fun BoxString_proj_0 (Term) FString)
; Projection inverse
;;; Fact-ids: 
(assert
 (! (forall ((@u0 FString))
   (! (= (BoxString_proj_0 (BoxString @u0)) @u0)
    :pattern ((BoxString @u0))
    :qid projection_inverse_BoxString_proj_0))
  :named projection_inverse_BoxString_proj_0))
; Discriminator definition
(define-fun is-BoxString ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 9) (= __@x0 (BoxString (BoxString_proj_0 __@x0)))))
; </end constructor BoxString>
; <start constructor BoxReal>
; Constructor
(declare-fun BoxReal (Real) Term)
; Constructor distinct
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Real))
   (! (= 10 (Term_constr_id (BoxReal @u0)))
    :pattern ((BoxReal @u0))
    :qid constructor_distinct_BoxReal))
  :named constructor_distinct_BoxReal))
; Projector
(declare-fun BoxReal_proj_0 (Term) Real)
; Projection inverse
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Real))
   (! (= (BoxReal_proj_0 (BoxReal @u0)) @u0)
    :pattern ((BoxReal @u0))
    :qid projection_inverse_BoxReal_proj_0))
  :named projection_inverse_BoxReal_proj_0))
; Discriminator definition
(define-fun is-BoxReal ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 10) (= __@x0 (BoxReal (BoxReal_proj_0 __@x0)))))
; </end constructor BoxReal>
; <start constructor LexCons>
; Constructor
(declare-fun LexCons (Term Term Term) Term)
; Constructor distinct
;;; Fact-ids: 
(assert
 (! (forall ((@x0 Term) (@x1 Term) (@x2 Term))
   (! (= 11 (Term_constr_id (LexCons @x0 @x1 @x2)))
    :pattern ((LexCons @x0 @x1 @x2))
    :qid constructor_distinct_LexCons))
  :named constructor_distinct_LexCons))
; Projector
(declare-fun LexCons_0 (Term) Term)
; Projection inverse
;;; Fact-ids: 
(assert
 (! (forall ((@x0 Term) (@x1 Term) (@x2 Term))
   (! (= (LexCons_0 (LexCons @x0 @x1 @x2)) @x0)
    :pattern ((LexCons @x0 @x1 @x2))
    :qid projection_inverse_LexCons_0))
  :named projection_inverse_LexCons_0))
; Projector
(declare-fun LexCons_1 (Term) Term)
; Projection inverse
;;; Fact-ids: 
(assert
 (! (forall ((@x0 Term) (@x1 Term) (@x2 Term))
   (! (= (LexCons_1 (LexCons @x0 @x1 @x2)) @x1)
    :pattern ((LexCons @x0 @x1 @x2))
    :qid projection_inverse_LexCons_1))
  :named projection_inverse_LexCons_1))
; Projector
(declare-fun LexCons_2 (Term) Term)
; Projection inverse
;;; Fact-ids: 
(assert
 (! (forall ((@x0 Term) (@x1 Term) (@x2 Term))
   (! (= (LexCons_2 (LexCons @x0 @x1 @x2)) @x2)
    :pattern ((LexCons @x0 @x1 @x2))
    :qid projection_inverse_LexCons_2))
  :named projection_inverse_LexCons_2))
; Discriminator definition
(define-fun is-LexCons ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 11)
  (= __@x0 (LexCons (LexCons_0 __@x0) (LexCons_1 __@x0) (LexCons_2 __@x0)))))
; </end constructor LexCons>
(declare-fun Prims.precedes@tok (Universe Universe) Term)
(assert
(forall ((u0 Universe) (u1 Universe) (@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term))
(! (= (ApplyTT (ApplyTT (ApplyTT (ApplyTT (Prims.precedes@tok u0 u1) @x0) @x1) @x2) @x3)
(Prims.precedes u0 u1 @x0 @x1 @x2 @x3))
:pattern ((ApplyTT (ApplyTT (ApplyTT (ApplyTT (Prims.precedes@tok u0 u1) @x0) @x1) @x2) @x3)))))

(define-fun is-Prims.LexCons ((t Term)) Bool 
(is-LexCons t))
(declare-fun Prims.lex_t () Term)
(declare-fun LexTop () Term)
(assert (forall ((u0 Universe) (u1 Universe) (t1 Term) (t2 Term) (x1 Term) (x2 Term) (y1 Term) (y2 Term))
(iff (Valid (Prims.precedes u0 u1 Prims.lex_t Prims.lex_t (LexCons t1 x1 x2) (LexCons t2 y1 y2)))
(or (Valid (Prims.precedes u0 u1 t1 t2 x1 y1))
(and (= x1 y1)
(Valid (Prims.precedes u0 u1 Prims.lex_t Prims.lex_t x2 y2)))))))
(assert (forall ((u0 Universe) (u1 Universe) (t1 Term) (t2 Term) (e1 Term) (e2 Term))
(! (iff (Valid (Prims.precedes u0 u1 t1 t2 e1 e2))
(Valid (Prims.precedes U_zero U_zero Prims.lex_t Prims.lex_t e1 e2)))
:pattern (Prims.precedes u0 u1 t1 t2 e1 e2))))
(assert (forall ((u0 Universe) (u1 Universe) (t1 Term) (t2 Term))
(! (iff (Valid (Prims.precedes u0 u1 Prims.lex_t Prims.lex_t t1 t2)) 
(Prec t1 t2))
:pattern ((Prims.precedes u0 u1 Prims.lex_t Prims.lex_t t1 t2)))))
(assert (forall ((e Term) (t Term))
(! (implies (HasType e t)
(Valid t))
:pattern ((HasType e t)
(Valid t))
:qid __prelude_valid_intro)))
(assert (forall ((u Universe) (t Term))
(! (iff (HasType (Tm_type u) t)
(= t (Tm_type (U_succ u))))
:pattern ((HasType (Tm_type u) t)))))

(push) ;; push{1
(declare-fun CLRS.Ch23.Kruskal.Impl.scan_min_inv (Term Term Term Term Term) Term)
(declare-fun CLRS.Ch23.Kruskal.UF.find_pure (Term Term Term Term) Term)
; Fuel-instrumented function name
(declare-fun CLRS.Ch23.Kruskal.UF.find_pure.fuel_instrumented (Fuel Term Term Term Term) Term)
(declare-fun FStar.Monotonic.Heap.core_mref (Term) Term)
(declare-fun FStar.Monotonic.Heap.lemma_mref_injectivity () Term)
(declare-fun FStar.Monotonic.Heap.mref (Term Term) Term)
(declare-fun FStar.Preorder.preorder (Universe Term) Term)
(declare-fun FStar.Preorder.preorder_rel (Universe Term Term) Term)
(declare-fun FStar.Preorder.reflexive (Universe Term Term) Term)
(declare-fun FStar.Preorder.relation (Universe Term) Term)
(declare-fun FStar.Preorder.transitive (Universe Term Term) Term)
(declare-fun FStar.Range.range () Term)
(declare-fun FStar.Seq.Base.index (Universe Term Term Term) Term)
(declare-fun FStar.Seq.Base.length (Universe Term Term) Term)
(declare-fun FStar.Seq.Base.seq (Universe Term) Term)
(declare-fun FStar.SizeT.fits (Term) Term)
(declare-fun FStar.SizeT.t (Dummy_sort) Term)
(declare-fun FStar.SizeT.uint_to_t (Term) Term)
(declare-fun FStar.SizeT.v (Term) Term)
; Constructor
(declare-fun FStar.Stubs.Tactics.Common.NotAListLiteral () Term)
; Constructor base
(declare-fun FStar.Stubs.Tactics.Common.NotAListLiteral@base () Term)
; Constructor
(declare-fun FStar.Stubs.Tactics.Common.SKIP () Term)
; Constructor base
(declare-fun FStar.Stubs.Tactics.Common.SKIP@base () Term)
; Constructor
(declare-fun FStar.Stubs.Tactics.Common.Stop () Term)
; Constructor base
(declare-fun FStar.Stubs.Tactics.Common.Stop@base () Term)
; Constructor
(declare-fun FStar.Tactics.V2.Derived.Goal_not_trivial () Term)
; Constructor base
(declare-fun FStar.Tactics.V2.Derived.Goal_not_trivial@base () Term)
(declare-fun Non_total_Tm_arrow_2672e45a784a2b0927230a9770301b34 (Term Term) Term)
(declare-fun Non_total_Tm_arrow_6dfaaa0e96f606a8d2b60f84543d775d (Term) Term)
(declare-fun Non_total_Tm_arrow_cd4cc5f03a4b4d3d9feee06a5831f1c2 (Term) Term)
(declare-fun Non_total_Tm_arrow_da9712c41bd4800828fa87c1bc605521 (Term Term) Term)
(declare-fun Non_total_Tm_arrow_e21d0d53adb3309db65169e4e063bae4 (Term) Term)
(declare-fun Non_total_Tm_arrow_eef5fa7bf2f900b7fa6a4f1653008996 (Term) Term)
(declare-fun Non_total_Tm_arrow_fd4a797c28acac3a2455c1745185ab2f (Term Term Term) Term)
; Constructor
(declare-fun Prims.Pair (Universe Universe Term Term Term Term) Term)
; Projector
(declare-fun Prims.Pair_@0 (Term) Universe)
; Projector
(declare-fun Prims.Pair_@1 (Term) Universe)
; Projector
(declare-fun Prims.Pair_@_1 (Term) Term)
; Projector
(declare-fun Prims.Pair_@_2 (Term) Term)
; Projector
(declare-fun Prims.Pair_@p (Term) Term)
; Projector
(declare-fun Prims.Pair_@q (Term) Term)
; Constructor
(declare-fun Prims.Refl (Universe Term Term) Term)
; Constructor base
(declare-fun Prims.Refl@base (Universe) Term)
; Projector
(declare-fun Prims.Refl_@0 (Term) Universe)
; Constructor
(declare-fun Prims.T () Term)
; data constructor proxy: Prims.T
(declare-fun Prims.T@tok () Term)
(declare-fun Prims.__cache_version_number__ () Term)
(declare-fun Prims.b2t (Term) Term)
(declare-fun Prims.bool () Term)
(declare-fun Prims.eq2 (Universe Term Term Term) Term)
(declare-fun Prims.eqtype () Term)
; Constructor
(declare-fun Prims.equals (Universe Term Term Term) Term)
; token
(declare-fun Prims.equals@tok (Universe) Term)
(declare-fun Prims.hasEq (Universe Term) Term)
(declare-fun Prims.int () Term)
(declare-fun Prims.l_True () Term)
(declare-fun Prims.l_and (Term Term) Term)
(declare-fun Prims.logical () Term)
(declare-fun Prims.nat () Term)
(declare-fun Prims.op_Addition (Term Term) Term)
(declare-fun Prims.op_BarBar (Term Term) Term)
(declare-fun Prims.op_Equality (Term Term Term) Term)
(declare-fun Prims.op_Equals_Equals_Equals (Universe Term Term Term Term) Term)
(declare-fun Prims.op_GreaterThan (Term Term) Term)
(declare-fun Prims.op_GreaterThanOrEqual (Term Term) Term)
(declare-fun Prims.op_LessThan (Term Term) Term)
(declare-fun Prims.op_Multiply (Term Term) Term)
(declare-fun Prims.op_Subtraction (Term Term) Term)
(declare-fun Prims.op_disEquality (Term Term Term) Term)
; Constructor
(declare-fun Prims.pair (Universe Universe Term Term) Term)
; token
(declare-fun Prims.pair@tok (Universe Universe) Term)
(declare-fun Prims.pos () Term)
; Fuel-instrumented function name
(declare-fun Prims.pow2.fuel_instrumented (Fuel Term) Term)
(declare-fun Prims.prop () Term)
(declare-fun Prims.pure_post (Universe Term) Term)
(declare-fun Prims.pure_post_ (Universe Universe Term Term) Term)
(declare-fun Prims.pure_wp (Universe Term) Term)
(declare-fun Prims.squash (Universe Term) Term)
(declare-fun Prims.subtype_of (Universe Universe Term Term) Term)
; Constructor
(declare-fun Prims.trivial () Term)
(declare-fun Prims.unit () Term)
(declare-fun Pulse.Lib.Core.emp (Dummy_sort) Term)
(declare-fun Pulse.Lib.Core.slprop () Term)
(declare-fun Pulse.Lib.Core.timeless (Term) Term)
(declare-fun Pulse.Lib.Core.timeless_emp () Term)
(declare-fun Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae (Universe Term Term) Term)
(declare-fun Tm_arrow_16f201d72071a2daf4be1ef0b08cdeb0 (Term Universe) Term)
(declare-fun Tm_arrow_8f4d0c93d793badb913a85a0bb821c13 (Term Universe) Term)
(declare-fun Tm_refine_160fe7faad9a466b3cae8455bac5be60 (Universe Term Term) Term)
(declare-fun Tm_refine_207024d2522be2ff59992eb07d6dc785 (Term) Term)
(declare-fun Tm_refine_2de20c066034c13bf76e9c0b94f4806c (Term) Term)
(declare-fun Tm_refine_542f9d4f129664613f2483a6c88bc7c2 () Term)
(declare-fun Tm_refine_774ba3f728d91ead8ef40be66c9802e5 () Term)
(declare-fun Tm_refine_7df43cb9feb536df62477b7b30ce1682 () Term)
(declare-fun Tm_refine_8856e20ff1b6ebce251f1ce59b5ef2e2 () Term)
(declare-fun Tm_refine_9d6af3f3535473623f7aec2f0501897f () Term)
(declare-fun Tm_refine_ba4be9e593fda710cd7cd90723afa87e () Term)
(declare-fun Tm_refine_cf63becb12ffbdf5c3ea7d1e75c3d75a (Universe Term) Term)
(declare-fun Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81 (Universe Term Term) Term)
; Discriminator definition
(define-fun is-FStar.Stubs.Tactics.Common.NotAListLiteral ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 102) (= __@x0 FStar.Stubs.Tactics.Common.NotAListLiteral)))
; Discriminator definition
(define-fun is-FStar.Stubs.Tactics.Common.SKIP ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 117) (= __@x0 FStar.Stubs.Tactics.Common.SKIP)))
; Discriminator definition
(define-fun is-FStar.Stubs.Tactics.Common.Stop ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 121) (= __@x0 FStar.Stubs.Tactics.Common.Stop)))
; Discriminator definition
(define-fun is-FStar.Tactics.V2.Derived.Goal_not_trivial ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 112) (= __@x0 FStar.Tactics.V2.Derived.Goal_not_trivial)))
; Discriminator definition
(define-fun is-Prims.Pair ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 157)
  (=
   __@x0
   (Prims.Pair
    (Prims.Pair_@0 __@x0)
    (Prims.Pair_@1 __@x0)
    (Prims.Pair_@p __@x0)
    (Prims.Pair_@q __@x0)
    (Prims.Pair_@_1 __@x0)
    (Prims.Pair_@_2 __@x0)))))
; Discriminator definition
(define-fun is-Prims.Refl ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 141)
  (exists ((@x0 Term) (@x1 Term))
   (! (= __@x0 (Prims.Refl (Prims.Refl_@0 __@x0) @x0 @x1)) :qid is-Prims.Refl))))
; Discriminator definition
(define-fun is-Prims.T ((__@x0 Term)) Bool (and (= (Term_constr_id __@x0) 122) (= __@x0 Prims.T)))
; Correspondence of recursive function to instrumented version
;;; Fact-ids: Name CLRS.Ch23.Kruskal.UF.find_pure; Namespace CLRS.Ch23.Kruskal.UF
(assert
 (! ;; def=CLRS.Ch23.Kruskal.UF.fsti(30,8-30,17); use=CLRS.Ch23.Kruskal.UF.fsti(30,8-30,17)
  (forall ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (=
     (CLRS.Ch23.Kruskal.UF.find_pure @x0 @x1 @x2 @x3)
     (CLRS.Ch23.Kruskal.UF.find_pure.fuel_instrumented MaxFuel @x0 @x1 @x2 @x3))
    :pattern ((CLRS.Ch23.Kruskal.UF.find_pure @x0 @x1 @x2 @x3))
    :qid @fuel_correspondence_CLRS.Ch23.Kruskal.UF.find_pure.fuel_instrumented))
  :named @fuel_correspondence_CLRS.Ch23.Kruskal.UF.find_pure.fuel_instrumented))
; Fuel irrelevance
;;; Fact-ids: Name CLRS.Ch23.Kruskal.UF.find_pure; Namespace CLRS.Ch23.Kruskal.UF
(assert
 (! ;; def=CLRS.Ch23.Kruskal.UF.fsti(30,8-30,17); use=CLRS.Ch23.Kruskal.UF.fsti(30,8-30,17)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
   (! (=
     (CLRS.Ch23.Kruskal.UF.find_pure.fuel_instrumented (SFuel @u0) @x1 @x2 @x3 @x4)
     (CLRS.Ch23.Kruskal.UF.find_pure.fuel_instrumented ZFuel @x1 @x2 @x3 @x4))
    :pattern ((CLRS.Ch23.Kruskal.UF.find_pure.fuel_instrumented (SFuel @u0) @x1 @x2 @x3 @x4))
    :qid @fuel_irrelevance_CLRS.Ch23.Kruskal.UF.find_pure.fuel_instrumented))
  :named @fuel_irrelevance_CLRS.Ch23.Kruskal.UF.find_pure.fuel_instrumented))
; Fuel irrelevance
;;; Fact-ids: Name Prims.pow2; Namespace Prims
(assert
 (! ;; def=Prims.fst(710,8-710,12); use=Prims.fst(710,8-710,12)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (= (Prims.pow2.fuel_instrumented (SFuel @u0) @x1) (Prims.pow2.fuel_instrumented ZFuel @x1))
    :pattern ((Prims.pow2.fuel_instrumented (SFuel @u0) @x1))
    :qid @fuel_irrelevance_Prims.pow2.fuel_instrumented))
  :named @fuel_irrelevance_Prims.pow2.fuel_instrumented))
; pretyping
;;; Fact-ids: Name FStar.Monotonic.Heap.core_mref; Namespace FStar.Monotonic.Heap
(assert
 (! ;; def=FStar.Monotonic.Heap.fsti(39,4-39,13); use=FStar.Monotonic.Heap.fsti(39,4-39,13)
  (forall ((@x0 Term) (@u1 Fuel) (@x2 Term))
   (! (implies
     (HasTypeFuel @u1 @x0 (FStar.Monotonic.Heap.core_mref @x2))
     (= (FStar.Monotonic.Heap.core_mref @x2) (PreType @x0)))
    :pattern ((HasTypeFuel @u1 @x0 (FStar.Monotonic.Heap.core_mref @x2)))
    :qid FStar.Monotonic.Heap_pretyping_67b0ade1260a0985dfe99d32b2574a59))
  :named FStar.Monotonic.Heap_pretyping_67b0ade1260a0985dfe99d32b2574a59))
; interpretation_Tm_arrow_16f201d72071a2daf4be1ef0b08cdeb0
;;; Fact-ids: Name FStar.Preorder.relation; Namespace FStar.Preorder
(assert
 (! ;; def=FStar.Preorder.fst(20,15-20,40); use=FStar.Preorder.fst(20,25-20,40)
  (forall ((@x0 Term) (@x1 Term) (@u2 Universe))
   (! (iff
     (HasTypeZ @x0 (Tm_arrow_16f201d72071a2daf4be1ef0b08cdeb0 @x1 @u2))
     (and
      ;; def=FStar.Preorder.fst(20,15-20,40); use=FStar.Preorder.fst(20,25-20,40)
      (forall ((@x3 Term) (@x4 Term))
       (! (implies
         (and (HasType @x3 @x1) (HasType @x4 @x1))
         (HasType (ApplyTT (ApplyTT @x0 @x3) @x4) (Tm_type U_zero)))
        :pattern ((ApplyTT (ApplyTT @x0 @x3) @x4))
        :qid FStar.Preorder_interpretation_Tm_arrow_16f201d72071a2daf4be1ef0b08cdeb0.1))
      (IsTotFun @x0)
      ;; def=FStar.Preorder.fst(20,15-20,40); use=FStar.Preorder.fst(20,25-20,40)
      (forall ((@x3 Term))
       (! (implies (HasType @x3 @x1) (IsTotFun (ApplyTT @x0 @x3)))
        :pattern ((ApplyTT @x0 @x3))
        :qid FStar.Preorder_interpretation_Tm_arrow_16f201d72071a2daf4be1ef0b08cdeb0.2))))
    :pattern ((HasTypeZ @x0 (Tm_arrow_16f201d72071a2daf4be1ef0b08cdeb0 @x1 @u2)))
    :qid FStar.Preorder_interpretation_Tm_arrow_16f201d72071a2daf4be1ef0b08cdeb0))
  :named FStar.Preorder_interpretation_Tm_arrow_16f201d72071a2daf4be1ef0b08cdeb0))
; pre-typing for functions
;;; Fact-ids: Name FStar.Preorder.relation; Namespace FStar.Preorder
(assert
 (! ;; def=FStar.Preorder.fst(20,15-20,40); use=FStar.Preorder.fst(20,25-20,40)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@u3 Universe))
   (! (implies
     (HasTypeFuel @u0 @x1 (Tm_arrow_16f201d72071a2daf4be1ef0b08cdeb0 @x2 @u3))
     (is-Tm_arrow (PreType @x1)))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_arrow_16f201d72071a2daf4be1ef0b08cdeb0 @x2 @u3)))
    :qid FStar.Preorder_pre_typing_Tm_arrow_16f201d72071a2daf4be1ef0b08cdeb0))
  :named FStar.Preorder_pre_typing_Tm_arrow_16f201d72071a2daf4be1ef0b08cdeb0))
; pretyping
;;; Fact-ids: Name FStar.Seq.Base.seq; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(23,8-23,11); use=FStar.Seq.Base.fsti(23,8-23,11)
  (forall ((@x0 Term) (@u1 Fuel) (@u2 Universe) (@x3 Term))
   (! (implies
     (HasTypeFuel @u1 @x0 (FStar.Seq.Base.seq @u2 @x3))
     (= (FStar.Seq.Base.seq @u2 @x3) (PreType @x0)))
    :pattern ((HasTypeFuel @u1 @x0 (FStar.Seq.Base.seq @u2 @x3)))
    :qid FStar.Seq.Base_pretyping_aec2ec0359b5151fd30ba679a2daadcd))
  :named FStar.Seq.Base_pretyping_aec2ec0359b5151fd30ba679a2daadcd))
; pretyping
;;; Fact-ids: Name FStar.SizeT.t; Namespace FStar.SizeT
(assert
 (! ;; def=FStar.SizeT.fsti(10,4-10,5); use=FStar.SizeT.fsti(10,4-10,5)
  (forall ((@x0 Term) (@u1 Fuel) (@u2 Dummy_sort))
   (! (implies (HasTypeFuel @u1 @x0 (FStar.SizeT.t @u2)) (= (FStar.SizeT.t @u2) (PreType @x0)))
    :pattern ((HasTypeFuel @u1 @x0 (FStar.SizeT.t @u2)))
    :qid FStar.SizeT_pretyping_4a605b34db6539ab166936a7792f508b))
  :named FStar.SizeT_pretyping_4a605b34db6539ab166936a7792f508b))
; interpretation_Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae
;;; Fact-ids: Name Prims.pure_post'; Namespace Prims
(assert
 (! ;; def=Prims.fst(323,31-323,54); use=Prims.fst(323,31-323,54)
  (forall ((@x0 Term) (@u1 Universe) (@x2 Term) (@x3 Term))
   (! (iff
     (HasTypeZ @x0 (Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae @u1 @x2 @x3))
     (and
      ;; def=Prims.fst(323,31-323,54); use=Prims.fst(323,31-323,54)
      (forall ((@x4 Term))
       (! (implies
         (HasType @x4 (Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81 @u1 @x2 @x3))
         (HasType (ApplyTT @x0 @x4) (Tm_type U_zero)))
        :pattern ((ApplyTT @x0 @x4))
        :qid Prims_interpretation_Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae.1))
      (IsTotFun @x0)))
    :pattern ((HasTypeZ @x0 (Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae @u1 @x2 @x3)))
    :qid Prims_interpretation_Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae))
  :named Prims_interpretation_Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae))
; pre-typing for functions
;;; Fact-ids: Name Prims.pure_post'; Namespace Prims
(assert
 (! ;; def=Prims.fst(323,31-323,54); use=Prims.fst(323,31-323,54)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@x3 Term) (@x4 Term))
   (! (implies
     (HasTypeFuel @u0 @x1 (Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae @u2 @x3 @x4))
     (is-Tm_arrow (PreType @x1)))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae @u2 @x3 @x4)))
    :qid Prims_pre_typing_Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae))
  :named Prims_pre_typing_Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae))
; pretyping
;;; Fact-ids: Name Prims.pair; Namespace Prims; Name Prims.Pair; Namespace Prims
(assert
 (! ;; def=Prims.fst(191,5-191,9); use=Prims.fst(191,5-191,9)
  (forall ((@x0 Term) (@u1 Fuel) (@u2 Universe) (@u3 Universe) (@x4 Term) (@x5 Term))
   (! (implies
     (HasTypeFuel @u1 @x0 (Prims.pair @u2 @u3 @x4 @x5))
     (= (Prims.pair @u2 @u3 @x4 @x5) (PreType @x0)))
    :pattern ((HasTypeFuel @u1 @x0 (Prims.pair @u2 @u3 @x4 @x5)))
    :qid Prims_pretyping_1333d5328802c11e236e8232eed17a78))
  :named Prims_pretyping_1333d5328802c11e236e8232eed17a78))
; pretyping
;;; Fact-ids: Name Prims.int; Namespace Prims
(assert
 (! ;; def=Prims.fst(522,5-522,8); use=Prims.fst(522,5-522,8)
  (forall ((@x0 Term) (@u1 Fuel))
   (! (implies (HasTypeFuel @u1 @x0 Prims.int) (= Prims.int (PreType @x0)))
    :pattern ((HasTypeFuel @u1 @x0 Prims.int))
    :qid Prims_pretyping_ae567c2fb75be05905677af440075565))
  :named Prims_pretyping_ae567c2fb75be05905677af440075565))
; pretyping
;;; Fact-ids: Name Prims.equals; Namespace Prims; Name Prims.Refl; Namespace Prims
(assert
 (! ;; def=Prims.fst(173,5-173,11); use=Prims.fst(173,5-173,11)
  (forall ((@x0 Term) (@u1 Fuel) (@u2 Universe) (@x3 Term) (@x4 Term) (@x5 Term))
   (! (implies
     (HasTypeFuel @u1 @x0 (Prims.equals @u2 @x3 @x4 @x5))
     (= (Term_constr_id (Prims.equals @u2 @x3 @x4 @x5)) (Term_constr_id (PreType @x0))))
    :pattern ((HasTypeFuel @u1 @x0 (Prims.equals @u2 @x3 @x4 @x5)))
    :qid Prims_pretyping_b6caf3433f0e1f74e18cc20e042395f8))
  :named Prims_pretyping_b6caf3433f0e1f74e18cc20e042395f8))
; pretyping
;;; Fact-ids: Name Prims.trivial; Namespace Prims; Name Prims.T; Namespace Prims
(assert
 (! ;; def=Prims.fst(99,5-99,12); use=Prims.fst(99,5-99,12)
  (forall ((@x0 Term) (@u1 Fuel))
   (! (implies (HasTypeFuel @u1 @x0 Prims.trivial) (= Prims.trivial (PreType @x0)))
    :pattern ((HasTypeFuel @u1 @x0 Prims.trivial))
    :qid Prims_pretyping_e8ffb7d227a1bbf69407a8d2ad2c4c83))
  :named Prims_pretyping_e8ffb7d227a1bbf69407a8d2ad2c4c83))
; pretyping
;;; Fact-ids: Name Prims.bool; Namespace Prims
(assert
 (! ;; def=Prims.fst(88,5-88,9); use=Prims.fst(88,5-88,9)
  (forall ((@x0 Term) (@u1 Fuel))
   (! (implies (HasTypeFuel @u1 @x0 Prims.bool) (= Prims.bool (PreType @x0)))
    :pattern ((HasTypeFuel @u1 @x0 Prims.bool))
    :qid Prims_pretyping_f537159ed795b314b4e58c260361ae86))
  :named Prims_pretyping_f537159ed795b314b4e58c260361ae86))
; pretyping
;;; Fact-ids: Name Prims.unit; Namespace Prims
(assert
 (! ;; def=Prims.fst(104,5-104,9); use=Prims.fst(104,5-104,9)
  (forall ((@x0 Term) (@u1 Fuel))
   (! (implies (HasTypeFuel @u1 @x0 Prims.unit) (= Prims.unit (PreType @x0)))
    :pattern ((HasTypeFuel @u1 @x0 Prims.unit))
    :qid Prims_pretyping_f8666440faa91836cc5a13998af863fc))
  :named Prims_pretyping_f8666440faa91836cc5a13998af863fc))
; b2t def
;;; Fact-ids: Name Prims.b2t; Namespace Prims
(assert
 (! ;; def=Prims.fst(188,5-188,8); use=Prims.fst(188,5-188,8)
  (forall ((@x0 Term))
   (! (= (Valid (Prims.b2t @x0)) (BoxBool_proj_0 @x0)) :pattern ((Prims.b2t @x0)) :qid b2t_def))
  :named b2t_def))
; b2t typing
;;; Fact-ids: Name Prims.b2t; Namespace Prims
(assert
 (! ;; def=Prims.fst(188,5-188,8); use=Prims.fst(188,5-188,8)
  (forall ((@x0 Term))
   (! (implies (HasType @x0 Prims.bool) (HasType (Prims.b2t @x0) (Tm_type U_zero)))
    :pattern ((Prims.b2t @x0))
    :qid b2t_typing))
  :named b2t_typing))
; bool inversion
;;; Fact-ids: Name Prims.bool; Namespace Prims
(assert
 (! (forall ((@u0 Fuel) (@x1 Term))
   (! (implies (HasTypeFuel @u0 @x1 Prims.bool) (is-BoxBool @x1))
    :pattern ((HasTypeFuel @u0 @x1 Prims.bool))
    :qid bool_inversion))
  :named bool_inversion))
; bool typing
;;; Fact-ids: Name Prims.bool; Namespace Prims
(assert
 (! (forall ((@u0 Bool))
   (! (HasType (BoxBool @u0) Prims.bool) :pattern ((BoxBool @u0)) :qid bool_typing))
  :named bool_typing))
; Constructor base
;;; Fact-ids: Name FStar.Stubs.Tactics.Common.NotAListLiteral; Namespace FStar.Stubs.Tactics.Common
(assert
 (! (implies
   (is-FStar.Stubs.Tactics.Common.NotAListLiteral FStar.Stubs.Tactics.Common.NotAListLiteral)
   (= FStar.Stubs.Tactics.Common.NotAListLiteral FStar.Stubs.Tactics.Common.NotAListLiteral@base))
  :named constructor_base_FStar.Stubs.Tactics.Common.NotAListLiteral))
; Constructor base
;;; Fact-ids: Name FStar.Stubs.Tactics.Common.SKIP; Namespace FStar.Stubs.Tactics.Common
(assert
 (! (implies
   (is-FStar.Stubs.Tactics.Common.SKIP FStar.Stubs.Tactics.Common.SKIP)
   (= FStar.Stubs.Tactics.Common.SKIP FStar.Stubs.Tactics.Common.SKIP@base))
  :named constructor_base_FStar.Stubs.Tactics.Common.SKIP))
; Constructor base
;;; Fact-ids: Name FStar.Stubs.Tactics.Common.Stop; Namespace FStar.Stubs.Tactics.Common
(assert
 (! (implies
   (is-FStar.Stubs.Tactics.Common.Stop FStar.Stubs.Tactics.Common.Stop)
   (= FStar.Stubs.Tactics.Common.Stop FStar.Stubs.Tactics.Common.Stop@base))
  :named constructor_base_FStar.Stubs.Tactics.Common.Stop))
; Constructor base
;;; Fact-ids: Name FStar.Tactics.V2.Derived.Goal_not_trivial; Namespace FStar.Tactics.V2.Derived
(assert
 (! (implies
   (is-FStar.Tactics.V2.Derived.Goal_not_trivial FStar.Tactics.V2.Derived.Goal_not_trivial)
   (= FStar.Tactics.V2.Derived.Goal_not_trivial FStar.Tactics.V2.Derived.Goal_not_trivial@base))
  :named constructor_base_FStar.Tactics.V2.Derived.Goal_not_trivial))
; Constructor base
;;; Fact-ids: Name Prims.equals; Namespace Prims; Name Prims.Refl; Namespace Prims
(assert
 (! ;; def=Prims.fst(173,46-173,50); use=Prims.fst(173,46-173,50)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (implies
     (is-Prims.Refl (Prims.Refl @u0 @x1 @x2))
     (= (Prims.Refl @u0 @x1 @x2) (Prims.Refl@base @u0)))
    :pattern ((Prims.Refl @u0 @x1 @x2))
    :qid constructor_base_Prims.Refl))
  :named constructor_base_Prims.Refl))
; Constructor distinct
;;; Fact-ids: Name FStar.Monotonic.Heap.core_mref; Namespace FStar.Monotonic.Heap
(assert
 (! ;; def=FStar.Monotonic.Heap.fsti(39,4-39,13); use=FStar.Monotonic.Heap.fsti(39,4-39,13)
  (forall ((@x0 Term))
   (! (= 111 (Term_constr_id (FStar.Monotonic.Heap.core_mref @x0)))
    :pattern ((FStar.Monotonic.Heap.core_mref @x0))
    :qid constructor_distinct_FStar.Monotonic.Heap.core_mref))
  :named constructor_distinct_FStar.Monotonic.Heap.core_mref))
; Constructor distinct
;;; Fact-ids: Name FStar.Seq.Base.seq; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(23,8-23,11); use=FStar.Seq.Base.fsti(23,8-23,11)
  (forall ((@u0 Universe) (@x1 Term))
   (! (= 103 (Term_constr_id (FStar.Seq.Base.seq @u0 @x1)))
    :pattern ((FStar.Seq.Base.seq @u0 @x1))
    :qid constructor_distinct_FStar.Seq.Base.seq))
  :named constructor_distinct_FStar.Seq.Base.seq))
; Constructor distinct
;;; Fact-ids: Name FStar.SizeT.t; Namespace FStar.SizeT
(assert
 (! ;; def=FStar.SizeT.fsti(10,4-10,5); use=FStar.SizeT.fsti(10,4-10,5)
  (forall ((@u0 Dummy_sort))
   (! (= 101 (Term_constr_id (FStar.SizeT.t @u0)))
    :pattern ((FStar.SizeT.t @u0))
    :qid constructor_distinct_FStar.SizeT.t))
  :named constructor_distinct_FStar.SizeT.t))
; Constructor distinct
;;; Fact-ids: Name Prims.pair; Namespace Prims; Name Prims.Pair; Namespace Prims
(assert
 (! ;; def=Prims.fst(191,34-191,38); use=Prims.fst(191,34-191,38)
  (forall ((@u0 Universe) (@u1 Universe) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term))
   (! (= 157 (Term_constr_id (Prims.Pair @u0 @u1 @x2 @x3 @x4 @x5)))
    :pattern ((Prims.Pair @u0 @u1 @x2 @x3 @x4 @x5))
    :qid constructor_distinct_Prims.Pair))
  :named constructor_distinct_Prims.Pair))
; Constructor distinct
;;; Fact-ids: Name Prims.equals; Namespace Prims; Name Prims.Refl; Namespace Prims
(assert
 (! ;; def=Prims.fst(173,46-173,50); use=Prims.fst(173,46-173,50)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (= 141 (Term_constr_id (Prims.Refl @u0 @x1 @x2)))
    :pattern ((Prims.Refl @u0 @x1 @x2))
    :qid constructor_distinct_Prims.Refl))
  :named constructor_distinct_Prims.Refl))
; Constructor distinct
;;; Fact-ids: Name Prims.trivial; Namespace Prims; Name Prims.T; Namespace Prims
(assert
 (! (= 122 (Term_constr_id Prims.T)) :named constructor_distinct_Prims.T))
; Constructor distinct
;;; Fact-ids: Name Prims.bool; Namespace Prims
(assert
 (! (= 107 (Term_constr_id Prims.bool)) :named constructor_distinct_Prims.bool))
; Constructor distinct
;;; Fact-ids: Name Prims.equals; Namespace Prims; Name Prims.Refl; Namespace Prims
(assert
 (! ;; def=Prims.fst(173,5-173,11); use=Prims.fst(173,5-173,11)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (= 134 (Term_constr_id (Prims.equals @u0 @x1 @x2 @x3)))
    :pattern ((Prims.equals @u0 @x1 @x2 @x3))
    :qid constructor_distinct_Prims.equals))
  :named constructor_distinct_Prims.equals))
; Constructor distinct
;;; Fact-ids: Name Prims.int; Namespace Prims
(assert
 (! (= 303 (Term_constr_id Prims.int)) :named constructor_distinct_Prims.int))
; Constructor distinct
;;; Fact-ids: Name Prims.pair; Namespace Prims; Name Prims.Pair; Namespace Prims
(assert
 (! ;; def=Prims.fst(191,5-191,9); use=Prims.fst(191,5-191,9)
  (forall ((@u0 Universe) (@u1 Universe) (@x2 Term) (@x3 Term))
   (! (= 150 (Term_constr_id (Prims.pair @u0 @u1 @x2 @x3)))
    :pattern ((Prims.pair @u0 @u1 @x2 @x3))
    :qid constructor_distinct_Prims.pair))
  :named constructor_distinct_Prims.pair))
; Constructor distinct
;;; Fact-ids: Name Prims.trivial; Namespace Prims; Name Prims.T; Namespace Prims
(assert
 (! (= 116 (Term_constr_id Prims.trivial)) :named constructor_distinct_Prims.trivial))
; Constructor distinct
;;; Fact-ids: Name Prims.unit; Namespace Prims
(assert
 (! (= 125 (Term_constr_id Prims.unit)) :named constructor_distinct_Prims.unit))
; data constructor typing elim
;;; Fact-ids: Name Prims.pair; Namespace Prims; Name Prims.Pair; Namespace Prims
(assert
 (! ;; def=Prims.fst(191,34-191,38); use=Prims.fst(191,34-191,38)
  (forall
    ((@u0 Fuel)
     (@u1 Universe)
     (@u2 Universe)
     (@x3 Term)
     (@x4 Term)
     (@x5 Term)
     (@x6 Term)
     (@x7 Term)
     (@x8 Term))
   (! (implies
     (HasTypeFuel (SFuel @u0) (Prims.Pair @u1 @u2 @x3 @x4 @x5 @x6) (Prims.pair @u1 @u2 @x7 @x8))
     (and
      (HasTypeFuel @u0 @x7 (Tm_type @u1))
      (HasTypeFuel @u0 @x8 (Tm_type @u2))
      (HasTypeFuel @u0 @x5 @x7)
      (HasTypeFuel @u0 @x6 @x8)))
    :pattern
     ((HasTypeFuel (SFuel @u0) (Prims.Pair @u1 @u2 @x3 @x4 @x5 @x6) (Prims.pair @u1 @u2 @x7 @x8)))
    :qid data_elim_Prims.Pair))
  :named data_elim_Prims.Pair))
; data constructor typing elim
;;; Fact-ids: Name Prims.equals; Namespace Prims; Name Prims.Refl; Namespace Prims
(assert
 (! ;; def=Prims.fst(173,46-173,50); use=Prims.fst(173,46-173,50)
  (forall ((@u0 Fuel) (@u1 Universe) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term) (@x6 Term))
   (! (implies
     (HasTypeFuel (SFuel @u0) (Prims.Refl @u1 @x2 @x3) (Prims.equals @u1 @x4 @x5 @x6))
     (and (= @x5 @x6) (HasTypeFuel @u0 @x4 (Tm_type @u1)) (HasTypeFuel @u0 @x5 @x4)))
    :pattern ((HasTypeFuel (SFuel @u0) (Prims.Refl @u1 @x2 @x3) (Prims.equals @u1 @x4 @x5 @x6)))
    :qid data_elim_Prims.Refl))
  :named data_elim_Prims.Refl))
; data constructor typing intro
;;; Fact-ids: Name Prims.pair; Namespace Prims; Name Prims.Pair; Namespace Prims
(assert
 (! ;; def=Prims.fst(191,34-191,38); use=Prims.fst(191,34-191,38)
  (forall ((@u0 Fuel) (@u1 Universe) (@u2 Universe) (@x3 Term) (@x4 Term) (@x5 Term) (@x6 Term))
   (! (implies
     (and
      (HasTypeFuel @u0 @x3 (Tm_type @u1))
      (HasTypeFuel @u0 @x4 (Tm_type @u2))
      (HasTypeFuel @u0 @x5 @x3)
      (HasTypeFuel @u0 @x6 @x4))
     (HasTypeFuel @u0 (Prims.Pair @u1 @u2 @x3 @x4 @x5 @x6) (Prims.pair @u1 @u2 @x3 @x4)))
    :pattern ((HasTypeFuel @u0 (Prims.Pair @u1 @u2 @x3 @x4 @x5 @x6) (Prims.pair @u1 @u2 @x3 @x4)))
    :qid data_typing_intro_Prims.Pair@tok))
  :named data_typing_intro_Prims.Pair@tok))
; data constructor typing intro
;;; Fact-ids: Name Prims.equals; Namespace Prims; Name Prims.Refl; Namespace Prims
(assert
 (! ;; def=Prims.fst(173,46-173,50); use=Prims.fst(173,46-173,50)
  (forall ((@u0 Fuel) (@u1 Universe) (@x2 Term) (@x3 Term) (@x4 Term))
   (! (implies
     (and (HasTypeFuel @u0 @x2 (Tm_type @u1)) (HasTypeFuel @u0 @x3 @x2) (= @x3 @x4))
     (HasTypeFuel @u0 (Prims.Refl @u1 @x2 @x3) (Prims.equals @u1 @x2 @x3 @x4)))
    :pattern ((HasTypeFuel @u0 (Prims.Refl @u1 @x2 @x3) (Prims.equals @u1 @x2 @x3 @x4)))
    :qid data_typing_intro_Prims.Refl@tok))
  :named data_typing_intro_Prims.Refl@tok))
; data constructor typing intro
;;; Fact-ids: Name Prims.trivial; Namespace Prims; Name Prims.T; Namespace Prims
(assert
 (! ;; def=Prims.fst(99,17-99,18); use=Prims.fst(99,17-99,18)
  (forall ((@u0 Fuel))
   (! (HasTypeFuel @u0 Prims.T Prims.trivial)
    :pattern ((HasTypeFuel @u0 Prims.T Prims.trivial))
    :qid data_typing_intro_Prims.T@tok))
  :named data_typing_intro_Prims.T@tok))
; Prop-typing for FStar.Preorder.preorder_rel
;;; Fact-ids: Name FStar.Preorder.preorder_rel; Namespace FStar.Preorder
(assert
 (! ;; def=FStar.Preorder.fst(30,4-30,16); use=FStar.Preorder.fst(30,4-30,16)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (implies
     (and (HasType @x1 (Tm_type @u0)) (HasType @x2 (FStar.Preorder.relation @u0 @x1)))
     (Valid (Prims.subtype_of U_zero U_zero (FStar.Preorder.preorder_rel @u0 @x1 @x2) Prims.unit)))
    :pattern ((Prims.subtype_of U_zero U_zero (FStar.Preorder.preorder_rel @u0 @x1 @x2) Prims.unit))
    :qid defn_equation_FStar.Preorder.preorder_rel))
  :named defn_equation_FStar.Preorder.preorder_rel))
; Prop-typing for FStar.Preorder.reflexive
;;; Fact-ids: Name FStar.Preorder.reflexive; Namespace FStar.Preorder
(assert
 (! ;; def=FStar.Preorder.fst(24,4-24,13); use=FStar.Preorder.fst(24,4-24,13)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (implies
     (and (HasType @x1 (Tm_type @u0)) (HasType @x2 (FStar.Preorder.relation @u0 @x1)))
     (Valid (Prims.subtype_of U_zero U_zero (FStar.Preorder.reflexive @u0 @x1 @x2) Prims.unit)))
    :pattern ((Prims.subtype_of U_zero U_zero (FStar.Preorder.reflexive @u0 @x1 @x2) Prims.unit))
    :qid defn_equation_FStar.Preorder.reflexive))
  :named defn_equation_FStar.Preorder.reflexive))
; Prop-typing for FStar.Preorder.transitive
;;; Fact-ids: Name FStar.Preorder.transitive; Namespace FStar.Preorder
(assert
 (! ;; def=FStar.Preorder.fst(27,4-27,14); use=FStar.Preorder.fst(27,4-27,14)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (implies
     (and (HasType @x1 (Tm_type @u0)) (HasType @x2 (FStar.Preorder.relation @u0 @x1)))
     (Valid (Prims.subtype_of U_zero U_zero (FStar.Preorder.transitive @u0 @x1 @x2) Prims.unit)))
    :pattern ((Prims.subtype_of U_zero U_zero (FStar.Preorder.transitive @u0 @x1 @x2) Prims.unit))
    :qid defn_equation_FStar.Preorder.transitive))
  :named defn_equation_FStar.Preorder.transitive))
; Prop-typing for Prims.op_Equals_Equals_Equals
;;; Fact-ids: Name Prims.op_Equals_Equals_Equals; Namespace Prims
(assert
 (! ;; def=Prims.fst(506,6-506,9); use=Prims.fst(506,6-506,9)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
   (! (implies
     (and
      (HasType @x1 (Tm_type @u0))
      (HasType @x2 (Tm_type @u0))
      (HasType @x3 @x1)
      (HasType @x4 @x2))
     (Valid
      (Prims.subtype_of U_zero U_zero (Prims.op_Equals_Equals_Equals @u0 @x1 @x2 @x3 @x4) Prims.unit)))
    :pattern
     ((Prims.subtype_of U_zero U_zero (Prims.op_Equals_Equals_Equals @u0 @x1 @x2 @x3 @x4) Prims.unit))
    :qid defn_equation_Prims.op_Equals_Equals_Equals))
  :named defn_equation_Prims.op_Equals_Equals_Equals))
; Prop-typing for Prims.subtype_of
;;; Fact-ids: Name Prims.subtype_of; Namespace Prims
(assert
 (! ;; def=Prims.fst(299,4-299,14); use=Prims.fst(299,4-299,14)
  (forall ((@u0 Universe) (@u1 Universe) (@x2 Term) (@x3 Term))
   (! (implies
     (and (HasType @x2 (Tm_type @u0)) (HasType @x3 (Tm_type @u1)))
     (Valid (Prims.subtype_of U_zero U_zero (Prims.subtype_of @u0 @u1 @x2 @x3) Prims.unit)))
    :pattern ((Prims.subtype_of U_zero U_zero (Prims.subtype_of @u0 @u1 @x2 @x3) Prims.unit))
    :qid defn_equation_Prims.subtype_of))
  :named defn_equation_Prims.subtype_of))
; Eq2 interpretation
;;; Fact-ids: Name Prims.eq2; Namespace Prims
(assert
 (! (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (iff (= @x2 @x3) (Valid (Prims.eq2 @u0 @x1 @x2 @x3)))
    :pattern ((Prims.eq2 @u0 @x1 @x2 @x3))
    :qid eq2-interp))
  :named eq2-interp))
; equality for proxy
;;; Fact-ids: Name Prims.trivial; Namespace Prims; Name Prims.T; Namespace Prims
(assert
 (! (= Prims.T@tok Prims.T) :named equality_tok_Prims.T@tok))
; Equation for FStar.Monotonic.Heap.mref
;;; Fact-ids: Name FStar.Monotonic.Heap.mref; Namespace FStar.Monotonic.Heap
(assert
 (! ;; def=FStar.Monotonic.Heap.fsti(41,4-41,8); use=FStar.Monotonic.Heap.fsti(41,4-41,8)
  (forall ((@x0 Term) (@x1 Term))
   (! (= (FStar.Monotonic.Heap.mref @x0 @x1) (FStar.Monotonic.Heap.core_mref @x0))
    :pattern ((FStar.Monotonic.Heap.mref @x0 @x1))
    :qid equation_FStar.Monotonic.Heap.mref))
  :named equation_FStar.Monotonic.Heap.mref))
; Equation for FStar.Preorder.preorder
;;; Fact-ids: Name FStar.Preorder.preorder; Namespace FStar.Preorder
(assert
 (! ;; def=FStar.Preorder.fst(33,5-33,13); use=FStar.Preorder.fst(33,5-33,13)
  (forall ((@u0 Universe) (@x1 Term))
   (! (= (FStar.Preorder.preorder @u0 @x1) (Tm_refine_cf63becb12ffbdf5c3ea7d1e75c3d75a @u0 @x1))
    :pattern ((FStar.Preorder.preorder @u0 @x1))
    :qid equation_FStar.Preorder.preorder))
  :named equation_FStar.Preorder.preorder))
; Equation for FStar.Preorder.preorder_rel
;;; Fact-ids: Name FStar.Preorder.preorder_rel; Namespace FStar.Preorder
(assert
 (! ;; def=FStar.Preorder.fst(30,4-30,16); use=FStar.Preorder.fst(30,4-30,16)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (=
     (Valid (FStar.Preorder.preorder_rel @u0 @x1 @x2))
     ;; def=FStar.Preorder.fst(31,2-31,33); use=FStar.Preorder.fst(31,2-31,33)
     (and
      ;; def=FStar.Preorder.fst(31,2-31,15); use=FStar.Preorder.fst(31,2-31,15)
      (Valid
       ;; def=FStar.Preorder.fst(31,2-31,15); use=FStar.Preorder.fst(31,2-31,15)
       (FStar.Preorder.reflexive @u0 @x1 @x2))
      ;; def=FStar.Preorder.fst(31,19-31,33); use=FStar.Preorder.fst(31,19-31,33)
      (Valid
       ;; def=FStar.Preorder.fst(31,19-31,33); use=FStar.Preorder.fst(31,19-31,33)
       (FStar.Preorder.transitive @u0 @x1 @x2))))
    :pattern ((FStar.Preorder.preorder_rel @u0 @x1 @x2))
    :qid equation_FStar.Preorder.preorder_rel))
  :named equation_FStar.Preorder.preorder_rel))
; Equation for FStar.Preorder.reflexive
;;; Fact-ids: Name FStar.Preorder.reflexive; Namespace FStar.Preorder
(assert
 (! ;; def=FStar.Preorder.fst(24,4-24,13); use=FStar.Preorder.fst(24,4-24,13)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (=
     (Valid (FStar.Preorder.reflexive @u0 @x1 @x2))
     ;; def=FStar.Preorder.fst(25,2-25,23); use=FStar.Preorder.fst(25,2-25,23)
     (forall ((@x3 Term))
      (! (implies
        (HasType @x3 @x1)
        ;; def=FStar.Preorder.fst(25,16-25,23); use=FStar.Preorder.fst(25,16-25,23)
        (Valid
         ;; def=FStar.Preorder.fst(25,16-25,23); use=FStar.Preorder.fst(25,16-25,23)
         (ApplyTT (ApplyTT @x2 @x3) @x3)))
       :qid equation_FStar.Preorder.reflexive.1)))
    :pattern ((FStar.Preorder.reflexive @u0 @x1 @x2))
    :qid equation_FStar.Preorder.reflexive))
  :named equation_FStar.Preorder.reflexive))
; Equation for FStar.Preorder.relation
;;; Fact-ids: Name FStar.Preorder.relation; Namespace FStar.Preorder
(assert
 (! ;; def=FStar.Preorder.fst(20,5-20,13); use=FStar.Preorder.fst(20,5-20,13)
  (forall ((@u0 Universe) (@x1 Term))
   (! (= (FStar.Preorder.relation @u0 @x1) (Tm_arrow_16f201d72071a2daf4be1ef0b08cdeb0 @x1 @u0))
    :pattern ((FStar.Preorder.relation @u0 @x1))
    :qid equation_FStar.Preorder.relation))
  :named equation_FStar.Preorder.relation))
; Equation for FStar.Preorder.transitive
;;; Fact-ids: Name FStar.Preorder.transitive; Namespace FStar.Preorder
(assert
 (! ;; def=FStar.Preorder.fst(27,4-27,14); use=FStar.Preorder.fst(27,4-27,14)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (=
     (Valid (FStar.Preorder.transitive @u0 @x1 @x2))
     ;; def=FStar.Preorder.fst(28,2-28,60); use=FStar.Preorder.fst(28,2-28,60)
     (forall ((@x3 Term) (@x4 Term) (@x5 Term))
      (! (implies
        (and
         (HasType @x3 @x1)
         (HasType @x4 @x1)
         (HasType @x5 @x1)
         ;; def=FStar.Preorder.fst(28,29-28,36); use=FStar.Preorder.fst(28,29-28,36)
         (Valid
          ;; def=FStar.Preorder.fst(28,29-28,36); use=FStar.Preorder.fst(28,29-28,36)
          (ApplyTT (ApplyTT @x2 @x3) @x4))
         ;; def=FStar.Preorder.fst(28,40-28,47); use=FStar.Preorder.fst(28,40-28,47)
         (Valid
          ;; def=FStar.Preorder.fst(28,40-28,47); use=FStar.Preorder.fst(28,40-28,47)
          (ApplyTT (ApplyTT @x2 @x4) @x5)))
        ;; def=FStar.Preorder.fst(28,53-28,60); use=FStar.Preorder.fst(28,53-28,60)
        (Valid
         ;; def=FStar.Preorder.fst(28,53-28,60); use=FStar.Preorder.fst(28,53-28,60)
         (ApplyTT (ApplyTT @x2 @x3) @x5)))
       :qid equation_FStar.Preorder.transitive.1)))
    :pattern ((FStar.Preorder.transitive @u0 @x1 @x2))
    :qid equation_FStar.Preorder.transitive))
  :named equation_FStar.Preorder.transitive))
; Equation for Prims.eq2
;;; Fact-ids: Name Prims.eq2; Namespace Prims
(assert
 (! ;; def=Prims.fst(183,5-183,8); use=Prims.fst(183,5-183,8)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (= (Prims.eq2 @u0 @x1 @x2 @x3) (Prims.squash U_zero (Prims.equals @u0 @x1 @x2 @x3)))
    :pattern ((Prims.eq2 @u0 @x1 @x2 @x3))
    :qid equation_Prims.eq2))
  :named equation_Prims.eq2))
; Equation for Prims.eqtype
;;; Fact-ids: Name Prims.eqtype; Namespace Prims
(assert
 (! (= Prims.eqtype Tm_refine_9d6af3f3535473623f7aec2f0501897f) :named equation_Prims.eqtype))
; Equation for Prims.l_True
;;; Fact-ids: Name Prims.l_True; Namespace Prims
(assert
 (! (= Prims.l_True (Prims.squash U_zero Prims.trivial)) :named equation_Prims.l_True))
; Equation for Prims.l_and
;;; Fact-ids: Name Prims.l_and; Namespace Prims
(assert
 (! ;; def=Prims.fst(196,5-196,10); use=Prims.fst(196,5-196,10)
  (forall ((@x0 Term) (@x1 Term))
   (! (= (Prims.l_and @x0 @x1) (Prims.squash U_zero (Prims.pair U_zero U_zero @x0 @x1)))
    :pattern ((Prims.l_and @x0 @x1))
    :qid equation_Prims.l_and))
  :named equation_Prims.l_and))
; Equation for Prims.logical
;;; Fact-ids: Name Prims.logical; Namespace Prims
(assert
 (! (= Prims.logical (Tm_type U_zero)) :named equation_Prims.logical))
; Equation for Prims.nat
;;; Fact-ids: Name Prims.nat; Namespace Prims
(assert
 (! (= Prims.nat Tm_refine_542f9d4f129664613f2483a6c88bc7c2) :named equation_Prims.nat))
; Equation for Prims.op_Equals_Equals_Equals
;;; Fact-ids: Name Prims.op_Equals_Equals_Equals; Namespace Prims
(assert
 (! ;; def=Prims.fst(506,6-506,9); use=Prims.fst(506,6-506,9)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
   (! (=
     (Valid (Prims.op_Equals_Equals_Equals @u0 @x1 @x2 @x3 @x4))
     ;; def=Prims.fst(506,52-506,68); use=Prims.fst(506,52-506,68)
     (and
      ;; def=Prims.fst(506,52-506,58); use=Prims.fst(506,52-506,58)
      (= @x1 @x2)
      ;; def=Prims.fst(506,62-506,68); use=Prims.fst(506,62-506,68)
      (= @x3 @x4)))
    :pattern ((Prims.op_Equals_Equals_Equals @u0 @x1 @x2 @x3 @x4))
    :qid equation_Prims.op_Equals_Equals_Equals))
  :named equation_Prims.op_Equals_Equals_Equals))
; Equation for Prims.pos
;;; Fact-ids: Name Prims.pos; Namespace Prims
(assert
 (! (= Prims.pos Tm_refine_774ba3f728d91ead8ef40be66c9802e5) :named equation_Prims.pos))
; Equation for Prims.prop
;;; Fact-ids: Name Prims.prop; Namespace Prims
(assert
 (! (= Prims.prop Tm_refine_ba4be9e593fda710cd7cd90723afa87e) :named equation_Prims.prop))
; Equation for Prims.pure_post
;;; Fact-ids: Name Prims.pure_post; Namespace Prims
(assert
 (! ;; def=Prims.fst(324,4-324,13); use=Prims.fst(324,4-324,13)
  (forall ((@u0 Universe) (@x1 Term))
   (! (= (Prims.pure_post @u0 @x1) (Prims.pure_post_ @u0 U_zero @x1 Prims.l_True))
    :pattern ((Prims.pure_post @u0 @x1))
    :qid equation_Prims.pure_post))
  :named equation_Prims.pure_post))
; Equation for Prims.pure_post'
;;; Fact-ids: Name Prims.pure_post'; Namespace Prims
(assert
 (! ;; def=Prims.fst(323,4-323,14); use=Prims.fst(323,4-323,14)
  (forall ((@u0 Universe) (@u1 Universe) (@x2 Term) (@x3 Term))
   (! (= (Prims.pure_post_ @u0 @u1 @x2 @x3) (Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae @u0 @x3 @x2))
    :pattern ((Prims.pure_post_ @u0 @u1 @x2 @x3))
    :qid equation_Prims.pure_post_))
  :named equation_Prims.pure_post_))
; Equation for Prims.squash
;;; Fact-ids: Name Prims.squash; Namespace Prims
(assert
 (! ;; def=Prims.fst(125,5-125,11); use=Prims.fst(125,5-125,11)
  (forall ((@u0 Universe) (@x1 Term))
   (! (= (Prims.squash @u0 @x1) (Tm_refine_2de20c066034c13bf76e9c0b94f4806c @x1))
    :pattern ((Prims.squash @u0 @x1))
    :qid equation_Prims.squash))
  :named equation_Prims.squash))
; Equation for Prims.subtype_of
;;; Fact-ids: Name Prims.subtype_of; Namespace Prims
(assert
 (! ;; def=Prims.fst(299,4-299,14); use=Prims.fst(299,4-299,14)
  (forall ((@u0 Universe) (@u1 Universe) (@x2 Term) (@x3 Term))
   (! (=
     (Valid (Prims.subtype_of @u0 @u1 @x2 @x3))
     ;; def=Prims.fst(299,31-299,60); use=Prims.fst(299,31-299,60)
     (forall ((@x4 Term))
      (! (implies (HasType @x4 @x2) (HasType @x4 @x3)) :qid equation_Prims.subtype_of.1)))
    :pattern ((Prims.subtype_of @u0 @u1 @x2 @x3))
    :qid equation_Prims.subtype_of))
  :named equation_Prims.subtype_of))
; Equation for fuel-instrumented recursive function: CLRS.Ch23.Kruskal.UF.find_pure
;;; Fact-ids: Name CLRS.Ch23.Kruskal.UF.find_pure; Namespace CLRS.Ch23.Kruskal.UF
(assert
 (! ;; def=CLRS.Ch23.Kruskal.UF.fsti(30,8-30,17); use=CLRS.Ch23.Kruskal.UF.fsti(30,8-30,17)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
   (! (implies
     (and
      (HasType @x1 (FStar.Seq.Base.seq U_zero (FStar.SizeT.t Dummy_value)))
      (HasType @x2 Prims.nat)
      (HasType @x3 Prims.nat)
      (HasType @x4 Prims.nat))
     (=
      (CLRS.Ch23.Kruskal.UF.find_pure.fuel_instrumented (SFuel @u0) @x1 @x2 @x3 @x4)
      (let
        ((@lb5
          (Prims.op_BarBar
           (Prims.op_BarBar
            (Prims.op_Equality Prims.int @x3 (BoxInt 0))
            (Prims.op_GreaterThanOrEqual @x2 @x4))
           (Prims.op_disEquality
            Prims.nat
            (FStar.Seq.Base.length U_zero (FStar.SizeT.t Dummy_value) @x1)
            @x4))))
       (ite
        (= @lb5 (BoxBool true))
        @x2
        (CLRS.Ch23.Kruskal.UF.find_pure.fuel_instrumented
         @u0
         @x1
         (FStar.SizeT.v (FStar.Seq.Base.index U_zero (FStar.SizeT.t Dummy_value) @x1 @x2))
         (Prims.op_Subtraction @x3 (BoxInt 1))
         @x4)))))
    :weight 0
    :pattern ((CLRS.Ch23.Kruskal.UF.find_pure.fuel_instrumented (SFuel @u0) @x1 @x2 @x3 @x4))
    :qid equation_with_fuel_CLRS.Ch23.Kruskal.UF.find_pure.fuel_instrumented))
  :named equation_with_fuel_CLRS.Ch23.Kruskal.UF.find_pure.fuel_instrumented))
; Equation for fuel-instrumented recursive function: Prims.pow2
;;; Fact-ids: Name Prims.pow2; Namespace Prims
(assert
 (! ;; def=Prims.fst(710,8-710,12); use=Prims.fst(710,8-710,12)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (implies
     (HasType @x1 Prims.nat)
     (=
      (Prims.pow2.fuel_instrumented (SFuel @u0) @x1)
      (let ((@lb2 @x1))
       (ite
        (= @lb2 (BoxInt 0))
        (BoxInt 1)
        (Prims.op_Multiply
         (BoxInt 2)
         (Prims.pow2.fuel_instrumented @u0 (Prims.op_Subtraction @x1 (BoxInt 1))))))))
    :weight 0
    :pattern ((Prims.pow2.fuel_instrumented (SFuel @u0) @x1))
    :qid equation_with_fuel_Prims.pow2.fuel_instrumented))
  :named equation_with_fuel_Prims.pow2.fuel_instrumented))
; fresh token
;;; Fact-ids: Name Prims.equals; Namespace Prims; Name Prims.Refl; Namespace Prims
(assert
 (! (forall ((@u0 Universe))
   (! (= 135 (Term_constr_id (Prims.equals@tok @u0)))
    :pattern ((Prims.equals@tok @u0))
    :qid fresh_token_Prims.equals@tok))
  :named fresh_token_Prims.equals@tok))
; fresh token
;;; Fact-ids: Name Prims.pair; Namespace Prims; Name Prims.Pair; Namespace Prims
(assert
 (! (forall ((@u0 Universe) (@u1 Universe))
   (! (= 151 (Term_constr_id (Prims.pair@tok @u0 @u1)))
    :pattern ((Prims.pair@tok @u0 @u1))
    :qid fresh_token_Prims.pair@tok))
  :named fresh_token_Prims.pair@tok))
; inversion axiom
;;; Fact-ids: Name Prims.equals; Namespace Prims; Name Prims.Refl; Namespace Prims
(assert
 (! ;; def=Prims.fst(173,5-173,11); use=Prims.fst(173,5-173,11)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@x3 Term) (@x4 Term) (@x5 Term))
   (! (implies
     (HasTypeFuel @u0 @x1 (Prims.equals @u2 @x3 @x4 @x5))
     (and (is-Prims.Refl @x1) (= @u2 (Prims.Refl_@0 @x1))))
    :pattern ((HasTypeFuel @u0 @x1 (Prims.equals @u2 @x3 @x4 @x5)))
    :qid fuel_guarded_inversion_Prims.equals))
  :named fuel_guarded_inversion_Prims.equals))
; inversion axiom
;;; Fact-ids: Name Prims.pair; Namespace Prims; Name Prims.Pair; Namespace Prims
(assert
 (! ;; def=Prims.fst(191,5-191,9); use=Prims.fst(191,5-191,9)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@u3 Universe) (@x4 Term) (@x5 Term))
   (! (implies
     (HasTypeFuel @u0 @x1 (Prims.pair @u2 @u3 @x4 @x5))
     (and
      (is-Prims.Pair @x1)
      (= @u2 (Prims.Pair_@0 @x1))
      (= @u3 (Prims.Pair_@1 @x1))
      (= @x4 (Prims.Pair_@p @x1))
      (= @x5 (Prims.Pair_@q @x1))))
    :pattern ((HasTypeFuel @u0 @x1 (Prims.pair @u2 @u3 @x4 @x5)))
    :qid fuel_guarded_inversion_Prims.pair))
  :named fuel_guarded_inversion_Prims.pair))
; inversion axiom
;;; Fact-ids: Name Prims.trivial; Namespace Prims; Name Prims.T; Namespace Prims
(assert
 (! ;; def=Prims.fst(99,5-99,12); use=Prims.fst(99,5-99,12)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (implies (HasTypeFuel @u0 @x1 Prims.trivial) (is-Prims.T @x1))
    :pattern ((HasTypeFuel @u0 @x1 Prims.trivial))
    :qid fuel_guarded_inversion_Prims.trivial))
  :named fuel_guarded_inversion_Prims.trivial))
; function token typing
;;; Fact-ids: Name FStar.Monotonic.Heap.lemma_mref_injectivity; Namespace FStar.Monotonic.Heap
(assert
 (! (HasType FStar.Monotonic.Heap.lemma_mref_injectivity Tm_refine_8856e20ff1b6ebce251f1ce59b5ef2e2)
  :named function_token_typing_FStar.Monotonic.Heap.lemma_mref_injectivity))
; function token typing
;;; Fact-ids: Name Prims.__cache_version_number__; Namespace Prims
(assert
 (! (HasType Prims.__cache_version_number__ Prims.int)
  :named function_token_typing_Prims.__cache_version_number__))
; function token typing
;;; Fact-ids: Name Prims.bool; Namespace Prims
(assert
 (! (HasType Prims.bool Prims.eqtype) :named function_token_typing_Prims.bool))
; function token typing
;;; Fact-ids: Name Prims.eqtype; Namespace Prims
(assert
 (! (HasType Prims.eqtype (Tm_type (U_succ U_zero))) :named function_token_typing_Prims.eqtype))
; function token typing
;;; Fact-ids: Name Prims.int; Namespace Prims
(assert
 (! (HasType Prims.int Prims.eqtype) :named function_token_typing_Prims.int))
; function token typing
;;; Fact-ids: Name Prims.l_True; Namespace Prims
(assert
 (! (HasType Prims.l_True Prims.logical) :named function_token_typing_Prims.l_True))
; function token typing
;;; Fact-ids: Name Prims.logical; Namespace Prims
(assert
 (! (HasType Prims.logical (Tm_type (U_succ U_zero))) :named function_token_typing_Prims.logical))
; function token typing
;;; Fact-ids: Name Prims.nat; Namespace Prims
(assert
 (! (HasType Prims.nat (Tm_type U_zero)) :named function_token_typing_Prims.nat))
; function token typing
;;; Fact-ids: Name Prims.pos; Namespace Prims
(assert
 (! (HasType Prims.pos (Tm_type U_zero)) :named function_token_typing_Prims.pos))
; function token typing
;;; Fact-ids: Name Prims.prop; Namespace Prims
(assert
 (! (HasType Prims.prop (Tm_type (U_succ U_zero))) :named function_token_typing_Prims.prop))
; function token typing
;;; Fact-ids: Name Prims.unit; Namespace Prims
(assert
 (! (HasType Prims.unit Prims.eqtype) :named function_token_typing_Prims.unit))
; function token typing
;;; Fact-ids: Name Pulse.Lib.Core.slprop; Namespace Pulse.Lib.Core
(assert
 (! (HasType Pulse.Lib.Core.slprop (Tm_type (U_succ (U_succ (U_succ (U_succ U_zero))))))
  :named function_token_typing_Pulse.Lib.Core.slprop))
; function token typing
;;; Fact-ids: Name Pulse.Lib.Core.timeless_emp; Namespace Pulse.Lib.Core
(assert
 (! (HasType
   Pulse.Lib.Core.timeless_emp
   (Prims.squash U_zero (Pulse.Lib.Core.timeless (Pulse.Lib.Core.emp Dummy_value))))
  :named function_token_typing_Pulse.Lib.Core.timeless_emp))
; haseq for Tm_refine_160fe7faad9a466b3cae8455bac5be60
;;; Fact-ids: Name FStar.Seq.Base.index; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(32,34-32,53); use=FStar.Seq.Base.fsti(32,34-32,53)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (iff
     (Valid (Prims.hasEq U_zero (Tm_refine_160fe7faad9a466b3cae8455bac5be60 @u0 @x1 @x2)))
     (Valid (Prims.hasEq U_zero Prims.nat)))
    :pattern ((Valid (Prims.hasEq U_zero (Tm_refine_160fe7faad9a466b3cae8455bac5be60 @u0 @x1 @x2))))
    :qid haseqTm_refine_160fe7faad9a466b3cae8455bac5be60))
  :named haseqTm_refine_160fe7faad9a466b3cae8455bac5be60))
; haseq for Tm_refine_207024d2522be2ff59992eb07d6dc785
;;; Fact-ids: Name FStar.SizeT.uint_to_t; Namespace FStar.SizeT
(assert
 (! ;; def=FStar.SizeT.fsti(39,30-39,31); use=FStar.SizeT.fsti(39,30-39,31)
  (forall ((@x0 Term))
   (! (iff
     (Valid (Prims.hasEq U_zero (Tm_refine_207024d2522be2ff59992eb07d6dc785 @x0)))
     (Valid (Prims.hasEq U_zero (FStar.SizeT.t Dummy_value))))
    :pattern ((Valid (Prims.hasEq U_zero (Tm_refine_207024d2522be2ff59992eb07d6dc785 @x0))))
    :qid haseqTm_refine_207024d2522be2ff59992eb07d6dc785))
  :named haseqTm_refine_207024d2522be2ff59992eb07d6dc785))
; haseq for Tm_refine_2de20c066034c13bf76e9c0b94f4806c
;;; Fact-ids: Name Prims.squash; Namespace Prims
(assert
 (! ;; def=Prims.fst(125,32-125,42); use=Prims.fst(125,32-125,42)
  (forall ((@x0 Term))
   (! (iff
     (Valid (Prims.hasEq U_zero (Tm_refine_2de20c066034c13bf76e9c0b94f4806c @x0)))
     (Valid (Prims.hasEq U_zero Prims.unit)))
    :pattern ((Valid (Prims.hasEq U_zero (Tm_refine_2de20c066034c13bf76e9c0b94f4806c @x0))))
    :qid haseqTm_refine_2de20c066034c13bf76e9c0b94f4806c))
  :named haseqTm_refine_2de20c066034c13bf76e9c0b94f4806c))
; haseq for Tm_refine_542f9d4f129664613f2483a6c88bc7c2
;;; Fact-ids: Name Prims.nat; Namespace Prims
(assert
 (! (iff
   (Valid (Prims.hasEq U_zero Tm_refine_542f9d4f129664613f2483a6c88bc7c2))
   (Valid (Prims.hasEq U_zero Prims.int)))
  :named haseqTm_refine_542f9d4f129664613f2483a6c88bc7c2))
; haseq for Tm_refine_774ba3f728d91ead8ef40be66c9802e5
;;; Fact-ids: Name Prims.pos; Namespace Prims
(assert
 (! (iff
   (Valid (Prims.hasEq U_zero Tm_refine_774ba3f728d91ead8ef40be66c9802e5))
   (Valid (Prims.hasEq U_zero Prims.int)))
  :named haseqTm_refine_774ba3f728d91ead8ef40be66c9802e5))
; haseq for Tm_refine_7df43cb9feb536df62477b7b30ce1682
;;; Fact-ids: Name FStar.SizeT.v; Namespace FStar.SizeT
(assert
 (! (iff
   (Valid (Prims.hasEq U_zero Tm_refine_7df43cb9feb536df62477b7b30ce1682))
   (Valid (Prims.hasEq U_zero Prims.nat)))
  :named haseqTm_refine_7df43cb9feb536df62477b7b30ce1682))
; haseq for Tm_refine_8856e20ff1b6ebce251f1ce59b5ef2e2
;;; Fact-ids: Name FStar.Monotonic.Heap.lemma_mref_injectivity; Namespace FStar.Monotonic.Heap
(assert
 (! (iff
   (Valid (Prims.hasEq U_zero Tm_refine_8856e20ff1b6ebce251f1ce59b5ef2e2))
   (Valid (Prims.hasEq U_zero Prims.unit)))
  :named haseqTm_refine_8856e20ff1b6ebce251f1ce59b5ef2e2))
; haseq for Tm_refine_9d6af3f3535473623f7aec2f0501897f
;;; Fact-ids: Name Prims.eqtype; Namespace Prims
(assert
 (! (iff
   (Valid (Prims.hasEq (U_succ U_zero) Tm_refine_9d6af3f3535473623f7aec2f0501897f))
   (Valid (Prims.hasEq (U_succ U_zero) (Tm_type U_zero))))
  :named haseqTm_refine_9d6af3f3535473623f7aec2f0501897f))
; haseq for Tm_refine_ba4be9e593fda710cd7cd90723afa87e
;;; Fact-ids: Name Prims.prop; Namespace Prims
(assert
 (! (iff
   (Valid (Prims.hasEq (U_succ U_zero) Tm_refine_ba4be9e593fda710cd7cd90723afa87e))
   (Valid (Prims.hasEq (U_succ U_zero) (Tm_type U_zero))))
  :named haseqTm_refine_ba4be9e593fda710cd7cd90723afa87e))
; haseq for Tm_refine_cf63becb12ffbdf5c3ea7d1e75c3d75a
;;; Fact-ids: Name FStar.Preorder.preorder; Namespace FStar.Preorder
(assert
 (! ;; def=FStar.Preorder.fst(33,25-33,57); use=FStar.Preorder.fst(33,25-33,57)
  (forall ((@u0 Universe) (@x1 Term))
   (! (iff
     (Valid
      (Prims.hasEq (U_max (U_succ U_zero) @u0) (Tm_refine_cf63becb12ffbdf5c3ea7d1e75c3d75a @u0 @x1)))
     (Valid (Prims.hasEq (U_max (U_succ U_zero) @u0) (FStar.Preorder.relation @u0 @x1))))
    :pattern
     ((Valid
       (Prims.hasEq (U_max (U_succ U_zero) @u0) (Tm_refine_cf63becb12ffbdf5c3ea7d1e75c3d75a @u0 @x1))))
    :qid haseqTm_refine_cf63becb12ffbdf5c3ea7d1e75c3d75a))
  :named haseqTm_refine_cf63becb12ffbdf5c3ea7d1e75c3d75a))
; haseq for Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81
;;; Fact-ids: Name Prims.pure_post'; Namespace Prims
(assert
 (! ;; def=Prims.fst(323,31-323,40); use=Prims.fst(323,31-323,40)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (iff
     (Valid (Prims.hasEq @u0 (Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81 @u0 @x1 @x2)))
     (Valid (Prims.hasEq @u0 @x2)))
    :pattern ((Valid (Prims.hasEq @u0 (Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81 @u0 @x1 @x2))))
    :qid haseqTm_refine_d79dab86b7f5fc89b7215ab23d0f2c81))
  :named haseqTm_refine_d79dab86b7f5fc89b7215ab23d0f2c81))
; int inversion
;;; Fact-ids: Name Prims.int; Namespace Prims
(assert
 (! (forall ((@u0 Fuel) (@x1 Term))
   (! (implies (HasTypeFuel @u0 @x1 Prims.int) (is-BoxInt @x1))
    :pattern ((HasTypeFuel @u0 @x1 Prims.int))
    :qid int_inversion))
  :named int_inversion))
; int typing
;;; Fact-ids: Name Prims.int; Namespace Prims
(assert
 (! (forall ((@u0 Int)) (! (HasType (BoxInt @u0) Prims.int) :pattern ((BoxInt @u0)) :qid int_typing))
  :named int_typing))
;;; Fact-ids: Name Prims.equals; Namespace Prims; Name Prims.Refl; Namespace Prims
(assert
 (! (and
   ;; def=Prims.fst(173,5-173,11); use=Prims.fst(173,5-173,11)
   (forall ((@u0 Universe))
    (! (IsTotFun (Prims.equals@tok @u0))
     :pattern ((Prims.equals@tok @u0))
     :qid kinding_Prims.equals@tok))
   ;; def=Prims.fst(173,5-173,11); use=Prims.fst(173,5-173,11)
   (forall ((@u0 Universe) (@x1 Term))
    (! (IsTotFun (ApplyTT (Prims.equals@tok @u0) @x1))
     :pattern ((ApplyTT (Prims.equals@tok @u0) @x1))
     :qid kinding_Prims.equals@tok.1))
   ;; def=Prims.fst(173,5-173,11); use=Prims.fst(173,5-173,11)
   (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
    (! (IsTotFun (ApplyTT (ApplyTT (Prims.equals@tok @u0) @x1) @x2))
     :pattern ((ApplyTT (ApplyTT (Prims.equals@tok @u0) @x1) @x2))
     :qid kinding_Prims.equals@tok.2))
   ;; def=Prims.fst(173,5-173,11); use=Prims.fst(173,5-173,11)
   (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
    (! (implies
      (and (HasType @x1 (Tm_type @u0)) (HasType @x2 @x1) (HasType @x3 @x1))
      (HasType (Prims.equals @u0 @x1 @x2 @x3) (Tm_type U_zero)))
     :pattern ((Prims.equals @u0 @x1 @x2 @x3))
     :qid kinding_Prims.equals@tok.3)))
  :named kinding_Prims.equals@tok))
;;; Fact-ids: Name Prims.pair; Namespace Prims; Name Prims.Pair; Namespace Prims
(assert
 (! (and
   ;; def=Prims.fst(191,5-191,9); use=Prims.fst(191,5-191,9)
   (forall ((@u0 Universe) (@u1 Universe))
    (! (IsTotFun (Prims.pair@tok @u0 @u1))
     :pattern ((Prims.pair@tok @u0 @u1))
     :qid kinding_Prims.pair@tok))
   ;; def=Prims.fst(191,5-191,9); use=Prims.fst(191,5-191,9)
   (forall ((@u0 Universe) (@u1 Universe) (@x2 Term))
    (! (IsTotFun (ApplyTT (Prims.pair@tok @u0 @u1) @x2))
     :pattern ((ApplyTT (Prims.pair@tok @u0 @u1) @x2))
     :qid kinding_Prims.pair@tok.1))
   ;; def=Prims.fst(191,5-191,9); use=Prims.fst(191,5-191,9)
   (forall ((@u0 Universe) (@u1 Universe) (@x2 Term) (@x3 Term))
    (! (implies
      (and (HasType @x2 (Tm_type @u0)) (HasType @x3 (Tm_type @u1)))
      (HasType (Prims.pair @u0 @u1 @x2 @x3) (Tm_type (U_max @u0 @u1))))
     :pattern ((Prims.pair @u0 @u1 @x2 @x3))
     :qid kinding_Prims.pair@tok.2)))
  :named kinding_Prims.pair@tok))
;;; Fact-ids: Name Prims.trivial; Namespace Prims; Name Prims.T; Namespace Prims
(assert
 (! (HasType Prims.trivial (Tm_type U_zero)) :named kinding_Prims.trivial@tok))
; kinding_Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae
;;; Fact-ids: Name Prims.pure_post'; Namespace Prims
(assert
 (! ;; def=Prims.fst(323,31-323,54); use=Prims.fst(323,31-323,54)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (HasType
     (Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae @u0 @x1 @x2)
     (Tm_type (U_max (U_succ U_zero) @u0)))
    :pattern
     ((HasType
       (Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae @u0 @x1 @x2)
       (Tm_type (U_max (U_succ U_zero) @u0))))
    :qid kinding_Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae))
  :named kinding_Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae))
; kinding_Tm_arrow_16f201d72071a2daf4be1ef0b08cdeb0
;;; Fact-ids: Name FStar.Preorder.relation; Namespace FStar.Preorder
(assert
 (! ;; def=FStar.Preorder.fst(20,15-20,40); use=FStar.Preorder.fst(20,25-20,40)
  (forall ((@x0 Term) (@u1 Universe))
   (! (HasType
     (Tm_arrow_16f201d72071a2daf4be1ef0b08cdeb0 @x0 @u1)
     (Tm_type (U_max (U_succ U_zero) @u1)))
    :pattern
     ((HasType
       (Tm_arrow_16f201d72071a2daf4be1ef0b08cdeb0 @x0 @u1)
       (Tm_type (U_max (U_succ U_zero) @u1))))
    :qid kinding_Tm_arrow_16f201d72071a2daf4be1ef0b08cdeb0))
  :named kinding_Tm_arrow_16f201d72071a2daf4be1ef0b08cdeb0))
; /\ interpretation
;;; Fact-ids: Name Prims.l_and; Namespace Prims
(assert
 (! (forall ((@x0 Term) (@x1 Term))
   (! (iff (and (Valid @x0) (Valid @x1)) (Valid (Prims.l_and @x0 @x1)))
    :pattern ((Prims.l_and @x0 @x1))
    :qid l_and-interp))
  :named l_and-interp))
; Lemma: FStar.Seq.Base.hasEq_lemma
;;; Fact-ids: Name FStar.Seq.Base.hasEq_lemma; Namespace FStar.Seq.Base
(assert
 (! (forall ((@u0 Universe) (@x1 Term))
   (! (implies
     (and
      (HasType @x1 (Tm_type @u0))
      ;; def=FStar.Seq.Base.fsti(163,43-163,52); use=FStar.Seq.Base.fsti(163,43-163,52)
      (Valid
       ;; def=FStar.Seq.Base.fsti(163,43-163,52); use=FStar.Seq.Base.fsti(163,43-163,52)
       (Prims.hasEq @u0 @x1)))
     ;; def=FStar.Seq.Base.fsti(163,63-163,78); use=FStar.Seq.Base.fsti(163,63-163,78)
     (Valid
      ;; def=FStar.Seq.Base.fsti(163,63-163,78); use=FStar.Seq.Base.fsti(163,63-163,78)
      (Prims.hasEq @u0 (FStar.Seq.Base.seq @u0 @x1))))
    :pattern ((Prims.hasEq @u0 (FStar.Seq.Base.seq @u0 @x1)))
    :qid lemma_FStar.Seq.Base.hasEq_lemma))
  :named lemma_FStar.Seq.Base.hasEq_lemma))
; Lemma: FStar.SizeT.fits_at_least_16
;;; Fact-ids: Name FStar.SizeT.fits_at_least_16; Namespace FStar.SizeT
(assert
 (! (forall ((@x0 Term))
   (! (implies
     (and
      (HasType @x0 Prims.nat)
      ;; def=FStar.SizeT.fsti(24,14-24,20); use=FStar.SizeT.fsti(24,14-24,20)
      (<= (BoxInt_proj_0 (BoxInt 0)) (BoxInt_proj_0 @x0))
      ;; def=FStar.SizeT.fsti(24,24-24,35); use=FStar.SizeT.fsti(24,24-24,35)
      (< (BoxInt_proj_0 @x0) (BoxInt_proj_0 (Prims.pow2.fuel_instrumented ZFuel (BoxInt 16)))))
     ;; def=FStar.SizeT.fsti(25,13-25,19); use=FStar.SizeT.fsti(25,13-25,19)
     (Valid
      ;; def=FStar.SizeT.fsti(25,13-25,19); use=FStar.SizeT.fsti(25,13-25,19)
      (FStar.SizeT.fits @x0)))
    :pattern ((FStar.SizeT.fits @x0))
    :qid lemma_FStar.SizeT.fits_at_least_16))
  :named lemma_FStar.SizeT.fits_at_least_16))
; Lemma: FStar.SizeT.fits_lte
;;; Fact-ids: Name FStar.SizeT.fits_lte; Namespace FStar.SizeT
(assert
 (! (forall ((@x0 Term) (@x1 Term))
   (! (implies
     (and
      (HasType @x0 Prims.nat)
      (HasType @x1 Prims.nat)
      ;; def=FStar.SizeT.fsti(110,13-110,19); use=FStar.SizeT.fsti(110,13-110,19)
      (<= (BoxInt_proj_0 @x0) (BoxInt_proj_0 @x1))
      ;; def=FStar.SizeT.fsti(110,23-110,29); use=FStar.SizeT.fsti(110,23-110,29)
      (Valid
       ;; def=FStar.SizeT.fsti(110,23-110,29); use=FStar.SizeT.fsti(110,23-110,29)
       (FStar.SizeT.fits @x1)))
     ;; def=FStar.SizeT.fsti(111,11-111,19); use=FStar.SizeT.fsti(111,11-111,19)
     (Valid
      ;; def=FStar.SizeT.fsti(111,11-111,19); use=FStar.SizeT.fsti(111,11-111,19)
      (FStar.SizeT.fits @x0)))
    :pattern ((FStar.SizeT.fits @x0) (FStar.SizeT.fits @x1))
    :qid lemma_FStar.SizeT.fits_lte))
  :named lemma_FStar.SizeT.fits_lte))
; Lemma: FStar.SizeT.fits_nonneg
;;; Fact-ids: Name FStar.SizeT.fits_nonneg; Namespace FStar.SizeT
(assert
 (! (forall ((@x0 Term))
   (! (implies
     (and
      (HasType @x0 Prims.int)
      ;; def=FStar.SizeT.fsti(15,20-15,26); use=FStar.SizeT.fsti(15,20-15,26)
      (Valid
       ;; def=FStar.SizeT.fsti(15,20-15,26); use=FStar.SizeT.fsti(15,20-15,26)
       (FStar.SizeT.fits @x0)))
     ;; def=FStar.SizeT.fsti(16,19-16,25); use=FStar.SizeT.fsti(16,19-16,25)
     (>= (BoxInt_proj_0 @x0) (BoxInt_proj_0 (BoxInt 0))))
    :pattern ((FStar.SizeT.fits @x0))
    :qid lemma_FStar.SizeT.fits_nonneg))
  :named lemma_FStar.SizeT.fits_nonneg))
; Lemma: FStar.SizeT.size_uint_to_t_inj
;;; Fact-ids: Name FStar.SizeT.size_uint_to_t_inj; Namespace FStar.SizeT
(assert
 (! (forall ((@x0 Term))
   (! (implies
     (and
      (HasType @x0 Prims.int)
      ;; def=FStar.SizeT.fsti(51,14-51,20); use=FStar.SizeT.fsti(51,14-51,20)
      (Valid
       ;; def=FStar.SizeT.fsti(51,14-51,20); use=FStar.SizeT.fsti(51,14-51,20)
       (FStar.SizeT.fits @x0)))
     ;; def=FStar.SizeT.fsti(52,13-52,33); use=FStar.SizeT.fsti(52,13-52,33)
     (= (FStar.SizeT.v (FStar.SizeT.uint_to_t @x0)) @x0))
    :pattern ((FStar.SizeT.uint_to_t @x0))
    :qid lemma_FStar.SizeT.size_uint_to_t_inj))
  :named lemma_FStar.SizeT.size_uint_to_t_inj))
; Lemma: FStar.SizeT.size_v_inj
;;; Fact-ids: Name FStar.SizeT.size_v_inj; Namespace FStar.SizeT
(assert
 (! (forall ((@x0 Term))
   (! (implies
     (HasType @x0 (FStar.SizeT.t Dummy_value))
     ;; def=FStar.SizeT.fsti(46,13-46,33); use=FStar.SizeT.fsti(46,13-46,33)
     (= (FStar.SizeT.uint_to_t (FStar.SizeT.v @x0)) @x0))
    :pattern ((FStar.SizeT.v @x0))
    :qid lemma_FStar.SizeT.size_v_inj))
  :named lemma_FStar.SizeT.size_v_inj))
; Lemma: FStar.UInt.pow2_values
;;; Fact-ids: Name FStar.UInt.pow2_values; Namespace FStar.UInt
(assert
 (! (forall ((@x0 Term))
   (! (implies
     (HasType @x0 Prims.nat)
     (let ((@lb1 @x0))
      (ite
       (= @lb1 (BoxInt 0))
       ;; def=FStar.UInt.fsti(28,11-28,14); use=FStar.UInt.fsti(28,11-28,14)
       (= (Prims.pow2.fuel_instrumented ZFuel @x0) (BoxInt 1))
       (ite
        (= @lb1 (BoxInt 1))
        ;; def=FStar.UInt.fsti(29,11-29,14); use=FStar.UInt.fsti(29,11-29,14)
        (= (Prims.pow2.fuel_instrumented ZFuel @x0) (BoxInt 2))
        (ite
         (= @lb1 (BoxInt 8))
         ;; def=FStar.UInt.fsti(30,11-30,16); use=FStar.UInt.fsti(30,11-30,16)
         (= (Prims.pow2.fuel_instrumented ZFuel @x0) (BoxInt 256))
         (ite
          (= @lb1 (BoxInt 16))
          ;; def=FStar.UInt.fsti(31,11-31,18); use=FStar.UInt.fsti(31,11-31,18)
          (= (Prims.pow2.fuel_instrumented ZFuel @x0) (BoxInt 65536))
          (ite
           (= @lb1 (BoxInt 31))
           ;; def=FStar.UInt.fsti(32,11-32,23); use=FStar.UInt.fsti(32,11-32,23)
           (= (Prims.pow2.fuel_instrumented ZFuel @x0) (BoxInt 2147483648))
           (ite
            (= @lb1 (BoxInt 32))
            ;; def=FStar.UInt.fsti(33,11-33,23); use=FStar.UInt.fsti(33,11-33,23)
            (= (Prims.pow2.fuel_instrumented ZFuel @x0) (BoxInt 4294967296))
            (ite
             (= @lb1 (BoxInt 63))
             ;; def=FStar.UInt.fsti(34,11-34,32); use=FStar.UInt.fsti(34,11-34,32)
             (= (Prims.pow2.fuel_instrumented ZFuel @x0) (BoxInt 9223372036854775808))
             (ite
              (= @lb1 (BoxInt 64))
              ;; def=FStar.UInt.fsti(35,11-35,33); use=FStar.UInt.fsti(35,11-35,33)
              (= (Prims.pow2.fuel_instrumented ZFuel @x0) (BoxInt 18446744073709551616))
              (implies
               (= @lb1 (BoxInt 128))
               ;; def=FStar.UInt.fsti(36,12-36,49); use=FStar.UInt.fsti(36,12-36,49)
               (=
                (Prims.pow2.fuel_instrumented ZFuel @x0)
                (BoxInt 340282366920938463463374607431768211456)))))))))))))
    :pattern ((Prims.pow2.fuel_instrumented ZFuel @x0))
    :qid lemma_FStar.UInt.pow2_values))
  :named lemma_FStar.UInt.pow2_values))
; Typing for non-total arrows
;;; Fact-ids: Name FStar.Tactics.Effect.tac; Namespace FStar.Tactics.Effect
(assert
 (! ;; def=FStar.Tactics.Effect.fsti(178,16-178,19); use=FStar.Tactics.Effect.fsti(178,22-178,32)
  (forall ((@u0 Universe) (@u1 Universe))
   (! ;; def=FStar.Tactics.Effect.fsti(178,16-178,19); use=FStar.Tactics.Effect.fsti(178,22-178,32)
    (forall ((@x2 Term) (@x3 Term))
     (! (implies
       (and (HasType @x2 (Tm_type @u0)) (HasType @x3 (Tm_type @u1)))
       (HasType (Non_total_Tm_arrow_2672e45a784a2b0927230a9770301b34 @x2 @x3) (Tm_type U_unknown)))
      :pattern
       ((HasType (Non_total_Tm_arrow_2672e45a784a2b0927230a9770301b34 @x2 @x3) (Tm_type U_unknown)))
      :qid non_total_function_typing_Non_total_Tm_arrow_2672e45a784a2b0927230a9770301b34.1))
    :qid non_total_function_typing_Non_total_Tm_arrow_2672e45a784a2b0927230a9770301b34))
  :named non_total_function_typing_Non_total_Tm_arrow_2672e45a784a2b0927230a9770301b34))
; Typing for non-total arrows
;;; Fact-ids: Name FStar.Tactics.Effect.tac_repr; Namespace FStar.Tactics.Effect
(assert
 (! ;; def=FStar.Tactics.Effect.fsti(36,14-37,16); use=FStar.Tactics.Effect.fsti(37,2-37,24)
  (forall ((@u0 Universe))
   (! ;; def=FStar.Tactics.Effect.fsti(36,14-37,16); use=FStar.Tactics.Effect.fsti(37,2-37,24)
    (forall ((@x1 Term))
     (! (implies
       (HasType @x1 (Tm_type @u0))
       (HasType (Non_total_Tm_arrow_6dfaaa0e96f606a8d2b60f84543d775d @x1) (Tm_type U_unknown)))
      :pattern
       ((HasType (Non_total_Tm_arrow_6dfaaa0e96f606a8d2b60f84543d775d @x1) (Tm_type U_unknown)))
      :qid non_total_function_typing_Non_total_Tm_arrow_6dfaaa0e96f606a8d2b60f84543d775d.1))
    :qid non_total_function_typing_Non_total_Tm_arrow_6dfaaa0e96f606a8d2b60f84543d775d))
  :named non_total_function_typing_Non_total_Tm_arrow_6dfaaa0e96f606a8d2b60f84543d775d))
; Typing for non-total arrows
;;; Fact-ids: Name FStar.Tactics.MApply.termable; Namespace FStar.Tactics.MApply; Name FStar.Tactics.MApply.Mktermable; Namespace FStar.Tactics.MApply
(assert
 (! ;; def=FStar.Tactics.MApply.fsti(10,16-11,25); use=FStar.Tactics.MApply.fsti(11,12-11,25)
  (forall ((@u0 Universe))
   (! ;; def=FStar.Tactics.MApply.fsti(10,16-11,25); use=FStar.Tactics.MApply.fsti(11,12-11,25)
    (forall ((@x1 Term))
     (! (implies
       (HasType @x1 (Tm_type @u0))
       (HasType (Non_total_Tm_arrow_cd4cc5f03a4b4d3d9feee06a5831f1c2 @x1) (Tm_type U_unknown)))
      :pattern
       ((HasType (Non_total_Tm_arrow_cd4cc5f03a4b4d3d9feee06a5831f1c2 @x1) (Tm_type U_unknown)))
      :qid non_total_function_typing_Non_total_Tm_arrow_cd4cc5f03a4b4d3d9feee06a5831f1c2.1))
    :qid non_total_function_typing_Non_total_Tm_arrow_cd4cc5f03a4b4d3d9feee06a5831f1c2))
  :named non_total_function_typing_Non_total_Tm_arrow_cd4cc5f03a4b4d3d9feee06a5831f1c2))
; Typing for non-total arrows
;;; Fact-ids: Name FStar.Tactics.Effect.lift_div_tac; Namespace FStar.Tactics.Effect
(assert
 (! ;; def=FStar.Tactics.Effect.fsti(138,18-138,48); use=FStar.Tactics.Effect.fsti(138,44-138,57)
  (forall ((@u0 Universe))
   (! ;; def=FStar.Tactics.Effect.fsti(138,18-138,48); use=FStar.Tactics.Effect.fsti(138,44-138,57)
    (forall ((@x1 Term) (@x2 Term))
     (! (implies
       (and (HasType @x1 (Tm_type @u0)) (HasType @x2 (Prims.pure_wp @u0 @x1)))
       (HasType (Non_total_Tm_arrow_da9712c41bd4800828fa87c1bc605521 @x1 @x2) (Tm_type U_unknown)))
      :pattern
       ((HasType (Non_total_Tm_arrow_da9712c41bd4800828fa87c1bc605521 @x1 @x2) (Tm_type U_unknown)))
      :qid non_total_function_typing_Non_total_Tm_arrow_da9712c41bd4800828fa87c1bc605521.1))
    :qid non_total_function_typing_Non_total_Tm_arrow_da9712c41bd4800828fa87c1bc605521))
  :named non_total_function_typing_Non_total_Tm_arrow_da9712c41bd4800828fa87c1bc605521))
; Typing for non-total arrows
;;; Fact-ids: Name FStar.Tactics.V2.Derived.op_Less_Bar_Greater; Namespace FStar.Tactics.V2.Derived
(assert
 (! ;; def=FStar.Tactics.V2.Derived.fst(474,13-476,27); use=FStar.Tactics.V2.Derived.fst(474,25-477,8)
  (forall ((@u0 Universe))
   (! ;; def=FStar.Tactics.V2.Derived.fst(474,13-476,27); use=FStar.Tactics.V2.Derived.fst(474,25-477,8)
    (forall ((@x1 Term))
     (! (implies
       (HasType @x1 (Tm_type @u0))
       (HasType (Non_total_Tm_arrow_e21d0d53adb3309db65169e4e063bae4 @x1) (Tm_type U_unknown)))
      :pattern
       ((HasType (Non_total_Tm_arrow_e21d0d53adb3309db65169e4e063bae4 @x1) (Tm_type U_unknown)))
      :qid non_total_function_typing_Non_total_Tm_arrow_e21d0d53adb3309db65169e4e063bae4.1))
    :qid non_total_function_typing_Non_total_Tm_arrow_e21d0d53adb3309db65169e4e063bae4))
  :named non_total_function_typing_Non_total_Tm_arrow_e21d0d53adb3309db65169e4e063bae4))
; Typing for non-total arrows
;;; Fact-ids: Name FStar.Tactics.V2.Derived.discard; Namespace FStar.Tactics.V2.Derived
(assert
 (! ;; def=FStar.Tactics.V2.Derived.fst(513,19-513,33); use=FStar.Tactics.V2.Derived.fst(513,19-513,33)
  (forall ((@u0 Universe))
   (! ;; def=FStar.Tactics.V2.Derived.fst(513,19-513,33); use=FStar.Tactics.V2.Derived.fst(513,19-513,33)
    (forall ((@x1 Term))
     (! (implies
       (HasType @x1 (Tm_type @u0))
       (HasType (Non_total_Tm_arrow_eef5fa7bf2f900b7fa6a4f1653008996 @x1) (Tm_type U_unknown)))
      :pattern
       ((HasType (Non_total_Tm_arrow_eef5fa7bf2f900b7fa6a4f1653008996 @x1) (Tm_type U_unknown)))
      :qid non_total_function_typing_Non_total_Tm_arrow_eef5fa7bf2f900b7fa6a4f1653008996.1))
    :qid non_total_function_typing_Non_total_Tm_arrow_eef5fa7bf2f900b7fa6a4f1653008996))
  :named non_total_function_typing_Non_total_Tm_arrow_eef5fa7bf2f900b7fa6a4f1653008996))
; Typing for non-total arrows
;;; Fact-ids: Name Pulse.Lib.Core.hide_div; Namespace Pulse.Lib.Core
(assert
 (! ;; def=Pulse.Lib.Core.fsti(262,30-262,57); use=Pulse.Lib.Core.fsti(262,30-262,57)
  (forall ((@u0 Universe))
   (! ;; def=Pulse.Lib.Core.fsti(262,30-262,57); use=Pulse.Lib.Core.fsti(262,30-262,57)
    (forall ((@x1 Term) (@x2 Term) (@x3 Term))
     (! (implies
       (and
        (HasType @x1 (Tm_type @u0))
        (HasType @x2 Pulse.Lib.Core.slprop)
        (HasType @x3 (Tm_arrow_8f4d0c93d793badb913a85a0bb821c13 @x1 @u0)))
       (HasType
        (Non_total_Tm_arrow_fd4a797c28acac3a2455c1745185ab2f @x1 @x2 @x3)
        (Tm_type U_unknown)))
      :pattern
       ((HasType
         (Non_total_Tm_arrow_fd4a797c28acac3a2455c1745185ab2f @x1 @x2 @x3)
         (Tm_type U_unknown)))
      :qid non_total_function_typing_Non_total_Tm_arrow_fd4a797c28acac3a2455c1745185ab2f.1))
    :qid non_total_function_typing_Non_total_Tm_arrow_fd4a797c28acac3a2455c1745185ab2f))
  :named non_total_function_typing_Non_total_Tm_arrow_fd4a797c28acac3a2455c1745185ab2f))
; kinding
;;; Fact-ids: Name Prims.equals; Namespace Prims; Name Prims.Refl; Namespace Prims
(assert
 (! ;; def=Prims.fst(173,5-173,11); use=Prims.fst(173,5-173,11)
  (forall ((@u0 Universe))
   (! (is-Tm_arrow (PreType (Prims.equals@tok @u0)))
    :pattern ((Prims.equals@tok @u0))
    :qid pre_kinding_Prims.equals@tok))
  :named pre_kinding_Prims.equals@tok))
; kinding
;;; Fact-ids: Name Prims.pair; Namespace Prims; Name Prims.Pair; Namespace Prims
(assert
 (! ;; def=Prims.fst(191,5-191,9); use=Prims.fst(191,5-191,9)
  (forall ((@u0 Universe) (@u1 Universe))
   (! (is-Tm_arrow (PreType (Prims.pair@tok @u0 @u1)))
    :pattern ((Prims.pair@tok @u0 @u1))
    :qid pre_kinding_Prims.pair@tok))
  :named pre_kinding_Prims.pair@tok))
;;; Fact-ids: Name Prims.op_Addition; Namespace Prims
(assert
 (! ;; def=Prims.fst(560,4-560,15); use=Prims.fst(560,4-560,15)
  (forall ((@x0 Term) (@x1 Term))
   (! (= (Prims.op_Addition @x0 @x1) (BoxInt (+ (BoxInt_proj_0 @x0) (BoxInt_proj_0 @x1))))
    :pattern ((Prims.op_Addition @x0 @x1))
    :qid primitive_Prims.op_Addition))
  :named primitive_Prims.op_Addition))
;;; Fact-ids: Name Prims.op_BarBar; Namespace Prims
(assert
 (! ;; def=Prims.fst(536,4-536,13); use=Prims.fst(536,4-536,13)
  (forall ((@x0 Term) (@x1 Term))
   (! (= (Prims.op_BarBar @x0 @x1) (BoxBool (or (BoxBool_proj_0 @x0) (BoxBool_proj_0 @x1))))
    :pattern ((Prims.op_BarBar @x0 @x1))
    :qid primitive_Prims.op_BarBar))
  :named primitive_Prims.op_BarBar))
;;; Fact-ids: Name Prims.op_Equality; Namespace Prims
(assert
 (! ;; def=Prims.fst(596,4-596,15); use=Prims.fst(596,4-596,15)
  (forall ((@x0 Term) (@x1 Term) (@x2 Term))
   (! (= (Prims.op_Equality @x0 @x1 @x2) (BoxBool (= @x1 @x2)))
    :pattern ((Prims.op_Equality @x0 @x1 @x2))
    :qid primitive_Prims.op_Equality))
  :named primitive_Prims.op_Equality))
;;; Fact-ids: Name Prims.op_GreaterThan; Namespace Prims
(assert
 (! ;; def=Prims.fst(578,4-578,18); use=Prims.fst(578,4-578,18)
  (forall ((@x0 Term) (@x1 Term))
   (! (= (Prims.op_GreaterThan @x0 @x1) (BoxBool (> (BoxInt_proj_0 @x0) (BoxInt_proj_0 @x1))))
    :pattern ((Prims.op_GreaterThan @x0 @x1))
    :qid primitive_Prims.op_GreaterThan))
  :named primitive_Prims.op_GreaterThan))
;;; Fact-ids: Name Prims.op_GreaterThanOrEqual; Namespace Prims
(assert
 (! ;; def=Prims.fst(584,4-584,25); use=Prims.fst(584,4-584,25)
  (forall ((@x0 Term) (@x1 Term))
   (! (=
     (Prims.op_GreaterThanOrEqual @x0 @x1)
     (BoxBool (>= (BoxInt_proj_0 @x0) (BoxInt_proj_0 @x1))))
    :pattern ((Prims.op_GreaterThanOrEqual @x0 @x1))
    :qid primitive_Prims.op_GreaterThanOrEqual))
  :named primitive_Prims.op_GreaterThanOrEqual))
;;; Fact-ids: Name Prims.op_LessThan; Namespace Prims
(assert
 (! ;; def=Prims.fst(590,4-590,15); use=Prims.fst(590,4-590,15)
  (forall ((@x0 Term) (@x1 Term))
   (! (= (Prims.op_LessThan @x0 @x1) (BoxBool (< (BoxInt_proj_0 @x0) (BoxInt_proj_0 @x1))))
    :pattern ((Prims.op_LessThan @x0 @x1))
    :qid primitive_Prims.op_LessThan))
  :named primitive_Prims.op_LessThan))
;;; Fact-ids: Name Prims.op_Multiply; Namespace Prims
(assert
 (! ;; def=Prims.fst(548,4-548,15); use=Prims.fst(548,4-548,15)
  (forall ((@x0 Term) (@x1 Term))
   (! (= (Prims.op_Multiply @x0 @x1) (BoxInt (* (BoxInt_proj_0 @x0) (BoxInt_proj_0 @x1))))
    :pattern ((Prims.op_Multiply @x0 @x1))
    :qid primitive_Prims.op_Multiply))
  :named primitive_Prims.op_Multiply))
;;; Fact-ids: Name Prims.op_Subtraction; Namespace Prims
(assert
 (! ;; def=Prims.fst(554,4-554,18); use=Prims.fst(554,4-554,18)
  (forall ((@x0 Term) (@x1 Term))
   (! (= (Prims.op_Subtraction @x0 @x1) (BoxInt (- (BoxInt_proj_0 @x0) (BoxInt_proj_0 @x1))))
    :pattern ((Prims.op_Subtraction @x0 @x1))
    :qid primitive_Prims.op_Subtraction))
  :named primitive_Prims.op_Subtraction))
;;; Fact-ids: Name Prims.op_disEquality; Namespace Prims
(assert
 (! ;; def=Prims.fst(602,4-602,18); use=Prims.fst(602,4-602,18)
  (forall ((@x0 Term) (@x1 Term) (@x2 Term))
   (! (= (Prims.op_disEquality @x0 @x1 @x2) (BoxBool (not (= @x1 @x2))))
    :pattern ((Prims.op_disEquality @x0 @x1 @x2))
    :qid primitive_Prims.op_disEquality))
  :named primitive_Prims.op_disEquality))
; Projection inverse
;;; Fact-ids: Name Prims.pair; Namespace Prims; Name Prims.Pair; Namespace Prims
(assert
 (! ;; def=Prims.fst(191,34-191,38); use=Prims.fst(191,34-191,38)
  (forall ((@u0 Universe) (@u1 Universe) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term))
   (! (= (Prims.Pair_@0 (Prims.Pair @u0 @u1 @x2 @x3 @x4 @x5)) @u0)
    :pattern ((Prims.Pair @u0 @u1 @x2 @x3 @x4 @x5))
    :qid projection_inverse_Prims.Pair_@0))
  :named projection_inverse_Prims.Pair_@0))
; Projection inverse
;;; Fact-ids: Name Prims.pair; Namespace Prims; Name Prims.Pair; Namespace Prims
(assert
 (! ;; def=Prims.fst(191,34-191,38); use=Prims.fst(191,34-191,38)
  (forall ((@u0 Universe) (@u1 Universe) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term))
   (! (= (Prims.Pair_@1 (Prims.Pair @u0 @u1 @x2 @x3 @x4 @x5)) @u1)
    :pattern ((Prims.Pair @u0 @u1 @x2 @x3 @x4 @x5))
    :qid projection_inverse_Prims.Pair_@1))
  :named projection_inverse_Prims.Pair_@1))
; Projection inverse
;;; Fact-ids: Name Prims.pair; Namespace Prims; Name Prims.Pair; Namespace Prims
(assert
 (! ;; def=Prims.fst(191,34-191,38); use=Prims.fst(191,34-191,38)
  (forall ((@u0 Universe) (@u1 Universe) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term))
   (! (= (Prims.Pair_@_1 (Prims.Pair @u0 @u1 @x2 @x3 @x4 @x5)) @x4)
    :pattern ((Prims.Pair @u0 @u1 @x2 @x3 @x4 @x5))
    :qid projection_inverse_Prims.Pair_@_1))
  :named projection_inverse_Prims.Pair_@_1))
; Projection inverse
;;; Fact-ids: Name Prims.pair; Namespace Prims; Name Prims.Pair; Namespace Prims
(assert
 (! ;; def=Prims.fst(191,34-191,38); use=Prims.fst(191,34-191,38)
  (forall ((@u0 Universe) (@u1 Universe) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term))
   (! (= (Prims.Pair_@_2 (Prims.Pair @u0 @u1 @x2 @x3 @x4 @x5)) @x5)
    :pattern ((Prims.Pair @u0 @u1 @x2 @x3 @x4 @x5))
    :qid projection_inverse_Prims.Pair_@_2))
  :named projection_inverse_Prims.Pair_@_2))
; Projection inverse
;;; Fact-ids: Name Prims.pair; Namespace Prims; Name Prims.Pair; Namespace Prims
(assert
 (! ;; def=Prims.fst(191,34-191,38); use=Prims.fst(191,34-191,38)
  (forall ((@u0 Universe) (@u1 Universe) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term))
   (! (= (Prims.Pair_@p (Prims.Pair @u0 @u1 @x2 @x3 @x4 @x5)) @x2)
    :pattern ((Prims.Pair @u0 @u1 @x2 @x3 @x4 @x5))
    :qid projection_inverse_Prims.Pair_@p))
  :named projection_inverse_Prims.Pair_@p))
; Projection inverse
;;; Fact-ids: Name Prims.pair; Namespace Prims; Name Prims.Pair; Namespace Prims
(assert
 (! ;; def=Prims.fst(191,34-191,38); use=Prims.fst(191,34-191,38)
  (forall ((@u0 Universe) (@u1 Universe) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term))
   (! (= (Prims.Pair_@q (Prims.Pair @u0 @u1 @x2 @x3 @x4 @x5)) @x3)
    :pattern ((Prims.Pair @u0 @u1 @x2 @x3 @x4 @x5))
    :qid projection_inverse_Prims.Pair_@q))
  :named projection_inverse_Prims.Pair_@q))
; Projection inverse
;;; Fact-ids: Name Prims.equals; Namespace Prims; Name Prims.Refl; Namespace Prims
(assert
 (! ;; def=Prims.fst(173,46-173,50); use=Prims.fst(173,46-173,50)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (= (Prims.Refl_@0 (Prims.Refl @u0 @x1 @x2)) @u0)
    :pattern ((Prims.Refl @u0 @x1 @x2))
    :qid projection_inverse_Prims.Refl_@0))
  :named projection_inverse_Prims.Refl_@0))
; refinement_interpretation
;;; Fact-ids: Name FStar.Seq.Base.index; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(32,34-32,53); use=FStar.Seq.Base.fsti(32,34-32,53)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@x3 Term) (@x4 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_160fe7faad9a466b3cae8455bac5be60 @u2 @x3 @x4))
     (and
      (HasTypeFuel @u0 @x1 Prims.nat)
      ;; def=FStar.Seq.Base.fsti(32,40-32,52); use=FStar.Seq.Base.fsti(32,40-32,52)
      (< (BoxInt_proj_0 @x1) (BoxInt_proj_0 (FStar.Seq.Base.length @u2 @x3 @x4)))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_160fe7faad9a466b3cae8455bac5be60 @u2 @x3 @x4)))
    :qid refinement_interpretation_Tm_refine_160fe7faad9a466b3cae8455bac5be60))
  :named refinement_interpretation_Tm_refine_160fe7faad9a466b3cae8455bac5be60))
; refinement_interpretation
;;; Fact-ids: Name FStar.SizeT.uint_to_t; Namespace FStar.SizeT
(assert
 (! ;; def=FStar.SizeT.fsti(39,30-39,31); use=FStar.SizeT.fsti(39,30-39,31)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_207024d2522be2ff59992eb07d6dc785 @x2))
     (and
      (HasTypeFuel @u0 @x1 (FStar.SizeT.t Dummy_value))
      ;; def=FStar.SizeT.fsti(41,21-41,29); use=FStar.SizeT.fsti(41,21-41,29)
      (= (FStar.SizeT.v @x1) @x2)))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_207024d2522be2ff59992eb07d6dc785 @x2)))
    :qid refinement_interpretation_Tm_refine_207024d2522be2ff59992eb07d6dc785))
  :named refinement_interpretation_Tm_refine_207024d2522be2ff59992eb07d6dc785))
; refinement_interpretation
;;; Fact-ids: Name Prims.squash; Namespace Prims
(assert
 (! ;; def=Prims.fst(125,32-125,42); use=Prims.fst(125,32-125,42)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_2de20c066034c13bf76e9c0b94f4806c @x2))
     (and
      (HasTypeFuel @u0 @x1 Prims.unit)
      ;; def=Prims.fst(125,13-125,14); use=Prims.fst(125,40-125,41)
      (Valid
       ;; def=Prims.fst(125,13-125,14); use=Prims.fst(125,40-125,41)
       @x2)))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_2de20c066034c13bf76e9c0b94f4806c @x2)))
    :qid refinement_interpretation_Tm_refine_2de20c066034c13bf76e9c0b94f4806c))
  :named refinement_interpretation_Tm_refine_2de20c066034c13bf76e9c0b94f4806c))
; refinement_interpretation
;;; Fact-ids: Name Prims.nat; Namespace Prims
(assert
 (! ;; def=Prims.fst(682,11-682,25); use=Prims.fst(682,11-682,25)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_542f9d4f129664613f2483a6c88bc7c2)
     (and
      (HasTypeFuel @u0 @x1 Prims.int)
      ;; def=Prims.fst(682,18-682,24); use=Prims.fst(682,18-682,24)
      (>= (BoxInt_proj_0 @x1) (BoxInt_proj_0 (BoxInt 0)))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_542f9d4f129664613f2483a6c88bc7c2))
    :qid refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2))
  :named refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2))
; refinement_interpretation
;;; Fact-ids: Name Prims.pos; Namespace Prims
(assert
 (! ;; def=Prims.fst(685,11-685,24); use=Prims.fst(685,11-685,24)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_774ba3f728d91ead8ef40be66c9802e5)
     (and
      (HasTypeFuel @u0 @x1 Prims.int)
      ;; def=Prims.fst(685,18-685,23); use=Prims.fst(685,18-685,23)
      (> (BoxInt_proj_0 @x1) (BoxInt_proj_0 (BoxInt 0)))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_774ba3f728d91ead8ef40be66c9802e5))
    :qid refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5))
  :named refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5))
; refinement_interpretation
;;; Fact-ids: Name FStar.SizeT.v; Namespace FStar.SizeT
(assert
 (! ;; def=FStar.SizeT.fsti(29,20-29,23); use=FStar.SizeT.fsti(29,20-29,23)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_7df43cb9feb536df62477b7b30ce1682)
     (and
      (HasTypeFuel @u0 @x1 Prims.nat)
      ;; def=FStar.SizeT.fsti(31,21-31,27); use=FStar.SizeT.fsti(31,21-31,27)
      (Valid
       ;; def=FStar.SizeT.fsti(31,21-31,27); use=FStar.SizeT.fsti(31,21-31,27)
       (FStar.SizeT.fits @x1))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_7df43cb9feb536df62477b7b30ce1682))
    :qid refinement_interpretation_Tm_refine_7df43cb9feb536df62477b7b30ce1682))
  :named refinement_interpretation_Tm_refine_7df43cb9feb536df62477b7b30ce1682))
; refinement_interpretation
;;; Fact-ids: Name FStar.Monotonic.Heap.lemma_mref_injectivity; Namespace FStar.Monotonic.Heap
(assert
 (! ;; def=FStar.Monotonic.Heap.fsti(207,3-207,136); use=FStar.Monotonic.Heap.fsti(207,3-207,136)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_8856e20ff1b6ebce251f1ce59b5ef2e2)
     (and
      (HasTypeFuel @u0 @x1 Prims.unit)
      ;; def=FStar.Monotonic.Heap.fsti(207,11-207,134); use=FStar.Monotonic.Heap.fsti(207,11-207,134)
      (forall ((@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term) (@x6 Term) (@x7 Term))
       (! (implies
         (and
          (HasType @x2 (Tm_type U_zero))
          (HasType @x3 (Tm_type U_zero))
          (HasType @x4 (FStar.Preorder.preorder U_zero @x2))
          (HasType @x5 (FStar.Preorder.preorder U_zero @x3))
          (HasType @x6 (FStar.Monotonic.Heap.mref @x2 @x4))
          (HasType @x7 (FStar.Monotonic.Heap.mref @x3 @x5))
          ;; def=FStar.Monotonic.Heap.fsti(207,109-207,116); use=FStar.Monotonic.Heap.fsti(207,109-207,116)
          (not
           ;; def=FStar.Monotonic.Heap.fsti(207,109-207,116); use=FStar.Monotonic.Heap.fsti(207,109-207,116)
           (= @x2 @x3)))
         ;; def=FStar.Monotonic.Heap.fsti(207,121-207,134); use=FStar.Monotonic.Heap.fsti(207,121-207,134)
         (not
          ;; def=FStar.Monotonic.Heap.fsti(207,123-207,134); use=FStar.Monotonic.Heap.fsti(207,123-207,134)
          (Valid
           ;; def=FStar.Monotonic.Heap.fsti(207,123-207,134); use=FStar.Monotonic.Heap.fsti(207,123-207,134)
           (Prims.op_Equals_Equals_Equals
            U_zero
            (FStar.Monotonic.Heap.mref @x2 @x4)
            (FStar.Monotonic.Heap.mref @x3 @x5)
            @x6
            @x7))))
        :qid refinement_interpretation_Tm_refine_8856e20ff1b6ebce251f1ce59b5ef2e2.1))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_8856e20ff1b6ebce251f1ce59b5ef2e2))
    :qid refinement_interpretation_Tm_refine_8856e20ff1b6ebce251f1ce59b5ef2e2))
  :named refinement_interpretation_Tm_refine_8856e20ff1b6ebce251f1ce59b5ef2e2))
; refinement_interpretation
;;; Fact-ids: Name Prims.eqtype; Namespace Prims
(assert
 (! ;; def=Prims.fst(81,14-81,31); use=Prims.fst(81,14-81,31)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_9d6af3f3535473623f7aec2f0501897f)
     (and
      (HasTypeFuel @u0 @x1 (Tm_type U_zero))
      ;; def=Prims.fst(81,23-81,30); use=Prims.fst(81,23-81,30)
      (Valid
       ;; def=Prims.fst(81,23-81,30); use=Prims.fst(81,23-81,30)
       (Prims.hasEq U_zero @x1))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_9d6af3f3535473623f7aec2f0501897f))
    :qid refinement_interpretation_Tm_refine_9d6af3f3535473623f7aec2f0501897f))
  :named refinement_interpretation_Tm_refine_9d6af3f3535473623f7aec2f0501897f))
; refinement_interpretation
;;; Fact-ids: Name Prims.prop; Namespace Prims
(assert
 (! ;; def=Prims.fst(312,12-312,41); use=Prims.fst(312,12-312,41)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_ba4be9e593fda710cd7cd90723afa87e)
     (and
      (HasTypeFuel @u0 @x1 (Tm_type U_zero))
      ;; def=Prims.fst(312,21-312,40); use=Prims.fst(312,21-312,40)
      (Valid
       ;; def=Prims.fst(312,21-312,40); use=Prims.fst(312,21-312,40)
       (Prims.subtype_of U_zero U_zero @x1 Prims.unit))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_ba4be9e593fda710cd7cd90723afa87e))
    :qid refinement_interpretation_Tm_refine_ba4be9e593fda710cd7cd90723afa87e))
  :named refinement_interpretation_Tm_refine_ba4be9e593fda710cd7cd90723afa87e))
; refinement_interpretation
;;; Fact-ids: Name FStar.Preorder.preorder; Namespace FStar.Preorder
(assert
 (! ;; def=FStar.Preorder.fst(33,25-33,57); use=FStar.Preorder.fst(33,25-33,57)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@x3 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_cf63becb12ffbdf5c3ea7d1e75c3d75a @u2 @x3))
     (and
      (HasTypeFuel @u0 @x1 (FStar.Preorder.relation @u2 @x3))
      ;; def=FStar.Preorder.fst(33,40-33,56); use=FStar.Preorder.fst(33,40-33,56)
      (Valid
       ;; def=FStar.Preorder.fst(33,40-33,56); use=FStar.Preorder.fst(33,40-33,56)
       (FStar.Preorder.preorder_rel @u2 @x3 @x1))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_cf63becb12ffbdf5c3ea7d1e75c3d75a @u2 @x3)))
    :qid refinement_interpretation_Tm_refine_cf63becb12ffbdf5c3ea7d1e75c3d75a))
  :named refinement_interpretation_Tm_refine_cf63becb12ffbdf5c3ea7d1e75c3d75a))
; refinement_interpretation
;;; Fact-ids: Name Prims.pure_post'; Namespace Prims
(assert
 (! ;; def=Prims.fst(323,31-323,40); use=Prims.fst(323,31-323,40)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@x3 Term) (@x4 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81 @u2 @x3 @x4))
     (and
      (HasTypeFuel @u0 @x1 @x4)
      ;; def=Prims.fst(323,18-323,21); use=Prims.fst(323,36-323,39)
      (Valid
       ;; def=Prims.fst(323,18-323,21); use=Prims.fst(323,36-323,39)
       @x3)))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81 @u2 @x3 @x4)))
    :qid refinement_interpretation_Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81))
  :named refinement_interpretation_Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81))
; refinement kinding
;;; Fact-ids: Name FStar.Seq.Base.index; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(32,34-32,53); use=FStar.Seq.Base.fsti(32,34-32,53)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (HasType (Tm_refine_160fe7faad9a466b3cae8455bac5be60 @u0 @x1 @x2) (Tm_type U_zero))
    :pattern ((HasType (Tm_refine_160fe7faad9a466b3cae8455bac5be60 @u0 @x1 @x2) (Tm_type U_zero)))
    :qid refinement_kinding_Tm_refine_160fe7faad9a466b3cae8455bac5be60))
  :named refinement_kinding_Tm_refine_160fe7faad9a466b3cae8455bac5be60))
; refinement kinding
;;; Fact-ids: Name FStar.SizeT.uint_to_t; Namespace FStar.SizeT
(assert
 (! ;; def=FStar.SizeT.fsti(39,30-39,31); use=FStar.SizeT.fsti(39,30-39,31)
  (forall ((@x0 Term))
   (! (HasType (Tm_refine_207024d2522be2ff59992eb07d6dc785 @x0) (Tm_type U_zero))
    :pattern ((HasType (Tm_refine_207024d2522be2ff59992eb07d6dc785 @x0) (Tm_type U_zero)))
    :qid refinement_kinding_Tm_refine_207024d2522be2ff59992eb07d6dc785))
  :named refinement_kinding_Tm_refine_207024d2522be2ff59992eb07d6dc785))
; refinement kinding
;;; Fact-ids: Name Prims.squash; Namespace Prims
(assert
 (! ;; def=Prims.fst(125,32-125,42); use=Prims.fst(125,32-125,42)
  (forall ((@x0 Term))
   (! (HasType (Tm_refine_2de20c066034c13bf76e9c0b94f4806c @x0) (Tm_type U_zero))
    :pattern ((HasType (Tm_refine_2de20c066034c13bf76e9c0b94f4806c @x0) (Tm_type U_zero)))
    :qid refinement_kinding_Tm_refine_2de20c066034c13bf76e9c0b94f4806c))
  :named refinement_kinding_Tm_refine_2de20c066034c13bf76e9c0b94f4806c))
; refinement kinding
;;; Fact-ids: Name Prims.nat; Namespace Prims
(assert
 (! (HasType Tm_refine_542f9d4f129664613f2483a6c88bc7c2 (Tm_type U_zero))
  :named refinement_kinding_Tm_refine_542f9d4f129664613f2483a6c88bc7c2))
; refinement kinding
;;; Fact-ids: Name Prims.pos; Namespace Prims
(assert
 (! (HasType Tm_refine_774ba3f728d91ead8ef40be66c9802e5 (Tm_type U_zero))
  :named refinement_kinding_Tm_refine_774ba3f728d91ead8ef40be66c9802e5))
; refinement kinding
;;; Fact-ids: Name FStar.SizeT.v; Namespace FStar.SizeT
(assert
 (! (HasType Tm_refine_7df43cb9feb536df62477b7b30ce1682 (Tm_type U_zero))
  :named refinement_kinding_Tm_refine_7df43cb9feb536df62477b7b30ce1682))
; refinement kinding
;;; Fact-ids: Name FStar.Monotonic.Heap.lemma_mref_injectivity; Namespace FStar.Monotonic.Heap
(assert
 (! (HasType Tm_refine_8856e20ff1b6ebce251f1ce59b5ef2e2 (Tm_type U_zero))
  :named refinement_kinding_Tm_refine_8856e20ff1b6ebce251f1ce59b5ef2e2))
; refinement kinding
;;; Fact-ids: Name Prims.eqtype; Namespace Prims
(assert
 (! (HasType Tm_refine_9d6af3f3535473623f7aec2f0501897f (Tm_type (U_succ U_zero)))
  :named refinement_kinding_Tm_refine_9d6af3f3535473623f7aec2f0501897f))
; refinement kinding
;;; Fact-ids: Name Prims.prop; Namespace Prims
(assert
 (! (HasType Tm_refine_ba4be9e593fda710cd7cd90723afa87e (Tm_type (U_succ U_zero)))
  :named refinement_kinding_Tm_refine_ba4be9e593fda710cd7cd90723afa87e))
; refinement kinding
;;; Fact-ids: Name FStar.Preorder.preorder; Namespace FStar.Preorder
(assert
 (! ;; def=FStar.Preorder.fst(33,25-33,57); use=FStar.Preorder.fst(33,25-33,57)
  (forall ((@u0 Universe) (@x1 Term))
   (! (HasType
     (Tm_refine_cf63becb12ffbdf5c3ea7d1e75c3d75a @u0 @x1)
     (Tm_type (U_max (U_succ U_zero) @u0)))
    :pattern
     ((HasType
       (Tm_refine_cf63becb12ffbdf5c3ea7d1e75c3d75a @u0 @x1)
       (Tm_type (U_max (U_succ U_zero) @u0))))
    :qid refinement_kinding_Tm_refine_cf63becb12ffbdf5c3ea7d1e75c3d75a))
  :named refinement_kinding_Tm_refine_cf63becb12ffbdf5c3ea7d1e75c3d75a))
; refinement kinding
;;; Fact-ids: Name Prims.pure_post'; Namespace Prims
(assert
 (! ;; def=Prims.fst(323,31-323,40); use=Prims.fst(323,31-323,40)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (HasType (Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81 @u0 @x1 @x2) (Tm_type @u0))
    :pattern ((HasType (Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81 @u0 @x1 @x2) (Tm_type @u0)))
    :qid refinement_kinding_Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81))
  :named refinement_kinding_Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81))
; subterm ordering
;;; Fact-ids: Name Prims.pair; Namespace Prims; Name Prims.Pair; Namespace Prims
(assert
 (! ;; def=Prims.fst(191,34-191,38); use=Prims.fst(191,34-191,38)
  (forall
    ((@u0 Fuel)
     (@u1 Universe)
     (@u2 Universe)
     (@x3 Term)
     (@x4 Term)
     (@x5 Term)
     (@x6 Term)
     (@x7 Term)
     (@x8 Term))
   (! (implies
     (HasTypeFuel (SFuel @u0) (Prims.Pair @u1 @u2 @x3 @x4 @x5 @x6) (Prims.pair @u1 @u2 @x7 @x8))
     (and
      (Valid
       (Prims.precedes
        U_zero
        U_zero
        Prims.lex_t
        Prims.lex_t
        @x5
        (Prims.Pair @u1 @u2 @x3 @x4 @x5 @x6)))
      (Valid
       (Prims.precedes
        U_zero
        U_zero
        Prims.lex_t
        Prims.lex_t
        @x6
        (Prims.Pair @u1 @u2 @x3 @x4 @x5 @x6)))))
    :pattern
     ((HasTypeFuel (SFuel @u0) (Prims.Pair @u1 @u2 @x3 @x4 @x5 @x6) (Prims.pair @u1 @u2 @x7 @x8)))
    :qid subterm_ordering_Prims.Pair))
  :named subterm_ordering_Prims.Pair))
; Typing correspondence of token to term
;;; Fact-ids: Name CLRS.Ch23.Kruskal.UF.find_pure; Namespace CLRS.Ch23.Kruskal.UF
(assert
 (! ;; def=CLRS.Ch23.Kruskal.UF.fsti(30,8-30,17); use=CLRS.Ch23.Kruskal.UF.fsti(30,8-30,17)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
   (! (implies
     (and
      (HasType @x1 (FStar.Seq.Base.seq U_zero (FStar.SizeT.t Dummy_value)))
      (HasType @x2 Prims.nat)
      (HasType @x3 Prims.nat)
      (HasType @x4 Prims.nat))
     (HasType (CLRS.Ch23.Kruskal.UF.find_pure.fuel_instrumented @u0 @x1 @x2 @x3 @x4) Prims.nat))
    :pattern ((CLRS.Ch23.Kruskal.UF.find_pure.fuel_instrumented @u0 @x1 @x2 @x3 @x4))
    :qid token_correspondence_CLRS.Ch23.Kruskal.UF.find_pure.fuel_instrumented))
  :named token_correspondence_CLRS.Ch23.Kruskal.UF.find_pure.fuel_instrumented))
; name-token correspondence
;;; Fact-ids: Name Prims.equals; Namespace Prims; Name Prims.Refl; Namespace Prims
(assert
 (! ;; def=Prims.fst(173,5-173,11); use=Prims.fst(173,5-173,11)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (=
     (ApplyTT (ApplyTT (ApplyTT (Prims.equals@tok @u0) @x1) @x2) @x3)
     (Prims.equals @u0 @x1 @x2 @x3))
    :pattern ((ApplyTT (ApplyTT (ApplyTT (Prims.equals@tok @u0) @x1) @x2) @x3))
    :pattern ((Prims.equals @u0 @x1 @x2 @x3))
    :qid token_correspondence_Prims.equals@tok))
  :named token_correspondence_Prims.equals@tok))
; name-token correspondence
;;; Fact-ids: Name Prims.pair; Namespace Prims; Name Prims.Pair; Namespace Prims
(assert
 (! ;; def=Prims.fst(191,5-191,9); use=Prims.fst(191,5-191,9)
  (forall ((@u0 Universe) (@u1 Universe) (@x2 Term) (@x3 Term))
   (! (= (ApplyTT (ApplyTT (Prims.pair@tok @u0 @u1) @x2) @x3) (Prims.pair @u0 @u1 @x2 @x3))
    :pattern ((ApplyTT (ApplyTT (Prims.pair@tok @u0 @u1) @x2) @x3))
    :pattern ((Prims.pair @u0 @u1 @x2 @x3))
    :qid token_correspondence_Prims.pair@tok))
  :named token_correspondence_Prims.pair@tok))
; Typing correspondence of token to term
;;; Fact-ids: Name Prims.pow2; Namespace Prims
(assert
 (! ;; def=Prims.fst(710,8-710,12); use=Prims.fst(710,8-710,12)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (implies (HasType @x1 Prims.nat) (HasType (Prims.pow2.fuel_instrumented @u0 @x1) Prims.pos))
    :pattern ((Prims.pow2.fuel_instrumented @u0 @x1))
    :qid token_correspondence_Prims.pow2.fuel_instrumented))
  :named token_correspondence_Prims.pow2.fuel_instrumented))
; True interpretation
;;; Fact-ids: Name Prims.l_True; Namespace Prims
(assert (! (Valid Prims.l_True) :named true_interp))
; free var typing
;;; Fact-ids: Name CLRS.Ch23.Kruskal.Impl.scan_min_inv; Namespace CLRS.Ch23.Kruskal.Impl
(assert
 (! ;; def=CLRS.Ch23.Kruskal.Impl.fst(161,4-161,16); use=CLRS.Ch23.Kruskal.Impl.fst(161,4-161,16)
  (forall ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
   (! (implies
     (and
      (HasType @x0 (FStar.Seq.Base.seq U_zero (FStar.SizeT.t Dummy_value)))
      (HasType @x1 (FStar.Seq.Base.seq U_zero Prims.int))
      (HasType @x2 Prims.nat)
      (HasType @x3 Prims.nat)
      (HasType @x4 Prims.int))
     (HasType (CLRS.Ch23.Kruskal.Impl.scan_min_inv @x0 @x1 @x2 @x3 @x4) Prims.prop))
    :pattern ((CLRS.Ch23.Kruskal.Impl.scan_min_inv @x0 @x1 @x2 @x3 @x4))
    :qid typing_CLRS.Ch23.Kruskal.Impl.scan_min_inv))
  :named typing_CLRS.Ch23.Kruskal.Impl.scan_min_inv))
; free var typing
;;; Fact-ids: Name CLRS.Ch23.Kruskal.UF.find_pure; Namespace CLRS.Ch23.Kruskal.UF
(assert
 (! ;; def=CLRS.Ch23.Kruskal.UF.fsti(30,8-30,17); use=CLRS.Ch23.Kruskal.UF.fsti(30,8-30,17)
  (forall ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (implies
     (and
      (HasType @x0 (FStar.Seq.Base.seq U_zero (FStar.SizeT.t Dummy_value)))
      (HasType @x1 Prims.nat)
      (HasType @x2 Prims.nat)
      (HasType @x3 Prims.nat))
     (HasType (CLRS.Ch23.Kruskal.UF.find_pure @x0 @x1 @x2 @x3) Prims.nat))
    :pattern ((CLRS.Ch23.Kruskal.UF.find_pure @x0 @x1 @x2 @x3))
    :qid typing_CLRS.Ch23.Kruskal.UF.find_pure))
  :named typing_CLRS.Ch23.Kruskal.UF.find_pure))
; free var typing
;;; Fact-ids: Name FStar.Monotonic.Heap.core_mref; Namespace FStar.Monotonic.Heap
(assert
 (! ;; def=FStar.Monotonic.Heap.fsti(39,4-39,13); use=FStar.Monotonic.Heap.fsti(39,4-39,13)
  (forall ((@x0 Term))
   (! (implies
     (HasType @x0 (Tm_type U_zero))
     (HasType (FStar.Monotonic.Heap.core_mref @x0) (Tm_type U_zero)))
    :pattern ((FStar.Monotonic.Heap.core_mref @x0))
    :qid typing_FStar.Monotonic.Heap.core_mref))
  :named typing_FStar.Monotonic.Heap.core_mref))
; free var typing
;;; Fact-ids: Name FStar.Monotonic.Heap.lemma_mref_injectivity; Namespace FStar.Monotonic.Heap
(assert
 (! (HasType FStar.Monotonic.Heap.lemma_mref_injectivity Tm_refine_8856e20ff1b6ebce251f1ce59b5ef2e2)
  :named typing_FStar.Monotonic.Heap.lemma_mref_injectivity))
; free var typing
;;; Fact-ids: Name FStar.Monotonic.Heap.mref; Namespace FStar.Monotonic.Heap
(assert
 (! ;; def=FStar.Monotonic.Heap.fsti(41,4-41,8); use=FStar.Monotonic.Heap.fsti(41,4-41,8)
  (forall ((@x0 Term) (@x1 Term))
   (! (implies
     (and (HasType @x0 (Tm_type U_zero)) (HasType @x1 (FStar.Preorder.preorder U_zero @x0)))
     (HasType (FStar.Monotonic.Heap.mref @x0 @x1) (Tm_type U_zero)))
    :pattern ((FStar.Monotonic.Heap.mref @x0 @x1))
    :qid typing_FStar.Monotonic.Heap.mref))
  :named typing_FStar.Monotonic.Heap.mref))
; free var typing
;;; Fact-ids: Name FStar.Preorder.preorder; Namespace FStar.Preorder
(assert
 (! ;; def=FStar.Preorder.fst(33,5-33,13); use=FStar.Preorder.fst(33,5-33,13)
  (forall ((@u0 Universe) (@x1 Term))
   (! (implies
     (HasType @x1 (Tm_type @u0))
     (HasType (FStar.Preorder.preorder @u0 @x1) (Tm_type (U_max (U_succ U_zero) @u0))))
    :pattern ((FStar.Preorder.preorder @u0 @x1))
    :qid typing_FStar.Preorder.preorder))
  :named typing_FStar.Preorder.preorder))
; free var typing
;;; Fact-ids: Name FStar.Preorder.preorder_rel; Namespace FStar.Preorder
(assert
 (! ;; def=FStar.Preorder.fst(30,4-30,16); use=FStar.Preorder.fst(30,4-30,16)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (implies
     (and (HasType @x1 (Tm_type @u0)) (HasType @x2 (FStar.Preorder.relation @u0 @x1)))
     (HasType (FStar.Preorder.preorder_rel @u0 @x1 @x2) Prims.logical))
    :pattern ((FStar.Preorder.preorder_rel @u0 @x1 @x2))
    :qid typing_FStar.Preorder.preorder_rel))
  :named typing_FStar.Preorder.preorder_rel))
; free var typing
;;; Fact-ids: Name FStar.Preorder.reflexive; Namespace FStar.Preorder
(assert
 (! ;; def=FStar.Preorder.fst(24,4-24,13); use=FStar.Preorder.fst(24,4-24,13)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (implies
     (and (HasType @x1 (Tm_type @u0)) (HasType @x2 (FStar.Preorder.relation @u0 @x1)))
     (HasType (FStar.Preorder.reflexive @u0 @x1 @x2) Prims.logical))
    :pattern ((FStar.Preorder.reflexive @u0 @x1 @x2))
    :qid typing_FStar.Preorder.reflexive))
  :named typing_FStar.Preorder.reflexive))
; free var typing
;;; Fact-ids: Name FStar.Preorder.relation; Namespace FStar.Preorder
(assert
 (! ;; def=FStar.Preorder.fst(20,5-20,13); use=FStar.Preorder.fst(20,5-20,13)
  (forall ((@u0 Universe) (@x1 Term))
   (! (implies
     (HasType @x1 (Tm_type @u0))
     (HasType (FStar.Preorder.relation @u0 @x1) (Tm_type (U_max (U_succ U_zero) @u0))))
    :pattern ((FStar.Preorder.relation @u0 @x1))
    :qid typing_FStar.Preorder.relation))
  :named typing_FStar.Preorder.relation))
; free var typing
;;; Fact-ids: Name FStar.Preorder.transitive; Namespace FStar.Preorder
(assert
 (! ;; def=FStar.Preorder.fst(27,4-27,14); use=FStar.Preorder.fst(27,4-27,14)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (implies
     (and (HasType @x1 (Tm_type @u0)) (HasType @x2 (FStar.Preorder.relation @u0 @x1)))
     (HasType (FStar.Preorder.transitive @u0 @x1 @x2) Prims.logical))
    :pattern ((FStar.Preorder.transitive @u0 @x1 @x2))
    :qid typing_FStar.Preorder.transitive))
  :named typing_FStar.Preorder.transitive))
; free var typing
;;; Fact-ids: Name FStar.Seq.Base.index; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(32,4-32,9); use=FStar.Seq.Base.fsti(32,4-32,9)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (implies
     (and
      (HasType @x1 (Tm_type @u0))
      (HasType @x2 (FStar.Seq.Base.seq @u0 @x1))
      (HasType @x3 (Tm_refine_160fe7faad9a466b3cae8455bac5be60 @u0 @x1 @x2)))
     (HasType (FStar.Seq.Base.index @u0 @x1 @x2 @x3) @x1))
    :pattern ((FStar.Seq.Base.index @u0 @x1 @x2 @x3))
    :qid typing_FStar.Seq.Base.index))
  :named typing_FStar.Seq.Base.index))
; free var typing
;;; Fact-ids: Name FStar.Seq.Base.length; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(26,4-26,10); use=FStar.Seq.Base.fsti(26,4-26,10)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (implies
     (and (HasType @x1 (Tm_type @u0)) (HasType @x2 (FStar.Seq.Base.seq @u0 @x1)))
     (HasType (FStar.Seq.Base.length @u0 @x1 @x2) Prims.nat))
    :pattern ((FStar.Seq.Base.length @u0 @x1 @x2))
    :qid typing_FStar.Seq.Base.length))
  :named typing_FStar.Seq.Base.length))
; free var typing
;;; Fact-ids: Name FStar.Seq.Base.seq; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(23,8-23,11); use=FStar.Seq.Base.fsti(23,8-23,11)
  (forall ((@u0 Universe) (@x1 Term))
   (! (implies (HasType @x1 (Tm_type @u0)) (HasType (FStar.Seq.Base.seq @u0 @x1) (Tm_type @u0)))
    :pattern ((FStar.Seq.Base.seq @u0 @x1))
    :qid typing_FStar.Seq.Base.seq))
  :named typing_FStar.Seq.Base.seq))
; free var typing
;;; Fact-ids: Name FStar.SizeT.fits; Namespace FStar.SizeT
(assert
 (! ;; def=FStar.SizeT.fsti(12,4-12,8); use=FStar.SizeT.fsti(12,4-12,8)
  (forall ((@x0 Term))
   (! (implies (HasType @x0 Prims.int) (HasType (FStar.SizeT.fits @x0) Prims.prop))
    :pattern ((FStar.SizeT.fits @x0))
    :qid typing_FStar.SizeT.fits))
  :named typing_FStar.SizeT.fits))
; free var typing
;;; Fact-ids: Name FStar.SizeT.t; Namespace FStar.SizeT
(assert
 (! ;; def=FStar.SizeT.fsti(10,4-10,5); use=FStar.SizeT.fsti(10,4-10,5)
  (forall ((@u0 Dummy_sort))
   (! (HasType (FStar.SizeT.t @u0) Prims.eqtype)
    :pattern ((FStar.SizeT.t @u0))
    :qid typing_FStar.SizeT.t))
  :named typing_FStar.SizeT.t))
; free var typing
;;; Fact-ids: Name FStar.SizeT.uint_to_t; Namespace FStar.SizeT
(assert
 (! ;; def=FStar.SizeT.fsti(39,4-39,13); use=FStar.SizeT.fsti(39,4-39,13)
  (forall ((@x0 Term))
   (! (implies
     (and
      ;; def=FStar.SizeT.fsti(40,12-40,20); use=FStar.SizeT.fsti(40,12-40,20)
      (Valid
       ;; def=FStar.SizeT.fsti(40,12-40,20); use=FStar.SizeT.fsti(40,12-40,20)
       (FStar.SizeT.fits @x0))
      (HasType @x0 Prims.int))
     (HasType (FStar.SizeT.uint_to_t @x0) (Tm_refine_207024d2522be2ff59992eb07d6dc785 @x0)))
    :pattern ((FStar.SizeT.uint_to_t @x0))
    :qid typing_FStar.SizeT.uint_to_t))
  :named typing_FStar.SizeT.uint_to_t))
; free var typing
;;; Fact-ids: Name FStar.SizeT.v; Namespace FStar.SizeT
(assert
 (! ;; def=FStar.SizeT.fsti(29,4-29,5); use=FStar.SizeT.fsti(29,4-29,5)
  (forall ((@x0 Term))
   (! (implies
     (HasType @x0 (FStar.SizeT.t Dummy_value))
     (HasType (FStar.SizeT.v @x0) Tm_refine_7df43cb9feb536df62477b7b30ce1682))
    :pattern ((FStar.SizeT.v @x0))
    :qid typing_FStar.SizeT.v))
  :named typing_FStar.SizeT.v))
; free var typing
;;; Fact-ids: Name Prims.bool; Namespace Prims
(assert
 (! (HasType Prims.bool Prims.eqtype) :named typing_Prims.bool))
; free var typing
;;; Fact-ids: Name Prims.eq2; Namespace Prims
(assert
 (! ;; def=Prims.fst(183,5-183,8); use=Prims.fst(183,5-183,8)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (implies
     (and (HasType @x1 (Tm_type @u0)) (HasType @x2 @x1) (HasType @x3 @x1))
     (HasType (Prims.eq2 @u0 @x1 @x2 @x3) Prims.logical))
    :pattern ((Prims.eq2 @u0 @x1 @x2 @x3))
    :qid typing_Prims.eq2))
  :named typing_Prims.eq2))
; free var typing
;;; Fact-ids: Name Prims.eqtype; Namespace Prims
(assert
 (! (HasType Prims.eqtype (Tm_type (U_succ U_zero))) :named typing_Prims.eqtype))
; free var typing
;;; Fact-ids: Name Prims.hasEq; Namespace Prims
(assert
 (! ;; def=Prims.fst(77,5-77,10); use=Prims.fst(77,5-77,10)
  (forall ((@u0 Universe) (@x1 Term))
   (! (implies (HasType @x1 (Tm_type @u0)) (HasType (Prims.hasEq @u0 @x1) (Tm_type U_zero)))
    :pattern ((Prims.hasEq @u0 @x1))
    :qid typing_Prims.hasEq))
  :named typing_Prims.hasEq))
; free var typing
;;; Fact-ids: Name Prims.int; Namespace Prims
(assert
 (! (HasType Prims.int Prims.eqtype) :named typing_Prims.int))
; free var typing
;;; Fact-ids: Name Prims.l_True; Namespace Prims
(assert
 (! (HasType Prims.l_True Prims.logical) :named typing_Prims.l_True))
; free var typing
;;; Fact-ids: Name Prims.l_and; Namespace Prims
(assert
 (! ;; def=Prims.fst(196,5-196,10); use=Prims.fst(196,5-196,10)
  (forall ((@x0 Term) (@x1 Term))
   (! (implies
     (and (HasType @x0 Prims.logical) (HasType @x1 Prims.logical))
     (HasType (Prims.l_and @x0 @x1) Prims.logical))
    :pattern ((Prims.l_and @x0 @x1))
    :qid typing_Prims.l_and))
  :named typing_Prims.l_and))
; free var typing
;;; Fact-ids: Name Prims.logical; Namespace Prims
(assert
 (! (HasType Prims.logical (Tm_type (U_succ U_zero))) :named typing_Prims.logical))
; free var typing
;;; Fact-ids: Name Prims.nat; Namespace Prims
(assert
 (! (HasType Prims.nat (Tm_type U_zero)) :named typing_Prims.nat))
; free var typing
;;; Fact-ids: Name Prims.op_Equals_Equals_Equals; Namespace Prims
(assert
 (! ;; def=Prims.fst(506,6-506,9); use=Prims.fst(506,6-506,9)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
   (! (implies
     (and
      (HasType @x1 (Tm_type @u0))
      (HasType @x2 (Tm_type @u0))
      (HasType @x3 @x1)
      (HasType @x4 @x2))
     (HasType (Prims.op_Equals_Equals_Equals @u0 @x1 @x2 @x3 @x4) Prims.logical))
    :pattern ((Prims.op_Equals_Equals_Equals @u0 @x1 @x2 @x3 @x4))
    :qid typing_Prims.op_Equals_Equals_Equals))
  :named typing_Prims.op_Equals_Equals_Equals))
; free var typing
;;; Fact-ids: Name Prims.pos; Namespace Prims
(assert
 (! (HasType Prims.pos (Tm_type U_zero)) :named typing_Prims.pos))
; free var typing
;;; Fact-ids: Name Prims.prop; Namespace Prims
(assert
 (! (HasType Prims.prop (Tm_type (U_succ U_zero))) :named typing_Prims.prop))
; free var typing
;;; Fact-ids: Name Prims.pure_post; Namespace Prims
(assert
 (! ;; def=Prims.fst(324,4-324,13); use=Prims.fst(324,4-324,13)
  (forall ((@u0 Universe) (@x1 Term))
   (! (implies
     (HasType @x1 (Tm_type @u0))
     (HasType (Prims.pure_post @u0 @x1) (Tm_type (U_max (U_succ U_zero) @u0))))
    :pattern ((Prims.pure_post @u0 @x1))
    :qid typing_Prims.pure_post))
  :named typing_Prims.pure_post))
; free var typing
;;; Fact-ids: Name Prims.pure_post'; Namespace Prims
(assert
 (! ;; def=Prims.fst(323,4-323,14); use=Prims.fst(323,4-323,14)
  (forall ((@u0 Universe) (@u1 Universe) (@x2 Term) (@x3 Term))
   (! (implies
     (and (HasType @x2 (Tm_type @u0)) (HasType @x3 (Tm_type @u1)))
     (HasType (Prims.pure_post_ @u0 @u1 @x2 @x3) (Tm_type (U_max (U_succ U_zero) @u0))))
    :pattern ((Prims.pure_post_ @u0 @u1 @x2 @x3))
    :qid typing_Prims.pure_post_))
  :named typing_Prims.pure_post_))
; free var typing
;;; Fact-ids: Name Prims.squash; Namespace Prims
(assert
 (! ;; def=Prims.fst(125,5-125,11); use=Prims.fst(125,5-125,11)
  (forall ((@u0 Universe) (@x1 Term))
   (! (implies (HasType @x1 (Tm_type @u0)) (HasType (Prims.squash @u0 @x1) (Tm_type U_zero)))
    :pattern ((Prims.squash @u0 @x1))
    :qid typing_Prims.squash))
  :named typing_Prims.squash))
; free var typing
;;; Fact-ids: Name Prims.subtype_of; Namespace Prims
(assert
 (! ;; def=Prims.fst(299,4-299,14); use=Prims.fst(299,4-299,14)
  (forall ((@u0 Universe) (@u1 Universe) (@x2 Term) (@x3 Term))
   (! (implies
     (and (HasType @x2 (Tm_type @u0)) (HasType @x3 (Tm_type @u1)))
     (HasType (Prims.subtype_of @u0 @u1 @x2 @x3) Prims.logical))
    :pattern ((Prims.subtype_of @u0 @u1 @x2 @x3))
    :qid typing_Prims.subtype_of))
  :named typing_Prims.subtype_of))
; free var typing
;;; Fact-ids: Name Prims.unit; Namespace Prims
(assert
 (! (HasType Prims.unit Prims.eqtype) :named typing_Prims.unit))
; free var typing
;;; Fact-ids: Name Pulse.Lib.Core.emp; Namespace Pulse.Lib.Core
(assert
 (! ;; def=Pulse.Lib.Core.fsti(77,4-77,7); use=Pulse.Lib.Core.fsti(77,4-77,7)
  (forall ((@u0 Dummy_sort))
   (! (HasType (Pulse.Lib.Core.emp @u0) Pulse.Lib.Core.slprop)
    :pattern ((Pulse.Lib.Core.emp @u0))
    :qid typing_Pulse.Lib.Core.emp))
  :named typing_Pulse.Lib.Core.emp))
; free var typing
;;; Fact-ids: Name Pulse.Lib.Core.slprop; Namespace Pulse.Lib.Core
(assert
 (! (HasType Pulse.Lib.Core.slprop (Tm_type (U_succ (U_succ (U_succ (U_succ U_zero))))))
  :named typing_Pulse.Lib.Core.slprop))
; free var typing
;;; Fact-ids: Name Pulse.Lib.Core.timeless; Namespace Pulse.Lib.Core
(assert
 (! ;; def=Pulse.Lib.Core.fsti(73,4-73,12); use=Pulse.Lib.Core.fsti(73,4-73,12)
  (forall ((@x0 Term))
   (! (implies
     (HasType @x0 Pulse.Lib.Core.slprop)
     (HasType (Pulse.Lib.Core.timeless @x0) Prims.prop))
    :pattern ((Pulse.Lib.Core.timeless @x0))
    :qid typing_Pulse.Lib.Core.timeless))
  :named typing_Pulse.Lib.Core.timeless))
; free var typing
;;; Fact-ids: Name Pulse.Lib.Core.timeless_emp; Namespace Pulse.Lib.Core
(assert
 (! (HasType
   Pulse.Lib.Core.timeless_emp
   (Prims.squash U_zero (Pulse.Lib.Core.timeless (Pulse.Lib.Core.emp Dummy_value))))
  :named typing_Pulse.Lib.Core.timeless_emp))
; Range_const typing
;;; Fact-ids: Name FStar.Range.range; Namespace FStar.Range
(assert
 (! (HasTypeZ (Range_const 1) FStar.Range.range) :named typing_range_const))
; typing for data constructor proxy
;;; Fact-ids: Name Prims.trivial; Namespace Prims; Name Prims.T; Namespace Prims
(assert
 (! (HasType Prims.T@tok Prims.trivial) :named typing_tok_Prims.T@tok))
; unit inversion
;;; Fact-ids: Name Prims.unit; Namespace Prims
(assert
 (! (forall ((@u0 Fuel) (@x1 Term))
   (! (implies (HasTypeFuel @u0 @x1 Prims.unit) (= @x1 Tm_unit))
    :pattern ((HasTypeFuel @u0 @x1 Prims.unit))
    :qid unit_inversion))
  :named unit_inversion))
; unit typing
;;; Fact-ids: Name Prims.unit; Namespace Prims
(assert
 (! (HasType Tm_unit Prims.unit) :named unit_typing))
; well-founded ordering on nat (alt)
;;; Fact-ids: Name Prims.int; Namespace Prims
(assert
 (! (forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
   (! (implies
     (and
      (HasTypeFuel @u0 @x1 Prims.int)
      (HasTypeFuel @u0 @x2 Prims.int)
      (> (BoxInt_proj_0 @x1) 0)
      (>= (BoxInt_proj_0 @x2) 0)
      (< (BoxInt_proj_0 @x2) (BoxInt_proj_0 @x1)))
     (Valid (Prims.precedes U_zero U_zero Prims.lex_t Prims.lex_t @x2 @x1)))
    :pattern
     ((HasTypeFuel @u0 @x1 Prims.int)
      (HasTypeFuel @u0 @x2 Prims.int)
      (Valid (Prims.precedes U_zero U_zero Prims.lex_t Prims.lex_t @x2 @x1)))
    :qid well-founded-ordering-on-nat))
  :named well-founded-ordering-on-nat))
(push) ;; push{2
(declare-fun label_24 () Bool)
(declare-fun label_23 () Bool)
(declare-fun label_22 () Bool)
(declare-fun label_21 () Bool)
(declare-fun label_20 () Bool)
(declare-fun label_19 () Bool)
(declare-fun label_18 () Bool)
(declare-fun label_17 () Bool)
(declare-fun label_16 () Bool)
(declare-fun label_15 () Bool)
(declare-fun label_14 () Bool)
(declare-fun label_13 () Bool)
(declare-fun label_12 () Bool)
(declare-fun label_11 () Bool)
(declare-fun label_10 () Bool)
(declare-fun label_9 () Bool)
(declare-fun label_8 () Bool)
(declare-fun label_7 () Bool)
(declare-fun label_6 () Bool)
(declare-fun label_5 () Bool)
(declare-fun label_4 () Bool)
(declare-fun label_3 () Bool)
(declare-fun label_2 () Bool)
(declare-fun label_1 () Bool)
(declare-fun
 Tm_refine_76acebc334fa7b3ec5e14213c956ea9a
 (Term Term Term Term Term Term Term Term)
 Term)
; refinement kinding
;;; Fact-ids: 
(assert
 (! ;; def=CLRS.Ch23.Kruskal.Impl.fst(1577,6-1583,64); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
  (forall ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term) (@x6 Term) (@x7 Term))
   (! (HasType
     (Tm_refine_76acebc334fa7b3ec5e14213c956ea9a @x0 @x1 @x2 @x3 @x4 @x5 @x6 @x7)
     (Tm_type U_zero))
    :pattern
     ((HasType
       (Tm_refine_76acebc334fa7b3ec5e14213c956ea9a @x0 @x1 @x2 @x3 @x4 @x5 @x6 @x7)
       (Tm_type U_zero)))
    :qid refinement_kinding_Tm_refine_76acebc334fa7b3ec5e14213c956ea9a))
  :named refinement_kinding_Tm_refine_76acebc334fa7b3ec5e14213c956ea9a))
; refinement_interpretation
;;; Fact-ids: 
(assert
 (! ;; def=CLRS.Ch23.Kruskal.Impl.fst(1577,6-1583,64); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
  (forall
    ((@u0 Fuel)
     (@x1 Term)
     (@x2 Term)
     (@x3 Term)
     (@x4 Term)
     (@x5 Term)
     (@x6 Term)
     (@x7 Term)
     (@x8 Term)
     (@x9 Term))
   (! (iff
     (HasTypeFuel
      @u0
      @x1
      (Tm_refine_76acebc334fa7b3ec5e14213c956ea9a @x2 @x3 @x4 @x5 @x6 @x7 @x8 @x9))
     (and
      (HasTypeFuel @u0 @x1 Prims.unit)
      ;; def=CLRS.Ch23.Kruskal.Impl.fst(1577,6-1577,45); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
      (Valid
       ;; def=CLRS.Ch23.Kruskal.Impl.fst(1577,6-1577,45); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
       (CLRS.Ch23.Kruskal.Impl.scan_min_inv @x2 @x3 @x4 (Prims.op_Multiply @x4 @x4) @x5))
      ;; def=CLRS.Ch23.Kruskal.Impl.fst(1578,6-1578,11); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
      (> (BoxInt_proj_0 @x4) (BoxInt_proj_0 (BoxInt 0)))
      ;; def=CLRS.Ch23.Kruskal.Impl.fst(1578,15-1578,39); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
      (= (FStar.Seq.Base.length U_zero Prims.int @x3) (Prims.op_Multiply @x4 @x4))
      ;; def=CLRS.Ch23.Kruskal.Impl.fst(1578,43-1578,66); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
      (>=
       (BoxInt_proj_0 (FStar.Seq.Base.length U_zero (FStar.SizeT.t Dummy_value) @x2))
       (BoxInt_proj_0 @x4))
      ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,6-1579,13); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
      (> (BoxInt_proj_0 @x5) (BoxInt_proj_0 (BoxInt 0)))
      ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,17-1579,24); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
      (< (BoxInt_proj_0 @x6) (BoxInt_proj_0 @x4))
      ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,28-1579,35); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
      (< (BoxInt_proj_0 @x7) (BoxInt_proj_0 @x4))
      ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,39-1579,45); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
      (< (BoxInt_proj_0 @x8) (BoxInt_proj_0 @x4))
      ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,49-1579,55); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
      (< (BoxInt_proj_0 @x9) (BoxInt_proj_0 @x4))
      ;; def=CLRS.Ch23.Kruskal.Impl.fst(1580,6-1580,25); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
      (<
       (BoxInt_proj_0 (Prims.op_Addition (Prims.op_Multiply @x8 @x4) @x9))
       (BoxInt_proj_0 (Prims.op_Multiply @x4 @x4)))
      ;; def=CLRS.Ch23.Kruskal.Impl.fst(1580,29-1580,48); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
      (<
       (BoxInt_proj_0 (Prims.op_Addition (Prims.op_Multiply @x9 @x4) @x8))
       (BoxInt_proj_0 (Prims.op_Multiply @x4 @x4)))
      ;; def=CLRS.Ch23.Kruskal.Impl.fst(1581,6-1581,66); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
      (not
       (=
        (CLRS.Ch23.Kruskal.UF.find_pure @x2 @x6 @x4 @x4)
        (CLRS.Ch23.Kruskal.UF.find_pure @x2 @x7 @x4 @x4)))
      ;; def=CLRS.Ch23.Kruskal.Impl.fst(1582,6-1582,42); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
      (=
       (FStar.Seq.Base.index
        U_zero
        Prims.int
        @x3
        (Prims.op_Addition (Prims.op_Multiply @x6 @x4) @x7))
       @x5)
      ;; def=CLRS.Ch23.Kruskal.Impl.fst(1583,6-1583,64); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
      (not
       (=
        (CLRS.Ch23.Kruskal.UF.find_pure @x2 @x8 @x4 @x4)
        (CLRS.Ch23.Kruskal.UF.find_pure @x2 @x9 @x4 @x4)))))
    :pattern
     ((HasTypeFuel
       @u0
       @x1
       (Tm_refine_76acebc334fa7b3ec5e14213c956ea9a @x2 @x3 @x4 @x5 @x6 @x7 @x8 @x9)))
    :qid refinement_interpretation_Tm_refine_76acebc334fa7b3ec5e14213c956ea9a))
  :named refinement_interpretation_Tm_refine_76acebc334fa7b3ec5e14213c956ea9a))
; haseq for Tm_refine_76acebc334fa7b3ec5e14213c956ea9a
;;; Fact-ids: 
(assert
 (! ;; def=CLRS.Ch23.Kruskal.Impl.fst(1577,6-1583,64); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
  (forall ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term) (@x6 Term) (@x7 Term))
   (! (iff
     (Valid
      (Prims.hasEq
       U_zero
       (Tm_refine_76acebc334fa7b3ec5e14213c956ea9a @x0 @x1 @x2 @x3 @x4 @x5 @x6 @x7)))
     (Valid (Prims.hasEq U_zero Prims.unit)))
    :pattern
     ((Valid
       (Prims.hasEq
        U_zero
        (Tm_refine_76acebc334fa7b3ec5e14213c956ea9a @x0 @x1 @x2 @x3 @x4 @x5 @x6 @x7))))
    :qid haseqTm_refine_76acebc334fa7b3ec5e14213c956ea9a))
  :named haseqTm_refine_76acebc334fa7b3ec5e14213c956ea9a))
; Encoding query formula : forall (sparent: FStar.Seq.Base.seq FStar.SizeT.t)
;   (sadj: FStar.Seq.Base.seq Prims.int)
;   (n: Prims.nat)
;   (vbw: Prims.int)
;   (vbu: Prims.nat)
;   (vbv: Prims.nat)
;   (eu: Prims.nat)
;   (ev: Prims.nat).
;   n * n >= 0 /\
;   (CLRS.Ch23.Kruskal.Impl.scan_min_inv sparent sadj n (n * n) vbw /\ n > 0 /\
;     FStar.Seq.Base.length sadj == n * n /\ FStar.Seq.Base.length sparent >= n /\ vbw > 0 /\ vbu < n /\
;     vbv < n /\ eu < n /\ ev < n /\ eu * n + ev < n * n /\ ev * n + eu < n * n ==>
;     Prims.hasEq Prims.nat) /\
;   (CLRS.Ch23.Kruskal.Impl.scan_min_inv sparent sadj n (n * n) vbw /\ n > 0 /\
;     FStar.Seq.Base.length sadj == n * n /\ FStar.Seq.Base.length sparent >= n /\ vbw > 0 /\ vbu < n /\
;     vbv < n /\ eu < n /\ ev < n /\ eu * n + ev < n * n /\ ev * n + eu < n * n /\
;     CLRS.Ch23.Kruskal.UF.find_pure sparent vbu n n <> CLRS.Ch23.Kruskal.UF.find_pure sparent vbv n n ==>
;     vbu * n + vbv >= 0 /\ vbu * n + vbv < FStar.Seq.Base.length sadj) /\
;   (CLRS.Ch23.Kruskal.Impl.scan_min_inv sparent sadj n (n * n) vbw /\ n > 0 /\
;     FStar.Seq.Base.length sadj == n * n /\ FStar.Seq.Base.length sparent >= n /\ vbw > 0 /\ vbu < n /\
;     vbv < n /\ eu < n /\ ev < n /\ eu * n + ev < n * n /\ ev * n + eu < n * n /\
;     CLRS.Ch23.Kruskal.UF.find_pure sparent vbu n n <> CLRS.Ch23.Kruskal.UF.find_pure sparent vbv n n /\
;     FStar.Seq.Base.index sadj (vbu * n + vbv) = vbw ==>
;     Prims.hasEq Prims.nat) /\
;   (forall (any_result: Prims.logical).
;       CLRS.Ch23.Kruskal.Impl.scan_min_inv sparent sadj n (n * n) vbw /\ (n > 0) /\
;       (FStar.Seq.Base.length sadj == n * n) /\
;       (FStar.Seq.Base.length sparent >= n) /\
;       (vbw > 0) /\
;       (vbu < n) /\
;       (vbv < n) /\
;       (eu < n) /\
;       (ev < n) /\
;       (eu * n + ev < n * n) /\
;       (ev * n + eu < n * n) /\
;       (CLRS.Ch23.Kruskal.UF.find_pure sparent vbu n n <>
;         CLRS.Ch23.Kruskal.UF.find_pure sparent vbv n n) /\
;       (FStar.Seq.Base.index sadj (vbu * n + vbv) = vbw) /\
;       (CLRS.Ch23.Kruskal.UF.find_pure sparent eu n n <>
;         CLRS.Ch23.Kruskal.UF.find_pure sparent ev n n) ==
;       any_result ==>
;       n * n >= 0 /\
;       (CLRS.Ch23.Kruskal.Impl.scan_min_inv sparent sadj n (n * n) vbw /\ n > 0 /\
;         FStar.Seq.Base.length sadj == n * n /\ FStar.Seq.Base.length sparent >= n /\ vbw > 0 /\
;         vbu < n /\ vbv < n /\ eu < n /\ ev < n /\ eu * n + ev < n * n /\ ev * n + eu < n * n ==>
;         Prims.hasEq Prims.nat) /\
;       (CLRS.Ch23.Kruskal.Impl.scan_min_inv sparent sadj n (n * n) vbw /\ n > 0 /\
;         FStar.Seq.Base.length sadj == n * n /\ FStar.Seq.Base.length sparent >= n /\ vbw > 0 /\
;         vbu < n /\ vbv < n /\ eu < n /\ ev < n /\ eu * n + ev < n * n /\ ev * n + eu < n * n /\
;         CLRS.Ch23.Kruskal.UF.find_pure sparent vbu n n <>
;         CLRS.Ch23.Kruskal.UF.find_pure sparent vbv n n ==>
;         vbu * n + vbv >= 0 /\ vbu * n + vbv < FStar.Seq.Base.length sadj) /\
;       (CLRS.Ch23.Kruskal.Impl.scan_min_inv sparent sadj n (n * n) vbw /\ n > 0 /\
;         FStar.Seq.Base.length sadj == n * n /\ FStar.Seq.Base.length sparent >= n /\ vbw > 0 /\
;         vbu < n /\ vbv < n /\ eu < n /\ ev < n /\ eu * n + ev < n * n /\ ev * n + eu < n * n /\
;         CLRS.Ch23.Kruskal.UF.find_pure sparent vbu n n <>
;         CLRS.Ch23.Kruskal.UF.find_pure sparent vbv n n /\
;         FStar.Seq.Base.index sadj (vbu * n + vbv) = vbw ==>
;         Prims.hasEq Prims.nat) /\
;       (forall (_:
;           Prims.squash (CLRS.Ch23.Kruskal.Impl.scan_min_inv sparent sadj n (n * n) vbw /\ n > 0 /\
;               FStar.Seq.Base.length sadj == n * n /\ FStar.Seq.Base.length sparent >= n /\ vbw > 0 /\
;               vbu < n /\ vbv < n /\ eu < n /\ ev < n /\ eu * n + ev < n * n /\ ev * n + eu < n * n /\
;               CLRS.Ch23.Kruskal.UF.find_pure sparent vbu n n <>
;               CLRS.Ch23.Kruskal.UF.find_pure sparent vbv n n /\
;               FStar.Seq.Base.index sadj (vbu * n + vbv) = vbw /\
;               CLRS.Ch23.Kruskal.UF.find_pure sparent eu n n <>
;               CLRS.Ch23.Kruskal.UF.find_pure sparent ev n n)).
;           (* - Could not prove post-condition *)
;           eu * n + ev >= 0 /\ eu * n + ev < FStar.Seq.Base.length sadj /\
;           (FStar.Seq.Base.index sadj (eu * n + ev) >= vbw ==>
;             ev * n + eu >= 0 /\ ev * n + eu < FStar.Seq.Base.length sadj))) /\
;   (forall (p: Prims.pure_post Prims.unit).
;       CLRS.Ch23.Kruskal.Impl.scan_min_inv sparent sadj n (n * n) vbw /\ n > 0 /\
;       FStar.Seq.Base.length sadj == n * n /\ FStar.Seq.Base.length sparent >= n /\ vbw > 0 /\
;       vbu < n /\ vbv < n /\ eu < n /\ ev < n /\ eu * n + ev < n * n /\ ev * n + eu < n * n /\
;       CLRS.Ch23.Kruskal.UF.find_pure sparent vbu n n <>
;       CLRS.Ch23.Kruskal.UF.find_pure sparent vbv n n /\
;       FStar.Seq.Base.index sadj (vbu * n + vbv) = vbw /\
;       CLRS.Ch23.Kruskal.UF.find_pure sparent eu n n <> CLRS.Ch23.Kruskal.UF.find_pure sparent ev n n /\
;       (forall (pure_result: Prims.unit).
;           FStar.Seq.Base.index sadj (eu * n + ev) >= vbw /\
;           FStar.Seq.Base.index sadj (ev * n + eu) >= vbw ==>
;           p pure_result) ==>
;       CLRS.Ch23.Kruskal.Impl.scan_min_inv sparent sadj n (n * n) vbw /\ n > 0 /\
;       FStar.Seq.Base.length sadj == n * n /\
;       (vbw > 0 ==>
;         vbu < n /\ vbv < n /\
;         CLRS.Ch23.Kruskal.UF.find_pure sparent vbu n n <>
;         CLRS.Ch23.Kruskal.UF.find_pure sparent vbv n n /\
;         FStar.Seq.Base.index sadj (vbu * n + vbv) = vbw) /\
;       (forall (pure_result: Prims.unit).
;           (vbw > 0 ==>
;             (forall (u': Prims.nat) (v': Prims.nat).
;                 u' < n /\ v' < n ==>
;                 FStar.Seq.Base.index sadj (u' * n + v') > 0 /\
;                 CLRS.Ch23.Kruskal.UF.find_pure sparent u' n n <>
;                 CLRS.Ch23.Kruskal.UF.find_pure sparent v' n n ==>
;                 FStar.Seq.Base.index sadj (u' * n + v') >= vbw)) /\
;           (vbw = 0 ==>
;             (forall (u': Prims.nat) (v': Prims.nat).
;                 u' < n /\ v' < n ==>
;                 FStar.Seq.Base.index sadj (u' * n + v') <= 0 \/
;                 CLRS.Ch23.Kruskal.UF.find_pure sparent u' n n =
;                 CLRS.Ch23.Kruskal.UF.find_pure sparent v' n n)) ==>
;           p pure_result))
; Context: While encoding a query
; While typechecking the top-level declaration `let scan_min_complete_adj_weight`
(push) ;; push{0
; <fuel='1' ifuel='0'>
;;; Fact-ids: 
(assert (! (= MaxFuel (SFuel ZFuel)) :named @MaxFuel_assumption))
;;; Fact-ids: 
(assert (! (= MaxIFuel ZFuel) :named @MaxIFuel_assumption))
; query
;;; Fact-ids: 
(assert
 (! (not
   (forall ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term) (@x6 Term) (@x7 Term))
    (! (implies
      (and
       (HasType @x0 (FStar.Seq.Base.seq U_zero (FStar.SizeT.t Dummy_value)))
       (HasType @x1 (FStar.Seq.Base.seq U_zero Prims.int))
       (HasType @x2 Prims.nat)
       (HasType @x3 Prims.int)
       (HasType @x4 Prims.nat)
       (HasType @x5 Prims.nat)
       (HasType @x6 Prims.nat)
       (HasType @x7 Prims.nat))
      ;; def=Prims.fst(414,51-467,89); use=Prims.fst(438,19-438,32)
      (and
       ;; def=Prims.fst(682,18-682,24); use=CLRS.Ch23.Kruskal.Impl.fst(1577,34-1577,41)
       (or
        label_1
        ;; def=Prims.fst(682,18-682,24); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
        (>= (BoxInt_proj_0 (Prims.op_Multiply @x2 @x2)) (BoxInt_proj_0 (BoxInt 0))))
       (implies
        ;; def=CLRS.Ch23.Kruskal.Impl.fst(1577,6-1580,48); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
        (and
         ;; def=CLRS.Ch23.Kruskal.Impl.fst(1577,6-1577,45); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
         (Valid
          ;; def=CLRS.Ch23.Kruskal.Impl.fst(1577,6-1577,45); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
          (CLRS.Ch23.Kruskal.Impl.scan_min_inv @x0 @x1 @x2 (Prims.op_Multiply @x2 @x2) @x3))
         ;; def=CLRS.Ch23.Kruskal.Impl.fst(1578,6-1578,11); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
         (> (BoxInt_proj_0 @x2) (BoxInt_proj_0 (BoxInt 0)))
         ;; def=CLRS.Ch23.Kruskal.Impl.fst(1578,15-1578,39); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
         (= (FStar.Seq.Base.length U_zero Prims.int @x1) (Prims.op_Multiply @x2 @x2))
         ;; def=CLRS.Ch23.Kruskal.Impl.fst(1578,43-1578,66); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
         (>=
          (BoxInt_proj_0 (FStar.Seq.Base.length U_zero (FStar.SizeT.t Dummy_value) @x0))
          (BoxInt_proj_0 @x2))
         ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,6-1579,13); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
         (> (BoxInt_proj_0 @x3) (BoxInt_proj_0 (BoxInt 0)))
         ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,17-1579,24); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
         (< (BoxInt_proj_0 @x4) (BoxInt_proj_0 @x2))
         ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,28-1579,35); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
         (< (BoxInt_proj_0 @x5) (BoxInt_proj_0 @x2))
         ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,39-1579,45); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
         (< (BoxInt_proj_0 @x6) (BoxInt_proj_0 @x2))
         ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,49-1579,55); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
         (< (BoxInt_proj_0 @x7) (BoxInt_proj_0 @x2))
         ;; def=CLRS.Ch23.Kruskal.Impl.fst(1580,6-1580,25); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
         (<
          (BoxInt_proj_0 (Prims.op_Addition (Prims.op_Multiply @x6 @x2) @x7))
          (BoxInt_proj_0 (Prims.op_Multiply @x2 @x2)))
         ;; def=CLRS.Ch23.Kruskal.Impl.fst(1580,29-1580,48); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
         (<
          (BoxInt_proj_0 (Prims.op_Addition (Prims.op_Multiply @x7 @x2) @x6))
          (BoxInt_proj_0 (Prims.op_Multiply @x2 @x2))))
        ;; def=Prims.fst(81,23-81,30); use=CLRS.Ch23.Kruskal.Impl.fst(1581,9-1581,18)
        (or
         label_2
         ;; def=Prims.fst(81,23-81,30); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
         (Valid
          ;; def=Prims.fst(81,23-81,30); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
          (Prims.hasEq U_zero Prims.nat))))
       (implies
        ;; def=CLRS.Ch23.Kruskal.Impl.fst(1577,6-1581,66); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
        (and
         ;; def=CLRS.Ch23.Kruskal.Impl.fst(1577,6-1577,45); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
         (Valid
          ;; def=CLRS.Ch23.Kruskal.Impl.fst(1577,6-1577,45); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
          (CLRS.Ch23.Kruskal.Impl.scan_min_inv @x0 @x1 @x2 (Prims.op_Multiply @x2 @x2) @x3))
         ;; def=CLRS.Ch23.Kruskal.Impl.fst(1578,6-1578,11); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
         (> (BoxInt_proj_0 @x2) (BoxInt_proj_0 (BoxInt 0)))
         ;; def=CLRS.Ch23.Kruskal.Impl.fst(1578,15-1578,39); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
         (= (FStar.Seq.Base.length U_zero Prims.int @x1) (Prims.op_Multiply @x2 @x2))
         ;; def=CLRS.Ch23.Kruskal.Impl.fst(1578,43-1578,66); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
         (>=
          (BoxInt_proj_0 (FStar.Seq.Base.length U_zero (FStar.SizeT.t Dummy_value) @x0))
          (BoxInt_proj_0 @x2))
         ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,6-1579,13); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
         (> (BoxInt_proj_0 @x3) (BoxInt_proj_0 (BoxInt 0)))
         ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,17-1579,24); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
         (< (BoxInt_proj_0 @x4) (BoxInt_proj_0 @x2))
         ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,28-1579,35); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
         (< (BoxInt_proj_0 @x5) (BoxInt_proj_0 @x2))
         ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,39-1579,45); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
         (< (BoxInt_proj_0 @x6) (BoxInt_proj_0 @x2))
         ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,49-1579,55); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
         (< (BoxInt_proj_0 @x7) (BoxInt_proj_0 @x2))
         ;; def=CLRS.Ch23.Kruskal.Impl.fst(1580,6-1580,25); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
         (<
          (BoxInt_proj_0 (Prims.op_Addition (Prims.op_Multiply @x6 @x2) @x7))
          (BoxInt_proj_0 (Prims.op_Multiply @x2 @x2)))
         ;; def=CLRS.Ch23.Kruskal.Impl.fst(1580,29-1580,48); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
         (<
          (BoxInt_proj_0 (Prims.op_Addition (Prims.op_Multiply @x7 @x2) @x6))
          (BoxInt_proj_0 (Prims.op_Multiply @x2 @x2)))
         ;; def=CLRS.Ch23.Kruskal.Impl.fst(1581,6-1581,66); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
         (not
          (=
           (CLRS.Ch23.Kruskal.UF.find_pure @x0 @x4 @x2 @x2)
           (CLRS.Ch23.Kruskal.UF.find_pure @x0 @x5 @x2 @x2))))
        ;; def=FStar.Seq.Base.fsti(32,40-32,52); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
        (and
         ;; def=Prims.fst(682,18-682,24); use=CLRS.Ch23.Kruskal.Impl.fst(1582,21-1582,36)
         (or
          label_3
          ;; def=Prims.fst(682,18-682,24); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
          (>=
           (BoxInt_proj_0 (Prims.op_Addition (Prims.op_Multiply @x4 @x2) @x5))
           (BoxInt_proj_0 (BoxInt 0))))
         ;; def=FStar.Seq.Base.fsti(32,40-32,52); use=CLRS.Ch23.Kruskal.Impl.fst(1582,21-1582,36)
         (or
          label_4
          ;; def=FStar.Seq.Base.fsti(32,40-32,52); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
          (<
           (BoxInt_proj_0 (Prims.op_Addition (Prims.op_Multiply @x4 @x2) @x5))
           (BoxInt_proj_0 (FStar.Seq.Base.length U_zero Prims.int @x1))))))
       (implies
        ;; def=CLRS.Ch23.Kruskal.Impl.fst(1577,6-1582,42); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
        (and
         ;; def=CLRS.Ch23.Kruskal.Impl.fst(1577,6-1577,45); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
         (Valid
          ;; def=CLRS.Ch23.Kruskal.Impl.fst(1577,6-1577,45); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
          (CLRS.Ch23.Kruskal.Impl.scan_min_inv @x0 @x1 @x2 (Prims.op_Multiply @x2 @x2) @x3))
         ;; def=CLRS.Ch23.Kruskal.Impl.fst(1578,6-1578,11); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
         (> (BoxInt_proj_0 @x2) (BoxInt_proj_0 (BoxInt 0)))
         ;; def=CLRS.Ch23.Kruskal.Impl.fst(1578,15-1578,39); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
         (= (FStar.Seq.Base.length U_zero Prims.int @x1) (Prims.op_Multiply @x2 @x2))
         ;; def=CLRS.Ch23.Kruskal.Impl.fst(1578,43-1578,66); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
         (>=
          (BoxInt_proj_0 (FStar.Seq.Base.length U_zero (FStar.SizeT.t Dummy_value) @x0))
          (BoxInt_proj_0 @x2))
         ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,6-1579,13); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
         (> (BoxInt_proj_0 @x3) (BoxInt_proj_0 (BoxInt 0)))
         ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,17-1579,24); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
         (< (BoxInt_proj_0 @x4) (BoxInt_proj_0 @x2))
         ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,28-1579,35); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
         (< (BoxInt_proj_0 @x5) (BoxInt_proj_0 @x2))
         ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,39-1579,45); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
         (< (BoxInt_proj_0 @x6) (BoxInt_proj_0 @x2))
         ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,49-1579,55); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
         (< (BoxInt_proj_0 @x7) (BoxInt_proj_0 @x2))
         ;; def=CLRS.Ch23.Kruskal.Impl.fst(1580,6-1580,25); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
         (<
          (BoxInt_proj_0 (Prims.op_Addition (Prims.op_Multiply @x6 @x2) @x7))
          (BoxInt_proj_0 (Prims.op_Multiply @x2 @x2)))
         ;; def=CLRS.Ch23.Kruskal.Impl.fst(1580,29-1580,48); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
         (<
          (BoxInt_proj_0 (Prims.op_Addition (Prims.op_Multiply @x7 @x2) @x6))
          (BoxInt_proj_0 (Prims.op_Multiply @x2 @x2)))
         ;; def=CLRS.Ch23.Kruskal.Impl.fst(1581,6-1581,66); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
         (not
          (=
           (CLRS.Ch23.Kruskal.UF.find_pure @x0 @x4 @x2 @x2)
           (CLRS.Ch23.Kruskal.UF.find_pure @x0 @x5 @x2 @x2)))
         ;; def=CLRS.Ch23.Kruskal.Impl.fst(1582,6-1582,42); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
         (=
          (FStar.Seq.Base.index
           U_zero
           Prims.int
           @x1
           (Prims.op_Addition (Prims.op_Multiply @x4 @x2) @x5))
          @x3))
        ;; def=Prims.fst(81,23-81,30); use=CLRS.Ch23.Kruskal.Impl.fst(1583,40-1583,49)
        (or
         label_5
         ;; def=Prims.fst(81,23-81,30); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
         (Valid
          ;; def=Prims.fst(81,23-81,30); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
          (Prims.hasEq U_zero Prims.nat))))
       ;; def=Prims.fst(459,66-459,102); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
       (forall ((@x8 Term))
        (! (implies
          (and
           (HasType @x8 Prims.logical)
           ;; def=FStar.Pervasives.fsti(112,28-112,31); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
           (=
            (Prims.l_and
             (Prims.l_and
              (Prims.l_and
               (Prims.l_and
                (Prims.l_and
                 (Prims.l_and
                  (Prims.l_and
                   (Prims.l_and
                    (Prims.l_and
                     (Prims.l_and
                      (Prims.l_and
                       (Prims.l_and
                        (Prims.l_and
                         (CLRS.Ch23.Kruskal.Impl.scan_min_inv
                          @x0
                          @x1
                          @x2
                          (Prims.op_Multiply @x2 @x2)
                          @x3)
                         (Prims.b2t (Prims.op_GreaterThan @x2 (BoxInt 0))))
                        (Prims.eq2
                         U_zero
                         Prims.int
                         (FStar.Seq.Base.length U_zero Prims.int @x1)
                         (Prims.op_Multiply @x2 @x2)))
                       (Prims.b2t
                        (Prims.op_GreaterThanOrEqual
                         (FStar.Seq.Base.length U_zero (FStar.SizeT.t Dummy_value) @x0)
                         @x2)))
                      (Prims.b2t (Prims.op_GreaterThan @x3 (BoxInt 0))))
                     (Prims.b2t (Prims.op_LessThan @x4 @x2)))
                    (Prims.b2t (Prims.op_LessThan @x5 @x2)))
                   (Prims.b2t (Prims.op_LessThan @x6 @x2)))
                  (Prims.b2t (Prims.op_LessThan @x7 @x2)))
                 (Prims.b2t
                  (Prims.op_LessThan
                   (Prims.op_Addition (Prims.op_Multiply @x6 @x2) @x7)
                   (Prims.op_Multiply @x2 @x2))))
                (Prims.b2t
                 (Prims.op_LessThan
                  (Prims.op_Addition (Prims.op_Multiply @x7 @x2) @x6)
                  (Prims.op_Multiply @x2 @x2))))
               (Prims.b2t
                (Prims.op_disEquality
                 Prims.nat
                 (CLRS.Ch23.Kruskal.UF.find_pure @x0 @x4 @x2 @x2)
                 (CLRS.Ch23.Kruskal.UF.find_pure @x0 @x5 @x2 @x2))))
              (Prims.b2t
               (Prims.op_Equality
                Prims.int
                (FStar.Seq.Base.index
                 U_zero
                 Prims.int
                 @x1
                 (Prims.op_Addition (Prims.op_Multiply @x4 @x2) @x5))
                @x3)))
             (Prims.b2t
              (Prims.op_disEquality
               Prims.nat
               (CLRS.Ch23.Kruskal.UF.find_pure @x0 @x6 @x2 @x2)
               (CLRS.Ch23.Kruskal.UF.find_pure @x0 @x7 @x2 @x2))))
            @x8))
          ;; def=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
          (and
           ;; def=Prims.fst(682,18-682,24); use=CLRS.Ch23.Kruskal.Impl.fst(1575,4-1575,9)
           (or
            label_6
            ;; def=Prims.fst(682,18-682,24); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
            (>= (BoxInt_proj_0 (Prims.op_Multiply @x2 @x2)) (BoxInt_proj_0 (BoxInt 0))))
           (implies
            ;; def=CLRS.Ch23.Kruskal.Impl.fst(1577,6-1580,48); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
            (and
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(1577,6-1577,45); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
             (Valid
              ;; def=CLRS.Ch23.Kruskal.Impl.fst(1577,6-1577,45); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
              (CLRS.Ch23.Kruskal.Impl.scan_min_inv @x0 @x1 @x2 (Prims.op_Multiply @x2 @x2) @x3))
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(1578,6-1578,11); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
             (> (BoxInt_proj_0 @x2) (BoxInt_proj_0 (BoxInt 0)))
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(1578,15-1578,39); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
             (= (FStar.Seq.Base.length U_zero Prims.int @x1) (Prims.op_Multiply @x2 @x2))
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(1578,43-1578,66); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
             (>=
              (BoxInt_proj_0 (FStar.Seq.Base.length U_zero (FStar.SizeT.t Dummy_value) @x0))
              (BoxInt_proj_0 @x2))
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,6-1579,13); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
             (> (BoxInt_proj_0 @x3) (BoxInt_proj_0 (BoxInt 0)))
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,17-1579,24); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
             (< (BoxInt_proj_0 @x4) (BoxInt_proj_0 @x2))
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,28-1579,35); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
             (< (BoxInt_proj_0 @x5) (BoxInt_proj_0 @x2))
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,39-1579,45); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
             (< (BoxInt_proj_0 @x6) (BoxInt_proj_0 @x2))
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,49-1579,55); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
             (< (BoxInt_proj_0 @x7) (BoxInt_proj_0 @x2))
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(1580,6-1580,25); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
             (<
              (BoxInt_proj_0 (Prims.op_Addition (Prims.op_Multiply @x6 @x2) @x7))
              (BoxInt_proj_0 (Prims.op_Multiply @x2 @x2)))
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(1580,29-1580,48); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
             (<
              (BoxInt_proj_0 (Prims.op_Addition (Prims.op_Multiply @x7 @x2) @x6))
              (BoxInt_proj_0 (Prims.op_Multiply @x2 @x2))))
            ;; def=Prims.fst(81,23-81,30); use=CLRS.Ch23.Kruskal.Impl.fst(1575,4-1575,9)
            (or
             label_7
             ;; def=Prims.fst(81,23-81,30); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
             (Valid
              ;; def=Prims.fst(81,23-81,30); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
              (Prims.hasEq U_zero Prims.nat))))
           (implies
            ;; def=CLRS.Ch23.Kruskal.Impl.fst(1577,6-1581,66); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
            (and
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(1577,6-1577,45); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
             (Valid
              ;; def=CLRS.Ch23.Kruskal.Impl.fst(1577,6-1577,45); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
              (CLRS.Ch23.Kruskal.Impl.scan_min_inv @x0 @x1 @x2 (Prims.op_Multiply @x2 @x2) @x3))
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(1578,6-1578,11); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
             (> (BoxInt_proj_0 @x2) (BoxInt_proj_0 (BoxInt 0)))
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(1578,15-1578,39); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
             (= (FStar.Seq.Base.length U_zero Prims.int @x1) (Prims.op_Multiply @x2 @x2))
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(1578,43-1578,66); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
             (>=
              (BoxInt_proj_0 (FStar.Seq.Base.length U_zero (FStar.SizeT.t Dummy_value) @x0))
              (BoxInt_proj_0 @x2))
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,6-1579,13); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
             (> (BoxInt_proj_0 @x3) (BoxInt_proj_0 (BoxInt 0)))
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,17-1579,24); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
             (< (BoxInt_proj_0 @x4) (BoxInt_proj_0 @x2))
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,28-1579,35); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
             (< (BoxInt_proj_0 @x5) (BoxInt_proj_0 @x2))
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,39-1579,45); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
             (< (BoxInt_proj_0 @x6) (BoxInt_proj_0 @x2))
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,49-1579,55); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
             (< (BoxInt_proj_0 @x7) (BoxInt_proj_0 @x2))
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(1580,6-1580,25); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
             (<
              (BoxInt_proj_0 (Prims.op_Addition (Prims.op_Multiply @x6 @x2) @x7))
              (BoxInt_proj_0 (Prims.op_Multiply @x2 @x2)))
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(1580,29-1580,48); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
             (<
              (BoxInt_proj_0 (Prims.op_Addition (Prims.op_Multiply @x7 @x2) @x6))
              (BoxInt_proj_0 (Prims.op_Multiply @x2 @x2)))
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(1581,6-1581,66); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
             (not
              (=
               (CLRS.Ch23.Kruskal.UF.find_pure @x0 @x4 @x2 @x2)
               (CLRS.Ch23.Kruskal.UF.find_pure @x0 @x5 @x2 @x2))))
            ;; def=FStar.Seq.Base.fsti(32,40-32,52); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
            (and
             ;; def=Prims.fst(682,18-682,24); use=CLRS.Ch23.Kruskal.Impl.fst(1575,4-1575,9)
             (or
              label_8
              ;; def=Prims.fst(682,18-682,24); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
              (>=
               (BoxInt_proj_0 (Prims.op_Addition (Prims.op_Multiply @x4 @x2) @x5))
               (BoxInt_proj_0 (BoxInt 0))))
             ;; def=FStar.Seq.Base.fsti(32,40-32,52); use=CLRS.Ch23.Kruskal.Impl.fst(1575,4-1575,9)
             (or
              label_9
              ;; def=FStar.Seq.Base.fsti(32,40-32,52); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
              (<
               (BoxInt_proj_0 (Prims.op_Addition (Prims.op_Multiply @x4 @x2) @x5))
               (BoxInt_proj_0 (FStar.Seq.Base.length U_zero Prims.int @x1))))))
           (implies
            ;; def=CLRS.Ch23.Kruskal.Impl.fst(1577,6-1582,42); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
            (and
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(1577,6-1577,45); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
             (Valid
              ;; def=CLRS.Ch23.Kruskal.Impl.fst(1577,6-1577,45); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
              (CLRS.Ch23.Kruskal.Impl.scan_min_inv @x0 @x1 @x2 (Prims.op_Multiply @x2 @x2) @x3))
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(1578,6-1578,11); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
             (> (BoxInt_proj_0 @x2) (BoxInt_proj_0 (BoxInt 0)))
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(1578,15-1578,39); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
             (= (FStar.Seq.Base.length U_zero Prims.int @x1) (Prims.op_Multiply @x2 @x2))
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(1578,43-1578,66); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
             (>=
              (BoxInt_proj_0 (FStar.Seq.Base.length U_zero (FStar.SizeT.t Dummy_value) @x0))
              (BoxInt_proj_0 @x2))
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,6-1579,13); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
             (> (BoxInt_proj_0 @x3) (BoxInt_proj_0 (BoxInt 0)))
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,17-1579,24); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
             (< (BoxInt_proj_0 @x4) (BoxInt_proj_0 @x2))
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,28-1579,35); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
             (< (BoxInt_proj_0 @x5) (BoxInt_proj_0 @x2))
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,39-1579,45); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
             (< (BoxInt_proj_0 @x6) (BoxInt_proj_0 @x2))
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,49-1579,55); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
             (< (BoxInt_proj_0 @x7) (BoxInt_proj_0 @x2))
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(1580,6-1580,25); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
             (<
              (BoxInt_proj_0 (Prims.op_Addition (Prims.op_Multiply @x6 @x2) @x7))
              (BoxInt_proj_0 (Prims.op_Multiply @x2 @x2)))
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(1580,29-1580,48); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
             (<
              (BoxInt_proj_0 (Prims.op_Addition (Prims.op_Multiply @x7 @x2) @x6))
              (BoxInt_proj_0 (Prims.op_Multiply @x2 @x2)))
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(1581,6-1581,66); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
             (not
              (=
               (CLRS.Ch23.Kruskal.UF.find_pure @x0 @x4 @x2 @x2)
               (CLRS.Ch23.Kruskal.UF.find_pure @x0 @x5 @x2 @x2)))
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(1582,6-1582,42); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
             (=
              (FStar.Seq.Base.index
               U_zero
               Prims.int
               @x1
               (Prims.op_Addition (Prims.op_Multiply @x4 @x2) @x5))
              @x3))
            ;; def=Prims.fst(81,23-81,30); use=CLRS.Ch23.Kruskal.Impl.fst(1575,4-1575,9)
            (or
             label_10
             ;; def=Prims.fst(81,23-81,30); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
             (Valid
              ;; def=Prims.fst(81,23-81,30); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
              (Prims.hasEq U_zero Prims.nat))))
           ;; def=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
           (forall ((@x9 Term))
            (! (implies
              (HasType
               @x9
               (Tm_refine_76acebc334fa7b3ec5e14213c956ea9a @x0 @x1 @x2 @x3 @x4 @x5 @x6 @x7))
              ;; def=CLRS.Ch23.Kruskal.Impl.fst(1585,6-1586,34); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
              (and
               ;; def=Prims.fst(682,18-682,24); use=CLRS.Ch23.Kruskal.Impl.fst(1585,21-1585,34)
               (or
                label_11
                ;; def=Prims.fst(682,18-682,24); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
                (>=
                 (BoxInt_proj_0 (Prims.op_Addition (Prims.op_Multiply @x6 @x2) @x7))
                 (BoxInt_proj_0 (BoxInt 0))))
               ;; def=FStar.Seq.Base.fsti(32,40-32,52); use=CLRS.Ch23.Kruskal.Impl.fst(1585,21-1585,34)
               (or
                label_12
                ;; def=FStar.Seq.Base.fsti(32,40-32,52); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
                (<
                 (BoxInt_proj_0 (Prims.op_Addition (Prims.op_Multiply @x6 @x2) @x7))
                 (BoxInt_proj_0 (FStar.Seq.Base.length U_zero Prims.int @x1))))
               (implies
                ;; def=CLRS.Ch23.Kruskal.Impl.fst(1585,6-1585,41); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
                (>=
                 (BoxInt_proj_0
                  (FStar.Seq.Base.index
                   U_zero
                   Prims.int
                   @x1
                   (Prims.op_Addition (Prims.op_Multiply @x6 @x2) @x7)))
                 (BoxInt_proj_0 @x3))
                ;; def=FStar.Seq.Base.fsti(32,40-32,52); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
                (and
                 ;; def=Prims.fst(682,18-682,24); use=CLRS.Ch23.Kruskal.Impl.fst(1586,21-1586,34)
                 (or
                  label_13
                  ;; def=Prims.fst(682,18-682,24); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
                  (>=
                   (BoxInt_proj_0 (Prims.op_Addition (Prims.op_Multiply @x7 @x2) @x6))
                   (BoxInt_proj_0 (BoxInt 0))))
                 ;; def=FStar.Seq.Base.fsti(32,40-32,52); use=CLRS.Ch23.Kruskal.Impl.fst(1586,21-1586,34)
                 (or
                  label_14
                  ;; def=FStar.Seq.Base.fsti(32,40-32,52); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
                  (<
                   (BoxInt_proj_0 (Prims.op_Addition (Prims.op_Multiply @x7 @x2) @x6))
                   (BoxInt_proj_0 (FStar.Seq.Base.length U_zero Prims.int @x1))))))))
             :qid @query.2))))
         :qid @query.1))
       ;; def=Prims.fst(414,51-414,91); use=Prims.fst(438,19-438,32)
       (forall ((@x8 Term))
        (! (implies
          (and
           (HasType @x8 (Prims.pure_post U_zero Prims.unit))
           ;; def=CLRS.Ch23.Kruskal.Impl.fst(1577,6-1577,45); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
           (Valid
            ;; def=CLRS.Ch23.Kruskal.Impl.fst(1577,6-1577,45); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
            (CLRS.Ch23.Kruskal.Impl.scan_min_inv @x0 @x1 @x2 (Prims.op_Multiply @x2 @x2) @x3))
           ;; def=CLRS.Ch23.Kruskal.Impl.fst(1578,6-1578,11); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
           (> (BoxInt_proj_0 @x2) (BoxInt_proj_0 (BoxInt 0)))
           ;; def=CLRS.Ch23.Kruskal.Impl.fst(1578,15-1578,39); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
           (= (FStar.Seq.Base.length U_zero Prims.int @x1) (Prims.op_Multiply @x2 @x2))
           ;; def=CLRS.Ch23.Kruskal.Impl.fst(1578,43-1578,66); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
           (>=
            (BoxInt_proj_0 (FStar.Seq.Base.length U_zero (FStar.SizeT.t Dummy_value) @x0))
            (BoxInt_proj_0 @x2))
           ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,6-1579,13); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
           (> (BoxInt_proj_0 @x3) (BoxInt_proj_0 (BoxInt 0)))
           ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,17-1579,24); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
           (< (BoxInt_proj_0 @x4) (BoxInt_proj_0 @x2))
           ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,28-1579,35); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
           (< (BoxInt_proj_0 @x5) (BoxInt_proj_0 @x2))
           ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,39-1579,45); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
           (< (BoxInt_proj_0 @x6) (BoxInt_proj_0 @x2))
           ;; def=CLRS.Ch23.Kruskal.Impl.fst(1579,49-1579,55); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
           (< (BoxInt_proj_0 @x7) (BoxInt_proj_0 @x2))
           ;; def=CLRS.Ch23.Kruskal.Impl.fst(1580,6-1580,25); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
           (<
            (BoxInt_proj_0 (Prims.op_Addition (Prims.op_Multiply @x6 @x2) @x7))
            (BoxInt_proj_0 (Prims.op_Multiply @x2 @x2)))
           ;; def=CLRS.Ch23.Kruskal.Impl.fst(1580,29-1580,48); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
           (<
            (BoxInt_proj_0 (Prims.op_Addition (Prims.op_Multiply @x7 @x2) @x6))
            (BoxInt_proj_0 (Prims.op_Multiply @x2 @x2)))
           ;; def=CLRS.Ch23.Kruskal.Impl.fst(1581,6-1581,66); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
           (not
            (=
             (CLRS.Ch23.Kruskal.UF.find_pure @x0 @x4 @x2 @x2)
             (CLRS.Ch23.Kruskal.UF.find_pure @x0 @x5 @x2 @x2)))
           ;; def=CLRS.Ch23.Kruskal.Impl.fst(1582,6-1582,42); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
           (=
            (FStar.Seq.Base.index
             U_zero
             Prims.int
             @x1
             (Prims.op_Addition (Prims.op_Multiply @x4 @x2) @x5))
            @x3)
           ;; def=CLRS.Ch23.Kruskal.Impl.fst(1583,6-1583,64); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
           (not
            (=
             (CLRS.Ch23.Kruskal.UF.find_pure @x0 @x6 @x2 @x2)
             (CLRS.Ch23.Kruskal.UF.find_pure @x0 @x7 @x2 @x2)))
           ;; def=Prims.fst(449,36-449,97); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
           (forall ((@x9 Term))
            (! (implies
              (and
               (or label_15 (HasType @x9 Prims.unit))
               ;; def=CLRS.Ch23.Kruskal.Impl.fst(1585,6-1585,41); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
               (or
                label_16
                ;; def=CLRS.Ch23.Kruskal.Impl.fst(1585,6-1585,41); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
                (>=
                 (BoxInt_proj_0
                  (FStar.Seq.Base.index
                   U_zero
                   Prims.int
                   @x1
                   (Prims.op_Addition (Prims.op_Multiply @x6 @x2) @x7)))
                 (BoxInt_proj_0 @x3)))
               ;; def=CLRS.Ch23.Kruskal.Impl.fst(1586,6-1586,41); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
               (or
                label_17
                ;; def=CLRS.Ch23.Kruskal.Impl.fst(1586,6-1586,41); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
                (>=
                 (BoxInt_proj_0
                  (FStar.Seq.Base.index
                   U_zero
                   Prims.int
                   @x1
                   (Prims.op_Addition (Prims.op_Multiply @x7 @x2) @x6)))
                 (BoxInt_proj_0 @x3))))
              ;; def=Prims.fst(449,83-449,96); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
              (Valid
               ;; def=Prims.fst(449,83-449,96); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
               (ApplyTT @x8 @x9)))
             :pattern
              (;; def=Prims.fst(449,83-449,96); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
               (Valid
                ;; def=Prims.fst(449,83-449,96); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
                (ApplyTT @x8 @x9)))
             :qid @query.4)))
          ;; def=Prims.fst(449,29-449,97); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
          (and
           ;; def=CLRS.Ch23.Kruskal.Impl.fst(201,6-201,45); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,25)
           (or
            label_18
            ;; def=CLRS.Ch23.Kruskal.Impl.fst(201,6-201,45); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,25)
            (Valid
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(201,6-201,45); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,25)
             (CLRS.Ch23.Kruskal.Impl.scan_min_inv @x0 @x1 @x2 (Prims.op_Multiply @x2 @x2) @x3)))
           ;; def=CLRS.Ch23.Kruskal.Impl.fst(202,6-202,11); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,25)
           (or
            label_19
            ;; def=CLRS.Ch23.Kruskal.Impl.fst(202,6-202,11); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,25)
            (> (BoxInt_proj_0 @x2) (BoxInt_proj_0 (BoxInt 0))))
           ;; def=CLRS.Ch23.Kruskal.Impl.fst(202,15-202,39); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,25)
           (or
            label_20
            ;; def=CLRS.Ch23.Kruskal.Impl.fst(202,15-202,39); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,25)
            (= (FStar.Seq.Base.length U_zero Prims.int @x1) (Prims.op_Multiply @x2 @x2)))
           (implies
            ;; def=CLRS.Ch23.Kruskal.Impl.fst(203,7-203,14); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,25)
            (> (BoxInt_proj_0 @x3) (BoxInt_proj_0 (BoxInt 0)))
            ;; def=CLRS.Ch23.Kruskal.Impl.fst(203,19-205,44); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,25)
            (and
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(203,19-203,26); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,25)
             (or
              label_21
              ;; def=CLRS.Ch23.Kruskal.Impl.fst(203,19-203,26); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,25)
              (< (BoxInt_proj_0 @x4) (BoxInt_proj_0 @x2)))
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(203,30-203,37); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,25)
             (or
              label_22
              ;; def=CLRS.Ch23.Kruskal.Impl.fst(203,30-203,37); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,25)
              (< (BoxInt_proj_0 @x5) (BoxInt_proj_0 @x2)))
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(204,8-204,68); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,25)
             (or
              label_23
              ;; def=CLRS.Ch23.Kruskal.Impl.fst(204,8-204,68); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,25)
              (not
               (=
                (CLRS.Ch23.Kruskal.UF.find_pure @x0 @x4 @x2 @x2)
                (CLRS.Ch23.Kruskal.UF.find_pure @x0 @x5 @x2 @x2))))
             ;; def=CLRS.Ch23.Kruskal.Impl.fst(205,8-205,44); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,25)
             (or
              label_24
              ;; def=CLRS.Ch23.Kruskal.Impl.fst(205,8-205,44); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,25)
              (=
               (FStar.Seq.Base.index
                U_zero
                Prims.int
                @x1
                (Prims.op_Addition (Prims.op_Multiply @x4 @x2) @x5))
               @x3))))
           ;; def=Prims.fst(449,36-449,97); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
           (forall ((@x9 Term))
            (! (implies
              (and
               (HasType @x9 Prims.unit)
               ;; def=CLRS.Ch23.Kruskal.Impl.fst(207,6-211,47); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,25)
               (implies
                ;; def=CLRS.Ch23.Kruskal.Impl.fst(207,7-207,14); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,25)
                (> (BoxInt_proj_0 @x3) (BoxInt_proj_0 (BoxInt 0)))
                ;; def=CLRS.Ch23.Kruskal.Impl.fst(208,8-211,46); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,25)
                (forall ((@x10 Term) (@x11 Term))
                 (! (implies
                   (and
                    (HasType @x10 Prims.nat)
                    (HasType @x11 Prims.nat)
                    ;; def=CLRS.Ch23.Kruskal.Impl.fst(208,30-208,36); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,25)
                    (< (BoxInt_proj_0 @x10) (BoxInt_proj_0 @x2))
                    ;; def=CLRS.Ch23.Kruskal.Impl.fst(208,40-208,46); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,25)
                    (< (BoxInt_proj_0 @x11) (BoxInt_proj_0 @x2))
                    ;; def=CLRS.Ch23.Kruskal.Impl.fst(209,11-209,43); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,25)
                    (>
                     (BoxInt_proj_0
                      (FStar.Seq.Base.index
                       U_zero
                       Prims.int
                       @x1
                       (Prims.op_Addition (Prims.op_Multiply @x10 @x2) @x11)))
                     (BoxInt_proj_0 (BoxInt 0)))
                    ;; def=CLRS.Ch23.Kruskal.Impl.fst(210,11-210,69); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,25)
                    (not
                     (=
                      (CLRS.Ch23.Kruskal.UF.find_pure @x0 @x10 @x2 @x2)
                      (CLRS.Ch23.Kruskal.UF.find_pure @x0 @x11 @x2 @x2))))
                   ;; def=CLRS.Ch23.Kruskal.Impl.fst(211,10-211,45); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,25)
                   (>=
                    (BoxInt_proj_0
                     (FStar.Seq.Base.index
                      U_zero
                      Prims.int
                      @x1
                      (Prims.op_Addition (Prims.op_Multiply @x10 @x2) @x11)))
                    (BoxInt_proj_0 @x3)))
                  :qid @query.6)))
               ;; def=CLRS.Ch23.Kruskal.Impl.fst(212,6-215,69); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,25)
               (implies
                ;; def=CLRS.Ch23.Kruskal.Impl.fst(212,7-212,14); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,25)
                (= @x3 (BoxInt 0))
                ;; def=CLRS.Ch23.Kruskal.Impl.fst(213,8-215,68); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,25)
                (forall ((@x10 Term) (@x11 Term))
                 (! (implies
                   (and
                    (HasType @x10 Prims.nat)
                    (HasType @x11 Prims.nat)
                    ;; def=CLRS.Ch23.Kruskal.Impl.fst(213,30-213,36); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,25)
                    (< (BoxInt_proj_0 @x10) (BoxInt_proj_0 @x2))
                    ;; def=CLRS.Ch23.Kruskal.Impl.fst(213,40-213,46); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,25)
                    (< (BoxInt_proj_0 @x11) (BoxInt_proj_0 @x2)))
                   ;; def=CLRS.Ch23.Kruskal.Impl.fst(214,10-215,67); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,25)
                   (or
                    ;; def=CLRS.Ch23.Kruskal.Impl.fst(214,10-214,43); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,25)
                    (<=
                     (BoxInt_proj_0
                      (FStar.Seq.Base.index
                       U_zero
                       Prims.int
                       @x1
                       (Prims.op_Addition (Prims.op_Multiply @x10 @x2) @x11)))
                     (BoxInt_proj_0 (BoxInt 0)))
                    ;; def=CLRS.Ch23.Kruskal.Impl.fst(215,10-215,67); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,25)
                    (=
                     (CLRS.Ch23.Kruskal.UF.find_pure @x0 @x10 @x2 @x2)
                     (CLRS.Ch23.Kruskal.UF.find_pure @x0 @x11 @x2 @x2))))
                  :qid @query.7))))
              ;; def=Prims.fst(449,83-449,96); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
              (Valid
               ;; def=Prims.fst(449,83-449,96); use=CLRS.Ch23.Kruskal.Impl.fst(1587,4-1587,52)
               (ApplyTT @x8 @x9)))
             :qid @query.5))))
         :qid @query.3))))
     :qid @query)))
  :named @query))
(set-option :rlimit 25000000)
(echo "<initial_stats>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "</initial_stats>")
(echo "<result>")
(check-sat)
(echo "</result>")
(set-option :rlimit 0)
(echo "<reason-unknown>") (get-info :reason-unknown) (echo "</reason-unknown>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "<labels>")
(echo "label_24")
(eval label_24)
(echo "label_23")
(eval label_23)
(echo "label_22")
(eval label_22)
(echo "label_21")
(eval label_21)
(echo "label_20")
(eval label_20)
(echo "label_19")
(eval label_19)
(echo "label_18")
(eval label_18)
(echo "label_17")
(eval label_17)
(echo "label_16")
(eval label_16)
(echo "label_15")
(eval label_15)
(echo "label_14")
(eval label_14)
(echo "label_13")
(eval label_13)
(echo "label_12")
(eval label_12)
(echo "label_11")
(eval label_11)
(echo "label_10")
(eval label_10)
(echo "label_9")
(eval label_9)
(echo "label_8")
(eval label_8)
(echo "label_7")
(eval label_7)
(echo "label_6")
(eval label_6)
(echo "label_5")
(eval label_5)
(echo "label_4")
(eval label_4)
(echo "label_3")
(eval label_3)
(echo "label_2")
(eval label_2)
(echo "label_1")
(eval label_1)
(echo "</labels>")
(echo "Done!")
(pop) ;; 0}pop

; QUERY ID: (CLRS.Ch23.Kruskal.Impl.scan_min_complete_adj_weight, 1)
; STATUS: unknown because (incomplete quantifiers)
