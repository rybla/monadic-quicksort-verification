(set-option :auto-config false)
(set-option :model true)
(set-option :model.partial false)

(set-option :smt.mbqi false)

(define-sort Str () Int)
(declare-fun strLen (Str) Int)
(declare-fun subString (Str Int Int) Str)
(declare-fun concatString (Str Str) Str)
(define-sort Elt () Int)
(define-sort LSet () (Array Elt Bool))
(define-fun smt_set_emp () LSet ((as const LSet) false))
(define-fun smt_set_mem ((x Elt) (s LSet)) Bool (select s x))
(define-fun smt_set_add ((s LSet) (x Elt)) LSet (store s x true))
(define-fun smt_set_cup ((s1 LSet) (s2 LSet)) LSet ((_ map or) s1 s2))
(define-fun smt_set_cap ((s1 LSet) (s2 LSet)) LSet ((_ map and) s1 s2))
(define-fun smt_set_com ((s LSet)) LSet ((_ map not) s))
(define-fun smt_set_dif ((s1 LSet) (s2 LSet)) LSet (smt_set_cap s1 (smt_set_com s2)))
(define-fun smt_set_sub ((s1 LSet) (s2 LSet)) Bool (= smt_set_emp (smt_set_dif s1 s2)))
(define-sort Map () (Array Elt Elt))
(define-fun smt_map_sel ((m Map) (k Elt)) Elt (select m k))
(define-fun smt_map_sto ((m Map) (k Elt) (v Elt)) Map (store m k v))
(define-fun smt_map_cup ((m1 Map) (m2 Map)) Map ((_ map (+ (Elt Elt) Elt)) m1 m2))
(define-fun smt_map_def ((v Elt)) Map ((as const (Map)) v))
(define-fun bool_to_int ((b Bool)) Int (ite b 1 0))
(define-fun Z3_OP_MUL ((x Int) (y Int)) Int (* x y))
(define-fun Z3_OP_DIV ((x Int) (y Int)) Int (div x y))
(declare-datatypes ((Natural.Natural 0)) ((par () (Natural.Zero (Natural.Suc (lqdc$35$$35$$36$select$35$$35$Natural.Suc$35$$35$1 Natural.Natural))))))
(declare-fun GHC.Base.id () Int)
(declare-fun cast_as_int () Int)
(declare-fun GHC.List.init () Int)
(declare-fun n$35$$35$a3h8 () Natural.Natural)
(declare-fun addrLen () Int)
(declare-fun papp5 () Int)
(declare-fun GHC.List.iterate () Int)
(declare-fun x_Tuple21 () Int)
(declare-fun GHC.Classes.$61$$61$ () Int)
(declare-fun GHC.Types.C$35$ () Int)
(declare-fun GHC.List.drop () Int)
(declare-fun is$36$GHC.Types.$91$$93$ () Int)
(declare-fun Data.Foldable.length () Int)
(declare-fun x_Tuple33 () Int)
(declare-fun is$36$GHC.Tuple.$40$$44$$41$ () Int)
(declare-fun GHC.Types.LT () Int)
(declare-fun GHC.List.replicate () Int)
(declare-fun GHC.List.zipWith () Int)
(declare-fun lit$36$$39$Suc () Str)
(declare-fun GHC.Classes.$62$$61$ () Int)
(declare-fun GHC.Num.fromInteger () Int)
(declare-fun papp3 () Int)
(declare-fun GHC.List.span () Int)
(declare-fun lqdc$35$$35$$36$select$35$$35$GHC.Tuple.$40$$44$$44$$41$$35$$35$1 () Int)
(declare-fun GHC.Classes.$62$ () Int)
(declare-fun GHC.Types.False () Bool)
(declare-fun GHC.List.scanr1 () Int)
(declare-fun lqdc$35$$35$$36$select$35$$35$GHC.Types.$58$$35$$35$1 () Int)
(declare-fun lq_tmp$36$x$35$$35$534 () Natural.Natural)
(declare-fun GHC.Types.$58$ () Int)
(declare-fun GHC.List.scanl () Int)
(declare-fun GHC.Types.krep$36$$42$ () Int)
(declare-fun GHC.Tuple.$40$$44$$44$$41$ () Int)
(declare-fun papp4 () Int)
(declare-fun GHC.Types.Module () Int)
(declare-fun GHC.List.zip () Int)
(declare-fun GHC.Tuple.$40$$41$ () Int)
(declare-fun GHC.Types.I$35$ () Int)
(declare-fun GHC.Types.KindRepFun () Int)
(declare-fun GHC.Types.KindRepTYPE () Int)
(declare-fun GHC.List.dropWhile () Int)
(declare-fun GHC.Real.C$58$Fractional () Int)
(declare-fun autolen () Int)
(declare-fun GHC.Integer.Type.$36$WJn$35$ () Int)
(declare-fun GHC.Real.$94$ () Int)
(declare-fun head () Int)
(declare-fun lq_tmp$36$x$35$$35$631 () Int)
(declare-fun is$36$GHC.Tuple.$40$$44$$44$$41$ () Int)
(declare-fun GHC.Types.$36$WKindRepTYPE () Int)
(declare-fun Natural.mul () Int)
(declare-fun GHC.Integer.Type.Jn$35$ () Int)
(declare-fun GHC.Classes.compare () Int)
(declare-fun is$36$GHC.Types.$58$ () Int)
(declare-fun papp2 () Int)
(declare-fun GHC.Stack.Types.EmptyCallStack () Int)
(declare-fun m$35$$35$a3h9 () Natural.Natural)
(declare-fun GHC.List.reverse () Int)
(declare-fun GHC.Integer.Type.$36$WJp$35$ () Int)
(declare-fun lit$36$main () Str)
(declare-fun GHC.List.filter () Int)
(declare-fun fromJust () Int)
(declare-fun GHC.Types.KindRepTyConApp () Int)
(declare-fun GHC.List.cycle () Int)
(declare-fun GHC.List.$33$$33$ () Int)
(declare-fun GHC.List.tail () Int)
(declare-fun papp7 () Int)
(declare-fun GHC.Classes.$47$$61$ () Int)
(declare-fun GHC.List.break () Int)
(declare-fun GHC.Types.True () Bool)
(declare-fun GHC.Types.$91$$93$ () Int)
(declare-fun GHC.List.splitAt () Int)
(declare-fun GHC.Base.$43$$43$ () Int)
(declare-fun GHC.Real.$58$$37$ () Int)
(declare-fun GHC.Tuple.$40$$44$$41$ () Int)
(declare-fun GHC.Classes.$38$$38$ () Int)
(declare-fun lit$36$Natural () Str)
(declare-fun GHC.Types.GT () Int)
(declare-fun GHC.Classes.C$58$IP () Int)
(declare-fun GHC.Classes.$124$$124$ () Int)
(declare-fun Data.Either.Left () Int)
(declare-fun GHC.List.last () Int)
(declare-fun GHC.Integer.Type.S$35$ () Int)
(declare-fun GHC.List.scanl1 () Int)
(declare-fun Data.Either.Right () Int)
(declare-fun GHC.Num.$45$ () Int)
(declare-fun len () Int)
(declare-fun papp6 () Int)
(declare-fun GHC.Base.. () Int)
(declare-fun x_Tuple22 () Int)
(declare-fun lq_tmp$36$x$35$$35$617 () Int)
(declare-fun ds_d3ii () Natural.Natural)
(declare-fun GHC.Types.KindRepTypeLitS () Int)
(declare-fun GHC.Real.$36$W$58$$37$ () Int)
(declare-fun ds_d3it () Natural.Natural)
(declare-fun isJust () Int)
(declare-fun GHC.List.takeWhile () Int)
(declare-fun GHC.Types.TrNameD () Int)
(declare-fun GHC.Types.KindRepVar () Int)
(declare-fun m$35$$35$a3hb () Natural.Natural)
(declare-fun GHC.Types.KindRepTypeLitD () Int)
(declare-fun x_Tuple31 () Int)
(declare-fun GHC.Integer.Type.Jp$35$ () Int)
(declare-fun ds_d3is () Natural.Natural)
(declare-fun GHC.IO.Exception.IOError () Int)
(declare-fun GHC.List.take () Int)
(declare-fun GHC.Stack.Types.PushCallStack () Int)
(declare-fun GHC.Classes.$60$$61$ () Int)
(declare-fun GHC.Types.TrNameS () Int)
(declare-fun GHC.Enum.C$58$Bounded () Int)
(declare-fun GHC.Base.map () Int)
(declare-fun lqdc$35$$35$$36$select$35$$35$GHC.Tuple.$40$$44$$41$$35$$35$2 () Int)
(declare-fun GHC.Base.$36$ () Int)
(declare-fun lit$36$$39$Zero () Str)
(declare-fun papp1 () Int)
(declare-fun GHC.Classes.max () Int)
(declare-fun lqdc$35$$35$$36$select$35$$35$GHC.Tuple.$40$$44$$44$$41$$35$$35$3 () Int)
(declare-fun GHC.Classes.$60$ () Int)
(declare-fun tail () Int)
(declare-fun GHC.Types.TyCon () Int)
(declare-fun GHC.Stack.Types.FreezeCallStack () Int)
(declare-fun GHC.Num.$42$ () Int)
(declare-fun lq_tmp$36$x$35$$35$488 () Natural.Natural)
(declare-fun GHC.Maybe.Nothing () Int)
(declare-fun GHC.Types.EQ () Int)
(declare-fun GHC.List.scanr () Int)
(declare-fun GHC.Num.negate () Int)
(declare-fun GHC.Real.fromIntegral () Int)
(declare-fun GHC.Maybe.Just () Int)
(declare-fun GHC.Classes.min () Int)
(declare-fun Natural.add () Int)
(declare-fun GHC.List.head () Int)
(declare-fun lqdc$35$$35$$36$select$35$$35$GHC.Tuple.$40$$44$$41$$35$$35$1 () Int)
(declare-fun GHC.Types.$36$WKindRepVar () Int)
(declare-fun x_Tuple32 () Int)
(declare-fun GHC.List.repeat () Int)
(declare-fun lqdc$35$$35$$36$select$35$$35$GHC.Types.$58$$35$$35$2 () Int)
(declare-fun GHC.Classes.not () Int)
(declare-fun GHC.Num.$43$ () Int)
(declare-fun Data.Tuple.fst () Int)
(declare-fun GHC.Types.KindRepApp () Int)
(declare-fun GHC.Real.C$58$Integral () Int)
(declare-fun GHC.Err.error () Int)
(declare-fun snd () Int)
(declare-fun fst () Int)
(declare-fun lqdc$35$$35$$36$select$35$$35$GHC.Tuple.$40$$44$$44$$41$$35$$35$2 () Int)
(declare-fun Data.Tuple.snd () Int)
(declare-fun apply$35$$35$23 (Int Natural.Natural) (_ BitVec 32))
(declare-fun apply$35$$35$16 (Int (_ BitVec 32)) Bool)
(declare-fun apply$35$$35$9 (Int Bool) Natural.Natural)
(declare-fun apply$35$$35$4 (Int Int) Natural.Natural)
(declare-fun apply$35$$35$11 (Int Str) Bool)
(declare-fun apply$35$$35$20 (Int Natural.Natural) Int)
(declare-fun apply$35$$35$7 (Int Bool) Str)
(declare-fun apply$35$$35$13 (Int Str) (_ BitVec 32))
(declare-fun apply$35$$35$18 (Int (_ BitVec 32)) (_ BitVec 32))
(declare-fun apply$35$$35$24 (Int Natural.Natural) Natural.Natural)
(declare-fun apply$35$$35$0 (Int Int) Int)
(declare-fun apply$35$$35$21 (Int Natural.Natural) Bool)
(declare-fun apply$35$$35$10 (Int Str) Int)
(declare-fun apply$35$$35$1 (Int Int) Bool)
(declare-fun apply$35$$35$19 (Int (_ BitVec 32)) Natural.Natural)
(declare-fun apply$35$$35$8 (Int Bool) (_ BitVec 32))
(declare-fun apply$35$$35$17 (Int (_ BitVec 32)) Str)
(declare-fun apply$35$$35$14 (Int Str) Natural.Natural)
(declare-fun apply$35$$35$12 (Int Str) Str)
(declare-fun apply$35$$35$6 (Int Bool) Bool)
(declare-fun apply$35$$35$2 (Int Int) Str)
(declare-fun apply$35$$35$15 (Int (_ BitVec 32)) Int)
(declare-fun apply$35$$35$3 (Int Int) (_ BitVec 32))
(declare-fun apply$35$$35$5 (Int Bool) Int)
(declare-fun apply$35$$35$22 (Int Natural.Natural) Str)
(declare-fun coerce$35$$35$23 (Natural.Natural) (_ BitVec 32))
(declare-fun coerce$35$$35$16 ((_ BitVec 32)) Bool)
(declare-fun coerce$35$$35$9 (Bool) Natural.Natural)
(declare-fun coerce$35$$35$4 (Int) Natural.Natural)
(declare-fun coerce$35$$35$11 (Str) Bool)
(declare-fun coerce$35$$35$20 (Natural.Natural) Int)
(declare-fun coerce$35$$35$7 (Bool) Str)
(declare-fun coerce$35$$35$13 (Str) (_ BitVec 32))
(declare-fun coerce$35$$35$18 ((_ BitVec 32)) (_ BitVec 32))
(declare-fun coerce$35$$35$24 (Natural.Natural) Natural.Natural)
(declare-fun coerce$35$$35$0 (Int) Int)
(declare-fun coerce$35$$35$21 (Natural.Natural) Bool)
(declare-fun coerce$35$$35$10 (Str) Int)
(declare-fun coerce$35$$35$1 (Int) Bool)
(declare-fun coerce$35$$35$19 ((_ BitVec 32)) Natural.Natural)
(declare-fun coerce$35$$35$8 (Bool) (_ BitVec 32))
(declare-fun coerce$35$$35$17 ((_ BitVec 32)) Str)
(declare-fun coerce$35$$35$14 (Str) Natural.Natural)
(declare-fun coerce$35$$35$12 (Str) Str)
(declare-fun coerce$35$$35$6 (Bool) Bool)
(declare-fun coerce$35$$35$2 (Int) Str)
(declare-fun coerce$35$$35$15 ((_ BitVec 32)) Int)
(declare-fun coerce$35$$35$3 (Int) (_ BitVec 32))
(declare-fun coerce$35$$35$5 (Bool) Int)
(declare-fun coerce$35$$35$22 (Natural.Natural) Str)
(declare-fun smt_lambda$35$$35$23 (Natural.Natural (_ BitVec 32)) Int)
(declare-fun smt_lambda$35$$35$16 ((_ BitVec 32) Bool) Int)
(declare-fun smt_lambda$35$$35$9 (Bool Natural.Natural) Int)
(declare-fun smt_lambda$35$$35$4 (Int Natural.Natural) Int)
(declare-fun smt_lambda$35$$35$11 (Str Bool) Int)
(declare-fun smt_lambda$35$$35$20 (Natural.Natural Int) Int)
(declare-fun smt_lambda$35$$35$7 (Bool Str) Int)
(declare-fun smt_lambda$35$$35$13 (Str (_ BitVec 32)) Int)
(declare-fun smt_lambda$35$$35$18 ((_ BitVec 32) (_ BitVec 32)) Int)
(declare-fun smt_lambda$35$$35$24 (Natural.Natural Natural.Natural) Int)
(declare-fun smt_lambda$35$$35$0 (Int Int) Int)
(declare-fun smt_lambda$35$$35$21 (Natural.Natural Bool) Int)
(declare-fun smt_lambda$35$$35$10 (Str Int) Int)
(declare-fun smt_lambda$35$$35$1 (Int Bool) Int)
(declare-fun smt_lambda$35$$35$19 ((_ BitVec 32) Natural.Natural) Int)
(declare-fun smt_lambda$35$$35$8 (Bool (_ BitVec 32)) Int)
(declare-fun smt_lambda$35$$35$17 ((_ BitVec 32) Str) Int)
(declare-fun smt_lambda$35$$35$14 (Str Natural.Natural) Int)
(declare-fun smt_lambda$35$$35$12 (Str Str) Int)
(declare-fun smt_lambda$35$$35$6 (Bool Bool) Int)
(declare-fun smt_lambda$35$$35$2 (Int Str) Int)
(declare-fun smt_lambda$35$$35$15 ((_ BitVec 32) Int) Int)
(declare-fun smt_lambda$35$$35$3 (Int (_ BitVec 32)) Int)
(declare-fun smt_lambda$35$$35$5 (Bool Int) Int)
(declare-fun smt_lambda$35$$35$22 (Natural.Natural Str) Int)
(declare-fun lam_arg$35$$35$1$35$$35$20 () Natural.Natural)
(declare-fun lam_arg$35$$35$2$35$$35$20 () Natural.Natural)
(declare-fun lam_arg$35$$35$3$35$$35$20 () Natural.Natural)
(declare-fun lam_arg$35$$35$4$35$$35$20 () Natural.Natural)
(declare-fun lam_arg$35$$35$5$35$$35$20 () Natural.Natural)
(declare-fun lam_arg$35$$35$6$35$$35$20 () Natural.Natural)
(declare-fun lam_arg$35$$35$7$35$$35$20 () Natural.Natural)
(declare-fun lam_arg$35$$35$1$35$$35$0 () Int)
(declare-fun lam_arg$35$$35$2$35$$35$0 () Int)
(declare-fun lam_arg$35$$35$3$35$$35$0 () Int)
(declare-fun lam_arg$35$$35$4$35$$35$0 () Int)
(declare-fun lam_arg$35$$35$5$35$$35$0 () Int)
(declare-fun lam_arg$35$$35$6$35$$35$0 () Int)
(declare-fun lam_arg$35$$35$7$35$$35$0 () Int)
(declare-fun lam_arg$35$$35$1$35$$35$10 () Str)
(declare-fun lam_arg$35$$35$2$35$$35$10 () Str)
(declare-fun lam_arg$35$$35$3$35$$35$10 () Str)
(declare-fun lam_arg$35$$35$4$35$$35$10 () Str)
(declare-fun lam_arg$35$$35$5$35$$35$10 () Str)
(declare-fun lam_arg$35$$35$6$35$$35$10 () Str)
(declare-fun lam_arg$35$$35$7$35$$35$10 () Str)
(declare-fun lam_arg$35$$35$1$35$$35$15 () (_ BitVec 32))
(declare-fun lam_arg$35$$35$2$35$$35$15 () (_ BitVec 32))
(declare-fun lam_arg$35$$35$3$35$$35$15 () (_ BitVec 32))
(declare-fun lam_arg$35$$35$4$35$$35$15 () (_ BitVec 32))
(declare-fun lam_arg$35$$35$5$35$$35$15 () (_ BitVec 32))
(declare-fun lam_arg$35$$35$6$35$$35$15 () (_ BitVec 32))
(declare-fun lam_arg$35$$35$7$35$$35$15 () (_ BitVec 32))
(declare-fun lam_arg$35$$35$1$35$$35$5 () Bool)
(declare-fun lam_arg$35$$35$2$35$$35$5 () Bool)
(declare-fun lam_arg$35$$35$3$35$$35$5 () Bool)
(declare-fun lam_arg$35$$35$4$35$$35$5 () Bool)
(declare-fun lam_arg$35$$35$5$35$$35$5 () Bool)
(declare-fun lam_arg$35$$35$6$35$$35$5 () Bool)
(declare-fun lam_arg$35$$35$7$35$$35$5 () Bool)


(assert (distinct lit$36$$39$Zero lit$36$Natural lit$36$main lit$36$$39$Suc))

(assert (distinct GHC.Types.True GHC.Types.False))
(assert (distinct GHC.Types.EQ GHC.Types.GT GHC.Types.LT))
(assert (= (strLen lit$36$$39$Suc) 4))
(assert (= (strLen lit$36$main) 4))
(assert (= (strLen lit$36$Natural) 7))
(assert (= (strLen lit$36$$39$Zero) 5))
(push 1)
