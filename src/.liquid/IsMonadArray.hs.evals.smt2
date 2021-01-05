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
(declare-datatypes ((VNat.VNat 0)) ((par () (VNat.Zero (VNat.Suc (lqdc$35$$35$$36$select$35$$35$VNat.Suc$35$$35$1 VNat.VNat))))))
(declare-datatypes ((VList.VList 1)) ((par (T0) (VList.Nil (VList.Cons (VList.hd T0) (VList.tl (VList.VList T0)))))))
(declare-datatypes ((Liquid.ProofCombinators.QED 0)) ((par () (Liquid.ProofCombinators.QED Liquid.ProofCombinators.Admit))))
(declare-datatypes ((IsSemigroup.IsSemigroup 1)) ((par (T0) ((junk$35$$35$IsSemigroup.IsSemigroup (junk$35$$35$IsSemigroup.IsSemigroup$35$$35$0 T0)) (IsSemigroup.IsSemigroup (IsSemigroup.op Int) (IsSemigroup.op_associative Int))))))
(declare-datatypes ((IsFunctor.IsFunctor 1)) ((par (T0) ((junk$35$$35$IsFunctor.IsFunctor (junk$35$$35$IsFunctor.IsFunctor$35$$35$0 T0)) (IsFunctor.IsFunctor (IsFunctor.vmap Int) (IsFunctor.vmap_vid Int))))))
(declare-datatypes ((IsMonad.IsMonad 1)) ((par (T0) ((junk$35$$35$IsMonad.IsMonad (junk$35$$35$IsMonad.IsMonad$35$$35$0 T0)) (IsMonad.IsMonad (IsMonad.isFunctor (IsFunctor.IsFunctor T0)) (IsMonad.vlift Int) (IsMonad.vbind Int) (IsMonad.vbind_correct Int) (IsMonad.vbind_identity Int) (IsMonad.vbind_vlift Int) (IsMonad.vbind_vbind Int))))))
(declare-datatypes ((IsMonadArray.IsMonadArray 2)) ((par (T0 T1) ((junk$35$$35$IsMonadArray.IsMonadArray (junk$35$$35$IsMonadArray.IsMonadArray$35$$35$0 T0) (junk$35$$35$IsMonadArray.IsMonadArray$35$$35$1 T1)) (IsMonadArray.IsMonadArray (IsMonadArray.isMonad (IsMonad.IsMonad T0)) (IsMonadArray.vread Int) (IsMonadArray.vwrite Int) (IsMonadArray.vread_vwrite Int) (IsMonadArray.vwrite_vread Int) (IsMonadArray.vwrite_vwrite Int) (IsMonadArray.vread_vread Int) (IsMonadArray.vread_commutative Int) (IsMonadArray.vwrite_commutative Int) (IsMonadArray.vread_vwrite_commutative Int))))))
(declare-fun GHC.Base.id () Int)
(declare-fun cast_as_int () Int)
(declare-fun VList.vreverse () Int)
(declare-fun GHC.Real.rem () Int)
(declare-fun GHC.List.init () Int)
(declare-fun addrLen () Int)
(declare-fun papp5 () Int)
(declare-fun GHC.List.iterate () Int)
(declare-fun x_Tuple21 () Int)
(declare-fun Liquid.ProofCombinators.axiomExt () Int)
(declare-fun VBool.vbranch () Int)
(declare-fun GHC.Classes.$61$$61$ () Int)
(declare-fun GHC.Types.C$35$ () Int)
(declare-fun GHC.List.drop () Int)
(declare-fun is$36$GHC.Types.$91$$93$ () Int)
(declare-fun Data.Foldable.length () Int)
(declare-fun x_Tuple33 () Int)
(declare-fun Function.vconst () Int)
(declare-fun is$36$GHC.Tuple.$40$$44$$41$ () Int)
(declare-fun GHC.Types.LT () Int)
(declare-fun GHC.List.replicate () Int)
(declare-fun GHC.List.zipWith () Int)
(declare-fun VNat.mul () Int)
(declare-fun GHC.Classes.$62$$61$ () Int)
(declare-fun Function.vid () Int)
(declare-fun GHC.Num.fromInteger () Int)
(declare-fun papp3 () Int)
(declare-fun VNat.add () Int)
(declare-fun GHC.Generics.SSym () Int)
(declare-fun GHC.List.span () Int)
(declare-fun lqdc$35$$35$$36$select$35$$35$GHC.Tuple.$40$$44$$44$$41$$35$$35$1 () Int)
(declare-fun GHC.Generics.$36$WSNoSourceStrictness () Int)
(declare-fun GHC.Classes.$62$ () Int)
(declare-fun GHC.Generics.SSourceUnpack () Int)
(declare-fun IsMonadArray.vreadList () Int)
(declare-fun IsMonadArray.vwriteListToLength () Int)
(declare-fun VNat.add_m_Sn () Int)
(declare-fun GHC.Types.False () Bool)
(declare-fun GHC.List.scanr1 () Int)
(declare-fun GHC.Generics.$36$WSNoSourceUnpackedness () Int)
(declare-fun lqdc$35$$35$$36$select$35$$35$GHC.Types.$58$$35$$35$1 () Int)
(declare-fun GHC.Generics.$36$WUDouble () Int)
(declare-fun IsMonadArray.vwriteList () Int)
(declare-fun GHC.Types.$58$ () Int)
(declare-fun GHC.Real.div () Int)
(declare-fun GHC.List.scanl () Int)
(declare-fun GHC.Generics.SJust () Int)
(declare-fun GHC.Generics.$36$WSRightAssociative () Int)
(declare-fun GHC.Tuple.$40$$44$$44$$41$ () Int)
(declare-fun papp4 () Int)
(declare-fun GHC.Types.Module () Int)
(declare-fun VNat.mul_annihilator () Int)
(declare-fun GHC.Generics.$36$WSSourceLazy () Int)
(declare-fun VNat.$36$tcVNat () Int)
(declare-fun GHC.List.zip () Int)
(declare-fun GHC.Generics.SInfix () Int)
(declare-fun IsMonad.vseq_identity () Int)
(declare-fun GHC.Tuple.$40$$41$ () Int)
(declare-fun GHC.Generics.SPrefix () Int)
(declare-fun GHC.Types.I$35$ () Int)
(declare-fun GHC.Generics.UWord () Int)
(declare-fun Liquid.ProofCombinators.$42$$42$$42$ () Int)
(declare-fun GHC.Generics.SDecidedLazy () Int)
(declare-fun GHC.Types.KindRepFun () Int)
(declare-fun IsMonad.$36$tcIsMonad () Int)
(declare-fun GHC.Generics.$36$WSNotAssociative () Int)
(declare-fun GHC.Generics.$36$WSSourceNoUnpack () Int)
(declare-fun GHC.Generics.UInt () Int)
(declare-fun GHC.Types.KindRepTYPE () Int)
(declare-fun GHC.List.dropWhile () Int)
(declare-fun IsMonad.vliftF2 () Int)
(declare-fun IsMonadArray.vwriteList2ToLength () Int)
(declare-fun GHC.Real.C$58$Fractional () Int)
(declare-fun autolen () Int)
(declare-fun IsMonad.kleisli () Int)
(declare-fun GHC.Integer.Type.$36$WJn$35$ () Int)
(declare-fun GHC.Real.$94$ () Int)
(declare-fun head () Int)
(declare-fun GHC.Real.mod () Int)
(declare-fun GHC.Generics.UAddr () Int)
(declare-fun GHC.Generics.SNothing () Int)
(declare-fun VNat.mul_distributive () Int)
(declare-fun is$36$GHC.Tuple.$40$$44$$44$$41$ () Int)
(declare-fun GHC.Generics.SNotAssociative () Int)
(declare-fun GHC.Generics.SSourceNoUnpack () Int)
(declare-fun GHC.Types.$36$WKindRepTYPE () Int)
(declare-fun VList.vsingleton () Int)
(declare-fun GHC.Real.divMod () Int)
(declare-fun GHC.Integer.Type.Jn$35$ () Int)
(declare-fun GHC.Generics.$36$WUAddr () Int)
(declare-fun VList.vappend_identity () Int)
(declare-fun GHC.Generics.UFloat () Int)
(declare-fun GHC.Classes.compare () Int)
(declare-fun Liquid.ProofCombinators.$61$$60$$61$ () Int)
(declare-fun GHC.Generics.$36$WSDecidedStrict () Int)
(declare-fun IsMonad.raw_kleisli () Int)
(declare-fun is$36$GHC.Types.$58$ () Int)
(declare-fun papp2 () Int)
(declare-fun GHC.Real.toInteger () Int)
(declare-fun GHC.Real.quotRem () Int)
(declare-fun GHC.Generics.$36$WSFalse () Int)
(declare-fun GHC.Stack.Types.EmptyCallStack () Int)
(declare-fun GHC.Types.krep$36$$42$Arr$42$ () Int)
(declare-fun Liquid.ProofCombinators.$61$$61$$33$ () Int)
(declare-fun GHC.List.reverse () Int)
(declare-fun GHC.Integer.Type.$36$WJp$35$ () Int)
(declare-fun GHC.List.filter () Int)
(declare-fun GHC.Generics.$36$WSInfix () Int)
(declare-fun fromJust () Int)
(declare-fun GHC.Tuple.$36$tc$40$$41$ () Int)
(declare-fun VUnit.vunit () Int)
(declare-fun GHC.Types.KindRepTyConApp () Int)
(declare-fun GHC.List.cycle () Int)
(declare-fun GHC.List.$33$$33$ () Int)
(declare-fun GHC.List.tail () Int)
(declare-fun VNat.add_associative () Int)
(declare-fun GHC.Generics.$36$WSDecidedLazy () Int)
(declare-fun papp7 () Int)
(declare-fun Liquid.ProofCombinators.impossible () Int)
(declare-fun GHC.Classes.$47$$61$ () Int)
(declare-fun GHC.Generics.SNoSourceStrictness () Int)
(declare-fun GHC.List.break () Int)
(declare-fun GHC.Types.True () Bool)
(declare-fun IsMonad.vseq_identity_left () Int)
(declare-fun GHC.Generics.$36$WSSourceUnpack () Int)
(declare-fun GHC.Types.$91$$93$ () Int)
(declare-fun GHC.List.splitAt () Int)
(declare-fun Liquid.ProofCombinators.withProof () Int)
(declare-fun GHC.Base.$43$$43$ () Int)
(declare-fun GHC.Real.$58$$37$ () Int)
(declare-fun VTuple.vtuple3D () Int)
(declare-fun GHC.Generics.SNoSourceUnpackedness () Int)
(declare-fun GHC.Generics.SDecidedUnpack () Int)
(declare-fun GHC.Tuple.$40$$44$$41$ () Int)
(declare-fun IsMonadArray.vwriteList3ToLength () Int)
(declare-fun IsMonad.vseq_epsilon () Int)
(declare-fun GHC.Real.quot () Int)
(declare-fun GHC.Real.$47$ () Int)
(declare-fun GHC.Classes.$38$$38$ () Int)
(declare-fun GHC.Types.GT () Int)
(declare-fun GHC.Classes.C$58$IP () Int)
(declare-fun GHC.Classes.$124$$124$ () Int)
(declare-fun Data.Either.Left () Int)
(declare-fun GHC.List.last () Int)
(declare-fun IsMonad.vseq () Int)
(declare-fun GHC.Integer.Type.S$35$ () Int)
(declare-fun GHC.List.scanl1 () Int)
(declare-fun Data.Either.Right () Int)
(declare-fun GHC.Num.$45$ () Int)
(declare-fun len () Int)
(declare-fun papp6 () Int)
(declare-fun GHC.Base.. () Int)
(declare-fun x_Tuple22 () Int)
(declare-fun VNat.add_commutative () Int)
(declare-fun IsMonad.vseq_identity_right () Int)
(declare-fun VList.vappend () Int)
(declare-fun IsMonad.vliftF () Int)
(declare-fun Liquid.ProofCombinators.$61$$61$$61$ () Int)
(declare-fun GHC.Types.KindRepTypeLitS () Int)
(declare-fun GHC.Real.$36$W$58$$37$ () Int)
(declare-fun VNat.mul_commutative () Int)
(declare-fun VList.isSemigroup_vappend () (IsSemigroup.IsSemigroup (VList.VList Int)))
(declare-fun GHC.Real.fromRational () Int)
(declare-fun isJust () Int)
(declare-fun GHC.List.takeWhile () Int)
(declare-fun GHC.Types.TrNameD () Int)
(declare-fun Function.$38$ () Int)
(declare-fun GHC.Generics.$36$WSDecidedUnpack () Int)
(declare-fun GHC.Types.KindRepVar () Int)
(declare-fun GHC.Types.KindRepTypeLitD () Int)
(declare-fun VList.vreverse_preserves_vlength () Int)
(declare-fun x_Tuple31 () Int)
(declare-fun GHC.Integer.Type.Jp$35$ () Int)
(declare-fun GHC.IO.Exception.IOError () Int)
(declare-fun GHC.List.take () Int)
(declare-fun GHC.Stack.Types.PushCallStack () Int)
(declare-fun prop () Int)
(declare-fun GHC.Classes.$60$$61$ () Int)
(declare-fun GHC.Types.TrNameS () Int)
(declare-fun GHC.Enum.C$58$Bounded () Int)
(declare-fun VBool.vnot () Int)
(declare-fun GHC.Base.map () Int)
(declare-fun GHC.Generics.SLeftAssociative () Int)
(declare-fun lqdc$35$$35$$36$select$35$$35$GHC.Tuple.$40$$44$$41$$35$$35$2 () Int)
(declare-fun VList.vall () Int)
(declare-fun GHC.Base.$36$ () Int)
(declare-fun papp1 () Int)
(declare-fun VTuple.vtuple2D () Int)
(declare-fun GHC.Generics.$36$WUChar () Int)
(declare-fun GHC.Classes.max () Int)
(declare-fun GHC.Generics.$36$WSSourceStrict () Int)
(declare-fun lqdc$35$$35$$36$select$35$$35$GHC.Tuple.$40$$44$$44$$41$$35$$35$3 () Int)
(declare-fun GHC.Classes.$60$ () Int)
(declare-fun tail () Int)
(declare-fun GHC.Generics.SDecidedStrict () Int)
(declare-fun Liquid.ProofCombinators.$63$ () Int)
(declare-fun VList.vlength () Int)
(declare-fun Liquid.ProofCombinators.isAdmit () Int)
(declare-fun GHC.Types.TyCon () Int)
(declare-fun GHC.Stack.Types.FreezeCallStack () Int)
(declare-fun GHC.Generics.$36$WSTrue () Int)
(declare-fun GHC.Generics.$36$WUFloat () Int)
(declare-fun GHC.Generics.SFalse () Int)
(declare-fun VList.vappend_sums_vlength () Int)
(declare-fun GHC.Num.$42$ () Int)
(declare-fun GHC.Generics.STrue () Int)
(declare-fun GHC.Real.recip () Int)
(declare-fun VBool.vand () Int)
(declare-fun VNat.add_identity () Int)
(declare-fun GHC.Generics.SSourceStrict () Int)
(declare-fun GHC.Generics.$36$WUInt () Int)
(declare-fun Function.vdiagonalize () Int)
(declare-fun GHC.Generics.UChar () Int)
(declare-fun GHC.Maybe.Nothing () Int)
(declare-fun Function.vcomp () Int)
(declare-fun GHC.Generics.$36$WSNothing () Int)
(declare-fun GHC.Types.EQ () Int)
(declare-fun GHC.List.scanr () Int)
(declare-fun GHC.Generics.$36$WUWord () Int)
(declare-fun GHC.Generics.SSourceLazy () Int)
(declare-fun GHC.Num.negate () Int)
(declare-fun VNat.mul_identity () Int)
(declare-fun GHC.Generics.$36$WSJust () Int)
(declare-fun GHC.Generics.SRightAssociative () Int)
(declare-fun GHC.Generics.$36$WSPrefix () Int)
(declare-fun GHC.Real.fromIntegral () Int)
(declare-fun GHC.Maybe.Just () Int)
(declare-fun GHC.Classes.min () Int)
(declare-fun GHC.Generics.UDouble () Int)
(declare-fun GHC.Generics.$36$WSLeftAssociative () Int)
(declare-fun GHC.List.head () Int)
(declare-fun lqdc$35$$35$$36$select$35$$35$GHC.Tuple.$40$$44$$41$$35$$35$1 () Int)
(declare-fun GHC.Types.$36$WKindRepVar () Int)
(declare-fun VList.vappend_associative () Int)
(declare-fun x_Tuple32 () Int)
(declare-fun GHC.List.repeat () Int)
(declare-fun lqdc$35$$35$$36$select$35$$35$GHC.Types.$58$$35$$35$2 () Int)
(declare-fun Liquid.ProofCombinators.$61$$62$$61$ () Int)
(declare-fun Function.vflip () Int)
(declare-fun GHC.Classes.not () Int)
(declare-fun GHC.Num.$43$ () Int)
(declare-fun Data.Tuple.fst () Int)
(declare-fun GHC.Types.KindRepApp () Int)
(declare-fun GHC.Generics.$36$WSSym () Int)
(declare-fun GHC.Real.C$58$Integral () Int)
(declare-fun GHC.Err.error () Int)
(declare-fun Function.vconstF () Int)
(declare-fun snd () Int)
(declare-fun fst () Int)
(declare-fun lqdc$35$$35$$36$select$35$$35$GHC.Tuple.$40$$44$$44$$41$$35$$35$2 () Int)
(declare-fun Data.Tuple.snd () Int)
(declare-fun apply$35$$35$55 (Int Liquid.ProofCombinators.QED) Bool)
(declare-fun apply$35$$35$45 (Int (IsMonadArray.IsMonadArray Int Int)) Int)
(declare-fun apply$35$$35$35 (Int (_ BitVec 32)) VNat.VNat)
(declare-fun apply$35$$35$5 (Int Int) (IsMonadArray.IsMonadArray Int Int))
(declare-fun apply$35$$35$28 (Int (_ BitVec 32)) Bool)
(declare-fun apply$35$$35$33 (Int (_ BitVec 32)) Liquid.ProofCombinators.QED)
(declare-fun apply$35$$35$48 (Int (IsMonadArray.IsMonadArray Int Int)) (_ BitVec 32))
(declare-fun apply$35$$35$24 (Int Str) Liquid.ProofCombinators.QED)
(declare-fun apply$35$$35$19 (Int Str) Bool)
(declare-fun apply$35$$35$22 (Int Str) (IsMonad.IsMonad Int))
(declare-fun apply$35$$35$25 (Int Str) (VList.VList Int))
(declare-fun apply$35$$35$11 (Int Bool) Str)
(declare-fun apply$35$$35$14 (Int Bool) (IsMonadArray.IsMonadArray Int Int))
(declare-fun apply$35$$35$46 (Int (IsMonadArray.IsMonadArray Int Int)) Bool)
(declare-fun apply$35$$35$26 (Int Str) VNat.VNat)
(declare-fun apply$35$$35$7 (Int Int) (VList.VList Int))
(declare-fun apply$35$$35$21 (Int Str) (_ BitVec 32))
(declare-fun apply$35$$35$54 (Int Liquid.ProofCombinators.QED) Int)
(declare-fun apply$35$$35$4 (Int Int) (IsMonad.IsMonad Int))
(declare-fun apply$35$$35$61 (Int Liquid.ProofCombinators.QED) (VList.VList Int))
(declare-fun apply$35$$35$58 (Int Liquid.ProofCombinators.QED) (IsMonad.IsMonad Int))
(declare-fun apply$35$$35$30 (Int (_ BitVec 32)) (_ BitVec 32))
(declare-fun apply$35$$35$50 (Int (IsMonadArray.IsMonadArray Int Int)) (IsMonadArray.IsMonadArray Int Int))
(declare-fun apply$35$$35$80 (Int VNat.VNat) VNat.VNat)
(declare-fun apply$35$$35$60 (Int Liquid.ProofCombinators.QED) Liquid.ProofCombinators.QED)
(declare-fun apply$35$$35$0 (Int Int) Int)
(declare-fun apply$35$$35$62 (Int Liquid.ProofCombinators.QED) VNat.VNat)
(declare-fun apply$35$$35$57 (Int Liquid.ProofCombinators.QED) (_ BitVec 32))
(declare-fun apply$35$$35$18 (Int Str) Int)
(declare-fun apply$35$$35$78 (Int VNat.VNat) Liquid.ProofCombinators.QED)
(declare-fun apply$35$$35$56 (Int Liquid.ProofCombinators.QED) Str)
(declare-fun apply$35$$35$49 (Int (IsMonadArray.IsMonadArray Int Int)) (IsMonad.IsMonad Int))
(declare-fun apply$35$$35$74 (Int VNat.VNat) Str)
(declare-fun apply$35$$35$41 (Int (IsMonad.IsMonad Int)) (IsMonadArray.IsMonadArray Int Int))
(declare-fun apply$35$$35$52 (Int (IsMonadArray.IsMonadArray Int Int)) (VList.VList Int))
(declare-fun apply$35$$35$1 (Int Int) Bool)
(declare-fun apply$35$$35$68 (Int (VList.VList Int)) (IsMonadArray.IsMonadArray Int Int))
(declare-fun apply$35$$35$64 (Int (VList.VList Int)) Bool)
(declare-fun apply$35$$35$16 (Int Bool) (VList.VList Int))
(declare-fun apply$35$$35$75 (Int VNat.VNat) (_ BitVec 32))
(declare-fun apply$35$$35$13 (Int Bool) (IsMonad.IsMonad Int))
(declare-fun apply$35$$35$37 (Int (IsMonad.IsMonad Int)) Bool)
(declare-fun apply$35$$35$15 (Int Bool) Liquid.ProofCombinators.QED)
(declare-fun apply$35$$35$12 (Int Bool) (_ BitVec 32))
(declare-fun apply$35$$35$31 (Int (_ BitVec 32)) (IsMonad.IsMonad Int))
(declare-fun apply$35$$35$47 (Int (IsMonadArray.IsMonadArray Int Int)) Str)
(declare-fun apply$35$$35$34 (Int (_ BitVec 32)) (VList.VList Int))
(declare-fun apply$35$$35$17 (Int Bool) VNat.VNat)
(declare-fun apply$35$$35$23 (Int Str) (IsMonadArray.IsMonadArray Int Int))
(declare-fun apply$35$$35$8 (Int Int) VNat.VNat)
(declare-fun apply$35$$35$32 (Int (_ BitVec 32)) (IsMonadArray.IsMonadArray Int Int))
(declare-fun apply$35$$35$72 (Int VNat.VNat) Int)
(declare-fun apply$35$$35$36 (Int (IsMonad.IsMonad Int)) Int)
(declare-fun apply$35$$35$6 (Int Int) Liquid.ProofCombinators.QED)
(declare-fun apply$35$$35$63 (Int (VList.VList Int)) Int)
(declare-fun apply$35$$35$29 (Int (_ BitVec 32)) Str)
(declare-fun apply$35$$35$20 (Int Str) Str)
(declare-fun apply$35$$35$43 (Int (IsMonad.IsMonad Int)) (VList.VList Int))
(declare-fun apply$35$$35$69 (Int (VList.VList Int)) Liquid.ProofCombinators.QED)
(declare-fun apply$35$$35$42 (Int (IsMonad.IsMonad Int)) Liquid.ProofCombinators.QED)
(declare-fun apply$35$$35$67 (Int (VList.VList Int)) (IsMonad.IsMonad Int))
(declare-fun apply$35$$35$40 (Int (IsMonad.IsMonad Int)) (IsMonad.IsMonad Int))
(declare-fun apply$35$$35$10 (Int Bool) Bool)
(declare-fun apply$35$$35$70 (Int (VList.VList Int)) (VList.VList Int))
(declare-fun apply$35$$35$66 (Int (VList.VList Int)) (_ BitVec 32))
(declare-fun apply$35$$35$76 (Int VNat.VNat) (IsMonad.IsMonad Int))
(declare-fun apply$35$$35$73 (Int VNat.VNat) Bool)
(declare-fun apply$35$$35$71 (Int (VList.VList Int)) VNat.VNat)
(declare-fun apply$35$$35$39 (Int (IsMonad.IsMonad Int)) (_ BitVec 32))
(declare-fun apply$35$$35$44 (Int (IsMonad.IsMonad Int)) VNat.VNat)
(declare-fun apply$35$$35$2 (Int Int) Str)
(declare-fun apply$35$$35$79 (Int VNat.VNat) (VList.VList Int))
(declare-fun apply$35$$35$65 (Int (VList.VList Int)) Str)
(declare-fun apply$35$$35$77 (Int VNat.VNat) (IsMonadArray.IsMonadArray Int Int))
(declare-fun apply$35$$35$27 (Int (_ BitVec 32)) Int)
(declare-fun apply$35$$35$3 (Int Int) (_ BitVec 32))
(declare-fun apply$35$$35$53 (Int (IsMonadArray.IsMonadArray Int Int)) VNat.VNat)
(declare-fun apply$35$$35$38 (Int (IsMonad.IsMonad Int)) Str)
(declare-fun apply$35$$35$9 (Int Bool) Int)
(declare-fun apply$35$$35$59 (Int Liquid.ProofCombinators.QED) (IsMonadArray.IsMonadArray Int Int))
(declare-fun apply$35$$35$51 (Int (IsMonadArray.IsMonadArray Int Int)) Liquid.ProofCombinators.QED)
(declare-fun coerce$35$$35$55 (Liquid.ProofCombinators.QED) Bool)
(declare-fun coerce$35$$35$45 ((IsMonadArray.IsMonadArray Int Int)) Int)
(declare-fun coerce$35$$35$35 ((_ BitVec 32)) VNat.VNat)
(declare-fun coerce$35$$35$5 (Int) (IsMonadArray.IsMonadArray Int Int))
(declare-fun coerce$35$$35$28 ((_ BitVec 32)) Bool)
(declare-fun coerce$35$$35$33 ((_ BitVec 32)) Liquid.ProofCombinators.QED)
(declare-fun coerce$35$$35$48 ((IsMonadArray.IsMonadArray Int Int)) (_ BitVec 32))
(declare-fun coerce$35$$35$24 (Str) Liquid.ProofCombinators.QED)
(declare-fun coerce$35$$35$19 (Str) Bool)
(declare-fun coerce$35$$35$22 (Str) (IsMonad.IsMonad Int))
(declare-fun coerce$35$$35$25 (Str) (VList.VList Int))
(declare-fun coerce$35$$35$11 (Bool) Str)
(declare-fun coerce$35$$35$14 (Bool) (IsMonadArray.IsMonadArray Int Int))
(declare-fun coerce$35$$35$46 ((IsMonadArray.IsMonadArray Int Int)) Bool)
(declare-fun coerce$35$$35$26 (Str) VNat.VNat)
(declare-fun coerce$35$$35$7 (Int) (VList.VList Int))
(declare-fun coerce$35$$35$21 (Str) (_ BitVec 32))
(declare-fun coerce$35$$35$54 (Liquid.ProofCombinators.QED) Int)
(declare-fun coerce$35$$35$4 (Int) (IsMonad.IsMonad Int))
(declare-fun coerce$35$$35$61 (Liquid.ProofCombinators.QED) (VList.VList Int))
(declare-fun coerce$35$$35$58 (Liquid.ProofCombinators.QED) (IsMonad.IsMonad Int))
(declare-fun coerce$35$$35$30 ((_ BitVec 32)) (_ BitVec 32))
(declare-fun coerce$35$$35$50 ((IsMonadArray.IsMonadArray Int Int)) (IsMonadArray.IsMonadArray Int Int))
(declare-fun coerce$35$$35$80 (VNat.VNat) VNat.VNat)
(declare-fun coerce$35$$35$60 (Liquid.ProofCombinators.QED) Liquid.ProofCombinators.QED)
(declare-fun coerce$35$$35$0 (Int) Int)
(declare-fun coerce$35$$35$62 (Liquid.ProofCombinators.QED) VNat.VNat)
(declare-fun coerce$35$$35$57 (Liquid.ProofCombinators.QED) (_ BitVec 32))
(declare-fun coerce$35$$35$18 (Str) Int)
(declare-fun coerce$35$$35$78 (VNat.VNat) Liquid.ProofCombinators.QED)
(declare-fun coerce$35$$35$56 (Liquid.ProofCombinators.QED) Str)
(declare-fun coerce$35$$35$49 ((IsMonadArray.IsMonadArray Int Int)) (IsMonad.IsMonad Int))
(declare-fun coerce$35$$35$74 (VNat.VNat) Str)
(declare-fun coerce$35$$35$41 ((IsMonad.IsMonad Int)) (IsMonadArray.IsMonadArray Int Int))
(declare-fun coerce$35$$35$52 ((IsMonadArray.IsMonadArray Int Int)) (VList.VList Int))
(declare-fun coerce$35$$35$1 (Int) Bool)
(declare-fun coerce$35$$35$68 ((VList.VList Int)) (IsMonadArray.IsMonadArray Int Int))
(declare-fun coerce$35$$35$64 ((VList.VList Int)) Bool)
(declare-fun coerce$35$$35$16 (Bool) (VList.VList Int))
(declare-fun coerce$35$$35$75 (VNat.VNat) (_ BitVec 32))
(declare-fun coerce$35$$35$13 (Bool) (IsMonad.IsMonad Int))
(declare-fun coerce$35$$35$37 ((IsMonad.IsMonad Int)) Bool)
(declare-fun coerce$35$$35$15 (Bool) Liquid.ProofCombinators.QED)
(declare-fun coerce$35$$35$12 (Bool) (_ BitVec 32))
(declare-fun coerce$35$$35$31 ((_ BitVec 32)) (IsMonad.IsMonad Int))
(declare-fun coerce$35$$35$47 ((IsMonadArray.IsMonadArray Int Int)) Str)
(declare-fun coerce$35$$35$34 ((_ BitVec 32)) (VList.VList Int))
(declare-fun coerce$35$$35$17 (Bool) VNat.VNat)
(declare-fun coerce$35$$35$23 (Str) (IsMonadArray.IsMonadArray Int Int))
(declare-fun coerce$35$$35$8 (Int) VNat.VNat)
(declare-fun coerce$35$$35$32 ((_ BitVec 32)) (IsMonadArray.IsMonadArray Int Int))
(declare-fun coerce$35$$35$72 (VNat.VNat) Int)
(declare-fun coerce$35$$35$36 ((IsMonad.IsMonad Int)) Int)
(declare-fun coerce$35$$35$6 (Int) Liquid.ProofCombinators.QED)
(declare-fun coerce$35$$35$63 ((VList.VList Int)) Int)
(declare-fun coerce$35$$35$29 ((_ BitVec 32)) Str)
(declare-fun coerce$35$$35$20 (Str) Str)
(declare-fun coerce$35$$35$43 ((IsMonad.IsMonad Int)) (VList.VList Int))
(declare-fun coerce$35$$35$69 ((VList.VList Int)) Liquid.ProofCombinators.QED)
(declare-fun coerce$35$$35$42 ((IsMonad.IsMonad Int)) Liquid.ProofCombinators.QED)
(declare-fun coerce$35$$35$67 ((VList.VList Int)) (IsMonad.IsMonad Int))
(declare-fun coerce$35$$35$40 ((IsMonad.IsMonad Int)) (IsMonad.IsMonad Int))
(declare-fun coerce$35$$35$10 (Bool) Bool)
(declare-fun coerce$35$$35$70 ((VList.VList Int)) (VList.VList Int))
(declare-fun coerce$35$$35$66 ((VList.VList Int)) (_ BitVec 32))
(declare-fun coerce$35$$35$76 (VNat.VNat) (IsMonad.IsMonad Int))
(declare-fun coerce$35$$35$73 (VNat.VNat) Bool)
(declare-fun coerce$35$$35$71 ((VList.VList Int)) VNat.VNat)
(declare-fun coerce$35$$35$39 ((IsMonad.IsMonad Int)) (_ BitVec 32))
(declare-fun coerce$35$$35$44 ((IsMonad.IsMonad Int)) VNat.VNat)
(declare-fun coerce$35$$35$2 (Int) Str)
(declare-fun coerce$35$$35$79 (VNat.VNat) (VList.VList Int))
(declare-fun coerce$35$$35$65 ((VList.VList Int)) Str)
(declare-fun coerce$35$$35$77 (VNat.VNat) (IsMonadArray.IsMonadArray Int Int))
(declare-fun coerce$35$$35$27 ((_ BitVec 32)) Int)
(declare-fun coerce$35$$35$3 (Int) (_ BitVec 32))
(declare-fun coerce$35$$35$53 ((IsMonadArray.IsMonadArray Int Int)) VNat.VNat)
(declare-fun coerce$35$$35$38 ((IsMonad.IsMonad Int)) Str)
(declare-fun coerce$35$$35$9 (Bool) Int)
(declare-fun coerce$35$$35$59 (Liquid.ProofCombinators.QED) (IsMonadArray.IsMonadArray Int Int))
(declare-fun coerce$35$$35$51 ((IsMonadArray.IsMonadArray Int Int)) Liquid.ProofCombinators.QED)
(declare-fun smt_lambda$35$$35$55 (Liquid.ProofCombinators.QED Bool) Int)
(declare-fun smt_lambda$35$$35$45 ((IsMonadArray.IsMonadArray Int Int) Int) Int)
(declare-fun smt_lambda$35$$35$35 ((_ BitVec 32) VNat.VNat) Int)
(declare-fun smt_lambda$35$$35$5 (Int (IsMonadArray.IsMonadArray Int Int)) Int)
(declare-fun smt_lambda$35$$35$28 ((_ BitVec 32) Bool) Int)
(declare-fun smt_lambda$35$$35$33 ((_ BitVec 32) Liquid.ProofCombinators.QED) Int)
(declare-fun smt_lambda$35$$35$48 ((IsMonadArray.IsMonadArray Int Int) (_ BitVec 32)) Int)
(declare-fun smt_lambda$35$$35$24 (Str Liquid.ProofCombinators.QED) Int)
(declare-fun smt_lambda$35$$35$19 (Str Bool) Int)
(declare-fun smt_lambda$35$$35$22 (Str (IsMonad.IsMonad Int)) Int)
(declare-fun smt_lambda$35$$35$25 (Str (VList.VList Int)) Int)
(declare-fun smt_lambda$35$$35$11 (Bool Str) Int)
(declare-fun smt_lambda$35$$35$14 (Bool (IsMonadArray.IsMonadArray Int Int)) Int)
(declare-fun smt_lambda$35$$35$46 ((IsMonadArray.IsMonadArray Int Int) Bool) Int)
(declare-fun smt_lambda$35$$35$26 (Str VNat.VNat) Int)
(declare-fun smt_lambda$35$$35$7 (Int (VList.VList Int)) Int)
(declare-fun smt_lambda$35$$35$21 (Str (_ BitVec 32)) Int)
(declare-fun smt_lambda$35$$35$54 (Liquid.ProofCombinators.QED Int) Int)
(declare-fun smt_lambda$35$$35$4 (Int (IsMonad.IsMonad Int)) Int)
(declare-fun smt_lambda$35$$35$61 (Liquid.ProofCombinators.QED (VList.VList Int)) Int)
(declare-fun smt_lambda$35$$35$58 (Liquid.ProofCombinators.QED (IsMonad.IsMonad Int)) Int)
(declare-fun smt_lambda$35$$35$30 ((_ BitVec 32) (_ BitVec 32)) Int)
(declare-fun smt_lambda$35$$35$50 ((IsMonadArray.IsMonadArray Int Int) (IsMonadArray.IsMonadArray Int Int)) Int)
(declare-fun smt_lambda$35$$35$80 (VNat.VNat VNat.VNat) Int)
(declare-fun smt_lambda$35$$35$60 (Liquid.ProofCombinators.QED Liquid.ProofCombinators.QED) Int)
(declare-fun smt_lambda$35$$35$0 (Int Int) Int)
(declare-fun smt_lambda$35$$35$62 (Liquid.ProofCombinators.QED VNat.VNat) Int)
(declare-fun smt_lambda$35$$35$57 (Liquid.ProofCombinators.QED (_ BitVec 32)) Int)
(declare-fun smt_lambda$35$$35$18 (Str Int) Int)
(declare-fun smt_lambda$35$$35$78 (VNat.VNat Liquid.ProofCombinators.QED) Int)
(declare-fun smt_lambda$35$$35$56 (Liquid.ProofCombinators.QED Str) Int)
(declare-fun smt_lambda$35$$35$49 ((IsMonadArray.IsMonadArray Int Int) (IsMonad.IsMonad Int)) Int)
(declare-fun smt_lambda$35$$35$74 (VNat.VNat Str) Int)
(declare-fun smt_lambda$35$$35$41 ((IsMonad.IsMonad Int) (IsMonadArray.IsMonadArray Int Int)) Int)
(declare-fun smt_lambda$35$$35$52 ((IsMonadArray.IsMonadArray Int Int) (VList.VList Int)) Int)
(declare-fun smt_lambda$35$$35$1 (Int Bool) Int)
(declare-fun smt_lambda$35$$35$68 ((VList.VList Int) (IsMonadArray.IsMonadArray Int Int)) Int)
(declare-fun smt_lambda$35$$35$64 ((VList.VList Int) Bool) Int)
(declare-fun smt_lambda$35$$35$16 (Bool (VList.VList Int)) Int)
(declare-fun smt_lambda$35$$35$75 (VNat.VNat (_ BitVec 32)) Int)
(declare-fun smt_lambda$35$$35$13 (Bool (IsMonad.IsMonad Int)) Int)
(declare-fun smt_lambda$35$$35$37 ((IsMonad.IsMonad Int) Bool) Int)
(declare-fun smt_lambda$35$$35$15 (Bool Liquid.ProofCombinators.QED) Int)
(declare-fun smt_lambda$35$$35$12 (Bool (_ BitVec 32)) Int)
(declare-fun smt_lambda$35$$35$31 ((_ BitVec 32) (IsMonad.IsMonad Int)) Int)
(declare-fun smt_lambda$35$$35$47 ((IsMonadArray.IsMonadArray Int Int) Str) Int)
(declare-fun smt_lambda$35$$35$34 ((_ BitVec 32) (VList.VList Int)) Int)
(declare-fun smt_lambda$35$$35$17 (Bool VNat.VNat) Int)
(declare-fun smt_lambda$35$$35$23 (Str (IsMonadArray.IsMonadArray Int Int)) Int)
(declare-fun smt_lambda$35$$35$8 (Int VNat.VNat) Int)
(declare-fun smt_lambda$35$$35$32 ((_ BitVec 32) (IsMonadArray.IsMonadArray Int Int)) Int)
(declare-fun smt_lambda$35$$35$72 (VNat.VNat Int) Int)
(declare-fun smt_lambda$35$$35$36 ((IsMonad.IsMonad Int) Int) Int)
(declare-fun smt_lambda$35$$35$6 (Int Liquid.ProofCombinators.QED) Int)
(declare-fun smt_lambda$35$$35$63 ((VList.VList Int) Int) Int)
(declare-fun smt_lambda$35$$35$29 ((_ BitVec 32) Str) Int)
(declare-fun smt_lambda$35$$35$20 (Str Str) Int)
(declare-fun smt_lambda$35$$35$43 ((IsMonad.IsMonad Int) (VList.VList Int)) Int)
(declare-fun smt_lambda$35$$35$69 ((VList.VList Int) Liquid.ProofCombinators.QED) Int)
(declare-fun smt_lambda$35$$35$42 ((IsMonad.IsMonad Int) Liquid.ProofCombinators.QED) Int)
(declare-fun smt_lambda$35$$35$67 ((VList.VList Int) (IsMonad.IsMonad Int)) Int)
(declare-fun smt_lambda$35$$35$40 ((IsMonad.IsMonad Int) (IsMonad.IsMonad Int)) Int)
(declare-fun smt_lambda$35$$35$10 (Bool Bool) Int)
(declare-fun smt_lambda$35$$35$70 ((VList.VList Int) (VList.VList Int)) Int)
(declare-fun smt_lambda$35$$35$66 ((VList.VList Int) (_ BitVec 32)) Int)
(declare-fun smt_lambda$35$$35$76 (VNat.VNat (IsMonad.IsMonad Int)) Int)
(declare-fun smt_lambda$35$$35$73 (VNat.VNat Bool) Int)
(declare-fun smt_lambda$35$$35$71 ((VList.VList Int) VNat.VNat) Int)
(declare-fun smt_lambda$35$$35$39 ((IsMonad.IsMonad Int) (_ BitVec 32)) Int)
(declare-fun smt_lambda$35$$35$44 ((IsMonad.IsMonad Int) VNat.VNat) Int)
(declare-fun smt_lambda$35$$35$2 (Int Str) Int)
(declare-fun smt_lambda$35$$35$79 (VNat.VNat (VList.VList Int)) Int)
(declare-fun smt_lambda$35$$35$65 ((VList.VList Int) Str) Int)
(declare-fun smt_lambda$35$$35$77 (VNat.VNat (IsMonadArray.IsMonadArray Int Int)) Int)
(declare-fun smt_lambda$35$$35$27 ((_ BitVec 32) Int) Int)
(declare-fun smt_lambda$35$$35$3 (Int (_ BitVec 32)) Int)
(declare-fun smt_lambda$35$$35$53 ((IsMonadArray.IsMonadArray Int Int) VNat.VNat) Int)
(declare-fun smt_lambda$35$$35$38 ((IsMonad.IsMonad Int) Str) Int)
(declare-fun smt_lambda$35$$35$9 (Bool Int) Int)
(declare-fun smt_lambda$35$$35$59 (Liquid.ProofCombinators.QED (IsMonadArray.IsMonadArray Int Int)) Int)
(declare-fun smt_lambda$35$$35$51 ((IsMonadArray.IsMonadArray Int Int) Liquid.ProofCombinators.QED) Int)
(declare-fun lam_arg$35$$35$1$35$$35$45 () (IsMonadArray.IsMonadArray Int Int))
(declare-fun lam_arg$35$$35$2$35$$35$45 () (IsMonadArray.IsMonadArray Int Int))
(declare-fun lam_arg$35$$35$3$35$$35$45 () (IsMonadArray.IsMonadArray Int Int))
(declare-fun lam_arg$35$$35$4$35$$35$45 () (IsMonadArray.IsMonadArray Int Int))
(declare-fun lam_arg$35$$35$5$35$$35$45 () (IsMonadArray.IsMonadArray Int Int))
(declare-fun lam_arg$35$$35$6$35$$35$45 () (IsMonadArray.IsMonadArray Int Int))
(declare-fun lam_arg$35$$35$7$35$$35$45 () (IsMonadArray.IsMonadArray Int Int))
(declare-fun lam_arg$35$$35$1$35$$35$54 () Liquid.ProofCombinators.QED)
(declare-fun lam_arg$35$$35$2$35$$35$54 () Liquid.ProofCombinators.QED)
(declare-fun lam_arg$35$$35$3$35$$35$54 () Liquid.ProofCombinators.QED)
(declare-fun lam_arg$35$$35$4$35$$35$54 () Liquid.ProofCombinators.QED)
(declare-fun lam_arg$35$$35$5$35$$35$54 () Liquid.ProofCombinators.QED)
(declare-fun lam_arg$35$$35$6$35$$35$54 () Liquid.ProofCombinators.QED)
(declare-fun lam_arg$35$$35$7$35$$35$54 () Liquid.ProofCombinators.QED)
(declare-fun lam_arg$35$$35$1$35$$35$0 () Int)
(declare-fun lam_arg$35$$35$2$35$$35$0 () Int)
(declare-fun lam_arg$35$$35$3$35$$35$0 () Int)
(declare-fun lam_arg$35$$35$4$35$$35$0 () Int)
(declare-fun lam_arg$35$$35$5$35$$35$0 () Int)
(declare-fun lam_arg$35$$35$6$35$$35$0 () Int)
(declare-fun lam_arg$35$$35$7$35$$35$0 () Int)
(declare-fun lam_arg$35$$35$1$35$$35$18 () Str)
(declare-fun lam_arg$35$$35$2$35$$35$18 () Str)
(declare-fun lam_arg$35$$35$3$35$$35$18 () Str)
(declare-fun lam_arg$35$$35$4$35$$35$18 () Str)
(declare-fun lam_arg$35$$35$5$35$$35$18 () Str)
(declare-fun lam_arg$35$$35$6$35$$35$18 () Str)
(declare-fun lam_arg$35$$35$7$35$$35$18 () Str)
(declare-fun lam_arg$35$$35$1$35$$35$72 () VNat.VNat)
(declare-fun lam_arg$35$$35$2$35$$35$72 () VNat.VNat)
(declare-fun lam_arg$35$$35$3$35$$35$72 () VNat.VNat)
(declare-fun lam_arg$35$$35$4$35$$35$72 () VNat.VNat)
(declare-fun lam_arg$35$$35$5$35$$35$72 () VNat.VNat)
(declare-fun lam_arg$35$$35$6$35$$35$72 () VNat.VNat)
(declare-fun lam_arg$35$$35$7$35$$35$72 () VNat.VNat)
(declare-fun lam_arg$35$$35$1$35$$35$36 () (IsMonad.IsMonad Int))
(declare-fun lam_arg$35$$35$2$35$$35$36 () (IsMonad.IsMonad Int))
(declare-fun lam_arg$35$$35$3$35$$35$36 () (IsMonad.IsMonad Int))
(declare-fun lam_arg$35$$35$4$35$$35$36 () (IsMonad.IsMonad Int))
(declare-fun lam_arg$35$$35$5$35$$35$36 () (IsMonad.IsMonad Int))
(declare-fun lam_arg$35$$35$6$35$$35$36 () (IsMonad.IsMonad Int))
(declare-fun lam_arg$35$$35$7$35$$35$36 () (IsMonad.IsMonad Int))
(declare-fun lam_arg$35$$35$1$35$$35$63 () (VList.VList Int))
(declare-fun lam_arg$35$$35$2$35$$35$63 () (VList.VList Int))
(declare-fun lam_arg$35$$35$3$35$$35$63 () (VList.VList Int))
(declare-fun lam_arg$35$$35$4$35$$35$63 () (VList.VList Int))
(declare-fun lam_arg$35$$35$5$35$$35$63 () (VList.VList Int))
(declare-fun lam_arg$35$$35$6$35$$35$63 () (VList.VList Int))
(declare-fun lam_arg$35$$35$7$35$$35$63 () (VList.VList Int))
(declare-fun lam_arg$35$$35$1$35$$35$27 () (_ BitVec 32))
(declare-fun lam_arg$35$$35$2$35$$35$27 () (_ BitVec 32))
(declare-fun lam_arg$35$$35$3$35$$35$27 () (_ BitVec 32))
(declare-fun lam_arg$35$$35$4$35$$35$27 () (_ BitVec 32))
(declare-fun lam_arg$35$$35$5$35$$35$27 () (_ BitVec 32))
(declare-fun lam_arg$35$$35$6$35$$35$27 () (_ BitVec 32))
(declare-fun lam_arg$35$$35$7$35$$35$27 () (_ BitVec 32))
(declare-fun lam_arg$35$$35$1$35$$35$9 () Bool)
(declare-fun lam_arg$35$$35$2$35$$35$9 () Bool)
(declare-fun lam_arg$35$$35$3$35$$35$9 () Bool)
(declare-fun lam_arg$35$$35$4$35$$35$9 () Bool)
(declare-fun lam_arg$35$$35$5$35$$35$9 () Bool)
(declare-fun lam_arg$35$$35$6$35$$35$9 () Bool)
(declare-fun lam_arg$35$$35$7$35$$35$9 () Bool)










(assert (distinct Liquid.ProofCombinators.QED Liquid.ProofCombinators.Admit))





(assert (distinct GHC.Types.True GHC.Types.False))



(assert (distinct GHC.Types.EQ GHC.Types.GT GHC.Types.LT))
(push 1)
