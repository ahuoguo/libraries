(set-option :auto_config false)
(set-option :smt.mbqi false)
(set-option :smt.case_split 3)
(set-option :smt.qi.eager_threshold 100.0)
(set-option :smt.delay_units true)
(set-option :smt.arith.solver 2)
(set-option :smt.arith.nl false)

;; Prelude

;; AIR prelude
(declare-sort %%Function%% 0)

(declare-sort FuelId 0)
(declare-sort Fuel 0)
(declare-const zero Fuel)
(declare-fun succ (Fuel) Fuel)
(declare-fun fuel_bool (FuelId) Bool)
(declare-fun fuel_bool_default (FuelId) Bool)
(declare-const fuel_defaults Bool)
(assert
 (=>
  fuel_defaults
  (forall ((id FuelId)) (!
    (= (fuel_bool id) (fuel_bool_default id))
    :pattern ((fuel_bool id))
    :qid prelude_fuel_defaults
    :skolemid skolem_prelude_fuel_defaults
))))
(declare-sort Char 0)
(declare-fun char%from_unicode (Int) Char)
(declare-fun char%to_unicode (Char) Int)
(declare-sort StrSlice 0)
(declare-fun str%strslice_is_ascii (StrSlice) Bool)
(declare-fun str%strslice_len (StrSlice) Int)
(declare-fun str%strslice_get_char (StrSlice Int) Char)
(declare-fun str%new_strlit (Int) StrSlice)
(declare-fun str%from_strlit (StrSlice) Int)
(declare-sort Poly 0)
(declare-sort Height 0)
(declare-fun I (Int) Poly)
(declare-fun B (Bool) Poly)
(declare-fun %I (Poly) Int)
(declare-fun %B (Poly) Bool)
(declare-fun S (StrSlice) Poly)
(declare-fun %S (Poly) StrSlice)
(declare-fun C (Char) Poly)
(declare-fun %C (Poly) Char)
(declare-sort Type 0)
(declare-const BOOL Type)
(declare-const INT Type)
(declare-const NAT Type)
(declare-const STRSLICE Type)
(declare-const CHAR Type)
(declare-fun UINT (Int) Type)
(declare-fun SINT (Int) Type)
(declare-fun CONST_INT (Int) Type)
(declare-fun REF (Type) Type)
(declare-fun MUT_REF (Type) Type)
(declare-fun BOX (Type) Type)
(declare-fun RC (Type) Type)
(declare-fun ARC (Type) Type)
(declare-fun GHOST (Type) Type)
(declare-fun TRACKED (Type) Type)
(declare-fun NEVER (Type) Type)
(declare-fun has_type (Poly Type) Bool)
(declare-fun as_type (Poly Type) Poly)
(declare-fun mk_fun (%%Function%%) %%Function%%)
(declare-fun const_int (Type) Int)
(assert
 (forall ((i Int)) (= i (const_int (CONST_INT i))))
)
(assert
 (has_type (B true) BOOL)
)
(assert
 (has_type (B false) BOOL)
)
(assert
 (forall ((x Poly) (t Type)) (!
   (and
    (has_type (as_type x t) t)
    (=>
     (has_type x t)
     (= x (as_type x t))
   ))
   :pattern ((as_type x t))
   :qid prelude_as_type
   :skolemid skolem_prelude_as_type
)))
(assert
 (forall ((x %%Function%%)) (!
   (= (mk_fun x) x)
   :pattern ((mk_fun x))
   :qid prelude_mk_fun
   :skolemid skolem_prelude_mk_fun
)))
(assert
 (forall ((x Bool)) (!
   (= x (%B (B x)))
   :pattern ((B x))
   :qid prelude_unbox_box_bool
   :skolemid skolem_prelude_unbox_box_bool
)))
(assert
 (forall ((x Int)) (!
   (= x (%I (I x)))
   :pattern ((I x))
   :qid prelude_unbox_box_int
   :skolemid skolem_prelude_unbox_box_int
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x BOOL)
    (= x (B (%B x)))
   )
   :pattern ((has_type x BOOL))
   :qid prelude_box_unbox_bool
   :skolemid skolem_prelude_box_unbox_bool
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x INT)
    (= x (I (%I x)))
   )
   :pattern ((has_type x INT))
   :qid prelude_box_unbox_int
   :skolemid skolem_prelude_box_unbox_int
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x NAT)
    (= x (I (%I x)))
   )
   :pattern ((has_type x NAT))
   :qid prelude_box_unbox_nat
   :skolemid skolem_prelude_box_unbox_nat
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (UINT bits))
    (= x (I (%I x)))
   )
   :pattern ((has_type x (UINT bits)))
   :qid prelude_box_unbox_uint
   :skolemid skolem_prelude_box_unbox_uint
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (SINT bits))
    (= x (I (%I x)))
   )
   :pattern ((has_type x (SINT bits)))
   :qid prelude_box_unbox_sint
   :skolemid skolem_prelude_box_unbox_sint
)))
(assert
 (forall ((x Int)) (!
   (= (str%from_strlit (str%new_strlit x)) x)
   :pattern ((str%new_strlit x))
   :qid prelude_strlit_injective
   :skolemid skolem_prelude_strlit_injective
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x STRSLICE)
    (= x (S (%S x)))
   )
   :pattern ((has_type x STRSLICE))
   :qid prelude_box_unbox_strslice
   :skolemid skolem_prelude_box_unbox_strslice
)))
(assert
 (forall ((x StrSlice)) (!
   (= x (%S (S x)))
   :pattern ((S x))
   :qid prelude_unbox_box_strslice
   :skolemid skolem_prelude_unbox_box_strslice
)))
(assert
 (forall ((x StrSlice)) (!
   (has_type (S x) STRSLICE)
   :pattern ((has_type (S x) STRSLICE))
   :qid prelude_has_type_strslice
   :skolemid skolem_prelude_has_type_strslice
)))
(declare-fun ext_eq (Bool Type Type Poly Poly) Bool)
(assert
 (forall ((deep Bool) (t Type) (td Type) (x Poly) (y Poly)) (!
   (= (= x y) (ext_eq deep t td x y))
   :pattern ((ext_eq deep t td x y))
   :qid prelude_ext_eq
   :skolemid skolem_prelude_ext_eq
)))
(declare-const SZ Int)
(assert
 (or
  (= SZ 32)
  (= SZ 64)
))
(declare-fun uHi (Int) Int)
(declare-fun iLo (Int) Int)
(declare-fun iHi (Int) Int)
(assert
 (= (uHi 8) 256)
)
(assert
 (= (uHi 16) 65536)
)
(assert
 (= (uHi 32) 4294967296)
)
(assert
 (= (uHi 64) 18446744073709551616)
)
(assert
 (= (uHi 128) (+ 1 340282366920938463463374607431768211455))
)
(assert
 (= (iLo 8) (- 128))
)
(assert
 (= (iLo 16) (- 32768))
)
(assert
 (= (iLo 32) (- 2147483648))
)
(assert
 (= (iLo 64) (- 9223372036854775808))
)
(assert
 (= (iLo 128) (- 170141183460469231731687303715884105728))
)
(assert
 (= (iHi 8) 128)
)
(assert
 (= (iHi 16) 32768)
)
(assert
 (= (iHi 32) 2147483648)
)
(assert
 (= (iHi 64) 9223372036854775808)
)
(assert
 (= (iHi 128) 170141183460469231731687303715884105728)
)
(declare-fun nClip (Int) Int)
(declare-fun uClip (Int Int) Int)
(declare-fun iClip (Int Int) Int)
(assert
 (forall ((i Int)) (!
   (and
    (<= 0 (nClip i))
    (=>
     (<= 0 i)
     (= i (nClip i))
   ))
   :pattern ((nClip i))
   :qid prelude_nat_clip
   :skolemid skolem_prelude_nat_clip
)))
(assert
 (forall ((bits Int) (i Int)) (!
   (and
    (<= 0 (uClip bits i))
    (< (uClip bits i) (uHi bits))
    (=>
     (and
      (<= 0 i)
      (< i (uHi bits))
     )
     (= i (uClip bits i))
   ))
   :pattern ((uClip bits i))
   :qid prelude_u_clip
   :skolemid skolem_prelude_u_clip
)))
(assert
 (forall ((bits Int) (i Int)) (!
   (and
    (<= (iLo bits) (iClip bits i))
    (< (iClip bits i) (iHi bits))
    (=>
     (and
      (<= (iLo bits) i)
      (< i (iHi bits))
     )
     (= i (iClip bits i))
   ))
   :pattern ((iClip bits i))
   :qid prelude_i_clip
   :skolemid skolem_prelude_i_clip
)))
(declare-fun uInv (Int Int) Bool)
(declare-fun iInv (Int Int) Bool)
(assert
 (forall ((bits Int) (i Int)) (!
   (= (uInv bits i) (and
     (<= 0 i)
     (< i (uHi bits))
   ))
   :pattern ((uInv bits i))
   :qid prelude_u_inv
   :skolemid skolem_prelude_u_inv
)))
(assert
 (forall ((bits Int) (i Int)) (!
   (= (iInv bits i) (and
     (<= (iLo bits) i)
     (< i (iHi bits))
   ))
   :pattern ((iInv bits i))
   :qid prelude_i_inv
   :skolemid skolem_prelude_i_inv
)))
(assert
 (forall ((x Int)) (!
   (has_type (I x) INT)
   :pattern ((has_type (I x) INT))
   :qid prelude_has_type_int
   :skolemid skolem_prelude_has_type_int
)))
(assert
 (forall ((x Int)) (!
   (=>
    (<= 0 x)
    (has_type (I x) NAT)
   )
   :pattern ((has_type (I x) NAT))
   :qid prelude_has_type_nat
   :skolemid skolem_prelude_has_type_nat
)))
(assert
 (forall ((bits Int) (x Int)) (!
   (=>
    (uInv bits x)
    (has_type (I x) (UINT bits))
   )
   :pattern ((has_type (I x) (UINT bits)))
   :qid prelude_has_type_uint
   :skolemid skolem_prelude_has_type_uint
)))
(assert
 (forall ((bits Int) (x Int)) (!
   (=>
    (iInv bits x)
    (has_type (I x) (SINT bits))
   )
   :pattern ((has_type (I x) (SINT bits)))
   :qid prelude_has_type_sint
   :skolemid skolem_prelude_has_type_sint
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x NAT)
    (<= 0 (%I x))
   )
   :pattern ((has_type x NAT))
   :qid prelude_unbox_int
   :skolemid skolem_prelude_unbox_int
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (UINT bits))
    (uInv bits (%I x))
   )
   :pattern ((has_type x (UINT bits)))
   :qid prelude_unbox_uint
   :skolemid skolem_prelude_unbox_uint
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (SINT bits))
    (iInv bits (%I x))
   )
   :pattern ((has_type x (SINT bits)))
   :qid prelude_unbox_sint
   :skolemid skolem_prelude_unbox_sint
)))
(declare-fun Mul (Int Int) Int)
(declare-fun EucDiv (Int Int) Int)
(declare-fun EucMod (Int Int) Int)
(assert
 (forall ((x Int) (y Int)) (!
   (= (Mul x y) (* x y))
   :pattern ((Mul x y))
   :qid prelude_mul
   :skolemid skolem_prelude_mul
)))
(assert
 (forall ((x Int) (y Int)) (!
   (= (EucDiv x y) (div x y))
   :pattern ((EucDiv x y))
   :qid prelude_eucdiv
   :skolemid skolem_prelude_eucdiv
)))
(assert
 (forall ((x Int) (y Int)) (!
   (= (EucMod x y) (mod x y))
   :pattern ((EucMod x y))
   :qid prelude_eucmod
   :skolemid skolem_prelude_eucmod
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x CHAR)
    (= x (C (%C x)))
   )
   :pattern ((has_type x CHAR))
   :qid prelude_box_unbox_char
   :skolemid skolem_prelude_box_unbox_char
)))
(assert
 (forall ((x Char)) (!
   (= x (%C (C x)))
   :pattern ((C x))
   :qid prelude_unbox_box_char
   :skolemid skolem_prelude_unbox_box_char
)))
(assert
 (forall ((x Char)) (!
   (has_type (C x) CHAR)
   :pattern ((has_type (C x) CHAR))
   :qid prelude_has_type_char
   :skolemid skolem_prelude_has_type_char
)))
(assert
 (forall ((x Int)) (!
   (= (char%to_unicode (char%from_unicode x)) x)
   :pattern ((char%from_unicode x))
   :qid prelude_char_injective
   :skolemid skolem_prelude_char_injective
)))
(assert
 (forall ((c Char)) (!
   (and
    (<= 0 (char%to_unicode c))
    (< (char%to_unicode c) (uHi 32))
   )
   :pattern ((char%to_unicode c))
   :qid prelude_to_unicode_bounds
   :skolemid skolem_prelude_to_unicode_bounds
)))
(declare-fun height (Poly) Height)
(declare-fun height_lt (Height Height) Bool)
(assert
 (forall ((x Height) (y Height)) (!
   (= (height_lt x y) (and
     ((_ partial-order 0) x y)
     (not (= x y))
   ))
   :pattern ((height_lt x y))
   :qid prelude_height_lt
   :skolemid skolem_prelude_height_lt
)))
(declare-fun fun_from_recursive_field (Poly) Poly)
(declare-fun check_decrease_int (Int Int Bool) Bool)
(assert
 (forall ((cur Int) (prev Int) (otherwise Bool)) (!
   (= (check_decrease_int cur prev otherwise) (or
     (and
      (<= 0 cur)
      (< cur prev)
     )
     (and
      (= cur prev)
      otherwise
   )))
   :pattern ((check_decrease_int cur prev otherwise))
   :qid prelude_check_decrease_int
   :skolemid skolem_prelude_check_decrease_int
)))
(declare-fun check_decrease_height (Poly Poly Bool) Bool)
(assert
 (forall ((cur Poly) (prev Poly) (otherwise Bool)) (!
   (= (check_decrease_height cur prev otherwise) (or
     (height_lt (height cur) (height prev))
     (and
      (= (height cur) (height prev))
      otherwise
   )))
   :pattern ((check_decrease_height cur prev otherwise))
   :qid prelude_check_decrease_height
   :skolemid skolem_prelude_check_decrease_height
)))
(declare-fun uintxor (Int Poly Poly) Int)
(declare-fun uintand (Int Poly Poly) Int)
(declare-fun uintor (Int Poly Poly) Int)
(declare-fun uintshr (Int Poly Poly) Int)
(declare-fun uintshl (Int Poly Poly) Int)
(declare-fun uintnot (Int Poly) Int)
(declare-fun closure_req (Type Type Type Type Poly Poly) Bool)
(declare-fun closure_ens (Type Type Type Type Poly Poly Poly) Bool)

;; MODULE ''
;; NonLinearArith/dist_unboxed.rs:90:1: 90:76 (#0)

;; Fuel
(declare-const fuel%dist_unboxed!dist_left_add. FuelId)
(declare-const fuel%dist_unboxed!dist_right_add. FuelId)
(declare-const fuel%dist_unboxed!dist_left_sub. FuelId)
(declare-const fuel%dist_unboxed!dist_right_sub. FuelId)
(declare-const fuel%dist_unboxed!mul. FuelId)
(declare-const fuel%dist_unboxed!add. FuelId)
(declare-const fuel%dist_unboxed!sub. FuelId)
(declare-const fuel%dist_unboxed!is_le. FuelId)
(assert
 (distinct fuel%dist_unboxed!dist_left_add. fuel%dist_unboxed!dist_right_add. fuel%dist_unboxed!dist_left_sub.
  fuel%dist_unboxed!dist_right_sub. fuel%dist_unboxed!mul. fuel%dist_unboxed!add. fuel%dist_unboxed!sub.
  fuel%dist_unboxed!is_le.
))

;; Datatypes
(declare-datatypes ((tuple%0. 0)) (((tuple%0./tuple%0))))
(declare-fun TYPE%fun%1. (Type Type) Type)
(declare-const TYPE%tuple%0. Type)
(declare-fun Poly%fun%1. (%%Function%%) Poly)
(declare-fun %Poly%fun%1. (Poly) %%Function%%)
(declare-fun Poly%tuple%0. (tuple%0.) Poly)
(declare-fun %Poly%tuple%0. (Poly) tuple%0.)
(assert
 (forall ((x@ %%Function%%)) (!
   (= x@ (%Poly%fun%1. (Poly%fun%1. x@)))
   :pattern ((Poly%fun%1. x@))
   :qid internal_crate__fun__1_box_axiom_definition
   :skolemid skolem_internal_crate__fun__1_box_axiom_definition
)))
(assert
 (forall ((T%0& Type) (T%1& Type) (x@ Poly)) (!
   (=>
    (has_type x@ (TYPE%fun%1. T%0& T%1&))
    (= x@ (Poly%fun%1. (%Poly%fun%1. x@)))
   )
   :pattern ((has_type x@ (TYPE%fun%1. T%0& T%1&)))
   :qid internal_crate__fun__1_unbox_axiom_definition
   :skolemid skolem_internal_crate__fun__1_unbox_axiom_definition
)))
(declare-fun %%apply%%0 (%%Function%% Poly) Poly)
(assert
 (forall ((T%0& Type) (T%1& Type) (x@ %%Function%%)) (!
   (=>
    (forall ((T%0@ Poly)) (!
      (=>
       (has_type T%0@ T%0&)
       (has_type (%%apply%%0 x@ T%0@) T%1&)
      )
      :pattern ((has_type (%%apply%%0 x@ T%0@) T%1&))
      :qid internal_crate__fun__1_constructor_inner_definition
      :skolemid skolem_internal_crate__fun__1_constructor_inner_definition
    ))
    (has_type (Poly%fun%1. (mk_fun x@)) (TYPE%fun%1. T%0& T%1&))
   )
   :pattern ((has_type (Poly%fun%1. (mk_fun x@)) (TYPE%fun%1. T%0& T%1&)))
   :qid internal_crate__fun__1_constructor_definition
   :skolemid skolem_internal_crate__fun__1_constructor_definition
)))
(assert
 (forall ((T%0& Type) (T%1& Type) (T%0@ Poly) (x@ %%Function%%)) (!
   (=>
    (and
     (has_type (Poly%fun%1. x@) (TYPE%fun%1. T%0& T%1&))
     (has_type T%0@ T%0&)
    )
    (has_type (%%apply%%0 x@ T%0@) T%1&)
   )
   :pattern ((%%apply%%0 x@ T%0@) (has_type (Poly%fun%1. x@) (TYPE%fun%1. T%0& T%1&)))
   :qid internal_crate__fun__1_apply_definition
   :skolemid skolem_internal_crate__fun__1_apply_definition
)))
(assert
 (forall ((T%0& Type) (T%1& Type) (T%0@ Poly) (x@ %%Function%%)) (!
   (=>
    (and
     (has_type (Poly%fun%1. x@) (TYPE%fun%1. T%0& T%1&))
     (has_type T%0@ T%0&)
    )
    (height_lt (height (%%apply%%0 x@ T%0@)) (height (fun_from_recursive_field (Poly%fun%1.
        (mk_fun x@)
   )))))
   :pattern ((height (%%apply%%0 x@ T%0@)) (has_type (Poly%fun%1. x@) (TYPE%fun%1. T%0&
      T%1&
   )))
   :qid internal_crate__fun__1_height_apply_definition
   :skolemid skolem_internal_crate__fun__1_height_apply_definition
)))
(assert
 (forall ((T%0& Type) (T%0&. Type) (T%1& Type) (T%1&. Type) (deep@ Bool) (x@ Poly) (
    y@ Poly
   )
  ) (!
   (=>
    (and
     (has_type x@ (TYPE%fun%1. T%0& T%1&))
     (has_type y@ (TYPE%fun%1. T%0& T%1&))
     (forall ((T%0@ Poly)) (!
       (=>
        (has_type T%0@ T%0&)
        (ext_eq deep@ T%1& T%1&. (%%apply%%0 (%Poly%fun%1. x@) T%0@) (%%apply%%0 (%Poly%fun%1.
           y@
          ) T%0@
       )))
       :pattern ((ext_eq deep@ T%1& T%1&. (%%apply%%0 (%Poly%fun%1. x@) T%0@) (%%apply%%0 (
           %Poly%fun%1. y@
          ) T%0@
       )))
       :qid internal_crate__fun__1_inner_ext_equal_definition
       :skolemid skolem_internal_crate__fun__1_inner_ext_equal_definition
    )))
    (ext_eq deep@ (TYPE%fun%1. T%0& T%1&) (TYPE%fun%1. T%0&. T%1&.) x@ y@)
   )
   :pattern ((ext_eq deep@ (TYPE%fun%1. T%0& T%1&) (TYPE%fun%1. T%0&. T%1&.) x@ y@))
   :qid internal_crate__fun__1_ext_equal_definition
   :skolemid skolem_internal_crate__fun__1_ext_equal_definition
)))
(assert
 (forall ((x@ tuple%0.)) (!
   (= x@ (%Poly%tuple%0. (Poly%tuple%0. x@)))
   :pattern ((Poly%tuple%0. x@))
   :qid internal_crate__tuple__0_box_axiom_definition
   :skolemid skolem_internal_crate__tuple__0_box_axiom_definition
)))
(assert
 (forall ((x@ Poly)) (!
   (=>
    (has_type x@ TYPE%tuple%0.)
    (= x@ (Poly%tuple%0. (%Poly%tuple%0. x@)))
   )
   :pattern ((has_type x@ TYPE%tuple%0.))
   :qid internal_crate__tuple__0_unbox_axiom_definition
   :skolemid skolem_internal_crate__tuple__0_unbox_axiom_definition
)))
(assert
 (forall ((x@ tuple%0.)) (!
   (has_type (Poly%tuple%0. x@) TYPE%tuple%0.)
   :pattern ((has_type (Poly%tuple%0. x@) TYPE%tuple%0.))
   :qid internal_crate__tuple__0_has_type_always_definition
   :skolemid skolem_internal_crate__tuple__0_has_type_always_definition
)))

;; Function-Decl dist_unboxed::dist_left_add
(declare-fun dist_unboxed!dist_left_add.? (Poly Poly Poly) Int)

;; Function-Decl dist_unboxed::dist_right_add
(declare-fun dist_unboxed!dist_right_add.? (Poly Poly Poly) Int)

;; Function-Decl dist_unboxed::dist_left_sub
(declare-fun dist_unboxed!dist_left_sub.? (Poly Poly Poly) Int)

;; Function-Decl dist_unboxed::dist_right_sub
(declare-fun dist_unboxed!dist_right_sub.? (Poly Poly Poly) Int)

;; Function-Decl dist_unboxed::mul
(declare-fun dist_unboxed!mul.? (Poly Poly) Int)

;; Function-Decl dist_unboxed::add
(declare-fun dist_unboxed!add.? (Poly Poly) Int)

;; Function-Decl dist_unboxed::sub
(declare-fun dist_unboxed!sub.? (Poly Poly) Int)

;; Function-Decl dist_unboxed::is_le
(declare-fun dist_unboxed!is_le.? (Poly Poly) Bool)

;; Function-Specs dist_unboxed::lemma_induction_helper_pos
(declare-fun req%dist_unboxed!lemma_induction_helper_pos. (Int %%Function%% Int) Bool)
(declare-const %%global_location_label%%0 Bool)
(declare-const %%global_location_label%%1 Bool)
(declare-const %%global_location_label%%2 Bool)
(declare-const %%global_location_label%%3 Bool)
(declare-const %%global_location_label%%4 Bool)
(assert
 (forall ((n~2@ Int) (f~4@ %%Function%%) (x~6@ Int)) (!
   (= (req%dist_unboxed!lemma_induction_helper_pos. n~2@ f~4@ x~6@) (and
     (=>
      %%global_location_label%%0
      (>= x~6@ 0)
     )
     (=>
      %%global_location_label%%1
      (> n~2@ 0)
     )
     (=>
      %%global_location_label%%2
      (forall ((i~40$ Poly)) (!
        (=>
         (has_type i~40$ INT)
         (=>
          (and
           (<= 0 (%I i~40$))
           (< (%I i~40$) n~2@)
          )
          (%B (%%apply%%0 f~4@ i~40$))
        ))
        :pattern ((%%apply%%0 f~4@ i~40$))
        :qid user_dist_unboxed__lemma_induction_helper_pos_0
        :skolemid skolem_user_dist_unboxed__lemma_induction_helper_pos_0
     )))
     (=>
      %%global_location_label%%3
      (forall ((i~90$ Poly)) (!
        (=>
         (has_type i~90$ INT)
         (=>
          (and
           (>= (%I i~90$) 0)
           (%B (%%apply%%0 f~4@ i~90$))
          )
          (%B (%%apply%%0 f~4@ (I (dist_unboxed!add.? i~90$ (I n~2@)))))
        ))
        :pattern ((%%apply%%0 f~4@ i~90$) (%%apply%%0 f~4@ (I (dist_unboxed!add.? i~90$ (I n~2@)))))
        :qid user_dist_unboxed__lemma_induction_helper_pos_1
        :skolemid skolem_user_dist_unboxed__lemma_induction_helper_pos_1
     )))
     (=>
      %%global_location_label%%4
      (forall ((i~131$ Poly)) (!
        (=>
         (has_type i~131$ INT)
         (=>
          (and
           (< (%I i~131$) n~2@)
           (%B (%%apply%%0 f~4@ i~131$))
          )
          (%B (%%apply%%0 f~4@ (I (dist_unboxed!sub.? i~131$ (I n~2@)))))
        ))
        :pattern ((%%apply%%0 f~4@ i~131$) (%%apply%%0 f~4@ (I (dist_unboxed!sub.? i~131$ (I n~2@)))))
        :qid user_dist_unboxed__lemma_induction_helper_pos_2
        :skolemid skolem_user_dist_unboxed__lemma_induction_helper_pos_2
   )))))
   :pattern ((req%dist_unboxed!lemma_induction_helper_pos. n~2@ f~4@ x~6@))
   :qid internal_req__dist_unboxed!lemma_induction_helper_pos._definition
   :skolemid skolem_internal_req__dist_unboxed!lemma_induction_helper_pos._definition
)))

;; Function-Specs dist_unboxed::lemma_induction_helper_neg
(declare-fun req%dist_unboxed!lemma_induction_helper_neg. (Int %%Function%% Int) Bool)
(declare-const %%global_location_label%%5 Bool)
(declare-const %%global_location_label%%6 Bool)
(declare-const %%global_location_label%%7 Bool)
(declare-const %%global_location_label%%8 Bool)
(declare-const %%global_location_label%%9 Bool)
(assert
 (forall ((n~2@ Int) (f~4@ %%Function%%) (x~6@ Int)) (!
   (= (req%dist_unboxed!lemma_induction_helper_neg. n~2@ f~4@ x~6@) (and
     (=>
      %%global_location_label%%5
      (< x~6@ 0)
     )
     (=>
      %%global_location_label%%6
      (> n~2@ 0)
     )
     (=>
      %%global_location_label%%7
      (forall ((i~40$ Poly)) (!
        (=>
         (has_type i~40$ INT)
         (=>
          (and
           (<= 0 (%I i~40$))
           (< (%I i~40$) n~2@)
          )
          (%B (%%apply%%0 f~4@ i~40$))
        ))
        :pattern ((%%apply%%0 f~4@ i~40$))
        :qid user_dist_unboxed__lemma_induction_helper_neg_3
        :skolemid skolem_user_dist_unboxed__lemma_induction_helper_neg_3
     )))
     (=>
      %%global_location_label%%8
      (forall ((i~90$ Poly)) (!
        (=>
         (has_type i~90$ INT)
         (=>
          (and
           (>= (%I i~90$) 0)
           (%B (%%apply%%0 f~4@ i~90$))
          )
          (%B (%%apply%%0 f~4@ (I (dist_unboxed!add.? i~90$ (I n~2@)))))
        ))
        :pattern ((%%apply%%0 f~4@ i~90$) (%%apply%%0 f~4@ (I (dist_unboxed!add.? i~90$ (I n~2@)))))
        :qid user_dist_unboxed__lemma_induction_helper_neg_4
        :skolemid skolem_user_dist_unboxed__lemma_induction_helper_neg_4
     )))
     (=>
      %%global_location_label%%9
      (forall ((i~131$ Poly)) (!
        (=>
         (has_type i~131$ INT)
         (=>
          (and
           (< (%I i~131$) n~2@)
           (%B (%%apply%%0 f~4@ i~131$))
          )
          (%B (%%apply%%0 f~4@ (I (dist_unboxed!sub.? i~131$ (I n~2@)))))
        ))
        :pattern ((%%apply%%0 f~4@ i~131$) (%%apply%%0 f~4@ (I (dist_unboxed!sub.? i~131$ (I n~2@)))))
        :qid user_dist_unboxed__lemma_induction_helper_neg_5
        :skolemid skolem_user_dist_unboxed__lemma_induction_helper_neg_5
   )))))
   :pattern ((req%dist_unboxed!lemma_induction_helper_neg. n~2@ f~4@ x~6@))
   :qid internal_req__dist_unboxed!lemma_induction_helper_neg._definition
   :skolemid skolem_internal_req__dist_unboxed!lemma_induction_helper_neg._definition
)))

;; Function-Specs dist_unboxed::lemma_induction_helper
(declare-fun req%dist_unboxed!lemma_induction_helper. (Int %%Function%% Int) Bool)
(declare-const %%global_location_label%%10 Bool)
(declare-const %%global_location_label%%11 Bool)
(declare-const %%global_location_label%%12 Bool)
(declare-const %%global_location_label%%13 Bool)
(assert
 (forall ((n~2@ Int) (f~4@ %%Function%%) (x~6@ Int)) (!
   (= (req%dist_unboxed!lemma_induction_helper. n~2@ f~4@ x~6@) (and
     (=>
      %%global_location_label%%10
      (> n~2@ 0)
     )
     (=>
      %%global_location_label%%11
      (forall ((i~30$ Poly)) (!
        (=>
         (has_type i~30$ INT)
         (=>
          (and
           (<= 0 (%I i~30$))
           (< (%I i~30$) n~2@)
          )
          (%B (%%apply%%0 f~4@ i~30$))
        ))
        :pattern ((%%apply%%0 f~4@ i~30$))
        :qid user_dist_unboxed__lemma_induction_helper_6
        :skolemid skolem_user_dist_unboxed__lemma_induction_helper_6
     )))
     (=>
      %%global_location_label%%12
      (forall ((i~80$ Poly)) (!
        (=>
         (has_type i~80$ INT)
         (=>
          (and
           (>= (%I i~80$) 0)
           (%B (%%apply%%0 f~4@ i~80$))
          )
          (%B (%%apply%%0 f~4@ (I (dist_unboxed!add.? i~80$ (I n~2@)))))
        ))
        :pattern ((%%apply%%0 f~4@ i~80$) (%%apply%%0 f~4@ (I (dist_unboxed!add.? i~80$ (I n~2@)))))
        :qid user_dist_unboxed__lemma_induction_helper_7
        :skolemid skolem_user_dist_unboxed__lemma_induction_helper_7
     )))
     (=>
      %%global_location_label%%13
      (forall ((i~121$ Poly)) (!
        (=>
         (has_type i~121$ INT)
         (=>
          (and
           (< (%I i~121$) n~2@)
           (%B (%%apply%%0 f~4@ i~121$))
          )
          (%B (%%apply%%0 f~4@ (I (dist_unboxed!sub.? i~121$ (I n~2@)))))
        ))
        :pattern ((%%apply%%0 f~4@ i~121$) (%%apply%%0 f~4@ (I (dist_unboxed!sub.? i~121$ (I n~2@)))))
        :qid user_dist_unboxed__lemma_induction_helper_8
        :skolemid skolem_user_dist_unboxed__lemma_induction_helper_8
   )))))
   :pattern ((req%dist_unboxed!lemma_induction_helper. n~2@ f~4@ x~6@))
   :qid internal_req__dist_unboxed!lemma_induction_helper._definition
   :skolemid skolem_internal_req__dist_unboxed!lemma_induction_helper._definition
)))

;; Function-Specs dist_unboxed::lemma_mul_induction
(declare-fun req%dist_unboxed!lemma_mul_induction. (%%Function%%) Bool)
(declare-const %%global_location_label%%14 Bool)
(declare-const %%global_location_label%%15 Bool)
(declare-const %%global_location_label%%16 Bool)
(assert
 (forall ((f~2@ %%Function%%)) (!
   (= (req%dist_unboxed!lemma_mul_induction. f~2@) (and
     (=>
      %%global_location_label%%14
      (%B (%%apply%%0 f~2@ (I 0)))
     )
     (=>
      %%global_location_label%%15
      (forall ((i~25$ Poly)) (!
        (=>
         (has_type i~25$ INT)
         (=>
          (and
           (>= (%I i~25$) 0)
           (%B (%%apply%%0 f~2@ i~25$))
          )
          (%B (%%apply%%0 f~2@ (I (dist_unboxed!add.? i~25$ (I 1)))))
        ))
        :pattern ((%%apply%%0 f~2@ i~25$) (%%apply%%0 f~2@ (I (dist_unboxed!add.? i~25$ (I 1)))))
        :qid user_dist_unboxed__lemma_mul_induction_9
        :skolemid skolem_user_dist_unboxed__lemma_mul_induction_9
     )))
     (=>
      %%global_location_label%%16
      (forall ((i~70$ Poly)) (!
        (=>
         (has_type i~70$ INT)
         (=>
          (and
           (<= (%I i~70$) 0)
           (%B (%%apply%%0 f~2@ i~70$))
          )
          (%B (%%apply%%0 f~2@ (I (dist_unboxed!sub.? i~70$ (I 1)))))
        ))
        :pattern ((%%apply%%0 f~2@ i~70$) (%%apply%%0 f~2@ (I (dist_unboxed!sub.? i~70$ (I 1)))))
        :qid user_dist_unboxed__lemma_mul_induction_10
        :skolemid skolem_user_dist_unboxed__lemma_mul_induction_10
   )))))
   :pattern ((req%dist_unboxed!lemma_mul_induction. f~2@))
   :qid internal_req__dist_unboxed!lemma_mul_induction._definition
   :skolemid skolem_internal_req__dist_unboxed!lemma_mul_induction._definition
)))

;; Function-Axioms dist_unboxed::dist_left_add
(assert
 (fuel_bool_default fuel%dist_unboxed!dist_left_add.)
)
(assert
 (=>
  (fuel_bool fuel%dist_unboxed!dist_left_add.)
  (forall ((a~2@ Poly) (b~4@ Poly) (c~6@ Poly)) (!
    (= (dist_unboxed!dist_left_add.? a~2@ b~4@ c~6@) (Mul (+ (%I a~2@) (%I b~4@)) (%I c~6@)))
    :pattern ((dist_unboxed!dist_left_add.? a~2@ b~4@ c~6@))
    :qid internal_dist_unboxed!dist_left_add.?_definition
    :skolemid skolem_internal_dist_unboxed!dist_left_add.?_definition
))))

;; Function-Axioms dist_unboxed::dist_right_add
(assert
 (fuel_bool_default fuel%dist_unboxed!dist_right_add.)
)
(assert
 (=>
  (fuel_bool fuel%dist_unboxed!dist_right_add.)
  (forall ((a~2@ Poly) (b~4@ Poly) (c~6@ Poly)) (!
    (= (dist_unboxed!dist_right_add.? a~2@ b~4@ c~6@) (+ (Mul (%I a~2@) (%I c~6@)) (Mul
       (%I b~4@) (%I c~6@)
    )))
    :pattern ((dist_unboxed!dist_right_add.? a~2@ b~4@ c~6@))
    :qid internal_dist_unboxed!dist_right_add.?_definition
    :skolemid skolem_internal_dist_unboxed!dist_right_add.?_definition
))))

;; Function-Axioms dist_unboxed::dist_left_sub
(assert
 (fuel_bool_default fuel%dist_unboxed!dist_left_sub.)
)
(assert
 (=>
  (fuel_bool fuel%dist_unboxed!dist_left_sub.)
  (forall ((a~2@ Poly) (b~4@ Poly) (c~6@ Poly)) (!
    (= (dist_unboxed!dist_left_sub.? a~2@ b~4@ c~6@) (Mul (- (%I a~2@) (%I b~4@)) (%I c~6@)))
    :pattern ((dist_unboxed!dist_left_sub.? a~2@ b~4@ c~6@))
    :qid internal_dist_unboxed!dist_left_sub.?_definition
    :skolemid skolem_internal_dist_unboxed!dist_left_sub.?_definition
))))

;; Function-Axioms dist_unboxed::dist_right_sub
(assert
 (fuel_bool_default fuel%dist_unboxed!dist_right_sub.)
)
(assert
 (=>
  (fuel_bool fuel%dist_unboxed!dist_right_sub.)
  (forall ((a~2@ Poly) (b~4@ Poly) (c~6@ Poly)) (!
    (= (dist_unboxed!dist_right_sub.? a~2@ b~4@ c~6@) (- (Mul (%I a~2@) (%I c~6@)) (Mul
       (%I b~4@) (%I c~6@)
    )))
    :pattern ((dist_unboxed!dist_right_sub.? a~2@ b~4@ c~6@))
    :qid internal_dist_unboxed!dist_right_sub.?_definition
    :skolemid skolem_internal_dist_unboxed!dist_right_sub.?_definition
))))

;; Function-Axioms dist_unboxed::mul
(assert
 (fuel_bool_default fuel%dist_unboxed!mul.)
)
(assert
 (=>
  (fuel_bool fuel%dist_unboxed!mul.)
  (forall ((a~2@ Poly) (b~4@ Poly)) (!
    (= (dist_unboxed!mul.? a~2@ b~4@) (Mul (%I a~2@) (%I b~4@)))
    :pattern ((dist_unboxed!mul.? a~2@ b~4@))
    :qid internal_dist_unboxed!mul.?_definition
    :skolemid skolem_internal_dist_unboxed!mul.?_definition
))))

;; Function-Axioms dist_unboxed::add
(assert
 (fuel_bool_default fuel%dist_unboxed!add.)
)
(assert
 (=>
  (fuel_bool fuel%dist_unboxed!add.)
  (forall ((a~2@ Poly) (b~4@ Poly)) (!
    (= (dist_unboxed!add.? a~2@ b~4@) (+ (%I a~2@) (%I b~4@)))
    :pattern ((dist_unboxed!add.? a~2@ b~4@))
    :qid internal_dist_unboxed!add.?_definition
    :skolemid skolem_internal_dist_unboxed!add.?_definition
))))

;; Function-Axioms dist_unboxed::sub
(assert
 (fuel_bool_default fuel%dist_unboxed!sub.)
)
(assert
 (=>
  (fuel_bool fuel%dist_unboxed!sub.)
  (forall ((a~2@ Poly) (b~4@ Poly)) (!
    (= (dist_unboxed!sub.? a~2@ b~4@) (- (%I a~2@) (%I b~4@)))
    :pattern ((dist_unboxed!sub.? a~2@ b~4@))
    :qid internal_dist_unboxed!sub.?_definition
    :skolemid skolem_internal_dist_unboxed!sub.?_definition
))))

;; Function-Axioms dist_unboxed::is_le
(assert
 (fuel_bool_default fuel%dist_unboxed!is_le.)
)
(assert
 (=>
  (fuel_bool fuel%dist_unboxed!is_le.)
  (forall ((x~2@ Poly) (y~4@ Poly)) (!
    (= (dist_unboxed!is_le.? x~2@ y~4@) (<= (%I x~2@) (%I y~4@)))
    :pattern ((dist_unboxed!is_le.? x~2@ y~4@))
    :qid internal_dist_unboxed!is_le.?_definition
    :skolemid skolem_internal_dist_unboxed!is_le.?_definition
))))

;; Function-Axioms dist_unboxed::lemma_induction_helper_pos
(declare-fun ens%dist_unboxed!lemma_induction_helper_pos. (Int %%Function%% Int) Bool)
(assert
 (forall ((n~2@ Int) (f~4@ %%Function%%) (x~6@ Int)) (!
   (= (ens%dist_unboxed!lemma_induction_helper_pos. n~2@ f~4@ x~6@) (%B (%%apply%%0 f~4@
      (I x~6@)
   )))
   :pattern ((ens%dist_unboxed!lemma_induction_helper_pos. n~2@ f~4@ x~6@))
   :qid internal_ens__dist_unboxed!lemma_induction_helper_pos._definition
   :skolemid skolem_internal_ens__dist_unboxed!lemma_induction_helper_pos._definition
)))

;; Function-Axioms dist_unboxed::lemma_induction_helper_neg
(declare-fun ens%dist_unboxed!lemma_induction_helper_neg. (Int %%Function%% Int) Bool)
(assert
 (forall ((n~2@ Int) (f~4@ %%Function%%) (x~6@ Int)) (!
   (= (ens%dist_unboxed!lemma_induction_helper_neg. n~2@ f~4@ x~6@) (%B (%%apply%%0 f~4@
      (I x~6@)
   )))
   :pattern ((ens%dist_unboxed!lemma_induction_helper_neg. n~2@ f~4@ x~6@))
   :qid internal_ens__dist_unboxed!lemma_induction_helper_neg._definition
   :skolemid skolem_internal_ens__dist_unboxed!lemma_induction_helper_neg._definition
)))

;; Function-Axioms dist_unboxed::lemma_induction_helper
(declare-fun ens%dist_unboxed!lemma_induction_helper. (Int %%Function%% Int) Bool)
(assert
 (forall ((n~2@ Int) (f~4@ %%Function%%) (x~6@ Int)) (!
   (= (ens%dist_unboxed!lemma_induction_helper. n~2@ f~4@ x~6@) (%B (%%apply%%0 f~4@ (I
       x~6@
   ))))
   :pattern ((ens%dist_unboxed!lemma_induction_helper. n~2@ f~4@ x~6@))
   :qid internal_ens__dist_unboxed!lemma_induction_helper._definition
   :skolemid skolem_internal_ens__dist_unboxed!lemma_induction_helper._definition
)))

;; Function-Axioms dist_unboxed::lemma_mul_induction
(declare-fun ens%dist_unboxed!lemma_mul_induction. (%%Function%%) Bool)
(assert
 (forall ((f~2@ %%Function%%)) (!
   (= (ens%dist_unboxed!lemma_mul_induction. f~2@) (forall ((i~122$ Poly)) (!
      (=>
       (has_type i~122$ INT)
       (%B (%%apply%%0 f~2@ i~122$))
      )
      :pattern ((%%apply%%0 f~2@ i~122$))
      :qid user_dist_unboxed__lemma_mul_induction_11
      :skolemid skolem_user_dist_unboxed__lemma_mul_induction_11
   )))
   :pattern ((ens%dist_unboxed!lemma_mul_induction. f~2@))
   :qid internal_ens__dist_unboxed!lemma_mul_induction._definition
   :skolemid skolem_internal_ens__dist_unboxed!lemma_mul_induction._definition
)))

;; Function-Axioms dist_unboxed::lemma_mul_distributes
(declare-fun ens%dist_unboxed!lemma_mul_distributes. (Int) Bool)
(assert
 (forall ((no%param@ Int)) (!
   (= (ens%dist_unboxed!lemma_mul_distributes. no%param@) (and
     (forall ((x~14$ Poly) (y~16$ Poly) (z~18$ Poly)) (!
       (=>
        (and
         (has_type x~14$ INT)
         (has_type y~16$ INT)
         (has_type z~18$ INT)
        )
        (= (dist_unboxed!dist_left_add.? x~14$ y~16$ z~18$) (dist_unboxed!dist_right_add.?
          x~14$ y~16$ z~18$
       )))
       :pattern ((dist_unboxed!dist_left_add.? x~14$ y~16$ z~18$))
       :qid user_dist_unboxed__lemma_mul_distributes_12
       :skolemid skolem_user_dist_unboxed__lemma_mul_distributes_12
     ))
     (forall ((x~52$ Poly) (y~54$ Poly) (z~56$ Poly)) (!
       (=>
        (and
         (has_type x~52$ INT)
         (has_type y~54$ INT)
         (has_type z~56$ INT)
        )
        (= (dist_unboxed!dist_left_sub.? x~52$ y~54$ z~56$) (dist_unboxed!dist_right_sub.?
          x~52$ y~54$ z~56$
       )))
       :pattern ((dist_unboxed!dist_left_sub.? x~52$ y~54$ z~56$))
       :qid user_dist_unboxed__lemma_mul_distributes_13
       :skolemid skolem_user_dist_unboxed__lemma_mul_distributes_13
   ))))
   :pattern ((ens%dist_unboxed!lemma_mul_distributes. no%param@))
   :qid internal_ens__dist_unboxed!lemma_mul_distributes._definition
   :skolemid skolem_internal_ens__dist_unboxed!lemma_mul_distributes._definition
)))

;; Function-Def dist_unboxed::lemma_induction_helper
(push)
 (declare-const n~2@ Int)
 (declare-const f~4@ %%Function%%)
 (declare-const x~6@ Int)
 (assert
  fuel_defaults
 )
 (assert
  (has_type (Poly%fun%1. f~4@) (TYPE%fun%1. INT BOOL))
 )
 (assert
  (> n~2@ 0)
 )
 (assert
  (forall ((i~30$ Poly)) (!
    (=>
     (has_type i~30$ INT)
     (=>
      (and
       (<= 0 (%I i~30$))
       (< (%I i~30$) n~2@)
      )
      (%B (%%apply%%0 f~4@ i~30$))
    ))
    :pattern ((%%apply%%0 f~4@ i~30$))
    :qid user_dist_unboxed__lemma_induction_helper_20
    :skolemid skolem_user_dist_unboxed__lemma_induction_helper_20
 )))
 (assert
  (forall ((i~80$ Poly)) (!
    (=>
     (has_type i~80$ INT)
     (=>
      (and
       (>= (%I i~80$) 0)
       (%B (%%apply%%0 f~4@ i~80$))
      )
      (%B (%%apply%%0 f~4@ (I (dist_unboxed!add.? i~80$ (I n~2@)))))
    ))
    :pattern ((%%apply%%0 f~4@ i~80$) (%%apply%%0 f~4@ (I (dist_unboxed!add.? i~80$ (I n~2@)))))
    :qid user_dist_unboxed__lemma_induction_helper_21
    :skolemid skolem_user_dist_unboxed__lemma_induction_helper_21
 )))
 (assert
  (forall ((i~121$ Poly)) (!
    (=>
     (has_type i~121$ INT)
     (=>
      (and
       (< (%I i~121$) n~2@)
       (%B (%%apply%%0 f~4@ i~121$))
      )
      (%B (%%apply%%0 f~4@ (I (dist_unboxed!sub.? i~121$ (I n~2@)))))
    ))
    :pattern ((%%apply%%0 f~4@ i~121$) (%%apply%%0 f~4@ (I (dist_unboxed!sub.? i~121$ (I n~2@)))))
    :qid user_dist_unboxed__lemma_induction_helper_22
    :skolemid skolem_user_dist_unboxed__lemma_induction_helper_22
 )))
 (declare-const %%switch_label%%0 Bool)
 ;; precondition not satisfied
 (declare-const %%location_label%%0 Bool)
 ;; precondition not satisfied
 (declare-const %%location_label%%1 Bool)
 ;; postcondition not satisfied
 (declare-const %%location_label%%2 Bool)
 (declare-const %%query%% Bool)
 (assert
  (=>
   %%query%%
   (not (or
     (and
      (=>
       (>= x~6@ 0)
       (and
        (=>
         %%location_label%%0
         (req%dist_unboxed!lemma_induction_helper_pos. n~2@ f~4@ x~6@)
        )
        (=>
         (ens%dist_unboxed!lemma_induction_helper_pos. n~2@ f~4@ x~6@)
         %%switch_label%%0
      )))
      (=>
       (not (>= x~6@ 0))
       (and
        (=>
         %%location_label%%1
         (req%dist_unboxed!lemma_induction_helper_neg. n~2@ f~4@ x~6@)
        )
        (=>
         (ens%dist_unboxed!lemma_induction_helper_neg. n~2@ f~4@ x~6@)
         %%switch_label%%0
     ))))
     (and
      (not %%switch_label%%0)
      (=>
       %%location_label%%2
       (%B (%%apply%%0 f~4@ (I x~6@)))
 ))))))
 (get-info :version)
 (assert
  %%query%%
 )
 (set-option :rlimit 30000000)
 (check-sat)
 (set-option :rlimit 0)
(pop)
