// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.Var
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Linear.LinearM import Lean.Meta.Tactic.Grind.Arith.Linear.Util
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_linearExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_1_, lean_object* v_x_2_, lean_object* v_x_3_, lean_object* v_x_4_){
_start:
{
lean_object* v_ks_5_; lean_object* v_vs_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_30_; 
v_ks_5_ = lean_ctor_get(v_x_1_, 0);
v_vs_6_ = lean_ctor_get(v_x_1_, 1);
v_isSharedCheck_30_ = !lean_is_exclusive(v_x_1_);
if (v_isSharedCheck_30_ == 0)
{
v___x_8_ = v_x_1_;
v_isShared_9_ = v_isSharedCheck_30_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_vs_6_);
lean_inc(v_ks_5_);
lean_dec(v_x_1_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_30_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; uint8_t v___x_11_; 
v___x_10_ = lean_array_get_size(v_ks_5_);
v___x_11_ = lean_nat_dec_lt(v_x_2_, v___x_10_);
if (v___x_11_ == 0)
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_15_; 
lean_dec(v_x_2_);
v___x_12_ = lean_array_push(v_ks_5_, v_x_3_);
v___x_13_ = lean_array_push(v_vs_6_, v_x_4_);
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v___x_13_);
lean_ctor_set(v___x_8_, 0, v___x_12_);
v___x_15_ = v___x_8_;
goto v_reusejp_14_;
}
else
{
lean_object* v_reuseFailAlloc_16_; 
v_reuseFailAlloc_16_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_16_, 0, v___x_12_);
lean_ctor_set(v_reuseFailAlloc_16_, 1, v___x_13_);
v___x_15_ = v_reuseFailAlloc_16_;
goto v_reusejp_14_;
}
v_reusejp_14_:
{
return v___x_15_;
}
}
else
{
lean_object* v_k_x27_17_; uint8_t v___x_18_; 
v_k_x27_17_ = lean_array_fget_borrowed(v_ks_5_, v_x_2_);
v___x_18_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_3_, v_k_x27_17_);
if (v___x_18_ == 0)
{
lean_object* v___x_20_; 
if (v_isShared_9_ == 0)
{
v___x_20_ = v___x_8_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v_ks_5_);
lean_ctor_set(v_reuseFailAlloc_24_, 1, v_vs_6_);
v___x_20_ = v_reuseFailAlloc_24_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_unsigned_to_nat(1u);
v___x_22_ = lean_nat_add(v_x_2_, v___x_21_);
lean_dec(v_x_2_);
v_x_1_ = v___x_20_;
v_x_2_ = v___x_22_;
goto _start;
}
}
else
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_28_; 
v___x_25_ = lean_array_fset(v_ks_5_, v_x_2_, v_x_3_);
v___x_26_ = lean_array_fset(v_vs_6_, v_x_2_, v_x_4_);
lean_dec(v_x_2_);
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v___x_26_);
lean_ctor_set(v___x_8_, 0, v___x_25_);
v___x_28_ = v___x_8_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v___x_25_);
lean_ctor_set(v_reuseFailAlloc_29_, 1, v___x_26_);
v___x_28_ = v_reuseFailAlloc_29_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
return v___x_28_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__4___redArg(lean_object* v_n_31_, lean_object* v_k_32_, lean_object* v_v_33_){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_34_ = lean_unsigned_to_nat(0u);
v___x_35_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__4_spec__5___redArg(v_n_31_, v___x_34_, v_k_32_, v_v_33_);
return v___x_35_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg(lean_object* v_x_37_, size_t v_x_38_, size_t v_x_39_, lean_object* v_x_40_, lean_object* v_x_41_){
_start:
{
if (lean_obj_tag(v_x_37_) == 0)
{
lean_object* v_es_42_; size_t v___x_43_; size_t v___x_44_; lean_object* v_j_45_; lean_object* v___x_46_; uint8_t v___x_47_; 
v_es_42_ = lean_ctor_get(v_x_37_, 0);
v___x_43_ = ((size_t)31ULL);
v___x_44_ = lean_usize_land(v_x_38_, v___x_43_);
v_j_45_ = lean_usize_to_nat(v___x_44_);
v___x_46_ = lean_array_get_size(v_es_42_);
v___x_47_ = lean_nat_dec_lt(v_j_45_, v___x_46_);
if (v___x_47_ == 0)
{
lean_dec(v_j_45_);
lean_dec(v_x_41_);
lean_dec_ref(v_x_40_);
return v_x_37_;
}
else
{
lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_86_; 
lean_inc_ref(v_es_42_);
v_isSharedCheck_86_ = !lean_is_exclusive(v_x_37_);
if (v_isSharedCheck_86_ == 0)
{
lean_object* v_unused_87_; 
v_unused_87_ = lean_ctor_get(v_x_37_, 0);
lean_dec(v_unused_87_);
v___x_49_ = v_x_37_;
v_isShared_50_ = v_isSharedCheck_86_;
goto v_resetjp_48_;
}
else
{
lean_dec(v_x_37_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_86_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
lean_object* v_v_51_; lean_object* v___x_52_; lean_object* v_xs_x27_53_; lean_object* v___y_55_; 
v_v_51_ = lean_array_fget(v_es_42_, v_j_45_);
v___x_52_ = lean_box(0);
v_xs_x27_53_ = lean_array_fset(v_es_42_, v_j_45_, v___x_52_);
switch(lean_obj_tag(v_v_51_))
{
case 0:
{
lean_object* v_key_60_; lean_object* v_val_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_71_; 
v_key_60_ = lean_ctor_get(v_v_51_, 0);
v_val_61_ = lean_ctor_get(v_v_51_, 1);
v_isSharedCheck_71_ = !lean_is_exclusive(v_v_51_);
if (v_isSharedCheck_71_ == 0)
{
v___x_63_ = v_v_51_;
v_isShared_64_ = v_isSharedCheck_71_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_val_61_);
lean_inc(v_key_60_);
lean_dec(v_v_51_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_71_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
uint8_t v___x_65_; 
v___x_65_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_40_, v_key_60_);
if (v___x_65_ == 0)
{
lean_object* v___x_66_; lean_object* v___x_67_; 
lean_del_object(v___x_63_);
v___x_66_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_60_, v_val_61_, v_x_40_, v_x_41_);
v___x_67_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
v___y_55_ = v___x_67_;
goto v___jp_54_;
}
else
{
lean_object* v___x_69_; 
lean_dec(v_val_61_);
lean_dec(v_key_60_);
if (v_isShared_64_ == 0)
{
lean_ctor_set(v___x_63_, 1, v_x_41_);
lean_ctor_set(v___x_63_, 0, v_x_40_);
v___x_69_ = v___x_63_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v_x_40_);
lean_ctor_set(v_reuseFailAlloc_70_, 1, v_x_41_);
v___x_69_ = v_reuseFailAlloc_70_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
v___y_55_ = v___x_69_;
goto v___jp_54_;
}
}
}
}
case 1:
{
lean_object* v_node_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_84_; 
v_node_72_ = lean_ctor_get(v_v_51_, 0);
v_isSharedCheck_84_ = !lean_is_exclusive(v_v_51_);
if (v_isSharedCheck_84_ == 0)
{
v___x_74_ = v_v_51_;
v_isShared_75_ = v_isSharedCheck_84_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_node_72_);
lean_dec(v_v_51_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_84_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
size_t v___x_76_; size_t v___x_77_; size_t v___x_78_; size_t v___x_79_; lean_object* v___x_80_; lean_object* v___x_82_; 
v___x_76_ = ((size_t)5ULL);
v___x_77_ = lean_usize_shift_right(v_x_38_, v___x_76_);
v___x_78_ = ((size_t)1ULL);
v___x_79_ = lean_usize_add(v_x_39_, v___x_78_);
v___x_80_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg(v_node_72_, v___x_77_, v___x_79_, v_x_40_, v_x_41_);
if (v_isShared_75_ == 0)
{
lean_ctor_set(v___x_74_, 0, v___x_80_);
v___x_82_ = v___x_74_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v___x_80_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
v___y_55_ = v___x_82_;
goto v___jp_54_;
}
}
}
default: 
{
lean_object* v___x_85_; 
v___x_85_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_85_, 0, v_x_40_);
lean_ctor_set(v___x_85_, 1, v_x_41_);
v___y_55_ = v___x_85_;
goto v___jp_54_;
}
}
v___jp_54_:
{
lean_object* v___x_56_; lean_object* v___x_58_; 
v___x_56_ = lean_array_fset(v_xs_x27_53_, v_j_45_, v___y_55_);
lean_dec(v_j_45_);
if (v_isShared_50_ == 0)
{
lean_ctor_set(v___x_49_, 0, v___x_56_);
v___x_58_ = v___x_49_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v___x_56_);
v___x_58_ = v_reuseFailAlloc_59_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
return v___x_58_;
}
}
}
}
}
else
{
lean_object* v_ks_88_; lean_object* v_vs_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_109_; 
v_ks_88_ = lean_ctor_get(v_x_37_, 0);
v_vs_89_ = lean_ctor_get(v_x_37_, 1);
v_isSharedCheck_109_ = !lean_is_exclusive(v_x_37_);
if (v_isSharedCheck_109_ == 0)
{
v___x_91_ = v_x_37_;
v_isShared_92_ = v_isSharedCheck_109_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_vs_89_);
lean_inc(v_ks_88_);
lean_dec(v_x_37_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_109_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_94_; 
if (v_isShared_92_ == 0)
{
v___x_94_ = v___x_91_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_ks_88_);
lean_ctor_set(v_reuseFailAlloc_108_, 1, v_vs_89_);
v___x_94_ = v_reuseFailAlloc_108_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
lean_object* v_newNode_95_; uint8_t v___y_97_; size_t v___x_103_; uint8_t v___x_104_; 
v_newNode_95_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__4___redArg(v___x_94_, v_x_40_, v_x_41_);
v___x_103_ = ((size_t)7ULL);
v___x_104_ = lean_usize_dec_le(v___x_103_, v_x_39_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_105_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_95_);
v___x_106_ = lean_unsigned_to_nat(4u);
v___x_107_ = lean_nat_dec_lt(v___x_105_, v___x_106_);
lean_dec(v___x_105_);
v___y_97_ = v___x_107_;
goto v___jp_96_;
}
else
{
v___y_97_ = v___x_104_;
goto v___jp_96_;
}
v___jp_96_:
{
if (v___y_97_ == 0)
{
lean_object* v_ks_98_; lean_object* v_vs_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v_ks_98_ = lean_ctor_get(v_newNode_95_, 0);
lean_inc_ref(v_ks_98_);
v_vs_99_ = lean_ctor_get(v_newNode_95_, 1);
lean_inc_ref(v_vs_99_);
lean_dec_ref(v_newNode_95_);
v___x_100_ = lean_unsigned_to_nat(0u);
v___x_101_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__0);
v___x_102_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5___redArg(v_x_39_, v_ks_98_, v_vs_99_, v___x_100_, v___x_101_);
lean_dec_ref(v_vs_99_);
lean_dec_ref(v_ks_98_);
return v___x_102_;
}
else
{
return v_newNode_95_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5___redArg(size_t v_depth_110_, lean_object* v_keys_111_, lean_object* v_vals_112_, lean_object* v_i_113_, lean_object* v_entries_114_){
_start:
{
lean_object* v___x_115_; uint8_t v___x_116_; 
v___x_115_ = lean_array_get_size(v_keys_111_);
v___x_116_ = lean_nat_dec_lt(v_i_113_, v___x_115_);
if (v___x_116_ == 0)
{
lean_dec(v_i_113_);
return v_entries_114_;
}
else
{
lean_object* v_k_117_; lean_object* v_v_118_; uint64_t v___x_119_; size_t v_h_120_; size_t v___x_121_; lean_object* v___x_122_; size_t v___x_123_; size_t v___x_124_; size_t v___x_125_; size_t v_h_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v_k_117_ = lean_array_fget_borrowed(v_keys_111_, v_i_113_);
v_v_118_ = lean_array_fget_borrowed(v_vals_112_, v_i_113_);
v___x_119_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_117_);
v_h_120_ = lean_uint64_to_usize(v___x_119_);
v___x_121_ = ((size_t)5ULL);
v___x_122_ = lean_unsigned_to_nat(1u);
v___x_123_ = ((size_t)1ULL);
v___x_124_ = lean_usize_sub(v_depth_110_, v___x_123_);
v___x_125_ = lean_usize_mul(v___x_121_, v___x_124_);
v_h_126_ = lean_usize_shift_right(v_h_120_, v___x_125_);
v___x_127_ = lean_nat_add(v_i_113_, v___x_122_);
lean_dec(v_i_113_);
lean_inc(v_v_118_);
lean_inc(v_k_117_);
v___x_128_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg(v_entries_114_, v_h_126_, v_depth_110_, v_k_117_, v_v_118_);
v_i_113_ = v___x_127_;
v_entries_114_ = v___x_128_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_130_, lean_object* v_keys_131_, lean_object* v_vals_132_, lean_object* v_i_133_, lean_object* v_entries_134_){
_start:
{
size_t v_depth_boxed_135_; lean_object* v_res_136_; 
v_depth_boxed_135_ = lean_unbox_usize(v_depth_130_);
lean_dec(v_depth_130_);
v_res_136_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5___redArg(v_depth_boxed_135_, v_keys_131_, v_vals_132_, v_i_133_, v_entries_134_);
lean_dec_ref(v_vals_132_);
lean_dec_ref(v_keys_131_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___boxed(lean_object* v_x_137_, lean_object* v_x_138_, lean_object* v_x_139_, lean_object* v_x_140_, lean_object* v_x_141_){
_start:
{
size_t v_x_7892__boxed_142_; size_t v_x_7893__boxed_143_; lean_object* v_res_144_; 
v_x_7892__boxed_142_ = lean_unbox_usize(v_x_138_);
lean_dec(v_x_138_);
v_x_7893__boxed_143_ = lean_unbox_usize(v_x_139_);
lean_dec(v_x_139_);
v_res_144_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg(v_x_137_, v_x_7892__boxed_142_, v_x_7893__boxed_143_, v_x_140_, v_x_141_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1___redArg(lean_object* v_x_145_, lean_object* v_x_146_, lean_object* v_x_147_){
_start:
{
uint64_t v___x_148_; size_t v___x_149_; size_t v___x_150_; lean_object* v___x_151_; 
v___x_148_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_146_);
v___x_149_ = lean_uint64_to_usize(v___x_148_);
v___x_150_ = ((size_t)1ULL);
v___x_151_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg(v_x_145_, v___x_149_, v___x_150_, v_x_146_, v_x_147_);
return v___x_151_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__0(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_152_ = lean_unsigned_to_nat(32u);
v___x_153_ = lean_mk_empty_array_with_capacity(v___x_152_);
v___x_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
return v___x_154_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__1(void){
_start:
{
size_t v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_155_ = ((size_t)5ULL);
v___x_156_ = lean_unsigned_to_nat(0u);
v___x_157_ = lean_unsigned_to_nat(32u);
v___x_158_ = lean_mk_empty_array_with_capacity(v___x_157_);
v___x_159_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__0);
v___x_160_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_160_, 0, v___x_159_);
lean_ctor_set(v___x_160_, 1, v___x_158_);
lean_ctor_set(v___x_160_, 2, v___x_156_);
lean_ctor_set(v___x_160_, 3, v___x_156_);
lean_ctor_set_usize(v___x_160_, 4, v___x_155_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0(lean_object* v_a_161_, lean_object* v_e_162_, lean_object* v_size_163_, lean_object* v_s_164_){
_start:
{
lean_object* v_structs_165_; lean_object* v_typeIdOf_166_; lean_object* v_exprToStructId_167_; lean_object* v_exprToStructIdEntries_168_; lean_object* v_forbiddenNatModules_169_; lean_object* v_natStructs_170_; lean_object* v_natTypeIdOf_171_; lean_object* v_exprToNatStructId_172_; lean_object* v___x_173_; uint8_t v___x_174_; 
v_structs_165_ = lean_ctor_get(v_s_164_, 0);
v_typeIdOf_166_ = lean_ctor_get(v_s_164_, 1);
v_exprToStructId_167_ = lean_ctor_get(v_s_164_, 2);
v_exprToStructIdEntries_168_ = lean_ctor_get(v_s_164_, 3);
v_forbiddenNatModules_169_ = lean_ctor_get(v_s_164_, 4);
v_natStructs_170_ = lean_ctor_get(v_s_164_, 5);
v_natTypeIdOf_171_ = lean_ctor_get(v_s_164_, 6);
v_exprToNatStructId_172_ = lean_ctor_get(v_s_164_, 7);
v___x_173_ = lean_array_get_size(v_structs_165_);
v___x_174_ = lean_nat_dec_lt(v_a_161_, v___x_173_);
if (v___x_174_ == 0)
{
lean_dec(v_size_163_);
lean_dec_ref(v_e_162_);
return v_s_164_;
}
else
{
lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_245_; 
lean_inc_ref(v_exprToNatStructId_172_);
lean_inc_ref(v_natTypeIdOf_171_);
lean_inc_ref(v_natStructs_170_);
lean_inc_ref(v_forbiddenNatModules_169_);
lean_inc_ref(v_exprToStructIdEntries_168_);
lean_inc_ref(v_exprToStructId_167_);
lean_inc_ref(v_typeIdOf_166_);
lean_inc_ref(v_structs_165_);
v_isSharedCheck_245_ = !lean_is_exclusive(v_s_164_);
if (v_isSharedCheck_245_ == 0)
{
lean_object* v_unused_246_; lean_object* v_unused_247_; lean_object* v_unused_248_; lean_object* v_unused_249_; lean_object* v_unused_250_; lean_object* v_unused_251_; lean_object* v_unused_252_; lean_object* v_unused_253_; 
v_unused_246_ = lean_ctor_get(v_s_164_, 7);
lean_dec(v_unused_246_);
v_unused_247_ = lean_ctor_get(v_s_164_, 6);
lean_dec(v_unused_247_);
v_unused_248_ = lean_ctor_get(v_s_164_, 5);
lean_dec(v_unused_248_);
v_unused_249_ = lean_ctor_get(v_s_164_, 4);
lean_dec(v_unused_249_);
v_unused_250_ = lean_ctor_get(v_s_164_, 3);
lean_dec(v_unused_250_);
v_unused_251_ = lean_ctor_get(v_s_164_, 2);
lean_dec(v_unused_251_);
v_unused_252_ = lean_ctor_get(v_s_164_, 1);
lean_dec(v_unused_252_);
v_unused_253_ = lean_ctor_get(v_s_164_, 0);
lean_dec(v_unused_253_);
v___x_176_ = v_s_164_;
v_isShared_177_ = v_isSharedCheck_245_;
goto v_resetjp_175_;
}
else
{
lean_dec(v_s_164_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_245_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v_v_178_; lean_object* v_id_179_; lean_object* v_ringId_x3f_180_; lean_object* v_type_181_; lean_object* v_u_182_; lean_object* v_intModuleInst_183_; lean_object* v_leInst_x3f_184_; lean_object* v_ltInst_x3f_185_; lean_object* v_lawfulOrderLTInst_x3f_186_; lean_object* v_isPreorderInst_x3f_187_; lean_object* v_orderedAddInst_x3f_188_; lean_object* v_isLinearInst_x3f_189_; lean_object* v_noNatDivInst_x3f_190_; lean_object* v_ringInst_x3f_191_; lean_object* v_commRingInst_x3f_192_; lean_object* v_orderedRingInst_x3f_193_; lean_object* v_fieldInst_x3f_194_; lean_object* v_charInst_x3f_195_; lean_object* v_zero_196_; lean_object* v_ofNatZero_197_; lean_object* v_one_x3f_198_; lean_object* v_leFn_x3f_199_; lean_object* v_ltFn_x3f_200_; lean_object* v_addFn_201_; lean_object* v_zsmulFn_202_; lean_object* v_nsmulFn_203_; lean_object* v_zsmulFn_x3f_204_; lean_object* v_nsmulFn_x3f_205_; lean_object* v_homomulFn_x3f_206_; lean_object* v_subFn_207_; lean_object* v_negFn_208_; lean_object* v_vars_209_; lean_object* v_varMap_210_; lean_object* v_lowers_211_; lean_object* v_uppers_212_; lean_object* v_diseqs_213_; lean_object* v_assignment_214_; uint8_t v_caseSplits_215_; lean_object* v_conflict_x3f_216_; lean_object* v_diseqSplits_217_; lean_object* v_elimEqs_218_; lean_object* v_elimStack_219_; lean_object* v_occurs_220_; lean_object* v_ignored_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_244_; 
v_v_178_ = lean_array_fget(v_structs_165_, v_a_161_);
v_id_179_ = lean_ctor_get(v_v_178_, 0);
v_ringId_x3f_180_ = lean_ctor_get(v_v_178_, 1);
v_type_181_ = lean_ctor_get(v_v_178_, 2);
v_u_182_ = lean_ctor_get(v_v_178_, 3);
v_intModuleInst_183_ = lean_ctor_get(v_v_178_, 4);
v_leInst_x3f_184_ = lean_ctor_get(v_v_178_, 5);
v_ltInst_x3f_185_ = lean_ctor_get(v_v_178_, 6);
v_lawfulOrderLTInst_x3f_186_ = lean_ctor_get(v_v_178_, 7);
v_isPreorderInst_x3f_187_ = lean_ctor_get(v_v_178_, 8);
v_orderedAddInst_x3f_188_ = lean_ctor_get(v_v_178_, 9);
v_isLinearInst_x3f_189_ = lean_ctor_get(v_v_178_, 10);
v_noNatDivInst_x3f_190_ = lean_ctor_get(v_v_178_, 11);
v_ringInst_x3f_191_ = lean_ctor_get(v_v_178_, 12);
v_commRingInst_x3f_192_ = lean_ctor_get(v_v_178_, 13);
v_orderedRingInst_x3f_193_ = lean_ctor_get(v_v_178_, 14);
v_fieldInst_x3f_194_ = lean_ctor_get(v_v_178_, 15);
v_charInst_x3f_195_ = lean_ctor_get(v_v_178_, 16);
v_zero_196_ = lean_ctor_get(v_v_178_, 17);
v_ofNatZero_197_ = lean_ctor_get(v_v_178_, 18);
v_one_x3f_198_ = lean_ctor_get(v_v_178_, 19);
v_leFn_x3f_199_ = lean_ctor_get(v_v_178_, 20);
v_ltFn_x3f_200_ = lean_ctor_get(v_v_178_, 21);
v_addFn_201_ = lean_ctor_get(v_v_178_, 22);
v_zsmulFn_202_ = lean_ctor_get(v_v_178_, 23);
v_nsmulFn_203_ = lean_ctor_get(v_v_178_, 24);
v_zsmulFn_x3f_204_ = lean_ctor_get(v_v_178_, 25);
v_nsmulFn_x3f_205_ = lean_ctor_get(v_v_178_, 26);
v_homomulFn_x3f_206_ = lean_ctor_get(v_v_178_, 27);
v_subFn_207_ = lean_ctor_get(v_v_178_, 28);
v_negFn_208_ = lean_ctor_get(v_v_178_, 29);
v_vars_209_ = lean_ctor_get(v_v_178_, 30);
v_varMap_210_ = lean_ctor_get(v_v_178_, 31);
v_lowers_211_ = lean_ctor_get(v_v_178_, 32);
v_uppers_212_ = lean_ctor_get(v_v_178_, 33);
v_diseqs_213_ = lean_ctor_get(v_v_178_, 34);
v_assignment_214_ = lean_ctor_get(v_v_178_, 35);
v_caseSplits_215_ = lean_ctor_get_uint8(v_v_178_, sizeof(void*)*42);
v_conflict_x3f_216_ = lean_ctor_get(v_v_178_, 36);
v_diseqSplits_217_ = lean_ctor_get(v_v_178_, 37);
v_elimEqs_218_ = lean_ctor_get(v_v_178_, 38);
v_elimStack_219_ = lean_ctor_get(v_v_178_, 39);
v_occurs_220_ = lean_ctor_get(v_v_178_, 40);
v_ignored_221_ = lean_ctor_get(v_v_178_, 41);
v_isSharedCheck_244_ = !lean_is_exclusive(v_v_178_);
if (v_isSharedCheck_244_ == 0)
{
v___x_223_ = v_v_178_;
v_isShared_224_ = v_isSharedCheck_244_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_ignored_221_);
lean_inc(v_occurs_220_);
lean_inc(v_elimStack_219_);
lean_inc(v_elimEqs_218_);
lean_inc(v_diseqSplits_217_);
lean_inc(v_conflict_x3f_216_);
lean_inc(v_assignment_214_);
lean_inc(v_diseqs_213_);
lean_inc(v_uppers_212_);
lean_inc(v_lowers_211_);
lean_inc(v_varMap_210_);
lean_inc(v_vars_209_);
lean_inc(v_negFn_208_);
lean_inc(v_subFn_207_);
lean_inc(v_homomulFn_x3f_206_);
lean_inc(v_nsmulFn_x3f_205_);
lean_inc(v_zsmulFn_x3f_204_);
lean_inc(v_nsmulFn_203_);
lean_inc(v_zsmulFn_202_);
lean_inc(v_addFn_201_);
lean_inc(v_ltFn_x3f_200_);
lean_inc(v_leFn_x3f_199_);
lean_inc(v_one_x3f_198_);
lean_inc(v_ofNatZero_197_);
lean_inc(v_zero_196_);
lean_inc(v_charInst_x3f_195_);
lean_inc(v_fieldInst_x3f_194_);
lean_inc(v_orderedRingInst_x3f_193_);
lean_inc(v_commRingInst_x3f_192_);
lean_inc(v_ringInst_x3f_191_);
lean_inc(v_noNatDivInst_x3f_190_);
lean_inc(v_isLinearInst_x3f_189_);
lean_inc(v_orderedAddInst_x3f_188_);
lean_inc(v_isPreorderInst_x3f_187_);
lean_inc(v_lawfulOrderLTInst_x3f_186_);
lean_inc(v_ltInst_x3f_185_);
lean_inc(v_leInst_x3f_184_);
lean_inc(v_intModuleInst_183_);
lean_inc(v_u_182_);
lean_inc(v_type_181_);
lean_inc(v_ringId_x3f_180_);
lean_inc(v_id_179_);
lean_dec(v_v_178_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_244_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_225_; lean_object* v_xs_x27_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_238_; 
v___x_225_ = lean_box(0);
v_xs_x27_226_ = lean_array_fset(v_structs_165_, v_a_161_, v___x_225_);
lean_inc_ref(v_e_162_);
v___x_227_ = l_Lean_PersistentArray_push___redArg(v_vars_209_, v_e_162_);
v___x_228_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1___redArg(v_varMap_210_, v_e_162_, v_size_163_);
v___x_229_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__1);
v___x_230_ = l_Lean_PersistentArray_push___redArg(v_lowers_211_, v___x_229_);
v___x_231_ = l_Lean_PersistentArray_push___redArg(v_uppers_212_, v___x_229_);
v___x_232_ = l_Lean_PersistentArray_push___redArg(v_diseqs_213_, v___x_229_);
v___x_233_ = lean_box(0);
v___x_234_ = l_Lean_PersistentArray_push___redArg(v_elimEqs_218_, v___x_233_);
v___x_235_ = lean_box(1);
v___x_236_ = l_Lean_PersistentArray_push___redArg(v_occurs_220_, v___x_235_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 40, v___x_236_);
lean_ctor_set(v___x_223_, 38, v___x_234_);
lean_ctor_set(v___x_223_, 34, v___x_232_);
lean_ctor_set(v___x_223_, 33, v___x_231_);
lean_ctor_set(v___x_223_, 32, v___x_230_);
lean_ctor_set(v___x_223_, 31, v___x_228_);
lean_ctor_set(v___x_223_, 30, v___x_227_);
v___x_238_ = v___x_223_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_id_179_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v_ringId_x3f_180_);
lean_ctor_set(v_reuseFailAlloc_243_, 2, v_type_181_);
lean_ctor_set(v_reuseFailAlloc_243_, 3, v_u_182_);
lean_ctor_set(v_reuseFailAlloc_243_, 4, v_intModuleInst_183_);
lean_ctor_set(v_reuseFailAlloc_243_, 5, v_leInst_x3f_184_);
lean_ctor_set(v_reuseFailAlloc_243_, 6, v_ltInst_x3f_185_);
lean_ctor_set(v_reuseFailAlloc_243_, 7, v_lawfulOrderLTInst_x3f_186_);
lean_ctor_set(v_reuseFailAlloc_243_, 8, v_isPreorderInst_x3f_187_);
lean_ctor_set(v_reuseFailAlloc_243_, 9, v_orderedAddInst_x3f_188_);
lean_ctor_set(v_reuseFailAlloc_243_, 10, v_isLinearInst_x3f_189_);
lean_ctor_set(v_reuseFailAlloc_243_, 11, v_noNatDivInst_x3f_190_);
lean_ctor_set(v_reuseFailAlloc_243_, 12, v_ringInst_x3f_191_);
lean_ctor_set(v_reuseFailAlloc_243_, 13, v_commRingInst_x3f_192_);
lean_ctor_set(v_reuseFailAlloc_243_, 14, v_orderedRingInst_x3f_193_);
lean_ctor_set(v_reuseFailAlloc_243_, 15, v_fieldInst_x3f_194_);
lean_ctor_set(v_reuseFailAlloc_243_, 16, v_charInst_x3f_195_);
lean_ctor_set(v_reuseFailAlloc_243_, 17, v_zero_196_);
lean_ctor_set(v_reuseFailAlloc_243_, 18, v_ofNatZero_197_);
lean_ctor_set(v_reuseFailAlloc_243_, 19, v_one_x3f_198_);
lean_ctor_set(v_reuseFailAlloc_243_, 20, v_leFn_x3f_199_);
lean_ctor_set(v_reuseFailAlloc_243_, 21, v_ltFn_x3f_200_);
lean_ctor_set(v_reuseFailAlloc_243_, 22, v_addFn_201_);
lean_ctor_set(v_reuseFailAlloc_243_, 23, v_zsmulFn_202_);
lean_ctor_set(v_reuseFailAlloc_243_, 24, v_nsmulFn_203_);
lean_ctor_set(v_reuseFailAlloc_243_, 25, v_zsmulFn_x3f_204_);
lean_ctor_set(v_reuseFailAlloc_243_, 26, v_nsmulFn_x3f_205_);
lean_ctor_set(v_reuseFailAlloc_243_, 27, v_homomulFn_x3f_206_);
lean_ctor_set(v_reuseFailAlloc_243_, 28, v_subFn_207_);
lean_ctor_set(v_reuseFailAlloc_243_, 29, v_negFn_208_);
lean_ctor_set(v_reuseFailAlloc_243_, 30, v___x_227_);
lean_ctor_set(v_reuseFailAlloc_243_, 31, v___x_228_);
lean_ctor_set(v_reuseFailAlloc_243_, 32, v___x_230_);
lean_ctor_set(v_reuseFailAlloc_243_, 33, v___x_231_);
lean_ctor_set(v_reuseFailAlloc_243_, 34, v___x_232_);
lean_ctor_set(v_reuseFailAlloc_243_, 35, v_assignment_214_);
lean_ctor_set(v_reuseFailAlloc_243_, 36, v_conflict_x3f_216_);
lean_ctor_set(v_reuseFailAlloc_243_, 37, v_diseqSplits_217_);
lean_ctor_set(v_reuseFailAlloc_243_, 38, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_243_, 39, v_elimStack_219_);
lean_ctor_set(v_reuseFailAlloc_243_, 40, v___x_236_);
lean_ctor_set(v_reuseFailAlloc_243_, 41, v_ignored_221_);
lean_ctor_set_uint8(v_reuseFailAlloc_243_, sizeof(void*)*42, v_caseSplits_215_);
v___x_238_ = v_reuseFailAlloc_243_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_239_ = lean_array_fset(v_xs_x27_226_, v_a_161_, v___x_238_);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 0, v___x_239_);
v___x_241_ = v___x_176_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_239_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_typeIdOf_166_);
lean_ctor_set(v_reuseFailAlloc_242_, 2, v_exprToStructId_167_);
lean_ctor_set(v_reuseFailAlloc_242_, 3, v_exprToStructIdEntries_168_);
lean_ctor_set(v_reuseFailAlloc_242_, 4, v_forbiddenNatModules_169_);
lean_ctor_set(v_reuseFailAlloc_242_, 5, v_natStructs_170_);
lean_ctor_set(v_reuseFailAlloc_242_, 6, v_natTypeIdOf_171_);
lean_ctor_set(v_reuseFailAlloc_242_, 7, v_exprToNatStructId_172_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___boxed(lean_object* v_a_254_, lean_object* v_e_255_, lean_object* v_size_256_, lean_object* v_s_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0(v_a_254_, v_e_255_, v_size_256_, v_s_257_);
lean_dec(v_a_254_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_259_, lean_object* v_vals_260_, lean_object* v_i_261_, lean_object* v_k_262_){
_start:
{
lean_object* v___x_263_; uint8_t v___x_264_; 
v___x_263_ = lean_array_get_size(v_keys_259_);
v___x_264_ = lean_nat_dec_lt(v_i_261_, v___x_263_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; 
lean_dec(v_i_261_);
v___x_265_ = lean_box(0);
return v___x_265_;
}
else
{
lean_object* v_k_x27_266_; uint8_t v___x_267_; 
v_k_x27_266_ = lean_array_fget_borrowed(v_keys_259_, v_i_261_);
v___x_267_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_262_, v_k_x27_266_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = lean_unsigned_to_nat(1u);
v___x_269_ = lean_nat_add(v_i_261_, v___x_268_);
lean_dec(v_i_261_);
v_i_261_ = v___x_269_;
goto _start;
}
else
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = lean_array_fget_borrowed(v_vals_260_, v_i_261_);
lean_dec(v_i_261_);
lean_inc(v___x_271_);
v___x_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
return v___x_272_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_273_, lean_object* v_vals_274_, lean_object* v_i_275_, lean_object* v_k_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1___redArg(v_keys_273_, v_vals_274_, v_i_275_, v_k_276_);
lean_dec_ref(v_k_276_);
lean_dec_ref(v_vals_274_);
lean_dec_ref(v_keys_273_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0___redArg(lean_object* v_x_278_, size_t v_x_279_, lean_object* v_x_280_){
_start:
{
if (lean_obj_tag(v_x_278_) == 0)
{
lean_object* v_es_281_; lean_object* v___x_282_; size_t v___x_283_; size_t v___x_284_; lean_object* v_j_285_; lean_object* v___x_286_; 
v_es_281_ = lean_ctor_get(v_x_278_, 0);
v___x_282_ = lean_box(2);
v___x_283_ = ((size_t)31ULL);
v___x_284_ = lean_usize_land(v_x_279_, v___x_283_);
v_j_285_ = lean_usize_to_nat(v___x_284_);
v___x_286_ = lean_array_get_borrowed(v___x_282_, v_es_281_, v_j_285_);
lean_dec(v_j_285_);
switch(lean_obj_tag(v___x_286_))
{
case 0:
{
lean_object* v_key_287_; lean_object* v_val_288_; uint8_t v___x_289_; 
v_key_287_ = lean_ctor_get(v___x_286_, 0);
v_val_288_ = lean_ctor_get(v___x_286_, 1);
v___x_289_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_280_, v_key_287_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; 
v___x_290_ = lean_box(0);
return v___x_290_;
}
else
{
lean_object* v___x_291_; 
lean_inc(v_val_288_);
v___x_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_291_, 0, v_val_288_);
return v___x_291_;
}
}
case 1:
{
lean_object* v_node_292_; size_t v___x_293_; size_t v___x_294_; 
v_node_292_ = lean_ctor_get(v___x_286_, 0);
v___x_293_ = ((size_t)5ULL);
v___x_294_ = lean_usize_shift_right(v_x_279_, v___x_293_);
v_x_278_ = v_node_292_;
v_x_279_ = v___x_294_;
goto _start;
}
default: 
{
lean_object* v___x_296_; 
v___x_296_ = lean_box(0);
return v___x_296_;
}
}
}
else
{
lean_object* v_ks_297_; lean_object* v_vs_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v_ks_297_ = lean_ctor_get(v_x_278_, 0);
v_vs_298_ = lean_ctor_get(v_x_278_, 1);
v___x_299_ = lean_unsigned_to_nat(0u);
v___x_300_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1___redArg(v_ks_297_, v_vs_298_, v___x_299_, v_x_280_);
return v___x_300_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0___redArg___boxed(lean_object* v_x_301_, lean_object* v_x_302_, lean_object* v_x_303_){
_start:
{
size_t v_x_8181__boxed_304_; lean_object* v_res_305_; 
v_x_8181__boxed_304_ = lean_unbox_usize(v_x_302_);
lean_dec(v_x_302_);
v_res_305_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0___redArg(v_x_301_, v_x_8181__boxed_304_, v_x_303_);
lean_dec_ref(v_x_303_);
lean_dec_ref(v_x_301_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0___redArg(lean_object* v_x_306_, lean_object* v_x_307_){
_start:
{
uint64_t v___x_308_; size_t v___x_309_; lean_object* v___x_310_; 
v___x_308_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_307_);
v___x_309_ = lean_uint64_to_usize(v___x_308_);
v___x_310_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0___redArg(v_x_306_, v___x_309_, v_x_307_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0___redArg___boxed(lean_object* v_x_311_, lean_object* v_x_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0___redArg(v_x_311_, v_x_312_);
lean_dec_ref(v_x_312_);
lean_dec_ref(v_x_311_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar(lean_object* v_e_314_, uint8_t v_mark_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_386_; 
v_a_329_ = lean_ctor_get(v___x_328_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_386_ == 0)
{
v___x_331_ = v___x_328_;
v_isShared_332_ = v_isSharedCheck_386_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_dec(v___x_328_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_386_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v_vars_333_; lean_object* v_varMap_334_; lean_object* v___x_335_; 
v_vars_333_ = lean_ctor_get(v_a_329_, 30);
lean_inc_ref(v_vars_333_);
v_varMap_334_ = lean_ctor_get(v_a_329_, 31);
lean_inc_ref(v_varMap_334_);
lean_dec(v_a_329_);
v___x_335_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0___redArg(v_varMap_334_, v_e_314_);
lean_dec_ref(v_varMap_334_);
if (lean_obj_tag(v___x_335_) == 1)
{
lean_object* v_val_336_; lean_object* v___x_338_; 
lean_dec_ref(v_vars_333_);
lean_dec_ref(v_e_314_);
v_val_336_ = lean_ctor_get(v___x_335_, 0);
lean_inc(v_val_336_);
lean_dec_ref_known(v___x_335_, 1);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 0, v_val_336_);
v___x_338_ = v___x_331_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_val_336_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
else
{
lean_object* v_size_340_; lean_object* v___f_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
lean_dec(v___x_335_);
lean_del_object(v___x_331_);
v_size_340_ = lean_ctor_get(v_vars_333_, 2);
lean_inc_n(v_size_340_, 2);
lean_dec_ref(v_vars_333_);
lean_inc_ref(v_e_314_);
lean_inc(v_a_316_);
v___f_341_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___boxed), 4, 3);
lean_closure_set(v___f_341_, 0, v_a_316_);
lean_closure_set(v___f_341_, 1, v_e_314_);
lean_closure_set(v___f_341_, 2, v_size_340_);
v___x_342_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_343_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_342_, v___f_341_, v_a_317_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v___x_344_; 
lean_dec_ref_known(v___x_343_, 1);
lean_inc_ref(v_e_314_);
v___x_344_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg(v_e_314_, v_a_316_, v_a_317_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_368_; 
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_368_ == 0)
{
lean_object* v_unused_369_; 
v_unused_369_ = lean_ctor_get(v___x_344_, 0);
lean_dec(v_unused_369_);
v___x_346_ = v___x_344_;
v_isShared_347_ = v_isSharedCheck_368_;
goto v_resetjp_345_;
}
else
{
lean_dec(v___x_344_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_368_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
if (v_mark_315_ == 0)
{
lean_object* v___x_349_; 
lean_dec_ref(v_e_314_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 0, v_size_340_);
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_size_340_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
else
{
lean_object* v___x_351_; 
lean_del_object(v___x_346_);
v___x_351_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_342_, v_e_314_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_358_ == 0)
{
lean_object* v_unused_359_; 
v_unused_359_ = lean_ctor_get(v___x_351_, 0);
lean_dec(v_unused_359_);
v___x_353_ = v___x_351_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_dec(v___x_351_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v_size_340_);
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_size_340_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
else
{
lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_367_; 
lean_dec(v_size_340_);
v_a_360_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_367_ == 0)
{
v___x_362_ = v___x_351_;
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_351_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_365_; 
if (v_isShared_363_ == 0)
{
v___x_365_ = v___x_362_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_a_360_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
}
}
else
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_377_; 
lean_dec(v_size_340_);
lean_dec_ref(v_e_314_);
v_a_370_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_377_ == 0)
{
v___x_372_ = v___x_344_;
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_344_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_375_; 
if (v_isShared_373_ == 0)
{
v___x_375_ = v___x_372_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_a_370_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
else
{
lean_object* v_a_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_385_; 
lean_dec(v_size_340_);
lean_dec_ref(v_e_314_);
v_a_378_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_385_ == 0)
{
v___x_380_ = v___x_343_;
v_isShared_381_ = v_isSharedCheck_385_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_a_378_);
lean_dec(v___x_343_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_385_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_383_; 
if (v_isShared_381_ == 0)
{
v___x_383_ = v___x_380_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_a_378_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
}
}
}
else
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_394_; 
lean_dec_ref(v_e_314_);
v_a_387_ = lean_ctor_get(v___x_328_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_394_ == 0)
{
v___x_389_ = v___x_328_;
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_328_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_392_; 
if (v_isShared_390_ == 0)
{
v___x_392_ = v___x_389_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_387_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar___boxed(lean_object* v_e_395_, lean_object* v_mark_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
uint8_t v_mark_boxed_409_; lean_object* v_res_410_; 
v_mark_boxed_409_ = lean_unbox(v_mark_396_);
v_res_410_ = l_Lean_Meta_Grind_Arith_Linear_mkVar(v_e_395_, v_mark_boxed_409_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_);
lean_dec(v_a_407_);
lean_dec_ref(v_a_406_);
lean_dec(v_a_405_);
lean_dec_ref(v_a_404_);
lean_dec(v_a_403_);
lean_dec_ref(v_a_402_);
lean_dec(v_a_401_);
lean_dec_ref(v_a_400_);
lean_dec(v_a_399_);
lean_dec(v_a_398_);
lean_dec(v_a_397_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0(lean_object* v_00_u03b2_411_, lean_object* v_x_412_, lean_object* v_x_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0___redArg(v_x_412_, v_x_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0___boxed(lean_object* v_00_u03b2_415_, lean_object* v_x_416_, lean_object* v_x_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0(v_00_u03b2_415_, v_x_416_, v_x_417_);
lean_dec_ref(v_x_417_);
lean_dec_ref(v_x_416_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1(lean_object* v_00_u03b2_419_, lean_object* v_x_420_, lean_object* v_x_421_, lean_object* v_x_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1___redArg(v_x_420_, v_x_421_, v_x_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0(lean_object* v_00_u03b2_424_, lean_object* v_x_425_, size_t v_x_426_, lean_object* v_x_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0___redArg(v_x_425_, v_x_426_, v_x_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_429_, lean_object* v_x_430_, lean_object* v_x_431_, lean_object* v_x_432_){
_start:
{
size_t v_x_8389__boxed_433_; lean_object* v_res_434_; 
v_x_8389__boxed_433_ = lean_unbox_usize(v_x_431_);
lean_dec(v_x_431_);
v_res_434_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0(v_00_u03b2_429_, v_x_430_, v_x_8389__boxed_433_, v_x_432_);
lean_dec_ref(v_x_432_);
lean_dec_ref(v_x_430_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2(lean_object* v_00_u03b2_435_, lean_object* v_x_436_, size_t v_x_437_, size_t v_x_438_, lean_object* v_x_439_, lean_object* v_x_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg(v_x_436_, v_x_437_, v_x_438_, v_x_439_, v_x_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___boxed(lean_object* v_00_u03b2_442_, lean_object* v_x_443_, lean_object* v_x_444_, lean_object* v_x_445_, lean_object* v_x_446_, lean_object* v_x_447_){
_start:
{
size_t v_x_8400__boxed_448_; size_t v_x_8401__boxed_449_; lean_object* v_res_450_; 
v_x_8400__boxed_448_ = lean_unbox_usize(v_x_444_);
lean_dec(v_x_444_);
v_x_8401__boxed_449_ = lean_unbox_usize(v_x_445_);
lean_dec(v_x_445_);
v_res_450_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2(v_00_u03b2_442_, v_x_443_, v_x_8400__boxed_448_, v_x_8401__boxed_449_, v_x_446_, v_x_447_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_451_, lean_object* v_keys_452_, lean_object* v_vals_453_, lean_object* v_heq_454_, lean_object* v_i_455_, lean_object* v_k_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1___redArg(v_keys_452_, v_vals_453_, v_i_455_, v_k_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_458_, lean_object* v_keys_459_, lean_object* v_vals_460_, lean_object* v_heq_461_, lean_object* v_i_462_, lean_object* v_k_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1(v_00_u03b2_458_, v_keys_459_, v_vals_460_, v_heq_461_, v_i_462_, v_k_463_);
lean_dec_ref(v_k_463_);
lean_dec_ref(v_vals_460_);
lean_dec_ref(v_keys_459_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_465_, lean_object* v_n_466_, lean_object* v_k_467_, lean_object* v_v_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__4___redArg(v_n_466_, v_k_467_, v_v_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_470_, size_t v_depth_471_, lean_object* v_keys_472_, lean_object* v_vals_473_, lean_object* v_heq_474_, lean_object* v_i_475_, lean_object* v_entries_476_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5___redArg(v_depth_471_, v_keys_472_, v_vals_473_, v_i_475_, v_entries_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_478_, lean_object* v_depth_479_, lean_object* v_keys_480_, lean_object* v_vals_481_, lean_object* v_heq_482_, lean_object* v_i_483_, lean_object* v_entries_484_){
_start:
{
size_t v_depth_boxed_485_; lean_object* v_res_486_; 
v_depth_boxed_485_ = lean_unbox_usize(v_depth_479_);
lean_dec(v_depth_479_);
v_res_486_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5(v_00_u03b2_478_, v_depth_boxed_485_, v_keys_480_, v_vals_481_, v_heq_482_, v_i_483_, v_entries_484_);
lean_dec_ref(v_vals_481_);
lean_dec_ref(v_keys_480_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_487_, lean_object* v_x_488_, lean_object* v_x_489_, lean_object* v_x_490_, lean_object* v_x_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__4_spec__5___redArg(v_x_488_, v_x_489_, v_x_490_, v_x_491_);
return v___x_492_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(builtin);
}
#ifdef __cplusplus
}
#endif
