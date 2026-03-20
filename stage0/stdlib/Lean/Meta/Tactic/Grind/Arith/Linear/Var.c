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
size_t lean_usize_shift_left(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_linearExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__2;
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
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_36_; size_t v___x_37_; size_t v___x_38_; 
v___x_36_ = ((size_t)5ULL);
v___x_37_ = ((size_t)1ULL);
v___x_38_ = lean_usize_shift_left(v___x_37_, v___x_36_);
return v___x_38_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_39_; size_t v___x_40_; size_t v___x_41_; 
v___x_39_ = ((size_t)1ULL);
v___x_40_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__0);
v___x_41_ = lean_usize_sub(v___x_40_, v___x_39_);
return v___x_41_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg(lean_object* v_x_43_, size_t v_x_44_, size_t v_x_45_, lean_object* v_x_46_, lean_object* v_x_47_){
_start:
{
if (lean_obj_tag(v_x_43_) == 0)
{
lean_object* v_es_48_; size_t v___x_49_; size_t v___x_50_; size_t v___x_51_; size_t v___x_52_; lean_object* v_j_53_; lean_object* v___x_54_; uint8_t v___x_55_; 
v_es_48_ = lean_ctor_get(v_x_43_, 0);
v___x_49_ = ((size_t)5ULL);
v___x_50_ = ((size_t)1ULL);
v___x_51_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__1);
v___x_52_ = lean_usize_land(v_x_44_, v___x_51_);
v_j_53_ = lean_usize_to_nat(v___x_52_);
v___x_54_ = lean_array_get_size(v_es_48_);
v___x_55_ = lean_nat_dec_lt(v_j_53_, v___x_54_);
if (v___x_55_ == 0)
{
lean_dec(v_j_53_);
lean_dec(v_x_47_);
lean_dec_ref(v_x_46_);
return v_x_43_;
}
else
{
lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_92_; 
lean_inc_ref(v_es_48_);
v_isSharedCheck_92_ = !lean_is_exclusive(v_x_43_);
if (v_isSharedCheck_92_ == 0)
{
lean_object* v_unused_93_; 
v_unused_93_ = lean_ctor_get(v_x_43_, 0);
lean_dec(v_unused_93_);
v___x_57_ = v_x_43_;
v_isShared_58_ = v_isSharedCheck_92_;
goto v_resetjp_56_;
}
else
{
lean_dec(v_x_43_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_92_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v_v_59_; lean_object* v___x_60_; lean_object* v_xs_x27_61_; lean_object* v___y_63_; 
v_v_59_ = lean_array_fget(v_es_48_, v_j_53_);
v___x_60_ = lean_box(0);
v_xs_x27_61_ = lean_array_fset(v_es_48_, v_j_53_, v___x_60_);
switch(lean_obj_tag(v_v_59_))
{
case 0:
{
lean_object* v_key_68_; lean_object* v_val_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_79_; 
v_key_68_ = lean_ctor_get(v_v_59_, 0);
v_val_69_ = lean_ctor_get(v_v_59_, 1);
v_isSharedCheck_79_ = !lean_is_exclusive(v_v_59_);
if (v_isSharedCheck_79_ == 0)
{
v___x_71_ = v_v_59_;
v_isShared_72_ = v_isSharedCheck_79_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_val_69_);
lean_inc(v_key_68_);
lean_dec(v_v_59_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_79_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
uint8_t v___x_73_; 
v___x_73_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_46_, v_key_68_);
if (v___x_73_ == 0)
{
lean_object* v___x_74_; lean_object* v___x_75_; 
lean_del_object(v___x_71_);
v___x_74_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_68_, v_val_69_, v_x_46_, v_x_47_);
v___x_75_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
v___y_63_ = v___x_75_;
goto v___jp_62_;
}
else
{
lean_object* v___x_77_; 
lean_dec(v_val_69_);
lean_dec(v_key_68_);
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 1, v_x_47_);
lean_ctor_set(v___x_71_, 0, v_x_46_);
v___x_77_ = v___x_71_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v_x_46_);
lean_ctor_set(v_reuseFailAlloc_78_, 1, v_x_47_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
v___y_63_ = v___x_77_;
goto v___jp_62_;
}
}
}
}
case 1:
{
lean_object* v_node_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_90_; 
v_node_80_ = lean_ctor_get(v_v_59_, 0);
v_isSharedCheck_90_ = !lean_is_exclusive(v_v_59_);
if (v_isSharedCheck_90_ == 0)
{
v___x_82_ = v_v_59_;
v_isShared_83_ = v_isSharedCheck_90_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_node_80_);
lean_dec(v_v_59_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_90_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
size_t v___x_84_; size_t v___x_85_; lean_object* v___x_86_; lean_object* v___x_88_; 
v___x_84_ = lean_usize_shift_right(v_x_44_, v___x_49_);
v___x_85_ = lean_usize_add(v_x_45_, v___x_50_);
v___x_86_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg(v_node_80_, v___x_84_, v___x_85_, v_x_46_, v_x_47_);
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 0, v___x_86_);
v___x_88_ = v___x_82_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v___x_86_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
v___y_63_ = v___x_88_;
goto v___jp_62_;
}
}
}
default: 
{
lean_object* v___x_91_; 
v___x_91_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_91_, 0, v_x_46_);
lean_ctor_set(v___x_91_, 1, v_x_47_);
v___y_63_ = v___x_91_;
goto v___jp_62_;
}
}
v___jp_62_:
{
lean_object* v___x_64_; lean_object* v___x_66_; 
v___x_64_ = lean_array_fset(v_xs_x27_61_, v_j_53_, v___y_63_);
lean_dec(v_j_53_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 0, v___x_64_);
v___x_66_ = v___x_57_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v___x_64_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
return v___x_66_;
}
}
}
}
}
else
{
lean_object* v_ks_94_; lean_object* v_vs_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_115_; 
v_ks_94_ = lean_ctor_get(v_x_43_, 0);
v_vs_95_ = lean_ctor_get(v_x_43_, 1);
v_isSharedCheck_115_ = !lean_is_exclusive(v_x_43_);
if (v_isSharedCheck_115_ == 0)
{
v___x_97_ = v_x_43_;
v_isShared_98_ = v_isSharedCheck_115_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_vs_95_);
lean_inc(v_ks_94_);
lean_dec(v_x_43_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_115_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_100_; 
if (v_isShared_98_ == 0)
{
v___x_100_ = v___x_97_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_ks_94_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v_vs_95_);
v___x_100_ = v_reuseFailAlloc_114_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
lean_object* v_newNode_101_; uint8_t v___y_103_; size_t v___x_109_; uint8_t v___x_110_; 
v_newNode_101_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__4___redArg(v___x_100_, v_x_46_, v_x_47_);
v___x_109_ = ((size_t)7ULL);
v___x_110_ = lean_usize_dec_le(v___x_109_, v_x_45_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_111_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_101_);
v___x_112_ = lean_unsigned_to_nat(4u);
v___x_113_ = lean_nat_dec_lt(v___x_111_, v___x_112_);
lean_dec(v___x_111_);
v___y_103_ = v___x_113_;
goto v___jp_102_;
}
else
{
v___y_103_ = v___x_110_;
goto v___jp_102_;
}
v___jp_102_:
{
if (v___y_103_ == 0)
{
lean_object* v_ks_104_; lean_object* v_vs_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v_ks_104_ = lean_ctor_get(v_newNode_101_, 0);
lean_inc_ref(v_ks_104_);
v_vs_105_ = lean_ctor_get(v_newNode_101_, 1);
lean_inc_ref(v_vs_105_);
lean_dec_ref(v_newNode_101_);
v___x_106_ = lean_unsigned_to_nat(0u);
v___x_107_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__2);
v___x_108_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5___redArg(v_x_45_, v_ks_104_, v_vs_105_, v___x_106_, v___x_107_);
lean_dec_ref(v_vs_105_);
lean_dec_ref(v_ks_104_);
return v___x_108_;
}
else
{
return v_newNode_101_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5___redArg(size_t v_depth_116_, lean_object* v_keys_117_, lean_object* v_vals_118_, lean_object* v_i_119_, lean_object* v_entries_120_){
_start:
{
lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_121_ = lean_array_get_size(v_keys_117_);
v___x_122_ = lean_nat_dec_lt(v_i_119_, v___x_121_);
if (v___x_122_ == 0)
{
lean_dec(v_i_119_);
return v_entries_120_;
}
else
{
lean_object* v_k_123_; lean_object* v_v_124_; uint64_t v___x_125_; size_t v_h_126_; size_t v___x_127_; lean_object* v___x_128_; size_t v___x_129_; size_t v___x_130_; size_t v___x_131_; size_t v_h_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v_k_123_ = lean_array_fget_borrowed(v_keys_117_, v_i_119_);
v_v_124_ = lean_array_fget_borrowed(v_vals_118_, v_i_119_);
v___x_125_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_123_);
v_h_126_ = lean_uint64_to_usize(v___x_125_);
v___x_127_ = ((size_t)5ULL);
v___x_128_ = lean_unsigned_to_nat(1u);
v___x_129_ = ((size_t)1ULL);
v___x_130_ = lean_usize_sub(v_depth_116_, v___x_129_);
v___x_131_ = lean_usize_mul(v___x_127_, v___x_130_);
v_h_132_ = lean_usize_shift_right(v_h_126_, v___x_131_);
v___x_133_ = lean_nat_add(v_i_119_, v___x_128_);
lean_dec(v_i_119_);
lean_inc(v_v_124_);
lean_inc(v_k_123_);
v___x_134_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg(v_entries_120_, v_h_132_, v_depth_116_, v_k_123_, v_v_124_);
v_i_119_ = v___x_133_;
v_entries_120_ = v___x_134_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_136_, lean_object* v_keys_137_, lean_object* v_vals_138_, lean_object* v_i_139_, lean_object* v_entries_140_){
_start:
{
size_t v_depth_boxed_141_; lean_object* v_res_142_; 
v_depth_boxed_141_ = lean_unbox_usize(v_depth_136_);
lean_dec(v_depth_136_);
v_res_142_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5___redArg(v_depth_boxed_141_, v_keys_137_, v_vals_138_, v_i_139_, v_entries_140_);
lean_dec_ref(v_vals_138_);
lean_dec_ref(v_keys_137_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___boxed(lean_object* v_x_143_, lean_object* v_x_144_, lean_object* v_x_145_, lean_object* v_x_146_, lean_object* v_x_147_){
_start:
{
size_t v_x_8414__boxed_148_; size_t v_x_8415__boxed_149_; lean_object* v_res_150_; 
v_x_8414__boxed_148_ = lean_unbox_usize(v_x_144_);
lean_dec(v_x_144_);
v_x_8415__boxed_149_ = lean_unbox_usize(v_x_145_);
lean_dec(v_x_145_);
v_res_150_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg(v_x_143_, v_x_8414__boxed_148_, v_x_8415__boxed_149_, v_x_146_, v_x_147_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1___redArg(lean_object* v_x_151_, lean_object* v_x_152_, lean_object* v_x_153_){
_start:
{
uint64_t v___x_154_; size_t v___x_155_; size_t v___x_156_; lean_object* v___x_157_; 
v___x_154_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_152_);
v___x_155_ = lean_uint64_to_usize(v___x_154_);
v___x_156_ = ((size_t)1ULL);
v___x_157_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg(v_x_151_, v___x_155_, v___x_156_, v_x_152_, v_x_153_);
return v___x_157_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__0(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = lean_unsigned_to_nat(32u);
v___x_159_ = lean_mk_empty_array_with_capacity(v___x_158_);
v___x_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
return v___x_160_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__1(void){
_start:
{
size_t v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_161_ = ((size_t)5ULL);
v___x_162_ = lean_unsigned_to_nat(0u);
v___x_163_ = lean_unsigned_to_nat(32u);
v___x_164_ = lean_mk_empty_array_with_capacity(v___x_163_);
v___x_165_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__0);
v___x_166_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_166_, 0, v___x_165_);
lean_ctor_set(v___x_166_, 1, v___x_164_);
lean_ctor_set(v___x_166_, 2, v___x_162_);
lean_ctor_set(v___x_166_, 3, v___x_162_);
lean_ctor_set_usize(v___x_166_, 4, v___x_161_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0(lean_object* v_a_167_, lean_object* v_e_168_, lean_object* v_size_169_, lean_object* v_s_170_){
_start:
{
lean_object* v_structs_171_; lean_object* v_typeIdOf_172_; lean_object* v_exprToStructId_173_; lean_object* v_exprToStructIdEntries_174_; lean_object* v_forbiddenNatModules_175_; lean_object* v_natStructs_176_; lean_object* v_natTypeIdOf_177_; lean_object* v_exprToNatStructId_178_; lean_object* v___x_179_; uint8_t v___x_180_; 
v_structs_171_ = lean_ctor_get(v_s_170_, 0);
v_typeIdOf_172_ = lean_ctor_get(v_s_170_, 1);
v_exprToStructId_173_ = lean_ctor_get(v_s_170_, 2);
v_exprToStructIdEntries_174_ = lean_ctor_get(v_s_170_, 3);
v_forbiddenNatModules_175_ = lean_ctor_get(v_s_170_, 4);
v_natStructs_176_ = lean_ctor_get(v_s_170_, 5);
v_natTypeIdOf_177_ = lean_ctor_get(v_s_170_, 6);
v_exprToNatStructId_178_ = lean_ctor_get(v_s_170_, 7);
v___x_179_ = lean_array_get_size(v_structs_171_);
v___x_180_ = lean_nat_dec_lt(v_a_167_, v___x_179_);
if (v___x_180_ == 0)
{
lean_dec(v_size_169_);
lean_dec_ref(v_e_168_);
return v_s_170_;
}
else
{
lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_251_; 
lean_inc_ref(v_exprToNatStructId_178_);
lean_inc_ref(v_natTypeIdOf_177_);
lean_inc_ref(v_natStructs_176_);
lean_inc_ref(v_forbiddenNatModules_175_);
lean_inc_ref(v_exprToStructIdEntries_174_);
lean_inc_ref(v_exprToStructId_173_);
lean_inc_ref(v_typeIdOf_172_);
lean_inc_ref(v_structs_171_);
v_isSharedCheck_251_ = !lean_is_exclusive(v_s_170_);
if (v_isSharedCheck_251_ == 0)
{
lean_object* v_unused_252_; lean_object* v_unused_253_; lean_object* v_unused_254_; lean_object* v_unused_255_; lean_object* v_unused_256_; lean_object* v_unused_257_; lean_object* v_unused_258_; lean_object* v_unused_259_; 
v_unused_252_ = lean_ctor_get(v_s_170_, 7);
lean_dec(v_unused_252_);
v_unused_253_ = lean_ctor_get(v_s_170_, 6);
lean_dec(v_unused_253_);
v_unused_254_ = lean_ctor_get(v_s_170_, 5);
lean_dec(v_unused_254_);
v_unused_255_ = lean_ctor_get(v_s_170_, 4);
lean_dec(v_unused_255_);
v_unused_256_ = lean_ctor_get(v_s_170_, 3);
lean_dec(v_unused_256_);
v_unused_257_ = lean_ctor_get(v_s_170_, 2);
lean_dec(v_unused_257_);
v_unused_258_ = lean_ctor_get(v_s_170_, 1);
lean_dec(v_unused_258_);
v_unused_259_ = lean_ctor_get(v_s_170_, 0);
lean_dec(v_unused_259_);
v___x_182_ = v_s_170_;
v_isShared_183_ = v_isSharedCheck_251_;
goto v_resetjp_181_;
}
else
{
lean_dec(v_s_170_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_251_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v_v_184_; lean_object* v_id_185_; lean_object* v_ringId_x3f_186_; lean_object* v_type_187_; lean_object* v_u_188_; lean_object* v_intModuleInst_189_; lean_object* v_leInst_x3f_190_; lean_object* v_ltInst_x3f_191_; lean_object* v_lawfulOrderLTInst_x3f_192_; lean_object* v_isPreorderInst_x3f_193_; lean_object* v_orderedAddInst_x3f_194_; lean_object* v_isLinearInst_x3f_195_; lean_object* v_noNatDivInst_x3f_196_; lean_object* v_ringInst_x3f_197_; lean_object* v_commRingInst_x3f_198_; lean_object* v_orderedRingInst_x3f_199_; lean_object* v_fieldInst_x3f_200_; lean_object* v_charInst_x3f_201_; lean_object* v_zero_202_; lean_object* v_ofNatZero_203_; lean_object* v_one_x3f_204_; lean_object* v_leFn_x3f_205_; lean_object* v_ltFn_x3f_206_; lean_object* v_addFn_207_; lean_object* v_zsmulFn_208_; lean_object* v_nsmulFn_209_; lean_object* v_zsmulFn_x3f_210_; lean_object* v_nsmulFn_x3f_211_; lean_object* v_homomulFn_x3f_212_; lean_object* v_subFn_213_; lean_object* v_negFn_214_; lean_object* v_vars_215_; lean_object* v_varMap_216_; lean_object* v_lowers_217_; lean_object* v_uppers_218_; lean_object* v_diseqs_219_; lean_object* v_assignment_220_; uint8_t v_caseSplits_221_; lean_object* v_conflict_x3f_222_; lean_object* v_diseqSplits_223_; lean_object* v_elimEqs_224_; lean_object* v_elimStack_225_; lean_object* v_occurs_226_; lean_object* v_ignored_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_250_; 
v_v_184_ = lean_array_fget(v_structs_171_, v_a_167_);
v_id_185_ = lean_ctor_get(v_v_184_, 0);
v_ringId_x3f_186_ = lean_ctor_get(v_v_184_, 1);
v_type_187_ = lean_ctor_get(v_v_184_, 2);
v_u_188_ = lean_ctor_get(v_v_184_, 3);
v_intModuleInst_189_ = lean_ctor_get(v_v_184_, 4);
v_leInst_x3f_190_ = lean_ctor_get(v_v_184_, 5);
v_ltInst_x3f_191_ = lean_ctor_get(v_v_184_, 6);
v_lawfulOrderLTInst_x3f_192_ = lean_ctor_get(v_v_184_, 7);
v_isPreorderInst_x3f_193_ = lean_ctor_get(v_v_184_, 8);
v_orderedAddInst_x3f_194_ = lean_ctor_get(v_v_184_, 9);
v_isLinearInst_x3f_195_ = lean_ctor_get(v_v_184_, 10);
v_noNatDivInst_x3f_196_ = lean_ctor_get(v_v_184_, 11);
v_ringInst_x3f_197_ = lean_ctor_get(v_v_184_, 12);
v_commRingInst_x3f_198_ = lean_ctor_get(v_v_184_, 13);
v_orderedRingInst_x3f_199_ = lean_ctor_get(v_v_184_, 14);
v_fieldInst_x3f_200_ = lean_ctor_get(v_v_184_, 15);
v_charInst_x3f_201_ = lean_ctor_get(v_v_184_, 16);
v_zero_202_ = lean_ctor_get(v_v_184_, 17);
v_ofNatZero_203_ = lean_ctor_get(v_v_184_, 18);
v_one_x3f_204_ = lean_ctor_get(v_v_184_, 19);
v_leFn_x3f_205_ = lean_ctor_get(v_v_184_, 20);
v_ltFn_x3f_206_ = lean_ctor_get(v_v_184_, 21);
v_addFn_207_ = lean_ctor_get(v_v_184_, 22);
v_zsmulFn_208_ = lean_ctor_get(v_v_184_, 23);
v_nsmulFn_209_ = lean_ctor_get(v_v_184_, 24);
v_zsmulFn_x3f_210_ = lean_ctor_get(v_v_184_, 25);
v_nsmulFn_x3f_211_ = lean_ctor_get(v_v_184_, 26);
v_homomulFn_x3f_212_ = lean_ctor_get(v_v_184_, 27);
v_subFn_213_ = lean_ctor_get(v_v_184_, 28);
v_negFn_214_ = lean_ctor_get(v_v_184_, 29);
v_vars_215_ = lean_ctor_get(v_v_184_, 30);
v_varMap_216_ = lean_ctor_get(v_v_184_, 31);
v_lowers_217_ = lean_ctor_get(v_v_184_, 32);
v_uppers_218_ = lean_ctor_get(v_v_184_, 33);
v_diseqs_219_ = lean_ctor_get(v_v_184_, 34);
v_assignment_220_ = lean_ctor_get(v_v_184_, 35);
v_caseSplits_221_ = lean_ctor_get_uint8(v_v_184_, sizeof(void*)*42);
v_conflict_x3f_222_ = lean_ctor_get(v_v_184_, 36);
v_diseqSplits_223_ = lean_ctor_get(v_v_184_, 37);
v_elimEqs_224_ = lean_ctor_get(v_v_184_, 38);
v_elimStack_225_ = lean_ctor_get(v_v_184_, 39);
v_occurs_226_ = lean_ctor_get(v_v_184_, 40);
v_ignored_227_ = lean_ctor_get(v_v_184_, 41);
v_isSharedCheck_250_ = !lean_is_exclusive(v_v_184_);
if (v_isSharedCheck_250_ == 0)
{
v___x_229_ = v_v_184_;
v_isShared_230_ = v_isSharedCheck_250_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_ignored_227_);
lean_inc(v_occurs_226_);
lean_inc(v_elimStack_225_);
lean_inc(v_elimEqs_224_);
lean_inc(v_diseqSplits_223_);
lean_inc(v_conflict_x3f_222_);
lean_inc(v_assignment_220_);
lean_inc(v_diseqs_219_);
lean_inc(v_uppers_218_);
lean_inc(v_lowers_217_);
lean_inc(v_varMap_216_);
lean_inc(v_vars_215_);
lean_inc(v_negFn_214_);
lean_inc(v_subFn_213_);
lean_inc(v_homomulFn_x3f_212_);
lean_inc(v_nsmulFn_x3f_211_);
lean_inc(v_zsmulFn_x3f_210_);
lean_inc(v_nsmulFn_209_);
lean_inc(v_zsmulFn_208_);
lean_inc(v_addFn_207_);
lean_inc(v_ltFn_x3f_206_);
lean_inc(v_leFn_x3f_205_);
lean_inc(v_one_x3f_204_);
lean_inc(v_ofNatZero_203_);
lean_inc(v_zero_202_);
lean_inc(v_charInst_x3f_201_);
lean_inc(v_fieldInst_x3f_200_);
lean_inc(v_orderedRingInst_x3f_199_);
lean_inc(v_commRingInst_x3f_198_);
lean_inc(v_ringInst_x3f_197_);
lean_inc(v_noNatDivInst_x3f_196_);
lean_inc(v_isLinearInst_x3f_195_);
lean_inc(v_orderedAddInst_x3f_194_);
lean_inc(v_isPreorderInst_x3f_193_);
lean_inc(v_lawfulOrderLTInst_x3f_192_);
lean_inc(v_ltInst_x3f_191_);
lean_inc(v_leInst_x3f_190_);
lean_inc(v_intModuleInst_189_);
lean_inc(v_u_188_);
lean_inc(v_type_187_);
lean_inc(v_ringId_x3f_186_);
lean_inc(v_id_185_);
lean_dec(v_v_184_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_250_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_231_; lean_object* v_xs_x27_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_244_; 
v___x_231_ = lean_box(0);
v_xs_x27_232_ = lean_array_fset(v_structs_171_, v_a_167_, v___x_231_);
lean_inc_ref(v_e_168_);
v___x_233_ = l_Lean_PersistentArray_push___redArg(v_vars_215_, v_e_168_);
v___x_234_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1___redArg(v_varMap_216_, v_e_168_, v_size_169_);
v___x_235_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__1);
v___x_236_ = l_Lean_PersistentArray_push___redArg(v_lowers_217_, v___x_235_);
v___x_237_ = l_Lean_PersistentArray_push___redArg(v_uppers_218_, v___x_235_);
v___x_238_ = l_Lean_PersistentArray_push___redArg(v_diseqs_219_, v___x_235_);
v___x_239_ = lean_box(0);
v___x_240_ = l_Lean_PersistentArray_push___redArg(v_elimEqs_224_, v___x_239_);
v___x_241_ = lean_box(1);
v___x_242_ = l_Lean_PersistentArray_push___redArg(v_occurs_226_, v___x_241_);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 40, v___x_242_);
lean_ctor_set(v___x_229_, 38, v___x_240_);
lean_ctor_set(v___x_229_, 34, v___x_238_);
lean_ctor_set(v___x_229_, 33, v___x_237_);
lean_ctor_set(v___x_229_, 32, v___x_236_);
lean_ctor_set(v___x_229_, 31, v___x_234_);
lean_ctor_set(v___x_229_, 30, v___x_233_);
v___x_244_ = v___x_229_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_id_185_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v_ringId_x3f_186_);
lean_ctor_set(v_reuseFailAlloc_249_, 2, v_type_187_);
lean_ctor_set(v_reuseFailAlloc_249_, 3, v_u_188_);
lean_ctor_set(v_reuseFailAlloc_249_, 4, v_intModuleInst_189_);
lean_ctor_set(v_reuseFailAlloc_249_, 5, v_leInst_x3f_190_);
lean_ctor_set(v_reuseFailAlloc_249_, 6, v_ltInst_x3f_191_);
lean_ctor_set(v_reuseFailAlloc_249_, 7, v_lawfulOrderLTInst_x3f_192_);
lean_ctor_set(v_reuseFailAlloc_249_, 8, v_isPreorderInst_x3f_193_);
lean_ctor_set(v_reuseFailAlloc_249_, 9, v_orderedAddInst_x3f_194_);
lean_ctor_set(v_reuseFailAlloc_249_, 10, v_isLinearInst_x3f_195_);
lean_ctor_set(v_reuseFailAlloc_249_, 11, v_noNatDivInst_x3f_196_);
lean_ctor_set(v_reuseFailAlloc_249_, 12, v_ringInst_x3f_197_);
lean_ctor_set(v_reuseFailAlloc_249_, 13, v_commRingInst_x3f_198_);
lean_ctor_set(v_reuseFailAlloc_249_, 14, v_orderedRingInst_x3f_199_);
lean_ctor_set(v_reuseFailAlloc_249_, 15, v_fieldInst_x3f_200_);
lean_ctor_set(v_reuseFailAlloc_249_, 16, v_charInst_x3f_201_);
lean_ctor_set(v_reuseFailAlloc_249_, 17, v_zero_202_);
lean_ctor_set(v_reuseFailAlloc_249_, 18, v_ofNatZero_203_);
lean_ctor_set(v_reuseFailAlloc_249_, 19, v_one_x3f_204_);
lean_ctor_set(v_reuseFailAlloc_249_, 20, v_leFn_x3f_205_);
lean_ctor_set(v_reuseFailAlloc_249_, 21, v_ltFn_x3f_206_);
lean_ctor_set(v_reuseFailAlloc_249_, 22, v_addFn_207_);
lean_ctor_set(v_reuseFailAlloc_249_, 23, v_zsmulFn_208_);
lean_ctor_set(v_reuseFailAlloc_249_, 24, v_nsmulFn_209_);
lean_ctor_set(v_reuseFailAlloc_249_, 25, v_zsmulFn_x3f_210_);
lean_ctor_set(v_reuseFailAlloc_249_, 26, v_nsmulFn_x3f_211_);
lean_ctor_set(v_reuseFailAlloc_249_, 27, v_homomulFn_x3f_212_);
lean_ctor_set(v_reuseFailAlloc_249_, 28, v_subFn_213_);
lean_ctor_set(v_reuseFailAlloc_249_, 29, v_negFn_214_);
lean_ctor_set(v_reuseFailAlloc_249_, 30, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_249_, 31, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_249_, 32, v___x_236_);
lean_ctor_set(v_reuseFailAlloc_249_, 33, v___x_237_);
lean_ctor_set(v_reuseFailAlloc_249_, 34, v___x_238_);
lean_ctor_set(v_reuseFailAlloc_249_, 35, v_assignment_220_);
lean_ctor_set(v_reuseFailAlloc_249_, 36, v_conflict_x3f_222_);
lean_ctor_set(v_reuseFailAlloc_249_, 37, v_diseqSplits_223_);
lean_ctor_set(v_reuseFailAlloc_249_, 38, v___x_240_);
lean_ctor_set(v_reuseFailAlloc_249_, 39, v_elimStack_225_);
lean_ctor_set(v_reuseFailAlloc_249_, 40, v___x_242_);
lean_ctor_set(v_reuseFailAlloc_249_, 41, v_ignored_227_);
lean_ctor_set_uint8(v_reuseFailAlloc_249_, sizeof(void*)*42, v_caseSplits_221_);
v___x_244_ = v_reuseFailAlloc_249_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
lean_object* v___x_245_; lean_object* v___x_247_; 
v___x_245_ = lean_array_fset(v_xs_x27_232_, v_a_167_, v___x_244_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 0, v___x_245_);
v___x_247_ = v___x_182_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_245_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v_typeIdOf_172_);
lean_ctor_set(v_reuseFailAlloc_248_, 2, v_exprToStructId_173_);
lean_ctor_set(v_reuseFailAlloc_248_, 3, v_exprToStructIdEntries_174_);
lean_ctor_set(v_reuseFailAlloc_248_, 4, v_forbiddenNatModules_175_);
lean_ctor_set(v_reuseFailAlloc_248_, 5, v_natStructs_176_);
lean_ctor_set(v_reuseFailAlloc_248_, 6, v_natTypeIdOf_177_);
lean_ctor_set(v_reuseFailAlloc_248_, 7, v_exprToNatStructId_178_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___boxed(lean_object* v_a_260_, lean_object* v_e_261_, lean_object* v_size_262_, lean_object* v_s_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0(v_a_260_, v_e_261_, v_size_262_, v_s_263_);
lean_dec(v_a_260_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_265_, lean_object* v_vals_266_, lean_object* v_i_267_, lean_object* v_k_268_){
_start:
{
lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_269_ = lean_array_get_size(v_keys_265_);
v___x_270_ = lean_nat_dec_lt(v_i_267_, v___x_269_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; 
lean_dec(v_i_267_);
v___x_271_ = lean_box(0);
return v___x_271_;
}
else
{
lean_object* v_k_x27_272_; uint8_t v___x_273_; 
v_k_x27_272_ = lean_array_fget_borrowed(v_keys_265_, v_i_267_);
v___x_273_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_268_, v_k_x27_272_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = lean_unsigned_to_nat(1u);
v___x_275_ = lean_nat_add(v_i_267_, v___x_274_);
lean_dec(v_i_267_);
v_i_267_ = v___x_275_;
goto _start;
}
else
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_array_fget_borrowed(v_vals_266_, v_i_267_);
lean_dec(v_i_267_);
lean_inc(v___x_277_);
v___x_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
return v___x_278_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_279_, lean_object* v_vals_280_, lean_object* v_i_281_, lean_object* v_k_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1___redArg(v_keys_279_, v_vals_280_, v_i_281_, v_k_282_);
lean_dec_ref(v_k_282_);
lean_dec_ref(v_vals_280_);
lean_dec_ref(v_keys_279_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0___redArg(lean_object* v_x_284_, size_t v_x_285_, lean_object* v_x_286_){
_start:
{
if (lean_obj_tag(v_x_284_) == 0)
{
lean_object* v_es_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_308_; 
v_es_287_ = lean_ctor_get(v_x_284_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v_x_284_);
if (v_isSharedCheck_308_ == 0)
{
v___x_289_ = v_x_284_;
v_isShared_290_ = v_isSharedCheck_308_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_es_287_);
lean_dec(v_x_284_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_308_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_291_; size_t v___x_292_; size_t v___x_293_; size_t v___x_294_; lean_object* v_j_295_; lean_object* v___x_296_; 
v___x_291_ = lean_box(2);
v___x_292_ = ((size_t)5ULL);
v___x_293_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__1);
v___x_294_ = lean_usize_land(v_x_285_, v___x_293_);
v_j_295_ = lean_usize_to_nat(v___x_294_);
v___x_296_ = lean_array_get(v___x_291_, v_es_287_, v_j_295_);
lean_dec(v_j_295_);
lean_dec_ref(v_es_287_);
switch(lean_obj_tag(v___x_296_))
{
case 0:
{
lean_object* v_key_297_; lean_object* v_val_298_; uint8_t v___x_299_; 
v_key_297_ = lean_ctor_get(v___x_296_, 0);
lean_inc(v_key_297_);
v_val_298_ = lean_ctor_get(v___x_296_, 1);
lean_inc(v_val_298_);
lean_dec_ref(v___x_296_);
v___x_299_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_286_, v_key_297_);
lean_dec(v_key_297_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; 
lean_dec(v_val_298_);
lean_del_object(v___x_289_);
v___x_300_ = lean_box(0);
return v___x_300_;
}
else
{
lean_object* v___x_302_; 
if (v_isShared_290_ == 0)
{
lean_ctor_set_tag(v___x_289_, 1);
lean_ctor_set(v___x_289_, 0, v_val_298_);
v___x_302_ = v___x_289_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_val_298_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
case 1:
{
lean_object* v_node_304_; size_t v___x_305_; 
lean_del_object(v___x_289_);
v_node_304_ = lean_ctor_get(v___x_296_, 0);
lean_inc(v_node_304_);
lean_dec_ref(v___x_296_);
v___x_305_ = lean_usize_shift_right(v_x_285_, v___x_292_);
v_x_284_ = v_node_304_;
v_x_285_ = v___x_305_;
goto _start;
}
default: 
{
lean_object* v___x_307_; 
lean_del_object(v___x_289_);
v___x_307_ = lean_box(0);
return v___x_307_;
}
}
}
}
else
{
lean_object* v_ks_309_; lean_object* v_vs_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v_ks_309_ = lean_ctor_get(v_x_284_, 0);
lean_inc_ref(v_ks_309_);
v_vs_310_ = lean_ctor_get(v_x_284_, 1);
lean_inc_ref(v_vs_310_);
lean_dec_ref(v_x_284_);
v___x_311_ = lean_unsigned_to_nat(0u);
v___x_312_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1___redArg(v_ks_309_, v_vs_310_, v___x_311_, v_x_286_);
lean_dec_ref(v_vs_310_);
lean_dec_ref(v_ks_309_);
return v___x_312_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0___redArg___boxed(lean_object* v_x_313_, lean_object* v_x_314_, lean_object* v_x_315_){
_start:
{
size_t v_x_8718__boxed_316_; lean_object* v_res_317_; 
v_x_8718__boxed_316_ = lean_unbox_usize(v_x_314_);
lean_dec(v_x_314_);
v_res_317_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0___redArg(v_x_313_, v_x_8718__boxed_316_, v_x_315_);
lean_dec_ref(v_x_315_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0___redArg(lean_object* v_x_318_, lean_object* v_x_319_){
_start:
{
uint64_t v___x_320_; size_t v___x_321_; lean_object* v___x_322_; 
v___x_320_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_319_);
v___x_321_ = lean_uint64_to_usize(v___x_320_);
v___x_322_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0___redArg(v_x_318_, v___x_321_, v_x_319_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0___redArg___boxed(lean_object* v_x_323_, lean_object* v_x_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0___redArg(v_x_323_, v_x_324_);
lean_dec_ref(v_x_324_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar(lean_object* v_e_326_, uint8_t v_mark_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_);
if (lean_obj_tag(v___x_340_) == 0)
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_398_; 
v_a_341_ = lean_ctor_get(v___x_340_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_398_ == 0)
{
v___x_343_ = v___x_340_;
v_isShared_344_ = v_isSharedCheck_398_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_340_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_398_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v_vars_345_; lean_object* v_varMap_346_; lean_object* v___x_347_; 
v_vars_345_ = lean_ctor_get(v_a_341_, 30);
lean_inc_ref(v_vars_345_);
v_varMap_346_ = lean_ctor_get(v_a_341_, 31);
lean_inc_ref(v_varMap_346_);
lean_dec(v_a_341_);
v___x_347_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0___redArg(v_varMap_346_, v_e_326_);
if (lean_obj_tag(v___x_347_) == 1)
{
lean_object* v_val_348_; lean_object* v___x_350_; 
lean_dec_ref(v_vars_345_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec(v_a_330_);
lean_dec(v_a_329_);
lean_dec(v_a_328_);
lean_dec_ref(v_e_326_);
v_val_348_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_val_348_);
lean_dec_ref(v___x_347_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 0, v_val_348_);
v___x_350_ = v___x_343_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_val_348_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
else
{
lean_object* v_size_352_; lean_object* v___f_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
lean_dec(v___x_347_);
lean_del_object(v___x_343_);
v_size_352_ = lean_ctor_get(v_vars_345_, 2);
lean_inc(v_size_352_);
lean_dec_ref(v_vars_345_);
lean_inc(v_size_352_);
lean_inc_ref(v_e_326_);
lean_inc(v_a_328_);
v___f_353_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___boxed), 4, 3);
lean_closure_set(v___f_353_, 0, v_a_328_);
lean_closure_set(v___f_353_, 1, v_e_326_);
lean_closure_set(v___f_353_, 2, v_size_352_);
v___x_354_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_355_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_354_, v___f_353_, v_a_329_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v___x_356_; 
lean_dec_ref(v___x_355_);
lean_inc_ref(v_e_326_);
v___x_356_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId(v_e_326_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_380_; 
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_380_ == 0)
{
lean_object* v_unused_381_; 
v_unused_381_ = lean_ctor_get(v___x_356_, 0);
lean_dec(v_unused_381_);
v___x_358_ = v___x_356_;
v_isShared_359_ = v_isSharedCheck_380_;
goto v_resetjp_357_;
}
else
{
lean_dec(v___x_356_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_380_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
if (v_mark_327_ == 0)
{
lean_object* v___x_361_; 
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec(v_a_330_);
lean_dec(v_a_329_);
lean_dec_ref(v_e_326_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v_size_352_);
v___x_361_ = v___x_358_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_size_352_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
else
{
lean_object* v___x_363_; 
lean_del_object(v___x_358_);
v___x_363_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_354_, v_e_326_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_370_; 
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_370_ == 0)
{
lean_object* v_unused_371_; 
v_unused_371_ = lean_ctor_get(v___x_363_, 0);
lean_dec(v_unused_371_);
v___x_365_ = v___x_363_;
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
else
{
lean_dec(v___x_363_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_368_; 
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 0, v_size_352_);
v___x_368_ = v___x_365_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_size_352_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
else
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_379_; 
lean_dec(v_size_352_);
v_a_372_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_379_ == 0)
{
v___x_374_ = v___x_363_;
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_363_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_a_372_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
}
}
else
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_389_; 
lean_dec(v_size_352_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec(v_a_330_);
lean_dec(v_a_329_);
lean_dec_ref(v_e_326_);
v_a_382_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_389_ == 0)
{
v___x_384_ = v___x_356_;
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_356_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
if (v_isShared_385_ == 0)
{
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_a_382_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
else
{
lean_object* v_a_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_397_; 
lean_dec(v_size_352_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec(v_a_330_);
lean_dec(v_a_329_);
lean_dec(v_a_328_);
lean_dec_ref(v_e_326_);
v_a_390_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_397_ == 0)
{
v___x_392_ = v___x_355_;
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_a_390_);
lean_dec(v___x_355_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
if (v_isShared_393_ == 0)
{
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_a_390_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
}
}
else
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec(v_a_330_);
lean_dec(v_a_329_);
lean_dec(v_a_328_);
lean_dec_ref(v_e_326_);
v_a_399_ = lean_ctor_get(v___x_340_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v___x_340_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_340_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_399_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar___boxed(lean_object* v_e_407_, lean_object* v_mark_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_){
_start:
{
uint8_t v_mark_boxed_421_; lean_object* v_res_422_; 
v_mark_boxed_421_ = lean_unbox(v_mark_408_);
v_res_422_ = l_Lean_Meta_Grind_Arith_Linear_mkVar(v_e_407_, v_mark_boxed_421_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0(lean_object* v_00_u03b2_423_, lean_object* v_x_424_, lean_object* v_x_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0___redArg(v_x_424_, v_x_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0___boxed(lean_object* v_00_u03b2_427_, lean_object* v_x_428_, lean_object* v_x_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0(v_00_u03b2_427_, v_x_428_, v_x_429_);
lean_dec_ref(v_x_429_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1(lean_object* v_00_u03b2_431_, lean_object* v_x_432_, lean_object* v_x_433_, lean_object* v_x_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1___redArg(v_x_432_, v_x_433_, v_x_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0(lean_object* v_00_u03b2_436_, lean_object* v_x_437_, size_t v_x_438_, lean_object* v_x_439_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0___redArg(v_x_437_, v_x_438_, v_x_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_441_, lean_object* v_x_442_, lean_object* v_x_443_, lean_object* v_x_444_){
_start:
{
size_t v_x_8973__boxed_445_; lean_object* v_res_446_; 
v_x_8973__boxed_445_ = lean_unbox_usize(v_x_443_);
lean_dec(v_x_443_);
v_res_446_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0(v_00_u03b2_441_, v_x_442_, v_x_8973__boxed_445_, v_x_444_);
lean_dec_ref(v_x_444_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2(lean_object* v_00_u03b2_447_, lean_object* v_x_448_, size_t v_x_449_, size_t v_x_450_, lean_object* v_x_451_, lean_object* v_x_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg(v_x_448_, v_x_449_, v_x_450_, v_x_451_, v_x_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___boxed(lean_object* v_00_u03b2_454_, lean_object* v_x_455_, lean_object* v_x_456_, lean_object* v_x_457_, lean_object* v_x_458_, lean_object* v_x_459_){
_start:
{
size_t v_x_8984__boxed_460_; size_t v_x_8985__boxed_461_; lean_object* v_res_462_; 
v_x_8984__boxed_460_ = lean_unbox_usize(v_x_456_);
lean_dec(v_x_456_);
v_x_8985__boxed_461_ = lean_unbox_usize(v_x_457_);
lean_dec(v_x_457_);
v_res_462_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2(v_00_u03b2_454_, v_x_455_, v_x_8984__boxed_460_, v_x_8985__boxed_461_, v_x_458_, v_x_459_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_463_, lean_object* v_keys_464_, lean_object* v_vals_465_, lean_object* v_heq_466_, lean_object* v_i_467_, lean_object* v_k_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1___redArg(v_keys_464_, v_vals_465_, v_i_467_, v_k_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_470_, lean_object* v_keys_471_, lean_object* v_vals_472_, lean_object* v_heq_473_, lean_object* v_i_474_, lean_object* v_k_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1(v_00_u03b2_470_, v_keys_471_, v_vals_472_, v_heq_473_, v_i_474_, v_k_475_);
lean_dec_ref(v_k_475_);
lean_dec_ref(v_vals_472_);
lean_dec_ref(v_keys_471_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_477_, lean_object* v_n_478_, lean_object* v_k_479_, lean_object* v_v_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__4___redArg(v_n_478_, v_k_479_, v_v_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_482_, size_t v_depth_483_, lean_object* v_keys_484_, lean_object* v_vals_485_, lean_object* v_heq_486_, lean_object* v_i_487_, lean_object* v_entries_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5___redArg(v_depth_483_, v_keys_484_, v_vals_485_, v_i_487_, v_entries_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_490_, lean_object* v_depth_491_, lean_object* v_keys_492_, lean_object* v_vals_493_, lean_object* v_heq_494_, lean_object* v_i_495_, lean_object* v_entries_496_){
_start:
{
size_t v_depth_boxed_497_; lean_object* v_res_498_; 
v_depth_boxed_497_ = lean_unbox_usize(v_depth_491_);
lean_dec(v_depth_491_);
v_res_498_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5(v_00_u03b2_490_, v_depth_boxed_497_, v_keys_492_, v_vals_493_, v_heq_494_, v_i_495_, v_entries_496_);
lean_dec_ref(v_vals_493_);
lean_dec_ref(v_keys_492_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_499_, lean_object* v_x_500_, lean_object* v_x_501_, lean_object* v_x_502_, lean_object* v_x_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__4_spec__5___redArg(v_x_500_, v_x_501_, v_x_502_, v_x_503_);
return v___x_504_;
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
