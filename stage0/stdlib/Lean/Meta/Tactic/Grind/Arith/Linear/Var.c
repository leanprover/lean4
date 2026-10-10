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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
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
lean_object* v_ks_5_; lean_object* v_vs_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_32_; 
v_ks_5_ = lean_ctor_get(v_x_1_, 0);
v_vs_6_ = lean_ctor_get(v_x_1_, 1);
v_isSharedCheck_32_ = !lean_is_exclusive(v_x_1_);
if (v_isSharedCheck_32_ == 0)
{
v___x_8_ = v_x_1_;
v_isShared_9_ = v_isSharedCheck_32_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_vs_6_);
lean_inc(v_ks_5_);
lean_dec(v_x_1_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_32_;
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
lean_object* v_k_x27_17_; size_t v___x_18_; size_t v___x_19_; uint8_t v___x_20_; 
v_k_x27_17_ = lean_array_fget_borrowed(v_ks_5_, v_x_2_);
v___x_18_ = lean_ptr_addr(v_x_3_);
v___x_19_ = lean_ptr_addr(v_k_x27_17_);
v___x_20_ = lean_usize_dec_eq(v___x_18_, v___x_19_);
if (v___x_20_ == 0)
{
lean_object* v___x_22_; 
if (v_isShared_9_ == 0)
{
v___x_22_ = v___x_8_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v_ks_5_);
lean_ctor_set(v_reuseFailAlloc_26_, 1, v_vs_6_);
v___x_22_ = v_reuseFailAlloc_26_;
goto v_reusejp_21_;
}
v_reusejp_21_:
{
lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_23_ = lean_unsigned_to_nat(1u);
v___x_24_ = lean_nat_add(v_x_2_, v___x_23_);
lean_dec(v_x_2_);
v_x_1_ = v___x_22_;
v_x_2_ = v___x_24_;
goto _start;
}
}
else
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_30_; 
v___x_27_ = lean_array_fset(v_ks_5_, v_x_2_, v_x_3_);
v___x_28_ = lean_array_fset(v_vs_6_, v_x_2_, v_x_4_);
lean_dec(v_x_2_);
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v___x_28_);
lean_ctor_set(v___x_8_, 0, v___x_27_);
v___x_30_ = v___x_8_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v___x_27_);
lean_ctor_set(v_reuseFailAlloc_31_, 1, v___x_28_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__4___redArg(lean_object* v_n_33_, lean_object* v_k_34_, lean_object* v_v_35_){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_unsigned_to_nat(0u);
v___x_37_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__4_spec__5___redArg(v_n_33_, v___x_36_, v_k_34_, v_v_35_);
return v___x_37_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_38_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg(lean_object* v_x_39_, size_t v_x_40_, size_t v_x_41_, lean_object* v_x_42_, lean_object* v_x_43_){
_start:
{
if (lean_obj_tag(v_x_39_) == 0)
{
lean_object* v_es_44_; size_t v___x_45_; size_t v___x_46_; lean_object* v_j_47_; lean_object* v___x_48_; uint8_t v___x_49_; 
v_es_44_ = lean_ctor_get(v_x_39_, 0);
v___x_45_ = ((size_t)31ULL);
v___x_46_ = lean_usize_land(v_x_40_, v___x_45_);
v_j_47_ = lean_usize_to_nat(v___x_46_);
v___x_48_ = lean_array_get_size(v_es_44_);
v___x_49_ = lean_nat_dec_lt(v_j_47_, v___x_48_);
if (v___x_49_ == 0)
{
lean_dec(v_j_47_);
lean_dec(v_x_43_);
lean_dec_ref(v_x_42_);
return v_x_39_;
}
else
{
lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_90_; 
lean_inc_ref(v_es_44_);
v_isSharedCheck_90_ = !lean_is_exclusive(v_x_39_);
if (v_isSharedCheck_90_ == 0)
{
lean_object* v_unused_91_; 
v_unused_91_ = lean_ctor_get(v_x_39_, 0);
lean_dec(v_unused_91_);
v___x_51_ = v_x_39_;
v_isShared_52_ = v_isSharedCheck_90_;
goto v_resetjp_50_;
}
else
{
lean_dec(v_x_39_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_90_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v_v_53_; lean_object* v___x_54_; lean_object* v_xs_x27_55_; lean_object* v___y_57_; 
v_v_53_ = lean_array_fget(v_es_44_, v_j_47_);
v___x_54_ = lean_box(0);
v_xs_x27_55_ = lean_array_fset(v_es_44_, v_j_47_, v___x_54_);
switch(lean_obj_tag(v_v_53_))
{
case 0:
{
lean_object* v_key_62_; lean_object* v_val_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_75_; 
v_key_62_ = lean_ctor_get(v_v_53_, 0);
v_val_63_ = lean_ctor_get(v_v_53_, 1);
v_isSharedCheck_75_ = !lean_is_exclusive(v_v_53_);
if (v_isSharedCheck_75_ == 0)
{
v___x_65_ = v_v_53_;
v_isShared_66_ = v_isSharedCheck_75_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_val_63_);
lean_inc(v_key_62_);
lean_dec(v_v_53_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_75_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
size_t v___x_67_; size_t v___x_68_; uint8_t v___x_69_; 
v___x_67_ = lean_ptr_addr(v_x_42_);
v___x_68_ = lean_ptr_addr(v_key_62_);
v___x_69_ = lean_usize_dec_eq(v___x_67_, v___x_68_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; lean_object* v___x_71_; 
lean_del_object(v___x_65_);
v___x_70_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_62_, v_val_63_, v_x_42_, v_x_43_);
v___x_71_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
v___y_57_ = v___x_71_;
goto v___jp_56_;
}
else
{
lean_object* v___x_73_; 
lean_dec(v_val_63_);
lean_dec(v_key_62_);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 1, v_x_43_);
lean_ctor_set(v___x_65_, 0, v_x_42_);
v___x_73_ = v___x_65_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v_x_42_);
lean_ctor_set(v_reuseFailAlloc_74_, 1, v_x_43_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
v___y_57_ = v___x_73_;
goto v___jp_56_;
}
}
}
}
case 1:
{
lean_object* v_node_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_88_; 
v_node_76_ = lean_ctor_get(v_v_53_, 0);
v_isSharedCheck_88_ = !lean_is_exclusive(v_v_53_);
if (v_isSharedCheck_88_ == 0)
{
v___x_78_ = v_v_53_;
v_isShared_79_ = v_isSharedCheck_88_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_node_76_);
lean_dec(v_v_53_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_88_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
size_t v___x_80_; size_t v___x_81_; size_t v___x_82_; size_t v___x_83_; lean_object* v___x_84_; lean_object* v___x_86_; 
v___x_80_ = ((size_t)5ULL);
v___x_81_ = lean_usize_shift_right(v_x_40_, v___x_80_);
v___x_82_ = ((size_t)1ULL);
v___x_83_ = lean_usize_add(v_x_41_, v___x_82_);
v___x_84_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg(v_node_76_, v___x_81_, v___x_83_, v_x_42_, v_x_43_);
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 0, v___x_84_);
v___x_86_ = v___x_78_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v___x_84_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
v___y_57_ = v___x_86_;
goto v___jp_56_;
}
}
}
default: 
{
lean_object* v___x_89_; 
v___x_89_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_89_, 0, v_x_42_);
lean_ctor_set(v___x_89_, 1, v_x_43_);
v___y_57_ = v___x_89_;
goto v___jp_56_;
}
}
v___jp_56_:
{
lean_object* v___x_58_; lean_object* v___x_60_; 
v___x_58_ = lean_array_fset(v_xs_x27_55_, v_j_47_, v___y_57_);
lean_dec(v_j_47_);
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 0, v___x_58_);
v___x_60_ = v___x_51_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v___x_58_);
v___x_60_ = v_reuseFailAlloc_61_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
return v___x_60_;
}
}
}
}
}
else
{
lean_object* v_ks_92_; lean_object* v_vs_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_111_; 
v_ks_92_ = lean_ctor_get(v_x_39_, 0);
v_vs_93_ = lean_ctor_get(v_x_39_, 1);
v_isSharedCheck_111_ = !lean_is_exclusive(v_x_39_);
if (v_isSharedCheck_111_ == 0)
{
v___x_95_ = v_x_39_;
v_isShared_96_ = v_isSharedCheck_111_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_vs_93_);
lean_inc(v_ks_92_);
lean_dec(v_x_39_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_111_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_98_; 
if (v_isShared_96_ == 0)
{
v___x_98_ = v___x_95_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_ks_92_);
lean_ctor_set(v_reuseFailAlloc_110_, 1, v_vs_93_);
v___x_98_ = v_reuseFailAlloc_110_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
lean_object* v_newNode_99_; size_t v___x_100_; uint8_t v___x_101_; 
v_newNode_99_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__4___redArg(v___x_98_, v_x_42_, v_x_43_);
v___x_100_ = ((size_t)7ULL);
v___x_101_ = lean_usize_dec_le(v___x_100_, v_x_41_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_102_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_99_);
v___x_103_ = lean_unsigned_to_nat(4u);
v___x_104_ = lean_nat_dec_lt(v___x_102_, v___x_103_);
lean_dec(v___x_102_);
if (v___x_104_ == 0)
{
lean_object* v_ks_105_; lean_object* v_vs_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v_ks_105_ = lean_ctor_get(v_newNode_99_, 0);
lean_inc_ref(v_ks_105_);
v_vs_106_ = lean_ctor_get(v_newNode_99_, 1);
lean_inc_ref(v_vs_106_);
lean_dec_ref(v_newNode_99_);
v___x_107_ = lean_unsigned_to_nat(0u);
v___x_108_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__0);
v___x_109_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5___redArg(v_x_41_, v_ks_105_, v_vs_106_, v___x_107_, v___x_108_);
lean_dec_ref(v_vs_106_);
lean_dec_ref(v_ks_105_);
return v___x_109_;
}
else
{
return v_newNode_99_;
}
}
else
{
return v_newNode_99_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_39_ = stack[0].m_obj;
size_t v_x_40_ = stack[1].m_num;
size_t v_x_41_ = stack[2].m_num;
lean_object* v_x_42_ = stack[3].m_obj;
lean_object* v_x_43_ = stack[4].m_obj;
lean_object* v_res_112_;
v_res_112_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg(v_x_39_, v_x_40_, v_x_41_, v_x_42_, v_x_43_);
stack->m_obj
 = v_res_112_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5___redArg(size_t v_depth_113_, lean_object* v_keys_114_, lean_object* v_vals_115_, lean_object* v_i_116_, lean_object* v_entries_117_){
_start:
{
lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_118_ = lean_array_get_size(v_keys_114_);
v___x_119_ = lean_nat_dec_lt(v_i_116_, v___x_118_);
if (v___x_119_ == 0)
{
lean_dec(v_i_116_);
return v_entries_117_;
}
else
{
lean_object* v_k_120_; lean_object* v_v_121_; size_t v___x_122_; size_t v___x_123_; size_t v___x_124_; uint64_t v___x_125_; size_t v_h_126_; size_t v___x_127_; lean_object* v___x_128_; size_t v___x_129_; size_t v___x_130_; size_t v___x_131_; size_t v_h_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v_k_120_ = lean_array_fget_borrowed(v_keys_114_, v_i_116_);
v_v_121_ = lean_array_fget_borrowed(v_vals_115_, v_i_116_);
v___x_122_ = lean_ptr_addr(v_k_120_);
v___x_123_ = ((size_t)3ULL);
v___x_124_ = lean_usize_shift_right(v___x_122_, v___x_123_);
v___x_125_ = lean_usize_to_uint64(v___x_124_);
v_h_126_ = lean_uint64_to_usize(v___x_125_);
v___x_127_ = ((size_t)5ULL);
v___x_128_ = lean_unsigned_to_nat(1u);
v___x_129_ = ((size_t)1ULL);
v___x_130_ = lean_usize_sub(v_depth_113_, v___x_129_);
v___x_131_ = lean_usize_mul(v___x_127_, v___x_130_);
v_h_132_ = lean_usize_shift_right(v_h_126_, v___x_131_);
v___x_133_ = lean_nat_add(v_i_116_, v___x_128_);
lean_dec(v_i_116_);
lean_inc(v_v_121_);
lean_inc(v_k_120_);
v___x_134_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg(v_entries_117_, v_h_132_, v_depth_113_, v_k_120_, v_v_121_);
v_i_116_ = v___x_133_;
v_entries_117_ = v___x_134_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_113_ = stack[0].m_num;
lean_object* v_keys_114_ = stack[1].m_obj;
lean_object* v_vals_115_ = stack[2].m_obj;
lean_object* v_i_116_ = stack[3].m_obj;
lean_object* v_entries_117_ = stack[4].m_obj;
lean_object* v_res_136_;
v_res_136_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5___redArg(v_depth_113_, v_keys_114_, v_vals_115_, v_i_116_, v_entries_117_);
stack->m_obj
 = v_res_136_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_137_, lean_object* v_keys_138_, lean_object* v_vals_139_, lean_object* v_i_140_, lean_object* v_entries_141_){
_start:
{
size_t v_depth_boxed_142_; lean_object* v_res_143_; 
v_depth_boxed_142_ = lean_unbox_usize(v_depth_137_);
lean_dec(v_depth_137_);
v_res_143_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5___redArg(v_depth_boxed_142_, v_keys_138_, v_vals_139_, v_i_140_, v_entries_141_);
lean_dec_ref(v_vals_139_);
lean_dec_ref(v_keys_138_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___boxed(lean_object* v_x_144_, lean_object* v_x_145_, lean_object* v_x_146_, lean_object* v_x_147_, lean_object* v_x_148_){
_start:
{
size_t v_x_7461__boxed_149_; size_t v_x_7462__boxed_150_; lean_object* v_res_151_; 
v_x_7461__boxed_149_ = lean_unbox_usize(v_x_145_);
lean_dec(v_x_145_);
v_x_7462__boxed_150_ = lean_unbox_usize(v_x_146_);
lean_dec(v_x_146_);
v_res_151_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg(v_x_144_, v_x_7461__boxed_149_, v_x_7462__boxed_150_, v_x_147_, v_x_148_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1___redArg(lean_object* v_x_152_, lean_object* v_x_153_, lean_object* v_x_154_){
_start:
{
size_t v___x_155_; size_t v___x_156_; size_t v___x_157_; uint64_t v___x_158_; size_t v___x_159_; size_t v___x_160_; lean_object* v___x_161_; 
v___x_155_ = lean_ptr_addr(v_x_153_);
v___x_156_ = ((size_t)3ULL);
v___x_157_ = lean_usize_shift_right(v___x_155_, v___x_156_);
v___x_158_ = lean_usize_to_uint64(v___x_157_);
v___x_159_ = lean_uint64_to_usize(v___x_158_);
v___x_160_ = ((size_t)1ULL);
v___x_161_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg(v_x_152_, v___x_159_, v___x_160_, v_x_153_, v_x_154_);
return v___x_161_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__0(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_162_ = lean_unsigned_to_nat(32u);
v___x_163_ = lean_mk_empty_array_with_capacity(v___x_162_);
v___x_164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
return v___x_164_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__1(void){
_start:
{
size_t v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_165_ = ((size_t)5ULL);
v___x_166_ = lean_unsigned_to_nat(0u);
v___x_167_ = lean_unsigned_to_nat(32u);
v___x_168_ = lean_mk_empty_array_with_capacity(v___x_167_);
v___x_169_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__0);
v___x_170_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v___x_168_);
lean_ctor_set(v___x_170_, 2, v___x_166_);
lean_ctor_set(v___x_170_, 3, v___x_166_);
lean_ctor_set_usize(v___x_170_, 4, v___x_165_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0(lean_object* v_a_171_, lean_object* v_e_172_, lean_object* v_size_173_, lean_object* v_s_174_){
_start:
{
lean_object* v_structs_175_; lean_object* v_typeIdOf_176_; lean_object* v_exprToStructId_177_; lean_object* v_exprToStructIdEntries_178_; lean_object* v_forbiddenNatModules_179_; lean_object* v_natStructs_180_; lean_object* v_natTypeIdOf_181_; lean_object* v_exprToNatStructId_182_; lean_object* v___x_183_; uint8_t v___x_184_; 
v_structs_175_ = lean_ctor_get(v_s_174_, 0);
v_typeIdOf_176_ = lean_ctor_get(v_s_174_, 1);
v_exprToStructId_177_ = lean_ctor_get(v_s_174_, 2);
v_exprToStructIdEntries_178_ = lean_ctor_get(v_s_174_, 3);
v_forbiddenNatModules_179_ = lean_ctor_get(v_s_174_, 4);
v_natStructs_180_ = lean_ctor_get(v_s_174_, 5);
v_natTypeIdOf_181_ = lean_ctor_get(v_s_174_, 6);
v_exprToNatStructId_182_ = lean_ctor_get(v_s_174_, 7);
v___x_183_ = lean_array_get_size(v_structs_175_);
v___x_184_ = lean_nat_dec_lt(v_a_171_, v___x_183_);
if (v___x_184_ == 0)
{
lean_dec(v_size_173_);
lean_dec_ref(v_e_172_);
return v_s_174_;
}
else
{
lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_255_; 
lean_inc_ref(v_exprToNatStructId_182_);
lean_inc_ref(v_natTypeIdOf_181_);
lean_inc_ref(v_natStructs_180_);
lean_inc_ref(v_forbiddenNatModules_179_);
lean_inc_ref(v_exprToStructIdEntries_178_);
lean_inc_ref(v_exprToStructId_177_);
lean_inc_ref(v_typeIdOf_176_);
lean_inc_ref(v_structs_175_);
v_isSharedCheck_255_ = !lean_is_exclusive(v_s_174_);
if (v_isSharedCheck_255_ == 0)
{
lean_object* v_unused_256_; lean_object* v_unused_257_; lean_object* v_unused_258_; lean_object* v_unused_259_; lean_object* v_unused_260_; lean_object* v_unused_261_; lean_object* v_unused_262_; lean_object* v_unused_263_; 
v_unused_256_ = lean_ctor_get(v_s_174_, 7);
lean_dec(v_unused_256_);
v_unused_257_ = lean_ctor_get(v_s_174_, 6);
lean_dec(v_unused_257_);
v_unused_258_ = lean_ctor_get(v_s_174_, 5);
lean_dec(v_unused_258_);
v_unused_259_ = lean_ctor_get(v_s_174_, 4);
lean_dec(v_unused_259_);
v_unused_260_ = lean_ctor_get(v_s_174_, 3);
lean_dec(v_unused_260_);
v_unused_261_ = lean_ctor_get(v_s_174_, 2);
lean_dec(v_unused_261_);
v_unused_262_ = lean_ctor_get(v_s_174_, 1);
lean_dec(v_unused_262_);
v_unused_263_ = lean_ctor_get(v_s_174_, 0);
lean_dec(v_unused_263_);
v___x_186_ = v_s_174_;
v_isShared_187_ = v_isSharedCheck_255_;
goto v_resetjp_185_;
}
else
{
lean_dec(v_s_174_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_255_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v_v_188_; lean_object* v_id_189_; lean_object* v_ringId_x3f_190_; lean_object* v_type_191_; lean_object* v_u_192_; lean_object* v_intModuleInst_193_; lean_object* v_leInst_x3f_194_; lean_object* v_ltInst_x3f_195_; lean_object* v_lawfulOrderLTInst_x3f_196_; lean_object* v_isPreorderInst_x3f_197_; lean_object* v_orderedAddInst_x3f_198_; lean_object* v_isLinearInst_x3f_199_; lean_object* v_noNatDivInst_x3f_200_; lean_object* v_ringInst_x3f_201_; lean_object* v_commRingInst_x3f_202_; lean_object* v_orderedRingInst_x3f_203_; lean_object* v_fieldInst_x3f_204_; lean_object* v_charInst_x3f_205_; lean_object* v_zero_206_; lean_object* v_ofNatZero_207_; lean_object* v_one_x3f_208_; lean_object* v_leFn_x3f_209_; lean_object* v_ltFn_x3f_210_; lean_object* v_addFn_211_; lean_object* v_zsmulFn_212_; lean_object* v_nsmulFn_213_; lean_object* v_zsmulFn_x3f_214_; lean_object* v_nsmulFn_x3f_215_; lean_object* v_homomulFn_x3f_216_; lean_object* v_subFn_217_; lean_object* v_negFn_218_; lean_object* v_vars_219_; lean_object* v_varMap_220_; lean_object* v_lowers_221_; lean_object* v_uppers_222_; lean_object* v_diseqs_223_; lean_object* v_assignment_224_; uint8_t v_caseSplits_225_; lean_object* v_conflict_x3f_226_; lean_object* v_diseqSplits_227_; lean_object* v_elimEqs_228_; lean_object* v_elimStack_229_; lean_object* v_occurs_230_; lean_object* v_ignored_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_254_; 
v_v_188_ = lean_array_fget(v_structs_175_, v_a_171_);
v_id_189_ = lean_ctor_get(v_v_188_, 0);
v_ringId_x3f_190_ = lean_ctor_get(v_v_188_, 1);
v_type_191_ = lean_ctor_get(v_v_188_, 2);
v_u_192_ = lean_ctor_get(v_v_188_, 3);
v_intModuleInst_193_ = lean_ctor_get(v_v_188_, 4);
v_leInst_x3f_194_ = lean_ctor_get(v_v_188_, 5);
v_ltInst_x3f_195_ = lean_ctor_get(v_v_188_, 6);
v_lawfulOrderLTInst_x3f_196_ = lean_ctor_get(v_v_188_, 7);
v_isPreorderInst_x3f_197_ = lean_ctor_get(v_v_188_, 8);
v_orderedAddInst_x3f_198_ = lean_ctor_get(v_v_188_, 9);
v_isLinearInst_x3f_199_ = lean_ctor_get(v_v_188_, 10);
v_noNatDivInst_x3f_200_ = lean_ctor_get(v_v_188_, 11);
v_ringInst_x3f_201_ = lean_ctor_get(v_v_188_, 12);
v_commRingInst_x3f_202_ = lean_ctor_get(v_v_188_, 13);
v_orderedRingInst_x3f_203_ = lean_ctor_get(v_v_188_, 14);
v_fieldInst_x3f_204_ = lean_ctor_get(v_v_188_, 15);
v_charInst_x3f_205_ = lean_ctor_get(v_v_188_, 16);
v_zero_206_ = lean_ctor_get(v_v_188_, 17);
v_ofNatZero_207_ = lean_ctor_get(v_v_188_, 18);
v_one_x3f_208_ = lean_ctor_get(v_v_188_, 19);
v_leFn_x3f_209_ = lean_ctor_get(v_v_188_, 20);
v_ltFn_x3f_210_ = lean_ctor_get(v_v_188_, 21);
v_addFn_211_ = lean_ctor_get(v_v_188_, 22);
v_zsmulFn_212_ = lean_ctor_get(v_v_188_, 23);
v_nsmulFn_213_ = lean_ctor_get(v_v_188_, 24);
v_zsmulFn_x3f_214_ = lean_ctor_get(v_v_188_, 25);
v_nsmulFn_x3f_215_ = lean_ctor_get(v_v_188_, 26);
v_homomulFn_x3f_216_ = lean_ctor_get(v_v_188_, 27);
v_subFn_217_ = lean_ctor_get(v_v_188_, 28);
v_negFn_218_ = lean_ctor_get(v_v_188_, 29);
v_vars_219_ = lean_ctor_get(v_v_188_, 30);
v_varMap_220_ = lean_ctor_get(v_v_188_, 31);
v_lowers_221_ = lean_ctor_get(v_v_188_, 32);
v_uppers_222_ = lean_ctor_get(v_v_188_, 33);
v_diseqs_223_ = lean_ctor_get(v_v_188_, 34);
v_assignment_224_ = lean_ctor_get(v_v_188_, 35);
v_caseSplits_225_ = lean_ctor_get_uint8(v_v_188_, sizeof(void*)*42);
v_conflict_x3f_226_ = lean_ctor_get(v_v_188_, 36);
v_diseqSplits_227_ = lean_ctor_get(v_v_188_, 37);
v_elimEqs_228_ = lean_ctor_get(v_v_188_, 38);
v_elimStack_229_ = lean_ctor_get(v_v_188_, 39);
v_occurs_230_ = lean_ctor_get(v_v_188_, 40);
v_ignored_231_ = lean_ctor_get(v_v_188_, 41);
v_isSharedCheck_254_ = !lean_is_exclusive(v_v_188_);
if (v_isSharedCheck_254_ == 0)
{
v___x_233_ = v_v_188_;
v_isShared_234_ = v_isSharedCheck_254_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_ignored_231_);
lean_inc(v_occurs_230_);
lean_inc(v_elimStack_229_);
lean_inc(v_elimEqs_228_);
lean_inc(v_diseqSplits_227_);
lean_inc(v_conflict_x3f_226_);
lean_inc(v_assignment_224_);
lean_inc(v_diseqs_223_);
lean_inc(v_uppers_222_);
lean_inc(v_lowers_221_);
lean_inc(v_varMap_220_);
lean_inc(v_vars_219_);
lean_inc(v_negFn_218_);
lean_inc(v_subFn_217_);
lean_inc(v_homomulFn_x3f_216_);
lean_inc(v_nsmulFn_x3f_215_);
lean_inc(v_zsmulFn_x3f_214_);
lean_inc(v_nsmulFn_213_);
lean_inc(v_zsmulFn_212_);
lean_inc(v_addFn_211_);
lean_inc(v_ltFn_x3f_210_);
lean_inc(v_leFn_x3f_209_);
lean_inc(v_one_x3f_208_);
lean_inc(v_ofNatZero_207_);
lean_inc(v_zero_206_);
lean_inc(v_charInst_x3f_205_);
lean_inc(v_fieldInst_x3f_204_);
lean_inc(v_orderedRingInst_x3f_203_);
lean_inc(v_commRingInst_x3f_202_);
lean_inc(v_ringInst_x3f_201_);
lean_inc(v_noNatDivInst_x3f_200_);
lean_inc(v_isLinearInst_x3f_199_);
lean_inc(v_orderedAddInst_x3f_198_);
lean_inc(v_isPreorderInst_x3f_197_);
lean_inc(v_lawfulOrderLTInst_x3f_196_);
lean_inc(v_ltInst_x3f_195_);
lean_inc(v_leInst_x3f_194_);
lean_inc(v_intModuleInst_193_);
lean_inc(v_u_192_);
lean_inc(v_type_191_);
lean_inc(v_ringId_x3f_190_);
lean_inc(v_id_189_);
lean_dec(v_v_188_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_254_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_235_; lean_object* v_xs_x27_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_248_; 
v___x_235_ = lean_box(0);
v_xs_x27_236_ = lean_array_fset(v_structs_175_, v_a_171_, v___x_235_);
lean_inc_ref(v_e_172_);
v___x_237_ = l_Lean_PersistentArray_push___redArg(v_vars_219_, v_e_172_);
v___x_238_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1___redArg(v_varMap_220_, v_e_172_, v_size_173_);
v___x_239_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__1);
v___x_240_ = l_Lean_PersistentArray_push___redArg(v_lowers_221_, v___x_239_);
v___x_241_ = l_Lean_PersistentArray_push___redArg(v_uppers_222_, v___x_239_);
v___x_242_ = l_Lean_PersistentArray_push___redArg(v_diseqs_223_, v___x_239_);
v___x_243_ = lean_box(0);
v___x_244_ = l_Lean_PersistentArray_push___redArg(v_elimEqs_228_, v___x_243_);
v___x_245_ = lean_box(1);
v___x_246_ = l_Lean_PersistentArray_push___redArg(v_occurs_230_, v___x_245_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 40, v___x_246_);
lean_ctor_set(v___x_233_, 38, v___x_244_);
lean_ctor_set(v___x_233_, 34, v___x_242_);
lean_ctor_set(v___x_233_, 33, v___x_241_);
lean_ctor_set(v___x_233_, 32, v___x_240_);
lean_ctor_set(v___x_233_, 31, v___x_238_);
lean_ctor_set(v___x_233_, 30, v___x_237_);
v___x_248_ = v___x_233_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_id_189_);
lean_ctor_set(v_reuseFailAlloc_253_, 1, v_ringId_x3f_190_);
lean_ctor_set(v_reuseFailAlloc_253_, 2, v_type_191_);
lean_ctor_set(v_reuseFailAlloc_253_, 3, v_u_192_);
lean_ctor_set(v_reuseFailAlloc_253_, 4, v_intModuleInst_193_);
lean_ctor_set(v_reuseFailAlloc_253_, 5, v_leInst_x3f_194_);
lean_ctor_set(v_reuseFailAlloc_253_, 6, v_ltInst_x3f_195_);
lean_ctor_set(v_reuseFailAlloc_253_, 7, v_lawfulOrderLTInst_x3f_196_);
lean_ctor_set(v_reuseFailAlloc_253_, 8, v_isPreorderInst_x3f_197_);
lean_ctor_set(v_reuseFailAlloc_253_, 9, v_orderedAddInst_x3f_198_);
lean_ctor_set(v_reuseFailAlloc_253_, 10, v_isLinearInst_x3f_199_);
lean_ctor_set(v_reuseFailAlloc_253_, 11, v_noNatDivInst_x3f_200_);
lean_ctor_set(v_reuseFailAlloc_253_, 12, v_ringInst_x3f_201_);
lean_ctor_set(v_reuseFailAlloc_253_, 13, v_commRingInst_x3f_202_);
lean_ctor_set(v_reuseFailAlloc_253_, 14, v_orderedRingInst_x3f_203_);
lean_ctor_set(v_reuseFailAlloc_253_, 15, v_fieldInst_x3f_204_);
lean_ctor_set(v_reuseFailAlloc_253_, 16, v_charInst_x3f_205_);
lean_ctor_set(v_reuseFailAlloc_253_, 17, v_zero_206_);
lean_ctor_set(v_reuseFailAlloc_253_, 18, v_ofNatZero_207_);
lean_ctor_set(v_reuseFailAlloc_253_, 19, v_one_x3f_208_);
lean_ctor_set(v_reuseFailAlloc_253_, 20, v_leFn_x3f_209_);
lean_ctor_set(v_reuseFailAlloc_253_, 21, v_ltFn_x3f_210_);
lean_ctor_set(v_reuseFailAlloc_253_, 22, v_addFn_211_);
lean_ctor_set(v_reuseFailAlloc_253_, 23, v_zsmulFn_212_);
lean_ctor_set(v_reuseFailAlloc_253_, 24, v_nsmulFn_213_);
lean_ctor_set(v_reuseFailAlloc_253_, 25, v_zsmulFn_x3f_214_);
lean_ctor_set(v_reuseFailAlloc_253_, 26, v_nsmulFn_x3f_215_);
lean_ctor_set(v_reuseFailAlloc_253_, 27, v_homomulFn_x3f_216_);
lean_ctor_set(v_reuseFailAlloc_253_, 28, v_subFn_217_);
lean_ctor_set(v_reuseFailAlloc_253_, 29, v_negFn_218_);
lean_ctor_set(v_reuseFailAlloc_253_, 30, v___x_237_);
lean_ctor_set(v_reuseFailAlloc_253_, 31, v___x_238_);
lean_ctor_set(v_reuseFailAlloc_253_, 32, v___x_240_);
lean_ctor_set(v_reuseFailAlloc_253_, 33, v___x_241_);
lean_ctor_set(v_reuseFailAlloc_253_, 34, v___x_242_);
lean_ctor_set(v_reuseFailAlloc_253_, 35, v_assignment_224_);
lean_ctor_set(v_reuseFailAlloc_253_, 36, v_conflict_x3f_226_);
lean_ctor_set(v_reuseFailAlloc_253_, 37, v_diseqSplits_227_);
lean_ctor_set(v_reuseFailAlloc_253_, 38, v___x_244_);
lean_ctor_set(v_reuseFailAlloc_253_, 39, v_elimStack_229_);
lean_ctor_set(v_reuseFailAlloc_253_, 40, v___x_246_);
lean_ctor_set(v_reuseFailAlloc_253_, 41, v_ignored_231_);
lean_ctor_set_uint8(v_reuseFailAlloc_253_, sizeof(void*)*42, v_caseSplits_225_);
v___x_248_ = v_reuseFailAlloc_253_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
lean_object* v___x_249_; lean_object* v___x_251_; 
v___x_249_ = lean_array_fset(v_xs_x27_236_, v_a_171_, v___x_248_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 0, v___x_249_);
v___x_251_ = v___x_186_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_249_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_typeIdOf_176_);
lean_ctor_set(v_reuseFailAlloc_252_, 2, v_exprToStructId_177_);
lean_ctor_set(v_reuseFailAlloc_252_, 3, v_exprToStructIdEntries_178_);
lean_ctor_set(v_reuseFailAlloc_252_, 4, v_forbiddenNatModules_179_);
lean_ctor_set(v_reuseFailAlloc_252_, 5, v_natStructs_180_);
lean_ctor_set(v_reuseFailAlloc_252_, 6, v_natTypeIdOf_181_);
lean_ctor_set(v_reuseFailAlloc_252_, 7, v_exprToNatStructId_182_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___boxed(lean_object* v_a_264_, lean_object* v_e_265_, lean_object* v_size_266_, lean_object* v_s_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0(v_a_264_, v_e_265_, v_size_266_, v_s_267_);
lean_dec(v_a_264_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_269_, lean_object* v_vals_270_, lean_object* v_i_271_, lean_object* v_k_272_){
_start:
{
lean_object* v___x_273_; uint8_t v___x_274_; 
v___x_273_ = lean_array_get_size(v_keys_269_);
v___x_274_ = lean_nat_dec_lt(v_i_271_, v___x_273_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; 
lean_dec(v_i_271_);
v___x_275_ = lean_box(0);
return v___x_275_;
}
else
{
lean_object* v_k_x27_276_; size_t v___x_277_; size_t v___x_278_; uint8_t v___x_279_; 
v_k_x27_276_ = lean_array_fget_borrowed(v_keys_269_, v_i_271_);
v___x_277_ = lean_ptr_addr(v_k_272_);
v___x_278_ = lean_ptr_addr(v_k_x27_276_);
v___x_279_ = lean_usize_dec_eq(v___x_277_, v___x_278_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = lean_unsigned_to_nat(1u);
v___x_281_ = lean_nat_add(v_i_271_, v___x_280_);
lean_dec(v_i_271_);
v_i_271_ = v___x_281_;
goto _start;
}
else
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = lean_array_fget_borrowed(v_vals_270_, v_i_271_);
lean_dec(v_i_271_);
lean_inc(v___x_283_);
v___x_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
return v___x_284_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_285_, lean_object* v_vals_286_, lean_object* v_i_287_, lean_object* v_k_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1___redArg(v_keys_285_, v_vals_286_, v_i_287_, v_k_288_);
lean_dec_ref(v_k_288_);
lean_dec_ref(v_vals_286_);
lean_dec_ref(v_keys_285_);
return v_res_289_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0___redArg(lean_object* v_x_290_, size_t v_x_291_, lean_object* v_x_292_){
_start:
{
if (lean_obj_tag(v_x_290_) == 0)
{
lean_object* v_es_293_; lean_object* v___x_294_; size_t v___x_295_; size_t v___x_296_; lean_object* v_j_297_; lean_object* v___x_298_; 
v_es_293_ = lean_ctor_get(v_x_290_, 0);
v___x_294_ = lean_box(2);
v___x_295_ = ((size_t)31ULL);
v___x_296_ = lean_usize_land(v_x_291_, v___x_295_);
v_j_297_ = lean_usize_to_nat(v___x_296_);
v___x_298_ = lean_array_get_borrowed(v___x_294_, v_es_293_, v_j_297_);
lean_dec(v_j_297_);
switch(lean_obj_tag(v___x_298_))
{
case 0:
{
lean_object* v_key_299_; lean_object* v_val_300_; size_t v___x_301_; size_t v___x_302_; uint8_t v___x_303_; 
v_key_299_ = lean_ctor_get(v___x_298_, 0);
v_val_300_ = lean_ctor_get(v___x_298_, 1);
v___x_301_ = lean_ptr_addr(v_x_292_);
v___x_302_ = lean_ptr_addr(v_key_299_);
v___x_303_ = lean_usize_dec_eq(v___x_301_, v___x_302_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; 
v___x_304_ = lean_box(0);
return v___x_304_;
}
else
{
lean_object* v___x_305_; 
lean_inc(v_val_300_);
v___x_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_305_, 0, v_val_300_);
return v___x_305_;
}
}
case 1:
{
lean_object* v_node_306_; size_t v___x_307_; size_t v___x_308_; 
v_node_306_ = lean_ctor_get(v___x_298_, 0);
v___x_307_ = ((size_t)5ULL);
v___x_308_ = lean_usize_shift_right(v_x_291_, v___x_307_);
v_x_290_ = v_node_306_;
v_x_291_ = v___x_308_;
goto _start;
}
default: 
{
lean_object* v___x_310_; 
v___x_310_ = lean_box(0);
return v___x_310_;
}
}
}
else
{
lean_object* v_ks_311_; lean_object* v_vs_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v_ks_311_ = lean_ctor_get(v_x_290_, 0);
v_vs_312_ = lean_ctor_get(v_x_290_, 1);
v___x_313_ = lean_unsigned_to_nat(0u);
v___x_314_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1___redArg(v_ks_311_, v_vs_312_, v___x_313_, v_x_292_);
return v___x_314_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_290_ = stack[0].m_obj;
size_t v_x_291_ = stack[1].m_num;
lean_object* v_x_292_ = stack[2].m_obj;
lean_object* v_res_315_;
v_res_315_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0___redArg(v_x_290_, v_x_291_, v_x_292_);
stack->m_obj
 = v_res_315_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0___redArg___boxed(lean_object* v_x_316_, lean_object* v_x_317_, lean_object* v_x_318_){
_start:
{
size_t v_x_7918__boxed_319_; lean_object* v_res_320_; 
v_x_7918__boxed_319_ = lean_unbox_usize(v_x_317_);
lean_dec(v_x_317_);
v_res_320_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0___redArg(v_x_316_, v_x_7918__boxed_319_, v_x_318_);
lean_dec_ref(v_x_318_);
lean_dec_ref(v_x_316_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0___redArg(lean_object* v_x_321_, lean_object* v_x_322_){
_start:
{
size_t v___x_323_; size_t v___x_324_; size_t v___x_325_; uint64_t v___x_326_; size_t v___x_327_; lean_object* v___x_328_; 
v___x_323_ = lean_ptr_addr(v_x_322_);
v___x_324_ = ((size_t)3ULL);
v___x_325_ = lean_usize_shift_right(v___x_323_, v___x_324_);
v___x_326_ = lean_usize_to_uint64(v___x_325_);
v___x_327_ = lean_uint64_to_usize(v___x_326_);
v___x_328_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0___redArg(v_x_321_, v___x_327_, v_x_322_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0___redArg___boxed(lean_object* v_x_329_, lean_object* v_x_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0___redArg(v_x_329_, v_x_330_);
lean_dec_ref(v_x_330_);
lean_dec_ref(v_x_329_);
return v_res_331_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar(lean_object* v_e_332_, uint8_t v_mark_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_404_; 
v_a_347_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_404_ == 0)
{
v___x_349_ = v___x_346_;
v_isShared_350_ = v_isSharedCheck_404_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_346_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_404_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v_vars_351_; lean_object* v_varMap_352_; lean_object* v___x_353_; 
v_vars_351_ = lean_ctor_get(v_a_347_, 30);
lean_inc_ref(v_vars_351_);
v_varMap_352_ = lean_ctor_get(v_a_347_, 31);
lean_inc_ref(v_varMap_352_);
lean_dec(v_a_347_);
v___x_353_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0___redArg(v_varMap_352_, v_e_332_);
lean_dec_ref(v_varMap_352_);
if (lean_obj_tag(v___x_353_) == 1)
{
lean_object* v_val_354_; lean_object* v___x_356_; 
lean_dec_ref(v_vars_351_);
lean_dec_ref(v_e_332_);
v_val_354_ = lean_ctor_get(v___x_353_, 0);
lean_inc(v_val_354_);
lean_dec_ref_known(v___x_353_, 1);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 0, v_val_354_);
v___x_356_ = v___x_349_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_val_354_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
else
{
lean_object* v_size_358_; lean_object* v___f_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
lean_dec(v___x_353_);
lean_del_object(v___x_349_);
v_size_358_ = lean_ctor_get(v_vars_351_, 2);
lean_inc_n(v_size_358_, 2);
lean_dec_ref(v_vars_351_);
lean_inc_ref(v_e_332_);
lean_inc(v_a_334_);
v___f_359_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___boxed), 4, 3);
lean_closure_set(v___f_359_, 0, v_a_334_);
lean_closure_set(v___f_359_, 1, v_e_332_);
lean_closure_set(v___f_359_, 2, v_size_358_);
v___x_360_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_361_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_360_, v___f_359_, v_a_335_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v___x_362_; 
lean_dec_ref_known(v___x_361_, 1);
lean_inc_ref(v_e_332_);
v___x_362_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg(v_e_332_, v_a_334_, v_a_335_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_386_; 
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_386_ == 0)
{
lean_object* v_unused_387_; 
v_unused_387_ = lean_ctor_get(v___x_362_, 0);
lean_dec(v_unused_387_);
v___x_364_ = v___x_362_;
v_isShared_365_ = v_isSharedCheck_386_;
goto v_resetjp_363_;
}
else
{
lean_dec(v___x_362_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_386_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
if (v_mark_333_ == 0)
{
lean_object* v___x_367_; 
lean_dec_ref(v_e_332_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 0, v_size_358_);
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_size_358_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
else
{
lean_object* v___x_369_; 
lean_del_object(v___x_364_);
v___x_369_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_360_, v_e_332_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_376_; 
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_376_ == 0)
{
lean_object* v_unused_377_; 
v_unused_377_ = lean_ctor_get(v___x_369_, 0);
lean_dec(v_unused_377_);
v___x_371_ = v___x_369_;
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
else
{
lean_dec(v___x_369_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_374_; 
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 0, v_size_358_);
v___x_374_ = v___x_371_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_size_358_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
else
{
lean_object* v_a_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_385_; 
lean_dec(v_size_358_);
v_a_378_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_385_ == 0)
{
v___x_380_ = v___x_369_;
v_isShared_381_ = v_isSharedCheck_385_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_a_378_);
lean_dec(v___x_369_);
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
lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_395_; 
lean_dec(v_size_358_);
lean_dec_ref(v_e_332_);
v_a_388_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_395_ == 0)
{
v___x_390_ = v___x_362_;
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_dec(v___x_362_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_a_388_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
else
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_403_; 
lean_dec(v_size_358_);
lean_dec_ref(v_e_332_);
v_a_396_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_403_ == 0)
{
v___x_398_ = v___x_361_;
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_361_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_401_; 
if (v_isShared_399_ == 0)
{
v___x_401_ = v___x_398_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_a_396_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
}
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
lean_dec_ref(v_e_332_);
v_a_405_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_346_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_346_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_mkVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_332_ = stack[0].m_obj;
uint8_t v_mark_333_ = stack[1].m_num;
lean_object* v_a_334_ = stack[2].m_obj;
lean_object* v_a_335_ = stack[3].m_obj;
lean_object* v_a_336_ = stack[4].m_obj;
lean_object* v_a_337_ = stack[5].m_obj;
lean_object* v_a_338_ = stack[6].m_obj;
lean_object* v_a_339_ = stack[7].m_obj;
lean_object* v_a_340_ = stack[8].m_obj;
lean_object* v_a_341_ = stack[9].m_obj;
lean_object* v_a_342_ = stack[10].m_obj;
lean_object* v_a_343_ = stack[11].m_obj;
lean_object* v_a_344_ = stack[12].m_obj;
lean_object* v_res_413_;
v_res_413_ = l_Lean_Meta_Grind_Arith_Linear_mkVar(v_e_332_, v_mark_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_);
stack->m_obj
 = v_res_413_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar___boxed(lean_object* v_e_414_, lean_object* v_mark_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
uint8_t v_mark_boxed_428_; lean_object* v_res_429_; 
v_mark_boxed_428_ = lean_unbox(v_mark_415_);
v_res_429_ = l_Lean_Meta_Grind_Arith_Linear_mkVar(v_e_414_, v_mark_boxed_428_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_);
lean_dec(v_a_426_);
lean_dec_ref(v_a_425_);
lean_dec(v_a_424_);
lean_dec_ref(v_a_423_);
lean_dec(v_a_422_);
lean_dec_ref(v_a_421_);
lean_dec(v_a_420_);
lean_dec_ref(v_a_419_);
lean_dec(v_a_418_);
lean_dec(v_a_417_);
lean_dec(v_a_416_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0(lean_object* v_00_u03b2_430_, lean_object* v_x_431_, lean_object* v_x_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0___redArg(v_x_431_, v_x_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0___boxed(lean_object* v_00_u03b2_434_, lean_object* v_x_435_, lean_object* v_x_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0(v_00_u03b2_434_, v_x_435_, v_x_436_);
lean_dec_ref(v_x_436_);
lean_dec_ref(v_x_435_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1(lean_object* v_00_u03b2_438_, lean_object* v_x_439_, lean_object* v_x_440_, lean_object* v_x_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1___redArg(v_x_439_, v_x_440_, v_x_441_);
return v___x_442_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0(lean_object* v_00_u03b2_443_, lean_object* v_x_444_, size_t v_x_445_, lean_object* v_x_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0___redArg(v_x_444_, v_x_445_, v_x_446_);
return v___x_447_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_444_ = stack[1].m_obj;
size_t v_x_445_ = stack[2].m_num;
lean_object* v_x_446_ = stack[3].m_obj;
lean_object* v_res_448_;
v_res_448_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0(lean_box(0), v_x_444_, v_x_445_, v_x_446_);
stack->m_obj
 = v_res_448_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_449_, lean_object* v_x_450_, lean_object* v_x_451_, lean_object* v_x_452_){
_start:
{
size_t v_x_8248__boxed_453_; lean_object* v_res_454_; 
v_x_8248__boxed_453_ = lean_unbox_usize(v_x_451_);
lean_dec(v_x_451_);
v_res_454_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0(v_00_u03b2_449_, v_x_450_, v_x_8248__boxed_453_, v_x_452_);
lean_dec_ref(v_x_452_);
lean_dec_ref(v_x_450_);
return v_res_454_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2(lean_object* v_00_u03b2_455_, lean_object* v_x_456_, size_t v_x_457_, size_t v_x_458_, lean_object* v_x_459_, lean_object* v_x_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg(v_x_456_, v_x_457_, v_x_458_, v_x_459_, v_x_460_);
return v___x_461_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_456_ = stack[1].m_obj;
size_t v_x_457_ = stack[2].m_num;
size_t v_x_458_ = stack[3].m_num;
lean_object* v_x_459_ = stack[4].m_obj;
lean_object* v_x_460_ = stack[5].m_obj;
lean_object* v_res_462_;
v_res_462_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2(lean_box(0), v_x_456_, v_x_457_, v_x_458_, v_x_459_, v_x_460_);
stack->m_obj
 = v_res_462_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___boxed(lean_object* v_00_u03b2_463_, lean_object* v_x_464_, lean_object* v_x_465_, lean_object* v_x_466_, lean_object* v_x_467_, lean_object* v_x_468_){
_start:
{
size_t v_x_8266__boxed_469_; size_t v_x_8267__boxed_470_; lean_object* v_res_471_; 
v_x_8266__boxed_469_ = lean_unbox_usize(v_x_465_);
lean_dec(v_x_465_);
v_x_8267__boxed_470_ = lean_unbox_usize(v_x_466_);
lean_dec(v_x_466_);
v_res_471_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2(v_00_u03b2_463_, v_x_464_, v_x_8266__boxed_469_, v_x_8267__boxed_470_, v_x_467_, v_x_468_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_472_, lean_object* v_keys_473_, lean_object* v_vals_474_, lean_object* v_heq_475_, lean_object* v_i_476_, lean_object* v_k_477_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1___redArg(v_keys_473_, v_vals_474_, v_i_476_, v_k_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_479_, lean_object* v_keys_480_, lean_object* v_vals_481_, lean_object* v_heq_482_, lean_object* v_i_483_, lean_object* v_k_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1(v_00_u03b2_479_, v_keys_480_, v_vals_481_, v_heq_482_, v_i_483_, v_k_484_);
lean_dec_ref(v_k_484_);
lean_dec_ref(v_vals_481_);
lean_dec_ref(v_keys_480_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_486_, lean_object* v_n_487_, lean_object* v_k_488_, lean_object* v_v_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__4___redArg(v_n_487_, v_k_488_, v_v_489_);
return v___x_490_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_491_, size_t v_depth_492_, lean_object* v_keys_493_, lean_object* v_vals_494_, lean_object* v_heq_495_, lean_object* v_i_496_, lean_object* v_entries_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5___redArg(v_depth_492_, v_keys_493_, v_vals_494_, v_i_496_, v_entries_497_);
return v___x_498_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
size_t v_depth_492_ = stack[1].m_num;
lean_object* v_keys_493_ = stack[2].m_obj;
lean_object* v_vals_494_ = stack[3].m_obj;
lean_object* v_i_496_ = stack[5].m_obj;
lean_object* v_entries_497_ = stack[6].m_obj;
lean_object* v_res_499_;
v_res_499_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5(lean_box(0), v_depth_492_, v_keys_493_, v_vals_494_, lean_box(0), v_i_496_, v_entries_497_);
stack->m_obj
 = v_res_499_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_500_, lean_object* v_depth_501_, lean_object* v_keys_502_, lean_object* v_vals_503_, lean_object* v_heq_504_, lean_object* v_i_505_, lean_object* v_entries_506_){
_start:
{
size_t v_depth_boxed_507_; lean_object* v_res_508_; 
v_depth_boxed_507_ = lean_unbox_usize(v_depth_501_);
lean_dec(v_depth_501_);
v_res_508_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5(v_00_u03b2_500_, v_depth_boxed_507_, v_keys_502_, v_vals_503_, v_heq_504_, v_i_505_, v_entries_506_);
lean_dec_ref(v_vals_503_);
lean_dec_ref(v_keys_502_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_509_, lean_object* v_x_510_, lean_object* v_x_511_, lean_object* v_x_512_, lean_object* v_x_513_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__4_spec__5___redArg(v_x_510_, v_x_511_, v_x_512_, v_x_513_);
return v___x_514_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
