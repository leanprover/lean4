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
v___x_38_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg(lean_object* v_x_39_, size_t v_x_40_, size_t v_x_41_, lean_object* v_x_42_, lean_object* v_x_43_){
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5___redArg(size_t v_depth_112_, lean_object* v_keys_113_, lean_object* v_vals_114_, lean_object* v_i_115_, lean_object* v_entries_116_){
_start:
{
lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_117_ = lean_array_get_size(v_keys_113_);
v___x_118_ = lean_nat_dec_lt(v_i_115_, v___x_117_);
if (v___x_118_ == 0)
{
lean_dec(v_i_115_);
return v_entries_116_;
}
else
{
lean_object* v_k_119_; lean_object* v_v_120_; size_t v___x_121_; size_t v___x_122_; size_t v___x_123_; uint64_t v___x_124_; size_t v_h_125_; size_t v___x_126_; lean_object* v___x_127_; size_t v___x_128_; size_t v___x_129_; size_t v___x_130_; size_t v_h_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v_k_119_ = lean_array_fget_borrowed(v_keys_113_, v_i_115_);
v_v_120_ = lean_array_fget_borrowed(v_vals_114_, v_i_115_);
v___x_121_ = lean_ptr_addr(v_k_119_);
v___x_122_ = ((size_t)3ULL);
v___x_123_ = lean_usize_shift_right(v___x_121_, v___x_122_);
v___x_124_ = lean_usize_to_uint64(v___x_123_);
v_h_125_ = lean_uint64_to_usize(v___x_124_);
v___x_126_ = ((size_t)5ULL);
v___x_127_ = lean_unsigned_to_nat(1u);
v___x_128_ = ((size_t)1ULL);
v___x_129_ = lean_usize_sub(v_depth_112_, v___x_128_);
v___x_130_ = lean_usize_mul(v___x_126_, v___x_129_);
v_h_131_ = lean_usize_shift_right(v_h_125_, v___x_130_);
v___x_132_ = lean_nat_add(v_i_115_, v___x_127_);
lean_dec(v_i_115_);
lean_inc(v_v_120_);
lean_inc(v_k_119_);
v___x_133_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg(v_entries_116_, v_h_131_, v_depth_112_, v_k_119_, v_v_120_);
v_i_115_ = v___x_132_;
v_entries_116_ = v___x_133_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_135_, lean_object* v_keys_136_, lean_object* v_vals_137_, lean_object* v_i_138_, lean_object* v_entries_139_){
_start:
{
size_t v_depth_boxed_140_; lean_object* v_res_141_; 
v_depth_boxed_140_ = lean_unbox_usize(v_depth_135_);
lean_dec(v_depth_135_);
v_res_141_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5___redArg(v_depth_boxed_140_, v_keys_136_, v_vals_137_, v_i_138_, v_entries_139_);
lean_dec_ref(v_vals_137_);
lean_dec_ref(v_keys_136_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___boxed(lean_object* v_x_142_, lean_object* v_x_143_, lean_object* v_x_144_, lean_object* v_x_145_, lean_object* v_x_146_){
_start:
{
size_t v_x_7416__boxed_147_; size_t v_x_7417__boxed_148_; lean_object* v_res_149_; 
v_x_7416__boxed_147_ = lean_unbox_usize(v_x_143_);
lean_dec(v_x_143_);
v_x_7417__boxed_148_ = lean_unbox_usize(v_x_144_);
lean_dec(v_x_144_);
v_res_149_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg(v_x_142_, v_x_7416__boxed_147_, v_x_7417__boxed_148_, v_x_145_, v_x_146_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1___redArg(lean_object* v_x_150_, lean_object* v_x_151_, lean_object* v_x_152_){
_start:
{
size_t v___x_153_; size_t v___x_154_; size_t v___x_155_; uint64_t v___x_156_; size_t v___x_157_; size_t v___x_158_; lean_object* v___x_159_; 
v___x_153_ = lean_ptr_addr(v_x_151_);
v___x_154_ = ((size_t)3ULL);
v___x_155_ = lean_usize_shift_right(v___x_153_, v___x_154_);
v___x_156_ = lean_usize_to_uint64(v___x_155_);
v___x_157_ = lean_uint64_to_usize(v___x_156_);
v___x_158_ = ((size_t)1ULL);
v___x_159_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg(v_x_150_, v___x_157_, v___x_158_, v_x_151_, v_x_152_);
return v___x_159_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__0(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_160_ = lean_unsigned_to_nat(32u);
v___x_161_ = lean_mk_empty_array_with_capacity(v___x_160_);
v___x_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
return v___x_162_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__1(void){
_start:
{
size_t v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_163_ = ((size_t)5ULL);
v___x_164_ = lean_unsigned_to_nat(0u);
v___x_165_ = lean_unsigned_to_nat(32u);
v___x_166_ = lean_mk_empty_array_with_capacity(v___x_165_);
v___x_167_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__0);
v___x_168_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_168_, 0, v___x_167_);
lean_ctor_set(v___x_168_, 1, v___x_166_);
lean_ctor_set(v___x_168_, 2, v___x_164_);
lean_ctor_set(v___x_168_, 3, v___x_164_);
lean_ctor_set_usize(v___x_168_, 4, v___x_163_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0(lean_object* v_a_169_, lean_object* v_e_170_, lean_object* v_size_171_, lean_object* v_s_172_){
_start:
{
lean_object* v_structs_173_; lean_object* v_typeIdOf_174_; lean_object* v_exprToStructId_175_; lean_object* v_exprToStructIdEntries_176_; lean_object* v_forbiddenNatModules_177_; lean_object* v_natStructs_178_; lean_object* v_natTypeIdOf_179_; lean_object* v_exprToNatStructId_180_; lean_object* v___x_181_; uint8_t v___x_182_; 
v_structs_173_ = lean_ctor_get(v_s_172_, 0);
v_typeIdOf_174_ = lean_ctor_get(v_s_172_, 1);
v_exprToStructId_175_ = lean_ctor_get(v_s_172_, 2);
v_exprToStructIdEntries_176_ = lean_ctor_get(v_s_172_, 3);
v_forbiddenNatModules_177_ = lean_ctor_get(v_s_172_, 4);
v_natStructs_178_ = lean_ctor_get(v_s_172_, 5);
v_natTypeIdOf_179_ = lean_ctor_get(v_s_172_, 6);
v_exprToNatStructId_180_ = lean_ctor_get(v_s_172_, 7);
v___x_181_ = lean_array_get_size(v_structs_173_);
v___x_182_ = lean_nat_dec_lt(v_a_169_, v___x_181_);
if (v___x_182_ == 0)
{
lean_dec(v_size_171_);
lean_dec_ref(v_e_170_);
return v_s_172_;
}
else
{
lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_253_; 
lean_inc_ref(v_exprToNatStructId_180_);
lean_inc_ref(v_natTypeIdOf_179_);
lean_inc_ref(v_natStructs_178_);
lean_inc_ref(v_forbiddenNatModules_177_);
lean_inc_ref(v_exprToStructIdEntries_176_);
lean_inc_ref(v_exprToStructId_175_);
lean_inc_ref(v_typeIdOf_174_);
lean_inc_ref(v_structs_173_);
v_isSharedCheck_253_ = !lean_is_exclusive(v_s_172_);
if (v_isSharedCheck_253_ == 0)
{
lean_object* v_unused_254_; lean_object* v_unused_255_; lean_object* v_unused_256_; lean_object* v_unused_257_; lean_object* v_unused_258_; lean_object* v_unused_259_; lean_object* v_unused_260_; lean_object* v_unused_261_; 
v_unused_254_ = lean_ctor_get(v_s_172_, 7);
lean_dec(v_unused_254_);
v_unused_255_ = lean_ctor_get(v_s_172_, 6);
lean_dec(v_unused_255_);
v_unused_256_ = lean_ctor_get(v_s_172_, 5);
lean_dec(v_unused_256_);
v_unused_257_ = lean_ctor_get(v_s_172_, 4);
lean_dec(v_unused_257_);
v_unused_258_ = lean_ctor_get(v_s_172_, 3);
lean_dec(v_unused_258_);
v_unused_259_ = lean_ctor_get(v_s_172_, 2);
lean_dec(v_unused_259_);
v_unused_260_ = lean_ctor_get(v_s_172_, 1);
lean_dec(v_unused_260_);
v_unused_261_ = lean_ctor_get(v_s_172_, 0);
lean_dec(v_unused_261_);
v___x_184_ = v_s_172_;
v_isShared_185_ = v_isSharedCheck_253_;
goto v_resetjp_183_;
}
else
{
lean_dec(v_s_172_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_253_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v_v_186_; lean_object* v_id_187_; lean_object* v_ringId_x3f_188_; lean_object* v_type_189_; lean_object* v_u_190_; lean_object* v_intModuleInst_191_; lean_object* v_leInst_x3f_192_; lean_object* v_ltInst_x3f_193_; lean_object* v_lawfulOrderLTInst_x3f_194_; lean_object* v_isPreorderInst_x3f_195_; lean_object* v_orderedAddInst_x3f_196_; lean_object* v_isLinearInst_x3f_197_; lean_object* v_noNatDivInst_x3f_198_; lean_object* v_ringInst_x3f_199_; lean_object* v_commRingInst_x3f_200_; lean_object* v_orderedRingInst_x3f_201_; lean_object* v_fieldInst_x3f_202_; lean_object* v_charInst_x3f_203_; lean_object* v_zero_204_; lean_object* v_ofNatZero_205_; lean_object* v_one_x3f_206_; lean_object* v_leFn_x3f_207_; lean_object* v_ltFn_x3f_208_; lean_object* v_addFn_209_; lean_object* v_zsmulFn_210_; lean_object* v_nsmulFn_211_; lean_object* v_zsmulFn_x3f_212_; lean_object* v_nsmulFn_x3f_213_; lean_object* v_homomulFn_x3f_214_; lean_object* v_subFn_215_; lean_object* v_negFn_216_; lean_object* v_vars_217_; lean_object* v_varMap_218_; lean_object* v_lowers_219_; lean_object* v_uppers_220_; lean_object* v_diseqs_221_; lean_object* v_assignment_222_; uint8_t v_caseSplits_223_; lean_object* v_conflict_x3f_224_; lean_object* v_diseqSplits_225_; lean_object* v_elimEqs_226_; lean_object* v_elimStack_227_; lean_object* v_occurs_228_; lean_object* v_ignored_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_252_; 
v_v_186_ = lean_array_fget(v_structs_173_, v_a_169_);
v_id_187_ = lean_ctor_get(v_v_186_, 0);
v_ringId_x3f_188_ = lean_ctor_get(v_v_186_, 1);
v_type_189_ = lean_ctor_get(v_v_186_, 2);
v_u_190_ = lean_ctor_get(v_v_186_, 3);
v_intModuleInst_191_ = lean_ctor_get(v_v_186_, 4);
v_leInst_x3f_192_ = lean_ctor_get(v_v_186_, 5);
v_ltInst_x3f_193_ = lean_ctor_get(v_v_186_, 6);
v_lawfulOrderLTInst_x3f_194_ = lean_ctor_get(v_v_186_, 7);
v_isPreorderInst_x3f_195_ = lean_ctor_get(v_v_186_, 8);
v_orderedAddInst_x3f_196_ = lean_ctor_get(v_v_186_, 9);
v_isLinearInst_x3f_197_ = lean_ctor_get(v_v_186_, 10);
v_noNatDivInst_x3f_198_ = lean_ctor_get(v_v_186_, 11);
v_ringInst_x3f_199_ = lean_ctor_get(v_v_186_, 12);
v_commRingInst_x3f_200_ = lean_ctor_get(v_v_186_, 13);
v_orderedRingInst_x3f_201_ = lean_ctor_get(v_v_186_, 14);
v_fieldInst_x3f_202_ = lean_ctor_get(v_v_186_, 15);
v_charInst_x3f_203_ = lean_ctor_get(v_v_186_, 16);
v_zero_204_ = lean_ctor_get(v_v_186_, 17);
v_ofNatZero_205_ = lean_ctor_get(v_v_186_, 18);
v_one_x3f_206_ = lean_ctor_get(v_v_186_, 19);
v_leFn_x3f_207_ = lean_ctor_get(v_v_186_, 20);
v_ltFn_x3f_208_ = lean_ctor_get(v_v_186_, 21);
v_addFn_209_ = lean_ctor_get(v_v_186_, 22);
v_zsmulFn_210_ = lean_ctor_get(v_v_186_, 23);
v_nsmulFn_211_ = lean_ctor_get(v_v_186_, 24);
v_zsmulFn_x3f_212_ = lean_ctor_get(v_v_186_, 25);
v_nsmulFn_x3f_213_ = lean_ctor_get(v_v_186_, 26);
v_homomulFn_x3f_214_ = lean_ctor_get(v_v_186_, 27);
v_subFn_215_ = lean_ctor_get(v_v_186_, 28);
v_negFn_216_ = lean_ctor_get(v_v_186_, 29);
v_vars_217_ = lean_ctor_get(v_v_186_, 30);
v_varMap_218_ = lean_ctor_get(v_v_186_, 31);
v_lowers_219_ = lean_ctor_get(v_v_186_, 32);
v_uppers_220_ = lean_ctor_get(v_v_186_, 33);
v_diseqs_221_ = lean_ctor_get(v_v_186_, 34);
v_assignment_222_ = lean_ctor_get(v_v_186_, 35);
v_caseSplits_223_ = lean_ctor_get_uint8(v_v_186_, sizeof(void*)*42);
v_conflict_x3f_224_ = lean_ctor_get(v_v_186_, 36);
v_diseqSplits_225_ = lean_ctor_get(v_v_186_, 37);
v_elimEqs_226_ = lean_ctor_get(v_v_186_, 38);
v_elimStack_227_ = lean_ctor_get(v_v_186_, 39);
v_occurs_228_ = lean_ctor_get(v_v_186_, 40);
v_ignored_229_ = lean_ctor_get(v_v_186_, 41);
v_isSharedCheck_252_ = !lean_is_exclusive(v_v_186_);
if (v_isSharedCheck_252_ == 0)
{
v___x_231_ = v_v_186_;
v_isShared_232_ = v_isSharedCheck_252_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_ignored_229_);
lean_inc(v_occurs_228_);
lean_inc(v_elimStack_227_);
lean_inc(v_elimEqs_226_);
lean_inc(v_diseqSplits_225_);
lean_inc(v_conflict_x3f_224_);
lean_inc(v_assignment_222_);
lean_inc(v_diseqs_221_);
lean_inc(v_uppers_220_);
lean_inc(v_lowers_219_);
lean_inc(v_varMap_218_);
lean_inc(v_vars_217_);
lean_inc(v_negFn_216_);
lean_inc(v_subFn_215_);
lean_inc(v_homomulFn_x3f_214_);
lean_inc(v_nsmulFn_x3f_213_);
lean_inc(v_zsmulFn_x3f_212_);
lean_inc(v_nsmulFn_211_);
lean_inc(v_zsmulFn_210_);
lean_inc(v_addFn_209_);
lean_inc(v_ltFn_x3f_208_);
lean_inc(v_leFn_x3f_207_);
lean_inc(v_one_x3f_206_);
lean_inc(v_ofNatZero_205_);
lean_inc(v_zero_204_);
lean_inc(v_charInst_x3f_203_);
lean_inc(v_fieldInst_x3f_202_);
lean_inc(v_orderedRingInst_x3f_201_);
lean_inc(v_commRingInst_x3f_200_);
lean_inc(v_ringInst_x3f_199_);
lean_inc(v_noNatDivInst_x3f_198_);
lean_inc(v_isLinearInst_x3f_197_);
lean_inc(v_orderedAddInst_x3f_196_);
lean_inc(v_isPreorderInst_x3f_195_);
lean_inc(v_lawfulOrderLTInst_x3f_194_);
lean_inc(v_ltInst_x3f_193_);
lean_inc(v_leInst_x3f_192_);
lean_inc(v_intModuleInst_191_);
lean_inc(v_u_190_);
lean_inc(v_type_189_);
lean_inc(v_ringId_x3f_188_);
lean_inc(v_id_187_);
lean_dec(v_v_186_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_252_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_233_; lean_object* v_xs_x27_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_246_; 
v___x_233_ = lean_box(0);
v_xs_x27_234_ = lean_array_fset(v_structs_173_, v_a_169_, v___x_233_);
lean_inc_ref(v_e_170_);
v___x_235_ = l_Lean_PersistentArray_push___redArg(v_vars_217_, v_e_170_);
v___x_236_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1___redArg(v_varMap_218_, v_e_170_, v_size_171_);
v___x_237_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__1);
v___x_238_ = l_Lean_PersistentArray_push___redArg(v_lowers_219_, v___x_237_);
v___x_239_ = l_Lean_PersistentArray_push___redArg(v_uppers_220_, v___x_237_);
v___x_240_ = l_Lean_PersistentArray_push___redArg(v_diseqs_221_, v___x_237_);
v___x_241_ = lean_box(0);
v___x_242_ = l_Lean_PersistentArray_push___redArg(v_elimEqs_226_, v___x_241_);
v___x_243_ = lean_box(1);
v___x_244_ = l_Lean_PersistentArray_push___redArg(v_occurs_228_, v___x_243_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 40, v___x_244_);
lean_ctor_set(v___x_231_, 38, v___x_242_);
lean_ctor_set(v___x_231_, 34, v___x_240_);
lean_ctor_set(v___x_231_, 33, v___x_239_);
lean_ctor_set(v___x_231_, 32, v___x_238_);
lean_ctor_set(v___x_231_, 31, v___x_236_);
lean_ctor_set(v___x_231_, 30, v___x_235_);
v___x_246_ = v___x_231_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_id_187_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v_ringId_x3f_188_);
lean_ctor_set(v_reuseFailAlloc_251_, 2, v_type_189_);
lean_ctor_set(v_reuseFailAlloc_251_, 3, v_u_190_);
lean_ctor_set(v_reuseFailAlloc_251_, 4, v_intModuleInst_191_);
lean_ctor_set(v_reuseFailAlloc_251_, 5, v_leInst_x3f_192_);
lean_ctor_set(v_reuseFailAlloc_251_, 6, v_ltInst_x3f_193_);
lean_ctor_set(v_reuseFailAlloc_251_, 7, v_lawfulOrderLTInst_x3f_194_);
lean_ctor_set(v_reuseFailAlloc_251_, 8, v_isPreorderInst_x3f_195_);
lean_ctor_set(v_reuseFailAlloc_251_, 9, v_orderedAddInst_x3f_196_);
lean_ctor_set(v_reuseFailAlloc_251_, 10, v_isLinearInst_x3f_197_);
lean_ctor_set(v_reuseFailAlloc_251_, 11, v_noNatDivInst_x3f_198_);
lean_ctor_set(v_reuseFailAlloc_251_, 12, v_ringInst_x3f_199_);
lean_ctor_set(v_reuseFailAlloc_251_, 13, v_commRingInst_x3f_200_);
lean_ctor_set(v_reuseFailAlloc_251_, 14, v_orderedRingInst_x3f_201_);
lean_ctor_set(v_reuseFailAlloc_251_, 15, v_fieldInst_x3f_202_);
lean_ctor_set(v_reuseFailAlloc_251_, 16, v_charInst_x3f_203_);
lean_ctor_set(v_reuseFailAlloc_251_, 17, v_zero_204_);
lean_ctor_set(v_reuseFailAlloc_251_, 18, v_ofNatZero_205_);
lean_ctor_set(v_reuseFailAlloc_251_, 19, v_one_x3f_206_);
lean_ctor_set(v_reuseFailAlloc_251_, 20, v_leFn_x3f_207_);
lean_ctor_set(v_reuseFailAlloc_251_, 21, v_ltFn_x3f_208_);
lean_ctor_set(v_reuseFailAlloc_251_, 22, v_addFn_209_);
lean_ctor_set(v_reuseFailAlloc_251_, 23, v_zsmulFn_210_);
lean_ctor_set(v_reuseFailAlloc_251_, 24, v_nsmulFn_211_);
lean_ctor_set(v_reuseFailAlloc_251_, 25, v_zsmulFn_x3f_212_);
lean_ctor_set(v_reuseFailAlloc_251_, 26, v_nsmulFn_x3f_213_);
lean_ctor_set(v_reuseFailAlloc_251_, 27, v_homomulFn_x3f_214_);
lean_ctor_set(v_reuseFailAlloc_251_, 28, v_subFn_215_);
lean_ctor_set(v_reuseFailAlloc_251_, 29, v_negFn_216_);
lean_ctor_set(v_reuseFailAlloc_251_, 30, v___x_235_);
lean_ctor_set(v_reuseFailAlloc_251_, 31, v___x_236_);
lean_ctor_set(v_reuseFailAlloc_251_, 32, v___x_238_);
lean_ctor_set(v_reuseFailAlloc_251_, 33, v___x_239_);
lean_ctor_set(v_reuseFailAlloc_251_, 34, v___x_240_);
lean_ctor_set(v_reuseFailAlloc_251_, 35, v_assignment_222_);
lean_ctor_set(v_reuseFailAlloc_251_, 36, v_conflict_x3f_224_);
lean_ctor_set(v_reuseFailAlloc_251_, 37, v_diseqSplits_225_);
lean_ctor_set(v_reuseFailAlloc_251_, 38, v___x_242_);
lean_ctor_set(v_reuseFailAlloc_251_, 39, v_elimStack_227_);
lean_ctor_set(v_reuseFailAlloc_251_, 40, v___x_244_);
lean_ctor_set(v_reuseFailAlloc_251_, 41, v_ignored_229_);
lean_ctor_set_uint8(v_reuseFailAlloc_251_, sizeof(void*)*42, v_caseSplits_223_);
v___x_246_ = v_reuseFailAlloc_251_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
lean_object* v___x_247_; lean_object* v___x_249_; 
v___x_247_ = lean_array_fset(v_xs_x27_234_, v_a_169_, v___x_246_);
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 0, v___x_247_);
v___x_249_ = v___x_184_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_247_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v_typeIdOf_174_);
lean_ctor_set(v_reuseFailAlloc_250_, 2, v_exprToStructId_175_);
lean_ctor_set(v_reuseFailAlloc_250_, 3, v_exprToStructIdEntries_176_);
lean_ctor_set(v_reuseFailAlloc_250_, 4, v_forbiddenNatModules_177_);
lean_ctor_set(v_reuseFailAlloc_250_, 5, v_natStructs_178_);
lean_ctor_set(v_reuseFailAlloc_250_, 6, v_natTypeIdOf_179_);
lean_ctor_set(v_reuseFailAlloc_250_, 7, v_exprToNatStructId_180_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___boxed(lean_object* v_a_262_, lean_object* v_e_263_, lean_object* v_size_264_, lean_object* v_s_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0(v_a_262_, v_e_263_, v_size_264_, v_s_265_);
lean_dec(v_a_262_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_267_, lean_object* v_vals_268_, lean_object* v_i_269_, lean_object* v_k_270_){
_start:
{
lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_271_ = lean_array_get_size(v_keys_267_);
v___x_272_ = lean_nat_dec_lt(v_i_269_, v___x_271_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; 
lean_dec(v_i_269_);
v___x_273_ = lean_box(0);
return v___x_273_;
}
else
{
lean_object* v_k_x27_274_; size_t v___x_275_; size_t v___x_276_; uint8_t v___x_277_; 
v_k_x27_274_ = lean_array_fget_borrowed(v_keys_267_, v_i_269_);
v___x_275_ = lean_ptr_addr(v_k_270_);
v___x_276_ = lean_ptr_addr(v_k_x27_274_);
v___x_277_ = lean_usize_dec_eq(v___x_275_, v___x_276_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = lean_unsigned_to_nat(1u);
v___x_279_ = lean_nat_add(v_i_269_, v___x_278_);
lean_dec(v_i_269_);
v_i_269_ = v___x_279_;
goto _start;
}
else
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = lean_array_fget_borrowed(v_vals_268_, v_i_269_);
lean_dec(v_i_269_);
lean_inc(v___x_281_);
v___x_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
return v___x_282_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_283_, lean_object* v_vals_284_, lean_object* v_i_285_, lean_object* v_k_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1___redArg(v_keys_283_, v_vals_284_, v_i_285_, v_k_286_);
lean_dec_ref(v_k_286_);
lean_dec_ref(v_vals_284_);
lean_dec_ref(v_keys_283_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0___redArg(lean_object* v_x_288_, size_t v_x_289_, lean_object* v_x_290_){
_start:
{
if (lean_obj_tag(v_x_288_) == 0)
{
lean_object* v_es_291_; lean_object* v___x_292_; size_t v___x_293_; size_t v___x_294_; lean_object* v_j_295_; lean_object* v___x_296_; 
v_es_291_ = lean_ctor_get(v_x_288_, 0);
v___x_292_ = lean_box(2);
v___x_293_ = ((size_t)31ULL);
v___x_294_ = lean_usize_land(v_x_289_, v___x_293_);
v_j_295_ = lean_usize_to_nat(v___x_294_);
v___x_296_ = lean_array_get_borrowed(v___x_292_, v_es_291_, v_j_295_);
lean_dec(v_j_295_);
switch(lean_obj_tag(v___x_296_))
{
case 0:
{
lean_object* v_key_297_; lean_object* v_val_298_; size_t v___x_299_; size_t v___x_300_; uint8_t v___x_301_; 
v_key_297_ = lean_ctor_get(v___x_296_, 0);
v_val_298_ = lean_ctor_get(v___x_296_, 1);
v___x_299_ = lean_ptr_addr(v_x_290_);
v___x_300_ = lean_ptr_addr(v_key_297_);
v___x_301_ = lean_usize_dec_eq(v___x_299_, v___x_300_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; 
v___x_302_ = lean_box(0);
return v___x_302_;
}
else
{
lean_object* v___x_303_; 
lean_inc(v_val_298_);
v___x_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_303_, 0, v_val_298_);
return v___x_303_;
}
}
case 1:
{
lean_object* v_node_304_; size_t v___x_305_; size_t v___x_306_; 
v_node_304_ = lean_ctor_get(v___x_296_, 0);
v___x_305_ = ((size_t)5ULL);
v___x_306_ = lean_usize_shift_right(v_x_289_, v___x_305_);
v_x_288_ = v_node_304_;
v_x_289_ = v___x_306_;
goto _start;
}
default: 
{
lean_object* v___x_308_; 
v___x_308_ = lean_box(0);
return v___x_308_;
}
}
}
else
{
lean_object* v_ks_309_; lean_object* v_vs_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v_ks_309_ = lean_ctor_get(v_x_288_, 0);
v_vs_310_ = lean_ctor_get(v_x_288_, 1);
v___x_311_ = lean_unsigned_to_nat(0u);
v___x_312_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1___redArg(v_ks_309_, v_vs_310_, v___x_311_, v_x_290_);
return v___x_312_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0___redArg___boxed(lean_object* v_x_313_, lean_object* v_x_314_, lean_object* v_x_315_){
_start:
{
size_t v_x_7718__boxed_316_; lean_object* v_res_317_; 
v_x_7718__boxed_316_ = lean_unbox_usize(v_x_314_);
lean_dec(v_x_314_);
v_res_317_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0___redArg(v_x_313_, v_x_7718__boxed_316_, v_x_315_);
lean_dec_ref(v_x_315_);
lean_dec_ref(v_x_313_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0___redArg(lean_object* v_x_318_, lean_object* v_x_319_){
_start:
{
size_t v___x_320_; size_t v___x_321_; size_t v___x_322_; uint64_t v___x_323_; size_t v___x_324_; lean_object* v___x_325_; 
v___x_320_ = lean_ptr_addr(v_x_319_);
v___x_321_ = ((size_t)3ULL);
v___x_322_ = lean_usize_shift_right(v___x_320_, v___x_321_);
v___x_323_ = lean_usize_to_uint64(v___x_322_);
v___x_324_ = lean_uint64_to_usize(v___x_323_);
v___x_325_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0___redArg(v_x_318_, v___x_324_, v_x_319_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0___redArg___boxed(lean_object* v_x_326_, lean_object* v_x_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0___redArg(v_x_326_, v_x_327_);
lean_dec_ref(v_x_327_);
lean_dec_ref(v_x_326_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar(lean_object* v_e_329_, uint8_t v_mark_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_401_; 
v_a_344_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_401_ == 0)
{
v___x_346_ = v___x_343_;
v_isShared_347_ = v_isSharedCheck_401_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_343_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_401_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v_vars_348_; lean_object* v_varMap_349_; lean_object* v___x_350_; 
v_vars_348_ = lean_ctor_get(v_a_344_, 30);
lean_inc_ref(v_vars_348_);
v_varMap_349_ = lean_ctor_get(v_a_344_, 31);
lean_inc_ref(v_varMap_349_);
lean_dec(v_a_344_);
v___x_350_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0___redArg(v_varMap_349_, v_e_329_);
lean_dec_ref(v_varMap_349_);
if (lean_obj_tag(v___x_350_) == 1)
{
lean_object* v_val_351_; lean_object* v___x_353_; 
lean_dec_ref(v_vars_348_);
lean_dec_ref(v_e_329_);
v_val_351_ = lean_ctor_get(v___x_350_, 0);
lean_inc(v_val_351_);
lean_dec_ref_known(v___x_350_, 1);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 0, v_val_351_);
v___x_353_ = v___x_346_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_val_351_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
else
{
lean_object* v_size_355_; lean_object* v___f_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
lean_dec(v___x_350_);
lean_del_object(v___x_346_);
v_size_355_ = lean_ctor_get(v_vars_348_, 2);
lean_inc_n(v_size_355_, 2);
lean_dec_ref(v_vars_348_);
lean_inc_ref(v_e_329_);
lean_inc(v_a_331_);
v___f_356_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___boxed), 4, 3);
lean_closure_set(v___f_356_, 0, v_a_331_);
lean_closure_set(v___f_356_, 1, v_e_329_);
lean_closure_set(v___f_356_, 2, v_size_355_);
v___x_357_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_358_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_357_, v___f_356_, v_a_332_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v___x_359_; 
lean_dec_ref_known(v___x_358_, 1);
lean_inc_ref(v_e_329_);
v___x_359_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg(v_e_329_, v_a_331_, v_a_332_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_);
if (lean_obj_tag(v___x_359_) == 0)
{
lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_383_; 
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_383_ == 0)
{
lean_object* v_unused_384_; 
v_unused_384_ = lean_ctor_get(v___x_359_, 0);
lean_dec(v_unused_384_);
v___x_361_ = v___x_359_;
v_isShared_362_ = v_isSharedCheck_383_;
goto v_resetjp_360_;
}
else
{
lean_dec(v___x_359_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_383_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
if (v_mark_330_ == 0)
{
lean_object* v___x_364_; 
lean_dec_ref(v_e_329_);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 0, v_size_355_);
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_size_355_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
else
{
lean_object* v___x_366_; 
lean_del_object(v___x_361_);
v___x_366_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_357_, v_e_329_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_373_; 
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_373_ == 0)
{
lean_object* v_unused_374_; 
v_unused_374_ = lean_ctor_get(v___x_366_, 0);
lean_dec(v_unused_374_);
v___x_368_ = v___x_366_;
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
else
{
lean_dec(v___x_366_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v_size_355_);
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_size_355_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
else
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_382_; 
lean_dec(v_size_355_);
v_a_375_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_382_ == 0)
{
v___x_377_ = v___x_366_;
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_366_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_380_; 
if (v_isShared_378_ == 0)
{
v___x_380_ = v___x_377_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_375_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
}
}
else
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
lean_dec(v_size_355_);
lean_dec_ref(v_e_329_);
v_a_385_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v___x_359_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_359_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_385_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
else
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
lean_dec(v_size_355_);
lean_dec_ref(v_e_329_);
v_a_393_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_358_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_358_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
}
}
else
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_409_; 
lean_dec_ref(v_e_329_);
v_a_402_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_409_ == 0)
{
v___x_404_ = v___x_343_;
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_343_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
if (v_isShared_405_ == 0)
{
v___x_407_ = v___x_404_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_a_402_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar___boxed(lean_object* v_e_410_, lean_object* v_mark_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_){
_start:
{
uint8_t v_mark_boxed_424_; lean_object* v_res_425_; 
v_mark_boxed_424_ = lean_unbox(v_mark_411_);
v_res_425_ = l_Lean_Meta_Grind_Arith_Linear_mkVar(v_e_410_, v_mark_boxed_424_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_);
lean_dec(v_a_422_);
lean_dec_ref(v_a_421_);
lean_dec(v_a_420_);
lean_dec_ref(v_a_419_);
lean_dec(v_a_418_);
lean_dec_ref(v_a_417_);
lean_dec(v_a_416_);
lean_dec_ref(v_a_415_);
lean_dec(v_a_414_);
lean_dec(v_a_413_);
lean_dec(v_a_412_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0(lean_object* v_00_u03b2_426_, lean_object* v_x_427_, lean_object* v_x_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0___redArg(v_x_427_, v_x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0___boxed(lean_object* v_00_u03b2_430_, lean_object* v_x_431_, lean_object* v_x_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0(v_00_u03b2_430_, v_x_431_, v_x_432_);
lean_dec_ref(v_x_432_);
lean_dec_ref(v_x_431_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1(lean_object* v_00_u03b2_434_, lean_object* v_x_435_, lean_object* v_x_436_, lean_object* v_x_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1___redArg(v_x_435_, v_x_436_, v_x_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0(lean_object* v_00_u03b2_439_, lean_object* v_x_440_, size_t v_x_441_, lean_object* v_x_442_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0___redArg(v_x_440_, v_x_441_, v_x_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_444_, lean_object* v_x_445_, lean_object* v_x_446_, lean_object* v_x_447_){
_start:
{
size_t v_x_7936__boxed_448_; lean_object* v_res_449_; 
v_x_7936__boxed_448_ = lean_unbox_usize(v_x_446_);
lean_dec(v_x_446_);
v_res_449_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0(v_00_u03b2_444_, v_x_445_, v_x_7936__boxed_448_, v_x_447_);
lean_dec_ref(v_x_447_);
lean_dec_ref(v_x_445_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2(lean_object* v_00_u03b2_450_, lean_object* v_x_451_, size_t v_x_452_, size_t v_x_453_, lean_object* v_x_454_, lean_object* v_x_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg(v_x_451_, v_x_452_, v_x_453_, v_x_454_, v_x_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___boxed(lean_object* v_00_u03b2_457_, lean_object* v_x_458_, lean_object* v_x_459_, lean_object* v_x_460_, lean_object* v_x_461_, lean_object* v_x_462_){
_start:
{
size_t v_x_7947__boxed_463_; size_t v_x_7948__boxed_464_; lean_object* v_res_465_; 
v_x_7947__boxed_463_ = lean_unbox_usize(v_x_459_);
lean_dec(v_x_459_);
v_x_7948__boxed_464_ = lean_unbox_usize(v_x_460_);
lean_dec(v_x_460_);
v_res_465_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2(v_00_u03b2_457_, v_x_458_, v_x_7947__boxed_463_, v_x_7948__boxed_464_, v_x_461_, v_x_462_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_466_, lean_object* v_keys_467_, lean_object* v_vals_468_, lean_object* v_heq_469_, lean_object* v_i_470_, lean_object* v_k_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1___redArg(v_keys_467_, v_vals_468_, v_i_470_, v_k_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_473_, lean_object* v_keys_474_, lean_object* v_vals_475_, lean_object* v_heq_476_, lean_object* v_i_477_, lean_object* v_k_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1(v_00_u03b2_473_, v_keys_474_, v_vals_475_, v_heq_476_, v_i_477_, v_k_478_);
lean_dec_ref(v_k_478_);
lean_dec_ref(v_vals_475_);
lean_dec_ref(v_keys_474_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_480_, lean_object* v_n_481_, lean_object* v_k_482_, lean_object* v_v_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__4___redArg(v_n_481_, v_k_482_, v_v_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_485_, size_t v_depth_486_, lean_object* v_keys_487_, lean_object* v_vals_488_, lean_object* v_heq_489_, lean_object* v_i_490_, lean_object* v_entries_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5___redArg(v_depth_486_, v_keys_487_, v_vals_488_, v_i_490_, v_entries_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_493_, lean_object* v_depth_494_, lean_object* v_keys_495_, lean_object* v_vals_496_, lean_object* v_heq_497_, lean_object* v_i_498_, lean_object* v_entries_499_){
_start:
{
size_t v_depth_boxed_500_; lean_object* v_res_501_; 
v_depth_boxed_500_ = lean_unbox_usize(v_depth_494_);
lean_dec(v_depth_494_);
v_res_501_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5(v_00_u03b2_493_, v_depth_boxed_500_, v_keys_495_, v_vals_496_, v_heq_497_, v_i_498_, v_entries_499_);
lean_dec_ref(v_vals_496_);
lean_dec_ref(v_keys_495_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_502_, lean_object* v_x_503_, lean_object* v_x_504_, lean_object* v_x_505_, lean_object* v_x_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__4_spec__5___redArg(v_x_503_, v_x_504_, v_x_505_, v_x_506_);
return v___x_507_;
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
