// Lean compiler output
// Module: Lean.Meta.Sym.MaxFVar
// Imports: public import Lean.Meta.Sym.SymM
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
lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg();
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
lean_object* l_Lean_LocalContext_lastDecl(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed(lean_object*);
lean_object* l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_getMaxFVar_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Meta.Sym.MaxFVar"};
static const lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_getMaxFVar_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_getMaxFVar_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Meta.Sym.getMaxFVar\?"};
static const lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_getMaxFVar_x3f___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_getMaxFVar_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_getMaxFVar_x3f___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(lean_object* v_fvarId1_x3f_1_, lean_object* v_fvarId2_x3f_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_){
_start:
{
if (lean_obj_tag(v_fvarId1_x3f_1_) == 1)
{
if (lean_obj_tag(v_fvarId2_x3f_2_) == 1)
{
lean_object* v_val_7_; lean_object* v_val_8_; uint8_t v___x_9_; 
v_val_7_ = lean_ctor_get(v_fvarId1_x3f_1_, 0);
v_val_8_ = lean_ctor_get(v_fvarId2_x3f_2_, 0);
v___x_9_ = l_Lean_instBEqFVarId_beq(v_val_7_, v_val_8_);
if (v___x_9_ == 0)
{
lean_object* v___x_10_; 
lean_inc(v_val_7_);
v___x_10_ = l_Lean_FVarId_getDecl___redArg(v_val_7_, v_a_3_, v_a_4_, v_a_5_);
if (lean_obj_tag(v___x_10_) == 0)
{
lean_object* v_a_11_; lean_object* v___x_12_; 
v_a_11_ = lean_ctor_get(v___x_10_, 0);
lean_inc(v_a_11_);
lean_dec_ref_known(v___x_10_, 1);
lean_inc(v_val_8_);
v___x_12_ = l_Lean_FVarId_getDecl___redArg(v_val_8_, v_a_3_, v_a_4_, v_a_5_);
if (lean_obj_tag(v___x_12_) == 0)
{
lean_object* v_a_13_; lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_26_; 
v_a_13_ = lean_ctor_get(v___x_12_, 0);
v_isSharedCheck_26_ = !lean_is_exclusive(v___x_12_);
if (v_isSharedCheck_26_ == 0)
{
v___x_15_ = v___x_12_;
v_isShared_16_ = v_isSharedCheck_26_;
goto v_resetjp_14_;
}
else
{
lean_inc(v_a_13_);
lean_dec(v___x_12_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_26_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_17_; lean_object* v___x_18_; uint8_t v___x_19_; 
v___x_17_ = l_Lean_LocalDecl_index(v_a_13_);
lean_dec(v_a_13_);
v___x_18_ = l_Lean_LocalDecl_index(v_a_11_);
lean_dec(v_a_11_);
v___x_19_ = lean_nat_dec_lt(v___x_17_, v___x_18_);
lean_dec(v___x_18_);
lean_dec(v___x_17_);
if (v___x_19_ == 0)
{
lean_object* v___x_21_; 
lean_dec_ref_known(v_fvarId1_x3f_1_, 1);
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v_fvarId2_x3f_2_);
v___x_21_ = v___x_15_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_fvarId2_x3f_2_);
v___x_21_ = v_reuseFailAlloc_22_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
return v___x_21_;
}
}
else
{
lean_object* v___x_24_; 
lean_dec_ref_known(v_fvarId2_x3f_2_, 1);
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v_fvarId1_x3f_1_);
v___x_24_ = v___x_15_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_25_; 
v_reuseFailAlloc_25_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_25_, 0, v_fvarId1_x3f_1_);
v___x_24_ = v_reuseFailAlloc_25_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
return v___x_24_;
}
}
}
}
else
{
lean_object* v_a_27_; lean_object* v___x_29_; uint8_t v_isShared_30_; uint8_t v_isSharedCheck_34_; 
lean_dec(v_a_11_);
lean_dec_ref_known(v_fvarId2_x3f_2_, 1);
lean_dec_ref_known(v_fvarId1_x3f_1_, 1);
v_a_27_ = lean_ctor_get(v___x_12_, 0);
v_isSharedCheck_34_ = !lean_is_exclusive(v___x_12_);
if (v_isSharedCheck_34_ == 0)
{
v___x_29_ = v___x_12_;
v_isShared_30_ = v_isSharedCheck_34_;
goto v_resetjp_28_;
}
else
{
lean_inc(v_a_27_);
lean_dec(v___x_12_);
v___x_29_ = lean_box(0);
v_isShared_30_ = v_isSharedCheck_34_;
goto v_resetjp_28_;
}
v_resetjp_28_:
{
lean_object* v___x_32_; 
if (v_isShared_30_ == 0)
{
v___x_32_ = v___x_29_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v_a_27_);
v___x_32_ = v_reuseFailAlloc_33_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
return v___x_32_;
}
}
}
}
else
{
lean_object* v_a_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_42_; 
lean_dec_ref_known(v_fvarId2_x3f_2_, 1);
lean_dec_ref_known(v_fvarId1_x3f_1_, 1);
v_a_35_ = lean_ctor_get(v___x_10_, 0);
v_isSharedCheck_42_ = !lean_is_exclusive(v___x_10_);
if (v_isSharedCheck_42_ == 0)
{
v___x_37_ = v___x_10_;
v_isShared_38_ = v_isSharedCheck_42_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_a_35_);
lean_dec(v___x_10_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_42_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_40_; 
if (v_isShared_38_ == 0)
{
v___x_40_ = v___x_37_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v_a_35_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
}
}
else
{
lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_49_; 
v_isSharedCheck_49_ = !lean_is_exclusive(v_fvarId2_x3f_2_);
if (v_isSharedCheck_49_ == 0)
{
lean_object* v_unused_50_; 
v_unused_50_ = lean_ctor_get(v_fvarId2_x3f_2_, 0);
lean_dec(v_unused_50_);
v___x_44_ = v_fvarId2_x3f_2_;
v_isShared_45_ = v_isSharedCheck_49_;
goto v_resetjp_43_;
}
else
{
lean_dec(v_fvarId2_x3f_2_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_49_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v___x_47_; 
if (v_isShared_45_ == 0)
{
lean_ctor_set_tag(v___x_44_, 0);
lean_ctor_set(v___x_44_, 0, v_fvarId1_x3f_1_);
v___x_47_ = v___x_44_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v_fvarId1_x3f_1_);
v___x_47_ = v_reuseFailAlloc_48_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
return v___x_47_;
}
}
}
}
else
{
lean_object* v___x_51_; 
lean_dec(v_fvarId2_x3f_2_);
v___x_51_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_51_, 0, v_fvarId1_x3f_1_);
return v___x_51_;
}
}
else
{
lean_object* v___x_52_; 
lean_dec(v_fvarId1_x3f_1_);
v___x_52_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_52_, 0, v_fvarId2_x3f_2_);
return v___x_52_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg___boxed(lean_object* v_fvarId1_x3f_53_, lean_object* v_fvarId2_x3f_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_fvarId1_x3f_53_, v_fvarId2_x3f_54_, v_a_55_, v_a_56_, v_a_57_);
lean_dec(v_a_57_);
lean_dec_ref(v_a_56_);
lean_dec_ref(v_a_55_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max(lean_object* v_fvarId1_x3f_60_, lean_object* v_fvarId2_x3f_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_fvarId1_x3f_60_, v_fvarId2_x3f_61_, v_a_62_, v_a_64_, v_a_65_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___boxed(lean_object* v_fvarId1_x3f_68_, lean_object* v_fvarId2_x3f_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max(v_fvarId1_x3f_68_, v_fvarId2_x3f_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_);
lean_dec(v_a_73_);
lean_dec_ref(v_a_72_);
lean_dec(v_a_71_);
lean_dec_ref(v_a_70_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check(lean_object* v_e_78_, lean_object* v_k_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_){
_start:
{
lean_object* v___f_87_; lean_object* v___f_88_; uint8_t v___x_133_; 
v___f_87_ = ((lean_object*)(l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__0));
v___f_88_ = ((lean_object*)(l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__1));
v___x_133_ = l_Lean_Expr_hasFVar(v_e_78_);
if (v___x_133_ == 0)
{
uint8_t v___x_134_; 
v___x_134_ = l_Lean_Expr_hasMVar(v_e_78_);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; lean_object* v___x_136_; 
lean_dec_ref(v_k_79_);
lean_dec_ref(v_e_78_);
v___x_135_ = lean_box(0);
v___x_136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
return v___x_136_;
}
else
{
goto v___jp_89_;
}
}
else
{
goto v___jp_89_;
}
v___jp_89_:
{
lean_object* v___x_90_; lean_object* v_maxFVar_91_; lean_object* v___x_92_; 
v___x_90_ = lean_st_ref_get(v_a_81_);
v_maxFVar_91_ = lean_ctor_get(v___x_90_, 1);
lean_inc_ref(v_maxFVar_91_);
lean_dec(v___x_90_);
lean_inc_ref(v_e_78_);
v___x_92_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_87_, v___f_88_, v_maxFVar_91_, v_e_78_);
lean_dec_ref(v_maxFVar_91_);
if (lean_obj_tag(v___x_92_) == 1)
{
lean_object* v_val_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_100_; 
lean_dec_ref(v_k_79_);
lean_dec_ref(v_e_78_);
v_val_93_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_100_ == 0)
{
v___x_95_ = v___x_92_;
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_val_93_);
lean_dec(v___x_92_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_98_; 
if (v_isShared_96_ == 0)
{
lean_ctor_set_tag(v___x_95_, 0);
v___x_98_ = v___x_95_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_val_93_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
else
{
lean_object* v___x_101_; 
lean_dec(v___x_92_);
lean_inc(v_a_85_);
lean_inc_ref(v_a_84_);
lean_inc(v_a_83_);
lean_inc_ref(v_a_82_);
lean_inc(v_a_81_);
lean_inc_ref(v_a_80_);
v___x_101_ = lean_apply_7(v_k_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_, lean_box(0));
if (lean_obj_tag(v___x_101_) == 0)
{
lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_132_; 
v_a_102_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_132_ == 0)
{
v___x_104_ = v___x_101_;
v_isShared_105_ = v_isSharedCheck_132_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v___x_101_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_132_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_106_; lean_object* v_share_107_; lean_object* v_maxFVar_108_; lean_object* v_proofInstInfo_109_; lean_object* v_proofInstInfoFVar_110_; lean_object* v_inferType_111_; lean_object* v_getLevel_112_; lean_object* v_congrInfo_113_; lean_object* v_defEqI_114_; lean_object* v_extensions_115_; lean_object* v_issues_116_; lean_object* v_canon_117_; lean_object* v_instanceOverrides_118_; uint8_t v_debug_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_131_; 
v___x_106_ = lean_st_ref_take(v_a_81_);
v_share_107_ = lean_ctor_get(v___x_106_, 0);
v_maxFVar_108_ = lean_ctor_get(v___x_106_, 1);
v_proofInstInfo_109_ = lean_ctor_get(v___x_106_, 2);
v_proofInstInfoFVar_110_ = lean_ctor_get(v___x_106_, 3);
v_inferType_111_ = lean_ctor_get(v___x_106_, 4);
v_getLevel_112_ = lean_ctor_get(v___x_106_, 5);
v_congrInfo_113_ = lean_ctor_get(v___x_106_, 6);
v_defEqI_114_ = lean_ctor_get(v___x_106_, 7);
v_extensions_115_ = lean_ctor_get(v___x_106_, 8);
v_issues_116_ = lean_ctor_get(v___x_106_, 9);
v_canon_117_ = lean_ctor_get(v___x_106_, 10);
v_instanceOverrides_118_ = lean_ctor_get(v___x_106_, 11);
v_debug_119_ = lean_ctor_get_uint8(v___x_106_, sizeof(void*)*12);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_131_ == 0)
{
v___x_121_ = v___x_106_;
v_isShared_122_ = v_isSharedCheck_131_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_instanceOverrides_118_);
lean_inc(v_canon_117_);
lean_inc(v_issues_116_);
lean_inc(v_extensions_115_);
lean_inc(v_defEqI_114_);
lean_inc(v_congrInfo_113_);
lean_inc(v_getLevel_112_);
lean_inc(v_inferType_111_);
lean_inc(v_proofInstInfoFVar_110_);
lean_inc(v_proofInstInfo_109_);
lean_inc(v_maxFVar_108_);
lean_inc(v_share_107_);
lean_dec(v___x_106_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_131_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_123_; lean_object* v___x_125_; 
lean_inc(v_a_102_);
v___x_123_ = l_Lean_PersistentHashMap_insert___redArg(v___f_87_, v___f_88_, v_maxFVar_108_, v_e_78_, v_a_102_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 1, v___x_123_);
v___x_125_ = v___x_121_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_share_107_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v___x_123_);
lean_ctor_set(v_reuseFailAlloc_130_, 2, v_proofInstInfo_109_);
lean_ctor_set(v_reuseFailAlloc_130_, 3, v_proofInstInfoFVar_110_);
lean_ctor_set(v_reuseFailAlloc_130_, 4, v_inferType_111_);
lean_ctor_set(v_reuseFailAlloc_130_, 5, v_getLevel_112_);
lean_ctor_set(v_reuseFailAlloc_130_, 6, v_congrInfo_113_);
lean_ctor_set(v_reuseFailAlloc_130_, 7, v_defEqI_114_);
lean_ctor_set(v_reuseFailAlloc_130_, 8, v_extensions_115_);
lean_ctor_set(v_reuseFailAlloc_130_, 9, v_issues_116_);
lean_ctor_set(v_reuseFailAlloc_130_, 10, v_canon_117_);
lean_ctor_set(v_reuseFailAlloc_130_, 11, v_instanceOverrides_118_);
lean_ctor_set_uint8(v_reuseFailAlloc_130_, sizeof(void*)*12, v_debug_119_);
v___x_125_ = v_reuseFailAlloc_130_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
lean_object* v___x_126_; lean_object* v___x_128_; 
v___x_126_ = lean_st_ref_put(v_a_81_, v___x_125_);
if (v_isShared_105_ == 0)
{
v___x_128_ = v___x_104_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_a_102_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_78_);
return v___x_101_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___boxed(lean_object* v_e_137_, lean_object* v_k_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check(v_e_137_, v_k_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_);
lean_dec(v_a_144_);
lean_dec_ref(v_a_143_);
lean_dec(v_a_142_);
lean_dec_ref(v_a_141_);
lean_dec(v_a_140_);
lean_dec_ref(v_a_139_);
return v_res_146_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0(void){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Lean_Meta_Sym_instInhabitedSymM___redArg();
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2(lean_object* v_msg_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v___x_156_; lean_object* v___x_4201__overap_157_; lean_object* v___x_158_; 
v___x_156_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0, &l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0);
v___x_4201__overap_157_ = lean_panic_fn_borrowed(v___x_156_, v_msg_148_);
lean_inc(v___y_154_);
lean_inc_ref(v___y_153_);
lean_inc(v___y_152_);
lean_inc_ref(v___y_151_);
lean_inc(v___y_150_);
lean_inc_ref(v___y_149_);
v___x_158_ = lean_apply_7(v___x_4201__overap_157_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, lean_box(0));
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___boxed(lean_object* v_msg_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2(v_msg_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_168_, lean_object* v_vals_169_, lean_object* v_i_170_, lean_object* v_k_171_){
_start:
{
lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_172_ = lean_array_get_size(v_keys_168_);
v___x_173_ = lean_nat_dec_lt(v_i_170_, v___x_172_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; 
lean_dec(v_i_170_);
v___x_174_ = lean_box(0);
return v___x_174_;
}
else
{
lean_object* v_k_x27_175_; size_t v___x_176_; size_t v___x_177_; uint8_t v___x_178_; 
v_k_x27_175_ = lean_array_fget_borrowed(v_keys_168_, v_i_170_);
v___x_176_ = lean_ptr_addr(v_k_171_);
v___x_177_ = lean_ptr_addr(v_k_x27_175_);
v___x_178_ = lean_usize_dec_eq(v___x_176_, v___x_177_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = lean_unsigned_to_nat(1u);
v___x_180_ = lean_nat_add(v_i_170_, v___x_179_);
lean_dec(v_i_170_);
v_i_170_ = v___x_180_;
goto _start;
}
else
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = lean_array_fget_borrowed(v_vals_169_, v_i_170_);
lean_dec(v_i_170_);
lean_inc(v___x_182_);
v___x_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
return v___x_183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_184_, lean_object* v_vals_185_, lean_object* v_i_186_, lean_object* v_k_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(v_keys_184_, v_vals_185_, v_i_186_, v_k_187_);
lean_dec_ref(v_k_187_);
lean_dec_ref(v_vals_185_);
lean_dec_ref(v_keys_184_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(lean_object* v_x_189_, size_t v_x_190_, lean_object* v_x_191_){
_start:
{
if (lean_obj_tag(v_x_189_) == 0)
{
lean_object* v_es_192_; lean_object* v___x_193_; size_t v___x_194_; size_t v___x_195_; lean_object* v_j_196_; lean_object* v___x_197_; 
v_es_192_ = lean_ctor_get(v_x_189_, 0);
v___x_193_ = lean_box(2);
v___x_194_ = ((size_t)31ULL);
v___x_195_ = lean_usize_land(v_x_190_, v___x_194_);
v_j_196_ = lean_usize_to_nat(v___x_195_);
v___x_197_ = lean_array_get_borrowed(v___x_193_, v_es_192_, v_j_196_);
lean_dec(v_j_196_);
switch(lean_obj_tag(v___x_197_))
{
case 0:
{
lean_object* v_key_198_; lean_object* v_val_199_; size_t v___x_200_; size_t v___x_201_; uint8_t v___x_202_; 
v_key_198_ = lean_ctor_get(v___x_197_, 0);
v_val_199_ = lean_ctor_get(v___x_197_, 1);
v___x_200_ = lean_ptr_addr(v_x_191_);
v___x_201_ = lean_ptr_addr(v_key_198_);
v___x_202_ = lean_usize_dec_eq(v___x_200_, v___x_201_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; 
v___x_203_ = lean_box(0);
return v___x_203_;
}
else
{
lean_object* v___x_204_; 
lean_inc(v_val_199_);
v___x_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_204_, 0, v_val_199_);
return v___x_204_;
}
}
case 1:
{
lean_object* v_node_205_; size_t v___x_206_; size_t v___x_207_; 
v_node_205_ = lean_ctor_get(v___x_197_, 0);
v___x_206_ = ((size_t)5ULL);
v___x_207_ = lean_usize_shift_right(v_x_190_, v___x_206_);
v_x_189_ = v_node_205_;
v_x_190_ = v___x_207_;
goto _start;
}
default: 
{
lean_object* v___x_209_; 
v___x_209_ = lean_box(0);
return v___x_209_;
}
}
}
else
{
lean_object* v_ks_210_; lean_object* v_vs_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v_ks_210_ = lean_ctor_get(v_x_189_, 0);
v_vs_211_ = lean_ctor_get(v_x_189_, 1);
v___x_212_ = lean_unsigned_to_nat(0u);
v___x_213_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(v_ks_210_, v_vs_211_, v___x_212_, v_x_191_);
return v___x_213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_214_, lean_object* v_x_215_, lean_object* v_x_216_){
_start:
{
size_t v_x_4694__boxed_217_; lean_object* v_res_218_; 
v_x_4694__boxed_217_ = lean_unbox_usize(v_x_215_);
lean_dec(v_x_215_);
v_res_218_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_214_, v_x_4694__boxed_217_, v_x_216_);
lean_dec_ref(v_x_216_);
lean_dec_ref(v_x_214_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(lean_object* v_x_219_, lean_object* v_x_220_){
_start:
{
size_t v___x_221_; size_t v___x_222_; size_t v___x_223_; uint64_t v___x_224_; size_t v___x_225_; lean_object* v___x_226_; 
v___x_221_ = lean_ptr_addr(v_x_220_);
v___x_222_ = ((size_t)3ULL);
v___x_223_ = lean_usize_shift_right(v___x_221_, v___x_222_);
v___x_224_ = lean_usize_to_uint64(v___x_223_);
v___x_225_ = lean_uint64_to_usize(v___x_224_);
v___x_226_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_219_, v___x_225_, v_x_220_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg___boxed(lean_object* v_x_227_, lean_object* v_x_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_x_227_, v_x_228_);
lean_dec_ref(v_x_228_);
lean_dec_ref(v_x_227_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__5_spec__6___redArg(lean_object* v_x_230_, lean_object* v_x_231_, lean_object* v_x_232_, lean_object* v_x_233_){
_start:
{
lean_object* v_ks_234_; lean_object* v_vs_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_261_; 
v_ks_234_ = lean_ctor_get(v_x_230_, 0);
v_vs_235_ = lean_ctor_get(v_x_230_, 1);
v_isSharedCheck_261_ = !lean_is_exclusive(v_x_230_);
if (v_isSharedCheck_261_ == 0)
{
v___x_237_ = v_x_230_;
v_isShared_238_ = v_isSharedCheck_261_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_vs_235_);
lean_inc(v_ks_234_);
lean_dec(v_x_230_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_261_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_239_; uint8_t v___x_240_; 
v___x_239_ = lean_array_get_size(v_ks_234_);
v___x_240_ = lean_nat_dec_lt(v_x_231_, v___x_239_);
if (v___x_240_ == 0)
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_244_; 
lean_dec(v_x_231_);
v___x_241_ = lean_array_push(v_ks_234_, v_x_232_);
v___x_242_ = lean_array_push(v_vs_235_, v_x_233_);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 1, v___x_242_);
lean_ctor_set(v___x_237_, 0, v___x_241_);
v___x_244_ = v___x_237_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v___x_241_);
lean_ctor_set(v_reuseFailAlloc_245_, 1, v___x_242_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
else
{
lean_object* v_k_x27_246_; size_t v___x_247_; size_t v___x_248_; uint8_t v___x_249_; 
v_k_x27_246_ = lean_array_fget_borrowed(v_ks_234_, v_x_231_);
v___x_247_ = lean_ptr_addr(v_x_232_);
v___x_248_ = lean_ptr_addr(v_k_x27_246_);
v___x_249_ = lean_usize_dec_eq(v___x_247_, v___x_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_251_; 
if (v_isShared_238_ == 0)
{
v___x_251_ = v___x_237_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_ks_234_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v_vs_235_);
v___x_251_ = v_reuseFailAlloc_255_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = lean_unsigned_to_nat(1u);
v___x_253_ = lean_nat_add(v_x_231_, v___x_252_);
lean_dec(v_x_231_);
v_x_230_ = v___x_251_;
v_x_231_ = v___x_253_;
goto _start;
}
}
else
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_259_; 
v___x_256_ = lean_array_fset(v_ks_234_, v_x_231_, v_x_232_);
v___x_257_ = lean_array_fset(v_vs_235_, v_x_231_, v_x_233_);
lean_dec(v_x_231_);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 1, v___x_257_);
lean_ctor_set(v___x_237_, 0, v___x_256_);
v___x_259_ = v___x_237_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_256_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v___x_257_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__5___redArg(lean_object* v_n_262_, lean_object* v_k_263_, lean_object* v_v_264_){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = lean_unsigned_to_nat(0u);
v___x_266_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__5_spec__6___redArg(v_n_262_, v___x_265_, v_k_263_, v_v_264_);
return v___x_266_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(lean_object* v_x_268_, size_t v_x_269_, size_t v_x_270_, lean_object* v_x_271_, lean_object* v_x_272_){
_start:
{
if (lean_obj_tag(v_x_268_) == 0)
{
lean_object* v_es_273_; size_t v___x_274_; size_t v___x_275_; lean_object* v_j_276_; lean_object* v___x_277_; uint8_t v___x_278_; 
v_es_273_ = lean_ctor_get(v_x_268_, 0);
v___x_274_ = ((size_t)31ULL);
v___x_275_ = lean_usize_land(v_x_269_, v___x_274_);
v_j_276_ = lean_usize_to_nat(v___x_275_);
v___x_277_ = lean_array_get_size(v_es_273_);
v___x_278_ = lean_nat_dec_lt(v_j_276_, v___x_277_);
if (v___x_278_ == 0)
{
lean_dec(v_j_276_);
lean_dec(v_x_272_);
lean_dec_ref(v_x_271_);
return v_x_268_;
}
else
{
lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_319_; 
lean_inc_ref(v_es_273_);
v_isSharedCheck_319_ = !lean_is_exclusive(v_x_268_);
if (v_isSharedCheck_319_ == 0)
{
lean_object* v_unused_320_; 
v_unused_320_ = lean_ctor_get(v_x_268_, 0);
lean_dec(v_unused_320_);
v___x_280_ = v_x_268_;
v_isShared_281_ = v_isSharedCheck_319_;
goto v_resetjp_279_;
}
else
{
lean_dec(v_x_268_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_319_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v_v_282_; lean_object* v___x_283_; lean_object* v_xs_x27_284_; lean_object* v___y_286_; 
v_v_282_ = lean_array_fget(v_es_273_, v_j_276_);
v___x_283_ = lean_box(0);
v_xs_x27_284_ = lean_array_fset(v_es_273_, v_j_276_, v___x_283_);
switch(lean_obj_tag(v_v_282_))
{
case 0:
{
lean_object* v_key_291_; lean_object* v_val_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_304_; 
v_key_291_ = lean_ctor_get(v_v_282_, 0);
v_val_292_ = lean_ctor_get(v_v_282_, 1);
v_isSharedCheck_304_ = !lean_is_exclusive(v_v_282_);
if (v_isSharedCheck_304_ == 0)
{
v___x_294_ = v_v_282_;
v_isShared_295_ = v_isSharedCheck_304_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_val_292_);
lean_inc(v_key_291_);
lean_dec(v_v_282_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_304_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
size_t v___x_296_; size_t v___x_297_; uint8_t v___x_298_; 
v___x_296_ = lean_ptr_addr(v_x_271_);
v___x_297_ = lean_ptr_addr(v_key_291_);
v___x_298_ = lean_usize_dec_eq(v___x_296_, v___x_297_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; lean_object* v___x_300_; 
lean_del_object(v___x_294_);
v___x_299_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_291_, v_val_292_, v_x_271_, v_x_272_);
v___x_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
v___y_286_ = v___x_300_;
goto v___jp_285_;
}
else
{
lean_object* v___x_302_; 
lean_dec(v_val_292_);
lean_dec(v_key_291_);
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 1, v_x_272_);
lean_ctor_set(v___x_294_, 0, v_x_271_);
v___x_302_ = v___x_294_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_x_271_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v_x_272_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
v___y_286_ = v___x_302_;
goto v___jp_285_;
}
}
}
}
case 1:
{
lean_object* v_node_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_317_; 
v_node_305_ = lean_ctor_get(v_v_282_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v_v_282_);
if (v_isSharedCheck_317_ == 0)
{
v___x_307_ = v_v_282_;
v_isShared_308_ = v_isSharedCheck_317_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_node_305_);
lean_dec(v_v_282_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_317_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
size_t v___x_309_; size_t v___x_310_; size_t v___x_311_; size_t v___x_312_; lean_object* v___x_313_; lean_object* v___x_315_; 
v___x_309_ = ((size_t)5ULL);
v___x_310_ = lean_usize_shift_right(v_x_269_, v___x_309_);
v___x_311_ = ((size_t)1ULL);
v___x_312_ = lean_usize_add(v_x_270_, v___x_311_);
v___x_313_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_node_305_, v___x_310_, v___x_312_, v_x_271_, v_x_272_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v___x_313_);
v___x_315_ = v___x_307_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_313_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
v___y_286_ = v___x_315_;
goto v___jp_285_;
}
}
}
default: 
{
lean_object* v___x_318_; 
v___x_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_318_, 0, v_x_271_);
lean_ctor_set(v___x_318_, 1, v_x_272_);
v___y_286_ = v___x_318_;
goto v___jp_285_;
}
}
v___jp_285_:
{
lean_object* v___x_287_; lean_object* v___x_289_; 
v___x_287_ = lean_array_fset(v_xs_x27_284_, v_j_276_, v___y_286_);
lean_dec(v_j_276_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 0, v___x_287_);
v___x_289_ = v___x_280_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v___x_287_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
}
}
else
{
lean_object* v_ks_321_; lean_object* v_vs_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_340_; 
v_ks_321_ = lean_ctor_get(v_x_268_, 0);
v_vs_322_ = lean_ctor_get(v_x_268_, 1);
v_isSharedCheck_340_ = !lean_is_exclusive(v_x_268_);
if (v_isSharedCheck_340_ == 0)
{
v___x_324_ = v_x_268_;
v_isShared_325_ = v_isSharedCheck_340_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_vs_322_);
lean_inc(v_ks_321_);
lean_dec(v_x_268_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_340_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_327_; 
if (v_isShared_325_ == 0)
{
v___x_327_ = v___x_324_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_ks_321_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v_vs_322_);
v___x_327_ = v_reuseFailAlloc_339_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_object* v_newNode_328_; size_t v___x_329_; uint8_t v___x_330_; 
v_newNode_328_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__5___redArg(v___x_327_, v_x_271_, v_x_272_);
v___x_329_ = ((size_t)7ULL);
v___x_330_ = lean_usize_dec_le(v___x_329_, v_x_270_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_331_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_328_);
v___x_332_ = lean_unsigned_to_nat(4u);
v___x_333_ = lean_nat_dec_lt(v___x_331_, v___x_332_);
lean_dec(v___x_331_);
if (v___x_333_ == 0)
{
lean_object* v_ks_334_; lean_object* v_vs_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v_ks_334_ = lean_ctor_get(v_newNode_328_, 0);
lean_inc_ref(v_ks_334_);
v_vs_335_ = lean_ctor_get(v_newNode_328_, 1);
lean_inc_ref(v_vs_335_);
lean_dec_ref(v_newNode_328_);
v___x_336_ = lean_unsigned_to_nat(0u);
v___x_337_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg___closed__0);
v___x_338_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_x_270_, v_ks_334_, v_vs_335_, v___x_336_, v___x_337_);
lean_dec_ref(v_vs_335_);
lean_dec_ref(v_ks_334_);
return v___x_338_;
}
else
{
return v_newNode_328_;
}
}
else
{
return v_newNode_328_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(size_t v_depth_341_, lean_object* v_keys_342_, lean_object* v_vals_343_, lean_object* v_i_344_, lean_object* v_entries_345_){
_start:
{
lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_346_ = lean_array_get_size(v_keys_342_);
v___x_347_ = lean_nat_dec_lt(v_i_344_, v___x_346_);
if (v___x_347_ == 0)
{
lean_dec(v_i_344_);
return v_entries_345_;
}
else
{
lean_object* v_k_348_; lean_object* v_v_349_; size_t v___x_350_; size_t v___x_351_; size_t v___x_352_; uint64_t v___x_353_; size_t v_h_354_; size_t v___x_355_; lean_object* v___x_356_; size_t v___x_357_; size_t v___x_358_; size_t v___x_359_; size_t v_h_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v_k_348_ = lean_array_fget_borrowed(v_keys_342_, v_i_344_);
v_v_349_ = lean_array_fget_borrowed(v_vals_343_, v_i_344_);
v___x_350_ = lean_ptr_addr(v_k_348_);
v___x_351_ = ((size_t)3ULL);
v___x_352_ = lean_usize_shift_right(v___x_350_, v___x_351_);
v___x_353_ = lean_usize_to_uint64(v___x_352_);
v_h_354_ = lean_uint64_to_usize(v___x_353_);
v___x_355_ = ((size_t)5ULL);
v___x_356_ = lean_unsigned_to_nat(1u);
v___x_357_ = ((size_t)1ULL);
v___x_358_ = lean_usize_sub(v_depth_341_, v___x_357_);
v___x_359_ = lean_usize_mul(v___x_355_, v___x_358_);
v_h_360_ = lean_usize_shift_right(v_h_354_, v___x_359_);
v___x_361_ = lean_nat_add(v_i_344_, v___x_356_);
lean_dec(v_i_344_);
lean_inc(v_v_349_);
lean_inc(v_k_348_);
v___x_362_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_entries_345_, v_h_360_, v_depth_341_, v_k_348_, v_v_349_);
v_i_344_ = v___x_361_;
v_entries_345_ = v___x_362_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_depth_364_, lean_object* v_keys_365_, lean_object* v_vals_366_, lean_object* v_i_367_, lean_object* v_entries_368_){
_start:
{
size_t v_depth_boxed_369_; lean_object* v_res_370_; 
v_depth_boxed_369_ = lean_unbox_usize(v_depth_364_);
lean_dec(v_depth_364_);
v_res_370_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_depth_boxed_369_, v_keys_365_, v_vals_366_, v_i_367_, v_entries_368_);
lean_dec_ref(v_vals_366_);
lean_dec_ref(v_keys_365_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_x_371_, lean_object* v_x_372_, lean_object* v_x_373_, lean_object* v_x_374_, lean_object* v_x_375_){
_start:
{
size_t v_x_4846__boxed_376_; size_t v_x_4847__boxed_377_; lean_object* v_res_378_; 
v_x_4846__boxed_376_ = lean_unbox_usize(v_x_372_);
lean_dec(v_x_372_);
v_x_4847__boxed_377_ = lean_unbox_usize(v_x_373_);
lean_dec(v_x_373_);
v_res_378_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_371_, v_x_4846__boxed_376_, v_x_4847__boxed_377_, v_x_374_, v_x_375_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(lean_object* v_x_379_, lean_object* v_x_380_, lean_object* v_x_381_){
_start:
{
size_t v___x_382_; size_t v___x_383_; size_t v___x_384_; uint64_t v___x_385_; size_t v___x_386_; size_t v___x_387_; lean_object* v___x_388_; 
v___x_382_ = lean_ptr_addr(v_x_380_);
v___x_383_ = ((size_t)3ULL);
v___x_384_ = lean_usize_shift_right(v___x_382_, v___x_383_);
v___x_385_ = lean_usize_to_uint64(v___x_384_);
v___x_386_ = lean_uint64_to_usize(v___x_385_);
v___x_387_ = ((size_t)1ULL);
v___x_388_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_379_, v___x_386_, v___x_387_, v_x_380_, v_x_381_);
return v___x_388_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_392_ = ((lean_object*)(l_Lean_Meta_Sym_getMaxFVar_x3f___closed__2));
v___x_393_ = lean_unsigned_to_nat(37u);
v___x_394_ = lean_unsigned_to_nat(52u);
v___x_395_ = ((lean_object*)(l_Lean_Meta_Sym_getMaxFVar_x3f___closed__1));
v___x_396_ = ((lean_object*)(l_Lean_Meta_Sym_getMaxFVar_x3f___closed__0));
v___x_397_ = l_mkPanicMessageWithDecl(v___x_396_, v___x_395_, v___x_394_, v___x_393_, v___x_392_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f(lean_object* v_e_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
lean_object* v_a_407_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v___y_436_; lean_object* v___y_437_; lean_object* v___y_438_; lean_object* v___y_439_; lean_object* v___y_440_; lean_object* v_d_489_; lean_object* v_b_490_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v___y_496_; 
switch(lean_obj_tag(v_e_398_))
{
case 1:
{
lean_object* v_fvarId_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v_fvarId_501_ = lean_ctor_get(v_e_398_, 0);
lean_inc(v_fvarId_501_);
lean_dec_ref_known(v_e_398_, 1);
v___x_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_502_, 0, v_fvarId_501_);
v___x_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
return v___x_503_;
}
case 2:
{
lean_object* v_mvarId_504_; uint8_t v___x_544_; 
v_mvarId_504_ = lean_ctor_get(v_e_398_, 0);
v___x_544_ = l_Lean_Expr_hasFVar(v_e_398_);
if (v___x_544_ == 0)
{
uint8_t v___x_545_; 
v___x_545_ = l_Lean_Expr_hasMVar(v_e_398_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; lean_object* v___x_547_; 
lean_dec_ref_known(v_e_398_, 1);
v___x_546_ = lean_box(0);
v___x_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
return v___x_547_;
}
else
{
goto v___jp_505_;
}
}
else
{
goto v___jp_505_;
}
v___jp_505_:
{
lean_object* v___x_506_; lean_object* v_maxFVar_507_; lean_object* v___x_508_; 
v___x_506_ = lean_st_ref_get(v_a_400_);
v_maxFVar_507_ = lean_ctor_get(v___x_506_, 1);
lean_inc_ref(v_maxFVar_507_);
lean_dec(v___x_506_);
v___x_508_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_507_, v_e_398_);
lean_dec_ref(v_maxFVar_507_);
if (lean_obj_tag(v___x_508_) == 1)
{
lean_object* v_val_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_516_; 
lean_dec_ref_known(v_e_398_, 1);
v_val_509_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_516_ == 0)
{
v___x_511_ = v___x_508_;
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_val_509_);
lean_dec(v___x_508_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_512_ == 0)
{
lean_ctor_set_tag(v___x_511_, 0);
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_val_509_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
else
{
lean_object* v___x_517_; 
lean_dec(v___x_508_);
lean_inc(v_mvarId_504_);
v___x_517_ = l_Lean_MVarId_getDecl(v_mvarId_504_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_518_; lean_object* v_lctx_519_; lean_object* v_decls_520_; uint8_t v___x_521_; 
v_a_518_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_a_518_);
lean_dec_ref_known(v___x_517_, 1);
v_lctx_519_ = lean_ctor_get(v_a_518_, 1);
lean_inc_ref(v_lctx_519_);
lean_dec(v_a_518_);
v_decls_520_ = lean_ctor_get(v_lctx_519_, 1);
v___x_521_ = l_Lean_PersistentArray_isEmpty___redArg(v_decls_520_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; 
v___x_522_ = l_Lean_LocalContext_lastDecl(v_lctx_519_);
lean_dec_ref(v_lctx_519_);
if (lean_obj_tag(v___x_522_) == 1)
{
lean_object* v_val_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_531_; 
v_val_523_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_531_ == 0)
{
v___x_525_ = v___x_522_;
v_isShared_526_ = v_isSharedCheck_531_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_val_523_);
lean_dec(v___x_522_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_531_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_527_ = l_Lean_LocalDecl_fvarId(v_val_523_);
lean_dec(v_val_523_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 0, v___x_527_);
v___x_529_ = v___x_525_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_527_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
v_a_407_ = v___x_529_;
goto v___jp_406_;
}
}
}
else
{
lean_object* v___x_532_; lean_object* v___x_533_; 
lean_dec(v___x_522_);
v___x_532_ = lean_obj_once(&l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3, &l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3_once, _init_l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3);
v___x_533_ = l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2(v___x_532_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v_a_534_; 
v_a_534_ = lean_ctor_get(v___x_533_, 0);
lean_inc(v_a_534_);
lean_dec_ref_known(v___x_533_, 1);
v_a_407_ = v_a_534_;
goto v___jp_406_;
}
else
{
lean_dec_ref_known(v_e_398_, 1);
return v___x_533_;
}
}
}
else
{
lean_object* v___x_535_; 
lean_dec_ref(v_lctx_519_);
v___x_535_ = lean_box(0);
v_a_407_ = v___x_535_;
goto v___jp_406_;
}
}
else
{
lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_543_; 
lean_dec_ref_known(v_e_398_, 1);
v_a_536_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_543_ == 0)
{
v___x_538_ = v___x_517_;
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_517_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_a_536_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
}
}
case 5:
{
lean_object* v_fn_548_; lean_object* v_arg_549_; uint8_t v___x_598_; 
v_fn_548_ = lean_ctor_get(v_e_398_, 0);
v_arg_549_ = lean_ctor_get(v_e_398_, 1);
v___x_598_ = l_Lean_Expr_hasFVar(v_e_398_);
if (v___x_598_ == 0)
{
uint8_t v___x_599_; 
v___x_599_ = l_Lean_Expr_hasMVar(v_e_398_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; lean_object* v___x_601_; 
lean_dec_ref_known(v_e_398_, 2);
v___x_600_ = lean_box(0);
v___x_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
return v___x_601_;
}
else
{
goto v___jp_550_;
}
}
else
{
goto v___jp_550_;
}
v___jp_550_:
{
lean_object* v___x_551_; lean_object* v_maxFVar_552_; lean_object* v___x_553_; 
v___x_551_ = lean_st_ref_get(v_a_400_);
v_maxFVar_552_ = lean_ctor_get(v___x_551_, 1);
lean_inc_ref(v_maxFVar_552_);
lean_dec(v___x_551_);
v___x_553_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_552_, v_e_398_);
lean_dec_ref(v_maxFVar_552_);
if (lean_obj_tag(v___x_553_) == 1)
{
lean_object* v_val_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
lean_dec_ref_known(v_e_398_, 2);
v_val_554_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_561_ == 0)
{
v___x_556_ = v___x_553_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_val_554_);
lean_dec(v___x_553_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
lean_ctor_set_tag(v___x_556_, 0);
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_val_554_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
else
{
lean_object* v___x_562_; 
lean_dec(v___x_553_);
lean_inc_ref(v_fn_548_);
v___x_562_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_fn_548_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v_a_563_; lean_object* v___x_564_; 
v_a_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc(v_a_563_);
lean_dec_ref_known(v___x_562_, 1);
lean_inc_ref(v_arg_549_);
v___x_564_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_arg_549_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v___x_566_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
lean_inc(v_a_565_);
lean_dec_ref_known(v___x_564_, 1);
v___x_566_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_563_, v_a_565_, v_a_401_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_597_; 
v_a_567_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_597_ == 0)
{
v___x_569_ = v___x_566_;
v_isShared_570_ = v_isSharedCheck_597_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_566_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_597_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_571_; lean_object* v_share_572_; lean_object* v_maxFVar_573_; lean_object* v_proofInstInfo_574_; lean_object* v_proofInstInfoFVar_575_; lean_object* v_inferType_576_; lean_object* v_getLevel_577_; lean_object* v_congrInfo_578_; lean_object* v_defEqI_579_; lean_object* v_extensions_580_; lean_object* v_issues_581_; lean_object* v_canon_582_; lean_object* v_instanceOverrides_583_; uint8_t v_debug_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_596_; 
v___x_571_ = lean_st_ref_take(v_a_400_);
v_share_572_ = lean_ctor_get(v___x_571_, 0);
v_maxFVar_573_ = lean_ctor_get(v___x_571_, 1);
v_proofInstInfo_574_ = lean_ctor_get(v___x_571_, 2);
v_proofInstInfoFVar_575_ = lean_ctor_get(v___x_571_, 3);
v_inferType_576_ = lean_ctor_get(v___x_571_, 4);
v_getLevel_577_ = lean_ctor_get(v___x_571_, 5);
v_congrInfo_578_ = lean_ctor_get(v___x_571_, 6);
v_defEqI_579_ = lean_ctor_get(v___x_571_, 7);
v_extensions_580_ = lean_ctor_get(v___x_571_, 8);
v_issues_581_ = lean_ctor_get(v___x_571_, 9);
v_canon_582_ = lean_ctor_get(v___x_571_, 10);
v_instanceOverrides_583_ = lean_ctor_get(v___x_571_, 11);
v_debug_584_ = lean_ctor_get_uint8(v___x_571_, sizeof(void*)*12);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_596_ == 0)
{
v___x_586_ = v___x_571_;
v_isShared_587_ = v_isSharedCheck_596_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_instanceOverrides_583_);
lean_inc(v_canon_582_);
lean_inc(v_issues_581_);
lean_inc(v_extensions_580_);
lean_inc(v_defEqI_579_);
lean_inc(v_congrInfo_578_);
lean_inc(v_getLevel_577_);
lean_inc(v_inferType_576_);
lean_inc(v_proofInstInfoFVar_575_);
lean_inc(v_proofInstInfo_574_);
lean_inc(v_maxFVar_573_);
lean_inc(v_share_572_);
lean_dec(v___x_571_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_596_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_588_; lean_object* v___x_590_; 
lean_inc(v_a_567_);
v___x_588_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_573_, v_e_398_, v_a_567_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 1, v___x_588_);
v___x_590_ = v___x_586_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_share_572_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v___x_588_);
lean_ctor_set(v_reuseFailAlloc_595_, 2, v_proofInstInfo_574_);
lean_ctor_set(v_reuseFailAlloc_595_, 3, v_proofInstInfoFVar_575_);
lean_ctor_set(v_reuseFailAlloc_595_, 4, v_inferType_576_);
lean_ctor_set(v_reuseFailAlloc_595_, 5, v_getLevel_577_);
lean_ctor_set(v_reuseFailAlloc_595_, 6, v_congrInfo_578_);
lean_ctor_set(v_reuseFailAlloc_595_, 7, v_defEqI_579_);
lean_ctor_set(v_reuseFailAlloc_595_, 8, v_extensions_580_);
lean_ctor_set(v_reuseFailAlloc_595_, 9, v_issues_581_);
lean_ctor_set(v_reuseFailAlloc_595_, 10, v_canon_582_);
lean_ctor_set(v_reuseFailAlloc_595_, 11, v_instanceOverrides_583_);
lean_ctor_set_uint8(v_reuseFailAlloc_595_, sizeof(void*)*12, v_debug_584_);
v___x_590_ = v_reuseFailAlloc_595_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_591_; lean_object* v___x_593_; 
v___x_591_ = lean_st_ref_put(v_a_400_, v___x_590_);
if (v_isShared_570_ == 0)
{
v___x_593_ = v___x_569_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_567_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_398_, 2);
return v___x_566_;
}
}
else
{
lean_dec(v_a_563_);
lean_dec_ref_known(v_e_398_, 2);
return v___x_564_;
}
}
else
{
lean_dec_ref_known(v_e_398_, 2);
return v___x_562_;
}
}
}
}
case 6:
{
lean_object* v_binderType_602_; lean_object* v_body_603_; 
v_binderType_602_ = lean_ctor_get(v_e_398_, 1);
v_body_603_ = lean_ctor_get(v_e_398_, 2);
lean_inc_ref(v_body_603_);
lean_inc_ref(v_binderType_602_);
v_d_489_ = v_binderType_602_;
v_b_490_ = v_body_603_;
v___y_491_ = v_a_399_;
v___y_492_ = v_a_400_;
v___y_493_ = v_a_401_;
v___y_494_ = v_a_402_;
v___y_495_ = v_a_403_;
v___y_496_ = v_a_404_;
goto v___jp_488_;
}
case 7:
{
lean_object* v_binderType_604_; lean_object* v_body_605_; 
v_binderType_604_ = lean_ctor_get(v_e_398_, 1);
v_body_605_ = lean_ctor_get(v_e_398_, 2);
lean_inc_ref(v_body_605_);
lean_inc_ref(v_binderType_604_);
v_d_489_ = v_binderType_604_;
v_b_490_ = v_body_605_;
v___y_491_ = v_a_399_;
v___y_492_ = v_a_400_;
v___y_493_ = v_a_401_;
v___y_494_ = v_a_402_;
v___y_495_ = v_a_403_;
v___y_496_ = v_a_404_;
goto v___jp_488_;
}
case 8:
{
lean_object* v_type_606_; lean_object* v_value_607_; lean_object* v_body_608_; uint8_t v___x_661_; 
v_type_606_ = lean_ctor_get(v_e_398_, 1);
v_value_607_ = lean_ctor_get(v_e_398_, 2);
v_body_608_ = lean_ctor_get(v_e_398_, 3);
v___x_661_ = l_Lean_Expr_hasFVar(v_e_398_);
if (v___x_661_ == 0)
{
uint8_t v___x_662_; 
v___x_662_ = l_Lean_Expr_hasMVar(v_e_398_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; lean_object* v___x_664_; 
lean_dec_ref_known(v_e_398_, 4);
v___x_663_ = lean_box(0);
v___x_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
return v___x_664_;
}
else
{
goto v___jp_609_;
}
}
else
{
goto v___jp_609_;
}
v___jp_609_:
{
lean_object* v___x_610_; lean_object* v_maxFVar_611_; lean_object* v___x_612_; 
v___x_610_ = lean_st_ref_get(v_a_400_);
v_maxFVar_611_ = lean_ctor_get(v___x_610_, 1);
lean_inc_ref(v_maxFVar_611_);
lean_dec(v___x_610_);
v___x_612_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_611_, v_e_398_);
lean_dec_ref(v_maxFVar_611_);
if (lean_obj_tag(v___x_612_) == 1)
{
lean_object* v_val_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_620_; 
lean_dec_ref_known(v_e_398_, 4);
v_val_613_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_620_ == 0)
{
v___x_615_ = v___x_612_;
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_val_613_);
lean_dec(v___x_612_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_618_; 
if (v_isShared_616_ == 0)
{
lean_ctor_set_tag(v___x_615_, 0);
v___x_618_ = v___x_615_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_val_613_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
else
{
lean_object* v___x_621_; 
lean_dec(v___x_612_);
lean_inc_ref(v_type_606_);
v___x_621_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_type_606_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_a_622_; lean_object* v___x_623_; 
v_a_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_a_622_);
lean_dec_ref_known(v___x_621_, 1);
lean_inc_ref(v_value_607_);
v___x_623_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_value_607_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_a_624_; lean_object* v___x_625_; 
v_a_624_ = lean_ctor_get(v___x_623_, 0);
lean_inc(v_a_624_);
lean_dec_ref_known(v___x_623_, 1);
v___x_625_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_622_, v_a_624_, v_a_401_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v_a_626_; lean_object* v___x_627_; 
v_a_626_ = lean_ctor_get(v___x_625_, 0);
lean_inc(v_a_626_);
lean_dec_ref_known(v___x_625_, 1);
lean_inc_ref(v_body_608_);
v___x_627_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_body_608_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v_a_628_; lean_object* v___x_629_; 
v_a_628_ = lean_ctor_get(v___x_627_, 0);
lean_inc(v_a_628_);
lean_dec_ref_known(v___x_627_, 1);
v___x_629_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_626_, v_a_628_, v_a_401_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_660_; 
v_a_630_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_660_ == 0)
{
v___x_632_ = v___x_629_;
v_isShared_633_ = v_isSharedCheck_660_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_629_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_660_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_634_; lean_object* v_share_635_; lean_object* v_maxFVar_636_; lean_object* v_proofInstInfo_637_; lean_object* v_proofInstInfoFVar_638_; lean_object* v_inferType_639_; lean_object* v_getLevel_640_; lean_object* v_congrInfo_641_; lean_object* v_defEqI_642_; lean_object* v_extensions_643_; lean_object* v_issues_644_; lean_object* v_canon_645_; lean_object* v_instanceOverrides_646_; uint8_t v_debug_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_659_; 
v___x_634_ = lean_st_ref_take(v_a_400_);
v_share_635_ = lean_ctor_get(v___x_634_, 0);
v_maxFVar_636_ = lean_ctor_get(v___x_634_, 1);
v_proofInstInfo_637_ = lean_ctor_get(v___x_634_, 2);
v_proofInstInfoFVar_638_ = lean_ctor_get(v___x_634_, 3);
v_inferType_639_ = lean_ctor_get(v___x_634_, 4);
v_getLevel_640_ = lean_ctor_get(v___x_634_, 5);
v_congrInfo_641_ = lean_ctor_get(v___x_634_, 6);
v_defEqI_642_ = lean_ctor_get(v___x_634_, 7);
v_extensions_643_ = lean_ctor_get(v___x_634_, 8);
v_issues_644_ = lean_ctor_get(v___x_634_, 9);
v_canon_645_ = lean_ctor_get(v___x_634_, 10);
v_instanceOverrides_646_ = lean_ctor_get(v___x_634_, 11);
v_debug_647_ = lean_ctor_get_uint8(v___x_634_, sizeof(void*)*12);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_659_ == 0)
{
v___x_649_ = v___x_634_;
v_isShared_650_ = v_isSharedCheck_659_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_instanceOverrides_646_);
lean_inc(v_canon_645_);
lean_inc(v_issues_644_);
lean_inc(v_extensions_643_);
lean_inc(v_defEqI_642_);
lean_inc(v_congrInfo_641_);
lean_inc(v_getLevel_640_);
lean_inc(v_inferType_639_);
lean_inc(v_proofInstInfoFVar_638_);
lean_inc(v_proofInstInfo_637_);
lean_inc(v_maxFVar_636_);
lean_inc(v_share_635_);
lean_dec(v___x_634_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_659_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_651_; lean_object* v___x_653_; 
lean_inc(v_a_630_);
v___x_651_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_636_, v_e_398_, v_a_630_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 1, v___x_651_);
v___x_653_ = v___x_649_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_share_635_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_658_, 2, v_proofInstInfo_637_);
lean_ctor_set(v_reuseFailAlloc_658_, 3, v_proofInstInfoFVar_638_);
lean_ctor_set(v_reuseFailAlloc_658_, 4, v_inferType_639_);
lean_ctor_set(v_reuseFailAlloc_658_, 5, v_getLevel_640_);
lean_ctor_set(v_reuseFailAlloc_658_, 6, v_congrInfo_641_);
lean_ctor_set(v_reuseFailAlloc_658_, 7, v_defEqI_642_);
lean_ctor_set(v_reuseFailAlloc_658_, 8, v_extensions_643_);
lean_ctor_set(v_reuseFailAlloc_658_, 9, v_issues_644_);
lean_ctor_set(v_reuseFailAlloc_658_, 10, v_canon_645_);
lean_ctor_set(v_reuseFailAlloc_658_, 11, v_instanceOverrides_646_);
lean_ctor_set_uint8(v_reuseFailAlloc_658_, sizeof(void*)*12, v_debug_647_);
v___x_653_ = v_reuseFailAlloc_658_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
lean_object* v___x_654_; lean_object* v___x_656_; 
v___x_654_ = lean_st_ref_put(v_a_400_, v___x_653_);
if (v_isShared_633_ == 0)
{
v___x_656_ = v___x_632_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_a_630_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_398_, 4);
return v___x_629_;
}
}
else
{
lean_dec(v_a_626_);
lean_dec_ref_known(v_e_398_, 4);
return v___x_627_;
}
}
else
{
lean_dec_ref_known(v_e_398_, 4);
return v___x_625_;
}
}
else
{
lean_dec(v_a_622_);
lean_dec_ref_known(v_e_398_, 4);
return v___x_623_;
}
}
else
{
lean_dec_ref_known(v_e_398_, 4);
return v___x_621_;
}
}
}
}
case 10:
{
lean_object* v_expr_665_; uint8_t v___x_710_; 
v_expr_665_ = lean_ctor_get(v_e_398_, 1);
lean_inc_ref(v_expr_665_);
lean_dec_ref_known(v_e_398_, 2);
v___x_710_ = l_Lean_Expr_hasFVar(v_expr_665_);
if (v___x_710_ == 0)
{
uint8_t v___x_711_; 
v___x_711_ = l_Lean_Expr_hasMVar(v_expr_665_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; lean_object* v___x_713_; 
lean_dec_ref(v_expr_665_);
v___x_712_ = lean_box(0);
v___x_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
return v___x_713_;
}
else
{
goto v___jp_666_;
}
}
else
{
goto v___jp_666_;
}
v___jp_666_:
{
lean_object* v___x_667_; lean_object* v_maxFVar_668_; lean_object* v___x_669_; 
v___x_667_ = lean_st_ref_get(v_a_400_);
v_maxFVar_668_ = lean_ctor_get(v___x_667_, 1);
lean_inc_ref(v_maxFVar_668_);
lean_dec(v___x_667_);
v___x_669_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_668_, v_expr_665_);
lean_dec_ref(v_maxFVar_668_);
if (lean_obj_tag(v___x_669_) == 1)
{
lean_object* v_val_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
lean_dec_ref(v_expr_665_);
v_val_670_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_669_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_val_670_);
lean_dec(v___x_669_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
lean_ctor_set_tag(v___x_672_, 0);
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_val_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
else
{
lean_object* v___x_678_; 
lean_dec(v___x_669_);
lean_inc_ref(v_expr_665_);
v___x_678_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_expr_665_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_709_; 
v_a_679_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_709_ == 0)
{
v___x_681_ = v___x_678_;
v_isShared_682_ = v_isSharedCheck_709_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_678_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_709_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_683_; lean_object* v_share_684_; lean_object* v_maxFVar_685_; lean_object* v_proofInstInfo_686_; lean_object* v_proofInstInfoFVar_687_; lean_object* v_inferType_688_; lean_object* v_getLevel_689_; lean_object* v_congrInfo_690_; lean_object* v_defEqI_691_; lean_object* v_extensions_692_; lean_object* v_issues_693_; lean_object* v_canon_694_; lean_object* v_instanceOverrides_695_; uint8_t v_debug_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_708_; 
v___x_683_ = lean_st_ref_take(v_a_400_);
v_share_684_ = lean_ctor_get(v___x_683_, 0);
v_maxFVar_685_ = lean_ctor_get(v___x_683_, 1);
v_proofInstInfo_686_ = lean_ctor_get(v___x_683_, 2);
v_proofInstInfoFVar_687_ = lean_ctor_get(v___x_683_, 3);
v_inferType_688_ = lean_ctor_get(v___x_683_, 4);
v_getLevel_689_ = lean_ctor_get(v___x_683_, 5);
v_congrInfo_690_ = lean_ctor_get(v___x_683_, 6);
v_defEqI_691_ = lean_ctor_get(v___x_683_, 7);
v_extensions_692_ = lean_ctor_get(v___x_683_, 8);
v_issues_693_ = lean_ctor_get(v___x_683_, 9);
v_canon_694_ = lean_ctor_get(v___x_683_, 10);
v_instanceOverrides_695_ = lean_ctor_get(v___x_683_, 11);
v_debug_696_ = lean_ctor_get_uint8(v___x_683_, sizeof(void*)*12);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_708_ == 0)
{
v___x_698_ = v___x_683_;
v_isShared_699_ = v_isSharedCheck_708_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_instanceOverrides_695_);
lean_inc(v_canon_694_);
lean_inc(v_issues_693_);
lean_inc(v_extensions_692_);
lean_inc(v_defEqI_691_);
lean_inc(v_congrInfo_690_);
lean_inc(v_getLevel_689_);
lean_inc(v_inferType_688_);
lean_inc(v_proofInstInfoFVar_687_);
lean_inc(v_proofInstInfo_686_);
lean_inc(v_maxFVar_685_);
lean_inc(v_share_684_);
lean_dec(v___x_683_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_708_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; lean_object* v___x_702_; 
lean_inc(v_a_679_);
v___x_700_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_685_, v_expr_665_, v_a_679_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 1, v___x_700_);
v___x_702_ = v___x_698_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_share_684_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_707_, 2, v_proofInstInfo_686_);
lean_ctor_set(v_reuseFailAlloc_707_, 3, v_proofInstInfoFVar_687_);
lean_ctor_set(v_reuseFailAlloc_707_, 4, v_inferType_688_);
lean_ctor_set(v_reuseFailAlloc_707_, 5, v_getLevel_689_);
lean_ctor_set(v_reuseFailAlloc_707_, 6, v_congrInfo_690_);
lean_ctor_set(v_reuseFailAlloc_707_, 7, v_defEqI_691_);
lean_ctor_set(v_reuseFailAlloc_707_, 8, v_extensions_692_);
lean_ctor_set(v_reuseFailAlloc_707_, 9, v_issues_693_);
lean_ctor_set(v_reuseFailAlloc_707_, 10, v_canon_694_);
lean_ctor_set(v_reuseFailAlloc_707_, 11, v_instanceOverrides_695_);
lean_ctor_set_uint8(v_reuseFailAlloc_707_, sizeof(void*)*12, v_debug_696_);
v___x_702_ = v_reuseFailAlloc_707_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
lean_object* v___x_703_; lean_object* v___x_705_; 
v___x_703_ = lean_st_ref_put(v_a_400_, v___x_702_);
if (v_isShared_682_ == 0)
{
v___x_705_ = v___x_681_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_679_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
}
else
{
lean_dec_ref(v_expr_665_);
return v___x_678_;
}
}
}
}
case 11:
{
lean_object* v_struct_714_; uint8_t v___x_759_; 
v_struct_714_ = lean_ctor_get(v_e_398_, 2);
v___x_759_ = l_Lean_Expr_hasFVar(v_e_398_);
if (v___x_759_ == 0)
{
uint8_t v___x_760_; 
v___x_760_ = l_Lean_Expr_hasMVar(v_e_398_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; lean_object* v___x_762_; 
lean_dec_ref_known(v_e_398_, 3);
v___x_761_ = lean_box(0);
v___x_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
return v___x_762_;
}
else
{
goto v___jp_715_;
}
}
else
{
goto v___jp_715_;
}
v___jp_715_:
{
lean_object* v___x_716_; lean_object* v_maxFVar_717_; lean_object* v___x_718_; 
v___x_716_ = lean_st_ref_get(v_a_400_);
v_maxFVar_717_ = lean_ctor_get(v___x_716_, 1);
lean_inc_ref(v_maxFVar_717_);
lean_dec(v___x_716_);
v___x_718_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_717_, v_e_398_);
lean_dec_ref(v_maxFVar_717_);
if (lean_obj_tag(v___x_718_) == 1)
{
lean_object* v_val_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
lean_dec_ref_known(v_e_398_, 3);
v_val_719_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v___x_718_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_val_719_);
lean_dec(v___x_718_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
lean_ctor_set_tag(v___x_721_, 0);
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_val_719_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
else
{
lean_object* v___x_727_; 
lean_dec(v___x_718_);
lean_inc_ref(v_struct_714_);
v___x_727_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_struct_714_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_758_; 
v_a_728_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_758_ == 0)
{
v___x_730_ = v___x_727_;
v_isShared_731_ = v_isSharedCheck_758_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_727_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_758_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_732_; lean_object* v_share_733_; lean_object* v_maxFVar_734_; lean_object* v_proofInstInfo_735_; lean_object* v_proofInstInfoFVar_736_; lean_object* v_inferType_737_; lean_object* v_getLevel_738_; lean_object* v_congrInfo_739_; lean_object* v_defEqI_740_; lean_object* v_extensions_741_; lean_object* v_issues_742_; lean_object* v_canon_743_; lean_object* v_instanceOverrides_744_; uint8_t v_debug_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_757_; 
v___x_732_ = lean_st_ref_take(v_a_400_);
v_share_733_ = lean_ctor_get(v___x_732_, 0);
v_maxFVar_734_ = lean_ctor_get(v___x_732_, 1);
v_proofInstInfo_735_ = lean_ctor_get(v___x_732_, 2);
v_proofInstInfoFVar_736_ = lean_ctor_get(v___x_732_, 3);
v_inferType_737_ = lean_ctor_get(v___x_732_, 4);
v_getLevel_738_ = lean_ctor_get(v___x_732_, 5);
v_congrInfo_739_ = lean_ctor_get(v___x_732_, 6);
v_defEqI_740_ = lean_ctor_get(v___x_732_, 7);
v_extensions_741_ = lean_ctor_get(v___x_732_, 8);
v_issues_742_ = lean_ctor_get(v___x_732_, 9);
v_canon_743_ = lean_ctor_get(v___x_732_, 10);
v_instanceOverrides_744_ = lean_ctor_get(v___x_732_, 11);
v_debug_745_ = lean_ctor_get_uint8(v___x_732_, sizeof(void*)*12);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_757_ == 0)
{
v___x_747_ = v___x_732_;
v_isShared_748_ = v_isSharedCheck_757_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_instanceOverrides_744_);
lean_inc(v_canon_743_);
lean_inc(v_issues_742_);
lean_inc(v_extensions_741_);
lean_inc(v_defEqI_740_);
lean_inc(v_congrInfo_739_);
lean_inc(v_getLevel_738_);
lean_inc(v_inferType_737_);
lean_inc(v_proofInstInfoFVar_736_);
lean_inc(v_proofInstInfo_735_);
lean_inc(v_maxFVar_734_);
lean_inc(v_share_733_);
lean_dec(v___x_732_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_757_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_749_; lean_object* v___x_751_; 
lean_inc(v_a_728_);
v___x_749_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_734_, v_e_398_, v_a_728_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 1, v___x_749_);
v___x_751_ = v___x_747_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_share_733_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v___x_749_);
lean_ctor_set(v_reuseFailAlloc_756_, 2, v_proofInstInfo_735_);
lean_ctor_set(v_reuseFailAlloc_756_, 3, v_proofInstInfoFVar_736_);
lean_ctor_set(v_reuseFailAlloc_756_, 4, v_inferType_737_);
lean_ctor_set(v_reuseFailAlloc_756_, 5, v_getLevel_738_);
lean_ctor_set(v_reuseFailAlloc_756_, 6, v_congrInfo_739_);
lean_ctor_set(v_reuseFailAlloc_756_, 7, v_defEqI_740_);
lean_ctor_set(v_reuseFailAlloc_756_, 8, v_extensions_741_);
lean_ctor_set(v_reuseFailAlloc_756_, 9, v_issues_742_);
lean_ctor_set(v_reuseFailAlloc_756_, 10, v_canon_743_);
lean_ctor_set(v_reuseFailAlloc_756_, 11, v_instanceOverrides_744_);
lean_ctor_set_uint8(v_reuseFailAlloc_756_, sizeof(void*)*12, v_debug_745_);
v___x_751_ = v_reuseFailAlloc_756_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_object* v___x_752_; lean_object* v___x_754_; 
v___x_752_ = lean_st_ref_put(v_a_400_, v___x_751_);
if (v_isShared_731_ == 0)
{
v___x_754_ = v___x_730_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_a_728_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_398_, 3);
return v___x_727_;
}
}
}
}
default: 
{
lean_object* v___x_763_; lean_object* v___x_764_; 
lean_dec_ref(v_e_398_);
v___x_763_ = lean_box(0);
v___x_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_764_, 0, v___x_763_);
return v___x_764_;
}
}
v___jp_406_:
{
lean_object* v___x_408_; lean_object* v_share_409_; lean_object* v_maxFVar_410_; lean_object* v_proofInstInfo_411_; lean_object* v_proofInstInfoFVar_412_; lean_object* v_inferType_413_; lean_object* v_getLevel_414_; lean_object* v_congrInfo_415_; lean_object* v_defEqI_416_; lean_object* v_extensions_417_; lean_object* v_issues_418_; lean_object* v_canon_419_; lean_object* v_instanceOverrides_420_; uint8_t v_debug_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_431_; 
v___x_408_ = lean_st_ref_take(v_a_400_);
v_share_409_ = lean_ctor_get(v___x_408_, 0);
v_maxFVar_410_ = lean_ctor_get(v___x_408_, 1);
v_proofInstInfo_411_ = lean_ctor_get(v___x_408_, 2);
v_proofInstInfoFVar_412_ = lean_ctor_get(v___x_408_, 3);
v_inferType_413_ = lean_ctor_get(v___x_408_, 4);
v_getLevel_414_ = lean_ctor_get(v___x_408_, 5);
v_congrInfo_415_ = lean_ctor_get(v___x_408_, 6);
v_defEqI_416_ = lean_ctor_get(v___x_408_, 7);
v_extensions_417_ = lean_ctor_get(v___x_408_, 8);
v_issues_418_ = lean_ctor_get(v___x_408_, 9);
v_canon_419_ = lean_ctor_get(v___x_408_, 10);
v_instanceOverrides_420_ = lean_ctor_get(v___x_408_, 11);
v_debug_421_ = lean_ctor_get_uint8(v___x_408_, sizeof(void*)*12);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_431_ == 0)
{
v___x_423_ = v___x_408_;
v_isShared_424_ = v_isSharedCheck_431_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_instanceOverrides_420_);
lean_inc(v_canon_419_);
lean_inc(v_issues_418_);
lean_inc(v_extensions_417_);
lean_inc(v_defEqI_416_);
lean_inc(v_congrInfo_415_);
lean_inc(v_getLevel_414_);
lean_inc(v_inferType_413_);
lean_inc(v_proofInstInfoFVar_412_);
lean_inc(v_proofInstInfo_411_);
lean_inc(v_maxFVar_410_);
lean_inc(v_share_409_);
lean_dec(v___x_408_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_431_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_425_; lean_object* v___x_427_; 
lean_inc(v_a_407_);
v___x_425_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_410_, v_e_398_, v_a_407_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 1, v___x_425_);
v___x_427_ = v___x_423_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_share_409_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v___x_425_);
lean_ctor_set(v_reuseFailAlloc_430_, 2, v_proofInstInfo_411_);
lean_ctor_set(v_reuseFailAlloc_430_, 3, v_proofInstInfoFVar_412_);
lean_ctor_set(v_reuseFailAlloc_430_, 4, v_inferType_413_);
lean_ctor_set(v_reuseFailAlloc_430_, 5, v_getLevel_414_);
lean_ctor_set(v_reuseFailAlloc_430_, 6, v_congrInfo_415_);
lean_ctor_set(v_reuseFailAlloc_430_, 7, v_defEqI_416_);
lean_ctor_set(v_reuseFailAlloc_430_, 8, v_extensions_417_);
lean_ctor_set(v_reuseFailAlloc_430_, 9, v_issues_418_);
lean_ctor_set(v_reuseFailAlloc_430_, 10, v_canon_419_);
lean_ctor_set(v_reuseFailAlloc_430_, 11, v_instanceOverrides_420_);
lean_ctor_set_uint8(v_reuseFailAlloc_430_, sizeof(void*)*12, v_debug_421_);
v___x_427_ = v_reuseFailAlloc_430_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = lean_st_ref_put(v_a_400_, v___x_427_);
v___x_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_429_, 0, v_a_407_);
return v___x_429_;
}
}
}
v___jp_432_:
{
lean_object* v___x_441_; lean_object* v_maxFVar_442_; lean_object* v___x_443_; 
v___x_441_ = lean_st_ref_get(v___y_439_);
v_maxFVar_442_ = lean_ctor_get(v___x_441_, 1);
lean_inc_ref(v_maxFVar_442_);
lean_dec(v___x_441_);
v___x_443_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_442_, v_e_398_);
lean_dec_ref(v_maxFVar_442_);
if (lean_obj_tag(v___x_443_) == 1)
{
lean_object* v_val_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_451_; 
lean_dec_ref(v___y_440_);
lean_dec_ref(v___y_437_);
lean_dec_ref(v_e_398_);
v_val_444_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_451_ == 0)
{
v___x_446_ = v___x_443_;
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_val_444_);
lean_dec(v___x_443_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_449_; 
if (v_isShared_447_ == 0)
{
lean_ctor_set_tag(v___x_446_, 0);
v___x_449_ = v___x_446_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_val_444_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
else
{
lean_object* v___x_452_; 
lean_dec(v___x_443_);
v___x_452_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v___y_437_, v___y_433_, v___y_439_, v___y_434_, v___y_436_, v___y_438_, v___y_435_);
if (lean_obj_tag(v___x_452_) == 0)
{
lean_object* v_a_453_; lean_object* v___x_454_; 
v_a_453_ = lean_ctor_get(v___x_452_, 0);
lean_inc(v_a_453_);
lean_dec_ref_known(v___x_452_, 1);
v___x_454_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v___y_440_, v___y_433_, v___y_439_, v___y_434_, v___y_436_, v___y_438_, v___y_435_);
if (lean_obj_tag(v___x_454_) == 0)
{
lean_object* v_a_455_; lean_object* v___x_456_; 
v_a_455_ = lean_ctor_get(v___x_454_, 0);
lean_inc(v_a_455_);
lean_dec_ref_known(v___x_454_, 1);
v___x_456_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_453_, v_a_455_, v___y_434_, v___y_438_, v___y_435_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_487_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_487_ == 0)
{
v___x_459_ = v___x_456_;
v_isShared_460_ = v_isSharedCheck_487_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_456_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_487_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_461_; lean_object* v_share_462_; lean_object* v_maxFVar_463_; lean_object* v_proofInstInfo_464_; lean_object* v_proofInstInfoFVar_465_; lean_object* v_inferType_466_; lean_object* v_getLevel_467_; lean_object* v_congrInfo_468_; lean_object* v_defEqI_469_; lean_object* v_extensions_470_; lean_object* v_issues_471_; lean_object* v_canon_472_; lean_object* v_instanceOverrides_473_; uint8_t v_debug_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_486_; 
v___x_461_ = lean_st_ref_take(v___y_439_);
v_share_462_ = lean_ctor_get(v___x_461_, 0);
v_maxFVar_463_ = lean_ctor_get(v___x_461_, 1);
v_proofInstInfo_464_ = lean_ctor_get(v___x_461_, 2);
v_proofInstInfoFVar_465_ = lean_ctor_get(v___x_461_, 3);
v_inferType_466_ = lean_ctor_get(v___x_461_, 4);
v_getLevel_467_ = lean_ctor_get(v___x_461_, 5);
v_congrInfo_468_ = lean_ctor_get(v___x_461_, 6);
v_defEqI_469_ = lean_ctor_get(v___x_461_, 7);
v_extensions_470_ = lean_ctor_get(v___x_461_, 8);
v_issues_471_ = lean_ctor_get(v___x_461_, 9);
v_canon_472_ = lean_ctor_get(v___x_461_, 10);
v_instanceOverrides_473_ = lean_ctor_get(v___x_461_, 11);
v_debug_474_ = lean_ctor_get_uint8(v___x_461_, sizeof(void*)*12);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_486_ == 0)
{
v___x_476_ = v___x_461_;
v_isShared_477_ = v_isSharedCheck_486_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_instanceOverrides_473_);
lean_inc(v_canon_472_);
lean_inc(v_issues_471_);
lean_inc(v_extensions_470_);
lean_inc(v_defEqI_469_);
lean_inc(v_congrInfo_468_);
lean_inc(v_getLevel_467_);
lean_inc(v_inferType_466_);
lean_inc(v_proofInstInfoFVar_465_);
lean_inc(v_proofInstInfo_464_);
lean_inc(v_maxFVar_463_);
lean_inc(v_share_462_);
lean_dec(v___x_461_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_486_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_478_; lean_object* v___x_480_; 
lean_inc(v_a_457_);
v___x_478_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_463_, v_e_398_, v_a_457_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 1, v___x_478_);
v___x_480_ = v___x_476_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_share_462_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v___x_478_);
lean_ctor_set(v_reuseFailAlloc_485_, 2, v_proofInstInfo_464_);
lean_ctor_set(v_reuseFailAlloc_485_, 3, v_proofInstInfoFVar_465_);
lean_ctor_set(v_reuseFailAlloc_485_, 4, v_inferType_466_);
lean_ctor_set(v_reuseFailAlloc_485_, 5, v_getLevel_467_);
lean_ctor_set(v_reuseFailAlloc_485_, 6, v_congrInfo_468_);
lean_ctor_set(v_reuseFailAlloc_485_, 7, v_defEqI_469_);
lean_ctor_set(v_reuseFailAlloc_485_, 8, v_extensions_470_);
lean_ctor_set(v_reuseFailAlloc_485_, 9, v_issues_471_);
lean_ctor_set(v_reuseFailAlloc_485_, 10, v_canon_472_);
lean_ctor_set(v_reuseFailAlloc_485_, 11, v_instanceOverrides_473_);
lean_ctor_set_uint8(v_reuseFailAlloc_485_, sizeof(void*)*12, v_debug_474_);
v___x_480_ = v_reuseFailAlloc_485_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
lean_object* v___x_481_; lean_object* v___x_483_; 
v___x_481_ = lean_st_ref_put(v___y_439_, v___x_480_);
if (v_isShared_460_ == 0)
{
v___x_483_ = v___x_459_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_a_457_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_398_);
return v___x_456_;
}
}
else
{
lean_dec(v_a_453_);
lean_dec_ref(v_e_398_);
return v___x_454_;
}
}
else
{
lean_dec_ref(v___y_440_);
lean_dec_ref(v_e_398_);
return v___x_452_;
}
}
}
v___jp_488_:
{
uint8_t v___x_497_; 
v___x_497_ = l_Lean_Expr_hasFVar(v_e_398_);
if (v___x_497_ == 0)
{
uint8_t v___x_498_; 
v___x_498_ = l_Lean_Expr_hasMVar(v_e_398_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; lean_object* v___x_500_; 
lean_dec_ref(v_b_490_);
lean_dec_ref(v_d_489_);
lean_dec_ref(v_e_398_);
v___x_499_ = lean_box(0);
v___x_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
return v___x_500_;
}
else
{
v___y_433_ = v___y_491_;
v___y_434_ = v___y_493_;
v___y_435_ = v___y_496_;
v___y_436_ = v___y_494_;
v___y_437_ = v_d_489_;
v___y_438_ = v___y_495_;
v___y_439_ = v___y_492_;
v___y_440_ = v_b_490_;
goto v___jp_432_;
}
}
else
{
v___y_433_ = v___y_491_;
v___y_434_ = v___y_493_;
v___y_435_ = v___y_496_;
v___y_436_ = v___y_494_;
v___y_437_ = v_d_489_;
v___y_438_ = v___y_495_;
v___y_439_ = v___y_492_;
v___y_440_ = v_b_490_;
goto v___jp_432_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f___boxed(lean_object* v_e_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_e_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_);
lean_dec(v_a_771_);
lean_dec_ref(v_a_770_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
lean_dec(v_a_767_);
lean_dec_ref(v_a_766_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0(lean_object* v_00_u03b2_774_, lean_object* v_x_775_, lean_object* v_x_776_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_x_775_, v_x_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___boxed(lean_object* v_00_u03b2_778_, lean_object* v_x_779_, lean_object* v_x_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0(v_00_u03b2_778_, v_x_779_, v_x_780_);
lean_dec_ref(v_x_780_);
lean_dec_ref(v_x_779_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1(lean_object* v_00_u03b2_782_, lean_object* v_x_783_, lean_object* v_x_784_, lean_object* v_x_785_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_x_783_, v_x_784_, v_x_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0(lean_object* v_00_u03b2_787_, lean_object* v_x_788_, size_t v_x_789_, lean_object* v_x_790_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_788_, v_x_789_, v_x_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_792_, lean_object* v_x_793_, lean_object* v_x_794_, lean_object* v_x_795_){
_start:
{
size_t v_x_5636__boxed_796_; lean_object* v_res_797_; 
v_x_5636__boxed_796_ = lean_unbox_usize(v_x_794_);
lean_dec(v_x_794_);
v_res_797_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0(v_00_u03b2_792_, v_x_793_, v_x_5636__boxed_796_, v_x_795_);
lean_dec_ref(v_x_795_);
lean_dec_ref(v_x_793_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2(lean_object* v_00_u03b2_798_, lean_object* v_x_799_, size_t v_x_800_, size_t v_x_801_, lean_object* v_x_802_, lean_object* v_x_803_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_799_, v_x_800_, v_x_801_, v_x_802_, v_x_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_805_, lean_object* v_x_806_, lean_object* v_x_807_, lean_object* v_x_808_, lean_object* v_x_809_, lean_object* v_x_810_){
_start:
{
size_t v_x_5647__boxed_811_; size_t v_x_5648__boxed_812_; lean_object* v_res_813_; 
v_x_5647__boxed_811_ = lean_unbox_usize(v_x_807_);
lean_dec(v_x_807_);
v_x_5648__boxed_812_ = lean_unbox_usize(v_x_808_);
lean_dec(v_x_808_);
v_res_813_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2(v_00_u03b2_805_, v_x_806_, v_x_5647__boxed_811_, v_x_5648__boxed_812_, v_x_809_, v_x_810_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_814_, lean_object* v_keys_815_, lean_object* v_vals_816_, lean_object* v_heq_817_, lean_object* v_i_818_, lean_object* v_k_819_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(v_keys_815_, v_vals_816_, v_i_818_, v_k_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_821_, lean_object* v_keys_822_, lean_object* v_vals_823_, lean_object* v_heq_824_, lean_object* v_i_825_, lean_object* v_k_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2(v_00_u03b2_821_, v_keys_822_, v_vals_823_, v_heq_824_, v_i_825_, v_k_826_);
lean_dec_ref(v_k_826_);
lean_dec_ref(v_vals_823_);
lean_dec_ref(v_keys_822_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_828_, lean_object* v_n_829_, lean_object* v_k_830_, lean_object* v_v_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__5___redArg(v_n_829_, v_k_830_, v_v_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_833_, size_t v_depth_834_, lean_object* v_keys_835_, lean_object* v_vals_836_, lean_object* v_heq_837_, lean_object* v_i_838_, lean_object* v_entries_839_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_depth_834_, v_keys_835_, v_vals_836_, v_i_838_, v_entries_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_841_, lean_object* v_depth_842_, lean_object* v_keys_843_, lean_object* v_vals_844_, lean_object* v_heq_845_, lean_object* v_i_846_, lean_object* v_entries_847_){
_start:
{
size_t v_depth_boxed_848_; lean_object* v_res_849_; 
v_depth_boxed_848_ = lean_unbox_usize(v_depth_842_);
lean_dec(v_depth_842_);
v_res_849_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6(v_00_u03b2_841_, v_depth_boxed_848_, v_keys_843_, v_vals_844_, v_heq_845_, v_i_846_, v_entries_847_);
lean_dec_ref(v_vals_844_);
lean_dec_ref(v_keys_843_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__5_spec__6(lean_object* v_00_u03b2_850_, lean_object* v_x_851_, lean_object* v_x_852_, lean_object* v_x_853_, lean_object* v_x_854_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__5_spec__6___redArg(v_x_851_, v_x_852_, v_x_853_, v_x_854_);
return v___x_855_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_MaxFVar(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_MaxFVar(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_MaxFVar(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_MaxFVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_MaxFVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_MaxFVar(builtin);
}
#ifdef __cplusplus
}
#endif
