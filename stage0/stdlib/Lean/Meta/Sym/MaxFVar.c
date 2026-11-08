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
lean_object* v___f_87_; lean_object* v___f_88_; uint8_t v___x_134_; 
v___f_87_ = ((lean_object*)(l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__0));
v___f_88_ = ((lean_object*)(l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__1));
v___x_134_ = l_Lean_Expr_hasFVar(v_e_78_);
if (v___x_134_ == 0)
{
uint8_t v___x_135_; 
v___x_135_ = l_Lean_Expr_hasMVar(v_e_78_);
if (v___x_135_ == 0)
{
lean_object* v___x_136_; lean_object* v___x_137_; 
lean_dec_ref(v_k_79_);
lean_dec_ref(v_e_78_);
v___x_136_ = lean_box(0);
v___x_137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
return v___x_137_;
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
lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_133_; 
v_a_102_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_133_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_133_ == 0)
{
v___x_104_ = v___x_101_;
v_isShared_105_ = v_isSharedCheck_133_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v___x_101_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_133_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_106_; lean_object* v_share_107_; lean_object* v_maxFVar_108_; lean_object* v_proofInstInfo_109_; lean_object* v_proofInstInfoFVar_110_; lean_object* v_letValue_111_; lean_object* v_inferType_112_; lean_object* v_getLevel_113_; lean_object* v_congrInfo_114_; lean_object* v_defEqI_115_; lean_object* v_extensions_116_; lean_object* v_issues_117_; lean_object* v_canon_118_; lean_object* v_instanceOverrides_119_; uint8_t v_debug_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_132_; 
v___x_106_ = lean_st_ref_take(v_a_81_);
v_share_107_ = lean_ctor_get(v___x_106_, 0);
v_maxFVar_108_ = lean_ctor_get(v___x_106_, 1);
v_proofInstInfo_109_ = lean_ctor_get(v___x_106_, 2);
v_proofInstInfoFVar_110_ = lean_ctor_get(v___x_106_, 3);
v_letValue_111_ = lean_ctor_get(v___x_106_, 4);
v_inferType_112_ = lean_ctor_get(v___x_106_, 5);
v_getLevel_113_ = lean_ctor_get(v___x_106_, 6);
v_congrInfo_114_ = lean_ctor_get(v___x_106_, 7);
v_defEqI_115_ = lean_ctor_get(v___x_106_, 8);
v_extensions_116_ = lean_ctor_get(v___x_106_, 9);
v_issues_117_ = lean_ctor_get(v___x_106_, 10);
v_canon_118_ = lean_ctor_get(v___x_106_, 11);
v_instanceOverrides_119_ = lean_ctor_get(v___x_106_, 12);
v_debug_120_ = lean_ctor_get_uint8(v___x_106_, sizeof(void*)*13);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_132_ == 0)
{
v___x_122_ = v___x_106_;
v_isShared_123_ = v_isSharedCheck_132_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_instanceOverrides_119_);
lean_inc(v_canon_118_);
lean_inc(v_issues_117_);
lean_inc(v_extensions_116_);
lean_inc(v_defEqI_115_);
lean_inc(v_congrInfo_114_);
lean_inc(v_getLevel_113_);
lean_inc(v_inferType_112_);
lean_inc(v_letValue_111_);
lean_inc(v_proofInstInfoFVar_110_);
lean_inc(v_proofInstInfo_109_);
lean_inc(v_maxFVar_108_);
lean_inc(v_share_107_);
lean_dec(v___x_106_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_132_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_124_; lean_object* v___x_126_; 
lean_inc(v_a_102_);
v___x_124_ = l_Lean_PersistentHashMap_insert___redArg(v___f_87_, v___f_88_, v_maxFVar_108_, v_e_78_, v_a_102_);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 1, v___x_124_);
v___x_126_ = v___x_122_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_share_107_);
lean_ctor_set(v_reuseFailAlloc_131_, 1, v___x_124_);
lean_ctor_set(v_reuseFailAlloc_131_, 2, v_proofInstInfo_109_);
lean_ctor_set(v_reuseFailAlloc_131_, 3, v_proofInstInfoFVar_110_);
lean_ctor_set(v_reuseFailAlloc_131_, 4, v_letValue_111_);
lean_ctor_set(v_reuseFailAlloc_131_, 5, v_inferType_112_);
lean_ctor_set(v_reuseFailAlloc_131_, 6, v_getLevel_113_);
lean_ctor_set(v_reuseFailAlloc_131_, 7, v_congrInfo_114_);
lean_ctor_set(v_reuseFailAlloc_131_, 8, v_defEqI_115_);
lean_ctor_set(v_reuseFailAlloc_131_, 9, v_extensions_116_);
lean_ctor_set(v_reuseFailAlloc_131_, 10, v_issues_117_);
lean_ctor_set(v_reuseFailAlloc_131_, 11, v_canon_118_);
lean_ctor_set(v_reuseFailAlloc_131_, 12, v_instanceOverrides_119_);
lean_ctor_set_uint8(v_reuseFailAlloc_131_, sizeof(void*)*13, v_debug_120_);
v___x_126_ = v_reuseFailAlloc_131_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
lean_object* v___x_127_; lean_object* v___x_129_; 
v___x_127_ = lean_st_ref_put(v_a_81_, v___x_126_);
if (v_isShared_105_ == 0)
{
v___x_129_ = v___x_104_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_a_102_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___boxed(lean_object* v_e_138_, lean_object* v_k_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check(v_e_138_, v_k_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_);
lean_dec(v_a_145_);
lean_dec_ref(v_a_144_);
lean_dec(v_a_143_);
lean_dec_ref(v_a_142_);
lean_dec(v_a_141_);
lean_dec_ref(v_a_140_);
return v_res_147_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0(void){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Lean_Meta_Sym_instInhabitedSymM___redArg();
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2(lean_object* v_msg_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
lean_object* v___x_157_; lean_object* v___x_4216__overap_158_; lean_object* v___x_159_; 
v___x_157_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0, &l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0);
v___x_4216__overap_158_ = lean_panic_fn_borrowed(v___x_157_, v_msg_149_);
lean_inc(v___y_155_);
lean_inc_ref(v___y_154_);
lean_inc(v___y_153_);
lean_inc_ref(v___y_152_);
lean_inc(v___y_151_);
lean_inc_ref(v___y_150_);
v___x_159_ = lean_apply_7(v___x_4216__overap_158_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, lean_box(0));
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___boxed(lean_object* v_msg_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2(v_msg_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_169_, lean_object* v_vals_170_, lean_object* v_i_171_, lean_object* v_k_172_){
_start:
{
lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_173_ = lean_array_get_size(v_keys_169_);
v___x_174_ = lean_nat_dec_lt(v_i_171_, v___x_173_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; 
lean_dec(v_i_171_);
v___x_175_ = lean_box(0);
return v___x_175_;
}
else
{
lean_object* v_k_x27_176_; size_t v___x_177_; size_t v___x_178_; uint8_t v___x_179_; 
v_k_x27_176_ = lean_array_fget_borrowed(v_keys_169_, v_i_171_);
v___x_177_ = lean_ptr_addr(v_k_172_);
v___x_178_ = lean_ptr_addr(v_k_x27_176_);
v___x_179_ = lean_usize_dec_eq(v___x_177_, v___x_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = lean_unsigned_to_nat(1u);
v___x_181_ = lean_nat_add(v_i_171_, v___x_180_);
lean_dec(v_i_171_);
v_i_171_ = v___x_181_;
goto _start;
}
else
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = lean_array_fget_borrowed(v_vals_170_, v_i_171_);
lean_dec(v_i_171_);
lean_inc(v___x_183_);
v___x_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
return v___x_184_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_185_, lean_object* v_vals_186_, lean_object* v_i_187_, lean_object* v_k_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(v_keys_185_, v_vals_186_, v_i_187_, v_k_188_);
lean_dec_ref(v_k_188_);
lean_dec_ref(v_vals_186_);
lean_dec_ref(v_keys_185_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(lean_object* v_x_190_, size_t v_x_191_, lean_object* v_x_192_){
_start:
{
if (lean_obj_tag(v_x_190_) == 0)
{
lean_object* v_es_193_; lean_object* v___x_194_; size_t v___x_195_; size_t v___x_196_; lean_object* v_j_197_; lean_object* v___x_198_; 
v_es_193_ = lean_ctor_get(v_x_190_, 0);
v___x_194_ = lean_box(2);
v___x_195_ = ((size_t)31ULL);
v___x_196_ = lean_usize_land(v_x_191_, v___x_195_);
v_j_197_ = lean_usize_to_nat(v___x_196_);
v___x_198_ = lean_array_get_borrowed(v___x_194_, v_es_193_, v_j_197_);
lean_dec(v_j_197_);
switch(lean_obj_tag(v___x_198_))
{
case 0:
{
lean_object* v_key_199_; lean_object* v_val_200_; size_t v___x_201_; size_t v___x_202_; uint8_t v___x_203_; 
v_key_199_ = lean_ctor_get(v___x_198_, 0);
v_val_200_ = lean_ctor_get(v___x_198_, 1);
v___x_201_ = lean_ptr_addr(v_x_192_);
v___x_202_ = lean_ptr_addr(v_key_199_);
v___x_203_ = lean_usize_dec_eq(v___x_201_, v___x_202_);
if (v___x_203_ == 0)
{
lean_object* v___x_204_; 
v___x_204_ = lean_box(0);
return v___x_204_;
}
else
{
lean_object* v___x_205_; 
lean_inc(v_val_200_);
v___x_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_205_, 0, v_val_200_);
return v___x_205_;
}
}
case 1:
{
lean_object* v_node_206_; size_t v___x_207_; size_t v___x_208_; 
v_node_206_ = lean_ctor_get(v___x_198_, 0);
v___x_207_ = ((size_t)5ULL);
v___x_208_ = lean_usize_shift_right(v_x_191_, v___x_207_);
v_x_190_ = v_node_206_;
v_x_191_ = v___x_208_;
goto _start;
}
default: 
{
lean_object* v___x_210_; 
v___x_210_ = lean_box(0);
return v___x_210_;
}
}
}
else
{
lean_object* v_ks_211_; lean_object* v_vs_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v_ks_211_ = lean_ctor_get(v_x_190_, 0);
v_vs_212_ = lean_ctor_get(v_x_190_, 1);
v___x_213_ = lean_unsigned_to_nat(0u);
v___x_214_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(v_ks_211_, v_vs_212_, v___x_213_, v_x_192_);
return v___x_214_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_215_, lean_object* v_x_216_, lean_object* v_x_217_){
_start:
{
size_t v_x_4709__boxed_218_; lean_object* v_res_219_; 
v_x_4709__boxed_218_ = lean_unbox_usize(v_x_216_);
lean_dec(v_x_216_);
v_res_219_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_215_, v_x_4709__boxed_218_, v_x_217_);
lean_dec_ref(v_x_217_);
lean_dec_ref(v_x_215_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(lean_object* v_x_220_, lean_object* v_x_221_){
_start:
{
size_t v___x_222_; size_t v___x_223_; size_t v___x_224_; uint64_t v___x_225_; size_t v___x_226_; lean_object* v___x_227_; 
v___x_222_ = lean_ptr_addr(v_x_221_);
v___x_223_ = ((size_t)3ULL);
v___x_224_ = lean_usize_shift_right(v___x_222_, v___x_223_);
v___x_225_ = lean_usize_to_uint64(v___x_224_);
v___x_226_ = lean_uint64_to_usize(v___x_225_);
v___x_227_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_220_, v___x_226_, v_x_221_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg___boxed(lean_object* v_x_228_, lean_object* v_x_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_x_228_, v_x_229_);
lean_dec_ref(v_x_229_);
lean_dec_ref(v_x_228_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__5_spec__6___redArg(lean_object* v_x_231_, lean_object* v_x_232_, lean_object* v_x_233_, lean_object* v_x_234_){
_start:
{
lean_object* v_ks_235_; lean_object* v_vs_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_262_; 
v_ks_235_ = lean_ctor_get(v_x_231_, 0);
v_vs_236_ = lean_ctor_get(v_x_231_, 1);
v_isSharedCheck_262_ = !lean_is_exclusive(v_x_231_);
if (v_isSharedCheck_262_ == 0)
{
v___x_238_ = v_x_231_;
v_isShared_239_ = v_isSharedCheck_262_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_vs_236_);
lean_inc(v_ks_235_);
lean_dec(v_x_231_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_262_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_240_; uint8_t v___x_241_; 
v___x_240_ = lean_array_get_size(v_ks_235_);
v___x_241_ = lean_nat_dec_lt(v_x_232_, v___x_240_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_245_; 
lean_dec(v_x_232_);
v___x_242_ = lean_array_push(v_ks_235_, v_x_233_);
v___x_243_ = lean_array_push(v_vs_236_, v_x_234_);
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 1, v___x_243_);
lean_ctor_set(v___x_238_, 0, v___x_242_);
v___x_245_ = v___x_238_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v___x_242_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v___x_243_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
else
{
lean_object* v_k_x27_247_; size_t v___x_248_; size_t v___x_249_; uint8_t v___x_250_; 
v_k_x27_247_ = lean_array_fget_borrowed(v_ks_235_, v_x_232_);
v___x_248_ = lean_ptr_addr(v_x_233_);
v___x_249_ = lean_ptr_addr(v_k_x27_247_);
v___x_250_ = lean_usize_dec_eq(v___x_248_, v___x_249_);
if (v___x_250_ == 0)
{
lean_object* v___x_252_; 
if (v_isShared_239_ == 0)
{
v___x_252_ = v___x_238_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_ks_235_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v_vs_236_);
v___x_252_ = v_reuseFailAlloc_256_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = lean_unsigned_to_nat(1u);
v___x_254_ = lean_nat_add(v_x_232_, v___x_253_);
lean_dec(v_x_232_);
v_x_231_ = v___x_252_;
v_x_232_ = v___x_254_;
goto _start;
}
}
else
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_260_; 
v___x_257_ = lean_array_fset(v_ks_235_, v_x_232_, v_x_233_);
v___x_258_ = lean_array_fset(v_vs_236_, v_x_232_, v_x_234_);
lean_dec(v_x_232_);
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 1, v___x_258_);
lean_ctor_set(v___x_238_, 0, v___x_257_);
v___x_260_ = v___x_238_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_257_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v___x_258_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__5___redArg(lean_object* v_n_263_, lean_object* v_k_264_, lean_object* v_v_265_){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = lean_unsigned_to_nat(0u);
v___x_267_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__5_spec__6___redArg(v_n_263_, v___x_266_, v_k_264_, v_v_265_);
return v___x_267_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(lean_object* v_x_269_, size_t v_x_270_, size_t v_x_271_, lean_object* v_x_272_, lean_object* v_x_273_){
_start:
{
if (lean_obj_tag(v_x_269_) == 0)
{
lean_object* v_es_274_; size_t v___x_275_; size_t v___x_276_; lean_object* v_j_277_; lean_object* v___x_278_; uint8_t v___x_279_; 
v_es_274_ = lean_ctor_get(v_x_269_, 0);
v___x_275_ = ((size_t)31ULL);
v___x_276_ = lean_usize_land(v_x_270_, v___x_275_);
v_j_277_ = lean_usize_to_nat(v___x_276_);
v___x_278_ = lean_array_get_size(v_es_274_);
v___x_279_ = lean_nat_dec_lt(v_j_277_, v___x_278_);
if (v___x_279_ == 0)
{
lean_dec(v_j_277_);
lean_dec(v_x_273_);
lean_dec_ref(v_x_272_);
return v_x_269_;
}
else
{
lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_320_; 
lean_inc_ref(v_es_274_);
v_isSharedCheck_320_ = !lean_is_exclusive(v_x_269_);
if (v_isSharedCheck_320_ == 0)
{
lean_object* v_unused_321_; 
v_unused_321_ = lean_ctor_get(v_x_269_, 0);
lean_dec(v_unused_321_);
v___x_281_ = v_x_269_;
v_isShared_282_ = v_isSharedCheck_320_;
goto v_resetjp_280_;
}
else
{
lean_dec(v_x_269_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_320_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v_v_283_; lean_object* v___x_284_; lean_object* v_xs_x27_285_; lean_object* v___y_287_; 
v_v_283_ = lean_array_fget(v_es_274_, v_j_277_);
v___x_284_ = lean_box(0);
v_xs_x27_285_ = lean_array_fset(v_es_274_, v_j_277_, v___x_284_);
switch(lean_obj_tag(v_v_283_))
{
case 0:
{
lean_object* v_key_292_; lean_object* v_val_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_305_; 
v_key_292_ = lean_ctor_get(v_v_283_, 0);
v_val_293_ = lean_ctor_get(v_v_283_, 1);
v_isSharedCheck_305_ = !lean_is_exclusive(v_v_283_);
if (v_isSharedCheck_305_ == 0)
{
v___x_295_ = v_v_283_;
v_isShared_296_ = v_isSharedCheck_305_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_val_293_);
lean_inc(v_key_292_);
lean_dec(v_v_283_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_305_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
size_t v___x_297_; size_t v___x_298_; uint8_t v___x_299_; 
v___x_297_ = lean_ptr_addr(v_x_272_);
v___x_298_ = lean_ptr_addr(v_key_292_);
v___x_299_ = lean_usize_dec_eq(v___x_297_, v___x_298_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; lean_object* v___x_301_; 
lean_del_object(v___x_295_);
v___x_300_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_292_, v_val_293_, v_x_272_, v_x_273_);
v___x_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
v___y_287_ = v___x_301_;
goto v___jp_286_;
}
else
{
lean_object* v___x_303_; 
lean_dec(v_val_293_);
lean_dec(v_key_292_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 1, v_x_273_);
lean_ctor_set(v___x_295_, 0, v_x_272_);
v___x_303_ = v___x_295_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_x_272_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v_x_273_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
v___y_287_ = v___x_303_;
goto v___jp_286_;
}
}
}
}
case 1:
{
lean_object* v_node_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_318_; 
v_node_306_ = lean_ctor_get(v_v_283_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v_v_283_);
if (v_isSharedCheck_318_ == 0)
{
v___x_308_ = v_v_283_;
v_isShared_309_ = v_isSharedCheck_318_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_node_306_);
lean_dec(v_v_283_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_318_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
size_t v___x_310_; size_t v___x_311_; size_t v___x_312_; size_t v___x_313_; lean_object* v___x_314_; lean_object* v___x_316_; 
v___x_310_ = ((size_t)5ULL);
v___x_311_ = lean_usize_shift_right(v_x_270_, v___x_310_);
v___x_312_ = ((size_t)1ULL);
v___x_313_ = lean_usize_add(v_x_271_, v___x_312_);
v___x_314_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_node_306_, v___x_311_, v___x_313_, v_x_272_, v_x_273_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 0, v___x_314_);
v___x_316_ = v___x_308_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_314_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
v___y_287_ = v___x_316_;
goto v___jp_286_;
}
}
}
default: 
{
lean_object* v___x_319_; 
v___x_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_319_, 0, v_x_272_);
lean_ctor_set(v___x_319_, 1, v_x_273_);
v___y_287_ = v___x_319_;
goto v___jp_286_;
}
}
v___jp_286_:
{
lean_object* v___x_288_; lean_object* v___x_290_; 
v___x_288_ = lean_array_fset(v_xs_x27_285_, v_j_277_, v___y_287_);
lean_dec(v_j_277_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 0, v___x_288_);
v___x_290_ = v___x_281_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v___x_288_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
}
else
{
lean_object* v_ks_322_; lean_object* v_vs_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_341_; 
v_ks_322_ = lean_ctor_get(v_x_269_, 0);
v_vs_323_ = lean_ctor_get(v_x_269_, 1);
v_isSharedCheck_341_ = !lean_is_exclusive(v_x_269_);
if (v_isSharedCheck_341_ == 0)
{
v___x_325_ = v_x_269_;
v_isShared_326_ = v_isSharedCheck_341_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_vs_323_);
lean_inc(v_ks_322_);
lean_dec(v_x_269_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_341_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_328_; 
if (v_isShared_326_ == 0)
{
v___x_328_ = v___x_325_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_ks_322_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v_vs_323_);
v___x_328_ = v_reuseFailAlloc_340_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_object* v_newNode_329_; size_t v___x_330_; uint8_t v___x_331_; 
v_newNode_329_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__5___redArg(v___x_328_, v_x_272_, v_x_273_);
v___x_330_ = ((size_t)7ULL);
v___x_331_ = lean_usize_dec_le(v___x_330_, v_x_271_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_332_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_329_);
v___x_333_ = lean_unsigned_to_nat(4u);
v___x_334_ = lean_nat_dec_lt(v___x_332_, v___x_333_);
lean_dec(v___x_332_);
if (v___x_334_ == 0)
{
lean_object* v_ks_335_; lean_object* v_vs_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v_ks_335_ = lean_ctor_get(v_newNode_329_, 0);
lean_inc_ref(v_ks_335_);
v_vs_336_ = lean_ctor_get(v_newNode_329_, 1);
lean_inc_ref(v_vs_336_);
lean_dec_ref(v_newNode_329_);
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg___closed__0);
v___x_339_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_x_271_, v_ks_335_, v_vs_336_, v___x_337_, v___x_338_);
lean_dec_ref(v_vs_336_);
lean_dec_ref(v_ks_335_);
return v___x_339_;
}
else
{
return v_newNode_329_;
}
}
else
{
return v_newNode_329_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(size_t v_depth_342_, lean_object* v_keys_343_, lean_object* v_vals_344_, lean_object* v_i_345_, lean_object* v_entries_346_){
_start:
{
lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_347_ = lean_array_get_size(v_keys_343_);
v___x_348_ = lean_nat_dec_lt(v_i_345_, v___x_347_);
if (v___x_348_ == 0)
{
lean_dec(v_i_345_);
return v_entries_346_;
}
else
{
lean_object* v_k_349_; lean_object* v_v_350_; size_t v___x_351_; size_t v___x_352_; size_t v___x_353_; uint64_t v___x_354_; size_t v_h_355_; size_t v___x_356_; lean_object* v___x_357_; size_t v___x_358_; size_t v___x_359_; size_t v___x_360_; size_t v_h_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v_k_349_ = lean_array_fget_borrowed(v_keys_343_, v_i_345_);
v_v_350_ = lean_array_fget_borrowed(v_vals_344_, v_i_345_);
v___x_351_ = lean_ptr_addr(v_k_349_);
v___x_352_ = ((size_t)3ULL);
v___x_353_ = lean_usize_shift_right(v___x_351_, v___x_352_);
v___x_354_ = lean_usize_to_uint64(v___x_353_);
v_h_355_ = lean_uint64_to_usize(v___x_354_);
v___x_356_ = ((size_t)5ULL);
v___x_357_ = lean_unsigned_to_nat(1u);
v___x_358_ = ((size_t)1ULL);
v___x_359_ = lean_usize_sub(v_depth_342_, v___x_358_);
v___x_360_ = lean_usize_mul(v___x_356_, v___x_359_);
v_h_361_ = lean_usize_shift_right(v_h_355_, v___x_360_);
v___x_362_ = lean_nat_add(v_i_345_, v___x_357_);
lean_dec(v_i_345_);
lean_inc(v_v_350_);
lean_inc(v_k_349_);
v___x_363_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_entries_346_, v_h_361_, v_depth_342_, v_k_349_, v_v_350_);
v_i_345_ = v___x_362_;
v_entries_346_ = v___x_363_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_depth_365_, lean_object* v_keys_366_, lean_object* v_vals_367_, lean_object* v_i_368_, lean_object* v_entries_369_){
_start:
{
size_t v_depth_boxed_370_; lean_object* v_res_371_; 
v_depth_boxed_370_ = lean_unbox_usize(v_depth_365_);
lean_dec(v_depth_365_);
v_res_371_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_depth_boxed_370_, v_keys_366_, v_vals_367_, v_i_368_, v_entries_369_);
lean_dec_ref(v_vals_367_);
lean_dec_ref(v_keys_366_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_x_372_, lean_object* v_x_373_, lean_object* v_x_374_, lean_object* v_x_375_, lean_object* v_x_376_){
_start:
{
size_t v_x_4861__boxed_377_; size_t v_x_4862__boxed_378_; lean_object* v_res_379_; 
v_x_4861__boxed_377_ = lean_unbox_usize(v_x_373_);
lean_dec(v_x_373_);
v_x_4862__boxed_378_ = lean_unbox_usize(v_x_374_);
lean_dec(v_x_374_);
v_res_379_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_372_, v_x_4861__boxed_377_, v_x_4862__boxed_378_, v_x_375_, v_x_376_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(lean_object* v_x_380_, lean_object* v_x_381_, lean_object* v_x_382_){
_start:
{
size_t v___x_383_; size_t v___x_384_; size_t v___x_385_; uint64_t v___x_386_; size_t v___x_387_; size_t v___x_388_; lean_object* v___x_389_; 
v___x_383_ = lean_ptr_addr(v_x_381_);
v___x_384_ = ((size_t)3ULL);
v___x_385_ = lean_usize_shift_right(v___x_383_, v___x_384_);
v___x_386_ = lean_usize_to_uint64(v___x_385_);
v___x_387_ = lean_uint64_to_usize(v___x_386_);
v___x_388_ = ((size_t)1ULL);
v___x_389_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_380_, v___x_387_, v___x_388_, v_x_381_, v_x_382_);
return v___x_389_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_393_ = ((lean_object*)(l_Lean_Meta_Sym_getMaxFVar_x3f___closed__2));
v___x_394_ = lean_unsigned_to_nat(37u);
v___x_395_ = lean_unsigned_to_nat(52u);
v___x_396_ = ((lean_object*)(l_Lean_Meta_Sym_getMaxFVar_x3f___closed__1));
v___x_397_ = ((lean_object*)(l_Lean_Meta_Sym_getMaxFVar_x3f___closed__0));
v___x_398_ = l_mkPanicMessageWithDecl(v___x_397_, v___x_396_, v___x_395_, v___x_394_, v___x_393_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f(lean_object* v_e_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_){
_start:
{
lean_object* v_a_408_; lean_object* v___y_435_; lean_object* v___y_436_; lean_object* v___y_437_; lean_object* v___y_438_; lean_object* v___y_439_; lean_object* v___y_440_; lean_object* v___y_441_; lean_object* v___y_442_; lean_object* v_d_492_; lean_object* v_b_493_; lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; 
switch(lean_obj_tag(v_e_399_))
{
case 1:
{
lean_object* v_fvarId_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v_fvarId_504_ = lean_ctor_get(v_e_399_, 0);
lean_inc(v_fvarId_504_);
lean_dec_ref_known(v_e_399_, 1);
v___x_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_505_, 0, v_fvarId_504_);
v___x_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
return v___x_506_;
}
case 2:
{
lean_object* v_mvarId_507_; uint8_t v___x_547_; 
v_mvarId_507_ = lean_ctor_get(v_e_399_, 0);
v___x_547_ = l_Lean_Expr_hasFVar(v_e_399_);
if (v___x_547_ == 0)
{
uint8_t v___x_548_; 
v___x_548_ = l_Lean_Expr_hasMVar(v_e_399_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; lean_object* v___x_550_; 
lean_dec_ref_known(v_e_399_, 1);
v___x_549_ = lean_box(0);
v___x_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
return v___x_550_;
}
else
{
goto v___jp_508_;
}
}
else
{
goto v___jp_508_;
}
v___jp_508_:
{
lean_object* v___x_509_; lean_object* v_maxFVar_510_; lean_object* v___x_511_; 
v___x_509_ = lean_st_ref_get(v_a_401_);
v_maxFVar_510_ = lean_ctor_get(v___x_509_, 1);
lean_inc_ref(v_maxFVar_510_);
lean_dec(v___x_509_);
v___x_511_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_510_, v_e_399_);
lean_dec_ref(v_maxFVar_510_);
if (lean_obj_tag(v___x_511_) == 1)
{
lean_object* v_val_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
lean_dec_ref_known(v_e_399_, 1);
v_val_512_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v___x_511_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_val_512_);
lean_dec(v___x_511_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
lean_ctor_set_tag(v___x_514_, 0);
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_val_512_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
else
{
lean_object* v___x_520_; 
lean_dec(v___x_511_);
lean_inc(v_mvarId_507_);
v___x_520_ = l_Lean_MVarId_getDecl(v_mvarId_507_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_a_521_; lean_object* v_lctx_522_; lean_object* v_decls_523_; uint8_t v___x_524_; 
v_a_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_a_521_);
lean_dec_ref_known(v___x_520_, 1);
v_lctx_522_ = lean_ctor_get(v_a_521_, 1);
lean_inc_ref(v_lctx_522_);
lean_dec(v_a_521_);
v_decls_523_ = lean_ctor_get(v_lctx_522_, 1);
v___x_524_ = l_Lean_PersistentArray_isEmpty___redArg(v_decls_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; 
v___x_525_ = l_Lean_LocalContext_lastDecl(v_lctx_522_);
lean_dec_ref(v_lctx_522_);
if (lean_obj_tag(v___x_525_) == 1)
{
lean_object* v_val_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_534_; 
v_val_526_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_534_ == 0)
{
v___x_528_ = v___x_525_;
v_isShared_529_ = v_isSharedCheck_534_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_val_526_);
lean_dec(v___x_525_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_534_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_530_; lean_object* v___x_532_; 
v___x_530_ = l_Lean_LocalDecl_fvarId(v_val_526_);
lean_dec(v_val_526_);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 0, v___x_530_);
v___x_532_ = v___x_528_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_530_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
v_a_408_ = v___x_532_;
goto v___jp_407_;
}
}
}
else
{
lean_object* v___x_535_; lean_object* v___x_536_; 
lean_dec(v___x_525_);
v___x_535_ = lean_obj_once(&l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3, &l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3_once, _init_l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3);
v___x_536_ = l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2(v___x_535_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v_a_537_; 
v_a_537_ = lean_ctor_get(v___x_536_, 0);
lean_inc(v_a_537_);
lean_dec_ref_known(v___x_536_, 1);
v_a_408_ = v_a_537_;
goto v___jp_407_;
}
else
{
lean_dec_ref_known(v_e_399_, 1);
return v___x_536_;
}
}
}
else
{
lean_object* v___x_538_; 
lean_dec_ref(v_lctx_522_);
v___x_538_ = lean_box(0);
v_a_408_ = v___x_538_;
goto v___jp_407_;
}
}
else
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
lean_dec_ref_known(v_e_399_, 1);
v_a_539_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_520_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_520_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
}
}
case 5:
{
lean_object* v_fn_551_; lean_object* v_arg_552_; uint8_t v___x_602_; 
v_fn_551_ = lean_ctor_get(v_e_399_, 0);
v_arg_552_ = lean_ctor_get(v_e_399_, 1);
v___x_602_ = l_Lean_Expr_hasFVar(v_e_399_);
if (v___x_602_ == 0)
{
uint8_t v___x_603_; 
v___x_603_ = l_Lean_Expr_hasMVar(v_e_399_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; lean_object* v___x_605_; 
lean_dec_ref_known(v_e_399_, 2);
v___x_604_ = lean_box(0);
v___x_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
return v___x_605_;
}
else
{
goto v___jp_553_;
}
}
else
{
goto v___jp_553_;
}
v___jp_553_:
{
lean_object* v___x_554_; lean_object* v_maxFVar_555_; lean_object* v___x_556_; 
v___x_554_ = lean_st_ref_get(v_a_401_);
v_maxFVar_555_ = lean_ctor_get(v___x_554_, 1);
lean_inc_ref(v_maxFVar_555_);
lean_dec(v___x_554_);
v___x_556_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_555_, v_e_399_);
lean_dec_ref(v_maxFVar_555_);
if (lean_obj_tag(v___x_556_) == 1)
{
lean_object* v_val_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_564_; 
lean_dec_ref_known(v_e_399_, 2);
v_val_557_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_564_ == 0)
{
v___x_559_ = v___x_556_;
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_val_557_);
lean_dec(v___x_556_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
if (v_isShared_560_ == 0)
{
lean_ctor_set_tag(v___x_559_, 0);
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_val_557_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
else
{
lean_object* v___x_565_; 
lean_dec(v___x_556_);
lean_inc_ref(v_fn_551_);
v___x_565_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_fn_551_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_a_566_; lean_object* v___x_567_; 
v_a_566_ = lean_ctor_get(v___x_565_, 0);
lean_inc(v_a_566_);
lean_dec_ref_known(v___x_565_, 1);
lean_inc_ref(v_arg_552_);
v___x_567_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_arg_552_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_a_568_; lean_object* v___x_569_; 
v_a_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_a_568_);
lean_dec_ref_known(v___x_567_, 1);
v___x_569_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_566_, v_a_568_, v_a_402_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_601_; 
v_a_570_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_601_ == 0)
{
v___x_572_ = v___x_569_;
v_isShared_573_ = v_isSharedCheck_601_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_569_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_601_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_574_; lean_object* v_share_575_; lean_object* v_maxFVar_576_; lean_object* v_proofInstInfo_577_; lean_object* v_proofInstInfoFVar_578_; lean_object* v_letValue_579_; lean_object* v_inferType_580_; lean_object* v_getLevel_581_; lean_object* v_congrInfo_582_; lean_object* v_defEqI_583_; lean_object* v_extensions_584_; lean_object* v_issues_585_; lean_object* v_canon_586_; lean_object* v_instanceOverrides_587_; uint8_t v_debug_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_600_; 
v___x_574_ = lean_st_ref_take(v_a_401_);
v_share_575_ = lean_ctor_get(v___x_574_, 0);
v_maxFVar_576_ = lean_ctor_get(v___x_574_, 1);
v_proofInstInfo_577_ = lean_ctor_get(v___x_574_, 2);
v_proofInstInfoFVar_578_ = lean_ctor_get(v___x_574_, 3);
v_letValue_579_ = lean_ctor_get(v___x_574_, 4);
v_inferType_580_ = lean_ctor_get(v___x_574_, 5);
v_getLevel_581_ = lean_ctor_get(v___x_574_, 6);
v_congrInfo_582_ = lean_ctor_get(v___x_574_, 7);
v_defEqI_583_ = lean_ctor_get(v___x_574_, 8);
v_extensions_584_ = lean_ctor_get(v___x_574_, 9);
v_issues_585_ = lean_ctor_get(v___x_574_, 10);
v_canon_586_ = lean_ctor_get(v___x_574_, 11);
v_instanceOverrides_587_ = lean_ctor_get(v___x_574_, 12);
v_debug_588_ = lean_ctor_get_uint8(v___x_574_, sizeof(void*)*13);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_600_ == 0)
{
v___x_590_ = v___x_574_;
v_isShared_591_ = v_isSharedCheck_600_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_instanceOverrides_587_);
lean_inc(v_canon_586_);
lean_inc(v_issues_585_);
lean_inc(v_extensions_584_);
lean_inc(v_defEqI_583_);
lean_inc(v_congrInfo_582_);
lean_inc(v_getLevel_581_);
lean_inc(v_inferType_580_);
lean_inc(v_letValue_579_);
lean_inc(v_proofInstInfoFVar_578_);
lean_inc(v_proofInstInfo_577_);
lean_inc(v_maxFVar_576_);
lean_inc(v_share_575_);
lean_dec(v___x_574_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_600_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_592_; lean_object* v___x_594_; 
lean_inc(v_a_570_);
v___x_592_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_576_, v_e_399_, v_a_570_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 1, v___x_592_);
v___x_594_ = v___x_590_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_share_575_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v___x_592_);
lean_ctor_set(v_reuseFailAlloc_599_, 2, v_proofInstInfo_577_);
lean_ctor_set(v_reuseFailAlloc_599_, 3, v_proofInstInfoFVar_578_);
lean_ctor_set(v_reuseFailAlloc_599_, 4, v_letValue_579_);
lean_ctor_set(v_reuseFailAlloc_599_, 5, v_inferType_580_);
lean_ctor_set(v_reuseFailAlloc_599_, 6, v_getLevel_581_);
lean_ctor_set(v_reuseFailAlloc_599_, 7, v_congrInfo_582_);
lean_ctor_set(v_reuseFailAlloc_599_, 8, v_defEqI_583_);
lean_ctor_set(v_reuseFailAlloc_599_, 9, v_extensions_584_);
lean_ctor_set(v_reuseFailAlloc_599_, 10, v_issues_585_);
lean_ctor_set(v_reuseFailAlloc_599_, 11, v_canon_586_);
lean_ctor_set(v_reuseFailAlloc_599_, 12, v_instanceOverrides_587_);
lean_ctor_set_uint8(v_reuseFailAlloc_599_, sizeof(void*)*13, v_debug_588_);
v___x_594_ = v_reuseFailAlloc_599_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_595_; lean_object* v___x_597_; 
v___x_595_ = lean_st_ref_put(v_a_401_, v___x_594_);
if (v_isShared_573_ == 0)
{
v___x_597_ = v___x_572_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_570_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_399_, 2);
return v___x_569_;
}
}
else
{
lean_dec(v_a_566_);
lean_dec_ref_known(v_e_399_, 2);
return v___x_567_;
}
}
else
{
lean_dec_ref_known(v_e_399_, 2);
return v___x_565_;
}
}
}
}
case 6:
{
lean_object* v_binderType_606_; lean_object* v_body_607_; 
v_binderType_606_ = lean_ctor_get(v_e_399_, 1);
v_body_607_ = lean_ctor_get(v_e_399_, 2);
lean_inc_ref(v_body_607_);
lean_inc_ref(v_binderType_606_);
v_d_492_ = v_binderType_606_;
v_b_493_ = v_body_607_;
v___y_494_ = v_a_400_;
v___y_495_ = v_a_401_;
v___y_496_ = v_a_402_;
v___y_497_ = v_a_403_;
v___y_498_ = v_a_404_;
v___y_499_ = v_a_405_;
goto v___jp_491_;
}
case 7:
{
lean_object* v_binderType_608_; lean_object* v_body_609_; 
v_binderType_608_ = lean_ctor_get(v_e_399_, 1);
v_body_609_ = lean_ctor_get(v_e_399_, 2);
lean_inc_ref(v_body_609_);
lean_inc_ref(v_binderType_608_);
v_d_492_ = v_binderType_608_;
v_b_493_ = v_body_609_;
v___y_494_ = v_a_400_;
v___y_495_ = v_a_401_;
v___y_496_ = v_a_402_;
v___y_497_ = v_a_403_;
v___y_498_ = v_a_404_;
v___y_499_ = v_a_405_;
goto v___jp_491_;
}
case 8:
{
lean_object* v_type_610_; lean_object* v_value_611_; lean_object* v_body_612_; uint8_t v___x_666_; 
v_type_610_ = lean_ctor_get(v_e_399_, 1);
v_value_611_ = lean_ctor_get(v_e_399_, 2);
v_body_612_ = lean_ctor_get(v_e_399_, 3);
v___x_666_ = l_Lean_Expr_hasFVar(v_e_399_);
if (v___x_666_ == 0)
{
uint8_t v___x_667_; 
v___x_667_ = l_Lean_Expr_hasMVar(v_e_399_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; lean_object* v___x_669_; 
lean_dec_ref_known(v_e_399_, 4);
v___x_668_ = lean_box(0);
v___x_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
return v___x_669_;
}
else
{
goto v___jp_613_;
}
}
else
{
goto v___jp_613_;
}
v___jp_613_:
{
lean_object* v___x_614_; lean_object* v_maxFVar_615_; lean_object* v___x_616_; 
v___x_614_ = lean_st_ref_get(v_a_401_);
v_maxFVar_615_ = lean_ctor_get(v___x_614_, 1);
lean_inc_ref(v_maxFVar_615_);
lean_dec(v___x_614_);
v___x_616_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_615_, v_e_399_);
lean_dec_ref(v_maxFVar_615_);
if (lean_obj_tag(v___x_616_) == 1)
{
lean_object* v_val_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_624_; 
lean_dec_ref_known(v_e_399_, 4);
v_val_617_ = lean_ctor_get(v___x_616_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_624_ == 0)
{
v___x_619_ = v___x_616_;
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_val_617_);
lean_dec(v___x_616_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
lean_ctor_set_tag(v___x_619_, 0);
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_val_617_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
else
{
lean_object* v___x_625_; 
lean_dec(v___x_616_);
lean_inc_ref(v_type_610_);
v___x_625_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_type_610_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v_a_626_; lean_object* v___x_627_; 
v_a_626_ = lean_ctor_get(v___x_625_, 0);
lean_inc(v_a_626_);
lean_dec_ref_known(v___x_625_, 1);
lean_inc_ref(v_value_611_);
v___x_627_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_value_611_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v_a_628_; lean_object* v___x_629_; 
v_a_628_ = lean_ctor_get(v___x_627_, 0);
lean_inc(v_a_628_);
lean_dec_ref_known(v___x_627_, 1);
v___x_629_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_626_, v_a_628_, v_a_402_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; lean_object* v___x_631_; 
v_a_630_ = lean_ctor_get(v___x_629_, 0);
lean_inc(v_a_630_);
lean_dec_ref_known(v___x_629_, 1);
lean_inc_ref(v_body_612_);
v___x_631_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_body_612_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; lean_object* v___x_633_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_a_632_);
lean_dec_ref_known(v___x_631_, 1);
v___x_633_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_630_, v_a_632_, v_a_402_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_665_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_665_ == 0)
{
v___x_636_ = v___x_633_;
v_isShared_637_ = v_isSharedCheck_665_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_633_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_665_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_638_; lean_object* v_share_639_; lean_object* v_maxFVar_640_; lean_object* v_proofInstInfo_641_; lean_object* v_proofInstInfoFVar_642_; lean_object* v_letValue_643_; lean_object* v_inferType_644_; lean_object* v_getLevel_645_; lean_object* v_congrInfo_646_; lean_object* v_defEqI_647_; lean_object* v_extensions_648_; lean_object* v_issues_649_; lean_object* v_canon_650_; lean_object* v_instanceOverrides_651_; uint8_t v_debug_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_664_; 
v___x_638_ = lean_st_ref_take(v_a_401_);
v_share_639_ = lean_ctor_get(v___x_638_, 0);
v_maxFVar_640_ = lean_ctor_get(v___x_638_, 1);
v_proofInstInfo_641_ = lean_ctor_get(v___x_638_, 2);
v_proofInstInfoFVar_642_ = lean_ctor_get(v___x_638_, 3);
v_letValue_643_ = lean_ctor_get(v___x_638_, 4);
v_inferType_644_ = lean_ctor_get(v___x_638_, 5);
v_getLevel_645_ = lean_ctor_get(v___x_638_, 6);
v_congrInfo_646_ = lean_ctor_get(v___x_638_, 7);
v_defEqI_647_ = lean_ctor_get(v___x_638_, 8);
v_extensions_648_ = lean_ctor_get(v___x_638_, 9);
v_issues_649_ = lean_ctor_get(v___x_638_, 10);
v_canon_650_ = lean_ctor_get(v___x_638_, 11);
v_instanceOverrides_651_ = lean_ctor_get(v___x_638_, 12);
v_debug_652_ = lean_ctor_get_uint8(v___x_638_, sizeof(void*)*13);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_664_ == 0)
{
v___x_654_ = v___x_638_;
v_isShared_655_ = v_isSharedCheck_664_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_instanceOverrides_651_);
lean_inc(v_canon_650_);
lean_inc(v_issues_649_);
lean_inc(v_extensions_648_);
lean_inc(v_defEqI_647_);
lean_inc(v_congrInfo_646_);
lean_inc(v_getLevel_645_);
lean_inc(v_inferType_644_);
lean_inc(v_letValue_643_);
lean_inc(v_proofInstInfoFVar_642_);
lean_inc(v_proofInstInfo_641_);
lean_inc(v_maxFVar_640_);
lean_inc(v_share_639_);
lean_dec(v___x_638_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_664_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_656_; lean_object* v___x_658_; 
lean_inc(v_a_634_);
v___x_656_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_640_, v_e_399_, v_a_634_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 1, v___x_656_);
v___x_658_ = v___x_654_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_share_639_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v___x_656_);
lean_ctor_set(v_reuseFailAlloc_663_, 2, v_proofInstInfo_641_);
lean_ctor_set(v_reuseFailAlloc_663_, 3, v_proofInstInfoFVar_642_);
lean_ctor_set(v_reuseFailAlloc_663_, 4, v_letValue_643_);
lean_ctor_set(v_reuseFailAlloc_663_, 5, v_inferType_644_);
lean_ctor_set(v_reuseFailAlloc_663_, 6, v_getLevel_645_);
lean_ctor_set(v_reuseFailAlloc_663_, 7, v_congrInfo_646_);
lean_ctor_set(v_reuseFailAlloc_663_, 8, v_defEqI_647_);
lean_ctor_set(v_reuseFailAlloc_663_, 9, v_extensions_648_);
lean_ctor_set(v_reuseFailAlloc_663_, 10, v_issues_649_);
lean_ctor_set(v_reuseFailAlloc_663_, 11, v_canon_650_);
lean_ctor_set(v_reuseFailAlloc_663_, 12, v_instanceOverrides_651_);
lean_ctor_set_uint8(v_reuseFailAlloc_663_, sizeof(void*)*13, v_debug_652_);
v___x_658_ = v_reuseFailAlloc_663_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_659_ = lean_st_ref_put(v_a_401_, v___x_658_);
if (v_isShared_637_ == 0)
{
v___x_661_ = v___x_636_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_634_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_399_, 4);
return v___x_633_;
}
}
else
{
lean_dec(v_a_630_);
lean_dec_ref_known(v_e_399_, 4);
return v___x_631_;
}
}
else
{
lean_dec_ref_known(v_e_399_, 4);
return v___x_629_;
}
}
else
{
lean_dec(v_a_626_);
lean_dec_ref_known(v_e_399_, 4);
return v___x_627_;
}
}
else
{
lean_dec_ref_known(v_e_399_, 4);
return v___x_625_;
}
}
}
}
case 10:
{
lean_object* v_expr_670_; uint8_t v___x_716_; 
v_expr_670_ = lean_ctor_get(v_e_399_, 1);
lean_inc_ref(v_expr_670_);
lean_dec_ref_known(v_e_399_, 2);
v___x_716_ = l_Lean_Expr_hasFVar(v_expr_670_);
if (v___x_716_ == 0)
{
uint8_t v___x_717_; 
v___x_717_ = l_Lean_Expr_hasMVar(v_expr_670_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; lean_object* v___x_719_; 
lean_dec_ref(v_expr_670_);
v___x_718_ = lean_box(0);
v___x_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
return v___x_719_;
}
else
{
goto v___jp_671_;
}
}
else
{
goto v___jp_671_;
}
v___jp_671_:
{
lean_object* v___x_672_; lean_object* v_maxFVar_673_; lean_object* v___x_674_; 
v___x_672_ = lean_st_ref_get(v_a_401_);
v_maxFVar_673_ = lean_ctor_get(v___x_672_, 1);
lean_inc_ref(v_maxFVar_673_);
lean_dec(v___x_672_);
v___x_674_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_673_, v_expr_670_);
lean_dec_ref(v_maxFVar_673_);
if (lean_obj_tag(v___x_674_) == 1)
{
lean_object* v_val_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_682_; 
lean_dec_ref(v_expr_670_);
v_val_675_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_682_ == 0)
{
v___x_677_ = v___x_674_;
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_val_675_);
lean_dec(v___x_674_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
if (v_isShared_678_ == 0)
{
lean_ctor_set_tag(v___x_677_, 0);
v___x_680_ = v___x_677_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_val_675_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
else
{
lean_object* v___x_683_; 
lean_dec(v___x_674_);
lean_inc_ref(v_expr_670_);
v___x_683_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_expr_670_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_715_; 
v_a_684_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_715_ == 0)
{
v___x_686_ = v___x_683_;
v_isShared_687_ = v_isSharedCheck_715_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_683_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_715_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v_share_689_; lean_object* v_maxFVar_690_; lean_object* v_proofInstInfo_691_; lean_object* v_proofInstInfoFVar_692_; lean_object* v_letValue_693_; lean_object* v_inferType_694_; lean_object* v_getLevel_695_; lean_object* v_congrInfo_696_; lean_object* v_defEqI_697_; lean_object* v_extensions_698_; lean_object* v_issues_699_; lean_object* v_canon_700_; lean_object* v_instanceOverrides_701_; uint8_t v_debug_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_714_; 
v___x_688_ = lean_st_ref_take(v_a_401_);
v_share_689_ = lean_ctor_get(v___x_688_, 0);
v_maxFVar_690_ = lean_ctor_get(v___x_688_, 1);
v_proofInstInfo_691_ = lean_ctor_get(v___x_688_, 2);
v_proofInstInfoFVar_692_ = lean_ctor_get(v___x_688_, 3);
v_letValue_693_ = lean_ctor_get(v___x_688_, 4);
v_inferType_694_ = lean_ctor_get(v___x_688_, 5);
v_getLevel_695_ = lean_ctor_get(v___x_688_, 6);
v_congrInfo_696_ = lean_ctor_get(v___x_688_, 7);
v_defEqI_697_ = lean_ctor_get(v___x_688_, 8);
v_extensions_698_ = lean_ctor_get(v___x_688_, 9);
v_issues_699_ = lean_ctor_get(v___x_688_, 10);
v_canon_700_ = lean_ctor_get(v___x_688_, 11);
v_instanceOverrides_701_ = lean_ctor_get(v___x_688_, 12);
v_debug_702_ = lean_ctor_get_uint8(v___x_688_, sizeof(void*)*13);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_714_ == 0)
{
v___x_704_ = v___x_688_;
v_isShared_705_ = v_isSharedCheck_714_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_instanceOverrides_701_);
lean_inc(v_canon_700_);
lean_inc(v_issues_699_);
lean_inc(v_extensions_698_);
lean_inc(v_defEqI_697_);
lean_inc(v_congrInfo_696_);
lean_inc(v_getLevel_695_);
lean_inc(v_inferType_694_);
lean_inc(v_letValue_693_);
lean_inc(v_proofInstInfoFVar_692_);
lean_inc(v_proofInstInfo_691_);
lean_inc(v_maxFVar_690_);
lean_inc(v_share_689_);
lean_dec(v___x_688_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_714_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_706_; lean_object* v___x_708_; 
lean_inc(v_a_684_);
v___x_706_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_690_, v_expr_670_, v_a_684_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 1, v___x_706_);
v___x_708_ = v___x_704_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_share_689_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v___x_706_);
lean_ctor_set(v_reuseFailAlloc_713_, 2, v_proofInstInfo_691_);
lean_ctor_set(v_reuseFailAlloc_713_, 3, v_proofInstInfoFVar_692_);
lean_ctor_set(v_reuseFailAlloc_713_, 4, v_letValue_693_);
lean_ctor_set(v_reuseFailAlloc_713_, 5, v_inferType_694_);
lean_ctor_set(v_reuseFailAlloc_713_, 6, v_getLevel_695_);
lean_ctor_set(v_reuseFailAlloc_713_, 7, v_congrInfo_696_);
lean_ctor_set(v_reuseFailAlloc_713_, 8, v_defEqI_697_);
lean_ctor_set(v_reuseFailAlloc_713_, 9, v_extensions_698_);
lean_ctor_set(v_reuseFailAlloc_713_, 10, v_issues_699_);
lean_ctor_set(v_reuseFailAlloc_713_, 11, v_canon_700_);
lean_ctor_set(v_reuseFailAlloc_713_, 12, v_instanceOverrides_701_);
lean_ctor_set_uint8(v_reuseFailAlloc_713_, sizeof(void*)*13, v_debug_702_);
v___x_708_ = v_reuseFailAlloc_713_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
lean_object* v___x_709_; lean_object* v___x_711_; 
v___x_709_ = lean_st_ref_put(v_a_401_, v___x_708_);
if (v_isShared_687_ == 0)
{
v___x_711_ = v___x_686_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_684_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
}
else
{
lean_dec_ref(v_expr_670_);
return v___x_683_;
}
}
}
}
case 11:
{
lean_object* v_struct_720_; uint8_t v___x_766_; 
v_struct_720_ = lean_ctor_get(v_e_399_, 2);
v___x_766_ = l_Lean_Expr_hasFVar(v_e_399_);
if (v___x_766_ == 0)
{
uint8_t v___x_767_; 
v___x_767_ = l_Lean_Expr_hasMVar(v_e_399_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; lean_object* v___x_769_; 
lean_dec_ref_known(v_e_399_, 3);
v___x_768_ = lean_box(0);
v___x_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
return v___x_769_;
}
else
{
goto v___jp_721_;
}
}
else
{
goto v___jp_721_;
}
v___jp_721_:
{
lean_object* v___x_722_; lean_object* v_maxFVar_723_; lean_object* v___x_724_; 
v___x_722_ = lean_st_ref_get(v_a_401_);
v_maxFVar_723_ = lean_ctor_get(v___x_722_, 1);
lean_inc_ref(v_maxFVar_723_);
lean_dec(v___x_722_);
v___x_724_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_723_, v_e_399_);
lean_dec_ref(v_maxFVar_723_);
if (lean_obj_tag(v___x_724_) == 1)
{
lean_object* v_val_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_dec_ref_known(v_e_399_, 3);
v_val_725_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_724_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_val_725_);
lean_dec(v___x_724_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
lean_ctor_set_tag(v___x_727_, 0);
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_val_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
else
{
lean_object* v___x_733_; 
lean_dec(v___x_724_);
lean_inc_ref(v_struct_720_);
v___x_733_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_struct_720_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_765_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_765_ == 0)
{
v___x_736_ = v___x_733_;
v_isShared_737_ = v_isSharedCheck_765_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_733_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_765_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_738_; lean_object* v_share_739_; lean_object* v_maxFVar_740_; lean_object* v_proofInstInfo_741_; lean_object* v_proofInstInfoFVar_742_; lean_object* v_letValue_743_; lean_object* v_inferType_744_; lean_object* v_getLevel_745_; lean_object* v_congrInfo_746_; lean_object* v_defEqI_747_; lean_object* v_extensions_748_; lean_object* v_issues_749_; lean_object* v_canon_750_; lean_object* v_instanceOverrides_751_; uint8_t v_debug_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_764_; 
v___x_738_ = lean_st_ref_take(v_a_401_);
v_share_739_ = lean_ctor_get(v___x_738_, 0);
v_maxFVar_740_ = lean_ctor_get(v___x_738_, 1);
v_proofInstInfo_741_ = lean_ctor_get(v___x_738_, 2);
v_proofInstInfoFVar_742_ = lean_ctor_get(v___x_738_, 3);
v_letValue_743_ = lean_ctor_get(v___x_738_, 4);
v_inferType_744_ = lean_ctor_get(v___x_738_, 5);
v_getLevel_745_ = lean_ctor_get(v___x_738_, 6);
v_congrInfo_746_ = lean_ctor_get(v___x_738_, 7);
v_defEqI_747_ = lean_ctor_get(v___x_738_, 8);
v_extensions_748_ = lean_ctor_get(v___x_738_, 9);
v_issues_749_ = lean_ctor_get(v___x_738_, 10);
v_canon_750_ = lean_ctor_get(v___x_738_, 11);
v_instanceOverrides_751_ = lean_ctor_get(v___x_738_, 12);
v_debug_752_ = lean_ctor_get_uint8(v___x_738_, sizeof(void*)*13);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_764_ == 0)
{
v___x_754_ = v___x_738_;
v_isShared_755_ = v_isSharedCheck_764_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_instanceOverrides_751_);
lean_inc(v_canon_750_);
lean_inc(v_issues_749_);
lean_inc(v_extensions_748_);
lean_inc(v_defEqI_747_);
lean_inc(v_congrInfo_746_);
lean_inc(v_getLevel_745_);
lean_inc(v_inferType_744_);
lean_inc(v_letValue_743_);
lean_inc(v_proofInstInfoFVar_742_);
lean_inc(v_proofInstInfo_741_);
lean_inc(v_maxFVar_740_);
lean_inc(v_share_739_);
lean_dec(v___x_738_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_764_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_756_; lean_object* v___x_758_; 
lean_inc(v_a_734_);
v___x_756_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_740_, v_e_399_, v_a_734_);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 1, v___x_756_);
v___x_758_ = v___x_754_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_share_739_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v___x_756_);
lean_ctor_set(v_reuseFailAlloc_763_, 2, v_proofInstInfo_741_);
lean_ctor_set(v_reuseFailAlloc_763_, 3, v_proofInstInfoFVar_742_);
lean_ctor_set(v_reuseFailAlloc_763_, 4, v_letValue_743_);
lean_ctor_set(v_reuseFailAlloc_763_, 5, v_inferType_744_);
lean_ctor_set(v_reuseFailAlloc_763_, 6, v_getLevel_745_);
lean_ctor_set(v_reuseFailAlloc_763_, 7, v_congrInfo_746_);
lean_ctor_set(v_reuseFailAlloc_763_, 8, v_defEqI_747_);
lean_ctor_set(v_reuseFailAlloc_763_, 9, v_extensions_748_);
lean_ctor_set(v_reuseFailAlloc_763_, 10, v_issues_749_);
lean_ctor_set(v_reuseFailAlloc_763_, 11, v_canon_750_);
lean_ctor_set(v_reuseFailAlloc_763_, 12, v_instanceOverrides_751_);
lean_ctor_set_uint8(v_reuseFailAlloc_763_, sizeof(void*)*13, v_debug_752_);
v___x_758_ = v_reuseFailAlloc_763_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
lean_object* v___x_759_; lean_object* v___x_761_; 
v___x_759_ = lean_st_ref_put(v_a_401_, v___x_758_);
if (v_isShared_737_ == 0)
{
v___x_761_ = v___x_736_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_734_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_399_, 3);
return v___x_733_;
}
}
}
}
default: 
{
lean_object* v___x_770_; lean_object* v___x_771_; 
lean_dec_ref(v_e_399_);
v___x_770_ = lean_box(0);
v___x_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
return v___x_771_;
}
}
v___jp_407_:
{
lean_object* v___x_409_; lean_object* v_share_410_; lean_object* v_maxFVar_411_; lean_object* v_proofInstInfo_412_; lean_object* v_proofInstInfoFVar_413_; lean_object* v_letValue_414_; lean_object* v_inferType_415_; lean_object* v_getLevel_416_; lean_object* v_congrInfo_417_; lean_object* v_defEqI_418_; lean_object* v_extensions_419_; lean_object* v_issues_420_; lean_object* v_canon_421_; lean_object* v_instanceOverrides_422_; uint8_t v_debug_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_433_; 
v___x_409_ = lean_st_ref_take(v_a_401_);
v_share_410_ = lean_ctor_get(v___x_409_, 0);
v_maxFVar_411_ = lean_ctor_get(v___x_409_, 1);
v_proofInstInfo_412_ = lean_ctor_get(v___x_409_, 2);
v_proofInstInfoFVar_413_ = lean_ctor_get(v___x_409_, 3);
v_letValue_414_ = lean_ctor_get(v___x_409_, 4);
v_inferType_415_ = lean_ctor_get(v___x_409_, 5);
v_getLevel_416_ = lean_ctor_get(v___x_409_, 6);
v_congrInfo_417_ = lean_ctor_get(v___x_409_, 7);
v_defEqI_418_ = lean_ctor_get(v___x_409_, 8);
v_extensions_419_ = lean_ctor_get(v___x_409_, 9);
v_issues_420_ = lean_ctor_get(v___x_409_, 10);
v_canon_421_ = lean_ctor_get(v___x_409_, 11);
v_instanceOverrides_422_ = lean_ctor_get(v___x_409_, 12);
v_debug_423_ = lean_ctor_get_uint8(v___x_409_, sizeof(void*)*13);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_433_ == 0)
{
v___x_425_ = v___x_409_;
v_isShared_426_ = v_isSharedCheck_433_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_instanceOverrides_422_);
lean_inc(v_canon_421_);
lean_inc(v_issues_420_);
lean_inc(v_extensions_419_);
lean_inc(v_defEqI_418_);
lean_inc(v_congrInfo_417_);
lean_inc(v_getLevel_416_);
lean_inc(v_inferType_415_);
lean_inc(v_letValue_414_);
lean_inc(v_proofInstInfoFVar_413_);
lean_inc(v_proofInstInfo_412_);
lean_inc(v_maxFVar_411_);
lean_inc(v_share_410_);
lean_dec(v___x_409_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_433_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_427_; lean_object* v___x_429_; 
lean_inc(v_a_408_);
v___x_427_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_411_, v_e_399_, v_a_408_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 1, v___x_427_);
v___x_429_ = v___x_425_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_share_410_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v___x_427_);
lean_ctor_set(v_reuseFailAlloc_432_, 2, v_proofInstInfo_412_);
lean_ctor_set(v_reuseFailAlloc_432_, 3, v_proofInstInfoFVar_413_);
lean_ctor_set(v_reuseFailAlloc_432_, 4, v_letValue_414_);
lean_ctor_set(v_reuseFailAlloc_432_, 5, v_inferType_415_);
lean_ctor_set(v_reuseFailAlloc_432_, 6, v_getLevel_416_);
lean_ctor_set(v_reuseFailAlloc_432_, 7, v_congrInfo_417_);
lean_ctor_set(v_reuseFailAlloc_432_, 8, v_defEqI_418_);
lean_ctor_set(v_reuseFailAlloc_432_, 9, v_extensions_419_);
lean_ctor_set(v_reuseFailAlloc_432_, 10, v_issues_420_);
lean_ctor_set(v_reuseFailAlloc_432_, 11, v_canon_421_);
lean_ctor_set(v_reuseFailAlloc_432_, 12, v_instanceOverrides_422_);
lean_ctor_set_uint8(v_reuseFailAlloc_432_, sizeof(void*)*13, v_debug_423_);
v___x_429_ = v_reuseFailAlloc_432_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = lean_st_ref_put(v_a_401_, v___x_429_);
v___x_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_431_, 0, v_a_408_);
return v___x_431_;
}
}
}
v___jp_434_:
{
lean_object* v___x_443_; lean_object* v_maxFVar_444_; lean_object* v___x_445_; 
v___x_443_ = lean_st_ref_get(v___y_435_);
v_maxFVar_444_ = lean_ctor_get(v___x_443_, 1);
lean_inc_ref(v_maxFVar_444_);
lean_dec(v___x_443_);
v___x_445_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_444_, v_e_399_);
lean_dec_ref(v_maxFVar_444_);
if (lean_obj_tag(v___x_445_) == 1)
{
lean_object* v_val_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
lean_dec_ref(v___y_437_);
lean_dec_ref(v___y_436_);
lean_dec_ref(v_e_399_);
v_val_446_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v___x_445_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_val_446_);
lean_dec(v___x_445_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
lean_ctor_set_tag(v___x_448_, 0);
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_val_446_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
else
{
lean_object* v___x_454_; 
lean_dec(v___x_445_);
v___x_454_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v___y_436_, v___y_439_, v___y_435_, v___y_442_, v___y_438_, v___y_440_, v___y_441_);
if (lean_obj_tag(v___x_454_) == 0)
{
lean_object* v_a_455_; lean_object* v___x_456_; 
v_a_455_ = lean_ctor_get(v___x_454_, 0);
lean_inc(v_a_455_);
lean_dec_ref_known(v___x_454_, 1);
v___x_456_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v___y_437_, v___y_439_, v___y_435_, v___y_442_, v___y_438_, v___y_440_, v___y_441_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; lean_object* v___x_458_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_a_457_);
lean_dec_ref_known(v___x_456_, 1);
v___x_458_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_455_, v_a_457_, v___y_442_, v___y_440_, v___y_441_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_490_; 
v_a_459_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_490_ == 0)
{
v___x_461_ = v___x_458_;
v_isShared_462_ = v_isSharedCheck_490_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_458_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_490_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_463_; lean_object* v_share_464_; lean_object* v_maxFVar_465_; lean_object* v_proofInstInfo_466_; lean_object* v_proofInstInfoFVar_467_; lean_object* v_letValue_468_; lean_object* v_inferType_469_; lean_object* v_getLevel_470_; lean_object* v_congrInfo_471_; lean_object* v_defEqI_472_; lean_object* v_extensions_473_; lean_object* v_issues_474_; lean_object* v_canon_475_; lean_object* v_instanceOverrides_476_; uint8_t v_debug_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_489_; 
v___x_463_ = lean_st_ref_take(v___y_435_);
v_share_464_ = lean_ctor_get(v___x_463_, 0);
v_maxFVar_465_ = lean_ctor_get(v___x_463_, 1);
v_proofInstInfo_466_ = lean_ctor_get(v___x_463_, 2);
v_proofInstInfoFVar_467_ = lean_ctor_get(v___x_463_, 3);
v_letValue_468_ = lean_ctor_get(v___x_463_, 4);
v_inferType_469_ = lean_ctor_get(v___x_463_, 5);
v_getLevel_470_ = lean_ctor_get(v___x_463_, 6);
v_congrInfo_471_ = lean_ctor_get(v___x_463_, 7);
v_defEqI_472_ = lean_ctor_get(v___x_463_, 8);
v_extensions_473_ = lean_ctor_get(v___x_463_, 9);
v_issues_474_ = lean_ctor_get(v___x_463_, 10);
v_canon_475_ = lean_ctor_get(v___x_463_, 11);
v_instanceOverrides_476_ = lean_ctor_get(v___x_463_, 12);
v_debug_477_ = lean_ctor_get_uint8(v___x_463_, sizeof(void*)*13);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_489_ == 0)
{
v___x_479_ = v___x_463_;
v_isShared_480_ = v_isSharedCheck_489_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_instanceOverrides_476_);
lean_inc(v_canon_475_);
lean_inc(v_issues_474_);
lean_inc(v_extensions_473_);
lean_inc(v_defEqI_472_);
lean_inc(v_congrInfo_471_);
lean_inc(v_getLevel_470_);
lean_inc(v_inferType_469_);
lean_inc(v_letValue_468_);
lean_inc(v_proofInstInfoFVar_467_);
lean_inc(v_proofInstInfo_466_);
lean_inc(v_maxFVar_465_);
lean_inc(v_share_464_);
lean_dec(v___x_463_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_489_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_481_; lean_object* v___x_483_; 
lean_inc(v_a_459_);
v___x_481_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_465_, v_e_399_, v_a_459_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 1, v___x_481_);
v___x_483_ = v___x_479_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_share_464_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v___x_481_);
lean_ctor_set(v_reuseFailAlloc_488_, 2, v_proofInstInfo_466_);
lean_ctor_set(v_reuseFailAlloc_488_, 3, v_proofInstInfoFVar_467_);
lean_ctor_set(v_reuseFailAlloc_488_, 4, v_letValue_468_);
lean_ctor_set(v_reuseFailAlloc_488_, 5, v_inferType_469_);
lean_ctor_set(v_reuseFailAlloc_488_, 6, v_getLevel_470_);
lean_ctor_set(v_reuseFailAlloc_488_, 7, v_congrInfo_471_);
lean_ctor_set(v_reuseFailAlloc_488_, 8, v_defEqI_472_);
lean_ctor_set(v_reuseFailAlloc_488_, 9, v_extensions_473_);
lean_ctor_set(v_reuseFailAlloc_488_, 10, v_issues_474_);
lean_ctor_set(v_reuseFailAlloc_488_, 11, v_canon_475_);
lean_ctor_set(v_reuseFailAlloc_488_, 12, v_instanceOverrides_476_);
lean_ctor_set_uint8(v_reuseFailAlloc_488_, sizeof(void*)*13, v_debug_477_);
v___x_483_ = v_reuseFailAlloc_488_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_484_ = lean_st_ref_put(v___y_435_, v___x_483_);
if (v_isShared_462_ == 0)
{
v___x_486_ = v___x_461_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_a_459_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_399_);
return v___x_458_;
}
}
else
{
lean_dec(v_a_455_);
lean_dec_ref(v_e_399_);
return v___x_456_;
}
}
else
{
lean_dec_ref(v___y_437_);
lean_dec_ref(v_e_399_);
return v___x_454_;
}
}
}
v___jp_491_:
{
uint8_t v___x_500_; 
v___x_500_ = l_Lean_Expr_hasFVar(v_e_399_);
if (v___x_500_ == 0)
{
uint8_t v___x_501_; 
v___x_501_ = l_Lean_Expr_hasMVar(v_e_399_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; lean_object* v___x_503_; 
lean_dec_ref(v_b_493_);
lean_dec_ref(v_d_492_);
lean_dec_ref(v_e_399_);
v___x_502_ = lean_box(0);
v___x_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
return v___x_503_;
}
else
{
v___y_435_ = v___y_495_;
v___y_436_ = v_d_492_;
v___y_437_ = v_b_493_;
v___y_438_ = v___y_497_;
v___y_439_ = v___y_494_;
v___y_440_ = v___y_498_;
v___y_441_ = v___y_499_;
v___y_442_ = v___y_496_;
goto v___jp_434_;
}
}
else
{
v___y_435_ = v___y_495_;
v___y_436_ = v_d_492_;
v___y_437_ = v_b_493_;
v___y_438_ = v___y_497_;
v___y_439_ = v___y_494_;
v___y_440_ = v___y_498_;
v___y_441_ = v___y_499_;
v___y_442_ = v___y_496_;
goto v___jp_434_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f___boxed(lean_object* v_e_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_e_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_);
lean_dec(v_a_778_);
lean_dec_ref(v_a_777_);
lean_dec(v_a_776_);
lean_dec_ref(v_a_775_);
lean_dec(v_a_774_);
lean_dec_ref(v_a_773_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0(lean_object* v_00_u03b2_781_, lean_object* v_x_782_, lean_object* v_x_783_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_x_782_, v_x_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___boxed(lean_object* v_00_u03b2_785_, lean_object* v_x_786_, lean_object* v_x_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0(v_00_u03b2_785_, v_x_786_, v_x_787_);
lean_dec_ref(v_x_787_);
lean_dec_ref(v_x_786_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1(lean_object* v_00_u03b2_789_, lean_object* v_x_790_, lean_object* v_x_791_, lean_object* v_x_792_){
_start:
{
lean_object* v___x_793_; 
v___x_793_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_x_790_, v_x_791_, v_x_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0(lean_object* v_00_u03b2_794_, lean_object* v_x_795_, size_t v_x_796_, lean_object* v_x_797_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_795_, v_x_796_, v_x_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_799_, lean_object* v_x_800_, lean_object* v_x_801_, lean_object* v_x_802_){
_start:
{
size_t v_x_5651__boxed_803_; lean_object* v_res_804_; 
v_x_5651__boxed_803_ = lean_unbox_usize(v_x_801_);
lean_dec(v_x_801_);
v_res_804_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0(v_00_u03b2_799_, v_x_800_, v_x_5651__boxed_803_, v_x_802_);
lean_dec_ref(v_x_802_);
lean_dec_ref(v_x_800_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2(lean_object* v_00_u03b2_805_, lean_object* v_x_806_, size_t v_x_807_, size_t v_x_808_, lean_object* v_x_809_, lean_object* v_x_810_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_806_, v_x_807_, v_x_808_, v_x_809_, v_x_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_812_, lean_object* v_x_813_, lean_object* v_x_814_, lean_object* v_x_815_, lean_object* v_x_816_, lean_object* v_x_817_){
_start:
{
size_t v_x_5662__boxed_818_; size_t v_x_5663__boxed_819_; lean_object* v_res_820_; 
v_x_5662__boxed_818_ = lean_unbox_usize(v_x_814_);
lean_dec(v_x_814_);
v_x_5663__boxed_819_ = lean_unbox_usize(v_x_815_);
lean_dec(v_x_815_);
v_res_820_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2(v_00_u03b2_812_, v_x_813_, v_x_5662__boxed_818_, v_x_5663__boxed_819_, v_x_816_, v_x_817_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_821_, lean_object* v_keys_822_, lean_object* v_vals_823_, lean_object* v_heq_824_, lean_object* v_i_825_, lean_object* v_k_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(v_keys_822_, v_vals_823_, v_i_825_, v_k_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_828_, lean_object* v_keys_829_, lean_object* v_vals_830_, lean_object* v_heq_831_, lean_object* v_i_832_, lean_object* v_k_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2(v_00_u03b2_828_, v_keys_829_, v_vals_830_, v_heq_831_, v_i_832_, v_k_833_);
lean_dec_ref(v_k_833_);
lean_dec_ref(v_vals_830_);
lean_dec_ref(v_keys_829_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_835_, lean_object* v_n_836_, lean_object* v_k_837_, lean_object* v_v_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__5___redArg(v_n_836_, v_k_837_, v_v_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_840_, size_t v_depth_841_, lean_object* v_keys_842_, lean_object* v_vals_843_, lean_object* v_heq_844_, lean_object* v_i_845_, lean_object* v_entries_846_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_depth_841_, v_keys_842_, v_vals_843_, v_i_845_, v_entries_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_848_, lean_object* v_depth_849_, lean_object* v_keys_850_, lean_object* v_vals_851_, lean_object* v_heq_852_, lean_object* v_i_853_, lean_object* v_entries_854_){
_start:
{
size_t v_depth_boxed_855_; lean_object* v_res_856_; 
v_depth_boxed_855_ = lean_unbox_usize(v_depth_849_);
lean_dec(v_depth_849_);
v_res_856_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6(v_00_u03b2_848_, v_depth_boxed_855_, v_keys_850_, v_vals_851_, v_heq_852_, v_i_853_, v_entries_854_);
lean_dec_ref(v_vals_851_);
lean_dec_ref(v_keys_850_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__5_spec__6(lean_object* v_00_u03b2_857_, lean_object* v_x_858_, lean_object* v_x_859_, lean_object* v_x_860_, lean_object* v_x_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__5_spec__6___redArg(v_x_858_, v_x_859_, v_x_860_, v_x_861_);
return v___x_862_;
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
