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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg();
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___f_87_; lean_object* v___f_88_; uint8_t v___y_90_; uint8_t v___x_136_; 
v___f_87_ = ((lean_object*)(l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__0));
v___f_88_ = ((lean_object*)(l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__1));
v___x_136_ = l_Lean_Expr_hasFVar(v_e_78_);
if (v___x_136_ == 0)
{
uint8_t v___x_137_; 
v___x_137_ = l_Lean_Expr_hasMVar(v_e_78_);
v___y_90_ = v___x_137_;
goto v___jp_89_;
}
else
{
v___y_90_ = v___x_136_;
goto v___jp_89_;
}
v___jp_89_:
{
if (v___y_90_ == 0)
{
lean_object* v___x_91_; lean_object* v___x_92_; 
lean_dec_ref(v_k_79_);
lean_dec_ref(v_e_78_);
v___x_91_ = lean_box(0);
v___x_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
return v___x_92_;
}
else
{
lean_object* v___x_93_; lean_object* v_maxFVar_94_; lean_object* v___x_95_; 
v___x_93_ = lean_st_ref_get(v_a_81_);
v_maxFVar_94_ = lean_ctor_get(v___x_93_, 1);
lean_inc_ref(v_maxFVar_94_);
lean_dec(v___x_93_);
lean_inc_ref(v_e_78_);
v___x_95_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_87_, v___f_88_, v_maxFVar_94_, v_e_78_);
lean_dec_ref(v_maxFVar_94_);
if (lean_obj_tag(v___x_95_) == 1)
{
lean_object* v_val_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_103_; 
lean_dec_ref(v_k_79_);
lean_dec_ref(v_e_78_);
v_val_96_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_103_ == 0)
{
v___x_98_ = v___x_95_;
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_val_96_);
lean_dec(v___x_95_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_101_; 
if (v_isShared_99_ == 0)
{
lean_ctor_set_tag(v___x_98_, 0);
v___x_101_ = v___x_98_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_val_96_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
else
{
lean_object* v___x_104_; 
lean_dec(v___x_95_);
lean_inc(v_a_85_);
lean_inc_ref(v_a_84_);
lean_inc(v_a_83_);
lean_inc_ref(v_a_82_);
lean_inc(v_a_81_);
lean_inc_ref(v_a_80_);
v___x_104_ = lean_apply_7(v_k_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_, lean_box(0));
if (lean_obj_tag(v___x_104_) == 0)
{
lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_135_; 
v_a_105_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_135_ == 0)
{
v___x_107_ = v___x_104_;
v_isShared_108_ = v_isSharedCheck_135_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_dec(v___x_104_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_135_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_109_; lean_object* v_share_110_; lean_object* v_maxFVar_111_; lean_object* v_proofInstInfo_112_; lean_object* v_proofInstInfoFVar_113_; lean_object* v_inferType_114_; lean_object* v_getLevel_115_; lean_object* v_congrInfo_116_; lean_object* v_defEqI_117_; lean_object* v_extensions_118_; lean_object* v_issues_119_; lean_object* v_canon_120_; lean_object* v_instanceOverrides_121_; uint8_t v_debug_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_134_; 
v___x_109_ = lean_st_ref_take(v_a_81_);
v_share_110_ = lean_ctor_get(v___x_109_, 0);
v_maxFVar_111_ = lean_ctor_get(v___x_109_, 1);
v_proofInstInfo_112_ = lean_ctor_get(v___x_109_, 2);
v_proofInstInfoFVar_113_ = lean_ctor_get(v___x_109_, 3);
v_inferType_114_ = lean_ctor_get(v___x_109_, 4);
v_getLevel_115_ = lean_ctor_get(v___x_109_, 5);
v_congrInfo_116_ = lean_ctor_get(v___x_109_, 6);
v_defEqI_117_ = lean_ctor_get(v___x_109_, 7);
v_extensions_118_ = lean_ctor_get(v___x_109_, 8);
v_issues_119_ = lean_ctor_get(v___x_109_, 9);
v_canon_120_ = lean_ctor_get(v___x_109_, 10);
v_instanceOverrides_121_ = lean_ctor_get(v___x_109_, 11);
v_debug_122_ = lean_ctor_get_uint8(v___x_109_, sizeof(void*)*12);
v_isSharedCheck_134_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_134_ == 0)
{
v___x_124_ = v___x_109_;
v_isShared_125_ = v_isSharedCheck_134_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_instanceOverrides_121_);
lean_inc(v_canon_120_);
lean_inc(v_issues_119_);
lean_inc(v_extensions_118_);
lean_inc(v_defEqI_117_);
lean_inc(v_congrInfo_116_);
lean_inc(v_getLevel_115_);
lean_inc(v_inferType_114_);
lean_inc(v_proofInstInfoFVar_113_);
lean_inc(v_proofInstInfo_112_);
lean_inc(v_maxFVar_111_);
lean_inc(v_share_110_);
lean_dec(v___x_109_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_134_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_126_; lean_object* v___x_128_; 
lean_inc(v_a_105_);
v___x_126_ = l_Lean_PersistentHashMap_insert___redArg(v___f_87_, v___f_88_, v_maxFVar_111_, v_e_78_, v_a_105_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 1, v___x_126_);
v___x_128_ = v___x_124_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_share_110_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v___x_126_);
lean_ctor_set(v_reuseFailAlloc_133_, 2, v_proofInstInfo_112_);
lean_ctor_set(v_reuseFailAlloc_133_, 3, v_proofInstInfoFVar_113_);
lean_ctor_set(v_reuseFailAlloc_133_, 4, v_inferType_114_);
lean_ctor_set(v_reuseFailAlloc_133_, 5, v_getLevel_115_);
lean_ctor_set(v_reuseFailAlloc_133_, 6, v_congrInfo_116_);
lean_ctor_set(v_reuseFailAlloc_133_, 7, v_defEqI_117_);
lean_ctor_set(v_reuseFailAlloc_133_, 8, v_extensions_118_);
lean_ctor_set(v_reuseFailAlloc_133_, 9, v_issues_119_);
lean_ctor_set(v_reuseFailAlloc_133_, 10, v_canon_120_);
lean_ctor_set(v_reuseFailAlloc_133_, 11, v_instanceOverrides_121_);
lean_ctor_set_uint8(v_reuseFailAlloc_133_, sizeof(void*)*12, v_debug_122_);
v___x_128_ = v_reuseFailAlloc_133_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
lean_object* v___x_129_; lean_object* v___x_131_; 
v___x_129_ = lean_st_ref_put(v_a_81_, v___x_128_);
if (v_isShared_108_ == 0)
{
v___x_131_ = v___x_107_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_a_105_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_78_);
return v___x_104_;
}
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
lean_object* v___x_157_; lean_object* v___x_4122__overap_158_; lean_object* v___x_159_; 
v___x_157_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0, &l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0);
v___x_4122__overap_158_ = lean_panic_fn_borrowed(v___x_157_, v_msg_149_);
lean_inc(v___y_155_);
lean_inc_ref(v___y_154_);
lean_inc(v___y_153_);
lean_inc_ref(v___y_152_);
lean_inc(v___y_151_);
lean_inc_ref(v___y_150_);
v___x_159_ = lean_apply_7(v___x_4122__overap_158_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, lean_box(0));
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_169_, lean_object* v_x_170_, lean_object* v_x_171_, lean_object* v_x_172_){
_start:
{
lean_object* v_ks_173_; lean_object* v_vs_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_200_; 
v_ks_173_ = lean_ctor_get(v_x_169_, 0);
v_vs_174_ = lean_ctor_get(v_x_169_, 1);
v_isSharedCheck_200_ = !lean_is_exclusive(v_x_169_);
if (v_isSharedCheck_200_ == 0)
{
v___x_176_ = v_x_169_;
v_isShared_177_ = v_isSharedCheck_200_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_vs_174_);
lean_inc(v_ks_173_);
lean_dec(v_x_169_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_200_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_178_; uint8_t v___x_179_; 
v___x_178_ = lean_array_get_size(v_ks_173_);
v___x_179_ = lean_nat_dec_lt(v_x_170_, v___x_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_183_; 
lean_dec(v_x_170_);
v___x_180_ = lean_array_push(v_ks_173_, v_x_171_);
v___x_181_ = lean_array_push(v_vs_174_, v_x_172_);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 1, v___x_181_);
lean_ctor_set(v___x_176_, 0, v___x_180_);
v___x_183_ = v___x_176_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_180_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v___x_181_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
else
{
lean_object* v_k_x27_185_; size_t v___x_186_; size_t v___x_187_; uint8_t v___x_188_; 
v_k_x27_185_ = lean_array_fget_borrowed(v_ks_173_, v_x_170_);
v___x_186_ = lean_ptr_addr(v_x_171_);
v___x_187_ = lean_ptr_addr(v_k_x27_185_);
v___x_188_ = lean_usize_dec_eq(v___x_186_, v___x_187_);
if (v___x_188_ == 0)
{
lean_object* v___x_190_; 
if (v_isShared_177_ == 0)
{
v___x_190_ = v___x_176_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_ks_173_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v_vs_174_);
v___x_190_ = v_reuseFailAlloc_194_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = lean_unsigned_to_nat(1u);
v___x_192_ = lean_nat_add(v_x_170_, v___x_191_);
lean_dec(v_x_170_);
v_x_169_ = v___x_190_;
v_x_170_ = v___x_192_;
goto _start;
}
}
else
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_198_; 
v___x_195_ = lean_array_fset(v_ks_173_, v_x_170_, v_x_171_);
v___x_196_ = lean_array_fset(v_vs_174_, v_x_170_, v_x_172_);
lean_dec(v_x_170_);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 1, v___x_196_);
lean_ctor_set(v___x_176_, 0, v___x_195_);
v___x_198_ = v___x_176_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_195_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v___x_196_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(lean_object* v_n_201_, lean_object* v_k_202_, lean_object* v_v_203_){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = lean_unsigned_to_nat(0u);
v___x_205_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_n_201_, v___x_204_, v_k_202_, v_v_203_);
return v___x_205_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(lean_object* v_x_207_, size_t v_x_208_, size_t v_x_209_, lean_object* v_x_210_, lean_object* v_x_211_){
_start:
{
if (lean_obj_tag(v_x_207_) == 0)
{
lean_object* v_es_212_; size_t v___x_213_; size_t v___x_214_; lean_object* v_j_215_; lean_object* v___x_216_; uint8_t v___x_217_; 
v_es_212_ = lean_ctor_get(v_x_207_, 0);
v___x_213_ = ((size_t)31ULL);
v___x_214_ = lean_usize_land(v_x_208_, v___x_213_);
v_j_215_ = lean_usize_to_nat(v___x_214_);
v___x_216_ = lean_array_get_size(v_es_212_);
v___x_217_ = lean_nat_dec_lt(v_j_215_, v___x_216_);
if (v___x_217_ == 0)
{
lean_dec(v_j_215_);
lean_dec(v_x_211_);
lean_dec_ref(v_x_210_);
return v_x_207_;
}
else
{
lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_258_; 
lean_inc_ref(v_es_212_);
v_isSharedCheck_258_ = !lean_is_exclusive(v_x_207_);
if (v_isSharedCheck_258_ == 0)
{
lean_object* v_unused_259_; 
v_unused_259_ = lean_ctor_get(v_x_207_, 0);
lean_dec(v_unused_259_);
v___x_219_ = v_x_207_;
v_isShared_220_ = v_isSharedCheck_258_;
goto v_resetjp_218_;
}
else
{
lean_dec(v_x_207_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_258_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v_v_221_; lean_object* v___x_222_; lean_object* v_xs_x27_223_; lean_object* v___y_225_; 
v_v_221_ = lean_array_fget(v_es_212_, v_j_215_);
v___x_222_ = lean_box(0);
v_xs_x27_223_ = lean_array_fset(v_es_212_, v_j_215_, v___x_222_);
switch(lean_obj_tag(v_v_221_))
{
case 0:
{
lean_object* v_key_230_; lean_object* v_val_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_243_; 
v_key_230_ = lean_ctor_get(v_v_221_, 0);
v_val_231_ = lean_ctor_get(v_v_221_, 1);
v_isSharedCheck_243_ = !lean_is_exclusive(v_v_221_);
if (v_isSharedCheck_243_ == 0)
{
v___x_233_ = v_v_221_;
v_isShared_234_ = v_isSharedCheck_243_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_val_231_);
lean_inc(v_key_230_);
lean_dec(v_v_221_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_243_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
size_t v___x_235_; size_t v___x_236_; uint8_t v___x_237_; 
v___x_235_ = lean_ptr_addr(v_x_210_);
v___x_236_ = lean_ptr_addr(v_key_230_);
v___x_237_ = lean_usize_dec_eq(v___x_235_, v___x_236_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; lean_object* v___x_239_; 
lean_del_object(v___x_233_);
v___x_238_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_230_, v_val_231_, v_x_210_, v_x_211_);
v___x_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
v___y_225_ = v___x_239_;
goto v___jp_224_;
}
else
{
lean_object* v___x_241_; 
lean_dec(v_val_231_);
lean_dec(v_key_230_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 1, v_x_211_);
lean_ctor_set(v___x_233_, 0, v_x_210_);
v___x_241_ = v___x_233_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_x_210_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_x_211_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
v___y_225_ = v___x_241_;
goto v___jp_224_;
}
}
}
}
case 1:
{
lean_object* v_node_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_256_; 
v_node_244_ = lean_ctor_get(v_v_221_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v_v_221_);
if (v_isSharedCheck_256_ == 0)
{
v___x_246_ = v_v_221_;
v_isShared_247_ = v_isSharedCheck_256_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_node_244_);
lean_dec(v_v_221_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_256_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
size_t v___x_248_; size_t v___x_249_; size_t v___x_250_; size_t v___x_251_; lean_object* v___x_252_; lean_object* v___x_254_; 
v___x_248_ = ((size_t)5ULL);
v___x_249_ = lean_usize_shift_right(v_x_208_, v___x_248_);
v___x_250_ = ((size_t)1ULL);
v___x_251_ = lean_usize_add(v_x_209_, v___x_250_);
v___x_252_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_node_244_, v___x_249_, v___x_251_, v_x_210_, v_x_211_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 0, v___x_252_);
v___x_254_ = v___x_246_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_252_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
v___y_225_ = v___x_254_;
goto v___jp_224_;
}
}
}
default: 
{
lean_object* v___x_257_; 
v___x_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_257_, 0, v_x_210_);
lean_ctor_set(v___x_257_, 1, v_x_211_);
v___y_225_ = v___x_257_;
goto v___jp_224_;
}
}
v___jp_224_:
{
lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_226_ = lean_array_fset(v_xs_x27_223_, v_j_215_, v___y_225_);
lean_dec(v_j_215_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 0, v___x_226_);
v___x_228_ = v___x_219_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_226_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
}
}
else
{
lean_object* v_ks_260_; lean_object* v_vs_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_279_; 
v_ks_260_ = lean_ctor_get(v_x_207_, 0);
v_vs_261_ = lean_ctor_get(v_x_207_, 1);
v_isSharedCheck_279_ = !lean_is_exclusive(v_x_207_);
if (v_isSharedCheck_279_ == 0)
{
v___x_263_ = v_x_207_;
v_isShared_264_ = v_isSharedCheck_279_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_vs_261_);
lean_inc(v_ks_260_);
lean_dec(v_x_207_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_279_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_ks_260_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v_vs_261_);
v___x_266_ = v_reuseFailAlloc_278_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
lean_object* v_newNode_267_; size_t v___x_268_; uint8_t v___x_269_; 
v_newNode_267_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(v___x_266_, v_x_210_, v_x_211_);
v___x_268_ = ((size_t)7ULL);
v___x_269_ = lean_usize_dec_le(v___x_268_, v_x_209_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_270_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_267_);
v___x_271_ = lean_unsigned_to_nat(4u);
v___x_272_ = lean_nat_dec_lt(v___x_270_, v___x_271_);
lean_dec(v___x_270_);
if (v___x_272_ == 0)
{
lean_object* v_ks_273_; lean_object* v_vs_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v_ks_273_ = lean_ctor_get(v_newNode_267_, 0);
lean_inc_ref(v_ks_273_);
v_vs_274_ = lean_ctor_get(v_newNode_267_, 1);
lean_inc_ref(v_vs_274_);
lean_dec_ref(v_newNode_267_);
v___x_275_ = lean_unsigned_to_nat(0u);
v___x_276_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0);
v___x_277_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(v_x_209_, v_ks_273_, v_vs_274_, v___x_275_, v___x_276_);
lean_dec_ref(v_vs_274_);
lean_dec_ref(v_ks_273_);
return v___x_277_;
}
else
{
return v_newNode_267_;
}
}
else
{
return v_newNode_267_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(size_t v_depth_280_, lean_object* v_keys_281_, lean_object* v_vals_282_, lean_object* v_i_283_, lean_object* v_entries_284_){
_start:
{
lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_285_ = lean_array_get_size(v_keys_281_);
v___x_286_ = lean_nat_dec_lt(v_i_283_, v___x_285_);
if (v___x_286_ == 0)
{
lean_dec(v_i_283_);
return v_entries_284_;
}
else
{
lean_object* v_k_287_; lean_object* v_v_288_; size_t v___x_289_; size_t v___x_290_; size_t v___x_291_; uint64_t v___x_292_; size_t v_h_293_; size_t v___x_294_; lean_object* v___x_295_; size_t v___x_296_; size_t v___x_297_; size_t v___x_298_; size_t v_h_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v_k_287_ = lean_array_fget_borrowed(v_keys_281_, v_i_283_);
v_v_288_ = lean_array_fget_borrowed(v_vals_282_, v_i_283_);
v___x_289_ = lean_ptr_addr(v_k_287_);
v___x_290_ = ((size_t)3ULL);
v___x_291_ = lean_usize_shift_right(v___x_289_, v___x_290_);
v___x_292_ = lean_usize_to_uint64(v___x_291_);
v_h_293_ = lean_uint64_to_usize(v___x_292_);
v___x_294_ = ((size_t)5ULL);
v___x_295_ = lean_unsigned_to_nat(1u);
v___x_296_ = ((size_t)1ULL);
v___x_297_ = lean_usize_sub(v_depth_280_, v___x_296_);
v___x_298_ = lean_usize_mul(v___x_294_, v___x_297_);
v_h_299_ = lean_usize_shift_right(v_h_293_, v___x_298_);
v___x_300_ = lean_nat_add(v_i_283_, v___x_295_);
lean_dec(v_i_283_);
lean_inc(v_v_288_);
lean_inc(v_k_287_);
v___x_301_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_entries_284_, v_h_299_, v_depth_280_, v_k_287_, v_v_288_);
v_i_283_ = v___x_300_;
v_entries_284_ = v___x_301_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_303_, lean_object* v_keys_304_, lean_object* v_vals_305_, lean_object* v_i_306_, lean_object* v_entries_307_){
_start:
{
size_t v_depth_boxed_308_; lean_object* v_res_309_; 
v_depth_boxed_308_ = lean_unbox_usize(v_depth_303_);
lean_dec(v_depth_303_);
v_res_309_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(v_depth_boxed_308_, v_keys_304_, v_vals_305_, v_i_306_, v_entries_307_);
lean_dec_ref(v_vals_305_);
lean_dec_ref(v_keys_304_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_310_, lean_object* v_x_311_, lean_object* v_x_312_, lean_object* v_x_313_, lean_object* v_x_314_){
_start:
{
size_t v_x_4677__boxed_315_; size_t v_x_4678__boxed_316_; lean_object* v_res_317_; 
v_x_4677__boxed_315_ = lean_unbox_usize(v_x_311_);
lean_dec(v_x_311_);
v_x_4678__boxed_316_ = lean_unbox_usize(v_x_312_);
lean_dec(v_x_312_);
v_res_317_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_310_, v_x_4677__boxed_315_, v_x_4678__boxed_316_, v_x_313_, v_x_314_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(lean_object* v_x_318_, lean_object* v_x_319_, lean_object* v_x_320_){
_start:
{
size_t v___x_321_; size_t v___x_322_; size_t v___x_323_; uint64_t v___x_324_; size_t v___x_325_; size_t v___x_326_; lean_object* v___x_327_; 
v___x_321_ = lean_ptr_addr(v_x_319_);
v___x_322_ = ((size_t)3ULL);
v___x_323_ = lean_usize_shift_right(v___x_321_, v___x_322_);
v___x_324_ = lean_usize_to_uint64(v___x_323_);
v___x_325_ = lean_uint64_to_usize(v___x_324_);
v___x_326_ = ((size_t)1ULL);
v___x_327_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_318_, v___x_325_, v___x_326_, v_x_319_, v_x_320_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(lean_object* v_keys_328_, lean_object* v_vals_329_, lean_object* v_i_330_, lean_object* v_k_331_){
_start:
{
lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_332_ = lean_array_get_size(v_keys_328_);
v___x_333_ = lean_nat_dec_lt(v_i_330_, v___x_332_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; 
lean_dec(v_i_330_);
v___x_334_ = lean_box(0);
return v___x_334_;
}
else
{
lean_object* v_k_x27_335_; size_t v___x_336_; size_t v___x_337_; uint8_t v___x_338_; 
v_k_x27_335_ = lean_array_fget_borrowed(v_keys_328_, v_i_330_);
v___x_336_ = lean_ptr_addr(v_k_331_);
v___x_337_ = lean_ptr_addr(v_k_x27_335_);
v___x_338_ = lean_usize_dec_eq(v___x_336_, v___x_337_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_unsigned_to_nat(1u);
v___x_340_ = lean_nat_add(v_i_330_, v___x_339_);
lean_dec(v_i_330_);
v_i_330_ = v___x_340_;
goto _start;
}
else
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = lean_array_fget_borrowed(v_vals_329_, v_i_330_);
lean_dec(v_i_330_);
lean_inc(v___x_342_);
v___x_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
return v___x_343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_keys_344_, lean_object* v_vals_345_, lean_object* v_i_346_, lean_object* v_k_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_keys_344_, v_vals_345_, v_i_346_, v_k_347_);
lean_dec_ref(v_k_347_);
lean_dec_ref(v_vals_345_);
lean_dec_ref(v_keys_344_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(lean_object* v_x_349_, size_t v_x_350_, lean_object* v_x_351_){
_start:
{
if (lean_obj_tag(v_x_349_) == 0)
{
lean_object* v_es_352_; lean_object* v___x_353_; size_t v___x_354_; size_t v___x_355_; lean_object* v_j_356_; lean_object* v___x_357_; 
v_es_352_ = lean_ctor_get(v_x_349_, 0);
v___x_353_ = lean_box(2);
v___x_354_ = ((size_t)31ULL);
v___x_355_ = lean_usize_land(v_x_350_, v___x_354_);
v_j_356_ = lean_usize_to_nat(v___x_355_);
v___x_357_ = lean_array_get_borrowed(v___x_353_, v_es_352_, v_j_356_);
lean_dec(v_j_356_);
switch(lean_obj_tag(v___x_357_))
{
case 0:
{
lean_object* v_key_358_; lean_object* v_val_359_; size_t v___x_360_; size_t v___x_361_; uint8_t v___x_362_; 
v_key_358_ = lean_ctor_get(v___x_357_, 0);
v_val_359_ = lean_ctor_get(v___x_357_, 1);
v___x_360_ = lean_ptr_addr(v_x_351_);
v___x_361_ = lean_ptr_addr(v_key_358_);
v___x_362_ = lean_usize_dec_eq(v___x_360_, v___x_361_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; 
v___x_363_ = lean_box(0);
return v___x_363_;
}
else
{
lean_object* v___x_364_; 
lean_inc(v_val_359_);
v___x_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_364_, 0, v_val_359_);
return v___x_364_;
}
}
case 1:
{
lean_object* v_node_365_; size_t v___x_366_; size_t v___x_367_; 
v_node_365_ = lean_ctor_get(v___x_357_, 0);
v___x_366_ = ((size_t)5ULL);
v___x_367_ = lean_usize_shift_right(v_x_350_, v___x_366_);
v_x_349_ = v_node_365_;
v_x_350_ = v___x_367_;
goto _start;
}
default: 
{
lean_object* v___x_369_; 
v___x_369_ = lean_box(0);
return v___x_369_;
}
}
}
else
{
lean_object* v_ks_370_; lean_object* v_vs_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v_ks_370_ = lean_ctor_get(v_x_349_, 0);
v_vs_371_ = lean_ctor_get(v_x_349_, 1);
v___x_372_ = lean_unsigned_to_nat(0u);
v___x_373_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_ks_370_, v_vs_371_, v___x_372_, v_x_351_);
return v___x_373_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_x_374_, lean_object* v_x_375_, lean_object* v_x_376_){
_start:
{
size_t v_x_4878__boxed_377_; lean_object* v_res_378_; 
v_x_4878__boxed_377_ = lean_unbox_usize(v_x_375_);
lean_dec(v_x_375_);
v_res_378_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_374_, v_x_4878__boxed_377_, v_x_376_);
lean_dec_ref(v_x_376_);
lean_dec_ref(v_x_374_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(lean_object* v_x_379_, lean_object* v_x_380_){
_start:
{
size_t v___x_381_; size_t v___x_382_; size_t v___x_383_; uint64_t v___x_384_; size_t v___x_385_; lean_object* v___x_386_; 
v___x_381_ = lean_ptr_addr(v_x_380_);
v___x_382_ = ((size_t)3ULL);
v___x_383_ = lean_usize_shift_right(v___x_381_, v___x_382_);
v___x_384_ = lean_usize_to_uint64(v___x_383_);
v___x_385_ = lean_uint64_to_usize(v___x_384_);
v___x_386_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_379_, v___x_385_, v_x_380_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg___boxed(lean_object* v_x_387_, lean_object* v_x_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_x_387_, v_x_388_);
lean_dec_ref(v_x_388_);
lean_dec_ref(v_x_387_);
return v_res_389_;
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
lean_object* v___y_408_; lean_object* v_a_441_; lean_object* v___y_467_; lean_object* v___y_468_; lean_object* v___y_501_; lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v___y_504_; lean_object* v___y_505_; lean_object* v___y_506_; lean_object* v___y_507_; lean_object* v___y_508_; uint8_t v___y_509_; lean_object* v_d_529_; lean_object* v_b_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_540_; 
switch(lean_obj_tag(v_e_399_))
{
case 1:
{
lean_object* v_fvarId_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v_fvarId_572_ = lean_ctor_get(v_e_399_, 0);
lean_inc(v_fvarId_572_);
lean_dec_ref_known(v_e_399_, 1);
v___x_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_573_, 0, v_fvarId_572_);
v___x_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
return v___x_574_;
}
case 2:
{
lean_object* v_mvarId_575_; uint8_t v___y_577_; uint8_t v___x_618_; 
v_mvarId_575_ = lean_ctor_get(v_e_399_, 0);
v___x_618_ = l_Lean_Expr_hasFVar(v_e_399_);
if (v___x_618_ == 0)
{
uint8_t v___x_619_; 
v___x_619_ = l_Lean_Expr_hasMVar(v_e_399_);
v___y_577_ = v___x_619_;
goto v___jp_576_;
}
else
{
v___y_577_ = v___x_618_;
goto v___jp_576_;
}
v___jp_576_:
{
if (v___y_577_ == 0)
{
lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec_ref_known(v_e_399_, 1);
v___x_578_ = lean_box(0);
v___x_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
return v___x_579_;
}
else
{
lean_object* v___x_580_; lean_object* v_maxFVar_581_; lean_object* v___x_582_; 
v___x_580_ = lean_st_ref_get(v_a_401_);
v_maxFVar_581_ = lean_ctor_get(v___x_580_, 1);
lean_inc_ref(v_maxFVar_581_);
lean_dec(v___x_580_);
v___x_582_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_581_, v_e_399_);
lean_dec_ref(v_maxFVar_581_);
if (lean_obj_tag(v___x_582_) == 1)
{
lean_object* v_val_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
lean_dec_ref_known(v_e_399_, 1);
v_val_583_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_582_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_val_583_);
lean_dec(v___x_582_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
lean_ctor_set_tag(v___x_585_, 0);
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_val_583_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
else
{
lean_object* v___x_591_; 
lean_dec(v___x_582_);
lean_inc(v_mvarId_575_);
v___x_591_ = l_Lean_MVarId_getDecl(v_mvarId_575_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; lean_object* v_lctx_593_; lean_object* v_decls_594_; uint8_t v___x_595_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
lean_inc(v_a_592_);
lean_dec_ref_known(v___x_591_, 1);
v_lctx_593_ = lean_ctor_get(v_a_592_, 1);
lean_inc_ref(v_lctx_593_);
lean_dec(v_a_592_);
v_decls_594_ = lean_ctor_get(v_lctx_593_, 1);
v___x_595_ = l_Lean_PersistentArray_isEmpty___redArg(v_decls_594_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; 
v___x_596_ = l_Lean_LocalContext_lastDecl(v_lctx_593_);
lean_dec_ref(v_lctx_593_);
if (lean_obj_tag(v___x_596_) == 1)
{
lean_object* v_val_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_605_; 
v_val_597_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_605_ == 0)
{
v___x_599_ = v___x_596_;
v_isShared_600_ = v_isSharedCheck_605_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_val_597_);
lean_dec(v___x_596_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_605_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_601_; lean_object* v___x_603_; 
v___x_601_ = l_Lean_LocalDecl_fvarId(v_val_597_);
lean_dec(v_val_597_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v___x_601_);
v___x_603_ = v___x_599_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_601_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
v_a_441_ = v___x_603_;
goto v___jp_440_;
}
}
}
else
{
lean_object* v___x_606_; lean_object* v___x_607_; 
lean_dec(v___x_596_);
v___x_606_ = lean_obj_once(&l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3, &l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3_once, _init_l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3);
v___x_607_ = l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2(v___x_606_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_a_608_);
lean_dec_ref_known(v___x_607_, 1);
v_a_441_ = v_a_608_;
goto v___jp_440_;
}
else
{
lean_dec_ref_known(v_e_399_, 1);
return v___x_607_;
}
}
}
else
{
lean_object* v___x_609_; 
lean_dec_ref(v_lctx_593_);
v___x_609_ = lean_box(0);
v_a_441_ = v___x_609_;
goto v___jp_440_;
}
}
else
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
lean_dec_ref_known(v_e_399_, 1);
v_a_610_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_617_ == 0)
{
v___x_612_ = v___x_591_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_591_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_610_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
}
}
}
case 5:
{
lean_object* v_fn_620_; lean_object* v_arg_621_; uint8_t v___y_623_; uint8_t v___x_642_; 
v_fn_620_ = lean_ctor_get(v_e_399_, 0);
v_arg_621_ = lean_ctor_get(v_e_399_, 1);
v___x_642_ = l_Lean_Expr_hasFVar(v_e_399_);
if (v___x_642_ == 0)
{
uint8_t v___x_643_; 
v___x_643_ = l_Lean_Expr_hasMVar(v_e_399_);
v___y_623_ = v___x_643_;
goto v___jp_622_;
}
else
{
v___y_623_ = v___x_642_;
goto v___jp_622_;
}
v___jp_622_:
{
if (v___y_623_ == 0)
{
lean_object* v___x_624_; lean_object* v___x_625_; 
lean_dec_ref_known(v_e_399_, 2);
v___x_624_ = lean_box(0);
v___x_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
return v___x_625_;
}
else
{
lean_object* v___x_626_; lean_object* v_maxFVar_627_; lean_object* v___x_628_; 
v___x_626_ = lean_st_ref_get(v_a_401_);
v_maxFVar_627_ = lean_ctor_get(v___x_626_, 1);
lean_inc_ref(v_maxFVar_627_);
lean_dec(v___x_626_);
v___x_628_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_627_, v_e_399_);
lean_dec_ref(v_maxFVar_627_);
if (lean_obj_tag(v___x_628_) == 1)
{
lean_object* v_val_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_636_; 
lean_dec_ref_known(v_e_399_, 2);
v_val_629_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_636_ == 0)
{
v___x_631_ = v___x_628_;
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_val_629_);
lean_dec(v___x_628_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_634_; 
if (v_isShared_632_ == 0)
{
lean_ctor_set_tag(v___x_631_, 0);
v___x_634_ = v___x_631_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_val_629_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
else
{
lean_object* v___x_637_; 
lean_dec(v___x_628_);
lean_inc_ref(v_fn_620_);
v___x_637_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_fn_620_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_638_; lean_object* v___x_639_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_a_638_);
lean_dec_ref_known(v___x_637_, 1);
lean_inc_ref(v_arg_621_);
v___x_639_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_arg_621_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_641_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_a_640_);
lean_dec_ref_known(v___x_639_, 1);
v___x_641_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_638_, v_a_640_, v_a_402_, v_a_404_, v_a_405_);
v___y_540_ = v___x_641_;
goto v___jp_539_;
}
else
{
lean_dec(v_a_638_);
v___y_540_ = v___x_639_;
goto v___jp_539_;
}
}
else
{
v___y_540_ = v___x_637_;
goto v___jp_539_;
}
}
}
}
}
case 6:
{
lean_object* v_binderType_644_; lean_object* v_body_645_; 
v_binderType_644_ = lean_ctor_get(v_e_399_, 1);
v_body_645_ = lean_ctor_get(v_e_399_, 2);
lean_inc_ref(v_body_645_);
lean_inc_ref(v_binderType_644_);
v_d_529_ = v_binderType_644_;
v_b_530_ = v_body_645_;
v___y_531_ = v_a_400_;
v___y_532_ = v_a_401_;
v___y_533_ = v_a_402_;
v___y_534_ = v_a_403_;
v___y_535_ = v_a_404_;
v___y_536_ = v_a_405_;
goto v___jp_528_;
}
case 7:
{
lean_object* v_binderType_646_; lean_object* v_body_647_; 
v_binderType_646_ = lean_ctor_get(v_e_399_, 1);
v_body_647_ = lean_ctor_get(v_e_399_, 2);
lean_inc_ref(v_body_647_);
lean_inc_ref(v_binderType_646_);
v_d_529_ = v_binderType_646_;
v_b_530_ = v_body_647_;
v___y_531_ = v_a_400_;
v___y_532_ = v_a_401_;
v___y_533_ = v_a_402_;
v___y_534_ = v_a_403_;
v___y_535_ = v_a_404_;
v___y_536_ = v_a_405_;
goto v___jp_528_;
}
case 8:
{
lean_object* v_type_648_; lean_object* v_value_649_; lean_object* v_body_650_; uint8_t v___y_652_; uint8_t v___x_675_; 
v_type_648_ = lean_ctor_get(v_e_399_, 1);
v_value_649_ = lean_ctor_get(v_e_399_, 2);
v_body_650_ = lean_ctor_get(v_e_399_, 3);
v___x_675_ = l_Lean_Expr_hasFVar(v_e_399_);
if (v___x_675_ == 0)
{
uint8_t v___x_676_; 
v___x_676_ = l_Lean_Expr_hasMVar(v_e_399_);
v___y_652_ = v___x_676_;
goto v___jp_651_;
}
else
{
v___y_652_ = v___x_675_;
goto v___jp_651_;
}
v___jp_651_:
{
if (v___y_652_ == 0)
{
lean_object* v___x_653_; lean_object* v___x_654_; 
lean_dec_ref_known(v_e_399_, 4);
v___x_653_ = lean_box(0);
v___x_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
return v___x_654_;
}
else
{
lean_object* v___x_655_; lean_object* v_maxFVar_656_; lean_object* v___x_657_; 
v___x_655_ = lean_st_ref_get(v_a_401_);
v_maxFVar_656_ = lean_ctor_get(v___x_655_, 1);
lean_inc_ref(v_maxFVar_656_);
lean_dec(v___x_655_);
v___x_657_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_656_, v_e_399_);
lean_dec_ref(v_maxFVar_656_);
if (lean_obj_tag(v___x_657_) == 1)
{
lean_object* v_val_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
lean_dec_ref_known(v_e_399_, 4);
v_val_658_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_657_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_val_658_);
lean_dec(v___x_657_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
lean_ctor_set_tag(v___x_660_, 0);
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_val_658_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
else
{
lean_object* v___x_666_; 
lean_dec(v___x_657_);
lean_inc_ref(v_type_648_);
v___x_666_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_type_648_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; lean_object* v___x_668_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_a_667_);
lean_dec_ref_known(v___x_666_, 1);
lean_inc_ref(v_value_649_);
v___x_668_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_value_649_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; lean_object* v___x_670_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_669_);
lean_dec_ref_known(v___x_668_, 1);
v___x_670_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_667_, v_a_669_, v_a_402_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; lean_object* v___x_672_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_a_671_);
lean_dec_ref_known(v___x_670_, 1);
lean_inc_ref(v_body_650_);
v___x_672_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_body_650_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; lean_object* v___x_674_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc(v_a_673_);
lean_dec_ref_known(v___x_672_, 1);
v___x_674_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_671_, v_a_673_, v_a_402_, v_a_404_, v_a_405_);
v___y_408_ = v___x_674_;
goto v___jp_407_;
}
else
{
lean_dec(v_a_671_);
v___y_408_ = v___x_672_;
goto v___jp_407_;
}
}
else
{
v___y_408_ = v___x_670_;
goto v___jp_407_;
}
}
else
{
lean_dec(v_a_667_);
v___y_408_ = v___x_668_;
goto v___jp_407_;
}
}
else
{
v___y_408_ = v___x_666_;
goto v___jp_407_;
}
}
}
}
}
case 10:
{
lean_object* v_expr_677_; uint8_t v___y_679_; uint8_t v___x_725_; 
v_expr_677_ = lean_ctor_get(v_e_399_, 1);
lean_inc_ref(v_expr_677_);
lean_dec_ref_known(v_e_399_, 2);
v___x_725_ = l_Lean_Expr_hasFVar(v_expr_677_);
if (v___x_725_ == 0)
{
uint8_t v___x_726_; 
v___x_726_ = l_Lean_Expr_hasMVar(v_expr_677_);
v___y_679_ = v___x_726_;
goto v___jp_678_;
}
else
{
v___y_679_ = v___x_725_;
goto v___jp_678_;
}
v___jp_678_:
{
if (v___y_679_ == 0)
{
lean_object* v___x_680_; lean_object* v___x_681_; 
lean_dec_ref(v_expr_677_);
v___x_680_ = lean_box(0);
v___x_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
return v___x_681_;
}
else
{
lean_object* v___x_682_; lean_object* v_maxFVar_683_; lean_object* v___x_684_; 
v___x_682_ = lean_st_ref_get(v_a_401_);
v_maxFVar_683_ = lean_ctor_get(v___x_682_, 1);
lean_inc_ref(v_maxFVar_683_);
lean_dec(v___x_682_);
v___x_684_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_683_, v_expr_677_);
lean_dec_ref(v_maxFVar_683_);
if (lean_obj_tag(v___x_684_) == 1)
{
lean_object* v_val_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_692_; 
lean_dec_ref(v_expr_677_);
v_val_685_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_692_ == 0)
{
v___x_687_ = v___x_684_;
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_val_685_);
lean_dec(v___x_684_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_690_; 
if (v_isShared_688_ == 0)
{
lean_ctor_set_tag(v___x_687_, 0);
v___x_690_ = v___x_687_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_val_685_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
else
{
lean_object* v___x_693_; 
lean_dec(v___x_684_);
lean_inc_ref(v_expr_677_);
v___x_693_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_expr_677_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_724_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_724_ == 0)
{
v___x_696_ = v___x_693_;
v_isShared_697_ = v_isSharedCheck_724_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_693_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_724_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_698_; lean_object* v_share_699_; lean_object* v_maxFVar_700_; lean_object* v_proofInstInfo_701_; lean_object* v_proofInstInfoFVar_702_; lean_object* v_inferType_703_; lean_object* v_getLevel_704_; lean_object* v_congrInfo_705_; lean_object* v_defEqI_706_; lean_object* v_extensions_707_; lean_object* v_issues_708_; lean_object* v_canon_709_; lean_object* v_instanceOverrides_710_; uint8_t v_debug_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_723_; 
v___x_698_ = lean_st_ref_take(v_a_401_);
v_share_699_ = lean_ctor_get(v___x_698_, 0);
v_maxFVar_700_ = lean_ctor_get(v___x_698_, 1);
v_proofInstInfo_701_ = lean_ctor_get(v___x_698_, 2);
v_proofInstInfoFVar_702_ = lean_ctor_get(v___x_698_, 3);
v_inferType_703_ = lean_ctor_get(v___x_698_, 4);
v_getLevel_704_ = lean_ctor_get(v___x_698_, 5);
v_congrInfo_705_ = lean_ctor_get(v___x_698_, 6);
v_defEqI_706_ = lean_ctor_get(v___x_698_, 7);
v_extensions_707_ = lean_ctor_get(v___x_698_, 8);
v_issues_708_ = lean_ctor_get(v___x_698_, 9);
v_canon_709_ = lean_ctor_get(v___x_698_, 10);
v_instanceOverrides_710_ = lean_ctor_get(v___x_698_, 11);
v_debug_711_ = lean_ctor_get_uint8(v___x_698_, sizeof(void*)*12);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_723_ == 0)
{
v___x_713_ = v___x_698_;
v_isShared_714_ = v_isSharedCheck_723_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_instanceOverrides_710_);
lean_inc(v_canon_709_);
lean_inc(v_issues_708_);
lean_inc(v_extensions_707_);
lean_inc(v_defEqI_706_);
lean_inc(v_congrInfo_705_);
lean_inc(v_getLevel_704_);
lean_inc(v_inferType_703_);
lean_inc(v_proofInstInfoFVar_702_);
lean_inc(v_proofInstInfo_701_);
lean_inc(v_maxFVar_700_);
lean_inc(v_share_699_);
lean_dec(v___x_698_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_723_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_715_; lean_object* v___x_717_; 
lean_inc(v_a_694_);
v___x_715_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_700_, v_expr_677_, v_a_694_);
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 1, v___x_715_);
v___x_717_ = v___x_713_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_share_699_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_722_, 2, v_proofInstInfo_701_);
lean_ctor_set(v_reuseFailAlloc_722_, 3, v_proofInstInfoFVar_702_);
lean_ctor_set(v_reuseFailAlloc_722_, 4, v_inferType_703_);
lean_ctor_set(v_reuseFailAlloc_722_, 5, v_getLevel_704_);
lean_ctor_set(v_reuseFailAlloc_722_, 6, v_congrInfo_705_);
lean_ctor_set(v_reuseFailAlloc_722_, 7, v_defEqI_706_);
lean_ctor_set(v_reuseFailAlloc_722_, 8, v_extensions_707_);
lean_ctor_set(v_reuseFailAlloc_722_, 9, v_issues_708_);
lean_ctor_set(v_reuseFailAlloc_722_, 10, v_canon_709_);
lean_ctor_set(v_reuseFailAlloc_722_, 11, v_instanceOverrides_710_);
lean_ctor_set_uint8(v_reuseFailAlloc_722_, sizeof(void*)*12, v_debug_711_);
v___x_717_ = v_reuseFailAlloc_722_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_718_; lean_object* v___x_720_; 
v___x_718_ = lean_st_ref_put(v_a_401_, v___x_717_);
if (v_isShared_697_ == 0)
{
v___x_720_ = v___x_696_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_a_694_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
}
else
{
lean_dec_ref(v_expr_677_);
return v___x_693_;
}
}
}
}
}
case 11:
{
lean_object* v_struct_727_; uint8_t v___y_729_; uint8_t v___x_775_; 
v_struct_727_ = lean_ctor_get(v_e_399_, 2);
v___x_775_ = l_Lean_Expr_hasFVar(v_e_399_);
if (v___x_775_ == 0)
{
uint8_t v___x_776_; 
v___x_776_ = l_Lean_Expr_hasMVar(v_e_399_);
v___y_729_ = v___x_776_;
goto v___jp_728_;
}
else
{
v___y_729_ = v___x_775_;
goto v___jp_728_;
}
v___jp_728_:
{
if (v___y_729_ == 0)
{
lean_object* v___x_730_; lean_object* v___x_731_; 
lean_dec_ref_known(v_e_399_, 3);
v___x_730_ = lean_box(0);
v___x_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
return v___x_731_;
}
else
{
lean_object* v___x_732_; lean_object* v_maxFVar_733_; lean_object* v___x_734_; 
v___x_732_ = lean_st_ref_get(v_a_401_);
v_maxFVar_733_ = lean_ctor_get(v___x_732_, 1);
lean_inc_ref(v_maxFVar_733_);
lean_dec(v___x_732_);
v___x_734_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_733_, v_e_399_);
lean_dec_ref(v_maxFVar_733_);
if (lean_obj_tag(v___x_734_) == 1)
{
lean_object* v_val_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
lean_dec_ref_known(v_e_399_, 3);
v_val_735_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___x_734_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_val_735_);
lean_dec(v___x_734_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
lean_ctor_set_tag(v___x_737_, 0);
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_val_735_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
else
{
lean_object* v___x_743_; 
lean_dec(v___x_734_);
lean_inc_ref(v_struct_727_);
v___x_743_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_struct_727_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_774_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_774_ == 0)
{
v___x_746_ = v___x_743_;
v_isShared_747_ = v_isSharedCheck_774_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_743_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_774_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_748_; lean_object* v_share_749_; lean_object* v_maxFVar_750_; lean_object* v_proofInstInfo_751_; lean_object* v_proofInstInfoFVar_752_; lean_object* v_inferType_753_; lean_object* v_getLevel_754_; lean_object* v_congrInfo_755_; lean_object* v_defEqI_756_; lean_object* v_extensions_757_; lean_object* v_issues_758_; lean_object* v_canon_759_; lean_object* v_instanceOverrides_760_; uint8_t v_debug_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_773_; 
v___x_748_ = lean_st_ref_take(v_a_401_);
v_share_749_ = lean_ctor_get(v___x_748_, 0);
v_maxFVar_750_ = lean_ctor_get(v___x_748_, 1);
v_proofInstInfo_751_ = lean_ctor_get(v___x_748_, 2);
v_proofInstInfoFVar_752_ = lean_ctor_get(v___x_748_, 3);
v_inferType_753_ = lean_ctor_get(v___x_748_, 4);
v_getLevel_754_ = lean_ctor_get(v___x_748_, 5);
v_congrInfo_755_ = lean_ctor_get(v___x_748_, 6);
v_defEqI_756_ = lean_ctor_get(v___x_748_, 7);
v_extensions_757_ = lean_ctor_get(v___x_748_, 8);
v_issues_758_ = lean_ctor_get(v___x_748_, 9);
v_canon_759_ = lean_ctor_get(v___x_748_, 10);
v_instanceOverrides_760_ = lean_ctor_get(v___x_748_, 11);
v_debug_761_ = lean_ctor_get_uint8(v___x_748_, sizeof(void*)*12);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_773_ == 0)
{
v___x_763_ = v___x_748_;
v_isShared_764_ = v_isSharedCheck_773_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_instanceOverrides_760_);
lean_inc(v_canon_759_);
lean_inc(v_issues_758_);
lean_inc(v_extensions_757_);
lean_inc(v_defEqI_756_);
lean_inc(v_congrInfo_755_);
lean_inc(v_getLevel_754_);
lean_inc(v_inferType_753_);
lean_inc(v_proofInstInfoFVar_752_);
lean_inc(v_proofInstInfo_751_);
lean_inc(v_maxFVar_750_);
lean_inc(v_share_749_);
lean_dec(v___x_748_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_773_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_765_; lean_object* v___x_767_; 
lean_inc(v_a_744_);
v___x_765_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_750_, v_e_399_, v_a_744_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 1, v___x_765_);
v___x_767_ = v___x_763_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_share_749_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v___x_765_);
lean_ctor_set(v_reuseFailAlloc_772_, 2, v_proofInstInfo_751_);
lean_ctor_set(v_reuseFailAlloc_772_, 3, v_proofInstInfoFVar_752_);
lean_ctor_set(v_reuseFailAlloc_772_, 4, v_inferType_753_);
lean_ctor_set(v_reuseFailAlloc_772_, 5, v_getLevel_754_);
lean_ctor_set(v_reuseFailAlloc_772_, 6, v_congrInfo_755_);
lean_ctor_set(v_reuseFailAlloc_772_, 7, v_defEqI_756_);
lean_ctor_set(v_reuseFailAlloc_772_, 8, v_extensions_757_);
lean_ctor_set(v_reuseFailAlloc_772_, 9, v_issues_758_);
lean_ctor_set(v_reuseFailAlloc_772_, 10, v_canon_759_);
lean_ctor_set(v_reuseFailAlloc_772_, 11, v_instanceOverrides_760_);
lean_ctor_set_uint8(v_reuseFailAlloc_772_, sizeof(void*)*12, v_debug_761_);
v___x_767_ = v_reuseFailAlloc_772_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
lean_object* v___x_768_; lean_object* v___x_770_; 
v___x_768_ = lean_st_ref_put(v_a_401_, v___x_767_);
if (v_isShared_747_ == 0)
{
v___x_770_ = v___x_746_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_744_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_399_, 3);
return v___x_743_;
}
}
}
}
}
default: 
{
lean_object* v___x_777_; lean_object* v___x_778_; 
lean_dec_ref(v_e_399_);
v___x_777_ = lean_box(0);
v___x_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
return v___x_778_;
}
}
v___jp_407_:
{
if (lean_obj_tag(v___y_408_) == 0)
{
lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_439_; 
v_a_409_ = lean_ctor_get(v___y_408_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___y_408_);
if (v_isSharedCheck_439_ == 0)
{
v___x_411_ = v___y_408_;
v_isShared_412_ = v_isSharedCheck_439_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_dec(v___y_408_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_439_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_413_; lean_object* v_share_414_; lean_object* v_maxFVar_415_; lean_object* v_proofInstInfo_416_; lean_object* v_proofInstInfoFVar_417_; lean_object* v_inferType_418_; lean_object* v_getLevel_419_; lean_object* v_congrInfo_420_; lean_object* v_defEqI_421_; lean_object* v_extensions_422_; lean_object* v_issues_423_; lean_object* v_canon_424_; lean_object* v_instanceOverrides_425_; uint8_t v_debug_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_438_; 
v___x_413_ = lean_st_ref_take(v_a_401_);
v_share_414_ = lean_ctor_get(v___x_413_, 0);
v_maxFVar_415_ = lean_ctor_get(v___x_413_, 1);
v_proofInstInfo_416_ = lean_ctor_get(v___x_413_, 2);
v_proofInstInfoFVar_417_ = lean_ctor_get(v___x_413_, 3);
v_inferType_418_ = lean_ctor_get(v___x_413_, 4);
v_getLevel_419_ = lean_ctor_get(v___x_413_, 5);
v_congrInfo_420_ = lean_ctor_get(v___x_413_, 6);
v_defEqI_421_ = lean_ctor_get(v___x_413_, 7);
v_extensions_422_ = lean_ctor_get(v___x_413_, 8);
v_issues_423_ = lean_ctor_get(v___x_413_, 9);
v_canon_424_ = lean_ctor_get(v___x_413_, 10);
v_instanceOverrides_425_ = lean_ctor_get(v___x_413_, 11);
v_debug_426_ = lean_ctor_get_uint8(v___x_413_, sizeof(void*)*12);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_438_ == 0)
{
v___x_428_ = v___x_413_;
v_isShared_429_ = v_isSharedCheck_438_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_instanceOverrides_425_);
lean_inc(v_canon_424_);
lean_inc(v_issues_423_);
lean_inc(v_extensions_422_);
lean_inc(v_defEqI_421_);
lean_inc(v_congrInfo_420_);
lean_inc(v_getLevel_419_);
lean_inc(v_inferType_418_);
lean_inc(v_proofInstInfoFVar_417_);
lean_inc(v_proofInstInfo_416_);
lean_inc(v_maxFVar_415_);
lean_inc(v_share_414_);
lean_dec(v___x_413_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_438_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_430_; lean_object* v___x_432_; 
lean_inc(v_a_409_);
v___x_430_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_415_, v_e_399_, v_a_409_);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 1, v___x_430_);
v___x_432_ = v___x_428_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_share_414_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_437_, 2, v_proofInstInfo_416_);
lean_ctor_set(v_reuseFailAlloc_437_, 3, v_proofInstInfoFVar_417_);
lean_ctor_set(v_reuseFailAlloc_437_, 4, v_inferType_418_);
lean_ctor_set(v_reuseFailAlloc_437_, 5, v_getLevel_419_);
lean_ctor_set(v_reuseFailAlloc_437_, 6, v_congrInfo_420_);
lean_ctor_set(v_reuseFailAlloc_437_, 7, v_defEqI_421_);
lean_ctor_set(v_reuseFailAlloc_437_, 8, v_extensions_422_);
lean_ctor_set(v_reuseFailAlloc_437_, 9, v_issues_423_);
lean_ctor_set(v_reuseFailAlloc_437_, 10, v_canon_424_);
lean_ctor_set(v_reuseFailAlloc_437_, 11, v_instanceOverrides_425_);
lean_ctor_set_uint8(v_reuseFailAlloc_437_, sizeof(void*)*12, v_debug_426_);
v___x_432_ = v_reuseFailAlloc_437_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_object* v___x_433_; lean_object* v___x_435_; 
v___x_433_ = lean_st_ref_put(v_a_401_, v___x_432_);
if (v_isShared_412_ == 0)
{
v___x_435_ = v___x_411_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_409_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_399_);
return v___y_408_;
}
}
v___jp_440_:
{
lean_object* v___x_442_; lean_object* v_share_443_; lean_object* v_maxFVar_444_; lean_object* v_proofInstInfo_445_; lean_object* v_proofInstInfoFVar_446_; lean_object* v_inferType_447_; lean_object* v_getLevel_448_; lean_object* v_congrInfo_449_; lean_object* v_defEqI_450_; lean_object* v_extensions_451_; lean_object* v_issues_452_; lean_object* v_canon_453_; lean_object* v_instanceOverrides_454_; uint8_t v_debug_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_465_; 
v___x_442_ = lean_st_ref_take(v_a_401_);
v_share_443_ = lean_ctor_get(v___x_442_, 0);
v_maxFVar_444_ = lean_ctor_get(v___x_442_, 1);
v_proofInstInfo_445_ = lean_ctor_get(v___x_442_, 2);
v_proofInstInfoFVar_446_ = lean_ctor_get(v___x_442_, 3);
v_inferType_447_ = lean_ctor_get(v___x_442_, 4);
v_getLevel_448_ = lean_ctor_get(v___x_442_, 5);
v_congrInfo_449_ = lean_ctor_get(v___x_442_, 6);
v_defEqI_450_ = lean_ctor_get(v___x_442_, 7);
v_extensions_451_ = lean_ctor_get(v___x_442_, 8);
v_issues_452_ = lean_ctor_get(v___x_442_, 9);
v_canon_453_ = lean_ctor_get(v___x_442_, 10);
v_instanceOverrides_454_ = lean_ctor_get(v___x_442_, 11);
v_debug_455_ = lean_ctor_get_uint8(v___x_442_, sizeof(void*)*12);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_465_ == 0)
{
v___x_457_ = v___x_442_;
v_isShared_458_ = v_isSharedCheck_465_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_instanceOverrides_454_);
lean_inc(v_canon_453_);
lean_inc(v_issues_452_);
lean_inc(v_extensions_451_);
lean_inc(v_defEqI_450_);
lean_inc(v_congrInfo_449_);
lean_inc(v_getLevel_448_);
lean_inc(v_inferType_447_);
lean_inc(v_proofInstInfoFVar_446_);
lean_inc(v_proofInstInfo_445_);
lean_inc(v_maxFVar_444_);
lean_inc(v_share_443_);
lean_dec(v___x_442_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_465_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_459_; lean_object* v___x_461_; 
lean_inc(v_a_441_);
v___x_459_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_444_, v_e_399_, v_a_441_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 1, v___x_459_);
v___x_461_ = v___x_457_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_share_443_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v___x_459_);
lean_ctor_set(v_reuseFailAlloc_464_, 2, v_proofInstInfo_445_);
lean_ctor_set(v_reuseFailAlloc_464_, 3, v_proofInstInfoFVar_446_);
lean_ctor_set(v_reuseFailAlloc_464_, 4, v_inferType_447_);
lean_ctor_set(v_reuseFailAlloc_464_, 5, v_getLevel_448_);
lean_ctor_set(v_reuseFailAlloc_464_, 6, v_congrInfo_449_);
lean_ctor_set(v_reuseFailAlloc_464_, 7, v_defEqI_450_);
lean_ctor_set(v_reuseFailAlloc_464_, 8, v_extensions_451_);
lean_ctor_set(v_reuseFailAlloc_464_, 9, v_issues_452_);
lean_ctor_set(v_reuseFailAlloc_464_, 10, v_canon_453_);
lean_ctor_set(v_reuseFailAlloc_464_, 11, v_instanceOverrides_454_);
lean_ctor_set_uint8(v_reuseFailAlloc_464_, sizeof(void*)*12, v_debug_455_);
v___x_461_ = v_reuseFailAlloc_464_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = lean_st_ref_put(v_a_401_, v___x_461_);
v___x_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_463_, 0, v_a_441_);
return v___x_463_;
}
}
}
v___jp_466_:
{
if (lean_obj_tag(v___y_468_) == 0)
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_499_; 
v_a_469_ = lean_ctor_get(v___y_468_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___y_468_);
if (v_isSharedCheck_499_ == 0)
{
v___x_471_ = v___y_468_;
v_isShared_472_ = v_isSharedCheck_499_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___y_468_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_499_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_473_; lean_object* v_share_474_; lean_object* v_maxFVar_475_; lean_object* v_proofInstInfo_476_; lean_object* v_proofInstInfoFVar_477_; lean_object* v_inferType_478_; lean_object* v_getLevel_479_; lean_object* v_congrInfo_480_; lean_object* v_defEqI_481_; lean_object* v_extensions_482_; lean_object* v_issues_483_; lean_object* v_canon_484_; lean_object* v_instanceOverrides_485_; uint8_t v_debug_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_498_; 
v___x_473_ = lean_st_ref_take(v___y_467_);
v_share_474_ = lean_ctor_get(v___x_473_, 0);
v_maxFVar_475_ = lean_ctor_get(v___x_473_, 1);
v_proofInstInfo_476_ = lean_ctor_get(v___x_473_, 2);
v_proofInstInfoFVar_477_ = lean_ctor_get(v___x_473_, 3);
v_inferType_478_ = lean_ctor_get(v___x_473_, 4);
v_getLevel_479_ = lean_ctor_get(v___x_473_, 5);
v_congrInfo_480_ = lean_ctor_get(v___x_473_, 6);
v_defEqI_481_ = lean_ctor_get(v___x_473_, 7);
v_extensions_482_ = lean_ctor_get(v___x_473_, 8);
v_issues_483_ = lean_ctor_get(v___x_473_, 9);
v_canon_484_ = lean_ctor_get(v___x_473_, 10);
v_instanceOverrides_485_ = lean_ctor_get(v___x_473_, 11);
v_debug_486_ = lean_ctor_get_uint8(v___x_473_, sizeof(void*)*12);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_498_ == 0)
{
v___x_488_ = v___x_473_;
v_isShared_489_ = v_isSharedCheck_498_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_instanceOverrides_485_);
lean_inc(v_canon_484_);
lean_inc(v_issues_483_);
lean_inc(v_extensions_482_);
lean_inc(v_defEqI_481_);
lean_inc(v_congrInfo_480_);
lean_inc(v_getLevel_479_);
lean_inc(v_inferType_478_);
lean_inc(v_proofInstInfoFVar_477_);
lean_inc(v_proofInstInfo_476_);
lean_inc(v_maxFVar_475_);
lean_inc(v_share_474_);
lean_dec(v___x_473_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_498_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_490_; lean_object* v___x_492_; 
lean_inc(v_a_469_);
v___x_490_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_475_, v_e_399_, v_a_469_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 1, v___x_490_);
v___x_492_ = v___x_488_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_share_474_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_497_, 2, v_proofInstInfo_476_);
lean_ctor_set(v_reuseFailAlloc_497_, 3, v_proofInstInfoFVar_477_);
lean_ctor_set(v_reuseFailAlloc_497_, 4, v_inferType_478_);
lean_ctor_set(v_reuseFailAlloc_497_, 5, v_getLevel_479_);
lean_ctor_set(v_reuseFailAlloc_497_, 6, v_congrInfo_480_);
lean_ctor_set(v_reuseFailAlloc_497_, 7, v_defEqI_481_);
lean_ctor_set(v_reuseFailAlloc_497_, 8, v_extensions_482_);
lean_ctor_set(v_reuseFailAlloc_497_, 9, v_issues_483_);
lean_ctor_set(v_reuseFailAlloc_497_, 10, v_canon_484_);
lean_ctor_set(v_reuseFailAlloc_497_, 11, v_instanceOverrides_485_);
lean_ctor_set_uint8(v_reuseFailAlloc_497_, sizeof(void*)*12, v_debug_486_);
v___x_492_ = v_reuseFailAlloc_497_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v___x_493_; lean_object* v___x_495_; 
v___x_493_ = lean_st_ref_put(v___y_467_, v___x_492_);
if (v_isShared_472_ == 0)
{
v___x_495_ = v___x_471_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_469_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_399_);
return v___y_468_;
}
}
v___jp_500_:
{
if (v___y_509_ == 0)
{
lean_object* v___x_510_; lean_object* v___x_511_; 
lean_dec_ref(v___y_508_);
lean_dec_ref(v___y_504_);
lean_dec_ref(v_e_399_);
v___x_510_ = lean_box(0);
v___x_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
return v___x_511_;
}
else
{
lean_object* v___x_512_; lean_object* v_maxFVar_513_; lean_object* v___x_514_; 
v___x_512_ = lean_st_ref_get(v___y_506_);
v_maxFVar_513_ = lean_ctor_get(v___x_512_, 1);
lean_inc_ref(v_maxFVar_513_);
lean_dec(v___x_512_);
v___x_514_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_513_, v_e_399_);
lean_dec_ref(v_maxFVar_513_);
if (lean_obj_tag(v___x_514_) == 1)
{
lean_object* v_val_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_522_; 
lean_dec_ref(v___y_508_);
lean_dec_ref(v___y_504_);
lean_dec_ref(v_e_399_);
v_val_515_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_522_ == 0)
{
v___x_517_ = v___x_514_;
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_val_515_);
lean_dec(v___x_514_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_520_; 
if (v_isShared_518_ == 0)
{
lean_ctor_set_tag(v___x_517_, 0);
v___x_520_ = v___x_517_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_val_515_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
else
{
lean_object* v___x_523_; 
lean_dec(v___x_514_);
v___x_523_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v___y_508_, v___y_507_, v___y_506_, v___y_501_, v___y_502_, v___y_505_, v___y_503_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_524_; lean_object* v___x_525_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_a_524_);
lean_dec_ref_known(v___x_523_, 1);
v___x_525_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v___y_504_, v___y_507_, v___y_506_, v___y_501_, v___y_502_, v___y_505_, v___y_503_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; lean_object* v___x_527_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_a_526_);
lean_dec_ref_known(v___x_525_, 1);
v___x_527_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_524_, v_a_526_, v___y_501_, v___y_505_, v___y_503_);
v___y_467_ = v___y_506_;
v___y_468_ = v___x_527_;
goto v___jp_466_;
}
else
{
lean_dec(v_a_524_);
v___y_467_ = v___y_506_;
v___y_468_ = v___x_525_;
goto v___jp_466_;
}
}
else
{
lean_dec_ref(v___y_504_);
v___y_467_ = v___y_506_;
v___y_468_ = v___x_523_;
goto v___jp_466_;
}
}
}
}
v___jp_528_:
{
uint8_t v___x_537_; 
v___x_537_ = l_Lean_Expr_hasFVar(v_e_399_);
if (v___x_537_ == 0)
{
uint8_t v___x_538_; 
v___x_538_ = l_Lean_Expr_hasMVar(v_e_399_);
v___y_501_ = v___y_533_;
v___y_502_ = v___y_534_;
v___y_503_ = v___y_536_;
v___y_504_ = v_b_530_;
v___y_505_ = v___y_535_;
v___y_506_ = v___y_532_;
v___y_507_ = v___y_531_;
v___y_508_ = v_d_529_;
v___y_509_ = v___x_538_;
goto v___jp_500_;
}
else
{
v___y_501_ = v___y_533_;
v___y_502_ = v___y_534_;
v___y_503_ = v___y_536_;
v___y_504_ = v_b_530_;
v___y_505_ = v___y_535_;
v___y_506_ = v___y_532_;
v___y_507_ = v___y_531_;
v___y_508_ = v_d_529_;
v___y_509_ = v___x_537_;
goto v___jp_500_;
}
}
v___jp_539_:
{
if (lean_obj_tag(v___y_540_) == 0)
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_571_; 
v_a_541_ = lean_ctor_get(v___y_540_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___y_540_);
if (v_isSharedCheck_571_ == 0)
{
v___x_543_ = v___y_540_;
v_isShared_544_ = v_isSharedCheck_571_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___y_540_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_571_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_545_; lean_object* v_share_546_; lean_object* v_maxFVar_547_; lean_object* v_proofInstInfo_548_; lean_object* v_proofInstInfoFVar_549_; lean_object* v_inferType_550_; lean_object* v_getLevel_551_; lean_object* v_congrInfo_552_; lean_object* v_defEqI_553_; lean_object* v_extensions_554_; lean_object* v_issues_555_; lean_object* v_canon_556_; lean_object* v_instanceOverrides_557_; uint8_t v_debug_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_570_; 
v___x_545_ = lean_st_ref_take(v_a_401_);
v_share_546_ = lean_ctor_get(v___x_545_, 0);
v_maxFVar_547_ = lean_ctor_get(v___x_545_, 1);
v_proofInstInfo_548_ = lean_ctor_get(v___x_545_, 2);
v_proofInstInfoFVar_549_ = lean_ctor_get(v___x_545_, 3);
v_inferType_550_ = lean_ctor_get(v___x_545_, 4);
v_getLevel_551_ = lean_ctor_get(v___x_545_, 5);
v_congrInfo_552_ = lean_ctor_get(v___x_545_, 6);
v_defEqI_553_ = lean_ctor_get(v___x_545_, 7);
v_extensions_554_ = lean_ctor_get(v___x_545_, 8);
v_issues_555_ = lean_ctor_get(v___x_545_, 9);
v_canon_556_ = lean_ctor_get(v___x_545_, 10);
v_instanceOverrides_557_ = lean_ctor_get(v___x_545_, 11);
v_debug_558_ = lean_ctor_get_uint8(v___x_545_, sizeof(void*)*12);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_570_ == 0)
{
v___x_560_ = v___x_545_;
v_isShared_561_ = v_isSharedCheck_570_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_instanceOverrides_557_);
lean_inc(v_canon_556_);
lean_inc(v_issues_555_);
lean_inc(v_extensions_554_);
lean_inc(v_defEqI_553_);
lean_inc(v_congrInfo_552_);
lean_inc(v_getLevel_551_);
lean_inc(v_inferType_550_);
lean_inc(v_proofInstInfoFVar_549_);
lean_inc(v_proofInstInfo_548_);
lean_inc(v_maxFVar_547_);
lean_inc(v_share_546_);
lean_dec(v___x_545_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_570_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_562_; lean_object* v___x_564_; 
lean_inc(v_a_541_);
v___x_562_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_547_, v_e_399_, v_a_541_);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 1, v___x_562_);
v___x_564_ = v___x_560_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_share_546_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v___x_562_);
lean_ctor_set(v_reuseFailAlloc_569_, 2, v_proofInstInfo_548_);
lean_ctor_set(v_reuseFailAlloc_569_, 3, v_proofInstInfoFVar_549_);
lean_ctor_set(v_reuseFailAlloc_569_, 4, v_inferType_550_);
lean_ctor_set(v_reuseFailAlloc_569_, 5, v_getLevel_551_);
lean_ctor_set(v_reuseFailAlloc_569_, 6, v_congrInfo_552_);
lean_ctor_set(v_reuseFailAlloc_569_, 7, v_defEqI_553_);
lean_ctor_set(v_reuseFailAlloc_569_, 8, v_extensions_554_);
lean_ctor_set(v_reuseFailAlloc_569_, 9, v_issues_555_);
lean_ctor_set(v_reuseFailAlloc_569_, 10, v_canon_556_);
lean_ctor_set(v_reuseFailAlloc_569_, 11, v_instanceOverrides_557_);
lean_ctor_set_uint8(v_reuseFailAlloc_569_, sizeof(void*)*12, v_debug_558_);
v___x_564_ = v_reuseFailAlloc_569_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
lean_object* v___x_565_; lean_object* v___x_567_; 
v___x_565_ = lean_st_ref_put(v_a_401_, v___x_564_);
if (v_isShared_544_ == 0)
{
v___x_567_ = v___x_543_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_a_541_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_399_);
return v___y_540_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f___boxed(lean_object* v_e_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_e_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_);
lean_dec(v_a_785_);
lean_dec_ref(v_a_784_);
lean_dec(v_a_783_);
lean_dec_ref(v_a_782_);
lean_dec(v_a_781_);
lean_dec_ref(v_a_780_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0(lean_object* v_00_u03b2_788_, lean_object* v_x_789_, lean_object* v_x_790_, lean_object* v_x_791_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_x_789_, v_x_790_, v_x_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1(lean_object* v_00_u03b2_793_, lean_object* v_x_794_, lean_object* v_x_795_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_x_794_, v_x_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___boxed(lean_object* v_00_u03b2_797_, lean_object* v_x_798_, lean_object* v_x_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1(v_00_u03b2_797_, v_x_798_, v_x_799_);
lean_dec_ref(v_x_799_);
lean_dec_ref(v_x_798_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0(lean_object* v_00_u03b2_801_, lean_object* v_x_802_, size_t v_x_803_, size_t v_x_804_, lean_object* v_x_805_, lean_object* v_x_806_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_802_, v_x_803_, v_x_804_, v_x_805_, v_x_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_808_, lean_object* v_x_809_, lean_object* v_x_810_, lean_object* v_x_811_, lean_object* v_x_812_, lean_object* v_x_813_){
_start:
{
size_t v_x_5584__boxed_814_; size_t v_x_5585__boxed_815_; lean_object* v_res_816_; 
v_x_5584__boxed_814_ = lean_unbox_usize(v_x_810_);
lean_dec(v_x_810_);
v_x_5585__boxed_815_ = lean_unbox_usize(v_x_811_);
lean_dec(v_x_811_);
v_res_816_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0(v_00_u03b2_808_, v_x_809_, v_x_5584__boxed_814_, v_x_5585__boxed_815_, v_x_812_, v_x_813_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2(lean_object* v_00_u03b2_817_, lean_object* v_x_818_, size_t v_x_819_, lean_object* v_x_820_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_818_, v_x_819_, v_x_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_822_, lean_object* v_x_823_, lean_object* v_x_824_, lean_object* v_x_825_){
_start:
{
size_t v_x_5601__boxed_826_; lean_object* v_res_827_; 
v_x_5601__boxed_826_ = lean_unbox_usize(v_x_824_);
lean_dec(v_x_824_);
v_res_827_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2(v_00_u03b2_822_, v_x_823_, v_x_5601__boxed_826_, v_x_825_);
lean_dec_ref(v_x_825_);
lean_dec_ref(v_x_823_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_828_, lean_object* v_n_829_, lean_object* v_k_830_, lean_object* v_v_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(v_n_829_, v_k_830_, v_v_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_833_, size_t v_depth_834_, lean_object* v_keys_835_, lean_object* v_vals_836_, lean_object* v_heq_837_, lean_object* v_i_838_, lean_object* v_entries_839_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(v_depth_834_, v_keys_835_, v_vals_836_, v_i_838_, v_entries_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_841_, lean_object* v_depth_842_, lean_object* v_keys_843_, lean_object* v_vals_844_, lean_object* v_heq_845_, lean_object* v_i_846_, lean_object* v_entries_847_){
_start:
{
size_t v_depth_boxed_848_; lean_object* v_res_849_; 
v_depth_boxed_848_ = lean_unbox_usize(v_depth_842_);
lean_dec(v_depth_842_);
v_res_849_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3(v_00_u03b2_841_, v_depth_boxed_848_, v_keys_843_, v_vals_844_, v_heq_845_, v_i_846_, v_entries_847_);
lean_dec_ref(v_vals_844_);
lean_dec_ref(v_keys_843_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_850_, lean_object* v_keys_851_, lean_object* v_vals_852_, lean_object* v_heq_853_, lean_object* v_i_854_, lean_object* v_k_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_keys_851_, v_vals_852_, v_i_854_, v_k_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_857_, lean_object* v_keys_858_, lean_object* v_vals_859_, lean_object* v_heq_860_, lean_object* v_i_861_, lean_object* v_k_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6(v_00_u03b2_857_, v_keys_858_, v_vals_859_, v_heq_860_, v_i_861_, v_k_862_);
lean_dec_ref(v_k_862_);
lean_dec_ref(v_vals_859_);
lean_dec_ref(v_keys_858_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_864_, lean_object* v_x_865_, lean_object* v_x_866_, lean_object* v_x_867_, lean_object* v_x_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_x_865_, v_x_866_, v_x_867_, v_x_868_);
return v___x_869_;
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
