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
lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(lean_object* v_fvarId1_x3f_1_, lean_object* v_fvarId2_x3f_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_){
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
LEAN_EXPORT void l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId1_x3f_1_ = stack[0].m_obj;
lean_object* v_fvarId2_x3f_2_ = stack[1].m_obj;
lean_object* v_a_3_ = stack[2].m_obj;
lean_object* v_a_4_ = stack[3].m_obj;
lean_object* v_a_5_ = stack[4].m_obj;
lean_object* v_res_53_;
v_res_53_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_fvarId1_x3f_1_, v_fvarId2_x3f_2_, v_a_3_, v_a_4_, v_a_5_);
stack->m_obj
 = v_res_53_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg___boxed(lean_object* v_fvarId1_x3f_54_, lean_object* v_fvarId2_x3f_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_fvarId1_x3f_54_, v_fvarId2_x3f_55_, v_a_56_, v_a_57_, v_a_58_);
lean_dec(v_a_58_);
lean_dec_ref(v_a_57_);
lean_dec_ref(v_a_56_);
return v_res_60_;
}
}
lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max(lean_object* v_fvarId1_x3f_61_, lean_object* v_fvarId2_x3f_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_fvarId1_x3f_61_, v_fvarId2_x3f_62_, v_a_63_, v_a_65_, v_a_66_);
return v___x_68_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId1_x3f_61_ = stack[0].m_obj;
lean_object* v_fvarId2_x3f_62_ = stack[1].m_obj;
lean_object* v_a_63_ = stack[2].m_obj;
lean_object* v_a_64_ = stack[3].m_obj;
lean_object* v_a_65_ = stack[4].m_obj;
lean_object* v_a_66_ = stack[5].m_obj;
lean_object* v_res_69_;
v_res_69_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max(v_fvarId1_x3f_61_, v_fvarId2_x3f_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_);
stack->m_obj
 = v_res_69_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___boxed(lean_object* v_fvarId1_x3f_70_, lean_object* v_fvarId2_x3f_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max(v_fvarId1_x3f_70_, v_fvarId2_x3f_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_);
lean_dec(v_a_75_);
lean_dec_ref(v_a_74_);
lean_dec(v_a_73_);
lean_dec_ref(v_a_72_);
return v_res_77_;
}
}
lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check(lean_object* v_e_80_, lean_object* v_k_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_){
_start:
{
lean_object* v___f_89_; lean_object* v___f_90_; uint8_t v___y_92_; uint8_t v___x_138_; 
v___f_89_ = ((lean_object*)(l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__0));
v___f_90_ = ((lean_object*)(l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__1));
v___x_138_ = l_Lean_Expr_hasFVar(v_e_80_);
if (v___x_138_ == 0)
{
uint8_t v___x_139_; 
v___x_139_ = l_Lean_Expr_hasMVar(v_e_80_);
v___y_92_ = v___x_139_;
goto v___jp_91_;
}
else
{
v___y_92_ = v___x_138_;
goto v___jp_91_;
}
v___jp_91_:
{
if (v___y_92_ == 0)
{
lean_object* v___x_93_; lean_object* v___x_94_; 
lean_dec_ref(v_k_81_);
lean_dec_ref(v_e_80_);
v___x_93_ = lean_box(0);
v___x_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
return v___x_94_;
}
else
{
lean_object* v___x_95_; lean_object* v_maxFVar_96_; lean_object* v___x_97_; 
v___x_95_ = lean_st_ref_get(v_a_83_);
v_maxFVar_96_ = lean_ctor_get(v___x_95_, 1);
lean_inc_ref(v_maxFVar_96_);
lean_dec(v___x_95_);
lean_inc_ref(v_e_80_);
v___x_97_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_89_, v___f_90_, v_maxFVar_96_, v_e_80_);
lean_dec_ref(v_maxFVar_96_);
if (lean_obj_tag(v___x_97_) == 1)
{
lean_object* v_val_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_105_; 
lean_dec_ref(v_k_81_);
lean_dec_ref(v_e_80_);
v_val_98_ = lean_ctor_get(v___x_97_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_105_ == 0)
{
v___x_100_ = v___x_97_;
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_val_98_);
lean_dec(v___x_97_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_103_; 
if (v_isShared_101_ == 0)
{
lean_ctor_set_tag(v___x_100_, 0);
v___x_103_ = v___x_100_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_val_98_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
}
else
{
lean_object* v___x_106_; 
lean_dec(v___x_97_);
lean_inc(v_a_87_);
lean_inc_ref(v_a_86_);
lean_inc(v_a_85_);
lean_inc_ref(v_a_84_);
lean_inc(v_a_83_);
lean_inc_ref(v_a_82_);
v___x_106_ = lean_apply_7(v_k_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, lean_box(0));
if (lean_obj_tag(v___x_106_) == 0)
{
lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_137_; 
v_a_107_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_137_ == 0)
{
v___x_109_ = v___x_106_;
v_isShared_110_ = v_isSharedCheck_137_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_dec(v___x_106_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_137_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; lean_object* v_share_112_; lean_object* v_maxFVar_113_; lean_object* v_proofInstInfo_114_; lean_object* v_proofInstInfoFVar_115_; lean_object* v_inferType_116_; lean_object* v_getLevel_117_; lean_object* v_congrInfo_118_; lean_object* v_defEqI_119_; lean_object* v_extensions_120_; lean_object* v_issues_121_; lean_object* v_canon_122_; lean_object* v_instanceOverrides_123_; uint8_t v_debug_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_136_; 
v___x_111_ = lean_st_ref_take(v_a_83_);
v_share_112_ = lean_ctor_get(v___x_111_, 0);
v_maxFVar_113_ = lean_ctor_get(v___x_111_, 1);
v_proofInstInfo_114_ = lean_ctor_get(v___x_111_, 2);
v_proofInstInfoFVar_115_ = lean_ctor_get(v___x_111_, 3);
v_inferType_116_ = lean_ctor_get(v___x_111_, 4);
v_getLevel_117_ = lean_ctor_get(v___x_111_, 5);
v_congrInfo_118_ = lean_ctor_get(v___x_111_, 6);
v_defEqI_119_ = lean_ctor_get(v___x_111_, 7);
v_extensions_120_ = lean_ctor_get(v___x_111_, 8);
v_issues_121_ = lean_ctor_get(v___x_111_, 9);
v_canon_122_ = lean_ctor_get(v___x_111_, 10);
v_instanceOverrides_123_ = lean_ctor_get(v___x_111_, 11);
v_debug_124_ = lean_ctor_get_uint8(v___x_111_, sizeof(void*)*12);
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_136_ == 0)
{
v___x_126_ = v___x_111_;
v_isShared_127_ = v_isSharedCheck_136_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_instanceOverrides_123_);
lean_inc(v_canon_122_);
lean_inc(v_issues_121_);
lean_inc(v_extensions_120_);
lean_inc(v_defEqI_119_);
lean_inc(v_congrInfo_118_);
lean_inc(v_getLevel_117_);
lean_inc(v_inferType_116_);
lean_inc(v_proofInstInfoFVar_115_);
lean_inc(v_proofInstInfo_114_);
lean_inc(v_maxFVar_113_);
lean_inc(v_share_112_);
lean_dec(v___x_111_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_136_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_128_; lean_object* v___x_130_; 
lean_inc(v_a_107_);
v___x_128_ = l_Lean_PersistentHashMap_insert___redArg(v___f_89_, v___f_90_, v_maxFVar_113_, v_e_80_, v_a_107_);
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 1, v___x_128_);
v___x_130_ = v___x_126_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_share_112_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v___x_128_);
lean_ctor_set(v_reuseFailAlloc_135_, 2, v_proofInstInfo_114_);
lean_ctor_set(v_reuseFailAlloc_135_, 3, v_proofInstInfoFVar_115_);
lean_ctor_set(v_reuseFailAlloc_135_, 4, v_inferType_116_);
lean_ctor_set(v_reuseFailAlloc_135_, 5, v_getLevel_117_);
lean_ctor_set(v_reuseFailAlloc_135_, 6, v_congrInfo_118_);
lean_ctor_set(v_reuseFailAlloc_135_, 7, v_defEqI_119_);
lean_ctor_set(v_reuseFailAlloc_135_, 8, v_extensions_120_);
lean_ctor_set(v_reuseFailAlloc_135_, 9, v_issues_121_);
lean_ctor_set(v_reuseFailAlloc_135_, 10, v_canon_122_);
lean_ctor_set(v_reuseFailAlloc_135_, 11, v_instanceOverrides_123_);
lean_ctor_set_uint8(v_reuseFailAlloc_135_, sizeof(void*)*12, v_debug_124_);
v___x_130_ = v_reuseFailAlloc_135_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
lean_object* v___x_131_; lean_object* v___x_133_; 
v___x_131_ = lean_st_ref_put(v_a_83_, v___x_130_);
if (v_isShared_110_ == 0)
{
v___x_133_ = v___x_109_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_a_107_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_80_);
return v___x_106_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_80_ = stack[0].m_obj;
lean_object* v_k_81_ = stack[1].m_obj;
lean_object* v_a_82_ = stack[2].m_obj;
lean_object* v_a_83_ = stack[3].m_obj;
lean_object* v_a_84_ = stack[4].m_obj;
lean_object* v_a_85_ = stack[5].m_obj;
lean_object* v_a_86_ = stack[6].m_obj;
lean_object* v_a_87_ = stack[7].m_obj;
lean_object* v_res_140_;
v_res_140_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check(v_e_80_, v_k_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_);
stack->m_obj
 = v_res_140_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___boxed(lean_object* v_e_141_, lean_object* v_k_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check(v_e_141_, v_k_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_);
lean_dec(v_a_148_);
lean_dec_ref(v_a_147_);
lean_dec(v_a_146_);
lean_dec_ref(v_a_145_);
lean_dec(v_a_144_);
lean_dec_ref(v_a_143_);
return v_res_150_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0(void){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l_Lean_Meta_Sym_instInhabitedSymM___redArg();
return v___x_151_;
}
}
lean_object* l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2(lean_object* v_msg_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_){
_start:
{
lean_object* v___x_160_; lean_object* v___x_4122__overap_161_; lean_object* v___x_162_; 
v___x_160_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0, &l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0);
v___x_4122__overap_161_ = lean_panic_fn_borrowed(v___x_160_, v_msg_152_);
lean_inc(v___y_158_);
lean_inc_ref(v___y_157_);
lean_inc(v___y_156_);
lean_inc_ref(v___y_155_);
lean_inc(v___y_154_);
lean_inc_ref(v___y_153_);
v___x_162_ = lean_apply_7(v___x_4122__overap_161_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_, lean_box(0));
return v___x_162_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_152_ = stack[0].m_obj;
lean_object* v___y_153_ = stack[1].m_obj;
lean_object* v___y_154_ = stack[2].m_obj;
lean_object* v___y_155_ = stack[3].m_obj;
lean_object* v___y_156_ = stack[4].m_obj;
lean_object* v___y_157_ = stack[5].m_obj;
lean_object* v___y_158_ = stack[6].m_obj;
lean_object* v_res_163_;
v_res_163_ = l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2(v_msg_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
stack->m_obj
 = v_res_163_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___boxed(lean_object* v_msg_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2(v_msg_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_173_, lean_object* v_x_174_, lean_object* v_x_175_, lean_object* v_x_176_){
_start:
{
lean_object* v_ks_177_; lean_object* v_vs_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_204_; 
v_ks_177_ = lean_ctor_get(v_x_173_, 0);
v_vs_178_ = lean_ctor_get(v_x_173_, 1);
v_isSharedCheck_204_ = !lean_is_exclusive(v_x_173_);
if (v_isSharedCheck_204_ == 0)
{
v___x_180_ = v_x_173_;
v_isShared_181_ = v_isSharedCheck_204_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_vs_178_);
lean_inc(v_ks_177_);
lean_dec(v_x_173_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_204_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_182_; uint8_t v___x_183_; 
v___x_182_ = lean_array_get_size(v_ks_177_);
v___x_183_ = lean_nat_dec_lt(v_x_174_, v___x_182_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_187_; 
lean_dec(v_x_174_);
v___x_184_ = lean_array_push(v_ks_177_, v_x_175_);
v___x_185_ = lean_array_push(v_vs_178_, v_x_176_);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 1, v___x_185_);
lean_ctor_set(v___x_180_, 0, v___x_184_);
v___x_187_ = v___x_180_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_184_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v___x_185_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
else
{
lean_object* v_k_x27_189_; size_t v___x_190_; size_t v___x_191_; uint8_t v___x_192_; 
v_k_x27_189_ = lean_array_fget_borrowed(v_ks_177_, v_x_174_);
v___x_190_ = lean_ptr_addr(v_x_175_);
v___x_191_ = lean_ptr_addr(v_k_x27_189_);
v___x_192_ = lean_usize_dec_eq(v___x_190_, v___x_191_);
if (v___x_192_ == 0)
{
lean_object* v___x_194_; 
if (v_isShared_181_ == 0)
{
v___x_194_ = v___x_180_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_ks_177_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_vs_178_);
v___x_194_ = v_reuseFailAlloc_198_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = lean_unsigned_to_nat(1u);
v___x_196_ = lean_nat_add(v_x_174_, v___x_195_);
lean_dec(v_x_174_);
v_x_173_ = v___x_194_;
v_x_174_ = v___x_196_;
goto _start;
}
}
else
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_202_; 
v___x_199_ = lean_array_fset(v_ks_177_, v_x_174_, v_x_175_);
v___x_200_ = lean_array_fset(v_vs_178_, v_x_174_, v_x_176_);
lean_dec(v_x_174_);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 1, v___x_200_);
lean_ctor_set(v___x_180_, 0, v___x_199_);
v___x_202_ = v___x_180_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_199_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v___x_200_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(lean_object* v_n_205_, lean_object* v_k_206_, lean_object* v_v_207_){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_208_ = lean_unsigned_to_nat(0u);
v___x_209_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_n_205_, v___x_208_, v_k_206_, v_v_207_);
return v___x_209_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_210_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(lean_object* v_x_211_, size_t v_x_212_, size_t v_x_213_, lean_object* v_x_214_, lean_object* v_x_215_){
_start:
{
if (lean_obj_tag(v_x_211_) == 0)
{
lean_object* v_es_216_; size_t v___x_217_; size_t v___x_218_; lean_object* v_j_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v_es_216_ = lean_ctor_get(v_x_211_, 0);
v___x_217_ = ((size_t)31ULL);
v___x_218_ = lean_usize_land(v_x_212_, v___x_217_);
v_j_219_ = lean_usize_to_nat(v___x_218_);
v___x_220_ = lean_array_get_size(v_es_216_);
v___x_221_ = lean_nat_dec_lt(v_j_219_, v___x_220_);
if (v___x_221_ == 0)
{
lean_dec(v_j_219_);
lean_dec(v_x_215_);
lean_dec_ref(v_x_214_);
return v_x_211_;
}
else
{
lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_262_; 
lean_inc_ref(v_es_216_);
v_isSharedCheck_262_ = !lean_is_exclusive(v_x_211_);
if (v_isSharedCheck_262_ == 0)
{
lean_object* v_unused_263_; 
v_unused_263_ = lean_ctor_get(v_x_211_, 0);
lean_dec(v_unused_263_);
v___x_223_ = v_x_211_;
v_isShared_224_ = v_isSharedCheck_262_;
goto v_resetjp_222_;
}
else
{
lean_dec(v_x_211_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_262_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v_v_225_; lean_object* v___x_226_; lean_object* v_xs_x27_227_; lean_object* v___y_229_; 
v_v_225_ = lean_array_fget(v_es_216_, v_j_219_);
v___x_226_ = lean_box(0);
v_xs_x27_227_ = lean_array_fset(v_es_216_, v_j_219_, v___x_226_);
switch(lean_obj_tag(v_v_225_))
{
case 0:
{
lean_object* v_key_234_; lean_object* v_val_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_247_; 
v_key_234_ = lean_ctor_get(v_v_225_, 0);
v_val_235_ = lean_ctor_get(v_v_225_, 1);
v_isSharedCheck_247_ = !lean_is_exclusive(v_v_225_);
if (v_isSharedCheck_247_ == 0)
{
v___x_237_ = v_v_225_;
v_isShared_238_ = v_isSharedCheck_247_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_val_235_);
lean_inc(v_key_234_);
lean_dec(v_v_225_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_247_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
size_t v___x_239_; size_t v___x_240_; uint8_t v___x_241_; 
v___x_239_ = lean_ptr_addr(v_x_214_);
v___x_240_ = lean_ptr_addr(v_key_234_);
v___x_241_ = lean_usize_dec_eq(v___x_239_, v___x_240_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; lean_object* v___x_243_; 
lean_del_object(v___x_237_);
v___x_242_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_234_, v_val_235_, v_x_214_, v_x_215_);
v___x_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
v___y_229_ = v___x_243_;
goto v___jp_228_;
}
else
{
lean_object* v___x_245_; 
lean_dec(v_val_235_);
lean_dec(v_key_234_);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 1, v_x_215_);
lean_ctor_set(v___x_237_, 0, v_x_214_);
v___x_245_ = v___x_237_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_x_214_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v_x_215_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
v___y_229_ = v___x_245_;
goto v___jp_228_;
}
}
}
}
case 1:
{
lean_object* v_node_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_260_; 
v_node_248_ = lean_ctor_get(v_v_225_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v_v_225_);
if (v_isSharedCheck_260_ == 0)
{
v___x_250_ = v_v_225_;
v_isShared_251_ = v_isSharedCheck_260_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_node_248_);
lean_dec(v_v_225_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_260_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
size_t v___x_252_; size_t v___x_253_; size_t v___x_254_; size_t v___x_255_; lean_object* v___x_256_; lean_object* v___x_258_; 
v___x_252_ = ((size_t)5ULL);
v___x_253_ = lean_usize_shift_right(v_x_212_, v___x_252_);
v___x_254_ = ((size_t)1ULL);
v___x_255_ = lean_usize_add(v_x_213_, v___x_254_);
v___x_256_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_node_248_, v___x_253_, v___x_255_, v_x_214_, v_x_215_);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 0, v___x_256_);
v___x_258_ = v___x_250_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_256_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
v___y_229_ = v___x_258_;
goto v___jp_228_;
}
}
}
default: 
{
lean_object* v___x_261_; 
v___x_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_261_, 0, v_x_214_);
lean_ctor_set(v___x_261_, 1, v_x_215_);
v___y_229_ = v___x_261_;
goto v___jp_228_;
}
}
v___jp_228_:
{
lean_object* v___x_230_; lean_object* v___x_232_; 
v___x_230_ = lean_array_fset(v_xs_x27_227_, v_j_219_, v___y_229_);
lean_dec(v_j_219_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 0, v___x_230_);
v___x_232_ = v___x_223_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_230_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
}
else
{
lean_object* v_ks_264_; lean_object* v_vs_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_283_; 
v_ks_264_ = lean_ctor_get(v_x_211_, 0);
v_vs_265_ = lean_ctor_get(v_x_211_, 1);
v_isSharedCheck_283_ = !lean_is_exclusive(v_x_211_);
if (v_isSharedCheck_283_ == 0)
{
v___x_267_ = v_x_211_;
v_isShared_268_ = v_isSharedCheck_283_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_vs_265_);
lean_inc(v_ks_264_);
lean_dec(v_x_211_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_283_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_270_; 
if (v_isShared_268_ == 0)
{
v___x_270_ = v___x_267_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_ks_264_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v_vs_265_);
v___x_270_ = v_reuseFailAlloc_282_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
lean_object* v_newNode_271_; size_t v___x_272_; uint8_t v___x_273_; 
v_newNode_271_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(v___x_270_, v_x_214_, v_x_215_);
v___x_272_ = ((size_t)7ULL);
v___x_273_ = lean_usize_dec_le(v___x_272_, v_x_213_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; 
v___x_274_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_271_);
v___x_275_ = lean_unsigned_to_nat(4u);
v___x_276_ = lean_nat_dec_lt(v___x_274_, v___x_275_);
lean_dec(v___x_274_);
if (v___x_276_ == 0)
{
lean_object* v_ks_277_; lean_object* v_vs_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v_ks_277_ = lean_ctor_get(v_newNode_271_, 0);
lean_inc_ref(v_ks_277_);
v_vs_278_ = lean_ctor_get(v_newNode_271_, 1);
lean_inc_ref(v_vs_278_);
lean_dec_ref(v_newNode_271_);
v___x_279_ = lean_unsigned_to_nat(0u);
v___x_280_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0);
v___x_281_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(v_x_213_, v_ks_277_, v_vs_278_, v___x_279_, v___x_280_);
lean_dec_ref(v_vs_278_);
lean_dec_ref(v_ks_277_);
return v___x_281_;
}
else
{
return v_newNode_271_;
}
}
else
{
return v_newNode_271_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_211_ = stack[0].m_obj;
size_t v_x_212_ = stack[1].m_num;
size_t v_x_213_ = stack[2].m_num;
lean_object* v_x_214_ = stack[3].m_obj;
lean_object* v_x_215_ = stack[4].m_obj;
lean_object* v_res_284_;
v_res_284_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_211_, v_x_212_, v_x_213_, v_x_214_, v_x_215_);
stack->m_obj
 = v_res_284_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(size_t v_depth_285_, lean_object* v_keys_286_, lean_object* v_vals_287_, lean_object* v_i_288_, lean_object* v_entries_289_){
_start:
{
lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_290_ = lean_array_get_size(v_keys_286_);
v___x_291_ = lean_nat_dec_lt(v_i_288_, v___x_290_);
if (v___x_291_ == 0)
{
lean_dec(v_i_288_);
return v_entries_289_;
}
else
{
lean_object* v_k_292_; lean_object* v_v_293_; size_t v___x_294_; size_t v___x_295_; size_t v___x_296_; uint64_t v___x_297_; size_t v_h_298_; size_t v___x_299_; lean_object* v___x_300_; size_t v___x_301_; size_t v___x_302_; size_t v___x_303_; size_t v_h_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v_k_292_ = lean_array_fget_borrowed(v_keys_286_, v_i_288_);
v_v_293_ = lean_array_fget_borrowed(v_vals_287_, v_i_288_);
v___x_294_ = lean_ptr_addr(v_k_292_);
v___x_295_ = ((size_t)3ULL);
v___x_296_ = lean_usize_shift_right(v___x_294_, v___x_295_);
v___x_297_ = lean_usize_to_uint64(v___x_296_);
v_h_298_ = lean_uint64_to_usize(v___x_297_);
v___x_299_ = ((size_t)5ULL);
v___x_300_ = lean_unsigned_to_nat(1u);
v___x_301_ = ((size_t)1ULL);
v___x_302_ = lean_usize_sub(v_depth_285_, v___x_301_);
v___x_303_ = lean_usize_mul(v___x_299_, v___x_302_);
v_h_304_ = lean_usize_shift_right(v_h_298_, v___x_303_);
v___x_305_ = lean_nat_add(v_i_288_, v___x_300_);
lean_dec(v_i_288_);
lean_inc(v_v_293_);
lean_inc(v_k_292_);
v___x_306_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_entries_289_, v_h_304_, v_depth_285_, v_k_292_, v_v_293_);
v_i_288_ = v___x_305_;
v_entries_289_ = v___x_306_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_285_ = stack[0].m_num;
lean_object* v_keys_286_ = stack[1].m_obj;
lean_object* v_vals_287_ = stack[2].m_obj;
lean_object* v_i_288_ = stack[3].m_obj;
lean_object* v_entries_289_ = stack[4].m_obj;
lean_object* v_res_308_;
v_res_308_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(v_depth_285_, v_keys_286_, v_vals_287_, v_i_288_, v_entries_289_);
stack->m_obj
 = v_res_308_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_309_, lean_object* v_keys_310_, lean_object* v_vals_311_, lean_object* v_i_312_, lean_object* v_entries_313_){
_start:
{
size_t v_depth_boxed_314_; lean_object* v_res_315_; 
v_depth_boxed_314_ = lean_unbox_usize(v_depth_309_);
lean_dec(v_depth_309_);
v_res_315_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(v_depth_boxed_314_, v_keys_310_, v_vals_311_, v_i_312_, v_entries_313_);
lean_dec_ref(v_vals_311_);
lean_dec_ref(v_keys_310_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_316_, lean_object* v_x_317_, lean_object* v_x_318_, lean_object* v_x_319_, lean_object* v_x_320_){
_start:
{
size_t v_x_4727__boxed_321_; size_t v_x_4728__boxed_322_; lean_object* v_res_323_; 
v_x_4727__boxed_321_ = lean_unbox_usize(v_x_317_);
lean_dec(v_x_317_);
v_x_4728__boxed_322_ = lean_unbox_usize(v_x_318_);
lean_dec(v_x_318_);
v_res_323_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_316_, v_x_4727__boxed_321_, v_x_4728__boxed_322_, v_x_319_, v_x_320_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(lean_object* v_x_324_, lean_object* v_x_325_, lean_object* v_x_326_){
_start:
{
size_t v___x_327_; size_t v___x_328_; size_t v___x_329_; uint64_t v___x_330_; size_t v___x_331_; size_t v___x_332_; lean_object* v___x_333_; 
v___x_327_ = lean_ptr_addr(v_x_325_);
v___x_328_ = ((size_t)3ULL);
v___x_329_ = lean_usize_shift_right(v___x_327_, v___x_328_);
v___x_330_ = lean_usize_to_uint64(v___x_329_);
v___x_331_ = lean_uint64_to_usize(v___x_330_);
v___x_332_ = ((size_t)1ULL);
v___x_333_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_324_, v___x_331_, v___x_332_, v_x_325_, v_x_326_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(lean_object* v_keys_334_, lean_object* v_vals_335_, lean_object* v_i_336_, lean_object* v_k_337_){
_start:
{
lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_338_ = lean_array_get_size(v_keys_334_);
v___x_339_ = lean_nat_dec_lt(v_i_336_, v___x_338_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; 
lean_dec(v_i_336_);
v___x_340_ = lean_box(0);
return v___x_340_;
}
else
{
lean_object* v_k_x27_341_; size_t v___x_342_; size_t v___x_343_; uint8_t v___x_344_; 
v_k_x27_341_ = lean_array_fget_borrowed(v_keys_334_, v_i_336_);
v___x_342_ = lean_ptr_addr(v_k_337_);
v___x_343_ = lean_ptr_addr(v_k_x27_341_);
v___x_344_ = lean_usize_dec_eq(v___x_342_, v___x_343_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = lean_unsigned_to_nat(1u);
v___x_346_ = lean_nat_add(v_i_336_, v___x_345_);
lean_dec(v_i_336_);
v_i_336_ = v___x_346_;
goto _start;
}
else
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_array_fget_borrowed(v_vals_335_, v_i_336_);
lean_dec(v_i_336_);
lean_inc(v___x_348_);
v___x_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
return v___x_349_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_keys_350_, lean_object* v_vals_351_, lean_object* v_i_352_, lean_object* v_k_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_keys_350_, v_vals_351_, v_i_352_, v_k_353_);
lean_dec_ref(v_k_353_);
lean_dec_ref(v_vals_351_);
lean_dec_ref(v_keys_350_);
return v_res_354_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(lean_object* v_x_355_, size_t v_x_356_, lean_object* v_x_357_){
_start:
{
if (lean_obj_tag(v_x_355_) == 0)
{
lean_object* v_es_358_; lean_object* v___x_359_; size_t v___x_360_; size_t v___x_361_; lean_object* v_j_362_; lean_object* v___x_363_; 
v_es_358_ = lean_ctor_get(v_x_355_, 0);
v___x_359_ = lean_box(2);
v___x_360_ = ((size_t)31ULL);
v___x_361_ = lean_usize_land(v_x_356_, v___x_360_);
v_j_362_ = lean_usize_to_nat(v___x_361_);
v___x_363_ = lean_array_get_borrowed(v___x_359_, v_es_358_, v_j_362_);
lean_dec(v_j_362_);
switch(lean_obj_tag(v___x_363_))
{
case 0:
{
lean_object* v_key_364_; lean_object* v_val_365_; size_t v___x_366_; size_t v___x_367_; uint8_t v___x_368_; 
v_key_364_ = lean_ctor_get(v___x_363_, 0);
v_val_365_ = lean_ctor_get(v___x_363_, 1);
v___x_366_ = lean_ptr_addr(v_x_357_);
v___x_367_ = lean_ptr_addr(v_key_364_);
v___x_368_ = lean_usize_dec_eq(v___x_366_, v___x_367_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; 
v___x_369_ = lean_box(0);
return v___x_369_;
}
else
{
lean_object* v___x_370_; 
lean_inc(v_val_365_);
v___x_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_370_, 0, v_val_365_);
return v___x_370_;
}
}
case 1:
{
lean_object* v_node_371_; size_t v___x_372_; size_t v___x_373_; 
v_node_371_ = lean_ctor_get(v___x_363_, 0);
v___x_372_ = ((size_t)5ULL);
v___x_373_ = lean_usize_shift_right(v_x_356_, v___x_372_);
v_x_355_ = v_node_371_;
v_x_356_ = v___x_373_;
goto _start;
}
default: 
{
lean_object* v___x_375_; 
v___x_375_ = lean_box(0);
return v___x_375_;
}
}
}
else
{
lean_object* v_ks_376_; lean_object* v_vs_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v_ks_376_ = lean_ctor_get(v_x_355_, 0);
v_vs_377_ = lean_ctor_get(v_x_355_, 1);
v___x_378_ = lean_unsigned_to_nat(0u);
v___x_379_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_ks_376_, v_vs_377_, v___x_378_, v_x_357_);
return v___x_379_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_355_ = stack[0].m_obj;
size_t v_x_356_ = stack[1].m_num;
lean_object* v_x_357_ = stack[2].m_obj;
lean_object* v_res_380_;
v_res_380_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_355_, v_x_356_, v_x_357_);
stack->m_obj
 = v_res_380_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_x_381_, lean_object* v_x_382_, lean_object* v_x_383_){
_start:
{
size_t v_x_5038__boxed_384_; lean_object* v_res_385_; 
v_x_5038__boxed_384_ = lean_unbox_usize(v_x_382_);
lean_dec(v_x_382_);
v_res_385_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_381_, v_x_5038__boxed_384_, v_x_383_);
lean_dec_ref(v_x_383_);
lean_dec_ref(v_x_381_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(lean_object* v_x_386_, lean_object* v_x_387_){
_start:
{
size_t v___x_388_; size_t v___x_389_; size_t v___x_390_; uint64_t v___x_391_; size_t v___x_392_; lean_object* v___x_393_; 
v___x_388_ = lean_ptr_addr(v_x_387_);
v___x_389_ = ((size_t)3ULL);
v___x_390_ = lean_usize_shift_right(v___x_388_, v___x_389_);
v___x_391_ = lean_usize_to_uint64(v___x_390_);
v___x_392_ = lean_uint64_to_usize(v___x_391_);
v___x_393_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_386_, v___x_392_, v_x_387_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg___boxed(lean_object* v_x_394_, lean_object* v_x_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_x_394_, v_x_395_);
lean_dec_ref(v_x_395_);
lean_dec_ref(v_x_394_);
return v_res_396_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3(void){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_400_ = ((lean_object*)(l_Lean_Meta_Sym_getMaxFVar_x3f___closed__2));
v___x_401_ = lean_unsigned_to_nat(37u);
v___x_402_ = lean_unsigned_to_nat(52u);
v___x_403_ = ((lean_object*)(l_Lean_Meta_Sym_getMaxFVar_x3f___closed__1));
v___x_404_ = ((lean_object*)(l_Lean_Meta_Sym_getMaxFVar_x3f___closed__0));
v___x_405_ = l_mkPanicMessageWithDecl(v___x_404_, v___x_403_, v___x_402_, v___x_401_, v___x_400_);
return v___x_405_;
}
}
lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f(lean_object* v_e_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_){
_start:
{
lean_object* v___y_415_; lean_object* v_a_448_; lean_object* v___y_474_; lean_object* v___y_475_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; uint8_t v___y_516_; lean_object* v_d_536_; lean_object* v_b_537_; lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v___y_540_; lean_object* v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_547_; 
switch(lean_obj_tag(v_e_406_))
{
case 1:
{
lean_object* v_fvarId_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v_fvarId_579_ = lean_ctor_get(v_e_406_, 0);
lean_inc(v_fvarId_579_);
lean_dec_ref_known(v_e_406_, 1);
v___x_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_580_, 0, v_fvarId_579_);
v___x_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
return v___x_581_;
}
case 2:
{
lean_object* v_mvarId_582_; uint8_t v___y_584_; uint8_t v___x_625_; 
v_mvarId_582_ = lean_ctor_get(v_e_406_, 0);
v___x_625_ = l_Lean_Expr_hasFVar(v_e_406_);
if (v___x_625_ == 0)
{
uint8_t v___x_626_; 
v___x_626_ = l_Lean_Expr_hasMVar(v_e_406_);
v___y_584_ = v___x_626_;
goto v___jp_583_;
}
else
{
v___y_584_ = v___x_625_;
goto v___jp_583_;
}
v___jp_583_:
{
if (v___y_584_ == 0)
{
lean_object* v___x_585_; lean_object* v___x_586_; 
lean_dec_ref_known(v_e_406_, 1);
v___x_585_ = lean_box(0);
v___x_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
return v___x_586_;
}
else
{
lean_object* v___x_587_; lean_object* v_maxFVar_588_; lean_object* v___x_589_; 
v___x_587_ = lean_st_ref_get(v_a_408_);
v_maxFVar_588_ = lean_ctor_get(v___x_587_, 1);
lean_inc_ref(v_maxFVar_588_);
lean_dec(v___x_587_);
v___x_589_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_588_, v_e_406_);
lean_dec_ref(v_maxFVar_588_);
if (lean_obj_tag(v___x_589_) == 1)
{
lean_object* v_val_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
lean_dec_ref_known(v_e_406_, 1);
v_val_590_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v___x_589_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_val_590_);
lean_dec(v___x_589_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
lean_ctor_set_tag(v___x_592_, 0);
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_val_590_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
else
{
lean_object* v___x_598_; 
lean_dec(v___x_589_);
lean_inc(v_mvarId_582_);
v___x_598_ = l_Lean_MVarId_getDecl(v_mvarId_582_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v_a_599_; lean_object* v_lctx_600_; lean_object* v_decls_601_; uint8_t v___x_602_; 
v_a_599_ = lean_ctor_get(v___x_598_, 0);
lean_inc(v_a_599_);
lean_dec_ref_known(v___x_598_, 1);
v_lctx_600_ = lean_ctor_get(v_a_599_, 1);
lean_inc_ref(v_lctx_600_);
lean_dec(v_a_599_);
v_decls_601_ = lean_ctor_get(v_lctx_600_, 1);
v___x_602_ = l_Lean_PersistentArray_isEmpty___redArg(v_decls_601_);
if (v___x_602_ == 0)
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_LocalContext_lastDecl(v_lctx_600_);
lean_dec_ref(v_lctx_600_);
if (lean_obj_tag(v___x_603_) == 1)
{
lean_object* v_val_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_612_; 
v_val_604_ = lean_ctor_get(v___x_603_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_612_ == 0)
{
v___x_606_ = v___x_603_;
v_isShared_607_ = v_isSharedCheck_612_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_val_604_);
lean_dec(v___x_603_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_612_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; lean_object* v___x_610_; 
v___x_608_ = l_Lean_LocalDecl_fvarId(v_val_604_);
lean_dec(v_val_604_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 0, v___x_608_);
v___x_610_ = v___x_606_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_608_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
v_a_448_ = v___x_610_;
goto v___jp_447_;
}
}
}
else
{
lean_object* v___x_613_; lean_object* v___x_614_; 
lean_dec(v___x_603_);
v___x_613_ = lean_obj_once(&l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3, &l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3_once, _init_l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3);
v___x_614_ = l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2(v___x_613_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_a_615_);
lean_dec_ref_known(v___x_614_, 1);
v_a_448_ = v_a_615_;
goto v___jp_447_;
}
else
{
lean_dec_ref_known(v_e_406_, 1);
return v___x_614_;
}
}
}
else
{
lean_object* v___x_616_; 
lean_dec_ref(v_lctx_600_);
v___x_616_ = lean_box(0);
v_a_448_ = v___x_616_;
goto v___jp_447_;
}
}
else
{
lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_624_; 
lean_dec_ref_known(v_e_406_, 1);
v_a_617_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_624_ == 0)
{
v___x_619_ = v___x_598_;
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_dec(v___x_598_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_a_617_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
}
}
}
}
case 5:
{
lean_object* v_fn_627_; lean_object* v_arg_628_; uint8_t v___y_630_; uint8_t v___x_649_; 
v_fn_627_ = lean_ctor_get(v_e_406_, 0);
v_arg_628_ = lean_ctor_get(v_e_406_, 1);
v___x_649_ = l_Lean_Expr_hasFVar(v_e_406_);
if (v___x_649_ == 0)
{
uint8_t v___x_650_; 
v___x_650_ = l_Lean_Expr_hasMVar(v_e_406_);
v___y_630_ = v___x_650_;
goto v___jp_629_;
}
else
{
v___y_630_ = v___x_649_;
goto v___jp_629_;
}
v___jp_629_:
{
if (v___y_630_ == 0)
{
lean_object* v___x_631_; lean_object* v___x_632_; 
lean_dec_ref_known(v_e_406_, 2);
v___x_631_ = lean_box(0);
v___x_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
return v___x_632_;
}
else
{
lean_object* v___x_633_; lean_object* v_maxFVar_634_; lean_object* v___x_635_; 
v___x_633_ = lean_st_ref_get(v_a_408_);
v_maxFVar_634_ = lean_ctor_get(v___x_633_, 1);
lean_inc_ref(v_maxFVar_634_);
lean_dec(v___x_633_);
v___x_635_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_634_, v_e_406_);
lean_dec_ref(v_maxFVar_634_);
if (lean_obj_tag(v___x_635_) == 1)
{
lean_object* v_val_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_643_; 
lean_dec_ref_known(v_e_406_, 2);
v_val_636_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_643_ == 0)
{
v___x_638_ = v___x_635_;
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_val_636_);
lean_dec(v___x_635_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_641_; 
if (v_isShared_639_ == 0)
{
lean_ctor_set_tag(v___x_638_, 0);
v___x_641_ = v___x_638_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_val_636_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
else
{
lean_object* v___x_644_; 
lean_dec(v___x_635_);
lean_inc_ref(v_fn_627_);
v___x_644_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_fn_627_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; lean_object* v___x_646_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_a_645_);
lean_dec_ref_known(v___x_644_, 1);
lean_inc_ref(v_arg_628_);
v___x_646_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_arg_628_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; lean_object* v___x_648_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_a_647_);
lean_dec_ref_known(v___x_646_, 1);
v___x_648_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_645_, v_a_647_, v_a_409_, v_a_411_, v_a_412_);
v___y_547_ = v___x_648_;
goto v___jp_546_;
}
else
{
lean_dec(v_a_645_);
v___y_547_ = v___x_646_;
goto v___jp_546_;
}
}
else
{
v___y_547_ = v___x_644_;
goto v___jp_546_;
}
}
}
}
}
case 6:
{
lean_object* v_binderType_651_; lean_object* v_body_652_; 
v_binderType_651_ = lean_ctor_get(v_e_406_, 1);
v_body_652_ = lean_ctor_get(v_e_406_, 2);
lean_inc_ref(v_body_652_);
lean_inc_ref(v_binderType_651_);
v_d_536_ = v_binderType_651_;
v_b_537_ = v_body_652_;
v___y_538_ = v_a_407_;
v___y_539_ = v_a_408_;
v___y_540_ = v_a_409_;
v___y_541_ = v_a_410_;
v___y_542_ = v_a_411_;
v___y_543_ = v_a_412_;
goto v___jp_535_;
}
case 7:
{
lean_object* v_binderType_653_; lean_object* v_body_654_; 
v_binderType_653_ = lean_ctor_get(v_e_406_, 1);
v_body_654_ = lean_ctor_get(v_e_406_, 2);
lean_inc_ref(v_body_654_);
lean_inc_ref(v_binderType_653_);
v_d_536_ = v_binderType_653_;
v_b_537_ = v_body_654_;
v___y_538_ = v_a_407_;
v___y_539_ = v_a_408_;
v___y_540_ = v_a_409_;
v___y_541_ = v_a_410_;
v___y_542_ = v_a_411_;
v___y_543_ = v_a_412_;
goto v___jp_535_;
}
case 8:
{
lean_object* v_type_655_; lean_object* v_value_656_; lean_object* v_body_657_; uint8_t v___y_659_; uint8_t v___x_682_; 
v_type_655_ = lean_ctor_get(v_e_406_, 1);
v_value_656_ = lean_ctor_get(v_e_406_, 2);
v_body_657_ = lean_ctor_get(v_e_406_, 3);
v___x_682_ = l_Lean_Expr_hasFVar(v_e_406_);
if (v___x_682_ == 0)
{
uint8_t v___x_683_; 
v___x_683_ = l_Lean_Expr_hasMVar(v_e_406_);
v___y_659_ = v___x_683_;
goto v___jp_658_;
}
else
{
v___y_659_ = v___x_682_;
goto v___jp_658_;
}
v___jp_658_:
{
if (v___y_659_ == 0)
{
lean_object* v___x_660_; lean_object* v___x_661_; 
lean_dec_ref_known(v_e_406_, 4);
v___x_660_ = lean_box(0);
v___x_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
return v___x_661_;
}
else
{
lean_object* v___x_662_; lean_object* v_maxFVar_663_; lean_object* v___x_664_; 
v___x_662_ = lean_st_ref_get(v_a_408_);
v_maxFVar_663_ = lean_ctor_get(v___x_662_, 1);
lean_inc_ref(v_maxFVar_663_);
lean_dec(v___x_662_);
v___x_664_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_663_, v_e_406_);
lean_dec_ref(v_maxFVar_663_);
if (lean_obj_tag(v___x_664_) == 1)
{
lean_object* v_val_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
lean_dec_ref_known(v_e_406_, 4);
v_val_665_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v___x_664_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_val_665_);
lean_dec(v___x_664_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
lean_ctor_set_tag(v___x_667_, 0);
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_val_665_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
else
{
lean_object* v___x_673_; 
lean_dec(v___x_664_);
lean_inc_ref(v_type_655_);
v___x_673_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_type_655_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; lean_object* v___x_675_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_a_674_);
lean_dec_ref_known(v___x_673_, 1);
lean_inc_ref(v_value_656_);
v___x_675_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_value_656_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; lean_object* v___x_677_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_a_676_);
lean_dec_ref_known(v___x_675_, 1);
v___x_677_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_674_, v_a_676_, v_a_409_, v_a_411_, v_a_412_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; lean_object* v___x_679_; 
v_a_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_a_678_);
lean_dec_ref_known(v___x_677_, 1);
lean_inc_ref(v_body_657_);
v___x_679_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_body_657_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v_a_680_; lean_object* v___x_681_; 
v_a_680_ = lean_ctor_get(v___x_679_, 0);
lean_inc(v_a_680_);
lean_dec_ref_known(v___x_679_, 1);
v___x_681_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_678_, v_a_680_, v_a_409_, v_a_411_, v_a_412_);
v___y_415_ = v___x_681_;
goto v___jp_414_;
}
else
{
lean_dec(v_a_678_);
v___y_415_ = v___x_679_;
goto v___jp_414_;
}
}
else
{
v___y_415_ = v___x_677_;
goto v___jp_414_;
}
}
else
{
lean_dec(v_a_674_);
v___y_415_ = v___x_675_;
goto v___jp_414_;
}
}
else
{
v___y_415_ = v___x_673_;
goto v___jp_414_;
}
}
}
}
}
case 10:
{
lean_object* v_expr_684_; uint8_t v___y_686_; uint8_t v___x_732_; 
v_expr_684_ = lean_ctor_get(v_e_406_, 1);
lean_inc_ref(v_expr_684_);
lean_dec_ref_known(v_e_406_, 2);
v___x_732_ = l_Lean_Expr_hasFVar(v_expr_684_);
if (v___x_732_ == 0)
{
uint8_t v___x_733_; 
v___x_733_ = l_Lean_Expr_hasMVar(v_expr_684_);
v___y_686_ = v___x_733_;
goto v___jp_685_;
}
else
{
v___y_686_ = v___x_732_;
goto v___jp_685_;
}
v___jp_685_:
{
if (v___y_686_ == 0)
{
lean_object* v___x_687_; lean_object* v___x_688_; 
lean_dec_ref(v_expr_684_);
v___x_687_ = lean_box(0);
v___x_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
return v___x_688_;
}
else
{
lean_object* v___x_689_; lean_object* v_maxFVar_690_; lean_object* v___x_691_; 
v___x_689_ = lean_st_ref_get(v_a_408_);
v_maxFVar_690_ = lean_ctor_get(v___x_689_, 1);
lean_inc_ref(v_maxFVar_690_);
lean_dec(v___x_689_);
v___x_691_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_690_, v_expr_684_);
lean_dec_ref(v_maxFVar_690_);
if (lean_obj_tag(v___x_691_) == 1)
{
lean_object* v_val_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_699_; 
lean_dec_ref(v_expr_684_);
v_val_692_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_699_ == 0)
{
v___x_694_ = v___x_691_;
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_val_692_);
lean_dec(v___x_691_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
lean_ctor_set_tag(v___x_694_, 0);
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_val_692_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
else
{
lean_object* v___x_700_; 
lean_dec(v___x_691_);
lean_inc_ref(v_expr_684_);
v___x_700_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_expr_684_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_731_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_731_ == 0)
{
v___x_703_ = v___x_700_;
v_isShared_704_ = v_isSharedCheck_731_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_700_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_731_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_705_; lean_object* v_share_706_; lean_object* v_maxFVar_707_; lean_object* v_proofInstInfo_708_; lean_object* v_proofInstInfoFVar_709_; lean_object* v_inferType_710_; lean_object* v_getLevel_711_; lean_object* v_congrInfo_712_; lean_object* v_defEqI_713_; lean_object* v_extensions_714_; lean_object* v_issues_715_; lean_object* v_canon_716_; lean_object* v_instanceOverrides_717_; uint8_t v_debug_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_730_; 
v___x_705_ = lean_st_ref_take(v_a_408_);
v_share_706_ = lean_ctor_get(v___x_705_, 0);
v_maxFVar_707_ = lean_ctor_get(v___x_705_, 1);
v_proofInstInfo_708_ = lean_ctor_get(v___x_705_, 2);
v_proofInstInfoFVar_709_ = lean_ctor_get(v___x_705_, 3);
v_inferType_710_ = lean_ctor_get(v___x_705_, 4);
v_getLevel_711_ = lean_ctor_get(v___x_705_, 5);
v_congrInfo_712_ = lean_ctor_get(v___x_705_, 6);
v_defEqI_713_ = lean_ctor_get(v___x_705_, 7);
v_extensions_714_ = lean_ctor_get(v___x_705_, 8);
v_issues_715_ = lean_ctor_get(v___x_705_, 9);
v_canon_716_ = lean_ctor_get(v___x_705_, 10);
v_instanceOverrides_717_ = lean_ctor_get(v___x_705_, 11);
v_debug_718_ = lean_ctor_get_uint8(v___x_705_, sizeof(void*)*12);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_730_ == 0)
{
v___x_720_ = v___x_705_;
v_isShared_721_ = v_isSharedCheck_730_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_instanceOverrides_717_);
lean_inc(v_canon_716_);
lean_inc(v_issues_715_);
lean_inc(v_extensions_714_);
lean_inc(v_defEqI_713_);
lean_inc(v_congrInfo_712_);
lean_inc(v_getLevel_711_);
lean_inc(v_inferType_710_);
lean_inc(v_proofInstInfoFVar_709_);
lean_inc(v_proofInstInfo_708_);
lean_inc(v_maxFVar_707_);
lean_inc(v_share_706_);
lean_dec(v___x_705_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_730_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_722_; lean_object* v___x_724_; 
lean_inc(v_a_701_);
v___x_722_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_707_, v_expr_684_, v_a_701_);
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 1, v___x_722_);
v___x_724_ = v___x_720_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_share_706_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v___x_722_);
lean_ctor_set(v_reuseFailAlloc_729_, 2, v_proofInstInfo_708_);
lean_ctor_set(v_reuseFailAlloc_729_, 3, v_proofInstInfoFVar_709_);
lean_ctor_set(v_reuseFailAlloc_729_, 4, v_inferType_710_);
lean_ctor_set(v_reuseFailAlloc_729_, 5, v_getLevel_711_);
lean_ctor_set(v_reuseFailAlloc_729_, 6, v_congrInfo_712_);
lean_ctor_set(v_reuseFailAlloc_729_, 7, v_defEqI_713_);
lean_ctor_set(v_reuseFailAlloc_729_, 8, v_extensions_714_);
lean_ctor_set(v_reuseFailAlloc_729_, 9, v_issues_715_);
lean_ctor_set(v_reuseFailAlloc_729_, 10, v_canon_716_);
lean_ctor_set(v_reuseFailAlloc_729_, 11, v_instanceOverrides_717_);
lean_ctor_set_uint8(v_reuseFailAlloc_729_, sizeof(void*)*12, v_debug_718_);
v___x_724_ = v_reuseFailAlloc_729_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
lean_object* v___x_725_; lean_object* v___x_727_; 
v___x_725_ = lean_st_ref_put(v_a_408_, v___x_724_);
if (v_isShared_704_ == 0)
{
v___x_727_ = v___x_703_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_701_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
}
else
{
lean_dec_ref(v_expr_684_);
return v___x_700_;
}
}
}
}
}
case 11:
{
lean_object* v_struct_734_; uint8_t v___y_736_; uint8_t v___x_782_; 
v_struct_734_ = lean_ctor_get(v_e_406_, 2);
v___x_782_ = l_Lean_Expr_hasFVar(v_e_406_);
if (v___x_782_ == 0)
{
uint8_t v___x_783_; 
v___x_783_ = l_Lean_Expr_hasMVar(v_e_406_);
v___y_736_ = v___x_783_;
goto v___jp_735_;
}
else
{
v___y_736_ = v___x_782_;
goto v___jp_735_;
}
v___jp_735_:
{
if (v___y_736_ == 0)
{
lean_object* v___x_737_; lean_object* v___x_738_; 
lean_dec_ref_known(v_e_406_, 3);
v___x_737_ = lean_box(0);
v___x_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
return v___x_738_;
}
else
{
lean_object* v___x_739_; lean_object* v_maxFVar_740_; lean_object* v___x_741_; 
v___x_739_ = lean_st_ref_get(v_a_408_);
v_maxFVar_740_ = lean_ctor_get(v___x_739_, 1);
lean_inc_ref(v_maxFVar_740_);
lean_dec(v___x_739_);
v___x_741_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_740_, v_e_406_);
lean_dec_ref(v_maxFVar_740_);
if (lean_obj_tag(v___x_741_) == 1)
{
lean_object* v_val_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_749_; 
lean_dec_ref_known(v_e_406_, 3);
v_val_742_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_749_ == 0)
{
v___x_744_ = v___x_741_;
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_val_742_);
lean_dec(v___x_741_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_747_; 
if (v_isShared_745_ == 0)
{
lean_ctor_set_tag(v___x_744_, 0);
v___x_747_ = v___x_744_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_val_742_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
else
{
lean_object* v___x_750_; 
lean_dec(v___x_741_);
lean_inc_ref(v_struct_734_);
v___x_750_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_struct_734_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_781_; 
v_a_751_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_781_ == 0)
{
v___x_753_ = v___x_750_;
v_isShared_754_ = v_isSharedCheck_781_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_750_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_781_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_755_; lean_object* v_share_756_; lean_object* v_maxFVar_757_; lean_object* v_proofInstInfo_758_; lean_object* v_proofInstInfoFVar_759_; lean_object* v_inferType_760_; lean_object* v_getLevel_761_; lean_object* v_congrInfo_762_; lean_object* v_defEqI_763_; lean_object* v_extensions_764_; lean_object* v_issues_765_; lean_object* v_canon_766_; lean_object* v_instanceOverrides_767_; uint8_t v_debug_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_780_; 
v___x_755_ = lean_st_ref_take(v_a_408_);
v_share_756_ = lean_ctor_get(v___x_755_, 0);
v_maxFVar_757_ = lean_ctor_get(v___x_755_, 1);
v_proofInstInfo_758_ = lean_ctor_get(v___x_755_, 2);
v_proofInstInfoFVar_759_ = lean_ctor_get(v___x_755_, 3);
v_inferType_760_ = lean_ctor_get(v___x_755_, 4);
v_getLevel_761_ = lean_ctor_get(v___x_755_, 5);
v_congrInfo_762_ = lean_ctor_get(v___x_755_, 6);
v_defEqI_763_ = lean_ctor_get(v___x_755_, 7);
v_extensions_764_ = lean_ctor_get(v___x_755_, 8);
v_issues_765_ = lean_ctor_get(v___x_755_, 9);
v_canon_766_ = lean_ctor_get(v___x_755_, 10);
v_instanceOverrides_767_ = lean_ctor_get(v___x_755_, 11);
v_debug_768_ = lean_ctor_get_uint8(v___x_755_, sizeof(void*)*12);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_780_ == 0)
{
v___x_770_ = v___x_755_;
v_isShared_771_ = v_isSharedCheck_780_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_instanceOverrides_767_);
lean_inc(v_canon_766_);
lean_inc(v_issues_765_);
lean_inc(v_extensions_764_);
lean_inc(v_defEqI_763_);
lean_inc(v_congrInfo_762_);
lean_inc(v_getLevel_761_);
lean_inc(v_inferType_760_);
lean_inc(v_proofInstInfoFVar_759_);
lean_inc(v_proofInstInfo_758_);
lean_inc(v_maxFVar_757_);
lean_inc(v_share_756_);
lean_dec(v___x_755_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_780_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_772_; lean_object* v___x_774_; 
lean_inc(v_a_751_);
v___x_772_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_757_, v_e_406_, v_a_751_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 1, v___x_772_);
v___x_774_ = v___x_770_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_share_756_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v___x_772_);
lean_ctor_set(v_reuseFailAlloc_779_, 2, v_proofInstInfo_758_);
lean_ctor_set(v_reuseFailAlloc_779_, 3, v_proofInstInfoFVar_759_);
lean_ctor_set(v_reuseFailAlloc_779_, 4, v_inferType_760_);
lean_ctor_set(v_reuseFailAlloc_779_, 5, v_getLevel_761_);
lean_ctor_set(v_reuseFailAlloc_779_, 6, v_congrInfo_762_);
lean_ctor_set(v_reuseFailAlloc_779_, 7, v_defEqI_763_);
lean_ctor_set(v_reuseFailAlloc_779_, 8, v_extensions_764_);
lean_ctor_set(v_reuseFailAlloc_779_, 9, v_issues_765_);
lean_ctor_set(v_reuseFailAlloc_779_, 10, v_canon_766_);
lean_ctor_set(v_reuseFailAlloc_779_, 11, v_instanceOverrides_767_);
lean_ctor_set_uint8(v_reuseFailAlloc_779_, sizeof(void*)*12, v_debug_768_);
v___x_774_ = v_reuseFailAlloc_779_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
lean_object* v___x_775_; lean_object* v___x_777_; 
v___x_775_ = lean_st_ref_put(v_a_408_, v___x_774_);
if (v_isShared_754_ == 0)
{
v___x_777_ = v___x_753_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_751_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_406_, 3);
return v___x_750_;
}
}
}
}
}
default: 
{
lean_object* v___x_784_; lean_object* v___x_785_; 
lean_dec_ref(v_e_406_);
v___x_784_ = lean_box(0);
v___x_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_785_, 0, v___x_784_);
return v___x_785_;
}
}
v___jp_414_:
{
if (lean_obj_tag(v___y_415_) == 0)
{
lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_446_; 
v_a_416_ = lean_ctor_get(v___y_415_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___y_415_);
if (v_isSharedCheck_446_ == 0)
{
v___x_418_ = v___y_415_;
v_isShared_419_ = v_isSharedCheck_446_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_dec(v___y_415_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_446_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_420_; lean_object* v_share_421_; lean_object* v_maxFVar_422_; lean_object* v_proofInstInfo_423_; lean_object* v_proofInstInfoFVar_424_; lean_object* v_inferType_425_; lean_object* v_getLevel_426_; lean_object* v_congrInfo_427_; lean_object* v_defEqI_428_; lean_object* v_extensions_429_; lean_object* v_issues_430_; lean_object* v_canon_431_; lean_object* v_instanceOverrides_432_; uint8_t v_debug_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_445_; 
v___x_420_ = lean_st_ref_take(v_a_408_);
v_share_421_ = lean_ctor_get(v___x_420_, 0);
v_maxFVar_422_ = lean_ctor_get(v___x_420_, 1);
v_proofInstInfo_423_ = lean_ctor_get(v___x_420_, 2);
v_proofInstInfoFVar_424_ = lean_ctor_get(v___x_420_, 3);
v_inferType_425_ = lean_ctor_get(v___x_420_, 4);
v_getLevel_426_ = lean_ctor_get(v___x_420_, 5);
v_congrInfo_427_ = lean_ctor_get(v___x_420_, 6);
v_defEqI_428_ = lean_ctor_get(v___x_420_, 7);
v_extensions_429_ = lean_ctor_get(v___x_420_, 8);
v_issues_430_ = lean_ctor_get(v___x_420_, 9);
v_canon_431_ = lean_ctor_get(v___x_420_, 10);
v_instanceOverrides_432_ = lean_ctor_get(v___x_420_, 11);
v_debug_433_ = lean_ctor_get_uint8(v___x_420_, sizeof(void*)*12);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_445_ == 0)
{
v___x_435_ = v___x_420_;
v_isShared_436_ = v_isSharedCheck_445_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_instanceOverrides_432_);
lean_inc(v_canon_431_);
lean_inc(v_issues_430_);
lean_inc(v_extensions_429_);
lean_inc(v_defEqI_428_);
lean_inc(v_congrInfo_427_);
lean_inc(v_getLevel_426_);
lean_inc(v_inferType_425_);
lean_inc(v_proofInstInfoFVar_424_);
lean_inc(v_proofInstInfo_423_);
lean_inc(v_maxFVar_422_);
lean_inc(v_share_421_);
lean_dec(v___x_420_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_445_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_437_; lean_object* v___x_439_; 
lean_inc(v_a_416_);
v___x_437_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_422_, v_e_406_, v_a_416_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 1, v___x_437_);
v___x_439_ = v___x_435_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_share_421_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v___x_437_);
lean_ctor_set(v_reuseFailAlloc_444_, 2, v_proofInstInfo_423_);
lean_ctor_set(v_reuseFailAlloc_444_, 3, v_proofInstInfoFVar_424_);
lean_ctor_set(v_reuseFailAlloc_444_, 4, v_inferType_425_);
lean_ctor_set(v_reuseFailAlloc_444_, 5, v_getLevel_426_);
lean_ctor_set(v_reuseFailAlloc_444_, 6, v_congrInfo_427_);
lean_ctor_set(v_reuseFailAlloc_444_, 7, v_defEqI_428_);
lean_ctor_set(v_reuseFailAlloc_444_, 8, v_extensions_429_);
lean_ctor_set(v_reuseFailAlloc_444_, 9, v_issues_430_);
lean_ctor_set(v_reuseFailAlloc_444_, 10, v_canon_431_);
lean_ctor_set(v_reuseFailAlloc_444_, 11, v_instanceOverrides_432_);
lean_ctor_set_uint8(v_reuseFailAlloc_444_, sizeof(void*)*12, v_debug_433_);
v___x_439_ = v_reuseFailAlloc_444_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
lean_object* v___x_440_; lean_object* v___x_442_; 
v___x_440_ = lean_st_ref_put(v_a_408_, v___x_439_);
if (v_isShared_419_ == 0)
{
v___x_442_ = v___x_418_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_a_416_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_406_);
return v___y_415_;
}
}
v___jp_447_:
{
lean_object* v___x_449_; lean_object* v_share_450_; lean_object* v_maxFVar_451_; lean_object* v_proofInstInfo_452_; lean_object* v_proofInstInfoFVar_453_; lean_object* v_inferType_454_; lean_object* v_getLevel_455_; lean_object* v_congrInfo_456_; lean_object* v_defEqI_457_; lean_object* v_extensions_458_; lean_object* v_issues_459_; lean_object* v_canon_460_; lean_object* v_instanceOverrides_461_; uint8_t v_debug_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_472_; 
v___x_449_ = lean_st_ref_take(v_a_408_);
v_share_450_ = lean_ctor_get(v___x_449_, 0);
v_maxFVar_451_ = lean_ctor_get(v___x_449_, 1);
v_proofInstInfo_452_ = lean_ctor_get(v___x_449_, 2);
v_proofInstInfoFVar_453_ = lean_ctor_get(v___x_449_, 3);
v_inferType_454_ = lean_ctor_get(v___x_449_, 4);
v_getLevel_455_ = lean_ctor_get(v___x_449_, 5);
v_congrInfo_456_ = lean_ctor_get(v___x_449_, 6);
v_defEqI_457_ = lean_ctor_get(v___x_449_, 7);
v_extensions_458_ = lean_ctor_get(v___x_449_, 8);
v_issues_459_ = lean_ctor_get(v___x_449_, 9);
v_canon_460_ = lean_ctor_get(v___x_449_, 10);
v_instanceOverrides_461_ = lean_ctor_get(v___x_449_, 11);
v_debug_462_ = lean_ctor_get_uint8(v___x_449_, sizeof(void*)*12);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_472_ == 0)
{
v___x_464_ = v___x_449_;
v_isShared_465_ = v_isSharedCheck_472_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_instanceOverrides_461_);
lean_inc(v_canon_460_);
lean_inc(v_issues_459_);
lean_inc(v_extensions_458_);
lean_inc(v_defEqI_457_);
lean_inc(v_congrInfo_456_);
lean_inc(v_getLevel_455_);
lean_inc(v_inferType_454_);
lean_inc(v_proofInstInfoFVar_453_);
lean_inc(v_proofInstInfo_452_);
lean_inc(v_maxFVar_451_);
lean_inc(v_share_450_);
lean_dec(v___x_449_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_472_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_466_; lean_object* v___x_468_; 
lean_inc(v_a_448_);
v___x_466_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_451_, v_e_406_, v_a_448_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 1, v___x_466_);
v___x_468_ = v___x_464_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_share_450_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v___x_466_);
lean_ctor_set(v_reuseFailAlloc_471_, 2, v_proofInstInfo_452_);
lean_ctor_set(v_reuseFailAlloc_471_, 3, v_proofInstInfoFVar_453_);
lean_ctor_set(v_reuseFailAlloc_471_, 4, v_inferType_454_);
lean_ctor_set(v_reuseFailAlloc_471_, 5, v_getLevel_455_);
lean_ctor_set(v_reuseFailAlloc_471_, 6, v_congrInfo_456_);
lean_ctor_set(v_reuseFailAlloc_471_, 7, v_defEqI_457_);
lean_ctor_set(v_reuseFailAlloc_471_, 8, v_extensions_458_);
lean_ctor_set(v_reuseFailAlloc_471_, 9, v_issues_459_);
lean_ctor_set(v_reuseFailAlloc_471_, 10, v_canon_460_);
lean_ctor_set(v_reuseFailAlloc_471_, 11, v_instanceOverrides_461_);
lean_ctor_set_uint8(v_reuseFailAlloc_471_, sizeof(void*)*12, v_debug_462_);
v___x_468_ = v_reuseFailAlloc_471_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = lean_st_ref_put(v_a_408_, v___x_468_);
v___x_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_470_, 0, v_a_448_);
return v___x_470_;
}
}
}
v___jp_473_:
{
if (lean_obj_tag(v___y_475_) == 0)
{
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_506_; 
v_a_476_ = lean_ctor_get(v___y_475_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___y_475_);
if (v_isSharedCheck_506_ == 0)
{
v___x_478_ = v___y_475_;
v_isShared_479_ = v_isSharedCheck_506_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___y_475_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_506_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_480_; lean_object* v_share_481_; lean_object* v_maxFVar_482_; lean_object* v_proofInstInfo_483_; lean_object* v_proofInstInfoFVar_484_; lean_object* v_inferType_485_; lean_object* v_getLevel_486_; lean_object* v_congrInfo_487_; lean_object* v_defEqI_488_; lean_object* v_extensions_489_; lean_object* v_issues_490_; lean_object* v_canon_491_; lean_object* v_instanceOverrides_492_; uint8_t v_debug_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_505_; 
v___x_480_ = lean_st_ref_take(v___y_474_);
v_share_481_ = lean_ctor_get(v___x_480_, 0);
v_maxFVar_482_ = lean_ctor_get(v___x_480_, 1);
v_proofInstInfo_483_ = lean_ctor_get(v___x_480_, 2);
v_proofInstInfoFVar_484_ = lean_ctor_get(v___x_480_, 3);
v_inferType_485_ = lean_ctor_get(v___x_480_, 4);
v_getLevel_486_ = lean_ctor_get(v___x_480_, 5);
v_congrInfo_487_ = lean_ctor_get(v___x_480_, 6);
v_defEqI_488_ = lean_ctor_get(v___x_480_, 7);
v_extensions_489_ = lean_ctor_get(v___x_480_, 8);
v_issues_490_ = lean_ctor_get(v___x_480_, 9);
v_canon_491_ = lean_ctor_get(v___x_480_, 10);
v_instanceOverrides_492_ = lean_ctor_get(v___x_480_, 11);
v_debug_493_ = lean_ctor_get_uint8(v___x_480_, sizeof(void*)*12);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_505_ == 0)
{
v___x_495_ = v___x_480_;
v_isShared_496_ = v_isSharedCheck_505_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_instanceOverrides_492_);
lean_inc(v_canon_491_);
lean_inc(v_issues_490_);
lean_inc(v_extensions_489_);
lean_inc(v_defEqI_488_);
lean_inc(v_congrInfo_487_);
lean_inc(v_getLevel_486_);
lean_inc(v_inferType_485_);
lean_inc(v_proofInstInfoFVar_484_);
lean_inc(v_proofInstInfo_483_);
lean_inc(v_maxFVar_482_);
lean_inc(v_share_481_);
lean_dec(v___x_480_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_505_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_497_; lean_object* v___x_499_; 
lean_inc(v_a_476_);
v___x_497_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_482_, v_e_406_, v_a_476_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 1, v___x_497_);
v___x_499_ = v___x_495_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_share_481_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_504_, 2, v_proofInstInfo_483_);
lean_ctor_set(v_reuseFailAlloc_504_, 3, v_proofInstInfoFVar_484_);
lean_ctor_set(v_reuseFailAlloc_504_, 4, v_inferType_485_);
lean_ctor_set(v_reuseFailAlloc_504_, 5, v_getLevel_486_);
lean_ctor_set(v_reuseFailAlloc_504_, 6, v_congrInfo_487_);
lean_ctor_set(v_reuseFailAlloc_504_, 7, v_defEqI_488_);
lean_ctor_set(v_reuseFailAlloc_504_, 8, v_extensions_489_);
lean_ctor_set(v_reuseFailAlloc_504_, 9, v_issues_490_);
lean_ctor_set(v_reuseFailAlloc_504_, 10, v_canon_491_);
lean_ctor_set(v_reuseFailAlloc_504_, 11, v_instanceOverrides_492_);
lean_ctor_set_uint8(v_reuseFailAlloc_504_, sizeof(void*)*12, v_debug_493_);
v___x_499_ = v_reuseFailAlloc_504_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
lean_object* v___x_500_; lean_object* v___x_502_; 
v___x_500_ = lean_st_ref_put(v___y_474_, v___x_499_);
if (v_isShared_479_ == 0)
{
v___x_502_ = v___x_478_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_a_476_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_406_);
return v___y_475_;
}
}
v___jp_507_:
{
if (v___y_516_ == 0)
{
lean_object* v___x_517_; lean_object* v___x_518_; 
lean_dec_ref(v___y_515_);
lean_dec_ref(v___y_511_);
lean_dec_ref(v_e_406_);
v___x_517_ = lean_box(0);
v___x_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
return v___x_518_;
}
else
{
lean_object* v___x_519_; lean_object* v_maxFVar_520_; lean_object* v___x_521_; 
v___x_519_ = lean_st_ref_get(v___y_513_);
v_maxFVar_520_ = lean_ctor_get(v___x_519_, 1);
lean_inc_ref(v_maxFVar_520_);
lean_dec(v___x_519_);
v___x_521_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_520_, v_e_406_);
lean_dec_ref(v_maxFVar_520_);
if (lean_obj_tag(v___x_521_) == 1)
{
lean_object* v_val_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
lean_dec_ref(v___y_515_);
lean_dec_ref(v___y_511_);
lean_dec_ref(v_e_406_);
v_val_522_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_529_ == 0)
{
v___x_524_ = v___x_521_;
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_val_522_);
lean_dec(v___x_521_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
lean_ctor_set_tag(v___x_524_, 0);
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_val_522_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
else
{
lean_object* v___x_530_; 
lean_dec(v___x_521_);
v___x_530_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v___y_515_, v___y_514_, v___y_513_, v___y_508_, v___y_509_, v___y_512_, v___y_510_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v_a_531_; lean_object* v___x_532_; 
v_a_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_a_531_);
lean_dec_ref_known(v___x_530_, 1);
v___x_532_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v___y_511_, v___y_514_, v___y_513_, v___y_508_, v___y_509_, v___y_512_, v___y_510_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_533_; lean_object* v___x_534_; 
v_a_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_a_533_);
lean_dec_ref_known(v___x_532_, 1);
v___x_534_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_531_, v_a_533_, v___y_508_, v___y_512_, v___y_510_);
v___y_474_ = v___y_513_;
v___y_475_ = v___x_534_;
goto v___jp_473_;
}
else
{
lean_dec(v_a_531_);
v___y_474_ = v___y_513_;
v___y_475_ = v___x_532_;
goto v___jp_473_;
}
}
else
{
lean_dec_ref(v___y_511_);
v___y_474_ = v___y_513_;
v___y_475_ = v___x_530_;
goto v___jp_473_;
}
}
}
}
v___jp_535_:
{
uint8_t v___x_544_; 
v___x_544_ = l_Lean_Expr_hasFVar(v_e_406_);
if (v___x_544_ == 0)
{
uint8_t v___x_545_; 
v___x_545_ = l_Lean_Expr_hasMVar(v_e_406_);
v___y_508_ = v___y_540_;
v___y_509_ = v___y_541_;
v___y_510_ = v___y_543_;
v___y_511_ = v_b_537_;
v___y_512_ = v___y_542_;
v___y_513_ = v___y_539_;
v___y_514_ = v___y_538_;
v___y_515_ = v_d_536_;
v___y_516_ = v___x_545_;
goto v___jp_507_;
}
else
{
v___y_508_ = v___y_540_;
v___y_509_ = v___y_541_;
v___y_510_ = v___y_543_;
v___y_511_ = v_b_537_;
v___y_512_ = v___y_542_;
v___y_513_ = v___y_539_;
v___y_514_ = v___y_538_;
v___y_515_ = v_d_536_;
v___y_516_ = v___x_544_;
goto v___jp_507_;
}
}
v___jp_546_:
{
if (lean_obj_tag(v___y_547_) == 0)
{
lean_object* v_a_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_578_; 
v_a_548_ = lean_ctor_get(v___y_547_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___y_547_);
if (v_isSharedCheck_578_ == 0)
{
v___x_550_ = v___y_547_;
v_isShared_551_ = v_isSharedCheck_578_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_a_548_);
lean_dec(v___y_547_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_578_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_552_; lean_object* v_share_553_; lean_object* v_maxFVar_554_; lean_object* v_proofInstInfo_555_; lean_object* v_proofInstInfoFVar_556_; lean_object* v_inferType_557_; lean_object* v_getLevel_558_; lean_object* v_congrInfo_559_; lean_object* v_defEqI_560_; lean_object* v_extensions_561_; lean_object* v_issues_562_; lean_object* v_canon_563_; lean_object* v_instanceOverrides_564_; uint8_t v_debug_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_577_; 
v___x_552_ = lean_st_ref_take(v_a_408_);
v_share_553_ = lean_ctor_get(v___x_552_, 0);
v_maxFVar_554_ = lean_ctor_get(v___x_552_, 1);
v_proofInstInfo_555_ = lean_ctor_get(v___x_552_, 2);
v_proofInstInfoFVar_556_ = lean_ctor_get(v___x_552_, 3);
v_inferType_557_ = lean_ctor_get(v___x_552_, 4);
v_getLevel_558_ = lean_ctor_get(v___x_552_, 5);
v_congrInfo_559_ = lean_ctor_get(v___x_552_, 6);
v_defEqI_560_ = lean_ctor_get(v___x_552_, 7);
v_extensions_561_ = lean_ctor_get(v___x_552_, 8);
v_issues_562_ = lean_ctor_get(v___x_552_, 9);
v_canon_563_ = lean_ctor_get(v___x_552_, 10);
v_instanceOverrides_564_ = lean_ctor_get(v___x_552_, 11);
v_debug_565_ = lean_ctor_get_uint8(v___x_552_, sizeof(void*)*12);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_577_ == 0)
{
v___x_567_ = v___x_552_;
v_isShared_568_ = v_isSharedCheck_577_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_instanceOverrides_564_);
lean_inc(v_canon_563_);
lean_inc(v_issues_562_);
lean_inc(v_extensions_561_);
lean_inc(v_defEqI_560_);
lean_inc(v_congrInfo_559_);
lean_inc(v_getLevel_558_);
lean_inc(v_inferType_557_);
lean_inc(v_proofInstInfoFVar_556_);
lean_inc(v_proofInstInfo_555_);
lean_inc(v_maxFVar_554_);
lean_inc(v_share_553_);
lean_dec(v___x_552_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_577_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_569_; lean_object* v___x_571_; 
lean_inc(v_a_548_);
v___x_569_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_554_, v_e_406_, v_a_548_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 1, v___x_569_);
v___x_571_ = v___x_567_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_share_553_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v___x_569_);
lean_ctor_set(v_reuseFailAlloc_576_, 2, v_proofInstInfo_555_);
lean_ctor_set(v_reuseFailAlloc_576_, 3, v_proofInstInfoFVar_556_);
lean_ctor_set(v_reuseFailAlloc_576_, 4, v_inferType_557_);
lean_ctor_set(v_reuseFailAlloc_576_, 5, v_getLevel_558_);
lean_ctor_set(v_reuseFailAlloc_576_, 6, v_congrInfo_559_);
lean_ctor_set(v_reuseFailAlloc_576_, 7, v_defEqI_560_);
lean_ctor_set(v_reuseFailAlloc_576_, 8, v_extensions_561_);
lean_ctor_set(v_reuseFailAlloc_576_, 9, v_issues_562_);
lean_ctor_set(v_reuseFailAlloc_576_, 10, v_canon_563_);
lean_ctor_set(v_reuseFailAlloc_576_, 11, v_instanceOverrides_564_);
lean_ctor_set_uint8(v_reuseFailAlloc_576_, sizeof(void*)*12, v_debug_565_);
v___x_571_ = v_reuseFailAlloc_576_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
lean_object* v___x_572_; lean_object* v___x_574_; 
v___x_572_ = lean_st_ref_put(v_a_408_, v___x_571_);
if (v_isShared_551_ == 0)
{
v___x_574_ = v___x_550_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_a_548_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_406_);
return v___y_547_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_getMaxFVar_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_406_ = stack[0].m_obj;
lean_object* v_a_407_ = stack[1].m_obj;
lean_object* v_a_408_ = stack[2].m_obj;
lean_object* v_a_409_ = stack[3].m_obj;
lean_object* v_a_410_ = stack[4].m_obj;
lean_object* v_a_411_ = stack[5].m_obj;
lean_object* v_a_412_ = stack[6].m_obj;
lean_object* v_res_786_;
v_res_786_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_e_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
stack->m_obj
 = v_res_786_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f___boxed(lean_object* v_e_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_e_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_);
lean_dec(v_a_793_);
lean_dec_ref(v_a_792_);
lean_dec(v_a_791_);
lean_dec_ref(v_a_790_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0(lean_object* v_00_u03b2_796_, lean_object* v_x_797_, lean_object* v_x_798_, lean_object* v_x_799_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_x_797_, v_x_798_, v_x_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1(lean_object* v_00_u03b2_801_, lean_object* v_x_802_, lean_object* v_x_803_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_x_802_, v_x_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___boxed(lean_object* v_00_u03b2_805_, lean_object* v_x_806_, lean_object* v_x_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1(v_00_u03b2_805_, v_x_806_, v_x_807_);
lean_dec_ref(v_x_807_);
lean_dec_ref(v_x_806_);
return v_res_808_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0(lean_object* v_00_u03b2_809_, lean_object* v_x_810_, size_t v_x_811_, size_t v_x_812_, lean_object* v_x_813_, lean_object* v_x_814_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_810_, v_x_811_, v_x_812_, v_x_813_, v_x_814_);
return v___x_815_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_810_ = stack[1].m_obj;
size_t v_x_811_ = stack[2].m_num;
size_t v_x_812_ = stack[3].m_num;
lean_object* v_x_813_ = stack[4].m_obj;
lean_object* v_x_814_ = stack[5].m_obj;
lean_object* v_res_816_;
v_res_816_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0(lean_box(0), v_x_810_, v_x_811_, v_x_812_, v_x_813_, v_x_814_);
stack->m_obj
 = v_res_816_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_817_, lean_object* v_x_818_, lean_object* v_x_819_, lean_object* v_x_820_, lean_object* v_x_821_, lean_object* v_x_822_){
_start:
{
size_t v_x_6085__boxed_823_; size_t v_x_6086__boxed_824_; lean_object* v_res_825_; 
v_x_6085__boxed_823_ = lean_unbox_usize(v_x_819_);
lean_dec(v_x_819_);
v_x_6086__boxed_824_ = lean_unbox_usize(v_x_820_);
lean_dec(v_x_820_);
v_res_825_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0(v_00_u03b2_817_, v_x_818_, v_x_6085__boxed_823_, v_x_6086__boxed_824_, v_x_821_, v_x_822_);
return v_res_825_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2(lean_object* v_00_u03b2_826_, lean_object* v_x_827_, size_t v_x_828_, lean_object* v_x_829_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_827_, v_x_828_, v_x_829_);
return v___x_830_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_827_ = stack[1].m_obj;
size_t v_x_828_ = stack[2].m_num;
lean_object* v_x_829_ = stack[3].m_obj;
lean_object* v_res_831_;
v_res_831_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2(lean_box(0), v_x_827_, v_x_828_, v_x_829_);
stack->m_obj
 = v_res_831_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_832_, lean_object* v_x_833_, lean_object* v_x_834_, lean_object* v_x_835_){
_start:
{
size_t v_x_6113__boxed_836_; lean_object* v_res_837_; 
v_x_6113__boxed_836_ = lean_unbox_usize(v_x_834_);
lean_dec(v_x_834_);
v_res_837_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2(v_00_u03b2_832_, v_x_833_, v_x_6113__boxed_836_, v_x_835_);
lean_dec_ref(v_x_835_);
lean_dec_ref(v_x_833_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_838_, lean_object* v_n_839_, lean_object* v_k_840_, lean_object* v_v_841_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(v_n_839_, v_k_840_, v_v_841_);
return v___x_842_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_843_, size_t v_depth_844_, lean_object* v_keys_845_, lean_object* v_vals_846_, lean_object* v_heq_847_, lean_object* v_i_848_, lean_object* v_entries_849_){
_start:
{
lean_object* v___x_850_; 
v___x_850_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(v_depth_844_, v_keys_845_, v_vals_846_, v_i_848_, v_entries_849_);
return v___x_850_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_depth_844_ = stack[1].m_num;
lean_object* v_keys_845_ = stack[2].m_obj;
lean_object* v_vals_846_ = stack[3].m_obj;
lean_object* v_i_848_ = stack[5].m_obj;
lean_object* v_entries_849_ = stack[6].m_obj;
lean_object* v_res_851_;
v_res_851_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3(lean_box(0), v_depth_844_, v_keys_845_, v_vals_846_, lean_box(0), v_i_848_, v_entries_849_);
stack->m_obj
 = v_res_851_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_852_, lean_object* v_depth_853_, lean_object* v_keys_854_, lean_object* v_vals_855_, lean_object* v_heq_856_, lean_object* v_i_857_, lean_object* v_entries_858_){
_start:
{
size_t v_depth_boxed_859_; lean_object* v_res_860_; 
v_depth_boxed_859_ = lean_unbox_usize(v_depth_853_);
lean_dec(v_depth_853_);
v_res_860_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3(v_00_u03b2_852_, v_depth_boxed_859_, v_keys_854_, v_vals_855_, v_heq_856_, v_i_857_, v_entries_858_);
lean_dec_ref(v_vals_855_);
lean_dec_ref(v_keys_854_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_861_, lean_object* v_keys_862_, lean_object* v_vals_863_, lean_object* v_heq_864_, lean_object* v_i_865_, lean_object* v_k_866_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_keys_862_, v_vals_863_, v_i_865_, v_k_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_868_, lean_object* v_keys_869_, lean_object* v_vals_870_, lean_object* v_heq_871_, lean_object* v_i_872_, lean_object* v_k_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6(v_00_u03b2_868_, v_keys_869_, v_vals_870_, v_heq_871_, v_i_872_, v_k_873_);
lean_dec_ref(v_k_873_);
lean_dec_ref(v_vals_870_);
lean_dec_ref(v_keys_869_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_875_, lean_object* v_x_876_, lean_object* v_x_877_, lean_object* v_x_878_, lean_object* v_x_879_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_x_876_, v_x_877_, v_x_878_, v_x_879_);
return v___x_880_;
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
