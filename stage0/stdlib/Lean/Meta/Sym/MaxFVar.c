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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instInhabitedSymM(lean_object*);
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
lean_object* v___f_87_; lean_object* v___f_88_; uint8_t v___y_90_; uint8_t v___x_135_; 
v___f_87_ = ((lean_object*)(l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__0));
v___f_88_ = ((lean_object*)(l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__1));
v___x_135_ = l_Lean_Expr_hasFVar(v_e_78_);
if (v___x_135_ == 0)
{
uint8_t v___x_136_; 
v___x_136_ = l_Lean_Expr_hasMVar(v_e_78_);
v___y_90_ = v___x_136_;
goto v___jp_89_;
}
else
{
v___y_90_ = v___x_135_;
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
lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_134_; 
v_a_105_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_134_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_134_ == 0)
{
v___x_107_ = v___x_104_;
v_isShared_108_ = v_isSharedCheck_134_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_dec(v___x_104_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_134_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_109_; lean_object* v_share_110_; lean_object* v_maxFVar_111_; lean_object* v_proofInstInfo_112_; lean_object* v_inferType_113_; lean_object* v_getLevel_114_; lean_object* v_congrInfo_115_; lean_object* v_defEqI_116_; lean_object* v_extensions_117_; lean_object* v_issues_118_; lean_object* v_canon_119_; lean_object* v_instanceOverrides_120_; uint8_t v_debug_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_133_; 
v___x_109_ = lean_st_ref_take(v_a_81_);
v_share_110_ = lean_ctor_get(v___x_109_, 0);
v_maxFVar_111_ = lean_ctor_get(v___x_109_, 1);
v_proofInstInfo_112_ = lean_ctor_get(v___x_109_, 2);
v_inferType_113_ = lean_ctor_get(v___x_109_, 3);
v_getLevel_114_ = lean_ctor_get(v___x_109_, 4);
v_congrInfo_115_ = lean_ctor_get(v___x_109_, 5);
v_defEqI_116_ = lean_ctor_get(v___x_109_, 6);
v_extensions_117_ = lean_ctor_get(v___x_109_, 7);
v_issues_118_ = lean_ctor_get(v___x_109_, 8);
v_canon_119_ = lean_ctor_get(v___x_109_, 9);
v_instanceOverrides_120_ = lean_ctor_get(v___x_109_, 10);
v_debug_121_ = lean_ctor_get_uint8(v___x_109_, sizeof(void*)*11);
v_isSharedCheck_133_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_133_ == 0)
{
v___x_123_ = v___x_109_;
v_isShared_124_ = v_isSharedCheck_133_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_instanceOverrides_120_);
lean_inc(v_canon_119_);
lean_inc(v_issues_118_);
lean_inc(v_extensions_117_);
lean_inc(v_defEqI_116_);
lean_inc(v_congrInfo_115_);
lean_inc(v_getLevel_114_);
lean_inc(v_inferType_113_);
lean_inc(v_proofInstInfo_112_);
lean_inc(v_maxFVar_111_);
lean_inc(v_share_110_);
lean_dec(v___x_109_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_133_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_125_; lean_object* v___x_127_; 
lean_inc(v_a_105_);
v___x_125_ = l_Lean_PersistentHashMap_insert___redArg(v___f_87_, v___f_88_, v_maxFVar_111_, v_e_78_, v_a_105_);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 1, v___x_125_);
v___x_127_ = v___x_123_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_share_110_);
lean_ctor_set(v_reuseFailAlloc_132_, 1, v___x_125_);
lean_ctor_set(v_reuseFailAlloc_132_, 2, v_proofInstInfo_112_);
lean_ctor_set(v_reuseFailAlloc_132_, 3, v_inferType_113_);
lean_ctor_set(v_reuseFailAlloc_132_, 4, v_getLevel_114_);
lean_ctor_set(v_reuseFailAlloc_132_, 5, v_congrInfo_115_);
lean_ctor_set(v_reuseFailAlloc_132_, 6, v_defEqI_116_);
lean_ctor_set(v_reuseFailAlloc_132_, 7, v_extensions_117_);
lean_ctor_set(v_reuseFailAlloc_132_, 8, v_issues_118_);
lean_ctor_set(v_reuseFailAlloc_132_, 9, v_canon_119_);
lean_ctor_set(v_reuseFailAlloc_132_, 10, v_instanceOverrides_120_);
lean_ctor_set_uint8(v_reuseFailAlloc_132_, sizeof(void*)*11, v_debug_121_);
v___x_127_ = v_reuseFailAlloc_132_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
lean_object* v___x_128_; lean_object* v___x_130_; 
v___x_128_ = lean_st_ref_put(v_a_81_, v___x_127_);
if (v_isShared_108_ == 0)
{
v___x_130_ = v___x_107_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_a_105_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
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
v___x_147_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2(lean_object* v_msg_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v___x_156_; lean_object* v___x_4553__overap_157_; lean_object* v___x_158_; 
v___x_156_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0, &l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0);
v___x_4553__overap_157_ = lean_panic_fn_borrowed(v___x_156_, v_msg_148_);
lean_inc(v___y_154_);
lean_inc_ref(v___y_153_);
lean_inc(v___y_152_);
lean_inc_ref(v___y_151_);
lean_inc(v___y_150_);
lean_inc_ref(v___y_149_);
v___x_158_ = lean_apply_7(v___x_4553__overap_157_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, lean_box(0));
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_168_, lean_object* v_x_169_, lean_object* v_x_170_, lean_object* v_x_171_){
_start:
{
lean_object* v_ks_172_; lean_object* v_vs_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_199_; 
v_ks_172_ = lean_ctor_get(v_x_168_, 0);
v_vs_173_ = lean_ctor_get(v_x_168_, 1);
v_isSharedCheck_199_ = !lean_is_exclusive(v_x_168_);
if (v_isSharedCheck_199_ == 0)
{
v___x_175_ = v_x_168_;
v_isShared_176_ = v_isSharedCheck_199_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_vs_173_);
lean_inc(v_ks_172_);
lean_dec(v_x_168_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_199_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_177_ = lean_array_get_size(v_ks_172_);
v___x_178_ = lean_nat_dec_lt(v_x_169_, v___x_177_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_182_; 
lean_dec(v_x_169_);
v___x_179_ = lean_array_push(v_ks_172_, v_x_170_);
v___x_180_ = lean_array_push(v_vs_173_, v_x_171_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 1, v___x_180_);
lean_ctor_set(v___x_175_, 0, v___x_179_);
v___x_182_ = v___x_175_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v___x_179_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v___x_180_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
else
{
lean_object* v_k_x27_184_; size_t v___x_185_; size_t v___x_186_; uint8_t v___x_187_; 
v_k_x27_184_ = lean_array_fget_borrowed(v_ks_172_, v_x_169_);
v___x_185_ = lean_ptr_addr(v_x_170_);
v___x_186_ = lean_ptr_addr(v_k_x27_184_);
v___x_187_ = lean_usize_dec_eq(v___x_185_, v___x_186_);
if (v___x_187_ == 0)
{
lean_object* v___x_189_; 
if (v_isShared_176_ == 0)
{
v___x_189_ = v___x_175_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_ks_172_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v_vs_173_);
v___x_189_ = v_reuseFailAlloc_193_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = lean_unsigned_to_nat(1u);
v___x_191_ = lean_nat_add(v_x_169_, v___x_190_);
lean_dec(v_x_169_);
v_x_168_ = v___x_189_;
v_x_169_ = v___x_191_;
goto _start;
}
}
else
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_197_; 
v___x_194_ = lean_array_fset(v_ks_172_, v_x_169_, v_x_170_);
v___x_195_ = lean_array_fset(v_vs_173_, v_x_169_, v_x_171_);
lean_dec(v_x_169_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 1, v___x_195_);
lean_ctor_set(v___x_175_, 0, v___x_194_);
v___x_197_ = v___x_175_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_194_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v___x_195_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(lean_object* v_n_200_, lean_object* v_k_201_, lean_object* v_v_202_){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = lean_unsigned_to_nat(0u);
v___x_204_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_n_200_, v___x_203_, v_k_201_, v_v_202_);
return v___x_204_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(lean_object* v_x_206_, size_t v_x_207_, size_t v_x_208_, lean_object* v_x_209_, lean_object* v_x_210_){
_start:
{
if (lean_obj_tag(v_x_206_) == 0)
{
lean_object* v_es_211_; size_t v___x_212_; size_t v___x_213_; lean_object* v_j_214_; lean_object* v___x_215_; uint8_t v___x_216_; 
v_es_211_ = lean_ctor_get(v_x_206_, 0);
v___x_212_ = ((size_t)31ULL);
v___x_213_ = lean_usize_land(v_x_207_, v___x_212_);
v_j_214_ = lean_usize_to_nat(v___x_213_);
v___x_215_ = lean_array_get_size(v_es_211_);
v___x_216_ = lean_nat_dec_lt(v_j_214_, v___x_215_);
if (v___x_216_ == 0)
{
lean_dec(v_j_214_);
lean_dec(v_x_210_);
lean_dec_ref(v_x_209_);
return v_x_206_;
}
else
{
lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_257_; 
lean_inc_ref(v_es_211_);
v_isSharedCheck_257_ = !lean_is_exclusive(v_x_206_);
if (v_isSharedCheck_257_ == 0)
{
lean_object* v_unused_258_; 
v_unused_258_ = lean_ctor_get(v_x_206_, 0);
lean_dec(v_unused_258_);
v___x_218_ = v_x_206_;
v_isShared_219_ = v_isSharedCheck_257_;
goto v_resetjp_217_;
}
else
{
lean_dec(v_x_206_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_257_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v_v_220_; lean_object* v___x_221_; lean_object* v_xs_x27_222_; lean_object* v___y_224_; 
v_v_220_ = lean_array_fget(v_es_211_, v_j_214_);
v___x_221_ = lean_box(0);
v_xs_x27_222_ = lean_array_fset(v_es_211_, v_j_214_, v___x_221_);
switch(lean_obj_tag(v_v_220_))
{
case 0:
{
lean_object* v_key_229_; lean_object* v_val_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_242_; 
v_key_229_ = lean_ctor_get(v_v_220_, 0);
v_val_230_ = lean_ctor_get(v_v_220_, 1);
v_isSharedCheck_242_ = !lean_is_exclusive(v_v_220_);
if (v_isSharedCheck_242_ == 0)
{
v___x_232_ = v_v_220_;
v_isShared_233_ = v_isSharedCheck_242_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_val_230_);
lean_inc(v_key_229_);
lean_dec(v_v_220_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_242_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
size_t v___x_234_; size_t v___x_235_; uint8_t v___x_236_; 
v___x_234_ = lean_ptr_addr(v_x_209_);
v___x_235_ = lean_ptr_addr(v_key_229_);
v___x_236_ = lean_usize_dec_eq(v___x_234_, v___x_235_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; lean_object* v___x_238_; 
lean_del_object(v___x_232_);
v___x_237_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_229_, v_val_230_, v_x_209_, v_x_210_);
v___x_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
v___y_224_ = v___x_238_;
goto v___jp_223_;
}
else
{
lean_object* v___x_240_; 
lean_dec(v_val_230_);
lean_dec(v_key_229_);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 1, v_x_210_);
lean_ctor_set(v___x_232_, 0, v_x_209_);
v___x_240_ = v___x_232_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_x_209_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v_x_210_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
v___y_224_ = v___x_240_;
goto v___jp_223_;
}
}
}
}
case 1:
{
lean_object* v_node_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_255_; 
v_node_243_ = lean_ctor_get(v_v_220_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v_v_220_);
if (v_isSharedCheck_255_ == 0)
{
v___x_245_ = v_v_220_;
v_isShared_246_ = v_isSharedCheck_255_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_node_243_);
lean_dec(v_v_220_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_255_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
size_t v___x_247_; size_t v___x_248_; size_t v___x_249_; size_t v___x_250_; lean_object* v___x_251_; lean_object* v___x_253_; 
v___x_247_ = ((size_t)5ULL);
v___x_248_ = lean_usize_shift_right(v_x_207_, v___x_247_);
v___x_249_ = ((size_t)1ULL);
v___x_250_ = lean_usize_add(v_x_208_, v___x_249_);
v___x_251_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_node_243_, v___x_248_, v___x_250_, v_x_209_, v_x_210_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v___x_251_);
v___x_253_ = v___x_245_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_251_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
v___y_224_ = v___x_253_;
goto v___jp_223_;
}
}
}
default: 
{
lean_object* v___x_256_; 
v___x_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_256_, 0, v_x_209_);
lean_ctor_set(v___x_256_, 1, v_x_210_);
v___y_224_ = v___x_256_;
goto v___jp_223_;
}
}
v___jp_223_:
{
lean_object* v___x_225_; lean_object* v___x_227_; 
v___x_225_ = lean_array_fset(v_xs_x27_222_, v_j_214_, v___y_224_);
lean_dec(v_j_214_);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 0, v___x_225_);
v___x_227_ = v___x_218_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v___x_225_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
}
else
{
lean_object* v_ks_259_; lean_object* v_vs_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_278_; 
v_ks_259_ = lean_ctor_get(v_x_206_, 0);
v_vs_260_ = lean_ctor_get(v_x_206_, 1);
v_isSharedCheck_278_ = !lean_is_exclusive(v_x_206_);
if (v_isSharedCheck_278_ == 0)
{
v___x_262_ = v_x_206_;
v_isShared_263_ = v_isSharedCheck_278_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_vs_260_);
lean_inc(v_ks_259_);
lean_dec(v_x_206_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_278_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_265_; 
if (v_isShared_263_ == 0)
{
v___x_265_ = v___x_262_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_ks_259_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v_vs_260_);
v___x_265_ = v_reuseFailAlloc_277_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
lean_object* v_newNode_266_; size_t v___x_267_; uint8_t v___x_268_; 
v_newNode_266_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(v___x_265_, v_x_209_, v_x_210_);
v___x_267_ = ((size_t)7ULL);
v___x_268_ = lean_usize_dec_le(v___x_267_, v_x_208_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; lean_object* v___x_270_; uint8_t v___x_271_; 
v___x_269_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_266_);
v___x_270_ = lean_unsigned_to_nat(4u);
v___x_271_ = lean_nat_dec_lt(v___x_269_, v___x_270_);
lean_dec(v___x_269_);
if (v___x_271_ == 0)
{
lean_object* v_ks_272_; lean_object* v_vs_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v_ks_272_ = lean_ctor_get(v_newNode_266_, 0);
lean_inc_ref(v_ks_272_);
v_vs_273_ = lean_ctor_get(v_newNode_266_, 1);
lean_inc_ref(v_vs_273_);
lean_dec_ref(v_newNode_266_);
v___x_274_ = lean_unsigned_to_nat(0u);
v___x_275_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0);
v___x_276_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(v_x_208_, v_ks_272_, v_vs_273_, v___x_274_, v___x_275_);
lean_dec_ref(v_vs_273_);
lean_dec_ref(v_ks_272_);
return v___x_276_;
}
else
{
return v_newNode_266_;
}
}
else
{
return v_newNode_266_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(size_t v_depth_279_, lean_object* v_keys_280_, lean_object* v_vals_281_, lean_object* v_i_282_, lean_object* v_entries_283_){
_start:
{
lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_284_ = lean_array_get_size(v_keys_280_);
v___x_285_ = lean_nat_dec_lt(v_i_282_, v___x_284_);
if (v___x_285_ == 0)
{
lean_dec(v_i_282_);
return v_entries_283_;
}
else
{
lean_object* v_k_286_; lean_object* v_v_287_; size_t v___x_288_; size_t v___x_289_; size_t v___x_290_; uint64_t v___x_291_; size_t v_h_292_; size_t v___x_293_; lean_object* v___x_294_; size_t v___x_295_; size_t v___x_296_; size_t v___x_297_; size_t v_h_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v_k_286_ = lean_array_fget_borrowed(v_keys_280_, v_i_282_);
v_v_287_ = lean_array_fget_borrowed(v_vals_281_, v_i_282_);
v___x_288_ = lean_ptr_addr(v_k_286_);
v___x_289_ = ((size_t)3ULL);
v___x_290_ = lean_usize_shift_right(v___x_288_, v___x_289_);
v___x_291_ = lean_usize_to_uint64(v___x_290_);
v_h_292_ = lean_uint64_to_usize(v___x_291_);
v___x_293_ = ((size_t)5ULL);
v___x_294_ = lean_unsigned_to_nat(1u);
v___x_295_ = ((size_t)1ULL);
v___x_296_ = lean_usize_sub(v_depth_279_, v___x_295_);
v___x_297_ = lean_usize_mul(v___x_293_, v___x_296_);
v_h_298_ = lean_usize_shift_right(v_h_292_, v___x_297_);
v___x_299_ = lean_nat_add(v_i_282_, v___x_294_);
lean_dec(v_i_282_);
lean_inc(v_v_287_);
lean_inc(v_k_286_);
v___x_300_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_entries_283_, v_h_298_, v_depth_279_, v_k_286_, v_v_287_);
v_i_282_ = v___x_299_;
v_entries_283_ = v___x_300_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_302_, lean_object* v_keys_303_, lean_object* v_vals_304_, lean_object* v_i_305_, lean_object* v_entries_306_){
_start:
{
size_t v_depth_boxed_307_; lean_object* v_res_308_; 
v_depth_boxed_307_ = lean_unbox_usize(v_depth_302_);
lean_dec(v_depth_302_);
v_res_308_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(v_depth_boxed_307_, v_keys_303_, v_vals_304_, v_i_305_, v_entries_306_);
lean_dec_ref(v_vals_304_);
lean_dec_ref(v_keys_303_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_309_, lean_object* v_x_310_, lean_object* v_x_311_, lean_object* v_x_312_, lean_object* v_x_313_){
_start:
{
size_t v_x_5099__boxed_314_; size_t v_x_5100__boxed_315_; lean_object* v_res_316_; 
v_x_5099__boxed_314_ = lean_unbox_usize(v_x_310_);
lean_dec(v_x_310_);
v_x_5100__boxed_315_ = lean_unbox_usize(v_x_311_);
lean_dec(v_x_311_);
v_res_316_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_309_, v_x_5099__boxed_314_, v_x_5100__boxed_315_, v_x_312_, v_x_313_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(lean_object* v_x_317_, lean_object* v_x_318_, lean_object* v_x_319_){
_start:
{
size_t v___x_320_; size_t v___x_321_; size_t v___x_322_; uint64_t v___x_323_; size_t v___x_324_; size_t v___x_325_; lean_object* v___x_326_; 
v___x_320_ = lean_ptr_addr(v_x_318_);
v___x_321_ = ((size_t)3ULL);
v___x_322_ = lean_usize_shift_right(v___x_320_, v___x_321_);
v___x_323_ = lean_usize_to_uint64(v___x_322_);
v___x_324_ = lean_uint64_to_usize(v___x_323_);
v___x_325_ = ((size_t)1ULL);
v___x_326_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_317_, v___x_324_, v___x_325_, v_x_318_, v_x_319_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(lean_object* v_keys_327_, lean_object* v_vals_328_, lean_object* v_i_329_, lean_object* v_k_330_){
_start:
{
lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_331_ = lean_array_get_size(v_keys_327_);
v___x_332_ = lean_nat_dec_lt(v_i_329_, v___x_331_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; 
lean_dec(v_i_329_);
v___x_333_ = lean_box(0);
return v___x_333_;
}
else
{
lean_object* v_k_x27_334_; size_t v___x_335_; size_t v___x_336_; uint8_t v___x_337_; 
v_k_x27_334_ = lean_array_fget_borrowed(v_keys_327_, v_i_329_);
v___x_335_ = lean_ptr_addr(v_k_330_);
v___x_336_ = lean_ptr_addr(v_k_x27_334_);
v___x_337_ = lean_usize_dec_eq(v___x_335_, v___x_336_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = lean_unsigned_to_nat(1u);
v___x_339_ = lean_nat_add(v_i_329_, v___x_338_);
lean_dec(v_i_329_);
v_i_329_ = v___x_339_;
goto _start;
}
else
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = lean_array_fget_borrowed(v_vals_328_, v_i_329_);
lean_dec(v_i_329_);
lean_inc(v___x_341_);
v___x_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
return v___x_342_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_keys_343_, lean_object* v_vals_344_, lean_object* v_i_345_, lean_object* v_k_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_keys_343_, v_vals_344_, v_i_345_, v_k_346_);
lean_dec_ref(v_k_346_);
lean_dec_ref(v_vals_344_);
lean_dec_ref(v_keys_343_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(lean_object* v_x_348_, size_t v_x_349_, lean_object* v_x_350_){
_start:
{
if (lean_obj_tag(v_x_348_) == 0)
{
lean_object* v_es_351_; lean_object* v___x_352_; size_t v___x_353_; size_t v___x_354_; lean_object* v_j_355_; lean_object* v___x_356_; 
v_es_351_ = lean_ctor_get(v_x_348_, 0);
v___x_352_ = lean_box(2);
v___x_353_ = ((size_t)31ULL);
v___x_354_ = lean_usize_land(v_x_349_, v___x_353_);
v_j_355_ = lean_usize_to_nat(v___x_354_);
v___x_356_ = lean_array_get_borrowed(v___x_352_, v_es_351_, v_j_355_);
lean_dec(v_j_355_);
switch(lean_obj_tag(v___x_356_))
{
case 0:
{
lean_object* v_key_357_; lean_object* v_val_358_; size_t v___x_359_; size_t v___x_360_; uint8_t v___x_361_; 
v_key_357_ = lean_ctor_get(v___x_356_, 0);
v_val_358_ = lean_ctor_get(v___x_356_, 1);
v___x_359_ = lean_ptr_addr(v_x_350_);
v___x_360_ = lean_ptr_addr(v_key_357_);
v___x_361_ = lean_usize_dec_eq(v___x_359_, v___x_360_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; 
v___x_362_ = lean_box(0);
return v___x_362_;
}
else
{
lean_object* v___x_363_; 
lean_inc(v_val_358_);
v___x_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_363_, 0, v_val_358_);
return v___x_363_;
}
}
case 1:
{
lean_object* v_node_364_; size_t v___x_365_; size_t v___x_366_; 
v_node_364_ = lean_ctor_get(v___x_356_, 0);
v___x_365_ = ((size_t)5ULL);
v___x_366_ = lean_usize_shift_right(v_x_349_, v___x_365_);
v_x_348_ = v_node_364_;
v_x_349_ = v___x_366_;
goto _start;
}
default: 
{
lean_object* v___x_368_; 
v___x_368_ = lean_box(0);
return v___x_368_;
}
}
}
else
{
lean_object* v_ks_369_; lean_object* v_vs_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v_ks_369_ = lean_ctor_get(v_x_348_, 0);
v_vs_370_ = lean_ctor_get(v_x_348_, 1);
v___x_371_ = lean_unsigned_to_nat(0u);
v___x_372_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_ks_369_, v_vs_370_, v___x_371_, v_x_350_);
return v___x_372_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_x_373_, lean_object* v_x_374_, lean_object* v_x_375_){
_start:
{
size_t v_x_5300__boxed_376_; lean_object* v_res_377_; 
v_x_5300__boxed_376_ = lean_unbox_usize(v_x_374_);
lean_dec(v_x_374_);
v_res_377_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_373_, v_x_5300__boxed_376_, v_x_375_);
lean_dec_ref(v_x_375_);
lean_dec_ref(v_x_373_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(lean_object* v_x_378_, lean_object* v_x_379_){
_start:
{
size_t v___x_380_; size_t v___x_381_; size_t v___x_382_; uint64_t v___x_383_; size_t v___x_384_; lean_object* v___x_385_; 
v___x_380_ = lean_ptr_addr(v_x_379_);
v___x_381_ = ((size_t)3ULL);
v___x_382_ = lean_usize_shift_right(v___x_380_, v___x_381_);
v___x_383_ = lean_usize_to_uint64(v___x_382_);
v___x_384_ = lean_uint64_to_usize(v___x_383_);
v___x_385_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_378_, v___x_384_, v_x_379_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg___boxed(lean_object* v_x_386_, lean_object* v_x_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_x_386_, v_x_387_);
lean_dec_ref(v_x_387_);
lean_dec_ref(v_x_386_);
return v_res_388_;
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
lean_object* v___y_407_; lean_object* v_a_439_; lean_object* v___y_464_; lean_object* v___y_465_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v___y_500_; lean_object* v___y_501_; lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v___y_504_; uint8_t v___y_505_; lean_object* v_d_525_; lean_object* v_b_526_; lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_536_; 
switch(lean_obj_tag(v_e_398_))
{
case 1:
{
lean_object* v_fvarId_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v_fvarId_567_ = lean_ctor_get(v_e_398_, 0);
lean_inc(v_fvarId_567_);
lean_dec_ref_known(v_e_398_, 1);
v___x_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_568_, 0, v_fvarId_567_);
v___x_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
return v___x_569_;
}
case 2:
{
lean_object* v_mvarId_570_; uint8_t v___y_572_; uint8_t v___x_613_; 
v_mvarId_570_ = lean_ctor_get(v_e_398_, 0);
v___x_613_ = l_Lean_Expr_hasFVar(v_e_398_);
if (v___x_613_ == 0)
{
uint8_t v___x_614_; 
v___x_614_ = l_Lean_Expr_hasMVar(v_e_398_);
v___y_572_ = v___x_614_;
goto v___jp_571_;
}
else
{
v___y_572_ = v___x_613_;
goto v___jp_571_;
}
v___jp_571_:
{
if (v___y_572_ == 0)
{
lean_object* v___x_573_; lean_object* v___x_574_; 
lean_dec_ref_known(v_e_398_, 1);
v___x_573_ = lean_box(0);
v___x_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
return v___x_574_;
}
else
{
lean_object* v___x_575_; lean_object* v_maxFVar_576_; lean_object* v___x_577_; 
v___x_575_ = lean_st_ref_get(v_a_400_);
v_maxFVar_576_ = lean_ctor_get(v___x_575_, 1);
lean_inc_ref(v_maxFVar_576_);
lean_dec(v___x_575_);
v___x_577_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_576_, v_e_398_);
lean_dec_ref(v_maxFVar_576_);
if (lean_obj_tag(v___x_577_) == 1)
{
lean_object* v_val_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_585_; 
lean_dec_ref_known(v_e_398_, 1);
v_val_578_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_585_ == 0)
{
v___x_580_ = v___x_577_;
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_val_578_);
lean_dec(v___x_577_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
if (v_isShared_581_ == 0)
{
lean_ctor_set_tag(v___x_580_, 0);
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_val_578_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
else
{
lean_object* v___x_586_; 
lean_dec(v___x_577_);
lean_inc(v_mvarId_570_);
v___x_586_ = l_Lean_MVarId_getDecl(v_mvarId_570_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v_a_587_; lean_object* v_lctx_588_; lean_object* v_decls_589_; uint8_t v___x_590_; 
v_a_587_ = lean_ctor_get(v___x_586_, 0);
lean_inc(v_a_587_);
lean_dec_ref_known(v___x_586_, 1);
v_lctx_588_ = lean_ctor_get(v_a_587_, 1);
lean_inc_ref(v_lctx_588_);
lean_dec(v_a_587_);
v_decls_589_ = lean_ctor_get(v_lctx_588_, 1);
v___x_590_ = l_Lean_PersistentArray_isEmpty___redArg(v_decls_589_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; 
v___x_591_ = l_Lean_LocalContext_lastDecl(v_lctx_588_);
lean_dec_ref(v_lctx_588_);
if (lean_obj_tag(v___x_591_) == 1)
{
lean_object* v_val_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_600_; 
v_val_592_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_600_ == 0)
{
v___x_594_ = v___x_591_;
v_isShared_595_ = v_isSharedCheck_600_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_val_592_);
lean_dec(v___x_591_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_600_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_596_; lean_object* v___x_598_; 
v___x_596_ = l_Lean_LocalDecl_fvarId(v_val_592_);
lean_dec(v_val_592_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v___x_596_);
v___x_598_ = v___x_594_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_596_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
v_a_439_ = v___x_598_;
goto v___jp_438_;
}
}
}
else
{
lean_object* v___x_601_; lean_object* v___x_602_; 
lean_dec(v___x_591_);
v___x_601_ = lean_obj_once(&l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3, &l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3_once, _init_l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3);
v___x_602_ = l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2(v___x_601_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_603_; 
v_a_603_ = lean_ctor_get(v___x_602_, 0);
lean_inc(v_a_603_);
lean_dec_ref_known(v___x_602_, 1);
v_a_439_ = v_a_603_;
goto v___jp_438_;
}
else
{
lean_dec_ref_known(v_e_398_, 1);
return v___x_602_;
}
}
}
else
{
lean_object* v___x_604_; 
lean_dec_ref(v_lctx_588_);
v___x_604_ = lean_box(0);
v_a_439_ = v___x_604_;
goto v___jp_438_;
}
}
else
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_612_; 
lean_dec_ref_known(v_e_398_, 1);
v_a_605_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_612_ == 0)
{
v___x_607_ = v___x_586_;
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_586_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_610_; 
if (v_isShared_608_ == 0)
{
v___x_610_ = v___x_607_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_a_605_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
}
}
}
case 5:
{
lean_object* v_fn_615_; lean_object* v_arg_616_; uint8_t v___y_618_; uint8_t v___x_637_; 
v_fn_615_ = lean_ctor_get(v_e_398_, 0);
v_arg_616_ = lean_ctor_get(v_e_398_, 1);
v___x_637_ = l_Lean_Expr_hasFVar(v_e_398_);
if (v___x_637_ == 0)
{
uint8_t v___x_638_; 
v___x_638_ = l_Lean_Expr_hasMVar(v_e_398_);
v___y_618_ = v___x_638_;
goto v___jp_617_;
}
else
{
v___y_618_ = v___x_637_;
goto v___jp_617_;
}
v___jp_617_:
{
if (v___y_618_ == 0)
{
lean_object* v___x_619_; lean_object* v___x_620_; 
lean_dec_ref_known(v_e_398_, 2);
v___x_619_ = lean_box(0);
v___x_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
return v___x_620_;
}
else
{
lean_object* v___x_621_; lean_object* v_maxFVar_622_; lean_object* v___x_623_; 
v___x_621_ = lean_st_ref_get(v_a_400_);
v_maxFVar_622_ = lean_ctor_get(v___x_621_, 1);
lean_inc_ref(v_maxFVar_622_);
lean_dec(v___x_621_);
v___x_623_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_622_, v_e_398_);
lean_dec_ref(v_maxFVar_622_);
if (lean_obj_tag(v___x_623_) == 1)
{
lean_object* v_val_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
lean_dec_ref_known(v_e_398_, 2);
v_val_624_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_623_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_val_624_);
lean_dec(v___x_623_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
lean_ctor_set_tag(v___x_626_, 0);
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_val_624_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
else
{
lean_object* v___x_632_; 
lean_dec(v___x_623_);
lean_inc_ref(v_fn_615_);
v___x_632_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_fn_615_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v___x_634_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_633_);
lean_dec_ref_known(v___x_632_, 1);
lean_inc_ref(v_arg_616_);
v___x_634_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_arg_616_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; lean_object* v___x_636_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc(v_a_635_);
lean_dec_ref_known(v___x_634_, 1);
v___x_636_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_633_, v_a_635_, v_a_401_, v_a_403_, v_a_404_);
v___y_536_ = v___x_636_;
goto v___jp_535_;
}
else
{
lean_dec(v_a_633_);
v___y_536_ = v___x_634_;
goto v___jp_535_;
}
}
else
{
v___y_536_ = v___x_632_;
goto v___jp_535_;
}
}
}
}
}
case 6:
{
lean_object* v_binderType_639_; lean_object* v_body_640_; 
v_binderType_639_ = lean_ctor_get(v_e_398_, 1);
v_body_640_ = lean_ctor_get(v_e_398_, 2);
lean_inc_ref(v_body_640_);
lean_inc_ref(v_binderType_639_);
v_d_525_ = v_binderType_639_;
v_b_526_ = v_body_640_;
v___y_527_ = v_a_399_;
v___y_528_ = v_a_400_;
v___y_529_ = v_a_401_;
v___y_530_ = v_a_402_;
v___y_531_ = v_a_403_;
v___y_532_ = v_a_404_;
goto v___jp_524_;
}
case 7:
{
lean_object* v_binderType_641_; lean_object* v_body_642_; 
v_binderType_641_ = lean_ctor_get(v_e_398_, 1);
v_body_642_ = lean_ctor_get(v_e_398_, 2);
lean_inc_ref(v_body_642_);
lean_inc_ref(v_binderType_641_);
v_d_525_ = v_binderType_641_;
v_b_526_ = v_body_642_;
v___y_527_ = v_a_399_;
v___y_528_ = v_a_400_;
v___y_529_ = v_a_401_;
v___y_530_ = v_a_402_;
v___y_531_ = v_a_403_;
v___y_532_ = v_a_404_;
goto v___jp_524_;
}
case 8:
{
lean_object* v_type_643_; lean_object* v_value_644_; lean_object* v_body_645_; uint8_t v___y_647_; uint8_t v___x_670_; 
v_type_643_ = lean_ctor_get(v_e_398_, 1);
v_value_644_ = lean_ctor_get(v_e_398_, 2);
v_body_645_ = lean_ctor_get(v_e_398_, 3);
v___x_670_ = l_Lean_Expr_hasFVar(v_e_398_);
if (v___x_670_ == 0)
{
uint8_t v___x_671_; 
v___x_671_ = l_Lean_Expr_hasMVar(v_e_398_);
v___y_647_ = v___x_671_;
goto v___jp_646_;
}
else
{
v___y_647_ = v___x_670_;
goto v___jp_646_;
}
v___jp_646_:
{
if (v___y_647_ == 0)
{
lean_object* v___x_648_; lean_object* v___x_649_; 
lean_dec_ref_known(v_e_398_, 4);
v___x_648_ = lean_box(0);
v___x_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
return v___x_649_;
}
else
{
lean_object* v___x_650_; lean_object* v_maxFVar_651_; lean_object* v___x_652_; 
v___x_650_ = lean_st_ref_get(v_a_400_);
v_maxFVar_651_ = lean_ctor_get(v___x_650_, 1);
lean_inc_ref(v_maxFVar_651_);
lean_dec(v___x_650_);
v___x_652_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_651_, v_e_398_);
lean_dec_ref(v_maxFVar_651_);
if (lean_obj_tag(v___x_652_) == 1)
{
lean_object* v_val_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_660_; 
lean_dec_ref_known(v_e_398_, 4);
v_val_653_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_660_ == 0)
{
v___x_655_ = v___x_652_;
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_val_653_);
lean_dec(v___x_652_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
lean_ctor_set_tag(v___x_655_, 0);
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_val_653_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
else
{
lean_object* v___x_661_; 
lean_dec(v___x_652_);
lean_inc_ref(v_type_643_);
v___x_661_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_type_643_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; lean_object* v___x_663_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_a_662_);
lean_dec_ref_known(v___x_661_, 1);
lean_inc_ref(v_value_644_);
v___x_663_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_value_644_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v_a_664_; lean_object* v___x_665_; 
v_a_664_ = lean_ctor_get(v___x_663_, 0);
lean_inc(v_a_664_);
lean_dec_ref_known(v___x_663_, 1);
v___x_665_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_662_, v_a_664_, v_a_401_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_a_666_; lean_object* v___x_667_; 
v_a_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_a_666_);
lean_dec_ref_known(v___x_665_, 1);
lean_inc_ref(v_body_645_);
v___x_667_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_body_645_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v_a_668_; lean_object* v___x_669_; 
v_a_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc(v_a_668_);
lean_dec_ref_known(v___x_667_, 1);
v___x_669_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_666_, v_a_668_, v_a_401_, v_a_403_, v_a_404_);
v___y_407_ = v___x_669_;
goto v___jp_406_;
}
else
{
lean_dec(v_a_666_);
v___y_407_ = v___x_667_;
goto v___jp_406_;
}
}
else
{
v___y_407_ = v___x_665_;
goto v___jp_406_;
}
}
else
{
lean_dec(v_a_662_);
v___y_407_ = v___x_663_;
goto v___jp_406_;
}
}
else
{
v___y_407_ = v___x_661_;
goto v___jp_406_;
}
}
}
}
}
case 10:
{
lean_object* v_expr_672_; uint8_t v___y_674_; uint8_t v___x_719_; 
v_expr_672_ = lean_ctor_get(v_e_398_, 1);
lean_inc_ref(v_expr_672_);
lean_dec_ref_known(v_e_398_, 2);
v___x_719_ = l_Lean_Expr_hasFVar(v_expr_672_);
if (v___x_719_ == 0)
{
uint8_t v___x_720_; 
v___x_720_ = l_Lean_Expr_hasMVar(v_expr_672_);
v___y_674_ = v___x_720_;
goto v___jp_673_;
}
else
{
v___y_674_ = v___x_719_;
goto v___jp_673_;
}
v___jp_673_:
{
if (v___y_674_ == 0)
{
lean_object* v___x_675_; lean_object* v___x_676_; 
lean_dec_ref(v_expr_672_);
v___x_675_ = lean_box(0);
v___x_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
return v___x_676_;
}
else
{
lean_object* v___x_677_; lean_object* v_maxFVar_678_; lean_object* v___x_679_; 
v___x_677_ = lean_st_ref_get(v_a_400_);
v_maxFVar_678_ = lean_ctor_get(v___x_677_, 1);
lean_inc_ref(v_maxFVar_678_);
lean_dec(v___x_677_);
v___x_679_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_678_, v_expr_672_);
lean_dec_ref(v_maxFVar_678_);
if (lean_obj_tag(v___x_679_) == 1)
{
lean_object* v_val_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_687_; 
lean_dec_ref(v_expr_672_);
v_val_680_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_687_ == 0)
{
v___x_682_ = v___x_679_;
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_val_680_);
lean_dec(v___x_679_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
if (v_isShared_683_ == 0)
{
lean_ctor_set_tag(v___x_682_, 0);
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_val_680_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
else
{
lean_object* v___x_688_; 
lean_dec(v___x_679_);
lean_inc_ref(v_expr_672_);
v___x_688_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_expr_672_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_718_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_718_ == 0)
{
v___x_691_ = v___x_688_;
v_isShared_692_ = v_isSharedCheck_718_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_688_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_718_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_693_; lean_object* v_share_694_; lean_object* v_maxFVar_695_; lean_object* v_proofInstInfo_696_; lean_object* v_inferType_697_; lean_object* v_getLevel_698_; lean_object* v_congrInfo_699_; lean_object* v_defEqI_700_; lean_object* v_extensions_701_; lean_object* v_issues_702_; lean_object* v_canon_703_; lean_object* v_instanceOverrides_704_; uint8_t v_debug_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_717_; 
v___x_693_ = lean_st_ref_take(v_a_400_);
v_share_694_ = lean_ctor_get(v___x_693_, 0);
v_maxFVar_695_ = lean_ctor_get(v___x_693_, 1);
v_proofInstInfo_696_ = lean_ctor_get(v___x_693_, 2);
v_inferType_697_ = lean_ctor_get(v___x_693_, 3);
v_getLevel_698_ = lean_ctor_get(v___x_693_, 4);
v_congrInfo_699_ = lean_ctor_get(v___x_693_, 5);
v_defEqI_700_ = lean_ctor_get(v___x_693_, 6);
v_extensions_701_ = lean_ctor_get(v___x_693_, 7);
v_issues_702_ = lean_ctor_get(v___x_693_, 8);
v_canon_703_ = lean_ctor_get(v___x_693_, 9);
v_instanceOverrides_704_ = lean_ctor_get(v___x_693_, 10);
v_debug_705_ = lean_ctor_get_uint8(v___x_693_, sizeof(void*)*11);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_717_ == 0)
{
v___x_707_ = v___x_693_;
v_isShared_708_ = v_isSharedCheck_717_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_instanceOverrides_704_);
lean_inc(v_canon_703_);
lean_inc(v_issues_702_);
lean_inc(v_extensions_701_);
lean_inc(v_defEqI_700_);
lean_inc(v_congrInfo_699_);
lean_inc(v_getLevel_698_);
lean_inc(v_inferType_697_);
lean_inc(v_proofInstInfo_696_);
lean_inc(v_maxFVar_695_);
lean_inc(v_share_694_);
lean_dec(v___x_693_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_717_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_709_; lean_object* v___x_711_; 
lean_inc(v_a_689_);
v___x_709_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_695_, v_expr_672_, v_a_689_);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 1, v___x_709_);
v___x_711_ = v___x_707_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_share_694_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v___x_709_);
lean_ctor_set(v_reuseFailAlloc_716_, 2, v_proofInstInfo_696_);
lean_ctor_set(v_reuseFailAlloc_716_, 3, v_inferType_697_);
lean_ctor_set(v_reuseFailAlloc_716_, 4, v_getLevel_698_);
lean_ctor_set(v_reuseFailAlloc_716_, 5, v_congrInfo_699_);
lean_ctor_set(v_reuseFailAlloc_716_, 6, v_defEqI_700_);
lean_ctor_set(v_reuseFailAlloc_716_, 7, v_extensions_701_);
lean_ctor_set(v_reuseFailAlloc_716_, 8, v_issues_702_);
lean_ctor_set(v_reuseFailAlloc_716_, 9, v_canon_703_);
lean_ctor_set(v_reuseFailAlloc_716_, 10, v_instanceOverrides_704_);
lean_ctor_set_uint8(v_reuseFailAlloc_716_, sizeof(void*)*11, v_debug_705_);
v___x_711_ = v_reuseFailAlloc_716_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
lean_object* v___x_712_; lean_object* v___x_714_; 
v___x_712_ = lean_st_ref_put(v_a_400_, v___x_711_);
if (v_isShared_692_ == 0)
{
v___x_714_ = v___x_691_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_689_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
}
else
{
lean_dec_ref(v_expr_672_);
return v___x_688_;
}
}
}
}
}
case 11:
{
lean_object* v_struct_721_; uint8_t v___y_723_; uint8_t v___x_768_; 
v_struct_721_ = lean_ctor_get(v_e_398_, 2);
v___x_768_ = l_Lean_Expr_hasFVar(v_e_398_);
if (v___x_768_ == 0)
{
uint8_t v___x_769_; 
v___x_769_ = l_Lean_Expr_hasMVar(v_e_398_);
v___y_723_ = v___x_769_;
goto v___jp_722_;
}
else
{
v___y_723_ = v___x_768_;
goto v___jp_722_;
}
v___jp_722_:
{
if (v___y_723_ == 0)
{
lean_object* v___x_724_; lean_object* v___x_725_; 
lean_dec_ref_known(v_e_398_, 3);
v___x_724_ = lean_box(0);
v___x_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
return v___x_725_;
}
else
{
lean_object* v___x_726_; lean_object* v_maxFVar_727_; lean_object* v___x_728_; 
v___x_726_ = lean_st_ref_get(v_a_400_);
v_maxFVar_727_ = lean_ctor_get(v___x_726_, 1);
lean_inc_ref(v_maxFVar_727_);
lean_dec(v___x_726_);
v___x_728_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_727_, v_e_398_);
lean_dec_ref(v_maxFVar_727_);
if (lean_obj_tag(v___x_728_) == 1)
{
lean_object* v_val_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_736_; 
lean_dec_ref_known(v_e_398_, 3);
v_val_729_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_736_ == 0)
{
v___x_731_ = v___x_728_;
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_val_729_);
lean_dec(v___x_728_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_734_; 
if (v_isShared_732_ == 0)
{
lean_ctor_set_tag(v___x_731_, 0);
v___x_734_ = v___x_731_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_val_729_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
else
{
lean_object* v___x_737_; 
lean_dec(v___x_728_);
lean_inc_ref(v_struct_721_);
v___x_737_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_struct_721_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_767_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_767_ == 0)
{
v___x_740_ = v___x_737_;
v_isShared_741_ = v_isSharedCheck_767_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_737_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_767_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_742_; lean_object* v_share_743_; lean_object* v_maxFVar_744_; lean_object* v_proofInstInfo_745_; lean_object* v_inferType_746_; lean_object* v_getLevel_747_; lean_object* v_congrInfo_748_; lean_object* v_defEqI_749_; lean_object* v_extensions_750_; lean_object* v_issues_751_; lean_object* v_canon_752_; lean_object* v_instanceOverrides_753_; uint8_t v_debug_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_766_; 
v___x_742_ = lean_st_ref_take(v_a_400_);
v_share_743_ = lean_ctor_get(v___x_742_, 0);
v_maxFVar_744_ = lean_ctor_get(v___x_742_, 1);
v_proofInstInfo_745_ = lean_ctor_get(v___x_742_, 2);
v_inferType_746_ = lean_ctor_get(v___x_742_, 3);
v_getLevel_747_ = lean_ctor_get(v___x_742_, 4);
v_congrInfo_748_ = lean_ctor_get(v___x_742_, 5);
v_defEqI_749_ = lean_ctor_get(v___x_742_, 6);
v_extensions_750_ = lean_ctor_get(v___x_742_, 7);
v_issues_751_ = lean_ctor_get(v___x_742_, 8);
v_canon_752_ = lean_ctor_get(v___x_742_, 9);
v_instanceOverrides_753_ = lean_ctor_get(v___x_742_, 10);
v_debug_754_ = lean_ctor_get_uint8(v___x_742_, sizeof(void*)*11);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_766_ == 0)
{
v___x_756_ = v___x_742_;
v_isShared_757_ = v_isSharedCheck_766_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_instanceOverrides_753_);
lean_inc(v_canon_752_);
lean_inc(v_issues_751_);
lean_inc(v_extensions_750_);
lean_inc(v_defEqI_749_);
lean_inc(v_congrInfo_748_);
lean_inc(v_getLevel_747_);
lean_inc(v_inferType_746_);
lean_inc(v_proofInstInfo_745_);
lean_inc(v_maxFVar_744_);
lean_inc(v_share_743_);
lean_dec(v___x_742_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_766_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_758_; lean_object* v___x_760_; 
lean_inc(v_a_738_);
v___x_758_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_744_, v_e_398_, v_a_738_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 1, v___x_758_);
v___x_760_ = v___x_756_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_share_743_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_765_, 2, v_proofInstInfo_745_);
lean_ctor_set(v_reuseFailAlloc_765_, 3, v_inferType_746_);
lean_ctor_set(v_reuseFailAlloc_765_, 4, v_getLevel_747_);
lean_ctor_set(v_reuseFailAlloc_765_, 5, v_congrInfo_748_);
lean_ctor_set(v_reuseFailAlloc_765_, 6, v_defEqI_749_);
lean_ctor_set(v_reuseFailAlloc_765_, 7, v_extensions_750_);
lean_ctor_set(v_reuseFailAlloc_765_, 8, v_issues_751_);
lean_ctor_set(v_reuseFailAlloc_765_, 9, v_canon_752_);
lean_ctor_set(v_reuseFailAlloc_765_, 10, v_instanceOverrides_753_);
lean_ctor_set_uint8(v_reuseFailAlloc_765_, sizeof(void*)*11, v_debug_754_);
v___x_760_ = v_reuseFailAlloc_765_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_761_; lean_object* v___x_763_; 
v___x_761_ = lean_st_ref_put(v_a_400_, v___x_760_);
if (v_isShared_741_ == 0)
{
v___x_763_ = v___x_740_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_738_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_398_, 3);
return v___x_737_;
}
}
}
}
}
default: 
{
lean_object* v___x_770_; lean_object* v___x_771_; 
lean_dec_ref(v_e_398_);
v___x_770_ = lean_box(0);
v___x_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
return v___x_771_;
}
}
v___jp_406_:
{
if (lean_obj_tag(v___y_407_) == 0)
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_437_; 
v_a_408_ = lean_ctor_get(v___y_407_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___y_407_);
if (v_isSharedCheck_437_ == 0)
{
v___x_410_ = v___y_407_;
v_isShared_411_ = v_isSharedCheck_437_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___y_407_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_437_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_412_; lean_object* v_share_413_; lean_object* v_maxFVar_414_; lean_object* v_proofInstInfo_415_; lean_object* v_inferType_416_; lean_object* v_getLevel_417_; lean_object* v_congrInfo_418_; lean_object* v_defEqI_419_; lean_object* v_extensions_420_; lean_object* v_issues_421_; lean_object* v_canon_422_; lean_object* v_instanceOverrides_423_; uint8_t v_debug_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_436_; 
v___x_412_ = lean_st_ref_take(v_a_400_);
v_share_413_ = lean_ctor_get(v___x_412_, 0);
v_maxFVar_414_ = lean_ctor_get(v___x_412_, 1);
v_proofInstInfo_415_ = lean_ctor_get(v___x_412_, 2);
v_inferType_416_ = lean_ctor_get(v___x_412_, 3);
v_getLevel_417_ = lean_ctor_get(v___x_412_, 4);
v_congrInfo_418_ = lean_ctor_get(v___x_412_, 5);
v_defEqI_419_ = lean_ctor_get(v___x_412_, 6);
v_extensions_420_ = lean_ctor_get(v___x_412_, 7);
v_issues_421_ = lean_ctor_get(v___x_412_, 8);
v_canon_422_ = lean_ctor_get(v___x_412_, 9);
v_instanceOverrides_423_ = lean_ctor_get(v___x_412_, 10);
v_debug_424_ = lean_ctor_get_uint8(v___x_412_, sizeof(void*)*11);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_436_ == 0)
{
v___x_426_ = v___x_412_;
v_isShared_427_ = v_isSharedCheck_436_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_instanceOverrides_423_);
lean_inc(v_canon_422_);
lean_inc(v_issues_421_);
lean_inc(v_extensions_420_);
lean_inc(v_defEqI_419_);
lean_inc(v_congrInfo_418_);
lean_inc(v_getLevel_417_);
lean_inc(v_inferType_416_);
lean_inc(v_proofInstInfo_415_);
lean_inc(v_maxFVar_414_);
lean_inc(v_share_413_);
lean_dec(v___x_412_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_436_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_428_; lean_object* v___x_430_; 
lean_inc(v_a_408_);
v___x_428_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_414_, v_e_398_, v_a_408_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 1, v___x_428_);
v___x_430_ = v___x_426_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_share_413_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v___x_428_);
lean_ctor_set(v_reuseFailAlloc_435_, 2, v_proofInstInfo_415_);
lean_ctor_set(v_reuseFailAlloc_435_, 3, v_inferType_416_);
lean_ctor_set(v_reuseFailAlloc_435_, 4, v_getLevel_417_);
lean_ctor_set(v_reuseFailAlloc_435_, 5, v_congrInfo_418_);
lean_ctor_set(v_reuseFailAlloc_435_, 6, v_defEqI_419_);
lean_ctor_set(v_reuseFailAlloc_435_, 7, v_extensions_420_);
lean_ctor_set(v_reuseFailAlloc_435_, 8, v_issues_421_);
lean_ctor_set(v_reuseFailAlloc_435_, 9, v_canon_422_);
lean_ctor_set(v_reuseFailAlloc_435_, 10, v_instanceOverrides_423_);
lean_ctor_set_uint8(v_reuseFailAlloc_435_, sizeof(void*)*11, v_debug_424_);
v___x_430_ = v_reuseFailAlloc_435_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
lean_object* v___x_431_; lean_object* v___x_433_; 
v___x_431_ = lean_st_ref_put(v_a_400_, v___x_430_);
if (v_isShared_411_ == 0)
{
v___x_433_ = v___x_410_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_408_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_398_);
return v___y_407_;
}
}
v___jp_438_:
{
lean_object* v___x_440_; lean_object* v_share_441_; lean_object* v_maxFVar_442_; lean_object* v_proofInstInfo_443_; lean_object* v_inferType_444_; lean_object* v_getLevel_445_; lean_object* v_congrInfo_446_; lean_object* v_defEqI_447_; lean_object* v_extensions_448_; lean_object* v_issues_449_; lean_object* v_canon_450_; lean_object* v_instanceOverrides_451_; uint8_t v_debug_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_462_; 
v___x_440_ = lean_st_ref_take(v_a_400_);
v_share_441_ = lean_ctor_get(v___x_440_, 0);
v_maxFVar_442_ = lean_ctor_get(v___x_440_, 1);
v_proofInstInfo_443_ = lean_ctor_get(v___x_440_, 2);
v_inferType_444_ = lean_ctor_get(v___x_440_, 3);
v_getLevel_445_ = lean_ctor_get(v___x_440_, 4);
v_congrInfo_446_ = lean_ctor_get(v___x_440_, 5);
v_defEqI_447_ = lean_ctor_get(v___x_440_, 6);
v_extensions_448_ = lean_ctor_get(v___x_440_, 7);
v_issues_449_ = lean_ctor_get(v___x_440_, 8);
v_canon_450_ = lean_ctor_get(v___x_440_, 9);
v_instanceOverrides_451_ = lean_ctor_get(v___x_440_, 10);
v_debug_452_ = lean_ctor_get_uint8(v___x_440_, sizeof(void*)*11);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_462_ == 0)
{
v___x_454_ = v___x_440_;
v_isShared_455_ = v_isSharedCheck_462_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_instanceOverrides_451_);
lean_inc(v_canon_450_);
lean_inc(v_issues_449_);
lean_inc(v_extensions_448_);
lean_inc(v_defEqI_447_);
lean_inc(v_congrInfo_446_);
lean_inc(v_getLevel_445_);
lean_inc(v_inferType_444_);
lean_inc(v_proofInstInfo_443_);
lean_inc(v_maxFVar_442_);
lean_inc(v_share_441_);
lean_dec(v___x_440_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_462_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_456_; lean_object* v___x_458_; 
lean_inc(v_a_439_);
v___x_456_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_442_, v_e_398_, v_a_439_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 1, v___x_456_);
v___x_458_ = v___x_454_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_share_441_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v___x_456_);
lean_ctor_set(v_reuseFailAlloc_461_, 2, v_proofInstInfo_443_);
lean_ctor_set(v_reuseFailAlloc_461_, 3, v_inferType_444_);
lean_ctor_set(v_reuseFailAlloc_461_, 4, v_getLevel_445_);
lean_ctor_set(v_reuseFailAlloc_461_, 5, v_congrInfo_446_);
lean_ctor_set(v_reuseFailAlloc_461_, 6, v_defEqI_447_);
lean_ctor_set(v_reuseFailAlloc_461_, 7, v_extensions_448_);
lean_ctor_set(v_reuseFailAlloc_461_, 8, v_issues_449_);
lean_ctor_set(v_reuseFailAlloc_461_, 9, v_canon_450_);
lean_ctor_set(v_reuseFailAlloc_461_, 10, v_instanceOverrides_451_);
lean_ctor_set_uint8(v_reuseFailAlloc_461_, sizeof(void*)*11, v_debug_452_);
v___x_458_ = v_reuseFailAlloc_461_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = lean_st_ref_put(v_a_400_, v___x_458_);
v___x_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_460_, 0, v_a_439_);
return v___x_460_;
}
}
}
v___jp_463_:
{
if (lean_obj_tag(v___y_465_) == 0)
{
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_495_; 
v_a_466_ = lean_ctor_get(v___y_465_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___y_465_);
if (v_isSharedCheck_495_ == 0)
{
v___x_468_ = v___y_465_;
v_isShared_469_ = v_isSharedCheck_495_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___y_465_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_495_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; lean_object* v_share_471_; lean_object* v_maxFVar_472_; lean_object* v_proofInstInfo_473_; lean_object* v_inferType_474_; lean_object* v_getLevel_475_; lean_object* v_congrInfo_476_; lean_object* v_defEqI_477_; lean_object* v_extensions_478_; lean_object* v_issues_479_; lean_object* v_canon_480_; lean_object* v_instanceOverrides_481_; uint8_t v_debug_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_494_; 
v___x_470_ = lean_st_ref_take(v___y_464_);
v_share_471_ = lean_ctor_get(v___x_470_, 0);
v_maxFVar_472_ = lean_ctor_get(v___x_470_, 1);
v_proofInstInfo_473_ = lean_ctor_get(v___x_470_, 2);
v_inferType_474_ = lean_ctor_get(v___x_470_, 3);
v_getLevel_475_ = lean_ctor_get(v___x_470_, 4);
v_congrInfo_476_ = lean_ctor_get(v___x_470_, 5);
v_defEqI_477_ = lean_ctor_get(v___x_470_, 6);
v_extensions_478_ = lean_ctor_get(v___x_470_, 7);
v_issues_479_ = lean_ctor_get(v___x_470_, 8);
v_canon_480_ = lean_ctor_get(v___x_470_, 9);
v_instanceOverrides_481_ = lean_ctor_get(v___x_470_, 10);
v_debug_482_ = lean_ctor_get_uint8(v___x_470_, sizeof(void*)*11);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_494_ == 0)
{
v___x_484_ = v___x_470_;
v_isShared_485_ = v_isSharedCheck_494_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_instanceOverrides_481_);
lean_inc(v_canon_480_);
lean_inc(v_issues_479_);
lean_inc(v_extensions_478_);
lean_inc(v_defEqI_477_);
lean_inc(v_congrInfo_476_);
lean_inc(v_getLevel_475_);
lean_inc(v_inferType_474_);
lean_inc(v_proofInstInfo_473_);
lean_inc(v_maxFVar_472_);
lean_inc(v_share_471_);
lean_dec(v___x_470_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_494_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_486_; lean_object* v___x_488_; 
lean_inc(v_a_466_);
v___x_486_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_472_, v_e_398_, v_a_466_);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 1, v___x_486_);
v___x_488_ = v___x_484_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_share_471_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v___x_486_);
lean_ctor_set(v_reuseFailAlloc_493_, 2, v_proofInstInfo_473_);
lean_ctor_set(v_reuseFailAlloc_493_, 3, v_inferType_474_);
lean_ctor_set(v_reuseFailAlloc_493_, 4, v_getLevel_475_);
lean_ctor_set(v_reuseFailAlloc_493_, 5, v_congrInfo_476_);
lean_ctor_set(v_reuseFailAlloc_493_, 6, v_defEqI_477_);
lean_ctor_set(v_reuseFailAlloc_493_, 7, v_extensions_478_);
lean_ctor_set(v_reuseFailAlloc_493_, 8, v_issues_479_);
lean_ctor_set(v_reuseFailAlloc_493_, 9, v_canon_480_);
lean_ctor_set(v_reuseFailAlloc_493_, 10, v_instanceOverrides_481_);
lean_ctor_set_uint8(v_reuseFailAlloc_493_, sizeof(void*)*11, v_debug_482_);
v___x_488_ = v_reuseFailAlloc_493_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
lean_object* v___x_489_; lean_object* v___x_491_; 
v___x_489_ = lean_st_ref_put(v___y_464_, v___x_488_);
if (v_isShared_469_ == 0)
{
v___x_491_ = v___x_468_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_a_466_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_398_);
return v___y_465_;
}
}
v___jp_496_:
{
if (v___y_505_ == 0)
{
lean_object* v___x_506_; lean_object* v___x_507_; 
lean_dec_ref(v___y_502_);
lean_dec_ref(v___y_498_);
lean_dec_ref(v_e_398_);
v___x_506_ = lean_box(0);
v___x_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
return v___x_507_;
}
else
{
lean_object* v___x_508_; lean_object* v_maxFVar_509_; lean_object* v___x_510_; 
v___x_508_ = lean_st_ref_get(v___y_499_);
v_maxFVar_509_ = lean_ctor_get(v___x_508_, 1);
lean_inc_ref(v_maxFVar_509_);
lean_dec(v___x_508_);
v___x_510_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_509_, v_e_398_);
lean_dec_ref(v_maxFVar_509_);
if (lean_obj_tag(v___x_510_) == 1)
{
lean_object* v_val_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
lean_dec_ref(v___y_502_);
lean_dec_ref(v___y_498_);
lean_dec_ref(v_e_398_);
v_val_511_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_518_ == 0)
{
v___x_513_ = v___x_510_;
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_val_511_);
lean_dec(v___x_510_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
lean_ctor_set_tag(v___x_513_, 0);
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_val_511_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
else
{
lean_object* v___x_519_; 
lean_dec(v___x_510_);
v___x_519_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v___y_498_, v___y_500_, v___y_499_, v___y_497_, v___y_503_, v___y_501_, v___y_504_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; lean_object* v___x_521_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_a_520_);
lean_dec_ref_known(v___x_519_, 1);
v___x_521_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v___y_502_, v___y_500_, v___y_499_, v___y_497_, v___y_503_, v___y_501_, v___y_504_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; lean_object* v___x_523_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_a_522_);
lean_dec_ref_known(v___x_521_, 1);
v___x_523_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_520_, v_a_522_, v___y_497_, v___y_501_, v___y_504_);
v___y_464_ = v___y_499_;
v___y_465_ = v___x_523_;
goto v___jp_463_;
}
else
{
lean_dec(v_a_520_);
v___y_464_ = v___y_499_;
v___y_465_ = v___x_521_;
goto v___jp_463_;
}
}
else
{
lean_dec_ref(v___y_502_);
v___y_464_ = v___y_499_;
v___y_465_ = v___x_519_;
goto v___jp_463_;
}
}
}
}
v___jp_524_:
{
uint8_t v___x_533_; 
v___x_533_ = l_Lean_Expr_hasFVar(v_e_398_);
if (v___x_533_ == 0)
{
uint8_t v___x_534_; 
v___x_534_ = l_Lean_Expr_hasMVar(v_e_398_);
v___y_497_ = v___y_529_;
v___y_498_ = v_d_525_;
v___y_499_ = v___y_528_;
v___y_500_ = v___y_527_;
v___y_501_ = v___y_531_;
v___y_502_ = v_b_526_;
v___y_503_ = v___y_530_;
v___y_504_ = v___y_532_;
v___y_505_ = v___x_534_;
goto v___jp_496_;
}
else
{
v___y_497_ = v___y_529_;
v___y_498_ = v_d_525_;
v___y_499_ = v___y_528_;
v___y_500_ = v___y_527_;
v___y_501_ = v___y_531_;
v___y_502_ = v_b_526_;
v___y_503_ = v___y_530_;
v___y_504_ = v___y_532_;
v___y_505_ = v___x_533_;
goto v___jp_496_;
}
}
v___jp_535_:
{
if (lean_obj_tag(v___y_536_) == 0)
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_566_; 
v_a_537_ = lean_ctor_get(v___y_536_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___y_536_);
if (v_isSharedCheck_566_ == 0)
{
v___x_539_ = v___y_536_;
v_isShared_540_ = v_isSharedCheck_566_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___y_536_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_566_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_541_; lean_object* v_share_542_; lean_object* v_maxFVar_543_; lean_object* v_proofInstInfo_544_; lean_object* v_inferType_545_; lean_object* v_getLevel_546_; lean_object* v_congrInfo_547_; lean_object* v_defEqI_548_; lean_object* v_extensions_549_; lean_object* v_issues_550_; lean_object* v_canon_551_; lean_object* v_instanceOverrides_552_; uint8_t v_debug_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_565_; 
v___x_541_ = lean_st_ref_take(v_a_400_);
v_share_542_ = lean_ctor_get(v___x_541_, 0);
v_maxFVar_543_ = lean_ctor_get(v___x_541_, 1);
v_proofInstInfo_544_ = lean_ctor_get(v___x_541_, 2);
v_inferType_545_ = lean_ctor_get(v___x_541_, 3);
v_getLevel_546_ = lean_ctor_get(v___x_541_, 4);
v_congrInfo_547_ = lean_ctor_get(v___x_541_, 5);
v_defEqI_548_ = lean_ctor_get(v___x_541_, 6);
v_extensions_549_ = lean_ctor_get(v___x_541_, 7);
v_issues_550_ = lean_ctor_get(v___x_541_, 8);
v_canon_551_ = lean_ctor_get(v___x_541_, 9);
v_instanceOverrides_552_ = lean_ctor_get(v___x_541_, 10);
v_debug_553_ = lean_ctor_get_uint8(v___x_541_, sizeof(void*)*11);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_565_ == 0)
{
v___x_555_ = v___x_541_;
v_isShared_556_ = v_isSharedCheck_565_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_instanceOverrides_552_);
lean_inc(v_canon_551_);
lean_inc(v_issues_550_);
lean_inc(v_extensions_549_);
lean_inc(v_defEqI_548_);
lean_inc(v_congrInfo_547_);
lean_inc(v_getLevel_546_);
lean_inc(v_inferType_545_);
lean_inc(v_proofInstInfo_544_);
lean_inc(v_maxFVar_543_);
lean_inc(v_share_542_);
lean_dec(v___x_541_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_565_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_557_; lean_object* v___x_559_; 
lean_inc(v_a_537_);
v___x_557_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_543_, v_e_398_, v_a_537_);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 1, v___x_557_);
v___x_559_ = v___x_555_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_share_542_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v___x_557_);
lean_ctor_set(v_reuseFailAlloc_564_, 2, v_proofInstInfo_544_);
lean_ctor_set(v_reuseFailAlloc_564_, 3, v_inferType_545_);
lean_ctor_set(v_reuseFailAlloc_564_, 4, v_getLevel_546_);
lean_ctor_set(v_reuseFailAlloc_564_, 5, v_congrInfo_547_);
lean_ctor_set(v_reuseFailAlloc_564_, 6, v_defEqI_548_);
lean_ctor_set(v_reuseFailAlloc_564_, 7, v_extensions_549_);
lean_ctor_set(v_reuseFailAlloc_564_, 8, v_issues_550_);
lean_ctor_set(v_reuseFailAlloc_564_, 9, v_canon_551_);
lean_ctor_set(v_reuseFailAlloc_564_, 10, v_instanceOverrides_552_);
lean_ctor_set_uint8(v_reuseFailAlloc_564_, sizeof(void*)*11, v_debug_553_);
v___x_559_ = v_reuseFailAlloc_564_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_560_; lean_object* v___x_562_; 
v___x_560_ = lean_st_ref_put(v_a_400_, v___x_559_);
if (v_isShared_540_ == 0)
{
v___x_562_ = v___x_539_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_a_537_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_398_);
return v___y_536_;
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0(lean_object* v_00_u03b2_781_, lean_object* v_x_782_, lean_object* v_x_783_, lean_object* v_x_784_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_x_782_, v_x_783_, v_x_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1(lean_object* v_00_u03b2_786_, lean_object* v_x_787_, lean_object* v_x_788_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_x_787_, v_x_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___boxed(lean_object* v_00_u03b2_790_, lean_object* v_x_791_, lean_object* v_x_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1(v_00_u03b2_790_, v_x_791_, v_x_792_);
lean_dec_ref(v_x_792_);
lean_dec_ref(v_x_791_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0(lean_object* v_00_u03b2_794_, lean_object* v_x_795_, size_t v_x_796_, size_t v_x_797_, lean_object* v_x_798_, lean_object* v_x_799_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_795_, v_x_796_, v_x_797_, v_x_798_, v_x_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_801_, lean_object* v_x_802_, lean_object* v_x_803_, lean_object* v_x_804_, lean_object* v_x_805_, lean_object* v_x_806_){
_start:
{
size_t v_x_6006__boxed_807_; size_t v_x_6007__boxed_808_; lean_object* v_res_809_; 
v_x_6006__boxed_807_ = lean_unbox_usize(v_x_803_);
lean_dec(v_x_803_);
v_x_6007__boxed_808_ = lean_unbox_usize(v_x_804_);
lean_dec(v_x_804_);
v_res_809_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0(v_00_u03b2_801_, v_x_802_, v_x_6006__boxed_807_, v_x_6007__boxed_808_, v_x_805_, v_x_806_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2(lean_object* v_00_u03b2_810_, lean_object* v_x_811_, size_t v_x_812_, lean_object* v_x_813_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_811_, v_x_812_, v_x_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_815_, lean_object* v_x_816_, lean_object* v_x_817_, lean_object* v_x_818_){
_start:
{
size_t v_x_6023__boxed_819_; lean_object* v_res_820_; 
v_x_6023__boxed_819_ = lean_unbox_usize(v_x_817_);
lean_dec(v_x_817_);
v_res_820_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2(v_00_u03b2_815_, v_x_816_, v_x_6023__boxed_819_, v_x_818_);
lean_dec_ref(v_x_818_);
lean_dec_ref(v_x_816_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_821_, lean_object* v_n_822_, lean_object* v_k_823_, lean_object* v_v_824_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(v_n_822_, v_k_823_, v_v_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_826_, size_t v_depth_827_, lean_object* v_keys_828_, lean_object* v_vals_829_, lean_object* v_heq_830_, lean_object* v_i_831_, lean_object* v_entries_832_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(v_depth_827_, v_keys_828_, v_vals_829_, v_i_831_, v_entries_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_834_, lean_object* v_depth_835_, lean_object* v_keys_836_, lean_object* v_vals_837_, lean_object* v_heq_838_, lean_object* v_i_839_, lean_object* v_entries_840_){
_start:
{
size_t v_depth_boxed_841_; lean_object* v_res_842_; 
v_depth_boxed_841_ = lean_unbox_usize(v_depth_835_);
lean_dec(v_depth_835_);
v_res_842_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3(v_00_u03b2_834_, v_depth_boxed_841_, v_keys_836_, v_vals_837_, v_heq_838_, v_i_839_, v_entries_840_);
lean_dec_ref(v_vals_837_);
lean_dec_ref(v_keys_836_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_843_, lean_object* v_keys_844_, lean_object* v_vals_845_, lean_object* v_heq_846_, lean_object* v_i_847_, lean_object* v_k_848_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_keys_844_, v_vals_845_, v_i_847_, v_k_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_850_, lean_object* v_keys_851_, lean_object* v_vals_852_, lean_object* v_heq_853_, lean_object* v_i_854_, lean_object* v_k_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6(v_00_u03b2_850_, v_keys_851_, v_vals_852_, v_heq_853_, v_i_854_, v_k_855_);
lean_dec_ref(v_k_855_);
lean_dec_ref(v_vals_852_);
lean_dec_ref(v_keys_851_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_857_, lean_object* v_x_858_, lean_object* v_x_859_, lean_object* v_x_860_, lean_object* v_x_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_x_858_, v_x_859_, v_x_860_, v_x_861_);
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
