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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_instInhabitedSymM(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
uint8_t v___y_88_; uint8_t v___x_135_; 
v___x_135_ = l_Lean_Expr_hasFVar(v_e_78_);
if (v___x_135_ == 0)
{
uint8_t v___x_136_; 
v___x_136_ = l_Lean_Expr_hasMVar(v_e_78_);
v___y_88_ = v___x_136_;
goto v___jp_87_;
}
else
{
v___y_88_ = v___x_135_;
goto v___jp_87_;
}
v___jp_87_:
{
if (v___y_88_ == 0)
{
lean_object* v___x_89_; lean_object* v___x_90_; 
lean_dec_ref(v_k_79_);
lean_dec_ref(v_e_78_);
v___x_89_ = lean_box(0);
v___x_90_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
return v___x_90_;
}
else
{
lean_object* v___x_91_; lean_object* v_maxFVar_92_; lean_object* v___f_93_; lean_object* v___f_94_; lean_object* v___x_95_; 
v___x_91_ = lean_st_ref_get(v_a_81_);
v_maxFVar_92_ = lean_ctor_get(v___x_91_, 1);
lean_inc_ref(v_maxFVar_92_);
lean_dec(v___x_91_);
v___f_93_ = ((lean_object*)(l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__0));
v___f_94_ = ((lean_object*)(l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__1));
lean_inc_ref(v_e_78_);
v___x_95_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_93_, v___f_94_, v_maxFVar_92_, v_e_78_);
lean_dec_ref(v_maxFVar_92_);
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
v___x_125_ = l_Lean_PersistentHashMap_insert___redArg(v___f_93_, v___f_94_, v_maxFVar_111_, v_e_78_, v_a_105_);
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
v___x_128_ = lean_st_ref_set(v_a_81_, v___x_127_);
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
lean_object* v___x_156_; lean_object* v___x_4742__overap_157_; lean_object* v___x_158_; 
v___x_156_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0, &l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0);
v___x_4742__overap_157_ = lean_panic_fn_borrowed(v___x_156_, v_msg_148_);
lean_inc(v___y_154_);
lean_inc_ref(v___y_153_);
lean_inc(v___y_152_);
lean_inc_ref(v___y_151_);
lean_inc(v___y_150_);
lean_inc_ref(v___y_149_);
v___x_158_ = lean_apply_7(v___x_4742__overap_157_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, lean_box(0));
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
lean_object* v_ks_259_; lean_object* v_vs_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_280_; 
v_ks_259_ = lean_ctor_get(v_x_206_, 0);
v_vs_260_ = lean_ctor_get(v_x_206_, 1);
v_isSharedCheck_280_ = !lean_is_exclusive(v_x_206_);
if (v_isSharedCheck_280_ == 0)
{
v___x_262_ = v_x_206_;
v_isShared_263_ = v_isSharedCheck_280_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_vs_260_);
lean_inc(v_ks_259_);
lean_dec(v_x_206_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_280_;
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
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_ks_259_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_vs_260_);
v___x_265_ = v_reuseFailAlloc_279_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
lean_object* v_newNode_266_; uint8_t v___y_268_; size_t v___x_274_; uint8_t v___x_275_; 
v_newNode_266_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(v___x_265_, v_x_209_, v_x_210_);
v___x_274_ = ((size_t)7ULL);
v___x_275_ = lean_usize_dec_le(v___x_274_, v_x_208_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_276_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_266_);
v___x_277_ = lean_unsigned_to_nat(4u);
v___x_278_ = lean_nat_dec_lt(v___x_276_, v___x_277_);
lean_dec(v___x_276_);
v___y_268_ = v___x_278_;
goto v___jp_267_;
}
else
{
v___y_268_ = v___x_275_;
goto v___jp_267_;
}
v___jp_267_:
{
if (v___y_268_ == 0)
{
lean_object* v_ks_269_; lean_object* v_vs_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v_ks_269_ = lean_ctor_get(v_newNode_266_, 0);
lean_inc_ref(v_ks_269_);
v_vs_270_ = lean_ctor_get(v_newNode_266_, 1);
lean_inc_ref(v_vs_270_);
lean_dec_ref(v_newNode_266_);
v___x_271_ = lean_unsigned_to_nat(0u);
v___x_272_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0);
v___x_273_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(v_x_208_, v_ks_269_, v_vs_270_, v___x_271_, v___x_272_);
lean_dec_ref(v_vs_270_);
lean_dec_ref(v_ks_269_);
return v___x_273_;
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
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(size_t v_depth_281_, lean_object* v_keys_282_, lean_object* v_vals_283_, lean_object* v_i_284_, lean_object* v_entries_285_){
_start:
{
lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_286_ = lean_array_get_size(v_keys_282_);
v___x_287_ = lean_nat_dec_lt(v_i_284_, v___x_286_);
if (v___x_287_ == 0)
{
lean_dec(v_i_284_);
return v_entries_285_;
}
else
{
lean_object* v_k_288_; lean_object* v_v_289_; size_t v___x_290_; size_t v___x_291_; size_t v___x_292_; uint64_t v___x_293_; size_t v_h_294_; size_t v___x_295_; lean_object* v___x_296_; size_t v___x_297_; size_t v___x_298_; size_t v___x_299_; size_t v_h_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v_k_288_ = lean_array_fget_borrowed(v_keys_282_, v_i_284_);
v_v_289_ = lean_array_fget_borrowed(v_vals_283_, v_i_284_);
v___x_290_ = lean_ptr_addr(v_k_288_);
v___x_291_ = ((size_t)3ULL);
v___x_292_ = lean_usize_shift_right(v___x_290_, v___x_291_);
v___x_293_ = lean_usize_to_uint64(v___x_292_);
v_h_294_ = lean_uint64_to_usize(v___x_293_);
v___x_295_ = ((size_t)5ULL);
v___x_296_ = lean_unsigned_to_nat(1u);
v___x_297_ = ((size_t)1ULL);
v___x_298_ = lean_usize_sub(v_depth_281_, v___x_297_);
v___x_299_ = lean_usize_mul(v___x_295_, v___x_298_);
v_h_300_ = lean_usize_shift_right(v_h_294_, v___x_299_);
v___x_301_ = lean_nat_add(v_i_284_, v___x_296_);
lean_dec(v_i_284_);
lean_inc(v_v_289_);
lean_inc(v_k_288_);
v___x_302_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_entries_285_, v_h_300_, v_depth_281_, v_k_288_, v_v_289_);
v_i_284_ = v___x_301_;
v_entries_285_ = v___x_302_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_304_, lean_object* v_keys_305_, lean_object* v_vals_306_, lean_object* v_i_307_, lean_object* v_entries_308_){
_start:
{
size_t v_depth_boxed_309_; lean_object* v_res_310_; 
v_depth_boxed_309_ = lean_unbox_usize(v_depth_304_);
lean_dec(v_depth_304_);
v_res_310_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(v_depth_boxed_309_, v_keys_305_, v_vals_306_, v_i_307_, v_entries_308_);
lean_dec_ref(v_vals_306_);
lean_dec_ref(v_keys_305_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_311_, lean_object* v_x_312_, lean_object* v_x_313_, lean_object* v_x_314_, lean_object* v_x_315_){
_start:
{
size_t v_x_5258__boxed_316_; size_t v_x_5259__boxed_317_; lean_object* v_res_318_; 
v_x_5258__boxed_316_ = lean_unbox_usize(v_x_312_);
lean_dec(v_x_312_);
v_x_5259__boxed_317_ = lean_unbox_usize(v_x_313_);
lean_dec(v_x_313_);
v_res_318_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_311_, v_x_5258__boxed_316_, v_x_5259__boxed_317_, v_x_314_, v_x_315_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(lean_object* v_x_319_, lean_object* v_x_320_, lean_object* v_x_321_){
_start:
{
size_t v___x_322_; size_t v___x_323_; size_t v___x_324_; uint64_t v___x_325_; size_t v___x_326_; size_t v___x_327_; lean_object* v___x_328_; 
v___x_322_ = lean_ptr_addr(v_x_320_);
v___x_323_ = ((size_t)3ULL);
v___x_324_ = lean_usize_shift_right(v___x_322_, v___x_323_);
v___x_325_ = lean_usize_to_uint64(v___x_324_);
v___x_326_ = lean_uint64_to_usize(v___x_325_);
v___x_327_ = ((size_t)1ULL);
v___x_328_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_319_, v___x_326_, v___x_327_, v_x_320_, v_x_321_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(lean_object* v_keys_329_, lean_object* v_vals_330_, lean_object* v_i_331_, lean_object* v_k_332_){
_start:
{
lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_333_ = lean_array_get_size(v_keys_329_);
v___x_334_ = lean_nat_dec_lt(v_i_331_, v___x_333_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; 
lean_dec(v_i_331_);
v___x_335_ = lean_box(0);
return v___x_335_;
}
else
{
lean_object* v_k_x27_336_; size_t v___x_337_; size_t v___x_338_; uint8_t v___x_339_; 
v_k_x27_336_ = lean_array_fget_borrowed(v_keys_329_, v_i_331_);
v___x_337_ = lean_ptr_addr(v_k_332_);
v___x_338_ = lean_ptr_addr(v_k_x27_336_);
v___x_339_ = lean_usize_dec_eq(v___x_337_, v___x_338_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = lean_unsigned_to_nat(1u);
v___x_341_ = lean_nat_add(v_i_331_, v___x_340_);
lean_dec(v_i_331_);
v_i_331_ = v___x_341_;
goto _start;
}
else
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = lean_array_fget_borrowed(v_vals_330_, v_i_331_);
lean_dec(v_i_331_);
lean_inc(v___x_343_);
v___x_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
return v___x_344_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_keys_345_, lean_object* v_vals_346_, lean_object* v_i_347_, lean_object* v_k_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_keys_345_, v_vals_346_, v_i_347_, v_k_348_);
lean_dec_ref(v_k_348_);
lean_dec_ref(v_vals_346_);
lean_dec_ref(v_keys_345_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(lean_object* v_x_350_, size_t v_x_351_, lean_object* v_x_352_){
_start:
{
if (lean_obj_tag(v_x_350_) == 0)
{
lean_object* v_es_353_; lean_object* v___x_354_; size_t v___x_355_; size_t v___x_356_; lean_object* v_j_357_; lean_object* v___x_358_; 
v_es_353_ = lean_ctor_get(v_x_350_, 0);
v___x_354_ = lean_box(2);
v___x_355_ = ((size_t)31ULL);
v___x_356_ = lean_usize_land(v_x_351_, v___x_355_);
v_j_357_ = lean_usize_to_nat(v___x_356_);
v___x_358_ = lean_array_get_borrowed(v___x_354_, v_es_353_, v_j_357_);
lean_dec(v_j_357_);
switch(lean_obj_tag(v___x_358_))
{
case 0:
{
lean_object* v_key_359_; lean_object* v_val_360_; size_t v___x_361_; size_t v___x_362_; uint8_t v___x_363_; 
v_key_359_ = lean_ctor_get(v___x_358_, 0);
v_val_360_ = lean_ctor_get(v___x_358_, 1);
v___x_361_ = lean_ptr_addr(v_x_352_);
v___x_362_ = lean_ptr_addr(v_key_359_);
v___x_363_ = lean_usize_dec_eq(v___x_361_, v___x_362_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; 
v___x_364_ = lean_box(0);
return v___x_364_;
}
else
{
lean_object* v___x_365_; 
lean_inc(v_val_360_);
v___x_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_365_, 0, v_val_360_);
return v___x_365_;
}
}
case 1:
{
lean_object* v_node_366_; size_t v___x_367_; size_t v___x_368_; 
v_node_366_ = lean_ctor_get(v___x_358_, 0);
v___x_367_ = ((size_t)5ULL);
v___x_368_ = lean_usize_shift_right(v_x_351_, v___x_367_);
v_x_350_ = v_node_366_;
v_x_351_ = v___x_368_;
goto _start;
}
default: 
{
lean_object* v___x_370_; 
v___x_370_ = lean_box(0);
return v___x_370_;
}
}
}
else
{
lean_object* v_ks_371_; lean_object* v_vs_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v_ks_371_ = lean_ctor_get(v_x_350_, 0);
v_vs_372_ = lean_ctor_get(v_x_350_, 1);
v___x_373_ = lean_unsigned_to_nat(0u);
v___x_374_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_ks_371_, v_vs_372_, v___x_373_, v_x_352_);
return v___x_374_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_x_375_, lean_object* v_x_376_, lean_object* v_x_377_){
_start:
{
size_t v_x_5463__boxed_378_; lean_object* v_res_379_; 
v_x_5463__boxed_378_ = lean_unbox_usize(v_x_376_);
lean_dec(v_x_376_);
v_res_379_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_375_, v_x_5463__boxed_378_, v_x_377_);
lean_dec_ref(v_x_377_);
lean_dec_ref(v_x_375_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(lean_object* v_x_380_, lean_object* v_x_381_){
_start:
{
size_t v___x_382_; size_t v___x_383_; size_t v___x_384_; uint64_t v___x_385_; size_t v___x_386_; lean_object* v___x_387_; 
v___x_382_ = lean_ptr_addr(v_x_381_);
v___x_383_ = ((size_t)3ULL);
v___x_384_ = lean_usize_shift_right(v___x_382_, v___x_383_);
v___x_385_ = lean_usize_to_uint64(v___x_384_);
v___x_386_ = lean_uint64_to_usize(v___x_385_);
v___x_387_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_380_, v___x_386_, v_x_381_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg___boxed(lean_object* v_x_388_, lean_object* v_x_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_x_388_, v_x_389_);
lean_dec_ref(v_x_389_);
lean_dec_ref(v_x_388_);
return v_res_390_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_394_ = ((lean_object*)(l_Lean_Meta_Sym_getMaxFVar_x3f___closed__2));
v___x_395_ = lean_unsigned_to_nat(37u);
v___x_396_ = lean_unsigned_to_nat(52u);
v___x_397_ = ((lean_object*)(l_Lean_Meta_Sym_getMaxFVar_x3f___closed__1));
v___x_398_ = ((lean_object*)(l_Lean_Meta_Sym_getMaxFVar_x3f___closed__0));
v___x_399_ = l_mkPanicMessageWithDecl(v___x_398_, v___x_397_, v___x_396_, v___x_395_, v___x_394_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f(lean_object* v_e_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
lean_object* v___y_409_; lean_object* v_a_441_; lean_object* v___y_466_; lean_object* v___y_467_; lean_object* v___y_499_; lean_object* v___y_500_; lean_object* v___y_501_; lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v___y_504_; lean_object* v___y_505_; lean_object* v___y_506_; uint8_t v___y_507_; lean_object* v_d_527_; lean_object* v_b_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_538_; 
switch(lean_obj_tag(v_e_400_))
{
case 1:
{
lean_object* v_fvarId_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v_fvarId_569_ = lean_ctor_get(v_e_400_, 0);
lean_inc(v_fvarId_569_);
lean_dec_ref_known(v_e_400_, 1);
v___x_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_570_, 0, v_fvarId_569_);
v___x_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
return v___x_571_;
}
case 2:
{
lean_object* v_mvarId_572_; uint8_t v___y_574_; uint8_t v___x_615_; 
v_mvarId_572_ = lean_ctor_get(v_e_400_, 0);
v___x_615_ = l_Lean_Expr_hasFVar(v_e_400_);
if (v___x_615_ == 0)
{
uint8_t v___x_616_; 
v___x_616_ = l_Lean_Expr_hasMVar(v_e_400_);
v___y_574_ = v___x_616_;
goto v___jp_573_;
}
else
{
v___y_574_ = v___x_615_;
goto v___jp_573_;
}
v___jp_573_:
{
if (v___y_574_ == 0)
{
lean_object* v___x_575_; lean_object* v___x_576_; 
lean_dec_ref_known(v_e_400_, 1);
v___x_575_ = lean_box(0);
v___x_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
return v___x_576_;
}
else
{
lean_object* v___x_577_; lean_object* v_maxFVar_578_; lean_object* v___x_579_; 
v___x_577_ = lean_st_ref_get(v_a_402_);
v_maxFVar_578_ = lean_ctor_get(v___x_577_, 1);
lean_inc_ref(v_maxFVar_578_);
lean_dec(v___x_577_);
v___x_579_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_578_, v_e_400_);
lean_dec_ref(v_maxFVar_578_);
if (lean_obj_tag(v___x_579_) == 1)
{
lean_object* v_val_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
lean_dec_ref_known(v_e_400_, 1);
v_val_580_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_579_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_val_580_);
lean_dec(v___x_579_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
lean_ctor_set_tag(v___x_582_, 0);
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_val_580_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
else
{
lean_object* v___x_588_; 
lean_dec(v___x_579_);
lean_inc(v_mvarId_572_);
v___x_588_ = l_Lean_MVarId_getDecl(v_mvarId_572_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v_a_589_; lean_object* v_lctx_590_; lean_object* v_decls_591_; uint8_t v___x_592_; 
v_a_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_a_589_);
lean_dec_ref_known(v___x_588_, 1);
v_lctx_590_ = lean_ctor_get(v_a_589_, 1);
lean_inc_ref(v_lctx_590_);
lean_dec(v_a_589_);
v_decls_591_ = lean_ctor_get(v_lctx_590_, 1);
v___x_592_ = l_Lean_PersistentArray_isEmpty___redArg(v_decls_591_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; 
v___x_593_ = l_Lean_LocalContext_lastDecl(v_lctx_590_);
lean_dec_ref(v_lctx_590_);
if (lean_obj_tag(v___x_593_) == 1)
{
lean_object* v_val_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_602_; 
v_val_594_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_602_ == 0)
{
v___x_596_ = v___x_593_;
v_isShared_597_ = v_isSharedCheck_602_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_val_594_);
lean_dec(v___x_593_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_602_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_598_; lean_object* v___x_600_; 
v___x_598_ = l_Lean_LocalDecl_fvarId(v_val_594_);
lean_dec(v_val_594_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 0, v___x_598_);
v___x_600_ = v___x_596_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_598_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
v_a_441_ = v___x_600_;
goto v___jp_440_;
}
}
}
else
{
lean_object* v___x_603_; lean_object* v___x_604_; 
lean_dec(v___x_593_);
v___x_603_ = lean_obj_once(&l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3, &l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3_once, _init_l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3);
v___x_604_ = l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2(v___x_603_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc(v_a_605_);
lean_dec_ref_known(v___x_604_, 1);
v_a_441_ = v_a_605_;
goto v___jp_440_;
}
else
{
lean_dec_ref_known(v_e_400_, 1);
return v___x_604_;
}
}
}
else
{
lean_object* v___x_606_; 
lean_dec_ref(v_lctx_590_);
v___x_606_ = lean_box(0);
v_a_441_ = v___x_606_;
goto v___jp_440_;
}
}
else
{
lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
lean_dec_ref_known(v_e_400_, 1);
v_a_607_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_614_ == 0)
{
v___x_609_ = v___x_588_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v___x_588_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_612_; 
if (v_isShared_610_ == 0)
{
v___x_612_ = v___x_609_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_a_607_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
}
}
}
case 5:
{
lean_object* v_fn_617_; lean_object* v_arg_618_; uint8_t v___y_620_; uint8_t v___x_639_; 
v_fn_617_ = lean_ctor_get(v_e_400_, 0);
v_arg_618_ = lean_ctor_get(v_e_400_, 1);
v___x_639_ = l_Lean_Expr_hasFVar(v_e_400_);
if (v___x_639_ == 0)
{
uint8_t v___x_640_; 
v___x_640_ = l_Lean_Expr_hasMVar(v_e_400_);
v___y_620_ = v___x_640_;
goto v___jp_619_;
}
else
{
v___y_620_ = v___x_639_;
goto v___jp_619_;
}
v___jp_619_:
{
if (v___y_620_ == 0)
{
lean_object* v___x_621_; lean_object* v___x_622_; 
lean_dec_ref_known(v_e_400_, 2);
v___x_621_ = lean_box(0);
v___x_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
return v___x_622_;
}
else
{
lean_object* v___x_623_; lean_object* v_maxFVar_624_; lean_object* v___x_625_; 
v___x_623_ = lean_st_ref_get(v_a_402_);
v_maxFVar_624_ = lean_ctor_get(v___x_623_, 1);
lean_inc_ref(v_maxFVar_624_);
lean_dec(v___x_623_);
v___x_625_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_624_, v_e_400_);
lean_dec_ref(v_maxFVar_624_);
if (lean_obj_tag(v___x_625_) == 1)
{
lean_object* v_val_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_633_; 
lean_dec_ref_known(v_e_400_, 2);
v_val_626_ = lean_ctor_get(v___x_625_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_633_ == 0)
{
v___x_628_ = v___x_625_;
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_val_626_);
lean_dec(v___x_625_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_629_ == 0)
{
lean_ctor_set_tag(v___x_628_, 0);
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_val_626_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
else
{
lean_object* v___x_634_; 
lean_dec(v___x_625_);
lean_inc_ref(v_fn_617_);
v___x_634_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_fn_617_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; lean_object* v___x_636_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc(v_a_635_);
lean_dec_ref_known(v___x_634_, 1);
lean_inc_ref(v_arg_618_);
v___x_636_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_arg_618_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_a_637_; lean_object* v___x_638_; 
v_a_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc(v_a_637_);
lean_dec_ref_known(v___x_636_, 1);
v___x_638_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_635_, v_a_637_, v_a_403_, v_a_405_, v_a_406_);
v___y_538_ = v___x_638_;
goto v___jp_537_;
}
else
{
lean_dec(v_a_635_);
v___y_538_ = v___x_636_;
goto v___jp_537_;
}
}
else
{
v___y_538_ = v___x_634_;
goto v___jp_537_;
}
}
}
}
}
case 6:
{
lean_object* v_binderType_641_; lean_object* v_body_642_; 
v_binderType_641_ = lean_ctor_get(v_e_400_, 1);
v_body_642_ = lean_ctor_get(v_e_400_, 2);
lean_inc_ref(v_body_642_);
lean_inc_ref(v_binderType_641_);
v_d_527_ = v_binderType_641_;
v_b_528_ = v_body_642_;
v___y_529_ = v_a_401_;
v___y_530_ = v_a_402_;
v___y_531_ = v_a_403_;
v___y_532_ = v_a_404_;
v___y_533_ = v_a_405_;
v___y_534_ = v_a_406_;
goto v___jp_526_;
}
case 7:
{
lean_object* v_binderType_643_; lean_object* v_body_644_; 
v_binderType_643_ = lean_ctor_get(v_e_400_, 1);
v_body_644_ = lean_ctor_get(v_e_400_, 2);
lean_inc_ref(v_body_644_);
lean_inc_ref(v_binderType_643_);
v_d_527_ = v_binderType_643_;
v_b_528_ = v_body_644_;
v___y_529_ = v_a_401_;
v___y_530_ = v_a_402_;
v___y_531_ = v_a_403_;
v___y_532_ = v_a_404_;
v___y_533_ = v_a_405_;
v___y_534_ = v_a_406_;
goto v___jp_526_;
}
case 8:
{
lean_object* v_type_645_; lean_object* v_value_646_; lean_object* v_body_647_; uint8_t v___y_649_; uint8_t v___x_672_; 
v_type_645_ = lean_ctor_get(v_e_400_, 1);
v_value_646_ = lean_ctor_get(v_e_400_, 2);
v_body_647_ = lean_ctor_get(v_e_400_, 3);
v___x_672_ = l_Lean_Expr_hasFVar(v_e_400_);
if (v___x_672_ == 0)
{
uint8_t v___x_673_; 
v___x_673_ = l_Lean_Expr_hasMVar(v_e_400_);
v___y_649_ = v___x_673_;
goto v___jp_648_;
}
else
{
v___y_649_ = v___x_672_;
goto v___jp_648_;
}
v___jp_648_:
{
if (v___y_649_ == 0)
{
lean_object* v___x_650_; lean_object* v___x_651_; 
lean_dec_ref_known(v_e_400_, 4);
v___x_650_ = lean_box(0);
v___x_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
return v___x_651_;
}
else
{
lean_object* v___x_652_; lean_object* v_maxFVar_653_; lean_object* v___x_654_; 
v___x_652_ = lean_st_ref_get(v_a_402_);
v_maxFVar_653_ = lean_ctor_get(v___x_652_, 1);
lean_inc_ref(v_maxFVar_653_);
lean_dec(v___x_652_);
v___x_654_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_653_, v_e_400_);
lean_dec_ref(v_maxFVar_653_);
if (lean_obj_tag(v___x_654_) == 1)
{
lean_object* v_val_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_662_; 
lean_dec_ref_known(v_e_400_, 4);
v_val_655_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_662_ == 0)
{
v___x_657_ = v___x_654_;
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_val_655_);
lean_dec(v___x_654_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_660_; 
if (v_isShared_658_ == 0)
{
lean_ctor_set_tag(v___x_657_, 0);
v___x_660_ = v___x_657_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_val_655_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
else
{
lean_object* v___x_663_; 
lean_dec(v___x_654_);
lean_inc_ref(v_type_645_);
v___x_663_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_type_645_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v_a_664_; lean_object* v___x_665_; 
v_a_664_ = lean_ctor_get(v___x_663_, 0);
lean_inc(v_a_664_);
lean_dec_ref_known(v___x_663_, 1);
lean_inc_ref(v_value_646_);
v___x_665_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_value_646_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_a_666_; lean_object* v___x_667_; 
v_a_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_a_666_);
lean_dec_ref_known(v___x_665_, 1);
v___x_667_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_664_, v_a_666_, v_a_403_, v_a_405_, v_a_406_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v_a_668_; lean_object* v___x_669_; 
v_a_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc(v_a_668_);
lean_dec_ref_known(v___x_667_, 1);
lean_inc_ref(v_body_647_);
v___x_669_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_body_647_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; lean_object* v___x_671_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_a_670_);
lean_dec_ref_known(v___x_669_, 1);
v___x_671_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_668_, v_a_670_, v_a_403_, v_a_405_, v_a_406_);
v___y_409_ = v___x_671_;
goto v___jp_408_;
}
else
{
lean_dec(v_a_668_);
v___y_409_ = v___x_669_;
goto v___jp_408_;
}
}
else
{
v___y_409_ = v___x_667_;
goto v___jp_408_;
}
}
else
{
lean_dec(v_a_664_);
v___y_409_ = v___x_665_;
goto v___jp_408_;
}
}
else
{
v___y_409_ = v___x_663_;
goto v___jp_408_;
}
}
}
}
}
case 10:
{
lean_object* v_expr_674_; uint8_t v___y_676_; uint8_t v___x_721_; 
v_expr_674_ = lean_ctor_get(v_e_400_, 1);
lean_inc_ref(v_expr_674_);
lean_dec_ref_known(v_e_400_, 2);
v___x_721_ = l_Lean_Expr_hasFVar(v_expr_674_);
if (v___x_721_ == 0)
{
uint8_t v___x_722_; 
v___x_722_ = l_Lean_Expr_hasMVar(v_expr_674_);
v___y_676_ = v___x_722_;
goto v___jp_675_;
}
else
{
v___y_676_ = v___x_721_;
goto v___jp_675_;
}
v___jp_675_:
{
if (v___y_676_ == 0)
{
lean_object* v___x_677_; lean_object* v___x_678_; 
lean_dec_ref(v_expr_674_);
v___x_677_ = lean_box(0);
v___x_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
return v___x_678_;
}
else
{
lean_object* v___x_679_; lean_object* v_maxFVar_680_; lean_object* v___x_681_; 
v___x_679_ = lean_st_ref_get(v_a_402_);
v_maxFVar_680_ = lean_ctor_get(v___x_679_, 1);
lean_inc_ref(v_maxFVar_680_);
lean_dec(v___x_679_);
v___x_681_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_680_, v_expr_674_);
lean_dec_ref(v_maxFVar_680_);
if (lean_obj_tag(v___x_681_) == 1)
{
lean_object* v_val_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
lean_dec_ref(v_expr_674_);
v_val_682_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_681_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_val_682_);
lean_dec(v___x_681_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
lean_ctor_set_tag(v___x_684_, 0);
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_val_682_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
else
{
lean_object* v___x_690_; 
lean_dec(v___x_681_);
lean_inc_ref(v_expr_674_);
v___x_690_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_expr_674_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_720_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_720_ == 0)
{
v___x_693_ = v___x_690_;
v_isShared_694_ = v_isSharedCheck_720_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_690_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_720_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_695_; lean_object* v_share_696_; lean_object* v_maxFVar_697_; lean_object* v_proofInstInfo_698_; lean_object* v_inferType_699_; lean_object* v_getLevel_700_; lean_object* v_congrInfo_701_; lean_object* v_defEqI_702_; lean_object* v_extensions_703_; lean_object* v_issues_704_; lean_object* v_canon_705_; lean_object* v_instanceOverrides_706_; uint8_t v_debug_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_719_; 
v___x_695_ = lean_st_ref_take(v_a_402_);
v_share_696_ = lean_ctor_get(v___x_695_, 0);
v_maxFVar_697_ = lean_ctor_get(v___x_695_, 1);
v_proofInstInfo_698_ = lean_ctor_get(v___x_695_, 2);
v_inferType_699_ = lean_ctor_get(v___x_695_, 3);
v_getLevel_700_ = lean_ctor_get(v___x_695_, 4);
v_congrInfo_701_ = lean_ctor_get(v___x_695_, 5);
v_defEqI_702_ = lean_ctor_get(v___x_695_, 6);
v_extensions_703_ = lean_ctor_get(v___x_695_, 7);
v_issues_704_ = lean_ctor_get(v___x_695_, 8);
v_canon_705_ = lean_ctor_get(v___x_695_, 9);
v_instanceOverrides_706_ = lean_ctor_get(v___x_695_, 10);
v_debug_707_ = lean_ctor_get_uint8(v___x_695_, sizeof(void*)*11);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_719_ == 0)
{
v___x_709_ = v___x_695_;
v_isShared_710_ = v_isSharedCheck_719_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_instanceOverrides_706_);
lean_inc(v_canon_705_);
lean_inc(v_issues_704_);
lean_inc(v_extensions_703_);
lean_inc(v_defEqI_702_);
lean_inc(v_congrInfo_701_);
lean_inc(v_getLevel_700_);
lean_inc(v_inferType_699_);
lean_inc(v_proofInstInfo_698_);
lean_inc(v_maxFVar_697_);
lean_inc(v_share_696_);
lean_dec(v___x_695_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_719_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_711_; lean_object* v___x_713_; 
lean_inc(v_a_691_);
v___x_711_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_697_, v_expr_674_, v_a_691_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 1, v___x_711_);
v___x_713_ = v___x_709_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_share_696_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v___x_711_);
lean_ctor_set(v_reuseFailAlloc_718_, 2, v_proofInstInfo_698_);
lean_ctor_set(v_reuseFailAlloc_718_, 3, v_inferType_699_);
lean_ctor_set(v_reuseFailAlloc_718_, 4, v_getLevel_700_);
lean_ctor_set(v_reuseFailAlloc_718_, 5, v_congrInfo_701_);
lean_ctor_set(v_reuseFailAlloc_718_, 6, v_defEqI_702_);
lean_ctor_set(v_reuseFailAlloc_718_, 7, v_extensions_703_);
lean_ctor_set(v_reuseFailAlloc_718_, 8, v_issues_704_);
lean_ctor_set(v_reuseFailAlloc_718_, 9, v_canon_705_);
lean_ctor_set(v_reuseFailAlloc_718_, 10, v_instanceOverrides_706_);
lean_ctor_set_uint8(v_reuseFailAlloc_718_, sizeof(void*)*11, v_debug_707_);
v___x_713_ = v_reuseFailAlloc_718_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_714_ = lean_st_ref_set(v_a_402_, v___x_713_);
if (v_isShared_694_ == 0)
{
v___x_716_ = v___x_693_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_a_691_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
}
else
{
lean_dec_ref(v_expr_674_);
return v___x_690_;
}
}
}
}
}
case 11:
{
lean_object* v_struct_723_; uint8_t v___y_725_; uint8_t v___x_770_; 
v_struct_723_ = lean_ctor_get(v_e_400_, 2);
v___x_770_ = l_Lean_Expr_hasFVar(v_e_400_);
if (v___x_770_ == 0)
{
uint8_t v___x_771_; 
v___x_771_ = l_Lean_Expr_hasMVar(v_e_400_);
v___y_725_ = v___x_771_;
goto v___jp_724_;
}
else
{
v___y_725_ = v___x_770_;
goto v___jp_724_;
}
v___jp_724_:
{
if (v___y_725_ == 0)
{
lean_object* v___x_726_; lean_object* v___x_727_; 
lean_dec_ref_known(v_e_400_, 3);
v___x_726_ = lean_box(0);
v___x_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
return v___x_727_;
}
else
{
lean_object* v___x_728_; lean_object* v_maxFVar_729_; lean_object* v___x_730_; 
v___x_728_ = lean_st_ref_get(v_a_402_);
v_maxFVar_729_ = lean_ctor_get(v___x_728_, 1);
lean_inc_ref(v_maxFVar_729_);
lean_dec(v___x_728_);
v___x_730_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_729_, v_e_400_);
lean_dec_ref(v_maxFVar_729_);
if (lean_obj_tag(v___x_730_) == 1)
{
lean_object* v_val_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_dec_ref_known(v_e_400_, 3);
v_val_731_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_730_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_val_731_);
lean_dec(v___x_730_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
lean_ctor_set_tag(v___x_733_, 0);
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_val_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
else
{
lean_object* v___x_739_; 
lean_dec(v___x_730_);
lean_inc_ref(v_struct_723_);
v___x_739_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_struct_723_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_769_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_769_ == 0)
{
v___x_742_ = v___x_739_;
v_isShared_743_ = v_isSharedCheck_769_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_739_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_769_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_744_; lean_object* v_share_745_; lean_object* v_maxFVar_746_; lean_object* v_proofInstInfo_747_; lean_object* v_inferType_748_; lean_object* v_getLevel_749_; lean_object* v_congrInfo_750_; lean_object* v_defEqI_751_; lean_object* v_extensions_752_; lean_object* v_issues_753_; lean_object* v_canon_754_; lean_object* v_instanceOverrides_755_; uint8_t v_debug_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_768_; 
v___x_744_ = lean_st_ref_take(v_a_402_);
v_share_745_ = lean_ctor_get(v___x_744_, 0);
v_maxFVar_746_ = lean_ctor_get(v___x_744_, 1);
v_proofInstInfo_747_ = lean_ctor_get(v___x_744_, 2);
v_inferType_748_ = lean_ctor_get(v___x_744_, 3);
v_getLevel_749_ = lean_ctor_get(v___x_744_, 4);
v_congrInfo_750_ = lean_ctor_get(v___x_744_, 5);
v_defEqI_751_ = lean_ctor_get(v___x_744_, 6);
v_extensions_752_ = lean_ctor_get(v___x_744_, 7);
v_issues_753_ = lean_ctor_get(v___x_744_, 8);
v_canon_754_ = lean_ctor_get(v___x_744_, 9);
v_instanceOverrides_755_ = lean_ctor_get(v___x_744_, 10);
v_debug_756_ = lean_ctor_get_uint8(v___x_744_, sizeof(void*)*11);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_768_ == 0)
{
v___x_758_ = v___x_744_;
v_isShared_759_ = v_isSharedCheck_768_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_instanceOverrides_755_);
lean_inc(v_canon_754_);
lean_inc(v_issues_753_);
lean_inc(v_extensions_752_);
lean_inc(v_defEqI_751_);
lean_inc(v_congrInfo_750_);
lean_inc(v_getLevel_749_);
lean_inc(v_inferType_748_);
lean_inc(v_proofInstInfo_747_);
lean_inc(v_maxFVar_746_);
lean_inc(v_share_745_);
lean_dec(v___x_744_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_768_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_760_; lean_object* v___x_762_; 
lean_inc(v_a_740_);
v___x_760_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_746_, v_e_400_, v_a_740_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 1, v___x_760_);
v___x_762_ = v___x_758_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_share_745_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v___x_760_);
lean_ctor_set(v_reuseFailAlloc_767_, 2, v_proofInstInfo_747_);
lean_ctor_set(v_reuseFailAlloc_767_, 3, v_inferType_748_);
lean_ctor_set(v_reuseFailAlloc_767_, 4, v_getLevel_749_);
lean_ctor_set(v_reuseFailAlloc_767_, 5, v_congrInfo_750_);
lean_ctor_set(v_reuseFailAlloc_767_, 6, v_defEqI_751_);
lean_ctor_set(v_reuseFailAlloc_767_, 7, v_extensions_752_);
lean_ctor_set(v_reuseFailAlloc_767_, 8, v_issues_753_);
lean_ctor_set(v_reuseFailAlloc_767_, 9, v_canon_754_);
lean_ctor_set(v_reuseFailAlloc_767_, 10, v_instanceOverrides_755_);
lean_ctor_set_uint8(v_reuseFailAlloc_767_, sizeof(void*)*11, v_debug_756_);
v___x_762_ = v_reuseFailAlloc_767_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
lean_object* v___x_763_; lean_object* v___x_765_; 
v___x_763_ = lean_st_ref_set(v_a_402_, v___x_762_);
if (v_isShared_743_ == 0)
{
v___x_765_ = v___x_742_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_740_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_400_, 3);
return v___x_739_;
}
}
}
}
}
default: 
{
lean_object* v___x_772_; lean_object* v___x_773_; 
lean_dec_ref(v_e_400_);
v___x_772_ = lean_box(0);
v___x_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
return v___x_773_;
}
}
v___jp_408_:
{
if (lean_obj_tag(v___y_409_) == 0)
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_439_; 
v_a_410_ = lean_ctor_get(v___y_409_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___y_409_);
if (v_isSharedCheck_439_ == 0)
{
v___x_412_ = v___y_409_;
v_isShared_413_ = v_isSharedCheck_439_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___y_409_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_439_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; lean_object* v_share_415_; lean_object* v_maxFVar_416_; lean_object* v_proofInstInfo_417_; lean_object* v_inferType_418_; lean_object* v_getLevel_419_; lean_object* v_congrInfo_420_; lean_object* v_defEqI_421_; lean_object* v_extensions_422_; lean_object* v_issues_423_; lean_object* v_canon_424_; lean_object* v_instanceOverrides_425_; uint8_t v_debug_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_438_; 
v___x_414_ = lean_st_ref_take(v_a_402_);
v_share_415_ = lean_ctor_get(v___x_414_, 0);
v_maxFVar_416_ = lean_ctor_get(v___x_414_, 1);
v_proofInstInfo_417_ = lean_ctor_get(v___x_414_, 2);
v_inferType_418_ = lean_ctor_get(v___x_414_, 3);
v_getLevel_419_ = lean_ctor_get(v___x_414_, 4);
v_congrInfo_420_ = lean_ctor_get(v___x_414_, 5);
v_defEqI_421_ = lean_ctor_get(v___x_414_, 6);
v_extensions_422_ = lean_ctor_get(v___x_414_, 7);
v_issues_423_ = lean_ctor_get(v___x_414_, 8);
v_canon_424_ = lean_ctor_get(v___x_414_, 9);
v_instanceOverrides_425_ = lean_ctor_get(v___x_414_, 10);
v_debug_426_ = lean_ctor_get_uint8(v___x_414_, sizeof(void*)*11);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_438_ == 0)
{
v___x_428_ = v___x_414_;
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
lean_inc(v_proofInstInfo_417_);
lean_inc(v_maxFVar_416_);
lean_inc(v_share_415_);
lean_dec(v___x_414_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_438_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_430_; lean_object* v___x_432_; 
lean_inc(v_a_410_);
v___x_430_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_416_, v_e_400_, v_a_410_);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 1, v___x_430_);
v___x_432_ = v___x_428_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_share_415_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_437_, 2, v_proofInstInfo_417_);
lean_ctor_set(v_reuseFailAlloc_437_, 3, v_inferType_418_);
lean_ctor_set(v_reuseFailAlloc_437_, 4, v_getLevel_419_);
lean_ctor_set(v_reuseFailAlloc_437_, 5, v_congrInfo_420_);
lean_ctor_set(v_reuseFailAlloc_437_, 6, v_defEqI_421_);
lean_ctor_set(v_reuseFailAlloc_437_, 7, v_extensions_422_);
lean_ctor_set(v_reuseFailAlloc_437_, 8, v_issues_423_);
lean_ctor_set(v_reuseFailAlloc_437_, 9, v_canon_424_);
lean_ctor_set(v_reuseFailAlloc_437_, 10, v_instanceOverrides_425_);
lean_ctor_set_uint8(v_reuseFailAlloc_437_, sizeof(void*)*11, v_debug_426_);
v___x_432_ = v_reuseFailAlloc_437_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_object* v___x_433_; lean_object* v___x_435_; 
v___x_433_ = lean_st_ref_set(v_a_402_, v___x_432_);
if (v_isShared_413_ == 0)
{
v___x_435_ = v___x_412_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_410_);
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
lean_dec_ref(v_e_400_);
return v___y_409_;
}
}
v___jp_440_:
{
lean_object* v___x_442_; lean_object* v_share_443_; lean_object* v_maxFVar_444_; lean_object* v_proofInstInfo_445_; lean_object* v_inferType_446_; lean_object* v_getLevel_447_; lean_object* v_congrInfo_448_; lean_object* v_defEqI_449_; lean_object* v_extensions_450_; lean_object* v_issues_451_; lean_object* v_canon_452_; lean_object* v_instanceOverrides_453_; uint8_t v_debug_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_464_; 
v___x_442_ = lean_st_ref_take(v_a_402_);
v_share_443_ = lean_ctor_get(v___x_442_, 0);
v_maxFVar_444_ = lean_ctor_get(v___x_442_, 1);
v_proofInstInfo_445_ = lean_ctor_get(v___x_442_, 2);
v_inferType_446_ = lean_ctor_get(v___x_442_, 3);
v_getLevel_447_ = lean_ctor_get(v___x_442_, 4);
v_congrInfo_448_ = lean_ctor_get(v___x_442_, 5);
v_defEqI_449_ = lean_ctor_get(v___x_442_, 6);
v_extensions_450_ = lean_ctor_get(v___x_442_, 7);
v_issues_451_ = lean_ctor_get(v___x_442_, 8);
v_canon_452_ = lean_ctor_get(v___x_442_, 9);
v_instanceOverrides_453_ = lean_ctor_get(v___x_442_, 10);
v_debug_454_ = lean_ctor_get_uint8(v___x_442_, sizeof(void*)*11);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_464_ == 0)
{
v___x_456_ = v___x_442_;
v_isShared_457_ = v_isSharedCheck_464_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_instanceOverrides_453_);
lean_inc(v_canon_452_);
lean_inc(v_issues_451_);
lean_inc(v_extensions_450_);
lean_inc(v_defEqI_449_);
lean_inc(v_congrInfo_448_);
lean_inc(v_getLevel_447_);
lean_inc(v_inferType_446_);
lean_inc(v_proofInstInfo_445_);
lean_inc(v_maxFVar_444_);
lean_inc(v_share_443_);
lean_dec(v___x_442_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_464_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_458_; lean_object* v___x_460_; 
lean_inc(v_a_441_);
v___x_458_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_444_, v_e_400_, v_a_441_);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 1, v___x_458_);
v___x_460_ = v___x_456_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_share_443_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v___x_458_);
lean_ctor_set(v_reuseFailAlloc_463_, 2, v_proofInstInfo_445_);
lean_ctor_set(v_reuseFailAlloc_463_, 3, v_inferType_446_);
lean_ctor_set(v_reuseFailAlloc_463_, 4, v_getLevel_447_);
lean_ctor_set(v_reuseFailAlloc_463_, 5, v_congrInfo_448_);
lean_ctor_set(v_reuseFailAlloc_463_, 6, v_defEqI_449_);
lean_ctor_set(v_reuseFailAlloc_463_, 7, v_extensions_450_);
lean_ctor_set(v_reuseFailAlloc_463_, 8, v_issues_451_);
lean_ctor_set(v_reuseFailAlloc_463_, 9, v_canon_452_);
lean_ctor_set(v_reuseFailAlloc_463_, 10, v_instanceOverrides_453_);
lean_ctor_set_uint8(v_reuseFailAlloc_463_, sizeof(void*)*11, v_debug_454_);
v___x_460_ = v_reuseFailAlloc_463_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = lean_st_ref_set(v_a_402_, v___x_460_);
v___x_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_462_, 0, v_a_441_);
return v___x_462_;
}
}
}
v___jp_465_:
{
if (lean_obj_tag(v___y_467_) == 0)
{
lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_497_; 
v_a_468_ = lean_ctor_get(v___y_467_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___y_467_);
if (v_isSharedCheck_497_ == 0)
{
v___x_470_ = v___y_467_;
v_isShared_471_ = v_isSharedCheck_497_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v___y_467_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_497_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_472_; lean_object* v_share_473_; lean_object* v_maxFVar_474_; lean_object* v_proofInstInfo_475_; lean_object* v_inferType_476_; lean_object* v_getLevel_477_; lean_object* v_congrInfo_478_; lean_object* v_defEqI_479_; lean_object* v_extensions_480_; lean_object* v_issues_481_; lean_object* v_canon_482_; lean_object* v_instanceOverrides_483_; uint8_t v_debug_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_496_; 
v___x_472_ = lean_st_ref_take(v___y_466_);
v_share_473_ = lean_ctor_get(v___x_472_, 0);
v_maxFVar_474_ = lean_ctor_get(v___x_472_, 1);
v_proofInstInfo_475_ = lean_ctor_get(v___x_472_, 2);
v_inferType_476_ = lean_ctor_get(v___x_472_, 3);
v_getLevel_477_ = lean_ctor_get(v___x_472_, 4);
v_congrInfo_478_ = lean_ctor_get(v___x_472_, 5);
v_defEqI_479_ = lean_ctor_get(v___x_472_, 6);
v_extensions_480_ = lean_ctor_get(v___x_472_, 7);
v_issues_481_ = lean_ctor_get(v___x_472_, 8);
v_canon_482_ = lean_ctor_get(v___x_472_, 9);
v_instanceOverrides_483_ = lean_ctor_get(v___x_472_, 10);
v_debug_484_ = lean_ctor_get_uint8(v___x_472_, sizeof(void*)*11);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_496_ == 0)
{
v___x_486_ = v___x_472_;
v_isShared_487_ = v_isSharedCheck_496_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_instanceOverrides_483_);
lean_inc(v_canon_482_);
lean_inc(v_issues_481_);
lean_inc(v_extensions_480_);
lean_inc(v_defEqI_479_);
lean_inc(v_congrInfo_478_);
lean_inc(v_getLevel_477_);
lean_inc(v_inferType_476_);
lean_inc(v_proofInstInfo_475_);
lean_inc(v_maxFVar_474_);
lean_inc(v_share_473_);
lean_dec(v___x_472_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_496_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_488_; lean_object* v___x_490_; 
lean_inc(v_a_468_);
v___x_488_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_474_, v_e_400_, v_a_468_);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 1, v___x_488_);
v___x_490_ = v___x_486_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_share_473_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v___x_488_);
lean_ctor_set(v_reuseFailAlloc_495_, 2, v_proofInstInfo_475_);
lean_ctor_set(v_reuseFailAlloc_495_, 3, v_inferType_476_);
lean_ctor_set(v_reuseFailAlloc_495_, 4, v_getLevel_477_);
lean_ctor_set(v_reuseFailAlloc_495_, 5, v_congrInfo_478_);
lean_ctor_set(v_reuseFailAlloc_495_, 6, v_defEqI_479_);
lean_ctor_set(v_reuseFailAlloc_495_, 7, v_extensions_480_);
lean_ctor_set(v_reuseFailAlloc_495_, 8, v_issues_481_);
lean_ctor_set(v_reuseFailAlloc_495_, 9, v_canon_482_);
lean_ctor_set(v_reuseFailAlloc_495_, 10, v_instanceOverrides_483_);
lean_ctor_set_uint8(v_reuseFailAlloc_495_, sizeof(void*)*11, v_debug_484_);
v___x_490_ = v_reuseFailAlloc_495_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_491_; lean_object* v___x_493_; 
v___x_491_ = lean_st_ref_set(v___y_466_, v___x_490_);
if (v_isShared_471_ == 0)
{
v___x_493_ = v___x_470_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_468_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_400_);
return v___y_467_;
}
}
v___jp_498_:
{
if (v___y_507_ == 0)
{
lean_object* v___x_508_; lean_object* v___x_509_; 
lean_dec_ref(v___y_506_);
lean_dec_ref(v___y_500_);
lean_dec_ref(v_e_400_);
v___x_508_ = lean_box(0);
v___x_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
return v___x_509_;
}
else
{
lean_object* v___x_510_; lean_object* v_maxFVar_511_; lean_object* v___x_512_; 
v___x_510_ = lean_st_ref_get(v___y_502_);
v_maxFVar_511_ = lean_ctor_get(v___x_510_, 1);
lean_inc_ref(v_maxFVar_511_);
lean_dec(v___x_510_);
v___x_512_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_511_, v_e_400_);
lean_dec_ref(v_maxFVar_511_);
if (lean_obj_tag(v___x_512_) == 1)
{
lean_object* v_val_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
lean_dec_ref(v___y_506_);
lean_dec_ref(v___y_500_);
lean_dec_ref(v_e_400_);
v_val_513_ = lean_ctor_get(v___x_512_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_520_ == 0)
{
v___x_515_ = v___x_512_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_val_513_);
lean_dec(v___x_512_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_516_ == 0)
{
lean_ctor_set_tag(v___x_515_, 0);
v___x_518_ = v___x_515_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_val_513_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
else
{
lean_object* v___x_521_; 
lean_dec(v___x_512_);
v___x_521_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v___y_506_, v___y_505_, v___y_502_, v___y_504_, v___y_503_, v___y_499_, v___y_501_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; lean_object* v___x_523_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_a_522_);
lean_dec_ref_known(v___x_521_, 1);
v___x_523_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v___y_500_, v___y_505_, v___y_502_, v___y_504_, v___y_503_, v___y_499_, v___y_501_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_524_; lean_object* v___x_525_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_a_524_);
lean_dec_ref_known(v___x_523_, 1);
v___x_525_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_522_, v_a_524_, v___y_504_, v___y_499_, v___y_501_);
v___y_466_ = v___y_502_;
v___y_467_ = v___x_525_;
goto v___jp_465_;
}
else
{
lean_dec(v_a_522_);
v___y_466_ = v___y_502_;
v___y_467_ = v___x_523_;
goto v___jp_465_;
}
}
else
{
lean_dec_ref(v___y_500_);
v___y_466_ = v___y_502_;
v___y_467_ = v___x_521_;
goto v___jp_465_;
}
}
}
}
v___jp_526_:
{
uint8_t v___x_535_; 
v___x_535_ = l_Lean_Expr_hasFVar(v_e_400_);
if (v___x_535_ == 0)
{
uint8_t v___x_536_; 
v___x_536_ = l_Lean_Expr_hasMVar(v_e_400_);
v___y_499_ = v___y_533_;
v___y_500_ = v_b_528_;
v___y_501_ = v___y_534_;
v___y_502_ = v___y_530_;
v___y_503_ = v___y_532_;
v___y_504_ = v___y_531_;
v___y_505_ = v___y_529_;
v___y_506_ = v_d_527_;
v___y_507_ = v___x_536_;
goto v___jp_498_;
}
else
{
v___y_499_ = v___y_533_;
v___y_500_ = v_b_528_;
v___y_501_ = v___y_534_;
v___y_502_ = v___y_530_;
v___y_503_ = v___y_532_;
v___y_504_ = v___y_531_;
v___y_505_ = v___y_529_;
v___y_506_ = v_d_527_;
v___y_507_ = v___x_535_;
goto v___jp_498_;
}
}
v___jp_537_:
{
if (lean_obj_tag(v___y_538_) == 0)
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_568_; 
v_a_539_ = lean_ctor_get(v___y_538_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___y_538_);
if (v_isSharedCheck_568_ == 0)
{
v___x_541_ = v___y_538_;
v_isShared_542_ = v_isSharedCheck_568_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___y_538_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_568_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_543_; lean_object* v_share_544_; lean_object* v_maxFVar_545_; lean_object* v_proofInstInfo_546_; lean_object* v_inferType_547_; lean_object* v_getLevel_548_; lean_object* v_congrInfo_549_; lean_object* v_defEqI_550_; lean_object* v_extensions_551_; lean_object* v_issues_552_; lean_object* v_canon_553_; lean_object* v_instanceOverrides_554_; uint8_t v_debug_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_567_; 
v___x_543_ = lean_st_ref_take(v_a_402_);
v_share_544_ = lean_ctor_get(v___x_543_, 0);
v_maxFVar_545_ = lean_ctor_get(v___x_543_, 1);
v_proofInstInfo_546_ = lean_ctor_get(v___x_543_, 2);
v_inferType_547_ = lean_ctor_get(v___x_543_, 3);
v_getLevel_548_ = lean_ctor_get(v___x_543_, 4);
v_congrInfo_549_ = lean_ctor_get(v___x_543_, 5);
v_defEqI_550_ = lean_ctor_get(v___x_543_, 6);
v_extensions_551_ = lean_ctor_get(v___x_543_, 7);
v_issues_552_ = lean_ctor_get(v___x_543_, 8);
v_canon_553_ = lean_ctor_get(v___x_543_, 9);
v_instanceOverrides_554_ = lean_ctor_get(v___x_543_, 10);
v_debug_555_ = lean_ctor_get_uint8(v___x_543_, sizeof(void*)*11);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_567_ == 0)
{
v___x_557_ = v___x_543_;
v_isShared_558_ = v_isSharedCheck_567_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_instanceOverrides_554_);
lean_inc(v_canon_553_);
lean_inc(v_issues_552_);
lean_inc(v_extensions_551_);
lean_inc(v_defEqI_550_);
lean_inc(v_congrInfo_549_);
lean_inc(v_getLevel_548_);
lean_inc(v_inferType_547_);
lean_inc(v_proofInstInfo_546_);
lean_inc(v_maxFVar_545_);
lean_inc(v_share_544_);
lean_dec(v___x_543_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_567_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_559_; lean_object* v___x_561_; 
lean_inc(v_a_539_);
v___x_559_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_545_, v_e_400_, v_a_539_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 1, v___x_559_);
v___x_561_ = v___x_557_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_share_544_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v___x_559_);
lean_ctor_set(v_reuseFailAlloc_566_, 2, v_proofInstInfo_546_);
lean_ctor_set(v_reuseFailAlloc_566_, 3, v_inferType_547_);
lean_ctor_set(v_reuseFailAlloc_566_, 4, v_getLevel_548_);
lean_ctor_set(v_reuseFailAlloc_566_, 5, v_congrInfo_549_);
lean_ctor_set(v_reuseFailAlloc_566_, 6, v_defEqI_550_);
lean_ctor_set(v_reuseFailAlloc_566_, 7, v_extensions_551_);
lean_ctor_set(v_reuseFailAlloc_566_, 8, v_issues_552_);
lean_ctor_set(v_reuseFailAlloc_566_, 9, v_canon_553_);
lean_ctor_set(v_reuseFailAlloc_566_, 10, v_instanceOverrides_554_);
lean_ctor_set_uint8(v_reuseFailAlloc_566_, sizeof(void*)*11, v_debug_555_);
v___x_561_ = v_reuseFailAlloc_566_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
lean_object* v___x_562_; lean_object* v___x_564_; 
v___x_562_ = lean_st_ref_set(v_a_402_, v___x_561_);
if (v_isShared_542_ == 0)
{
v___x_564_ = v___x_541_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_a_539_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_400_);
return v___y_538_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f___boxed(lean_object* v_e_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_e_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
lean_dec(v_a_780_);
lean_dec_ref(v_a_779_);
lean_dec(v_a_778_);
lean_dec_ref(v_a_777_);
lean_dec(v_a_776_);
lean_dec_ref(v_a_775_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0(lean_object* v_00_u03b2_783_, lean_object* v_x_784_, lean_object* v_x_785_, lean_object* v_x_786_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_x_784_, v_x_785_, v_x_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1(lean_object* v_00_u03b2_788_, lean_object* v_x_789_, lean_object* v_x_790_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_x_789_, v_x_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___boxed(lean_object* v_00_u03b2_792_, lean_object* v_x_793_, lean_object* v_x_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1(v_00_u03b2_792_, v_x_793_, v_x_794_);
lean_dec_ref(v_x_794_);
lean_dec_ref(v_x_793_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0(lean_object* v_00_u03b2_796_, lean_object* v_x_797_, size_t v_x_798_, size_t v_x_799_, lean_object* v_x_800_, lean_object* v_x_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_797_, v_x_798_, v_x_799_, v_x_800_, v_x_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_803_, lean_object* v_x_804_, lean_object* v_x_805_, lean_object* v_x_806_, lean_object* v_x_807_, lean_object* v_x_808_){
_start:
{
size_t v_x_6169__boxed_809_; size_t v_x_6170__boxed_810_; lean_object* v_res_811_; 
v_x_6169__boxed_809_ = lean_unbox_usize(v_x_805_);
lean_dec(v_x_805_);
v_x_6170__boxed_810_ = lean_unbox_usize(v_x_806_);
lean_dec(v_x_806_);
v_res_811_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0(v_00_u03b2_803_, v_x_804_, v_x_6169__boxed_809_, v_x_6170__boxed_810_, v_x_807_, v_x_808_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2(lean_object* v_00_u03b2_812_, lean_object* v_x_813_, size_t v_x_814_, lean_object* v_x_815_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_813_, v_x_814_, v_x_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_817_, lean_object* v_x_818_, lean_object* v_x_819_, lean_object* v_x_820_){
_start:
{
size_t v_x_6186__boxed_821_; lean_object* v_res_822_; 
v_x_6186__boxed_821_ = lean_unbox_usize(v_x_819_);
lean_dec(v_x_819_);
v_res_822_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2(v_00_u03b2_817_, v_x_818_, v_x_6186__boxed_821_, v_x_820_);
lean_dec_ref(v_x_820_);
lean_dec_ref(v_x_818_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_823_, lean_object* v_n_824_, lean_object* v_k_825_, lean_object* v_v_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(v_n_824_, v_k_825_, v_v_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_828_, size_t v_depth_829_, lean_object* v_keys_830_, lean_object* v_vals_831_, lean_object* v_heq_832_, lean_object* v_i_833_, lean_object* v_entries_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(v_depth_829_, v_keys_830_, v_vals_831_, v_i_833_, v_entries_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_836_, lean_object* v_depth_837_, lean_object* v_keys_838_, lean_object* v_vals_839_, lean_object* v_heq_840_, lean_object* v_i_841_, lean_object* v_entries_842_){
_start:
{
size_t v_depth_boxed_843_; lean_object* v_res_844_; 
v_depth_boxed_843_ = lean_unbox_usize(v_depth_837_);
lean_dec(v_depth_837_);
v_res_844_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3(v_00_u03b2_836_, v_depth_boxed_843_, v_keys_838_, v_vals_839_, v_heq_840_, v_i_841_, v_entries_842_);
lean_dec_ref(v_vals_839_);
lean_dec_ref(v_keys_838_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_845_, lean_object* v_keys_846_, lean_object* v_vals_847_, lean_object* v_heq_848_, lean_object* v_i_849_, lean_object* v_k_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_keys_846_, v_vals_847_, v_i_849_, v_k_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_852_, lean_object* v_keys_853_, lean_object* v_vals_854_, lean_object* v_heq_855_, lean_object* v_i_856_, lean_object* v_k_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6(v_00_u03b2_852_, v_keys_853_, v_vals_854_, v_heq_855_, v_i_856_, v_k_857_);
lean_dec_ref(v_k_857_);
lean_dec_ref(v_vals_854_);
lean_dec_ref(v_keys_853_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_859_, lean_object* v_x_860_, lean_object* v_x_861_, lean_object* v_x_862_, lean_object* v_x_863_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_x_860_, v_x_861_, v_x_862_, v_x_863_);
return v___x_864_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_MaxFVar(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
