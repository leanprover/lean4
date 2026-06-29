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
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed(lean_object*);
lean_object* l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
uint8_t v___y_88_; uint8_t v___x_134_; 
v___x_134_ = l_Lean_Expr_hasFVar(v_e_78_);
if (v___x_134_ == 0)
{
uint8_t v___x_135_; 
v___x_135_ = l_Lean_Expr_hasMVar(v_e_78_);
v___y_88_ = v___x_135_;
goto v___jp_87_;
}
else
{
v___y_88_ = v___x_134_;
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
lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_133_; 
v_a_105_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_133_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_133_ == 0)
{
v___x_107_ = v___x_104_;
v_isShared_108_ = v_isSharedCheck_133_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_dec(v___x_104_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_133_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_109_; lean_object* v_share_110_; lean_object* v_maxFVar_111_; lean_object* v_proofInstInfo_112_; lean_object* v_inferType_113_; lean_object* v_getLevel_114_; lean_object* v_congrInfo_115_; lean_object* v_defEqI_116_; lean_object* v_extensions_117_; lean_object* v_issues_118_; lean_object* v_canon_119_; uint8_t v_debug_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_132_; 
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
v_debug_120_ = lean_ctor_get_uint8(v___x_109_, sizeof(void*)*10);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_132_ == 0)
{
v___x_122_ = v___x_109_;
v_isShared_123_ = v_isSharedCheck_132_;
goto v_resetjp_121_;
}
else
{
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
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_132_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_124_; lean_object* v___x_126_; 
lean_inc(v_a_105_);
v___x_124_ = l_Lean_PersistentHashMap_insert___redArg(v___f_93_, v___f_94_, v_maxFVar_111_, v_e_78_, v_a_105_);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 1, v___x_124_);
v___x_126_ = v___x_122_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_share_110_);
lean_ctor_set(v_reuseFailAlloc_131_, 1, v___x_124_);
lean_ctor_set(v_reuseFailAlloc_131_, 2, v_proofInstInfo_112_);
lean_ctor_set(v_reuseFailAlloc_131_, 3, v_inferType_113_);
lean_ctor_set(v_reuseFailAlloc_131_, 4, v_getLevel_114_);
lean_ctor_set(v_reuseFailAlloc_131_, 5, v_congrInfo_115_);
lean_ctor_set(v_reuseFailAlloc_131_, 6, v_defEqI_116_);
lean_ctor_set(v_reuseFailAlloc_131_, 7, v_extensions_117_);
lean_ctor_set(v_reuseFailAlloc_131_, 8, v_issues_118_);
lean_ctor_set(v_reuseFailAlloc_131_, 9, v_canon_119_);
lean_ctor_set_uint8(v_reuseFailAlloc_131_, sizeof(void*)*10, v_debug_120_);
v___x_126_ = v_reuseFailAlloc_131_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
lean_object* v___x_127_; lean_object* v___x_129_; 
v___x_127_ = lean_st_ref_set(v_a_81_, v___x_126_);
if (v_isShared_108_ == 0)
{
v___x_129_ = v___x_107_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_a_105_);
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
return v___x_104_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___boxed(lean_object* v_e_136_, lean_object* v_k_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check(v_e_136_, v_k_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_);
lean_dec(v_a_143_);
lean_dec_ref(v_a_142_);
lean_dec(v_a_141_);
lean_dec_ref(v_a_140_);
lean_dec(v_a_139_);
lean_dec_ref(v_a_138_);
return v_res_145_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0(void){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2(lean_object* v_msg_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
lean_object* v___x_155_; lean_object* v___x_4718__overap_156_; lean_object* v___x_157_; 
v___x_155_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0, &l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0);
v___x_4718__overap_156_ = lean_panic_fn_borrowed(v___x_155_, v_msg_147_);
lean_inc(v___y_153_);
lean_inc_ref(v___y_152_);
lean_inc(v___y_151_);
lean_inc_ref(v___y_150_);
lean_inc(v___y_149_);
lean_inc_ref(v___y_148_);
v___x_157_ = lean_apply_7(v___x_4718__overap_156_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, lean_box(0));
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___boxed(lean_object* v_msg_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2(v_msg_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_167_, lean_object* v_x_168_, lean_object* v_x_169_, lean_object* v_x_170_){
_start:
{
lean_object* v_ks_171_; lean_object* v_vs_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_196_; 
v_ks_171_ = lean_ctor_get(v_x_167_, 0);
v_vs_172_ = lean_ctor_get(v_x_167_, 1);
v_isSharedCheck_196_ = !lean_is_exclusive(v_x_167_);
if (v_isSharedCheck_196_ == 0)
{
v___x_174_ = v_x_167_;
v_isShared_175_ = v_isSharedCheck_196_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_vs_172_);
lean_inc(v_ks_171_);
lean_dec(v_x_167_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_196_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_176_ = lean_array_get_size(v_ks_171_);
v___x_177_ = lean_nat_dec_lt(v_x_168_, v___x_176_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_181_; 
lean_dec(v_x_168_);
v___x_178_ = lean_array_push(v_ks_171_, v_x_169_);
v___x_179_ = lean_array_push(v_vs_172_, v_x_170_);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 1, v___x_179_);
lean_ctor_set(v___x_174_, 0, v___x_178_);
v___x_181_ = v___x_174_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v___x_178_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v___x_179_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
else
{
lean_object* v_k_x27_183_; uint8_t v___x_184_; 
v_k_x27_183_ = lean_array_fget_borrowed(v_ks_171_, v_x_168_);
v___x_184_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_169_, v_k_x27_183_);
if (v___x_184_ == 0)
{
lean_object* v___x_186_; 
if (v_isShared_175_ == 0)
{
v___x_186_ = v___x_174_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_ks_171_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v_vs_172_);
v___x_186_ = v_reuseFailAlloc_190_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = lean_unsigned_to_nat(1u);
v___x_188_ = lean_nat_add(v_x_168_, v___x_187_);
lean_dec(v_x_168_);
v_x_167_ = v___x_186_;
v_x_168_ = v___x_188_;
goto _start;
}
}
else
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_194_; 
v___x_191_ = lean_array_fset(v_ks_171_, v_x_168_, v_x_169_);
v___x_192_ = lean_array_fset(v_vs_172_, v_x_168_, v_x_170_);
lean_dec(v_x_168_);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 1, v___x_192_);
lean_ctor_set(v___x_174_, 0, v___x_191_);
v___x_194_ = v___x_174_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_191_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v___x_192_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(lean_object* v_n_197_, lean_object* v_k_198_, lean_object* v_v_199_){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = lean_unsigned_to_nat(0u);
v___x_201_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_n_197_, v___x_200_, v_k_198_, v_v_199_);
return v___x_201_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(lean_object* v_x_203_, size_t v_x_204_, size_t v_x_205_, lean_object* v_x_206_, lean_object* v_x_207_){
_start:
{
if (lean_obj_tag(v_x_203_) == 0)
{
lean_object* v_es_208_; size_t v___x_209_; size_t v___x_210_; lean_object* v_j_211_; lean_object* v___x_212_; uint8_t v___x_213_; 
v_es_208_ = lean_ctor_get(v_x_203_, 0);
v___x_209_ = ((size_t)31ULL);
v___x_210_ = lean_usize_land(v_x_204_, v___x_209_);
v_j_211_ = lean_usize_to_nat(v___x_210_);
v___x_212_ = lean_array_get_size(v_es_208_);
v___x_213_ = lean_nat_dec_lt(v_j_211_, v___x_212_);
if (v___x_213_ == 0)
{
lean_dec(v_j_211_);
lean_dec(v_x_207_);
lean_dec_ref(v_x_206_);
return v_x_203_;
}
else
{
lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_252_; 
lean_inc_ref(v_es_208_);
v_isSharedCheck_252_ = !lean_is_exclusive(v_x_203_);
if (v_isSharedCheck_252_ == 0)
{
lean_object* v_unused_253_; 
v_unused_253_ = lean_ctor_get(v_x_203_, 0);
lean_dec(v_unused_253_);
v___x_215_ = v_x_203_;
v_isShared_216_ = v_isSharedCheck_252_;
goto v_resetjp_214_;
}
else
{
lean_dec(v_x_203_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_252_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v_v_217_; lean_object* v___x_218_; lean_object* v_xs_x27_219_; lean_object* v___y_221_; 
v_v_217_ = lean_array_fget(v_es_208_, v_j_211_);
v___x_218_ = lean_box(0);
v_xs_x27_219_ = lean_array_fset(v_es_208_, v_j_211_, v___x_218_);
switch(lean_obj_tag(v_v_217_))
{
case 0:
{
lean_object* v_key_226_; lean_object* v_val_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_237_; 
v_key_226_ = lean_ctor_get(v_v_217_, 0);
v_val_227_ = lean_ctor_get(v_v_217_, 1);
v_isSharedCheck_237_ = !lean_is_exclusive(v_v_217_);
if (v_isSharedCheck_237_ == 0)
{
v___x_229_ = v_v_217_;
v_isShared_230_ = v_isSharedCheck_237_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_val_227_);
lean_inc(v_key_226_);
lean_dec(v_v_217_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_237_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
uint8_t v___x_231_; 
v___x_231_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_206_, v_key_226_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; lean_object* v___x_233_; 
lean_del_object(v___x_229_);
v___x_232_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_226_, v_val_227_, v_x_206_, v_x_207_);
v___x_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
v___y_221_ = v___x_233_;
goto v___jp_220_;
}
else
{
lean_object* v___x_235_; 
lean_dec(v_val_227_);
lean_dec(v_key_226_);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 1, v_x_207_);
lean_ctor_set(v___x_229_, 0, v_x_206_);
v___x_235_ = v___x_229_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_x_206_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v_x_207_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
v___y_221_ = v___x_235_;
goto v___jp_220_;
}
}
}
}
case 1:
{
lean_object* v_node_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_250_; 
v_node_238_ = lean_ctor_get(v_v_217_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v_v_217_);
if (v_isSharedCheck_250_ == 0)
{
v___x_240_ = v_v_217_;
v_isShared_241_ = v_isSharedCheck_250_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_node_238_);
lean_dec(v_v_217_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_250_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
size_t v___x_242_; size_t v___x_243_; size_t v___x_244_; size_t v___x_245_; lean_object* v___x_246_; lean_object* v___x_248_; 
v___x_242_ = ((size_t)5ULL);
v___x_243_ = lean_usize_shift_right(v_x_204_, v___x_242_);
v___x_244_ = ((size_t)1ULL);
v___x_245_ = lean_usize_add(v_x_205_, v___x_244_);
v___x_246_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_node_238_, v___x_243_, v___x_245_, v_x_206_, v_x_207_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v___x_246_);
v___x_248_ = v___x_240_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_246_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
v___y_221_ = v___x_248_;
goto v___jp_220_;
}
}
}
default: 
{
lean_object* v___x_251_; 
v___x_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_251_, 0, v_x_206_);
lean_ctor_set(v___x_251_, 1, v_x_207_);
v___y_221_ = v___x_251_;
goto v___jp_220_;
}
}
v___jp_220_:
{
lean_object* v___x_222_; lean_object* v___x_224_; 
v___x_222_ = lean_array_fset(v_xs_x27_219_, v_j_211_, v___y_221_);
lean_dec(v_j_211_);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 0, v___x_222_);
v___x_224_ = v___x_215_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_222_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
}
else
{
lean_object* v_ks_254_; lean_object* v_vs_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_275_; 
v_ks_254_ = lean_ctor_get(v_x_203_, 0);
v_vs_255_ = lean_ctor_get(v_x_203_, 1);
v_isSharedCheck_275_ = !lean_is_exclusive(v_x_203_);
if (v_isSharedCheck_275_ == 0)
{
v___x_257_ = v_x_203_;
v_isShared_258_ = v_isSharedCheck_275_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_vs_255_);
lean_inc(v_ks_254_);
lean_dec(v_x_203_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_275_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_ks_254_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v_vs_255_);
v___x_260_ = v_reuseFailAlloc_274_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
lean_object* v_newNode_261_; uint8_t v___y_263_; size_t v___x_269_; uint8_t v___x_270_; 
v_newNode_261_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(v___x_260_, v_x_206_, v_x_207_);
v___x_269_ = ((size_t)7ULL);
v___x_270_ = lean_usize_dec_le(v___x_269_, v_x_205_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; lean_object* v___x_272_; uint8_t v___x_273_; 
v___x_271_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_261_);
v___x_272_ = lean_unsigned_to_nat(4u);
v___x_273_ = lean_nat_dec_lt(v___x_271_, v___x_272_);
lean_dec(v___x_271_);
v___y_263_ = v___x_273_;
goto v___jp_262_;
}
else
{
v___y_263_ = v___x_270_;
goto v___jp_262_;
}
v___jp_262_:
{
if (v___y_263_ == 0)
{
lean_object* v_ks_264_; lean_object* v_vs_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v_ks_264_ = lean_ctor_get(v_newNode_261_, 0);
lean_inc_ref(v_ks_264_);
v_vs_265_ = lean_ctor_get(v_newNode_261_, 1);
lean_inc_ref(v_vs_265_);
lean_dec_ref(v_newNode_261_);
v___x_266_ = lean_unsigned_to_nat(0u);
v___x_267_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0);
v___x_268_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(v_x_205_, v_ks_264_, v_vs_265_, v___x_266_, v___x_267_);
lean_dec_ref(v_vs_265_);
lean_dec_ref(v_ks_264_);
return v___x_268_;
}
else
{
return v_newNode_261_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(size_t v_depth_276_, lean_object* v_keys_277_, lean_object* v_vals_278_, lean_object* v_i_279_, lean_object* v_entries_280_){
_start:
{
lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_281_ = lean_array_get_size(v_keys_277_);
v___x_282_ = lean_nat_dec_lt(v_i_279_, v___x_281_);
if (v___x_282_ == 0)
{
lean_dec(v_i_279_);
return v_entries_280_;
}
else
{
lean_object* v_k_283_; lean_object* v_v_284_; uint64_t v___x_285_; size_t v_h_286_; size_t v___x_287_; lean_object* v___x_288_; size_t v___x_289_; size_t v___x_290_; size_t v___x_291_; size_t v_h_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v_k_283_ = lean_array_fget_borrowed(v_keys_277_, v_i_279_);
v_v_284_ = lean_array_fget_borrowed(v_vals_278_, v_i_279_);
v___x_285_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_283_);
v_h_286_ = lean_uint64_to_usize(v___x_285_);
v___x_287_ = ((size_t)5ULL);
v___x_288_ = lean_unsigned_to_nat(1u);
v___x_289_ = ((size_t)1ULL);
v___x_290_ = lean_usize_sub(v_depth_276_, v___x_289_);
v___x_291_ = lean_usize_mul(v___x_287_, v___x_290_);
v_h_292_ = lean_usize_shift_right(v_h_286_, v___x_291_);
v___x_293_ = lean_nat_add(v_i_279_, v___x_288_);
lean_dec(v_i_279_);
lean_inc(v_v_284_);
lean_inc(v_k_283_);
v___x_294_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_entries_280_, v_h_292_, v_depth_276_, v_k_283_, v_v_284_);
v_i_279_ = v___x_293_;
v_entries_280_ = v___x_294_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_296_, lean_object* v_keys_297_, lean_object* v_vals_298_, lean_object* v_i_299_, lean_object* v_entries_300_){
_start:
{
size_t v_depth_boxed_301_; lean_object* v_res_302_; 
v_depth_boxed_301_ = lean_unbox_usize(v_depth_296_);
lean_dec(v_depth_296_);
v_res_302_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(v_depth_boxed_301_, v_keys_297_, v_vals_298_, v_i_299_, v_entries_300_);
lean_dec_ref(v_vals_298_);
lean_dec_ref(v_keys_297_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_303_, lean_object* v_x_304_, lean_object* v_x_305_, lean_object* v_x_306_, lean_object* v_x_307_){
_start:
{
size_t v_x_5193__boxed_308_; size_t v_x_5194__boxed_309_; lean_object* v_res_310_; 
v_x_5193__boxed_308_ = lean_unbox_usize(v_x_304_);
lean_dec(v_x_304_);
v_x_5194__boxed_309_ = lean_unbox_usize(v_x_305_);
lean_dec(v_x_305_);
v_res_310_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_303_, v_x_5193__boxed_308_, v_x_5194__boxed_309_, v_x_306_, v_x_307_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(lean_object* v_x_311_, lean_object* v_x_312_, lean_object* v_x_313_){
_start:
{
uint64_t v___x_314_; size_t v___x_315_; size_t v___x_316_; lean_object* v___x_317_; 
v___x_314_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_312_);
v___x_315_ = lean_uint64_to_usize(v___x_314_);
v___x_316_ = ((size_t)1ULL);
v___x_317_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_311_, v___x_315_, v___x_316_, v_x_312_, v_x_313_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(lean_object* v_keys_318_, lean_object* v_vals_319_, lean_object* v_i_320_, lean_object* v_k_321_){
_start:
{
lean_object* v___x_322_; uint8_t v___x_323_; 
v___x_322_ = lean_array_get_size(v_keys_318_);
v___x_323_ = lean_nat_dec_lt(v_i_320_, v___x_322_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; 
lean_dec(v_i_320_);
v___x_324_ = lean_box(0);
return v___x_324_;
}
else
{
lean_object* v_k_x27_325_; uint8_t v___x_326_; 
v_k_x27_325_ = lean_array_fget_borrowed(v_keys_318_, v_i_320_);
v___x_326_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_321_, v_k_x27_325_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = lean_unsigned_to_nat(1u);
v___x_328_ = lean_nat_add(v_i_320_, v___x_327_);
lean_dec(v_i_320_);
v_i_320_ = v___x_328_;
goto _start;
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = lean_array_fget_borrowed(v_vals_319_, v_i_320_);
lean_dec(v_i_320_);
lean_inc(v___x_330_);
v___x_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
return v___x_331_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_keys_332_, lean_object* v_vals_333_, lean_object* v_i_334_, lean_object* v_k_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_keys_332_, v_vals_333_, v_i_334_, v_k_335_);
lean_dec_ref(v_k_335_);
lean_dec_ref(v_vals_333_);
lean_dec_ref(v_keys_332_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(lean_object* v_x_337_, size_t v_x_338_, lean_object* v_x_339_){
_start:
{
if (lean_obj_tag(v_x_337_) == 0)
{
lean_object* v_es_340_; lean_object* v___x_341_; size_t v___x_342_; size_t v___x_343_; lean_object* v_j_344_; lean_object* v___x_345_; 
v_es_340_ = lean_ctor_get(v_x_337_, 0);
v___x_341_ = lean_box(2);
v___x_342_ = ((size_t)31ULL);
v___x_343_ = lean_usize_land(v_x_338_, v___x_342_);
v_j_344_ = lean_usize_to_nat(v___x_343_);
v___x_345_ = lean_array_get_borrowed(v___x_341_, v_es_340_, v_j_344_);
lean_dec(v_j_344_);
switch(lean_obj_tag(v___x_345_))
{
case 0:
{
lean_object* v_key_346_; lean_object* v_val_347_; uint8_t v___x_348_; 
v_key_346_ = lean_ctor_get(v___x_345_, 0);
v_val_347_ = lean_ctor_get(v___x_345_, 1);
v___x_348_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_339_, v_key_346_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; 
v___x_349_ = lean_box(0);
return v___x_349_;
}
else
{
lean_object* v___x_350_; 
lean_inc(v_val_347_);
v___x_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_350_, 0, v_val_347_);
return v___x_350_;
}
}
case 1:
{
lean_object* v_node_351_; size_t v___x_352_; size_t v___x_353_; 
v_node_351_ = lean_ctor_get(v___x_345_, 0);
v___x_352_ = ((size_t)5ULL);
v___x_353_ = lean_usize_shift_right(v_x_338_, v___x_352_);
v_x_337_ = v_node_351_;
v_x_338_ = v___x_353_;
goto _start;
}
default: 
{
lean_object* v___x_355_; 
v___x_355_ = lean_box(0);
return v___x_355_;
}
}
}
else
{
lean_object* v_ks_356_; lean_object* v_vs_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v_ks_356_ = lean_ctor_get(v_x_337_, 0);
v_vs_357_ = lean_ctor_get(v_x_337_, 1);
v___x_358_ = lean_unsigned_to_nat(0u);
v___x_359_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_ks_356_, v_vs_357_, v___x_358_, v_x_339_);
return v___x_359_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_x_360_, lean_object* v_x_361_, lean_object* v_x_362_){
_start:
{
size_t v_x_5381__boxed_363_; lean_object* v_res_364_; 
v_x_5381__boxed_363_ = lean_unbox_usize(v_x_361_);
lean_dec(v_x_361_);
v_res_364_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_360_, v_x_5381__boxed_363_, v_x_362_);
lean_dec_ref(v_x_362_);
lean_dec_ref(v_x_360_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(lean_object* v_x_365_, lean_object* v_x_366_){
_start:
{
uint64_t v___x_367_; size_t v___x_368_; lean_object* v___x_369_; 
v___x_367_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_366_);
v___x_368_ = lean_uint64_to_usize(v___x_367_);
v___x_369_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_365_, v___x_368_, v_x_366_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg___boxed(lean_object* v_x_370_, lean_object* v_x_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_x_370_, v_x_371_);
lean_dec_ref(v_x_371_);
lean_dec_ref(v_x_370_);
return v_res_372_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_376_ = ((lean_object*)(l_Lean_Meta_Sym_getMaxFVar_x3f___closed__2));
v___x_377_ = lean_unsigned_to_nat(37u);
v___x_378_ = lean_unsigned_to_nat(52u);
v___x_379_ = ((lean_object*)(l_Lean_Meta_Sym_getMaxFVar_x3f___closed__1));
v___x_380_ = ((lean_object*)(l_Lean_Meta_Sym_getMaxFVar_x3f___closed__0));
v___x_381_ = l_mkPanicMessageWithDecl(v___x_380_, v___x_379_, v___x_378_, v___x_377_, v___x_376_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f(lean_object* v_e_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_){
_start:
{
lean_object* v___y_391_; lean_object* v_a_422_; lean_object* v___y_446_; lean_object* v___y_447_; lean_object* v___y_478_; lean_object* v___y_479_; lean_object* v___y_480_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v___y_485_; uint8_t v___y_486_; lean_object* v_d_506_; lean_object* v_b_507_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_517_; 
switch(lean_obj_tag(v_e_382_))
{
case 1:
{
lean_object* v_fvarId_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v_fvarId_547_ = lean_ctor_get(v_e_382_, 0);
lean_inc(v_fvarId_547_);
lean_dec_ref_known(v_e_382_, 1);
v___x_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_548_, 0, v_fvarId_547_);
v___x_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
return v___x_549_;
}
case 2:
{
lean_object* v_mvarId_550_; uint8_t v___y_552_; uint8_t v___x_593_; 
v_mvarId_550_ = lean_ctor_get(v_e_382_, 0);
v___x_593_ = l_Lean_Expr_hasFVar(v_e_382_);
if (v___x_593_ == 0)
{
uint8_t v___x_594_; 
v___x_594_ = l_Lean_Expr_hasMVar(v_e_382_);
v___y_552_ = v___x_594_;
goto v___jp_551_;
}
else
{
v___y_552_ = v___x_593_;
goto v___jp_551_;
}
v___jp_551_:
{
if (v___y_552_ == 0)
{
lean_object* v___x_553_; lean_object* v___x_554_; 
lean_dec_ref_known(v_e_382_, 1);
v___x_553_ = lean_box(0);
v___x_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
return v___x_554_;
}
else
{
lean_object* v___x_555_; lean_object* v_maxFVar_556_; lean_object* v___x_557_; 
v___x_555_ = lean_st_ref_get(v_a_384_);
v_maxFVar_556_ = lean_ctor_get(v___x_555_, 1);
lean_inc_ref(v_maxFVar_556_);
lean_dec(v___x_555_);
v___x_557_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_556_, v_e_382_);
lean_dec_ref(v_maxFVar_556_);
if (lean_obj_tag(v___x_557_) == 1)
{
lean_object* v_val_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_565_; 
lean_dec_ref_known(v_e_382_, 1);
v_val_558_ = lean_ctor_get(v___x_557_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_565_ == 0)
{
v___x_560_ = v___x_557_;
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_val_558_);
lean_dec(v___x_557_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_563_; 
if (v_isShared_561_ == 0)
{
lean_ctor_set_tag(v___x_560_, 0);
v___x_563_ = v___x_560_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_val_558_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
else
{
lean_object* v___x_566_; 
lean_dec(v___x_557_);
lean_inc(v_mvarId_550_);
v___x_566_ = l_Lean_MVarId_getDecl(v_mvarId_550_, v_a_385_, v_a_386_, v_a_387_, v_a_388_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v_a_567_; lean_object* v_lctx_568_; lean_object* v_decls_569_; uint8_t v___x_570_; 
v_a_567_ = lean_ctor_get(v___x_566_, 0);
lean_inc(v_a_567_);
lean_dec_ref_known(v___x_566_, 1);
v_lctx_568_ = lean_ctor_get(v_a_567_, 1);
lean_inc_ref(v_lctx_568_);
lean_dec(v_a_567_);
v_decls_569_ = lean_ctor_get(v_lctx_568_, 1);
v___x_570_ = l_Lean_PersistentArray_isEmpty___redArg(v_decls_569_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; 
v___x_571_ = l_Lean_LocalContext_lastDecl(v_lctx_568_);
lean_dec_ref(v_lctx_568_);
if (lean_obj_tag(v___x_571_) == 1)
{
lean_object* v_val_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_580_; 
v_val_572_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_580_ == 0)
{
v___x_574_ = v___x_571_;
v_isShared_575_ = v_isSharedCheck_580_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_val_572_);
lean_dec(v___x_571_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_580_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_576_; lean_object* v___x_578_; 
v___x_576_ = l_Lean_LocalDecl_fvarId(v_val_572_);
lean_dec(v_val_572_);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v___x_576_);
v___x_578_ = v___x_574_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_576_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
v_a_422_ = v___x_578_;
goto v___jp_421_;
}
}
}
else
{
lean_object* v___x_581_; lean_object* v___x_582_; 
lean_dec(v___x_571_);
v___x_581_ = lean_obj_once(&l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3, &l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3_once, _init_l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3);
v___x_582_ = l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2(v___x_581_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_a_583_);
lean_dec_ref_known(v___x_582_, 1);
v_a_422_ = v_a_583_;
goto v___jp_421_;
}
else
{
lean_dec_ref_known(v_e_382_, 1);
return v___x_582_;
}
}
}
else
{
lean_object* v___x_584_; 
lean_dec_ref(v_lctx_568_);
v___x_584_ = lean_box(0);
v_a_422_ = v___x_584_;
goto v___jp_421_;
}
}
else
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_592_; 
lean_dec_ref_known(v_e_382_, 1);
v_a_585_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_592_ == 0)
{
v___x_587_ = v___x_566_;
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_566_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_588_ == 0)
{
v___x_590_ = v___x_587_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_585_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
}
}
}
case 5:
{
lean_object* v_fn_595_; lean_object* v_arg_596_; uint8_t v___y_598_; uint8_t v___x_617_; 
v_fn_595_ = lean_ctor_get(v_e_382_, 0);
v_arg_596_ = lean_ctor_get(v_e_382_, 1);
v___x_617_ = l_Lean_Expr_hasFVar(v_e_382_);
if (v___x_617_ == 0)
{
uint8_t v___x_618_; 
v___x_618_ = l_Lean_Expr_hasMVar(v_e_382_);
v___y_598_ = v___x_618_;
goto v___jp_597_;
}
else
{
v___y_598_ = v___x_617_;
goto v___jp_597_;
}
v___jp_597_:
{
if (v___y_598_ == 0)
{
lean_object* v___x_599_; lean_object* v___x_600_; 
lean_dec_ref_known(v_e_382_, 2);
v___x_599_ = lean_box(0);
v___x_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
return v___x_600_;
}
else
{
lean_object* v___x_601_; lean_object* v_maxFVar_602_; lean_object* v___x_603_; 
v___x_601_ = lean_st_ref_get(v_a_384_);
v_maxFVar_602_ = lean_ctor_get(v___x_601_, 1);
lean_inc_ref(v_maxFVar_602_);
lean_dec(v___x_601_);
v___x_603_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_602_, v_e_382_);
lean_dec_ref(v_maxFVar_602_);
if (lean_obj_tag(v___x_603_) == 1)
{
lean_object* v_val_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
lean_dec_ref_known(v_e_382_, 2);
v_val_604_ = lean_ctor_get(v___x_603_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___x_603_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_val_604_);
lean_dec(v___x_603_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
lean_ctor_set_tag(v___x_606_, 0);
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_val_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
else
{
lean_object* v___x_612_; 
lean_dec(v___x_603_);
lean_inc_ref(v_fn_595_);
v___x_612_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_fn_595_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_613_; lean_object* v___x_614_; 
v_a_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_a_613_);
lean_dec_ref_known(v___x_612_, 1);
lean_inc_ref(v_arg_596_);
v___x_614_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_arg_596_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; lean_object* v___x_616_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_a_615_);
lean_dec_ref_known(v___x_614_, 1);
v___x_616_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_613_, v_a_615_, v_a_385_, v_a_387_, v_a_388_);
v___y_517_ = v___x_616_;
goto v___jp_516_;
}
else
{
lean_dec(v_a_613_);
v___y_517_ = v___x_614_;
goto v___jp_516_;
}
}
else
{
v___y_517_ = v___x_612_;
goto v___jp_516_;
}
}
}
}
}
case 6:
{
lean_object* v_binderType_619_; lean_object* v_body_620_; 
v_binderType_619_ = lean_ctor_get(v_e_382_, 1);
v_body_620_ = lean_ctor_get(v_e_382_, 2);
lean_inc_ref(v_body_620_);
lean_inc_ref(v_binderType_619_);
v_d_506_ = v_binderType_619_;
v_b_507_ = v_body_620_;
v___y_508_ = v_a_383_;
v___y_509_ = v_a_384_;
v___y_510_ = v_a_385_;
v___y_511_ = v_a_386_;
v___y_512_ = v_a_387_;
v___y_513_ = v_a_388_;
goto v___jp_505_;
}
case 7:
{
lean_object* v_binderType_621_; lean_object* v_body_622_; 
v_binderType_621_ = lean_ctor_get(v_e_382_, 1);
v_body_622_ = lean_ctor_get(v_e_382_, 2);
lean_inc_ref(v_body_622_);
lean_inc_ref(v_binderType_621_);
v_d_506_ = v_binderType_621_;
v_b_507_ = v_body_622_;
v___y_508_ = v_a_383_;
v___y_509_ = v_a_384_;
v___y_510_ = v_a_385_;
v___y_511_ = v_a_386_;
v___y_512_ = v_a_387_;
v___y_513_ = v_a_388_;
goto v___jp_505_;
}
case 8:
{
lean_object* v_type_623_; lean_object* v_value_624_; lean_object* v_body_625_; uint8_t v___y_627_; uint8_t v___x_650_; 
v_type_623_ = lean_ctor_get(v_e_382_, 1);
v_value_624_ = lean_ctor_get(v_e_382_, 2);
v_body_625_ = lean_ctor_get(v_e_382_, 3);
v___x_650_ = l_Lean_Expr_hasFVar(v_e_382_);
if (v___x_650_ == 0)
{
uint8_t v___x_651_; 
v___x_651_ = l_Lean_Expr_hasMVar(v_e_382_);
v___y_627_ = v___x_651_;
goto v___jp_626_;
}
else
{
v___y_627_ = v___x_650_;
goto v___jp_626_;
}
v___jp_626_:
{
if (v___y_627_ == 0)
{
lean_object* v___x_628_; lean_object* v___x_629_; 
lean_dec_ref_known(v_e_382_, 4);
v___x_628_ = lean_box(0);
v___x_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
return v___x_629_;
}
else
{
lean_object* v___x_630_; lean_object* v_maxFVar_631_; lean_object* v___x_632_; 
v___x_630_ = lean_st_ref_get(v_a_384_);
v_maxFVar_631_ = lean_ctor_get(v___x_630_, 1);
lean_inc_ref(v_maxFVar_631_);
lean_dec(v___x_630_);
v___x_632_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_631_, v_e_382_);
lean_dec_ref(v_maxFVar_631_);
if (lean_obj_tag(v___x_632_) == 1)
{
lean_object* v_val_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
lean_dec_ref_known(v_e_382_, 4);
v_val_633_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_640_ == 0)
{
v___x_635_ = v___x_632_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_val_633_);
lean_dec(v___x_632_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
lean_ctor_set_tag(v___x_635_, 0);
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_val_633_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
else
{
lean_object* v___x_641_; 
lean_dec(v___x_632_);
lean_inc_ref(v_type_623_);
v___x_641_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_type_623_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; lean_object* v___x_643_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_a_642_);
lean_dec_ref_known(v___x_641_, 1);
lean_inc_ref(v_value_624_);
v___x_643_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_value_624_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v_a_644_; lean_object* v___x_645_; 
v_a_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_a_644_);
lean_dec_ref_known(v___x_643_, 1);
v___x_645_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_642_, v_a_644_, v_a_385_, v_a_387_, v_a_388_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v_a_646_; lean_object* v___x_647_; 
v_a_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_a_646_);
lean_dec_ref_known(v___x_645_, 1);
lean_inc_ref(v_body_625_);
v___x_647_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_body_625_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; lean_object* v___x_649_; 
v_a_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc(v_a_648_);
lean_dec_ref_known(v___x_647_, 1);
v___x_649_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_646_, v_a_648_, v_a_385_, v_a_387_, v_a_388_);
v___y_391_ = v___x_649_;
goto v___jp_390_;
}
else
{
lean_dec(v_a_646_);
v___y_391_ = v___x_647_;
goto v___jp_390_;
}
}
else
{
v___y_391_ = v___x_645_;
goto v___jp_390_;
}
}
else
{
lean_dec(v_a_642_);
v___y_391_ = v___x_643_;
goto v___jp_390_;
}
}
else
{
v___y_391_ = v___x_641_;
goto v___jp_390_;
}
}
}
}
}
case 10:
{
lean_object* v_expr_652_; uint8_t v___y_654_; uint8_t v___x_698_; 
v_expr_652_ = lean_ctor_get(v_e_382_, 1);
lean_inc_ref(v_expr_652_);
lean_dec_ref_known(v_e_382_, 2);
v___x_698_ = l_Lean_Expr_hasFVar(v_expr_652_);
if (v___x_698_ == 0)
{
uint8_t v___x_699_; 
v___x_699_ = l_Lean_Expr_hasMVar(v_expr_652_);
v___y_654_ = v___x_699_;
goto v___jp_653_;
}
else
{
v___y_654_ = v___x_698_;
goto v___jp_653_;
}
v___jp_653_:
{
if (v___y_654_ == 0)
{
lean_object* v___x_655_; lean_object* v___x_656_; 
lean_dec_ref(v_expr_652_);
v___x_655_ = lean_box(0);
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
return v___x_656_;
}
else
{
lean_object* v___x_657_; lean_object* v_maxFVar_658_; lean_object* v___x_659_; 
v___x_657_ = lean_st_ref_get(v_a_384_);
v_maxFVar_658_ = lean_ctor_get(v___x_657_, 1);
lean_inc_ref(v_maxFVar_658_);
lean_dec(v___x_657_);
v___x_659_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_658_, v_expr_652_);
lean_dec_ref(v_maxFVar_658_);
if (lean_obj_tag(v___x_659_) == 1)
{
lean_object* v_val_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_667_; 
lean_dec_ref(v_expr_652_);
v_val_660_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_667_ == 0)
{
v___x_662_ = v___x_659_;
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_val_660_);
lean_dec(v___x_659_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
if (v_isShared_663_ == 0)
{
lean_ctor_set_tag(v___x_662_, 0);
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_val_660_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
else
{
lean_object* v___x_668_; 
lean_dec(v___x_659_);
lean_inc_ref(v_expr_652_);
v___x_668_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_expr_652_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_697_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_697_ == 0)
{
v___x_671_ = v___x_668_;
v_isShared_672_ = v_isSharedCheck_697_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_668_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_697_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_673_; lean_object* v_share_674_; lean_object* v_maxFVar_675_; lean_object* v_proofInstInfo_676_; lean_object* v_inferType_677_; lean_object* v_getLevel_678_; lean_object* v_congrInfo_679_; lean_object* v_defEqI_680_; lean_object* v_extensions_681_; lean_object* v_issues_682_; lean_object* v_canon_683_; uint8_t v_debug_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_696_; 
v___x_673_ = lean_st_ref_take(v_a_384_);
v_share_674_ = lean_ctor_get(v___x_673_, 0);
v_maxFVar_675_ = lean_ctor_get(v___x_673_, 1);
v_proofInstInfo_676_ = lean_ctor_get(v___x_673_, 2);
v_inferType_677_ = lean_ctor_get(v___x_673_, 3);
v_getLevel_678_ = lean_ctor_get(v___x_673_, 4);
v_congrInfo_679_ = lean_ctor_get(v___x_673_, 5);
v_defEqI_680_ = lean_ctor_get(v___x_673_, 6);
v_extensions_681_ = lean_ctor_get(v___x_673_, 7);
v_issues_682_ = lean_ctor_get(v___x_673_, 8);
v_canon_683_ = lean_ctor_get(v___x_673_, 9);
v_debug_684_ = lean_ctor_get_uint8(v___x_673_, sizeof(void*)*10);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_696_ == 0)
{
v___x_686_ = v___x_673_;
v_isShared_687_ = v_isSharedCheck_696_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_canon_683_);
lean_inc(v_issues_682_);
lean_inc(v_extensions_681_);
lean_inc(v_defEqI_680_);
lean_inc(v_congrInfo_679_);
lean_inc(v_getLevel_678_);
lean_inc(v_inferType_677_);
lean_inc(v_proofInstInfo_676_);
lean_inc(v_maxFVar_675_);
lean_inc(v_share_674_);
lean_dec(v___x_673_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_696_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v___x_690_; 
lean_inc(v_a_669_);
v___x_688_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_675_, v_expr_652_, v_a_669_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 1, v___x_688_);
v___x_690_ = v___x_686_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_share_674_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v___x_688_);
lean_ctor_set(v_reuseFailAlloc_695_, 2, v_proofInstInfo_676_);
lean_ctor_set(v_reuseFailAlloc_695_, 3, v_inferType_677_);
lean_ctor_set(v_reuseFailAlloc_695_, 4, v_getLevel_678_);
lean_ctor_set(v_reuseFailAlloc_695_, 5, v_congrInfo_679_);
lean_ctor_set(v_reuseFailAlloc_695_, 6, v_defEqI_680_);
lean_ctor_set(v_reuseFailAlloc_695_, 7, v_extensions_681_);
lean_ctor_set(v_reuseFailAlloc_695_, 8, v_issues_682_);
lean_ctor_set(v_reuseFailAlloc_695_, 9, v_canon_683_);
lean_ctor_set_uint8(v_reuseFailAlloc_695_, sizeof(void*)*10, v_debug_684_);
v___x_690_ = v_reuseFailAlloc_695_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
lean_object* v___x_691_; lean_object* v___x_693_; 
v___x_691_ = lean_st_ref_set(v_a_384_, v___x_690_);
if (v_isShared_672_ == 0)
{
v___x_693_ = v___x_671_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_a_669_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
}
else
{
lean_dec_ref(v_expr_652_);
return v___x_668_;
}
}
}
}
}
case 11:
{
lean_object* v_struct_700_; uint8_t v___y_702_; uint8_t v___x_746_; 
v_struct_700_ = lean_ctor_get(v_e_382_, 2);
v___x_746_ = l_Lean_Expr_hasFVar(v_e_382_);
if (v___x_746_ == 0)
{
uint8_t v___x_747_; 
v___x_747_ = l_Lean_Expr_hasMVar(v_e_382_);
v___y_702_ = v___x_747_;
goto v___jp_701_;
}
else
{
v___y_702_ = v___x_746_;
goto v___jp_701_;
}
v___jp_701_:
{
if (v___y_702_ == 0)
{
lean_object* v___x_703_; lean_object* v___x_704_; 
lean_dec_ref_known(v_e_382_, 3);
v___x_703_ = lean_box(0);
v___x_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
return v___x_704_;
}
else
{
lean_object* v___x_705_; lean_object* v_maxFVar_706_; lean_object* v___x_707_; 
v___x_705_ = lean_st_ref_get(v_a_384_);
v_maxFVar_706_ = lean_ctor_get(v___x_705_, 1);
lean_inc_ref(v_maxFVar_706_);
lean_dec(v___x_705_);
v___x_707_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_706_, v_e_382_);
lean_dec_ref(v_maxFVar_706_);
if (lean_obj_tag(v___x_707_) == 1)
{
lean_object* v_val_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
lean_dec_ref_known(v_e_382_, 3);
v_val_708_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___x_707_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_val_708_);
lean_dec(v___x_707_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
lean_ctor_set_tag(v___x_710_, 0);
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_val_708_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
else
{
lean_object* v___x_716_; 
lean_dec(v___x_707_);
lean_inc_ref(v_struct_700_);
v___x_716_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_struct_700_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_745_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_745_ == 0)
{
v___x_719_ = v___x_716_;
v_isShared_720_ = v_isSharedCheck_745_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_716_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_745_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_721_; lean_object* v_share_722_; lean_object* v_maxFVar_723_; lean_object* v_proofInstInfo_724_; lean_object* v_inferType_725_; lean_object* v_getLevel_726_; lean_object* v_congrInfo_727_; lean_object* v_defEqI_728_; lean_object* v_extensions_729_; lean_object* v_issues_730_; lean_object* v_canon_731_; uint8_t v_debug_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_744_; 
v___x_721_ = lean_st_ref_take(v_a_384_);
v_share_722_ = lean_ctor_get(v___x_721_, 0);
v_maxFVar_723_ = lean_ctor_get(v___x_721_, 1);
v_proofInstInfo_724_ = lean_ctor_get(v___x_721_, 2);
v_inferType_725_ = lean_ctor_get(v___x_721_, 3);
v_getLevel_726_ = lean_ctor_get(v___x_721_, 4);
v_congrInfo_727_ = lean_ctor_get(v___x_721_, 5);
v_defEqI_728_ = lean_ctor_get(v___x_721_, 6);
v_extensions_729_ = lean_ctor_get(v___x_721_, 7);
v_issues_730_ = lean_ctor_get(v___x_721_, 8);
v_canon_731_ = lean_ctor_get(v___x_721_, 9);
v_debug_732_ = lean_ctor_get_uint8(v___x_721_, sizeof(void*)*10);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_744_ == 0)
{
v___x_734_ = v___x_721_;
v_isShared_735_ = v_isSharedCheck_744_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_canon_731_);
lean_inc(v_issues_730_);
lean_inc(v_extensions_729_);
lean_inc(v_defEqI_728_);
lean_inc(v_congrInfo_727_);
lean_inc(v_getLevel_726_);
lean_inc(v_inferType_725_);
lean_inc(v_proofInstInfo_724_);
lean_inc(v_maxFVar_723_);
lean_inc(v_share_722_);
lean_dec(v___x_721_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_744_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_736_; lean_object* v___x_738_; 
lean_inc(v_a_717_);
v___x_736_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_723_, v_e_382_, v_a_717_);
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 1, v___x_736_);
v___x_738_ = v___x_734_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_share_722_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v___x_736_);
lean_ctor_set(v_reuseFailAlloc_743_, 2, v_proofInstInfo_724_);
lean_ctor_set(v_reuseFailAlloc_743_, 3, v_inferType_725_);
lean_ctor_set(v_reuseFailAlloc_743_, 4, v_getLevel_726_);
lean_ctor_set(v_reuseFailAlloc_743_, 5, v_congrInfo_727_);
lean_ctor_set(v_reuseFailAlloc_743_, 6, v_defEqI_728_);
lean_ctor_set(v_reuseFailAlloc_743_, 7, v_extensions_729_);
lean_ctor_set(v_reuseFailAlloc_743_, 8, v_issues_730_);
lean_ctor_set(v_reuseFailAlloc_743_, 9, v_canon_731_);
lean_ctor_set_uint8(v_reuseFailAlloc_743_, sizeof(void*)*10, v_debug_732_);
v___x_738_ = v_reuseFailAlloc_743_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
lean_object* v___x_739_; lean_object* v___x_741_; 
v___x_739_ = lean_st_ref_set(v_a_384_, v___x_738_);
if (v_isShared_720_ == 0)
{
v___x_741_ = v___x_719_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_717_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_382_, 3);
return v___x_716_;
}
}
}
}
}
default: 
{
lean_object* v___x_748_; lean_object* v___x_749_; 
lean_dec_ref(v_e_382_);
v___x_748_ = lean_box(0);
v___x_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
return v___x_749_;
}
}
v___jp_390_:
{
if (lean_obj_tag(v___y_391_) == 0)
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_420_; 
v_a_392_ = lean_ctor_get(v___y_391_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___y_391_);
if (v_isSharedCheck_420_ == 0)
{
v___x_394_ = v___y_391_;
v_isShared_395_ = v_isSharedCheck_420_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___y_391_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_420_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_396_; lean_object* v_share_397_; lean_object* v_maxFVar_398_; lean_object* v_proofInstInfo_399_; lean_object* v_inferType_400_; lean_object* v_getLevel_401_; lean_object* v_congrInfo_402_; lean_object* v_defEqI_403_; lean_object* v_extensions_404_; lean_object* v_issues_405_; lean_object* v_canon_406_; uint8_t v_debug_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_419_; 
v___x_396_ = lean_st_ref_take(v_a_384_);
v_share_397_ = lean_ctor_get(v___x_396_, 0);
v_maxFVar_398_ = lean_ctor_get(v___x_396_, 1);
v_proofInstInfo_399_ = lean_ctor_get(v___x_396_, 2);
v_inferType_400_ = lean_ctor_get(v___x_396_, 3);
v_getLevel_401_ = lean_ctor_get(v___x_396_, 4);
v_congrInfo_402_ = lean_ctor_get(v___x_396_, 5);
v_defEqI_403_ = lean_ctor_get(v___x_396_, 6);
v_extensions_404_ = lean_ctor_get(v___x_396_, 7);
v_issues_405_ = lean_ctor_get(v___x_396_, 8);
v_canon_406_ = lean_ctor_get(v___x_396_, 9);
v_debug_407_ = lean_ctor_get_uint8(v___x_396_, sizeof(void*)*10);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_419_ == 0)
{
v___x_409_ = v___x_396_;
v_isShared_410_ = v_isSharedCheck_419_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_canon_406_);
lean_inc(v_issues_405_);
lean_inc(v_extensions_404_);
lean_inc(v_defEqI_403_);
lean_inc(v_congrInfo_402_);
lean_inc(v_getLevel_401_);
lean_inc(v_inferType_400_);
lean_inc(v_proofInstInfo_399_);
lean_inc(v_maxFVar_398_);
lean_inc(v_share_397_);
lean_dec(v___x_396_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_419_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_411_; lean_object* v___x_413_; 
lean_inc(v_a_392_);
v___x_411_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_398_, v_e_382_, v_a_392_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 1, v___x_411_);
v___x_413_ = v___x_409_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_share_397_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v___x_411_);
lean_ctor_set(v_reuseFailAlloc_418_, 2, v_proofInstInfo_399_);
lean_ctor_set(v_reuseFailAlloc_418_, 3, v_inferType_400_);
lean_ctor_set(v_reuseFailAlloc_418_, 4, v_getLevel_401_);
lean_ctor_set(v_reuseFailAlloc_418_, 5, v_congrInfo_402_);
lean_ctor_set(v_reuseFailAlloc_418_, 6, v_defEqI_403_);
lean_ctor_set(v_reuseFailAlloc_418_, 7, v_extensions_404_);
lean_ctor_set(v_reuseFailAlloc_418_, 8, v_issues_405_);
lean_ctor_set(v_reuseFailAlloc_418_, 9, v_canon_406_);
lean_ctor_set_uint8(v_reuseFailAlloc_418_, sizeof(void*)*10, v_debug_407_);
v___x_413_ = v_reuseFailAlloc_418_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
lean_object* v___x_414_; lean_object* v___x_416_; 
v___x_414_ = lean_st_ref_set(v_a_384_, v___x_413_);
if (v_isShared_395_ == 0)
{
v___x_416_ = v___x_394_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_a_392_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_382_);
return v___y_391_;
}
}
v___jp_421_:
{
lean_object* v___x_423_; lean_object* v_share_424_; lean_object* v_maxFVar_425_; lean_object* v_proofInstInfo_426_; lean_object* v_inferType_427_; lean_object* v_getLevel_428_; lean_object* v_congrInfo_429_; lean_object* v_defEqI_430_; lean_object* v_extensions_431_; lean_object* v_issues_432_; lean_object* v_canon_433_; uint8_t v_debug_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_444_; 
v___x_423_ = lean_st_ref_take(v_a_384_);
v_share_424_ = lean_ctor_get(v___x_423_, 0);
v_maxFVar_425_ = lean_ctor_get(v___x_423_, 1);
v_proofInstInfo_426_ = lean_ctor_get(v___x_423_, 2);
v_inferType_427_ = lean_ctor_get(v___x_423_, 3);
v_getLevel_428_ = lean_ctor_get(v___x_423_, 4);
v_congrInfo_429_ = lean_ctor_get(v___x_423_, 5);
v_defEqI_430_ = lean_ctor_get(v___x_423_, 6);
v_extensions_431_ = lean_ctor_get(v___x_423_, 7);
v_issues_432_ = lean_ctor_get(v___x_423_, 8);
v_canon_433_ = lean_ctor_get(v___x_423_, 9);
v_debug_434_ = lean_ctor_get_uint8(v___x_423_, sizeof(void*)*10);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_444_ == 0)
{
v___x_436_ = v___x_423_;
v_isShared_437_ = v_isSharedCheck_444_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_canon_433_);
lean_inc(v_issues_432_);
lean_inc(v_extensions_431_);
lean_inc(v_defEqI_430_);
lean_inc(v_congrInfo_429_);
lean_inc(v_getLevel_428_);
lean_inc(v_inferType_427_);
lean_inc(v_proofInstInfo_426_);
lean_inc(v_maxFVar_425_);
lean_inc(v_share_424_);
lean_dec(v___x_423_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_444_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_438_; lean_object* v___x_440_; 
lean_inc(v_a_422_);
v___x_438_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_425_, v_e_382_, v_a_422_);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 1, v___x_438_);
v___x_440_ = v___x_436_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_share_424_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v___x_438_);
lean_ctor_set(v_reuseFailAlloc_443_, 2, v_proofInstInfo_426_);
lean_ctor_set(v_reuseFailAlloc_443_, 3, v_inferType_427_);
lean_ctor_set(v_reuseFailAlloc_443_, 4, v_getLevel_428_);
lean_ctor_set(v_reuseFailAlloc_443_, 5, v_congrInfo_429_);
lean_ctor_set(v_reuseFailAlloc_443_, 6, v_defEqI_430_);
lean_ctor_set(v_reuseFailAlloc_443_, 7, v_extensions_431_);
lean_ctor_set(v_reuseFailAlloc_443_, 8, v_issues_432_);
lean_ctor_set(v_reuseFailAlloc_443_, 9, v_canon_433_);
lean_ctor_set_uint8(v_reuseFailAlloc_443_, sizeof(void*)*10, v_debug_434_);
v___x_440_ = v_reuseFailAlloc_443_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = lean_st_ref_set(v_a_384_, v___x_440_);
v___x_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_442_, 0, v_a_422_);
return v___x_442_;
}
}
}
v___jp_445_:
{
if (lean_obj_tag(v___y_447_) == 0)
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_476_; 
v_a_448_ = lean_ctor_get(v___y_447_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___y_447_);
if (v_isSharedCheck_476_ == 0)
{
v___x_450_ = v___y_447_;
v_isShared_451_ = v_isSharedCheck_476_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___y_447_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_476_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_452_; lean_object* v_share_453_; lean_object* v_maxFVar_454_; lean_object* v_proofInstInfo_455_; lean_object* v_inferType_456_; lean_object* v_getLevel_457_; lean_object* v_congrInfo_458_; lean_object* v_defEqI_459_; lean_object* v_extensions_460_; lean_object* v_issues_461_; lean_object* v_canon_462_; uint8_t v_debug_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_475_; 
v___x_452_ = lean_st_ref_take(v___y_446_);
v_share_453_ = lean_ctor_get(v___x_452_, 0);
v_maxFVar_454_ = lean_ctor_get(v___x_452_, 1);
v_proofInstInfo_455_ = lean_ctor_get(v___x_452_, 2);
v_inferType_456_ = lean_ctor_get(v___x_452_, 3);
v_getLevel_457_ = lean_ctor_get(v___x_452_, 4);
v_congrInfo_458_ = lean_ctor_get(v___x_452_, 5);
v_defEqI_459_ = lean_ctor_get(v___x_452_, 6);
v_extensions_460_ = lean_ctor_get(v___x_452_, 7);
v_issues_461_ = lean_ctor_get(v___x_452_, 8);
v_canon_462_ = lean_ctor_get(v___x_452_, 9);
v_debug_463_ = lean_ctor_get_uint8(v___x_452_, sizeof(void*)*10);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_475_ == 0)
{
v___x_465_ = v___x_452_;
v_isShared_466_ = v_isSharedCheck_475_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_canon_462_);
lean_inc(v_issues_461_);
lean_inc(v_extensions_460_);
lean_inc(v_defEqI_459_);
lean_inc(v_congrInfo_458_);
lean_inc(v_getLevel_457_);
lean_inc(v_inferType_456_);
lean_inc(v_proofInstInfo_455_);
lean_inc(v_maxFVar_454_);
lean_inc(v_share_453_);
lean_dec(v___x_452_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_475_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_467_; lean_object* v___x_469_; 
lean_inc(v_a_448_);
v___x_467_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_454_, v_e_382_, v_a_448_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 1, v___x_467_);
v___x_469_ = v___x_465_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_share_453_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v___x_467_);
lean_ctor_set(v_reuseFailAlloc_474_, 2, v_proofInstInfo_455_);
lean_ctor_set(v_reuseFailAlloc_474_, 3, v_inferType_456_);
lean_ctor_set(v_reuseFailAlloc_474_, 4, v_getLevel_457_);
lean_ctor_set(v_reuseFailAlloc_474_, 5, v_congrInfo_458_);
lean_ctor_set(v_reuseFailAlloc_474_, 6, v_defEqI_459_);
lean_ctor_set(v_reuseFailAlloc_474_, 7, v_extensions_460_);
lean_ctor_set(v_reuseFailAlloc_474_, 8, v_issues_461_);
lean_ctor_set(v_reuseFailAlloc_474_, 9, v_canon_462_);
lean_ctor_set_uint8(v_reuseFailAlloc_474_, sizeof(void*)*10, v_debug_463_);
v___x_469_ = v_reuseFailAlloc_474_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_470_; lean_object* v___x_472_; 
v___x_470_ = lean_st_ref_set(v___y_446_, v___x_469_);
if (v_isShared_451_ == 0)
{
v___x_472_ = v___x_450_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_a_448_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_382_);
return v___y_447_;
}
}
v___jp_477_:
{
if (v___y_486_ == 0)
{
lean_object* v___x_487_; lean_object* v___x_488_; 
lean_dec_ref(v___y_485_);
lean_dec_ref(v___y_479_);
lean_dec_ref(v_e_382_);
v___x_487_ = lean_box(0);
v___x_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
return v___x_488_;
}
else
{
lean_object* v___x_489_; lean_object* v_maxFVar_490_; lean_object* v___x_491_; 
v___x_489_ = lean_st_ref_get(v___y_478_);
v_maxFVar_490_ = lean_ctor_get(v___x_489_, 1);
lean_inc_ref(v_maxFVar_490_);
lean_dec(v___x_489_);
v___x_491_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_490_, v_e_382_);
lean_dec_ref(v_maxFVar_490_);
if (lean_obj_tag(v___x_491_) == 1)
{
lean_object* v_val_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_499_; 
lean_dec_ref(v___y_485_);
lean_dec_ref(v___y_479_);
lean_dec_ref(v_e_382_);
v_val_492_ = lean_ctor_get(v___x_491_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_491_);
if (v_isSharedCheck_499_ == 0)
{
v___x_494_ = v___x_491_;
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_val_492_);
lean_dec(v___x_491_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_497_; 
if (v_isShared_495_ == 0)
{
lean_ctor_set_tag(v___x_494_, 0);
v___x_497_ = v___x_494_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_val_492_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
else
{
lean_object* v___x_500_; 
lean_dec(v___x_491_);
v___x_500_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v___y_485_, v___y_484_, v___y_478_, v___y_483_, v___y_480_, v___y_482_, v___y_481_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; lean_object* v___x_502_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_a_501_);
lean_dec_ref_known(v___x_500_, 1);
v___x_502_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v___y_479_, v___y_484_, v___y_478_, v___y_483_, v___y_480_, v___y_482_, v___y_481_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; lean_object* v___x_504_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_a_503_);
lean_dec_ref_known(v___x_502_, 1);
v___x_504_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_501_, v_a_503_, v___y_483_, v___y_482_, v___y_481_);
v___y_446_ = v___y_478_;
v___y_447_ = v___x_504_;
goto v___jp_445_;
}
else
{
lean_dec(v_a_501_);
v___y_446_ = v___y_478_;
v___y_447_ = v___x_502_;
goto v___jp_445_;
}
}
else
{
lean_dec_ref(v___y_479_);
v___y_446_ = v___y_478_;
v___y_447_ = v___x_500_;
goto v___jp_445_;
}
}
}
}
v___jp_505_:
{
uint8_t v___x_514_; 
v___x_514_ = l_Lean_Expr_hasFVar(v_e_382_);
if (v___x_514_ == 0)
{
uint8_t v___x_515_; 
v___x_515_ = l_Lean_Expr_hasMVar(v_e_382_);
v___y_478_ = v___y_509_;
v___y_479_ = v_b_507_;
v___y_480_ = v___y_511_;
v___y_481_ = v___y_513_;
v___y_482_ = v___y_512_;
v___y_483_ = v___y_510_;
v___y_484_ = v___y_508_;
v___y_485_ = v_d_506_;
v___y_486_ = v___x_515_;
goto v___jp_477_;
}
else
{
v___y_478_ = v___y_509_;
v___y_479_ = v_b_507_;
v___y_480_ = v___y_511_;
v___y_481_ = v___y_513_;
v___y_482_ = v___y_512_;
v___y_483_ = v___y_510_;
v___y_484_ = v___y_508_;
v___y_485_ = v_d_506_;
v___y_486_ = v___x_514_;
goto v___jp_477_;
}
}
v___jp_516_:
{
if (lean_obj_tag(v___y_517_) == 0)
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_546_; 
v_a_518_ = lean_ctor_get(v___y_517_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___y_517_);
if (v_isSharedCheck_546_ == 0)
{
v___x_520_ = v___y_517_;
v_isShared_521_ = v_isSharedCheck_546_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___y_517_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_546_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_522_; lean_object* v_share_523_; lean_object* v_maxFVar_524_; lean_object* v_proofInstInfo_525_; lean_object* v_inferType_526_; lean_object* v_getLevel_527_; lean_object* v_congrInfo_528_; lean_object* v_defEqI_529_; lean_object* v_extensions_530_; lean_object* v_issues_531_; lean_object* v_canon_532_; uint8_t v_debug_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_545_; 
v___x_522_ = lean_st_ref_take(v_a_384_);
v_share_523_ = lean_ctor_get(v___x_522_, 0);
v_maxFVar_524_ = lean_ctor_get(v___x_522_, 1);
v_proofInstInfo_525_ = lean_ctor_get(v___x_522_, 2);
v_inferType_526_ = lean_ctor_get(v___x_522_, 3);
v_getLevel_527_ = lean_ctor_get(v___x_522_, 4);
v_congrInfo_528_ = lean_ctor_get(v___x_522_, 5);
v_defEqI_529_ = lean_ctor_get(v___x_522_, 6);
v_extensions_530_ = lean_ctor_get(v___x_522_, 7);
v_issues_531_ = lean_ctor_get(v___x_522_, 8);
v_canon_532_ = lean_ctor_get(v___x_522_, 9);
v_debug_533_ = lean_ctor_get_uint8(v___x_522_, sizeof(void*)*10);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_545_ == 0)
{
v___x_535_ = v___x_522_;
v_isShared_536_ = v_isSharedCheck_545_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_canon_532_);
lean_inc(v_issues_531_);
lean_inc(v_extensions_530_);
lean_inc(v_defEqI_529_);
lean_inc(v_congrInfo_528_);
lean_inc(v_getLevel_527_);
lean_inc(v_inferType_526_);
lean_inc(v_proofInstInfo_525_);
lean_inc(v_maxFVar_524_);
lean_inc(v_share_523_);
lean_dec(v___x_522_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_545_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_537_; lean_object* v___x_539_; 
lean_inc(v_a_518_);
v___x_537_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_524_, v_e_382_, v_a_518_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 1, v___x_537_);
v___x_539_ = v___x_535_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_share_523_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v___x_537_);
lean_ctor_set(v_reuseFailAlloc_544_, 2, v_proofInstInfo_525_);
lean_ctor_set(v_reuseFailAlloc_544_, 3, v_inferType_526_);
lean_ctor_set(v_reuseFailAlloc_544_, 4, v_getLevel_527_);
lean_ctor_set(v_reuseFailAlloc_544_, 5, v_congrInfo_528_);
lean_ctor_set(v_reuseFailAlloc_544_, 6, v_defEqI_529_);
lean_ctor_set(v_reuseFailAlloc_544_, 7, v_extensions_530_);
lean_ctor_set(v_reuseFailAlloc_544_, 8, v_issues_531_);
lean_ctor_set(v_reuseFailAlloc_544_, 9, v_canon_532_);
lean_ctor_set_uint8(v_reuseFailAlloc_544_, sizeof(void*)*10, v_debug_533_);
v___x_539_ = v_reuseFailAlloc_544_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
lean_object* v___x_540_; lean_object* v___x_542_; 
v___x_540_ = lean_st_ref_set(v_a_384_, v___x_539_);
if (v_isShared_521_ == 0)
{
v___x_542_ = v___x_520_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_518_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_382_);
return v___y_517_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f___boxed(lean_object* v_e_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_e_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_);
lean_dec(v_a_756_);
lean_dec_ref(v_a_755_);
lean_dec(v_a_754_);
lean_dec_ref(v_a_753_);
lean_dec(v_a_752_);
lean_dec_ref(v_a_751_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0(lean_object* v_00_u03b2_759_, lean_object* v_x_760_, lean_object* v_x_761_, lean_object* v_x_762_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_x_760_, v_x_761_, v_x_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1(lean_object* v_00_u03b2_764_, lean_object* v_x_765_, lean_object* v_x_766_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_x_765_, v_x_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___boxed(lean_object* v_00_u03b2_768_, lean_object* v_x_769_, lean_object* v_x_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1(v_00_u03b2_768_, v_x_769_, v_x_770_);
lean_dec_ref(v_x_770_);
lean_dec_ref(v_x_769_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0(lean_object* v_00_u03b2_772_, lean_object* v_x_773_, size_t v_x_774_, size_t v_x_775_, lean_object* v_x_776_, lean_object* v_x_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_773_, v_x_774_, v_x_775_, v_x_776_, v_x_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_779_, lean_object* v_x_780_, lean_object* v_x_781_, lean_object* v_x_782_, lean_object* v_x_783_, lean_object* v_x_784_){
_start:
{
size_t v_x_6077__boxed_785_; size_t v_x_6078__boxed_786_; lean_object* v_res_787_; 
v_x_6077__boxed_785_ = lean_unbox_usize(v_x_781_);
lean_dec(v_x_781_);
v_x_6078__boxed_786_ = lean_unbox_usize(v_x_782_);
lean_dec(v_x_782_);
v_res_787_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0(v_00_u03b2_779_, v_x_780_, v_x_6077__boxed_785_, v_x_6078__boxed_786_, v_x_783_, v_x_784_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2(lean_object* v_00_u03b2_788_, lean_object* v_x_789_, size_t v_x_790_, lean_object* v_x_791_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_789_, v_x_790_, v_x_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_793_, lean_object* v_x_794_, lean_object* v_x_795_, lean_object* v_x_796_){
_start:
{
size_t v_x_6094__boxed_797_; lean_object* v_res_798_; 
v_x_6094__boxed_797_ = lean_unbox_usize(v_x_795_);
lean_dec(v_x_795_);
v_res_798_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2(v_00_u03b2_793_, v_x_794_, v_x_6094__boxed_797_, v_x_796_);
lean_dec_ref(v_x_796_);
lean_dec_ref(v_x_794_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_799_, lean_object* v_n_800_, lean_object* v_k_801_, lean_object* v_v_802_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(v_n_800_, v_k_801_, v_v_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_804_, size_t v_depth_805_, lean_object* v_keys_806_, lean_object* v_vals_807_, lean_object* v_heq_808_, lean_object* v_i_809_, lean_object* v_entries_810_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(v_depth_805_, v_keys_806_, v_vals_807_, v_i_809_, v_entries_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_812_, lean_object* v_depth_813_, lean_object* v_keys_814_, lean_object* v_vals_815_, lean_object* v_heq_816_, lean_object* v_i_817_, lean_object* v_entries_818_){
_start:
{
size_t v_depth_boxed_819_; lean_object* v_res_820_; 
v_depth_boxed_819_ = lean_unbox_usize(v_depth_813_);
lean_dec(v_depth_813_);
v_res_820_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3(v_00_u03b2_812_, v_depth_boxed_819_, v_keys_814_, v_vals_815_, v_heq_816_, v_i_817_, v_entries_818_);
lean_dec_ref(v_vals_815_);
lean_dec_ref(v_keys_814_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_821_, lean_object* v_keys_822_, lean_object* v_vals_823_, lean_object* v_heq_824_, lean_object* v_i_825_, lean_object* v_k_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_keys_822_, v_vals_823_, v_i_825_, v_k_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_828_, lean_object* v_keys_829_, lean_object* v_vals_830_, lean_object* v_heq_831_, lean_object* v_i_832_, lean_object* v_k_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6(v_00_u03b2_828_, v_keys_829_, v_vals_830_, v_heq_831_, v_i_832_, v_k_833_);
lean_dec_ref(v_k_833_);
lean_dec_ref(v_vals_830_);
lean_dec_ref(v_keys_829_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_835_, lean_object* v_x_836_, lean_object* v_x_837_, lean_object* v_x_838_, lean_object* v_x_839_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_x_836_, v_x_837_, v_x_838_, v_x_839_);
return v___x_840_;
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
