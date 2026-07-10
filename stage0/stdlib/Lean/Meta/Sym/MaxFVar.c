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
lean_object* v___x_156_; lean_object* v___x_4730__overap_157_; lean_object* v___x_158_; 
v___x_156_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0, &l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0);
v___x_4730__overap_157_ = lean_panic_fn_borrowed(v___x_156_, v_msg_148_);
lean_inc(v___y_154_);
lean_inc_ref(v___y_153_);
lean_inc(v___y_152_);
lean_inc_ref(v___y_151_);
lean_inc(v___y_150_);
lean_inc_ref(v___y_149_);
v___x_158_ = lean_apply_7(v___x_4730__overap_157_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, lean_box(0));
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
lean_object* v_ks_172_; lean_object* v_vs_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_197_; 
v_ks_172_ = lean_ctor_get(v_x_168_, 0);
v_vs_173_ = lean_ctor_get(v_x_168_, 1);
v_isSharedCheck_197_ = !lean_is_exclusive(v_x_168_);
if (v_isSharedCheck_197_ == 0)
{
v___x_175_ = v_x_168_;
v_isShared_176_ = v_isSharedCheck_197_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_vs_173_);
lean_inc(v_ks_172_);
lean_dec(v_x_168_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_197_;
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
lean_object* v_k_x27_184_; uint8_t v___x_185_; 
v_k_x27_184_ = lean_array_fget_borrowed(v_ks_172_, v_x_169_);
v___x_185_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_170_, v_k_x27_184_);
if (v___x_185_ == 0)
{
lean_object* v___x_187_; 
if (v_isShared_176_ == 0)
{
v___x_187_ = v___x_175_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_ks_172_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_vs_173_);
v___x_187_ = v_reuseFailAlloc_191_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = lean_unsigned_to_nat(1u);
v___x_189_ = lean_nat_add(v_x_169_, v___x_188_);
lean_dec(v_x_169_);
v_x_168_ = v___x_187_;
v_x_169_ = v___x_189_;
goto _start;
}
}
else
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_195_; 
v___x_192_ = lean_array_fset(v_ks_172_, v_x_169_, v_x_170_);
v___x_193_ = lean_array_fset(v_vs_173_, v_x_169_, v_x_171_);
lean_dec(v_x_169_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 1, v___x_193_);
lean_ctor_set(v___x_175_, 0, v___x_192_);
v___x_195_ = v___x_175_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___x_192_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v___x_193_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(lean_object* v_n_198_, lean_object* v_k_199_, lean_object* v_v_200_){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = lean_unsigned_to_nat(0u);
v___x_202_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_n_198_, v___x_201_, v_k_199_, v_v_200_);
return v___x_202_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(lean_object* v_x_204_, size_t v_x_205_, size_t v_x_206_, lean_object* v_x_207_, lean_object* v_x_208_){
_start:
{
if (lean_obj_tag(v_x_204_) == 0)
{
lean_object* v_es_209_; size_t v___x_210_; size_t v___x_211_; lean_object* v_j_212_; lean_object* v___x_213_; uint8_t v___x_214_; 
v_es_209_ = lean_ctor_get(v_x_204_, 0);
v___x_210_ = ((size_t)31ULL);
v___x_211_ = lean_usize_land(v_x_205_, v___x_210_);
v_j_212_ = lean_usize_to_nat(v___x_211_);
v___x_213_ = lean_array_get_size(v_es_209_);
v___x_214_ = lean_nat_dec_lt(v_j_212_, v___x_213_);
if (v___x_214_ == 0)
{
lean_dec(v_j_212_);
lean_dec(v_x_208_);
lean_dec_ref(v_x_207_);
return v_x_204_;
}
else
{
lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_253_; 
lean_inc_ref(v_es_209_);
v_isSharedCheck_253_ = !lean_is_exclusive(v_x_204_);
if (v_isSharedCheck_253_ == 0)
{
lean_object* v_unused_254_; 
v_unused_254_ = lean_ctor_get(v_x_204_, 0);
lean_dec(v_unused_254_);
v___x_216_ = v_x_204_;
v_isShared_217_ = v_isSharedCheck_253_;
goto v_resetjp_215_;
}
else
{
lean_dec(v_x_204_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_253_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v_v_218_; lean_object* v___x_219_; lean_object* v_xs_x27_220_; lean_object* v___y_222_; 
v_v_218_ = lean_array_fget(v_es_209_, v_j_212_);
v___x_219_ = lean_box(0);
v_xs_x27_220_ = lean_array_fset(v_es_209_, v_j_212_, v___x_219_);
switch(lean_obj_tag(v_v_218_))
{
case 0:
{
lean_object* v_key_227_; lean_object* v_val_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_238_; 
v_key_227_ = lean_ctor_get(v_v_218_, 0);
v_val_228_ = lean_ctor_get(v_v_218_, 1);
v_isSharedCheck_238_ = !lean_is_exclusive(v_v_218_);
if (v_isSharedCheck_238_ == 0)
{
v___x_230_ = v_v_218_;
v_isShared_231_ = v_isSharedCheck_238_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_val_228_);
lean_inc(v_key_227_);
lean_dec(v_v_218_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_238_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
uint8_t v___x_232_; 
v___x_232_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_207_, v_key_227_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; lean_object* v___x_234_; 
lean_del_object(v___x_230_);
v___x_233_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_227_, v_val_228_, v_x_207_, v_x_208_);
v___x_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
v___y_222_ = v___x_234_;
goto v___jp_221_;
}
else
{
lean_object* v___x_236_; 
lean_dec(v_val_228_);
lean_dec(v_key_227_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 1, v_x_208_);
lean_ctor_set(v___x_230_, 0, v_x_207_);
v___x_236_ = v___x_230_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_x_207_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v_x_208_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
v___y_222_ = v___x_236_;
goto v___jp_221_;
}
}
}
}
case 1:
{
lean_object* v_node_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_251_; 
v_node_239_ = lean_ctor_get(v_v_218_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v_v_218_);
if (v_isSharedCheck_251_ == 0)
{
v___x_241_ = v_v_218_;
v_isShared_242_ = v_isSharedCheck_251_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_node_239_);
lean_dec(v_v_218_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_251_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
size_t v___x_243_; size_t v___x_244_; size_t v___x_245_; size_t v___x_246_; lean_object* v___x_247_; lean_object* v___x_249_; 
v___x_243_ = ((size_t)5ULL);
v___x_244_ = lean_usize_shift_right(v_x_205_, v___x_243_);
v___x_245_ = ((size_t)1ULL);
v___x_246_ = lean_usize_add(v_x_206_, v___x_245_);
v___x_247_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_node_239_, v___x_244_, v___x_246_, v_x_207_, v_x_208_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 0, v___x_247_);
v___x_249_ = v___x_241_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_247_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
v___y_222_ = v___x_249_;
goto v___jp_221_;
}
}
}
default: 
{
lean_object* v___x_252_; 
v___x_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_252_, 0, v_x_207_);
lean_ctor_set(v___x_252_, 1, v_x_208_);
v___y_222_ = v___x_252_;
goto v___jp_221_;
}
}
v___jp_221_:
{
lean_object* v___x_223_; lean_object* v___x_225_; 
v___x_223_ = lean_array_fset(v_xs_x27_220_, v_j_212_, v___y_222_);
lean_dec(v_j_212_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 0, v___x_223_);
v___x_225_ = v___x_216_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_223_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
}
else
{
lean_object* v_ks_255_; lean_object* v_vs_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_276_; 
v_ks_255_ = lean_ctor_get(v_x_204_, 0);
v_vs_256_ = lean_ctor_get(v_x_204_, 1);
v_isSharedCheck_276_ = !lean_is_exclusive(v_x_204_);
if (v_isSharedCheck_276_ == 0)
{
v___x_258_ = v_x_204_;
v_isShared_259_ = v_isSharedCheck_276_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_vs_256_);
lean_inc(v_ks_255_);
lean_dec(v_x_204_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_276_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_261_; 
if (v_isShared_259_ == 0)
{
v___x_261_ = v___x_258_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_ks_255_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v_vs_256_);
v___x_261_ = v_reuseFailAlloc_275_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
lean_object* v_newNode_262_; uint8_t v___y_264_; size_t v___x_270_; uint8_t v___x_271_; 
v_newNode_262_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(v___x_261_, v_x_207_, v_x_208_);
v___x_270_ = ((size_t)7ULL);
v___x_271_ = lean_usize_dec_le(v___x_270_, v_x_206_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; lean_object* v___x_273_; uint8_t v___x_274_; 
v___x_272_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_262_);
v___x_273_ = lean_unsigned_to_nat(4u);
v___x_274_ = lean_nat_dec_lt(v___x_272_, v___x_273_);
lean_dec(v___x_272_);
v___y_264_ = v___x_274_;
goto v___jp_263_;
}
else
{
v___y_264_ = v___x_271_;
goto v___jp_263_;
}
v___jp_263_:
{
if (v___y_264_ == 0)
{
lean_object* v_ks_265_; lean_object* v_vs_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v_ks_265_ = lean_ctor_get(v_newNode_262_, 0);
lean_inc_ref(v_ks_265_);
v_vs_266_ = lean_ctor_get(v_newNode_262_, 1);
lean_inc_ref(v_vs_266_);
lean_dec_ref(v_newNode_262_);
v___x_267_ = lean_unsigned_to_nat(0u);
v___x_268_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0);
v___x_269_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(v_x_206_, v_ks_265_, v_vs_266_, v___x_267_, v___x_268_);
lean_dec_ref(v_vs_266_);
lean_dec_ref(v_ks_265_);
return v___x_269_;
}
else
{
return v_newNode_262_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(size_t v_depth_277_, lean_object* v_keys_278_, lean_object* v_vals_279_, lean_object* v_i_280_, lean_object* v_entries_281_){
_start:
{
lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_282_ = lean_array_get_size(v_keys_278_);
v___x_283_ = lean_nat_dec_lt(v_i_280_, v___x_282_);
if (v___x_283_ == 0)
{
lean_dec(v_i_280_);
return v_entries_281_;
}
else
{
lean_object* v_k_284_; lean_object* v_v_285_; uint64_t v___x_286_; size_t v_h_287_; size_t v___x_288_; lean_object* v___x_289_; size_t v___x_290_; size_t v___x_291_; size_t v___x_292_; size_t v_h_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v_k_284_ = lean_array_fget_borrowed(v_keys_278_, v_i_280_);
v_v_285_ = lean_array_fget_borrowed(v_vals_279_, v_i_280_);
v___x_286_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_284_);
v_h_287_ = lean_uint64_to_usize(v___x_286_);
v___x_288_ = ((size_t)5ULL);
v___x_289_ = lean_unsigned_to_nat(1u);
v___x_290_ = ((size_t)1ULL);
v___x_291_ = lean_usize_sub(v_depth_277_, v___x_290_);
v___x_292_ = lean_usize_mul(v___x_288_, v___x_291_);
v_h_293_ = lean_usize_shift_right(v_h_287_, v___x_292_);
v___x_294_ = lean_nat_add(v_i_280_, v___x_289_);
lean_dec(v_i_280_);
lean_inc(v_v_285_);
lean_inc(v_k_284_);
v___x_295_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_entries_281_, v_h_293_, v_depth_277_, v_k_284_, v_v_285_);
v_i_280_ = v___x_294_;
v_entries_281_ = v___x_295_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_297_, lean_object* v_keys_298_, lean_object* v_vals_299_, lean_object* v_i_300_, lean_object* v_entries_301_){
_start:
{
size_t v_depth_boxed_302_; lean_object* v_res_303_; 
v_depth_boxed_302_ = lean_unbox_usize(v_depth_297_);
lean_dec(v_depth_297_);
v_res_303_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(v_depth_boxed_302_, v_keys_298_, v_vals_299_, v_i_300_, v_entries_301_);
lean_dec_ref(v_vals_299_);
lean_dec_ref(v_keys_298_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_304_, lean_object* v_x_305_, lean_object* v_x_306_, lean_object* v_x_307_, lean_object* v_x_308_){
_start:
{
size_t v_x_5205__boxed_309_; size_t v_x_5206__boxed_310_; lean_object* v_res_311_; 
v_x_5205__boxed_309_ = lean_unbox_usize(v_x_305_);
lean_dec(v_x_305_);
v_x_5206__boxed_310_ = lean_unbox_usize(v_x_306_);
lean_dec(v_x_306_);
v_res_311_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_304_, v_x_5205__boxed_309_, v_x_5206__boxed_310_, v_x_307_, v_x_308_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(lean_object* v_x_312_, lean_object* v_x_313_, lean_object* v_x_314_){
_start:
{
uint64_t v___x_315_; size_t v___x_316_; size_t v___x_317_; lean_object* v___x_318_; 
v___x_315_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_313_);
v___x_316_ = lean_uint64_to_usize(v___x_315_);
v___x_317_ = ((size_t)1ULL);
v___x_318_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_312_, v___x_316_, v___x_317_, v_x_313_, v_x_314_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(lean_object* v_keys_319_, lean_object* v_vals_320_, lean_object* v_i_321_, lean_object* v_k_322_){
_start:
{
lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_323_ = lean_array_get_size(v_keys_319_);
v___x_324_ = lean_nat_dec_lt(v_i_321_, v___x_323_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; 
lean_dec(v_i_321_);
v___x_325_ = lean_box(0);
return v___x_325_;
}
else
{
lean_object* v_k_x27_326_; uint8_t v___x_327_; 
v_k_x27_326_ = lean_array_fget_borrowed(v_keys_319_, v_i_321_);
v___x_327_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_322_, v_k_x27_326_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = lean_unsigned_to_nat(1u);
v___x_329_ = lean_nat_add(v_i_321_, v___x_328_);
lean_dec(v_i_321_);
v_i_321_ = v___x_329_;
goto _start;
}
else
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = lean_array_fget_borrowed(v_vals_320_, v_i_321_);
lean_dec(v_i_321_);
lean_inc(v___x_331_);
v___x_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
return v___x_332_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_keys_333_, lean_object* v_vals_334_, lean_object* v_i_335_, lean_object* v_k_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_keys_333_, v_vals_334_, v_i_335_, v_k_336_);
lean_dec_ref(v_k_336_);
lean_dec_ref(v_vals_334_);
lean_dec_ref(v_keys_333_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(lean_object* v_x_338_, size_t v_x_339_, lean_object* v_x_340_){
_start:
{
if (lean_obj_tag(v_x_338_) == 0)
{
lean_object* v_es_341_; lean_object* v___x_342_; size_t v___x_343_; size_t v___x_344_; lean_object* v_j_345_; lean_object* v___x_346_; 
v_es_341_ = lean_ctor_get(v_x_338_, 0);
v___x_342_ = lean_box(2);
v___x_343_ = ((size_t)31ULL);
v___x_344_ = lean_usize_land(v_x_339_, v___x_343_);
v_j_345_ = lean_usize_to_nat(v___x_344_);
v___x_346_ = lean_array_get_borrowed(v___x_342_, v_es_341_, v_j_345_);
lean_dec(v_j_345_);
switch(lean_obj_tag(v___x_346_))
{
case 0:
{
lean_object* v_key_347_; lean_object* v_val_348_; uint8_t v___x_349_; 
v_key_347_ = lean_ctor_get(v___x_346_, 0);
v_val_348_ = lean_ctor_get(v___x_346_, 1);
v___x_349_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_340_, v_key_347_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; 
v___x_350_ = lean_box(0);
return v___x_350_;
}
else
{
lean_object* v___x_351_; 
lean_inc(v_val_348_);
v___x_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_351_, 0, v_val_348_);
return v___x_351_;
}
}
case 1:
{
lean_object* v_node_352_; size_t v___x_353_; size_t v___x_354_; 
v_node_352_ = lean_ctor_get(v___x_346_, 0);
v___x_353_ = ((size_t)5ULL);
v___x_354_ = lean_usize_shift_right(v_x_339_, v___x_353_);
v_x_338_ = v_node_352_;
v_x_339_ = v___x_354_;
goto _start;
}
default: 
{
lean_object* v___x_356_; 
v___x_356_ = lean_box(0);
return v___x_356_;
}
}
}
else
{
lean_object* v_ks_357_; lean_object* v_vs_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v_ks_357_ = lean_ctor_get(v_x_338_, 0);
v_vs_358_ = lean_ctor_get(v_x_338_, 1);
v___x_359_ = lean_unsigned_to_nat(0u);
v___x_360_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_ks_357_, v_vs_358_, v___x_359_, v_x_340_);
return v___x_360_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_x_361_, lean_object* v_x_362_, lean_object* v_x_363_){
_start:
{
size_t v_x_5393__boxed_364_; lean_object* v_res_365_; 
v_x_5393__boxed_364_ = lean_unbox_usize(v_x_362_);
lean_dec(v_x_362_);
v_res_365_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_361_, v_x_5393__boxed_364_, v_x_363_);
lean_dec_ref(v_x_363_);
lean_dec_ref(v_x_361_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(lean_object* v_x_366_, lean_object* v_x_367_){
_start:
{
uint64_t v___x_368_; size_t v___x_369_; lean_object* v___x_370_; 
v___x_368_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_367_);
v___x_369_ = lean_uint64_to_usize(v___x_368_);
v___x_370_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_366_, v___x_369_, v_x_367_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg___boxed(lean_object* v_x_371_, lean_object* v_x_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_x_371_, v_x_372_);
lean_dec_ref(v_x_372_);
lean_dec_ref(v_x_371_);
return v_res_373_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_377_ = ((lean_object*)(l_Lean_Meta_Sym_getMaxFVar_x3f___closed__2));
v___x_378_ = lean_unsigned_to_nat(37u);
v___x_379_ = lean_unsigned_to_nat(52u);
v___x_380_ = ((lean_object*)(l_Lean_Meta_Sym_getMaxFVar_x3f___closed__1));
v___x_381_ = ((lean_object*)(l_Lean_Meta_Sym_getMaxFVar_x3f___closed__0));
v___x_382_ = l_mkPanicMessageWithDecl(v___x_381_, v___x_380_, v___x_379_, v___x_378_, v___x_377_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f(lean_object* v_e_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_){
_start:
{
lean_object* v___y_392_; lean_object* v_a_424_; lean_object* v___y_449_; lean_object* v___y_450_; lean_object* v___y_482_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v___y_485_; lean_object* v___y_486_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v___y_489_; uint8_t v___y_490_; lean_object* v_d_510_; lean_object* v_b_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_521_; 
switch(lean_obj_tag(v_e_383_))
{
case 1:
{
lean_object* v_fvarId_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v_fvarId_552_ = lean_ctor_get(v_e_383_, 0);
lean_inc(v_fvarId_552_);
lean_dec_ref_known(v_e_383_, 1);
v___x_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_553_, 0, v_fvarId_552_);
v___x_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
return v___x_554_;
}
case 2:
{
lean_object* v_mvarId_555_; uint8_t v___y_557_; uint8_t v___x_598_; 
v_mvarId_555_ = lean_ctor_get(v_e_383_, 0);
v___x_598_ = l_Lean_Expr_hasFVar(v_e_383_);
if (v___x_598_ == 0)
{
uint8_t v___x_599_; 
v___x_599_ = l_Lean_Expr_hasMVar(v_e_383_);
v___y_557_ = v___x_599_;
goto v___jp_556_;
}
else
{
v___y_557_ = v___x_598_;
goto v___jp_556_;
}
v___jp_556_:
{
if (v___y_557_ == 0)
{
lean_object* v___x_558_; lean_object* v___x_559_; 
lean_dec_ref_known(v_e_383_, 1);
v___x_558_ = lean_box(0);
v___x_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
return v___x_559_;
}
else
{
lean_object* v___x_560_; lean_object* v_maxFVar_561_; lean_object* v___x_562_; 
v___x_560_ = lean_st_ref_get(v_a_385_);
v_maxFVar_561_ = lean_ctor_get(v___x_560_, 1);
lean_inc_ref(v_maxFVar_561_);
lean_dec(v___x_560_);
v___x_562_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_561_, v_e_383_);
lean_dec_ref(v_maxFVar_561_);
if (lean_obj_tag(v___x_562_) == 1)
{
lean_object* v_val_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
lean_dec_ref_known(v_e_383_, 1);
v_val_563_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_570_ == 0)
{
v___x_565_ = v___x_562_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_val_563_);
lean_dec(v___x_562_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
lean_ctor_set_tag(v___x_565_, 0);
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_val_563_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
else
{
lean_object* v___x_571_; 
lean_dec(v___x_562_);
lean_inc(v_mvarId_555_);
v___x_571_ = l_Lean_MVarId_getDecl(v_mvarId_555_, v_a_386_, v_a_387_, v_a_388_, v_a_389_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v_a_572_; lean_object* v_lctx_573_; lean_object* v_decls_574_; uint8_t v___x_575_; 
v_a_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_a_572_);
lean_dec_ref_known(v___x_571_, 1);
v_lctx_573_ = lean_ctor_get(v_a_572_, 1);
lean_inc_ref(v_lctx_573_);
lean_dec(v_a_572_);
v_decls_574_ = lean_ctor_get(v_lctx_573_, 1);
v___x_575_ = l_Lean_PersistentArray_isEmpty___redArg(v_decls_574_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; 
v___x_576_ = l_Lean_LocalContext_lastDecl(v_lctx_573_);
lean_dec_ref(v_lctx_573_);
if (lean_obj_tag(v___x_576_) == 1)
{
lean_object* v_val_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_585_; 
v_val_577_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_585_ == 0)
{
v___x_579_ = v___x_576_;
v_isShared_580_ = v_isSharedCheck_585_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_val_577_);
lean_dec(v___x_576_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_585_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_581_; lean_object* v___x_583_; 
v___x_581_ = l_Lean_LocalDecl_fvarId(v_val_577_);
lean_dec(v_val_577_);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 0, v___x_581_);
v___x_583_ = v___x_579_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_581_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
v_a_424_ = v___x_583_;
goto v___jp_423_;
}
}
}
else
{
lean_object* v___x_586_; lean_object* v___x_587_; 
lean_dec(v___x_576_);
v___x_586_ = lean_obj_once(&l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3, &l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3_once, _init_l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3);
v___x_587_ = l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2(v___x_586_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_a_588_);
lean_dec_ref_known(v___x_587_, 1);
v_a_424_ = v_a_588_;
goto v___jp_423_;
}
else
{
lean_dec_ref_known(v_e_383_, 1);
return v___x_587_;
}
}
}
else
{
lean_object* v___x_589_; 
lean_dec_ref(v_lctx_573_);
v___x_589_ = lean_box(0);
v_a_424_ = v___x_589_;
goto v___jp_423_;
}
}
else
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
lean_dec_ref_known(v_e_383_, 1);
v_a_590_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v___x_571_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_571_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_590_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
}
}
}
case 5:
{
lean_object* v_fn_600_; lean_object* v_arg_601_; uint8_t v___y_603_; uint8_t v___x_622_; 
v_fn_600_ = lean_ctor_get(v_e_383_, 0);
v_arg_601_ = lean_ctor_get(v_e_383_, 1);
v___x_622_ = l_Lean_Expr_hasFVar(v_e_383_);
if (v___x_622_ == 0)
{
uint8_t v___x_623_; 
v___x_623_ = l_Lean_Expr_hasMVar(v_e_383_);
v___y_603_ = v___x_623_;
goto v___jp_602_;
}
else
{
v___y_603_ = v___x_622_;
goto v___jp_602_;
}
v___jp_602_:
{
if (v___y_603_ == 0)
{
lean_object* v___x_604_; lean_object* v___x_605_; 
lean_dec_ref_known(v_e_383_, 2);
v___x_604_ = lean_box(0);
v___x_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
return v___x_605_;
}
else
{
lean_object* v___x_606_; lean_object* v_maxFVar_607_; lean_object* v___x_608_; 
v___x_606_ = lean_st_ref_get(v_a_385_);
v_maxFVar_607_ = lean_ctor_get(v___x_606_, 1);
lean_inc_ref(v_maxFVar_607_);
lean_dec(v___x_606_);
v___x_608_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_607_, v_e_383_);
lean_dec_ref(v_maxFVar_607_);
if (lean_obj_tag(v___x_608_) == 1)
{
lean_object* v_val_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
lean_dec_ref_known(v_e_383_, 2);
v_val_609_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_616_ == 0)
{
v___x_611_ = v___x_608_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_val_609_);
lean_dec(v___x_608_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
lean_ctor_set_tag(v___x_611_, 0);
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_val_609_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
else
{
lean_object* v___x_617_; 
lean_dec(v___x_608_);
lean_inc_ref(v_fn_600_);
v___x_617_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_fn_600_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_a_618_; lean_object* v___x_619_; 
v_a_618_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_a_618_);
lean_dec_ref_known(v___x_617_, 1);
lean_inc_ref(v_arg_601_);
v___x_619_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_arg_601_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_object* v_a_620_; lean_object* v___x_621_; 
v_a_620_ = lean_ctor_get(v___x_619_, 0);
lean_inc(v_a_620_);
lean_dec_ref_known(v___x_619_, 1);
v___x_621_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_618_, v_a_620_, v_a_386_, v_a_388_, v_a_389_);
v___y_521_ = v___x_621_;
goto v___jp_520_;
}
else
{
lean_dec(v_a_618_);
v___y_521_ = v___x_619_;
goto v___jp_520_;
}
}
else
{
v___y_521_ = v___x_617_;
goto v___jp_520_;
}
}
}
}
}
case 6:
{
lean_object* v_binderType_624_; lean_object* v_body_625_; 
v_binderType_624_ = lean_ctor_get(v_e_383_, 1);
v_body_625_ = lean_ctor_get(v_e_383_, 2);
lean_inc_ref(v_body_625_);
lean_inc_ref(v_binderType_624_);
v_d_510_ = v_binderType_624_;
v_b_511_ = v_body_625_;
v___y_512_ = v_a_384_;
v___y_513_ = v_a_385_;
v___y_514_ = v_a_386_;
v___y_515_ = v_a_387_;
v___y_516_ = v_a_388_;
v___y_517_ = v_a_389_;
goto v___jp_509_;
}
case 7:
{
lean_object* v_binderType_626_; lean_object* v_body_627_; 
v_binderType_626_ = lean_ctor_get(v_e_383_, 1);
v_body_627_ = lean_ctor_get(v_e_383_, 2);
lean_inc_ref(v_body_627_);
lean_inc_ref(v_binderType_626_);
v_d_510_ = v_binderType_626_;
v_b_511_ = v_body_627_;
v___y_512_ = v_a_384_;
v___y_513_ = v_a_385_;
v___y_514_ = v_a_386_;
v___y_515_ = v_a_387_;
v___y_516_ = v_a_388_;
v___y_517_ = v_a_389_;
goto v___jp_509_;
}
case 8:
{
lean_object* v_type_628_; lean_object* v_value_629_; lean_object* v_body_630_; uint8_t v___y_632_; uint8_t v___x_655_; 
v_type_628_ = lean_ctor_get(v_e_383_, 1);
v_value_629_ = lean_ctor_get(v_e_383_, 2);
v_body_630_ = lean_ctor_get(v_e_383_, 3);
v___x_655_ = l_Lean_Expr_hasFVar(v_e_383_);
if (v___x_655_ == 0)
{
uint8_t v___x_656_; 
v___x_656_ = l_Lean_Expr_hasMVar(v_e_383_);
v___y_632_ = v___x_656_;
goto v___jp_631_;
}
else
{
v___y_632_ = v___x_655_;
goto v___jp_631_;
}
v___jp_631_:
{
if (v___y_632_ == 0)
{
lean_object* v___x_633_; lean_object* v___x_634_; 
lean_dec_ref_known(v_e_383_, 4);
v___x_633_ = lean_box(0);
v___x_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
return v___x_634_;
}
else
{
lean_object* v___x_635_; lean_object* v_maxFVar_636_; lean_object* v___x_637_; 
v___x_635_ = lean_st_ref_get(v_a_385_);
v_maxFVar_636_ = lean_ctor_get(v___x_635_, 1);
lean_inc_ref(v_maxFVar_636_);
lean_dec(v___x_635_);
v___x_637_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_636_, v_e_383_);
lean_dec_ref(v_maxFVar_636_);
if (lean_obj_tag(v___x_637_) == 1)
{
lean_object* v_val_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_645_; 
lean_dec_ref_known(v_e_383_, 4);
v_val_638_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_645_ == 0)
{
v___x_640_ = v___x_637_;
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_val_638_);
lean_dec(v___x_637_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_643_; 
if (v_isShared_641_ == 0)
{
lean_ctor_set_tag(v___x_640_, 0);
v___x_643_ = v___x_640_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_val_638_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
else
{
lean_object* v___x_646_; 
lean_dec(v___x_637_);
lean_inc_ref(v_type_628_);
v___x_646_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_type_628_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; lean_object* v___x_648_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_a_647_);
lean_dec_ref_known(v___x_646_, 1);
lean_inc_ref(v_value_629_);
v___x_648_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_value_629_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v_a_649_; lean_object* v___x_650_; 
v_a_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_a_649_);
lean_dec_ref_known(v___x_648_, 1);
v___x_650_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_647_, v_a_649_, v_a_386_, v_a_388_, v_a_389_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; lean_object* v___x_652_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_a_651_);
lean_dec_ref_known(v___x_650_, 1);
lean_inc_ref(v_body_630_);
v___x_652_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_body_630_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v___x_654_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_a_653_);
lean_dec_ref_known(v___x_652_, 1);
v___x_654_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_651_, v_a_653_, v_a_386_, v_a_388_, v_a_389_);
v___y_392_ = v___x_654_;
goto v___jp_391_;
}
else
{
lean_dec(v_a_651_);
v___y_392_ = v___x_652_;
goto v___jp_391_;
}
}
else
{
v___y_392_ = v___x_650_;
goto v___jp_391_;
}
}
else
{
lean_dec(v_a_647_);
v___y_392_ = v___x_648_;
goto v___jp_391_;
}
}
else
{
v___y_392_ = v___x_646_;
goto v___jp_391_;
}
}
}
}
}
case 10:
{
lean_object* v_expr_657_; uint8_t v___y_659_; uint8_t v___x_704_; 
v_expr_657_ = lean_ctor_get(v_e_383_, 1);
lean_inc_ref(v_expr_657_);
lean_dec_ref_known(v_e_383_, 2);
v___x_704_ = l_Lean_Expr_hasFVar(v_expr_657_);
if (v___x_704_ == 0)
{
uint8_t v___x_705_; 
v___x_705_ = l_Lean_Expr_hasMVar(v_expr_657_);
v___y_659_ = v___x_705_;
goto v___jp_658_;
}
else
{
v___y_659_ = v___x_704_;
goto v___jp_658_;
}
v___jp_658_:
{
if (v___y_659_ == 0)
{
lean_object* v___x_660_; lean_object* v___x_661_; 
lean_dec_ref(v_expr_657_);
v___x_660_ = lean_box(0);
v___x_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
return v___x_661_;
}
else
{
lean_object* v___x_662_; lean_object* v_maxFVar_663_; lean_object* v___x_664_; 
v___x_662_ = lean_st_ref_get(v_a_385_);
v_maxFVar_663_ = lean_ctor_get(v___x_662_, 1);
lean_inc_ref(v_maxFVar_663_);
lean_dec(v___x_662_);
v___x_664_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_663_, v_expr_657_);
lean_dec_ref(v_maxFVar_663_);
if (lean_obj_tag(v___x_664_) == 1)
{
lean_object* v_val_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
lean_dec_ref(v_expr_657_);
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
lean_inc_ref(v_expr_657_);
v___x_673_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_expr_657_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_703_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_703_ == 0)
{
v___x_676_ = v___x_673_;
v_isShared_677_ = v_isSharedCheck_703_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_673_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_703_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_678_; lean_object* v_share_679_; lean_object* v_maxFVar_680_; lean_object* v_proofInstInfo_681_; lean_object* v_inferType_682_; lean_object* v_getLevel_683_; lean_object* v_congrInfo_684_; lean_object* v_defEqI_685_; lean_object* v_extensions_686_; lean_object* v_issues_687_; lean_object* v_canon_688_; lean_object* v_instanceOverrides_689_; uint8_t v_debug_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_702_; 
v___x_678_ = lean_st_ref_take(v_a_385_);
v_share_679_ = lean_ctor_get(v___x_678_, 0);
v_maxFVar_680_ = lean_ctor_get(v___x_678_, 1);
v_proofInstInfo_681_ = lean_ctor_get(v___x_678_, 2);
v_inferType_682_ = lean_ctor_get(v___x_678_, 3);
v_getLevel_683_ = lean_ctor_get(v___x_678_, 4);
v_congrInfo_684_ = lean_ctor_get(v___x_678_, 5);
v_defEqI_685_ = lean_ctor_get(v___x_678_, 6);
v_extensions_686_ = lean_ctor_get(v___x_678_, 7);
v_issues_687_ = lean_ctor_get(v___x_678_, 8);
v_canon_688_ = lean_ctor_get(v___x_678_, 9);
v_instanceOverrides_689_ = lean_ctor_get(v___x_678_, 10);
v_debug_690_ = lean_ctor_get_uint8(v___x_678_, sizeof(void*)*11);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_702_ == 0)
{
v___x_692_ = v___x_678_;
v_isShared_693_ = v_isSharedCheck_702_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_instanceOverrides_689_);
lean_inc(v_canon_688_);
lean_inc(v_issues_687_);
lean_inc(v_extensions_686_);
lean_inc(v_defEqI_685_);
lean_inc(v_congrInfo_684_);
lean_inc(v_getLevel_683_);
lean_inc(v_inferType_682_);
lean_inc(v_proofInstInfo_681_);
lean_inc(v_maxFVar_680_);
lean_inc(v_share_679_);
lean_dec(v___x_678_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_702_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_694_; lean_object* v___x_696_; 
lean_inc(v_a_674_);
v___x_694_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_680_, v_expr_657_, v_a_674_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 1, v___x_694_);
v___x_696_ = v___x_692_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_share_679_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v___x_694_);
lean_ctor_set(v_reuseFailAlloc_701_, 2, v_proofInstInfo_681_);
lean_ctor_set(v_reuseFailAlloc_701_, 3, v_inferType_682_);
lean_ctor_set(v_reuseFailAlloc_701_, 4, v_getLevel_683_);
lean_ctor_set(v_reuseFailAlloc_701_, 5, v_congrInfo_684_);
lean_ctor_set(v_reuseFailAlloc_701_, 6, v_defEqI_685_);
lean_ctor_set(v_reuseFailAlloc_701_, 7, v_extensions_686_);
lean_ctor_set(v_reuseFailAlloc_701_, 8, v_issues_687_);
lean_ctor_set(v_reuseFailAlloc_701_, 9, v_canon_688_);
lean_ctor_set(v_reuseFailAlloc_701_, 10, v_instanceOverrides_689_);
lean_ctor_set_uint8(v_reuseFailAlloc_701_, sizeof(void*)*11, v_debug_690_);
v___x_696_ = v_reuseFailAlloc_701_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_697_ = lean_st_ref_set(v_a_385_, v___x_696_);
if (v_isShared_677_ == 0)
{
v___x_699_ = v___x_676_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_674_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
}
else
{
lean_dec_ref(v_expr_657_);
return v___x_673_;
}
}
}
}
}
case 11:
{
lean_object* v_struct_706_; uint8_t v___y_708_; uint8_t v___x_753_; 
v_struct_706_ = lean_ctor_get(v_e_383_, 2);
v___x_753_ = l_Lean_Expr_hasFVar(v_e_383_);
if (v___x_753_ == 0)
{
uint8_t v___x_754_; 
v___x_754_ = l_Lean_Expr_hasMVar(v_e_383_);
v___y_708_ = v___x_754_;
goto v___jp_707_;
}
else
{
v___y_708_ = v___x_753_;
goto v___jp_707_;
}
v___jp_707_:
{
if (v___y_708_ == 0)
{
lean_object* v___x_709_; lean_object* v___x_710_; 
lean_dec_ref_known(v_e_383_, 3);
v___x_709_ = lean_box(0);
v___x_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
return v___x_710_;
}
else
{
lean_object* v___x_711_; lean_object* v_maxFVar_712_; lean_object* v___x_713_; 
v___x_711_ = lean_st_ref_get(v_a_385_);
v_maxFVar_712_ = lean_ctor_get(v___x_711_, 1);
lean_inc_ref(v_maxFVar_712_);
lean_dec(v___x_711_);
v___x_713_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_712_, v_e_383_);
lean_dec_ref(v_maxFVar_712_);
if (lean_obj_tag(v___x_713_) == 1)
{
lean_object* v_val_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
lean_dec_ref_known(v_e_383_, 3);
v_val_714_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_713_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_val_714_);
lean_dec(v___x_713_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
lean_ctor_set_tag(v___x_716_, 0);
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_val_714_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
else
{
lean_object* v___x_722_; 
lean_dec(v___x_713_);
lean_inc_ref(v_struct_706_);
v___x_722_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_struct_706_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_752_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_752_ == 0)
{
v___x_725_ = v___x_722_;
v_isShared_726_ = v_isSharedCheck_752_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_722_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_752_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_727_; lean_object* v_share_728_; lean_object* v_maxFVar_729_; lean_object* v_proofInstInfo_730_; lean_object* v_inferType_731_; lean_object* v_getLevel_732_; lean_object* v_congrInfo_733_; lean_object* v_defEqI_734_; lean_object* v_extensions_735_; lean_object* v_issues_736_; lean_object* v_canon_737_; lean_object* v_instanceOverrides_738_; uint8_t v_debug_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_751_; 
v___x_727_ = lean_st_ref_take(v_a_385_);
v_share_728_ = lean_ctor_get(v___x_727_, 0);
v_maxFVar_729_ = lean_ctor_get(v___x_727_, 1);
v_proofInstInfo_730_ = lean_ctor_get(v___x_727_, 2);
v_inferType_731_ = lean_ctor_get(v___x_727_, 3);
v_getLevel_732_ = lean_ctor_get(v___x_727_, 4);
v_congrInfo_733_ = lean_ctor_get(v___x_727_, 5);
v_defEqI_734_ = lean_ctor_get(v___x_727_, 6);
v_extensions_735_ = lean_ctor_get(v___x_727_, 7);
v_issues_736_ = lean_ctor_get(v___x_727_, 8);
v_canon_737_ = lean_ctor_get(v___x_727_, 9);
v_instanceOverrides_738_ = lean_ctor_get(v___x_727_, 10);
v_debug_739_ = lean_ctor_get_uint8(v___x_727_, sizeof(void*)*11);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_751_ == 0)
{
v___x_741_ = v___x_727_;
v_isShared_742_ = v_isSharedCheck_751_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_instanceOverrides_738_);
lean_inc(v_canon_737_);
lean_inc(v_issues_736_);
lean_inc(v_extensions_735_);
lean_inc(v_defEqI_734_);
lean_inc(v_congrInfo_733_);
lean_inc(v_getLevel_732_);
lean_inc(v_inferType_731_);
lean_inc(v_proofInstInfo_730_);
lean_inc(v_maxFVar_729_);
lean_inc(v_share_728_);
lean_dec(v___x_727_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_751_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_743_; lean_object* v___x_745_; 
lean_inc(v_a_723_);
v___x_743_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_729_, v_e_383_, v_a_723_);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 1, v___x_743_);
v___x_745_ = v___x_741_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_share_728_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v___x_743_);
lean_ctor_set(v_reuseFailAlloc_750_, 2, v_proofInstInfo_730_);
lean_ctor_set(v_reuseFailAlloc_750_, 3, v_inferType_731_);
lean_ctor_set(v_reuseFailAlloc_750_, 4, v_getLevel_732_);
lean_ctor_set(v_reuseFailAlloc_750_, 5, v_congrInfo_733_);
lean_ctor_set(v_reuseFailAlloc_750_, 6, v_defEqI_734_);
lean_ctor_set(v_reuseFailAlloc_750_, 7, v_extensions_735_);
lean_ctor_set(v_reuseFailAlloc_750_, 8, v_issues_736_);
lean_ctor_set(v_reuseFailAlloc_750_, 9, v_canon_737_);
lean_ctor_set(v_reuseFailAlloc_750_, 10, v_instanceOverrides_738_);
lean_ctor_set_uint8(v_reuseFailAlloc_750_, sizeof(void*)*11, v_debug_739_);
v___x_745_ = v_reuseFailAlloc_750_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
lean_object* v___x_746_; lean_object* v___x_748_; 
v___x_746_ = lean_st_ref_set(v_a_385_, v___x_745_);
if (v_isShared_726_ == 0)
{
v___x_748_ = v___x_725_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_a_723_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_383_, 3);
return v___x_722_;
}
}
}
}
}
default: 
{
lean_object* v___x_755_; lean_object* v___x_756_; 
lean_dec_ref(v_e_383_);
v___x_755_ = lean_box(0);
v___x_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
return v___x_756_;
}
}
v___jp_391_:
{
if (lean_obj_tag(v___y_392_) == 0)
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_422_; 
v_a_393_ = lean_ctor_get(v___y_392_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___y_392_);
if (v_isSharedCheck_422_ == 0)
{
v___x_395_ = v___y_392_;
v_isShared_396_ = v_isSharedCheck_422_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___y_392_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_422_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_397_; lean_object* v_share_398_; lean_object* v_maxFVar_399_; lean_object* v_proofInstInfo_400_; lean_object* v_inferType_401_; lean_object* v_getLevel_402_; lean_object* v_congrInfo_403_; lean_object* v_defEqI_404_; lean_object* v_extensions_405_; lean_object* v_issues_406_; lean_object* v_canon_407_; lean_object* v_instanceOverrides_408_; uint8_t v_debug_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_421_; 
v___x_397_ = lean_st_ref_take(v_a_385_);
v_share_398_ = lean_ctor_get(v___x_397_, 0);
v_maxFVar_399_ = lean_ctor_get(v___x_397_, 1);
v_proofInstInfo_400_ = lean_ctor_get(v___x_397_, 2);
v_inferType_401_ = lean_ctor_get(v___x_397_, 3);
v_getLevel_402_ = lean_ctor_get(v___x_397_, 4);
v_congrInfo_403_ = lean_ctor_get(v___x_397_, 5);
v_defEqI_404_ = lean_ctor_get(v___x_397_, 6);
v_extensions_405_ = lean_ctor_get(v___x_397_, 7);
v_issues_406_ = lean_ctor_get(v___x_397_, 8);
v_canon_407_ = lean_ctor_get(v___x_397_, 9);
v_instanceOverrides_408_ = lean_ctor_get(v___x_397_, 10);
v_debug_409_ = lean_ctor_get_uint8(v___x_397_, sizeof(void*)*11);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_421_ == 0)
{
v___x_411_ = v___x_397_;
v_isShared_412_ = v_isSharedCheck_421_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_instanceOverrides_408_);
lean_inc(v_canon_407_);
lean_inc(v_issues_406_);
lean_inc(v_extensions_405_);
lean_inc(v_defEqI_404_);
lean_inc(v_congrInfo_403_);
lean_inc(v_getLevel_402_);
lean_inc(v_inferType_401_);
lean_inc(v_proofInstInfo_400_);
lean_inc(v_maxFVar_399_);
lean_inc(v_share_398_);
lean_dec(v___x_397_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_421_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_413_; lean_object* v___x_415_; 
lean_inc(v_a_393_);
v___x_413_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_399_, v_e_383_, v_a_393_);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 1, v___x_413_);
v___x_415_ = v___x_411_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_share_398_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v___x_413_);
lean_ctor_set(v_reuseFailAlloc_420_, 2, v_proofInstInfo_400_);
lean_ctor_set(v_reuseFailAlloc_420_, 3, v_inferType_401_);
lean_ctor_set(v_reuseFailAlloc_420_, 4, v_getLevel_402_);
lean_ctor_set(v_reuseFailAlloc_420_, 5, v_congrInfo_403_);
lean_ctor_set(v_reuseFailAlloc_420_, 6, v_defEqI_404_);
lean_ctor_set(v_reuseFailAlloc_420_, 7, v_extensions_405_);
lean_ctor_set(v_reuseFailAlloc_420_, 8, v_issues_406_);
lean_ctor_set(v_reuseFailAlloc_420_, 9, v_canon_407_);
lean_ctor_set(v_reuseFailAlloc_420_, 10, v_instanceOverrides_408_);
lean_ctor_set_uint8(v_reuseFailAlloc_420_, sizeof(void*)*11, v_debug_409_);
v___x_415_ = v_reuseFailAlloc_420_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
lean_object* v___x_416_; lean_object* v___x_418_; 
v___x_416_ = lean_st_ref_set(v_a_385_, v___x_415_);
if (v_isShared_396_ == 0)
{
v___x_418_ = v___x_395_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_393_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_383_);
return v___y_392_;
}
}
v___jp_423_:
{
lean_object* v___x_425_; lean_object* v_share_426_; lean_object* v_maxFVar_427_; lean_object* v_proofInstInfo_428_; lean_object* v_inferType_429_; lean_object* v_getLevel_430_; lean_object* v_congrInfo_431_; lean_object* v_defEqI_432_; lean_object* v_extensions_433_; lean_object* v_issues_434_; lean_object* v_canon_435_; lean_object* v_instanceOverrides_436_; uint8_t v_debug_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_447_; 
v___x_425_ = lean_st_ref_take(v_a_385_);
v_share_426_ = lean_ctor_get(v___x_425_, 0);
v_maxFVar_427_ = lean_ctor_get(v___x_425_, 1);
v_proofInstInfo_428_ = lean_ctor_get(v___x_425_, 2);
v_inferType_429_ = lean_ctor_get(v___x_425_, 3);
v_getLevel_430_ = lean_ctor_get(v___x_425_, 4);
v_congrInfo_431_ = lean_ctor_get(v___x_425_, 5);
v_defEqI_432_ = lean_ctor_get(v___x_425_, 6);
v_extensions_433_ = lean_ctor_get(v___x_425_, 7);
v_issues_434_ = lean_ctor_get(v___x_425_, 8);
v_canon_435_ = lean_ctor_get(v___x_425_, 9);
v_instanceOverrides_436_ = lean_ctor_get(v___x_425_, 10);
v_debug_437_ = lean_ctor_get_uint8(v___x_425_, sizeof(void*)*11);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_447_ == 0)
{
v___x_439_ = v___x_425_;
v_isShared_440_ = v_isSharedCheck_447_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_instanceOverrides_436_);
lean_inc(v_canon_435_);
lean_inc(v_issues_434_);
lean_inc(v_extensions_433_);
lean_inc(v_defEqI_432_);
lean_inc(v_congrInfo_431_);
lean_inc(v_getLevel_430_);
lean_inc(v_inferType_429_);
lean_inc(v_proofInstInfo_428_);
lean_inc(v_maxFVar_427_);
lean_inc(v_share_426_);
lean_dec(v___x_425_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_447_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v___x_443_; 
lean_inc(v_a_424_);
v___x_441_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_427_, v_e_383_, v_a_424_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 1, v___x_441_);
v___x_443_ = v___x_439_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_share_426_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v___x_441_);
lean_ctor_set(v_reuseFailAlloc_446_, 2, v_proofInstInfo_428_);
lean_ctor_set(v_reuseFailAlloc_446_, 3, v_inferType_429_);
lean_ctor_set(v_reuseFailAlloc_446_, 4, v_getLevel_430_);
lean_ctor_set(v_reuseFailAlloc_446_, 5, v_congrInfo_431_);
lean_ctor_set(v_reuseFailAlloc_446_, 6, v_defEqI_432_);
lean_ctor_set(v_reuseFailAlloc_446_, 7, v_extensions_433_);
lean_ctor_set(v_reuseFailAlloc_446_, 8, v_issues_434_);
lean_ctor_set(v_reuseFailAlloc_446_, 9, v_canon_435_);
lean_ctor_set(v_reuseFailAlloc_446_, 10, v_instanceOverrides_436_);
lean_ctor_set_uint8(v_reuseFailAlloc_446_, sizeof(void*)*11, v_debug_437_);
v___x_443_ = v_reuseFailAlloc_446_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = lean_st_ref_set(v_a_385_, v___x_443_);
v___x_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_445_, 0, v_a_424_);
return v___x_445_;
}
}
}
v___jp_448_:
{
if (lean_obj_tag(v___y_450_) == 0)
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_480_; 
v_a_451_ = lean_ctor_get(v___y_450_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___y_450_);
if (v_isSharedCheck_480_ == 0)
{
v___x_453_ = v___y_450_;
v_isShared_454_ = v_isSharedCheck_480_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___y_450_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_480_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_455_; lean_object* v_share_456_; lean_object* v_maxFVar_457_; lean_object* v_proofInstInfo_458_; lean_object* v_inferType_459_; lean_object* v_getLevel_460_; lean_object* v_congrInfo_461_; lean_object* v_defEqI_462_; lean_object* v_extensions_463_; lean_object* v_issues_464_; lean_object* v_canon_465_; lean_object* v_instanceOverrides_466_; uint8_t v_debug_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_479_; 
v___x_455_ = lean_st_ref_take(v___y_449_);
v_share_456_ = lean_ctor_get(v___x_455_, 0);
v_maxFVar_457_ = lean_ctor_get(v___x_455_, 1);
v_proofInstInfo_458_ = lean_ctor_get(v___x_455_, 2);
v_inferType_459_ = lean_ctor_get(v___x_455_, 3);
v_getLevel_460_ = lean_ctor_get(v___x_455_, 4);
v_congrInfo_461_ = lean_ctor_get(v___x_455_, 5);
v_defEqI_462_ = lean_ctor_get(v___x_455_, 6);
v_extensions_463_ = lean_ctor_get(v___x_455_, 7);
v_issues_464_ = lean_ctor_get(v___x_455_, 8);
v_canon_465_ = lean_ctor_get(v___x_455_, 9);
v_instanceOverrides_466_ = lean_ctor_get(v___x_455_, 10);
v_debug_467_ = lean_ctor_get_uint8(v___x_455_, sizeof(void*)*11);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_479_ == 0)
{
v___x_469_ = v___x_455_;
v_isShared_470_ = v_isSharedCheck_479_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_instanceOverrides_466_);
lean_inc(v_canon_465_);
lean_inc(v_issues_464_);
lean_inc(v_extensions_463_);
lean_inc(v_defEqI_462_);
lean_inc(v_congrInfo_461_);
lean_inc(v_getLevel_460_);
lean_inc(v_inferType_459_);
lean_inc(v_proofInstInfo_458_);
lean_inc(v_maxFVar_457_);
lean_inc(v_share_456_);
lean_dec(v___x_455_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_479_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_471_; lean_object* v___x_473_; 
lean_inc(v_a_451_);
v___x_471_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_457_, v_e_383_, v_a_451_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 1, v___x_471_);
v___x_473_ = v___x_469_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_share_456_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v___x_471_);
lean_ctor_set(v_reuseFailAlloc_478_, 2, v_proofInstInfo_458_);
lean_ctor_set(v_reuseFailAlloc_478_, 3, v_inferType_459_);
lean_ctor_set(v_reuseFailAlloc_478_, 4, v_getLevel_460_);
lean_ctor_set(v_reuseFailAlloc_478_, 5, v_congrInfo_461_);
lean_ctor_set(v_reuseFailAlloc_478_, 6, v_defEqI_462_);
lean_ctor_set(v_reuseFailAlloc_478_, 7, v_extensions_463_);
lean_ctor_set(v_reuseFailAlloc_478_, 8, v_issues_464_);
lean_ctor_set(v_reuseFailAlloc_478_, 9, v_canon_465_);
lean_ctor_set(v_reuseFailAlloc_478_, 10, v_instanceOverrides_466_);
lean_ctor_set_uint8(v_reuseFailAlloc_478_, sizeof(void*)*11, v_debug_467_);
v___x_473_ = v_reuseFailAlloc_478_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
lean_object* v___x_474_; lean_object* v___x_476_; 
v___x_474_ = lean_st_ref_set(v___y_449_, v___x_473_);
if (v_isShared_454_ == 0)
{
v___x_476_ = v___x_453_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_451_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_383_);
return v___y_450_;
}
}
v___jp_481_:
{
if (v___y_490_ == 0)
{
lean_object* v___x_491_; lean_object* v___x_492_; 
lean_dec_ref(v___y_485_);
lean_dec_ref(v___y_482_);
lean_dec_ref(v_e_383_);
v___x_491_ = lean_box(0);
v___x_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
return v___x_492_;
}
else
{
lean_object* v___x_493_; lean_object* v_maxFVar_494_; lean_object* v___x_495_; 
v___x_493_ = lean_st_ref_get(v___y_484_);
v_maxFVar_494_ = lean_ctor_get(v___x_493_, 1);
lean_inc_ref(v_maxFVar_494_);
lean_dec(v___x_493_);
v___x_495_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_494_, v_e_383_);
lean_dec_ref(v_maxFVar_494_);
if (lean_obj_tag(v___x_495_) == 1)
{
lean_object* v_val_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
lean_dec_ref(v___y_485_);
lean_dec_ref(v___y_482_);
lean_dec_ref(v_e_383_);
v_val_496_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v___x_495_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_val_496_);
lean_dec(v___x_495_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
lean_ctor_set_tag(v___x_498_, 0);
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_val_496_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
else
{
lean_object* v___x_504_; 
lean_dec(v___x_495_);
v___x_504_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v___y_482_, v___y_487_, v___y_484_, v___y_488_, v___y_486_, v___y_489_, v___y_483_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v_a_505_; lean_object* v___x_506_; 
v_a_505_ = lean_ctor_get(v___x_504_, 0);
lean_inc(v_a_505_);
lean_dec_ref_known(v___x_504_, 1);
v___x_506_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v___y_485_, v___y_487_, v___y_484_, v___y_488_, v___y_486_, v___y_489_, v___y_483_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; lean_object* v___x_508_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_a_507_);
lean_dec_ref_known(v___x_506_, 1);
v___x_508_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_505_, v_a_507_, v___y_488_, v___y_489_, v___y_483_);
v___y_449_ = v___y_484_;
v___y_450_ = v___x_508_;
goto v___jp_448_;
}
else
{
lean_dec(v_a_505_);
v___y_449_ = v___y_484_;
v___y_450_ = v___x_506_;
goto v___jp_448_;
}
}
else
{
lean_dec_ref(v___y_485_);
v___y_449_ = v___y_484_;
v___y_450_ = v___x_504_;
goto v___jp_448_;
}
}
}
}
v___jp_509_:
{
uint8_t v___x_518_; 
v___x_518_ = l_Lean_Expr_hasFVar(v_e_383_);
if (v___x_518_ == 0)
{
uint8_t v___x_519_; 
v___x_519_ = l_Lean_Expr_hasMVar(v_e_383_);
v___y_482_ = v_d_510_;
v___y_483_ = v___y_517_;
v___y_484_ = v___y_513_;
v___y_485_ = v_b_511_;
v___y_486_ = v___y_515_;
v___y_487_ = v___y_512_;
v___y_488_ = v___y_514_;
v___y_489_ = v___y_516_;
v___y_490_ = v___x_519_;
goto v___jp_481_;
}
else
{
v___y_482_ = v_d_510_;
v___y_483_ = v___y_517_;
v___y_484_ = v___y_513_;
v___y_485_ = v_b_511_;
v___y_486_ = v___y_515_;
v___y_487_ = v___y_512_;
v___y_488_ = v___y_514_;
v___y_489_ = v___y_516_;
v___y_490_ = v___x_518_;
goto v___jp_481_;
}
}
v___jp_520_:
{
if (lean_obj_tag(v___y_521_) == 0)
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_551_; 
v_a_522_ = lean_ctor_get(v___y_521_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___y_521_);
if (v_isSharedCheck_551_ == 0)
{
v___x_524_ = v___y_521_;
v_isShared_525_ = v_isSharedCheck_551_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___y_521_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_551_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_526_; lean_object* v_share_527_; lean_object* v_maxFVar_528_; lean_object* v_proofInstInfo_529_; lean_object* v_inferType_530_; lean_object* v_getLevel_531_; lean_object* v_congrInfo_532_; lean_object* v_defEqI_533_; lean_object* v_extensions_534_; lean_object* v_issues_535_; lean_object* v_canon_536_; lean_object* v_instanceOverrides_537_; uint8_t v_debug_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_550_; 
v___x_526_ = lean_st_ref_take(v_a_385_);
v_share_527_ = lean_ctor_get(v___x_526_, 0);
v_maxFVar_528_ = lean_ctor_get(v___x_526_, 1);
v_proofInstInfo_529_ = lean_ctor_get(v___x_526_, 2);
v_inferType_530_ = lean_ctor_get(v___x_526_, 3);
v_getLevel_531_ = lean_ctor_get(v___x_526_, 4);
v_congrInfo_532_ = lean_ctor_get(v___x_526_, 5);
v_defEqI_533_ = lean_ctor_get(v___x_526_, 6);
v_extensions_534_ = lean_ctor_get(v___x_526_, 7);
v_issues_535_ = lean_ctor_get(v___x_526_, 8);
v_canon_536_ = lean_ctor_get(v___x_526_, 9);
v_instanceOverrides_537_ = lean_ctor_get(v___x_526_, 10);
v_debug_538_ = lean_ctor_get_uint8(v___x_526_, sizeof(void*)*11);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_550_ == 0)
{
v___x_540_ = v___x_526_;
v_isShared_541_ = v_isSharedCheck_550_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_instanceOverrides_537_);
lean_inc(v_canon_536_);
lean_inc(v_issues_535_);
lean_inc(v_extensions_534_);
lean_inc(v_defEqI_533_);
lean_inc(v_congrInfo_532_);
lean_inc(v_getLevel_531_);
lean_inc(v_inferType_530_);
lean_inc(v_proofInstInfo_529_);
lean_inc(v_maxFVar_528_);
lean_inc(v_share_527_);
lean_dec(v___x_526_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_550_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_542_; lean_object* v___x_544_; 
lean_inc(v_a_522_);
v___x_542_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_528_, v_e_383_, v_a_522_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 1, v___x_542_);
v___x_544_ = v___x_540_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_share_527_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v___x_542_);
lean_ctor_set(v_reuseFailAlloc_549_, 2, v_proofInstInfo_529_);
lean_ctor_set(v_reuseFailAlloc_549_, 3, v_inferType_530_);
lean_ctor_set(v_reuseFailAlloc_549_, 4, v_getLevel_531_);
lean_ctor_set(v_reuseFailAlloc_549_, 5, v_congrInfo_532_);
lean_ctor_set(v_reuseFailAlloc_549_, 6, v_defEqI_533_);
lean_ctor_set(v_reuseFailAlloc_549_, 7, v_extensions_534_);
lean_ctor_set(v_reuseFailAlloc_549_, 8, v_issues_535_);
lean_ctor_set(v_reuseFailAlloc_549_, 9, v_canon_536_);
lean_ctor_set(v_reuseFailAlloc_549_, 10, v_instanceOverrides_537_);
lean_ctor_set_uint8(v_reuseFailAlloc_549_, sizeof(void*)*11, v_debug_538_);
v___x_544_ = v_reuseFailAlloc_549_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_object* v___x_545_; lean_object* v___x_547_; 
v___x_545_ = lean_st_ref_set(v_a_385_, v___x_544_);
if (v_isShared_525_ == 0)
{
v___x_547_ = v___x_524_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_522_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_383_);
return v___y_521_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f___boxed(lean_object* v_e_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_e_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_);
lean_dec(v_a_763_);
lean_dec_ref(v_a_762_);
lean_dec(v_a_761_);
lean_dec_ref(v_a_760_);
lean_dec(v_a_759_);
lean_dec_ref(v_a_758_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0(lean_object* v_00_u03b2_766_, lean_object* v_x_767_, lean_object* v_x_768_, lean_object* v_x_769_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_x_767_, v_x_768_, v_x_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1(lean_object* v_00_u03b2_771_, lean_object* v_x_772_, lean_object* v_x_773_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_x_772_, v_x_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___boxed(lean_object* v_00_u03b2_775_, lean_object* v_x_776_, lean_object* v_x_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1(v_00_u03b2_775_, v_x_776_, v_x_777_);
lean_dec_ref(v_x_777_);
lean_dec_ref(v_x_776_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0(lean_object* v_00_u03b2_779_, lean_object* v_x_780_, size_t v_x_781_, size_t v_x_782_, lean_object* v_x_783_, lean_object* v_x_784_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_780_, v_x_781_, v_x_782_, v_x_783_, v_x_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_786_, lean_object* v_x_787_, lean_object* v_x_788_, lean_object* v_x_789_, lean_object* v_x_790_, lean_object* v_x_791_){
_start:
{
size_t v_x_6089__boxed_792_; size_t v_x_6090__boxed_793_; lean_object* v_res_794_; 
v_x_6089__boxed_792_ = lean_unbox_usize(v_x_788_);
lean_dec(v_x_788_);
v_x_6090__boxed_793_ = lean_unbox_usize(v_x_789_);
lean_dec(v_x_789_);
v_res_794_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0(v_00_u03b2_786_, v_x_787_, v_x_6089__boxed_792_, v_x_6090__boxed_793_, v_x_790_, v_x_791_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2(lean_object* v_00_u03b2_795_, lean_object* v_x_796_, size_t v_x_797_, lean_object* v_x_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_796_, v_x_797_, v_x_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_800_, lean_object* v_x_801_, lean_object* v_x_802_, lean_object* v_x_803_){
_start:
{
size_t v_x_6106__boxed_804_; lean_object* v_res_805_; 
v_x_6106__boxed_804_ = lean_unbox_usize(v_x_802_);
lean_dec(v_x_802_);
v_res_805_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2(v_00_u03b2_800_, v_x_801_, v_x_6106__boxed_804_, v_x_803_);
lean_dec_ref(v_x_803_);
lean_dec_ref(v_x_801_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_806_, lean_object* v_n_807_, lean_object* v_k_808_, lean_object* v_v_809_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(v_n_807_, v_k_808_, v_v_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_811_, size_t v_depth_812_, lean_object* v_keys_813_, lean_object* v_vals_814_, lean_object* v_heq_815_, lean_object* v_i_816_, lean_object* v_entries_817_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(v_depth_812_, v_keys_813_, v_vals_814_, v_i_816_, v_entries_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_819_, lean_object* v_depth_820_, lean_object* v_keys_821_, lean_object* v_vals_822_, lean_object* v_heq_823_, lean_object* v_i_824_, lean_object* v_entries_825_){
_start:
{
size_t v_depth_boxed_826_; lean_object* v_res_827_; 
v_depth_boxed_826_ = lean_unbox_usize(v_depth_820_);
lean_dec(v_depth_820_);
v_res_827_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3(v_00_u03b2_819_, v_depth_boxed_826_, v_keys_821_, v_vals_822_, v_heq_823_, v_i_824_, v_entries_825_);
lean_dec_ref(v_vals_822_);
lean_dec_ref(v_keys_821_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_828_, lean_object* v_keys_829_, lean_object* v_vals_830_, lean_object* v_heq_831_, lean_object* v_i_832_, lean_object* v_k_833_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_keys_829_, v_vals_830_, v_i_832_, v_k_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_835_, lean_object* v_keys_836_, lean_object* v_vals_837_, lean_object* v_heq_838_, lean_object* v_i_839_, lean_object* v_k_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6(v_00_u03b2_835_, v_keys_836_, v_vals_837_, v_heq_838_, v_i_839_, v_k_840_);
lean_dec_ref(v_k_840_);
lean_dec_ref(v_vals_837_);
lean_dec_ref(v_keys_836_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_842_, lean_object* v_x_843_, lean_object* v_x_844_, lean_object* v_x_845_, lean_object* v_x_846_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_x_843_, v_x_844_, v_x_845_, v_x_846_);
return v___x_847_;
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
