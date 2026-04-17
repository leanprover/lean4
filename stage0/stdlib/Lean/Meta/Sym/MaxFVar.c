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
size_t lean_usize_shift_left(size_t, size_t);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__2;
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
lean_dec_ref(v___x_10_);
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
lean_dec_ref(v_fvarId1_x3f_1_);
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
lean_dec_ref(v_fvarId2_x3f_2_);
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
lean_dec_ref(v_fvarId2_x3f_2_);
lean_dec_ref(v_fvarId1_x3f_1_);
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
lean_dec_ref(v_fvarId2_x3f_2_);
lean_dec_ref(v_fvarId1_x3f_1_);
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
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_202_; size_t v___x_203_; size_t v___x_204_; 
v___x_202_ = ((size_t)5ULL);
v___x_203_ = ((size_t)1ULL);
v___x_204_ = lean_usize_shift_left(v___x_203_, v___x_202_);
return v___x_204_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_205_; size_t v___x_206_; size_t v___x_207_; 
v___x_205_ = ((size_t)1ULL);
v___x_206_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0);
v___x_207_ = lean_usize_sub(v___x_206_, v___x_205_);
return v___x_207_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(lean_object* v_x_209_, size_t v_x_210_, size_t v_x_211_, lean_object* v_x_212_, lean_object* v_x_213_){
_start:
{
if (lean_obj_tag(v_x_209_) == 0)
{
lean_object* v_es_214_; size_t v___x_215_; size_t v___x_216_; size_t v___x_217_; size_t v___x_218_; lean_object* v_j_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v_es_214_ = lean_ctor_get(v_x_209_, 0);
v___x_215_ = ((size_t)5ULL);
v___x_216_ = ((size_t)1ULL);
v___x_217_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1);
v___x_218_ = lean_usize_land(v_x_210_, v___x_217_);
v_j_219_ = lean_usize_to_nat(v___x_218_);
v___x_220_ = lean_array_get_size(v_es_214_);
v___x_221_ = lean_nat_dec_lt(v_j_219_, v___x_220_);
if (v___x_221_ == 0)
{
lean_dec(v_j_219_);
lean_dec(v_x_213_);
lean_dec_ref(v_x_212_);
return v_x_209_;
}
else
{
lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_258_; 
lean_inc_ref(v_es_214_);
v_isSharedCheck_258_ = !lean_is_exclusive(v_x_209_);
if (v_isSharedCheck_258_ == 0)
{
lean_object* v_unused_259_; 
v_unused_259_ = lean_ctor_get(v_x_209_, 0);
lean_dec(v_unused_259_);
v___x_223_ = v_x_209_;
v_isShared_224_ = v_isSharedCheck_258_;
goto v_resetjp_222_;
}
else
{
lean_dec(v_x_209_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_258_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v_v_225_; lean_object* v___x_226_; lean_object* v_xs_x27_227_; lean_object* v___y_229_; 
v_v_225_ = lean_array_fget(v_es_214_, v_j_219_);
v___x_226_ = lean_box(0);
v_xs_x27_227_ = lean_array_fset(v_es_214_, v_j_219_, v___x_226_);
switch(lean_obj_tag(v_v_225_))
{
case 0:
{
lean_object* v_key_234_; lean_object* v_val_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_245_; 
v_key_234_ = lean_ctor_get(v_v_225_, 0);
v_val_235_ = lean_ctor_get(v_v_225_, 1);
v_isSharedCheck_245_ = !lean_is_exclusive(v_v_225_);
if (v_isSharedCheck_245_ == 0)
{
v___x_237_ = v_v_225_;
v_isShared_238_ = v_isSharedCheck_245_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_val_235_);
lean_inc(v_key_234_);
lean_dec(v_v_225_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_245_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
uint8_t v___x_239_; 
v___x_239_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_212_, v_key_234_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; lean_object* v___x_241_; 
lean_del_object(v___x_237_);
v___x_240_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_234_, v_val_235_, v_x_212_, v_x_213_);
v___x_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
v___y_229_ = v___x_241_;
goto v___jp_228_;
}
else
{
lean_object* v___x_243_; 
lean_dec(v_val_235_);
lean_dec(v_key_234_);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 1, v_x_213_);
lean_ctor_set(v___x_237_, 0, v_x_212_);
v___x_243_ = v___x_237_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_x_212_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v_x_213_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
v___y_229_ = v___x_243_;
goto v___jp_228_;
}
}
}
}
case 1:
{
lean_object* v_node_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_256_; 
v_node_246_ = lean_ctor_get(v_v_225_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v_v_225_);
if (v_isSharedCheck_256_ == 0)
{
v___x_248_ = v_v_225_;
v_isShared_249_ = v_isSharedCheck_256_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_node_246_);
lean_dec(v_v_225_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_256_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
size_t v___x_250_; size_t v___x_251_; lean_object* v___x_252_; lean_object* v___x_254_; 
v___x_250_ = lean_usize_shift_right(v_x_210_, v___x_215_);
v___x_251_ = lean_usize_add(v_x_211_, v___x_216_);
v___x_252_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_node_246_, v___x_250_, v___x_251_, v_x_212_, v_x_213_);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 0, v___x_252_);
v___x_254_ = v___x_248_;
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
v___y_229_ = v___x_254_;
goto v___jp_228_;
}
}
}
default: 
{
lean_object* v___x_257_; 
v___x_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_257_, 0, v_x_212_);
lean_ctor_set(v___x_257_, 1, v_x_213_);
v___y_229_ = v___x_257_;
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
lean_object* v_ks_260_; lean_object* v_vs_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_281_; 
v_ks_260_ = lean_ctor_get(v_x_209_, 0);
v_vs_261_ = lean_ctor_get(v_x_209_, 1);
v_isSharedCheck_281_ = !lean_is_exclusive(v_x_209_);
if (v_isSharedCheck_281_ == 0)
{
v___x_263_ = v_x_209_;
v_isShared_264_ = v_isSharedCheck_281_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_vs_261_);
lean_inc(v_ks_260_);
lean_dec(v_x_209_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_281_;
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
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_ks_260_);
lean_ctor_set(v_reuseFailAlloc_280_, 1, v_vs_261_);
v___x_266_ = v_reuseFailAlloc_280_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
lean_object* v_newNode_267_; uint8_t v___y_269_; size_t v___x_275_; uint8_t v___x_276_; 
v_newNode_267_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(v___x_266_, v_x_212_, v_x_213_);
v___x_275_ = ((size_t)7ULL);
v___x_276_ = lean_usize_dec_le(v___x_275_, v_x_211_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_277_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_267_);
v___x_278_ = lean_unsigned_to_nat(4u);
v___x_279_ = lean_nat_dec_lt(v___x_277_, v___x_278_);
lean_dec(v___x_277_);
v___y_269_ = v___x_279_;
goto v___jp_268_;
}
else
{
v___y_269_ = v___x_276_;
goto v___jp_268_;
}
v___jp_268_:
{
if (v___y_269_ == 0)
{
lean_object* v_ks_270_; lean_object* v_vs_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v_ks_270_ = lean_ctor_get(v_newNode_267_, 0);
lean_inc_ref(v_ks_270_);
v_vs_271_ = lean_ctor_get(v_newNode_267_, 1);
lean_inc_ref(v_vs_271_);
lean_dec_ref(v_newNode_267_);
v___x_272_ = lean_unsigned_to_nat(0u);
v___x_273_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__2);
v___x_274_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(v_x_211_, v_ks_270_, v_vs_271_, v___x_272_, v___x_273_);
lean_dec_ref(v_vs_271_);
lean_dec_ref(v_ks_270_);
return v___x_274_;
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
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(size_t v_depth_282_, lean_object* v_keys_283_, lean_object* v_vals_284_, lean_object* v_i_285_, lean_object* v_entries_286_){
_start:
{
lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_287_ = lean_array_get_size(v_keys_283_);
v___x_288_ = lean_nat_dec_lt(v_i_285_, v___x_287_);
if (v___x_288_ == 0)
{
lean_dec(v_i_285_);
return v_entries_286_;
}
else
{
lean_object* v_k_289_; lean_object* v_v_290_; uint64_t v___x_291_; size_t v_h_292_; size_t v___x_293_; lean_object* v___x_294_; size_t v___x_295_; size_t v___x_296_; size_t v___x_297_; size_t v_h_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v_k_289_ = lean_array_fget_borrowed(v_keys_283_, v_i_285_);
v_v_290_ = lean_array_fget_borrowed(v_vals_284_, v_i_285_);
v___x_291_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_289_);
v_h_292_ = lean_uint64_to_usize(v___x_291_);
v___x_293_ = ((size_t)5ULL);
v___x_294_ = lean_unsigned_to_nat(1u);
v___x_295_ = ((size_t)1ULL);
v___x_296_ = lean_usize_sub(v_depth_282_, v___x_295_);
v___x_297_ = lean_usize_mul(v___x_293_, v___x_296_);
v_h_298_ = lean_usize_shift_right(v_h_292_, v___x_297_);
v___x_299_ = lean_nat_add(v_i_285_, v___x_294_);
lean_dec(v_i_285_);
lean_inc(v_v_290_);
lean_inc(v_k_289_);
v___x_300_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_entries_286_, v_h_298_, v_depth_282_, v_k_289_, v_v_290_);
v_i_285_ = v___x_299_;
v_entries_286_ = v___x_300_;
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
size_t v_x_5211__boxed_314_; size_t v_x_5212__boxed_315_; lean_object* v_res_316_; 
v_x_5211__boxed_314_ = lean_unbox_usize(v_x_310_);
lean_dec(v_x_310_);
v_x_5212__boxed_315_ = lean_unbox_usize(v_x_311_);
lean_dec(v_x_311_);
v_res_316_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_309_, v_x_5211__boxed_314_, v_x_5212__boxed_315_, v_x_312_, v_x_313_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(lean_object* v_x_317_, lean_object* v_x_318_, lean_object* v_x_319_){
_start:
{
uint64_t v___x_320_; size_t v___x_321_; size_t v___x_322_; lean_object* v___x_323_; 
v___x_320_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_318_);
v___x_321_ = lean_uint64_to_usize(v___x_320_);
v___x_322_ = ((size_t)1ULL);
v___x_323_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_317_, v___x_321_, v___x_322_, v_x_318_, v_x_319_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(lean_object* v_keys_324_, lean_object* v_vals_325_, lean_object* v_i_326_, lean_object* v_k_327_){
_start:
{
lean_object* v___x_328_; uint8_t v___x_329_; 
v___x_328_ = lean_array_get_size(v_keys_324_);
v___x_329_ = lean_nat_dec_lt(v_i_326_, v___x_328_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; 
lean_dec(v_i_326_);
v___x_330_ = lean_box(0);
return v___x_330_;
}
else
{
lean_object* v_k_x27_331_; uint8_t v___x_332_; 
v_k_x27_331_ = lean_array_fget_borrowed(v_keys_324_, v_i_326_);
v___x_332_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_327_, v_k_x27_331_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_unsigned_to_nat(1u);
v___x_334_ = lean_nat_add(v_i_326_, v___x_333_);
lean_dec(v_i_326_);
v_i_326_ = v___x_334_;
goto _start;
}
else
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = lean_array_fget_borrowed(v_vals_325_, v_i_326_);
lean_dec(v_i_326_);
lean_inc(v___x_336_);
v___x_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
return v___x_337_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_keys_338_, lean_object* v_vals_339_, lean_object* v_i_340_, lean_object* v_k_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_keys_338_, v_vals_339_, v_i_340_, v_k_341_);
lean_dec_ref(v_k_341_);
lean_dec_ref(v_vals_339_);
lean_dec_ref(v_keys_338_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(lean_object* v_x_343_, size_t v_x_344_, lean_object* v_x_345_){
_start:
{
if (lean_obj_tag(v_x_343_) == 0)
{
lean_object* v_es_346_; lean_object* v___x_347_; size_t v___x_348_; size_t v___x_349_; size_t v___x_350_; lean_object* v_j_351_; lean_object* v___x_352_; 
v_es_346_ = lean_ctor_get(v_x_343_, 0);
v___x_347_ = lean_box(2);
v___x_348_ = ((size_t)5ULL);
v___x_349_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1);
v___x_350_ = lean_usize_land(v_x_344_, v___x_349_);
v_j_351_ = lean_usize_to_nat(v___x_350_);
v___x_352_ = lean_array_get_borrowed(v___x_347_, v_es_346_, v_j_351_);
lean_dec(v_j_351_);
switch(lean_obj_tag(v___x_352_))
{
case 0:
{
lean_object* v_key_353_; lean_object* v_val_354_; uint8_t v___x_355_; 
v_key_353_ = lean_ctor_get(v___x_352_, 0);
v_val_354_ = lean_ctor_get(v___x_352_, 1);
v___x_355_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_345_, v_key_353_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; 
v___x_356_ = lean_box(0);
return v___x_356_;
}
else
{
lean_object* v___x_357_; 
lean_inc(v_val_354_);
v___x_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_357_, 0, v_val_354_);
return v___x_357_;
}
}
case 1:
{
lean_object* v_node_358_; size_t v___x_359_; 
v_node_358_ = lean_ctor_get(v___x_352_, 0);
v___x_359_ = lean_usize_shift_right(v_x_344_, v___x_348_);
v_x_343_ = v_node_358_;
v_x_344_ = v___x_359_;
goto _start;
}
default: 
{
lean_object* v___x_361_; 
v___x_361_ = lean_box(0);
return v___x_361_;
}
}
}
else
{
lean_object* v_ks_362_; lean_object* v_vs_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v_ks_362_ = lean_ctor_get(v_x_343_, 0);
v_vs_363_ = lean_ctor_get(v_x_343_, 1);
v___x_364_ = lean_unsigned_to_nat(0u);
v___x_365_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_ks_362_, v_vs_363_, v___x_364_, v_x_345_);
return v___x_365_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_x_366_, lean_object* v_x_367_, lean_object* v_x_368_){
_start:
{
size_t v_x_5411__boxed_369_; lean_object* v_res_370_; 
v_x_5411__boxed_369_ = lean_unbox_usize(v_x_367_);
lean_dec(v_x_367_);
v_res_370_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_366_, v_x_5411__boxed_369_, v_x_368_);
lean_dec_ref(v_x_368_);
lean_dec_ref(v_x_366_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(lean_object* v_x_371_, lean_object* v_x_372_){
_start:
{
uint64_t v___x_373_; size_t v___x_374_; lean_object* v___x_375_; 
v___x_373_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_372_);
v___x_374_ = lean_uint64_to_usize(v___x_373_);
v___x_375_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_371_, v___x_374_, v_x_372_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg___boxed(lean_object* v_x_376_, lean_object* v_x_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_x_376_, v_x_377_);
lean_dec_ref(v_x_377_);
lean_dec_ref(v_x_376_);
return v_res_378_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_382_ = ((lean_object*)(l_Lean_Meta_Sym_getMaxFVar_x3f___closed__2));
v___x_383_ = lean_unsigned_to_nat(37u);
v___x_384_ = lean_unsigned_to_nat(52u);
v___x_385_ = ((lean_object*)(l_Lean_Meta_Sym_getMaxFVar_x3f___closed__1));
v___x_386_ = ((lean_object*)(l_Lean_Meta_Sym_getMaxFVar_x3f___closed__0));
v___x_387_ = l_mkPanicMessageWithDecl(v___x_386_, v___x_385_, v___x_384_, v___x_383_, v___x_382_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f(lean_object* v_e_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_){
_start:
{
lean_object* v___y_397_; lean_object* v_a_428_; lean_object* v___y_452_; lean_object* v___y_453_; lean_object* v___y_484_; lean_object* v___y_485_; lean_object* v___y_486_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; uint8_t v___y_492_; lean_object* v_d_512_; lean_object* v_b_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_523_; 
switch(lean_obj_tag(v_e_388_))
{
case 1:
{
lean_object* v_fvarId_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v_fvarId_553_ = lean_ctor_get(v_e_388_, 0);
lean_inc(v_fvarId_553_);
lean_dec_ref(v_e_388_);
v___x_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_554_, 0, v_fvarId_553_);
v___x_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
return v___x_555_;
}
case 2:
{
lean_object* v_mvarId_556_; uint8_t v___y_558_; uint8_t v___x_599_; 
v_mvarId_556_ = lean_ctor_get(v_e_388_, 0);
v___x_599_ = l_Lean_Expr_hasFVar(v_e_388_);
if (v___x_599_ == 0)
{
uint8_t v___x_600_; 
v___x_600_ = l_Lean_Expr_hasMVar(v_e_388_);
v___y_558_ = v___x_600_;
goto v___jp_557_;
}
else
{
v___y_558_ = v___x_599_;
goto v___jp_557_;
}
v___jp_557_:
{
if (v___y_558_ == 0)
{
lean_object* v___x_559_; lean_object* v___x_560_; 
lean_dec_ref(v_e_388_);
v___x_559_ = lean_box(0);
v___x_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
return v___x_560_;
}
else
{
lean_object* v___x_561_; lean_object* v_maxFVar_562_; lean_object* v___x_563_; 
v___x_561_ = lean_st_ref_get(v_a_390_);
v_maxFVar_562_ = lean_ctor_get(v___x_561_, 1);
lean_inc_ref(v_maxFVar_562_);
lean_dec(v___x_561_);
v___x_563_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_562_, v_e_388_);
lean_dec_ref(v_maxFVar_562_);
if (lean_obj_tag(v___x_563_) == 1)
{
lean_object* v_val_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
lean_dec_ref(v_e_388_);
v_val_564_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_563_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_val_564_);
lean_dec(v___x_563_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
lean_ctor_set_tag(v___x_566_, 0);
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_val_564_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
else
{
lean_object* v___x_572_; 
lean_dec(v___x_563_);
lean_inc(v_mvarId_556_);
v___x_572_ = l_Lean_MVarId_getDecl(v_mvarId_556_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v_lctx_574_; lean_object* v_decls_575_; uint8_t v___x_576_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_a_573_);
lean_dec_ref(v___x_572_);
v_lctx_574_ = lean_ctor_get(v_a_573_, 1);
lean_inc_ref(v_lctx_574_);
lean_dec(v_a_573_);
v_decls_575_ = lean_ctor_get(v_lctx_574_, 1);
v___x_576_ = l_Lean_PersistentArray_isEmpty___redArg(v_decls_575_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; 
v___x_577_ = l_Lean_LocalContext_lastDecl(v_lctx_574_);
lean_dec_ref(v_lctx_574_);
if (lean_obj_tag(v___x_577_) == 1)
{
lean_object* v_val_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_586_; 
v_val_578_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_586_ == 0)
{
v___x_580_ = v___x_577_;
v_isShared_581_ = v_isSharedCheck_586_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_val_578_);
lean_dec(v___x_577_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_586_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_582_; lean_object* v___x_584_; 
v___x_582_ = l_Lean_LocalDecl_fvarId(v_val_578_);
lean_dec(v_val_578_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 0, v___x_582_);
v___x_584_ = v___x_580_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_582_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
v_a_428_ = v___x_584_;
goto v___jp_427_;
}
}
}
else
{
lean_object* v___x_587_; lean_object* v___x_588_; 
lean_dec(v___x_577_);
v___x_587_ = lean_obj_once(&l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3, &l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3_once, _init_l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3);
v___x_588_ = l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2(v___x_587_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v_a_589_; 
v_a_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_a_589_);
lean_dec_ref(v___x_588_);
v_a_428_ = v_a_589_;
goto v___jp_427_;
}
else
{
lean_dec_ref(v_e_388_);
return v___x_588_;
}
}
}
else
{
lean_object* v___x_590_; 
lean_dec_ref(v_lctx_574_);
v___x_590_ = lean_box(0);
v_a_428_ = v___x_590_;
goto v___jp_427_;
}
}
else
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_598_; 
lean_dec_ref(v_e_388_);
v_a_591_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_598_ == 0)
{
v___x_593_ = v___x_572_;
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_572_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_594_ == 0)
{
v___x_596_ = v___x_593_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_591_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
}
}
}
case 5:
{
lean_object* v_fn_601_; lean_object* v_arg_602_; uint8_t v___y_604_; uint8_t v___x_623_; 
v_fn_601_ = lean_ctor_get(v_e_388_, 0);
v_arg_602_ = lean_ctor_get(v_e_388_, 1);
v___x_623_ = l_Lean_Expr_hasFVar(v_e_388_);
if (v___x_623_ == 0)
{
uint8_t v___x_624_; 
v___x_624_ = l_Lean_Expr_hasMVar(v_e_388_);
v___y_604_ = v___x_624_;
goto v___jp_603_;
}
else
{
v___y_604_ = v___x_623_;
goto v___jp_603_;
}
v___jp_603_:
{
if (v___y_604_ == 0)
{
lean_object* v___x_605_; lean_object* v___x_606_; 
lean_dec_ref(v_e_388_);
v___x_605_ = lean_box(0);
v___x_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
return v___x_606_;
}
else
{
lean_object* v___x_607_; lean_object* v_maxFVar_608_; lean_object* v___x_609_; 
v___x_607_ = lean_st_ref_get(v_a_390_);
v_maxFVar_608_ = lean_ctor_get(v___x_607_, 1);
lean_inc_ref(v_maxFVar_608_);
lean_dec(v___x_607_);
v___x_609_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_608_, v_e_388_);
lean_dec_ref(v_maxFVar_608_);
if (lean_obj_tag(v___x_609_) == 1)
{
lean_object* v_val_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
lean_dec_ref(v_e_388_);
v_val_610_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_617_ == 0)
{
v___x_612_ = v___x_609_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_val_610_);
lean_dec(v___x_609_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
lean_ctor_set_tag(v___x_612_, 0);
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_val_610_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
else
{
lean_object* v___x_618_; 
lean_dec(v___x_609_);
lean_inc_ref(v_fn_601_);
v___x_618_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_fn_601_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_a_619_; lean_object* v___x_620_; 
v_a_619_ = lean_ctor_get(v___x_618_, 0);
lean_inc(v_a_619_);
lean_dec_ref(v___x_618_);
lean_inc_ref(v_arg_602_);
v___x_620_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_arg_602_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; lean_object* v___x_622_; 
v_a_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_a_621_);
lean_dec_ref(v___x_620_);
v___x_622_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_619_, v_a_621_, v_a_391_, v_a_393_, v_a_394_);
v___y_523_ = v___x_622_;
goto v___jp_522_;
}
else
{
lean_dec(v_a_619_);
v___y_523_ = v___x_620_;
goto v___jp_522_;
}
}
else
{
v___y_523_ = v___x_618_;
goto v___jp_522_;
}
}
}
}
}
case 6:
{
lean_object* v_binderType_625_; lean_object* v_body_626_; 
v_binderType_625_ = lean_ctor_get(v_e_388_, 1);
v_body_626_ = lean_ctor_get(v_e_388_, 2);
lean_inc_ref(v_body_626_);
lean_inc_ref(v_binderType_625_);
v_d_512_ = v_binderType_625_;
v_b_513_ = v_body_626_;
v___y_514_ = v_a_389_;
v___y_515_ = v_a_390_;
v___y_516_ = v_a_391_;
v___y_517_ = v_a_392_;
v___y_518_ = v_a_393_;
v___y_519_ = v_a_394_;
goto v___jp_511_;
}
case 7:
{
lean_object* v_binderType_627_; lean_object* v_body_628_; 
v_binderType_627_ = lean_ctor_get(v_e_388_, 1);
v_body_628_ = lean_ctor_get(v_e_388_, 2);
lean_inc_ref(v_body_628_);
lean_inc_ref(v_binderType_627_);
v_d_512_ = v_binderType_627_;
v_b_513_ = v_body_628_;
v___y_514_ = v_a_389_;
v___y_515_ = v_a_390_;
v___y_516_ = v_a_391_;
v___y_517_ = v_a_392_;
v___y_518_ = v_a_393_;
v___y_519_ = v_a_394_;
goto v___jp_511_;
}
case 8:
{
lean_object* v_type_629_; lean_object* v_value_630_; lean_object* v_body_631_; uint8_t v___y_633_; uint8_t v___x_656_; 
v_type_629_ = lean_ctor_get(v_e_388_, 1);
v_value_630_ = lean_ctor_get(v_e_388_, 2);
v_body_631_ = lean_ctor_get(v_e_388_, 3);
v___x_656_ = l_Lean_Expr_hasFVar(v_e_388_);
if (v___x_656_ == 0)
{
uint8_t v___x_657_; 
v___x_657_ = l_Lean_Expr_hasMVar(v_e_388_);
v___y_633_ = v___x_657_;
goto v___jp_632_;
}
else
{
v___y_633_ = v___x_656_;
goto v___jp_632_;
}
v___jp_632_:
{
if (v___y_633_ == 0)
{
lean_object* v___x_634_; lean_object* v___x_635_; 
lean_dec_ref(v_e_388_);
v___x_634_ = lean_box(0);
v___x_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
return v___x_635_;
}
else
{
lean_object* v___x_636_; lean_object* v_maxFVar_637_; lean_object* v___x_638_; 
v___x_636_ = lean_st_ref_get(v_a_390_);
v_maxFVar_637_ = lean_ctor_get(v___x_636_, 1);
lean_inc_ref(v_maxFVar_637_);
lean_dec(v___x_636_);
v___x_638_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_637_, v_e_388_);
lean_dec_ref(v_maxFVar_637_);
if (lean_obj_tag(v___x_638_) == 1)
{
lean_object* v_val_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_646_; 
lean_dec_ref(v_e_388_);
v_val_639_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_646_ == 0)
{
v___x_641_ = v___x_638_;
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_val_639_);
lean_dec(v___x_638_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
lean_ctor_set_tag(v___x_641_, 0);
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_val_639_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
else
{
lean_object* v___x_647_; 
lean_dec(v___x_638_);
lean_inc_ref(v_type_629_);
v___x_647_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_type_629_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; lean_object* v___x_649_; 
v_a_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc(v_a_648_);
lean_dec_ref(v___x_647_);
lean_inc_ref(v_value_630_);
v___x_649_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_value_630_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_a_650_; lean_object* v___x_651_; 
v_a_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_a_650_);
lean_dec_ref(v___x_649_);
v___x_651_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_648_, v_a_650_, v_a_391_, v_a_393_, v_a_394_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; lean_object* v___x_653_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_a_652_);
lean_dec_ref(v___x_651_);
lean_inc_ref(v_body_631_);
v___x_653_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_body_631_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; lean_object* v___x_655_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_a_654_);
lean_dec_ref(v___x_653_);
v___x_655_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_652_, v_a_654_, v_a_391_, v_a_393_, v_a_394_);
v___y_397_ = v___x_655_;
goto v___jp_396_;
}
else
{
lean_dec(v_a_652_);
v___y_397_ = v___x_653_;
goto v___jp_396_;
}
}
else
{
v___y_397_ = v___x_651_;
goto v___jp_396_;
}
}
else
{
lean_dec(v_a_648_);
v___y_397_ = v___x_649_;
goto v___jp_396_;
}
}
else
{
v___y_397_ = v___x_647_;
goto v___jp_396_;
}
}
}
}
}
case 10:
{
lean_object* v_expr_658_; uint8_t v___y_660_; uint8_t v___x_704_; 
v_expr_658_ = lean_ctor_get(v_e_388_, 1);
lean_inc_ref(v_expr_658_);
lean_dec_ref(v_e_388_);
v___x_704_ = l_Lean_Expr_hasFVar(v_expr_658_);
if (v___x_704_ == 0)
{
uint8_t v___x_705_; 
v___x_705_ = l_Lean_Expr_hasMVar(v_expr_658_);
v___y_660_ = v___x_705_;
goto v___jp_659_;
}
else
{
v___y_660_ = v___x_704_;
goto v___jp_659_;
}
v___jp_659_:
{
if (v___y_660_ == 0)
{
lean_object* v___x_661_; lean_object* v___x_662_; 
lean_dec_ref(v_expr_658_);
v___x_661_ = lean_box(0);
v___x_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_662_, 0, v___x_661_);
return v___x_662_;
}
else
{
lean_object* v___x_663_; lean_object* v_maxFVar_664_; lean_object* v___x_665_; 
v___x_663_ = lean_st_ref_get(v_a_390_);
v_maxFVar_664_ = lean_ctor_get(v___x_663_, 1);
lean_inc_ref(v_maxFVar_664_);
lean_dec(v___x_663_);
v___x_665_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_664_, v_expr_658_);
lean_dec_ref(v_maxFVar_664_);
if (lean_obj_tag(v___x_665_) == 1)
{
lean_object* v_val_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_673_; 
lean_dec_ref(v_expr_658_);
v_val_666_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_673_ == 0)
{
v___x_668_ = v___x_665_;
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_val_666_);
lean_dec(v___x_665_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
lean_ctor_set_tag(v___x_668_, 0);
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_val_666_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
else
{
lean_object* v___x_674_; 
lean_dec(v___x_665_);
lean_inc_ref(v_expr_658_);
v___x_674_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_expr_658_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_703_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_703_ == 0)
{
v___x_677_ = v___x_674_;
v_isShared_678_ = v_isSharedCheck_703_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_674_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_703_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_679_; lean_object* v_share_680_; lean_object* v_maxFVar_681_; lean_object* v_proofInstInfo_682_; lean_object* v_inferType_683_; lean_object* v_getLevel_684_; lean_object* v_congrInfo_685_; lean_object* v_defEqI_686_; lean_object* v_extensions_687_; lean_object* v_issues_688_; lean_object* v_canon_689_; uint8_t v_debug_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_702_; 
v___x_679_ = lean_st_ref_take(v_a_390_);
v_share_680_ = lean_ctor_get(v___x_679_, 0);
v_maxFVar_681_ = lean_ctor_get(v___x_679_, 1);
v_proofInstInfo_682_ = lean_ctor_get(v___x_679_, 2);
v_inferType_683_ = lean_ctor_get(v___x_679_, 3);
v_getLevel_684_ = lean_ctor_get(v___x_679_, 4);
v_congrInfo_685_ = lean_ctor_get(v___x_679_, 5);
v_defEqI_686_ = lean_ctor_get(v___x_679_, 6);
v_extensions_687_ = lean_ctor_get(v___x_679_, 7);
v_issues_688_ = lean_ctor_get(v___x_679_, 8);
v_canon_689_ = lean_ctor_get(v___x_679_, 9);
v_debug_690_ = lean_ctor_get_uint8(v___x_679_, sizeof(void*)*10);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_702_ == 0)
{
v___x_692_ = v___x_679_;
v_isShared_693_ = v_isSharedCheck_702_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_canon_689_);
lean_inc(v_issues_688_);
lean_inc(v_extensions_687_);
lean_inc(v_defEqI_686_);
lean_inc(v_congrInfo_685_);
lean_inc(v_getLevel_684_);
lean_inc(v_inferType_683_);
lean_inc(v_proofInstInfo_682_);
lean_inc(v_maxFVar_681_);
lean_inc(v_share_680_);
lean_dec(v___x_679_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_702_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_694_; lean_object* v___x_696_; 
lean_inc(v_a_675_);
v___x_694_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_681_, v_expr_658_, v_a_675_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 1, v___x_694_);
v___x_696_ = v___x_692_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_share_680_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v___x_694_);
lean_ctor_set(v_reuseFailAlloc_701_, 2, v_proofInstInfo_682_);
lean_ctor_set(v_reuseFailAlloc_701_, 3, v_inferType_683_);
lean_ctor_set(v_reuseFailAlloc_701_, 4, v_getLevel_684_);
lean_ctor_set(v_reuseFailAlloc_701_, 5, v_congrInfo_685_);
lean_ctor_set(v_reuseFailAlloc_701_, 6, v_defEqI_686_);
lean_ctor_set(v_reuseFailAlloc_701_, 7, v_extensions_687_);
lean_ctor_set(v_reuseFailAlloc_701_, 8, v_issues_688_);
lean_ctor_set(v_reuseFailAlloc_701_, 9, v_canon_689_);
lean_ctor_set_uint8(v_reuseFailAlloc_701_, sizeof(void*)*10, v_debug_690_);
v___x_696_ = v_reuseFailAlloc_701_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_697_ = lean_st_ref_set(v_a_390_, v___x_696_);
if (v_isShared_678_ == 0)
{
v___x_699_ = v___x_677_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_675_);
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
lean_dec_ref(v_expr_658_);
return v___x_674_;
}
}
}
}
}
case 11:
{
lean_object* v_struct_706_; uint8_t v___y_708_; uint8_t v___x_752_; 
v_struct_706_ = lean_ctor_get(v_e_388_, 2);
v___x_752_ = l_Lean_Expr_hasFVar(v_e_388_);
if (v___x_752_ == 0)
{
uint8_t v___x_753_; 
v___x_753_ = l_Lean_Expr_hasMVar(v_e_388_);
v___y_708_ = v___x_753_;
goto v___jp_707_;
}
else
{
v___y_708_ = v___x_752_;
goto v___jp_707_;
}
v___jp_707_:
{
if (v___y_708_ == 0)
{
lean_object* v___x_709_; lean_object* v___x_710_; 
lean_dec_ref(v_e_388_);
v___x_709_ = lean_box(0);
v___x_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
return v___x_710_;
}
else
{
lean_object* v___x_711_; lean_object* v_maxFVar_712_; lean_object* v___x_713_; 
v___x_711_ = lean_st_ref_get(v_a_390_);
v_maxFVar_712_ = lean_ctor_get(v___x_711_, 1);
lean_inc_ref(v_maxFVar_712_);
lean_dec(v___x_711_);
v___x_713_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_712_, v_e_388_);
lean_dec_ref(v_maxFVar_712_);
if (lean_obj_tag(v___x_713_) == 1)
{
lean_object* v_val_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
lean_dec_ref(v_e_388_);
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
v___x_722_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_struct_706_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_751_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_751_ == 0)
{
v___x_725_ = v___x_722_;
v_isShared_726_ = v_isSharedCheck_751_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_722_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_751_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_727_; lean_object* v_share_728_; lean_object* v_maxFVar_729_; lean_object* v_proofInstInfo_730_; lean_object* v_inferType_731_; lean_object* v_getLevel_732_; lean_object* v_congrInfo_733_; lean_object* v_defEqI_734_; lean_object* v_extensions_735_; lean_object* v_issues_736_; lean_object* v_canon_737_; uint8_t v_debug_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_750_; 
v___x_727_ = lean_st_ref_take(v_a_390_);
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
v_debug_738_ = lean_ctor_get_uint8(v___x_727_, sizeof(void*)*10);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_750_ == 0)
{
v___x_740_ = v___x_727_;
v_isShared_741_ = v_isSharedCheck_750_;
goto v_resetjp_739_;
}
else
{
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
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_750_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_742_; lean_object* v___x_744_; 
lean_inc(v_a_723_);
v___x_742_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_729_, v_e_388_, v_a_723_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 1, v___x_742_);
v___x_744_ = v___x_740_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_share_728_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v___x_742_);
lean_ctor_set(v_reuseFailAlloc_749_, 2, v_proofInstInfo_730_);
lean_ctor_set(v_reuseFailAlloc_749_, 3, v_inferType_731_);
lean_ctor_set(v_reuseFailAlloc_749_, 4, v_getLevel_732_);
lean_ctor_set(v_reuseFailAlloc_749_, 5, v_congrInfo_733_);
lean_ctor_set(v_reuseFailAlloc_749_, 6, v_defEqI_734_);
lean_ctor_set(v_reuseFailAlloc_749_, 7, v_extensions_735_);
lean_ctor_set(v_reuseFailAlloc_749_, 8, v_issues_736_);
lean_ctor_set(v_reuseFailAlloc_749_, 9, v_canon_737_);
lean_ctor_set_uint8(v_reuseFailAlloc_749_, sizeof(void*)*10, v_debug_738_);
v___x_744_ = v_reuseFailAlloc_749_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
lean_object* v___x_745_; lean_object* v___x_747_; 
v___x_745_ = lean_st_ref_set(v_a_390_, v___x_744_);
if (v_isShared_726_ == 0)
{
v___x_747_ = v___x_725_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_a_723_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_388_);
return v___x_722_;
}
}
}
}
}
default: 
{
lean_object* v___x_754_; lean_object* v___x_755_; 
lean_dec_ref(v_e_388_);
v___x_754_ = lean_box(0);
v___x_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
return v___x_755_;
}
}
v___jp_396_:
{
if (lean_obj_tag(v___y_397_) == 0)
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_426_; 
v_a_398_ = lean_ctor_get(v___y_397_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___y_397_);
if (v_isSharedCheck_426_ == 0)
{
v___x_400_ = v___y_397_;
v_isShared_401_ = v_isSharedCheck_426_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___y_397_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_426_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; lean_object* v_share_403_; lean_object* v_maxFVar_404_; lean_object* v_proofInstInfo_405_; lean_object* v_inferType_406_; lean_object* v_getLevel_407_; lean_object* v_congrInfo_408_; lean_object* v_defEqI_409_; lean_object* v_extensions_410_; lean_object* v_issues_411_; lean_object* v_canon_412_; uint8_t v_debug_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_425_; 
v___x_402_ = lean_st_ref_take(v_a_390_);
v_share_403_ = lean_ctor_get(v___x_402_, 0);
v_maxFVar_404_ = lean_ctor_get(v___x_402_, 1);
v_proofInstInfo_405_ = lean_ctor_get(v___x_402_, 2);
v_inferType_406_ = lean_ctor_get(v___x_402_, 3);
v_getLevel_407_ = lean_ctor_get(v___x_402_, 4);
v_congrInfo_408_ = lean_ctor_get(v___x_402_, 5);
v_defEqI_409_ = lean_ctor_get(v___x_402_, 6);
v_extensions_410_ = lean_ctor_get(v___x_402_, 7);
v_issues_411_ = lean_ctor_get(v___x_402_, 8);
v_canon_412_ = lean_ctor_get(v___x_402_, 9);
v_debug_413_ = lean_ctor_get_uint8(v___x_402_, sizeof(void*)*10);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_425_ == 0)
{
v___x_415_ = v___x_402_;
v_isShared_416_ = v_isSharedCheck_425_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_canon_412_);
lean_inc(v_issues_411_);
lean_inc(v_extensions_410_);
lean_inc(v_defEqI_409_);
lean_inc(v_congrInfo_408_);
lean_inc(v_getLevel_407_);
lean_inc(v_inferType_406_);
lean_inc(v_proofInstInfo_405_);
lean_inc(v_maxFVar_404_);
lean_inc(v_share_403_);
lean_dec(v___x_402_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_425_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_417_; lean_object* v___x_419_; 
lean_inc(v_a_398_);
v___x_417_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_404_, v_e_388_, v_a_398_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 1, v___x_417_);
v___x_419_ = v___x_415_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_share_403_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v___x_417_);
lean_ctor_set(v_reuseFailAlloc_424_, 2, v_proofInstInfo_405_);
lean_ctor_set(v_reuseFailAlloc_424_, 3, v_inferType_406_);
lean_ctor_set(v_reuseFailAlloc_424_, 4, v_getLevel_407_);
lean_ctor_set(v_reuseFailAlloc_424_, 5, v_congrInfo_408_);
lean_ctor_set(v_reuseFailAlloc_424_, 6, v_defEqI_409_);
lean_ctor_set(v_reuseFailAlloc_424_, 7, v_extensions_410_);
lean_ctor_set(v_reuseFailAlloc_424_, 8, v_issues_411_);
lean_ctor_set(v_reuseFailAlloc_424_, 9, v_canon_412_);
lean_ctor_set_uint8(v_reuseFailAlloc_424_, sizeof(void*)*10, v_debug_413_);
v___x_419_ = v_reuseFailAlloc_424_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
lean_object* v___x_420_; lean_object* v___x_422_; 
v___x_420_ = lean_st_ref_set(v_a_390_, v___x_419_);
if (v_isShared_401_ == 0)
{
v___x_422_ = v___x_400_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_a_398_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_388_);
return v___y_397_;
}
}
v___jp_427_:
{
lean_object* v___x_429_; lean_object* v_share_430_; lean_object* v_maxFVar_431_; lean_object* v_proofInstInfo_432_; lean_object* v_inferType_433_; lean_object* v_getLevel_434_; lean_object* v_congrInfo_435_; lean_object* v_defEqI_436_; lean_object* v_extensions_437_; lean_object* v_issues_438_; lean_object* v_canon_439_; uint8_t v_debug_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_450_; 
v___x_429_ = lean_st_ref_take(v_a_390_);
v_share_430_ = lean_ctor_get(v___x_429_, 0);
v_maxFVar_431_ = lean_ctor_get(v___x_429_, 1);
v_proofInstInfo_432_ = lean_ctor_get(v___x_429_, 2);
v_inferType_433_ = lean_ctor_get(v___x_429_, 3);
v_getLevel_434_ = lean_ctor_get(v___x_429_, 4);
v_congrInfo_435_ = lean_ctor_get(v___x_429_, 5);
v_defEqI_436_ = lean_ctor_get(v___x_429_, 6);
v_extensions_437_ = lean_ctor_get(v___x_429_, 7);
v_issues_438_ = lean_ctor_get(v___x_429_, 8);
v_canon_439_ = lean_ctor_get(v___x_429_, 9);
v_debug_440_ = lean_ctor_get_uint8(v___x_429_, sizeof(void*)*10);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_450_ == 0)
{
v___x_442_ = v___x_429_;
v_isShared_443_ = v_isSharedCheck_450_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_canon_439_);
lean_inc(v_issues_438_);
lean_inc(v_extensions_437_);
lean_inc(v_defEqI_436_);
lean_inc(v_congrInfo_435_);
lean_inc(v_getLevel_434_);
lean_inc(v_inferType_433_);
lean_inc(v_proofInstInfo_432_);
lean_inc(v_maxFVar_431_);
lean_inc(v_share_430_);
lean_dec(v___x_429_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_450_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; lean_object* v___x_446_; 
lean_inc(v_a_428_);
v___x_444_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_431_, v_e_388_, v_a_428_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 1, v___x_444_);
v___x_446_ = v___x_442_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_share_430_);
lean_ctor_set(v_reuseFailAlloc_449_, 1, v___x_444_);
lean_ctor_set(v_reuseFailAlloc_449_, 2, v_proofInstInfo_432_);
lean_ctor_set(v_reuseFailAlloc_449_, 3, v_inferType_433_);
lean_ctor_set(v_reuseFailAlloc_449_, 4, v_getLevel_434_);
lean_ctor_set(v_reuseFailAlloc_449_, 5, v_congrInfo_435_);
lean_ctor_set(v_reuseFailAlloc_449_, 6, v_defEqI_436_);
lean_ctor_set(v_reuseFailAlloc_449_, 7, v_extensions_437_);
lean_ctor_set(v_reuseFailAlloc_449_, 8, v_issues_438_);
lean_ctor_set(v_reuseFailAlloc_449_, 9, v_canon_439_);
lean_ctor_set_uint8(v_reuseFailAlloc_449_, sizeof(void*)*10, v_debug_440_);
v___x_446_ = v_reuseFailAlloc_449_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = lean_st_ref_set(v_a_390_, v___x_446_);
v___x_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_448_, 0, v_a_428_);
return v___x_448_;
}
}
}
v___jp_451_:
{
if (lean_obj_tag(v___y_453_) == 0)
{
lean_object* v_a_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_482_; 
v_a_454_ = lean_ctor_get(v___y_453_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___y_453_);
if (v_isSharedCheck_482_ == 0)
{
v___x_456_ = v___y_453_;
v_isShared_457_ = v_isSharedCheck_482_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_a_454_);
lean_dec(v___y_453_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_482_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_458_; lean_object* v_share_459_; lean_object* v_maxFVar_460_; lean_object* v_proofInstInfo_461_; lean_object* v_inferType_462_; lean_object* v_getLevel_463_; lean_object* v_congrInfo_464_; lean_object* v_defEqI_465_; lean_object* v_extensions_466_; lean_object* v_issues_467_; lean_object* v_canon_468_; uint8_t v_debug_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_481_; 
v___x_458_ = lean_st_ref_take(v___y_452_);
v_share_459_ = lean_ctor_get(v___x_458_, 0);
v_maxFVar_460_ = lean_ctor_get(v___x_458_, 1);
v_proofInstInfo_461_ = lean_ctor_get(v___x_458_, 2);
v_inferType_462_ = lean_ctor_get(v___x_458_, 3);
v_getLevel_463_ = lean_ctor_get(v___x_458_, 4);
v_congrInfo_464_ = lean_ctor_get(v___x_458_, 5);
v_defEqI_465_ = lean_ctor_get(v___x_458_, 6);
v_extensions_466_ = lean_ctor_get(v___x_458_, 7);
v_issues_467_ = lean_ctor_get(v___x_458_, 8);
v_canon_468_ = lean_ctor_get(v___x_458_, 9);
v_debug_469_ = lean_ctor_get_uint8(v___x_458_, sizeof(void*)*10);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_481_ == 0)
{
v___x_471_ = v___x_458_;
v_isShared_472_ = v_isSharedCheck_481_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_canon_468_);
lean_inc(v_issues_467_);
lean_inc(v_extensions_466_);
lean_inc(v_defEqI_465_);
lean_inc(v_congrInfo_464_);
lean_inc(v_getLevel_463_);
lean_inc(v_inferType_462_);
lean_inc(v_proofInstInfo_461_);
lean_inc(v_maxFVar_460_);
lean_inc(v_share_459_);
lean_dec(v___x_458_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_481_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_473_; lean_object* v___x_475_; 
lean_inc(v_a_454_);
v___x_473_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_460_, v_e_388_, v_a_454_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 1, v___x_473_);
v___x_475_ = v___x_471_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_share_459_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v___x_473_);
lean_ctor_set(v_reuseFailAlloc_480_, 2, v_proofInstInfo_461_);
lean_ctor_set(v_reuseFailAlloc_480_, 3, v_inferType_462_);
lean_ctor_set(v_reuseFailAlloc_480_, 4, v_getLevel_463_);
lean_ctor_set(v_reuseFailAlloc_480_, 5, v_congrInfo_464_);
lean_ctor_set(v_reuseFailAlloc_480_, 6, v_defEqI_465_);
lean_ctor_set(v_reuseFailAlloc_480_, 7, v_extensions_466_);
lean_ctor_set(v_reuseFailAlloc_480_, 8, v_issues_467_);
lean_ctor_set(v_reuseFailAlloc_480_, 9, v_canon_468_);
lean_ctor_set_uint8(v_reuseFailAlloc_480_, sizeof(void*)*10, v_debug_469_);
v___x_475_ = v_reuseFailAlloc_480_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
lean_object* v___x_476_; lean_object* v___x_478_; 
v___x_476_ = lean_st_ref_set(v___y_452_, v___x_475_);
if (v_isShared_457_ == 0)
{
v___x_478_ = v___x_456_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_454_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_388_);
return v___y_453_;
}
}
v___jp_483_:
{
if (v___y_492_ == 0)
{
lean_object* v___x_493_; lean_object* v___x_494_; 
lean_dec_ref(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec_ref(v_e_388_);
v___x_493_ = lean_box(0);
v___x_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
return v___x_494_;
}
else
{
lean_object* v___x_495_; lean_object* v_maxFVar_496_; lean_object* v___x_497_; 
v___x_495_ = lean_st_ref_get(v___y_484_);
v_maxFVar_496_ = lean_ctor_get(v___x_495_, 1);
lean_inc_ref(v_maxFVar_496_);
lean_dec(v___x_495_);
v___x_497_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_496_, v_e_388_);
lean_dec_ref(v_maxFVar_496_);
if (lean_obj_tag(v___x_497_) == 1)
{
lean_object* v_val_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
lean_dec_ref(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec_ref(v_e_388_);
v_val_498_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___x_497_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_val_498_);
lean_dec(v___x_497_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set_tag(v___x_500_, 0);
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_val_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
else
{
lean_object* v___x_506_; 
lean_dec(v___x_497_);
v___x_506_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v___y_486_, v___y_489_, v___y_484_, v___y_490_, v___y_491_, v___y_485_, v___y_488_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; lean_object* v___x_508_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_a_507_);
lean_dec_ref(v___x_506_);
v___x_508_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v___y_487_, v___y_489_, v___y_484_, v___y_490_, v___y_491_, v___y_485_, v___y_488_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; lean_object* v___x_510_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_a_509_);
lean_dec_ref(v___x_508_);
v___x_510_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_507_, v_a_509_, v___y_490_, v___y_485_, v___y_488_);
v___y_452_ = v___y_484_;
v___y_453_ = v___x_510_;
goto v___jp_451_;
}
else
{
lean_dec(v_a_507_);
v___y_452_ = v___y_484_;
v___y_453_ = v___x_508_;
goto v___jp_451_;
}
}
else
{
lean_dec_ref(v___y_487_);
v___y_452_ = v___y_484_;
v___y_453_ = v___x_506_;
goto v___jp_451_;
}
}
}
}
v___jp_511_:
{
uint8_t v___x_520_; 
v___x_520_ = l_Lean_Expr_hasFVar(v_e_388_);
if (v___x_520_ == 0)
{
uint8_t v___x_521_; 
v___x_521_ = l_Lean_Expr_hasMVar(v_e_388_);
v___y_484_ = v___y_515_;
v___y_485_ = v___y_518_;
v___y_486_ = v_d_512_;
v___y_487_ = v_b_513_;
v___y_488_ = v___y_519_;
v___y_489_ = v___y_514_;
v___y_490_ = v___y_516_;
v___y_491_ = v___y_517_;
v___y_492_ = v___x_521_;
goto v___jp_483_;
}
else
{
v___y_484_ = v___y_515_;
v___y_485_ = v___y_518_;
v___y_486_ = v_d_512_;
v___y_487_ = v_b_513_;
v___y_488_ = v___y_519_;
v___y_489_ = v___y_514_;
v___y_490_ = v___y_516_;
v___y_491_ = v___y_517_;
v___y_492_ = v___x_520_;
goto v___jp_483_;
}
}
v___jp_522_:
{
if (lean_obj_tag(v___y_523_) == 0)
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_552_; 
v_a_524_ = lean_ctor_get(v___y_523_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___y_523_);
if (v_isSharedCheck_552_ == 0)
{
v___x_526_ = v___y_523_;
v_isShared_527_ = v_isSharedCheck_552_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___y_523_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_552_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_528_; lean_object* v_share_529_; lean_object* v_maxFVar_530_; lean_object* v_proofInstInfo_531_; lean_object* v_inferType_532_; lean_object* v_getLevel_533_; lean_object* v_congrInfo_534_; lean_object* v_defEqI_535_; lean_object* v_extensions_536_; lean_object* v_issues_537_; lean_object* v_canon_538_; uint8_t v_debug_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_551_; 
v___x_528_ = lean_st_ref_take(v_a_390_);
v_share_529_ = lean_ctor_get(v___x_528_, 0);
v_maxFVar_530_ = lean_ctor_get(v___x_528_, 1);
v_proofInstInfo_531_ = lean_ctor_get(v___x_528_, 2);
v_inferType_532_ = lean_ctor_get(v___x_528_, 3);
v_getLevel_533_ = lean_ctor_get(v___x_528_, 4);
v_congrInfo_534_ = lean_ctor_get(v___x_528_, 5);
v_defEqI_535_ = lean_ctor_get(v___x_528_, 6);
v_extensions_536_ = lean_ctor_get(v___x_528_, 7);
v_issues_537_ = lean_ctor_get(v___x_528_, 8);
v_canon_538_ = lean_ctor_get(v___x_528_, 9);
v_debug_539_ = lean_ctor_get_uint8(v___x_528_, sizeof(void*)*10);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_551_ == 0)
{
v___x_541_ = v___x_528_;
v_isShared_542_ = v_isSharedCheck_551_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_canon_538_);
lean_inc(v_issues_537_);
lean_inc(v_extensions_536_);
lean_inc(v_defEqI_535_);
lean_inc(v_congrInfo_534_);
lean_inc(v_getLevel_533_);
lean_inc(v_inferType_532_);
lean_inc(v_proofInstInfo_531_);
lean_inc(v_maxFVar_530_);
lean_inc(v_share_529_);
lean_dec(v___x_528_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_551_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_543_; lean_object* v___x_545_; 
lean_inc(v_a_524_);
v___x_543_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_530_, v_e_388_, v_a_524_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 1, v___x_543_);
v___x_545_ = v___x_541_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_share_529_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v___x_543_);
lean_ctor_set(v_reuseFailAlloc_550_, 2, v_proofInstInfo_531_);
lean_ctor_set(v_reuseFailAlloc_550_, 3, v_inferType_532_);
lean_ctor_set(v_reuseFailAlloc_550_, 4, v_getLevel_533_);
lean_ctor_set(v_reuseFailAlloc_550_, 5, v_congrInfo_534_);
lean_ctor_set(v_reuseFailAlloc_550_, 6, v_defEqI_535_);
lean_ctor_set(v_reuseFailAlloc_550_, 7, v_extensions_536_);
lean_ctor_set(v_reuseFailAlloc_550_, 8, v_issues_537_);
lean_ctor_set(v_reuseFailAlloc_550_, 9, v_canon_538_);
lean_ctor_set_uint8(v_reuseFailAlloc_550_, sizeof(void*)*10, v_debug_539_);
v___x_545_ = v_reuseFailAlloc_550_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
lean_object* v___x_546_; lean_object* v___x_548_; 
v___x_546_ = lean_st_ref_set(v_a_390_, v___x_545_);
if (v_isShared_527_ == 0)
{
v___x_548_ = v___x_526_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_a_524_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_388_);
return v___y_523_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f___boxed(lean_object* v_e_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_e_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_);
lean_dec(v_a_762_);
lean_dec_ref(v_a_761_);
lean_dec(v_a_760_);
lean_dec_ref(v_a_759_);
lean_dec(v_a_758_);
lean_dec_ref(v_a_757_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0(lean_object* v_00_u03b2_765_, lean_object* v_x_766_, lean_object* v_x_767_, lean_object* v_x_768_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_x_766_, v_x_767_, v_x_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1(lean_object* v_00_u03b2_770_, lean_object* v_x_771_, lean_object* v_x_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_x_771_, v_x_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___boxed(lean_object* v_00_u03b2_774_, lean_object* v_x_775_, lean_object* v_x_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1(v_00_u03b2_774_, v_x_775_, v_x_776_);
lean_dec_ref(v_x_776_);
lean_dec_ref(v_x_775_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0(lean_object* v_00_u03b2_778_, lean_object* v_x_779_, size_t v_x_780_, size_t v_x_781_, lean_object* v_x_782_, lean_object* v_x_783_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_779_, v_x_780_, v_x_781_, v_x_782_, v_x_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_785_, lean_object* v_x_786_, lean_object* v_x_787_, lean_object* v_x_788_, lean_object* v_x_789_, lean_object* v_x_790_){
_start:
{
size_t v_x_6109__boxed_791_; size_t v_x_6110__boxed_792_; lean_object* v_res_793_; 
v_x_6109__boxed_791_ = lean_unbox_usize(v_x_787_);
lean_dec(v_x_787_);
v_x_6110__boxed_792_ = lean_unbox_usize(v_x_788_);
lean_dec(v_x_788_);
v_res_793_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0(v_00_u03b2_785_, v_x_786_, v_x_6109__boxed_791_, v_x_6110__boxed_792_, v_x_789_, v_x_790_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2(lean_object* v_00_u03b2_794_, lean_object* v_x_795_, size_t v_x_796_, lean_object* v_x_797_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_795_, v_x_796_, v_x_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_799_, lean_object* v_x_800_, lean_object* v_x_801_, lean_object* v_x_802_){
_start:
{
size_t v_x_6126__boxed_803_; lean_object* v_res_804_; 
v_x_6126__boxed_803_ = lean_unbox_usize(v_x_801_);
lean_dec(v_x_801_);
v_res_804_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2(v_00_u03b2_799_, v_x_800_, v_x_6126__boxed_803_, v_x_802_);
lean_dec_ref(v_x_802_);
lean_dec_ref(v_x_800_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_805_, lean_object* v_n_806_, lean_object* v_k_807_, lean_object* v_v_808_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(v_n_806_, v_k_807_, v_v_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_810_, size_t v_depth_811_, lean_object* v_keys_812_, lean_object* v_vals_813_, lean_object* v_heq_814_, lean_object* v_i_815_, lean_object* v_entries_816_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(v_depth_811_, v_keys_812_, v_vals_813_, v_i_815_, v_entries_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_818_, lean_object* v_depth_819_, lean_object* v_keys_820_, lean_object* v_vals_821_, lean_object* v_heq_822_, lean_object* v_i_823_, lean_object* v_entries_824_){
_start:
{
size_t v_depth_boxed_825_; lean_object* v_res_826_; 
v_depth_boxed_825_ = lean_unbox_usize(v_depth_819_);
lean_dec(v_depth_819_);
v_res_826_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3(v_00_u03b2_818_, v_depth_boxed_825_, v_keys_820_, v_vals_821_, v_heq_822_, v_i_823_, v_entries_824_);
lean_dec_ref(v_vals_821_);
lean_dec_ref(v_keys_820_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_827_, lean_object* v_keys_828_, lean_object* v_vals_829_, lean_object* v_heq_830_, lean_object* v_i_831_, lean_object* v_k_832_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_keys_828_, v_vals_829_, v_i_831_, v_k_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_834_, lean_object* v_keys_835_, lean_object* v_vals_836_, lean_object* v_heq_837_, lean_object* v_i_838_, lean_object* v_k_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6(v_00_u03b2_834_, v_keys_835_, v_vals_836_, v_heq_837_, v_i_838_, v_k_839_);
lean_dec_ref(v_k_839_);
lean_dec_ref(v_vals_836_);
lean_dec_ref(v_keys_835_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_841_, lean_object* v_x_842_, lean_object* v_x_843_, lean_object* v_x_844_, lean_object* v_x_845_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_x_842_, v_x_843_, v_x_844_, v_x_845_);
return v___x_846_;
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
