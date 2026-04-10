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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
lean_object* v_es_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_367_; 
v_es_346_ = lean_ctor_get(v_x_343_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v_x_343_);
if (v_isSharedCheck_367_ == 0)
{
v___x_348_ = v_x_343_;
v_isShared_349_ = v_isSharedCheck_367_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_es_346_);
lean_dec(v_x_343_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_367_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_350_; size_t v___x_351_; size_t v___x_352_; size_t v___x_353_; lean_object* v_j_354_; lean_object* v___x_355_; 
v___x_350_ = lean_box(2);
v___x_351_ = ((size_t)5ULL);
v___x_352_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1);
v___x_353_ = lean_usize_land(v_x_344_, v___x_352_);
v_j_354_ = lean_usize_to_nat(v___x_353_);
v___x_355_ = lean_array_get(v___x_350_, v_es_346_, v_j_354_);
lean_dec(v_j_354_);
lean_dec_ref(v_es_346_);
switch(lean_obj_tag(v___x_355_))
{
case 0:
{
lean_object* v_key_356_; lean_object* v_val_357_; uint8_t v___x_358_; 
v_key_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_key_356_);
v_val_357_ = lean_ctor_get(v___x_355_, 1);
lean_inc(v_val_357_);
lean_dec_ref(v___x_355_);
v___x_358_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_345_, v_key_356_);
lean_dec(v_key_356_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; 
lean_dec(v_val_357_);
lean_del_object(v___x_348_);
v___x_359_ = lean_box(0);
return v___x_359_;
}
else
{
lean_object* v___x_361_; 
if (v_isShared_349_ == 0)
{
lean_ctor_set_tag(v___x_348_, 1);
lean_ctor_set(v___x_348_, 0, v_val_357_);
v___x_361_ = v___x_348_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_val_357_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
case 1:
{
lean_object* v_node_363_; size_t v___x_364_; 
lean_del_object(v___x_348_);
v_node_363_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_node_363_);
lean_dec_ref(v___x_355_);
v___x_364_ = lean_usize_shift_right(v_x_344_, v___x_351_);
v_x_343_ = v_node_363_;
v_x_344_ = v___x_364_;
goto _start;
}
default: 
{
lean_object* v___x_366_; 
lean_del_object(v___x_348_);
v___x_366_ = lean_box(0);
return v___x_366_;
}
}
}
}
else
{
lean_object* v_ks_368_; lean_object* v_vs_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v_ks_368_ = lean_ctor_get(v_x_343_, 0);
lean_inc_ref(v_ks_368_);
v_vs_369_ = lean_ctor_get(v_x_343_, 1);
lean_inc_ref(v_vs_369_);
lean_dec_ref(v_x_343_);
v___x_370_ = lean_unsigned_to_nat(0u);
v___x_371_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_ks_368_, v_vs_369_, v___x_370_, v_x_345_);
lean_dec_ref(v_vs_369_);
lean_dec_ref(v_ks_368_);
return v___x_371_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_x_372_, lean_object* v_x_373_, lean_object* v_x_374_){
_start:
{
size_t v_x_5411__boxed_375_; lean_object* v_res_376_; 
v_x_5411__boxed_375_ = lean_unbox_usize(v_x_373_);
lean_dec(v_x_373_);
v_res_376_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_372_, v_x_5411__boxed_375_, v_x_374_);
lean_dec_ref(v_x_374_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(lean_object* v_x_377_, lean_object* v_x_378_){
_start:
{
uint64_t v___x_379_; size_t v___x_380_; lean_object* v___x_381_; 
v___x_379_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_378_);
v___x_380_ = lean_uint64_to_usize(v___x_379_);
v___x_381_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_377_, v___x_380_, v_x_378_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg___boxed(lean_object* v_x_382_, lean_object* v_x_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_x_382_, v_x_383_);
lean_dec_ref(v_x_383_);
return v_res_384_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_388_ = ((lean_object*)(l_Lean_Meta_Sym_getMaxFVar_x3f___closed__2));
v___x_389_ = lean_unsigned_to_nat(37u);
v___x_390_ = lean_unsigned_to_nat(52u);
v___x_391_ = ((lean_object*)(l_Lean_Meta_Sym_getMaxFVar_x3f___closed__1));
v___x_392_ = ((lean_object*)(l_Lean_Meta_Sym_getMaxFVar_x3f___closed__0));
v___x_393_ = l_mkPanicMessageWithDecl(v___x_392_, v___x_391_, v___x_390_, v___x_389_, v___x_388_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f(lean_object* v_e_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
lean_object* v___y_403_; lean_object* v_a_434_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; uint8_t v___y_498_; lean_object* v_d_518_; lean_object* v_b_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_529_; 
switch(lean_obj_tag(v_e_394_))
{
case 1:
{
lean_object* v_fvarId_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v_fvarId_559_ = lean_ctor_get(v_e_394_, 0);
lean_inc(v_fvarId_559_);
lean_dec_ref(v_e_394_);
v___x_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_560_, 0, v_fvarId_559_);
v___x_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
return v___x_561_;
}
case 2:
{
lean_object* v_mvarId_562_; uint8_t v___y_564_; uint8_t v___x_605_; 
v_mvarId_562_ = lean_ctor_get(v_e_394_, 0);
v___x_605_ = l_Lean_Expr_hasFVar(v_e_394_);
if (v___x_605_ == 0)
{
uint8_t v___x_606_; 
v___x_606_ = l_Lean_Expr_hasMVar(v_e_394_);
v___y_564_ = v___x_606_;
goto v___jp_563_;
}
else
{
v___y_564_ = v___x_605_;
goto v___jp_563_;
}
v___jp_563_:
{
if (v___y_564_ == 0)
{
lean_object* v___x_565_; lean_object* v___x_566_; 
lean_dec_ref(v_e_394_);
v___x_565_ = lean_box(0);
v___x_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
return v___x_566_;
}
else
{
lean_object* v___x_567_; lean_object* v_maxFVar_568_; lean_object* v___x_569_; 
v___x_567_ = lean_st_ref_get(v_a_396_);
v_maxFVar_568_ = lean_ctor_get(v___x_567_, 1);
lean_inc_ref(v_maxFVar_568_);
lean_dec(v___x_567_);
v___x_569_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_568_, v_e_394_);
if (lean_obj_tag(v___x_569_) == 1)
{
lean_object* v_val_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_577_; 
lean_dec_ref(v_e_394_);
v_val_570_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_577_ == 0)
{
v___x_572_ = v___x_569_;
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_val_570_);
lean_dec(v___x_569_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
lean_ctor_set_tag(v___x_572_, 0);
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_val_570_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
else
{
lean_object* v___x_578_; 
lean_dec(v___x_569_);
lean_inc(v_mvarId_562_);
v___x_578_ = l_Lean_MVarId_getDecl(v_mvarId_562_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; lean_object* v_lctx_580_; lean_object* v_decls_581_; uint8_t v___x_582_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_a_579_);
lean_dec_ref(v___x_578_);
v_lctx_580_ = lean_ctor_get(v_a_579_, 1);
lean_inc_ref(v_lctx_580_);
lean_dec(v_a_579_);
v_decls_581_ = lean_ctor_get(v_lctx_580_, 1);
v___x_582_ = l_Lean_PersistentArray_isEmpty___redArg(v_decls_581_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; 
v___x_583_ = l_Lean_LocalContext_lastDecl(v_lctx_580_);
lean_dec_ref(v_lctx_580_);
if (lean_obj_tag(v___x_583_) == 1)
{
lean_object* v_val_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_592_; 
v_val_584_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_592_ == 0)
{
v___x_586_ = v___x_583_;
v_isShared_587_ = v_isSharedCheck_592_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_val_584_);
lean_dec(v___x_583_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_592_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_588_; lean_object* v___x_590_; 
v___x_588_ = l_Lean_LocalDecl_fvarId(v_val_584_);
lean_dec(v_val_584_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v___x_588_);
v___x_590_ = v___x_586_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_588_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
v_a_434_ = v___x_590_;
goto v___jp_433_;
}
}
}
else
{
lean_object* v___x_593_; lean_object* v___x_594_; 
lean_dec(v___x_583_);
v___x_593_ = lean_obj_once(&l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3, &l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3_once, _init_l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3);
v___x_594_ = l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2(v___x_593_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v_a_595_; 
v_a_595_ = lean_ctor_get(v___x_594_, 0);
lean_inc(v_a_595_);
lean_dec_ref(v___x_594_);
v_a_434_ = v_a_595_;
goto v___jp_433_;
}
else
{
lean_dec_ref(v_e_394_);
return v___x_594_;
}
}
}
else
{
lean_object* v___x_596_; 
lean_dec_ref(v_lctx_580_);
v___x_596_ = lean_box(0);
v_a_434_ = v___x_596_;
goto v___jp_433_;
}
}
else
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
lean_dec_ref(v_e_394_);
v_a_597_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_604_ == 0)
{
v___x_599_ = v___x_578_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_578_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_a_597_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
}
}
}
case 5:
{
lean_object* v_fn_607_; lean_object* v_arg_608_; uint8_t v___y_610_; uint8_t v___x_629_; 
v_fn_607_ = lean_ctor_get(v_e_394_, 0);
v_arg_608_ = lean_ctor_get(v_e_394_, 1);
v___x_629_ = l_Lean_Expr_hasFVar(v_e_394_);
if (v___x_629_ == 0)
{
uint8_t v___x_630_; 
v___x_630_ = l_Lean_Expr_hasMVar(v_e_394_);
v___y_610_ = v___x_630_;
goto v___jp_609_;
}
else
{
v___y_610_ = v___x_629_;
goto v___jp_609_;
}
v___jp_609_:
{
if (v___y_610_ == 0)
{
lean_object* v___x_611_; lean_object* v___x_612_; 
lean_dec_ref(v_e_394_);
v___x_611_ = lean_box(0);
v___x_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
return v___x_612_;
}
else
{
lean_object* v___x_613_; lean_object* v_maxFVar_614_; lean_object* v___x_615_; 
v___x_613_ = lean_st_ref_get(v_a_396_);
v_maxFVar_614_ = lean_ctor_get(v___x_613_, 1);
lean_inc_ref(v_maxFVar_614_);
lean_dec(v___x_613_);
v___x_615_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_614_, v_e_394_);
if (lean_obj_tag(v___x_615_) == 1)
{
lean_object* v_val_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
lean_dec_ref(v_e_394_);
v_val_616_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___x_615_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_val_616_);
lean_dec(v___x_615_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
lean_ctor_set_tag(v___x_618_, 0);
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_val_616_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
else
{
lean_object* v___x_624_; 
lean_dec(v___x_615_);
lean_inc_ref(v_fn_607_);
v___x_624_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_fn_607_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_a_625_; lean_object* v___x_626_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_a_625_);
lean_dec_ref(v___x_624_);
lean_inc_ref(v_arg_608_);
v___x_626_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_arg_608_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v_a_627_; lean_object* v___x_628_; 
v_a_627_ = lean_ctor_get(v___x_626_, 0);
lean_inc(v_a_627_);
lean_dec_ref(v___x_626_);
v___x_628_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_625_, v_a_627_, v_a_397_, v_a_399_, v_a_400_);
v___y_529_ = v___x_628_;
goto v___jp_528_;
}
else
{
lean_dec(v_a_625_);
v___y_529_ = v___x_626_;
goto v___jp_528_;
}
}
else
{
v___y_529_ = v___x_624_;
goto v___jp_528_;
}
}
}
}
}
case 6:
{
lean_object* v_binderType_631_; lean_object* v_body_632_; 
v_binderType_631_ = lean_ctor_get(v_e_394_, 1);
v_body_632_ = lean_ctor_get(v_e_394_, 2);
lean_inc_ref(v_body_632_);
lean_inc_ref(v_binderType_631_);
v_d_518_ = v_binderType_631_;
v_b_519_ = v_body_632_;
v___y_520_ = v_a_395_;
v___y_521_ = v_a_396_;
v___y_522_ = v_a_397_;
v___y_523_ = v_a_398_;
v___y_524_ = v_a_399_;
v___y_525_ = v_a_400_;
goto v___jp_517_;
}
case 7:
{
lean_object* v_binderType_633_; lean_object* v_body_634_; 
v_binderType_633_ = lean_ctor_get(v_e_394_, 1);
v_body_634_ = lean_ctor_get(v_e_394_, 2);
lean_inc_ref(v_body_634_);
lean_inc_ref(v_binderType_633_);
v_d_518_ = v_binderType_633_;
v_b_519_ = v_body_634_;
v___y_520_ = v_a_395_;
v___y_521_ = v_a_396_;
v___y_522_ = v_a_397_;
v___y_523_ = v_a_398_;
v___y_524_ = v_a_399_;
v___y_525_ = v_a_400_;
goto v___jp_517_;
}
case 8:
{
lean_object* v_type_635_; lean_object* v_value_636_; lean_object* v_body_637_; uint8_t v___y_639_; uint8_t v___x_662_; 
v_type_635_ = lean_ctor_get(v_e_394_, 1);
v_value_636_ = lean_ctor_get(v_e_394_, 2);
v_body_637_ = lean_ctor_get(v_e_394_, 3);
v___x_662_ = l_Lean_Expr_hasFVar(v_e_394_);
if (v___x_662_ == 0)
{
uint8_t v___x_663_; 
v___x_663_ = l_Lean_Expr_hasMVar(v_e_394_);
v___y_639_ = v___x_663_;
goto v___jp_638_;
}
else
{
v___y_639_ = v___x_662_;
goto v___jp_638_;
}
v___jp_638_:
{
if (v___y_639_ == 0)
{
lean_object* v___x_640_; lean_object* v___x_641_; 
lean_dec_ref(v_e_394_);
v___x_640_ = lean_box(0);
v___x_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
return v___x_641_;
}
else
{
lean_object* v___x_642_; lean_object* v_maxFVar_643_; lean_object* v___x_644_; 
v___x_642_ = lean_st_ref_get(v_a_396_);
v_maxFVar_643_ = lean_ctor_get(v___x_642_, 1);
lean_inc_ref(v_maxFVar_643_);
lean_dec(v___x_642_);
v___x_644_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_643_, v_e_394_);
if (lean_obj_tag(v___x_644_) == 1)
{
lean_object* v_val_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
lean_dec_ref(v_e_394_);
v_val_645_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_652_ == 0)
{
v___x_647_ = v___x_644_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_val_645_);
lean_dec(v___x_644_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
lean_ctor_set_tag(v___x_647_, 0);
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_val_645_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
else
{
lean_object* v___x_653_; 
lean_dec(v___x_644_);
lean_inc_ref(v_type_635_);
v___x_653_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_type_635_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; lean_object* v___x_655_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_a_654_);
lean_dec_ref(v___x_653_);
lean_inc_ref(v_value_636_);
v___x_655_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_value_636_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; lean_object* v___x_657_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_a_656_);
lean_dec_ref(v___x_655_);
v___x_657_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_654_, v_a_656_, v_a_397_, v_a_399_, v_a_400_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_a_658_; lean_object* v___x_659_; 
v_a_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_a_658_);
lean_dec_ref(v___x_657_);
lean_inc_ref(v_body_637_);
v___x_659_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_body_637_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v_a_660_; lean_object* v___x_661_; 
v_a_660_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_a_660_);
lean_dec_ref(v___x_659_);
v___x_661_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_658_, v_a_660_, v_a_397_, v_a_399_, v_a_400_);
v___y_403_ = v___x_661_;
goto v___jp_402_;
}
else
{
lean_dec(v_a_658_);
v___y_403_ = v___x_659_;
goto v___jp_402_;
}
}
else
{
v___y_403_ = v___x_657_;
goto v___jp_402_;
}
}
else
{
lean_dec(v_a_654_);
v___y_403_ = v___x_655_;
goto v___jp_402_;
}
}
else
{
v___y_403_ = v___x_653_;
goto v___jp_402_;
}
}
}
}
}
case 10:
{
lean_object* v_expr_664_; uint8_t v___y_666_; uint8_t v___x_710_; 
v_expr_664_ = lean_ctor_get(v_e_394_, 1);
lean_inc_ref(v_expr_664_);
lean_dec_ref(v_e_394_);
v___x_710_ = l_Lean_Expr_hasFVar(v_expr_664_);
if (v___x_710_ == 0)
{
uint8_t v___x_711_; 
v___x_711_ = l_Lean_Expr_hasMVar(v_expr_664_);
v___y_666_ = v___x_711_;
goto v___jp_665_;
}
else
{
v___y_666_ = v___x_710_;
goto v___jp_665_;
}
v___jp_665_:
{
if (v___y_666_ == 0)
{
lean_object* v___x_667_; lean_object* v___x_668_; 
lean_dec_ref(v_expr_664_);
v___x_667_ = lean_box(0);
v___x_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
return v___x_668_;
}
else
{
lean_object* v___x_669_; lean_object* v_maxFVar_670_; lean_object* v___x_671_; 
v___x_669_ = lean_st_ref_get(v_a_396_);
v_maxFVar_670_ = lean_ctor_get(v___x_669_, 1);
lean_inc_ref(v_maxFVar_670_);
lean_dec(v___x_669_);
v___x_671_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_670_, v_expr_664_);
if (lean_obj_tag(v___x_671_) == 1)
{
lean_object* v_val_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_679_; 
lean_dec_ref(v_expr_664_);
v_val_672_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_679_ == 0)
{
v___x_674_ = v___x_671_;
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_val_672_);
lean_dec(v___x_671_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_677_; 
if (v_isShared_675_ == 0)
{
lean_ctor_set_tag(v___x_674_, 0);
v___x_677_ = v___x_674_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_val_672_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
else
{
lean_object* v___x_680_; 
lean_dec(v___x_671_);
lean_inc_ref(v_expr_664_);
v___x_680_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_expr_664_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_709_; 
v_a_681_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_709_ == 0)
{
v___x_683_ = v___x_680_;
v_isShared_684_ = v_isSharedCheck_709_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_680_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_709_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_685_; lean_object* v_share_686_; lean_object* v_maxFVar_687_; lean_object* v_proofInstInfo_688_; lean_object* v_inferType_689_; lean_object* v_getLevel_690_; lean_object* v_congrInfo_691_; lean_object* v_defEqI_692_; lean_object* v_extensions_693_; lean_object* v_issues_694_; lean_object* v_canon_695_; uint8_t v_debug_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_708_; 
v___x_685_ = lean_st_ref_take(v_a_396_);
v_share_686_ = lean_ctor_get(v___x_685_, 0);
v_maxFVar_687_ = lean_ctor_get(v___x_685_, 1);
v_proofInstInfo_688_ = lean_ctor_get(v___x_685_, 2);
v_inferType_689_ = lean_ctor_get(v___x_685_, 3);
v_getLevel_690_ = lean_ctor_get(v___x_685_, 4);
v_congrInfo_691_ = lean_ctor_get(v___x_685_, 5);
v_defEqI_692_ = lean_ctor_get(v___x_685_, 6);
v_extensions_693_ = lean_ctor_get(v___x_685_, 7);
v_issues_694_ = lean_ctor_get(v___x_685_, 8);
v_canon_695_ = lean_ctor_get(v___x_685_, 9);
v_debug_696_ = lean_ctor_get_uint8(v___x_685_, sizeof(void*)*10);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_708_ == 0)
{
v___x_698_ = v___x_685_;
v_isShared_699_ = v_isSharedCheck_708_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_canon_695_);
lean_inc(v_issues_694_);
lean_inc(v_extensions_693_);
lean_inc(v_defEqI_692_);
lean_inc(v_congrInfo_691_);
lean_inc(v_getLevel_690_);
lean_inc(v_inferType_689_);
lean_inc(v_proofInstInfo_688_);
lean_inc(v_maxFVar_687_);
lean_inc(v_share_686_);
lean_dec(v___x_685_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_708_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; lean_object* v___x_702_; 
lean_inc(v_a_681_);
v___x_700_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_687_, v_expr_664_, v_a_681_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 1, v___x_700_);
v___x_702_ = v___x_698_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_share_686_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_707_, 2, v_proofInstInfo_688_);
lean_ctor_set(v_reuseFailAlloc_707_, 3, v_inferType_689_);
lean_ctor_set(v_reuseFailAlloc_707_, 4, v_getLevel_690_);
lean_ctor_set(v_reuseFailAlloc_707_, 5, v_congrInfo_691_);
lean_ctor_set(v_reuseFailAlloc_707_, 6, v_defEqI_692_);
lean_ctor_set(v_reuseFailAlloc_707_, 7, v_extensions_693_);
lean_ctor_set(v_reuseFailAlloc_707_, 8, v_issues_694_);
lean_ctor_set(v_reuseFailAlloc_707_, 9, v_canon_695_);
lean_ctor_set_uint8(v_reuseFailAlloc_707_, sizeof(void*)*10, v_debug_696_);
v___x_702_ = v_reuseFailAlloc_707_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
lean_object* v___x_703_; lean_object* v___x_705_; 
v___x_703_ = lean_st_ref_set(v_a_396_, v___x_702_);
if (v_isShared_684_ == 0)
{
v___x_705_ = v___x_683_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_681_);
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
lean_dec_ref(v_expr_664_);
return v___x_680_;
}
}
}
}
}
case 11:
{
lean_object* v_struct_712_; uint8_t v___y_714_; uint8_t v___x_758_; 
v_struct_712_ = lean_ctor_get(v_e_394_, 2);
v___x_758_ = l_Lean_Expr_hasFVar(v_e_394_);
if (v___x_758_ == 0)
{
uint8_t v___x_759_; 
v___x_759_ = l_Lean_Expr_hasMVar(v_e_394_);
v___y_714_ = v___x_759_;
goto v___jp_713_;
}
else
{
v___y_714_ = v___x_758_;
goto v___jp_713_;
}
v___jp_713_:
{
if (v___y_714_ == 0)
{
lean_object* v___x_715_; lean_object* v___x_716_; 
lean_dec_ref(v_e_394_);
v___x_715_ = lean_box(0);
v___x_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_716_, 0, v___x_715_);
return v___x_716_;
}
else
{
lean_object* v___x_717_; lean_object* v_maxFVar_718_; lean_object* v___x_719_; 
v___x_717_ = lean_st_ref_get(v_a_396_);
v_maxFVar_718_ = lean_ctor_get(v___x_717_, 1);
lean_inc_ref(v_maxFVar_718_);
lean_dec(v___x_717_);
v___x_719_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_718_, v_e_394_);
if (lean_obj_tag(v___x_719_) == 1)
{
lean_object* v_val_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_727_; 
lean_dec_ref(v_e_394_);
v_val_720_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_727_ == 0)
{
v___x_722_ = v___x_719_;
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_val_720_);
lean_dec(v___x_719_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_723_ == 0)
{
lean_ctor_set_tag(v___x_722_, 0);
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_val_720_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
else
{
lean_object* v___x_728_; 
lean_dec(v___x_719_);
lean_inc_ref(v_struct_712_);
v___x_728_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_struct_712_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_757_; 
v_a_729_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_757_ == 0)
{
v___x_731_ = v___x_728_;
v_isShared_732_ = v_isSharedCheck_757_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_728_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_757_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_733_; lean_object* v_share_734_; lean_object* v_maxFVar_735_; lean_object* v_proofInstInfo_736_; lean_object* v_inferType_737_; lean_object* v_getLevel_738_; lean_object* v_congrInfo_739_; lean_object* v_defEqI_740_; lean_object* v_extensions_741_; lean_object* v_issues_742_; lean_object* v_canon_743_; uint8_t v_debug_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_756_; 
v___x_733_ = lean_st_ref_take(v_a_396_);
v_share_734_ = lean_ctor_get(v___x_733_, 0);
v_maxFVar_735_ = lean_ctor_get(v___x_733_, 1);
v_proofInstInfo_736_ = lean_ctor_get(v___x_733_, 2);
v_inferType_737_ = lean_ctor_get(v___x_733_, 3);
v_getLevel_738_ = lean_ctor_get(v___x_733_, 4);
v_congrInfo_739_ = lean_ctor_get(v___x_733_, 5);
v_defEqI_740_ = lean_ctor_get(v___x_733_, 6);
v_extensions_741_ = lean_ctor_get(v___x_733_, 7);
v_issues_742_ = lean_ctor_get(v___x_733_, 8);
v_canon_743_ = lean_ctor_get(v___x_733_, 9);
v_debug_744_ = lean_ctor_get_uint8(v___x_733_, sizeof(void*)*10);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_756_ == 0)
{
v___x_746_ = v___x_733_;
v_isShared_747_ = v_isSharedCheck_756_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_canon_743_);
lean_inc(v_issues_742_);
lean_inc(v_extensions_741_);
lean_inc(v_defEqI_740_);
lean_inc(v_congrInfo_739_);
lean_inc(v_getLevel_738_);
lean_inc(v_inferType_737_);
lean_inc(v_proofInstInfo_736_);
lean_inc(v_maxFVar_735_);
lean_inc(v_share_734_);
lean_dec(v___x_733_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_756_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_748_; lean_object* v___x_750_; 
lean_inc(v_a_729_);
v___x_748_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_735_, v_e_394_, v_a_729_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 1, v___x_748_);
v___x_750_ = v___x_746_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_share_734_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_755_, 2, v_proofInstInfo_736_);
lean_ctor_set(v_reuseFailAlloc_755_, 3, v_inferType_737_);
lean_ctor_set(v_reuseFailAlloc_755_, 4, v_getLevel_738_);
lean_ctor_set(v_reuseFailAlloc_755_, 5, v_congrInfo_739_);
lean_ctor_set(v_reuseFailAlloc_755_, 6, v_defEqI_740_);
lean_ctor_set(v_reuseFailAlloc_755_, 7, v_extensions_741_);
lean_ctor_set(v_reuseFailAlloc_755_, 8, v_issues_742_);
lean_ctor_set(v_reuseFailAlloc_755_, 9, v_canon_743_);
lean_ctor_set_uint8(v_reuseFailAlloc_755_, sizeof(void*)*10, v_debug_744_);
v___x_750_ = v_reuseFailAlloc_755_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
lean_object* v___x_751_; lean_object* v___x_753_; 
v___x_751_ = lean_st_ref_set(v_a_396_, v___x_750_);
if (v_isShared_732_ == 0)
{
v___x_753_ = v___x_731_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_729_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_394_);
return v___x_728_;
}
}
}
}
}
default: 
{
lean_object* v___x_760_; lean_object* v___x_761_; 
lean_dec_ref(v_e_394_);
v___x_760_ = lean_box(0);
v___x_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
return v___x_761_;
}
}
v___jp_402_:
{
if (lean_obj_tag(v___y_403_) == 0)
{
lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_432_; 
v_a_404_ = lean_ctor_get(v___y_403_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___y_403_);
if (v_isSharedCheck_432_ == 0)
{
v___x_406_ = v___y_403_;
v_isShared_407_ = v_isSharedCheck_432_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_dec(v___y_403_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_432_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; lean_object* v_share_409_; lean_object* v_maxFVar_410_; lean_object* v_proofInstInfo_411_; lean_object* v_inferType_412_; lean_object* v_getLevel_413_; lean_object* v_congrInfo_414_; lean_object* v_defEqI_415_; lean_object* v_extensions_416_; lean_object* v_issues_417_; lean_object* v_canon_418_; uint8_t v_debug_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_431_; 
v___x_408_ = lean_st_ref_take(v_a_396_);
v_share_409_ = lean_ctor_get(v___x_408_, 0);
v_maxFVar_410_ = lean_ctor_get(v___x_408_, 1);
v_proofInstInfo_411_ = lean_ctor_get(v___x_408_, 2);
v_inferType_412_ = lean_ctor_get(v___x_408_, 3);
v_getLevel_413_ = lean_ctor_get(v___x_408_, 4);
v_congrInfo_414_ = lean_ctor_get(v___x_408_, 5);
v_defEqI_415_ = lean_ctor_get(v___x_408_, 6);
v_extensions_416_ = lean_ctor_get(v___x_408_, 7);
v_issues_417_ = lean_ctor_get(v___x_408_, 8);
v_canon_418_ = lean_ctor_get(v___x_408_, 9);
v_debug_419_ = lean_ctor_get_uint8(v___x_408_, sizeof(void*)*10);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_431_ == 0)
{
v___x_421_ = v___x_408_;
v_isShared_422_ = v_isSharedCheck_431_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_canon_418_);
lean_inc(v_issues_417_);
lean_inc(v_extensions_416_);
lean_inc(v_defEqI_415_);
lean_inc(v_congrInfo_414_);
lean_inc(v_getLevel_413_);
lean_inc(v_inferType_412_);
lean_inc(v_proofInstInfo_411_);
lean_inc(v_maxFVar_410_);
lean_inc(v_share_409_);
lean_dec(v___x_408_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_431_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_423_; lean_object* v___x_425_; 
lean_inc(v_a_404_);
v___x_423_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_410_, v_e_394_, v_a_404_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 1, v___x_423_);
v___x_425_ = v___x_421_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_share_409_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v___x_423_);
lean_ctor_set(v_reuseFailAlloc_430_, 2, v_proofInstInfo_411_);
lean_ctor_set(v_reuseFailAlloc_430_, 3, v_inferType_412_);
lean_ctor_set(v_reuseFailAlloc_430_, 4, v_getLevel_413_);
lean_ctor_set(v_reuseFailAlloc_430_, 5, v_congrInfo_414_);
lean_ctor_set(v_reuseFailAlloc_430_, 6, v_defEqI_415_);
lean_ctor_set(v_reuseFailAlloc_430_, 7, v_extensions_416_);
lean_ctor_set(v_reuseFailAlloc_430_, 8, v_issues_417_);
lean_ctor_set(v_reuseFailAlloc_430_, 9, v_canon_418_);
lean_ctor_set_uint8(v_reuseFailAlloc_430_, sizeof(void*)*10, v_debug_419_);
v___x_425_ = v_reuseFailAlloc_430_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
lean_object* v___x_426_; lean_object* v___x_428_; 
v___x_426_ = lean_st_ref_set(v_a_396_, v___x_425_);
if (v_isShared_407_ == 0)
{
v___x_428_ = v___x_406_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_404_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_394_);
return v___y_403_;
}
}
v___jp_433_:
{
lean_object* v___x_435_; lean_object* v_share_436_; lean_object* v_maxFVar_437_; lean_object* v_proofInstInfo_438_; lean_object* v_inferType_439_; lean_object* v_getLevel_440_; lean_object* v_congrInfo_441_; lean_object* v_defEqI_442_; lean_object* v_extensions_443_; lean_object* v_issues_444_; lean_object* v_canon_445_; uint8_t v_debug_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_456_; 
v___x_435_ = lean_st_ref_take(v_a_396_);
v_share_436_ = lean_ctor_get(v___x_435_, 0);
v_maxFVar_437_ = lean_ctor_get(v___x_435_, 1);
v_proofInstInfo_438_ = lean_ctor_get(v___x_435_, 2);
v_inferType_439_ = lean_ctor_get(v___x_435_, 3);
v_getLevel_440_ = lean_ctor_get(v___x_435_, 4);
v_congrInfo_441_ = lean_ctor_get(v___x_435_, 5);
v_defEqI_442_ = lean_ctor_get(v___x_435_, 6);
v_extensions_443_ = lean_ctor_get(v___x_435_, 7);
v_issues_444_ = lean_ctor_get(v___x_435_, 8);
v_canon_445_ = lean_ctor_get(v___x_435_, 9);
v_debug_446_ = lean_ctor_get_uint8(v___x_435_, sizeof(void*)*10);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_456_ == 0)
{
v___x_448_ = v___x_435_;
v_isShared_449_ = v_isSharedCheck_456_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_canon_445_);
lean_inc(v_issues_444_);
lean_inc(v_extensions_443_);
lean_inc(v_defEqI_442_);
lean_inc(v_congrInfo_441_);
lean_inc(v_getLevel_440_);
lean_inc(v_inferType_439_);
lean_inc(v_proofInstInfo_438_);
lean_inc(v_maxFVar_437_);
lean_inc(v_share_436_);
lean_dec(v___x_435_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_456_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_450_; lean_object* v___x_452_; 
lean_inc(v_a_434_);
v___x_450_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_437_, v_e_394_, v_a_434_);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 1, v___x_450_);
v___x_452_ = v___x_448_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_share_436_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v___x_450_);
lean_ctor_set(v_reuseFailAlloc_455_, 2, v_proofInstInfo_438_);
lean_ctor_set(v_reuseFailAlloc_455_, 3, v_inferType_439_);
lean_ctor_set(v_reuseFailAlloc_455_, 4, v_getLevel_440_);
lean_ctor_set(v_reuseFailAlloc_455_, 5, v_congrInfo_441_);
lean_ctor_set(v_reuseFailAlloc_455_, 6, v_defEqI_442_);
lean_ctor_set(v_reuseFailAlloc_455_, 7, v_extensions_443_);
lean_ctor_set(v_reuseFailAlloc_455_, 8, v_issues_444_);
lean_ctor_set(v_reuseFailAlloc_455_, 9, v_canon_445_);
lean_ctor_set_uint8(v_reuseFailAlloc_455_, sizeof(void*)*10, v_debug_446_);
v___x_452_ = v_reuseFailAlloc_455_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = lean_st_ref_set(v_a_396_, v___x_452_);
v___x_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_454_, 0, v_a_434_);
return v___x_454_;
}
}
}
v___jp_457_:
{
if (lean_obj_tag(v___y_459_) == 0)
{
lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_488_; 
v_a_460_ = lean_ctor_get(v___y_459_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___y_459_);
if (v_isSharedCheck_488_ == 0)
{
v___x_462_ = v___y_459_;
v_isShared_463_ = v_isSharedCheck_488_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v___y_459_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_488_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_464_; lean_object* v_share_465_; lean_object* v_maxFVar_466_; lean_object* v_proofInstInfo_467_; lean_object* v_inferType_468_; lean_object* v_getLevel_469_; lean_object* v_congrInfo_470_; lean_object* v_defEqI_471_; lean_object* v_extensions_472_; lean_object* v_issues_473_; lean_object* v_canon_474_; uint8_t v_debug_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_487_; 
v___x_464_ = lean_st_ref_take(v___y_458_);
v_share_465_ = lean_ctor_get(v___x_464_, 0);
v_maxFVar_466_ = lean_ctor_get(v___x_464_, 1);
v_proofInstInfo_467_ = lean_ctor_get(v___x_464_, 2);
v_inferType_468_ = lean_ctor_get(v___x_464_, 3);
v_getLevel_469_ = lean_ctor_get(v___x_464_, 4);
v_congrInfo_470_ = lean_ctor_get(v___x_464_, 5);
v_defEqI_471_ = lean_ctor_get(v___x_464_, 6);
v_extensions_472_ = lean_ctor_get(v___x_464_, 7);
v_issues_473_ = lean_ctor_get(v___x_464_, 8);
v_canon_474_ = lean_ctor_get(v___x_464_, 9);
v_debug_475_ = lean_ctor_get_uint8(v___x_464_, sizeof(void*)*10);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_487_ == 0)
{
v___x_477_ = v___x_464_;
v_isShared_478_ = v_isSharedCheck_487_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_canon_474_);
lean_inc(v_issues_473_);
lean_inc(v_extensions_472_);
lean_inc(v_defEqI_471_);
lean_inc(v_congrInfo_470_);
lean_inc(v_getLevel_469_);
lean_inc(v_inferType_468_);
lean_inc(v_proofInstInfo_467_);
lean_inc(v_maxFVar_466_);
lean_inc(v_share_465_);
lean_dec(v___x_464_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_487_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_479_; lean_object* v___x_481_; 
lean_inc(v_a_460_);
v___x_479_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_466_, v_e_394_, v_a_460_);
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 1, v___x_479_);
v___x_481_ = v___x_477_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_share_465_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v___x_479_);
lean_ctor_set(v_reuseFailAlloc_486_, 2, v_proofInstInfo_467_);
lean_ctor_set(v_reuseFailAlloc_486_, 3, v_inferType_468_);
lean_ctor_set(v_reuseFailAlloc_486_, 4, v_getLevel_469_);
lean_ctor_set(v_reuseFailAlloc_486_, 5, v_congrInfo_470_);
lean_ctor_set(v_reuseFailAlloc_486_, 6, v_defEqI_471_);
lean_ctor_set(v_reuseFailAlloc_486_, 7, v_extensions_472_);
lean_ctor_set(v_reuseFailAlloc_486_, 8, v_issues_473_);
lean_ctor_set(v_reuseFailAlloc_486_, 9, v_canon_474_);
lean_ctor_set_uint8(v_reuseFailAlloc_486_, sizeof(void*)*10, v_debug_475_);
v___x_481_ = v_reuseFailAlloc_486_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
lean_object* v___x_482_; lean_object* v___x_484_; 
v___x_482_ = lean_st_ref_set(v___y_458_, v___x_481_);
if (v_isShared_463_ == 0)
{
v___x_484_ = v___x_462_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_a_460_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_394_);
return v___y_459_;
}
}
v___jp_489_:
{
if (v___y_498_ == 0)
{
lean_object* v___x_499_; lean_object* v___x_500_; 
lean_dec_ref(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec_ref(v_e_394_);
v___x_499_ = lean_box(0);
v___x_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
return v___x_500_;
}
else
{
lean_object* v___x_501_; lean_object* v_maxFVar_502_; lean_object* v___x_503_; 
v___x_501_ = lean_st_ref_get(v___y_490_);
v_maxFVar_502_ = lean_ctor_get(v___x_501_, 1);
lean_inc_ref(v_maxFVar_502_);
lean_dec(v___x_501_);
v___x_503_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_502_, v_e_394_);
if (lean_obj_tag(v___x_503_) == 1)
{
lean_object* v_val_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_511_; 
lean_dec_ref(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec_ref(v_e_394_);
v_val_504_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_511_ == 0)
{
v___x_506_ = v___x_503_;
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_val_504_);
lean_dec(v___x_503_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_509_; 
if (v_isShared_507_ == 0)
{
lean_ctor_set_tag(v___x_506_, 0);
v___x_509_ = v___x_506_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_val_504_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
else
{
lean_object* v___x_512_; 
lean_dec(v___x_503_);
v___x_512_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v___y_492_, v___y_495_, v___y_490_, v___y_496_, v___y_497_, v___y_491_, v___y_494_);
if (lean_obj_tag(v___x_512_) == 0)
{
lean_object* v_a_513_; lean_object* v___x_514_; 
v_a_513_ = lean_ctor_get(v___x_512_, 0);
lean_inc(v_a_513_);
lean_dec_ref(v___x_512_);
v___x_514_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v___y_493_, v___y_495_, v___y_490_, v___y_496_, v___y_497_, v___y_491_, v___y_494_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; lean_object* v___x_516_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
lean_inc(v_a_515_);
lean_dec_ref(v___x_514_);
v___x_516_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_513_, v_a_515_, v___y_496_, v___y_491_, v___y_494_);
v___y_458_ = v___y_490_;
v___y_459_ = v___x_516_;
goto v___jp_457_;
}
else
{
lean_dec(v_a_513_);
v___y_458_ = v___y_490_;
v___y_459_ = v___x_514_;
goto v___jp_457_;
}
}
else
{
lean_dec_ref(v___y_493_);
v___y_458_ = v___y_490_;
v___y_459_ = v___x_512_;
goto v___jp_457_;
}
}
}
}
v___jp_517_:
{
uint8_t v___x_526_; 
v___x_526_ = l_Lean_Expr_hasFVar(v_e_394_);
if (v___x_526_ == 0)
{
uint8_t v___x_527_; 
v___x_527_ = l_Lean_Expr_hasMVar(v_e_394_);
v___y_490_ = v___y_521_;
v___y_491_ = v___y_524_;
v___y_492_ = v_d_518_;
v___y_493_ = v_b_519_;
v___y_494_ = v___y_525_;
v___y_495_ = v___y_520_;
v___y_496_ = v___y_522_;
v___y_497_ = v___y_523_;
v___y_498_ = v___x_527_;
goto v___jp_489_;
}
else
{
v___y_490_ = v___y_521_;
v___y_491_ = v___y_524_;
v___y_492_ = v_d_518_;
v___y_493_ = v_b_519_;
v___y_494_ = v___y_525_;
v___y_495_ = v___y_520_;
v___y_496_ = v___y_522_;
v___y_497_ = v___y_523_;
v___y_498_ = v___x_526_;
goto v___jp_489_;
}
}
v___jp_528_:
{
if (lean_obj_tag(v___y_529_) == 0)
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_558_; 
v_a_530_ = lean_ctor_get(v___y_529_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___y_529_);
if (v_isSharedCheck_558_ == 0)
{
v___x_532_ = v___y_529_;
v_isShared_533_ = v_isSharedCheck_558_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___y_529_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_558_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_534_; lean_object* v_share_535_; lean_object* v_maxFVar_536_; lean_object* v_proofInstInfo_537_; lean_object* v_inferType_538_; lean_object* v_getLevel_539_; lean_object* v_congrInfo_540_; lean_object* v_defEqI_541_; lean_object* v_extensions_542_; lean_object* v_issues_543_; lean_object* v_canon_544_; uint8_t v_debug_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_557_; 
v___x_534_ = lean_st_ref_take(v_a_396_);
v_share_535_ = lean_ctor_get(v___x_534_, 0);
v_maxFVar_536_ = lean_ctor_get(v___x_534_, 1);
v_proofInstInfo_537_ = lean_ctor_get(v___x_534_, 2);
v_inferType_538_ = lean_ctor_get(v___x_534_, 3);
v_getLevel_539_ = lean_ctor_get(v___x_534_, 4);
v_congrInfo_540_ = lean_ctor_get(v___x_534_, 5);
v_defEqI_541_ = lean_ctor_get(v___x_534_, 6);
v_extensions_542_ = lean_ctor_get(v___x_534_, 7);
v_issues_543_ = lean_ctor_get(v___x_534_, 8);
v_canon_544_ = lean_ctor_get(v___x_534_, 9);
v_debug_545_ = lean_ctor_get_uint8(v___x_534_, sizeof(void*)*10);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_557_ == 0)
{
v___x_547_ = v___x_534_;
v_isShared_548_ = v_isSharedCheck_557_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_canon_544_);
lean_inc(v_issues_543_);
lean_inc(v_extensions_542_);
lean_inc(v_defEqI_541_);
lean_inc(v_congrInfo_540_);
lean_inc(v_getLevel_539_);
lean_inc(v_inferType_538_);
lean_inc(v_proofInstInfo_537_);
lean_inc(v_maxFVar_536_);
lean_inc(v_share_535_);
lean_dec(v___x_534_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_557_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_549_; lean_object* v___x_551_; 
lean_inc(v_a_530_);
v___x_549_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_536_, v_e_394_, v_a_530_);
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 1, v___x_549_);
v___x_551_ = v___x_547_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_share_535_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_556_, 2, v_proofInstInfo_537_);
lean_ctor_set(v_reuseFailAlloc_556_, 3, v_inferType_538_);
lean_ctor_set(v_reuseFailAlloc_556_, 4, v_getLevel_539_);
lean_ctor_set(v_reuseFailAlloc_556_, 5, v_congrInfo_540_);
lean_ctor_set(v_reuseFailAlloc_556_, 6, v_defEqI_541_);
lean_ctor_set(v_reuseFailAlloc_556_, 7, v_extensions_542_);
lean_ctor_set(v_reuseFailAlloc_556_, 8, v_issues_543_);
lean_ctor_set(v_reuseFailAlloc_556_, 9, v_canon_544_);
lean_ctor_set_uint8(v_reuseFailAlloc_556_, sizeof(void*)*10, v_debug_545_);
v___x_551_ = v_reuseFailAlloc_556_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
lean_object* v___x_552_; lean_object* v___x_554_; 
v___x_552_ = lean_st_ref_set(v_a_396_, v___x_551_);
if (v_isShared_533_ == 0)
{
v___x_554_ = v___x_532_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_530_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_394_);
return v___y_529_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f___boxed(lean_object* v_e_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_e_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_);
lean_dec(v_a_768_);
lean_dec_ref(v_a_767_);
lean_dec(v_a_766_);
lean_dec_ref(v_a_765_);
lean_dec(v_a_764_);
lean_dec_ref(v_a_763_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0(lean_object* v_00_u03b2_771_, lean_object* v_x_772_, lean_object* v_x_773_, lean_object* v_x_774_){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_x_772_, v_x_773_, v_x_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1(lean_object* v_00_u03b2_776_, lean_object* v_x_777_, lean_object* v_x_778_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_x_777_, v_x_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___boxed(lean_object* v_00_u03b2_780_, lean_object* v_x_781_, lean_object* v_x_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1(v_00_u03b2_780_, v_x_781_, v_x_782_);
lean_dec_ref(v_x_782_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0(lean_object* v_00_u03b2_784_, lean_object* v_x_785_, size_t v_x_786_, size_t v_x_787_, lean_object* v_x_788_, lean_object* v_x_789_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_785_, v_x_786_, v_x_787_, v_x_788_, v_x_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_791_, lean_object* v_x_792_, lean_object* v_x_793_, lean_object* v_x_794_, lean_object* v_x_795_, lean_object* v_x_796_){
_start:
{
size_t v_x_6121__boxed_797_; size_t v_x_6122__boxed_798_; lean_object* v_res_799_; 
v_x_6121__boxed_797_ = lean_unbox_usize(v_x_793_);
lean_dec(v_x_793_);
v_x_6122__boxed_798_ = lean_unbox_usize(v_x_794_);
lean_dec(v_x_794_);
v_res_799_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0(v_00_u03b2_791_, v_x_792_, v_x_6121__boxed_797_, v_x_6122__boxed_798_, v_x_795_, v_x_796_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2(lean_object* v_00_u03b2_800_, lean_object* v_x_801_, size_t v_x_802_, lean_object* v_x_803_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_801_, v_x_802_, v_x_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_805_, lean_object* v_x_806_, lean_object* v_x_807_, lean_object* v_x_808_){
_start:
{
size_t v_x_6138__boxed_809_; lean_object* v_res_810_; 
v_x_6138__boxed_809_ = lean_unbox_usize(v_x_807_);
lean_dec(v_x_807_);
v_res_810_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2(v_00_u03b2_805_, v_x_806_, v_x_6138__boxed_809_, v_x_808_);
lean_dec_ref(v_x_808_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_811_, lean_object* v_n_812_, lean_object* v_k_813_, lean_object* v_v_814_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(v_n_812_, v_k_813_, v_v_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_816_, size_t v_depth_817_, lean_object* v_keys_818_, lean_object* v_vals_819_, lean_object* v_heq_820_, lean_object* v_i_821_, lean_object* v_entries_822_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(v_depth_817_, v_keys_818_, v_vals_819_, v_i_821_, v_entries_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_824_, lean_object* v_depth_825_, lean_object* v_keys_826_, lean_object* v_vals_827_, lean_object* v_heq_828_, lean_object* v_i_829_, lean_object* v_entries_830_){
_start:
{
size_t v_depth_boxed_831_; lean_object* v_res_832_; 
v_depth_boxed_831_ = lean_unbox_usize(v_depth_825_);
lean_dec(v_depth_825_);
v_res_832_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3(v_00_u03b2_824_, v_depth_boxed_831_, v_keys_826_, v_vals_827_, v_heq_828_, v_i_829_, v_entries_830_);
lean_dec_ref(v_vals_827_);
lean_dec_ref(v_keys_826_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_833_, lean_object* v_keys_834_, lean_object* v_vals_835_, lean_object* v_heq_836_, lean_object* v_i_837_, lean_object* v_k_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_keys_834_, v_vals_835_, v_i_837_, v_k_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_840_, lean_object* v_keys_841_, lean_object* v_vals_842_, lean_object* v_heq_843_, lean_object* v_i_844_, lean_object* v_k_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6(v_00_u03b2_840_, v_keys_841_, v_vals_842_, v_heq_843_, v_i_844_, v_k_845_);
lean_dec_ref(v_k_845_);
lean_dec_ref(v_vals_842_);
lean_dec_ref(v_keys_841_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_847_, lean_object* v_x_848_, lean_object* v_x_849_, lean_object* v_x_850_, lean_object* v_x_851_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_x_848_, v_x_849_, v_x_850_, v_x_851_);
return v___x_852_;
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
