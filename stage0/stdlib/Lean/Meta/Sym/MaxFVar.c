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
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
lean_inc_ref(v_a_3_);
lean_inc(v_val_7_);
v___x_10_ = l_Lean_FVarId_getDecl___redArg(v_val_7_, v_a_3_, v_a_4_, v_a_5_);
if (lean_obj_tag(v___x_10_) == 0)
{
lean_object* v_a_11_; lean_object* v___x_12_; 
v_a_11_ = lean_ctor_get(v___x_10_, 0);
lean_inc(v_a_11_);
lean_dec_ref(v___x_10_);
lean_inc_ref(v_a_3_);
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
uint8_t v___y_88_; uint8_t v___x_132_; 
v___x_132_ = l_Lean_Expr_hasFVar(v_e_78_);
if (v___x_132_ == 0)
{
uint8_t v___x_133_; 
v___x_133_ = l_Lean_Expr_hasMVar(v_e_78_);
v___y_88_ = v___x_133_;
goto v___jp_87_;
}
else
{
v___y_88_ = v___x_132_;
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
lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_131_; 
v_a_105_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_131_ == 0)
{
v___x_107_ = v___x_104_;
v_isShared_108_ = v_isSharedCheck_131_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_dec(v___x_104_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_131_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_109_; lean_object* v_share_110_; lean_object* v_maxFVar_111_; lean_object* v_proofInstInfo_112_; lean_object* v_inferType_113_; lean_object* v_getLevel_114_; lean_object* v_congrInfo_115_; lean_object* v_defEqI_116_; lean_object* v_extensions_117_; uint8_t v_debug_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_130_; 
v___x_109_ = lean_st_ref_take(v_a_81_);
v_share_110_ = lean_ctor_get(v___x_109_, 0);
v_maxFVar_111_ = lean_ctor_get(v___x_109_, 1);
v_proofInstInfo_112_ = lean_ctor_get(v___x_109_, 2);
v_inferType_113_ = lean_ctor_get(v___x_109_, 3);
v_getLevel_114_ = lean_ctor_get(v___x_109_, 4);
v_congrInfo_115_ = lean_ctor_get(v___x_109_, 5);
v_defEqI_116_ = lean_ctor_get(v___x_109_, 6);
v_extensions_117_ = lean_ctor_get(v___x_109_, 7);
v_debug_118_ = lean_ctor_get_uint8(v___x_109_, sizeof(void*)*8);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_130_ == 0)
{
v___x_120_ = v___x_109_;
v_isShared_121_ = v_isSharedCheck_130_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_extensions_117_);
lean_inc(v_defEqI_116_);
lean_inc(v_congrInfo_115_);
lean_inc(v_getLevel_114_);
lean_inc(v_inferType_113_);
lean_inc(v_proofInstInfo_112_);
lean_inc(v_maxFVar_111_);
lean_inc(v_share_110_);
lean_dec(v___x_109_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_130_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_122_; lean_object* v___x_124_; 
lean_inc(v_a_105_);
v___x_122_ = l_Lean_PersistentHashMap_insert___redArg(v___f_93_, v___f_94_, v_maxFVar_111_, v_e_78_, v_a_105_);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 1, v___x_122_);
v___x_124_ = v___x_120_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_share_110_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v___x_122_);
lean_ctor_set(v_reuseFailAlloc_129_, 2, v_proofInstInfo_112_);
lean_ctor_set(v_reuseFailAlloc_129_, 3, v_inferType_113_);
lean_ctor_set(v_reuseFailAlloc_129_, 4, v_getLevel_114_);
lean_ctor_set(v_reuseFailAlloc_129_, 5, v_congrInfo_115_);
lean_ctor_set(v_reuseFailAlloc_129_, 6, v_defEqI_116_);
lean_ctor_set(v_reuseFailAlloc_129_, 7, v_extensions_117_);
lean_ctor_set_uint8(v_reuseFailAlloc_129_, sizeof(void*)*8, v_debug_118_);
v___x_124_ = v_reuseFailAlloc_129_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
lean_object* v___x_125_; lean_object* v___x_127_; 
v___x_125_ = lean_st_ref_set(v_a_81_, v___x_124_);
if (v_isShared_108_ == 0)
{
v___x_127_ = v___x_107_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_a_105_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___boxed(lean_object* v_e_134_, lean_object* v_k_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check(v_e_134_, v_k_135_, v_a_136_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_);
lean_dec(v_a_141_);
lean_dec_ref(v_a_140_);
lean_dec(v_a_139_);
lean_dec_ref(v_a_138_);
lean_dec(v_a_137_);
lean_dec_ref(v_a_136_);
return v_res_143_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0(void){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2(lean_object* v_msg_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v___x_153_; lean_object* v___x_4694__overap_154_; lean_object* v___x_155_; 
v___x_153_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0, &l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0);
v___x_4694__overap_154_ = lean_panic_fn(v___x_153_, v_msg_145_);
lean_inc(v___y_151_);
lean_inc_ref(v___y_150_);
lean_inc(v___y_149_);
lean_inc_ref(v___y_148_);
lean_inc(v___y_147_);
lean_inc_ref(v___y_146_);
v___x_155_ = lean_apply_7(v___x_4694__overap_154_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, lean_box(0));
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___boxed(lean_object* v_msg_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2(v_msg_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
lean_dec(v___y_158_);
lean_dec_ref(v___y_157_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_165_, lean_object* v_x_166_, lean_object* v_x_167_, lean_object* v_x_168_){
_start:
{
lean_object* v_ks_169_; lean_object* v_vs_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_194_; 
v_ks_169_ = lean_ctor_get(v_x_165_, 0);
v_vs_170_ = lean_ctor_get(v_x_165_, 1);
v_isSharedCheck_194_ = !lean_is_exclusive(v_x_165_);
if (v_isSharedCheck_194_ == 0)
{
v___x_172_ = v_x_165_;
v_isShared_173_ = v_isSharedCheck_194_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_vs_170_);
lean_inc(v_ks_169_);
lean_dec(v_x_165_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_194_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_174_ = lean_array_get_size(v_ks_169_);
v___x_175_ = lean_nat_dec_lt(v_x_166_, v___x_174_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_179_; 
lean_dec(v_x_166_);
v___x_176_ = lean_array_push(v_ks_169_, v_x_167_);
v___x_177_ = lean_array_push(v_vs_170_, v_x_168_);
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 1, v___x_177_);
lean_ctor_set(v___x_172_, 0, v___x_176_);
v___x_179_ = v___x_172_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_176_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v___x_177_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
else
{
lean_object* v_k_x27_181_; uint8_t v___x_182_; 
v_k_x27_181_ = lean_array_fget_borrowed(v_ks_169_, v_x_166_);
v___x_182_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_167_, v_k_x27_181_);
if (v___x_182_ == 0)
{
lean_object* v___x_184_; 
if (v_isShared_173_ == 0)
{
v___x_184_ = v___x_172_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_ks_169_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v_vs_170_);
v___x_184_ = v_reuseFailAlloc_188_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = lean_unsigned_to_nat(1u);
v___x_186_ = lean_nat_add(v_x_166_, v___x_185_);
lean_dec(v_x_166_);
v_x_165_ = v___x_184_;
v_x_166_ = v___x_186_;
goto _start;
}
}
else
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_192_; 
v___x_189_ = lean_array_fset(v_ks_169_, v_x_166_, v_x_167_);
v___x_190_ = lean_array_fset(v_vs_170_, v_x_166_, v_x_168_);
lean_dec(v_x_166_);
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 1, v___x_190_);
lean_ctor_set(v___x_172_, 0, v___x_189_);
v___x_192_ = v___x_172_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_189_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v___x_190_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(lean_object* v_n_195_, lean_object* v_k_196_, lean_object* v_v_197_){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = lean_unsigned_to_nat(0u);
v___x_199_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_n_195_, v___x_198_, v_k_196_, v_v_197_);
return v___x_199_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_200_; size_t v___x_201_; size_t v___x_202_; 
v___x_200_ = ((size_t)5ULL);
v___x_201_ = ((size_t)1ULL);
v___x_202_ = lean_usize_shift_left(v___x_201_, v___x_200_);
return v___x_202_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_203_; size_t v___x_204_; size_t v___x_205_; 
v___x_203_ = ((size_t)1ULL);
v___x_204_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0);
v___x_205_ = lean_usize_sub(v___x_204_, v___x_203_);
return v___x_205_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(lean_object* v_x_207_, size_t v_x_208_, size_t v_x_209_, lean_object* v_x_210_, lean_object* v_x_211_){
_start:
{
if (lean_obj_tag(v_x_207_) == 0)
{
lean_object* v_es_212_; size_t v___x_213_; size_t v___x_214_; size_t v___x_215_; size_t v___x_216_; lean_object* v_j_217_; lean_object* v___x_218_; uint8_t v___x_219_; 
v_es_212_ = lean_ctor_get(v_x_207_, 0);
v___x_213_ = ((size_t)5ULL);
v___x_214_ = ((size_t)1ULL);
v___x_215_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1);
v___x_216_ = lean_usize_land(v_x_208_, v___x_215_);
v_j_217_ = lean_usize_to_nat(v___x_216_);
v___x_218_ = lean_array_get_size(v_es_212_);
v___x_219_ = lean_nat_dec_lt(v_j_217_, v___x_218_);
if (v___x_219_ == 0)
{
lean_dec(v_j_217_);
lean_dec(v_x_211_);
lean_dec_ref(v_x_210_);
return v_x_207_;
}
else
{
lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_256_; 
lean_inc_ref(v_es_212_);
v_isSharedCheck_256_ = !lean_is_exclusive(v_x_207_);
if (v_isSharedCheck_256_ == 0)
{
lean_object* v_unused_257_; 
v_unused_257_ = lean_ctor_get(v_x_207_, 0);
lean_dec(v_unused_257_);
v___x_221_ = v_x_207_;
v_isShared_222_ = v_isSharedCheck_256_;
goto v_resetjp_220_;
}
else
{
lean_dec(v_x_207_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_256_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v_v_223_; lean_object* v___x_224_; lean_object* v_xs_x27_225_; lean_object* v___y_227_; 
v_v_223_ = lean_array_fget(v_es_212_, v_j_217_);
v___x_224_ = lean_box(0);
v_xs_x27_225_ = lean_array_fset(v_es_212_, v_j_217_, v___x_224_);
switch(lean_obj_tag(v_v_223_))
{
case 0:
{
lean_object* v_key_232_; lean_object* v_val_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_243_; 
v_key_232_ = lean_ctor_get(v_v_223_, 0);
v_val_233_ = lean_ctor_get(v_v_223_, 1);
v_isSharedCheck_243_ = !lean_is_exclusive(v_v_223_);
if (v_isSharedCheck_243_ == 0)
{
v___x_235_ = v_v_223_;
v_isShared_236_ = v_isSharedCheck_243_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_val_233_);
lean_inc(v_key_232_);
lean_dec(v_v_223_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_243_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
uint8_t v___x_237_; 
v___x_237_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_210_, v_key_232_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; lean_object* v___x_239_; 
lean_del_object(v___x_235_);
v___x_238_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_232_, v_val_233_, v_x_210_, v_x_211_);
v___x_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
v___y_227_ = v___x_239_;
goto v___jp_226_;
}
else
{
lean_object* v___x_241_; 
lean_dec(v_val_233_);
lean_dec(v_key_232_);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 1, v_x_211_);
lean_ctor_set(v___x_235_, 0, v_x_210_);
v___x_241_ = v___x_235_;
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
v___y_227_ = v___x_241_;
goto v___jp_226_;
}
}
}
}
case 1:
{
lean_object* v_node_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_254_; 
v_node_244_ = lean_ctor_get(v_v_223_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v_v_223_);
if (v_isSharedCheck_254_ == 0)
{
v___x_246_ = v_v_223_;
v_isShared_247_ = v_isSharedCheck_254_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_node_244_);
lean_dec(v_v_223_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_254_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
size_t v___x_248_; size_t v___x_249_; lean_object* v___x_250_; lean_object* v___x_252_; 
v___x_248_ = lean_usize_shift_right(v_x_208_, v___x_213_);
v___x_249_ = lean_usize_add(v_x_209_, v___x_214_);
v___x_250_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_node_244_, v___x_248_, v___x_249_, v_x_210_, v_x_211_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 0, v___x_250_);
v___x_252_ = v___x_246_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_250_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
v___y_227_ = v___x_252_;
goto v___jp_226_;
}
}
}
default: 
{
lean_object* v___x_255_; 
v___x_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_255_, 0, v_x_210_);
lean_ctor_set(v___x_255_, 1, v_x_211_);
v___y_227_ = v___x_255_;
goto v___jp_226_;
}
}
v___jp_226_:
{
lean_object* v___x_228_; lean_object* v___x_230_; 
v___x_228_ = lean_array_fset(v_xs_x27_225_, v_j_217_, v___y_227_);
lean_dec(v_j_217_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_228_);
v___x_230_ = v___x_221_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_228_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
}
}
else
{
lean_object* v_ks_258_; lean_object* v_vs_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_279_; 
v_ks_258_ = lean_ctor_get(v_x_207_, 0);
v_vs_259_ = lean_ctor_get(v_x_207_, 1);
v_isSharedCheck_279_ = !lean_is_exclusive(v_x_207_);
if (v_isSharedCheck_279_ == 0)
{
v___x_261_ = v_x_207_;
v_isShared_262_ = v_isSharedCheck_279_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_vs_259_);
lean_inc(v_ks_258_);
lean_dec(v_x_207_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_279_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_262_ == 0)
{
v___x_264_ = v___x_261_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_ks_258_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v_vs_259_);
v___x_264_ = v_reuseFailAlloc_278_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
lean_object* v_newNode_265_; uint8_t v___y_267_; size_t v___x_273_; uint8_t v___x_274_; 
v_newNode_265_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(v___x_264_, v_x_210_, v_x_211_);
v___x_273_ = ((size_t)7ULL);
v___x_274_ = lean_usize_dec_le(v___x_273_, v_x_209_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; lean_object* v___x_276_; uint8_t v___x_277_; 
v___x_275_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_265_);
v___x_276_ = lean_unsigned_to_nat(4u);
v___x_277_ = lean_nat_dec_lt(v___x_275_, v___x_276_);
lean_dec(v___x_275_);
v___y_267_ = v___x_277_;
goto v___jp_266_;
}
else
{
v___y_267_ = v___x_274_;
goto v___jp_266_;
}
v___jp_266_:
{
if (v___y_267_ == 0)
{
lean_object* v_ks_268_; lean_object* v_vs_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v_ks_268_ = lean_ctor_get(v_newNode_265_, 0);
lean_inc_ref(v_ks_268_);
v_vs_269_ = lean_ctor_get(v_newNode_265_, 1);
lean_inc_ref(v_vs_269_);
lean_dec_ref(v_newNode_265_);
v___x_270_ = lean_unsigned_to_nat(0u);
v___x_271_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__2);
v___x_272_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(v_x_209_, v_ks_268_, v_vs_269_, v___x_270_, v___x_271_);
lean_dec_ref(v_vs_269_);
lean_dec_ref(v_ks_268_);
return v___x_272_;
}
else
{
return v_newNode_265_;
}
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
lean_object* v_k_287_; lean_object* v_v_288_; uint64_t v___x_289_; size_t v_h_290_; size_t v___x_291_; lean_object* v___x_292_; size_t v___x_293_; size_t v___x_294_; size_t v___x_295_; size_t v_h_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v_k_287_ = lean_array_fget_borrowed(v_keys_281_, v_i_283_);
v_v_288_ = lean_array_fget_borrowed(v_vals_282_, v_i_283_);
v___x_289_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_287_);
v_h_290_ = lean_uint64_to_usize(v___x_289_);
v___x_291_ = ((size_t)5ULL);
v___x_292_ = lean_unsigned_to_nat(1u);
v___x_293_ = ((size_t)1ULL);
v___x_294_ = lean_usize_sub(v_depth_280_, v___x_293_);
v___x_295_ = lean_usize_mul(v___x_291_, v___x_294_);
v_h_296_ = lean_usize_shift_right(v_h_290_, v___x_295_);
v___x_297_ = lean_nat_add(v_i_283_, v___x_292_);
lean_dec(v_i_283_);
lean_inc(v_v_288_);
lean_inc(v_k_287_);
v___x_298_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_entries_284_, v_h_296_, v_depth_280_, v_k_287_, v_v_288_);
v_i_283_ = v___x_297_;
v_entries_284_ = v___x_298_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_300_, lean_object* v_keys_301_, lean_object* v_vals_302_, lean_object* v_i_303_, lean_object* v_entries_304_){
_start:
{
size_t v_depth_boxed_305_; lean_object* v_res_306_; 
v_depth_boxed_305_ = lean_unbox_usize(v_depth_300_);
lean_dec(v_depth_300_);
v_res_306_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(v_depth_boxed_305_, v_keys_301_, v_vals_302_, v_i_303_, v_entries_304_);
lean_dec_ref(v_vals_302_);
lean_dec_ref(v_keys_301_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_307_, lean_object* v_x_308_, lean_object* v_x_309_, lean_object* v_x_310_, lean_object* v_x_311_){
_start:
{
size_t v_x_5187__boxed_312_; size_t v_x_5188__boxed_313_; lean_object* v_res_314_; 
v_x_5187__boxed_312_ = lean_unbox_usize(v_x_308_);
lean_dec(v_x_308_);
v_x_5188__boxed_313_ = lean_unbox_usize(v_x_309_);
lean_dec(v_x_309_);
v_res_314_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_307_, v_x_5187__boxed_312_, v_x_5188__boxed_313_, v_x_310_, v_x_311_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(lean_object* v_x_315_, lean_object* v_x_316_, lean_object* v_x_317_){
_start:
{
uint64_t v___x_318_; size_t v___x_319_; size_t v___x_320_; lean_object* v___x_321_; 
v___x_318_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_316_);
v___x_319_ = lean_uint64_to_usize(v___x_318_);
v___x_320_ = ((size_t)1ULL);
v___x_321_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_315_, v___x_319_, v___x_320_, v_x_316_, v_x_317_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(lean_object* v_keys_322_, lean_object* v_vals_323_, lean_object* v_i_324_, lean_object* v_k_325_){
_start:
{
lean_object* v___x_326_; uint8_t v___x_327_; 
v___x_326_ = lean_array_get_size(v_keys_322_);
v___x_327_ = lean_nat_dec_lt(v_i_324_, v___x_326_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; 
lean_dec(v_i_324_);
v___x_328_ = lean_box(0);
return v___x_328_;
}
else
{
lean_object* v_k_x27_329_; uint8_t v___x_330_; 
v_k_x27_329_ = lean_array_fget_borrowed(v_keys_322_, v_i_324_);
v___x_330_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_325_, v_k_x27_329_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = lean_unsigned_to_nat(1u);
v___x_332_ = lean_nat_add(v_i_324_, v___x_331_);
lean_dec(v_i_324_);
v_i_324_ = v___x_332_;
goto _start;
}
else
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = lean_array_fget_borrowed(v_vals_323_, v_i_324_);
lean_dec(v_i_324_);
lean_inc(v___x_334_);
v___x_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
return v___x_335_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_keys_336_, lean_object* v_vals_337_, lean_object* v_i_338_, lean_object* v_k_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_keys_336_, v_vals_337_, v_i_338_, v_k_339_);
lean_dec_ref(v_k_339_);
lean_dec_ref(v_vals_337_);
lean_dec_ref(v_keys_336_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(lean_object* v_x_341_, size_t v_x_342_, lean_object* v_x_343_){
_start:
{
if (lean_obj_tag(v_x_341_) == 0)
{
lean_object* v_es_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_365_; 
v_es_344_ = lean_ctor_get(v_x_341_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v_x_341_);
if (v_isSharedCheck_365_ == 0)
{
v___x_346_ = v_x_341_;
v_isShared_347_ = v_isSharedCheck_365_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_es_344_);
lean_dec(v_x_341_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_365_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_348_; size_t v___x_349_; size_t v___x_350_; size_t v___x_351_; lean_object* v_j_352_; lean_object* v___x_353_; 
v___x_348_ = lean_box(2);
v___x_349_ = ((size_t)5ULL);
v___x_350_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1);
v___x_351_ = lean_usize_land(v_x_342_, v___x_350_);
v_j_352_ = lean_usize_to_nat(v___x_351_);
v___x_353_ = lean_array_get(v___x_348_, v_es_344_, v_j_352_);
lean_dec(v_j_352_);
lean_dec_ref(v_es_344_);
switch(lean_obj_tag(v___x_353_))
{
case 0:
{
lean_object* v_key_354_; lean_object* v_val_355_; uint8_t v___x_356_; 
v_key_354_ = lean_ctor_get(v___x_353_, 0);
lean_inc(v_key_354_);
v_val_355_ = lean_ctor_get(v___x_353_, 1);
lean_inc(v_val_355_);
lean_dec_ref(v___x_353_);
v___x_356_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_343_, v_key_354_);
lean_dec(v_key_354_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; 
lean_dec(v_val_355_);
lean_del_object(v___x_346_);
v___x_357_ = lean_box(0);
return v___x_357_;
}
else
{
lean_object* v___x_359_; 
if (v_isShared_347_ == 0)
{
lean_ctor_set_tag(v___x_346_, 1);
lean_ctor_set(v___x_346_, 0, v_val_355_);
v___x_359_ = v___x_346_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_val_355_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
case 1:
{
lean_object* v_node_361_; size_t v___x_362_; 
lean_del_object(v___x_346_);
v_node_361_ = lean_ctor_get(v___x_353_, 0);
lean_inc(v_node_361_);
lean_dec_ref(v___x_353_);
v___x_362_ = lean_usize_shift_right(v_x_342_, v___x_349_);
v_x_341_ = v_node_361_;
v_x_342_ = v___x_362_;
goto _start;
}
default: 
{
lean_object* v___x_364_; 
lean_del_object(v___x_346_);
v___x_364_ = lean_box(0);
return v___x_364_;
}
}
}
}
else
{
lean_object* v_ks_366_; lean_object* v_vs_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v_ks_366_ = lean_ctor_get(v_x_341_, 0);
lean_inc_ref(v_ks_366_);
v_vs_367_ = lean_ctor_get(v_x_341_, 1);
lean_inc_ref(v_vs_367_);
lean_dec_ref(v_x_341_);
v___x_368_ = lean_unsigned_to_nat(0u);
v___x_369_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_ks_366_, v_vs_367_, v___x_368_, v_x_343_);
lean_dec_ref(v_vs_367_);
lean_dec_ref(v_ks_366_);
return v___x_369_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_x_370_, lean_object* v_x_371_, lean_object* v_x_372_){
_start:
{
size_t v_x_5387__boxed_373_; lean_object* v_res_374_; 
v_x_5387__boxed_373_ = lean_unbox_usize(v_x_371_);
lean_dec(v_x_371_);
v_res_374_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_370_, v_x_5387__boxed_373_, v_x_372_);
lean_dec_ref(v_x_372_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(lean_object* v_x_375_, lean_object* v_x_376_){
_start:
{
uint64_t v___x_377_; size_t v___x_378_; lean_object* v___x_379_; 
v___x_377_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_376_);
v___x_378_ = lean_uint64_to_usize(v___x_377_);
v___x_379_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_375_, v___x_378_, v_x_376_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg___boxed(lean_object* v_x_380_, lean_object* v_x_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_x_380_, v_x_381_);
lean_dec_ref(v_x_381_);
return v_res_382_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3(void){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_386_ = ((lean_object*)(l_Lean_Meta_Sym_getMaxFVar_x3f___closed__2));
v___x_387_ = lean_unsigned_to_nat(37u);
v___x_388_ = lean_unsigned_to_nat(52u);
v___x_389_ = ((lean_object*)(l_Lean_Meta_Sym_getMaxFVar_x3f___closed__1));
v___x_390_ = ((lean_object*)(l_Lean_Meta_Sym_getMaxFVar_x3f___closed__0));
v___x_391_ = l_mkPanicMessageWithDecl(v___x_390_, v___x_389_, v___x_388_, v___x_387_, v___x_386_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f(lean_object* v_e_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_){
_start:
{
lean_object* v___y_401_; lean_object* v_a_430_; lean_object* v___y_452_; lean_object* v___y_453_; lean_object* v___y_482_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v___y_485_; lean_object* v___y_486_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v___y_489_; uint8_t v___y_490_; lean_object* v_d_510_; lean_object* v_b_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_521_; 
switch(lean_obj_tag(v_e_392_))
{
case 1:
{
lean_object* v_fvarId_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v_fvarId_549_ = lean_ctor_get(v_e_392_, 0);
lean_inc(v_fvarId_549_);
lean_dec_ref(v_e_392_);
v___x_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_550_, 0, v_fvarId_549_);
v___x_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
return v___x_551_;
}
case 2:
{
lean_object* v_mvarId_552_; uint8_t v___y_554_; uint8_t v___x_595_; 
v_mvarId_552_ = lean_ctor_get(v_e_392_, 0);
v___x_595_ = l_Lean_Expr_hasFVar(v_e_392_);
if (v___x_595_ == 0)
{
uint8_t v___x_596_; 
v___x_596_ = l_Lean_Expr_hasMVar(v_e_392_);
v___y_554_ = v___x_596_;
goto v___jp_553_;
}
else
{
v___y_554_ = v___x_595_;
goto v___jp_553_;
}
v___jp_553_:
{
if (v___y_554_ == 0)
{
lean_object* v___x_555_; lean_object* v___x_556_; 
lean_dec_ref(v_e_392_);
v___x_555_ = lean_box(0);
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
return v___x_556_;
}
else
{
lean_object* v___x_557_; lean_object* v_maxFVar_558_; lean_object* v___x_559_; 
v___x_557_ = lean_st_ref_get(v_a_394_);
v_maxFVar_558_ = lean_ctor_get(v___x_557_, 1);
lean_inc_ref(v_maxFVar_558_);
lean_dec(v___x_557_);
v___x_559_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_558_, v_e_392_);
if (lean_obj_tag(v___x_559_) == 1)
{
lean_object* v_val_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
lean_dec_ref(v_e_392_);
v_val_560_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_567_ == 0)
{
v___x_562_ = v___x_559_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_val_560_);
lean_dec(v___x_559_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
lean_ctor_set_tag(v___x_562_, 0);
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_val_560_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
else
{
lean_object* v___x_568_; 
lean_dec(v___x_559_);
lean_inc(v_mvarId_552_);
v___x_568_ = l_Lean_MVarId_getDecl(v_mvarId_552_, v_a_395_, v_a_396_, v_a_397_, v_a_398_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_569_; lean_object* v_lctx_570_; lean_object* v_decls_571_; uint8_t v___x_572_; 
v_a_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_a_569_);
lean_dec_ref(v___x_568_);
v_lctx_570_ = lean_ctor_get(v_a_569_, 1);
lean_inc_ref(v_lctx_570_);
lean_dec(v_a_569_);
v_decls_571_ = lean_ctor_get(v_lctx_570_, 1);
v___x_572_ = l_Lean_PersistentArray_isEmpty___redArg(v_decls_571_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; 
v___x_573_ = l_Lean_LocalContext_lastDecl(v_lctx_570_);
if (lean_obj_tag(v___x_573_) == 1)
{
lean_object* v_val_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_582_; 
v_val_574_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_582_ == 0)
{
v___x_576_ = v___x_573_;
v_isShared_577_ = v_isSharedCheck_582_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_val_574_);
lean_dec(v___x_573_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_582_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_578_; lean_object* v___x_580_; 
v___x_578_ = l_Lean_LocalDecl_fvarId(v_val_574_);
lean_dec(v_val_574_);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 0, v___x_578_);
v___x_580_ = v___x_576_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_578_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
v_a_430_ = v___x_580_;
goto v___jp_429_;
}
}
}
else
{
lean_object* v___x_583_; lean_object* v___x_584_; 
lean_dec(v___x_573_);
v___x_583_ = lean_obj_once(&l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3, &l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3_once, _init_l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3);
v___x_584_ = l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2(v___x_583_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v_a_585_; 
v_a_585_ = lean_ctor_get(v___x_584_, 0);
lean_inc(v_a_585_);
lean_dec_ref(v___x_584_);
v_a_430_ = v_a_585_;
goto v___jp_429_;
}
else
{
lean_dec_ref(v_e_392_);
return v___x_584_;
}
}
}
else
{
lean_object* v___x_586_; 
lean_dec_ref(v_lctx_570_);
v___x_586_ = lean_box(0);
v_a_430_ = v___x_586_;
goto v___jp_429_;
}
}
else
{
lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_594_; 
lean_dec_ref(v_e_392_);
v_a_587_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_594_ == 0)
{
v___x_589_ = v___x_568_;
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v___x_568_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_592_; 
if (v_isShared_590_ == 0)
{
v___x_592_ = v___x_589_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_a_587_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
}
}
}
case 5:
{
lean_object* v_fn_597_; lean_object* v_arg_598_; uint8_t v___y_600_; uint8_t v___x_619_; 
v_fn_597_ = lean_ctor_get(v_e_392_, 0);
v_arg_598_ = lean_ctor_get(v_e_392_, 1);
v___x_619_ = l_Lean_Expr_hasFVar(v_e_392_);
if (v___x_619_ == 0)
{
uint8_t v___x_620_; 
v___x_620_ = l_Lean_Expr_hasMVar(v_e_392_);
v___y_600_ = v___x_620_;
goto v___jp_599_;
}
else
{
v___y_600_ = v___x_619_;
goto v___jp_599_;
}
v___jp_599_:
{
if (v___y_600_ == 0)
{
lean_object* v___x_601_; lean_object* v___x_602_; 
lean_dec_ref(v_e_392_);
v___x_601_ = lean_box(0);
v___x_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
return v___x_602_;
}
else
{
lean_object* v___x_603_; lean_object* v_maxFVar_604_; lean_object* v___x_605_; 
v___x_603_ = lean_st_ref_get(v_a_394_);
v_maxFVar_604_ = lean_ctor_get(v___x_603_, 1);
lean_inc_ref(v_maxFVar_604_);
lean_dec(v___x_603_);
v___x_605_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_604_, v_e_392_);
if (lean_obj_tag(v___x_605_) == 1)
{
lean_object* v_val_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
lean_dec_ref(v_e_392_);
v_val_606_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_605_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_val_606_);
lean_dec(v___x_605_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
lean_ctor_set_tag(v___x_608_, 0);
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_val_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
else
{
lean_object* v___x_614_; 
lean_dec(v___x_605_);
lean_inc_ref(v_fn_597_);
v___x_614_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_fn_597_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; lean_object* v___x_616_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_a_615_);
lean_dec_ref(v___x_614_);
lean_inc_ref(v_arg_598_);
v___x_616_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_arg_598_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_);
if (lean_obj_tag(v___x_616_) == 0)
{
lean_object* v_a_617_; lean_object* v___x_618_; 
v_a_617_ = lean_ctor_get(v___x_616_, 0);
lean_inc(v_a_617_);
lean_dec_ref(v___x_616_);
v___x_618_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_615_, v_a_617_, v_a_395_, v_a_397_, v_a_398_);
v___y_521_ = v___x_618_;
goto v___jp_520_;
}
else
{
lean_dec(v_a_615_);
v___y_521_ = v___x_616_;
goto v___jp_520_;
}
}
else
{
v___y_521_ = v___x_614_;
goto v___jp_520_;
}
}
}
}
}
case 6:
{
lean_object* v_binderType_621_; lean_object* v_body_622_; 
v_binderType_621_ = lean_ctor_get(v_e_392_, 1);
v_body_622_ = lean_ctor_get(v_e_392_, 2);
lean_inc_ref(v_body_622_);
lean_inc_ref(v_binderType_621_);
v_d_510_ = v_binderType_621_;
v_b_511_ = v_body_622_;
v___y_512_ = v_a_393_;
v___y_513_ = v_a_394_;
v___y_514_ = v_a_395_;
v___y_515_ = v_a_396_;
v___y_516_ = v_a_397_;
v___y_517_ = v_a_398_;
goto v___jp_509_;
}
case 7:
{
lean_object* v_binderType_623_; lean_object* v_body_624_; 
v_binderType_623_ = lean_ctor_get(v_e_392_, 1);
v_body_624_ = lean_ctor_get(v_e_392_, 2);
lean_inc_ref(v_body_624_);
lean_inc_ref(v_binderType_623_);
v_d_510_ = v_binderType_623_;
v_b_511_ = v_body_624_;
v___y_512_ = v_a_393_;
v___y_513_ = v_a_394_;
v___y_514_ = v_a_395_;
v___y_515_ = v_a_396_;
v___y_516_ = v_a_397_;
v___y_517_ = v_a_398_;
goto v___jp_509_;
}
case 8:
{
lean_object* v_type_625_; lean_object* v_value_626_; lean_object* v_body_627_; uint8_t v___y_629_; uint8_t v___x_652_; 
v_type_625_ = lean_ctor_get(v_e_392_, 1);
v_value_626_ = lean_ctor_get(v_e_392_, 2);
v_body_627_ = lean_ctor_get(v_e_392_, 3);
v___x_652_ = l_Lean_Expr_hasFVar(v_e_392_);
if (v___x_652_ == 0)
{
uint8_t v___x_653_; 
v___x_653_ = l_Lean_Expr_hasMVar(v_e_392_);
v___y_629_ = v___x_653_;
goto v___jp_628_;
}
else
{
v___y_629_ = v___x_652_;
goto v___jp_628_;
}
v___jp_628_:
{
if (v___y_629_ == 0)
{
lean_object* v___x_630_; lean_object* v___x_631_; 
lean_dec_ref(v_e_392_);
v___x_630_ = lean_box(0);
v___x_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
return v___x_631_;
}
else
{
lean_object* v___x_632_; lean_object* v_maxFVar_633_; lean_object* v___x_634_; 
v___x_632_ = lean_st_ref_get(v_a_394_);
v_maxFVar_633_ = lean_ctor_get(v___x_632_, 1);
lean_inc_ref(v_maxFVar_633_);
lean_dec(v___x_632_);
v___x_634_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_633_, v_e_392_);
if (lean_obj_tag(v___x_634_) == 1)
{
lean_object* v_val_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_642_; 
lean_dec_ref(v_e_392_);
v_val_635_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_642_ == 0)
{
v___x_637_ = v___x_634_;
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_val_635_);
lean_dec(v___x_634_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_640_; 
if (v_isShared_638_ == 0)
{
lean_ctor_set_tag(v___x_637_, 0);
v___x_640_ = v___x_637_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_val_635_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
else
{
lean_object* v___x_643_; 
lean_dec(v___x_634_);
lean_inc_ref(v_type_625_);
v___x_643_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_type_625_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v_a_644_; lean_object* v___x_645_; 
v_a_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_a_644_);
lean_dec_ref(v___x_643_);
lean_inc_ref(v_value_626_);
v___x_645_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_value_626_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v_a_646_; lean_object* v___x_647_; 
v_a_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_a_646_);
lean_dec_ref(v___x_645_);
v___x_647_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_644_, v_a_646_, v_a_395_, v_a_397_, v_a_398_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; lean_object* v___x_649_; 
v_a_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc(v_a_648_);
lean_dec_ref(v___x_647_);
lean_inc_ref(v_body_627_);
v___x_649_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_body_627_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_a_650_; lean_object* v___x_651_; 
v_a_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_a_650_);
lean_dec_ref(v___x_649_);
v___x_651_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_648_, v_a_650_, v_a_395_, v_a_397_, v_a_398_);
v___y_401_ = v___x_651_;
goto v___jp_400_;
}
else
{
lean_dec(v_a_648_);
v___y_401_ = v___x_649_;
goto v___jp_400_;
}
}
else
{
v___y_401_ = v___x_647_;
goto v___jp_400_;
}
}
else
{
lean_dec(v_a_644_);
v___y_401_ = v___x_645_;
goto v___jp_400_;
}
}
else
{
v___y_401_ = v___x_643_;
goto v___jp_400_;
}
}
}
}
}
case 10:
{
lean_object* v_expr_654_; uint8_t v___y_656_; uint8_t v___x_698_; 
v_expr_654_ = lean_ctor_get(v_e_392_, 1);
lean_inc_ref(v_expr_654_);
lean_dec_ref(v_e_392_);
v___x_698_ = l_Lean_Expr_hasFVar(v_expr_654_);
if (v___x_698_ == 0)
{
uint8_t v___x_699_; 
v___x_699_ = l_Lean_Expr_hasMVar(v_expr_654_);
v___y_656_ = v___x_699_;
goto v___jp_655_;
}
else
{
v___y_656_ = v___x_698_;
goto v___jp_655_;
}
v___jp_655_:
{
if (v___y_656_ == 0)
{
lean_object* v___x_657_; lean_object* v___x_658_; 
lean_dec_ref(v_expr_654_);
v___x_657_ = lean_box(0);
v___x_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
return v___x_658_;
}
else
{
lean_object* v___x_659_; lean_object* v_maxFVar_660_; lean_object* v___x_661_; 
v___x_659_ = lean_st_ref_get(v_a_394_);
v_maxFVar_660_ = lean_ctor_get(v___x_659_, 1);
lean_inc_ref(v_maxFVar_660_);
lean_dec(v___x_659_);
v___x_661_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_660_, v_expr_654_);
if (lean_obj_tag(v___x_661_) == 1)
{
lean_object* v_val_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
lean_dec_ref(v_expr_654_);
v_val_662_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___x_661_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_val_662_);
lean_dec(v___x_661_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
lean_ctor_set_tag(v___x_664_, 0);
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_val_662_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
else
{
lean_object* v___x_670_; 
lean_dec(v___x_661_);
lean_inc_ref(v_expr_654_);
v___x_670_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_expr_654_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_697_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_697_ == 0)
{
v___x_673_ = v___x_670_;
v_isShared_674_ = v_isSharedCheck_697_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_670_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_697_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_675_; lean_object* v_share_676_; lean_object* v_maxFVar_677_; lean_object* v_proofInstInfo_678_; lean_object* v_inferType_679_; lean_object* v_getLevel_680_; lean_object* v_congrInfo_681_; lean_object* v_defEqI_682_; lean_object* v_extensions_683_; uint8_t v_debug_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_696_; 
v___x_675_ = lean_st_ref_take(v_a_394_);
v_share_676_ = lean_ctor_get(v___x_675_, 0);
v_maxFVar_677_ = lean_ctor_get(v___x_675_, 1);
v_proofInstInfo_678_ = lean_ctor_get(v___x_675_, 2);
v_inferType_679_ = lean_ctor_get(v___x_675_, 3);
v_getLevel_680_ = lean_ctor_get(v___x_675_, 4);
v_congrInfo_681_ = lean_ctor_get(v___x_675_, 5);
v_defEqI_682_ = lean_ctor_get(v___x_675_, 6);
v_extensions_683_ = lean_ctor_get(v___x_675_, 7);
v_debug_684_ = lean_ctor_get_uint8(v___x_675_, sizeof(void*)*8);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_696_ == 0)
{
v___x_686_ = v___x_675_;
v_isShared_687_ = v_isSharedCheck_696_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_extensions_683_);
lean_inc(v_defEqI_682_);
lean_inc(v_congrInfo_681_);
lean_inc(v_getLevel_680_);
lean_inc(v_inferType_679_);
lean_inc(v_proofInstInfo_678_);
lean_inc(v_maxFVar_677_);
lean_inc(v_share_676_);
lean_dec(v___x_675_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_696_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v___x_690_; 
lean_inc(v_a_671_);
v___x_688_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_677_, v_expr_654_, v_a_671_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 1, v___x_688_);
v___x_690_ = v___x_686_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_share_676_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v___x_688_);
lean_ctor_set(v_reuseFailAlloc_695_, 2, v_proofInstInfo_678_);
lean_ctor_set(v_reuseFailAlloc_695_, 3, v_inferType_679_);
lean_ctor_set(v_reuseFailAlloc_695_, 4, v_getLevel_680_);
lean_ctor_set(v_reuseFailAlloc_695_, 5, v_congrInfo_681_);
lean_ctor_set(v_reuseFailAlloc_695_, 6, v_defEqI_682_);
lean_ctor_set(v_reuseFailAlloc_695_, 7, v_extensions_683_);
lean_ctor_set_uint8(v_reuseFailAlloc_695_, sizeof(void*)*8, v_debug_684_);
v___x_690_ = v_reuseFailAlloc_695_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
lean_object* v___x_691_; lean_object* v___x_693_; 
v___x_691_ = lean_st_ref_set(v_a_394_, v___x_690_);
if (v_isShared_674_ == 0)
{
v___x_693_ = v___x_673_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_a_671_);
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
lean_dec_ref(v_expr_654_);
return v___x_670_;
}
}
}
}
}
case 11:
{
lean_object* v_struct_700_; uint8_t v___y_702_; uint8_t v___x_744_; 
v_struct_700_ = lean_ctor_get(v_e_392_, 2);
v___x_744_ = l_Lean_Expr_hasFVar(v_e_392_);
if (v___x_744_ == 0)
{
uint8_t v___x_745_; 
v___x_745_ = l_Lean_Expr_hasMVar(v_e_392_);
v___y_702_ = v___x_745_;
goto v___jp_701_;
}
else
{
v___y_702_ = v___x_744_;
goto v___jp_701_;
}
v___jp_701_:
{
if (v___y_702_ == 0)
{
lean_object* v___x_703_; lean_object* v___x_704_; 
lean_dec_ref(v_e_392_);
v___x_703_ = lean_box(0);
v___x_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
return v___x_704_;
}
else
{
lean_object* v___x_705_; lean_object* v_maxFVar_706_; lean_object* v___x_707_; 
v___x_705_ = lean_st_ref_get(v_a_394_);
v_maxFVar_706_ = lean_ctor_get(v___x_705_, 1);
lean_inc_ref(v_maxFVar_706_);
lean_dec(v___x_705_);
v___x_707_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_706_, v_e_392_);
if (lean_obj_tag(v___x_707_) == 1)
{
lean_object* v_val_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
lean_dec_ref(v_e_392_);
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
v___x_716_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_struct_700_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_743_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_743_ == 0)
{
v___x_719_ = v___x_716_;
v_isShared_720_ = v_isSharedCheck_743_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_716_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_743_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_721_; lean_object* v_share_722_; lean_object* v_maxFVar_723_; lean_object* v_proofInstInfo_724_; lean_object* v_inferType_725_; lean_object* v_getLevel_726_; lean_object* v_congrInfo_727_; lean_object* v_defEqI_728_; lean_object* v_extensions_729_; uint8_t v_debug_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_742_; 
v___x_721_ = lean_st_ref_take(v_a_394_);
v_share_722_ = lean_ctor_get(v___x_721_, 0);
v_maxFVar_723_ = lean_ctor_get(v___x_721_, 1);
v_proofInstInfo_724_ = lean_ctor_get(v___x_721_, 2);
v_inferType_725_ = lean_ctor_get(v___x_721_, 3);
v_getLevel_726_ = lean_ctor_get(v___x_721_, 4);
v_congrInfo_727_ = lean_ctor_get(v___x_721_, 5);
v_defEqI_728_ = lean_ctor_get(v___x_721_, 6);
v_extensions_729_ = lean_ctor_get(v___x_721_, 7);
v_debug_730_ = lean_ctor_get_uint8(v___x_721_, sizeof(void*)*8);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_742_ == 0)
{
v___x_732_ = v___x_721_;
v_isShared_733_ = v_isSharedCheck_742_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_extensions_729_);
lean_inc(v_defEqI_728_);
lean_inc(v_congrInfo_727_);
lean_inc(v_getLevel_726_);
lean_inc(v_inferType_725_);
lean_inc(v_proofInstInfo_724_);
lean_inc(v_maxFVar_723_);
lean_inc(v_share_722_);
lean_dec(v___x_721_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_742_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_734_; lean_object* v___x_736_; 
lean_inc(v_a_717_);
v___x_734_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_723_, v_e_392_, v_a_717_);
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 1, v___x_734_);
v___x_736_ = v___x_732_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_share_722_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v___x_734_);
lean_ctor_set(v_reuseFailAlloc_741_, 2, v_proofInstInfo_724_);
lean_ctor_set(v_reuseFailAlloc_741_, 3, v_inferType_725_);
lean_ctor_set(v_reuseFailAlloc_741_, 4, v_getLevel_726_);
lean_ctor_set(v_reuseFailAlloc_741_, 5, v_congrInfo_727_);
lean_ctor_set(v_reuseFailAlloc_741_, 6, v_defEqI_728_);
lean_ctor_set(v_reuseFailAlloc_741_, 7, v_extensions_729_);
lean_ctor_set_uint8(v_reuseFailAlloc_741_, sizeof(void*)*8, v_debug_730_);
v___x_736_ = v_reuseFailAlloc_741_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
lean_object* v___x_737_; lean_object* v___x_739_; 
v___x_737_ = lean_st_ref_set(v_a_394_, v___x_736_);
if (v_isShared_720_ == 0)
{
v___x_739_ = v___x_719_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_a_717_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_392_);
return v___x_716_;
}
}
}
}
}
default: 
{
lean_object* v___x_746_; lean_object* v___x_747_; 
lean_dec_ref(v_e_392_);
v___x_746_ = lean_box(0);
v___x_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
return v___x_747_;
}
}
v___jp_400_:
{
if (lean_obj_tag(v___y_401_) == 0)
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_428_; 
v_a_402_ = lean_ctor_get(v___y_401_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___y_401_);
if (v_isSharedCheck_428_ == 0)
{
v___x_404_ = v___y_401_;
v_isShared_405_ = v_isSharedCheck_428_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___y_401_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_428_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_406_; lean_object* v_share_407_; lean_object* v_maxFVar_408_; lean_object* v_proofInstInfo_409_; lean_object* v_inferType_410_; lean_object* v_getLevel_411_; lean_object* v_congrInfo_412_; lean_object* v_defEqI_413_; lean_object* v_extensions_414_; uint8_t v_debug_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_427_; 
v___x_406_ = lean_st_ref_take(v_a_394_);
v_share_407_ = lean_ctor_get(v___x_406_, 0);
v_maxFVar_408_ = lean_ctor_get(v___x_406_, 1);
v_proofInstInfo_409_ = lean_ctor_get(v___x_406_, 2);
v_inferType_410_ = lean_ctor_get(v___x_406_, 3);
v_getLevel_411_ = lean_ctor_get(v___x_406_, 4);
v_congrInfo_412_ = lean_ctor_get(v___x_406_, 5);
v_defEqI_413_ = lean_ctor_get(v___x_406_, 6);
v_extensions_414_ = lean_ctor_get(v___x_406_, 7);
v_debug_415_ = lean_ctor_get_uint8(v___x_406_, sizeof(void*)*8);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_427_ == 0)
{
v___x_417_ = v___x_406_;
v_isShared_418_ = v_isSharedCheck_427_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_extensions_414_);
lean_inc(v_defEqI_413_);
lean_inc(v_congrInfo_412_);
lean_inc(v_getLevel_411_);
lean_inc(v_inferType_410_);
lean_inc(v_proofInstInfo_409_);
lean_inc(v_maxFVar_408_);
lean_inc(v_share_407_);
lean_dec(v___x_406_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_427_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; lean_object* v___x_421_; 
lean_inc(v_a_402_);
v___x_419_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_408_, v_e_392_, v_a_402_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 1, v___x_419_);
v___x_421_ = v___x_417_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_share_407_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v___x_419_);
lean_ctor_set(v_reuseFailAlloc_426_, 2, v_proofInstInfo_409_);
lean_ctor_set(v_reuseFailAlloc_426_, 3, v_inferType_410_);
lean_ctor_set(v_reuseFailAlloc_426_, 4, v_getLevel_411_);
lean_ctor_set(v_reuseFailAlloc_426_, 5, v_congrInfo_412_);
lean_ctor_set(v_reuseFailAlloc_426_, 6, v_defEqI_413_);
lean_ctor_set(v_reuseFailAlloc_426_, 7, v_extensions_414_);
lean_ctor_set_uint8(v_reuseFailAlloc_426_, sizeof(void*)*8, v_debug_415_);
v___x_421_ = v_reuseFailAlloc_426_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
lean_object* v___x_422_; lean_object* v___x_424_; 
v___x_422_ = lean_st_ref_set(v_a_394_, v___x_421_);
if (v_isShared_405_ == 0)
{
v___x_424_ = v___x_404_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_a_402_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_392_);
return v___y_401_;
}
}
v___jp_429_:
{
lean_object* v___x_431_; lean_object* v_share_432_; lean_object* v_maxFVar_433_; lean_object* v_proofInstInfo_434_; lean_object* v_inferType_435_; lean_object* v_getLevel_436_; lean_object* v_congrInfo_437_; lean_object* v_defEqI_438_; lean_object* v_extensions_439_; uint8_t v_debug_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_450_; 
v___x_431_ = lean_st_ref_take(v_a_394_);
v_share_432_ = lean_ctor_get(v___x_431_, 0);
v_maxFVar_433_ = lean_ctor_get(v___x_431_, 1);
v_proofInstInfo_434_ = lean_ctor_get(v___x_431_, 2);
v_inferType_435_ = lean_ctor_get(v___x_431_, 3);
v_getLevel_436_ = lean_ctor_get(v___x_431_, 4);
v_congrInfo_437_ = lean_ctor_get(v___x_431_, 5);
v_defEqI_438_ = lean_ctor_get(v___x_431_, 6);
v_extensions_439_ = lean_ctor_get(v___x_431_, 7);
v_debug_440_ = lean_ctor_get_uint8(v___x_431_, sizeof(void*)*8);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_450_ == 0)
{
v___x_442_ = v___x_431_;
v_isShared_443_ = v_isSharedCheck_450_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_extensions_439_);
lean_inc(v_defEqI_438_);
lean_inc(v_congrInfo_437_);
lean_inc(v_getLevel_436_);
lean_inc(v_inferType_435_);
lean_inc(v_proofInstInfo_434_);
lean_inc(v_maxFVar_433_);
lean_inc(v_share_432_);
lean_dec(v___x_431_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_450_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; lean_object* v___x_446_; 
lean_inc(v_a_430_);
v___x_444_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_433_, v_e_392_, v_a_430_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 1, v___x_444_);
v___x_446_ = v___x_442_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_share_432_);
lean_ctor_set(v_reuseFailAlloc_449_, 1, v___x_444_);
lean_ctor_set(v_reuseFailAlloc_449_, 2, v_proofInstInfo_434_);
lean_ctor_set(v_reuseFailAlloc_449_, 3, v_inferType_435_);
lean_ctor_set(v_reuseFailAlloc_449_, 4, v_getLevel_436_);
lean_ctor_set(v_reuseFailAlloc_449_, 5, v_congrInfo_437_);
lean_ctor_set(v_reuseFailAlloc_449_, 6, v_defEqI_438_);
lean_ctor_set(v_reuseFailAlloc_449_, 7, v_extensions_439_);
lean_ctor_set_uint8(v_reuseFailAlloc_449_, sizeof(void*)*8, v_debug_440_);
v___x_446_ = v_reuseFailAlloc_449_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = lean_st_ref_set(v_a_394_, v___x_446_);
v___x_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_448_, 0, v_a_430_);
return v___x_448_;
}
}
}
v___jp_451_:
{
if (lean_obj_tag(v___y_453_) == 0)
{
lean_object* v_a_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_480_; 
v_a_454_ = lean_ctor_get(v___y_453_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___y_453_);
if (v_isSharedCheck_480_ == 0)
{
v___x_456_ = v___y_453_;
v_isShared_457_ = v_isSharedCheck_480_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_a_454_);
lean_dec(v___y_453_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_480_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_458_; lean_object* v_share_459_; lean_object* v_maxFVar_460_; lean_object* v_proofInstInfo_461_; lean_object* v_inferType_462_; lean_object* v_getLevel_463_; lean_object* v_congrInfo_464_; lean_object* v_defEqI_465_; lean_object* v_extensions_466_; uint8_t v_debug_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_479_; 
v___x_458_ = lean_st_ref_take(v___y_452_);
v_share_459_ = lean_ctor_get(v___x_458_, 0);
v_maxFVar_460_ = lean_ctor_get(v___x_458_, 1);
v_proofInstInfo_461_ = lean_ctor_get(v___x_458_, 2);
v_inferType_462_ = lean_ctor_get(v___x_458_, 3);
v_getLevel_463_ = lean_ctor_get(v___x_458_, 4);
v_congrInfo_464_ = lean_ctor_get(v___x_458_, 5);
v_defEqI_465_ = lean_ctor_get(v___x_458_, 6);
v_extensions_466_ = lean_ctor_get(v___x_458_, 7);
v_debug_467_ = lean_ctor_get_uint8(v___x_458_, sizeof(void*)*8);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_479_ == 0)
{
v___x_469_ = v___x_458_;
v_isShared_470_ = v_isSharedCheck_479_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_extensions_466_);
lean_inc(v_defEqI_465_);
lean_inc(v_congrInfo_464_);
lean_inc(v_getLevel_463_);
lean_inc(v_inferType_462_);
lean_inc(v_proofInstInfo_461_);
lean_inc(v_maxFVar_460_);
lean_inc(v_share_459_);
lean_dec(v___x_458_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_479_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_471_; lean_object* v___x_473_; 
lean_inc(v_a_454_);
v___x_471_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_460_, v_e_392_, v_a_454_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 1, v___x_471_);
v___x_473_ = v___x_469_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_share_459_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v___x_471_);
lean_ctor_set(v_reuseFailAlloc_478_, 2, v_proofInstInfo_461_);
lean_ctor_set(v_reuseFailAlloc_478_, 3, v_inferType_462_);
lean_ctor_set(v_reuseFailAlloc_478_, 4, v_getLevel_463_);
lean_ctor_set(v_reuseFailAlloc_478_, 5, v_congrInfo_464_);
lean_ctor_set(v_reuseFailAlloc_478_, 6, v_defEqI_465_);
lean_ctor_set(v_reuseFailAlloc_478_, 7, v_extensions_466_);
lean_ctor_set_uint8(v_reuseFailAlloc_478_, sizeof(void*)*8, v_debug_467_);
v___x_473_ = v_reuseFailAlloc_478_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
lean_object* v___x_474_; lean_object* v___x_476_; 
v___x_474_ = lean_st_ref_set(v___y_452_, v___x_473_);
if (v_isShared_457_ == 0)
{
v___x_476_ = v___x_456_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_454_);
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
lean_dec_ref(v_e_392_);
return v___y_453_;
}
}
v___jp_481_:
{
if (v___y_490_ == 0)
{
lean_object* v___x_491_; lean_object* v___x_492_; 
lean_dec_ref(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec_ref(v_e_392_);
v___x_491_ = lean_box(0);
v___x_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
return v___x_492_;
}
else
{
lean_object* v___x_493_; lean_object* v_maxFVar_494_; lean_object* v___x_495_; 
v___x_493_ = lean_st_ref_get(v___y_489_);
v_maxFVar_494_ = lean_ctor_get(v___x_493_, 1);
lean_inc_ref(v_maxFVar_494_);
lean_dec(v___x_493_);
v___x_495_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_494_, v_e_392_);
if (lean_obj_tag(v___x_495_) == 1)
{
lean_object* v_val_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
lean_dec_ref(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec_ref(v_e_392_);
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
v___x_504_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v___y_483_, v___y_486_, v___y_489_, v___y_485_, v___y_487_, v___y_488_, v___y_482_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v_a_505_; lean_object* v___x_506_; 
v_a_505_ = lean_ctor_get(v___x_504_, 0);
lean_inc(v_a_505_);
lean_dec_ref(v___x_504_);
v___x_506_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v___y_484_, v___y_486_, v___y_489_, v___y_485_, v___y_487_, v___y_488_, v___y_482_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; lean_object* v___x_508_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_a_507_);
lean_dec_ref(v___x_506_);
v___x_508_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_505_, v_a_507_, v___y_485_, v___y_488_, v___y_482_);
v___y_452_ = v___y_489_;
v___y_453_ = v___x_508_;
goto v___jp_451_;
}
else
{
lean_dec(v_a_505_);
v___y_452_ = v___y_489_;
v___y_453_ = v___x_506_;
goto v___jp_451_;
}
}
else
{
lean_dec_ref(v___y_484_);
v___y_452_ = v___y_489_;
v___y_453_ = v___x_504_;
goto v___jp_451_;
}
}
}
}
v___jp_509_:
{
uint8_t v___x_518_; 
v___x_518_ = l_Lean_Expr_hasFVar(v_e_392_);
if (v___x_518_ == 0)
{
uint8_t v___x_519_; 
v___x_519_ = l_Lean_Expr_hasMVar(v_e_392_);
v___y_482_ = v___y_517_;
v___y_483_ = v_d_510_;
v___y_484_ = v_b_511_;
v___y_485_ = v___y_514_;
v___y_486_ = v___y_512_;
v___y_487_ = v___y_515_;
v___y_488_ = v___y_516_;
v___y_489_ = v___y_513_;
v___y_490_ = v___x_519_;
goto v___jp_481_;
}
else
{
v___y_482_ = v___y_517_;
v___y_483_ = v_d_510_;
v___y_484_ = v_b_511_;
v___y_485_ = v___y_514_;
v___y_486_ = v___y_512_;
v___y_487_ = v___y_515_;
v___y_488_ = v___y_516_;
v___y_489_ = v___y_513_;
v___y_490_ = v___x_518_;
goto v___jp_481_;
}
}
v___jp_520_:
{
if (lean_obj_tag(v___y_521_) == 0)
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_548_; 
v_a_522_ = lean_ctor_get(v___y_521_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___y_521_);
if (v_isSharedCheck_548_ == 0)
{
v___x_524_ = v___y_521_;
v_isShared_525_ = v_isSharedCheck_548_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___y_521_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_548_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_526_; lean_object* v_share_527_; lean_object* v_maxFVar_528_; lean_object* v_proofInstInfo_529_; lean_object* v_inferType_530_; lean_object* v_getLevel_531_; lean_object* v_congrInfo_532_; lean_object* v_defEqI_533_; lean_object* v_extensions_534_; uint8_t v_debug_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_547_; 
v___x_526_ = lean_st_ref_take(v_a_394_);
v_share_527_ = lean_ctor_get(v___x_526_, 0);
v_maxFVar_528_ = lean_ctor_get(v___x_526_, 1);
v_proofInstInfo_529_ = lean_ctor_get(v___x_526_, 2);
v_inferType_530_ = lean_ctor_get(v___x_526_, 3);
v_getLevel_531_ = lean_ctor_get(v___x_526_, 4);
v_congrInfo_532_ = lean_ctor_get(v___x_526_, 5);
v_defEqI_533_ = lean_ctor_get(v___x_526_, 6);
v_extensions_534_ = lean_ctor_get(v___x_526_, 7);
v_debug_535_ = lean_ctor_get_uint8(v___x_526_, sizeof(void*)*8);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_547_ == 0)
{
v___x_537_ = v___x_526_;
v_isShared_538_ = v_isSharedCheck_547_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_extensions_534_);
lean_inc(v_defEqI_533_);
lean_inc(v_congrInfo_532_);
lean_inc(v_getLevel_531_);
lean_inc(v_inferType_530_);
lean_inc(v_proofInstInfo_529_);
lean_inc(v_maxFVar_528_);
lean_inc(v_share_527_);
lean_dec(v___x_526_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_547_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_539_; lean_object* v___x_541_; 
lean_inc(v_a_522_);
v___x_539_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_528_, v_e_392_, v_a_522_);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 1, v___x_539_);
v___x_541_ = v___x_537_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_share_527_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v___x_539_);
lean_ctor_set(v_reuseFailAlloc_546_, 2, v_proofInstInfo_529_);
lean_ctor_set(v_reuseFailAlloc_546_, 3, v_inferType_530_);
lean_ctor_set(v_reuseFailAlloc_546_, 4, v_getLevel_531_);
lean_ctor_set(v_reuseFailAlloc_546_, 5, v_congrInfo_532_);
lean_ctor_set(v_reuseFailAlloc_546_, 6, v_defEqI_533_);
lean_ctor_set(v_reuseFailAlloc_546_, 7, v_extensions_534_);
lean_ctor_set_uint8(v_reuseFailAlloc_546_, sizeof(void*)*8, v_debug_535_);
v___x_541_ = v_reuseFailAlloc_546_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_542_; lean_object* v___x_544_; 
v___x_542_ = lean_st_ref_set(v_a_394_, v___x_541_);
if (v_isShared_525_ == 0)
{
v___x_544_ = v___x_524_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_522_);
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
else
{
lean_dec_ref(v_e_392_);
return v___y_521_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f___boxed(lean_object* v_e_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_e_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_);
lean_dec(v_a_754_);
lean_dec_ref(v_a_753_);
lean_dec(v_a_752_);
lean_dec_ref(v_a_751_);
lean_dec(v_a_750_);
lean_dec_ref(v_a_749_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0(lean_object* v_00_u03b2_757_, lean_object* v_x_758_, lean_object* v_x_759_, lean_object* v_x_760_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_x_758_, v_x_759_, v_x_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1(lean_object* v_00_u03b2_762_, lean_object* v_x_763_, lean_object* v_x_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_x_763_, v_x_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___boxed(lean_object* v_00_u03b2_766_, lean_object* v_x_767_, lean_object* v_x_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1(v_00_u03b2_766_, v_x_767_, v_x_768_);
lean_dec_ref(v_x_768_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0(lean_object* v_00_u03b2_770_, lean_object* v_x_771_, size_t v_x_772_, size_t v_x_773_, lean_object* v_x_774_, lean_object* v_x_775_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_771_, v_x_772_, v_x_773_, v_x_774_, v_x_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_777_, lean_object* v_x_778_, lean_object* v_x_779_, lean_object* v_x_780_, lean_object* v_x_781_, lean_object* v_x_782_){
_start:
{
size_t v_x_6097__boxed_783_; size_t v_x_6098__boxed_784_; lean_object* v_res_785_; 
v_x_6097__boxed_783_ = lean_unbox_usize(v_x_779_);
lean_dec(v_x_779_);
v_x_6098__boxed_784_ = lean_unbox_usize(v_x_780_);
lean_dec(v_x_780_);
v_res_785_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0(v_00_u03b2_777_, v_x_778_, v_x_6097__boxed_783_, v_x_6098__boxed_784_, v_x_781_, v_x_782_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2(lean_object* v_00_u03b2_786_, lean_object* v_x_787_, size_t v_x_788_, lean_object* v_x_789_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_787_, v_x_788_, v_x_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_791_, lean_object* v_x_792_, lean_object* v_x_793_, lean_object* v_x_794_){
_start:
{
size_t v_x_6114__boxed_795_; lean_object* v_res_796_; 
v_x_6114__boxed_795_ = lean_unbox_usize(v_x_793_);
lean_dec(v_x_793_);
v_res_796_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2(v_00_u03b2_791_, v_x_792_, v_x_6114__boxed_795_, v_x_794_);
lean_dec_ref(v_x_794_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_797_, lean_object* v_n_798_, lean_object* v_k_799_, lean_object* v_v_800_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(v_n_798_, v_k_799_, v_v_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_802_, size_t v_depth_803_, lean_object* v_keys_804_, lean_object* v_vals_805_, lean_object* v_heq_806_, lean_object* v_i_807_, lean_object* v_entries_808_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(v_depth_803_, v_keys_804_, v_vals_805_, v_i_807_, v_entries_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_810_, lean_object* v_depth_811_, lean_object* v_keys_812_, lean_object* v_vals_813_, lean_object* v_heq_814_, lean_object* v_i_815_, lean_object* v_entries_816_){
_start:
{
size_t v_depth_boxed_817_; lean_object* v_res_818_; 
v_depth_boxed_817_ = lean_unbox_usize(v_depth_811_);
lean_dec(v_depth_811_);
v_res_818_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3(v_00_u03b2_810_, v_depth_boxed_817_, v_keys_812_, v_vals_813_, v_heq_814_, v_i_815_, v_entries_816_);
lean_dec_ref(v_vals_813_);
lean_dec_ref(v_keys_812_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_819_, lean_object* v_keys_820_, lean_object* v_vals_821_, lean_object* v_heq_822_, lean_object* v_i_823_, lean_object* v_k_824_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_keys_820_, v_vals_821_, v_i_823_, v_k_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_826_, lean_object* v_keys_827_, lean_object* v_vals_828_, lean_object* v_heq_829_, lean_object* v_i_830_, lean_object* v_k_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6(v_00_u03b2_826_, v_keys_827_, v_vals_828_, v_heq_829_, v_i_830_, v_k_831_);
lean_dec_ref(v_k_831_);
lean_dec_ref(v_vals_828_);
lean_dec_ref(v_keys_827_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_833_, lean_object* v_x_834_, lean_object* v_x_835_, lean_object* v_x_836_, lean_object* v_x_837_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_x_834_, v_x_835_, v_x_836_, v_x_837_);
return v___x_838_;
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
