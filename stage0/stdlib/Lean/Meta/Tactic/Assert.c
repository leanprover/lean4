// Lean compiler output
// Module: Lean.Meta.Tactic.Assert
// Imports: public import Lean.Meta.Tactic.FVarSubst public import Lean.Meta.Tactic.Intro public import Lean.Meta.Tactic.Revert public import Lean.Util.ForEachExpr import Lean.Meta.AppBuilder
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
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_revertAfter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_setKind(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instDecidableEqLocalDeclKind(uint8_t, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_modifyExprMVarLCtx(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assert___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assert___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_assert___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "assert"};
static const lean_object* l_Lean_MVarId_assert___closed__0 = (const lean_object*)&l_Lean_MVarId_assert___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_assert___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_assert___closed__0_value),LEAN_SCALAR_PTR_LITERAL(17, 243, 163, 93, 35, 220, 207, 86)}};
static const lean_object* l_Lean_MVarId_assert___closed__1 = (const lean_object*)&l_Lean_MVarId_assert___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_note(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_note___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_define___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_define___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_define___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "define"};
static const lean_object* l_Lean_MVarId_define___closed__0 = (const lean_object*)&l_Lean_MVarId_define___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_define___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_define___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 225, 179, 252, 13, 73, 16, 168)}};
static const lean_object* l_Lean_MVarId_define___closed__1 = (const lean_object*)&l_Lean_MVarId_define___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_define(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_define___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_assertExt___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_MVarId_assertExt___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_assertExt___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_assertExt___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_assertExt___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_MVarId_assertExt___lam__0___closed__1 = (const lean_object*)&l_Lean_MVarId_assertExt___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_MVarId_assertExt___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_assertExt___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_MVarId_assertExt___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assertExt___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assertExt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assertExt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_assertAfter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "assertAfter"};
static const lean_object* l_Lean_MVarId_assertAfter___closed__0 = (const lean_object*)&l_Lean_MVarId_assertAfter___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_assertAfter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_assertAfter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(39, 174, 1, 90, 222, 201, 211, 92)}};
static const lean_object* l_Lean_MVarId_assertAfter___closed__1 = (const lean_object*)&l_Lean_MVarId_assertAfter___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_assertAfter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assertAfter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_assertHypotheses___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "assertHypotheses"};
static const lean_object* l_Lean_MVarId_assertHypotheses___closed__0 = (const lean_object*)&l_Lean_MVarId_assertHypotheses___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_assertHypotheses___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_assertHypotheses___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 34, 150, 130, 103, 166, 191, 222)}};
static const lean_object* l_Lean_MVarId_assertHypotheses___closed__1 = (const lean_object*)&l_Lean_MVarId_assertHypotheses___closed__1_value;
static const lean_array_object l_Lean_MVarId_assertHypotheses___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_MVarId_assertHypotheses___closed__2 = (const lean_object*)&l_Lean_MVarId_assertHypotheses___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___closed__1;
static const lean_closure_object l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replace___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replace___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replace___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replace___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(lean_object* v_mvarId_1_, lean_object* v_x_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1_, v_x_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_);
if (lean_obj_tag(v___x_8_) == 0)
{
lean_object* v_a_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_16_; 
v_a_9_ = lean_ctor_get(v___x_8_, 0);
v_isSharedCheck_16_ = !lean_is_exclusive(v___x_8_);
if (v_isSharedCheck_16_ == 0)
{
v___x_11_ = v___x_8_;
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_a_9_);
lean_dec(v___x_8_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
v_resetjp_10_:
{
lean_object* v___x_14_; 
if (v_isShared_12_ == 0)
{
v___x_14_ = v___x_11_;
goto v_reusejp_13_;
}
else
{
lean_object* v_reuseFailAlloc_15_; 
v_reuseFailAlloc_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_15_, 0, v_a_9_);
v___x_14_ = v_reuseFailAlloc_15_;
goto v_reusejp_13_;
}
v_reusejp_13_:
{
return v___x_14_;
}
}
}
else
{
lean_object* v_a_17_; lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_24_; 
v_a_17_ = lean_ctor_get(v___x_8_, 0);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_8_);
if (v_isSharedCheck_24_ == 0)
{
v___x_19_ = v___x_8_;
v_isShared_20_ = v_isSharedCheck_24_;
goto v_resetjp_18_;
}
else
{
lean_inc(v_a_17_);
lean_dec(v___x_8_);
v___x_19_ = lean_box(0);
v_isShared_20_ = v_isSharedCheck_24_;
goto v_resetjp_18_;
}
v_resetjp_18_:
{
lean_object* v___x_22_; 
if (v_isShared_20_ == 0)
{
v___x_22_ = v___x_19_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_a_17_);
v___x_22_ = v_reuseFailAlloc_23_;
goto v_reusejp_21_;
}
v_reusejp_21_:
{
return v___x_22_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg___boxed(lean_object* v_mvarId_25_, lean_object* v_x_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(v_mvarId_25_, v_x_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_);
lean_dec(v___y_30_);
lean_dec_ref(v___y_29_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1(lean_object* v_00_u03b1_33_, lean_object* v_mvarId_34_, lean_object* v_x_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(v_mvarId_34_, v_x_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___boxed(lean_object* v_00_u03b1_42_, lean_object* v_mvarId_43_, lean_object* v_x_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1(v_00_u03b1_42_, v_mvarId_43_, v_x_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
lean_dec(v___y_46_);
lean_dec_ref(v___y_45_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(lean_object* v_x_51_, lean_object* v_x_52_, lean_object* v_x_53_, lean_object* v_x_54_){
_start:
{
lean_object* v_ks_55_; lean_object* v_vs_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_80_; 
v_ks_55_ = lean_ctor_get(v_x_51_, 0);
v_vs_56_ = lean_ctor_get(v_x_51_, 1);
v_isSharedCheck_80_ = !lean_is_exclusive(v_x_51_);
if (v_isSharedCheck_80_ == 0)
{
v___x_58_ = v_x_51_;
v_isShared_59_ = v_isSharedCheck_80_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_vs_56_);
lean_inc(v_ks_55_);
lean_dec(v_x_51_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_80_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_60_; uint8_t v___x_61_; 
v___x_60_ = lean_array_get_size(v_ks_55_);
v___x_61_ = lean_nat_dec_lt(v_x_52_, v___x_60_);
if (v___x_61_ == 0)
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_65_; 
lean_dec(v_x_52_);
v___x_62_ = lean_array_push(v_ks_55_, v_x_53_);
v___x_63_ = lean_array_push(v_vs_56_, v_x_54_);
if (v_isShared_59_ == 0)
{
lean_ctor_set(v___x_58_, 1, v___x_63_);
lean_ctor_set(v___x_58_, 0, v___x_62_);
v___x_65_ = v___x_58_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v___x_62_);
lean_ctor_set(v_reuseFailAlloc_66_, 1, v___x_63_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
return v___x_65_;
}
}
else
{
lean_object* v_k_x27_67_; uint8_t v___x_68_; 
v_k_x27_67_ = lean_array_fget_borrowed(v_ks_55_, v_x_52_);
v___x_68_ = l_Lean_instBEqMVarId_beq(v_x_53_, v_k_x27_67_);
if (v___x_68_ == 0)
{
lean_object* v___x_70_; 
if (v_isShared_59_ == 0)
{
v___x_70_ = v___x_58_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v_ks_55_);
lean_ctor_set(v_reuseFailAlloc_74_, 1, v_vs_56_);
v___x_70_ = v_reuseFailAlloc_74_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_unsigned_to_nat(1u);
v___x_72_ = lean_nat_add(v_x_52_, v___x_71_);
lean_dec(v_x_52_);
v_x_51_ = v___x_70_;
v_x_52_ = v___x_72_;
goto _start;
}
}
else
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_78_; 
v___x_75_ = lean_array_fset(v_ks_55_, v_x_52_, v_x_53_);
v___x_76_ = lean_array_fset(v_vs_56_, v_x_52_, v_x_54_);
lean_dec(v_x_52_);
if (v_isShared_59_ == 0)
{
lean_ctor_set(v___x_58_, 1, v___x_76_);
lean_ctor_set(v___x_58_, 0, v___x_75_);
v___x_78_ = v___x_58_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v___x_75_);
lean_ctor_set(v_reuseFailAlloc_79_, 1, v___x_76_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_n_81_, lean_object* v_k_82_, lean_object* v_v_83_){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_84_ = lean_unsigned_to_nat(0u);
v___x_85_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_n_81_, v___x_84_, v_k_82_, v_v_83_);
return v___x_85_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_86_; size_t v___x_87_; size_t v___x_88_; 
v___x_86_ = ((size_t)5ULL);
v___x_87_ = ((size_t)1ULL);
v___x_88_ = lean_usize_shift_left(v___x_87_, v___x_86_);
return v___x_88_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_89_; size_t v___x_90_; size_t v___x_91_; 
v___x_89_ = ((size_t)1ULL);
v___x_90_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_91_ = lean_usize_sub(v___x_90_, v___x_89_);
return v___x_91_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(lean_object* v_x_93_, size_t v_x_94_, size_t v_x_95_, lean_object* v_x_96_, lean_object* v_x_97_){
_start:
{
if (lean_obj_tag(v_x_93_) == 0)
{
lean_object* v_es_98_; size_t v___x_99_; size_t v___x_100_; size_t v___x_101_; size_t v___x_102_; lean_object* v_j_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v_es_98_ = lean_ctor_get(v_x_93_, 0);
v___x_99_ = ((size_t)5ULL);
v___x_100_ = ((size_t)1ULL);
v___x_101_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_102_ = lean_usize_land(v_x_94_, v___x_101_);
v_j_103_ = lean_usize_to_nat(v___x_102_);
v___x_104_ = lean_array_get_size(v_es_98_);
v___x_105_ = lean_nat_dec_lt(v_j_103_, v___x_104_);
if (v___x_105_ == 0)
{
lean_dec(v_j_103_);
lean_dec(v_x_97_);
lean_dec(v_x_96_);
return v_x_93_;
}
else
{
lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_142_; 
lean_inc_ref(v_es_98_);
v_isSharedCheck_142_ = !lean_is_exclusive(v_x_93_);
if (v_isSharedCheck_142_ == 0)
{
lean_object* v_unused_143_; 
v_unused_143_ = lean_ctor_get(v_x_93_, 0);
lean_dec(v_unused_143_);
v___x_107_ = v_x_93_;
v_isShared_108_ = v_isSharedCheck_142_;
goto v_resetjp_106_;
}
else
{
lean_dec(v_x_93_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_142_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v_v_109_; lean_object* v___x_110_; lean_object* v_xs_x27_111_; lean_object* v___y_113_; 
v_v_109_ = lean_array_fget(v_es_98_, v_j_103_);
v___x_110_ = lean_box(0);
v_xs_x27_111_ = lean_array_fset(v_es_98_, v_j_103_, v___x_110_);
switch(lean_obj_tag(v_v_109_))
{
case 0:
{
lean_object* v_key_118_; lean_object* v_val_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_129_; 
v_key_118_ = lean_ctor_get(v_v_109_, 0);
v_val_119_ = lean_ctor_get(v_v_109_, 1);
v_isSharedCheck_129_ = !lean_is_exclusive(v_v_109_);
if (v_isSharedCheck_129_ == 0)
{
v___x_121_ = v_v_109_;
v_isShared_122_ = v_isSharedCheck_129_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_val_119_);
lean_inc(v_key_118_);
lean_dec(v_v_109_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_129_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
uint8_t v___x_123_; 
v___x_123_ = l_Lean_instBEqMVarId_beq(v_x_96_, v_key_118_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; lean_object* v___x_125_; 
lean_del_object(v___x_121_);
v___x_124_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_118_, v_val_119_, v_x_96_, v_x_97_);
v___x_125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
v___y_113_ = v___x_125_;
goto v___jp_112_;
}
else
{
lean_object* v___x_127_; 
lean_dec(v_val_119_);
lean_dec(v_key_118_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 1, v_x_97_);
lean_ctor_set(v___x_121_, 0, v_x_96_);
v___x_127_ = v___x_121_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_x_96_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v_x_97_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
v___y_113_ = v___x_127_;
goto v___jp_112_;
}
}
}
}
case 1:
{
lean_object* v_node_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_140_; 
v_node_130_ = lean_ctor_get(v_v_109_, 0);
v_isSharedCheck_140_ = !lean_is_exclusive(v_v_109_);
if (v_isSharedCheck_140_ == 0)
{
v___x_132_ = v_v_109_;
v_isShared_133_ = v_isSharedCheck_140_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_node_130_);
lean_dec(v_v_109_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_140_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
size_t v___x_134_; size_t v___x_135_; lean_object* v___x_136_; lean_object* v___x_138_; 
v___x_134_ = lean_usize_shift_right(v_x_94_, v___x_99_);
v___x_135_ = lean_usize_add(v_x_95_, v___x_100_);
v___x_136_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(v_node_130_, v___x_134_, v___x_135_, v_x_96_, v_x_97_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 0, v___x_136_);
v___x_138_ = v___x_132_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v___x_136_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
v___y_113_ = v___x_138_;
goto v___jp_112_;
}
}
}
default: 
{
lean_object* v___x_141_; 
v___x_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_141_, 0, v_x_96_);
lean_ctor_set(v___x_141_, 1, v_x_97_);
v___y_113_ = v___x_141_;
goto v___jp_112_;
}
}
v___jp_112_:
{
lean_object* v___x_114_; lean_object* v___x_116_; 
v___x_114_ = lean_array_fset(v_xs_x27_111_, v_j_103_, v___y_113_);
lean_dec(v_j_103_);
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 0, v___x_114_);
v___x_116_ = v___x_107_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_114_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
}
}
}
else
{
lean_object* v_ks_144_; lean_object* v_vs_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_165_; 
v_ks_144_ = lean_ctor_get(v_x_93_, 0);
v_vs_145_ = lean_ctor_get(v_x_93_, 1);
v_isSharedCheck_165_ = !lean_is_exclusive(v_x_93_);
if (v_isSharedCheck_165_ == 0)
{
v___x_147_ = v_x_93_;
v_isShared_148_ = v_isSharedCheck_165_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_vs_145_);
lean_inc(v_ks_144_);
lean_dec(v_x_93_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_165_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_150_; 
if (v_isShared_148_ == 0)
{
v___x_150_ = v___x_147_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_ks_144_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v_vs_145_);
v___x_150_ = v_reuseFailAlloc_164_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v_newNode_151_; uint8_t v___y_153_; size_t v___x_159_; uint8_t v___x_160_; 
v_newNode_151_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3___redArg(v___x_150_, v_x_96_, v_x_97_);
v___x_159_ = ((size_t)7ULL);
v___x_160_ = lean_usize_dec_le(v___x_159_, v_x_95_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_161_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_151_);
v___x_162_ = lean_unsigned_to_nat(4u);
v___x_163_ = lean_nat_dec_lt(v___x_161_, v___x_162_);
lean_dec(v___x_161_);
v___y_153_ = v___x_163_;
goto v___jp_152_;
}
else
{
v___y_153_ = v___x_160_;
goto v___jp_152_;
}
v___jp_152_:
{
if (v___y_153_ == 0)
{
lean_object* v_ks_154_; lean_object* v_vs_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v_ks_154_ = lean_ctor_get(v_newNode_151_, 0);
lean_inc_ref(v_ks_154_);
v_vs_155_ = lean_ctor_get(v_newNode_151_, 1);
lean_inc_ref(v_vs_155_);
lean_dec_ref(v_newNode_151_);
v___x_156_ = lean_unsigned_to_nat(0u);
v___x_157_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__2);
v___x_158_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg(v_x_95_, v_ks_154_, v_vs_155_, v___x_156_, v___x_157_);
lean_dec_ref(v_vs_155_);
lean_dec_ref(v_ks_154_);
return v___x_158_;
}
else
{
return v_newNode_151_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg(size_t v_depth_166_, lean_object* v_keys_167_, lean_object* v_vals_168_, lean_object* v_i_169_, lean_object* v_entries_170_){
_start:
{
lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_171_ = lean_array_get_size(v_keys_167_);
v___x_172_ = lean_nat_dec_lt(v_i_169_, v___x_171_);
if (v___x_172_ == 0)
{
lean_dec(v_i_169_);
return v_entries_170_;
}
else
{
lean_object* v_k_173_; lean_object* v_v_174_; uint64_t v___x_175_; size_t v_h_176_; size_t v___x_177_; lean_object* v___x_178_; size_t v___x_179_; size_t v___x_180_; size_t v___x_181_; size_t v_h_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v_k_173_ = lean_array_fget_borrowed(v_keys_167_, v_i_169_);
v_v_174_ = lean_array_fget_borrowed(v_vals_168_, v_i_169_);
v___x_175_ = l_Lean_instHashableMVarId_hash(v_k_173_);
v_h_176_ = lean_uint64_to_usize(v___x_175_);
v___x_177_ = ((size_t)5ULL);
v___x_178_ = lean_unsigned_to_nat(1u);
v___x_179_ = ((size_t)1ULL);
v___x_180_ = lean_usize_sub(v_depth_166_, v___x_179_);
v___x_181_ = lean_usize_mul(v___x_177_, v___x_180_);
v_h_182_ = lean_usize_shift_right(v_h_176_, v___x_181_);
v___x_183_ = lean_nat_add(v_i_169_, v___x_178_);
lean_dec(v_i_169_);
lean_inc(v_v_174_);
lean_inc(v_k_173_);
v___x_184_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(v_entries_170_, v_h_182_, v_depth_166_, v_k_173_, v_v_174_);
v_i_169_ = v___x_183_;
v_entries_170_ = v___x_184_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_depth_186_, lean_object* v_keys_187_, lean_object* v_vals_188_, lean_object* v_i_189_, lean_object* v_entries_190_){
_start:
{
size_t v_depth_boxed_191_; lean_object* v_res_192_; 
v_depth_boxed_191_ = lean_unbox_usize(v_depth_186_);
lean_dec(v_depth_186_);
v_res_192_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_191_, v_keys_187_, v_vals_188_, v_i_189_, v_entries_190_);
lean_dec_ref(v_vals_188_);
lean_dec_ref(v_keys_187_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_193_, lean_object* v_x_194_, lean_object* v_x_195_, lean_object* v_x_196_, lean_object* v_x_197_){
_start:
{
size_t v_x_1323__boxed_198_; size_t v_x_1324__boxed_199_; lean_object* v_res_200_; 
v_x_1323__boxed_198_ = lean_unbox_usize(v_x_194_);
lean_dec(v_x_194_);
v_x_1324__boxed_199_ = lean_unbox_usize(v_x_195_);
lean_dec(v_x_195_);
v_res_200_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(v_x_193_, v_x_1323__boxed_198_, v_x_1324__boxed_199_, v_x_196_, v_x_197_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0___redArg(lean_object* v_x_201_, lean_object* v_x_202_, lean_object* v_x_203_){
_start:
{
uint64_t v___x_204_; size_t v___x_205_; size_t v___x_206_; lean_object* v___x_207_; 
v___x_204_ = l_Lean_instHashableMVarId_hash(v_x_202_);
v___x_205_ = lean_uint64_to_usize(v___x_204_);
v___x_206_ = ((size_t)1ULL);
v___x_207_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(v_x_201_, v___x_205_, v___x_206_, v_x_202_, v_x_203_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(lean_object* v_mvarId_208_, lean_object* v_val_209_, lean_object* v___y_210_){
_start:
{
lean_object* v___x_212_; lean_object* v_mctx_213_; lean_object* v_cache_214_; lean_object* v_zetaDeltaFVarIds_215_; lean_object* v_postponed_216_; lean_object* v_diag_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_245_; 
v___x_212_ = lean_st_ref_take(v___y_210_);
v_mctx_213_ = lean_ctor_get(v___x_212_, 0);
v_cache_214_ = lean_ctor_get(v___x_212_, 1);
v_zetaDeltaFVarIds_215_ = lean_ctor_get(v___x_212_, 2);
v_postponed_216_ = lean_ctor_get(v___x_212_, 3);
v_diag_217_ = lean_ctor_get(v___x_212_, 4);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_245_ == 0)
{
v___x_219_ = v___x_212_;
v_isShared_220_ = v_isSharedCheck_245_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_diag_217_);
lean_inc(v_postponed_216_);
lean_inc(v_zetaDeltaFVarIds_215_);
lean_inc(v_cache_214_);
lean_inc(v_mctx_213_);
lean_dec(v___x_212_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_245_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v_depth_221_; lean_object* v_levelAssignDepth_222_; lean_object* v_lmvarCounter_223_; lean_object* v_mvarCounter_224_; lean_object* v_lDecls_225_; lean_object* v_decls_226_; lean_object* v_userNames_227_; lean_object* v_lAssignment_228_; lean_object* v_eAssignment_229_; lean_object* v_dAssignment_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_244_; 
v_depth_221_ = lean_ctor_get(v_mctx_213_, 0);
v_levelAssignDepth_222_ = lean_ctor_get(v_mctx_213_, 1);
v_lmvarCounter_223_ = lean_ctor_get(v_mctx_213_, 2);
v_mvarCounter_224_ = lean_ctor_get(v_mctx_213_, 3);
v_lDecls_225_ = lean_ctor_get(v_mctx_213_, 4);
v_decls_226_ = lean_ctor_get(v_mctx_213_, 5);
v_userNames_227_ = lean_ctor_get(v_mctx_213_, 6);
v_lAssignment_228_ = lean_ctor_get(v_mctx_213_, 7);
v_eAssignment_229_ = lean_ctor_get(v_mctx_213_, 8);
v_dAssignment_230_ = lean_ctor_get(v_mctx_213_, 9);
v_isSharedCheck_244_ = !lean_is_exclusive(v_mctx_213_);
if (v_isSharedCheck_244_ == 0)
{
v___x_232_ = v_mctx_213_;
v_isShared_233_ = v_isSharedCheck_244_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_dAssignment_230_);
lean_inc(v_eAssignment_229_);
lean_inc(v_lAssignment_228_);
lean_inc(v_userNames_227_);
lean_inc(v_decls_226_);
lean_inc(v_lDecls_225_);
lean_inc(v_mvarCounter_224_);
lean_inc(v_lmvarCounter_223_);
lean_inc(v_levelAssignDepth_222_);
lean_inc(v_depth_221_);
lean_dec(v_mctx_213_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_244_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_234_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0___redArg(v_eAssignment_229_, v_mvarId_208_, v_val_209_);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 8, v___x_234_);
v___x_236_ = v___x_232_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_depth_221_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v_levelAssignDepth_222_);
lean_ctor_set(v_reuseFailAlloc_243_, 2, v_lmvarCounter_223_);
lean_ctor_set(v_reuseFailAlloc_243_, 3, v_mvarCounter_224_);
lean_ctor_set(v_reuseFailAlloc_243_, 4, v_lDecls_225_);
lean_ctor_set(v_reuseFailAlloc_243_, 5, v_decls_226_);
lean_ctor_set(v_reuseFailAlloc_243_, 6, v_userNames_227_);
lean_ctor_set(v_reuseFailAlloc_243_, 7, v_lAssignment_228_);
lean_ctor_set(v_reuseFailAlloc_243_, 8, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_243_, 9, v_dAssignment_230_);
v___x_236_ = v_reuseFailAlloc_243_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v___x_238_; 
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 0, v___x_236_);
v___x_238_ = v___x_219_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_236_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_cache_214_);
lean_ctor_set(v_reuseFailAlloc_242_, 2, v_zetaDeltaFVarIds_215_);
lean_ctor_set(v_reuseFailAlloc_242_, 3, v_postponed_216_);
lean_ctor_set(v_reuseFailAlloc_242_, 4, v_diag_217_);
v___x_238_ = v_reuseFailAlloc_242_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_239_ = lean_st_ref_set(v___y_210_, v___x_238_);
v___x_240_ = lean_box(0);
v___x_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
return v___x_241_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg___boxed(lean_object* v_mvarId_246_, lean_object* v_val_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(v_mvarId_246_, v_val_247_, v___y_248_);
lean_dec(v___y_248_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assert___lam__0(lean_object* v_mvarId_251_, lean_object* v___x_252_, lean_object* v_name_253_, lean_object* v_type_254_, lean_object* v_val_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v___x_261_; 
lean_inc(v_mvarId_251_);
v___x_261_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_251_, v___x_252_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v___x_262_; 
lean_dec_ref(v___x_261_);
lean_inc(v_mvarId_251_);
v___x_262_ = l_Lean_MVarId_getTag(v_mvarId_251_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v_a_263_; lean_object* v___x_264_; 
v_a_263_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_a_263_);
lean_dec_ref(v___x_262_);
lean_inc(v_mvarId_251_);
v___x_264_ = l_Lean_MVarId_getType(v_mvarId_251_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v_a_265_; uint8_t v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v_a_265_ = lean_ctor_get(v___x_264_, 0);
lean_inc(v_a_265_);
lean_dec_ref(v___x_264_);
v___x_266_ = 0;
v___x_267_ = l_Lean_mkForall(v_name_253_, v___x_266_, v_type_254_, v_a_265_);
v___x_268_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_267_, v_a_263_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_a_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_279_; 
v_a_269_ = lean_ctor_get(v___x_268_, 0);
lean_inc_n(v_a_269_, 2);
lean_dec_ref(v___x_268_);
v___x_270_ = l_Lean_Expr_app___override(v_a_269_, v_val_255_);
v___x_271_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(v_mvarId_251_, v___x_270_, v___y_257_);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_279_ == 0)
{
lean_object* v_unused_280_; 
v_unused_280_ = lean_ctor_get(v___x_271_, 0);
lean_dec(v_unused_280_);
v___x_273_ = v___x_271_;
v_isShared_274_ = v_isSharedCheck_279_;
goto v_resetjp_272_;
}
else
{
lean_dec(v___x_271_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_279_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_275_; lean_object* v___x_277_; 
v___x_275_ = l_Lean_Expr_mvarId_x21(v_a_269_);
lean_dec(v_a_269_);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 0, v___x_275_);
v___x_277_ = v___x_273_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_275_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
else
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_288_; 
lean_dec_ref(v_val_255_);
lean_dec(v_mvarId_251_);
v_a_281_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_288_ == 0)
{
v___x_283_ = v___x_268_;
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_268_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_286_; 
if (v_isShared_284_ == 0)
{
v___x_286_ = v___x_283_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_a_281_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
}
else
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_296_; 
lean_dec(v_a_263_);
lean_dec_ref(v_val_255_);
lean_dec_ref(v_type_254_);
lean_dec(v_name_253_);
lean_dec(v_mvarId_251_);
v_a_289_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_296_ == 0)
{
v___x_291_ = v___x_264_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_264_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_289_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
else
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_304_; 
lean_dec_ref(v_val_255_);
lean_dec_ref(v_type_254_);
lean_dec(v_name_253_);
lean_dec(v_mvarId_251_);
v_a_297_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_304_ == 0)
{
v___x_299_ = v___x_262_;
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_262_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_300_ == 0)
{
v___x_302_ = v___x_299_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_a_297_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
}
else
{
lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_312_; 
lean_dec_ref(v_val_255_);
lean_dec_ref(v_type_254_);
lean_dec(v_name_253_);
lean_dec(v_mvarId_251_);
v_a_305_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_312_ == 0)
{
v___x_307_ = v___x_261_;
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_261_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
if (v_isShared_308_ == 0)
{
v___x_310_ = v___x_307_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_a_305_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assert___lam__0___boxed(lean_object* v_mvarId_313_, lean_object* v___x_314_, lean_object* v_name_315_, lean_object* v_type_316_, lean_object* v_val_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_MVarId_assert___lam__0(v_mvarId_313_, v___x_314_, v_name_315_, v_type_316_, v_val_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assert(lean_object* v_mvarId_327_, lean_object* v_name_328_, lean_object* v_type_329_, lean_object* v_val_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
lean_object* v___x_336_; lean_object* v___f_337_; lean_object* v___x_338_; 
v___x_336_ = ((lean_object*)(l_Lean_MVarId_assert___closed__1));
lean_inc(v_mvarId_327_);
v___f_337_ = lean_alloc_closure((void*)(l_Lean_MVarId_assert___lam__0___boxed), 10, 5);
lean_closure_set(v___f_337_, 0, v_mvarId_327_);
lean_closure_set(v___f_337_, 1, v___x_336_);
lean_closure_set(v___f_337_, 2, v_name_328_);
lean_closure_set(v___f_337_, 3, v_type_329_);
lean_closure_set(v___f_337_, 4, v_val_330_);
v___x_338_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(v_mvarId_327_, v___f_337_, v_a_331_, v_a_332_, v_a_333_, v_a_334_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assert___boxed(lean_object* v_mvarId_339_, lean_object* v_name_340_, lean_object* v_type_341_, lean_object* v_val_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_MVarId_assert(v_mvarId_339_, v_name_340_, v_type_341_, v_val_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_);
lean_dec(v_a_346_);
lean_dec_ref(v_a_345_);
lean_dec(v_a_344_);
lean_dec_ref(v_a_343_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0(lean_object* v_mvarId_349_, lean_object* v_val_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(v_mvarId_349_, v_val_350_, v___y_352_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___boxed(lean_object* v_mvarId_357_, lean_object* v_val_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0(v_mvarId_357_, v_val_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0(lean_object* v_00_u03b2_365_, lean_object* v_x_366_, lean_object* v_x_367_, lean_object* v_x_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0___redArg(v_x_366_, v_x_367_, v_x_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_370_, lean_object* v_x_371_, size_t v_x_372_, size_t v_x_373_, lean_object* v_x_374_, lean_object* v_x_375_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(v_x_371_, v_x_372_, v_x_373_, v_x_374_, v_x_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_377_, lean_object* v_x_378_, lean_object* v_x_379_, lean_object* v_x_380_, lean_object* v_x_381_, lean_object* v_x_382_){
_start:
{
size_t v_x_1711__boxed_383_; size_t v_x_1712__boxed_384_; lean_object* v_res_385_; 
v_x_1711__boxed_383_ = lean_unbox_usize(v_x_379_);
lean_dec(v_x_379_);
v_x_1712__boxed_384_ = lean_unbox_usize(v_x_380_);
lean_dec(v_x_380_);
v_res_385_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2(v_00_u03b2_377_, v_x_378_, v_x_1711__boxed_383_, v_x_1712__boxed_384_, v_x_381_, v_x_382_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_386_, lean_object* v_n_387_, lean_object* v_k_388_, lean_object* v_v_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3___redArg(v_n_387_, v_k_388_, v_v_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_391_, size_t v_depth_392_, lean_object* v_keys_393_, lean_object* v_vals_394_, lean_object* v_heq_395_, lean_object* v_i_396_, lean_object* v_entries_397_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_392_, v_keys_393_, v_vals_394_, v_i_396_, v_entries_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_399_, lean_object* v_depth_400_, lean_object* v_keys_401_, lean_object* v_vals_402_, lean_object* v_heq_403_, lean_object* v_i_404_, lean_object* v_entries_405_){
_start:
{
size_t v_depth_boxed_406_; lean_object* v_res_407_; 
v_depth_boxed_406_ = lean_unbox_usize(v_depth_400_);
lean_dec(v_depth_400_);
v_res_407_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_399_, v_depth_boxed_406_, v_keys_401_, v_vals_402_, v_heq_403_, v_i_404_, v_entries_405_);
lean_dec_ref(v_vals_402_);
lean_dec_ref(v_keys_401_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_408_, lean_object* v_x_409_, lean_object* v_x_410_, lean_object* v_x_411_, lean_object* v_x_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_409_, v_x_410_, v_x_411_, v_x_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_note(lean_object* v_g_414_, lean_object* v_h_415_, lean_object* v_v_416_, lean_object* v_t_x3f_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_){
_start:
{
lean_object* v_a_424_; 
if (lean_obj_tag(v_t_x3f_417_) == 0)
{
lean_object* v___x_437_; 
lean_inc(v_a_421_);
lean_inc_ref(v_a_420_);
lean_inc(v_a_419_);
lean_inc_ref(v_a_418_);
lean_inc_ref(v_v_416_);
v___x_437_ = lean_infer_type(v_v_416_, v_a_418_, v_a_419_, v_a_420_, v_a_421_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_a_438_);
lean_dec_ref(v___x_437_);
v_a_424_ = v_a_438_;
goto v___jp_423_;
}
else
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_446_; 
lean_dec_ref(v_v_416_);
lean_dec(v_h_415_);
lean_dec(v_g_414_);
v_a_439_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_446_ == 0)
{
v___x_441_ = v___x_437_;
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___x_437_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_444_; 
if (v_isShared_442_ == 0)
{
v___x_444_ = v___x_441_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_a_439_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
else
{
lean_object* v_val_447_; 
v_val_447_ = lean_ctor_get(v_t_x3f_417_, 0);
lean_inc(v_val_447_);
lean_dec_ref(v_t_x3f_417_);
v_a_424_ = v_val_447_;
goto v___jp_423_;
}
v___jp_423_:
{
lean_object* v___x_425_; 
v___x_425_ = l_Lean_MVarId_assert(v_g_414_, v_h_415_, v_a_424_, v_v_416_, v_a_418_, v_a_419_, v_a_420_, v_a_421_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v_a_426_; uint8_t v___x_427_; lean_object* v___x_428_; 
v_a_426_ = lean_ctor_get(v___x_425_, 0);
lean_inc(v_a_426_);
lean_dec_ref(v___x_425_);
v___x_427_ = 1;
v___x_428_ = l_Lean_Meta_intro1Core(v_a_426_, v___x_427_, v_a_418_, v_a_419_, v_a_420_, v_a_421_);
return v___x_428_;
}
else
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_436_; 
v_a_429_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_436_ == 0)
{
v___x_431_ = v___x_425_;
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_425_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_a_429_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_note___boxed(lean_object* v_g_448_, lean_object* v_h_449_, lean_object* v_v_450_, lean_object* v_t_x3f_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lean_MVarId_note(v_g_448_, v_h_449_, v_v_450_, v_t_x3f_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_);
lean_dec(v_a_455_);
lean_dec_ref(v_a_454_);
lean_dec(v_a_453_);
lean_dec_ref(v_a_452_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_define___lam__0(lean_object* v_mvarId_458_, lean_object* v___x_459_, lean_object* v_name_460_, lean_object* v_type_461_, lean_object* v_val_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v___x_468_; 
lean_inc(v_mvarId_458_);
v___x_468_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_458_, v___x_459_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v___x_469_; 
lean_dec_ref(v___x_468_);
lean_inc(v_mvarId_458_);
v___x_469_ = l_Lean_MVarId_getTag(v_mvarId_458_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; lean_object* v___x_471_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_a_470_);
lean_dec_ref(v___x_469_);
lean_inc(v_mvarId_458_);
v___x_471_ = l_Lean_MVarId_getType(v_mvarId_458_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_472_; uint8_t v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v_a_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_a_472_);
lean_dec_ref(v___x_471_);
v___x_473_ = 0;
v___x_474_ = l_Lean_Expr_letE___override(v_name_460_, v_type_461_, v_val_462_, v_a_472_, v___x_473_);
v___x_475_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_474_, v_a_470_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v_a_476_; lean_object* v___x_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_485_; 
v_a_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc_n(v_a_476_, 2);
lean_dec_ref(v___x_475_);
v___x_477_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(v_mvarId_458_, v_a_476_, v___y_464_);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_485_ == 0)
{
lean_object* v_unused_486_; 
v_unused_486_ = lean_ctor_get(v___x_477_, 0);
lean_dec(v_unused_486_);
v___x_479_ = v___x_477_;
v_isShared_480_ = v_isSharedCheck_485_;
goto v_resetjp_478_;
}
else
{
lean_dec(v___x_477_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_485_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_481_; lean_object* v___x_483_; 
v___x_481_ = l_Lean_Expr_mvarId_x21(v_a_476_);
lean_dec(v_a_476_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v___x_481_);
v___x_483_ = v___x_479_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_481_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
else
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_494_; 
lean_dec(v_mvarId_458_);
v_a_487_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_494_ == 0)
{
v___x_489_ = v___x_475_;
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___x_475_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_492_; 
if (v_isShared_490_ == 0)
{
v___x_492_ = v___x_489_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_a_487_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
else
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_502_; 
lean_dec(v_a_470_);
lean_dec_ref(v_val_462_);
lean_dec_ref(v_type_461_);
lean_dec(v_name_460_);
lean_dec(v_mvarId_458_);
v_a_495_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_502_ == 0)
{
v___x_497_ = v___x_471_;
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_471_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_500_; 
if (v_isShared_498_ == 0)
{
v___x_500_ = v___x_497_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_a_495_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
else
{
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_510_; 
lean_dec_ref(v_val_462_);
lean_dec_ref(v_type_461_);
lean_dec(v_name_460_);
lean_dec(v_mvarId_458_);
v_a_503_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_510_ == 0)
{
v___x_505_ = v___x_469_;
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_469_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_508_; 
if (v_isShared_506_ == 0)
{
v___x_508_ = v___x_505_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_a_503_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
else
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
lean_dec_ref(v_val_462_);
lean_dec_ref(v_type_461_);
lean_dec(v_name_460_);
lean_dec(v_mvarId_458_);
v_a_511_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_518_ == 0)
{
v___x_513_ = v___x_468_;
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_468_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_a_511_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_define___lam__0___boxed(lean_object* v_mvarId_519_, lean_object* v___x_520_, lean_object* v_name_521_, lean_object* v_type_522_, lean_object* v_val_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Lean_MVarId_define___lam__0(v_mvarId_519_, v___x_520_, v_name_521_, v_type_522_, v_val_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_define(lean_object* v_mvarId_533_, lean_object* v_name_534_, lean_object* v_type_535_, lean_object* v_val_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_){
_start:
{
lean_object* v___x_542_; lean_object* v___f_543_; lean_object* v___x_544_; 
v___x_542_ = ((lean_object*)(l_Lean_MVarId_define___closed__1));
lean_inc(v_mvarId_533_);
v___f_543_ = lean_alloc_closure((void*)(l_Lean_MVarId_define___lam__0___boxed), 10, 5);
lean_closure_set(v___f_543_, 0, v_mvarId_533_);
lean_closure_set(v___f_543_, 1, v___x_542_);
lean_closure_set(v___f_543_, 2, v_name_534_);
lean_closure_set(v___f_543_, 3, v_type_535_);
lean_closure_set(v___f_543_, 4, v_val_536_);
v___x_544_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(v_mvarId_533_, v___f_543_, v_a_537_, v_a_538_, v_a_539_, v_a_540_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_define___boxed(lean_object* v_mvarId_545_, lean_object* v_name_546_, lean_object* v_type_547_, lean_object* v_val_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_MVarId_define(v_mvarId_545_, v_name_546_, v_type_547_, v_val_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_);
lean_dec(v_a_552_);
lean_dec_ref(v_a_551_);
lean_dec(v_a_550_);
lean_dec_ref(v_a_549_);
return v_res_554_;
}
}
static lean_object* _init_l_Lean_MVarId_assertExt___lam__0___closed__2(void){
_start:
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = lean_unsigned_to_nat(0u);
v___x_559_ = l_Lean_mkBVar(v___x_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertExt___lam__0(lean_object* v_mvarId_560_, lean_object* v___x_561_, lean_object* v_type_562_, lean_object* v_val_563_, lean_object* v_hName_564_, lean_object* v_name_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v___x_571_; 
lean_inc(v_mvarId_560_);
v___x_571_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_560_, v___x_561_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v___x_572_; 
lean_dec_ref(v___x_571_);
lean_inc(v_mvarId_560_);
v___x_572_ = l_Lean_MVarId_getTag(v_mvarId_560_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v___x_574_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_a_573_);
lean_dec_ref(v___x_572_);
lean_inc(v_mvarId_560_);
v___x_574_ = l_Lean_MVarId_getType(v_mvarId_560_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; lean_object* v___x_576_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_a_575_);
lean_dec_ref(v___x_574_);
lean_inc_ref(v_type_562_);
v___x_576_ = l_Lean_Meta_getLevel(v_type_562_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v_a_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; uint8_t v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v_a_577_ = lean_ctor_get(v___x_576_, 0);
lean_inc(v_a_577_);
lean_dec_ref(v___x_576_);
v___x_578_ = ((lean_object*)(l_Lean_MVarId_assertExt___lam__0___closed__1));
v___x_579_ = lean_box(0);
v___x_580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_580_, 0, v_a_577_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
v___x_581_ = l_Lean_mkConst(v___x_578_, v___x_580_);
v___x_582_ = lean_obj_once(&l_Lean_MVarId_assertExt___lam__0___closed__2, &l_Lean_MVarId_assertExt___lam__0___closed__2_once, _init_l_Lean_MVarId_assertExt___lam__0___closed__2);
lean_inc_ref(v_val_563_);
lean_inc_ref(v_type_562_);
v___x_583_ = l_Lean_mkApp3(v___x_581_, v_type_562_, v___x_582_, v_val_563_);
v___x_584_ = 0;
v___x_585_ = l_Lean_mkForall(v_hName_564_, v___x_584_, v___x_583_, v_a_575_);
v___x_586_ = l_Lean_mkForall(v_name_565_, v___x_584_, v_type_562_, v___x_585_);
v___x_587_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_586_, v_a_573_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; lean_object* v___x_589_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_a_588_);
lean_dec_ref(v___x_587_);
lean_inc_ref(v_val_563_);
v___x_589_ = l_Lean_Meta_mkEqRefl(v_val_563_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v_a_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_600_; 
v_a_590_ = lean_ctor_get(v___x_589_, 0);
lean_inc(v_a_590_);
lean_dec_ref(v___x_589_);
lean_inc(v_a_588_);
v___x_591_ = l_Lean_mkAppB(v_a_588_, v_val_563_, v_a_590_);
v___x_592_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(v_mvarId_560_, v___x_591_, v___y_567_);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_600_ == 0)
{
lean_object* v_unused_601_; 
v_unused_601_ = lean_ctor_get(v___x_592_, 0);
lean_dec(v_unused_601_);
v___x_594_ = v___x_592_;
v_isShared_595_ = v_isSharedCheck_600_;
goto v_resetjp_593_;
}
else
{
lean_dec(v___x_592_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_600_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_596_; lean_object* v___x_598_; 
v___x_596_ = l_Lean_Expr_mvarId_x21(v_a_588_);
lean_dec(v_a_588_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v___x_596_);
v___x_598_ = v___x_594_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_596_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
else
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_609_; 
lean_dec(v_a_588_);
lean_dec_ref(v_val_563_);
lean_dec(v_mvarId_560_);
v_a_602_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_609_ == 0)
{
v___x_604_ = v___x_589_;
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_589_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_a_602_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
else
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
lean_dec_ref(v_val_563_);
lean_dec(v_mvarId_560_);
v_a_610_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_617_ == 0)
{
v___x_612_ = v___x_587_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_587_);
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
else
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
lean_dec(v_a_575_);
lean_dec(v_a_573_);
lean_dec(v_name_565_);
lean_dec(v_hName_564_);
lean_dec_ref(v_val_563_);
lean_dec_ref(v_type_562_);
lean_dec(v_mvarId_560_);
v_a_618_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_625_ == 0)
{
v___x_620_ = v___x_576_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_576_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_618_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
else
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_633_; 
lean_dec(v_a_573_);
lean_dec(v_name_565_);
lean_dec(v_hName_564_);
lean_dec_ref(v_val_563_);
lean_dec_ref(v_type_562_);
lean_dec(v_mvarId_560_);
v_a_626_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_633_ == 0)
{
v___x_628_ = v___x_574_;
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_574_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_629_ == 0)
{
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_a_626_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
else
{
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_641_; 
lean_dec(v_name_565_);
lean_dec(v_hName_564_);
lean_dec_ref(v_val_563_);
lean_dec_ref(v_type_562_);
lean_dec(v_mvarId_560_);
v_a_634_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_641_ == 0)
{
v___x_636_ = v___x_572_;
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_572_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_639_; 
if (v_isShared_637_ == 0)
{
v___x_639_ = v___x_636_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_a_634_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
}
else
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_649_; 
lean_dec(v_name_565_);
lean_dec(v_hName_564_);
lean_dec_ref(v_val_563_);
lean_dec_ref(v_type_562_);
lean_dec(v_mvarId_560_);
v_a_642_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_649_ == 0)
{
v___x_644_ = v___x_571_;
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_571_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
if (v_isShared_645_ == 0)
{
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_a_642_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertExt___lam__0___boxed(lean_object* v_mvarId_650_, lean_object* v___x_651_, lean_object* v_type_652_, lean_object* v_val_653_, lean_object* v_hName_654_, lean_object* v_name_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Lean_MVarId_assertExt___lam__0(v_mvarId_650_, v___x_651_, v_type_652_, v_val_653_, v_hName_654_, v_name_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertExt(lean_object* v_mvarId_662_, lean_object* v_name_663_, lean_object* v_type_664_, lean_object* v_val_665_, lean_object* v_hName_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_){
_start:
{
lean_object* v___x_672_; lean_object* v___f_673_; lean_object* v___x_674_; 
v___x_672_ = ((lean_object*)(l_Lean_MVarId_assert___closed__1));
lean_inc(v_mvarId_662_);
v___f_673_ = lean_alloc_closure((void*)(l_Lean_MVarId_assertExt___lam__0___boxed), 11, 6);
lean_closure_set(v___f_673_, 0, v_mvarId_662_);
lean_closure_set(v___f_673_, 1, v___x_672_);
lean_closure_set(v___f_673_, 2, v_type_664_);
lean_closure_set(v___f_673_, 3, v_val_665_);
lean_closure_set(v___f_673_, 4, v_hName_666_);
lean_closure_set(v___f_673_, 5, v_name_663_);
v___x_674_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(v_mvarId_662_, v___f_673_, v_a_667_, v_a_668_, v_a_669_, v_a_670_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertExt___boxed(lean_object* v_mvarId_675_, lean_object* v_name_676_, lean_object* v_type_677_, lean_object* v_val_678_, lean_object* v_hName_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Lean_MVarId_assertExt(v_mvarId_675_, v_name_676_, v_type_677_, v_val_678_, v_hName_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_);
lean_dec(v_a_683_);
lean_dec_ref(v_a_682_);
lean_dec(v_a_681_);
lean_dec_ref(v_a_680_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__0___redArg(lean_object* v_as_686_, size_t v_sz_687_, size_t v_i_688_, lean_object* v_b_689_){
_start:
{
uint8_t v___x_691_; 
v___x_691_ = lean_usize_dec_lt(v_i_688_, v_sz_687_);
if (v___x_691_ == 0)
{
lean_object* v___x_692_; 
v___x_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_692_, 0, v_b_689_);
return v___x_692_;
}
else
{
lean_object* v_snd_693_; lean_object* v_fst_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_728_; 
v_snd_693_ = lean_ctor_get(v_b_689_, 1);
v_fst_694_ = lean_ctor_get(v_b_689_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v_b_689_);
if (v_isSharedCheck_728_ == 0)
{
v___x_696_ = v_b_689_;
v_isShared_697_ = v_isSharedCheck_728_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_snd_693_);
lean_inc(v_fst_694_);
lean_dec(v_b_689_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_728_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v_array_698_; lean_object* v_start_699_; lean_object* v_stop_700_; uint8_t v___x_701_; 
v_array_698_ = lean_ctor_get(v_snd_693_, 0);
v_start_699_ = lean_ctor_get(v_snd_693_, 1);
v_stop_700_ = lean_ctor_get(v_snd_693_, 2);
v___x_701_ = lean_nat_dec_lt(v_start_699_, v_stop_700_);
if (v___x_701_ == 0)
{
lean_object* v___x_703_; 
if (v_isShared_697_ == 0)
{
v___x_703_ = v___x_696_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_fst_694_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v_snd_693_);
v___x_703_ = v_reuseFailAlloc_705_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
lean_object* v___x_704_; 
v___x_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
return v___x_704_;
}
}
else
{
lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_724_; 
lean_inc(v_stop_700_);
lean_inc(v_start_699_);
lean_inc_ref(v_array_698_);
v_isSharedCheck_724_ = !lean_is_exclusive(v_snd_693_);
if (v_isSharedCheck_724_ == 0)
{
lean_object* v_unused_725_; lean_object* v_unused_726_; lean_object* v_unused_727_; 
v_unused_725_ = lean_ctor_get(v_snd_693_, 2);
lean_dec(v_unused_725_);
v_unused_726_ = lean_ctor_get(v_snd_693_, 1);
lean_dec(v_unused_726_);
v_unused_727_ = lean_ctor_get(v_snd_693_, 0);
lean_dec(v_unused_727_);
v___x_707_ = v_snd_693_;
v_isShared_708_ = v_isSharedCheck_724_;
goto v_resetjp_706_;
}
else
{
lean_dec(v_snd_693_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_724_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v_a_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_714_; 
v_a_709_ = lean_array_uget_borrowed(v_as_686_, v_i_688_);
v___x_710_ = lean_array_fget(v_array_698_, v_start_699_);
v___x_711_ = lean_unsigned_to_nat(1u);
v___x_712_ = lean_nat_add(v_start_699_, v___x_711_);
lean_dec(v_start_699_);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 1, v___x_712_);
v___x_714_ = v___x_707_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_array_698_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_723_, 2, v_stop_700_);
v___x_714_ = v_reuseFailAlloc_723_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_718_; 
v___x_715_ = l_Lean_mkFVar(v___x_710_);
lean_inc(v_a_709_);
v___x_716_ = l_Lean_Meta_FVarSubst_insert(v_fst_694_, v_a_709_, v___x_715_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 1, v___x_714_);
lean_ctor_set(v___x_696_, 0, v___x_716_);
v___x_718_ = v___x_696_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_716_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v___x_714_);
v___x_718_ = v_reuseFailAlloc_722_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
size_t v___x_719_; size_t v___x_720_; 
v___x_719_ = ((size_t)1ULL);
v___x_720_ = lean_usize_add(v_i_688_, v___x_719_);
v_i_688_ = v___x_720_;
v_b_689_ = v___x_718_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__0___redArg___boxed(lean_object* v_as_729_, lean_object* v_sz_730_, lean_object* v_i_731_, lean_object* v_b_732_, lean_object* v___y_733_){
_start:
{
size_t v_sz_boxed_734_; size_t v_i_boxed_735_; lean_object* v_res_736_; 
v_sz_boxed_734_ = lean_unbox_usize(v_sz_730_);
lean_dec(v_sz_730_);
v_i_boxed_735_ = lean_unbox_usize(v_i_731_);
lean_dec(v_i_731_);
v_res_736_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__0___redArg(v_as_729_, v_sz_boxed_734_, v_i_boxed_735_, v_b_732_);
lean_dec_ref(v_as_729_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertAfter(lean_object* v_mvarId_740_, lean_object* v_fvarId_741_, lean_object* v_userName_742_, lean_object* v_type_743_, lean_object* v_val_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = ((lean_object*)(l_Lean_MVarId_assertAfter___closed__1));
lean_inc(v_mvarId_740_);
v___x_751_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_740_, v___x_750_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v___x_752_; 
lean_dec_ref(v___x_751_);
v___x_752_ = l_Lean_MVarId_revertAfter(v_mvarId_740_, v_fvarId_741_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_a_753_; lean_object* v_fst_754_; lean_object* v_snd_755_; lean_object* v___x_756_; 
v_a_753_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_a_753_);
lean_dec_ref(v___x_752_);
v_fst_754_ = lean_ctor_get(v_a_753_, 0);
lean_inc(v_fst_754_);
v_snd_755_ = lean_ctor_get(v_a_753_, 1);
lean_inc(v_snd_755_);
lean_dec(v_a_753_);
v___x_756_ = l_Lean_MVarId_assert(v_snd_755_, v_userName_742_, v_type_743_, v_val_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_object* v_a_757_; uint8_t v___x_758_; lean_object* v___x_759_; 
v_a_757_ = lean_ctor_get(v___x_756_, 0);
lean_inc(v_a_757_);
lean_dec_ref(v___x_756_);
v___x_758_ = 1;
v___x_759_ = l_Lean_Meta_intro1Core(v_a_757_, v___x_758_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; lean_object* v_fst_761_; lean_object* v_snd_762_; lean_object* v___x_763_; lean_object* v___x_764_; uint8_t v___x_765_; lean_object* v___x_766_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_a_760_);
lean_dec_ref(v___x_759_);
v_fst_761_ = lean_ctor_get(v_a_760_, 0);
lean_inc(v_fst_761_);
v_snd_762_ = lean_ctor_get(v_a_760_, 1);
lean_inc(v_snd_762_);
lean_dec(v_a_760_);
v___x_763_ = lean_array_get_size(v_fst_754_);
v___x_764_ = lean_box(0);
v___x_765_ = 0;
v___x_766_ = l_Lean_Meta_introNCore(v_snd_762_, v___x_763_, v___x_764_, v___x_765_, v___x_758_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v_fst_768_; lean_object* v_snd_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_801_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_a_767_);
lean_dec_ref(v___x_766_);
v_fst_768_ = lean_ctor_get(v_a_767_, 0);
v_snd_769_ = lean_ctor_get(v_a_767_, 1);
v_isSharedCheck_801_ = !lean_is_exclusive(v_a_767_);
if (v_isSharedCheck_801_ == 0)
{
v___x_771_ = v_a_767_;
v_isShared_772_ = v_isSharedCheck_801_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_snd_769_);
lean_inc(v_fst_768_);
lean_dec(v_a_767_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_801_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_778_; 
v___x_773_ = lean_box(0);
v___x_774_ = lean_unsigned_to_nat(0u);
v___x_775_ = lean_array_get_size(v_fst_768_);
v___x_776_ = l_Array_toSubarray___redArg(v_fst_768_, v___x_774_, v___x_775_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 1, v___x_776_);
lean_ctor_set(v___x_771_, 0, v___x_773_);
v___x_778_ = v___x_771_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_773_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v___x_776_);
v___x_778_ = v_reuseFailAlloc_800_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
size_t v_sz_779_; size_t v___x_780_; lean_object* v___x_781_; 
v_sz_779_ = lean_array_size(v_fst_754_);
v___x_780_ = ((size_t)0ULL);
v___x_781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__0___redArg(v_fst_754_, v_sz_779_, v___x_780_, v___x_778_);
lean_dec(v_fst_754_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_791_; 
v_a_782_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_791_ == 0)
{
v___x_784_ = v___x_781_;
v_isShared_785_ = v_isSharedCheck_791_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___x_781_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_791_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v_fst_786_; lean_object* v___x_787_; lean_object* v___x_789_; 
v_fst_786_ = lean_ctor_get(v_a_782_, 0);
lean_inc(v_fst_786_);
lean_dec(v_a_782_);
v___x_787_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_787_, 0, v_fst_761_);
lean_ctor_set(v___x_787_, 1, v_snd_769_);
lean_ctor_set(v___x_787_, 2, v_fst_786_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 0, v___x_787_);
v___x_789_ = v___x_784_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_787_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
else
{
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_799_; 
lean_dec(v_snd_769_);
lean_dec(v_fst_761_);
v_a_792_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_799_ == 0)
{
v___x_794_ = v___x_781_;
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_781_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
if (v_isShared_795_ == 0)
{
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_a_792_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
}
}
else
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_809_; 
lean_dec(v_fst_761_);
lean_dec(v_fst_754_);
v_a_802_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_809_ == 0)
{
v___x_804_ = v___x_766_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_766_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_807_; 
if (v_isShared_805_ == 0)
{
v___x_807_ = v___x_804_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_802_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_dec(v_fst_754_);
v_a_810_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_759_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_759_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
else
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_825_; 
lean_dec(v_fst_754_);
v_a_818_ = lean_ctor_get(v___x_756_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_825_ == 0)
{
v___x_820_ = v___x_756_;
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_756_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
else
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
lean_dec_ref(v_val_744_);
lean_dec_ref(v_type_743_);
lean_dec(v_userName_742_);
v_a_826_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___x_752_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_752_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_826_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
else
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_841_; 
lean_dec_ref(v_val_744_);
lean_dec_ref(v_type_743_);
lean_dec(v_userName_742_);
lean_dec(v_fvarId_741_);
lean_dec(v_mvarId_740_);
v_a_834_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_841_ == 0)
{
v___x_836_ = v___x_751_;
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_751_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_837_ == 0)
{
v___x_839_ = v___x_836_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_a_834_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertAfter___boxed(lean_object* v_mvarId_842_, lean_object* v_fvarId_843_, lean_object* v_userName_844_, lean_object* v_type_845_, lean_object* v_val_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Lean_MVarId_assertAfter(v_mvarId_842_, v_fvarId_843_, v_userName_844_, v_type_845_, v_val_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_);
lean_dec(v_a_850_);
lean_dec_ref(v_a_849_);
lean_dec(v_a_848_);
lean_dec_ref(v_a_847_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__0(lean_object* v_as_853_, size_t v_sz_854_, size_t v_i_855_, lean_object* v_b_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__0___redArg(v_as_853_, v_sz_854_, v_i_855_, v_b_856_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__0___boxed(lean_object* v_as_863_, lean_object* v_sz_864_, lean_object* v_i_865_, lean_object* v_b_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
size_t v_sz_boxed_872_; size_t v_i_boxed_873_; lean_object* v_res_874_; 
v_sz_boxed_872_ = lean_unbox_usize(v_sz_864_);
lean_dec(v_sz_864_);
v_i_boxed_873_ = lean_unbox_usize(v_i_865_);
lean_dec(v_i_865_);
v_res_874_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__0(v_as_863_, v_sz_boxed_872_, v_i_boxed_873_, v_b_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec_ref(v_as_863_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg(lean_object* v_mvarId_875_, lean_object* v_f_876_, lean_object* v___y_877_){
_start:
{
lean_object* v___x_879_; lean_object* v_mctx_880_; lean_object* v_cache_881_; lean_object* v_zetaDeltaFVarIds_882_; lean_object* v_postponed_883_; lean_object* v_diag_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_895_; 
v___x_879_ = lean_st_ref_take(v___y_877_);
v_mctx_880_ = lean_ctor_get(v___x_879_, 0);
v_cache_881_ = lean_ctor_get(v___x_879_, 1);
v_zetaDeltaFVarIds_882_ = lean_ctor_get(v___x_879_, 2);
v_postponed_883_ = lean_ctor_get(v___x_879_, 3);
v_diag_884_ = lean_ctor_get(v___x_879_, 4);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_895_ == 0)
{
v___x_886_ = v___x_879_;
v_isShared_887_ = v_isSharedCheck_895_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_diag_884_);
lean_inc(v_postponed_883_);
lean_inc(v_zetaDeltaFVarIds_882_);
lean_inc(v_cache_881_);
lean_inc(v_mctx_880_);
lean_dec(v___x_879_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_895_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_888_; lean_object* v___x_890_; 
v___x_888_ = l_Lean_MetavarContext_modifyExprMVarLCtx(v_mctx_880_, v_mvarId_875_, v_f_876_);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 0, v___x_888_);
v___x_890_ = v___x_886_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_888_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v_cache_881_);
lean_ctor_set(v_reuseFailAlloc_894_, 2, v_zetaDeltaFVarIds_882_);
lean_ctor_set(v_reuseFailAlloc_894_, 3, v_postponed_883_);
lean_ctor_set(v_reuseFailAlloc_894_, 4, v_diag_884_);
v___x_890_ = v_reuseFailAlloc_894_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_891_ = lean_st_ref_set(v___y_877_, v___x_890_);
v___x_892_ = lean_box(0);
v___x_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
return v___x_893_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg___boxed(lean_object* v_mvarId_896_, lean_object* v_f_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg(v_mvarId_896_, v_f_897_, v___y_898_);
lean_dec(v___y_898_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1(lean_object* v_mvarId_901_, lean_object* v_f_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg(v_mvarId_901_, v_f_902_, v___y_904_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___boxed(lean_object* v_mvarId_909_, lean_object* v_f_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1(v_mvarId_909_, v_f_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg(lean_object* v_upperBound_917_, lean_object* v_hs_918_, lean_object* v_fst_919_, lean_object* v___x_920_, lean_object* v_a_921_, lean_object* v_b_922_){
_start:
{
lean_object* v_a_924_; uint8_t v___x_928_; 
v___x_928_ = lean_nat_dec_lt(v_a_921_, v_upperBound_917_);
if (v___x_928_ == 0)
{
lean_dec(v_a_921_);
return v_b_922_;
}
else
{
lean_object* v___x_929_; uint8_t v_kind_930_; uint8_t v___x_935_; uint8_t v___x_936_; 
v___x_929_ = lean_array_fget_borrowed(v_hs_918_, v_a_921_);
v_kind_930_ = lean_ctor_get_uint8(v___x_929_, sizeof(void*)*3 + 1);
v___x_935_ = 0;
v___x_936_ = l_Lean_instDecidableEqLocalDeclKind(v_kind_930_, v___x_935_);
if (v___x_936_ == 0)
{
goto v___jp_931_;
}
else
{
lean_object* v___x_937_; uint8_t v___x_938_; 
v___x_937_ = lean_unsigned_to_nat(0u);
v___x_938_ = lean_nat_dec_eq(v___x_920_, v___x_937_);
if (v___x_938_ == 0)
{
v_a_924_ = v_b_922_;
goto v___jp_923_;
}
else
{
goto v___jp_931_;
}
}
v___jp_931_:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_932_ = lean_box(0);
v___x_933_ = lean_array_get_borrowed(v___x_932_, v_fst_919_, v_a_921_);
lean_inc(v___x_933_);
v___x_934_ = l_Lean_LocalContext_setKind(v_b_922_, v___x_933_, v_kind_930_);
v_a_924_ = v___x_934_;
goto v___jp_923_;
}
}
v___jp_923_:
{
lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_925_ = lean_unsigned_to_nat(1u);
v___x_926_ = lean_nat_add(v_a_921_, v___x_925_);
lean_dec(v_a_921_);
v_a_921_ = v___x_926_;
v_b_922_ = v_a_924_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg___boxed(lean_object* v_upperBound_939_, lean_object* v_hs_940_, lean_object* v_fst_941_, lean_object* v___x_942_, lean_object* v_a_943_, lean_object* v_b_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg(v_upperBound_939_, v_hs_940_, v_fst_941_, v___x_942_, v_a_943_, v_b_944_);
lean_dec(v___x_942_);
lean_dec_ref(v_fst_941_);
lean_dec_ref(v_hs_940_);
lean_dec(v_upperBound_939_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___lam__0(lean_object* v___x_946_, lean_object* v_hs_947_, lean_object* v_fst_948_, lean_object* v___x_949_, lean_object* v_lctx_950_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg(v___x_946_, v_hs_947_, v_fst_948_, v___x_946_, v___x_949_, v_lctx_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___lam__0___boxed(lean_object* v___x_952_, lean_object* v_hs_953_, lean_object* v_fst_954_, lean_object* v___x_955_, lean_object* v_lctx_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_MVarId_assertHypotheses___lam__0(v___x_952_, v_hs_953_, v_fst_954_, v___x_955_, v_lctx_956_);
lean_dec_ref(v_fst_954_);
lean_dec_ref(v_hs_953_);
lean_dec(v___x_952_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__3(lean_object* v_as_958_, size_t v_i_959_, size_t v_stop_960_, lean_object* v_b_961_){
_start:
{
uint8_t v___x_962_; 
v___x_962_ = lean_usize_dec_eq(v_i_959_, v_stop_960_);
if (v___x_962_ == 0)
{
size_t v___x_963_; size_t v___x_964_; lean_object* v___x_965_; lean_object* v_userName_966_; lean_object* v_type_967_; uint8_t v_binderInfo_968_; lean_object* v___x_969_; 
v___x_963_ = ((size_t)1ULL);
v___x_964_ = lean_usize_sub(v_i_959_, v___x_963_);
v___x_965_ = lean_array_uget_borrowed(v_as_958_, v___x_964_);
v_userName_966_ = lean_ctor_get(v___x_965_, 0);
v_type_967_ = lean_ctor_get(v___x_965_, 1);
v_binderInfo_968_ = lean_ctor_get_uint8(v___x_965_, sizeof(void*)*3);
lean_inc_ref(v_type_967_);
lean_inc(v_userName_966_);
v___x_969_ = l_Lean_Expr_forallE___override(v_userName_966_, v_type_967_, v_b_961_, v_binderInfo_968_);
v_i_959_ = v___x_964_;
v_b_961_ = v___x_969_;
goto _start;
}
else
{
return v_b_961_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__3___boxed(lean_object* v_as_971_, lean_object* v_i_972_, lean_object* v_stop_973_, lean_object* v_b_974_){
_start:
{
size_t v_i_boxed_975_; size_t v_stop_boxed_976_; lean_object* v_res_977_; 
v_i_boxed_975_ = lean_unbox_usize(v_i_972_);
lean_dec(v_i_972_);
v_stop_boxed_976_ = lean_unbox_usize(v_stop_973_);
lean_dec(v_stop_973_);
v_res_977_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__3(v_as_971_, v_i_boxed_975_, v_stop_boxed_976_, v_b_974_);
lean_dec_ref(v_as_971_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2(lean_object* v_as_978_, size_t v_i_979_, size_t v_stop_980_, lean_object* v_b_981_){
_start:
{
uint8_t v___x_982_; 
v___x_982_ = lean_usize_dec_eq(v_i_979_, v_stop_980_);
if (v___x_982_ == 0)
{
lean_object* v___x_983_; lean_object* v_value_984_; lean_object* v___x_985_; size_t v___x_986_; size_t v___x_987_; 
v___x_983_ = lean_array_uget_borrowed(v_as_978_, v_i_979_);
v_value_984_ = lean_ctor_get(v___x_983_, 2);
lean_inc_ref(v_value_984_);
v___x_985_ = l_Lean_Expr_app___override(v_b_981_, v_value_984_);
v___x_986_ = ((size_t)1ULL);
v___x_987_ = lean_usize_add(v_i_979_, v___x_986_);
v_i_979_ = v___x_987_;
v_b_981_ = v___x_985_;
goto _start;
}
else
{
return v_b_981_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2___boxed(lean_object* v_as_989_, lean_object* v_i_990_, lean_object* v_stop_991_, lean_object* v_b_992_){
_start:
{
size_t v_i_boxed_993_; size_t v_stop_boxed_994_; lean_object* v_res_995_; 
v_i_boxed_993_ = lean_unbox_usize(v_i_990_);
lean_dec(v_i_990_);
v_stop_boxed_994_ = lean_unbox_usize(v_stop_991_);
lean_dec(v_stop_991_);
v_res_995_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2(v_as_989_, v_i_boxed_993_, v_stop_boxed_994_, v_b_992_);
lean_dec_ref(v_as_989_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___lam__1(lean_object* v_mvarId_996_, lean_object* v___x_997_, lean_object* v___x_998_, uint8_t v___x_999_, lean_object* v_hs_1000_, lean_object* v___x_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___x_1028_; 
lean_inc(v_mvarId_996_);
v___x_1028_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_996_, v___x_997_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v___x_1029_; 
lean_dec_ref(v___x_1028_);
lean_inc(v_mvarId_996_);
v___x_1029_ = l_Lean_MVarId_getTag(v_mvarId_996_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v_a_1030_; lean_object* v___x_1031_; 
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_a_1030_);
lean_dec_ref(v___x_1029_);
lean_inc(v_mvarId_996_);
v___x_1031_ = l_Lean_MVarId_getType(v_mvarId_996_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; lean_object* v___y_1034_; uint8_t v___x_1053_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_a_1032_);
lean_dec_ref(v___x_1031_);
v___x_1053_ = lean_nat_dec_lt(v___x_1001_, v___x_998_);
if (v___x_1053_ == 0)
{
v___y_1034_ = v_a_1032_;
goto v___jp_1033_;
}
else
{
size_t v___x_1054_; size_t v___x_1055_; lean_object* v___x_1056_; 
v___x_1054_ = lean_usize_of_nat(v___x_998_);
v___x_1055_ = ((size_t)0ULL);
v___x_1056_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__3(v_hs_1000_, v___x_1054_, v___x_1055_, v_a_1032_);
v___y_1034_ = v___x_1056_;
goto v___jp_1033_;
}
v___jp_1033_:
{
lean_object* v___x_1035_; 
v___x_1035_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_1034_, v_a_1030_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; uint8_t v___x_1037_; 
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_a_1036_);
lean_dec_ref(v___x_1035_);
v___x_1037_ = lean_nat_dec_lt(v___x_1001_, v___x_998_);
if (v___x_1037_ == 0)
{
lean_inc(v_a_1036_);
v___y_1008_ = v_a_1036_;
v___y_1009_ = v_a_1036_;
goto v___jp_1007_;
}
else
{
uint8_t v___x_1038_; 
v___x_1038_ = lean_nat_dec_le(v___x_998_, v___x_998_);
if (v___x_1038_ == 0)
{
if (v___x_1037_ == 0)
{
lean_inc(v_a_1036_);
v___y_1008_ = v_a_1036_;
v___y_1009_ = v_a_1036_;
goto v___jp_1007_;
}
else
{
size_t v___x_1039_; size_t v___x_1040_; lean_object* v___x_1041_; 
v___x_1039_ = ((size_t)0ULL);
v___x_1040_ = lean_usize_of_nat(v___x_998_);
lean_inc(v_a_1036_);
v___x_1041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2(v_hs_1000_, v___x_1039_, v___x_1040_, v_a_1036_);
v___y_1008_ = v_a_1036_;
v___y_1009_ = v___x_1041_;
goto v___jp_1007_;
}
}
else
{
size_t v___x_1042_; size_t v___x_1043_; lean_object* v___x_1044_; 
v___x_1042_ = ((size_t)0ULL);
v___x_1043_ = lean_usize_of_nat(v___x_998_);
lean_inc(v_a_1036_);
v___x_1044_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2(v_hs_1000_, v___x_1042_, v___x_1043_, v_a_1036_);
v___y_1008_ = v_a_1036_;
v___y_1009_ = v___x_1044_;
goto v___jp_1007_;
}
}
}
else
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
lean_dec(v___x_1001_);
lean_dec_ref(v_hs_1000_);
lean_dec(v___x_998_);
lean_dec(v_mvarId_996_);
v_a_1045_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___x_1035_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1035_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1045_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
}
else
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
lean_dec(v_a_1030_);
lean_dec(v___x_1001_);
lean_dec_ref(v_hs_1000_);
lean_dec(v___x_998_);
lean_dec(v_mvarId_996_);
v_a_1057_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1059_ = v___x_1031_;
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_1031_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
if (v_isShared_1060_ == 0)
{
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1057_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
else
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1072_; 
lean_dec(v___x_1001_);
lean_dec_ref(v_hs_1000_);
lean_dec(v___x_998_);
lean_dec(v_mvarId_996_);
v_a_1065_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1067_ = v___x_1029_;
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1029_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1068_ == 0)
{
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_a_1065_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
else
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
lean_dec(v___x_1001_);
lean_dec_ref(v_hs_1000_);
lean_dec(v___x_998_);
lean_dec(v_mvarId_996_);
v_a_1073_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v___x_1028_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1028_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1073_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
v___jp_1007_:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; uint8_t v___x_1013_; lean_object* v___x_1014_; 
v___x_1010_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(v_mvarId_996_, v___y_1009_, v___y_1003_);
lean_dec_ref(v___x_1010_);
v___x_1011_ = l_Lean_Expr_mvarId_x21(v___y_1008_);
lean_dec_ref(v___y_1008_);
v___x_1012_ = lean_box(0);
v___x_1013_ = 1;
lean_inc(v___x_998_);
v___x_1014_ = l_Lean_Meta_introNCore(v___x_1011_, v___x_998_, v___x_1012_, v___x_999_, v___x_1013_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; lean_object* v_fst_1016_; lean_object* v_snd_1017_; lean_object* v___f_1018_; lean_object* v___x_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_a_1015_);
lean_dec_ref(v___x_1014_);
v_fst_1016_ = lean_ctor_get(v_a_1015_, 0);
v_snd_1017_ = lean_ctor_get(v_a_1015_, 1);
lean_inc(v_fst_1016_);
v___f_1018_ = lean_alloc_closure((void*)(l_Lean_MVarId_assertHypotheses___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1018_, 0, v___x_998_);
lean_closure_set(v___f_1018_, 1, v_hs_1000_);
lean_closure_set(v___f_1018_, 2, v_fst_1016_);
lean_closure_set(v___f_1018_, 3, v___x_1001_);
lean_inc(v_snd_1017_);
v___x_1019_ = l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg(v_snd_1017_, v___f_1018_, v___y_1003_);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1026_ == 0)
{
lean_object* v_unused_1027_; 
v_unused_1027_ = lean_ctor_get(v___x_1019_, 0);
lean_dec(v_unused_1027_);
v___x_1021_ = v___x_1019_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_dec(v___x_1019_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 0, v_a_1015_);
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1015_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
else
{
lean_dec(v___x_1001_);
lean_dec_ref(v_hs_1000_);
lean_dec(v___x_998_);
return v___x_1014_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___lam__1___boxed(lean_object* v_mvarId_1081_, lean_object* v___x_1082_, lean_object* v___x_1083_, lean_object* v___x_1084_, lean_object* v_hs_1085_, lean_object* v___x_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
uint8_t v___x_3359__boxed_1092_; lean_object* v_res_1093_; 
v___x_3359__boxed_1092_ = lean_unbox(v___x_1084_);
v_res_1093_ = l_Lean_MVarId_assertHypotheses___lam__1(v_mvarId_1081_, v___x_1082_, v___x_1083_, v___x_3359__boxed_1092_, v_hs_1085_, v___x_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses(lean_object* v_mvarId_1099_, lean_object* v_hs_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; uint8_t v___x_1108_; 
v___x_1106_ = lean_array_get_size(v_hs_1100_);
v___x_1107_ = lean_unsigned_to_nat(0u);
v___x_1108_ = lean_nat_dec_eq(v___x_1106_, v___x_1107_);
if (v___x_1108_ == 0)
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___f_1111_; lean_object* v___x_1112_; 
v___x_1109_ = ((lean_object*)(l_Lean_MVarId_assertHypotheses___closed__1));
v___x_1110_ = lean_box(v___x_1108_);
lean_inc(v_mvarId_1099_);
v___f_1111_ = lean_alloc_closure((void*)(l_Lean_MVarId_assertHypotheses___lam__1___boxed), 11, 6);
lean_closure_set(v___f_1111_, 0, v_mvarId_1099_);
lean_closure_set(v___f_1111_, 1, v___x_1109_);
lean_closure_set(v___f_1111_, 2, v___x_1106_);
lean_closure_set(v___f_1111_, 3, v___x_1110_);
lean_closure_set(v___f_1111_, 4, v_hs_1100_);
lean_closure_set(v___f_1111_, 5, v___x_1107_);
v___x_1112_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(v_mvarId_1099_, v___f_1111_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_);
return v___x_1112_;
}
else
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
lean_dec_ref(v_hs_1100_);
v___x_1113_ = ((lean_object*)(l_Lean_MVarId_assertHypotheses___closed__2));
v___x_1114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
lean_ctor_set(v___x_1114_, 1, v_mvarId_1099_);
v___x_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1114_);
return v___x_1115_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___boxed(lean_object* v_mvarId_1116_, lean_object* v_hs_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Lean_MVarId_assertHypotheses(v_mvarId_1116_, v_hs_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_);
lean_dec(v_a_1121_);
lean_dec_ref(v_a_1120_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0(lean_object* v_upperBound_1124_, lean_object* v_hs_1125_, lean_object* v_fst_1126_, lean_object* v___x_1127_, lean_object* v_inst_1128_, lean_object* v_R_1129_, lean_object* v_a_1130_, lean_object* v_b_1131_, lean_object* v_c_1132_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg(v_upperBound_1124_, v_hs_1125_, v_fst_1126_, v___x_1127_, v_a_1130_, v_b_1131_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___boxed(lean_object* v_upperBound_1134_, lean_object* v_hs_1135_, lean_object* v_fst_1136_, lean_object* v___x_1137_, lean_object* v_inst_1138_, lean_object* v_R_1139_, lean_object* v_a_1140_, lean_object* v_b_1141_, lean_object* v_c_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0(v_upperBound_1134_, v_hs_1135_, v_fst_1136_, v___x_1137_, v_inst_1138_, v_R_1139_, v_a_1140_, v_b_1141_, v_c_1142_);
lean_dec(v___x_1137_);
lean_dec_ref(v_fst_1136_);
lean_dec_ref(v_hs_1135_);
lean_dec(v_upperBound_1134_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___lam__0(lean_object* v_e_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
uint8_t v___x_1151_; 
v___x_1151_ = l_Lean_Expr_isFVar(v_e_1144_);
if (v___x_1151_ == 0)
{
uint8_t v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1152_ = l_Lean_Expr_hasFVar(v_e_1144_);
v___x_1153_ = lean_box(v___x_1152_);
v___x_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
return v___x_1154_;
}
else
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1155_ = l_Lean_Expr_fvarId_x21(v_e_1144_);
v___x_1156_ = l_Lean_FVarId_getDecl___redArg(v___x_1155_, v___y_1146_, v___y_1148_, v___y_1149_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1173_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1159_ = v___x_1156_;
v_isShared_1160_ = v_isSharedCheck_1173_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1156_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1173_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1161_; lean_object* v_snd_1163_; lean_object* v___x_1170_; lean_object* v___x_1171_; uint8_t v___x_1172_; 
v___x_1161_ = lean_st_ref_take(v___y_1145_);
v___x_1170_ = l_Lean_LocalDecl_index(v___x_1161_);
v___x_1171_ = l_Lean_LocalDecl_index(v_a_1157_);
v___x_1172_ = lean_nat_dec_lt(v___x_1170_, v___x_1171_);
lean_dec(v___x_1171_);
lean_dec(v___x_1170_);
if (v___x_1172_ == 0)
{
lean_dec(v_a_1157_);
v_snd_1163_ = v___x_1161_;
goto v___jp_1162_;
}
else
{
lean_dec(v___x_1161_);
v_snd_1163_ = v_a_1157_;
goto v___jp_1162_;
}
v___jp_1162_:
{
lean_object* v___x_1164_; uint8_t v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1168_; 
v___x_1164_ = lean_st_ref_set(v___y_1145_, v_snd_1163_);
v___x_1165_ = 0;
v___x_1166_ = lean_box(v___x_1165_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v___x_1166_);
v___x_1168_ = v___x_1159_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1166_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
else
{
lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1181_; 
v_a_1174_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1176_ = v___x_1156_;
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_dec(v___x_1156_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1179_; 
if (v_isShared_1177_ == 0)
{
v___x_1179_ = v___x_1176_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1174_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___lam__0___boxed(lean_object* v_e_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___lam__0(v_e_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec(v___y_1183_);
lean_dec_ref(v_e_1182_);
return v_res_1189_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__3___redArg(lean_object* v_a_1190_, lean_object* v_x_1191_){
_start:
{
if (lean_obj_tag(v_x_1191_) == 0)
{
uint8_t v___x_1192_; 
v___x_1192_ = 0;
return v___x_1192_;
}
else
{
lean_object* v_key_1193_; lean_object* v_tail_1194_; uint8_t v___x_1195_; 
v_key_1193_ = lean_ctor_get(v_x_1191_, 0);
v_tail_1194_ = lean_ctor_get(v_x_1191_, 2);
v___x_1195_ = lean_expr_eqv(v_key_1193_, v_a_1190_);
if (v___x_1195_ == 0)
{
v_x_1191_ = v_tail_1194_;
goto _start;
}
else
{
return v___x_1195_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_a_1197_, lean_object* v_x_1198_){
_start:
{
uint8_t v_res_1199_; lean_object* v_r_1200_; 
v_res_1199_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__3___redArg(v_a_1197_, v_x_1198_);
lean_dec(v_x_1198_);
lean_dec_ref(v_a_1197_);
v_r_1200_ = lean_box(v_res_1199_);
return v_r_1200_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__5___redArg(lean_object* v_a_1201_, lean_object* v_b_1202_, lean_object* v_x_1203_){
_start:
{
if (lean_obj_tag(v_x_1203_) == 0)
{
lean_dec(v_b_1202_);
lean_dec_ref(v_a_1201_);
return v_x_1203_;
}
else
{
lean_object* v_key_1204_; lean_object* v_value_1205_; lean_object* v_tail_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1218_; 
v_key_1204_ = lean_ctor_get(v_x_1203_, 0);
v_value_1205_ = lean_ctor_get(v_x_1203_, 1);
v_tail_1206_ = lean_ctor_get(v_x_1203_, 2);
v_isSharedCheck_1218_ = !lean_is_exclusive(v_x_1203_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1208_ = v_x_1203_;
v_isShared_1209_ = v_isSharedCheck_1218_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_tail_1206_);
lean_inc(v_value_1205_);
lean_inc(v_key_1204_);
lean_dec(v_x_1203_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1218_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
uint8_t v___x_1210_; 
v___x_1210_ = lean_expr_eqv(v_key_1204_, v_a_1201_);
if (v___x_1210_ == 0)
{
lean_object* v___x_1211_; lean_object* v___x_1213_; 
v___x_1211_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__5___redArg(v_a_1201_, v_b_1202_, v_tail_1206_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 2, v___x_1211_);
v___x_1213_ = v___x_1208_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_key_1204_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v_value_1205_);
lean_ctor_set(v_reuseFailAlloc_1214_, 2, v___x_1211_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
else
{
lean_object* v___x_1216_; 
lean_dec(v_value_1205_);
lean_dec(v_key_1204_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 1, v_b_1202_);
lean_ctor_set(v___x_1208_, 0, v_a_1201_);
v___x_1216_ = v___x_1208_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_a_1201_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v_b_1202_);
lean_ctor_set(v_reuseFailAlloc_1217_, 2, v_tail_1206_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_x_1219_, lean_object* v_x_1220_){
_start:
{
if (lean_obj_tag(v_x_1220_) == 0)
{
return v_x_1219_;
}
else
{
lean_object* v_key_1221_; lean_object* v_value_1222_; lean_object* v_tail_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1246_; 
v_key_1221_ = lean_ctor_get(v_x_1220_, 0);
v_value_1222_ = lean_ctor_get(v_x_1220_, 1);
v_tail_1223_ = lean_ctor_get(v_x_1220_, 2);
v_isSharedCheck_1246_ = !lean_is_exclusive(v_x_1220_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1225_ = v_x_1220_;
v_isShared_1226_ = v_isSharedCheck_1246_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_tail_1223_);
lean_inc(v_value_1222_);
lean_inc(v_key_1221_);
lean_dec(v_x_1220_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1246_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1227_; uint64_t v___x_1228_; uint64_t v___x_1229_; uint64_t v___x_1230_; uint64_t v_fold_1231_; uint64_t v___x_1232_; uint64_t v___x_1233_; uint64_t v___x_1234_; size_t v___x_1235_; size_t v___x_1236_; size_t v___x_1237_; size_t v___x_1238_; size_t v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1242_; 
v___x_1227_ = lean_array_get_size(v_x_1219_);
v___x_1228_ = l_Lean_Expr_hash(v_key_1221_);
v___x_1229_ = 32ULL;
v___x_1230_ = lean_uint64_shift_right(v___x_1228_, v___x_1229_);
v_fold_1231_ = lean_uint64_xor(v___x_1228_, v___x_1230_);
v___x_1232_ = 16ULL;
v___x_1233_ = lean_uint64_shift_right(v_fold_1231_, v___x_1232_);
v___x_1234_ = lean_uint64_xor(v_fold_1231_, v___x_1233_);
v___x_1235_ = lean_uint64_to_usize(v___x_1234_);
v___x_1236_ = lean_usize_of_nat(v___x_1227_);
v___x_1237_ = ((size_t)1ULL);
v___x_1238_ = lean_usize_sub(v___x_1236_, v___x_1237_);
v___x_1239_ = lean_usize_land(v___x_1235_, v___x_1238_);
v___x_1240_ = lean_array_uget_borrowed(v_x_1219_, v___x_1239_);
lean_inc(v___x_1240_);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 2, v___x_1240_);
v___x_1242_ = v___x_1225_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_key_1221_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v_value_1222_);
lean_ctor_set(v_reuseFailAlloc_1245_, 2, v___x_1240_);
v___x_1242_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
lean_object* v___x_1243_; 
v___x_1243_ = lean_array_uset(v_x_1219_, v___x_1239_, v___x_1242_);
v_x_1219_ = v___x_1243_;
v_x_1220_ = v_tail_1223_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__4_spec__5___redArg(lean_object* v_i_1247_, lean_object* v_source_1248_, lean_object* v_target_1249_){
_start:
{
lean_object* v___x_1250_; uint8_t v___x_1251_; 
v___x_1250_ = lean_array_get_size(v_source_1248_);
v___x_1251_ = lean_nat_dec_lt(v_i_1247_, v___x_1250_);
if (v___x_1251_ == 0)
{
lean_dec_ref(v_source_1248_);
lean_dec(v_i_1247_);
return v_target_1249_;
}
else
{
lean_object* v_es_1252_; lean_object* v___x_1253_; lean_object* v_source_1254_; lean_object* v_target_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v_es_1252_ = lean_array_fget(v_source_1248_, v_i_1247_);
v___x_1253_ = lean_box(0);
v_source_1254_ = lean_array_fset(v_source_1248_, v_i_1247_, v___x_1253_);
v_target_1255_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_target_1249_, v_es_1252_);
v___x_1256_ = lean_unsigned_to_nat(1u);
v___x_1257_ = lean_nat_add(v_i_1247_, v___x_1256_);
lean_dec(v_i_1247_);
v_i_1247_ = v___x_1257_;
v_source_1248_ = v_source_1254_;
v_target_1249_ = v_target_1255_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__4___redArg(lean_object* v_data_1259_){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v_nbuckets_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1260_ = lean_array_get_size(v_data_1259_);
v___x_1261_ = lean_unsigned_to_nat(2u);
v_nbuckets_1262_ = lean_nat_mul(v___x_1260_, v___x_1261_);
v___x_1263_ = lean_unsigned_to_nat(0u);
v___x_1264_ = lean_box(0);
v___x_1265_ = lean_mk_array(v_nbuckets_1262_, v___x_1264_);
v___x_1266_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__4_spec__5___redArg(v___x_1263_, v_data_1259_, v___x_1265_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1___redArg(lean_object* v_m_1267_, lean_object* v_a_1268_, lean_object* v_b_1269_){
_start:
{
lean_object* v_size_1270_; lean_object* v_buckets_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1314_; 
v_size_1270_ = lean_ctor_get(v_m_1267_, 0);
v_buckets_1271_ = lean_ctor_get(v_m_1267_, 1);
v_isSharedCheck_1314_ = !lean_is_exclusive(v_m_1267_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1273_ = v_m_1267_;
v_isShared_1274_ = v_isSharedCheck_1314_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_buckets_1271_);
lean_inc(v_size_1270_);
lean_dec(v_m_1267_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1314_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1275_; uint64_t v___x_1276_; uint64_t v___x_1277_; uint64_t v___x_1278_; uint64_t v_fold_1279_; uint64_t v___x_1280_; uint64_t v___x_1281_; uint64_t v___x_1282_; size_t v___x_1283_; size_t v___x_1284_; size_t v___x_1285_; size_t v___x_1286_; size_t v___x_1287_; lean_object* v_bkt_1288_; uint8_t v___x_1289_; 
v___x_1275_ = lean_array_get_size(v_buckets_1271_);
v___x_1276_ = l_Lean_Expr_hash(v_a_1268_);
v___x_1277_ = 32ULL;
v___x_1278_ = lean_uint64_shift_right(v___x_1276_, v___x_1277_);
v_fold_1279_ = lean_uint64_xor(v___x_1276_, v___x_1278_);
v___x_1280_ = 16ULL;
v___x_1281_ = lean_uint64_shift_right(v_fold_1279_, v___x_1280_);
v___x_1282_ = lean_uint64_xor(v_fold_1279_, v___x_1281_);
v___x_1283_ = lean_uint64_to_usize(v___x_1282_);
v___x_1284_ = lean_usize_of_nat(v___x_1275_);
v___x_1285_ = ((size_t)1ULL);
v___x_1286_ = lean_usize_sub(v___x_1284_, v___x_1285_);
v___x_1287_ = lean_usize_land(v___x_1283_, v___x_1286_);
v_bkt_1288_ = lean_array_uget_borrowed(v_buckets_1271_, v___x_1287_);
v___x_1289_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__3___redArg(v_a_1268_, v_bkt_1288_);
if (v___x_1289_ == 0)
{
lean_object* v___x_1290_; lean_object* v_size_x27_1291_; lean_object* v___x_1292_; lean_object* v_buckets_x27_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; uint8_t v___x_1299_; 
v___x_1290_ = lean_unsigned_to_nat(1u);
v_size_x27_1291_ = lean_nat_add(v_size_1270_, v___x_1290_);
lean_dec(v_size_1270_);
lean_inc(v_bkt_1288_);
v___x_1292_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1292_, 0, v_a_1268_);
lean_ctor_set(v___x_1292_, 1, v_b_1269_);
lean_ctor_set(v___x_1292_, 2, v_bkt_1288_);
v_buckets_x27_1293_ = lean_array_uset(v_buckets_1271_, v___x_1287_, v___x_1292_);
v___x_1294_ = lean_unsigned_to_nat(4u);
v___x_1295_ = lean_nat_mul(v_size_x27_1291_, v___x_1294_);
v___x_1296_ = lean_unsigned_to_nat(3u);
v___x_1297_ = lean_nat_div(v___x_1295_, v___x_1296_);
lean_dec(v___x_1295_);
v___x_1298_ = lean_array_get_size(v_buckets_x27_1293_);
v___x_1299_ = lean_nat_dec_le(v___x_1297_, v___x_1298_);
lean_dec(v___x_1297_);
if (v___x_1299_ == 0)
{
lean_object* v_val_1300_; lean_object* v___x_1302_; 
v_val_1300_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__4___redArg(v_buckets_x27_1293_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 1, v_val_1300_);
lean_ctor_set(v___x_1273_, 0, v_size_x27_1291_);
v___x_1302_ = v___x_1273_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_size_x27_1291_);
lean_ctor_set(v_reuseFailAlloc_1303_, 1, v_val_1300_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
else
{
lean_object* v___x_1305_; 
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 1, v_buckets_x27_1293_);
lean_ctor_set(v___x_1273_, 0, v_size_x27_1291_);
v___x_1305_ = v___x_1273_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_size_x27_1291_);
lean_ctor_set(v_reuseFailAlloc_1306_, 1, v_buckets_x27_1293_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
else
{
lean_object* v___x_1307_; lean_object* v_buckets_x27_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1312_; 
lean_inc(v_bkt_1288_);
v___x_1307_ = lean_box(0);
v_buckets_x27_1308_ = lean_array_uset(v_buckets_1271_, v___x_1287_, v___x_1307_);
v___x_1309_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__5___redArg(v_a_1268_, v_b_1269_, v_bkt_1288_);
v___x_1310_ = lean_array_uset(v_buckets_x27_1308_, v___x_1287_, v___x_1309_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 1, v___x_1310_);
v___x_1312_ = v___x_1273_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_size_1270_);
lean_ctor_set(v_reuseFailAlloc_1313_, 1, v___x_1310_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0_spec__1___redArg(lean_object* v_a_1315_, lean_object* v_x_1316_){
_start:
{
if (lean_obj_tag(v_x_1316_) == 0)
{
lean_object* v___x_1317_; 
v___x_1317_ = lean_box(0);
return v___x_1317_;
}
else
{
lean_object* v_key_1318_; lean_object* v_value_1319_; lean_object* v_tail_1320_; uint8_t v___x_1321_; 
v_key_1318_ = lean_ctor_get(v_x_1316_, 0);
v_value_1319_ = lean_ctor_get(v_x_1316_, 1);
v_tail_1320_ = lean_ctor_get(v_x_1316_, 2);
v___x_1321_ = lean_expr_eqv(v_key_1318_, v_a_1315_);
if (v___x_1321_ == 0)
{
v_x_1316_ = v_tail_1320_;
goto _start;
}
else
{
lean_object* v___x_1323_; 
lean_inc(v_value_1319_);
v___x_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1323_, 0, v_value_1319_);
return v___x_1323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_a_1324_, lean_object* v_x_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0_spec__1___redArg(v_a_1324_, v_x_1325_);
lean_dec(v_x_1325_);
lean_dec_ref(v_a_1324_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0___redArg(lean_object* v_m_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v_buckets_1329_; lean_object* v___x_1330_; uint64_t v___x_1331_; uint64_t v___x_1332_; uint64_t v___x_1333_; uint64_t v_fold_1334_; uint64_t v___x_1335_; uint64_t v___x_1336_; uint64_t v___x_1337_; size_t v___x_1338_; size_t v___x_1339_; size_t v___x_1340_; size_t v___x_1341_; size_t v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v_buckets_1329_ = lean_ctor_get(v_m_1327_, 1);
v___x_1330_ = lean_array_get_size(v_buckets_1329_);
v___x_1331_ = l_Lean_Expr_hash(v_a_1328_);
v___x_1332_ = 32ULL;
v___x_1333_ = lean_uint64_shift_right(v___x_1331_, v___x_1332_);
v_fold_1334_ = lean_uint64_xor(v___x_1331_, v___x_1333_);
v___x_1335_ = 16ULL;
v___x_1336_ = lean_uint64_shift_right(v_fold_1334_, v___x_1335_);
v___x_1337_ = lean_uint64_xor(v_fold_1334_, v___x_1336_);
v___x_1338_ = lean_uint64_to_usize(v___x_1337_);
v___x_1339_ = lean_usize_of_nat(v___x_1330_);
v___x_1340_ = ((size_t)1ULL);
v___x_1341_ = lean_usize_sub(v___x_1339_, v___x_1340_);
v___x_1342_ = lean_usize_land(v___x_1338_, v___x_1341_);
v___x_1343_ = lean_array_uget_borrowed(v_buckets_1329_, v___x_1342_);
v___x_1344_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0_spec__1___redArg(v_a_1328_, v___x_1343_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0___redArg___boxed(lean_object* v_m_1345_, lean_object* v_a_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0___redArg(v_m_1345_, v_a_1346_);
lean_dec_ref(v_a_1346_);
lean_dec_ref(v_m_1345_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0(lean_object* v_g_1348_, lean_object* v_e_1349_, lean_object* v_a_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v_a_1358_; lean_object* v___y_1364_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1366_ = lean_st_ref_get(v_a_1350_);
v___x_1367_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0___redArg(v___x_1366_, v_e_1349_);
lean_dec(v___x_1366_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v___x_1368_; 
lean_inc_ref(v_g_1348_);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
lean_inc(v___y_1351_);
lean_inc_ref(v_e_1349_);
v___x_1368_ = lean_apply_7(v_g_1348_, v_e_1349_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, lean_box(0));
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; lean_object* v_d_1371_; lean_object* v_b_1372_; lean_object* v___y_1373_; uint8_t v___x_1376_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_a_1369_);
lean_dec_ref(v___x_1368_);
v___x_1376_ = lean_unbox(v_a_1369_);
lean_dec(v_a_1369_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; 
lean_dec_ref(v_g_1348_);
v___x_1377_ = lean_box(0);
v_a_1358_ = v___x_1377_;
goto v___jp_1357_;
}
else
{
switch(lean_obj_tag(v_e_1349_))
{
case 7:
{
lean_object* v_binderType_1378_; lean_object* v_body_1379_; 
v_binderType_1378_ = lean_ctor_get(v_e_1349_, 1);
v_body_1379_ = lean_ctor_get(v_e_1349_, 2);
lean_inc_ref(v_body_1379_);
lean_inc_ref(v_binderType_1378_);
v_d_1371_ = v_binderType_1378_;
v_b_1372_ = v_body_1379_;
v___y_1373_ = v_a_1350_;
goto v___jp_1370_;
}
case 6:
{
lean_object* v_binderType_1380_; lean_object* v_body_1381_; 
v_binderType_1380_ = lean_ctor_get(v_e_1349_, 1);
v_body_1381_ = lean_ctor_get(v_e_1349_, 2);
lean_inc_ref(v_body_1381_);
lean_inc_ref(v_binderType_1380_);
v_d_1371_ = v_binderType_1380_;
v_b_1372_ = v_body_1381_;
v___y_1373_ = v_a_1350_;
goto v___jp_1370_;
}
case 8:
{
lean_object* v_type_1382_; lean_object* v_value_1383_; lean_object* v_body_1384_; lean_object* v___x_1385_; 
v_type_1382_ = lean_ctor_get(v_e_1349_, 1);
v_value_1383_ = lean_ctor_get(v_e_1349_, 2);
v_body_1384_ = lean_ctor_get(v_e_1349_, 3);
lean_inc_ref(v_type_1382_);
lean_inc_ref(v_g_1348_);
v___x_1385_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0(v_g_1348_, v_type_1382_, v_a_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v___x_1386_; 
lean_dec_ref(v___x_1385_);
lean_inc_ref(v_value_1383_);
lean_inc_ref(v_g_1348_);
v___x_1386_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0(v_g_1348_, v_value_1383_, v_a_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v___x_1387_; 
lean_dec_ref(v___x_1386_);
lean_inc_ref(v_body_1384_);
v___x_1387_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0(v_g_1348_, v_body_1384_, v_a_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
v___y_1364_ = v___x_1387_;
goto v___jp_1363_;
}
else
{
lean_dec_ref(v_g_1348_);
v___y_1364_ = v___x_1386_;
goto v___jp_1363_;
}
}
else
{
lean_dec_ref(v_g_1348_);
v___y_1364_ = v___x_1385_;
goto v___jp_1363_;
}
}
case 5:
{
lean_object* v_fn_1388_; lean_object* v_arg_1389_; lean_object* v___x_1390_; 
v_fn_1388_ = lean_ctor_get(v_e_1349_, 0);
v_arg_1389_ = lean_ctor_get(v_e_1349_, 1);
lean_inc_ref(v_fn_1388_);
lean_inc_ref(v_g_1348_);
v___x_1390_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0(v_g_1348_, v_fn_1388_, v_a_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v___x_1391_; 
lean_dec_ref(v___x_1390_);
lean_inc_ref(v_arg_1389_);
v___x_1391_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0(v_g_1348_, v_arg_1389_, v_a_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
v___y_1364_ = v___x_1391_;
goto v___jp_1363_;
}
else
{
lean_dec_ref(v_g_1348_);
v___y_1364_ = v___x_1390_;
goto v___jp_1363_;
}
}
case 10:
{
lean_object* v_expr_1392_; lean_object* v___x_1393_; 
v_expr_1392_ = lean_ctor_get(v_e_1349_, 1);
lean_inc_ref(v_expr_1392_);
v___x_1393_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0(v_g_1348_, v_expr_1392_, v_a_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
v___y_1364_ = v___x_1393_;
goto v___jp_1363_;
}
case 11:
{
lean_object* v_struct_1394_; lean_object* v___x_1395_; 
v_struct_1394_ = lean_ctor_get(v_e_1349_, 2);
lean_inc_ref(v_struct_1394_);
v___x_1395_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0(v_g_1348_, v_struct_1394_, v_a_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
v___y_1364_ = v___x_1395_;
goto v___jp_1363_;
}
default: 
{
lean_object* v___x_1396_; 
lean_dec_ref(v_g_1348_);
v___x_1396_ = lean_box(0);
v_a_1358_ = v___x_1396_;
goto v___jp_1357_;
}
}
}
v___jp_1370_:
{
lean_object* v___x_1374_; 
lean_inc_ref(v_g_1348_);
v___x_1374_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0(v_g_1348_, v_d_1371_, v___y_1373_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v___x_1375_; 
lean_dec_ref(v___x_1374_);
v___x_1375_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0(v_g_1348_, v_b_1372_, v___y_1373_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
v___y_1364_ = v___x_1375_;
goto v___jp_1363_;
}
else
{
lean_dec_ref(v_b_1372_);
lean_dec_ref(v_g_1348_);
v___y_1364_ = v___x_1374_;
goto v___jp_1363_;
}
}
}
else
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1404_; 
lean_dec_ref(v_e_1349_);
lean_dec_ref(v_g_1348_);
v_a_1397_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1399_ = v___x_1368_;
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1368_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1397_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
else
{
lean_object* v_val_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
lean_dec_ref(v_e_1349_);
lean_dec_ref(v_g_1348_);
v_val_1405_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1367_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_val_1405_);
lean_dec(v___x_1367_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
lean_ctor_set_tag(v___x_1407_, 0);
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_val_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
v___jp_1357_:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1359_ = lean_st_ref_take(v_a_1350_);
v___x_1360_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1___redArg(v___x_1359_, v_e_1349_, v_a_1358_);
v___x_1361_ = lean_st_ref_set(v_a_1350_, v___x_1360_);
v___x_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1362_, 0, v_a_1358_);
return v___x_1362_;
}
v___jp_1363_:
{
if (lean_obj_tag(v___y_1364_) == 0)
{
lean_object* v_a_1365_; 
v_a_1365_ = lean_ctor_get(v___y_1364_, 0);
lean_inc(v_a_1365_);
lean_dec_ref(v___y_1364_);
v_a_1358_ = v_a_1365_;
goto v___jp_1357_;
}
else
{
lean_dec_ref(v_e_1349_);
return v___y_1364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0___boxed(lean_object* v_g_1413_, lean_object* v_e_1414_, lean_object* v_a_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0(v_g_1413_, v_e_1414_, v_a_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec(v___y_1416_);
lean_dec(v_a_1415_);
return v_res_1422_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___closed__0(void){
_start:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1423_ = lean_box(0);
v___x_1424_ = lean_unsigned_to_nat(16u);
v___x_1425_ = lean_mk_array(v___x_1424_, v___x_1423_);
return v___x_1425_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___closed__1(void){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1426_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___closed__0, &l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___closed__0_once, _init_l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___closed__0);
v___x_1427_ = lean_unsigned_to_nat(0u);
v___x_1428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1427_);
lean_ctor_set(v___x_1428_, 1, v___x_1426_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar(lean_object* v_e_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_){
_start:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___f_1439_; lean_object* v___x_1440_; 
v___x_1437_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___closed__1, &l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___closed__1_once, _init_l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___closed__1);
v___x_1438_ = lean_st_mk_ref(v___x_1437_);
v___f_1439_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___closed__2));
v___x_1440_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0(v___f_1439_, v_e_1430_, v___x_1438_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1449_; 
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1443_ = v___x_1440_;
v_isShared_1444_ = v_isSharedCheck_1449_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1440_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1449_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1445_; lean_object* v___x_1447_; 
v___x_1445_ = lean_st_ref_get(v___x_1438_);
lean_dec(v___x_1438_);
lean_dec(v___x_1445_);
if (v_isShared_1444_ == 0)
{
v___x_1447_ = v___x_1443_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1441_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
else
{
lean_dec(v___x_1438_);
return v___x_1440_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___boxed(lean_object* v_e_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar(v_e_1450_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_);
lean_dec(v_a_1455_);
lean_dec_ref(v_a_1454_);
lean_dec(v_a_1453_);
lean_dec_ref(v_a_1452_);
lean_dec(v_a_1451_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0(lean_object* v_00_u03b2_1458_, lean_object* v_m_1459_, lean_object* v_a_1460_){
_start:
{
lean_object* v___x_1461_; 
v___x_1461_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0___redArg(v_m_1459_, v_a_1460_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1462_, lean_object* v_m_1463_, lean_object* v_a_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0(v_00_u03b2_1462_, v_m_1463_, v_a_1464_);
lean_dec_ref(v_a_1464_);
lean_dec_ref(v_m_1463_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1(lean_object* v_00_u03b2_1466_, lean_object* v_m_1467_, lean_object* v_a_1468_, lean_object* v_b_1469_){
_start:
{
lean_object* v___x_1470_; 
v___x_1470_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1___redArg(v_m_1467_, v_a_1468_, v_b_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1471_, lean_object* v_a_1472_, lean_object* v_x_1473_){
_start:
{
lean_object* v___x_1474_; 
v___x_1474_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0_spec__1___redArg(v_a_1472_, v_x_1473_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1475_, lean_object* v_a_1476_, lean_object* v_x_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0_spec__1(v_00_u03b2_1475_, v_a_1476_, v_x_1477_);
lean_dec(v_x_1477_);
lean_dec_ref(v_a_1476_);
return v_res_1478_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1479_, lean_object* v_a_1480_, lean_object* v_x_1481_){
_start:
{
uint8_t v___x_1482_; 
v___x_1482_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__3___redArg(v_a_1480_, v_x_1481_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1483_, lean_object* v_a_1484_, lean_object* v_x_1485_){
_start:
{
uint8_t v_res_1486_; lean_object* v_r_1487_; 
v_res_1486_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__3(v_00_u03b2_1483_, v_a_1484_, v_x_1485_);
lean_dec(v_x_1485_);
lean_dec_ref(v_a_1484_);
v_r_1487_ = lean_box(v_res_1486_);
return v_r_1487_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_1488_, lean_object* v_data_1489_){
_start:
{
lean_object* v___x_1490_; 
v___x_1490_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__4___redArg(v_data_1489_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_1491_, lean_object* v_a_1492_, lean_object* v_b_1493_, lean_object* v_x_1494_){
_start:
{
lean_object* v___x_1495_; 
v___x_1495_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__5___redArg(v_a_1492_, v_b_1493_, v_x_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__4_spec__5(lean_object* v_00_u03b2_1496_, lean_object* v_i_1497_, lean_object* v_source_1498_, lean_object* v_target_1499_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__4_spec__5___redArg(v_i_1497_, v_source_1498_, v_target_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_1501_, lean_object* v_x_1502_, lean_object* v_x_1503_){
_start:
{
lean_object* v___x_1504_; 
v___x_1504_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_x_1502_, v_x_1503_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replace___lam__0(lean_object* v_hyp_1505_, lean_object* v_g_1506_, lean_object* v_proof_1507_, lean_object* v_typeNew_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v___x_1514_; 
lean_inc(v_hyp_1505_);
v___x_1514_ = l_Lean_FVarId_getDecl___redArg(v_hyp_1505_, v___y_1509_, v___y_1511_, v___y_1512_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc_n(v_a_1515_, 2);
lean_dec_ref(v___x_1514_);
v___x_1516_ = lean_st_mk_ref(v_a_1515_);
lean_inc_ref(v_typeNew_1508_);
v___x_1517_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar(v_typeNew_1508_, v___x_1516_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
lean_dec_ref(v___x_1517_);
v___x_1518_ = lean_st_ref_get(v___x_1516_);
lean_dec(v___x_1516_);
v___x_1519_ = l_Lean_LocalDecl_fvarId(v___x_1518_);
lean_dec(v___x_1518_);
v___x_1520_ = l_Lean_LocalDecl_userName(v_a_1515_);
lean_dec(v_a_1515_);
v___x_1521_ = l_Lean_MVarId_assertAfter(v_g_1506_, v___x_1519_, v___x_1520_, v_typeNew_1508_, v_proof_1507_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; lean_object* v___x_1523_; 
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_a_1522_);
lean_dec_ref(v___x_1521_);
v___x_1523_ = l_Lean_Meta_saveState___redArg(v___y_1510_, v___y_1512_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_a_1524_; lean_object* v_fvarId_1525_; lean_object* v_mvarId_1526_; lean_object* v_subst_1527_; lean_object* v___x_1528_; 
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_a_1524_);
lean_dec_ref(v___x_1523_);
v_fvarId_1525_ = lean_ctor_get(v_a_1522_, 0);
v_mvarId_1526_ = lean_ctor_get(v_a_1522_, 1);
v_subst_1527_ = lean_ctor_get(v_a_1522_, 2);
lean_inc(v_mvarId_1526_);
v___x_1528_ = l_Lean_MVarId_clear(v_mvarId_1526_, v_hyp_1505_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1543_; 
lean_inc(v_subst_1527_);
lean_inc(v_fvarId_1525_);
lean_dec(v_a_1524_);
v_isSharedCheck_1543_ = !lean_is_exclusive(v_a_1522_);
if (v_isSharedCheck_1543_ == 0)
{
lean_object* v_unused_1544_; lean_object* v_unused_1545_; lean_object* v_unused_1546_; 
v_unused_1544_ = lean_ctor_get(v_a_1522_, 2);
lean_dec(v_unused_1544_);
v_unused_1545_ = lean_ctor_get(v_a_1522_, 1);
lean_dec(v_unused_1545_);
v_unused_1546_ = lean_ctor_get(v_a_1522_, 0);
lean_dec(v_unused_1546_);
v___x_1530_ = v_a_1522_;
v_isShared_1531_ = v_isSharedCheck_1543_;
goto v_resetjp_1529_;
}
else
{
lean_dec(v_a_1522_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1543_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1542_; 
v_a_1532_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1534_ = v___x_1528_;
v_isShared_1535_ = v_isSharedCheck_1542_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v___x_1528_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1542_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1537_; 
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 1, v_a_1532_);
v___x_1537_ = v___x_1530_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_fvarId_1525_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v_a_1532_);
lean_ctor_set(v_reuseFailAlloc_1541_, 2, v_subst_1527_);
v___x_1537_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
lean_object* v___x_1539_; 
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 0, v___x_1537_);
v___x_1539_ = v___x_1534_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1537_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
}
}
else
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1575_; 
v_a_1547_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1549_ = v___x_1528_;
v_isShared_1550_ = v_isSharedCheck_1575_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1528_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1575_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1552_; 
lean_inc(v_a_1547_);
if (v_isShared_1550_ == 0)
{
v___x_1552_ = v___x_1549_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1547_);
v___x_1552_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
uint8_t v___y_1554_; uint8_t v___x_1572_; 
v___x_1572_ = l_Lean_Exception_isInterrupt(v_a_1547_);
if (v___x_1572_ == 0)
{
uint8_t v___x_1573_; 
v___x_1573_ = l_Lean_Exception_isRuntime(v_a_1547_);
v___y_1554_ = v___x_1573_;
goto v___jp_1553_;
}
else
{
lean_dec(v_a_1547_);
v___y_1554_ = v___x_1572_;
goto v___jp_1553_;
}
v___jp_1553_:
{
if (v___y_1554_ == 0)
{
lean_object* v___x_1555_; 
lean_dec_ref(v___x_1552_);
v___x_1555_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1524_, v___y_1510_, v___y_1512_);
lean_dec(v_a_1524_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1562_; 
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1562_ == 0)
{
lean_object* v_unused_1563_; 
v_unused_1563_ = lean_ctor_get(v___x_1555_, 0);
lean_dec(v_unused_1563_);
v___x_1557_ = v___x_1555_;
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
else
{
lean_dec(v___x_1555_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1560_; 
if (v_isShared_1558_ == 0)
{
lean_ctor_set(v___x_1557_, 0, v_a_1522_);
v___x_1560_ = v___x_1557_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1522_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
else
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
lean_dec(v_a_1522_);
v_a_1564_ = lean_ctor_get(v___x_1555_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1555_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1555_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1564_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
else
{
lean_dec(v_a_1524_);
lean_dec(v_a_1522_);
return v___x_1552_;
}
}
}
}
}
}
else
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
lean_dec(v_a_1522_);
lean_dec(v_hyp_1505_);
v_a_1576_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1578_ = v___x_1523_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1523_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1576_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
else
{
lean_dec(v_hyp_1505_);
return v___x_1521_;
}
}
else
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1591_; 
lean_dec(v___x_1516_);
lean_dec(v_a_1515_);
lean_dec_ref(v_typeNew_1508_);
lean_dec_ref(v_proof_1507_);
lean_dec(v_g_1506_);
lean_dec(v_hyp_1505_);
v_a_1584_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1586_ = v___x_1517_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1517_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1584_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
else
{
lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1599_; 
lean_dec_ref(v_typeNew_1508_);
lean_dec_ref(v_proof_1507_);
lean_dec(v_g_1506_);
lean_dec(v_hyp_1505_);
v_a_1592_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1594_ = v___x_1514_;
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1514_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1597_; 
if (v_isShared_1595_ == 0)
{
v___x_1597_ = v___x_1594_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1592_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replace___lam__0___boxed(lean_object* v_hyp_1600_, lean_object* v_g_1601_, lean_object* v_proof_1602_, lean_object* v_typeNew_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_Lean_MVarId_replace___lam__0(v_hyp_1600_, v_g_1601_, v_proof_1602_, v_typeNew_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replace___lam__1(lean_object* v_typeNew_1610_, lean_object* v_proof_1611_, lean_object* v___f_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
if (lean_obj_tag(v_typeNew_1610_) == 0)
{
lean_object* v___x_1618_; 
lean_inc(v___y_1616_);
lean_inc_ref(v___y_1615_);
lean_inc(v___y_1614_);
lean_inc_ref(v___y_1613_);
v___x_1618_ = lean_infer_type(v_proof_1611_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1619_; lean_object* v___x_1620_; 
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_a_1619_);
lean_dec_ref(v___x_1618_);
lean_inc(v___y_1616_);
lean_inc_ref(v___y_1615_);
lean_inc(v___y_1614_);
lean_inc_ref(v___y_1613_);
v___x_1620_ = lean_apply_6(v___f_1612_, v_a_1619_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, lean_box(0));
return v___x_1620_;
}
else
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
lean_dec_ref(v___f_1612_);
v_a_1621_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1623_ = v___x_1618_;
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1618_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1626_; 
if (v_isShared_1624_ == 0)
{
v___x_1626_ = v___x_1623_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
else
{
lean_object* v_val_1629_; lean_object* v___x_1630_; 
lean_dec_ref(v_proof_1611_);
v_val_1629_ = lean_ctor_get(v_typeNew_1610_, 0);
lean_inc(v_val_1629_);
lean_dec_ref(v_typeNew_1610_);
lean_inc(v___y_1616_);
lean_inc_ref(v___y_1615_);
lean_inc(v___y_1614_);
lean_inc_ref(v___y_1613_);
v___x_1630_ = lean_apply_6(v___f_1612_, v_val_1629_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, lean_box(0));
return v___x_1630_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replace___lam__1___boxed(lean_object* v_typeNew_1631_, lean_object* v_proof_1632_, lean_object* v___f_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l_Lean_MVarId_replace___lam__1(v_typeNew_1631_, v_proof_1632_, v___f_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replace(lean_object* v_g_1640_, lean_object* v_hyp_1641_, lean_object* v_proof_1642_, lean_object* v_typeNew_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_){
_start:
{
lean_object* v___f_1649_; lean_object* v___y_1650_; lean_object* v___x_1651_; 
lean_inc_ref(v_proof_1642_);
lean_inc(v_g_1640_);
v___f_1649_ = lean_alloc_closure((void*)(l_Lean_MVarId_replace___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1649_, 0, v_hyp_1641_);
lean_closure_set(v___f_1649_, 1, v_g_1640_);
lean_closure_set(v___f_1649_, 2, v_proof_1642_);
v___y_1650_ = lean_alloc_closure((void*)(l_Lean_MVarId_replace___lam__1___boxed), 8, 3);
lean_closure_set(v___y_1650_, 0, v_typeNew_1643_);
lean_closure_set(v___y_1650_, 1, v_proof_1642_);
lean_closure_set(v___y_1650_, 2, v___f_1649_);
v___x_1651_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(v_g_1640_, v___y_1650_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replace___boxed(lean_object* v_g_1652_, lean_object* v_hyp_1653_, lean_object* v_proof_1654_, lean_object* v_typeNew_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l_Lean_MVarId_replace(v_g_1652_, v_hyp_1653_, v_proof_1654_, v_typeNew_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_);
lean_dec(v_a_1659_);
lean_dec_ref(v_a_1658_);
lean_dec(v_a_1657_);
lean_dec_ref(v_a_1656_);
return v_res_1661_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_FVarSubst(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Intro(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Revert(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_ForEachExpr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Assert(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_FVarSubst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Revert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_ForEachExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Assert(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_FVarSubst(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Intro(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Revert(uint8_t builtin);
lean_object* initialize_Lean_Util_ForEachExpr(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Assert(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_FVarSubst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Revert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ForEachExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Assert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Assert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Assert(builtin);
}
#ifdef __cplusplus
}
#endif
