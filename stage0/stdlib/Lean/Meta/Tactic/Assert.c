// Lean compiler output
// Module: Lean.Meta.Tactic.Assert
// Imports: public import Lean.Meta.Tactic.FVarSubst public import Lean.Meta.Tactic.Intro public import Lean.Meta.Tactic.Revert public import Lean.Elab.InfoTree.Main public import Lean.Util.ForEachExpr import Lean.Meta.AppBuilder
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
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_get_x21(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_setKind(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instDecidableEqLocalDeclKind(uint8_t, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_modifyExprMVarLCtx(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_MVarId_revertAfter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__0;
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_assertAfter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "assertAfter"};
static const lean_object* l_Lean_MVarId_assertAfter___closed__0 = (const lean_object*)&l_Lean_MVarId_assertAfter___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_assertAfter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_assertAfter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(39, 174, 1, 90, 222, 201, 211, 92)}};
static const lean_object* l_Lean_MVarId_assertAfter___closed__1 = (const lean_object*)&l_Lean_MVarId_assertAfter___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_assertAfter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assertAfter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__1;
static const lean_closure_object l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assertAfter_x27___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assertAfter_x27___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assertAfter_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assertAfter_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v___x_261_, 1);
lean_inc(v_mvarId_251_);
v___x_262_ = l_Lean_MVarId_getTag(v_mvarId_251_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v_a_263_; lean_object* v___x_264_; 
v_a_263_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_a_263_);
lean_dec_ref_known(v___x_262_, 1);
lean_inc(v_mvarId_251_);
v___x_264_ = l_Lean_MVarId_getType(v_mvarId_251_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v_a_265_; uint8_t v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v_a_265_ = lean_ctor_get(v___x_264_, 0);
lean_inc(v_a_265_);
lean_dec_ref_known(v___x_264_, 1);
v___x_266_ = 0;
v___x_267_ = l_Lean_mkForall(v_name_253_, v___x_266_, v_type_254_, v_a_265_);
v___x_268_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_267_, v_a_263_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_a_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_279_; 
v_a_269_ = lean_ctor_get(v___x_268_, 0);
lean_inc_n(v_a_269_, 2);
lean_dec_ref_known(v___x_268_, 1);
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
lean_object* v_____do__lift_424_; lean_object* v___y_425_; lean_object* v___y_426_; lean_object* v___y_427_; lean_object* v___y_428_; 
if (lean_obj_tag(v_t_x3f_417_) == 0)
{
lean_object* v___x_441_; 
lean_inc(v_a_421_);
lean_inc_ref(v_a_420_);
lean_inc(v_a_419_);
lean_inc_ref(v_a_418_);
lean_inc_ref(v_v_416_);
v___x_441_ = lean_infer_type(v_v_416_, v_a_418_, v_a_419_, v_a_420_, v_a_421_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v_a_442_; 
v_a_442_ = lean_ctor_get(v___x_441_, 0);
lean_inc(v_a_442_);
lean_dec_ref_known(v___x_441_, 1);
v_____do__lift_424_ = v_a_442_;
v___y_425_ = v_a_418_;
v___y_426_ = v_a_419_;
v___y_427_ = v_a_420_;
v___y_428_ = v_a_421_;
goto v___jp_423_;
}
else
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_450_; 
lean_dec_ref(v_v_416_);
lean_dec(v_h_415_);
lean_dec(v_g_414_);
v_a_443_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_450_ == 0)
{
v___x_445_ = v___x_441_;
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_441_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_448_; 
if (v_isShared_446_ == 0)
{
v___x_448_ = v___x_445_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_a_443_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
else
{
lean_object* v_val_451_; 
v_val_451_ = lean_ctor_get(v_t_x3f_417_, 0);
lean_inc(v_val_451_);
lean_dec_ref_known(v_t_x3f_417_, 1);
v_____do__lift_424_ = v_val_451_;
v___y_425_ = v_a_418_;
v___y_426_ = v_a_419_;
v___y_427_ = v_a_420_;
v___y_428_ = v_a_421_;
goto v___jp_423_;
}
v___jp_423_:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_MVarId_assert(v_g_414_, v_h_415_, v_____do__lift_424_, v_v_416_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; uint8_t v___x_431_; lean_object* v___x_432_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_a_430_);
lean_dec_ref_known(v___x_429_, 1);
v___x_431_ = 1;
v___x_432_ = l_Lean_Meta_intro1Core(v_a_430_, v___x_431_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
return v___x_432_;
}
else
{
lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_440_; 
v_a_433_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_440_ == 0)
{
v___x_435_ = v___x_429_;
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v___x_429_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_438_; 
if (v_isShared_436_ == 0)
{
v___x_438_ = v___x_435_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_a_433_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_note___boxed(lean_object* v_g_452_, lean_object* v_h_453_, lean_object* v_v_454_, lean_object* v_t_x3f_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lean_MVarId_note(v_g_452_, v_h_453_, v_v_454_, v_t_x3f_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
lean_dec(v_a_459_);
lean_dec_ref(v_a_458_);
lean_dec(v_a_457_);
lean_dec_ref(v_a_456_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_define___lam__0(lean_object* v_mvarId_462_, lean_object* v___x_463_, lean_object* v_name_464_, lean_object* v_type_465_, lean_object* v_val_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v___x_472_; 
lean_inc(v_mvarId_462_);
v___x_472_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_462_, v___x_463_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v___x_473_; 
lean_dec_ref_known(v___x_472_, 1);
lean_inc(v_mvarId_462_);
v___x_473_ = l_Lean_MVarId_getTag(v_mvarId_462_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; lean_object* v___x_475_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
lean_inc(v_a_474_);
lean_dec_ref_known(v___x_473_, 1);
lean_inc(v_mvarId_462_);
v___x_475_ = l_Lean_MVarId_getType(v_mvarId_462_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v_a_476_; uint8_t v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v_a_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_a_476_);
lean_dec_ref_known(v___x_475_, 1);
v___x_477_ = 0;
v___x_478_ = l_Lean_Expr_letE___override(v_name_464_, v_type_465_, v_val_466_, v_a_476_, v___x_477_);
v___x_479_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_478_, v_a_474_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_480_; lean_object* v___x_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_489_; 
v_a_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc_n(v_a_480_, 2);
lean_dec_ref_known(v___x_479_, 1);
v___x_481_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(v_mvarId_462_, v_a_480_, v___y_468_);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_489_ == 0)
{
lean_object* v_unused_490_; 
v_unused_490_ = lean_ctor_get(v___x_481_, 0);
lean_dec(v_unused_490_);
v___x_483_ = v___x_481_;
v_isShared_484_ = v_isSharedCheck_489_;
goto v_resetjp_482_;
}
else
{
lean_dec(v___x_481_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_489_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; lean_object* v___x_487_; 
v___x_485_ = l_Lean_Expr_mvarId_x21(v_a_480_);
lean_dec(v_a_480_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 0, v___x_485_);
v___x_487_ = v___x_483_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v___x_485_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
else
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
lean_dec(v_mvarId_462_);
v_a_491_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_479_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_479_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
else
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_506_; 
lean_dec(v_a_474_);
lean_dec_ref(v_val_466_);
lean_dec_ref(v_type_465_);
lean_dec(v_name_464_);
lean_dec(v_mvarId_462_);
v_a_499_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_506_ == 0)
{
v___x_501_ = v___x_475_;
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_475_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_502_ == 0)
{
v___x_504_ = v___x_501_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_a_499_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
else
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_514_; 
lean_dec_ref(v_val_466_);
lean_dec_ref(v_type_465_);
lean_dec(v_name_464_);
lean_dec(v_mvarId_462_);
v_a_507_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_514_ == 0)
{
v___x_509_ = v___x_473_;
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___x_473_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_512_; 
if (v_isShared_510_ == 0)
{
v___x_512_ = v___x_509_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_a_507_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
}
else
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_522_; 
lean_dec_ref(v_val_466_);
lean_dec_ref(v_type_465_);
lean_dec(v_name_464_);
lean_dec(v_mvarId_462_);
v_a_515_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_522_ == 0)
{
v___x_517_ = v___x_472_;
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_472_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_520_; 
if (v_isShared_518_ == 0)
{
v___x_520_ = v___x_517_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_a_515_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_define___lam__0___boxed(lean_object* v_mvarId_523_, lean_object* v___x_524_, lean_object* v_name_525_, lean_object* v_type_526_, lean_object* v_val_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Lean_MVarId_define___lam__0(v_mvarId_523_, v___x_524_, v_name_525_, v_type_526_, v_val_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_define(lean_object* v_mvarId_537_, lean_object* v_name_538_, lean_object* v_type_539_, lean_object* v_val_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_){
_start:
{
lean_object* v___x_546_; lean_object* v___f_547_; lean_object* v___x_548_; 
v___x_546_ = ((lean_object*)(l_Lean_MVarId_define___closed__1));
lean_inc(v_mvarId_537_);
v___f_547_ = lean_alloc_closure((void*)(l_Lean_MVarId_define___lam__0___boxed), 10, 5);
lean_closure_set(v___f_547_, 0, v_mvarId_537_);
lean_closure_set(v___f_547_, 1, v___x_546_);
lean_closure_set(v___f_547_, 2, v_name_538_);
lean_closure_set(v___f_547_, 3, v_type_539_);
lean_closure_set(v___f_547_, 4, v_val_540_);
v___x_548_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(v_mvarId_537_, v___f_547_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_define___boxed(lean_object* v_mvarId_549_, lean_object* v_name_550_, lean_object* v_type_551_, lean_object* v_val_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lean_MVarId_define(v_mvarId_549_, v_name_550_, v_type_551_, v_val_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_);
lean_dec(v_a_556_);
lean_dec_ref(v_a_555_);
lean_dec(v_a_554_);
lean_dec_ref(v_a_553_);
return v_res_558_;
}
}
static lean_object* _init_l_Lean_MVarId_assertExt___lam__0___closed__2(void){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = lean_unsigned_to_nat(0u);
v___x_563_ = l_Lean_mkBVar(v___x_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertExt___lam__0(lean_object* v_mvarId_564_, lean_object* v___x_565_, lean_object* v_type_566_, lean_object* v_val_567_, lean_object* v_hName_568_, lean_object* v_name_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
lean_object* v___x_575_; 
lean_inc(v_mvarId_564_);
v___x_575_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_564_, v___x_565_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v___x_576_; 
lean_dec_ref_known(v___x_575_, 1);
lean_inc(v_mvarId_564_);
v___x_576_ = l_Lean_MVarId_getTag(v_mvarId_564_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v_a_577_; lean_object* v___x_578_; 
v_a_577_ = lean_ctor_get(v___x_576_, 0);
lean_inc(v_a_577_);
lean_dec_ref_known(v___x_576_, 1);
lean_inc(v_mvarId_564_);
v___x_578_ = l_Lean_MVarId_getType(v_mvarId_564_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; lean_object* v___x_580_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_a_579_);
lean_dec_ref_known(v___x_578_, 1);
lean_inc_ref(v_type_566_);
v___x_580_ = l_Lean_Meta_getLevel(v_type_566_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; uint8_t v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v_a_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_a_581_);
lean_dec_ref_known(v___x_580_, 1);
v___x_582_ = ((lean_object*)(l_Lean_MVarId_assertExt___lam__0___closed__1));
v___x_583_ = lean_box(0);
v___x_584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_584_, 0, v_a_581_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
v___x_585_ = l_Lean_mkConst(v___x_582_, v___x_584_);
v___x_586_ = lean_obj_once(&l_Lean_MVarId_assertExt___lam__0___closed__2, &l_Lean_MVarId_assertExt___lam__0___closed__2_once, _init_l_Lean_MVarId_assertExt___lam__0___closed__2);
lean_inc_ref(v_val_567_);
lean_inc_ref(v_type_566_);
v___x_587_ = l_Lean_mkApp3(v___x_585_, v_type_566_, v___x_586_, v_val_567_);
v___x_588_ = 0;
v___x_589_ = l_Lean_mkForall(v_hName_568_, v___x_588_, v___x_587_, v_a_579_);
v___x_590_ = l_Lean_mkForall(v_name_569_, v___x_588_, v_type_566_, v___x_589_);
v___x_591_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_590_, v_a_577_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; lean_object* v___x_593_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
lean_inc(v_a_592_);
lean_dec_ref_known(v___x_591_, 1);
lean_inc_ref(v_val_567_);
v___x_593_ = l_Lean_Meta_mkEqRefl(v_val_567_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v_a_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_604_; 
v_a_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_a_594_);
lean_dec_ref_known(v___x_593_, 1);
lean_inc(v_a_592_);
v___x_595_ = l_Lean_mkAppB(v_a_592_, v_val_567_, v_a_594_);
v___x_596_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(v_mvarId_564_, v___x_595_, v___y_571_);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_604_ == 0)
{
lean_object* v_unused_605_; 
v_unused_605_ = lean_ctor_get(v___x_596_, 0);
lean_dec(v_unused_605_);
v___x_598_ = v___x_596_;
v_isShared_599_ = v_isSharedCheck_604_;
goto v_resetjp_597_;
}
else
{
lean_dec(v___x_596_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_604_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_600_; lean_object* v___x_602_; 
v___x_600_ = l_Lean_Expr_mvarId_x21(v_a_592_);
lean_dec(v_a_592_);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 0, v___x_600_);
v___x_602_ = v___x_598_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_600_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
lean_dec(v_a_592_);
lean_dec_ref(v_val_567_);
lean_dec(v_mvarId_564_);
v_a_606_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_593_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_593_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
else
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_621_; 
lean_dec_ref(v_val_567_);
lean_dec(v_mvarId_564_);
v_a_614_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_621_ == 0)
{
v___x_616_ = v___x_591_;
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_591_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
if (v_isShared_617_ == 0)
{
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_a_614_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
else
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
lean_dec(v_a_579_);
lean_dec(v_a_577_);
lean_dec(v_name_569_);
lean_dec(v_hName_568_);
lean_dec_ref(v_val_567_);
lean_dec_ref(v_type_566_);
lean_dec(v_mvarId_564_);
v_a_622_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v___x_580_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_580_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_627_; 
if (v_isShared_625_ == 0)
{
v___x_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_622_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
else
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
lean_dec(v_a_577_);
lean_dec(v_name_569_);
lean_dec(v_hName_568_);
lean_dec_ref(v_val_567_);
lean_dec_ref(v_type_566_);
lean_dec(v_mvarId_564_);
v_a_630_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___x_578_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_578_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_633_ == 0)
{
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_a_630_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
else
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_645_; 
lean_dec(v_name_569_);
lean_dec(v_hName_568_);
lean_dec_ref(v_val_567_);
lean_dec_ref(v_type_566_);
lean_dec(v_mvarId_564_);
v_a_638_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_645_ == 0)
{
v___x_640_ = v___x_576_;
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_576_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_643_; 
if (v_isShared_641_ == 0)
{
v___x_643_ = v___x_640_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_a_638_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
else
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_653_; 
lean_dec(v_name_569_);
lean_dec(v_hName_568_);
lean_dec_ref(v_val_567_);
lean_dec_ref(v_type_566_);
lean_dec(v_mvarId_564_);
v_a_646_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_653_ == 0)
{
v___x_648_ = v___x_575_;
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_575_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_a_646_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertExt___lam__0___boxed(lean_object* v_mvarId_654_, lean_object* v___x_655_, lean_object* v_type_656_, lean_object* v_val_657_, lean_object* v_hName_658_, lean_object* v_name_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Lean_MVarId_assertExt___lam__0(v_mvarId_654_, v___x_655_, v_type_656_, v_val_657_, v_hName_658_, v_name_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertExt(lean_object* v_mvarId_666_, lean_object* v_name_667_, lean_object* v_type_668_, lean_object* v_val_669_, lean_object* v_hName_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
lean_object* v___x_676_; lean_object* v___f_677_; lean_object* v___x_678_; 
v___x_676_ = ((lean_object*)(l_Lean_MVarId_assert___closed__1));
lean_inc(v_mvarId_666_);
v___f_677_ = lean_alloc_closure((void*)(l_Lean_MVarId_assertExt___lam__0___boxed), 11, 6);
lean_closure_set(v___f_677_, 0, v_mvarId_666_);
lean_closure_set(v___f_677_, 1, v___x_676_);
lean_closure_set(v___f_677_, 2, v_type_668_);
lean_closure_set(v___f_677_, 3, v_val_669_);
lean_closure_set(v___f_677_, 4, v_hName_670_);
lean_closure_set(v___f_677_, 5, v_name_667_);
v___x_678_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(v_mvarId_666_, v___f_677_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertExt___boxed(lean_object* v_mvarId_679_, lean_object* v_name_680_, lean_object* v_type_681_, lean_object* v_val_682_, lean_object* v_hName_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_MVarId_assertExt(v_mvarId_679_, v_name_680_, v_type_681_, v_val_682_, v_hName_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_);
lean_dec(v_a_687_);
lean_dec_ref(v_a_686_);
lean_dec(v_a_685_);
lean_dec_ref(v_a_684_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___redArg(lean_object* v_t_690_, lean_object* v___y_691_){
_start:
{
lean_object* v___x_693_; lean_object* v_infoState_694_; uint8_t v_enabled_695_; 
v___x_693_ = lean_st_ref_get(v___y_691_);
v_infoState_694_ = lean_ctor_get(v___x_693_, 7);
lean_inc_ref(v_infoState_694_);
lean_dec(v___x_693_);
v_enabled_695_ = lean_ctor_get_uint8(v_infoState_694_, sizeof(void*)*3);
lean_dec_ref(v_infoState_694_);
if (v_enabled_695_ == 0)
{
lean_object* v___x_696_; lean_object* v___x_697_; 
lean_dec_ref(v_t_690_);
v___x_696_ = lean_box(0);
v___x_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
return v___x_697_;
}
else
{
lean_object* v___x_698_; lean_object* v_infoState_699_; lean_object* v_env_700_; lean_object* v_nextMacroScope_701_; lean_object* v_ngen_702_; lean_object* v_auxDeclNGen_703_; lean_object* v_traceState_704_; lean_object* v_cache_705_; lean_object* v_messages_706_; lean_object* v_snapshotTasks_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_729_; 
v___x_698_ = lean_st_ref_take(v___y_691_);
v_infoState_699_ = lean_ctor_get(v___x_698_, 7);
v_env_700_ = lean_ctor_get(v___x_698_, 0);
v_nextMacroScope_701_ = lean_ctor_get(v___x_698_, 1);
v_ngen_702_ = lean_ctor_get(v___x_698_, 2);
v_auxDeclNGen_703_ = lean_ctor_get(v___x_698_, 3);
v_traceState_704_ = lean_ctor_get(v___x_698_, 4);
v_cache_705_ = lean_ctor_get(v___x_698_, 5);
v_messages_706_ = lean_ctor_get(v___x_698_, 6);
v_snapshotTasks_707_ = lean_ctor_get(v___x_698_, 8);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_729_ == 0)
{
v___x_709_ = v___x_698_;
v_isShared_710_ = v_isSharedCheck_729_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_snapshotTasks_707_);
lean_inc(v_infoState_699_);
lean_inc(v_messages_706_);
lean_inc(v_cache_705_);
lean_inc(v_traceState_704_);
lean_inc(v_auxDeclNGen_703_);
lean_inc(v_ngen_702_);
lean_inc(v_nextMacroScope_701_);
lean_inc(v_env_700_);
lean_dec(v___x_698_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_729_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
uint8_t v_enabled_711_; lean_object* v_assignment_712_; lean_object* v_lazyAssignment_713_; lean_object* v_trees_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_728_; 
v_enabled_711_ = lean_ctor_get_uint8(v_infoState_699_, sizeof(void*)*3);
v_assignment_712_ = lean_ctor_get(v_infoState_699_, 0);
v_lazyAssignment_713_ = lean_ctor_get(v_infoState_699_, 1);
v_trees_714_ = lean_ctor_get(v_infoState_699_, 2);
v_isSharedCheck_728_ = !lean_is_exclusive(v_infoState_699_);
if (v_isSharedCheck_728_ == 0)
{
v___x_716_ = v_infoState_699_;
v_isShared_717_ = v_isSharedCheck_728_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_trees_714_);
lean_inc(v_lazyAssignment_713_);
lean_inc(v_assignment_712_);
lean_dec(v_infoState_699_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_728_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_718_; lean_object* v___x_720_; 
v___x_718_ = l_Lean_PersistentArray_push___redArg(v_trees_714_, v_t_690_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 2, v___x_718_);
v___x_720_ = v___x_716_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_assignment_712_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v_lazyAssignment_713_);
lean_ctor_set(v_reuseFailAlloc_727_, 2, v___x_718_);
lean_ctor_set_uint8(v_reuseFailAlloc_727_, sizeof(void*)*3, v_enabled_711_);
v___x_720_ = v_reuseFailAlloc_727_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
lean_object* v___x_722_; 
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 7, v___x_720_);
v___x_722_ = v___x_709_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_env_700_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v_nextMacroScope_701_);
lean_ctor_set(v_reuseFailAlloc_726_, 2, v_ngen_702_);
lean_ctor_set(v_reuseFailAlloc_726_, 3, v_auxDeclNGen_703_);
lean_ctor_set(v_reuseFailAlloc_726_, 4, v_traceState_704_);
lean_ctor_set(v_reuseFailAlloc_726_, 5, v_cache_705_);
lean_ctor_set(v_reuseFailAlloc_726_, 6, v_messages_706_);
lean_ctor_set(v_reuseFailAlloc_726_, 7, v___x_720_);
lean_ctor_set(v_reuseFailAlloc_726_, 8, v_snapshotTasks_707_);
v___x_722_ = v_reuseFailAlloc_726_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_723_ = lean_st_ref_set(v___y_691_, v___x_722_);
v___x_724_ = lean_box(0);
v___x_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
return v___x_725_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___redArg___boxed(lean_object* v_t_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___redArg(v_t_730_, v___y_731_);
lean_dec(v___y_731_);
return v_res_733_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__0(void){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_734_ = lean_unsigned_to_nat(32u);
v___x_735_ = lean_mk_empty_array_with_capacity(v___x_734_);
v___x_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
return v___x_736_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__1(void){
_start:
{
size_t v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_737_ = ((size_t)5ULL);
v___x_738_ = lean_unsigned_to_nat(0u);
v___x_739_ = lean_unsigned_to_nat(32u);
v___x_740_ = lean_mk_empty_array_with_capacity(v___x_739_);
v___x_741_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__0);
v___x_742_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_742_, 0, v___x_741_);
lean_ctor_set(v___x_742_, 1, v___x_740_);
lean_ctor_set(v___x_742_, 2, v___x_738_);
lean_ctor_set(v___x_742_, 3, v___x_738_);
lean_ctor_set_usize(v___x_742_, 4, v___x_737_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0(lean_object* v_t_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v___x_749_; lean_object* v_infoState_750_; uint8_t v_enabled_751_; 
v___x_749_ = lean_st_ref_get(v___y_747_);
v_infoState_750_ = lean_ctor_get(v___x_749_, 7);
lean_inc_ref(v_infoState_750_);
lean_dec(v___x_749_);
v_enabled_751_ = lean_ctor_get_uint8(v_infoState_750_, sizeof(void*)*3);
lean_dec_ref(v_infoState_750_);
if (v_enabled_751_ == 0)
{
lean_object* v___x_752_; lean_object* v___x_753_; 
lean_dec_ref(v_t_743_);
v___x_752_ = lean_box(0);
v___x_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
return v___x_753_;
}
else
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_754_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__1);
v___x_755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_755_, 0, v_t_743_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
v___x_756_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___redArg(v___x_755_, v___y_747_);
return v___x_756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___boxed(lean_object* v_t_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0(v_t_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__1(lean_object* v___x_764_, lean_object* v_as_765_, size_t v_sz_766_, size_t v_i_767_, lean_object* v_b_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
uint8_t v___x_774_; 
v___x_774_ = lean_usize_dec_lt(v_i_767_, v_sz_766_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; 
lean_dec_ref(v___x_764_);
v___x_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_775_, 0, v_b_768_);
return v___x_775_;
}
else
{
lean_object* v_snd_776_; lean_object* v_fst_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_824_; 
v_snd_776_ = lean_ctor_get(v_b_768_, 1);
v_fst_777_ = lean_ctor_get(v_b_768_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v_b_768_);
if (v_isSharedCheck_824_ == 0)
{
v___x_779_ = v_b_768_;
v_isShared_780_ = v_isSharedCheck_824_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_snd_776_);
lean_inc(v_fst_777_);
lean_dec(v_b_768_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_824_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v_array_781_; lean_object* v_start_782_; lean_object* v_stop_783_; uint8_t v___x_784_; 
v_array_781_ = lean_ctor_get(v_snd_776_, 0);
v_start_782_ = lean_ctor_get(v_snd_776_, 1);
v_stop_783_ = lean_ctor_get(v_snd_776_, 2);
v___x_784_ = lean_nat_dec_lt(v_start_782_, v_stop_783_);
if (v___x_784_ == 0)
{
lean_object* v___x_786_; 
lean_dec_ref(v___x_764_);
if (v_isShared_780_ == 0)
{
v___x_786_ = v___x_779_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_fst_777_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v_snd_776_);
v___x_786_ = v_reuseFailAlloc_788_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
lean_object* v___x_787_; 
v___x_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_787_, 0, v___x_786_);
return v___x_787_;
}
}
else
{
lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_820_; 
lean_inc(v_stop_783_);
lean_inc(v_start_782_);
lean_inc_ref(v_array_781_);
v_isSharedCheck_820_ = !lean_is_exclusive(v_snd_776_);
if (v_isSharedCheck_820_ == 0)
{
lean_object* v_unused_821_; lean_object* v_unused_822_; lean_object* v_unused_823_; 
v_unused_821_ = lean_ctor_get(v_snd_776_, 2);
lean_dec(v_unused_821_);
v_unused_822_ = lean_ctor_get(v_snd_776_, 1);
lean_dec(v_unused_822_);
v_unused_823_ = lean_ctor_get(v_snd_776_, 0);
lean_dec(v_unused_823_);
v___x_790_ = v_snd_776_;
v_isShared_791_ = v_isSharedCheck_820_;
goto v_resetjp_789_;
}
else
{
lean_dec(v_snd_776_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_820_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v_a_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v_a_792_ = lean_array_uget_borrowed(v_as_765_, v_i_767_);
v___x_793_ = lean_array_fget_borrowed(v_array_781_, v_start_782_);
lean_inc_n(v___x_793_, 3);
v___x_794_ = l_Lean_mkFVar(v___x_793_);
lean_inc_n(v_a_792_, 2);
v___x_795_ = l_Lean_Meta_FVarSubst_insert(v_fst_777_, v_a_792_, v___x_794_);
lean_inc_ref(v___x_764_);
v___x_796_ = l_Lean_LocalContext_get_x21(v___x_764_, v___x_793_);
v___x_797_ = l_Lean_LocalDecl_userName(v___x_796_);
lean_dec_ref(v___x_796_);
v___x_798_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
lean_ctor_set(v___x_798_, 1, v___x_793_);
lean_ctor_set(v___x_798_, 2, v_a_792_);
v___x_799_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
v___x_800_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0(v___x_799_, v___y_769_, v___y_770_, v___y_771_, v___y_772_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_804_; 
lean_dec_ref_known(v___x_800_, 1);
v___x_801_ = lean_unsigned_to_nat(1u);
v___x_802_ = lean_nat_add(v_start_782_, v___x_801_);
lean_dec(v_start_782_);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 1, v___x_802_);
v___x_804_ = v___x_790_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_array_781_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v___x_802_);
lean_ctor_set(v_reuseFailAlloc_811_, 2, v_stop_783_);
v___x_804_ = v_reuseFailAlloc_811_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
lean_object* v___x_806_; 
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 1, v___x_804_);
lean_ctor_set(v___x_779_, 0, v___x_795_);
v___x_806_ = v___x_779_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_795_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v___x_804_);
v___x_806_ = v_reuseFailAlloc_810_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
size_t v___x_807_; size_t v___x_808_; 
v___x_807_ = ((size_t)1ULL);
v___x_808_ = lean_usize_add(v_i_767_, v___x_807_);
v_i_767_ = v___x_808_;
v_b_768_ = v___x_806_;
goto _start;
}
}
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_dec(v___x_795_);
lean_del_object(v___x_790_);
lean_dec(v_stop_783_);
lean_dec(v_start_782_);
lean_dec_ref(v_array_781_);
lean_del_object(v___x_779_);
lean_dec_ref(v___x_764_);
v_a_812_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_800_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_800_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__1___boxed(lean_object* v___x_825_, lean_object* v_as_826_, lean_object* v_sz_827_, lean_object* v_i_828_, lean_object* v_b_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
size_t v_sz_boxed_835_; size_t v_i_boxed_836_; lean_object* v_res_837_; 
v_sz_boxed_835_ = lean_unbox_usize(v_sz_827_);
lean_dec(v_sz_827_);
v_i_boxed_836_ = lean_unbox_usize(v_i_828_);
lean_dec(v_i_828_);
v_res_837_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__1(v___x_825_, v_as_826_, v_sz_boxed_835_, v_i_boxed_836_, v_b_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec_ref(v_as_826_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertAfter(lean_object* v_mvarId_841_, lean_object* v_fvarId_842_, lean_object* v_userName_843_, lean_object* v_type_844_, lean_object* v_val_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = ((lean_object*)(l_Lean_MVarId_assertAfter___closed__1));
lean_inc(v_mvarId_841_);
v___x_852_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_841_, v___x_851_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v___x_853_; 
lean_dec_ref_known(v___x_852_, 1);
v___x_853_ = l_Lean_MVarId_revertAfter(v_mvarId_841_, v_fvarId_842_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v_fst_855_; lean_object* v_snd_856_; lean_object* v___x_857_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_854_);
lean_dec_ref_known(v___x_853_, 1);
v_fst_855_ = lean_ctor_get(v_a_854_, 0);
lean_inc(v_fst_855_);
v_snd_856_ = lean_ctor_get(v_a_854_, 1);
lean_inc(v_snd_856_);
lean_dec(v_a_854_);
v___x_857_ = l_Lean_MVarId_assert(v_snd_856_, v_userName_843_, v_type_844_, v_val_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; uint8_t v___x_859_; lean_object* v___x_860_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_a_858_);
lean_dec_ref_known(v___x_857_, 1);
v___x_859_ = 1;
v___x_860_ = l_Lean_Meta_intro1Core(v_a_858_, v___x_859_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v_fst_862_; lean_object* v_snd_863_; lean_object* v___x_864_; lean_object* v___x_865_; uint8_t v___x_866_; lean_object* v___x_867_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_a_861_);
lean_dec_ref_known(v___x_860_, 1);
v_fst_862_ = lean_ctor_get(v_a_861_, 0);
lean_inc(v_fst_862_);
v_snd_863_ = lean_ctor_get(v_a_861_, 1);
lean_inc(v_snd_863_);
lean_dec(v_a_861_);
v___x_864_ = lean_array_get_size(v_fst_855_);
v___x_865_ = lean_box(0);
v___x_866_ = 0;
v___x_867_ = l_Lean_Meta_introNCore(v_snd_863_, v___x_864_, v___x_865_, v___x_866_, v___x_859_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v_fst_869_; lean_object* v_snd_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_913_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_868_);
lean_dec_ref_known(v___x_867_, 1);
v_fst_869_ = lean_ctor_get(v_a_868_, 0);
v_snd_870_ = lean_ctor_get(v_a_868_, 1);
v_isSharedCheck_913_ = !lean_is_exclusive(v_a_868_);
if (v_isSharedCheck_913_ == 0)
{
v___x_872_ = v_a_868_;
v_isShared_873_ = v_isSharedCheck_913_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_snd_870_);
lean_inc(v_fst_869_);
lean_dec(v_a_868_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_913_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_874_; 
lean_inc(v_snd_870_);
v___x_874_ = l_Lean_MVarId_getDecl(v_snd_870_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; lean_object* v_lctx_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_882_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_a_875_);
lean_dec_ref_known(v___x_874_, 1);
v_lctx_876_ = lean_ctor_get(v_a_875_, 1);
lean_inc_ref(v_lctx_876_);
lean_dec(v_a_875_);
v___x_877_ = lean_box(0);
v___x_878_ = lean_unsigned_to_nat(0u);
v___x_879_ = lean_array_get_size(v_fst_869_);
v___x_880_ = l_Array_toSubarray___redArg(v_fst_869_, v___x_878_, v___x_879_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 1, v___x_880_);
lean_ctor_set(v___x_872_, 0, v___x_877_);
v___x_882_ = v___x_872_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_877_);
lean_ctor_set(v_reuseFailAlloc_904_, 1, v___x_880_);
v___x_882_ = v_reuseFailAlloc_904_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
size_t v_sz_883_; size_t v___x_884_; lean_object* v___x_885_; 
v_sz_883_ = lean_array_size(v_fst_855_);
v___x_884_ = ((size_t)0ULL);
v___x_885_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__1(v_lctx_876_, v_fst_855_, v_sz_883_, v___x_884_, v___x_882_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
lean_dec(v_fst_855_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_895_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_895_ == 0)
{
v___x_888_ = v___x_885_;
v_isShared_889_ = v_isSharedCheck_895_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_885_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_895_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v_fst_890_; lean_object* v___x_891_; lean_object* v___x_893_; 
v_fst_890_ = lean_ctor_get(v_a_886_, 0);
lean_inc(v_fst_890_);
lean_dec(v_a_886_);
v___x_891_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_891_, 0, v_fst_862_);
lean_ctor_set(v___x_891_, 1, v_snd_870_);
lean_ctor_set(v___x_891_, 2, v_fst_890_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v___x_891_);
v___x_893_ = v___x_888_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_891_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
else
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_903_; 
lean_dec(v_snd_870_);
lean_dec(v_fst_862_);
v_a_896_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_903_ == 0)
{
v___x_898_ = v___x_885_;
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_885_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_901_; 
if (v_isShared_899_ == 0)
{
v___x_901_ = v___x_898_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_896_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
}
else
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
lean_del_object(v___x_872_);
lean_dec(v_snd_870_);
lean_dec(v_fst_869_);
lean_dec(v_fst_862_);
lean_dec(v_fst_855_);
v_a_905_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_912_ == 0)
{
v___x_907_ = v___x_874_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_874_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_905_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
}
else
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_921_; 
lean_dec(v_fst_862_);
lean_dec(v_fst_855_);
v_a_914_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_921_ == 0)
{
v___x_916_ = v___x_867_;
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_867_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_917_ == 0)
{
v___x_919_ = v___x_916_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_a_914_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
lean_dec(v_fst_855_);
v_a_922_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_860_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_860_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
else
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_937_; 
lean_dec(v_fst_855_);
v_a_930_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_937_ == 0)
{
v___x_932_ = v___x_857_;
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_857_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
if (v_isShared_933_ == 0)
{
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_a_930_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
else
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_945_; 
lean_dec_ref(v_val_845_);
lean_dec_ref(v_type_844_);
lean_dec(v_userName_843_);
v_a_938_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_945_ == 0)
{
v___x_940_ = v___x_853_;
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_853_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_943_; 
if (v_isShared_941_ == 0)
{
v___x_943_ = v___x_940_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_a_938_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
else
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_953_; 
lean_dec_ref(v_val_845_);
lean_dec_ref(v_type_844_);
lean_dec(v_userName_843_);
lean_dec(v_fvarId_842_);
lean_dec(v_mvarId_841_);
v_a_946_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_953_ == 0)
{
v___x_948_ = v___x_852_;
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_852_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_951_; 
if (v_isShared_949_ == 0)
{
v___x_951_ = v___x_948_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_946_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertAfter___boxed(lean_object* v_mvarId_954_, lean_object* v_fvarId_955_, lean_object* v_userName_956_, lean_object* v_type_957_, lean_object* v_val_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_MVarId_assertAfter(v_mvarId_954_, v_fvarId_955_, v_userName_956_, v_type_957_, v_val_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0(lean_object* v_t_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___redArg(v_t_965_, v___y_969_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___boxed(lean_object* v_t_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0(v_t_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg(lean_object* v_ldecl_x27_979_, lean_object* v_a_980_){
_start:
{
lean_object* v___x_982_; lean_object* v_fst_984_; lean_object* v_snd_985_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; uint8_t v___x_991_; 
v___x_982_ = lean_st_ref_take(v_a_980_);
v___x_988_ = lean_box(0);
v___x_989_ = l_Lean_LocalDecl_index(v___x_982_);
v___x_990_ = l_Lean_LocalDecl_index(v_ldecl_x27_979_);
v___x_991_ = lean_nat_dec_lt(v___x_989_, v___x_990_);
lean_dec(v___x_990_);
lean_dec(v___x_989_);
if (v___x_991_ == 0)
{
lean_dec_ref(v_ldecl_x27_979_);
v_fst_984_ = v___x_988_;
v_snd_985_ = v___x_982_;
goto v___jp_983_;
}
else
{
lean_dec(v___x_982_);
v_fst_984_ = v___x_988_;
v_snd_985_ = v_ldecl_x27_979_;
goto v___jp_983_;
}
v___jp_983_:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = lean_st_ref_set(v_a_980_, v_snd_985_);
v___x_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_987_, 0, v_fst_984_);
return v___x_987_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg___boxed(lean_object* v_ldecl_x27_992_, lean_object* v_a_993_, lean_object* v_a_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg(v_ldecl_x27_992_, v_a_993_);
lean_dec(v_a_993_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl(lean_object* v_ldecl_x27_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg(v_ldecl_x27_996_, v_a_997_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___boxed(lean_object* v_ldecl_x27_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl(v_ldecl_x27_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
lean_dec(v_a_1009_);
lean_dec_ref(v_a_1008_);
lean_dec(v_a_1007_);
lean_dec_ref(v_a_1006_);
lean_dec(v_a_1005_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___redArg(lean_object* v_as_1012_, size_t v_i_1013_, size_t v_stop_1014_, lean_object* v_b_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v_a_1022_; uint8_t v___x_1026_; 
v___x_1026_ = lean_usize_dec_eq(v_i_1013_, v_stop_1014_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1027_; 
v___x_1027_ = lean_array_uget_borrowed(v_as_1012_, v_i_1013_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v___x_1028_; 
v___x_1028_ = lean_box(0);
v_a_1022_ = v___x_1028_;
goto v___jp_1021_;
}
else
{
lean_object* v_val_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v_val_1029_ = lean_ctor_get(v___x_1027_, 0);
v___x_1030_ = l_Lean_LocalDecl_fvarId(v_val_1029_);
v___x_1031_ = l_Lean_FVarId_getDecl___redArg(v___x_1030_, v___y_1017_, v___y_1018_, v___y_1019_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; lean_object* v___x_1033_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_a_1032_);
lean_dec_ref_known(v___x_1031_, 1);
v___x_1033_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg(v_a_1032_, v___y_1016_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v_a_1034_; 
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
lean_inc(v_a_1034_);
lean_dec_ref_known(v___x_1033_, 1);
v_a_1022_ = v_a_1034_;
goto v___jp_1021_;
}
else
{
return v___x_1033_;
}
}
else
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
v_a_1035_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1037_ = v___x_1031_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_1031_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1038_ == 0)
{
v___x_1040_ = v___x_1037_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1035_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
}
else
{
lean_object* v___x_1043_; 
v___x_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1043_, 0, v_b_1015_);
return v___x_1043_;
}
v___jp_1021_:
{
size_t v___x_1023_; size_t v___x_1024_; 
v___x_1023_ = ((size_t)1ULL);
v___x_1024_ = lean_usize_add(v_i_1013_, v___x_1023_);
v_i_1013_ = v___x_1024_;
v_b_1015_ = v_a_1022_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_as_1044_, lean_object* v_i_1045_, lean_object* v_stop_1046_, lean_object* v_b_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
size_t v_i_boxed_1053_; size_t v_stop_boxed_1054_; lean_object* v_res_1055_; 
v_i_boxed_1053_ = lean_unbox_usize(v_i_1045_);
lean_dec(v_i_1045_);
v_stop_boxed_1054_ = lean_unbox_usize(v_stop_1046_);
lean_dec(v_stop_1046_);
v_res_1055_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___redArg(v_as_1044_, v_i_boxed_1053_, v_stop_boxed_1054_, v_b_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v_as_1044_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(lean_object* v_as_1056_, size_t v_i_1057_, size_t v_stop_1058_, lean_object* v_b_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v_a_1067_; uint8_t v___x_1071_; 
v___x_1071_ = lean_usize_dec_eq(v_i_1057_, v_stop_1058_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; 
v___x_1072_ = lean_array_uget_borrowed(v_as_1056_, v_i_1057_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v___x_1073_; 
v___x_1073_ = lean_box(0);
v_a_1067_ = v___x_1073_;
goto v___jp_1066_;
}
else
{
lean_object* v_val_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v_val_1074_ = lean_ctor_get(v___x_1072_, 0);
v___x_1075_ = l_Lean_LocalDecl_fvarId(v_val_1074_);
v___x_1076_ = l_Lean_FVarId_getDecl___redArg(v___x_1075_, v___y_1061_, v___y_1063_, v___y_1064_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; lean_object* v___x_1078_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_a_1077_);
lean_dec_ref_known(v___x_1076_, 1);
v___x_1078_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg(v_a_1077_, v___y_1060_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; 
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_a_1079_);
lean_dec_ref_known(v___x_1078_, 1);
v_a_1067_ = v_a_1079_;
goto v___jp_1066_;
}
else
{
return v___x_1078_;
}
}
else
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
v_a_1080_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_1076_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1076_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
}
else
{
lean_object* v___x_1088_; 
v___x_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1088_, 0, v_b_1059_);
return v___x_1088_;
}
v___jp_1066_:
{
size_t v___x_1068_; size_t v___x_1069_; lean_object* v___x_1070_; 
v___x_1068_ = ((size_t)1ULL);
v___x_1069_ = lean_usize_add(v_i_1057_, v___x_1068_);
v___x_1070_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___redArg(v_as_1056_, v___x_1069_, v_stop_1058_, v_a_1067_, v___y_1060_, v___y_1061_, v___y_1063_, v___y_1064_);
return v___x_1070_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2___boxed(lean_object* v_as_1089_, lean_object* v_i_1090_, lean_object* v_stop_1091_, lean_object* v_b_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
size_t v_i_boxed_1099_; size_t v_stop_boxed_1100_; lean_object* v_res_1101_; 
v_i_boxed_1099_ = lean_unbox_usize(v_i_1090_);
lean_dec(v_i_1090_);
v_stop_boxed_1100_ = lean_unbox_usize(v_stop_1091_);
lean_dec(v_stop_1091_);
v_res_1101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_as_1089_, v_i_boxed_1099_, v_stop_boxed_1100_, v_b_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v_as_1089_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
if (lean_obj_tag(v_x_1102_) == 0)
{
lean_object* v_cs_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1130_; 
v_cs_1109_ = lean_ctor_get(v_x_1102_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v_x_1102_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1111_ = v_x_1102_;
v_isShared_1112_ = v_isSharedCheck_1130_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_cs_1109_);
lean_dec(v_x_1102_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1130_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; uint8_t v___x_1116_; 
v___x_1113_ = lean_unsigned_to_nat(0u);
v___x_1114_ = lean_array_get_size(v_cs_1109_);
v___x_1115_ = lean_box(0);
v___x_1116_ = lean_nat_dec_lt(v___x_1113_, v___x_1114_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1118_; 
lean_dec_ref(v_cs_1109_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 0, v___x_1115_);
v___x_1118_ = v___x_1111_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1115_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
else
{
uint8_t v___x_1120_; 
v___x_1120_ = lean_nat_dec_le(v___x_1114_, v___x_1114_);
if (v___x_1120_ == 0)
{
if (v___x_1116_ == 0)
{
lean_object* v___x_1122_; 
lean_dec_ref(v_cs_1109_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 0, v___x_1115_);
v___x_1122_ = v___x_1111_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1115_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
else
{
size_t v___x_1124_; size_t v___x_1125_; lean_object* v___x_1126_; 
lean_del_object(v___x_1111_);
v___x_1124_ = ((size_t)0ULL);
v___x_1125_ = lean_usize_of_nat(v___x_1114_);
v___x_1126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4(v_cs_1109_, v___x_1124_, v___x_1125_, v___x_1115_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
lean_dec_ref(v_cs_1109_);
return v___x_1126_;
}
}
else
{
size_t v___x_1127_; size_t v___x_1128_; lean_object* v___x_1129_; 
lean_del_object(v___x_1111_);
v___x_1127_ = ((size_t)0ULL);
v___x_1128_ = lean_usize_of_nat(v___x_1114_);
v___x_1129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4(v_cs_1109_, v___x_1127_, v___x_1128_, v___x_1115_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
lean_dec_ref(v_cs_1109_);
return v___x_1129_;
}
}
}
}
else
{
lean_object* v_vs_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1152_; 
v_vs_1131_ = lean_ctor_get(v_x_1102_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v_x_1102_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1133_ = v_x_1102_;
v_isShared_1134_ = v_isSharedCheck_1152_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_vs_1131_);
lean_dec(v_x_1102_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1152_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; uint8_t v___x_1138_; 
v___x_1135_ = lean_unsigned_to_nat(0u);
v___x_1136_ = lean_array_get_size(v_vs_1131_);
v___x_1137_ = lean_box(0);
v___x_1138_ = lean_nat_dec_lt(v___x_1135_, v___x_1136_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1140_; 
lean_dec_ref(v_vs_1131_);
if (v_isShared_1134_ == 0)
{
lean_ctor_set_tag(v___x_1133_, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1137_);
v___x_1140_ = v___x_1133_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1137_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
else
{
uint8_t v___x_1142_; 
v___x_1142_ = lean_nat_dec_le(v___x_1136_, v___x_1136_);
if (v___x_1142_ == 0)
{
if (v___x_1138_ == 0)
{
lean_object* v___x_1144_; 
lean_dec_ref(v_vs_1131_);
if (v_isShared_1134_ == 0)
{
lean_ctor_set_tag(v___x_1133_, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1137_);
v___x_1144_ = v___x_1133_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1137_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
else
{
size_t v___x_1146_; size_t v___x_1147_; lean_object* v___x_1148_; 
lean_del_object(v___x_1133_);
v___x_1146_ = ((size_t)0ULL);
v___x_1147_ = lean_usize_of_nat(v___x_1136_);
v___x_1148_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_vs_1131_, v___x_1146_, v___x_1147_, v___x_1137_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
lean_dec_ref(v_vs_1131_);
return v___x_1148_;
}
}
else
{
size_t v___x_1149_; size_t v___x_1150_; lean_object* v___x_1151_; 
lean_del_object(v___x_1133_);
v___x_1149_ = ((size_t)0ULL);
v___x_1150_ = lean_usize_of_nat(v___x_1136_);
v___x_1151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_vs_1131_, v___x_1149_, v___x_1150_, v___x_1137_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
lean_dec_ref(v_vs_1131_);
return v___x_1151_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4(lean_object* v_as_1153_, size_t v_i_1154_, size_t v_stop_1155_, lean_object* v_b_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
uint8_t v___x_1163_; 
v___x_1163_ = lean_usize_dec_eq(v_i_1154_, v_stop_1155_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = lean_array_uget_borrowed(v_as_1153_, v_i_1154_);
lean_inc(v___x_1164_);
v___x_1165_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__3(v___x_1164_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; size_t v___x_1167_; size_t v___x_1168_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_a_1166_);
lean_dec_ref_known(v___x_1165_, 1);
v___x_1167_ = ((size_t)1ULL);
v___x_1168_ = lean_usize_add(v_i_1154_, v___x_1167_);
v_i_1154_ = v___x_1168_;
v_b_1156_ = v_a_1166_;
goto _start;
}
else
{
return v___x_1165_;
}
}
else
{
lean_object* v___x_1170_; 
v___x_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1170_, 0, v_b_1156_);
return v___x_1170_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_as_1171_, lean_object* v_i_1172_, lean_object* v_stop_1173_, lean_object* v_b_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
size_t v_i_boxed_1181_; size_t v_stop_boxed_1182_; lean_object* v_res_1183_; 
v_i_boxed_1181_ = lean_unbox_usize(v_i_1172_);
lean_dec(v_i_1172_);
v_stop_boxed_1182_ = lean_unbox_usize(v_stop_1173_);
lean_dec(v_stop_1173_);
v_res_1183_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4(v_as_1171_, v_i_boxed_1181_, v_stop_boxed_1182_, v_b_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___y_1175_);
lean_dec_ref(v_as_1171_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__3(v_x_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v___y_1185_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__3(lean_object* v_t_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v_root_1199_; lean_object* v_tail_1200_; lean_object* v___x_1201_; 
v_root_1199_ = lean_ctor_get(v_t_1192_, 0);
lean_inc_ref(v_root_1199_);
v_tail_1200_ = lean_ctor_get(v_t_1192_, 1);
lean_inc_ref(v_tail_1200_);
lean_dec_ref(v_t_1192_);
v___x_1201_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__3(v_root_1199_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
if (lean_obj_tag(v___x_1201_) == 0)
{
lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1222_; 
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1222_ == 0)
{
lean_object* v_unused_1223_; 
v_unused_1223_ = lean_ctor_get(v___x_1201_, 0);
lean_dec(v_unused_1223_);
v___x_1203_ = v___x_1201_;
v_isShared_1204_ = v_isSharedCheck_1222_;
goto v_resetjp_1202_;
}
else
{
lean_dec(v___x_1201_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1222_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; uint8_t v___x_1208_; 
v___x_1205_ = lean_unsigned_to_nat(0u);
v___x_1206_ = lean_array_get_size(v_tail_1200_);
v___x_1207_ = lean_box(0);
v___x_1208_ = lean_nat_dec_lt(v___x_1205_, v___x_1206_);
if (v___x_1208_ == 0)
{
lean_object* v___x_1210_; 
lean_dec_ref(v_tail_1200_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 0, v___x_1207_);
v___x_1210_ = v___x_1203_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1207_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
else
{
uint8_t v___x_1212_; 
v___x_1212_ = lean_nat_dec_le(v___x_1206_, v___x_1206_);
if (v___x_1212_ == 0)
{
if (v___x_1208_ == 0)
{
lean_object* v___x_1214_; 
lean_dec_ref(v_tail_1200_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 0, v___x_1207_);
v___x_1214_ = v___x_1203_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1207_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
else
{
size_t v___x_1216_; size_t v___x_1217_; lean_object* v___x_1218_; 
lean_del_object(v___x_1203_);
v___x_1216_ = ((size_t)0ULL);
v___x_1217_ = lean_usize_of_nat(v___x_1206_);
v___x_1218_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_tail_1200_, v___x_1216_, v___x_1217_, v___x_1207_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
lean_dec_ref(v_tail_1200_);
return v___x_1218_;
}
}
else
{
size_t v___x_1219_; size_t v___x_1220_; lean_object* v___x_1221_; 
lean_del_object(v___x_1203_);
v___x_1219_ = ((size_t)0ULL);
v___x_1220_ = lean_usize_of_nat(v___x_1206_);
v___x_1221_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_tail_1200_, v___x_1219_, v___x_1220_, v___x_1207_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
lean_dec_ref(v_tail_1200_);
return v___x_1221_;
}
}
}
}
else
{
lean_dec_ref(v_tail_1200_);
return v___x_1201_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__3___boxed(lean_object* v_t_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__3(v_t_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
return v_res_1231_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1232_; 
v___x_1232_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1(lean_object* v_x_1233_, size_t v_x_1234_, size_t v_x_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
if (lean_obj_tag(v_x_1233_) == 0)
{
lean_object* v_cs_1242_; lean_object* v___x_1243_; size_t v___x_1244_; lean_object* v_j_1245_; lean_object* v___x_1246_; size_t v___x_1247_; size_t v___x_1248_; size_t v___x_1249_; size_t v___x_1250_; size_t v___x_1251_; size_t v___x_1252_; lean_object* v___x_1253_; 
v_cs_1242_ = lean_ctor_get(v_x_1233_, 0);
lean_inc_ref(v_cs_1242_);
lean_dec_ref_known(v_x_1233_, 1);
v___x_1243_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___closed__0);
v___x_1244_ = lean_usize_shift_right(v_x_1234_, v_x_1235_);
v_j_1245_ = lean_usize_to_nat(v___x_1244_);
v___x_1246_ = lean_array_get_borrowed(v___x_1243_, v_cs_1242_, v_j_1245_);
v___x_1247_ = ((size_t)1ULL);
v___x_1248_ = lean_usize_shift_left(v___x_1247_, v_x_1235_);
v___x_1249_ = lean_usize_sub(v___x_1248_, v___x_1247_);
v___x_1250_ = lean_usize_land(v_x_1234_, v___x_1249_);
v___x_1251_ = ((size_t)5ULL);
v___x_1252_ = lean_usize_sub(v_x_1235_, v___x_1251_);
lean_inc(v___x_1246_);
v___x_1253_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1(v___x_1246_, v___x_1250_, v___x_1252_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1275_; 
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1275_ == 0)
{
lean_object* v_unused_1276_; 
v_unused_1276_ = lean_ctor_get(v___x_1253_, 0);
lean_dec(v_unused_1276_);
v___x_1255_ = v___x_1253_;
v_isShared_1256_ = v_isSharedCheck_1275_;
goto v_resetjp_1254_;
}
else
{
lean_dec(v___x_1253_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1275_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; uint8_t v___x_1261_; 
v___x_1257_ = lean_unsigned_to_nat(1u);
v___x_1258_ = lean_nat_add(v_j_1245_, v___x_1257_);
lean_dec(v_j_1245_);
v___x_1259_ = lean_array_get_size(v_cs_1242_);
v___x_1260_ = lean_box(0);
v___x_1261_ = lean_nat_dec_lt(v___x_1258_, v___x_1259_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1263_; 
lean_dec(v___x_1258_);
lean_dec_ref(v_cs_1242_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 0, v___x_1260_);
v___x_1263_ = v___x_1255_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1260_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
else
{
uint8_t v___x_1265_; 
v___x_1265_ = lean_nat_dec_le(v___x_1259_, v___x_1259_);
if (v___x_1265_ == 0)
{
if (v___x_1261_ == 0)
{
lean_object* v___x_1267_; 
lean_dec(v___x_1258_);
lean_dec_ref(v_cs_1242_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 0, v___x_1260_);
v___x_1267_ = v___x_1255_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1260_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
else
{
size_t v___x_1269_; size_t v___x_1270_; lean_object* v___x_1271_; 
lean_del_object(v___x_1255_);
v___x_1269_ = lean_usize_of_nat(v___x_1258_);
lean_dec(v___x_1258_);
v___x_1270_ = lean_usize_of_nat(v___x_1259_);
v___x_1271_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4(v_cs_1242_, v___x_1269_, v___x_1270_, v___x_1260_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
lean_dec_ref(v_cs_1242_);
return v___x_1271_;
}
}
else
{
size_t v___x_1272_; size_t v___x_1273_; lean_object* v___x_1274_; 
lean_del_object(v___x_1255_);
v___x_1272_ = lean_usize_of_nat(v___x_1258_);
lean_dec(v___x_1258_);
v___x_1273_ = lean_usize_of_nat(v___x_1259_);
v___x_1274_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4(v_cs_1242_, v___x_1272_, v___x_1273_, v___x_1260_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
lean_dec_ref(v_cs_1242_);
return v___x_1274_;
}
}
}
}
else
{
lean_dec(v_j_1245_);
lean_dec_ref(v_cs_1242_);
return v___x_1253_;
}
}
else
{
lean_object* v_vs_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1298_; 
v_vs_1277_ = lean_ctor_get(v_x_1233_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v_x_1233_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1279_ = v_x_1233_;
v_isShared_1280_ = v_isSharedCheck_1298_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_vs_1277_);
lean_dec(v_x_1233_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1298_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; uint8_t v___x_1284_; 
v___x_1281_ = lean_usize_to_nat(v_x_1234_);
v___x_1282_ = lean_array_get_size(v_vs_1277_);
v___x_1283_ = lean_box(0);
v___x_1284_ = lean_nat_dec_lt(v___x_1281_, v___x_1282_);
if (v___x_1284_ == 0)
{
lean_object* v___x_1286_; 
lean_dec(v___x_1281_);
lean_dec_ref(v_vs_1277_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set_tag(v___x_1279_, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1283_);
v___x_1286_ = v___x_1279_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1283_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
else
{
uint8_t v___x_1288_; 
v___x_1288_ = lean_nat_dec_le(v___x_1282_, v___x_1282_);
if (v___x_1288_ == 0)
{
if (v___x_1284_ == 0)
{
lean_object* v___x_1290_; 
lean_dec(v___x_1281_);
lean_dec_ref(v_vs_1277_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set_tag(v___x_1279_, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1283_);
v___x_1290_ = v___x_1279_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1283_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
else
{
size_t v___x_1292_; size_t v___x_1293_; lean_object* v___x_1294_; 
lean_del_object(v___x_1279_);
v___x_1292_ = lean_usize_of_nat(v___x_1281_);
lean_dec(v___x_1281_);
v___x_1293_ = lean_usize_of_nat(v___x_1282_);
v___x_1294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_vs_1277_, v___x_1292_, v___x_1293_, v___x_1283_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
lean_dec_ref(v_vs_1277_);
return v___x_1294_;
}
}
else
{
size_t v___x_1295_; size_t v___x_1296_; lean_object* v___x_1297_; 
lean_del_object(v___x_1279_);
v___x_1295_ = lean_usize_of_nat(v___x_1281_);
lean_dec(v___x_1281_);
v___x_1296_ = lean_usize_of_nat(v___x_1282_);
v___x_1297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_vs_1277_, v___x_1295_, v___x_1296_, v___x_1283_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
lean_dec_ref(v_vs_1277_);
return v___x_1297_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___boxed(lean_object* v_x_1299_, lean_object* v_x_1300_, lean_object* v_x_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
size_t v_x_9426__boxed_1308_; size_t v_x_9427__boxed_1309_; lean_object* v_res_1310_; 
v_x_9426__boxed_1308_ = lean_unbox_usize(v_x_1300_);
lean_dec(v_x_1300_);
v_x_9427__boxed_1309_ = lean_unbox_usize(v_x_1301_);
lean_dec(v_x_1301_);
v_res_1310_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1(v_x_1299_, v_x_9426__boxed_1308_, v_x_9427__boxed_1309_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0(lean_object* v_t_1311_, lean_object* v_start_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v___x_1319_; uint8_t v___x_1320_; 
v___x_1319_ = lean_unsigned_to_nat(0u);
v___x_1320_ = lean_nat_dec_eq(v_start_1312_, v___x_1319_);
if (v___x_1320_ == 0)
{
lean_object* v_root_1321_; lean_object* v_tail_1322_; size_t v_shift_1323_; lean_object* v_tailOff_1324_; uint8_t v___x_1325_; 
v_root_1321_ = lean_ctor_get(v_t_1311_, 0);
lean_inc_ref(v_root_1321_);
v_tail_1322_ = lean_ctor_get(v_t_1311_, 1);
lean_inc_ref(v_tail_1322_);
v_shift_1323_ = lean_ctor_get_usize(v_t_1311_, 4);
v_tailOff_1324_ = lean_ctor_get(v_t_1311_, 3);
lean_inc(v_tailOff_1324_);
lean_dec_ref(v_t_1311_);
v___x_1325_ = lean_nat_dec_le(v_tailOff_1324_, v_start_1312_);
if (v___x_1325_ == 0)
{
size_t v___x_1326_; lean_object* v___x_1327_; 
lean_dec(v_tailOff_1324_);
v___x_1326_ = lean_usize_of_nat(v_start_1312_);
v___x_1327_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1(v_root_1321_, v___x_1326_, v_shift_1323_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1347_; 
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1347_ == 0)
{
lean_object* v_unused_1348_; 
v_unused_1348_ = lean_ctor_get(v___x_1327_, 0);
lean_dec(v_unused_1348_);
v___x_1329_ = v___x_1327_;
v_isShared_1330_ = v_isSharedCheck_1347_;
goto v_resetjp_1328_;
}
else
{
lean_dec(v___x_1327_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1347_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; uint8_t v___x_1333_; 
v___x_1331_ = lean_array_get_size(v_tail_1322_);
v___x_1332_ = lean_box(0);
v___x_1333_ = lean_nat_dec_lt(v___x_1319_, v___x_1331_);
if (v___x_1333_ == 0)
{
lean_object* v___x_1335_; 
lean_dec_ref(v_tail_1322_);
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 0, v___x_1332_);
v___x_1335_ = v___x_1329_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1332_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
else
{
uint8_t v___x_1337_; 
v___x_1337_ = lean_nat_dec_le(v___x_1331_, v___x_1331_);
if (v___x_1337_ == 0)
{
if (v___x_1333_ == 0)
{
lean_object* v___x_1339_; 
lean_dec_ref(v_tail_1322_);
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 0, v___x_1332_);
v___x_1339_ = v___x_1329_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1332_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
else
{
size_t v___x_1341_; size_t v___x_1342_; lean_object* v___x_1343_; 
lean_del_object(v___x_1329_);
v___x_1341_ = ((size_t)0ULL);
v___x_1342_ = lean_usize_of_nat(v___x_1331_);
v___x_1343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_tail_1322_, v___x_1341_, v___x_1342_, v___x_1332_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
lean_dec_ref(v_tail_1322_);
return v___x_1343_;
}
}
else
{
size_t v___x_1344_; size_t v___x_1345_; lean_object* v___x_1346_; 
lean_del_object(v___x_1329_);
v___x_1344_ = ((size_t)0ULL);
v___x_1345_ = lean_usize_of_nat(v___x_1331_);
v___x_1346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_tail_1322_, v___x_1344_, v___x_1345_, v___x_1332_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
lean_dec_ref(v_tail_1322_);
return v___x_1346_;
}
}
}
}
else
{
lean_dec_ref(v_tail_1322_);
return v___x_1327_;
}
}
else
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; 
lean_dec_ref(v_root_1321_);
v___x_1349_ = lean_nat_sub(v_start_1312_, v_tailOff_1324_);
lean_dec(v_tailOff_1324_);
v___x_1350_ = lean_array_get_size(v_tail_1322_);
v___x_1351_ = lean_box(0);
v___x_1352_ = lean_nat_dec_lt(v___x_1349_, v___x_1350_);
if (v___x_1352_ == 0)
{
lean_object* v___x_1353_; 
lean_dec(v___x_1349_);
lean_dec_ref(v_tail_1322_);
v___x_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1351_);
return v___x_1353_;
}
else
{
uint8_t v___x_1354_; 
v___x_1354_ = lean_nat_dec_le(v___x_1350_, v___x_1350_);
if (v___x_1354_ == 0)
{
if (v___x_1352_ == 0)
{
lean_object* v___x_1355_; 
lean_dec(v___x_1349_);
lean_dec_ref(v_tail_1322_);
v___x_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1351_);
return v___x_1355_;
}
else
{
size_t v___x_1356_; size_t v___x_1357_; lean_object* v___x_1358_; 
v___x_1356_ = lean_usize_of_nat(v___x_1349_);
lean_dec(v___x_1349_);
v___x_1357_ = lean_usize_of_nat(v___x_1350_);
v___x_1358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_tail_1322_, v___x_1356_, v___x_1357_, v___x_1351_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
lean_dec_ref(v_tail_1322_);
return v___x_1358_;
}
}
else
{
size_t v___x_1359_; size_t v___x_1360_; lean_object* v___x_1361_; 
v___x_1359_ = lean_usize_of_nat(v___x_1349_);
lean_dec(v___x_1349_);
v___x_1360_ = lean_usize_of_nat(v___x_1350_);
v___x_1361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_tail_1322_, v___x_1359_, v___x_1360_, v___x_1351_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
lean_dec_ref(v_tail_1322_);
return v___x_1361_;
}
}
}
}
else
{
lean_object* v___x_1362_; 
v___x_1362_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__3(v_t_1311_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
return v___x_1362_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0___boxed(lean_object* v_t_1363_, lean_object* v_start_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0(v_t_1363_, v_start_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
lean_dec(v___y_1365_);
lean_dec(v_start_1364_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0(lean_object* v_lctx_1372_, lean_object* v_start_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v_decls_1380_; lean_object* v___x_1381_; 
v_decls_1380_ = lean_ctor_get(v_lctx_1372_, 1);
lean_inc_ref(v_decls_1380_);
lean_dec_ref(v_lctx_1372_);
v___x_1381_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0(v_decls_1380_, v_start_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0___boxed(lean_object* v_lctx_1382_, lean_object* v_start_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0(v_lctx_1382_, v_start_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
lean_dec(v___y_1384_);
lean_dec(v_start_1383_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___lam__0(lean_object* v_e_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
if (lean_obj_tag(v_e_1391_) == 1)
{
lean_object* v_fvarId_1398_; lean_object* v___x_1399_; 
v_fvarId_1398_ = lean_ctor_get(v_e_1391_, 0);
lean_inc(v_fvarId_1398_);
lean_dec_ref_known(v_e_1391_, 1);
v___x_1399_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1398_, v___y_1393_, v___y_1395_, v___y_1396_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v_a_1400_; lean_object* v___x_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1410_; 
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
lean_inc(v_a_1400_);
lean_dec_ref_known(v___x_1399_, 1);
v___x_1401_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg(v_a_1400_, v___y_1392_);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1410_ == 0)
{
lean_object* v_unused_1411_; 
v_unused_1411_ = lean_ctor_get(v___x_1401_, 0);
lean_dec(v_unused_1411_);
v___x_1403_ = v___x_1401_;
v_isShared_1404_ = v_isSharedCheck_1410_;
goto v_resetjp_1402_;
}
else
{
lean_dec(v___x_1401_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1410_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
uint8_t v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1408_; 
v___x_1405_ = 0;
v___x_1406_ = lean_box(v___x_1405_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 0, v___x_1406_);
v___x_1408_ = v___x_1403_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1406_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
else
{
lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1419_; 
v_a_1412_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1414_ = v___x_1399_;
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1399_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1412_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
else
{
if (lean_obj_tag(v_e_1391_) == 2)
{
lean_object* v_mvarId_1420_; lean_object* v___x_1421_; 
v_mvarId_1420_ = lean_ctor_get(v_e_1391_, 0);
lean_inc(v_mvarId_1420_);
lean_dec_ref_known(v_e_1391_, 1);
v___x_1421_ = l_Lean_MVarId_getDecl(v_mvarId_1420_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; lean_object* v_lctx_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_a_1422_);
lean_dec_ref_known(v___x_1421_, 1);
v_lctx_1423_ = lean_ctor_get(v_a_1422_, 1);
lean_inc_ref(v_lctx_1423_);
lean_dec(v_a_1422_);
v___x_1424_ = lean_unsigned_to_nat(0u);
v___x_1425_ = l_Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0(v_lctx_1423_, v___x_1424_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1434_; 
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1434_ == 0)
{
lean_object* v_unused_1435_; 
v_unused_1435_ = lean_ctor_get(v___x_1425_, 0);
lean_dec(v_unused_1435_);
v___x_1427_ = v___x_1425_;
v_isShared_1428_ = v_isSharedCheck_1434_;
goto v_resetjp_1426_;
}
else
{
lean_dec(v___x_1425_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1434_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
uint8_t v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1432_; 
v___x_1429_ = 0;
v___x_1430_ = lean_box(v___x_1429_);
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 0, v___x_1430_);
v___x_1432_ = v___x_1427_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1430_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
v_a_1436_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___x_1425_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1425_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
if (v_isShared_1439_ == 0)
{
v___x_1441_ = v___x_1438_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1436_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
else
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1451_; 
v_a_1444_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1446_ = v___x_1421_;
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1421_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1449_; 
if (v_isShared_1447_ == 0)
{
v___x_1449_ = v___x_1446_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_a_1444_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
}
else
{
uint8_t v___x_1452_; 
v___x_1452_ = l_Lean_Expr_hasFVar(v_e_1391_);
if (v___x_1452_ == 0)
{
uint8_t v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1453_ = l_Lean_Expr_hasExprMVar(v_e_1391_);
lean_dec_ref(v_e_1391_);
v___x_1454_ = lean_box(v___x_1453_);
v___x_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1454_);
return v___x_1455_;
}
else
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
lean_dec_ref(v_e_1391_);
v___x_1456_ = lean_box(v___x_1452_);
v___x_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1456_);
return v___x_1457_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___lam__0___boxed(lean_object* v_e_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___lam__0(v_e_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___y_1459_);
return v_res_1465_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___redArg(lean_object* v_a_1466_, lean_object* v_x_1467_){
_start:
{
if (lean_obj_tag(v_x_1467_) == 0)
{
uint8_t v___x_1468_; 
v___x_1468_ = 0;
return v___x_1468_;
}
else
{
lean_object* v_key_1469_; lean_object* v_tail_1470_; uint8_t v___x_1471_; 
v_key_1469_ = lean_ctor_get(v_x_1467_, 0);
v_tail_1470_ = lean_ctor_get(v_x_1467_, 2);
v___x_1471_ = lean_expr_eqv(v_key_1469_, v_a_1466_);
if (v___x_1471_ == 0)
{
v_x_1467_ = v_tail_1470_;
goto _start;
}
else
{
return v___x_1471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_a_1473_, lean_object* v_x_1474_){
_start:
{
uint8_t v_res_1475_; lean_object* v_r_1476_; 
v_res_1475_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___redArg(v_a_1473_, v_x_1474_);
lean_dec(v_x_1474_);
lean_dec_ref(v_a_1473_);
v_r_1476_ = lean_box(v_res_1475_);
return v_r_1476_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13_spec__14___redArg(lean_object* v_x_1477_, lean_object* v_x_1478_){
_start:
{
if (lean_obj_tag(v_x_1478_) == 0)
{
return v_x_1477_;
}
else
{
lean_object* v_key_1479_; lean_object* v_value_1480_; lean_object* v_tail_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1504_; 
v_key_1479_ = lean_ctor_get(v_x_1478_, 0);
v_value_1480_ = lean_ctor_get(v_x_1478_, 1);
v_tail_1481_ = lean_ctor_get(v_x_1478_, 2);
v_isSharedCheck_1504_ = !lean_is_exclusive(v_x_1478_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1483_ = v_x_1478_;
v_isShared_1484_ = v_isSharedCheck_1504_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_tail_1481_);
lean_inc(v_value_1480_);
lean_inc(v_key_1479_);
lean_dec(v_x_1478_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1504_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1485_; uint64_t v___x_1486_; uint64_t v___x_1487_; uint64_t v___x_1488_; uint64_t v_fold_1489_; uint64_t v___x_1490_; uint64_t v___x_1491_; uint64_t v___x_1492_; size_t v___x_1493_; size_t v___x_1494_; size_t v___x_1495_; size_t v___x_1496_; size_t v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1500_; 
v___x_1485_ = lean_array_get_size(v_x_1477_);
v___x_1486_ = l_Lean_Expr_hash(v_key_1479_);
v___x_1487_ = 32ULL;
v___x_1488_ = lean_uint64_shift_right(v___x_1486_, v___x_1487_);
v_fold_1489_ = lean_uint64_xor(v___x_1486_, v___x_1488_);
v___x_1490_ = 16ULL;
v___x_1491_ = lean_uint64_shift_right(v_fold_1489_, v___x_1490_);
v___x_1492_ = lean_uint64_xor(v_fold_1489_, v___x_1491_);
v___x_1493_ = lean_uint64_to_usize(v___x_1492_);
v___x_1494_ = lean_usize_of_nat(v___x_1485_);
v___x_1495_ = ((size_t)1ULL);
v___x_1496_ = lean_usize_sub(v___x_1494_, v___x_1495_);
v___x_1497_ = lean_usize_land(v___x_1493_, v___x_1496_);
v___x_1498_ = lean_array_uget_borrowed(v_x_1477_, v___x_1497_);
lean_inc(v___x_1498_);
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 2, v___x_1498_);
v___x_1500_ = v___x_1483_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_key_1479_);
lean_ctor_set(v_reuseFailAlloc_1503_, 1, v_value_1480_);
lean_ctor_set(v_reuseFailAlloc_1503_, 2, v___x_1498_);
v___x_1500_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
lean_object* v___x_1501_; 
v___x_1501_ = lean_array_uset(v_x_1477_, v___x_1497_, v___x_1500_);
v_x_1477_ = v___x_1501_;
v_x_1478_ = v_tail_1481_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13___redArg(lean_object* v_i_1505_, lean_object* v_source_1506_, lean_object* v_target_1507_){
_start:
{
lean_object* v___x_1508_; uint8_t v___x_1509_; 
v___x_1508_ = lean_array_get_size(v_source_1506_);
v___x_1509_ = lean_nat_dec_lt(v_i_1505_, v___x_1508_);
if (v___x_1509_ == 0)
{
lean_dec_ref(v_source_1506_);
lean_dec(v_i_1505_);
return v_target_1507_;
}
else
{
lean_object* v_es_1510_; lean_object* v___x_1511_; lean_object* v_source_1512_; lean_object* v_target_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v_es_1510_ = lean_array_fget(v_source_1506_, v_i_1505_);
v___x_1511_ = lean_box(0);
v_source_1512_ = lean_array_fset(v_source_1506_, v_i_1505_, v___x_1511_);
v_target_1513_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13_spec__14___redArg(v_target_1507_, v_es_1510_);
v___x_1514_ = lean_unsigned_to_nat(1u);
v___x_1515_ = lean_nat_add(v_i_1505_, v___x_1514_);
lean_dec(v_i_1505_);
v_i_1505_ = v___x_1515_;
v_source_1506_ = v_source_1512_;
v_target_1507_ = v_target_1513_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9___redArg(lean_object* v_data_1517_){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v_nbuckets_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1518_ = lean_array_get_size(v_data_1517_);
v___x_1519_ = lean_unsigned_to_nat(2u);
v_nbuckets_1520_ = lean_nat_mul(v___x_1518_, v___x_1519_);
v___x_1521_ = lean_unsigned_to_nat(0u);
v___x_1522_ = lean_box(0);
v___x_1523_ = lean_mk_array(v_nbuckets_1520_, v___x_1522_);
v___x_1524_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13___redArg(v___x_1521_, v_data_1517_, v___x_1523_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__10___redArg(lean_object* v_a_1525_, lean_object* v_b_1526_, lean_object* v_x_1527_){
_start:
{
if (lean_obj_tag(v_x_1527_) == 0)
{
lean_dec(v_b_1526_);
lean_dec_ref(v_a_1525_);
return v_x_1527_;
}
else
{
lean_object* v_key_1528_; lean_object* v_value_1529_; lean_object* v_tail_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1542_; 
v_key_1528_ = lean_ctor_get(v_x_1527_, 0);
v_value_1529_ = lean_ctor_get(v_x_1527_, 1);
v_tail_1530_ = lean_ctor_get(v_x_1527_, 2);
v_isSharedCheck_1542_ = !lean_is_exclusive(v_x_1527_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1532_ = v_x_1527_;
v_isShared_1533_ = v_isSharedCheck_1542_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_tail_1530_);
lean_inc(v_value_1529_);
lean_inc(v_key_1528_);
lean_dec(v_x_1527_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1542_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
uint8_t v___x_1534_; 
v___x_1534_ = lean_expr_eqv(v_key_1528_, v_a_1525_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; lean_object* v___x_1537_; 
v___x_1535_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__10___redArg(v_a_1525_, v_b_1526_, v_tail_1530_);
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 2, v___x_1535_);
v___x_1537_ = v___x_1532_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_key_1528_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_value_1529_);
lean_ctor_set(v_reuseFailAlloc_1538_, 2, v___x_1535_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
else
{
lean_object* v___x_1540_; 
lean_dec(v_value_1529_);
lean_dec(v_key_1528_);
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 1, v_b_1526_);
lean_ctor_set(v___x_1532_, 0, v_a_1525_);
v___x_1540_ = v___x_1532_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_a_1525_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v_b_1526_);
lean_ctor_set(v_reuseFailAlloc_1541_, 2, v_tail_1530_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3___redArg(lean_object* v_m_1543_, lean_object* v_a_1544_, lean_object* v_b_1545_){
_start:
{
lean_object* v_size_1546_; lean_object* v_buckets_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1590_; 
v_size_1546_ = lean_ctor_get(v_m_1543_, 0);
v_buckets_1547_ = lean_ctor_get(v_m_1543_, 1);
v_isSharedCheck_1590_ = !lean_is_exclusive(v_m_1543_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1549_ = v_m_1543_;
v_isShared_1550_ = v_isSharedCheck_1590_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_buckets_1547_);
lean_inc(v_size_1546_);
lean_dec(v_m_1543_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1590_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1551_; uint64_t v___x_1552_; uint64_t v___x_1553_; uint64_t v___x_1554_; uint64_t v_fold_1555_; uint64_t v___x_1556_; uint64_t v___x_1557_; uint64_t v___x_1558_; size_t v___x_1559_; size_t v___x_1560_; size_t v___x_1561_; size_t v___x_1562_; size_t v___x_1563_; lean_object* v_bkt_1564_; uint8_t v___x_1565_; 
v___x_1551_ = lean_array_get_size(v_buckets_1547_);
v___x_1552_ = l_Lean_Expr_hash(v_a_1544_);
v___x_1553_ = 32ULL;
v___x_1554_ = lean_uint64_shift_right(v___x_1552_, v___x_1553_);
v_fold_1555_ = lean_uint64_xor(v___x_1552_, v___x_1554_);
v___x_1556_ = 16ULL;
v___x_1557_ = lean_uint64_shift_right(v_fold_1555_, v___x_1556_);
v___x_1558_ = lean_uint64_xor(v_fold_1555_, v___x_1557_);
v___x_1559_ = lean_uint64_to_usize(v___x_1558_);
v___x_1560_ = lean_usize_of_nat(v___x_1551_);
v___x_1561_ = ((size_t)1ULL);
v___x_1562_ = lean_usize_sub(v___x_1560_, v___x_1561_);
v___x_1563_ = lean_usize_land(v___x_1559_, v___x_1562_);
v_bkt_1564_ = lean_array_uget_borrowed(v_buckets_1547_, v___x_1563_);
v___x_1565_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___redArg(v_a_1544_, v_bkt_1564_);
if (v___x_1565_ == 0)
{
lean_object* v___x_1566_; lean_object* v_size_x27_1567_; lean_object* v___x_1568_; lean_object* v_buckets_x27_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; uint8_t v___x_1575_; 
v___x_1566_ = lean_unsigned_to_nat(1u);
v_size_x27_1567_ = lean_nat_add(v_size_1546_, v___x_1566_);
lean_dec(v_size_1546_);
lean_inc(v_bkt_1564_);
v___x_1568_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1568_, 0, v_a_1544_);
lean_ctor_set(v___x_1568_, 1, v_b_1545_);
lean_ctor_set(v___x_1568_, 2, v_bkt_1564_);
v_buckets_x27_1569_ = lean_array_uset(v_buckets_1547_, v___x_1563_, v___x_1568_);
v___x_1570_ = lean_unsigned_to_nat(4u);
v___x_1571_ = lean_nat_mul(v_size_x27_1567_, v___x_1570_);
v___x_1572_ = lean_unsigned_to_nat(3u);
v___x_1573_ = lean_nat_div(v___x_1571_, v___x_1572_);
lean_dec(v___x_1571_);
v___x_1574_ = lean_array_get_size(v_buckets_x27_1569_);
v___x_1575_ = lean_nat_dec_le(v___x_1573_, v___x_1574_);
lean_dec(v___x_1573_);
if (v___x_1575_ == 0)
{
lean_object* v_val_1576_; lean_object* v___x_1578_; 
v_val_1576_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9___redArg(v_buckets_x27_1569_);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 1, v_val_1576_);
lean_ctor_set(v___x_1549_, 0, v_size_x27_1567_);
v___x_1578_ = v___x_1549_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_size_x27_1567_);
lean_ctor_set(v_reuseFailAlloc_1579_, 1, v_val_1576_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
else
{
lean_object* v___x_1581_; 
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 1, v_buckets_x27_1569_);
lean_ctor_set(v___x_1549_, 0, v_size_x27_1567_);
v___x_1581_ = v___x_1549_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_size_x27_1567_);
lean_ctor_set(v_reuseFailAlloc_1582_, 1, v_buckets_x27_1569_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
else
{
lean_object* v___x_1583_; lean_object* v_buckets_x27_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1588_; 
lean_inc(v_bkt_1564_);
v___x_1583_ = lean_box(0);
v_buckets_x27_1584_ = lean_array_uset(v_buckets_1547_, v___x_1563_, v___x_1583_);
v___x_1585_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__10___redArg(v_a_1544_, v_b_1545_, v_bkt_1564_);
v___x_1586_ = lean_array_uset(v_buckets_x27_1584_, v___x_1563_, v___x_1585_);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 1, v___x_1586_);
v___x_1588_ = v___x_1549_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_size_1546_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v___x_1586_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___redArg(lean_object* v_a_1591_, lean_object* v_x_1592_){
_start:
{
if (lean_obj_tag(v_x_1592_) == 0)
{
lean_object* v___x_1593_; 
v___x_1593_ = lean_box(0);
return v___x_1593_;
}
else
{
lean_object* v_key_1594_; lean_object* v_value_1595_; lean_object* v_tail_1596_; uint8_t v___x_1597_; 
v_key_1594_ = lean_ctor_get(v_x_1592_, 0);
v_value_1595_ = lean_ctor_get(v_x_1592_, 1);
v_tail_1596_ = lean_ctor_get(v_x_1592_, 2);
v___x_1597_ = lean_expr_eqv(v_key_1594_, v_a_1591_);
if (v___x_1597_ == 0)
{
v_x_1592_ = v_tail_1596_;
goto _start;
}
else
{
lean_object* v___x_1599_; 
lean_inc(v_value_1595_);
v___x_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1599_, 0, v_value_1595_);
return v___x_1599_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_a_1600_, lean_object* v_x_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___redArg(v_a_1600_, v_x_1601_);
lean_dec(v_x_1601_);
lean_dec_ref(v_a_1600_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___redArg(lean_object* v_m_1603_, lean_object* v_a_1604_){
_start:
{
lean_object* v_buckets_1605_; lean_object* v___x_1606_; uint64_t v___x_1607_; uint64_t v___x_1608_; uint64_t v___x_1609_; uint64_t v_fold_1610_; uint64_t v___x_1611_; uint64_t v___x_1612_; uint64_t v___x_1613_; size_t v___x_1614_; size_t v___x_1615_; size_t v___x_1616_; size_t v___x_1617_; size_t v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v_buckets_1605_ = lean_ctor_get(v_m_1603_, 1);
v___x_1606_ = lean_array_get_size(v_buckets_1605_);
v___x_1607_ = l_Lean_Expr_hash(v_a_1604_);
v___x_1608_ = 32ULL;
v___x_1609_ = lean_uint64_shift_right(v___x_1607_, v___x_1608_);
v_fold_1610_ = lean_uint64_xor(v___x_1607_, v___x_1609_);
v___x_1611_ = 16ULL;
v___x_1612_ = lean_uint64_shift_right(v_fold_1610_, v___x_1611_);
v___x_1613_ = lean_uint64_xor(v_fold_1610_, v___x_1612_);
v___x_1614_ = lean_uint64_to_usize(v___x_1613_);
v___x_1615_ = lean_usize_of_nat(v___x_1606_);
v___x_1616_ = ((size_t)1ULL);
v___x_1617_ = lean_usize_sub(v___x_1615_, v___x_1616_);
v___x_1618_ = lean_usize_land(v___x_1614_, v___x_1617_);
v___x_1619_ = lean_array_uget_borrowed(v_buckets_1605_, v___x_1618_);
v___x_1620_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___redArg(v_a_1604_, v___x_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___redArg___boxed(lean_object* v_m_1621_, lean_object* v_a_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___redArg(v_m_1621_, v_a_1622_);
lean_dec_ref(v_a_1622_);
lean_dec_ref(v_m_1621_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(lean_object* v_g_1624_, lean_object* v_e_1625_, lean_object* v_a_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v_a_1634_; lean_object* v___y_1640_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1642_ = lean_st_ref_get(v_a_1626_);
v___x_1643_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___redArg(v___x_1642_, v_e_1625_);
lean_dec(v___x_1642_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v___x_1644_; 
lean_inc_ref(v_g_1624_);
lean_inc(v___y_1631_);
lean_inc_ref(v___y_1630_);
lean_inc(v___y_1629_);
lean_inc_ref(v___y_1628_);
lean_inc(v___y_1627_);
lean_inc_ref(v_e_1625_);
v___x_1644_ = lean_apply_7(v_g_1624_, v_e_1625_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, lean_box(0));
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v_a_1645_; lean_object* v_d_1647_; lean_object* v_b_1648_; lean_object* v___y_1649_; uint8_t v___x_1652_; 
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
lean_inc(v_a_1645_);
lean_dec_ref_known(v___x_1644_, 1);
v___x_1652_ = lean_unbox(v_a_1645_);
lean_dec(v_a_1645_);
if (v___x_1652_ == 0)
{
lean_object* v___x_1653_; 
lean_dec_ref(v_g_1624_);
v___x_1653_ = lean_box(0);
v_a_1634_ = v___x_1653_;
goto v___jp_1633_;
}
else
{
switch(lean_obj_tag(v_e_1625_))
{
case 7:
{
lean_object* v_binderType_1654_; lean_object* v_body_1655_; 
v_binderType_1654_ = lean_ctor_get(v_e_1625_, 1);
v_body_1655_ = lean_ctor_get(v_e_1625_, 2);
lean_inc_ref(v_body_1655_);
lean_inc_ref(v_binderType_1654_);
v_d_1647_ = v_binderType_1654_;
v_b_1648_ = v_body_1655_;
v___y_1649_ = v_a_1626_;
goto v___jp_1646_;
}
case 6:
{
lean_object* v_binderType_1656_; lean_object* v_body_1657_; 
v_binderType_1656_ = lean_ctor_get(v_e_1625_, 1);
v_body_1657_ = lean_ctor_get(v_e_1625_, 2);
lean_inc_ref(v_body_1657_);
lean_inc_ref(v_binderType_1656_);
v_d_1647_ = v_binderType_1656_;
v_b_1648_ = v_body_1657_;
v___y_1649_ = v_a_1626_;
goto v___jp_1646_;
}
case 8:
{
lean_object* v_type_1658_; lean_object* v_value_1659_; lean_object* v_body_1660_; lean_object* v___x_1661_; 
v_type_1658_ = lean_ctor_get(v_e_1625_, 1);
v_value_1659_ = lean_ctor_get(v_e_1625_, 2);
v_body_1660_ = lean_ctor_get(v_e_1625_, 3);
lean_inc_ref(v_type_1658_);
lean_inc_ref(v_g_1624_);
v___x_1661_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1624_, v_type_1658_, v_a_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v___x_1662_; 
lean_dec_ref_known(v___x_1661_, 1);
lean_inc_ref(v_value_1659_);
lean_inc_ref(v_g_1624_);
v___x_1662_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1624_, v_value_1659_, v_a_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v___x_1663_; 
lean_dec_ref_known(v___x_1662_, 1);
lean_inc_ref(v_body_1660_);
v___x_1663_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1624_, v_body_1660_, v_a_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
v___y_1640_ = v___x_1663_;
goto v___jp_1639_;
}
else
{
lean_dec_ref(v_g_1624_);
v___y_1640_ = v___x_1662_;
goto v___jp_1639_;
}
}
else
{
lean_dec_ref(v_g_1624_);
v___y_1640_ = v___x_1661_;
goto v___jp_1639_;
}
}
case 5:
{
lean_object* v_fn_1664_; lean_object* v_arg_1665_; lean_object* v___x_1666_; 
v_fn_1664_ = lean_ctor_get(v_e_1625_, 0);
v_arg_1665_ = lean_ctor_get(v_e_1625_, 1);
lean_inc_ref(v_fn_1664_);
lean_inc_ref(v_g_1624_);
v___x_1666_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1624_, v_fn_1664_, v_a_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v___x_1667_; 
lean_dec_ref_known(v___x_1666_, 1);
lean_inc_ref(v_arg_1665_);
v___x_1667_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1624_, v_arg_1665_, v_a_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
v___y_1640_ = v___x_1667_;
goto v___jp_1639_;
}
else
{
lean_dec_ref(v_g_1624_);
v___y_1640_ = v___x_1666_;
goto v___jp_1639_;
}
}
case 10:
{
lean_object* v_expr_1668_; lean_object* v___x_1669_; 
v_expr_1668_ = lean_ctor_get(v_e_1625_, 1);
lean_inc_ref(v_expr_1668_);
v___x_1669_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1624_, v_expr_1668_, v_a_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
v___y_1640_ = v___x_1669_;
goto v___jp_1639_;
}
case 11:
{
lean_object* v_struct_1670_; lean_object* v___x_1671_; 
v_struct_1670_ = lean_ctor_get(v_e_1625_, 2);
lean_inc_ref(v_struct_1670_);
v___x_1671_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1624_, v_struct_1670_, v_a_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
v___y_1640_ = v___x_1671_;
goto v___jp_1639_;
}
default: 
{
lean_object* v___x_1672_; 
lean_dec_ref(v_g_1624_);
v___x_1672_ = lean_box(0);
v_a_1634_ = v___x_1672_;
goto v___jp_1633_;
}
}
}
v___jp_1646_:
{
lean_object* v___x_1650_; 
lean_inc_ref(v_g_1624_);
v___x_1650_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1624_, v_d_1647_, v___y_1649_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v___x_1651_; 
lean_dec_ref_known(v___x_1650_, 1);
v___x_1651_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1624_, v_b_1648_, v___y_1649_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
v___y_1640_ = v___x_1651_;
goto v___jp_1639_;
}
else
{
lean_dec_ref(v_b_1648_);
lean_dec_ref(v_g_1624_);
v___y_1640_ = v___x_1650_;
goto v___jp_1639_;
}
}
}
else
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1680_; 
lean_dec_ref(v_e_1625_);
lean_dec_ref(v_g_1624_);
v_a_1673_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1675_ = v___x_1644_;
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1644_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1676_ == 0)
{
v___x_1678_ = v___x_1675_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1673_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
}
else
{
lean_object* v_val_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
lean_dec_ref(v_e_1625_);
lean_dec_ref(v_g_1624_);
v_val_1681_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1683_ = v___x_1643_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_val_1681_);
lean_dec(v___x_1643_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1684_ == 0)
{
lean_ctor_set_tag(v___x_1683_, 0);
v___x_1686_ = v___x_1683_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_val_1681_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
v___jp_1633_:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1635_ = lean_st_ref_take(v_a_1626_);
v___x_1636_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3___redArg(v___x_1635_, v_e_1625_, v_a_1634_);
v___x_1637_ = lean_st_ref_set(v_a_1626_, v___x_1636_);
v___x_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1638_, 0, v_a_1634_);
return v___x_1638_;
}
v___jp_1639_:
{
if (lean_obj_tag(v___y_1640_) == 0)
{
lean_object* v_a_1641_; 
v_a_1641_ = lean_ctor_get(v___y_1640_, 0);
lean_inc(v_a_1641_);
lean_dec_ref_known(v___y_1640_, 1);
v_a_1634_ = v_a_1641_;
goto v___jp_1633_;
}
else
{
lean_dec_ref(v_e_1625_);
return v___y_1640_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1___boxed(lean_object* v_g_1689_, lean_object* v_e_1690_, lean_object* v_a_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1689_, v_e_1690_, v_a_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec(v_a_1691_);
return v_res_1698_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__0(void){
_start:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1699_ = lean_box(0);
v___x_1700_ = lean_unsigned_to_nat(16u);
v___x_1701_ = lean_mk_array(v___x_1700_, v___x_1699_);
return v___x_1701_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__1(void){
_start:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1702_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__0, &l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__0_once, _init_l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__0);
v___x_1703_ = lean_unsigned_to_nat(0u);
v___x_1704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1703_);
lean_ctor_set(v___x_1704_, 1, v___x_1702_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar(lean_object* v_e_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_){
_start:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___f_1715_; lean_object* v___x_1716_; 
v___x_1713_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__1, &l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__1_once, _init_l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__1);
v___x_1714_ = lean_st_mk_ref(v___x_1713_);
v___f_1715_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__2));
v___x_1716_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v___f_1715_, v_e_1706_, v___x_1714_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1725_; 
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1719_ = v___x_1716_;
v_isShared_1720_ = v_isSharedCheck_1725_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1716_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1725_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1721_; lean_object* v___x_1723_; 
v___x_1721_ = lean_st_ref_get(v___x_1714_);
lean_dec(v___x_1714_);
lean_dec(v___x_1721_);
if (v_isShared_1720_ == 0)
{
v___x_1723_ = v___x_1719_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1717_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
else
{
lean_dec(v___x_1714_);
return v___x_1716_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___boxed(lean_object* v_e_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar(v_e_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_);
lean_dec(v_a_1731_);
lean_dec_ref(v_a_1730_);
lean_dec(v_a_1729_);
lean_dec_ref(v_a_1728_);
lean_dec(v_a_1727_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2(lean_object* v_00_u03b2_1734_, lean_object* v_m_1735_, lean_object* v_a_1736_){
_start:
{
lean_object* v___x_1737_; 
v___x_1737_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___redArg(v_m_1735_, v_a_1736_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1738_, lean_object* v_m_1739_, lean_object* v_a_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2(v_00_u03b2_1738_, v_m_1739_, v_a_1740_);
lean_dec_ref(v_a_1740_);
lean_dec_ref(v_m_1739_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3(lean_object* v_00_u03b2_1742_, lean_object* v_m_1743_, lean_object* v_a_1744_, lean_object* v_b_1745_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3___redArg(v_m_1743_, v_a_1744_, v_b_1745_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_1747_, lean_object* v_a_1748_, lean_object* v_x_1749_){
_start:
{
lean_object* v___x_1750_; 
v___x_1750_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___redArg(v_a_1748_, v_x_1749_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1751_, lean_object* v_a_1752_, lean_object* v_x_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6(v_00_u03b2_1751_, v_a_1752_, v_x_1753_);
lean_dec(v_x_1753_);
lean_dec_ref(v_a_1752_);
return v_res_1754_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_1755_, lean_object* v_a_1756_, lean_object* v_x_1757_){
_start:
{
uint8_t v___x_1758_; 
v___x_1758_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___redArg(v_a_1756_, v_x_1757_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___boxed(lean_object* v_00_u03b2_1759_, lean_object* v_a_1760_, lean_object* v_x_1761_){
_start:
{
uint8_t v_res_1762_; lean_object* v_r_1763_; 
v_res_1762_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8(v_00_u03b2_1759_, v_a_1760_, v_x_1761_);
lean_dec(v_x_1761_);
lean_dec_ref(v_a_1760_);
v_r_1763_ = lean_box(v_res_1762_);
return v_r_1763_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9(lean_object* v_00_u03b2_1764_, lean_object* v_data_1765_){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9___redArg(v_data_1765_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__10(lean_object* v_00_u03b2_1767_, lean_object* v_a_1768_, lean_object* v_b_1769_, lean_object* v_x_1770_){
_start:
{
lean_object* v___x_1771_; 
v___x_1771_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__10___redArg(v_a_1768_, v_b_1769_, v_x_1770_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6(lean_object* v_as_1772_, size_t v_i_1773_, size_t v_stop_1774_, lean_object* v_b_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v___x_1782_; 
v___x_1782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___redArg(v_as_1772_, v_i_1773_, v_stop_1774_, v_b_1775_, v___y_1776_, v___y_1777_, v___y_1779_, v___y_1780_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* v_as_1783_, lean_object* v_i_1784_, lean_object* v_stop_1785_, lean_object* v_b_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
size_t v_i_boxed_1793_; size_t v_stop_boxed_1794_; lean_object* v_res_1795_; 
v_i_boxed_1793_ = lean_unbox_usize(v_i_1784_);
lean_dec(v_i_1784_);
v_stop_boxed_1794_ = lean_unbox_usize(v_stop_1785_);
lean_dec(v_stop_1785_);
v_res_1795_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6(v_as_1783_, v_i_boxed_1793_, v_stop_boxed_1794_, v_b_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v_as_1783_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13(lean_object* v_00_u03b2_1796_, lean_object* v_i_1797_, lean_object* v_source_1798_, lean_object* v_target_1799_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13___redArg(v_i_1797_, v_source_1798_, v_target_1799_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13_spec__14(lean_object* v_00_u03b2_1801_, lean_object* v_x_1802_, lean_object* v_x_1803_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13_spec__14___redArg(v_x_1802_, v_x_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___redArg(lean_object* v_e_1805_, lean_object* v___y_1806_){
_start:
{
uint8_t v___x_1808_; 
v___x_1808_ = l_Lean_Expr_hasMVar(v_e_1805_);
if (v___x_1808_ == 0)
{
lean_object* v___x_1809_; 
v___x_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1809_, 0, v_e_1805_);
return v___x_1809_;
}
else
{
lean_object* v___x_1810_; lean_object* v_mctx_1811_; lean_object* v___x_1812_; lean_object* v_fst_1813_; lean_object* v_snd_1814_; lean_object* v___x_1815_; lean_object* v_cache_1816_; lean_object* v_zetaDeltaFVarIds_1817_; lean_object* v_postponed_1818_; lean_object* v_diag_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1828_; 
v___x_1810_ = lean_st_ref_get(v___y_1806_);
v_mctx_1811_ = lean_ctor_get(v___x_1810_, 0);
lean_inc_ref(v_mctx_1811_);
lean_dec(v___x_1810_);
v___x_1812_ = l_Lean_instantiateMVarsCore(v_mctx_1811_, v_e_1805_);
v_fst_1813_ = lean_ctor_get(v___x_1812_, 0);
lean_inc(v_fst_1813_);
v_snd_1814_ = lean_ctor_get(v___x_1812_, 1);
lean_inc(v_snd_1814_);
lean_dec_ref(v___x_1812_);
v___x_1815_ = lean_st_ref_take(v___y_1806_);
v_cache_1816_ = lean_ctor_get(v___x_1815_, 1);
v_zetaDeltaFVarIds_1817_ = lean_ctor_get(v___x_1815_, 2);
v_postponed_1818_ = lean_ctor_get(v___x_1815_, 3);
v_diag_1819_ = lean_ctor_get(v___x_1815_, 4);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1828_ == 0)
{
lean_object* v_unused_1829_; 
v_unused_1829_ = lean_ctor_get(v___x_1815_, 0);
lean_dec(v_unused_1829_);
v___x_1821_ = v___x_1815_;
v_isShared_1822_ = v_isSharedCheck_1828_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_diag_1819_);
lean_inc(v_postponed_1818_);
lean_inc(v_zetaDeltaFVarIds_1817_);
lean_inc(v_cache_1816_);
lean_dec(v___x_1815_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1828_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1824_; 
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 0, v_snd_1814_);
v___x_1824_ = v___x_1821_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_snd_1814_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v_cache_1816_);
lean_ctor_set(v_reuseFailAlloc_1827_, 2, v_zetaDeltaFVarIds_1817_);
lean_ctor_set(v_reuseFailAlloc_1827_, 3, v_postponed_1818_);
lean_ctor_set(v_reuseFailAlloc_1827_, 4, v_diag_1819_);
v___x_1824_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1825_ = lean_st_ref_set(v___y_1806_, v___x_1824_);
v___x_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1826_, 0, v_fst_1813_);
return v___x_1826_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___redArg___boxed(lean_object* v_e_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___redArg(v_e_1830_, v___y_1831_);
lean_dec(v___y_1831_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0(lean_object* v_e_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
lean_object* v___x_1840_; 
v___x_1840_ = l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___redArg(v_e_1834_, v___y_1836_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___boxed(lean_object* v_e_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0(v_e_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertAfter_x27___lam__0(lean_object* v_type_1848_, lean_object* v_fvarId_1849_, lean_object* v_mvarId_1850_, lean_object* v_userName_1851_, lean_object* v_val_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
lean_object* v___x_1858_; lean_object* v_a_1859_; lean_object* v___x_1860_; 
v___x_1858_ = l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___redArg(v_type_1848_, v___y_1854_);
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
lean_inc(v_a_1859_);
lean_dec_ref(v___x_1858_);
v___x_1860_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1849_, v___y_1853_, v___y_1855_, v___y_1856_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
lean_inc(v_a_1861_);
lean_dec_ref_known(v___x_1860_, 1);
v___x_1862_ = lean_st_mk_ref(v_a_1861_);
lean_inc(v_a_1859_);
v___x_1863_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar(v_a_1859_, v___x_1862_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
lean_dec_ref_known(v___x_1863_, 1);
v___x_1864_ = lean_st_ref_get(v___x_1862_);
lean_dec(v___x_1862_);
v___x_1865_ = l_Lean_LocalDecl_fvarId(v___x_1864_);
lean_dec(v___x_1864_);
v___x_1866_ = l_Lean_MVarId_assertAfter(v_mvarId_1850_, v___x_1865_, v_userName_1851_, v_a_1859_, v_val_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
return v___x_1866_;
}
else
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1874_; 
lean_dec(v___x_1862_);
lean_dec(v_a_1859_);
lean_dec_ref(v_val_1852_);
lean_dec(v_userName_1851_);
lean_dec(v_mvarId_1850_);
v_a_1867_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1869_ = v___x_1863_;
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1863_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1872_; 
if (v_isShared_1870_ == 0)
{
v___x_1872_ = v___x_1869_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_a_1867_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
}
else
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1882_; 
lean_dec(v_a_1859_);
lean_dec_ref(v_val_1852_);
lean_dec(v_userName_1851_);
lean_dec(v_mvarId_1850_);
v_a_1875_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1877_ = v___x_1860_;
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1860_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1880_; 
if (v_isShared_1878_ == 0)
{
v___x_1880_ = v___x_1877_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_a_1875_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertAfter_x27___lam__0___boxed(lean_object* v_type_1883_, lean_object* v_fvarId_1884_, lean_object* v_mvarId_1885_, lean_object* v_userName_1886_, lean_object* v_val_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l_Lean_MVarId_assertAfter_x27___lam__0(v_type_1883_, v_fvarId_1884_, v_mvarId_1885_, v_userName_1886_, v_val_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertAfter_x27(lean_object* v_mvarId_1894_, lean_object* v_fvarId_1895_, lean_object* v_userName_1896_, lean_object* v_type_1897_, lean_object* v_val_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_){
_start:
{
lean_object* v___f_1904_; lean_object* v___x_1905_; 
lean_inc(v_mvarId_1894_);
v___f_1904_ = lean_alloc_closure((void*)(l_Lean_MVarId_assertAfter_x27___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1904_, 0, v_type_1897_);
lean_closure_set(v___f_1904_, 1, v_fvarId_1895_);
lean_closure_set(v___f_1904_, 2, v_mvarId_1894_);
lean_closure_set(v___f_1904_, 3, v_userName_1896_);
lean_closure_set(v___f_1904_, 4, v_val_1898_);
v___x_1905_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(v_mvarId_1894_, v___f_1904_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertAfter_x27___boxed(lean_object* v_mvarId_1906_, lean_object* v_fvarId_1907_, lean_object* v_userName_1908_, lean_object* v_type_1909_, lean_object* v_val_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l_Lean_MVarId_assertAfter_x27(v_mvarId_1906_, v_fvarId_1907_, v_userName_1908_, v_type_1909_, v_val_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
lean_dec(v_a_1914_);
lean_dec_ref(v_a_1913_);
lean_dec(v_a_1912_);
lean_dec_ref(v_a_1911_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg(lean_object* v_mvarId_1917_, lean_object* v_f_1918_, lean_object* v___y_1919_){
_start:
{
lean_object* v___x_1921_; lean_object* v_mctx_1922_; lean_object* v_cache_1923_; lean_object* v_zetaDeltaFVarIds_1924_; lean_object* v_postponed_1925_; lean_object* v_diag_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1937_; 
v___x_1921_ = lean_st_ref_take(v___y_1919_);
v_mctx_1922_ = lean_ctor_get(v___x_1921_, 0);
v_cache_1923_ = lean_ctor_get(v___x_1921_, 1);
v_zetaDeltaFVarIds_1924_ = lean_ctor_get(v___x_1921_, 2);
v_postponed_1925_ = lean_ctor_get(v___x_1921_, 3);
v_diag_1926_ = lean_ctor_get(v___x_1921_, 4);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1928_ = v___x_1921_;
v_isShared_1929_ = v_isSharedCheck_1937_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_diag_1926_);
lean_inc(v_postponed_1925_);
lean_inc(v_zetaDeltaFVarIds_1924_);
lean_inc(v_cache_1923_);
lean_inc(v_mctx_1922_);
lean_dec(v___x_1921_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1937_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1930_; lean_object* v___x_1932_; 
v___x_1930_ = l_Lean_MetavarContext_modifyExprMVarLCtx(v_mctx_1922_, v_mvarId_1917_, v_f_1918_);
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 0, v___x_1930_);
v___x_1932_ = v___x_1928_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v___x_1930_);
lean_ctor_set(v_reuseFailAlloc_1936_, 1, v_cache_1923_);
lean_ctor_set(v_reuseFailAlloc_1936_, 2, v_zetaDeltaFVarIds_1924_);
lean_ctor_set(v_reuseFailAlloc_1936_, 3, v_postponed_1925_);
lean_ctor_set(v_reuseFailAlloc_1936_, 4, v_diag_1926_);
v___x_1932_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1933_ = lean_st_ref_set(v___y_1919_, v___x_1932_);
v___x_1934_ = lean_box(0);
v___x_1935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1934_);
return v___x_1935_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg___boxed(lean_object* v_mvarId_1938_, lean_object* v_f_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg(v_mvarId_1938_, v_f_1939_, v___y_1940_);
lean_dec(v___y_1940_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1(lean_object* v_mvarId_1943_, lean_object* v_f_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg(v_mvarId_1943_, v_f_1944_, v___y_1946_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___boxed(lean_object* v_mvarId_1951_, lean_object* v_f_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1(v_mvarId_1951_, v_f_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg(lean_object* v_upperBound_1959_, lean_object* v_hs_1960_, lean_object* v_fst_1961_, lean_object* v___x_1962_, lean_object* v_a_1963_, lean_object* v_b_1964_){
_start:
{
lean_object* v_a_1966_; uint8_t v___x_1970_; 
v___x_1970_ = lean_nat_dec_lt(v_a_1963_, v_upperBound_1959_);
if (v___x_1970_ == 0)
{
lean_dec(v_a_1963_);
return v_b_1964_;
}
else
{
lean_object* v___x_1971_; uint8_t v_kind_1972_; uint8_t v___x_1977_; uint8_t v___x_1978_; 
v___x_1971_ = lean_array_fget_borrowed(v_hs_1960_, v_a_1963_);
v_kind_1972_ = lean_ctor_get_uint8(v___x_1971_, sizeof(void*)*3 + 1);
v___x_1977_ = 0;
v___x_1978_ = l_Lean_instDecidableEqLocalDeclKind(v_kind_1972_, v___x_1977_);
if (v___x_1978_ == 0)
{
goto v___jp_1973_;
}
else
{
lean_object* v___x_1979_; uint8_t v___x_1980_; 
v___x_1979_ = lean_unsigned_to_nat(0u);
v___x_1980_ = lean_nat_dec_eq(v___x_1962_, v___x_1979_);
if (v___x_1980_ == 0)
{
v_a_1966_ = v_b_1964_;
goto v___jp_1965_;
}
else
{
goto v___jp_1973_;
}
}
v___jp_1973_:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1974_ = lean_box(0);
v___x_1975_ = lean_array_get_borrowed(v___x_1974_, v_fst_1961_, v_a_1963_);
lean_inc(v___x_1975_);
v___x_1976_ = l_Lean_LocalContext_setKind(v_b_1964_, v___x_1975_, v_kind_1972_);
v_a_1966_ = v___x_1976_;
goto v___jp_1965_;
}
}
v___jp_1965_:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1967_ = lean_unsigned_to_nat(1u);
v___x_1968_ = lean_nat_add(v_a_1963_, v___x_1967_);
lean_dec(v_a_1963_);
v_a_1963_ = v___x_1968_;
v_b_1964_ = v_a_1966_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg___boxed(lean_object* v_upperBound_1981_, lean_object* v_hs_1982_, lean_object* v_fst_1983_, lean_object* v___x_1984_, lean_object* v_a_1985_, lean_object* v_b_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg(v_upperBound_1981_, v_hs_1982_, v_fst_1983_, v___x_1984_, v_a_1985_, v_b_1986_);
lean_dec(v___x_1984_);
lean_dec_ref(v_fst_1983_);
lean_dec_ref(v_hs_1982_);
lean_dec(v_upperBound_1981_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___lam__0(lean_object* v___x_1988_, lean_object* v_hs_1989_, lean_object* v_fst_1990_, lean_object* v___x_1991_, lean_object* v_lctx_1992_){
_start:
{
lean_object* v___x_1993_; 
v___x_1993_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg(v___x_1988_, v_hs_1989_, v_fst_1990_, v___x_1988_, v___x_1991_, v_lctx_1992_);
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___lam__0___boxed(lean_object* v___x_1994_, lean_object* v_hs_1995_, lean_object* v_fst_1996_, lean_object* v___x_1997_, lean_object* v_lctx_1998_){
_start:
{
lean_object* v_res_1999_; 
v_res_1999_ = l_Lean_MVarId_assertHypotheses___lam__0(v___x_1994_, v_hs_1995_, v_fst_1996_, v___x_1997_, v_lctx_1998_);
lean_dec_ref(v_fst_1996_);
lean_dec_ref(v_hs_1995_);
lean_dec(v___x_1994_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__3(lean_object* v_as_2000_, size_t v_i_2001_, size_t v_stop_2002_, lean_object* v_b_2003_){
_start:
{
uint8_t v___x_2004_; 
v___x_2004_ = lean_usize_dec_eq(v_i_2001_, v_stop_2002_);
if (v___x_2004_ == 0)
{
size_t v___x_2005_; size_t v___x_2006_; lean_object* v___x_2007_; lean_object* v_userName_2008_; lean_object* v_type_2009_; uint8_t v_binderInfo_2010_; lean_object* v___x_2011_; 
v___x_2005_ = ((size_t)1ULL);
v___x_2006_ = lean_usize_sub(v_i_2001_, v___x_2005_);
v___x_2007_ = lean_array_uget_borrowed(v_as_2000_, v___x_2006_);
v_userName_2008_ = lean_ctor_get(v___x_2007_, 0);
v_type_2009_ = lean_ctor_get(v___x_2007_, 1);
v_binderInfo_2010_ = lean_ctor_get_uint8(v___x_2007_, sizeof(void*)*3);
lean_inc_ref(v_type_2009_);
lean_inc(v_userName_2008_);
v___x_2011_ = l_Lean_Expr_forallE___override(v_userName_2008_, v_type_2009_, v_b_2003_, v_binderInfo_2010_);
v_i_2001_ = v___x_2006_;
v_b_2003_ = v___x_2011_;
goto _start;
}
else
{
return v_b_2003_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__3___boxed(lean_object* v_as_2013_, lean_object* v_i_2014_, lean_object* v_stop_2015_, lean_object* v_b_2016_){
_start:
{
size_t v_i_boxed_2017_; size_t v_stop_boxed_2018_; lean_object* v_res_2019_; 
v_i_boxed_2017_ = lean_unbox_usize(v_i_2014_);
lean_dec(v_i_2014_);
v_stop_boxed_2018_ = lean_unbox_usize(v_stop_2015_);
lean_dec(v_stop_2015_);
v_res_2019_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__3(v_as_2013_, v_i_boxed_2017_, v_stop_boxed_2018_, v_b_2016_);
lean_dec_ref(v_as_2013_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2(lean_object* v_as_2020_, size_t v_i_2021_, size_t v_stop_2022_, lean_object* v_b_2023_){
_start:
{
uint8_t v___x_2024_; 
v___x_2024_ = lean_usize_dec_eq(v_i_2021_, v_stop_2022_);
if (v___x_2024_ == 0)
{
lean_object* v___x_2025_; lean_object* v_value_2026_; lean_object* v___x_2027_; size_t v___x_2028_; size_t v___x_2029_; 
v___x_2025_ = lean_array_uget_borrowed(v_as_2020_, v_i_2021_);
v_value_2026_ = lean_ctor_get(v___x_2025_, 2);
lean_inc_ref(v_value_2026_);
v___x_2027_ = l_Lean_Expr_app___override(v_b_2023_, v_value_2026_);
v___x_2028_ = ((size_t)1ULL);
v___x_2029_ = lean_usize_add(v_i_2021_, v___x_2028_);
v_i_2021_ = v___x_2029_;
v_b_2023_ = v___x_2027_;
goto _start;
}
else
{
return v_b_2023_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2___boxed(lean_object* v_as_2031_, lean_object* v_i_2032_, lean_object* v_stop_2033_, lean_object* v_b_2034_){
_start:
{
size_t v_i_boxed_2035_; size_t v_stop_boxed_2036_; lean_object* v_res_2037_; 
v_i_boxed_2035_ = lean_unbox_usize(v_i_2032_);
lean_dec(v_i_2032_);
v_stop_boxed_2036_ = lean_unbox_usize(v_stop_2033_);
lean_dec(v_stop_2033_);
v_res_2037_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2(v_as_2031_, v_i_boxed_2035_, v_stop_boxed_2036_, v_b_2034_);
lean_dec_ref(v_as_2031_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___lam__1(lean_object* v_mvarId_2038_, lean_object* v___x_2039_, lean_object* v___x_2040_, uint8_t v___x_2041_, lean_object* v_hs_2042_, lean_object* v___x_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
lean_object* v___y_2050_; lean_object* v___y_2051_; lean_object* v___x_2070_; 
lean_inc(v_mvarId_2038_);
v___x_2070_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2038_, v___x_2039_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v___x_2071_; 
lean_dec_ref_known(v___x_2070_, 1);
lean_inc(v_mvarId_2038_);
v___x_2071_ = l_Lean_MVarId_getTag(v_mvarId_2038_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v_a_2072_; lean_object* v___x_2073_; 
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
lean_inc(v_a_2072_);
lean_dec_ref_known(v___x_2071_, 1);
lean_inc(v_mvarId_2038_);
v___x_2073_ = l_Lean_MVarId_getType(v_mvarId_2038_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v_a_2074_; lean_object* v___y_2076_; uint8_t v___x_2095_; 
v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
lean_inc(v_a_2074_);
lean_dec_ref_known(v___x_2073_, 1);
v___x_2095_ = lean_nat_dec_lt(v___x_2043_, v___x_2040_);
if (v___x_2095_ == 0)
{
v___y_2076_ = v_a_2074_;
goto v___jp_2075_;
}
else
{
size_t v___x_2096_; size_t v___x_2097_; lean_object* v___x_2098_; 
v___x_2096_ = lean_usize_of_nat(v___x_2040_);
v___x_2097_ = ((size_t)0ULL);
v___x_2098_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__3(v_hs_2042_, v___x_2096_, v___x_2097_, v_a_2074_);
v___y_2076_ = v___x_2098_;
goto v___jp_2075_;
}
v___jp_2075_:
{
lean_object* v___x_2077_; 
v___x_2077_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_2076_, v_a_2072_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; uint8_t v___x_2079_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_a_2078_);
lean_dec_ref_known(v___x_2077_, 1);
v___x_2079_ = lean_nat_dec_lt(v___x_2043_, v___x_2040_);
if (v___x_2079_ == 0)
{
lean_inc(v_a_2078_);
v___y_2050_ = v_a_2078_;
v___y_2051_ = v_a_2078_;
goto v___jp_2049_;
}
else
{
uint8_t v___x_2080_; 
v___x_2080_ = lean_nat_dec_le(v___x_2040_, v___x_2040_);
if (v___x_2080_ == 0)
{
if (v___x_2079_ == 0)
{
lean_inc(v_a_2078_);
v___y_2050_ = v_a_2078_;
v___y_2051_ = v_a_2078_;
goto v___jp_2049_;
}
else
{
size_t v___x_2081_; size_t v___x_2082_; lean_object* v___x_2083_; 
v___x_2081_ = ((size_t)0ULL);
v___x_2082_ = lean_usize_of_nat(v___x_2040_);
lean_inc(v_a_2078_);
v___x_2083_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2(v_hs_2042_, v___x_2081_, v___x_2082_, v_a_2078_);
v___y_2050_ = v_a_2078_;
v___y_2051_ = v___x_2083_;
goto v___jp_2049_;
}
}
else
{
size_t v___x_2084_; size_t v___x_2085_; lean_object* v___x_2086_; 
v___x_2084_ = ((size_t)0ULL);
v___x_2085_ = lean_usize_of_nat(v___x_2040_);
lean_inc(v_a_2078_);
v___x_2086_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2(v_hs_2042_, v___x_2084_, v___x_2085_, v_a_2078_);
v___y_2050_ = v_a_2078_;
v___y_2051_ = v___x_2086_;
goto v___jp_2049_;
}
}
}
else
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
lean_dec(v___x_2043_);
lean_dec_ref(v_hs_2042_);
lean_dec(v___x_2040_);
lean_dec(v_mvarId_2038_);
v_a_2087_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_2077_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2077_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
}
}
else
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
lean_dec(v_a_2072_);
lean_dec(v___x_2043_);
lean_dec_ref(v_hs_2042_);
lean_dec(v___x_2040_);
lean_dec(v_mvarId_2038_);
v_a_2099_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v___x_2073_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2073_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_a_2099_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
}
else
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2114_; 
lean_dec(v___x_2043_);
lean_dec_ref(v_hs_2042_);
lean_dec(v___x_2040_);
lean_dec(v_mvarId_2038_);
v_a_2107_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___x_2071_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2071_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2110_ == 0)
{
v___x_2112_ = v___x_2109_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_a_2107_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
}
else
{
lean_object* v_a_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2122_; 
lean_dec(v___x_2043_);
lean_dec_ref(v_hs_2042_);
lean_dec(v___x_2040_);
lean_dec(v_mvarId_2038_);
v_a_2115_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2117_ = v___x_2070_;
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v___x_2070_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2120_; 
if (v_isShared_2118_ == 0)
{
v___x_2120_ = v___x_2117_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_a_2115_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
v___jp_2049_:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; uint8_t v___x_2055_; lean_object* v___x_2056_; 
v___x_2052_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(v_mvarId_2038_, v___y_2051_, v___y_2045_);
lean_dec_ref(v___x_2052_);
v___x_2053_ = l_Lean_Expr_mvarId_x21(v___y_2050_);
lean_dec_ref(v___y_2050_);
v___x_2054_ = lean_box(0);
v___x_2055_ = 1;
lean_inc(v___x_2040_);
v___x_2056_ = l_Lean_Meta_introNCore(v___x_2053_, v___x_2040_, v___x_2054_, v___x_2041_, v___x_2055_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v_a_2057_; lean_object* v_fst_2058_; lean_object* v_snd_2059_; lean_object* v___f_2060_; lean_object* v___x_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
v_a_2057_ = lean_ctor_get(v___x_2056_, 0);
lean_inc(v_a_2057_);
lean_dec_ref_known(v___x_2056_, 1);
v_fst_2058_ = lean_ctor_get(v_a_2057_, 0);
v_snd_2059_ = lean_ctor_get(v_a_2057_, 1);
lean_inc(v_fst_2058_);
v___f_2060_ = lean_alloc_closure((void*)(l_Lean_MVarId_assertHypotheses___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2060_, 0, v___x_2040_);
lean_closure_set(v___f_2060_, 1, v_hs_2042_);
lean_closure_set(v___f_2060_, 2, v_fst_2058_);
lean_closure_set(v___f_2060_, 3, v___x_2043_);
lean_inc(v_snd_2059_);
v___x_2061_ = l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg(v_snd_2059_, v___f_2060_, v___y_2045_);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2068_ == 0)
{
lean_object* v_unused_2069_; 
v_unused_2069_ = lean_ctor_get(v___x_2061_, 0);
lean_dec(v_unused_2069_);
v___x_2063_ = v___x_2061_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_dec(v___x_2061_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 0, v_a_2057_);
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_a_2057_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
else
{
lean_dec(v___x_2043_);
lean_dec_ref(v_hs_2042_);
lean_dec(v___x_2040_);
return v___x_2056_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___lam__1___boxed(lean_object* v_mvarId_2123_, lean_object* v___x_2124_, lean_object* v___x_2125_, lean_object* v___x_2126_, lean_object* v_hs_2127_, lean_object* v___x_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_){
_start:
{
uint8_t v___x_3359__boxed_2134_; lean_object* v_res_2135_; 
v___x_3359__boxed_2134_ = lean_unbox(v___x_2126_);
v_res_2135_ = l_Lean_MVarId_assertHypotheses___lam__1(v_mvarId_2123_, v___x_2124_, v___x_2125_, v___x_3359__boxed_2134_, v_hs_2127_, v___x_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses(lean_object* v_mvarId_2141_, lean_object* v_hs_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_){
_start:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; uint8_t v___x_2150_; 
v___x_2148_ = lean_array_get_size(v_hs_2142_);
v___x_2149_ = lean_unsigned_to_nat(0u);
v___x_2150_ = lean_nat_dec_eq(v___x_2148_, v___x_2149_);
if (v___x_2150_ == 0)
{
lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___f_2153_; lean_object* v___x_2154_; 
v___x_2151_ = ((lean_object*)(l_Lean_MVarId_assertHypotheses___closed__1));
v___x_2152_ = lean_box(v___x_2150_);
lean_inc(v_mvarId_2141_);
v___f_2153_ = lean_alloc_closure((void*)(l_Lean_MVarId_assertHypotheses___lam__1___boxed), 11, 6);
lean_closure_set(v___f_2153_, 0, v_mvarId_2141_);
lean_closure_set(v___f_2153_, 1, v___x_2151_);
lean_closure_set(v___f_2153_, 2, v___x_2148_);
lean_closure_set(v___f_2153_, 3, v___x_2152_);
lean_closure_set(v___f_2153_, 4, v_hs_2142_);
lean_closure_set(v___f_2153_, 5, v___x_2149_);
v___x_2154_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(v_mvarId_2141_, v___f_2153_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_);
return v___x_2154_;
}
else
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
lean_dec_ref(v_hs_2142_);
v___x_2155_ = ((lean_object*)(l_Lean_MVarId_assertHypotheses___closed__2));
v___x_2156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2155_);
lean_ctor_set(v___x_2156_, 1, v_mvarId_2141_);
v___x_2157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2156_);
return v___x_2157_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___boxed(lean_object* v_mvarId_2158_, lean_object* v_hs_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_){
_start:
{
lean_object* v_res_2165_; 
v_res_2165_ = l_Lean_MVarId_assertHypotheses(v_mvarId_2158_, v_hs_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_);
lean_dec(v_a_2163_);
lean_dec_ref(v_a_2162_);
lean_dec(v_a_2161_);
lean_dec_ref(v_a_2160_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0(lean_object* v_upperBound_2166_, lean_object* v_hs_2167_, lean_object* v_fst_2168_, lean_object* v___x_2169_, lean_object* v_inst_2170_, lean_object* v_R_2171_, lean_object* v_a_2172_, lean_object* v_b_2173_, lean_object* v_c_2174_){
_start:
{
lean_object* v___x_2175_; 
v___x_2175_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg(v_upperBound_2166_, v_hs_2167_, v_fst_2168_, v___x_2169_, v_a_2172_, v_b_2173_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___boxed(lean_object* v_upperBound_2176_, lean_object* v_hs_2177_, lean_object* v_fst_2178_, lean_object* v___x_2179_, lean_object* v_inst_2180_, lean_object* v_R_2181_, lean_object* v_a_2182_, lean_object* v_b_2183_, lean_object* v_c_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0(v_upperBound_2176_, v_hs_2177_, v_fst_2178_, v___x_2179_, v_inst_2180_, v_R_2181_, v_a_2182_, v_b_2183_, v_c_2184_);
lean_dec(v___x_2179_);
lean_dec_ref(v_fst_2178_);
lean_dec_ref(v_hs_2177_);
lean_dec(v_upperBound_2176_);
return v_res_2185_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_FVarSubst(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Intro(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Revert(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_InfoTree_Main(uint8_t builtin);
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
res = runtime_initialize_Lean_Elab_InfoTree_Main(builtin);
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
lean_object* initialize_Lean_Elab_InfoTree_Main(uint8_t builtin);
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
res = initialize_Lean_Elab_InfoTree_Main(builtin);
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
