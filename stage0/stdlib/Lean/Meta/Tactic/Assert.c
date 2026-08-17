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
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
size_t lean_usize_shift_left(size_t, size_t);
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
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__0;
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
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(lean_object* v_x_87_, size_t v_x_88_, size_t v_x_89_, lean_object* v_x_90_, lean_object* v_x_91_){
_start:
{
if (lean_obj_tag(v_x_87_) == 0)
{
lean_object* v_es_92_; size_t v___x_93_; size_t v___x_94_; lean_object* v_j_95_; lean_object* v___x_96_; uint8_t v___x_97_; 
v_es_92_ = lean_ctor_get(v_x_87_, 0);
v___x_93_ = ((size_t)31ULL);
v___x_94_ = lean_usize_land(v_x_88_, v___x_93_);
v_j_95_ = lean_usize_to_nat(v___x_94_);
v___x_96_ = lean_array_get_size(v_es_92_);
v___x_97_ = lean_nat_dec_lt(v_j_95_, v___x_96_);
if (v___x_97_ == 0)
{
lean_dec(v_j_95_);
lean_dec(v_x_91_);
lean_dec(v_x_90_);
return v_x_87_;
}
else
{
lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_136_; 
lean_inc_ref(v_es_92_);
v_isSharedCheck_136_ = !lean_is_exclusive(v_x_87_);
if (v_isSharedCheck_136_ == 0)
{
lean_object* v_unused_137_; 
v_unused_137_ = lean_ctor_get(v_x_87_, 0);
lean_dec(v_unused_137_);
v___x_99_ = v_x_87_;
v_isShared_100_ = v_isSharedCheck_136_;
goto v_resetjp_98_;
}
else
{
lean_dec(v_x_87_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_136_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v_v_101_; lean_object* v___x_102_; lean_object* v_xs_x27_103_; lean_object* v___y_105_; 
v_v_101_ = lean_array_fget(v_es_92_, v_j_95_);
v___x_102_ = lean_box(0);
v_xs_x27_103_ = lean_array_fset(v_es_92_, v_j_95_, v___x_102_);
switch(lean_obj_tag(v_v_101_))
{
case 0:
{
lean_object* v_key_110_; lean_object* v_val_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_121_; 
v_key_110_ = lean_ctor_get(v_v_101_, 0);
v_val_111_ = lean_ctor_get(v_v_101_, 1);
v_isSharedCheck_121_ = !lean_is_exclusive(v_v_101_);
if (v_isSharedCheck_121_ == 0)
{
v___x_113_ = v_v_101_;
v_isShared_114_ = v_isSharedCheck_121_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_val_111_);
lean_inc(v_key_110_);
lean_dec(v_v_101_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_121_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
uint8_t v___x_115_; 
v___x_115_ = l_Lean_instBEqMVarId_beq(v_x_90_, v_key_110_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; lean_object* v___x_117_; 
lean_del_object(v___x_113_);
v___x_116_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_110_, v_val_111_, v_x_90_, v_x_91_);
v___x_117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
v___y_105_ = v___x_117_;
goto v___jp_104_;
}
else
{
lean_object* v___x_119_; 
lean_dec(v_val_111_);
lean_dec(v_key_110_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 1, v_x_91_);
lean_ctor_set(v___x_113_, 0, v_x_90_);
v___x_119_ = v___x_113_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v_x_90_);
lean_ctor_set(v_reuseFailAlloc_120_, 1, v_x_91_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
v___y_105_ = v___x_119_;
goto v___jp_104_;
}
}
}
}
case 1:
{
lean_object* v_node_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_134_; 
v_node_122_ = lean_ctor_get(v_v_101_, 0);
v_isSharedCheck_134_ = !lean_is_exclusive(v_v_101_);
if (v_isSharedCheck_134_ == 0)
{
v___x_124_ = v_v_101_;
v_isShared_125_ = v_isSharedCheck_134_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_node_122_);
lean_dec(v_v_101_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_134_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
size_t v___x_126_; size_t v___x_127_; size_t v___x_128_; size_t v___x_129_; lean_object* v___x_130_; lean_object* v___x_132_; 
v___x_126_ = ((size_t)5ULL);
v___x_127_ = lean_usize_shift_right(v_x_88_, v___x_126_);
v___x_128_ = ((size_t)1ULL);
v___x_129_ = lean_usize_add(v_x_89_, v___x_128_);
v___x_130_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(v_node_122_, v___x_127_, v___x_129_, v_x_90_, v_x_91_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 0, v___x_130_);
v___x_132_ = v___x_124_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_130_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
v___y_105_ = v___x_132_;
goto v___jp_104_;
}
}
}
default: 
{
lean_object* v___x_135_; 
v___x_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_135_, 0, v_x_90_);
lean_ctor_set(v___x_135_, 1, v_x_91_);
v___y_105_ = v___x_135_;
goto v___jp_104_;
}
}
v___jp_104_:
{
lean_object* v___x_106_; lean_object* v___x_108_; 
v___x_106_ = lean_array_fset(v_xs_x27_103_, v_j_95_, v___y_105_);
lean_dec(v_j_95_);
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 0, v___x_106_);
v___x_108_ = v___x_99_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v___x_106_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
return v___x_108_;
}
}
}
}
}
else
{
lean_object* v_ks_138_; lean_object* v_vs_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_159_; 
v_ks_138_ = lean_ctor_get(v_x_87_, 0);
v_vs_139_ = lean_ctor_get(v_x_87_, 1);
v_isSharedCheck_159_ = !lean_is_exclusive(v_x_87_);
if (v_isSharedCheck_159_ == 0)
{
v___x_141_ = v_x_87_;
v_isShared_142_ = v_isSharedCheck_159_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_vs_139_);
lean_inc(v_ks_138_);
lean_dec(v_x_87_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_159_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_144_; 
if (v_isShared_142_ == 0)
{
v___x_144_ = v___x_141_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_ks_138_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v_vs_139_);
v___x_144_ = v_reuseFailAlloc_158_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
lean_object* v_newNode_145_; uint8_t v___y_147_; size_t v___x_153_; uint8_t v___x_154_; 
v_newNode_145_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3___redArg(v___x_144_, v_x_90_, v_x_91_);
v___x_153_ = ((size_t)7ULL);
v___x_154_ = lean_usize_dec_le(v___x_153_, v_x_89_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_155_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_145_);
v___x_156_ = lean_unsigned_to_nat(4u);
v___x_157_ = lean_nat_dec_lt(v___x_155_, v___x_156_);
lean_dec(v___x_155_);
v___y_147_ = v___x_157_;
goto v___jp_146_;
}
else
{
v___y_147_ = v___x_154_;
goto v___jp_146_;
}
v___jp_146_:
{
if (v___y_147_ == 0)
{
lean_object* v_ks_148_; lean_object* v_vs_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v_ks_148_ = lean_ctor_get(v_newNode_145_, 0);
lean_inc_ref(v_ks_148_);
v_vs_149_ = lean_ctor_get(v_newNode_145_, 1);
lean_inc_ref(v_vs_149_);
lean_dec_ref(v_newNode_145_);
v___x_150_ = lean_unsigned_to_nat(0u);
v___x_151_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_152_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg(v_x_89_, v_ks_148_, v_vs_149_, v___x_150_, v___x_151_);
lean_dec_ref(v_vs_149_);
lean_dec_ref(v_ks_148_);
return v___x_152_;
}
else
{
return v_newNode_145_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg(size_t v_depth_160_, lean_object* v_keys_161_, lean_object* v_vals_162_, lean_object* v_i_163_, lean_object* v_entries_164_){
_start:
{
lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_165_ = lean_array_get_size(v_keys_161_);
v___x_166_ = lean_nat_dec_lt(v_i_163_, v___x_165_);
if (v___x_166_ == 0)
{
lean_dec(v_i_163_);
return v_entries_164_;
}
else
{
lean_object* v_k_167_; lean_object* v_v_168_; uint64_t v___x_169_; size_t v_h_170_; size_t v___x_171_; lean_object* v___x_172_; size_t v___x_173_; size_t v___x_174_; size_t v___x_175_; size_t v_h_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v_k_167_ = lean_array_fget_borrowed(v_keys_161_, v_i_163_);
v_v_168_ = lean_array_fget_borrowed(v_vals_162_, v_i_163_);
v___x_169_ = l_Lean_instHashableMVarId_hash(v_k_167_);
v_h_170_ = lean_uint64_to_usize(v___x_169_);
v___x_171_ = ((size_t)5ULL);
v___x_172_ = lean_unsigned_to_nat(1u);
v___x_173_ = ((size_t)1ULL);
v___x_174_ = lean_usize_sub(v_depth_160_, v___x_173_);
v___x_175_ = lean_usize_mul(v___x_171_, v___x_174_);
v_h_176_ = lean_usize_shift_right(v_h_170_, v___x_175_);
v___x_177_ = lean_nat_add(v_i_163_, v___x_172_);
lean_dec(v_i_163_);
lean_inc(v_v_168_);
lean_inc(v_k_167_);
v___x_178_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(v_entries_164_, v_h_176_, v_depth_160_, v_k_167_, v_v_168_);
v_i_163_ = v___x_177_;
v_entries_164_ = v___x_178_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_depth_180_, lean_object* v_keys_181_, lean_object* v_vals_182_, lean_object* v_i_183_, lean_object* v_entries_184_){
_start:
{
size_t v_depth_boxed_185_; lean_object* v_res_186_; 
v_depth_boxed_185_ = lean_unbox_usize(v_depth_180_);
lean_dec(v_depth_180_);
v_res_186_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_185_, v_keys_181_, v_vals_182_, v_i_183_, v_entries_184_);
lean_dec_ref(v_vals_182_);
lean_dec_ref(v_keys_181_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_187_, lean_object* v_x_188_, lean_object* v_x_189_, lean_object* v_x_190_, lean_object* v_x_191_){
_start:
{
size_t v_x_1313__boxed_192_; size_t v_x_1314__boxed_193_; lean_object* v_res_194_; 
v_x_1313__boxed_192_ = lean_unbox_usize(v_x_188_);
lean_dec(v_x_188_);
v_x_1314__boxed_193_ = lean_unbox_usize(v_x_189_);
lean_dec(v_x_189_);
v_res_194_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(v_x_187_, v_x_1313__boxed_192_, v_x_1314__boxed_193_, v_x_190_, v_x_191_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0___redArg(lean_object* v_x_195_, lean_object* v_x_196_, lean_object* v_x_197_){
_start:
{
uint64_t v___x_198_; size_t v___x_199_; size_t v___x_200_; lean_object* v___x_201_; 
v___x_198_ = l_Lean_instHashableMVarId_hash(v_x_196_);
v___x_199_ = lean_uint64_to_usize(v___x_198_);
v___x_200_ = ((size_t)1ULL);
v___x_201_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(v_x_195_, v___x_199_, v___x_200_, v_x_196_, v_x_197_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(lean_object* v_mvarId_202_, lean_object* v_val_203_, lean_object* v___y_204_){
_start:
{
lean_object* v___x_206_; lean_object* v_mctx_207_; lean_object* v_cache_208_; lean_object* v_zetaDeltaFVarIds_209_; lean_object* v_postponed_210_; lean_object* v_diag_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_240_; 
v___x_206_ = lean_st_ref_take(v___y_204_);
v_mctx_207_ = lean_ctor_get(v___x_206_, 0);
v_cache_208_ = lean_ctor_get(v___x_206_, 1);
v_zetaDeltaFVarIds_209_ = lean_ctor_get(v___x_206_, 2);
v_postponed_210_ = lean_ctor_get(v___x_206_, 3);
v_diag_211_ = lean_ctor_get(v___x_206_, 4);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_240_ == 0)
{
v___x_213_ = v___x_206_;
v_isShared_214_ = v_isSharedCheck_240_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_diag_211_);
lean_inc(v_postponed_210_);
lean_inc(v_zetaDeltaFVarIds_209_);
lean_inc(v_cache_208_);
lean_inc(v_mctx_207_);
lean_dec(v___x_206_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_240_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v_depth_215_; lean_object* v_levelAssignDepth_216_; lean_object* v_lmvarCounter_217_; lean_object* v_mvarCounter_218_; lean_object* v_lDecls_219_; lean_object* v_decls_220_; lean_object* v_userNames_221_; lean_object* v_lAssignment_222_; lean_object* v_eAssignment_223_; lean_object* v_dAssignment_224_; lean_object* v_instanceTypedMVars_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_239_; 
v_depth_215_ = lean_ctor_get(v_mctx_207_, 0);
v_levelAssignDepth_216_ = lean_ctor_get(v_mctx_207_, 1);
v_lmvarCounter_217_ = lean_ctor_get(v_mctx_207_, 2);
v_mvarCounter_218_ = lean_ctor_get(v_mctx_207_, 3);
v_lDecls_219_ = lean_ctor_get(v_mctx_207_, 4);
v_decls_220_ = lean_ctor_get(v_mctx_207_, 5);
v_userNames_221_ = lean_ctor_get(v_mctx_207_, 6);
v_lAssignment_222_ = lean_ctor_get(v_mctx_207_, 7);
v_eAssignment_223_ = lean_ctor_get(v_mctx_207_, 8);
v_dAssignment_224_ = lean_ctor_get(v_mctx_207_, 9);
v_instanceTypedMVars_225_ = lean_ctor_get(v_mctx_207_, 10);
v_isSharedCheck_239_ = !lean_is_exclusive(v_mctx_207_);
if (v_isSharedCheck_239_ == 0)
{
v___x_227_ = v_mctx_207_;
v_isShared_228_ = v_isSharedCheck_239_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_instanceTypedMVars_225_);
lean_inc(v_dAssignment_224_);
lean_inc(v_eAssignment_223_);
lean_inc(v_lAssignment_222_);
lean_inc(v_userNames_221_);
lean_inc(v_decls_220_);
lean_inc(v_lDecls_219_);
lean_inc(v_mvarCounter_218_);
lean_inc(v_lmvarCounter_217_);
lean_inc(v_levelAssignDepth_216_);
lean_inc(v_depth_215_);
lean_dec(v_mctx_207_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_239_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_229_; lean_object* v___x_231_; 
v___x_229_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0___redArg(v_eAssignment_223_, v_mvarId_202_, v_val_203_);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 8, v___x_229_);
v___x_231_ = v___x_227_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_depth_215_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v_levelAssignDepth_216_);
lean_ctor_set(v_reuseFailAlloc_238_, 2, v_lmvarCounter_217_);
lean_ctor_set(v_reuseFailAlloc_238_, 3, v_mvarCounter_218_);
lean_ctor_set(v_reuseFailAlloc_238_, 4, v_lDecls_219_);
lean_ctor_set(v_reuseFailAlloc_238_, 5, v_decls_220_);
lean_ctor_set(v_reuseFailAlloc_238_, 6, v_userNames_221_);
lean_ctor_set(v_reuseFailAlloc_238_, 7, v_lAssignment_222_);
lean_ctor_set(v_reuseFailAlloc_238_, 8, v___x_229_);
lean_ctor_set(v_reuseFailAlloc_238_, 9, v_dAssignment_224_);
lean_ctor_set(v_reuseFailAlloc_238_, 10, v_instanceTypedMVars_225_);
v___x_231_ = v_reuseFailAlloc_238_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
lean_object* v___x_233_; 
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 0, v___x_231_);
v___x_233_ = v___x_213_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_231_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v_cache_208_);
lean_ctor_set(v_reuseFailAlloc_237_, 2, v_zetaDeltaFVarIds_209_);
lean_ctor_set(v_reuseFailAlloc_237_, 3, v_postponed_210_);
lean_ctor_set(v_reuseFailAlloc_237_, 4, v_diag_211_);
v___x_233_ = v_reuseFailAlloc_237_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_234_ = lean_st_ref_put(v___y_204_, v___x_233_);
v___x_235_ = lean_box(0);
v___x_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
return v___x_236_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg___boxed(lean_object* v_mvarId_241_, lean_object* v_val_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(v_mvarId_241_, v_val_242_, v___y_243_);
lean_dec(v___y_243_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assert___lam__0(lean_object* v_mvarId_246_, lean_object* v___x_247_, lean_object* v_name_248_, lean_object* v_type_249_, lean_object* v_val_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v___x_256_; 
lean_inc(v_mvarId_246_);
v___x_256_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_246_, v___x_247_, v___y_251_, v___y_252_, v___y_253_, v___y_254_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v___x_257_; 
lean_dec_ref_known(v___x_256_, 1);
lean_inc(v_mvarId_246_);
v___x_257_ = l_Lean_MVarId_getTag(v_mvarId_246_, v___y_251_, v___y_252_, v___y_253_, v___y_254_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v_a_258_; lean_object* v___x_259_; 
v_a_258_ = lean_ctor_get(v___x_257_, 0);
lean_inc(v_a_258_);
lean_dec_ref_known(v___x_257_, 1);
lean_inc(v_mvarId_246_);
v___x_259_ = l_Lean_MVarId_getType(v_mvarId_246_, v___y_251_, v___y_252_, v___y_253_, v___y_254_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_object* v_a_260_; uint8_t v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v_a_260_ = lean_ctor_get(v___x_259_, 0);
lean_inc(v_a_260_);
lean_dec_ref_known(v___x_259_, 1);
v___x_261_ = 0;
v___x_262_ = l_Lean_mkForall(v_name_248_, v___x_261_, v_type_249_, v_a_260_);
v___x_263_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_262_, v_a_258_, v___y_251_, v___y_252_, v___y_253_, v___y_254_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v_a_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_274_; 
v_a_264_ = lean_ctor_get(v___x_263_, 0);
lean_inc_n(v_a_264_, 2);
lean_dec_ref_known(v___x_263_, 1);
v___x_265_ = l_Lean_Expr_app___override(v_a_264_, v_val_250_);
v___x_266_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(v_mvarId_246_, v___x_265_, v___y_252_);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_274_ == 0)
{
lean_object* v_unused_275_; 
v_unused_275_ = lean_ctor_get(v___x_266_, 0);
lean_dec(v_unused_275_);
v___x_268_ = v___x_266_;
v_isShared_269_ = v_isSharedCheck_274_;
goto v_resetjp_267_;
}
else
{
lean_dec(v___x_266_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_274_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_270_; lean_object* v___x_272_; 
v___x_270_ = l_Lean_Expr_mvarId_x21(v_a_264_);
lean_dec(v_a_264_);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 0, v___x_270_);
v___x_272_ = v___x_268_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v___x_270_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
else
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_283_; 
lean_dec_ref(v_val_250_);
lean_dec(v_mvarId_246_);
v_a_276_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_283_ == 0)
{
v___x_278_ = v___x_263_;
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_263_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_281_; 
if (v_isShared_279_ == 0)
{
v___x_281_ = v___x_278_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_276_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
else
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_291_; 
lean_dec(v_a_258_);
lean_dec_ref(v_val_250_);
lean_dec_ref(v_type_249_);
lean_dec(v_name_248_);
lean_dec(v_mvarId_246_);
v_a_284_ = lean_ctor_get(v___x_259_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_291_ == 0)
{
v___x_286_ = v___x_259_;
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___x_259_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_289_; 
if (v_isShared_287_ == 0)
{
v___x_289_ = v___x_286_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_a_284_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
}
else
{
lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_299_; 
lean_dec_ref(v_val_250_);
lean_dec_ref(v_type_249_);
lean_dec(v_name_248_);
lean_dec(v_mvarId_246_);
v_a_292_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_299_ == 0)
{
v___x_294_ = v___x_257_;
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v___x_257_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_297_; 
if (v_isShared_295_ == 0)
{
v___x_297_ = v___x_294_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_a_292_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
else
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
lean_dec_ref(v_val_250_);
lean_dec_ref(v_type_249_);
lean_dec(v_name_248_);
lean_dec(v_mvarId_246_);
v_a_300_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_307_ == 0)
{
v___x_302_ = v___x_256_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_256_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_a_300_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assert___lam__0___boxed(lean_object* v_mvarId_308_, lean_object* v___x_309_, lean_object* v_name_310_, lean_object* v_type_311_, lean_object* v_val_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lean_MVarId_assert___lam__0(v_mvarId_308_, v___x_309_, v_name_310_, v_type_311_, v_val_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assert(lean_object* v_mvarId_322_, lean_object* v_name_323_, lean_object* v_type_324_, lean_object* v_val_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_){
_start:
{
lean_object* v___x_331_; lean_object* v___f_332_; lean_object* v___x_333_; 
v___x_331_ = ((lean_object*)(l_Lean_MVarId_assert___closed__1));
lean_inc(v_mvarId_322_);
v___f_332_ = lean_alloc_closure((void*)(l_Lean_MVarId_assert___lam__0___boxed), 10, 5);
lean_closure_set(v___f_332_, 0, v_mvarId_322_);
lean_closure_set(v___f_332_, 1, v___x_331_);
lean_closure_set(v___f_332_, 2, v_name_323_);
lean_closure_set(v___f_332_, 3, v_type_324_);
lean_closure_set(v___f_332_, 4, v_val_325_);
v___x_333_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(v_mvarId_322_, v___f_332_, v_a_326_, v_a_327_, v_a_328_, v_a_329_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assert___boxed(lean_object* v_mvarId_334_, lean_object* v_name_335_, lean_object* v_type_336_, lean_object* v_val_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Lean_MVarId_assert(v_mvarId_334_, v_name_335_, v_type_336_, v_val_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_);
lean_dec(v_a_341_);
lean_dec_ref(v_a_340_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0(lean_object* v_mvarId_344_, lean_object* v_val_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(v_mvarId_344_, v_val_345_, v___y_347_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___boxed(lean_object* v_mvarId_352_, lean_object* v_val_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0(v_mvarId_352_, v_val_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0(lean_object* v_00_u03b2_360_, lean_object* v_x_361_, lean_object* v_x_362_, lean_object* v_x_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0___redArg(v_x_361_, v_x_362_, v_x_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_365_, lean_object* v_x_366_, size_t v_x_367_, size_t v_x_368_, lean_object* v_x_369_, lean_object* v_x_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(v_x_366_, v_x_367_, v_x_368_, v_x_369_, v_x_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_372_, lean_object* v_x_373_, lean_object* v_x_374_, lean_object* v_x_375_, lean_object* v_x_376_, lean_object* v_x_377_){
_start:
{
size_t v_x_1695__boxed_378_; size_t v_x_1696__boxed_379_; lean_object* v_res_380_; 
v_x_1695__boxed_378_ = lean_unbox_usize(v_x_374_);
lean_dec(v_x_374_);
v_x_1696__boxed_379_ = lean_unbox_usize(v_x_375_);
lean_dec(v_x_375_);
v_res_380_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2(v_00_u03b2_372_, v_x_373_, v_x_1695__boxed_378_, v_x_1696__boxed_379_, v_x_376_, v_x_377_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_381_, lean_object* v_n_382_, lean_object* v_k_383_, lean_object* v_v_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3___redArg(v_n_382_, v_k_383_, v_v_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_386_, size_t v_depth_387_, lean_object* v_keys_388_, lean_object* v_vals_389_, lean_object* v_heq_390_, lean_object* v_i_391_, lean_object* v_entries_392_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_387_, v_keys_388_, v_vals_389_, v_i_391_, v_entries_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_394_, lean_object* v_depth_395_, lean_object* v_keys_396_, lean_object* v_vals_397_, lean_object* v_heq_398_, lean_object* v_i_399_, lean_object* v_entries_400_){
_start:
{
size_t v_depth_boxed_401_; lean_object* v_res_402_; 
v_depth_boxed_401_ = lean_unbox_usize(v_depth_395_);
lean_dec(v_depth_395_);
v_res_402_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_394_, v_depth_boxed_401_, v_keys_396_, v_vals_397_, v_heq_398_, v_i_399_, v_entries_400_);
lean_dec_ref(v_vals_397_);
lean_dec_ref(v_keys_396_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_403_, lean_object* v_x_404_, lean_object* v_x_405_, lean_object* v_x_406_, lean_object* v_x_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_404_, v_x_405_, v_x_406_, v_x_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_note(lean_object* v_g_409_, lean_object* v_h_410_, lean_object* v_v_411_, lean_object* v_t_x3f_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
lean_object* v_____do__lift_419_; lean_object* v___y_420_; lean_object* v___y_421_; lean_object* v___y_422_; lean_object* v___y_423_; 
if (lean_obj_tag(v_t_x3f_412_) == 0)
{
lean_object* v___x_436_; 
lean_inc(v_a_416_);
lean_inc_ref(v_a_415_);
lean_inc(v_a_414_);
lean_inc_ref(v_a_413_);
lean_inc_ref(v_v_411_);
v___x_436_ = lean_infer_type(v_v_411_, v_a_413_, v_a_414_, v_a_415_, v_a_416_);
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v_a_437_; 
v_a_437_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_a_437_);
lean_dec_ref_known(v___x_436_, 1);
v_____do__lift_419_ = v_a_437_;
v___y_420_ = v_a_413_;
v___y_421_ = v_a_414_;
v___y_422_ = v_a_415_;
v___y_423_ = v_a_416_;
goto v___jp_418_;
}
else
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_445_; 
lean_dec_ref(v_v_411_);
lean_dec(v_h_410_);
lean_dec(v_g_409_);
v_a_438_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_445_ == 0)
{
v___x_440_ = v___x_436_;
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_436_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_438_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
else
{
lean_object* v_val_446_; 
v_val_446_ = lean_ctor_get(v_t_x3f_412_, 0);
lean_inc(v_val_446_);
lean_dec_ref_known(v_t_x3f_412_, 1);
v_____do__lift_419_ = v_val_446_;
v___y_420_ = v_a_413_;
v___y_421_ = v_a_414_;
v___y_422_ = v_a_415_;
v___y_423_ = v_a_416_;
goto v___jp_418_;
}
v___jp_418_:
{
lean_object* v___x_424_; 
v___x_424_ = l_Lean_MVarId_assert(v_g_409_, v_h_410_, v_____do__lift_419_, v_v_411_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_a_425_; uint8_t v___x_426_; lean_object* v___x_427_; 
v_a_425_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_a_425_);
lean_dec_ref_known(v___x_424_, 1);
v___x_426_ = 1;
v___x_427_ = l_Lean_Meta_intro1Core(v_a_425_, v___x_426_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
return v___x_427_;
}
else
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
v_a_428_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v___x_424_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_424_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_note___boxed(lean_object* v_g_447_, lean_object* v_h_448_, lean_object* v_v_449_, lean_object* v_t_x3f_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_MVarId_note(v_g_447_, v_h_448_, v_v_449_, v_t_x3f_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_);
lean_dec(v_a_454_);
lean_dec_ref(v_a_453_);
lean_dec(v_a_452_);
lean_dec_ref(v_a_451_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_define___lam__0(lean_object* v_mvarId_457_, lean_object* v___x_458_, lean_object* v_name_459_, lean_object* v_type_460_, lean_object* v_val_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v___x_467_; 
lean_inc(v_mvarId_457_);
v___x_467_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_457_, v___x_458_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v___x_468_; 
lean_dec_ref_known(v___x_467_, 1);
lean_inc(v_mvarId_457_);
v___x_468_ = l_Lean_MVarId_getTag(v_mvarId_457_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v___x_470_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_a_469_);
lean_dec_ref_known(v___x_468_, 1);
lean_inc(v_mvarId_457_);
v___x_470_ = l_Lean_MVarId_getType(v_mvarId_457_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
if (lean_obj_tag(v___x_470_) == 0)
{
lean_object* v_a_471_; uint8_t v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v_a_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_a_471_);
lean_dec_ref_known(v___x_470_, 1);
v___x_472_ = 0;
v___x_473_ = l_Lean_Expr_letE___override(v_name_459_, v_type_460_, v_val_461_, v_a_471_, v___x_472_);
v___x_474_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_473_, v_a_469_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v_a_475_; lean_object* v___x_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_484_; 
v_a_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc_n(v_a_475_, 2);
lean_dec_ref_known(v___x_474_, 1);
v___x_476_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(v_mvarId_457_, v_a_475_, v___y_463_);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_484_ == 0)
{
lean_object* v_unused_485_; 
v_unused_485_ = lean_ctor_get(v___x_476_, 0);
lean_dec(v_unused_485_);
v___x_478_ = v___x_476_;
v_isShared_479_ = v_isSharedCheck_484_;
goto v_resetjp_477_;
}
else
{
lean_dec(v___x_476_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_484_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_480_; lean_object* v___x_482_; 
v___x_480_ = l_Lean_Expr_mvarId_x21(v_a_475_);
lean_dec(v_a_475_);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 0, v___x_480_);
v___x_482_ = v___x_478_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_480_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
else
{
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
lean_dec(v_mvarId_457_);
v_a_486_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_493_ == 0)
{
v___x_488_ = v___x_474_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_474_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_a_486_);
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
else
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
lean_dec(v_a_469_);
lean_dec_ref(v_val_461_);
lean_dec_ref(v_type_460_);
lean_dec(v_name_459_);
lean_dec(v_mvarId_457_);
v_a_494_ = lean_ctor_get(v___x_470_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_470_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_470_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_494_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
else
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_509_; 
lean_dec_ref(v_val_461_);
lean_dec_ref(v_type_460_);
lean_dec(v_name_459_);
lean_dec(v_mvarId_457_);
v_a_502_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_509_ == 0)
{
v___x_504_ = v___x_468_;
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_468_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_507_; 
if (v_isShared_505_ == 0)
{
v___x_507_ = v___x_504_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_502_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
else
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
lean_dec_ref(v_val_461_);
lean_dec_ref(v_type_460_);
lean_dec(v_name_459_);
lean_dec(v_mvarId_457_);
v_a_510_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_467_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_467_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_define___lam__0___boxed(lean_object* v_mvarId_518_, lean_object* v___x_519_, lean_object* v_name_520_, lean_object* v_type_521_, lean_object* v_val_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Lean_MVarId_define___lam__0(v_mvarId_518_, v___x_519_, v_name_520_, v_type_521_, v_val_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_define(lean_object* v_mvarId_532_, lean_object* v_name_533_, lean_object* v_type_534_, lean_object* v_val_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_){
_start:
{
lean_object* v___x_541_; lean_object* v___f_542_; lean_object* v___x_543_; 
v___x_541_ = ((lean_object*)(l_Lean_MVarId_define___closed__1));
lean_inc(v_mvarId_532_);
v___f_542_ = lean_alloc_closure((void*)(l_Lean_MVarId_define___lam__0___boxed), 10, 5);
lean_closure_set(v___f_542_, 0, v_mvarId_532_);
lean_closure_set(v___f_542_, 1, v___x_541_);
lean_closure_set(v___f_542_, 2, v_name_533_);
lean_closure_set(v___f_542_, 3, v_type_534_);
lean_closure_set(v___f_542_, 4, v_val_535_);
v___x_543_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(v_mvarId_532_, v___f_542_, v_a_536_, v_a_537_, v_a_538_, v_a_539_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_define___boxed(lean_object* v_mvarId_544_, lean_object* v_name_545_, lean_object* v_type_546_, lean_object* v_val_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_MVarId_define(v_mvarId_544_, v_name_545_, v_type_546_, v_val_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_);
lean_dec(v_a_551_);
lean_dec_ref(v_a_550_);
lean_dec(v_a_549_);
lean_dec_ref(v_a_548_);
return v_res_553_;
}
}
static lean_object* _init_l_Lean_MVarId_assertExt___lam__0___closed__2(void){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = lean_unsigned_to_nat(0u);
v___x_558_ = l_Lean_mkBVar(v___x_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertExt___lam__0(lean_object* v_mvarId_559_, lean_object* v___x_560_, lean_object* v_type_561_, lean_object* v_val_562_, lean_object* v_hName_563_, lean_object* v_name_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v___x_570_; 
lean_inc(v_mvarId_559_);
v___x_570_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_559_, v___x_560_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v___x_571_; 
lean_dec_ref_known(v___x_570_, 1);
lean_inc(v_mvarId_559_);
v___x_571_ = l_Lean_MVarId_getTag(v_mvarId_559_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v_a_572_; lean_object* v___x_573_; 
v_a_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_a_572_);
lean_dec_ref_known(v___x_571_, 1);
lean_inc(v_mvarId_559_);
v___x_573_ = l_Lean_MVarId_getType(v_mvarId_559_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v_a_574_; lean_object* v___x_575_; 
v_a_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc(v_a_574_);
lean_dec_ref_known(v___x_573_, 1);
lean_inc_ref(v_type_561_);
v___x_575_ = l_Lean_Meta_getLevel(v_type_561_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_a_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; uint8_t v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v_a_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_a_576_);
lean_dec_ref_known(v___x_575_, 1);
v___x_577_ = ((lean_object*)(l_Lean_MVarId_assertExt___lam__0___closed__1));
v___x_578_ = lean_box(0);
v___x_579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_579_, 0, v_a_576_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
v___x_580_ = l_Lean_mkConst(v___x_577_, v___x_579_);
v___x_581_ = lean_obj_once(&l_Lean_MVarId_assertExt___lam__0___closed__2, &l_Lean_MVarId_assertExt___lam__0___closed__2_once, _init_l_Lean_MVarId_assertExt___lam__0___closed__2);
lean_inc_ref(v_val_562_);
lean_inc_ref(v_type_561_);
v___x_582_ = l_Lean_mkApp3(v___x_580_, v_type_561_, v___x_581_, v_val_562_);
v___x_583_ = 0;
v___x_584_ = l_Lean_mkForall(v_hName_563_, v___x_583_, v___x_582_, v_a_574_);
v___x_585_ = l_Lean_mkForall(v_name_564_, v___x_583_, v_type_561_, v___x_584_);
v___x_586_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_585_, v_a_572_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v_a_587_; lean_object* v___x_588_; 
v_a_587_ = lean_ctor_get(v___x_586_, 0);
lean_inc(v_a_587_);
lean_dec_ref_known(v___x_586_, 1);
lean_inc_ref(v_val_562_);
v___x_588_ = l_Lean_Meta_mkEqRefl(v_val_562_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v_a_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_599_; 
v_a_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_a_589_);
lean_dec_ref_known(v___x_588_, 1);
lean_inc(v_a_587_);
v___x_590_ = l_Lean_mkAppB(v_a_587_, v_val_562_, v_a_589_);
v___x_591_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(v_mvarId_559_, v___x_590_, v___y_566_);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_599_ == 0)
{
lean_object* v_unused_600_; 
v_unused_600_ = lean_ctor_get(v___x_591_, 0);
lean_dec(v_unused_600_);
v___x_593_ = v___x_591_;
v_isShared_594_ = v_isSharedCheck_599_;
goto v_resetjp_592_;
}
else
{
lean_dec(v___x_591_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_599_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; lean_object* v___x_597_; 
v___x_595_ = l_Lean_Expr_mvarId_x21(v_a_587_);
lean_dec(v_a_587_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_595_);
v___x_597_ = v___x_593_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_595_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
else
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
lean_dec(v_a_587_);
lean_dec_ref(v_val_562_);
lean_dec(v_mvarId_559_);
v_a_601_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_608_ == 0)
{
v___x_603_ = v___x_588_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_588_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_601_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
else
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
lean_dec_ref(v_val_562_);
lean_dec(v_mvarId_559_);
v_a_609_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_616_ == 0)
{
v___x_611_ = v___x_586_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_586_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_609_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
else
{
lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_624_; 
lean_dec(v_a_574_);
lean_dec(v_a_572_);
lean_dec(v_name_564_);
lean_dec(v_hName_563_);
lean_dec_ref(v_val_562_);
lean_dec_ref(v_type_561_);
lean_dec(v_mvarId_559_);
v_a_617_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_624_ == 0)
{
v___x_619_ = v___x_575_;
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_dec(v___x_575_);
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
else
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
lean_dec(v_a_572_);
lean_dec(v_name_564_);
lean_dec(v_hName_563_);
lean_dec_ref(v_val_562_);
lean_dec_ref(v_type_561_);
lean_dec(v_mvarId_559_);
v_a_625_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_573_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_573_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
else
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
lean_dec(v_name_564_);
lean_dec(v_hName_563_);
lean_dec_ref(v_val_562_);
lean_dec_ref(v_type_561_);
lean_dec(v_mvarId_559_);
v_a_633_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_640_ == 0)
{
v___x_635_ = v___x_571_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_571_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_a_633_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
else
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_648_; 
lean_dec(v_name_564_);
lean_dec(v_hName_563_);
lean_dec_ref(v_val_562_);
lean_dec_ref(v_type_561_);
lean_dec(v_mvarId_559_);
v_a_641_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_648_ == 0)
{
v___x_643_ = v___x_570_;
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_570_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_641_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertExt___lam__0___boxed(lean_object* v_mvarId_649_, lean_object* v___x_650_, lean_object* v_type_651_, lean_object* v_val_652_, lean_object* v_hName_653_, lean_object* v_name_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Lean_MVarId_assertExt___lam__0(v_mvarId_649_, v___x_650_, v_type_651_, v_val_652_, v_hName_653_, v_name_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertExt(lean_object* v_mvarId_661_, lean_object* v_name_662_, lean_object* v_type_663_, lean_object* v_val_664_, lean_object* v_hName_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_){
_start:
{
lean_object* v___x_671_; lean_object* v___f_672_; lean_object* v___x_673_; 
v___x_671_ = ((lean_object*)(l_Lean_MVarId_assert___closed__1));
lean_inc(v_mvarId_661_);
v___f_672_ = lean_alloc_closure((void*)(l_Lean_MVarId_assertExt___lam__0___boxed), 11, 6);
lean_closure_set(v___f_672_, 0, v_mvarId_661_);
lean_closure_set(v___f_672_, 1, v___x_671_);
lean_closure_set(v___f_672_, 2, v_type_663_);
lean_closure_set(v___f_672_, 3, v_val_664_);
lean_closure_set(v___f_672_, 4, v_hName_665_);
lean_closure_set(v___f_672_, 5, v_name_662_);
v___x_673_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(v_mvarId_661_, v___f_672_, v_a_666_, v_a_667_, v_a_668_, v_a_669_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertExt___boxed(lean_object* v_mvarId_674_, lean_object* v_name_675_, lean_object* v_type_676_, lean_object* v_val_677_, lean_object* v_hName_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_MVarId_assertExt(v_mvarId_674_, v_name_675_, v_type_676_, v_val_677_, v_hName_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_);
lean_dec(v_a_682_);
lean_dec_ref(v_a_681_);
lean_dec(v_a_680_);
lean_dec_ref(v_a_679_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___redArg(lean_object* v_t_685_, lean_object* v___y_686_){
_start:
{
lean_object* v___x_688_; lean_object* v_infoState_689_; uint8_t v_enabled_690_; 
v___x_688_ = lean_st_ref_get(v___y_686_);
v_infoState_689_ = lean_ctor_get(v___x_688_, 7);
lean_inc_ref(v_infoState_689_);
lean_dec(v___x_688_);
v_enabled_690_ = lean_ctor_get_uint8(v_infoState_689_, sizeof(void*)*3);
lean_dec_ref(v_infoState_689_);
if (v_enabled_690_ == 0)
{
lean_object* v___x_691_; lean_object* v___x_692_; 
lean_dec_ref(v_t_685_);
v___x_691_ = lean_box(0);
v___x_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
return v___x_692_;
}
else
{
lean_object* v___x_693_; lean_object* v_infoState_694_; lean_object* v_env_695_; lean_object* v_nextMacroScope_696_; lean_object* v_ngen_697_; lean_object* v_auxDeclNGen_698_; lean_object* v_traceState_699_; lean_object* v_cache_700_; lean_object* v_messages_701_; lean_object* v_snapshotTasks_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_724_; 
v___x_693_ = lean_st_ref_take(v___y_686_);
v_infoState_694_ = lean_ctor_get(v___x_693_, 7);
v_env_695_ = lean_ctor_get(v___x_693_, 0);
v_nextMacroScope_696_ = lean_ctor_get(v___x_693_, 1);
v_ngen_697_ = lean_ctor_get(v___x_693_, 2);
v_auxDeclNGen_698_ = lean_ctor_get(v___x_693_, 3);
v_traceState_699_ = lean_ctor_get(v___x_693_, 4);
v_cache_700_ = lean_ctor_get(v___x_693_, 5);
v_messages_701_ = lean_ctor_get(v___x_693_, 6);
v_snapshotTasks_702_ = lean_ctor_get(v___x_693_, 8);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_724_ == 0)
{
v___x_704_ = v___x_693_;
v_isShared_705_ = v_isSharedCheck_724_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_snapshotTasks_702_);
lean_inc(v_infoState_694_);
lean_inc(v_messages_701_);
lean_inc(v_cache_700_);
lean_inc(v_traceState_699_);
lean_inc(v_auxDeclNGen_698_);
lean_inc(v_ngen_697_);
lean_inc(v_nextMacroScope_696_);
lean_inc(v_env_695_);
lean_dec(v___x_693_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_724_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
uint8_t v_enabled_706_; lean_object* v_assignment_707_; lean_object* v_lazyAssignment_708_; lean_object* v_trees_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_723_; 
v_enabled_706_ = lean_ctor_get_uint8(v_infoState_694_, sizeof(void*)*3);
v_assignment_707_ = lean_ctor_get(v_infoState_694_, 0);
v_lazyAssignment_708_ = lean_ctor_get(v_infoState_694_, 1);
v_trees_709_ = lean_ctor_get(v_infoState_694_, 2);
v_isSharedCheck_723_ = !lean_is_exclusive(v_infoState_694_);
if (v_isSharedCheck_723_ == 0)
{
v___x_711_ = v_infoState_694_;
v_isShared_712_ = v_isSharedCheck_723_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_trees_709_);
lean_inc(v_lazyAssignment_708_);
lean_inc(v_assignment_707_);
lean_dec(v_infoState_694_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_723_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v___x_715_; 
v___x_713_ = l_Lean_PersistentArray_push___redArg(v_trees_709_, v_t_685_);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 2, v___x_713_);
v___x_715_ = v___x_711_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_assignment_707_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_lazyAssignment_708_);
lean_ctor_set(v_reuseFailAlloc_722_, 2, v___x_713_);
lean_ctor_set_uint8(v_reuseFailAlloc_722_, sizeof(void*)*3, v_enabled_706_);
v___x_715_ = v_reuseFailAlloc_722_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v___x_717_; 
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 7, v___x_715_);
v___x_717_ = v___x_704_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_env_695_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_nextMacroScope_696_);
lean_ctor_set(v_reuseFailAlloc_721_, 2, v_ngen_697_);
lean_ctor_set(v_reuseFailAlloc_721_, 3, v_auxDeclNGen_698_);
lean_ctor_set(v_reuseFailAlloc_721_, 4, v_traceState_699_);
lean_ctor_set(v_reuseFailAlloc_721_, 5, v_cache_700_);
lean_ctor_set(v_reuseFailAlloc_721_, 6, v_messages_701_);
lean_ctor_set(v_reuseFailAlloc_721_, 7, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_721_, 8, v_snapshotTasks_702_);
v___x_717_ = v_reuseFailAlloc_721_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_718_ = lean_st_ref_put(v___y_686_, v___x_717_);
v___x_719_ = lean_box(0);
v___x_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
return v___x_720_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___redArg___boxed(lean_object* v_t_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___redArg(v_t_725_, v___y_726_);
lean_dec(v___y_726_);
return v_res_728_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__0(void){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_729_ = lean_unsigned_to_nat(32u);
v___x_730_ = lean_mk_empty_array_with_capacity(v___x_729_);
v___x_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
return v___x_731_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__1(void){
_start:
{
size_t v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_732_ = ((size_t)5ULL);
v___x_733_ = lean_unsigned_to_nat(0u);
v___x_734_ = lean_unsigned_to_nat(32u);
v___x_735_ = lean_mk_empty_array_with_capacity(v___x_734_);
v___x_736_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__0);
v___x_737_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_737_, 0, v___x_736_);
lean_ctor_set(v___x_737_, 1, v___x_735_);
lean_ctor_set(v___x_737_, 2, v___x_733_);
lean_ctor_set(v___x_737_, 3, v___x_733_);
lean_ctor_set_usize(v___x_737_, 4, v___x_732_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0(lean_object* v_t_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
lean_object* v___x_744_; lean_object* v_infoState_745_; uint8_t v_enabled_746_; 
v___x_744_ = lean_st_ref_get(v___y_742_);
v_infoState_745_ = lean_ctor_get(v___x_744_, 7);
lean_inc_ref(v_infoState_745_);
lean_dec(v___x_744_);
v_enabled_746_ = lean_ctor_get_uint8(v_infoState_745_, sizeof(void*)*3);
lean_dec_ref(v_infoState_745_);
if (v_enabled_746_ == 0)
{
lean_object* v___x_747_; lean_object* v___x_748_; 
lean_dec_ref(v_t_738_);
v___x_747_ = lean_box(0);
v___x_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
return v___x_748_;
}
else
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_749_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__1);
v___x_750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_750_, 0, v_t_738_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
v___x_751_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___redArg(v___x_750_, v___y_742_);
return v___x_751_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___boxed(lean_object* v_t_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0(v_t_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__1(lean_object* v___x_759_, lean_object* v_as_760_, size_t v_sz_761_, size_t v_i_762_, lean_object* v_b_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
uint8_t v___x_769_; 
v___x_769_ = lean_usize_dec_lt(v_i_762_, v_sz_761_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; 
lean_dec_ref(v___x_759_);
v___x_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_770_, 0, v_b_763_);
return v___x_770_;
}
else
{
lean_object* v_snd_771_; lean_object* v_fst_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_819_; 
v_snd_771_ = lean_ctor_get(v_b_763_, 1);
v_fst_772_ = lean_ctor_get(v_b_763_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v_b_763_);
if (v_isSharedCheck_819_ == 0)
{
v___x_774_ = v_b_763_;
v_isShared_775_ = v_isSharedCheck_819_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_snd_771_);
lean_inc(v_fst_772_);
lean_dec(v_b_763_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_819_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v_array_776_; lean_object* v_start_777_; lean_object* v_stop_778_; uint8_t v___x_779_; 
v_array_776_ = lean_ctor_get(v_snd_771_, 0);
v_start_777_ = lean_ctor_get(v_snd_771_, 1);
v_stop_778_ = lean_ctor_get(v_snd_771_, 2);
v___x_779_ = lean_nat_dec_lt(v_start_777_, v_stop_778_);
if (v___x_779_ == 0)
{
lean_object* v___x_781_; 
lean_dec_ref(v___x_759_);
if (v_isShared_775_ == 0)
{
v___x_781_ = v___x_774_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_fst_772_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v_snd_771_);
v___x_781_ = v_reuseFailAlloc_783_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_782_; 
v___x_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
return v___x_782_;
}
}
else
{
lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_815_; 
lean_inc(v_stop_778_);
lean_inc(v_start_777_);
lean_inc_ref(v_array_776_);
v_isSharedCheck_815_ = !lean_is_exclusive(v_snd_771_);
if (v_isSharedCheck_815_ == 0)
{
lean_object* v_unused_816_; lean_object* v_unused_817_; lean_object* v_unused_818_; 
v_unused_816_ = lean_ctor_get(v_snd_771_, 2);
lean_dec(v_unused_816_);
v_unused_817_ = lean_ctor_get(v_snd_771_, 1);
lean_dec(v_unused_817_);
v_unused_818_ = lean_ctor_get(v_snd_771_, 0);
lean_dec(v_unused_818_);
v___x_785_ = v_snd_771_;
v_isShared_786_ = v_isSharedCheck_815_;
goto v_resetjp_784_;
}
else
{
lean_dec(v_snd_771_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_815_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v_a_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v_a_787_ = lean_array_uget_borrowed(v_as_760_, v_i_762_);
v___x_788_ = lean_array_fget_borrowed(v_array_776_, v_start_777_);
lean_inc_n(v___x_788_, 3);
v___x_789_ = l_Lean_mkFVar(v___x_788_);
lean_inc_n(v_a_787_, 2);
v___x_790_ = l_Lean_Meta_FVarSubst_insert(v_fst_772_, v_a_787_, v___x_789_);
lean_inc_ref(v___x_759_);
v___x_791_ = l_Lean_LocalContext_get_x21(v___x_759_, v___x_788_);
v___x_792_ = l_Lean_LocalDecl_userName(v___x_791_);
lean_dec_ref(v___x_791_);
v___x_793_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
lean_ctor_set(v___x_793_, 1, v___x_788_);
lean_ctor_set(v___x_793_, 2, v_a_787_);
v___x_794_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_794_, 0, v___x_793_);
v___x_795_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0(v___x_794_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_799_; 
lean_dec_ref_known(v___x_795_, 1);
v___x_796_ = lean_unsigned_to_nat(1u);
v___x_797_ = lean_nat_add(v_start_777_, v___x_796_);
lean_dec(v_start_777_);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 1, v___x_797_);
v___x_799_ = v___x_785_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_array_776_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_806_, 2, v_stop_778_);
v___x_799_ = v_reuseFailAlloc_806_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v___x_801_; 
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 1, v___x_799_);
lean_ctor_set(v___x_774_, 0, v___x_790_);
v___x_801_ = v___x_774_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v___x_799_);
v___x_801_ = v_reuseFailAlloc_805_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
size_t v___x_802_; size_t v___x_803_; 
v___x_802_ = ((size_t)1ULL);
v___x_803_ = lean_usize_add(v_i_762_, v___x_802_);
v_i_762_ = v___x_803_;
v_b_763_ = v___x_801_;
goto _start;
}
}
}
else
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_814_; 
lean_dec(v___x_790_);
lean_del_object(v___x_785_);
lean_dec(v_stop_778_);
lean_dec(v_start_777_);
lean_dec_ref(v_array_776_);
lean_del_object(v___x_774_);
lean_dec_ref(v___x_759_);
v_a_807_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_814_ == 0)
{
v___x_809_ = v___x_795_;
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_795_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
if (v_isShared_810_ == 0)
{
v___x_812_ = v___x_809_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_807_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__1___boxed(lean_object* v___x_820_, lean_object* v_as_821_, lean_object* v_sz_822_, lean_object* v_i_823_, lean_object* v_b_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
size_t v_sz_boxed_830_; size_t v_i_boxed_831_; lean_object* v_res_832_; 
v_sz_boxed_830_ = lean_unbox_usize(v_sz_822_);
lean_dec(v_sz_822_);
v_i_boxed_831_ = lean_unbox_usize(v_i_823_);
lean_dec(v_i_823_);
v_res_832_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__1(v___x_820_, v_as_821_, v_sz_boxed_830_, v_i_boxed_831_, v_b_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec_ref(v_as_821_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertAfter(lean_object* v_mvarId_836_, lean_object* v_fvarId_837_, lean_object* v_userName_838_, lean_object* v_type_839_, lean_object* v_val_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_846_ = ((lean_object*)(l_Lean_MVarId_assertAfter___closed__1));
lean_inc(v_mvarId_836_);
v___x_847_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_836_, v___x_846_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v___x_848_; 
lean_dec_ref_known(v___x_847_, 1);
v___x_848_ = l_Lean_MVarId_revertAfter(v_mvarId_836_, v_fvarId_837_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v_fst_850_; lean_object* v_snd_851_; lean_object* v___x_852_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_a_849_);
lean_dec_ref_known(v___x_848_, 1);
v_fst_850_ = lean_ctor_get(v_a_849_, 0);
lean_inc(v_fst_850_);
v_snd_851_ = lean_ctor_get(v_a_849_, 1);
lean_inc(v_snd_851_);
lean_dec(v_a_849_);
v___x_852_ = l_Lean_MVarId_assert(v_snd_851_, v_userName_838_, v_type_839_, v_val_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; uint8_t v___x_854_; lean_object* v___x_855_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_a_853_);
lean_dec_ref_known(v___x_852_, 1);
v___x_854_ = 1;
v___x_855_ = l_Lean_Meta_intro1Core(v_a_853_, v___x_854_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v_fst_857_; lean_object* v_snd_858_; lean_object* v___x_859_; lean_object* v___x_860_; uint8_t v___x_861_; lean_object* v___x_862_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_a_856_);
lean_dec_ref_known(v___x_855_, 1);
v_fst_857_ = lean_ctor_get(v_a_856_, 0);
lean_inc(v_fst_857_);
v_snd_858_ = lean_ctor_get(v_a_856_, 1);
lean_inc(v_snd_858_);
lean_dec(v_a_856_);
v___x_859_ = lean_array_get_size(v_fst_850_);
v___x_860_ = lean_box(0);
v___x_861_ = 0;
v___x_862_ = l_Lean_Meta_introNCore(v_snd_858_, v___x_859_, v___x_860_, v___x_861_, v___x_854_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; lean_object* v_fst_864_; lean_object* v_snd_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_908_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_a_863_);
lean_dec_ref_known(v___x_862_, 1);
v_fst_864_ = lean_ctor_get(v_a_863_, 0);
v_snd_865_ = lean_ctor_get(v_a_863_, 1);
v_isSharedCheck_908_ = !lean_is_exclusive(v_a_863_);
if (v_isSharedCheck_908_ == 0)
{
v___x_867_ = v_a_863_;
v_isShared_868_ = v_isSharedCheck_908_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_snd_865_);
lean_inc(v_fst_864_);
lean_dec(v_a_863_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_908_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_869_; 
lean_inc(v_snd_865_);
v___x_869_ = l_Lean_MVarId_getDecl(v_snd_865_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; lean_object* v_lctx_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_877_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
lean_inc(v_a_870_);
lean_dec_ref_known(v___x_869_, 1);
v_lctx_871_ = lean_ctor_get(v_a_870_, 1);
lean_inc_ref(v_lctx_871_);
lean_dec(v_a_870_);
v___x_872_ = lean_box(0);
v___x_873_ = lean_unsigned_to_nat(0u);
v___x_874_ = lean_array_get_size(v_fst_864_);
v___x_875_ = l_Array_toSubarray___redArg(v_fst_864_, v___x_873_, v___x_874_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 1, v___x_875_);
lean_ctor_set(v___x_867_, 0, v___x_872_);
v___x_877_ = v___x_867_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_872_);
lean_ctor_set(v_reuseFailAlloc_899_, 1, v___x_875_);
v___x_877_ = v_reuseFailAlloc_899_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
size_t v_sz_878_; size_t v___x_879_; lean_object* v___x_880_; 
v_sz_878_ = lean_array_size(v_fst_850_);
v___x_879_ = ((size_t)0ULL);
v___x_880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__1(v_lctx_871_, v_fst_850_, v_sz_878_, v___x_879_, v___x_877_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
lean_dec(v_fst_850_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_890_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_890_ == 0)
{
v___x_883_ = v___x_880_;
v_isShared_884_ = v_isSharedCheck_890_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_880_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_890_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v_fst_885_; lean_object* v___x_886_; lean_object* v___x_888_; 
v_fst_885_ = lean_ctor_get(v_a_881_, 0);
lean_inc(v_fst_885_);
lean_dec(v_a_881_);
v___x_886_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_886_, 0, v_fst_857_);
lean_ctor_set(v___x_886_, 1, v_snd_865_);
lean_ctor_set(v___x_886_, 2, v_fst_885_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v___x_886_);
v___x_888_ = v___x_883_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_886_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
else
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_898_; 
lean_dec(v_snd_865_);
lean_dec(v_fst_857_);
v_a_891_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_898_ == 0)
{
v___x_893_ = v___x_880_;
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_880_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_896_; 
if (v_isShared_894_ == 0)
{
v___x_896_ = v___x_893_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_a_891_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
}
else
{
lean_object* v_a_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_907_; 
lean_del_object(v___x_867_);
lean_dec(v_snd_865_);
lean_dec(v_fst_864_);
lean_dec(v_fst_857_);
lean_dec(v_fst_850_);
v_a_900_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_907_ == 0)
{
v___x_902_ = v___x_869_;
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_a_900_);
lean_dec(v___x_869_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_905_; 
if (v_isShared_903_ == 0)
{
v___x_905_ = v___x_902_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_a_900_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
}
else
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_916_; 
lean_dec(v_fst_857_);
lean_dec(v_fst_850_);
v_a_909_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_916_ == 0)
{
v___x_911_ = v___x_862_;
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_862_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_912_ == 0)
{
v___x_914_ = v___x_911_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_909_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
lean_dec(v_fst_850_);
v_a_917_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_855_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_855_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_917_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
else
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_dec(v_fst_850_);
v_a_925_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_852_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_852_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
else
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_940_; 
lean_dec_ref(v_val_840_);
lean_dec_ref(v_type_839_);
lean_dec(v_userName_838_);
v_a_933_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_940_ == 0)
{
v___x_935_ = v___x_848_;
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_848_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_a_933_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
else
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
lean_dec_ref(v_val_840_);
lean_dec_ref(v_type_839_);
lean_dec(v_userName_838_);
lean_dec(v_fvarId_837_);
lean_dec(v_mvarId_836_);
v_a_941_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_847_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_847_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_941_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertAfter___boxed(lean_object* v_mvarId_949_, lean_object* v_fvarId_950_, lean_object* v_userName_951_, lean_object* v_type_952_, lean_object* v_val_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Lean_MVarId_assertAfter(v_mvarId_949_, v_fvarId_950_, v_userName_951_, v_type_952_, v_val_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_);
lean_dec(v_a_957_);
lean_dec_ref(v_a_956_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0(lean_object* v_t_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___redArg(v_t_960_, v___y_964_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___boxed(lean_object* v_t_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0(v_t_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg(lean_object* v_ldecl_x27_974_, lean_object* v_a_975_){
_start:
{
lean_object* v___x_977_; lean_object* v_fst_979_; lean_object* v_snd_980_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; uint8_t v___x_986_; 
v___x_977_ = lean_st_ref_take(v_a_975_);
v___x_983_ = lean_box(0);
v___x_984_ = l_Lean_LocalDecl_index(v___x_977_);
v___x_985_ = l_Lean_LocalDecl_index(v_ldecl_x27_974_);
v___x_986_ = lean_nat_dec_lt(v___x_984_, v___x_985_);
lean_dec(v___x_985_);
lean_dec(v___x_984_);
if (v___x_986_ == 0)
{
lean_dec_ref(v_ldecl_x27_974_);
v_fst_979_ = v___x_983_;
v_snd_980_ = v___x_977_;
goto v___jp_978_;
}
else
{
lean_dec(v___x_977_);
v_fst_979_ = v___x_983_;
v_snd_980_ = v_ldecl_x27_974_;
goto v___jp_978_;
}
v___jp_978_:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = lean_st_ref_put(v_a_975_, v_snd_980_);
v___x_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_982_, 0, v_fst_979_);
return v___x_982_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg___boxed(lean_object* v_ldecl_x27_987_, lean_object* v_a_988_, lean_object* v_a_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg(v_ldecl_x27_987_, v_a_988_);
lean_dec(v_a_988_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl(lean_object* v_ldecl_x27_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg(v_ldecl_x27_991_, v_a_992_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___boxed(lean_object* v_ldecl_x27_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl(v_ldecl_x27_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_);
lean_dec(v_a_1004_);
lean_dec_ref(v_a_1003_);
lean_dec(v_a_1002_);
lean_dec_ref(v_a_1001_);
lean_dec(v_a_1000_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___redArg(lean_object* v_as_1007_, size_t v_i_1008_, size_t v_stop_1009_, lean_object* v_b_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v_a_1017_; uint8_t v___x_1021_; 
v___x_1021_ = lean_usize_dec_eq(v_i_1008_, v_stop_1009_);
if (v___x_1021_ == 0)
{
lean_object* v___x_1022_; 
v___x_1022_ = lean_array_uget_borrowed(v_as_1007_, v_i_1008_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v___x_1023_; 
v___x_1023_ = lean_box(0);
v_a_1017_ = v___x_1023_;
goto v___jp_1016_;
}
else
{
lean_object* v_val_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v_val_1024_ = lean_ctor_get(v___x_1022_, 0);
v___x_1025_ = l_Lean_LocalDecl_fvarId(v_val_1024_);
v___x_1026_ = l_Lean_FVarId_getDecl___redArg(v___x_1025_, v___y_1012_, v___y_1013_, v___y_1014_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; lean_object* v___x_1028_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_a_1027_);
lean_dec_ref_known(v___x_1026_, 1);
v___x_1028_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg(v_a_1027_, v___y_1011_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v_a_1029_; 
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_a_1029_);
lean_dec_ref_known(v___x_1028_, 1);
v_a_1017_ = v_a_1029_;
goto v___jp_1016_;
}
else
{
return v___x_1028_;
}
}
else
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1037_; 
v_a_1030_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1032_ = v___x_1026_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_1026_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1030_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
}
else
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1038_, 0, v_b_1010_);
return v___x_1038_;
}
v___jp_1016_:
{
size_t v___x_1018_; size_t v___x_1019_; 
v___x_1018_ = ((size_t)1ULL);
v___x_1019_ = lean_usize_add(v_i_1008_, v___x_1018_);
v_i_1008_ = v___x_1019_;
v_b_1010_ = v_a_1017_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_as_1039_, lean_object* v_i_1040_, lean_object* v_stop_1041_, lean_object* v_b_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
size_t v_i_boxed_1048_; size_t v_stop_boxed_1049_; lean_object* v_res_1050_; 
v_i_boxed_1048_ = lean_unbox_usize(v_i_1040_);
lean_dec(v_i_1040_);
v_stop_boxed_1049_ = lean_unbox_usize(v_stop_1041_);
lean_dec(v_stop_1041_);
v_res_1050_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___redArg(v_as_1039_, v_i_boxed_1048_, v_stop_boxed_1049_, v_b_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v_as_1039_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(lean_object* v_as_1051_, size_t v_i_1052_, size_t v_stop_1053_, lean_object* v_b_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v_a_1062_; uint8_t v___x_1066_; 
v___x_1066_ = lean_usize_dec_eq(v_i_1052_, v_stop_1053_);
if (v___x_1066_ == 0)
{
lean_object* v___x_1067_; 
v___x_1067_ = lean_array_uget_borrowed(v_as_1051_, v_i_1052_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v___x_1068_; 
v___x_1068_ = lean_box(0);
v_a_1062_ = v___x_1068_;
goto v___jp_1061_;
}
else
{
lean_object* v_val_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v_val_1069_ = lean_ctor_get(v___x_1067_, 0);
v___x_1070_ = l_Lean_LocalDecl_fvarId(v_val_1069_);
v___x_1071_ = l_Lean_FVarId_getDecl___redArg(v___x_1070_, v___y_1056_, v___y_1058_, v___y_1059_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v___x_1073_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_a_1072_);
lean_dec_ref_known(v___x_1071_, 1);
v___x_1073_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg(v_a_1072_, v___y_1055_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
lean_inc(v_a_1074_);
lean_dec_ref_known(v___x_1073_, 1);
v_a_1062_ = v_a_1074_;
goto v___jp_1061_;
}
else
{
return v___x_1073_;
}
}
else
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
v_a_1075_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_1071_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1071_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1075_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
}
else
{
lean_object* v___x_1083_; 
v___x_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1083_, 0, v_b_1054_);
return v___x_1083_;
}
v___jp_1061_:
{
size_t v___x_1063_; size_t v___x_1064_; lean_object* v___x_1065_; 
v___x_1063_ = ((size_t)1ULL);
v___x_1064_ = lean_usize_add(v_i_1052_, v___x_1063_);
v___x_1065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___redArg(v_as_1051_, v___x_1064_, v_stop_1053_, v_a_1062_, v___y_1055_, v___y_1056_, v___y_1058_, v___y_1059_);
return v___x_1065_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2___boxed(lean_object* v_as_1084_, lean_object* v_i_1085_, lean_object* v_stop_1086_, lean_object* v_b_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
size_t v_i_boxed_1094_; size_t v_stop_boxed_1095_; lean_object* v_res_1096_; 
v_i_boxed_1094_ = lean_unbox_usize(v_i_1085_);
lean_dec(v_i_1085_);
v_stop_boxed_1095_ = lean_unbox_usize(v_stop_1086_);
lean_dec(v_stop_1086_);
v_res_1096_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_as_1084_, v_i_boxed_1094_, v_stop_boxed_1095_, v_b_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec_ref(v_as_1084_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
if (lean_obj_tag(v_x_1097_) == 0)
{
lean_object* v_cs_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1125_; 
v_cs_1104_ = lean_ctor_get(v_x_1097_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_x_1097_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1106_ = v_x_1097_;
v_isShared_1107_ = v_isSharedCheck_1125_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_cs_1104_);
lean_dec(v_x_1097_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1125_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; uint8_t v___x_1111_; 
v___x_1108_ = lean_unsigned_to_nat(0u);
v___x_1109_ = lean_array_get_size(v_cs_1104_);
v___x_1110_ = lean_box(0);
v___x_1111_ = lean_nat_dec_lt(v___x_1108_, v___x_1109_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1113_; 
lean_dec_ref(v_cs_1104_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 0, v___x_1110_);
v___x_1113_ = v___x_1106_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1110_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
else
{
uint8_t v___x_1115_; 
v___x_1115_ = lean_nat_dec_le(v___x_1109_, v___x_1109_);
if (v___x_1115_ == 0)
{
if (v___x_1111_ == 0)
{
lean_object* v___x_1117_; 
lean_dec_ref(v_cs_1104_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 0, v___x_1110_);
v___x_1117_ = v___x_1106_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v___x_1110_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
else
{
size_t v___x_1119_; size_t v___x_1120_; lean_object* v___x_1121_; 
lean_del_object(v___x_1106_);
v___x_1119_ = ((size_t)0ULL);
v___x_1120_ = lean_usize_of_nat(v___x_1109_);
v___x_1121_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4(v_cs_1104_, v___x_1119_, v___x_1120_, v___x_1110_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
lean_dec_ref(v_cs_1104_);
return v___x_1121_;
}
}
else
{
size_t v___x_1122_; size_t v___x_1123_; lean_object* v___x_1124_; 
lean_del_object(v___x_1106_);
v___x_1122_ = ((size_t)0ULL);
v___x_1123_ = lean_usize_of_nat(v___x_1109_);
v___x_1124_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4(v_cs_1104_, v___x_1122_, v___x_1123_, v___x_1110_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
lean_dec_ref(v_cs_1104_);
return v___x_1124_;
}
}
}
}
else
{
lean_object* v_vs_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1147_; 
v_vs_1126_ = lean_ctor_get(v_x_1097_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v_x_1097_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1128_ = v_x_1097_;
v_isShared_1129_ = v_isSharedCheck_1147_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_vs_1126_);
lean_dec(v_x_1097_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1147_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; uint8_t v___x_1133_; 
v___x_1130_ = lean_unsigned_to_nat(0u);
v___x_1131_ = lean_array_get_size(v_vs_1126_);
v___x_1132_ = lean_box(0);
v___x_1133_ = lean_nat_dec_lt(v___x_1130_, v___x_1131_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1135_; 
lean_dec_ref(v_vs_1126_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set_tag(v___x_1128_, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1132_);
v___x_1135_ = v___x_1128_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1132_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
else
{
uint8_t v___x_1137_; 
v___x_1137_ = lean_nat_dec_le(v___x_1131_, v___x_1131_);
if (v___x_1137_ == 0)
{
if (v___x_1133_ == 0)
{
lean_object* v___x_1139_; 
lean_dec_ref(v_vs_1126_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set_tag(v___x_1128_, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1132_);
v___x_1139_ = v___x_1128_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1132_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
else
{
size_t v___x_1141_; size_t v___x_1142_; lean_object* v___x_1143_; 
lean_del_object(v___x_1128_);
v___x_1141_ = ((size_t)0ULL);
v___x_1142_ = lean_usize_of_nat(v___x_1131_);
v___x_1143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_vs_1126_, v___x_1141_, v___x_1142_, v___x_1132_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
lean_dec_ref(v_vs_1126_);
return v___x_1143_;
}
}
else
{
size_t v___x_1144_; size_t v___x_1145_; lean_object* v___x_1146_; 
lean_del_object(v___x_1128_);
v___x_1144_ = ((size_t)0ULL);
v___x_1145_ = lean_usize_of_nat(v___x_1131_);
v___x_1146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_vs_1126_, v___x_1144_, v___x_1145_, v___x_1132_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
lean_dec_ref(v_vs_1126_);
return v___x_1146_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4(lean_object* v_as_1148_, size_t v_i_1149_, size_t v_stop_1150_, lean_object* v_b_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
uint8_t v___x_1158_; 
v___x_1158_ = lean_usize_dec_eq(v_i_1149_, v_stop_1150_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1159_ = lean_array_uget_borrowed(v_as_1148_, v_i_1149_);
lean_inc(v___x_1159_);
v___x_1160_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__3(v___x_1159_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v_a_1161_; size_t v___x_1162_; size_t v___x_1163_; 
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
lean_inc(v_a_1161_);
lean_dec_ref_known(v___x_1160_, 1);
v___x_1162_ = ((size_t)1ULL);
v___x_1163_ = lean_usize_add(v_i_1149_, v___x_1162_);
v_i_1149_ = v___x_1163_;
v_b_1151_ = v_a_1161_;
goto _start;
}
else
{
return v___x_1160_;
}
}
else
{
lean_object* v___x_1165_; 
v___x_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1165_, 0, v_b_1151_);
return v___x_1165_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_as_1166_, lean_object* v_i_1167_, lean_object* v_stop_1168_, lean_object* v_b_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
size_t v_i_boxed_1176_; size_t v_stop_boxed_1177_; lean_object* v_res_1178_; 
v_i_boxed_1176_ = lean_unbox_usize(v_i_1167_);
lean_dec(v_i_1167_);
v_stop_boxed_1177_ = lean_unbox_usize(v_stop_1168_);
lean_dec(v_stop_1168_);
v_res_1178_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4(v_as_1166_, v_i_boxed_1176_, v_stop_boxed_1177_, v_b_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v_as_1166_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__3(v_x_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec(v___y_1180_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__3(lean_object* v_t_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v_root_1194_; lean_object* v_tail_1195_; lean_object* v___x_1196_; 
v_root_1194_ = lean_ctor_get(v_t_1187_, 0);
lean_inc_ref(v_root_1194_);
v_tail_1195_ = lean_ctor_get(v_t_1187_, 1);
lean_inc_ref(v_tail_1195_);
lean_dec_ref(v_t_1187_);
v___x_1196_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__3(v_root_1194_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1217_; 
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1217_ == 0)
{
lean_object* v_unused_1218_; 
v_unused_1218_ = lean_ctor_get(v___x_1196_, 0);
lean_dec(v_unused_1218_);
v___x_1198_ = v___x_1196_;
v_isShared_1199_ = v_isSharedCheck_1217_;
goto v_resetjp_1197_;
}
else
{
lean_dec(v___x_1196_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1217_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; uint8_t v___x_1203_; 
v___x_1200_ = lean_unsigned_to_nat(0u);
v___x_1201_ = lean_array_get_size(v_tail_1195_);
v___x_1202_ = lean_box(0);
v___x_1203_ = lean_nat_dec_lt(v___x_1200_, v___x_1201_);
if (v___x_1203_ == 0)
{
lean_object* v___x_1205_; 
lean_dec_ref(v_tail_1195_);
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 0, v___x_1202_);
v___x_1205_ = v___x_1198_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1202_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
else
{
uint8_t v___x_1207_; 
v___x_1207_ = lean_nat_dec_le(v___x_1201_, v___x_1201_);
if (v___x_1207_ == 0)
{
if (v___x_1203_ == 0)
{
lean_object* v___x_1209_; 
lean_dec_ref(v_tail_1195_);
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 0, v___x_1202_);
v___x_1209_ = v___x_1198_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1202_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
else
{
size_t v___x_1211_; size_t v___x_1212_; lean_object* v___x_1213_; 
lean_del_object(v___x_1198_);
v___x_1211_ = ((size_t)0ULL);
v___x_1212_ = lean_usize_of_nat(v___x_1201_);
v___x_1213_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_tail_1195_, v___x_1211_, v___x_1212_, v___x_1202_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
lean_dec_ref(v_tail_1195_);
return v___x_1213_;
}
}
else
{
size_t v___x_1214_; size_t v___x_1215_; lean_object* v___x_1216_; 
lean_del_object(v___x_1198_);
v___x_1214_ = ((size_t)0ULL);
v___x_1215_ = lean_usize_of_nat(v___x_1201_);
v___x_1216_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_tail_1195_, v___x_1214_, v___x_1215_, v___x_1202_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
lean_dec_ref(v_tail_1195_);
return v___x_1216_;
}
}
}
}
else
{
lean_dec_ref(v_tail_1195_);
return v___x_1196_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__3___boxed(lean_object* v_t_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__3(v_t_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
return v_res_1226_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1(lean_object* v_x_1228_, size_t v_x_1229_, size_t v_x_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
if (lean_obj_tag(v_x_1228_) == 0)
{
lean_object* v_cs_1237_; lean_object* v___x_1238_; size_t v___x_1239_; lean_object* v_j_1240_; lean_object* v___x_1241_; size_t v___x_1242_; size_t v___x_1243_; size_t v___x_1244_; size_t v___x_1245_; size_t v___x_1246_; size_t v___x_1247_; lean_object* v___x_1248_; 
v_cs_1237_ = lean_ctor_get(v_x_1228_, 0);
lean_inc_ref(v_cs_1237_);
lean_dec_ref_known(v_x_1228_, 1);
v___x_1238_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___closed__0);
v___x_1239_ = lean_usize_shift_right(v_x_1229_, v_x_1230_);
v_j_1240_ = lean_usize_to_nat(v___x_1239_);
v___x_1241_ = lean_array_get_borrowed(v___x_1238_, v_cs_1237_, v_j_1240_);
v___x_1242_ = ((size_t)1ULL);
v___x_1243_ = lean_usize_shift_left(v___x_1242_, v_x_1230_);
v___x_1244_ = lean_usize_sub(v___x_1243_, v___x_1242_);
v___x_1245_ = lean_usize_land(v_x_1229_, v___x_1244_);
v___x_1246_ = ((size_t)5ULL);
v___x_1247_ = lean_usize_sub(v_x_1230_, v___x_1246_);
lean_inc(v___x_1241_);
v___x_1248_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1(v___x_1241_, v___x_1245_, v___x_1247_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1270_; 
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1270_ == 0)
{
lean_object* v_unused_1271_; 
v_unused_1271_ = lean_ctor_get(v___x_1248_, 0);
lean_dec(v_unused_1271_);
v___x_1250_ = v___x_1248_;
v_isShared_1251_ = v_isSharedCheck_1270_;
goto v_resetjp_1249_;
}
else
{
lean_dec(v___x_1248_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1270_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; uint8_t v___x_1256_; 
v___x_1252_ = lean_unsigned_to_nat(1u);
v___x_1253_ = lean_nat_add(v_j_1240_, v___x_1252_);
lean_dec(v_j_1240_);
v___x_1254_ = lean_array_get_size(v_cs_1237_);
v___x_1255_ = lean_box(0);
v___x_1256_ = lean_nat_dec_lt(v___x_1253_, v___x_1254_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1258_; 
lean_dec(v___x_1253_);
lean_dec_ref(v_cs_1237_);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 0, v___x_1255_);
v___x_1258_ = v___x_1250_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v___x_1255_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
else
{
uint8_t v___x_1260_; 
v___x_1260_ = lean_nat_dec_le(v___x_1254_, v___x_1254_);
if (v___x_1260_ == 0)
{
if (v___x_1256_ == 0)
{
lean_object* v___x_1262_; 
lean_dec(v___x_1253_);
lean_dec_ref(v_cs_1237_);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 0, v___x_1255_);
v___x_1262_ = v___x_1250_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1255_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
else
{
size_t v___x_1264_; size_t v___x_1265_; lean_object* v___x_1266_; 
lean_del_object(v___x_1250_);
v___x_1264_ = lean_usize_of_nat(v___x_1253_);
lean_dec(v___x_1253_);
v___x_1265_ = lean_usize_of_nat(v___x_1254_);
v___x_1266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4(v_cs_1237_, v___x_1264_, v___x_1265_, v___x_1255_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
lean_dec_ref(v_cs_1237_);
return v___x_1266_;
}
}
else
{
size_t v___x_1267_; size_t v___x_1268_; lean_object* v___x_1269_; 
lean_del_object(v___x_1250_);
v___x_1267_ = lean_usize_of_nat(v___x_1253_);
lean_dec(v___x_1253_);
v___x_1268_ = lean_usize_of_nat(v___x_1254_);
v___x_1269_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4(v_cs_1237_, v___x_1267_, v___x_1268_, v___x_1255_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
lean_dec_ref(v_cs_1237_);
return v___x_1269_;
}
}
}
}
else
{
lean_dec(v_j_1240_);
lean_dec_ref(v_cs_1237_);
return v___x_1248_;
}
}
else
{
lean_object* v_vs_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1293_; 
v_vs_1272_ = lean_ctor_get(v_x_1228_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v_x_1228_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1274_ = v_x_1228_;
v_isShared_1275_ = v_isSharedCheck_1293_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_vs_1272_);
lean_dec(v_x_1228_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1293_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; 
v___x_1276_ = lean_usize_to_nat(v_x_1229_);
v___x_1277_ = lean_array_get_size(v_vs_1272_);
v___x_1278_ = lean_box(0);
v___x_1279_ = lean_nat_dec_lt(v___x_1276_, v___x_1277_);
if (v___x_1279_ == 0)
{
lean_object* v___x_1281_; 
lean_dec(v___x_1276_);
lean_dec_ref(v_vs_1272_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set_tag(v___x_1274_, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1278_);
v___x_1281_ = v___x_1274_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1278_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
else
{
uint8_t v___x_1283_; 
v___x_1283_ = lean_nat_dec_le(v___x_1277_, v___x_1277_);
if (v___x_1283_ == 0)
{
if (v___x_1279_ == 0)
{
lean_object* v___x_1285_; 
lean_dec(v___x_1276_);
lean_dec_ref(v_vs_1272_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set_tag(v___x_1274_, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1278_);
v___x_1285_ = v___x_1274_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1278_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
else
{
size_t v___x_1287_; size_t v___x_1288_; lean_object* v___x_1289_; 
lean_del_object(v___x_1274_);
v___x_1287_ = lean_usize_of_nat(v___x_1276_);
lean_dec(v___x_1276_);
v___x_1288_ = lean_usize_of_nat(v___x_1277_);
v___x_1289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_vs_1272_, v___x_1287_, v___x_1288_, v___x_1278_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
lean_dec_ref(v_vs_1272_);
return v___x_1289_;
}
}
else
{
size_t v___x_1290_; size_t v___x_1291_; lean_object* v___x_1292_; 
lean_del_object(v___x_1274_);
v___x_1290_ = lean_usize_of_nat(v___x_1276_);
lean_dec(v___x_1276_);
v___x_1291_ = lean_usize_of_nat(v___x_1277_);
v___x_1292_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_vs_1272_, v___x_1290_, v___x_1291_, v___x_1278_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
lean_dec_ref(v_vs_1272_);
return v___x_1292_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___boxed(lean_object* v_x_1294_, lean_object* v_x_1295_, lean_object* v_x_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
size_t v_x_9471__boxed_1303_; size_t v_x_9472__boxed_1304_; lean_object* v_res_1305_; 
v_x_9471__boxed_1303_ = lean_unbox_usize(v_x_1295_);
lean_dec(v_x_1295_);
v_x_9472__boxed_1304_ = lean_unbox_usize(v_x_1296_);
lean_dec(v_x_1296_);
v_res_1305_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1(v_x_1294_, v_x_9471__boxed_1303_, v_x_9472__boxed_1304_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0(lean_object* v_t_1306_, lean_object* v_start_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v___x_1314_; uint8_t v___x_1315_; 
v___x_1314_ = lean_unsigned_to_nat(0u);
v___x_1315_ = lean_nat_dec_eq(v_start_1307_, v___x_1314_);
if (v___x_1315_ == 0)
{
lean_object* v_root_1316_; lean_object* v_tail_1317_; size_t v_shift_1318_; lean_object* v_tailOff_1319_; uint8_t v___x_1320_; 
v_root_1316_ = lean_ctor_get(v_t_1306_, 0);
lean_inc_ref(v_root_1316_);
v_tail_1317_ = lean_ctor_get(v_t_1306_, 1);
lean_inc_ref(v_tail_1317_);
v_shift_1318_ = lean_ctor_get_usize(v_t_1306_, 4);
v_tailOff_1319_ = lean_ctor_get(v_t_1306_, 3);
lean_inc(v_tailOff_1319_);
lean_dec_ref(v_t_1306_);
v___x_1320_ = lean_nat_dec_le(v_tailOff_1319_, v_start_1307_);
if (v___x_1320_ == 0)
{
size_t v___x_1321_; lean_object* v___x_1322_; 
lean_dec(v_tailOff_1319_);
v___x_1321_ = lean_usize_of_nat(v_start_1307_);
v___x_1322_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1(v_root_1316_, v___x_1321_, v_shift_1318_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1342_; 
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1342_ == 0)
{
lean_object* v_unused_1343_; 
v_unused_1343_ = lean_ctor_get(v___x_1322_, 0);
lean_dec(v_unused_1343_);
v___x_1324_ = v___x_1322_;
v_isShared_1325_ = v_isSharedCheck_1342_;
goto v_resetjp_1323_;
}
else
{
lean_dec(v___x_1322_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1342_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; uint8_t v___x_1328_; 
v___x_1326_ = lean_array_get_size(v_tail_1317_);
v___x_1327_ = lean_box(0);
v___x_1328_ = lean_nat_dec_lt(v___x_1314_, v___x_1326_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1330_; 
lean_dec_ref(v_tail_1317_);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 0, v___x_1327_);
v___x_1330_ = v___x_1324_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1327_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
else
{
uint8_t v___x_1332_; 
v___x_1332_ = lean_nat_dec_le(v___x_1326_, v___x_1326_);
if (v___x_1332_ == 0)
{
if (v___x_1328_ == 0)
{
lean_object* v___x_1334_; 
lean_dec_ref(v_tail_1317_);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 0, v___x_1327_);
v___x_1334_ = v___x_1324_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1327_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
else
{
size_t v___x_1336_; size_t v___x_1337_; lean_object* v___x_1338_; 
lean_del_object(v___x_1324_);
v___x_1336_ = ((size_t)0ULL);
v___x_1337_ = lean_usize_of_nat(v___x_1326_);
v___x_1338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_tail_1317_, v___x_1336_, v___x_1337_, v___x_1327_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
lean_dec_ref(v_tail_1317_);
return v___x_1338_;
}
}
else
{
size_t v___x_1339_; size_t v___x_1340_; lean_object* v___x_1341_; 
lean_del_object(v___x_1324_);
v___x_1339_ = ((size_t)0ULL);
v___x_1340_ = lean_usize_of_nat(v___x_1326_);
v___x_1341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_tail_1317_, v___x_1339_, v___x_1340_, v___x_1327_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
lean_dec_ref(v_tail_1317_);
return v___x_1341_;
}
}
}
}
else
{
lean_dec_ref(v_tail_1317_);
return v___x_1322_;
}
}
else
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; uint8_t v___x_1347_; 
lean_dec_ref(v_root_1316_);
v___x_1344_ = lean_nat_sub(v_start_1307_, v_tailOff_1319_);
lean_dec(v_tailOff_1319_);
v___x_1345_ = lean_array_get_size(v_tail_1317_);
v___x_1346_ = lean_box(0);
v___x_1347_ = lean_nat_dec_lt(v___x_1344_, v___x_1345_);
if (v___x_1347_ == 0)
{
lean_object* v___x_1348_; 
lean_dec(v___x_1344_);
lean_dec_ref(v_tail_1317_);
v___x_1348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1346_);
return v___x_1348_;
}
else
{
uint8_t v___x_1349_; 
v___x_1349_ = lean_nat_dec_le(v___x_1345_, v___x_1345_);
if (v___x_1349_ == 0)
{
if (v___x_1347_ == 0)
{
lean_object* v___x_1350_; 
lean_dec(v___x_1344_);
lean_dec_ref(v_tail_1317_);
v___x_1350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1346_);
return v___x_1350_;
}
else
{
size_t v___x_1351_; size_t v___x_1352_; lean_object* v___x_1353_; 
v___x_1351_ = lean_usize_of_nat(v___x_1344_);
lean_dec(v___x_1344_);
v___x_1352_ = lean_usize_of_nat(v___x_1345_);
v___x_1353_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_tail_1317_, v___x_1351_, v___x_1352_, v___x_1346_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
lean_dec_ref(v_tail_1317_);
return v___x_1353_;
}
}
else
{
size_t v___x_1354_; size_t v___x_1355_; lean_object* v___x_1356_; 
v___x_1354_ = lean_usize_of_nat(v___x_1344_);
lean_dec(v___x_1344_);
v___x_1355_ = lean_usize_of_nat(v___x_1345_);
v___x_1356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_tail_1317_, v___x_1354_, v___x_1355_, v___x_1346_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
lean_dec_ref(v_tail_1317_);
return v___x_1356_;
}
}
}
}
else
{
lean_object* v___x_1357_; 
v___x_1357_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__3(v_t_1306_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
return v___x_1357_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0___boxed(lean_object* v_t_1358_, lean_object* v_start_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0(v_t_1358_, v_start_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v___y_1360_);
lean_dec(v_start_1359_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0(lean_object* v_lctx_1367_, lean_object* v_start_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
lean_object* v_decls_1375_; lean_object* v___x_1376_; 
v_decls_1375_ = lean_ctor_get(v_lctx_1367_, 1);
lean_inc_ref(v_decls_1375_);
lean_dec_ref(v_lctx_1367_);
v___x_1376_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0(v_decls_1375_, v_start_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0___boxed(lean_object* v_lctx_1377_, lean_object* v_start_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l_Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0(v_lctx_1377_, v_start_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec(v_start_1378_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___lam__0(lean_object* v_e_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
if (lean_obj_tag(v_e_1386_) == 1)
{
lean_object* v_fvarId_1393_; lean_object* v___x_1394_; 
v_fvarId_1393_ = lean_ctor_get(v_e_1386_, 0);
lean_inc(v_fvarId_1393_);
lean_dec_ref_known(v_e_1386_, 1);
v___x_1394_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1393_, v___y_1388_, v___y_1390_, v___y_1391_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v_a_1395_; lean_object* v___x_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1405_; 
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_a_1395_);
lean_dec_ref_known(v___x_1394_, 1);
v___x_1396_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg(v_a_1395_, v___y_1387_);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1405_ == 0)
{
lean_object* v_unused_1406_; 
v_unused_1406_ = lean_ctor_get(v___x_1396_, 0);
lean_dec(v_unused_1406_);
v___x_1398_ = v___x_1396_;
v_isShared_1399_ = v_isSharedCheck_1405_;
goto v_resetjp_1397_;
}
else
{
lean_dec(v___x_1396_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1405_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
uint8_t v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1403_; 
v___x_1400_ = 0;
v___x_1401_ = lean_box(v___x_1400_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 0, v___x_1401_);
v___x_1403_ = v___x_1398_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1401_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1414_; 
v_a_1407_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1409_ = v___x_1394_;
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1394_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1412_; 
if (v_isShared_1410_ == 0)
{
v___x_1412_ = v___x_1409_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1407_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
else
{
if (lean_obj_tag(v_e_1386_) == 2)
{
lean_object* v_mvarId_1415_; lean_object* v___x_1416_; 
v_mvarId_1415_ = lean_ctor_get(v_e_1386_, 0);
lean_inc(v_mvarId_1415_);
lean_dec_ref_known(v_e_1386_, 1);
v___x_1416_ = l_Lean_MVarId_getDecl(v_mvarId_1415_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v_a_1417_; lean_object* v_lctx_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc(v_a_1417_);
lean_dec_ref_known(v___x_1416_, 1);
v_lctx_1418_ = lean_ctor_get(v_a_1417_, 1);
lean_inc_ref(v_lctx_1418_);
lean_dec(v_a_1417_);
v___x_1419_ = lean_unsigned_to_nat(0u);
v___x_1420_ = l_Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0(v_lctx_1418_, v___x_1419_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1429_; 
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1429_ == 0)
{
lean_object* v_unused_1430_; 
v_unused_1430_ = lean_ctor_get(v___x_1420_, 0);
lean_dec(v_unused_1430_);
v___x_1422_ = v___x_1420_;
v_isShared_1423_ = v_isSharedCheck_1429_;
goto v_resetjp_1421_;
}
else
{
lean_dec(v___x_1420_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1429_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
uint8_t v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1427_; 
v___x_1424_ = 0;
v___x_1425_ = lean_box(v___x_1424_);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 0, v___x_1425_);
v___x_1427_ = v___x_1422_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1425_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
else
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
v_a_1431_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v___x_1420_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1420_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1431_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
v_a_1439_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1416_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1416_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
else
{
uint8_t v___x_1447_; 
v___x_1447_ = l_Lean_Expr_hasFVar(v_e_1386_);
if (v___x_1447_ == 0)
{
uint8_t v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1448_ = l_Lean_Expr_hasExprMVar(v_e_1386_);
lean_dec_ref(v_e_1386_);
v___x_1449_ = lean_box(v___x_1448_);
v___x_1450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1449_);
return v___x_1450_;
}
else
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
lean_dec_ref(v_e_1386_);
v___x_1451_ = lean_box(v___x_1447_);
v___x_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1451_);
return v___x_1452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___lam__0___boxed(lean_object* v_e_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___lam__0(v_e_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
lean_dec(v___y_1454_);
return v_res_1460_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___redArg(lean_object* v_a_1461_, lean_object* v_x_1462_){
_start:
{
if (lean_obj_tag(v_x_1462_) == 0)
{
uint8_t v___x_1463_; 
v___x_1463_ = 0;
return v___x_1463_;
}
else
{
lean_object* v_key_1464_; lean_object* v_tail_1465_; uint8_t v___x_1466_; 
v_key_1464_ = lean_ctor_get(v_x_1462_, 0);
v_tail_1465_ = lean_ctor_get(v_x_1462_, 2);
v___x_1466_ = lean_expr_eqv(v_key_1464_, v_a_1461_);
if (v___x_1466_ == 0)
{
v_x_1462_ = v_tail_1465_;
goto _start;
}
else
{
return v___x_1466_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_a_1468_, lean_object* v_x_1469_){
_start:
{
uint8_t v_res_1470_; lean_object* v_r_1471_; 
v_res_1470_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___redArg(v_a_1468_, v_x_1469_);
lean_dec(v_x_1469_);
lean_dec_ref(v_a_1468_);
v_r_1471_ = lean_box(v_res_1470_);
return v_r_1471_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13_spec__14___redArg(lean_object* v_x_1472_, lean_object* v_x_1473_){
_start:
{
if (lean_obj_tag(v_x_1473_) == 0)
{
return v_x_1472_;
}
else
{
lean_object* v_key_1474_; lean_object* v_value_1475_; lean_object* v_tail_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1499_; 
v_key_1474_ = lean_ctor_get(v_x_1473_, 0);
v_value_1475_ = lean_ctor_get(v_x_1473_, 1);
v_tail_1476_ = lean_ctor_get(v_x_1473_, 2);
v_isSharedCheck_1499_ = !lean_is_exclusive(v_x_1473_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1478_ = v_x_1473_;
v_isShared_1479_ = v_isSharedCheck_1499_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_tail_1476_);
lean_inc(v_value_1475_);
lean_inc(v_key_1474_);
lean_dec(v_x_1473_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1499_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1480_; uint64_t v___x_1481_; uint64_t v___x_1482_; uint64_t v___x_1483_; uint64_t v_fold_1484_; uint64_t v___x_1485_; uint64_t v___x_1486_; uint64_t v___x_1487_; size_t v___x_1488_; size_t v___x_1489_; size_t v___x_1490_; size_t v___x_1491_; size_t v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1495_; 
v___x_1480_ = lean_array_get_size(v_x_1472_);
v___x_1481_ = l_Lean_Expr_hash(v_key_1474_);
v___x_1482_ = 32ULL;
v___x_1483_ = lean_uint64_shift_right(v___x_1481_, v___x_1482_);
v_fold_1484_ = lean_uint64_xor(v___x_1481_, v___x_1483_);
v___x_1485_ = 16ULL;
v___x_1486_ = lean_uint64_shift_right(v_fold_1484_, v___x_1485_);
v___x_1487_ = lean_uint64_xor(v_fold_1484_, v___x_1486_);
v___x_1488_ = lean_uint64_to_usize(v___x_1487_);
v___x_1489_ = lean_usize_of_nat(v___x_1480_);
v___x_1490_ = ((size_t)1ULL);
v___x_1491_ = lean_usize_sub(v___x_1489_, v___x_1490_);
v___x_1492_ = lean_usize_land(v___x_1488_, v___x_1491_);
v___x_1493_ = lean_array_uget_borrowed(v_x_1472_, v___x_1492_);
lean_inc(v___x_1493_);
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 2, v___x_1493_);
v___x_1495_ = v___x_1478_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_key_1474_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v_value_1475_);
lean_ctor_set(v_reuseFailAlloc_1498_, 2, v___x_1493_);
v___x_1495_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
lean_object* v___x_1496_; 
v___x_1496_ = lean_array_uset(v_x_1472_, v___x_1492_, v___x_1495_);
v_x_1472_ = v___x_1496_;
v_x_1473_ = v_tail_1476_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13___redArg(lean_object* v_i_1500_, lean_object* v_source_1501_, lean_object* v_target_1502_){
_start:
{
lean_object* v___x_1503_; uint8_t v___x_1504_; 
v___x_1503_ = lean_array_get_size(v_source_1501_);
v___x_1504_ = lean_nat_dec_lt(v_i_1500_, v___x_1503_);
if (v___x_1504_ == 0)
{
lean_dec_ref(v_source_1501_);
lean_dec(v_i_1500_);
return v_target_1502_;
}
else
{
lean_object* v_es_1505_; lean_object* v___x_1506_; lean_object* v_source_1507_; lean_object* v_target_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v_es_1505_ = lean_array_fget(v_source_1501_, v_i_1500_);
v___x_1506_ = lean_box(0);
v_source_1507_ = lean_array_fset(v_source_1501_, v_i_1500_, v___x_1506_);
v_target_1508_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13_spec__14___redArg(v_target_1502_, v_es_1505_);
v___x_1509_ = lean_unsigned_to_nat(1u);
v___x_1510_ = lean_nat_add(v_i_1500_, v___x_1509_);
lean_dec(v_i_1500_);
v_i_1500_ = v___x_1510_;
v_source_1501_ = v_source_1507_;
v_target_1502_ = v_target_1508_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9___redArg(lean_object* v_data_1512_){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v_nbuckets_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1513_ = lean_array_get_size(v_data_1512_);
v___x_1514_ = lean_unsigned_to_nat(2u);
v_nbuckets_1515_ = lean_nat_mul(v___x_1513_, v___x_1514_);
v___x_1516_ = lean_unsigned_to_nat(0u);
v___x_1517_ = lean_box(0);
v___x_1518_ = lean_mk_array(v_nbuckets_1515_, v___x_1517_);
v___x_1519_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13___redArg(v___x_1516_, v_data_1512_, v___x_1518_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__10___redArg(lean_object* v_a_1520_, lean_object* v_b_1521_, lean_object* v_x_1522_){
_start:
{
if (lean_obj_tag(v_x_1522_) == 0)
{
lean_dec(v_b_1521_);
lean_dec_ref(v_a_1520_);
return v_x_1522_;
}
else
{
lean_object* v_key_1523_; lean_object* v_value_1524_; lean_object* v_tail_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1537_; 
v_key_1523_ = lean_ctor_get(v_x_1522_, 0);
v_value_1524_ = lean_ctor_get(v_x_1522_, 1);
v_tail_1525_ = lean_ctor_get(v_x_1522_, 2);
v_isSharedCheck_1537_ = !lean_is_exclusive(v_x_1522_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1527_ = v_x_1522_;
v_isShared_1528_ = v_isSharedCheck_1537_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_tail_1525_);
lean_inc(v_value_1524_);
lean_inc(v_key_1523_);
lean_dec(v_x_1522_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1537_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
uint8_t v___x_1529_; 
v___x_1529_ = lean_expr_eqv(v_key_1523_, v_a_1520_);
if (v___x_1529_ == 0)
{
lean_object* v___x_1530_; lean_object* v___x_1532_; 
v___x_1530_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__10___redArg(v_a_1520_, v_b_1521_, v_tail_1525_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 2, v___x_1530_);
v___x_1532_ = v___x_1527_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_key_1523_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v_value_1524_);
lean_ctor_set(v_reuseFailAlloc_1533_, 2, v___x_1530_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
else
{
lean_object* v___x_1535_; 
lean_dec(v_value_1524_);
lean_dec(v_key_1523_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 1, v_b_1521_);
lean_ctor_set(v___x_1527_, 0, v_a_1520_);
v___x_1535_ = v___x_1527_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_a_1520_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v_b_1521_);
lean_ctor_set(v_reuseFailAlloc_1536_, 2, v_tail_1525_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3___redArg(lean_object* v_m_1538_, lean_object* v_a_1539_, lean_object* v_b_1540_){
_start:
{
lean_object* v_size_1541_; lean_object* v_buckets_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1585_; 
v_size_1541_ = lean_ctor_get(v_m_1538_, 0);
v_buckets_1542_ = lean_ctor_get(v_m_1538_, 1);
v_isSharedCheck_1585_ = !lean_is_exclusive(v_m_1538_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1544_ = v_m_1538_;
v_isShared_1545_ = v_isSharedCheck_1585_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_buckets_1542_);
lean_inc(v_size_1541_);
lean_dec(v_m_1538_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1585_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1546_; uint64_t v___x_1547_; uint64_t v___x_1548_; uint64_t v___x_1549_; uint64_t v_fold_1550_; uint64_t v___x_1551_; uint64_t v___x_1552_; uint64_t v___x_1553_; size_t v___x_1554_; size_t v___x_1555_; size_t v___x_1556_; size_t v___x_1557_; size_t v___x_1558_; lean_object* v_bkt_1559_; uint8_t v___x_1560_; 
v___x_1546_ = lean_array_get_size(v_buckets_1542_);
v___x_1547_ = l_Lean_Expr_hash(v_a_1539_);
v___x_1548_ = 32ULL;
v___x_1549_ = lean_uint64_shift_right(v___x_1547_, v___x_1548_);
v_fold_1550_ = lean_uint64_xor(v___x_1547_, v___x_1549_);
v___x_1551_ = 16ULL;
v___x_1552_ = lean_uint64_shift_right(v_fold_1550_, v___x_1551_);
v___x_1553_ = lean_uint64_xor(v_fold_1550_, v___x_1552_);
v___x_1554_ = lean_uint64_to_usize(v___x_1553_);
v___x_1555_ = lean_usize_of_nat(v___x_1546_);
v___x_1556_ = ((size_t)1ULL);
v___x_1557_ = lean_usize_sub(v___x_1555_, v___x_1556_);
v___x_1558_ = lean_usize_land(v___x_1554_, v___x_1557_);
v_bkt_1559_ = lean_array_uget_borrowed(v_buckets_1542_, v___x_1558_);
v___x_1560_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___redArg(v_a_1539_, v_bkt_1559_);
if (v___x_1560_ == 0)
{
lean_object* v___x_1561_; lean_object* v_size_x27_1562_; lean_object* v___x_1563_; lean_object* v_buckets_x27_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; uint8_t v___x_1570_; 
v___x_1561_ = lean_unsigned_to_nat(1u);
v_size_x27_1562_ = lean_nat_add(v_size_1541_, v___x_1561_);
lean_dec(v_size_1541_);
lean_inc(v_bkt_1559_);
v___x_1563_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1563_, 0, v_a_1539_);
lean_ctor_set(v___x_1563_, 1, v_b_1540_);
lean_ctor_set(v___x_1563_, 2, v_bkt_1559_);
v_buckets_x27_1564_ = lean_array_uset(v_buckets_1542_, v___x_1558_, v___x_1563_);
v___x_1565_ = lean_unsigned_to_nat(4u);
v___x_1566_ = lean_nat_mul(v_size_x27_1562_, v___x_1565_);
v___x_1567_ = lean_unsigned_to_nat(3u);
v___x_1568_ = lean_nat_div(v___x_1566_, v___x_1567_);
lean_dec(v___x_1566_);
v___x_1569_ = lean_array_get_size(v_buckets_x27_1564_);
v___x_1570_ = lean_nat_dec_le(v___x_1568_, v___x_1569_);
lean_dec(v___x_1568_);
if (v___x_1570_ == 0)
{
lean_object* v_val_1571_; lean_object* v___x_1573_; 
v_val_1571_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9___redArg(v_buckets_x27_1564_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 1, v_val_1571_);
lean_ctor_set(v___x_1544_, 0, v_size_x27_1562_);
v___x_1573_ = v___x_1544_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_size_x27_1562_);
lean_ctor_set(v_reuseFailAlloc_1574_, 1, v_val_1571_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
else
{
lean_object* v___x_1576_; 
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 1, v_buckets_x27_1564_);
lean_ctor_set(v___x_1544_, 0, v_size_x27_1562_);
v___x_1576_ = v___x_1544_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_size_x27_1562_);
lean_ctor_set(v_reuseFailAlloc_1577_, 1, v_buckets_x27_1564_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
else
{
lean_object* v___x_1578_; lean_object* v_buckets_x27_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1583_; 
lean_inc(v_bkt_1559_);
v___x_1578_ = lean_box(0);
v_buckets_x27_1579_ = lean_array_uset(v_buckets_1542_, v___x_1558_, v___x_1578_);
v___x_1580_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__10___redArg(v_a_1539_, v_b_1540_, v_bkt_1559_);
v___x_1581_ = lean_array_uset(v_buckets_x27_1579_, v___x_1558_, v___x_1580_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 1, v___x_1581_);
v___x_1583_ = v___x_1544_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_size_1541_);
lean_ctor_set(v_reuseFailAlloc_1584_, 1, v___x_1581_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___redArg(lean_object* v_a_1586_, lean_object* v_x_1587_){
_start:
{
if (lean_obj_tag(v_x_1587_) == 0)
{
lean_object* v___x_1588_; 
v___x_1588_ = lean_box(0);
return v___x_1588_;
}
else
{
lean_object* v_key_1589_; lean_object* v_value_1590_; lean_object* v_tail_1591_; uint8_t v___x_1592_; 
v_key_1589_ = lean_ctor_get(v_x_1587_, 0);
v_value_1590_ = lean_ctor_get(v_x_1587_, 1);
v_tail_1591_ = lean_ctor_get(v_x_1587_, 2);
v___x_1592_ = lean_expr_eqv(v_key_1589_, v_a_1586_);
if (v___x_1592_ == 0)
{
v_x_1587_ = v_tail_1591_;
goto _start;
}
else
{
lean_object* v___x_1594_; 
lean_inc(v_value_1590_);
v___x_1594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1594_, 0, v_value_1590_);
return v___x_1594_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_a_1595_, lean_object* v_x_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___redArg(v_a_1595_, v_x_1596_);
lean_dec(v_x_1596_);
lean_dec_ref(v_a_1595_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___redArg(lean_object* v_m_1598_, lean_object* v_a_1599_){
_start:
{
lean_object* v_buckets_1600_; lean_object* v___x_1601_; uint64_t v___x_1602_; uint64_t v___x_1603_; uint64_t v___x_1604_; uint64_t v_fold_1605_; uint64_t v___x_1606_; uint64_t v___x_1607_; uint64_t v___x_1608_; size_t v___x_1609_; size_t v___x_1610_; size_t v___x_1611_; size_t v___x_1612_; size_t v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v_buckets_1600_ = lean_ctor_get(v_m_1598_, 1);
v___x_1601_ = lean_array_get_size(v_buckets_1600_);
v___x_1602_ = l_Lean_Expr_hash(v_a_1599_);
v___x_1603_ = 32ULL;
v___x_1604_ = lean_uint64_shift_right(v___x_1602_, v___x_1603_);
v_fold_1605_ = lean_uint64_xor(v___x_1602_, v___x_1604_);
v___x_1606_ = 16ULL;
v___x_1607_ = lean_uint64_shift_right(v_fold_1605_, v___x_1606_);
v___x_1608_ = lean_uint64_xor(v_fold_1605_, v___x_1607_);
v___x_1609_ = lean_uint64_to_usize(v___x_1608_);
v___x_1610_ = lean_usize_of_nat(v___x_1601_);
v___x_1611_ = ((size_t)1ULL);
v___x_1612_ = lean_usize_sub(v___x_1610_, v___x_1611_);
v___x_1613_ = lean_usize_land(v___x_1609_, v___x_1612_);
v___x_1614_ = lean_array_uget_borrowed(v_buckets_1600_, v___x_1613_);
v___x_1615_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___redArg(v_a_1599_, v___x_1614_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___redArg___boxed(lean_object* v_m_1616_, lean_object* v_a_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___redArg(v_m_1616_, v_a_1617_);
lean_dec_ref(v_a_1617_);
lean_dec_ref(v_m_1616_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(lean_object* v_g_1619_, lean_object* v_e_1620_, lean_object* v_a_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v_a_1629_; lean_object* v___y_1635_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1637_ = lean_st_ref_get(v_a_1621_);
v___x_1638_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___redArg(v___x_1637_, v_e_1620_);
lean_dec(v___x_1637_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v___x_1639_; 
lean_inc_ref(v_g_1619_);
lean_inc(v___y_1626_);
lean_inc_ref(v___y_1625_);
lean_inc(v___y_1624_);
lean_inc_ref(v___y_1623_);
lean_inc(v___y_1622_);
lean_inc_ref(v_e_1620_);
v___x_1639_ = lean_apply_7(v_g_1619_, v_e_1620_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, lean_box(0));
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v_d_1642_; lean_object* v_b_1643_; lean_object* v___y_1644_; uint8_t v___x_1647_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_a_1640_);
lean_dec_ref_known(v___x_1639_, 1);
v___x_1647_ = lean_unbox(v_a_1640_);
lean_dec(v_a_1640_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; 
lean_dec_ref(v_g_1619_);
v___x_1648_ = lean_box(0);
v_a_1629_ = v___x_1648_;
goto v___jp_1628_;
}
else
{
switch(lean_obj_tag(v_e_1620_))
{
case 7:
{
lean_object* v_binderType_1649_; lean_object* v_body_1650_; 
v_binderType_1649_ = lean_ctor_get(v_e_1620_, 1);
v_body_1650_ = lean_ctor_get(v_e_1620_, 2);
lean_inc_ref(v_body_1650_);
lean_inc_ref(v_binderType_1649_);
v_d_1642_ = v_binderType_1649_;
v_b_1643_ = v_body_1650_;
v___y_1644_ = v_a_1621_;
goto v___jp_1641_;
}
case 6:
{
lean_object* v_binderType_1651_; lean_object* v_body_1652_; 
v_binderType_1651_ = lean_ctor_get(v_e_1620_, 1);
v_body_1652_ = lean_ctor_get(v_e_1620_, 2);
lean_inc_ref(v_body_1652_);
lean_inc_ref(v_binderType_1651_);
v_d_1642_ = v_binderType_1651_;
v_b_1643_ = v_body_1652_;
v___y_1644_ = v_a_1621_;
goto v___jp_1641_;
}
case 8:
{
lean_object* v_type_1653_; lean_object* v_value_1654_; lean_object* v_body_1655_; lean_object* v___x_1656_; 
v_type_1653_ = lean_ctor_get(v_e_1620_, 1);
v_value_1654_ = lean_ctor_get(v_e_1620_, 2);
v_body_1655_ = lean_ctor_get(v_e_1620_, 3);
lean_inc_ref(v_type_1653_);
lean_inc_ref(v_g_1619_);
v___x_1656_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1619_, v_type_1653_, v_a_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v___x_1657_; 
lean_dec_ref_known(v___x_1656_, 1);
lean_inc_ref(v_value_1654_);
lean_inc_ref(v_g_1619_);
v___x_1657_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1619_, v_value_1654_, v_a_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v___x_1658_; 
lean_dec_ref_known(v___x_1657_, 1);
lean_inc_ref(v_body_1655_);
v___x_1658_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1619_, v_body_1655_, v_a_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
v___y_1635_ = v___x_1658_;
goto v___jp_1634_;
}
else
{
lean_dec_ref(v_g_1619_);
v___y_1635_ = v___x_1657_;
goto v___jp_1634_;
}
}
else
{
lean_dec_ref(v_g_1619_);
v___y_1635_ = v___x_1656_;
goto v___jp_1634_;
}
}
case 5:
{
lean_object* v_fn_1659_; lean_object* v_arg_1660_; lean_object* v___x_1661_; 
v_fn_1659_ = lean_ctor_get(v_e_1620_, 0);
v_arg_1660_ = lean_ctor_get(v_e_1620_, 1);
lean_inc_ref(v_fn_1659_);
lean_inc_ref(v_g_1619_);
v___x_1661_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1619_, v_fn_1659_, v_a_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v___x_1662_; 
lean_dec_ref_known(v___x_1661_, 1);
lean_inc_ref(v_arg_1660_);
v___x_1662_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1619_, v_arg_1660_, v_a_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
v___y_1635_ = v___x_1662_;
goto v___jp_1634_;
}
else
{
lean_dec_ref(v_g_1619_);
v___y_1635_ = v___x_1661_;
goto v___jp_1634_;
}
}
case 10:
{
lean_object* v_expr_1663_; lean_object* v___x_1664_; 
v_expr_1663_ = lean_ctor_get(v_e_1620_, 1);
lean_inc_ref(v_expr_1663_);
v___x_1664_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1619_, v_expr_1663_, v_a_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
v___y_1635_ = v___x_1664_;
goto v___jp_1634_;
}
case 11:
{
lean_object* v_struct_1665_; lean_object* v___x_1666_; 
v_struct_1665_ = lean_ctor_get(v_e_1620_, 2);
lean_inc_ref(v_struct_1665_);
v___x_1666_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1619_, v_struct_1665_, v_a_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
v___y_1635_ = v___x_1666_;
goto v___jp_1634_;
}
default: 
{
lean_object* v___x_1667_; 
lean_dec_ref(v_g_1619_);
v___x_1667_ = lean_box(0);
v_a_1629_ = v___x_1667_;
goto v___jp_1628_;
}
}
}
v___jp_1641_:
{
lean_object* v___x_1645_; 
lean_inc_ref(v_g_1619_);
v___x_1645_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1619_, v_d_1642_, v___y_1644_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v___x_1646_; 
lean_dec_ref_known(v___x_1645_, 1);
v___x_1646_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1619_, v_b_1643_, v___y_1644_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
v___y_1635_ = v___x_1646_;
goto v___jp_1634_;
}
else
{
lean_dec_ref(v_b_1643_);
lean_dec_ref(v_g_1619_);
v___y_1635_ = v___x_1645_;
goto v___jp_1634_;
}
}
}
else
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
lean_dec_ref(v_e_1620_);
lean_dec_ref(v_g_1619_);
v_a_1668_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v___x_1639_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1639_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
}
else
{
lean_object* v_val_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1683_; 
lean_dec_ref(v_e_1620_);
lean_dec_ref(v_g_1619_);
v_val_1676_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1678_ = v___x_1638_;
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_val_1676_);
lean_dec(v___x_1638_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1681_; 
if (v_isShared_1679_ == 0)
{
lean_ctor_set_tag(v___x_1678_, 0);
v___x_1681_ = v___x_1678_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_val_1676_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
v___jp_1628_:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1630_ = lean_st_ref_take(v_a_1621_);
v___x_1631_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3___redArg(v___x_1630_, v_e_1620_, v_a_1629_);
v___x_1632_ = lean_st_ref_put(v_a_1621_, v___x_1631_);
v___x_1633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1633_, 0, v_a_1629_);
return v___x_1633_;
}
v___jp_1634_:
{
if (lean_obj_tag(v___y_1635_) == 0)
{
lean_object* v_a_1636_; 
v_a_1636_ = lean_ctor_get(v___y_1635_, 0);
lean_inc(v_a_1636_);
lean_dec_ref_known(v___y_1635_, 1);
v_a_1629_ = v_a_1636_;
goto v___jp_1628_;
}
else
{
lean_dec_ref(v_e_1620_);
return v___y_1635_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1___boxed(lean_object* v_g_1684_, lean_object* v_e_1685_, lean_object* v_a_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1684_, v_e_1685_, v_a_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec(v_a_1686_);
return v_res_1693_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__0(void){
_start:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1694_ = lean_box(0);
v___x_1695_ = lean_unsigned_to_nat(16u);
v___x_1696_ = lean_mk_array(v___x_1695_, v___x_1694_);
return v___x_1696_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__1(void){
_start:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1697_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__0, &l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__0_once, _init_l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__0);
v___x_1698_ = lean_unsigned_to_nat(0u);
v___x_1699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1698_);
lean_ctor_set(v___x_1699_, 1, v___x_1697_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar(lean_object* v_e_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_){
_start:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___f_1710_; lean_object* v___x_1711_; 
v___x_1708_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__1, &l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__1_once, _init_l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__1);
v___x_1709_ = lean_st_mk_ref(v___x_1708_);
v___f_1710_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__2));
v___x_1711_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v___f_1710_, v_e_1701_, v___x_1709_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_);
if (lean_obj_tag(v___x_1711_) == 0)
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1720_; 
v_a_1712_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1714_ = v___x_1711_;
v_isShared_1715_ = v_isSharedCheck_1720_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1711_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1720_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1716_; lean_object* v___x_1718_; 
v___x_1716_ = lean_st_ref_get(v___x_1709_);
lean_dec(v___x_1709_);
lean_dec(v___x_1716_);
if (v_isShared_1715_ == 0)
{
v___x_1718_ = v___x_1714_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1712_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
else
{
lean_dec(v___x_1709_);
return v___x_1711_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___boxed(lean_object* v_e_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar(v_e_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_);
lean_dec(v_a_1726_);
lean_dec_ref(v_a_1725_);
lean_dec(v_a_1724_);
lean_dec_ref(v_a_1723_);
lean_dec(v_a_1722_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2(lean_object* v_00_u03b2_1729_, lean_object* v_m_1730_, lean_object* v_a_1731_){
_start:
{
lean_object* v___x_1732_; 
v___x_1732_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___redArg(v_m_1730_, v_a_1731_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1733_, lean_object* v_m_1734_, lean_object* v_a_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2(v_00_u03b2_1733_, v_m_1734_, v_a_1735_);
lean_dec_ref(v_a_1735_);
lean_dec_ref(v_m_1734_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3(lean_object* v_00_u03b2_1737_, lean_object* v_m_1738_, lean_object* v_a_1739_, lean_object* v_b_1740_){
_start:
{
lean_object* v___x_1741_; 
v___x_1741_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3___redArg(v_m_1738_, v_a_1739_, v_b_1740_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_1742_, lean_object* v_a_1743_, lean_object* v_x_1744_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___redArg(v_a_1743_, v_x_1744_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1746_, lean_object* v_a_1747_, lean_object* v_x_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6(v_00_u03b2_1746_, v_a_1747_, v_x_1748_);
lean_dec(v_x_1748_);
lean_dec_ref(v_a_1747_);
return v_res_1749_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_1750_, lean_object* v_a_1751_, lean_object* v_x_1752_){
_start:
{
uint8_t v___x_1753_; 
v___x_1753_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___redArg(v_a_1751_, v_x_1752_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___boxed(lean_object* v_00_u03b2_1754_, lean_object* v_a_1755_, lean_object* v_x_1756_){
_start:
{
uint8_t v_res_1757_; lean_object* v_r_1758_; 
v_res_1757_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8(v_00_u03b2_1754_, v_a_1755_, v_x_1756_);
lean_dec(v_x_1756_);
lean_dec_ref(v_a_1755_);
v_r_1758_ = lean_box(v_res_1757_);
return v_r_1758_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9(lean_object* v_00_u03b2_1759_, lean_object* v_data_1760_){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9___redArg(v_data_1760_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__10(lean_object* v_00_u03b2_1762_, lean_object* v_a_1763_, lean_object* v_b_1764_, lean_object* v_x_1765_){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__10___redArg(v_a_1763_, v_b_1764_, v_x_1765_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6(lean_object* v_as_1767_, size_t v_i_1768_, size_t v_stop_1769_, lean_object* v_b_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___redArg(v_as_1767_, v_i_1768_, v_stop_1769_, v_b_1770_, v___y_1771_, v___y_1772_, v___y_1774_, v___y_1775_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* v_as_1778_, lean_object* v_i_1779_, lean_object* v_stop_1780_, lean_object* v_b_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
size_t v_i_boxed_1788_; size_t v_stop_boxed_1789_; lean_object* v_res_1790_; 
v_i_boxed_1788_ = lean_unbox_usize(v_i_1779_);
lean_dec(v_i_1779_);
v_stop_boxed_1789_ = lean_unbox_usize(v_stop_1780_);
lean_dec(v_stop_1780_);
v_res_1790_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6(v_as_1778_, v_i_boxed_1788_, v_stop_boxed_1789_, v_b_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v___y_1782_);
lean_dec_ref(v_as_1778_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13(lean_object* v_00_u03b2_1791_, lean_object* v_i_1792_, lean_object* v_source_1793_, lean_object* v_target_1794_){
_start:
{
lean_object* v___x_1795_; 
v___x_1795_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13___redArg(v_i_1792_, v_source_1793_, v_target_1794_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13_spec__14(lean_object* v_00_u03b2_1796_, lean_object* v_x_1797_, lean_object* v_x_1798_){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13_spec__14___redArg(v_x_1797_, v_x_1798_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___redArg(lean_object* v_e_1800_, lean_object* v___y_1801_){
_start:
{
uint8_t v___x_1803_; 
v___x_1803_ = l_Lean_Expr_hasMVar(v_e_1800_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; 
v___x_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1804_, 0, v_e_1800_);
return v___x_1804_;
}
else
{
lean_object* v___x_1805_; lean_object* v_mctx_1806_; lean_object* v___x_1807_; lean_object* v_fst_1808_; lean_object* v_snd_1809_; lean_object* v___x_1810_; lean_object* v_cache_1811_; lean_object* v_zetaDeltaFVarIds_1812_; lean_object* v_postponed_1813_; lean_object* v_diag_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1823_; 
v___x_1805_ = lean_st_ref_get(v___y_1801_);
v_mctx_1806_ = lean_ctor_get(v___x_1805_, 0);
lean_inc_ref(v_mctx_1806_);
lean_dec(v___x_1805_);
v___x_1807_ = l_Lean_instantiateMVarsCore(v_mctx_1806_, v_e_1800_);
v_fst_1808_ = lean_ctor_get(v___x_1807_, 0);
lean_inc(v_fst_1808_);
v_snd_1809_ = lean_ctor_get(v___x_1807_, 1);
lean_inc(v_snd_1809_);
lean_dec_ref(v___x_1807_);
v___x_1810_ = lean_st_ref_take(v___y_1801_);
v_cache_1811_ = lean_ctor_get(v___x_1810_, 1);
v_zetaDeltaFVarIds_1812_ = lean_ctor_get(v___x_1810_, 2);
v_postponed_1813_ = lean_ctor_get(v___x_1810_, 3);
v_diag_1814_ = lean_ctor_get(v___x_1810_, 4);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1823_ == 0)
{
lean_object* v_unused_1824_; 
v_unused_1824_ = lean_ctor_get(v___x_1810_, 0);
lean_dec(v_unused_1824_);
v___x_1816_ = v___x_1810_;
v_isShared_1817_ = v_isSharedCheck_1823_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_diag_1814_);
lean_inc(v_postponed_1813_);
lean_inc(v_zetaDeltaFVarIds_1812_);
lean_inc(v_cache_1811_);
lean_dec(v___x_1810_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1823_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1819_; 
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 0, v_snd_1809_);
v___x_1819_ = v___x_1816_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_snd_1809_);
lean_ctor_set(v_reuseFailAlloc_1822_, 1, v_cache_1811_);
lean_ctor_set(v_reuseFailAlloc_1822_, 2, v_zetaDeltaFVarIds_1812_);
lean_ctor_set(v_reuseFailAlloc_1822_, 3, v_postponed_1813_);
lean_ctor_set(v_reuseFailAlloc_1822_, 4, v_diag_1814_);
v___x_1819_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1820_ = lean_st_ref_put(v___y_1801_, v___x_1819_);
v___x_1821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1821_, 0, v_fst_1808_);
return v___x_1821_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___redArg___boxed(lean_object* v_e_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___redArg(v_e_1825_, v___y_1826_);
lean_dec(v___y_1826_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0(lean_object* v_e_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___redArg(v_e_1829_, v___y_1831_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___boxed(lean_object* v_e_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0(v_e_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertAfter_x27___lam__0(lean_object* v_type_1843_, lean_object* v_fvarId_1844_, lean_object* v_mvarId_1845_, lean_object* v_userName_1846_, lean_object* v_val_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_){
_start:
{
lean_object* v___x_1853_; lean_object* v_a_1854_; lean_object* v___x_1855_; 
v___x_1853_ = l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___redArg(v_type_1843_, v___y_1849_);
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
lean_inc(v_a_1854_);
lean_dec_ref(v___x_1853_);
v___x_1855_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1844_, v___y_1848_, v___y_1850_, v___y_1851_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v_a_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v_a_1856_ = lean_ctor_get(v___x_1855_, 0);
lean_inc(v_a_1856_);
lean_dec_ref_known(v___x_1855_, 1);
v___x_1857_ = lean_st_mk_ref(v_a_1856_);
lean_inc(v_a_1854_);
v___x_1858_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar(v_a_1854_, v___x_1857_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
lean_dec_ref_known(v___x_1858_, 1);
v___x_1859_ = lean_st_ref_get(v___x_1857_);
lean_dec(v___x_1857_);
v___x_1860_ = l_Lean_LocalDecl_fvarId(v___x_1859_);
lean_dec(v___x_1859_);
v___x_1861_ = l_Lean_MVarId_assertAfter(v_mvarId_1845_, v___x_1860_, v_userName_1846_, v_a_1854_, v_val_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
return v___x_1861_;
}
else
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
lean_dec(v___x_1857_);
lean_dec(v_a_1854_);
lean_dec_ref(v_val_1847_);
lean_dec(v_userName_1846_);
lean_dec(v_mvarId_1845_);
v_a_1862_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1858_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1858_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
lean_dec(v_a_1854_);
lean_dec_ref(v_val_1847_);
lean_dec(v_userName_1846_);
lean_dec(v_mvarId_1845_);
v_a_1870_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1855_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1855_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertAfter_x27___lam__0___boxed(lean_object* v_type_1878_, lean_object* v_fvarId_1879_, lean_object* v_mvarId_1880_, lean_object* v_userName_1881_, lean_object* v_val_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l_Lean_MVarId_assertAfter_x27___lam__0(v_type_1878_, v_fvarId_1879_, v_mvarId_1880_, v_userName_1881_, v_val_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertAfter_x27(lean_object* v_mvarId_1889_, lean_object* v_fvarId_1890_, lean_object* v_userName_1891_, lean_object* v_type_1892_, lean_object* v_val_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_){
_start:
{
lean_object* v___f_1899_; lean_object* v___x_1900_; 
lean_inc(v_mvarId_1889_);
v___f_1899_ = lean_alloc_closure((void*)(l_Lean_MVarId_assertAfter_x27___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1899_, 0, v_type_1892_);
lean_closure_set(v___f_1899_, 1, v_fvarId_1890_);
lean_closure_set(v___f_1899_, 2, v_mvarId_1889_);
lean_closure_set(v___f_1899_, 3, v_userName_1891_);
lean_closure_set(v___f_1899_, 4, v_val_1893_);
v___x_1900_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(v_mvarId_1889_, v___f_1899_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertAfter_x27___boxed(lean_object* v_mvarId_1901_, lean_object* v_fvarId_1902_, lean_object* v_userName_1903_, lean_object* v_type_1904_, lean_object* v_val_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l_Lean_MVarId_assertAfter_x27(v_mvarId_1901_, v_fvarId_1902_, v_userName_1903_, v_type_1904_, v_val_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_);
lean_dec(v_a_1909_);
lean_dec_ref(v_a_1908_);
lean_dec(v_a_1907_);
lean_dec_ref(v_a_1906_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg(lean_object* v_mvarId_1912_, lean_object* v_f_1913_, lean_object* v___y_1914_){
_start:
{
lean_object* v___x_1916_; lean_object* v_mctx_1917_; lean_object* v_cache_1918_; lean_object* v_zetaDeltaFVarIds_1919_; lean_object* v_postponed_1920_; lean_object* v_diag_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1932_; 
v___x_1916_ = lean_st_ref_take(v___y_1914_);
v_mctx_1917_ = lean_ctor_get(v___x_1916_, 0);
v_cache_1918_ = lean_ctor_get(v___x_1916_, 1);
v_zetaDeltaFVarIds_1919_ = lean_ctor_get(v___x_1916_, 2);
v_postponed_1920_ = lean_ctor_get(v___x_1916_, 3);
v_diag_1921_ = lean_ctor_get(v___x_1916_, 4);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1923_ = v___x_1916_;
v_isShared_1924_ = v_isSharedCheck_1932_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_diag_1921_);
lean_inc(v_postponed_1920_);
lean_inc(v_zetaDeltaFVarIds_1919_);
lean_inc(v_cache_1918_);
lean_inc(v_mctx_1917_);
lean_dec(v___x_1916_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1932_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1925_; lean_object* v___x_1927_; 
v___x_1925_ = l_Lean_MetavarContext_modifyExprMVarLCtx(v_mctx_1917_, v_mvarId_1912_, v_f_1913_);
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 0, v___x_1925_);
v___x_1927_ = v___x_1923_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1925_);
lean_ctor_set(v_reuseFailAlloc_1931_, 1, v_cache_1918_);
lean_ctor_set(v_reuseFailAlloc_1931_, 2, v_zetaDeltaFVarIds_1919_);
lean_ctor_set(v_reuseFailAlloc_1931_, 3, v_postponed_1920_);
lean_ctor_set(v_reuseFailAlloc_1931_, 4, v_diag_1921_);
v___x_1927_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1928_ = lean_st_ref_put(v___y_1914_, v___x_1927_);
v___x_1929_ = lean_box(0);
v___x_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1929_);
return v___x_1930_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg___boxed(lean_object* v_mvarId_1933_, lean_object* v_f_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg(v_mvarId_1933_, v_f_1934_, v___y_1935_);
lean_dec(v___y_1935_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1(lean_object* v_mvarId_1938_, lean_object* v_f_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg(v_mvarId_1938_, v_f_1939_, v___y_1941_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___boxed(lean_object* v_mvarId_1946_, lean_object* v_f_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_){
_start:
{
lean_object* v_res_1953_; 
v_res_1953_ = l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1(v_mvarId_1946_, v_f_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
return v_res_1953_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg(lean_object* v_upperBound_1954_, lean_object* v_hs_1955_, lean_object* v_fst_1956_, lean_object* v___x_1957_, lean_object* v_a_1958_, lean_object* v_b_1959_){
_start:
{
lean_object* v_a_1961_; uint8_t v___x_1965_; 
v___x_1965_ = lean_nat_dec_lt(v_a_1958_, v_upperBound_1954_);
if (v___x_1965_ == 0)
{
lean_dec(v_a_1958_);
return v_b_1959_;
}
else
{
lean_object* v___x_1966_; uint8_t v_kind_1967_; uint8_t v___x_1972_; uint8_t v___x_1973_; 
v___x_1966_ = lean_array_fget_borrowed(v_hs_1955_, v_a_1958_);
v_kind_1967_ = lean_ctor_get_uint8(v___x_1966_, sizeof(void*)*3 + 1);
v___x_1972_ = 0;
v___x_1973_ = l_Lean_instDecidableEqLocalDeclKind(v_kind_1967_, v___x_1972_);
if (v___x_1973_ == 0)
{
goto v___jp_1968_;
}
else
{
lean_object* v___x_1974_; uint8_t v___x_1975_; 
v___x_1974_ = lean_unsigned_to_nat(0u);
v___x_1975_ = lean_nat_dec_eq(v___x_1957_, v___x_1974_);
if (v___x_1975_ == 0)
{
v_a_1961_ = v_b_1959_;
goto v___jp_1960_;
}
else
{
goto v___jp_1968_;
}
}
v___jp_1968_:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1969_ = lean_box(0);
v___x_1970_ = lean_array_get_borrowed(v___x_1969_, v_fst_1956_, v_a_1958_);
lean_inc(v___x_1970_);
v___x_1971_ = l_Lean_LocalContext_setKind(v_b_1959_, v___x_1970_, v_kind_1967_);
v_a_1961_ = v___x_1971_;
goto v___jp_1960_;
}
}
v___jp_1960_:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1962_ = lean_unsigned_to_nat(1u);
v___x_1963_ = lean_nat_add(v_a_1958_, v___x_1962_);
lean_dec(v_a_1958_);
v_a_1958_ = v___x_1963_;
v_b_1959_ = v_a_1961_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg___boxed(lean_object* v_upperBound_1976_, lean_object* v_hs_1977_, lean_object* v_fst_1978_, lean_object* v___x_1979_, lean_object* v_a_1980_, lean_object* v_b_1981_){
_start:
{
lean_object* v_res_1982_; 
v_res_1982_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg(v_upperBound_1976_, v_hs_1977_, v_fst_1978_, v___x_1979_, v_a_1980_, v_b_1981_);
lean_dec(v___x_1979_);
lean_dec_ref(v_fst_1978_);
lean_dec_ref(v_hs_1977_);
lean_dec(v_upperBound_1976_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___lam__0(lean_object* v___x_1983_, lean_object* v_hs_1984_, lean_object* v_fst_1985_, lean_object* v___x_1986_, lean_object* v_lctx_1987_){
_start:
{
lean_object* v___x_1988_; 
v___x_1988_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg(v___x_1983_, v_hs_1984_, v_fst_1985_, v___x_1983_, v___x_1986_, v_lctx_1987_);
return v___x_1988_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___lam__0___boxed(lean_object* v___x_1989_, lean_object* v_hs_1990_, lean_object* v_fst_1991_, lean_object* v___x_1992_, lean_object* v_lctx_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = l_Lean_MVarId_assertHypotheses___lam__0(v___x_1989_, v_hs_1990_, v_fst_1991_, v___x_1992_, v_lctx_1993_);
lean_dec_ref(v_fst_1991_);
lean_dec_ref(v_hs_1990_);
lean_dec(v___x_1989_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__3(lean_object* v_as_1995_, size_t v_i_1996_, size_t v_stop_1997_, lean_object* v_b_1998_){
_start:
{
uint8_t v___x_1999_; 
v___x_1999_ = lean_usize_dec_eq(v_i_1996_, v_stop_1997_);
if (v___x_1999_ == 0)
{
size_t v___x_2000_; size_t v___x_2001_; lean_object* v___x_2002_; lean_object* v_userName_2003_; lean_object* v_type_2004_; uint8_t v_binderInfo_2005_; lean_object* v___x_2006_; 
v___x_2000_ = ((size_t)1ULL);
v___x_2001_ = lean_usize_sub(v_i_1996_, v___x_2000_);
v___x_2002_ = lean_array_uget_borrowed(v_as_1995_, v___x_2001_);
v_userName_2003_ = lean_ctor_get(v___x_2002_, 0);
v_type_2004_ = lean_ctor_get(v___x_2002_, 1);
v_binderInfo_2005_ = lean_ctor_get_uint8(v___x_2002_, sizeof(void*)*3);
lean_inc_ref(v_type_2004_);
lean_inc(v_userName_2003_);
v___x_2006_ = l_Lean_Expr_forallE___override(v_userName_2003_, v_type_2004_, v_b_1998_, v_binderInfo_2005_);
v_i_1996_ = v___x_2001_;
v_b_1998_ = v___x_2006_;
goto _start;
}
else
{
return v_b_1998_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__3___boxed(lean_object* v_as_2008_, lean_object* v_i_2009_, lean_object* v_stop_2010_, lean_object* v_b_2011_){
_start:
{
size_t v_i_boxed_2012_; size_t v_stop_boxed_2013_; lean_object* v_res_2014_; 
v_i_boxed_2012_ = lean_unbox_usize(v_i_2009_);
lean_dec(v_i_2009_);
v_stop_boxed_2013_ = lean_unbox_usize(v_stop_2010_);
lean_dec(v_stop_2010_);
v_res_2014_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__3(v_as_2008_, v_i_boxed_2012_, v_stop_boxed_2013_, v_b_2011_);
lean_dec_ref(v_as_2008_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2(lean_object* v_as_2015_, size_t v_i_2016_, size_t v_stop_2017_, lean_object* v_b_2018_){
_start:
{
uint8_t v___x_2019_; 
v___x_2019_ = lean_usize_dec_eq(v_i_2016_, v_stop_2017_);
if (v___x_2019_ == 0)
{
lean_object* v___x_2020_; lean_object* v_value_2021_; lean_object* v___x_2022_; size_t v___x_2023_; size_t v___x_2024_; 
v___x_2020_ = lean_array_uget_borrowed(v_as_2015_, v_i_2016_);
v_value_2021_ = lean_ctor_get(v___x_2020_, 2);
lean_inc_ref(v_value_2021_);
v___x_2022_ = l_Lean_Expr_app___override(v_b_2018_, v_value_2021_);
v___x_2023_ = ((size_t)1ULL);
v___x_2024_ = lean_usize_add(v_i_2016_, v___x_2023_);
v_i_2016_ = v___x_2024_;
v_b_2018_ = v___x_2022_;
goto _start;
}
else
{
return v_b_2018_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2___boxed(lean_object* v_as_2026_, lean_object* v_i_2027_, lean_object* v_stop_2028_, lean_object* v_b_2029_){
_start:
{
size_t v_i_boxed_2030_; size_t v_stop_boxed_2031_; lean_object* v_res_2032_; 
v_i_boxed_2030_ = lean_unbox_usize(v_i_2027_);
lean_dec(v_i_2027_);
v_stop_boxed_2031_ = lean_unbox_usize(v_stop_2028_);
lean_dec(v_stop_2028_);
v_res_2032_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2(v_as_2026_, v_i_boxed_2030_, v_stop_boxed_2031_, v_b_2029_);
lean_dec_ref(v_as_2026_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___lam__1(lean_object* v_mvarId_2033_, lean_object* v___x_2034_, lean_object* v___x_2035_, uint8_t v___x_2036_, lean_object* v_hs_2037_, lean_object* v___x_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___x_2065_; 
lean_inc(v_mvarId_2033_);
v___x_2065_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2033_, v___x_2034_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v___x_2066_; 
lean_dec_ref_known(v___x_2065_, 1);
lean_inc(v_mvarId_2033_);
v___x_2066_ = l_Lean_MVarId_getTag(v_mvarId_2033_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2067_; lean_object* v___x_2068_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
lean_inc(v_a_2067_);
lean_dec_ref_known(v___x_2066_, 1);
lean_inc(v_mvarId_2033_);
v___x_2068_ = l_Lean_MVarId_getType(v_mvarId_2033_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_object* v_a_2069_; lean_object* v___y_2071_; uint8_t v___x_2090_; 
v_a_2069_ = lean_ctor_get(v___x_2068_, 0);
lean_inc(v_a_2069_);
lean_dec_ref_known(v___x_2068_, 1);
v___x_2090_ = lean_nat_dec_lt(v___x_2038_, v___x_2035_);
if (v___x_2090_ == 0)
{
v___y_2071_ = v_a_2069_;
goto v___jp_2070_;
}
else
{
size_t v___x_2091_; size_t v___x_2092_; lean_object* v___x_2093_; 
v___x_2091_ = lean_usize_of_nat(v___x_2035_);
v___x_2092_ = ((size_t)0ULL);
v___x_2093_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__3(v_hs_2037_, v___x_2091_, v___x_2092_, v_a_2069_);
v___y_2071_ = v___x_2093_;
goto v___jp_2070_;
}
v___jp_2070_:
{
lean_object* v___x_2072_; 
v___x_2072_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_2071_, v_a_2067_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v_a_2073_; uint8_t v___x_2074_; 
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
lean_inc(v_a_2073_);
lean_dec_ref_known(v___x_2072_, 1);
v___x_2074_ = lean_nat_dec_lt(v___x_2038_, v___x_2035_);
if (v___x_2074_ == 0)
{
lean_inc(v_a_2073_);
v___y_2045_ = v_a_2073_;
v___y_2046_ = v_a_2073_;
goto v___jp_2044_;
}
else
{
uint8_t v___x_2075_; 
v___x_2075_ = lean_nat_dec_le(v___x_2035_, v___x_2035_);
if (v___x_2075_ == 0)
{
if (v___x_2074_ == 0)
{
lean_inc(v_a_2073_);
v___y_2045_ = v_a_2073_;
v___y_2046_ = v_a_2073_;
goto v___jp_2044_;
}
else
{
size_t v___x_2076_; size_t v___x_2077_; lean_object* v___x_2078_; 
v___x_2076_ = ((size_t)0ULL);
v___x_2077_ = lean_usize_of_nat(v___x_2035_);
lean_inc(v_a_2073_);
v___x_2078_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2(v_hs_2037_, v___x_2076_, v___x_2077_, v_a_2073_);
v___y_2045_ = v_a_2073_;
v___y_2046_ = v___x_2078_;
goto v___jp_2044_;
}
}
else
{
size_t v___x_2079_; size_t v___x_2080_; lean_object* v___x_2081_; 
v___x_2079_ = ((size_t)0ULL);
v___x_2080_ = lean_usize_of_nat(v___x_2035_);
lean_inc(v_a_2073_);
v___x_2081_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2(v_hs_2037_, v___x_2079_, v___x_2080_, v_a_2073_);
v___y_2045_ = v_a_2073_;
v___y_2046_ = v___x_2081_;
goto v___jp_2044_;
}
}
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
lean_dec(v___x_2038_);
lean_dec_ref(v_hs_2037_);
lean_dec(v___x_2035_);
lean_dec(v_mvarId_2033_);
v_a_2082_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2072_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2072_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
}
else
{
lean_object* v_a_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2101_; 
lean_dec(v_a_2067_);
lean_dec(v___x_2038_);
lean_dec_ref(v_hs_2037_);
lean_dec(v___x_2035_);
lean_dec(v_mvarId_2033_);
v_a_2094_ = lean_ctor_get(v___x_2068_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2096_ = v___x_2068_;
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_a_2094_);
lean_dec(v___x_2068_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2099_; 
if (v_isShared_2097_ == 0)
{
v___x_2099_ = v___x_2096_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_a_2094_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
}
else
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2109_; 
lean_dec(v___x_2038_);
lean_dec_ref(v_hs_2037_);
lean_dec(v___x_2035_);
lean_dec(v_mvarId_2033_);
v_a_2102_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2104_ = v___x_2066_;
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2066_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2105_ == 0)
{
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_a_2102_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
else
{
lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2117_; 
lean_dec(v___x_2038_);
lean_dec_ref(v_hs_2037_);
lean_dec(v___x_2035_);
lean_dec(v_mvarId_2033_);
v_a_2110_ = lean_ctor_get(v___x_2065_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2112_ = v___x_2065_;
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_2065_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2115_; 
if (v_isShared_2113_ == 0)
{
v___x_2115_ = v___x_2112_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_a_2110_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
v___jp_2044_:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; uint8_t v___x_2050_; lean_object* v___x_2051_; 
v___x_2047_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(v_mvarId_2033_, v___y_2046_, v___y_2040_);
lean_dec_ref(v___x_2047_);
v___x_2048_ = l_Lean_Expr_mvarId_x21(v___y_2045_);
lean_dec_ref(v___y_2045_);
v___x_2049_ = lean_box(0);
v___x_2050_ = 1;
lean_inc(v___x_2035_);
v___x_2051_ = l_Lean_Meta_introNCore(v___x_2048_, v___x_2035_, v___x_2049_, v___x_2036_, v___x_2050_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; lean_object* v_fst_2053_; lean_object* v_snd_2054_; lean_object* v___f_2055_; lean_object* v___x_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_a_2052_);
lean_dec_ref_known(v___x_2051_, 1);
v_fst_2053_ = lean_ctor_get(v_a_2052_, 0);
v_snd_2054_ = lean_ctor_get(v_a_2052_, 1);
lean_inc(v_fst_2053_);
v___f_2055_ = lean_alloc_closure((void*)(l_Lean_MVarId_assertHypotheses___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2055_, 0, v___x_2035_);
lean_closure_set(v___f_2055_, 1, v_hs_2037_);
lean_closure_set(v___f_2055_, 2, v_fst_2053_);
lean_closure_set(v___f_2055_, 3, v___x_2038_);
lean_inc(v_snd_2054_);
v___x_2056_ = l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg(v_snd_2054_, v___f_2055_, v___y_2040_);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2063_ == 0)
{
lean_object* v_unused_2064_; 
v_unused_2064_ = lean_ctor_get(v___x_2056_, 0);
lean_dec(v_unused_2064_);
v___x_2058_ = v___x_2056_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_dec(v___x_2056_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2061_; 
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 0, v_a_2052_);
v___x_2061_ = v___x_2058_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2052_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
else
{
lean_dec(v___x_2038_);
lean_dec_ref(v_hs_2037_);
lean_dec(v___x_2035_);
return v___x_2051_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___lam__1___boxed(lean_object* v_mvarId_2118_, lean_object* v___x_2119_, lean_object* v___x_2120_, lean_object* v___x_2121_, lean_object* v_hs_2122_, lean_object* v___x_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
uint8_t v___x_3359__boxed_2129_; lean_object* v_res_2130_; 
v___x_3359__boxed_2129_ = lean_unbox(v___x_2121_);
v_res_2130_ = l_Lean_MVarId_assertHypotheses___lam__1(v_mvarId_2118_, v___x_2119_, v___x_2120_, v___x_3359__boxed_2129_, v_hs_2122_, v___x_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses(lean_object* v_mvarId_2136_, lean_object* v_hs_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_){
_start:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; uint8_t v___x_2145_; 
v___x_2143_ = lean_array_get_size(v_hs_2137_);
v___x_2144_ = lean_unsigned_to_nat(0u);
v___x_2145_ = lean_nat_dec_eq(v___x_2143_, v___x_2144_);
if (v___x_2145_ == 0)
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___f_2148_; lean_object* v___x_2149_; 
v___x_2146_ = ((lean_object*)(l_Lean_MVarId_assertHypotheses___closed__1));
v___x_2147_ = lean_box(v___x_2145_);
lean_inc(v_mvarId_2136_);
v___f_2148_ = lean_alloc_closure((void*)(l_Lean_MVarId_assertHypotheses___lam__1___boxed), 11, 6);
lean_closure_set(v___f_2148_, 0, v_mvarId_2136_);
lean_closure_set(v___f_2148_, 1, v___x_2146_);
lean_closure_set(v___f_2148_, 2, v___x_2143_);
lean_closure_set(v___f_2148_, 3, v___x_2147_);
lean_closure_set(v___f_2148_, 4, v_hs_2137_);
lean_closure_set(v___f_2148_, 5, v___x_2144_);
v___x_2149_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(v_mvarId_2136_, v___f_2148_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
return v___x_2149_;
}
else
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
lean_dec_ref(v_hs_2137_);
v___x_2150_ = ((lean_object*)(l_Lean_MVarId_assertHypotheses___closed__2));
v___x_2151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2150_);
lean_ctor_set(v___x_2151_, 1, v_mvarId_2136_);
v___x_2152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2151_);
return v___x_2152_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___boxed(lean_object* v_mvarId_2153_, lean_object* v_hs_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_){
_start:
{
lean_object* v_res_2160_; 
v_res_2160_ = l_Lean_MVarId_assertHypotheses(v_mvarId_2153_, v_hs_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_);
lean_dec(v_a_2158_);
lean_dec_ref(v_a_2157_);
lean_dec(v_a_2156_);
lean_dec_ref(v_a_2155_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0(lean_object* v_upperBound_2161_, lean_object* v_hs_2162_, lean_object* v_fst_2163_, lean_object* v___x_2164_, lean_object* v_inst_2165_, lean_object* v_R_2166_, lean_object* v_a_2167_, lean_object* v_b_2168_, lean_object* v_c_2169_){
_start:
{
lean_object* v___x_2170_; 
v___x_2170_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg(v_upperBound_2161_, v_hs_2162_, v_fst_2163_, v___x_2164_, v_a_2167_, v_b_2168_);
return v___x_2170_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___boxed(lean_object* v_upperBound_2171_, lean_object* v_hs_2172_, lean_object* v_fst_2173_, lean_object* v___x_2174_, lean_object* v_inst_2175_, lean_object* v_R_2176_, lean_object* v_a_2177_, lean_object* v_b_2178_, lean_object* v_c_2179_){
_start:
{
lean_object* v_res_2180_; 
v_res_2180_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0(v_upperBound_2171_, v_hs_2172_, v_fst_2173_, v___x_2174_, v_inst_2175_, v_R_2176_, v_a_2177_, v_b_2178_, v_c_2179_);
lean_dec(v___x_2174_);
lean_dec_ref(v_fst_2173_);
lean_dec_ref(v_hs_2172_);
lean_dec(v_upperBound_2171_);
return v_res_2180_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_FVarSubst(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Intro(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Revert(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_InfoTree_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_ForEachExpr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Assert(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
