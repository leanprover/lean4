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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDeclKind_ctorIdx(uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_setKind(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MetavarContext_modifyExprMVarLCtx(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg();
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
static const lean_closure_object l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__2;
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
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_assertHypotheses___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "assertHypotheses"};
static const lean_object* l_Lean_MVarId_assertHypotheses___closed__0 = (const lean_object*)&l_Lean_MVarId_assertHypotheses___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_assertHypotheses___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_assertHypotheses___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 34, 150, 130, 103, 166, 191, 222)}};
static const lean_object* l_Lean_MVarId_assertHypotheses___closed__1 = (const lean_object*)&l_Lean_MVarId_assertHypotheses___closed__1_value;
static const lean_array_object l_Lean_MVarId_assertHypotheses___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_MVarId_assertHypotheses___closed__2 = (const lean_object*)&l_Lean_MVarId_assertHypotheses___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_86_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
lean_object* v_ks_138_; lean_object* v_vs_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_157_; 
v_ks_138_ = lean_ctor_get(v_x_87_, 0);
v_vs_139_ = lean_ctor_get(v_x_87_, 1);
v_isSharedCheck_157_ = !lean_is_exclusive(v_x_87_);
if (v_isSharedCheck_157_ == 0)
{
v___x_141_ = v_x_87_;
v_isShared_142_ = v_isSharedCheck_157_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_vs_139_);
lean_inc(v_ks_138_);
lean_dec(v_x_87_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_157_;
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
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_ks_138_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_vs_139_);
v___x_144_ = v_reuseFailAlloc_156_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
lean_object* v_newNode_145_; size_t v___x_146_; uint8_t v___x_147_; 
v_newNode_145_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3___redArg(v___x_144_, v_x_90_, v_x_91_);
v___x_146_ = ((size_t)7ULL);
v___x_147_ = lean_usize_dec_le(v___x_146_, v_x_89_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_148_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_145_);
v___x_149_ = lean_unsigned_to_nat(4u);
v___x_150_ = lean_nat_dec_lt(v___x_148_, v___x_149_);
lean_dec(v___x_148_);
if (v___x_150_ == 0)
{
lean_object* v_ks_151_; lean_object* v_vs_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v_ks_151_ = lean_ctor_get(v_newNode_145_, 0);
lean_inc_ref(v_ks_151_);
v_vs_152_ = lean_ctor_get(v_newNode_145_, 1);
lean_inc_ref(v_vs_152_);
lean_dec_ref(v_newNode_145_);
v___x_153_ = lean_unsigned_to_nat(0u);
v___x_154_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_155_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg(v_x_89_, v_ks_151_, v_vs_152_, v___x_153_, v___x_154_);
lean_dec_ref(v_vs_152_);
lean_dec_ref(v_ks_151_);
return v___x_155_;
}
else
{
return v_newNode_145_;
}
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg(size_t v_depth_158_, lean_object* v_keys_159_, lean_object* v_vals_160_, lean_object* v_i_161_, lean_object* v_entries_162_){
_start:
{
lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_163_ = lean_array_get_size(v_keys_159_);
v___x_164_ = lean_nat_dec_lt(v_i_161_, v___x_163_);
if (v___x_164_ == 0)
{
lean_dec(v_i_161_);
return v_entries_162_;
}
else
{
lean_object* v_k_165_; lean_object* v_v_166_; uint64_t v___x_167_; size_t v_h_168_; size_t v___x_169_; lean_object* v___x_170_; size_t v___x_171_; size_t v___x_172_; size_t v___x_173_; size_t v_h_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v_k_165_ = lean_array_fget_borrowed(v_keys_159_, v_i_161_);
v_v_166_ = lean_array_fget_borrowed(v_vals_160_, v_i_161_);
v___x_167_ = l_Lean_instHashableMVarId_hash(v_k_165_);
v_h_168_ = lean_uint64_to_usize(v___x_167_);
v___x_169_ = ((size_t)5ULL);
v___x_170_ = lean_unsigned_to_nat(1u);
v___x_171_ = ((size_t)1ULL);
v___x_172_ = lean_usize_sub(v_depth_158_, v___x_171_);
v___x_173_ = lean_usize_mul(v___x_169_, v___x_172_);
v_h_174_ = lean_usize_shift_right(v_h_168_, v___x_173_);
v___x_175_ = lean_nat_add(v_i_161_, v___x_170_);
lean_dec(v_i_161_);
lean_inc(v_v_166_);
lean_inc(v_k_165_);
v___x_176_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(v_entries_162_, v_h_174_, v_depth_158_, v_k_165_, v_v_166_);
v_i_161_ = v___x_175_;
v_entries_162_ = v___x_176_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_depth_178_, lean_object* v_keys_179_, lean_object* v_vals_180_, lean_object* v_i_181_, lean_object* v_entries_182_){
_start:
{
size_t v_depth_boxed_183_; lean_object* v_res_184_; 
v_depth_boxed_183_ = lean_unbox_usize(v_depth_178_);
lean_dec(v_depth_178_);
v_res_184_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_183_, v_keys_179_, v_vals_180_, v_i_181_, v_entries_182_);
lean_dec_ref(v_vals_180_);
lean_dec_ref(v_keys_179_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_185_, lean_object* v_x_186_, lean_object* v_x_187_, lean_object* v_x_188_, lean_object* v_x_189_){
_start:
{
size_t v_x_1320__boxed_190_; size_t v_x_1321__boxed_191_; lean_object* v_res_192_; 
v_x_1320__boxed_190_ = lean_unbox_usize(v_x_186_);
lean_dec(v_x_186_);
v_x_1321__boxed_191_ = lean_unbox_usize(v_x_187_);
lean_dec(v_x_187_);
v_res_192_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(v_x_185_, v_x_1320__boxed_190_, v_x_1321__boxed_191_, v_x_188_, v_x_189_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0___redArg(lean_object* v_x_193_, lean_object* v_x_194_, lean_object* v_x_195_){
_start:
{
uint64_t v___x_196_; size_t v___x_197_; size_t v___x_198_; lean_object* v___x_199_; 
v___x_196_ = l_Lean_instHashableMVarId_hash(v_x_194_);
v___x_197_ = lean_uint64_to_usize(v___x_196_);
v___x_198_ = ((size_t)1ULL);
v___x_199_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(v_x_193_, v___x_197_, v___x_198_, v_x_194_, v_x_195_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(lean_object* v_mvarId_200_, lean_object* v_val_201_, lean_object* v___y_202_){
_start:
{
lean_object* v___x_204_; lean_object* v_mctx_205_; lean_object* v_cache_206_; lean_object* v_zetaDeltaFVarIds_207_; lean_object* v_postponed_208_; lean_object* v_diag_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_238_; 
v___x_204_ = lean_st_ref_take(v___y_202_);
v_mctx_205_ = lean_ctor_get(v___x_204_, 0);
v_cache_206_ = lean_ctor_get(v___x_204_, 1);
v_zetaDeltaFVarIds_207_ = lean_ctor_get(v___x_204_, 2);
v_postponed_208_ = lean_ctor_get(v___x_204_, 3);
v_diag_209_ = lean_ctor_get(v___x_204_, 4);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_238_ == 0)
{
v___x_211_ = v___x_204_;
v_isShared_212_ = v_isSharedCheck_238_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_diag_209_);
lean_inc(v_postponed_208_);
lean_inc(v_zetaDeltaFVarIds_207_);
lean_inc(v_cache_206_);
lean_inc(v_mctx_205_);
lean_dec(v___x_204_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_238_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v_depth_213_; lean_object* v_levelAssignDepth_214_; lean_object* v_lmvarCounter_215_; lean_object* v_mvarCounter_216_; lean_object* v_lDecls_217_; lean_object* v_decls_218_; lean_object* v_userNames_219_; lean_object* v_lAssignment_220_; lean_object* v_eAssignment_221_; lean_object* v_dAssignment_222_; lean_object* v_instanceTypedMVars_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_237_; 
v_depth_213_ = lean_ctor_get(v_mctx_205_, 0);
v_levelAssignDepth_214_ = lean_ctor_get(v_mctx_205_, 1);
v_lmvarCounter_215_ = lean_ctor_get(v_mctx_205_, 2);
v_mvarCounter_216_ = lean_ctor_get(v_mctx_205_, 3);
v_lDecls_217_ = lean_ctor_get(v_mctx_205_, 4);
v_decls_218_ = lean_ctor_get(v_mctx_205_, 5);
v_userNames_219_ = lean_ctor_get(v_mctx_205_, 6);
v_lAssignment_220_ = lean_ctor_get(v_mctx_205_, 7);
v_eAssignment_221_ = lean_ctor_get(v_mctx_205_, 8);
v_dAssignment_222_ = lean_ctor_get(v_mctx_205_, 9);
v_instanceTypedMVars_223_ = lean_ctor_get(v_mctx_205_, 10);
v_isSharedCheck_237_ = !lean_is_exclusive(v_mctx_205_);
if (v_isSharedCheck_237_ == 0)
{
v___x_225_ = v_mctx_205_;
v_isShared_226_ = v_isSharedCheck_237_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_instanceTypedMVars_223_);
lean_inc(v_dAssignment_222_);
lean_inc(v_eAssignment_221_);
lean_inc(v_lAssignment_220_);
lean_inc(v_userNames_219_);
lean_inc(v_decls_218_);
lean_inc(v_lDecls_217_);
lean_inc(v_mvarCounter_216_);
lean_inc(v_lmvarCounter_215_);
lean_inc(v_levelAssignDepth_214_);
lean_inc(v_depth_213_);
lean_dec(v_mctx_205_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_237_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_230_; 
v___x_227_ = lean_box(0);
v___x_228_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0___redArg(v_eAssignment_221_, v_mvarId_200_, v_val_201_);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 8, v___x_228_);
v___x_230_ = v___x_225_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_depth_213_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v_levelAssignDepth_214_);
lean_ctor_set(v_reuseFailAlloc_236_, 2, v_lmvarCounter_215_);
lean_ctor_set(v_reuseFailAlloc_236_, 3, v_mvarCounter_216_);
lean_ctor_set(v_reuseFailAlloc_236_, 4, v_lDecls_217_);
lean_ctor_set(v_reuseFailAlloc_236_, 5, v_decls_218_);
lean_ctor_set(v_reuseFailAlloc_236_, 6, v_userNames_219_);
lean_ctor_set(v_reuseFailAlloc_236_, 7, v_lAssignment_220_);
lean_ctor_set(v_reuseFailAlloc_236_, 8, v___x_228_);
lean_ctor_set(v_reuseFailAlloc_236_, 9, v_dAssignment_222_);
lean_ctor_set(v_reuseFailAlloc_236_, 10, v_instanceTypedMVars_223_);
v___x_230_ = v_reuseFailAlloc_236_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
lean_object* v___x_232_; 
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 0, v___x_230_);
v___x_232_ = v___x_211_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_230_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v_cache_206_);
lean_ctor_set(v_reuseFailAlloc_235_, 2, v_zetaDeltaFVarIds_207_);
lean_ctor_set(v_reuseFailAlloc_235_, 3, v_postponed_208_);
lean_ctor_set(v_reuseFailAlloc_235_, 4, v_diag_209_);
v___x_232_ = v_reuseFailAlloc_235_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = lean_st_ref_put(v___y_202_, v___x_232_);
v___x_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_227_);
return v___x_234_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg___boxed(lean_object* v_mvarId_239_, lean_object* v_val_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(v_mvarId_239_, v_val_240_, v___y_241_);
lean_dec(v___y_241_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assert___lam__0(lean_object* v_mvarId_244_, lean_object* v___x_245_, lean_object* v_name_246_, lean_object* v_type_247_, lean_object* v_val_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v___x_254_; 
lean_inc(v_mvarId_244_);
v___x_254_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_244_, v___x_245_, v___y_249_, v___y_250_, v___y_251_, v___y_252_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v___x_255_; 
lean_dec_ref_known(v___x_254_, 1);
lean_inc(v_mvarId_244_);
v___x_255_ = l_Lean_MVarId_getTag(v_mvarId_244_, v___y_249_, v___y_250_, v___y_251_, v___y_252_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v_a_256_; lean_object* v___x_257_; 
v_a_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_a_256_);
lean_dec_ref_known(v___x_255_, 1);
lean_inc(v_mvarId_244_);
v___x_257_ = l_Lean_MVarId_getType(v_mvarId_244_, v___y_249_, v___y_250_, v___y_251_, v___y_252_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v_a_258_; uint8_t v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v_a_258_ = lean_ctor_get(v___x_257_, 0);
lean_inc(v_a_258_);
lean_dec_ref_known(v___x_257_, 1);
v___x_259_ = 0;
v___x_260_ = l_Lean_mkForall(v_name_246_, v___x_259_, v_type_247_, v_a_258_);
v___x_261_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_260_, v_a_256_, v___y_249_, v___y_250_, v___y_251_, v___y_252_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_a_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_272_; 
v_a_262_ = lean_ctor_get(v___x_261_, 0);
lean_inc_n(v_a_262_, 2);
lean_dec_ref_known(v___x_261_, 1);
v___x_263_ = l_Lean_Expr_app___override(v_a_262_, v_val_248_);
v___x_264_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(v_mvarId_244_, v___x_263_, v___y_250_);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_272_ == 0)
{
lean_object* v_unused_273_; 
v_unused_273_ = lean_ctor_get(v___x_264_, 0);
lean_dec(v_unused_273_);
v___x_266_ = v___x_264_;
v_isShared_267_ = v_isSharedCheck_272_;
goto v_resetjp_265_;
}
else
{
lean_dec(v___x_264_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_272_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_268_; lean_object* v___x_270_; 
v___x_268_ = l_Lean_Expr_mvarId_x21(v_a_262_);
lean_dec(v_a_262_);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 0, v___x_268_);
v___x_270_ = v___x_266_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_268_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
else
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_281_; 
lean_dec_ref(v_val_248_);
lean_dec(v_mvarId_244_);
v_a_274_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_281_ == 0)
{
v___x_276_ = v___x_261_;
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_261_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
if (v_isShared_277_ == 0)
{
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_274_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
else
{
lean_object* v_a_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_289_; 
lean_dec(v_a_256_);
lean_dec_ref(v_val_248_);
lean_dec_ref(v_type_247_);
lean_dec(v_name_246_);
lean_dec(v_mvarId_244_);
v_a_282_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_289_ == 0)
{
v___x_284_ = v___x_257_;
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_a_282_);
lean_dec(v___x_257_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_287_; 
if (v_isShared_285_ == 0)
{
v___x_287_ = v___x_284_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_a_282_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
else
{
lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_297_; 
lean_dec_ref(v_val_248_);
lean_dec_ref(v_type_247_);
lean_dec(v_name_246_);
lean_dec(v_mvarId_244_);
v_a_290_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_297_ == 0)
{
v___x_292_ = v___x_255_;
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_dec(v___x_255_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_295_; 
if (v_isShared_293_ == 0)
{
v___x_295_ = v___x_292_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_a_290_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
else
{
lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_305_; 
lean_dec_ref(v_val_248_);
lean_dec_ref(v_type_247_);
lean_dec(v_name_246_);
lean_dec(v_mvarId_244_);
v_a_298_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_305_ == 0)
{
v___x_300_ = v___x_254_;
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_254_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_303_; 
if (v_isShared_301_ == 0)
{
v___x_303_ = v___x_300_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_a_298_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assert___lam__0___boxed(lean_object* v_mvarId_306_, lean_object* v___x_307_, lean_object* v_name_308_, lean_object* v_type_309_, lean_object* v_val_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Lean_MVarId_assert___lam__0(v_mvarId_306_, v___x_307_, v_name_308_, v_type_309_, v_val_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assert(lean_object* v_mvarId_320_, lean_object* v_name_321_, lean_object* v_type_322_, lean_object* v_val_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v___x_329_; lean_object* v___f_330_; lean_object* v___x_331_; 
v___x_329_ = ((lean_object*)(l_Lean_MVarId_assert___closed__1));
lean_inc(v_mvarId_320_);
v___f_330_ = lean_alloc_closure((void*)(l_Lean_MVarId_assert___lam__0___boxed), 10, 5);
lean_closure_set(v___f_330_, 0, v_mvarId_320_);
lean_closure_set(v___f_330_, 1, v___x_329_);
lean_closure_set(v___f_330_, 2, v_name_321_);
lean_closure_set(v___f_330_, 3, v_type_322_);
lean_closure_set(v___f_330_, 4, v_val_323_);
v___x_331_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(v_mvarId_320_, v___f_330_, v_a_324_, v_a_325_, v_a_326_, v_a_327_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assert___boxed(lean_object* v_mvarId_332_, lean_object* v_name_333_, lean_object* v_type_334_, lean_object* v_val_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_MVarId_assert(v_mvarId_332_, v_name_333_, v_type_334_, v_val_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0(lean_object* v_mvarId_342_, lean_object* v_val_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(v_mvarId_342_, v_val_343_, v___y_345_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___boxed(lean_object* v_mvarId_350_, lean_object* v_val_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0(v_mvarId_350_, v_val_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0(lean_object* v_00_u03b2_358_, lean_object* v_x_359_, lean_object* v_x_360_, lean_object* v_x_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0___redArg(v_x_359_, v_x_360_, v_x_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_363_, lean_object* v_x_364_, size_t v_x_365_, size_t v_x_366_, lean_object* v_x_367_, lean_object* v_x_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(v_x_364_, v_x_365_, v_x_366_, v_x_367_, v_x_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_370_, lean_object* v_x_371_, lean_object* v_x_372_, lean_object* v_x_373_, lean_object* v_x_374_, lean_object* v_x_375_){
_start:
{
size_t v_x_1698__boxed_376_; size_t v_x_1699__boxed_377_; lean_object* v_res_378_; 
v_x_1698__boxed_376_ = lean_unbox_usize(v_x_372_);
lean_dec(v_x_372_);
v_x_1699__boxed_377_ = lean_unbox_usize(v_x_373_);
lean_dec(v_x_373_);
v_res_378_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2(v_00_u03b2_370_, v_x_371_, v_x_1698__boxed_376_, v_x_1699__boxed_377_, v_x_374_, v_x_375_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_379_, lean_object* v_n_380_, lean_object* v_k_381_, lean_object* v_v_382_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3___redArg(v_n_380_, v_k_381_, v_v_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_384_, size_t v_depth_385_, lean_object* v_keys_386_, lean_object* v_vals_387_, lean_object* v_heq_388_, lean_object* v_i_389_, lean_object* v_entries_390_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_385_, v_keys_386_, v_vals_387_, v_i_389_, v_entries_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_392_, lean_object* v_depth_393_, lean_object* v_keys_394_, lean_object* v_vals_395_, lean_object* v_heq_396_, lean_object* v_i_397_, lean_object* v_entries_398_){
_start:
{
size_t v_depth_boxed_399_; lean_object* v_res_400_; 
v_depth_boxed_399_ = lean_unbox_usize(v_depth_393_);
lean_dec(v_depth_393_);
v_res_400_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_392_, v_depth_boxed_399_, v_keys_394_, v_vals_395_, v_heq_396_, v_i_397_, v_entries_398_);
lean_dec_ref(v_vals_395_);
lean_dec_ref(v_keys_394_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_401_, lean_object* v_x_402_, lean_object* v_x_403_, lean_object* v_x_404_, lean_object* v_x_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_402_, v_x_403_, v_x_404_, v_x_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_note(lean_object* v_g_407_, lean_object* v_h_408_, lean_object* v_v_409_, lean_object* v_t_x3f_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v_____do__lift_417_; lean_object* v___y_418_; lean_object* v___y_419_; lean_object* v___y_420_; lean_object* v___y_421_; 
if (lean_obj_tag(v_t_x3f_410_) == 0)
{
lean_object* v___x_434_; 
lean_inc(v_a_414_);
lean_inc_ref(v_a_413_);
lean_inc(v_a_412_);
lean_inc_ref(v_a_411_);
lean_inc_ref(v_v_409_);
v___x_434_ = lean_infer_type(v_v_409_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v_a_435_; 
v_a_435_ = lean_ctor_get(v___x_434_, 0);
lean_inc(v_a_435_);
lean_dec_ref_known(v___x_434_, 1);
v_____do__lift_417_ = v_a_435_;
v___y_418_ = v_a_411_;
v___y_419_ = v_a_412_;
v___y_420_ = v_a_413_;
v___y_421_ = v_a_414_;
goto v___jp_416_;
}
else
{
lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_443_; 
lean_dec_ref(v_v_409_);
lean_dec(v_h_408_);
lean_dec(v_g_407_);
v_a_436_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_443_ == 0)
{
v___x_438_ = v___x_434_;
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___x_434_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_441_; 
if (v_isShared_439_ == 0)
{
v___x_441_ = v___x_438_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_a_436_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
}
else
{
lean_object* v_val_444_; 
v_val_444_ = lean_ctor_get(v_t_x3f_410_, 0);
lean_inc(v_val_444_);
lean_dec_ref_known(v_t_x3f_410_, 1);
v_____do__lift_417_ = v_val_444_;
v___y_418_ = v_a_411_;
v___y_419_ = v_a_412_;
v___y_420_ = v_a_413_;
v___y_421_ = v_a_414_;
goto v___jp_416_;
}
v___jp_416_:
{
lean_object* v___x_422_; 
v___x_422_ = l_Lean_MVarId_assert(v_g_407_, v_h_408_, v_____do__lift_417_, v_v_409_, v___y_418_, v___y_419_, v___y_420_, v___y_421_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v_a_423_; uint8_t v___x_424_; lean_object* v___x_425_; 
v_a_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_a_423_);
lean_dec_ref_known(v___x_422_, 1);
v___x_424_ = 1;
v___x_425_ = l_Lean_Meta_intro1Core(v_a_423_, v___x_424_, v___y_418_, v___y_419_, v___y_420_, v___y_421_);
return v___x_425_;
}
else
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
v_a_426_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_433_ == 0)
{
v___x_428_ = v___x_422_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_422_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_a_426_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_note___boxed(lean_object* v_g_445_, lean_object* v_h_446_, lean_object* v_v_447_, lean_object* v_t_x3f_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_MVarId_note(v_g_445_, v_h_446_, v_v_447_, v_t_x3f_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_);
lean_dec(v_a_452_);
lean_dec_ref(v_a_451_);
lean_dec(v_a_450_);
lean_dec_ref(v_a_449_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_define___lam__0(lean_object* v_mvarId_455_, lean_object* v___x_456_, lean_object* v_name_457_, lean_object* v_type_458_, lean_object* v_val_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
lean_object* v___x_465_; 
lean_inc(v_mvarId_455_);
v___x_465_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_455_, v___x_456_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v___x_466_; 
lean_dec_ref_known(v___x_465_, 1);
lean_inc(v_mvarId_455_);
v___x_466_ = l_Lean_MVarId_getTag(v_mvarId_455_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v_a_467_; lean_object* v___x_468_; 
v_a_467_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_a_467_);
lean_dec_ref_known(v___x_466_, 1);
lean_inc(v_mvarId_455_);
v___x_468_ = l_Lean_MVarId_getType(v_mvarId_455_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; uint8_t v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_a_469_);
lean_dec_ref_known(v___x_468_, 1);
v___x_470_ = 0;
v___x_471_ = l_Lean_Expr_letE___override(v_name_457_, v_type_458_, v_val_459_, v_a_469_, v___x_470_);
v___x_472_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_471_, v_a_467_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v___x_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_482_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc_n(v_a_473_, 2);
lean_dec_ref_known(v___x_472_, 1);
v___x_474_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(v_mvarId_455_, v_a_473_, v___y_461_);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_482_ == 0)
{
lean_object* v_unused_483_; 
v_unused_483_ = lean_ctor_get(v___x_474_, 0);
lean_dec(v_unused_483_);
v___x_476_ = v___x_474_;
v_isShared_477_ = v_isSharedCheck_482_;
goto v_resetjp_475_;
}
else
{
lean_dec(v___x_474_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_482_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_478_; lean_object* v___x_480_; 
v___x_478_ = l_Lean_Expr_mvarId_x21(v_a_473_);
lean_dec(v_a_473_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 0, v___x_478_);
v___x_480_ = v___x_476_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_478_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
else
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_491_; 
lean_dec(v_mvarId_455_);
v_a_484_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_491_ == 0)
{
v___x_486_ = v___x_472_;
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_472_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_a_484_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
else
{
lean_object* v_a_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_499_; 
lean_dec(v_a_467_);
lean_dec_ref(v_val_459_);
lean_dec_ref(v_type_458_);
lean_dec(v_name_457_);
lean_dec(v_mvarId_455_);
v_a_492_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_499_ == 0)
{
v___x_494_ = v___x_468_;
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_a_492_);
lean_dec(v___x_468_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_497_; 
if (v_isShared_495_ == 0)
{
v___x_497_ = v___x_494_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_a_492_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
else
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_507_; 
lean_dec_ref(v_val_459_);
lean_dec_ref(v_type_458_);
lean_dec(v_name_457_);
lean_dec(v_mvarId_455_);
v_a_500_ = lean_ctor_get(v___x_466_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_507_ == 0)
{
v___x_502_ = v___x_466_;
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_466_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_505_; 
if (v_isShared_503_ == 0)
{
v___x_505_ = v___x_502_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_a_500_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
else
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
lean_dec_ref(v_val_459_);
lean_dec_ref(v_type_458_);
lean_dec(v_name_457_);
lean_dec(v_mvarId_455_);
v_a_508_ = lean_ctor_get(v___x_465_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_515_ == 0)
{
v___x_510_ = v___x_465_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_465_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_511_ == 0)
{
v___x_513_ = v___x_510_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_508_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_define___lam__0___boxed(lean_object* v_mvarId_516_, lean_object* v___x_517_, lean_object* v_name_518_, lean_object* v_type_519_, lean_object* v_val_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Lean_MVarId_define___lam__0(v_mvarId_516_, v___x_517_, v_name_518_, v_type_519_, v_val_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_define(lean_object* v_mvarId_530_, lean_object* v_name_531_, lean_object* v_type_532_, lean_object* v_val_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_){
_start:
{
lean_object* v___x_539_; lean_object* v___f_540_; lean_object* v___x_541_; 
v___x_539_ = ((lean_object*)(l_Lean_MVarId_define___closed__1));
lean_inc(v_mvarId_530_);
v___f_540_ = lean_alloc_closure((void*)(l_Lean_MVarId_define___lam__0___boxed), 10, 5);
lean_closure_set(v___f_540_, 0, v_mvarId_530_);
lean_closure_set(v___f_540_, 1, v___x_539_);
lean_closure_set(v___f_540_, 2, v_name_531_);
lean_closure_set(v___f_540_, 3, v_type_532_);
lean_closure_set(v___f_540_, 4, v_val_533_);
v___x_541_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(v_mvarId_530_, v___f_540_, v_a_534_, v_a_535_, v_a_536_, v_a_537_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_define___boxed(lean_object* v_mvarId_542_, lean_object* v_name_543_, lean_object* v_type_544_, lean_object* v_val_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Lean_MVarId_define(v_mvarId_542_, v_name_543_, v_type_544_, v_val_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
lean_dec(v_a_549_);
lean_dec_ref(v_a_548_);
lean_dec(v_a_547_);
lean_dec_ref(v_a_546_);
return v_res_551_;
}
}
static lean_object* _init_l_Lean_MVarId_assertExt___lam__0___closed__2(void){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = lean_unsigned_to_nat(0u);
v___x_556_ = l_Lean_mkBVar(v___x_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertExt___lam__0(lean_object* v_mvarId_557_, lean_object* v___x_558_, lean_object* v_type_559_, lean_object* v_val_560_, lean_object* v_hName_561_, lean_object* v_name_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
lean_object* v___x_568_; 
lean_inc(v_mvarId_557_);
v___x_568_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_557_, v___x_558_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v___x_569_; 
lean_dec_ref_known(v___x_568_, 1);
lean_inc(v_mvarId_557_);
v___x_569_ = l_Lean_MVarId_getTag(v_mvarId_557_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; lean_object* v___x_571_; 
v_a_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_a_570_);
lean_dec_ref_known(v___x_569_, 1);
lean_inc(v_mvarId_557_);
v___x_571_ = l_Lean_MVarId_getType(v_mvarId_557_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v_a_572_; lean_object* v___x_573_; 
v_a_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_a_572_);
lean_dec_ref_known(v___x_571_, 1);
lean_inc_ref(v_type_559_);
v___x_573_ = l_Lean_Meta_getLevel(v_type_559_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v_a_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; uint8_t v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v_a_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc(v_a_574_);
lean_dec_ref_known(v___x_573_, 1);
v___x_575_ = ((lean_object*)(l_Lean_MVarId_assertExt___lam__0___closed__1));
v___x_576_ = lean_box(0);
v___x_577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_577_, 0, v_a_574_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
v___x_578_ = l_Lean_mkConst(v___x_575_, v___x_577_);
v___x_579_ = lean_obj_once(&l_Lean_MVarId_assertExt___lam__0___closed__2, &l_Lean_MVarId_assertExt___lam__0___closed__2_once, _init_l_Lean_MVarId_assertExt___lam__0___closed__2);
lean_inc_ref(v_val_560_);
lean_inc_ref(v_type_559_);
v___x_580_ = l_Lean_mkApp3(v___x_578_, v_type_559_, v___x_579_, v_val_560_);
v___x_581_ = 0;
v___x_582_ = l_Lean_mkForall(v_hName_561_, v___x_581_, v___x_580_, v_a_572_);
v___x_583_ = l_Lean_mkForall(v_name_562_, v___x_581_, v_type_559_, v___x_582_);
v___x_584_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_583_, v_a_570_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v_a_585_; lean_object* v___x_586_; 
v_a_585_ = lean_ctor_get(v___x_584_, 0);
lean_inc(v_a_585_);
lean_dec_ref_known(v___x_584_, 1);
lean_inc_ref(v_val_560_);
v___x_586_ = l_Lean_Meta_mkEqRefl(v_val_560_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v_a_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_597_; 
v_a_587_ = lean_ctor_get(v___x_586_, 0);
lean_inc(v_a_587_);
lean_dec_ref_known(v___x_586_, 1);
lean_inc(v_a_585_);
v___x_588_ = l_Lean_mkAppB(v_a_585_, v_val_560_, v_a_587_);
v___x_589_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(v_mvarId_557_, v___x_588_, v___y_564_);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_597_ == 0)
{
lean_object* v_unused_598_; 
v_unused_598_ = lean_ctor_get(v___x_589_, 0);
lean_dec(v_unused_598_);
v___x_591_ = v___x_589_;
v_isShared_592_ = v_isSharedCheck_597_;
goto v_resetjp_590_;
}
else
{
lean_dec(v___x_589_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_597_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_593_; lean_object* v___x_595_; 
v___x_593_ = l_Lean_Expr_mvarId_x21(v_a_585_);
lean_dec(v_a_585_);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 0, v___x_593_);
v___x_595_ = v___x_591_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_593_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
else
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_606_; 
lean_dec(v_a_585_);
lean_dec_ref(v_val_560_);
lean_dec(v_mvarId_557_);
v_a_599_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_606_ == 0)
{
v___x_601_ = v___x_586_;
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___x_586_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_604_; 
if (v_isShared_602_ == 0)
{
v___x_604_ = v___x_601_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_a_599_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
else
{
lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
lean_dec_ref(v_val_560_);
lean_dec(v_mvarId_557_);
v_a_607_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_614_ == 0)
{
v___x_609_ = v___x_584_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v___x_584_);
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
else
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_622_; 
lean_dec(v_a_572_);
lean_dec(v_a_570_);
lean_dec(v_name_562_);
lean_dec(v_hName_561_);
lean_dec_ref(v_val_560_);
lean_dec_ref(v_type_559_);
lean_dec(v_mvarId_557_);
v_a_615_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_622_ == 0)
{
v___x_617_ = v___x_573_;
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_573_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_620_; 
if (v_isShared_618_ == 0)
{
v___x_620_ = v___x_617_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_a_615_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
else
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
lean_dec(v_a_570_);
lean_dec(v_name_562_);
lean_dec(v_hName_561_);
lean_dec_ref(v_val_560_);
lean_dec_ref(v_type_559_);
lean_dec(v_mvarId_557_);
v_a_623_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_571_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_571_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
else
{
lean_object* v_a_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_638_; 
lean_dec(v_name_562_);
lean_dec(v_hName_561_);
lean_dec_ref(v_val_560_);
lean_dec_ref(v_type_559_);
lean_dec(v_mvarId_557_);
v_a_631_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_638_ == 0)
{
v___x_633_ = v___x_569_;
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_a_631_);
lean_dec(v___x_569_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_636_; 
if (v_isShared_634_ == 0)
{
v___x_636_ = v___x_633_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_a_631_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
else
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_646_; 
lean_dec(v_name_562_);
lean_dec(v_hName_561_);
lean_dec_ref(v_val_560_);
lean_dec_ref(v_type_559_);
lean_dec(v_mvarId_557_);
v_a_639_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_646_ == 0)
{
v___x_641_ = v___x_568_;
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_568_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_a_639_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertExt___lam__0___boxed(lean_object* v_mvarId_647_, lean_object* v___x_648_, lean_object* v_type_649_, lean_object* v_val_650_, lean_object* v_hName_651_, lean_object* v_name_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Lean_MVarId_assertExt___lam__0(v_mvarId_647_, v___x_648_, v_type_649_, v_val_650_, v_hName_651_, v_name_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertExt(lean_object* v_mvarId_659_, lean_object* v_name_660_, lean_object* v_type_661_, lean_object* v_val_662_, lean_object* v_hName_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_){
_start:
{
lean_object* v___x_669_; lean_object* v___f_670_; lean_object* v___x_671_; 
v___x_669_ = ((lean_object*)(l_Lean_MVarId_assert___closed__1));
lean_inc(v_mvarId_659_);
v___f_670_ = lean_alloc_closure((void*)(l_Lean_MVarId_assertExt___lam__0___boxed), 11, 6);
lean_closure_set(v___f_670_, 0, v_mvarId_659_);
lean_closure_set(v___f_670_, 1, v___x_669_);
lean_closure_set(v___f_670_, 2, v_type_661_);
lean_closure_set(v___f_670_, 3, v_val_662_);
lean_closure_set(v___f_670_, 4, v_hName_663_);
lean_closure_set(v___f_670_, 5, v_name_660_);
v___x_671_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(v_mvarId_659_, v___f_670_, v_a_664_, v_a_665_, v_a_666_, v_a_667_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertExt___boxed(lean_object* v_mvarId_672_, lean_object* v_name_673_, lean_object* v_type_674_, lean_object* v_val_675_, lean_object* v_hName_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_MVarId_assertExt(v_mvarId_672_, v_name_673_, v_type_674_, v_val_675_, v_hName_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
lean_dec(v_a_680_);
lean_dec_ref(v_a_679_);
lean_dec(v_a_678_);
lean_dec_ref(v_a_677_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___redArg(lean_object* v_t_683_, lean_object* v___y_684_){
_start:
{
lean_object* v___x_686_; lean_object* v_infoState_687_; uint8_t v_enabled_688_; 
v___x_686_ = lean_st_ref_get(v___y_684_);
v_infoState_687_ = lean_ctor_get(v___x_686_, 8);
lean_inc_ref(v_infoState_687_);
lean_dec(v___x_686_);
v_enabled_688_ = lean_ctor_get_uint8(v_infoState_687_, sizeof(void*)*3);
lean_dec_ref(v_infoState_687_);
if (v_enabled_688_ == 0)
{
lean_object* v___x_689_; lean_object* v___x_690_; 
lean_dec_ref(v_t_683_);
v___x_689_ = lean_box(0);
v___x_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
return v___x_690_;
}
else
{
lean_object* v___x_691_; lean_object* v_infoState_692_; lean_object* v_env_693_; lean_object* v_nextMacroScope_694_; lean_object* v_ngen_695_; lean_object* v_auxDeclNGen_696_; lean_object* v_traceState_697_; lean_object* v_cache_698_; lean_object* v_recordedDeps_699_; lean_object* v_messages_700_; lean_object* v_snapshotTasks_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_723_; 
v___x_691_ = lean_st_ref_take(v___y_684_);
v_infoState_692_ = lean_ctor_get(v___x_691_, 8);
v_env_693_ = lean_ctor_get(v___x_691_, 0);
v_nextMacroScope_694_ = lean_ctor_get(v___x_691_, 1);
v_ngen_695_ = lean_ctor_get(v___x_691_, 2);
v_auxDeclNGen_696_ = lean_ctor_get(v___x_691_, 3);
v_traceState_697_ = lean_ctor_get(v___x_691_, 4);
v_cache_698_ = lean_ctor_get(v___x_691_, 5);
v_recordedDeps_699_ = lean_ctor_get(v___x_691_, 6);
v_messages_700_ = lean_ctor_get(v___x_691_, 7);
v_snapshotTasks_701_ = lean_ctor_get(v___x_691_, 9);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_723_ == 0)
{
v___x_703_ = v___x_691_;
v_isShared_704_ = v_isSharedCheck_723_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_snapshotTasks_701_);
lean_inc(v_infoState_692_);
lean_inc(v_messages_700_);
lean_inc(v_recordedDeps_699_);
lean_inc(v_cache_698_);
lean_inc(v_traceState_697_);
lean_inc(v_auxDeclNGen_696_);
lean_inc(v_ngen_695_);
lean_inc(v_nextMacroScope_694_);
lean_inc(v_env_693_);
lean_dec(v___x_691_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_723_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
uint8_t v_enabled_705_; lean_object* v_assignment_706_; lean_object* v_lazyAssignment_707_; lean_object* v_trees_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_722_; 
v_enabled_705_ = lean_ctor_get_uint8(v_infoState_692_, sizeof(void*)*3);
v_assignment_706_ = lean_ctor_get(v_infoState_692_, 0);
v_lazyAssignment_707_ = lean_ctor_get(v_infoState_692_, 1);
v_trees_708_ = lean_ctor_get(v_infoState_692_, 2);
v_isSharedCheck_722_ = !lean_is_exclusive(v_infoState_692_);
if (v_isSharedCheck_722_ == 0)
{
v___x_710_ = v_infoState_692_;
v_isShared_711_ = v_isSharedCheck_722_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_trees_708_);
lean_inc(v_lazyAssignment_707_);
lean_inc(v_assignment_706_);
lean_dec(v_infoState_692_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_722_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_715_; 
v___x_712_ = lean_box(0);
v___x_713_ = l_Lean_PersistentArray_push___redArg(v_trees_708_, v_t_683_);
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 2, v___x_713_);
v___x_715_ = v___x_710_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_assignment_706_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_lazyAssignment_707_);
lean_ctor_set(v_reuseFailAlloc_721_, 2, v___x_713_);
lean_ctor_set_uint8(v_reuseFailAlloc_721_, sizeof(void*)*3, v_enabled_705_);
v___x_715_ = v_reuseFailAlloc_721_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v___x_717_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 8, v___x_715_);
v___x_717_ = v___x_703_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_env_693_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v_nextMacroScope_694_);
lean_ctor_set(v_reuseFailAlloc_720_, 2, v_ngen_695_);
lean_ctor_set(v_reuseFailAlloc_720_, 3, v_auxDeclNGen_696_);
lean_ctor_set(v_reuseFailAlloc_720_, 4, v_traceState_697_);
lean_ctor_set(v_reuseFailAlloc_720_, 5, v_cache_698_);
lean_ctor_set(v_reuseFailAlloc_720_, 6, v_recordedDeps_699_);
lean_ctor_set(v_reuseFailAlloc_720_, 7, v_messages_700_);
lean_ctor_set(v_reuseFailAlloc_720_, 8, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_720_, 9, v_snapshotTasks_701_);
v___x_717_ = v_reuseFailAlloc_720_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = lean_st_ref_put(v___y_684_, v___x_717_);
v___x_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_719_, 0, v___x_712_);
return v___x_719_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___redArg___boxed(lean_object* v_t_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___redArg(v_t_724_, v___y_725_);
lean_dec(v___y_725_);
return v_res_727_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__0(void){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_728_ = lean_unsigned_to_nat(32u);
v___x_729_ = lean_mk_empty_array_with_capacity(v___x_728_);
v___x_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
return v___x_730_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__1(void){
_start:
{
size_t v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_731_ = ((size_t)5ULL);
v___x_732_ = lean_unsigned_to_nat(0u);
v___x_733_ = lean_unsigned_to_nat(32u);
v___x_734_ = lean_mk_empty_array_with_capacity(v___x_733_);
v___x_735_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__0);
v___x_736_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_736_, 0, v___x_735_);
lean_ctor_set(v___x_736_, 1, v___x_734_);
lean_ctor_set(v___x_736_, 2, v___x_732_);
lean_ctor_set(v___x_736_, 3, v___x_732_);
lean_ctor_set_usize(v___x_736_, 4, v___x_731_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0(lean_object* v_t_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v___x_743_; lean_object* v_infoState_744_; uint8_t v_enabled_745_; 
v___x_743_ = lean_st_ref_get(v___y_741_);
v_infoState_744_ = lean_ctor_get(v___x_743_, 8);
lean_inc_ref(v_infoState_744_);
lean_dec(v___x_743_);
v_enabled_745_ = lean_ctor_get_uint8(v_infoState_744_, sizeof(void*)*3);
lean_dec_ref(v_infoState_744_);
if (v_enabled_745_ == 0)
{
lean_object* v___x_746_; lean_object* v___x_747_; 
lean_dec_ref(v_t_737_);
v___x_746_ = lean_box(0);
v___x_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
return v___x_747_;
}
else
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_748_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__1);
v___x_749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_749_, 0, v_t_737_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
v___x_750_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___redArg(v___x_749_, v___y_741_);
return v___x_750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___boxed(lean_object* v_t_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0(v_t_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__1(lean_object* v___x_758_, lean_object* v_as_759_, size_t v_sz_760_, size_t v_i_761_, lean_object* v_b_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
uint8_t v___x_768_; 
v___x_768_ = lean_usize_dec_lt(v_i_761_, v_sz_760_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; 
lean_dec_ref(v___x_758_);
v___x_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_769_, 0, v_b_762_);
return v___x_769_;
}
else
{
lean_object* v_snd_770_; lean_object* v_fst_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_818_; 
v_snd_770_ = lean_ctor_get(v_b_762_, 1);
v_fst_771_ = lean_ctor_get(v_b_762_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v_b_762_);
if (v_isSharedCheck_818_ == 0)
{
v___x_773_ = v_b_762_;
v_isShared_774_ = v_isSharedCheck_818_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_snd_770_);
lean_inc(v_fst_771_);
lean_dec(v_b_762_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_818_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v_array_775_; lean_object* v_start_776_; lean_object* v_stop_777_; uint8_t v___x_778_; 
v_array_775_ = lean_ctor_get(v_snd_770_, 0);
v_start_776_ = lean_ctor_get(v_snd_770_, 1);
v_stop_777_ = lean_ctor_get(v_snd_770_, 2);
v___x_778_ = lean_nat_dec_lt(v_start_776_, v_stop_777_);
if (v___x_778_ == 0)
{
lean_object* v___x_780_; 
lean_dec_ref(v___x_758_);
if (v_isShared_774_ == 0)
{
v___x_780_ = v___x_773_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_fst_771_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_snd_770_);
v___x_780_ = v_reuseFailAlloc_782_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_781_; 
v___x_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
return v___x_781_;
}
}
else
{
lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_814_; 
lean_inc(v_stop_777_);
lean_inc(v_start_776_);
lean_inc_ref(v_array_775_);
v_isSharedCheck_814_ = !lean_is_exclusive(v_snd_770_);
if (v_isSharedCheck_814_ == 0)
{
lean_object* v_unused_815_; lean_object* v_unused_816_; lean_object* v_unused_817_; 
v_unused_815_ = lean_ctor_get(v_snd_770_, 2);
lean_dec(v_unused_815_);
v_unused_816_ = lean_ctor_get(v_snd_770_, 1);
lean_dec(v_unused_816_);
v_unused_817_ = lean_ctor_get(v_snd_770_, 0);
lean_dec(v_unused_817_);
v___x_784_ = v_snd_770_;
v_isShared_785_ = v_isSharedCheck_814_;
goto v_resetjp_783_;
}
else
{
lean_dec(v_snd_770_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_814_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v_a_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_791_; 
v_a_786_ = lean_array_uget_borrowed(v_as_759_, v_i_761_);
v___x_787_ = lean_array_fget(v_array_775_, v_start_776_);
v___x_788_ = lean_unsigned_to_nat(1u);
v___x_789_ = lean_nat_add(v_start_776_, v___x_788_);
lean_dec(v_start_776_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 1, v___x_789_);
v___x_791_ = v___x_784_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_array_775_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v___x_789_);
lean_ctor_set(v_reuseFailAlloc_813_, 2, v_stop_777_);
v___x_791_ = v_reuseFailAlloc_813_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
lean_inc_n(v___x_787_, 2);
v___x_792_ = l_Lean_mkFVar(v___x_787_);
lean_inc_n(v_a_786_, 2);
v___x_793_ = l_Lean_Meta_FVarSubst_insert(v_fst_771_, v_a_786_, v___x_792_);
lean_inc_ref(v___x_758_);
v___x_794_ = l_Lean_LocalContext_get_x21(v___x_758_, v___x_787_);
v___x_795_ = l_Lean_LocalDecl_userName(v___x_794_);
lean_dec_ref(v___x_794_);
v___x_796_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_796_, 0, v___x_795_);
lean_ctor_set(v___x_796_, 1, v___x_787_);
lean_ctor_set(v___x_796_, 2, v_a_786_);
v___x_797_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
v___x_798_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0(v___x_797_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v___x_800_; 
lean_dec_ref_known(v___x_798_, 1);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 1, v___x_791_);
lean_ctor_set(v___x_773_, 0, v___x_793_);
v___x_800_ = v___x_773_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_793_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v___x_791_);
v___x_800_ = v_reuseFailAlloc_804_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
size_t v___x_801_; size_t v___x_802_; 
v___x_801_ = ((size_t)1ULL);
v___x_802_ = lean_usize_add(v_i_761_, v___x_801_);
v_i_761_ = v___x_802_;
v_b_762_ = v___x_800_;
goto _start;
}
}
else
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
lean_dec(v___x_793_);
lean_dec_ref(v___x_791_);
lean_del_object(v___x_773_);
lean_dec_ref(v___x_758_);
v_a_805_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_812_ == 0)
{
v___x_807_ = v___x_798_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_798_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_a_805_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__1___boxed(lean_object* v___x_819_, lean_object* v_as_820_, lean_object* v_sz_821_, lean_object* v_i_822_, lean_object* v_b_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
size_t v_sz_boxed_829_; size_t v_i_boxed_830_; lean_object* v_res_831_; 
v_sz_boxed_829_ = lean_unbox_usize(v_sz_821_);
lean_dec(v_sz_821_);
v_i_boxed_830_ = lean_unbox_usize(v_i_822_);
lean_dec(v_i_822_);
v_res_831_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__1(v___x_819_, v_as_820_, v_sz_boxed_829_, v_i_boxed_830_, v_b_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
lean_dec_ref(v_as_820_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertAfter(lean_object* v_mvarId_835_, lean_object* v_fvarId_836_, lean_object* v_userName_837_, lean_object* v_type_838_, lean_object* v_val_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = ((lean_object*)(l_Lean_MVarId_assertAfter___closed__1));
lean_inc(v_mvarId_835_);
v___x_846_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_835_, v___x_845_, v_a_840_, v_a_841_, v_a_842_, v_a_843_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v___x_847_; 
lean_dec_ref_known(v___x_846_, 1);
v___x_847_ = l_Lean_MVarId_revertAfter(v_mvarId_835_, v_fvarId_836_, v_a_840_, v_a_841_, v_a_842_, v_a_843_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_848_; lean_object* v_fst_849_; lean_object* v_snd_850_; lean_object* v___x_851_; 
v_a_848_ = lean_ctor_get(v___x_847_, 0);
lean_inc(v_a_848_);
lean_dec_ref_known(v___x_847_, 1);
v_fst_849_ = lean_ctor_get(v_a_848_, 0);
lean_inc(v_fst_849_);
v_snd_850_ = lean_ctor_get(v_a_848_, 1);
lean_inc(v_snd_850_);
lean_dec(v_a_848_);
v___x_851_ = l_Lean_MVarId_assert(v_snd_850_, v_userName_837_, v_type_838_, v_val_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v_a_852_; uint8_t v___x_853_; lean_object* v___x_854_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_a_852_);
lean_dec_ref_known(v___x_851_, 1);
v___x_853_ = 1;
v___x_854_ = l_Lean_Meta_intro1Core(v_a_852_, v___x_853_, v_a_840_, v_a_841_, v_a_842_, v_a_843_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v_fst_856_; lean_object* v_snd_857_; lean_object* v___x_858_; lean_object* v___x_859_; uint8_t v___x_860_; lean_object* v___x_861_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_855_);
lean_dec_ref_known(v___x_854_, 1);
v_fst_856_ = lean_ctor_get(v_a_855_, 0);
lean_inc(v_fst_856_);
v_snd_857_ = lean_ctor_get(v_a_855_, 1);
lean_inc(v_snd_857_);
lean_dec(v_a_855_);
v___x_858_ = lean_array_get_size(v_fst_849_);
v___x_859_ = lean_box(0);
v___x_860_ = 0;
v___x_861_ = l_Lean_Meta_introNCore(v_snd_857_, v___x_858_, v___x_859_, v___x_860_, v___x_853_, v_a_840_, v_a_841_, v_a_842_, v_a_843_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; lean_object* v_fst_863_; lean_object* v_snd_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_907_; 
v_a_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_a_862_);
lean_dec_ref_known(v___x_861_, 1);
v_fst_863_ = lean_ctor_get(v_a_862_, 0);
v_snd_864_ = lean_ctor_get(v_a_862_, 1);
v_isSharedCheck_907_ = !lean_is_exclusive(v_a_862_);
if (v_isSharedCheck_907_ == 0)
{
v___x_866_ = v_a_862_;
v_isShared_867_ = v_isSharedCheck_907_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_snd_864_);
lean_inc(v_fst_863_);
lean_dec(v_a_862_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_907_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_868_; 
lean_inc(v_snd_864_);
v___x_868_ = l_Lean_MVarId_getDecl(v_snd_864_, v_a_840_, v_a_841_, v_a_842_, v_a_843_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; lean_object* v_lctx_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_876_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_a_869_);
lean_dec_ref_known(v___x_868_, 1);
v_lctx_870_ = lean_ctor_get(v_a_869_, 1);
lean_inc_ref(v_lctx_870_);
lean_dec(v_a_869_);
v___x_871_ = lean_box(0);
v___x_872_ = lean_unsigned_to_nat(0u);
v___x_873_ = lean_array_get_size(v_fst_863_);
v___x_874_ = l_Array_toSubarray___redArg(v_fst_863_, v___x_872_, v___x_873_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 1, v___x_874_);
lean_ctor_set(v___x_866_, 0, v___x_871_);
v___x_876_ = v___x_866_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_871_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v___x_874_);
v___x_876_ = v_reuseFailAlloc_898_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
size_t v_sz_877_; size_t v___x_878_; lean_object* v___x_879_; 
v_sz_877_ = lean_array_size(v_fst_849_);
v___x_878_ = ((size_t)0ULL);
v___x_879_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__1(v_lctx_870_, v_fst_849_, v_sz_877_, v___x_878_, v___x_876_, v_a_840_, v_a_841_, v_a_842_, v_a_843_);
lean_dec(v_fst_849_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_889_; 
v_a_880_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_889_ == 0)
{
v___x_882_ = v___x_879_;
v_isShared_883_ = v_isSharedCheck_889_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_879_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_889_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v_fst_884_; lean_object* v___x_885_; lean_object* v___x_887_; 
v_fst_884_ = lean_ctor_get(v_a_880_, 0);
lean_inc(v_fst_884_);
lean_dec(v_a_880_);
v___x_885_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_885_, 0, v_fst_856_);
lean_ctor_set(v___x_885_, 1, v_snd_864_);
lean_ctor_set(v___x_885_, 2, v_fst_884_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v___x_885_);
v___x_887_ = v___x_882_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_885_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
else
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_897_; 
lean_dec(v_snd_864_);
lean_dec(v_fst_856_);
v_a_890_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_897_ == 0)
{
v___x_892_ = v___x_879_;
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_879_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
if (v_isShared_893_ == 0)
{
v___x_895_ = v___x_892_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_890_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
}
else
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
lean_del_object(v___x_866_);
lean_dec(v_snd_864_);
lean_dec(v_fst_863_);
lean_dec(v_fst_856_);
lean_dec(v_fst_849_);
v_a_899_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_868_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_868_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_899_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
}
else
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_915_; 
lean_dec(v_fst_856_);
lean_dec(v_fst_849_);
v_a_908_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_915_ == 0)
{
v___x_910_ = v___x_861_;
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_861_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_913_; 
if (v_isShared_911_ == 0)
{
v___x_913_ = v___x_910_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_a_908_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
else
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
lean_dec(v_fst_849_);
v_a_916_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_923_ == 0)
{
v___x_918_ = v___x_854_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_854_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_916_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
lean_dec(v_fst_849_);
v_a_924_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_851_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_851_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
else
{
lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_939_; 
lean_dec_ref(v_val_839_);
lean_dec_ref(v_type_838_);
lean_dec(v_userName_837_);
v_a_932_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_939_ == 0)
{
v___x_934_ = v___x_847_;
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_847_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_937_; 
if (v_isShared_935_ == 0)
{
v___x_937_ = v___x_934_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_a_932_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec_ref(v_val_839_);
lean_dec_ref(v_type_838_);
lean_dec(v_userName_837_);
lean_dec(v_fvarId_836_);
lean_dec(v_mvarId_835_);
v_a_940_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_846_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_846_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertAfter___boxed(lean_object* v_mvarId_948_, lean_object* v_fvarId_949_, lean_object* v_userName_950_, lean_object* v_type_951_, lean_object* v_val_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_MVarId_assertAfter(v_mvarId_948_, v_fvarId_949_, v_userName_950_, v_type_951_, v_val_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0(lean_object* v_t_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___redArg(v_t_959_, v___y_963_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___boxed(lean_object* v_t_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0(v_t_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg(lean_object* v_ldecl_x27_973_, lean_object* v_a_974_){
_start:
{
lean_object* v___x_976_; lean_object* v_fst_978_; lean_object* v_snd_979_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; uint8_t v___x_985_; 
v___x_976_ = lean_st_ref_take(v_a_974_);
v___x_982_ = lean_box(0);
v___x_983_ = l_Lean_LocalDecl_index(v___x_976_);
v___x_984_ = l_Lean_LocalDecl_index(v_ldecl_x27_973_);
v___x_985_ = lean_nat_dec_lt(v___x_983_, v___x_984_);
lean_dec(v___x_984_);
lean_dec(v___x_983_);
if (v___x_985_ == 0)
{
lean_dec_ref(v_ldecl_x27_973_);
v_fst_978_ = v___x_982_;
v_snd_979_ = v___x_976_;
goto v___jp_977_;
}
else
{
lean_dec(v___x_976_);
v_fst_978_ = v___x_982_;
v_snd_979_ = v_ldecl_x27_973_;
goto v___jp_977_;
}
v___jp_977_:
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = lean_st_ref_put(v_a_974_, v_snd_979_);
v___x_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_981_, 0, v_fst_978_);
return v___x_981_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg___boxed(lean_object* v_ldecl_x27_986_, lean_object* v_a_987_, lean_object* v_a_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg(v_ldecl_x27_986_, v_a_987_);
lean_dec(v_a_987_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl(lean_object* v_ldecl_x27_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg(v_ldecl_x27_990_, v_a_991_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___boxed(lean_object* v_ldecl_x27_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl(v_ldecl_x27_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
lean_dec(v_a_1003_);
lean_dec_ref(v_a_1002_);
lean_dec(v_a_1001_);
lean_dec_ref(v_a_1000_);
lean_dec(v_a_999_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___redArg(lean_object* v_as_1006_, size_t v_i_1007_, size_t v_stop_1008_, lean_object* v_b_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v_a_1016_; uint8_t v___x_1020_; 
v___x_1020_ = lean_usize_dec_eq(v_i_1007_, v_stop_1008_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; 
v___x_1021_ = lean_array_uget_borrowed(v_as_1006_, v_i_1007_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v___x_1022_; 
v___x_1022_ = lean_box(0);
v_a_1016_ = v___x_1022_;
goto v___jp_1015_;
}
else
{
lean_object* v_val_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v_val_1023_ = lean_ctor_get(v___x_1021_, 0);
v___x_1024_ = l_Lean_LocalDecl_fvarId(v_val_1023_);
v___x_1025_ = l_Lean_FVarId_getDecl___redArg(v___x_1024_, v___y_1011_, v___y_1012_, v___y_1013_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v___x_1027_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_a_1026_);
lean_dec_ref_known(v___x_1025_, 1);
v___x_1027_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg(v_a_1026_, v___y_1010_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
lean_inc(v_a_1028_);
lean_dec_ref_known(v___x_1027_, 1);
v_a_1016_ = v_a_1028_;
goto v___jp_1015_;
}
else
{
return v___x_1027_;
}
}
else
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1036_; 
v_a_1029_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1031_ = v___x_1025_;
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_1025_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_a_1029_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
}
else
{
lean_object* v___x_1037_; 
v___x_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1037_, 0, v_b_1009_);
return v___x_1037_;
}
v___jp_1015_:
{
size_t v___x_1017_; size_t v___x_1018_; 
v___x_1017_ = ((size_t)1ULL);
v___x_1018_ = lean_usize_add(v_i_1007_, v___x_1017_);
v_i_1007_ = v___x_1018_;
v_b_1009_ = v_a_1016_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_as_1038_, lean_object* v_i_1039_, lean_object* v_stop_1040_, lean_object* v_b_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
size_t v_i_boxed_1047_; size_t v_stop_boxed_1048_; lean_object* v_res_1049_; 
v_i_boxed_1047_ = lean_unbox_usize(v_i_1039_);
lean_dec(v_i_1039_);
v_stop_boxed_1048_ = lean_unbox_usize(v_stop_1040_);
lean_dec(v_stop_1040_);
v_res_1049_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___redArg(v_as_1038_, v_i_boxed_1047_, v_stop_boxed_1048_, v_b_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v_as_1038_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(lean_object* v_as_1050_, size_t v_i_1051_, size_t v_stop_1052_, lean_object* v_b_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v_a_1061_; uint8_t v___x_1065_; 
v___x_1065_ = lean_usize_dec_eq(v_i_1051_, v_stop_1052_);
if (v___x_1065_ == 0)
{
lean_object* v___x_1066_; 
v___x_1066_ = lean_array_uget_borrowed(v_as_1050_, v_i_1051_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v___x_1067_; 
v___x_1067_ = lean_box(0);
v_a_1061_ = v___x_1067_;
goto v___jp_1060_;
}
else
{
lean_object* v_val_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v_val_1068_ = lean_ctor_get(v___x_1066_, 0);
v___x_1069_ = l_Lean_LocalDecl_fvarId(v_val_1068_);
v___x_1070_ = l_Lean_FVarId_getDecl___redArg(v___x_1069_, v___y_1055_, v___y_1057_, v___y_1058_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v___x_1072_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
lean_inc(v_a_1071_);
lean_dec_ref_known(v___x_1070_, 1);
v___x_1072_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg(v_a_1071_, v___y_1054_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_a_1073_);
lean_dec_ref_known(v___x_1072_, 1);
v_a_1061_ = v_a_1073_;
goto v___jp_1060_;
}
else
{
return v___x_1072_;
}
}
else
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1081_; 
v_a_1074_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1076_ = v___x_1070_;
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1070_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_a_1074_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
}
}
else
{
lean_object* v___x_1082_; 
v___x_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1082_, 0, v_b_1053_);
return v___x_1082_;
}
v___jp_1060_:
{
size_t v___x_1062_; size_t v___x_1063_; lean_object* v___x_1064_; 
v___x_1062_ = ((size_t)1ULL);
v___x_1063_ = lean_usize_add(v_i_1051_, v___x_1062_);
v___x_1064_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___redArg(v_as_1050_, v___x_1063_, v_stop_1052_, v_a_1061_, v___y_1054_, v___y_1055_, v___y_1057_, v___y_1058_);
return v___x_1064_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2___boxed(lean_object* v_as_1083_, lean_object* v_i_1084_, lean_object* v_stop_1085_, lean_object* v_b_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
size_t v_i_boxed_1093_; size_t v_stop_boxed_1094_; lean_object* v_res_1095_; 
v_i_boxed_1093_ = lean_unbox_usize(v_i_1084_);
lean_dec(v_i_1084_);
v_stop_boxed_1094_ = lean_unbox_usize(v_stop_1085_);
lean_dec(v_stop_1085_);
v_res_1095_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_as_1083_, v_i_boxed_1093_, v_stop_boxed_1094_, v_b_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
lean_dec(v___y_1087_);
lean_dec_ref(v_as_1083_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
if (lean_obj_tag(v_x_1096_) == 0)
{
lean_object* v_cs_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1117_; 
v_cs_1103_ = lean_ctor_get(v_x_1096_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v_x_1096_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1105_ = v_x_1096_;
v_isShared_1106_ = v_isSharedCheck_1117_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_cs_1103_);
lean_dec(v_x_1096_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1117_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; uint8_t v___x_1110_; 
v___x_1107_ = lean_unsigned_to_nat(0u);
v___x_1108_ = lean_array_get_size(v_cs_1103_);
v___x_1109_ = lean_box(0);
v___x_1110_ = lean_nat_dec_lt(v___x_1107_, v___x_1108_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1112_; 
lean_dec_ref(v_cs_1103_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 0, v___x_1109_);
v___x_1112_ = v___x_1105_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1109_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
else
{
size_t v___x_1114_; size_t v___x_1115_; lean_object* v___x_1116_; 
lean_del_object(v___x_1105_);
v___x_1114_ = ((size_t)0ULL);
v___x_1115_ = lean_usize_of_nat(v___x_1108_);
v___x_1116_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4(v_cs_1103_, v___x_1114_, v___x_1115_, v___x_1109_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
lean_dec_ref(v_cs_1103_);
return v___x_1116_;
}
}
}
else
{
lean_object* v_vs_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1132_; 
v_vs_1118_ = lean_ctor_get(v_x_1096_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v_x_1096_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1120_ = v_x_1096_;
v_isShared_1121_ = v_isSharedCheck_1132_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_vs_1118_);
lean_dec(v_x_1096_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1132_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; uint8_t v___x_1125_; 
v___x_1122_ = lean_unsigned_to_nat(0u);
v___x_1123_ = lean_array_get_size(v_vs_1118_);
v___x_1124_ = lean_box(0);
v___x_1125_ = lean_nat_dec_lt(v___x_1122_, v___x_1123_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1127_; 
lean_dec_ref(v_vs_1118_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set_tag(v___x_1120_, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1124_);
v___x_1127_ = v___x_1120_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1124_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
else
{
size_t v___x_1129_; size_t v___x_1130_; lean_object* v___x_1131_; 
lean_del_object(v___x_1120_);
v___x_1129_ = ((size_t)0ULL);
v___x_1130_ = lean_usize_of_nat(v___x_1123_);
v___x_1131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_vs_1118_, v___x_1129_, v___x_1130_, v___x_1124_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
lean_dec_ref(v_vs_1118_);
return v___x_1131_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4(lean_object* v_as_1133_, size_t v_i_1134_, size_t v_stop_1135_, lean_object* v_b_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
uint8_t v___x_1143_; 
v___x_1143_ = lean_usize_dec_eq(v_i_1134_, v_stop_1135_);
if (v___x_1143_ == 0)
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = lean_array_uget_borrowed(v_as_1133_, v_i_1134_);
lean_inc(v___x_1144_);
v___x_1145_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__3(v___x_1144_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; size_t v___x_1147_; size_t v___x_1148_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_a_1146_);
lean_dec_ref_known(v___x_1145_, 1);
v___x_1147_ = ((size_t)1ULL);
v___x_1148_ = lean_usize_add(v_i_1134_, v___x_1147_);
v_i_1134_ = v___x_1148_;
v_b_1136_ = v_a_1146_;
goto _start;
}
else
{
return v___x_1145_;
}
}
else
{
lean_object* v___x_1150_; 
v___x_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1150_, 0, v_b_1136_);
return v___x_1150_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_as_1151_, lean_object* v_i_1152_, lean_object* v_stop_1153_, lean_object* v_b_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
size_t v_i_boxed_1161_; size_t v_stop_boxed_1162_; lean_object* v_res_1163_; 
v_i_boxed_1161_ = lean_unbox_usize(v_i_1152_);
lean_dec(v_i_1152_);
v_stop_boxed_1162_ = lean_unbox_usize(v_stop_1153_);
lean_dec(v_stop_1153_);
v_res_1163_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4(v_as_1151_, v_i_boxed_1161_, v_stop_boxed_1162_, v_b_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v_as_1151_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__3(v_x_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v___y_1165_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__3(lean_object* v_t_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v_root_1179_; lean_object* v_tail_1180_; lean_object* v___x_1181_; 
v_root_1179_ = lean_ctor_get(v_t_1172_, 0);
lean_inc_ref(v_root_1179_);
v_tail_1180_ = lean_ctor_get(v_t_1172_, 1);
lean_inc_ref(v_tail_1180_);
lean_dec_ref(v_t_1172_);
v___x_1181_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__3(v_root_1179_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1195_; 
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1195_ == 0)
{
lean_object* v_unused_1196_; 
v_unused_1196_ = lean_ctor_get(v___x_1181_, 0);
lean_dec(v_unused_1196_);
v___x_1183_ = v___x_1181_;
v_isShared_1184_ = v_isSharedCheck_1195_;
goto v_resetjp_1182_;
}
else
{
lean_dec(v___x_1181_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1195_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; uint8_t v___x_1188_; 
v___x_1185_ = lean_unsigned_to_nat(0u);
v___x_1186_ = lean_array_get_size(v_tail_1180_);
v___x_1187_ = lean_box(0);
v___x_1188_ = lean_nat_dec_lt(v___x_1185_, v___x_1186_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1190_; 
lean_dec_ref(v_tail_1180_);
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 0, v___x_1187_);
v___x_1190_ = v___x_1183_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1187_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
else
{
size_t v___x_1192_; size_t v___x_1193_; lean_object* v___x_1194_; 
lean_del_object(v___x_1183_);
v___x_1192_ = ((size_t)0ULL);
v___x_1193_ = lean_usize_of_nat(v___x_1186_);
v___x_1194_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_tail_1180_, v___x_1192_, v___x_1193_, v___x_1187_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
lean_dec_ref(v_tail_1180_);
return v___x_1194_;
}
}
}
else
{
lean_dec_ref(v_tail_1180_);
return v___x_1181_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__3___boxed(lean_object* v_t_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__3(v_t_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
return v_res_1204_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1205_; 
v___x_1205_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1(lean_object* v_x_1206_, size_t v_x_1207_, size_t v_x_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
if (lean_obj_tag(v_x_1206_) == 0)
{
lean_object* v_cs_1215_; lean_object* v___x_1216_; size_t v___x_1217_; lean_object* v_j_1218_; lean_object* v___x_1219_; size_t v___x_1220_; size_t v___x_1221_; size_t v___x_1222_; size_t v___x_1223_; size_t v___x_1224_; size_t v___x_1225_; lean_object* v___x_1226_; 
v_cs_1215_ = lean_ctor_get(v_x_1206_, 0);
lean_inc_ref(v_cs_1215_);
lean_dec_ref_known(v_x_1206_, 1);
v___x_1216_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___closed__0);
v___x_1217_ = lean_usize_shift_right(v_x_1207_, v_x_1208_);
v_j_1218_ = lean_usize_to_nat(v___x_1217_);
v___x_1219_ = lean_array_get_borrowed(v___x_1216_, v_cs_1215_, v_j_1218_);
v___x_1220_ = ((size_t)1ULL);
v___x_1221_ = lean_usize_shift_left(v___x_1220_, v_x_1208_);
v___x_1222_ = lean_usize_sub(v___x_1221_, v___x_1220_);
v___x_1223_ = lean_usize_land(v_x_1207_, v___x_1222_);
v___x_1224_ = ((size_t)5ULL);
v___x_1225_ = lean_usize_sub(v_x_1208_, v___x_1224_);
lean_inc(v___x_1219_);
v___x_1226_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1(v___x_1219_, v___x_1223_, v___x_1225_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1241_; 
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1241_ == 0)
{
lean_object* v_unused_1242_; 
v_unused_1242_ = lean_ctor_get(v___x_1226_, 0);
lean_dec(v_unused_1242_);
v___x_1228_ = v___x_1226_;
v_isShared_1229_ = v_isSharedCheck_1241_;
goto v_resetjp_1227_;
}
else
{
lean_dec(v___x_1226_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1241_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1230_ = lean_unsigned_to_nat(1u);
v___x_1231_ = lean_nat_add(v_j_1218_, v___x_1230_);
lean_dec(v_j_1218_);
v___x_1232_ = lean_array_get_size(v_cs_1215_);
v___x_1233_ = lean_box(0);
v___x_1234_ = lean_nat_dec_lt(v___x_1231_, v___x_1232_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1236_; 
lean_dec(v___x_1231_);
lean_dec_ref(v_cs_1215_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 0, v___x_1233_);
v___x_1236_ = v___x_1228_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1233_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
else
{
size_t v___x_1238_; size_t v___x_1239_; lean_object* v___x_1240_; 
lean_del_object(v___x_1228_);
v___x_1238_ = lean_usize_of_nat(v___x_1231_);
lean_dec(v___x_1231_);
v___x_1239_ = lean_usize_of_nat(v___x_1232_);
v___x_1240_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4(v_cs_1215_, v___x_1238_, v___x_1239_, v___x_1233_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
lean_dec_ref(v_cs_1215_);
return v___x_1240_;
}
}
}
else
{
lean_dec(v_j_1218_);
lean_dec_ref(v_cs_1215_);
return v___x_1226_;
}
}
else
{
lean_object* v_vs_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1257_; 
v_vs_1243_ = lean_ctor_get(v_x_1206_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v_x_1206_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1245_ = v_x_1206_;
v_isShared_1246_ = v_isSharedCheck_1257_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_vs_1243_);
lean_dec(v_x_1206_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1257_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; uint8_t v___x_1250_; 
v___x_1247_ = lean_usize_to_nat(v_x_1207_);
v___x_1248_ = lean_array_get_size(v_vs_1243_);
v___x_1249_ = lean_box(0);
v___x_1250_ = lean_nat_dec_lt(v___x_1247_, v___x_1248_);
if (v___x_1250_ == 0)
{
lean_object* v___x_1252_; 
lean_dec(v___x_1247_);
lean_dec_ref(v_vs_1243_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set_tag(v___x_1245_, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1249_);
v___x_1252_ = v___x_1245_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1249_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
else
{
size_t v___x_1254_; size_t v___x_1255_; lean_object* v___x_1256_; 
lean_del_object(v___x_1245_);
v___x_1254_ = lean_usize_of_nat(v___x_1247_);
lean_dec(v___x_1247_);
v___x_1255_ = lean_usize_of_nat(v___x_1248_);
v___x_1256_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_vs_1243_, v___x_1254_, v___x_1255_, v___x_1249_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
lean_dec_ref(v_vs_1243_);
return v___x_1256_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___boxed(lean_object* v_x_1258_, lean_object* v_x_1259_, lean_object* v_x_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
size_t v_x_8695__boxed_1267_; size_t v_x_8696__boxed_1268_; lean_object* v_res_1269_; 
v_x_8695__boxed_1267_ = lean_unbox_usize(v_x_1259_);
lean_dec(v_x_1259_);
v_x_8696__boxed_1268_ = lean_unbox_usize(v_x_1260_);
lean_dec(v_x_1260_);
v_res_1269_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1(v_x_1258_, v_x_8695__boxed_1267_, v_x_8696__boxed_1268_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec(v___y_1261_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0(lean_object* v_t_1270_, lean_object* v_start_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v___x_1278_; uint8_t v___x_1279_; 
v___x_1278_ = lean_unsigned_to_nat(0u);
v___x_1279_ = lean_nat_dec_eq(v_start_1271_, v___x_1278_);
if (v___x_1279_ == 0)
{
lean_object* v_root_1280_; lean_object* v_tail_1281_; size_t v_shift_1282_; lean_object* v_tailOff_1283_; uint8_t v___x_1284_; 
v_root_1280_ = lean_ctor_get(v_t_1270_, 0);
lean_inc_ref(v_root_1280_);
v_tail_1281_ = lean_ctor_get(v_t_1270_, 1);
lean_inc_ref(v_tail_1281_);
v_shift_1282_ = lean_ctor_get_usize(v_t_1270_, 4);
v_tailOff_1283_ = lean_ctor_get(v_t_1270_, 3);
lean_inc(v_tailOff_1283_);
lean_dec_ref(v_t_1270_);
v___x_1284_ = lean_nat_dec_le(v_tailOff_1283_, v_start_1271_);
if (v___x_1284_ == 0)
{
size_t v___x_1285_; lean_object* v___x_1286_; 
lean_dec(v_tailOff_1283_);
v___x_1285_ = lean_usize_of_nat(v_start_1271_);
v___x_1286_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1(v_root_1280_, v___x_1285_, v_shift_1282_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1299_; 
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1299_ == 0)
{
lean_object* v_unused_1300_; 
v_unused_1300_ = lean_ctor_get(v___x_1286_, 0);
lean_dec(v_unused_1300_);
v___x_1288_ = v___x_1286_;
v_isShared_1289_ = v_isSharedCheck_1299_;
goto v_resetjp_1287_;
}
else
{
lean_dec(v___x_1286_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1299_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; uint8_t v___x_1292_; 
v___x_1290_ = lean_array_get_size(v_tail_1281_);
v___x_1291_ = lean_box(0);
v___x_1292_ = lean_nat_dec_lt(v___x_1278_, v___x_1290_);
if (v___x_1292_ == 0)
{
lean_object* v___x_1294_; 
lean_dec_ref(v_tail_1281_);
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 0, v___x_1291_);
v___x_1294_ = v___x_1288_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v___x_1291_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
else
{
size_t v___x_1296_; size_t v___x_1297_; lean_object* v___x_1298_; 
lean_del_object(v___x_1288_);
v___x_1296_ = ((size_t)0ULL);
v___x_1297_ = lean_usize_of_nat(v___x_1290_);
v___x_1298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_tail_1281_, v___x_1296_, v___x_1297_, v___x_1291_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
lean_dec_ref(v_tail_1281_);
return v___x_1298_;
}
}
}
else
{
lean_dec_ref(v_tail_1281_);
return v___x_1286_;
}
}
else
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; uint8_t v___x_1304_; 
lean_dec_ref(v_root_1280_);
v___x_1301_ = lean_nat_sub(v_start_1271_, v_tailOff_1283_);
lean_dec(v_tailOff_1283_);
v___x_1302_ = lean_array_get_size(v_tail_1281_);
v___x_1303_ = lean_box(0);
v___x_1304_ = lean_nat_dec_lt(v___x_1301_, v___x_1302_);
if (v___x_1304_ == 0)
{
lean_object* v___x_1305_; 
lean_dec(v___x_1301_);
lean_dec_ref(v_tail_1281_);
v___x_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1303_);
return v___x_1305_;
}
else
{
size_t v___x_1306_; size_t v___x_1307_; lean_object* v___x_1308_; 
v___x_1306_ = lean_usize_of_nat(v___x_1301_);
lean_dec(v___x_1301_);
v___x_1307_ = lean_usize_of_nat(v___x_1302_);
v___x_1308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_tail_1281_, v___x_1306_, v___x_1307_, v___x_1303_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
lean_dec_ref(v_tail_1281_);
return v___x_1308_;
}
}
}
else
{
lean_object* v___x_1309_; 
v___x_1309_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__3(v_t_1270_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
return v___x_1309_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0___boxed(lean_object* v_t_1310_, lean_object* v_start_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0(v_t_1310_, v_start_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec(v_start_1311_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0(lean_object* v_lctx_1319_, lean_object* v_start_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v_decls_1327_; lean_object* v___x_1328_; 
v_decls_1327_ = lean_ctor_get(v_lctx_1319_, 1);
lean_inc_ref(v_decls_1327_);
lean_dec_ref(v_lctx_1319_);
v___x_1328_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0(v_decls_1327_, v_start_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0___boxed(lean_object* v_lctx_1329_, lean_object* v_start_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0(v_lctx_1329_, v_start_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec(v_start_1330_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___lam__0(lean_object* v_e_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
if (lean_obj_tag(v_e_1338_) == 1)
{
lean_object* v_fvarId_1345_; lean_object* v___x_1346_; 
v_fvarId_1345_ = lean_ctor_get(v_e_1338_, 0);
lean_inc(v_fvarId_1345_);
lean_dec_ref_known(v_e_1338_, 1);
v___x_1346_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1345_, v___y_1340_, v___y_1342_, v___y_1343_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v_a_1347_; lean_object* v___x_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1357_; 
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
lean_inc(v_a_1347_);
lean_dec_ref_known(v___x_1346_, 1);
v___x_1348_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg(v_a_1347_, v___y_1339_);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1357_ == 0)
{
lean_object* v_unused_1358_; 
v_unused_1358_ = lean_ctor_get(v___x_1348_, 0);
lean_dec(v_unused_1358_);
v___x_1350_ = v___x_1348_;
v_isShared_1351_ = v_isSharedCheck_1357_;
goto v_resetjp_1349_;
}
else
{
lean_dec(v___x_1348_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1357_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
uint8_t v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1355_; 
v___x_1352_ = 0;
v___x_1353_ = lean_box(v___x_1352_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 0, v___x_1353_);
v___x_1355_ = v___x_1350_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1353_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
else
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1366_; 
v_a_1359_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1361_ = v___x_1346_;
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1346_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1364_; 
if (v_isShared_1362_ == 0)
{
v___x_1364_ = v___x_1361_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_a_1359_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
else
{
if (lean_obj_tag(v_e_1338_) == 2)
{
lean_object* v_mvarId_1367_; lean_object* v___x_1368_; 
v_mvarId_1367_ = lean_ctor_get(v_e_1338_, 0);
lean_inc(v_mvarId_1367_);
lean_dec_ref_known(v_e_1338_, 1);
v___x_1368_ = l_Lean_MVarId_getDecl(v_mvarId_1367_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; lean_object* v_lctx_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_a_1369_);
lean_dec_ref_known(v___x_1368_, 1);
v_lctx_1370_ = lean_ctor_get(v_a_1369_, 1);
lean_inc_ref(v_lctx_1370_);
lean_dec(v_a_1369_);
v___x_1371_ = lean_unsigned_to_nat(0u);
v___x_1372_ = l_Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0(v_lctx_1370_, v___x_1371_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1381_; 
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1381_ == 0)
{
lean_object* v_unused_1382_; 
v_unused_1382_ = lean_ctor_get(v___x_1372_, 0);
lean_dec(v_unused_1382_);
v___x_1374_ = v___x_1372_;
v_isShared_1375_ = v_isSharedCheck_1381_;
goto v_resetjp_1373_;
}
else
{
lean_dec(v___x_1372_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1381_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
uint8_t v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1379_; 
v___x_1376_ = 0;
v___x_1377_ = lean_box(v___x_1376_);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 0, v___x_1377_);
v___x_1379_ = v___x_1374_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1377_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
else
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1390_; 
v_a_1383_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1385_ = v___x_1372_;
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1372_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1388_; 
if (v_isShared_1386_ == 0)
{
v___x_1388_ = v___x_1385_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_a_1383_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
}
else
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1398_; 
v_a_1391_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1393_ = v___x_1368_;
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1368_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
if (v_isShared_1394_ == 0)
{
v___x_1396_ = v___x_1393_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_a_1391_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
}
else
{
uint8_t v___x_1399_; 
v___x_1399_ = l_Lean_Expr_hasFVar(v_e_1338_);
if (v___x_1399_ == 0)
{
uint8_t v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1400_ = l_Lean_Expr_hasExprMVar(v_e_1338_);
lean_dec_ref(v_e_1338_);
v___x_1401_ = lean_box(v___x_1400_);
v___x_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1401_);
return v___x_1402_;
}
else
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
lean_dec_ref(v_e_1338_);
v___x_1403_ = lean_box(v___x_1399_);
v___x_1404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1403_);
return v___x_1404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___lam__0___boxed(lean_object* v_e_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___lam__0(v_e_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
return v_res_1412_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___redArg(lean_object* v_a_1413_, lean_object* v_x_1414_){
_start:
{
if (lean_obj_tag(v_x_1414_) == 0)
{
uint8_t v___x_1415_; 
v___x_1415_ = 0;
return v___x_1415_;
}
else
{
lean_object* v_key_1416_; lean_object* v_tail_1417_; uint8_t v___x_1418_; 
v_key_1416_ = lean_ctor_get(v_x_1414_, 0);
v_tail_1417_ = lean_ctor_get(v_x_1414_, 2);
v___x_1418_ = lean_expr_eqv(v_key_1416_, v_a_1413_);
if (v___x_1418_ == 0)
{
v_x_1414_ = v_tail_1417_;
goto _start;
}
else
{
return v___x_1418_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_a_1420_, lean_object* v_x_1421_){
_start:
{
uint8_t v_res_1422_; lean_object* v_r_1423_; 
v_res_1422_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___redArg(v_a_1420_, v_x_1421_);
lean_dec(v_x_1421_);
lean_dec_ref(v_a_1420_);
v_r_1423_ = lean_box(v_res_1422_);
return v_r_1423_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13_spec__14___redArg(lean_object* v_x_1424_, lean_object* v_x_1425_){
_start:
{
if (lean_obj_tag(v_x_1425_) == 0)
{
return v_x_1424_;
}
else
{
lean_object* v_key_1426_; lean_object* v_value_1427_; lean_object* v_tail_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1451_; 
v_key_1426_ = lean_ctor_get(v_x_1425_, 0);
v_value_1427_ = lean_ctor_get(v_x_1425_, 1);
v_tail_1428_ = lean_ctor_get(v_x_1425_, 2);
v_isSharedCheck_1451_ = !lean_is_exclusive(v_x_1425_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1430_ = v_x_1425_;
v_isShared_1431_ = v_isSharedCheck_1451_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_tail_1428_);
lean_inc(v_value_1427_);
lean_inc(v_key_1426_);
lean_dec(v_x_1425_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1451_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; uint64_t v___x_1433_; uint64_t v___x_1434_; uint64_t v___x_1435_; uint64_t v_fold_1436_; uint64_t v___x_1437_; uint64_t v___x_1438_; uint64_t v___x_1439_; size_t v___x_1440_; size_t v___x_1441_; size_t v___x_1442_; size_t v___x_1443_; size_t v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1447_; 
v___x_1432_ = lean_array_get_size(v_x_1424_);
v___x_1433_ = l_Lean_Expr_hash(v_key_1426_);
v___x_1434_ = 32ULL;
v___x_1435_ = lean_uint64_shift_right(v___x_1433_, v___x_1434_);
v_fold_1436_ = lean_uint64_xor(v___x_1433_, v___x_1435_);
v___x_1437_ = 16ULL;
v___x_1438_ = lean_uint64_shift_right(v_fold_1436_, v___x_1437_);
v___x_1439_ = lean_uint64_xor(v_fold_1436_, v___x_1438_);
v___x_1440_ = lean_uint64_to_usize(v___x_1439_);
v___x_1441_ = lean_usize_of_nat(v___x_1432_);
v___x_1442_ = ((size_t)1ULL);
v___x_1443_ = lean_usize_sub(v___x_1441_, v___x_1442_);
v___x_1444_ = lean_usize_land(v___x_1440_, v___x_1443_);
v___x_1445_ = lean_array_uget_borrowed(v_x_1424_, v___x_1444_);
lean_inc(v___x_1445_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 2, v___x_1445_);
v___x_1447_ = v___x_1430_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_key_1426_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v_value_1427_);
lean_ctor_set(v_reuseFailAlloc_1450_, 2, v___x_1445_);
v___x_1447_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
lean_object* v___x_1448_; 
v___x_1448_ = lean_array_uset(v_x_1424_, v___x_1444_, v___x_1447_);
v_x_1424_ = v___x_1448_;
v_x_1425_ = v_tail_1428_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13___redArg(lean_object* v_i_1452_, lean_object* v_source_1453_, lean_object* v_target_1454_){
_start:
{
lean_object* v___x_1455_; uint8_t v___x_1456_; 
v___x_1455_ = lean_array_get_size(v_source_1453_);
v___x_1456_ = lean_nat_dec_lt(v_i_1452_, v___x_1455_);
if (v___x_1456_ == 0)
{
lean_dec_ref(v_source_1453_);
lean_dec(v_i_1452_);
return v_target_1454_;
}
else
{
lean_object* v_es_1457_; lean_object* v___x_1458_; lean_object* v_source_1459_; lean_object* v_target_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v_es_1457_ = lean_array_fget(v_source_1453_, v_i_1452_);
v___x_1458_ = lean_box(0);
v_source_1459_ = lean_array_fset(v_source_1453_, v_i_1452_, v___x_1458_);
v_target_1460_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13_spec__14___redArg(v_target_1454_, v_es_1457_);
v___x_1461_ = lean_unsigned_to_nat(1u);
v___x_1462_ = lean_nat_add(v_i_1452_, v___x_1461_);
lean_dec(v_i_1452_);
v_i_1452_ = v___x_1462_;
v_source_1453_ = v_source_1459_;
v_target_1454_ = v_target_1460_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9___redArg(lean_object* v_data_1464_){
_start:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v_nbuckets_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1465_ = lean_array_get_size(v_data_1464_);
v___x_1466_ = lean_unsigned_to_nat(2u);
v_nbuckets_1467_ = lean_nat_mul(v___x_1465_, v___x_1466_);
v___x_1468_ = lean_unsigned_to_nat(0u);
v___x_1469_ = lean_box(0);
v___x_1470_ = lean_mk_array(v_nbuckets_1467_, v___x_1469_);
v___x_1471_ = lean_array_propagate_mark(v_data_1464_, v___x_1470_);
v___x_1472_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13___redArg(v___x_1468_, v_data_1464_, v___x_1471_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__10___redArg(lean_object* v_a_1473_, lean_object* v_b_1474_, lean_object* v_x_1475_){
_start:
{
if (lean_obj_tag(v_x_1475_) == 0)
{
lean_dec(v_b_1474_);
lean_dec_ref(v_a_1473_);
return v_x_1475_;
}
else
{
lean_object* v_key_1476_; lean_object* v_value_1477_; lean_object* v_tail_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1490_; 
v_key_1476_ = lean_ctor_get(v_x_1475_, 0);
v_value_1477_ = lean_ctor_get(v_x_1475_, 1);
v_tail_1478_ = lean_ctor_get(v_x_1475_, 2);
v_isSharedCheck_1490_ = !lean_is_exclusive(v_x_1475_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1480_ = v_x_1475_;
v_isShared_1481_ = v_isSharedCheck_1490_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_tail_1478_);
lean_inc(v_value_1477_);
lean_inc(v_key_1476_);
lean_dec(v_x_1475_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1490_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
uint8_t v___x_1482_; 
v___x_1482_ = lean_expr_eqv(v_key_1476_, v_a_1473_);
if (v___x_1482_ == 0)
{
lean_object* v___x_1483_; lean_object* v___x_1485_; 
v___x_1483_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__10___redArg(v_a_1473_, v_b_1474_, v_tail_1478_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 2, v___x_1483_);
v___x_1485_ = v___x_1480_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_key_1476_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v_value_1477_);
lean_ctor_set(v_reuseFailAlloc_1486_, 2, v___x_1483_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
else
{
lean_object* v___x_1488_; 
lean_dec(v_value_1477_);
lean_dec(v_key_1476_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 1, v_b_1474_);
lean_ctor_set(v___x_1480_, 0, v_a_1473_);
v___x_1488_ = v___x_1480_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1473_);
lean_ctor_set(v_reuseFailAlloc_1489_, 1, v_b_1474_);
lean_ctor_set(v_reuseFailAlloc_1489_, 2, v_tail_1478_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3___redArg(lean_object* v_m_1491_, lean_object* v_a_1492_, lean_object* v_b_1493_){
_start:
{
lean_object* v_size_1494_; lean_object* v_buckets_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1538_; 
v_size_1494_ = lean_ctor_get(v_m_1491_, 0);
v_buckets_1495_ = lean_ctor_get(v_m_1491_, 1);
v_isSharedCheck_1538_ = !lean_is_exclusive(v_m_1491_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1497_ = v_m_1491_;
v_isShared_1498_ = v_isSharedCheck_1538_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_buckets_1495_);
lean_inc(v_size_1494_);
lean_dec(v_m_1491_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1538_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1499_; uint64_t v___x_1500_; uint64_t v___x_1501_; uint64_t v___x_1502_; uint64_t v_fold_1503_; uint64_t v___x_1504_; uint64_t v___x_1505_; uint64_t v___x_1506_; size_t v___x_1507_; size_t v___x_1508_; size_t v___x_1509_; size_t v___x_1510_; size_t v___x_1511_; lean_object* v_bkt_1512_; uint8_t v___x_1513_; 
v___x_1499_ = lean_array_get_size(v_buckets_1495_);
v___x_1500_ = l_Lean_Expr_hash(v_a_1492_);
v___x_1501_ = 32ULL;
v___x_1502_ = lean_uint64_shift_right(v___x_1500_, v___x_1501_);
v_fold_1503_ = lean_uint64_xor(v___x_1500_, v___x_1502_);
v___x_1504_ = 16ULL;
v___x_1505_ = lean_uint64_shift_right(v_fold_1503_, v___x_1504_);
v___x_1506_ = lean_uint64_xor(v_fold_1503_, v___x_1505_);
v___x_1507_ = lean_uint64_to_usize(v___x_1506_);
v___x_1508_ = lean_usize_of_nat(v___x_1499_);
v___x_1509_ = ((size_t)1ULL);
v___x_1510_ = lean_usize_sub(v___x_1508_, v___x_1509_);
v___x_1511_ = lean_usize_land(v___x_1507_, v___x_1510_);
v_bkt_1512_ = lean_array_uget_borrowed(v_buckets_1495_, v___x_1511_);
v___x_1513_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___redArg(v_a_1492_, v_bkt_1512_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1514_; lean_object* v_size_x27_1515_; lean_object* v___x_1516_; lean_object* v_buckets_x27_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; uint8_t v___x_1523_; 
v___x_1514_ = lean_unsigned_to_nat(1u);
v_size_x27_1515_ = lean_nat_add(v_size_1494_, v___x_1514_);
lean_dec(v_size_1494_);
lean_inc(v_bkt_1512_);
v___x_1516_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1516_, 0, v_a_1492_);
lean_ctor_set(v___x_1516_, 1, v_b_1493_);
lean_ctor_set(v___x_1516_, 2, v_bkt_1512_);
v_buckets_x27_1517_ = lean_array_uset(v_buckets_1495_, v___x_1511_, v___x_1516_);
v___x_1518_ = lean_unsigned_to_nat(4u);
v___x_1519_ = lean_nat_mul(v_size_x27_1515_, v___x_1518_);
v___x_1520_ = lean_unsigned_to_nat(3u);
v___x_1521_ = lean_nat_div(v___x_1519_, v___x_1520_);
lean_dec(v___x_1519_);
v___x_1522_ = lean_array_get_size(v_buckets_x27_1517_);
v___x_1523_ = lean_nat_dec_le(v___x_1521_, v___x_1522_);
lean_dec(v___x_1521_);
if (v___x_1523_ == 0)
{
lean_object* v_val_1524_; lean_object* v___x_1526_; 
v_val_1524_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9___redArg(v_buckets_x27_1517_);
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 1, v_val_1524_);
lean_ctor_set(v___x_1497_, 0, v_size_x27_1515_);
v___x_1526_ = v___x_1497_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_size_x27_1515_);
lean_ctor_set(v_reuseFailAlloc_1527_, 1, v_val_1524_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
else
{
lean_object* v___x_1529_; 
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 1, v_buckets_x27_1517_);
lean_ctor_set(v___x_1497_, 0, v_size_x27_1515_);
v___x_1529_ = v___x_1497_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_size_x27_1515_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v_buckets_x27_1517_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
else
{
lean_object* v___x_1531_; lean_object* v_buckets_x27_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1536_; 
lean_inc(v_bkt_1512_);
v___x_1531_ = lean_box(0);
v_buckets_x27_1532_ = lean_array_uset(v_buckets_1495_, v___x_1511_, v___x_1531_);
v___x_1533_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__10___redArg(v_a_1492_, v_b_1493_, v_bkt_1512_);
v___x_1534_ = lean_array_uset(v_buckets_x27_1532_, v___x_1511_, v___x_1533_);
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 1, v___x_1534_);
v___x_1536_ = v___x_1497_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_size_1494_);
lean_ctor_set(v_reuseFailAlloc_1537_, 1, v___x_1534_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___redArg(lean_object* v_a_1539_, lean_object* v_x_1540_){
_start:
{
if (lean_obj_tag(v_x_1540_) == 0)
{
lean_object* v___x_1541_; 
v___x_1541_ = lean_box(0);
return v___x_1541_;
}
else
{
lean_object* v_key_1542_; lean_object* v_value_1543_; lean_object* v_tail_1544_; uint8_t v___x_1545_; 
v_key_1542_ = lean_ctor_get(v_x_1540_, 0);
v_value_1543_ = lean_ctor_get(v_x_1540_, 1);
v_tail_1544_ = lean_ctor_get(v_x_1540_, 2);
v___x_1545_ = lean_expr_eqv(v_key_1542_, v_a_1539_);
if (v___x_1545_ == 0)
{
v_x_1540_ = v_tail_1544_;
goto _start;
}
else
{
lean_object* v___x_1547_; 
lean_inc(v_value_1543_);
v___x_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1547_, 0, v_value_1543_);
return v___x_1547_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_a_1548_, lean_object* v_x_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___redArg(v_a_1548_, v_x_1549_);
lean_dec(v_x_1549_);
lean_dec_ref(v_a_1548_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___redArg(lean_object* v_m_1551_, lean_object* v_a_1552_){
_start:
{
lean_object* v_buckets_1553_; lean_object* v___x_1554_; uint64_t v___x_1555_; uint64_t v___x_1556_; uint64_t v___x_1557_; uint64_t v_fold_1558_; uint64_t v___x_1559_; uint64_t v___x_1560_; uint64_t v___x_1561_; size_t v___x_1562_; size_t v___x_1563_; size_t v___x_1564_; size_t v___x_1565_; size_t v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v_buckets_1553_ = lean_ctor_get(v_m_1551_, 1);
v___x_1554_ = lean_array_get_size(v_buckets_1553_);
v___x_1555_ = l_Lean_Expr_hash(v_a_1552_);
v___x_1556_ = 32ULL;
v___x_1557_ = lean_uint64_shift_right(v___x_1555_, v___x_1556_);
v_fold_1558_ = lean_uint64_xor(v___x_1555_, v___x_1557_);
v___x_1559_ = 16ULL;
v___x_1560_ = lean_uint64_shift_right(v_fold_1558_, v___x_1559_);
v___x_1561_ = lean_uint64_xor(v_fold_1558_, v___x_1560_);
v___x_1562_ = lean_uint64_to_usize(v___x_1561_);
v___x_1563_ = lean_usize_of_nat(v___x_1554_);
v___x_1564_ = ((size_t)1ULL);
v___x_1565_ = lean_usize_sub(v___x_1563_, v___x_1564_);
v___x_1566_ = lean_usize_land(v___x_1562_, v___x_1565_);
v___x_1567_ = lean_array_uget_borrowed(v_buckets_1553_, v___x_1566_);
v___x_1568_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___redArg(v_a_1552_, v___x_1567_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___redArg___boxed(lean_object* v_m_1569_, lean_object* v_a_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___redArg(v_m_1569_, v_a_1570_);
lean_dec_ref(v_a_1570_);
lean_dec_ref(v_m_1569_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(lean_object* v_g_1572_, lean_object* v_e_1573_, lean_object* v_a_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v_a_1582_; lean_object* v___y_1588_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = lean_st_ref_get(v_a_1574_);
v___x_1591_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___redArg(v___x_1590_, v_e_1573_);
lean_dec(v___x_1590_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v___x_1592_; 
lean_inc_ref(v_g_1572_);
lean_inc(v___y_1579_);
lean_inc_ref(v___y_1578_);
lean_inc(v___y_1577_);
lean_inc_ref(v___y_1576_);
lean_inc(v___y_1575_);
lean_inc_ref(v_e_1573_);
v___x_1592_ = lean_apply_7(v_g_1572_, v_e_1573_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, lean_box(0));
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v_a_1593_; lean_object* v_d_1595_; lean_object* v_b_1596_; lean_object* v___y_1597_; uint8_t v___x_1600_; 
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
lean_inc(v_a_1593_);
lean_dec_ref_known(v___x_1592_, 1);
v___x_1600_ = lean_unbox(v_a_1593_);
lean_dec(v_a_1593_);
if (v___x_1600_ == 0)
{
lean_object* v___x_1601_; 
lean_dec_ref(v_g_1572_);
v___x_1601_ = lean_box(0);
v_a_1582_ = v___x_1601_;
goto v___jp_1581_;
}
else
{
switch(lean_obj_tag(v_e_1573_))
{
case 7:
{
lean_object* v_binderType_1602_; lean_object* v_body_1603_; 
v_binderType_1602_ = lean_ctor_get(v_e_1573_, 1);
v_body_1603_ = lean_ctor_get(v_e_1573_, 2);
lean_inc_ref(v_body_1603_);
lean_inc_ref(v_binderType_1602_);
v_d_1595_ = v_binderType_1602_;
v_b_1596_ = v_body_1603_;
v___y_1597_ = v_a_1574_;
goto v___jp_1594_;
}
case 6:
{
lean_object* v_binderType_1604_; lean_object* v_body_1605_; 
v_binderType_1604_ = lean_ctor_get(v_e_1573_, 1);
v_body_1605_ = lean_ctor_get(v_e_1573_, 2);
lean_inc_ref(v_body_1605_);
lean_inc_ref(v_binderType_1604_);
v_d_1595_ = v_binderType_1604_;
v_b_1596_ = v_body_1605_;
v___y_1597_ = v_a_1574_;
goto v___jp_1594_;
}
case 8:
{
lean_object* v_type_1606_; lean_object* v_value_1607_; lean_object* v_body_1608_; lean_object* v___x_1609_; 
v_type_1606_ = lean_ctor_get(v_e_1573_, 1);
v_value_1607_ = lean_ctor_get(v_e_1573_, 2);
v_body_1608_ = lean_ctor_get(v_e_1573_, 3);
lean_inc_ref(v_type_1606_);
lean_inc_ref(v_g_1572_);
v___x_1609_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1572_, v_type_1606_, v_a_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v___x_1610_; 
lean_dec_ref_known(v___x_1609_, 1);
lean_inc_ref(v_value_1607_);
lean_inc_ref(v_g_1572_);
v___x_1610_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1572_, v_value_1607_, v_a_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v___x_1611_; 
lean_dec_ref_known(v___x_1610_, 1);
lean_inc_ref(v_body_1608_);
v___x_1611_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1572_, v_body_1608_, v_a_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
v___y_1588_ = v___x_1611_;
goto v___jp_1587_;
}
else
{
lean_dec_ref(v_g_1572_);
v___y_1588_ = v___x_1610_;
goto v___jp_1587_;
}
}
else
{
lean_dec_ref(v_g_1572_);
v___y_1588_ = v___x_1609_;
goto v___jp_1587_;
}
}
case 5:
{
lean_object* v_fn_1612_; lean_object* v_arg_1613_; lean_object* v___x_1614_; 
v_fn_1612_ = lean_ctor_get(v_e_1573_, 0);
v_arg_1613_ = lean_ctor_get(v_e_1573_, 1);
lean_inc_ref(v_fn_1612_);
lean_inc_ref(v_g_1572_);
v___x_1614_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1572_, v_fn_1612_, v_a_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v___x_1615_; 
lean_dec_ref_known(v___x_1614_, 1);
lean_inc_ref(v_arg_1613_);
v___x_1615_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1572_, v_arg_1613_, v_a_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
v___y_1588_ = v___x_1615_;
goto v___jp_1587_;
}
else
{
lean_dec_ref(v_g_1572_);
v___y_1588_ = v___x_1614_;
goto v___jp_1587_;
}
}
case 10:
{
lean_object* v_expr_1616_; lean_object* v___x_1617_; 
v_expr_1616_ = lean_ctor_get(v_e_1573_, 1);
lean_inc_ref(v_expr_1616_);
v___x_1617_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1572_, v_expr_1616_, v_a_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
v___y_1588_ = v___x_1617_;
goto v___jp_1587_;
}
case 11:
{
lean_object* v_struct_1618_; lean_object* v___x_1619_; 
v_struct_1618_ = lean_ctor_get(v_e_1573_, 2);
lean_inc_ref(v_struct_1618_);
v___x_1619_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1572_, v_struct_1618_, v_a_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
v___y_1588_ = v___x_1619_;
goto v___jp_1587_;
}
default: 
{
lean_object* v___x_1620_; 
lean_dec_ref(v_g_1572_);
v___x_1620_ = lean_box(0);
v_a_1582_ = v___x_1620_;
goto v___jp_1581_;
}
}
}
v___jp_1594_:
{
lean_object* v___x_1598_; 
lean_inc_ref(v_g_1572_);
v___x_1598_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1572_, v_d_1595_, v___y_1597_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v___x_1599_; 
lean_dec_ref_known(v___x_1598_, 1);
v___x_1599_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1572_, v_b_1596_, v___y_1597_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
v___y_1588_ = v___x_1599_;
goto v___jp_1587_;
}
else
{
lean_dec_ref(v_b_1596_);
lean_dec_ref(v_g_1572_);
v___y_1588_ = v___x_1598_;
goto v___jp_1587_;
}
}
}
else
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
lean_dec_ref(v_e_1573_);
lean_dec_ref(v_g_1572_);
v_a_1621_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1623_ = v___x_1592_;
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1592_);
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
lean_object* v_val_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1636_; 
lean_dec_ref(v_e_1573_);
lean_dec_ref(v_g_1572_);
v_val_1629_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1631_ = v___x_1591_;
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_val_1629_);
lean_dec(v___x_1591_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1634_; 
if (v_isShared_1632_ == 0)
{
lean_ctor_set_tag(v___x_1631_, 0);
v___x_1634_ = v___x_1631_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_val_1629_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
v___jp_1581_:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1583_ = lean_st_ref_take(v_a_1574_);
v___x_1584_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3___redArg(v___x_1583_, v_e_1573_, v_a_1582_);
v___x_1585_ = lean_st_ref_put(v_a_1574_, v___x_1584_);
v___x_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1586_, 0, v_a_1582_);
return v___x_1586_;
}
v___jp_1587_:
{
if (lean_obj_tag(v___y_1588_) == 0)
{
lean_object* v_a_1589_; 
v_a_1589_ = lean_ctor_get(v___y_1588_, 0);
lean_inc(v_a_1589_);
lean_dec_ref_known(v___y_1588_, 1);
v_a_1582_ = v_a_1589_;
goto v___jp_1581_;
}
else
{
lean_dec_ref(v_e_1573_);
return v___y_1588_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1___boxed(lean_object* v_g_1637_, lean_object* v_e_1638_, lean_object* v_a_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1637_, v_e_1638_, v_a_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1640_);
lean_dec(v_a_1639_);
return v_res_1646_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__1(void){
_start:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1648_ = lean_box(0);
v___x_1649_ = lean_unsigned_to_nat(16u);
v___x_1650_ = lean_mk_array(v___x_1649_, v___x_1648_);
return v___x_1650_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__2(void){
_start:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1651_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__1, &l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__1_once, _init_l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__1);
v___x_1652_ = lean_unsigned_to_nat(0u);
v___x_1653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
lean_ctor_set(v___x_1653_, 1, v___x_1651_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar(lean_object* v_e_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_){
_start:
{
lean_object* v___f_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___f_1661_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__0));
v___x_1662_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__2, &l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__2_once, _init_l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__2);
v___x_1663_ = lean_st_mk_ref(v___x_1662_);
v___x_1664_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v___f_1661_, v_e_1654_, v___x_1663_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1673_; 
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1667_ = v___x_1664_;
v_isShared_1668_ = v_isSharedCheck_1673_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1664_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1673_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1669_; lean_object* v___x_1671_; 
v___x_1669_ = lean_st_ref_get(v___x_1663_);
lean_dec(v___x_1663_);
lean_dec(v___x_1669_);
if (v_isShared_1668_ == 0)
{
v___x_1671_ = v___x_1667_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_a_1665_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
else
{
lean_dec(v___x_1663_);
return v___x_1664_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___boxed(lean_object* v_e_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar(v_e_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_);
lean_dec(v_a_1679_);
lean_dec_ref(v_a_1678_);
lean_dec(v_a_1677_);
lean_dec_ref(v_a_1676_);
lean_dec(v_a_1675_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2(lean_object* v_00_u03b2_1682_, lean_object* v_m_1683_, lean_object* v_a_1684_){
_start:
{
lean_object* v___x_1685_; 
v___x_1685_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___redArg(v_m_1683_, v_a_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1686_, lean_object* v_m_1687_, lean_object* v_a_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2(v_00_u03b2_1686_, v_m_1687_, v_a_1688_);
lean_dec_ref(v_a_1688_);
lean_dec_ref(v_m_1687_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3(lean_object* v_00_u03b2_1690_, lean_object* v_m_1691_, lean_object* v_a_1692_, lean_object* v_b_1693_){
_start:
{
lean_object* v___x_1694_; 
v___x_1694_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3___redArg(v_m_1691_, v_a_1692_, v_b_1693_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_1695_, lean_object* v_a_1696_, lean_object* v_x_1697_){
_start:
{
lean_object* v___x_1698_; 
v___x_1698_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___redArg(v_a_1696_, v_x_1697_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1699_, lean_object* v_a_1700_, lean_object* v_x_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6(v_00_u03b2_1699_, v_a_1700_, v_x_1701_);
lean_dec(v_x_1701_);
lean_dec_ref(v_a_1700_);
return v_res_1702_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_1703_, lean_object* v_a_1704_, lean_object* v_x_1705_){
_start:
{
uint8_t v___x_1706_; 
v___x_1706_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___redArg(v_a_1704_, v_x_1705_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___boxed(lean_object* v_00_u03b2_1707_, lean_object* v_a_1708_, lean_object* v_x_1709_){
_start:
{
uint8_t v_res_1710_; lean_object* v_r_1711_; 
v_res_1710_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8(v_00_u03b2_1707_, v_a_1708_, v_x_1709_);
lean_dec(v_x_1709_);
lean_dec_ref(v_a_1708_);
v_r_1711_ = lean_box(v_res_1710_);
return v_r_1711_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9(lean_object* v_00_u03b2_1712_, lean_object* v_data_1713_){
_start:
{
lean_object* v___x_1714_; 
v___x_1714_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9___redArg(v_data_1713_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__10(lean_object* v_00_u03b2_1715_, lean_object* v_a_1716_, lean_object* v_b_1717_, lean_object* v_x_1718_){
_start:
{
lean_object* v___x_1719_; 
v___x_1719_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__10___redArg(v_a_1716_, v_b_1717_, v_x_1718_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6(lean_object* v_as_1720_, size_t v_i_1721_, size_t v_stop_1722_, lean_object* v_b_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v___x_1730_; 
v___x_1730_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___redArg(v_as_1720_, v_i_1721_, v_stop_1722_, v_b_1723_, v___y_1724_, v___y_1725_, v___y_1727_, v___y_1728_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* v_as_1731_, lean_object* v_i_1732_, lean_object* v_stop_1733_, lean_object* v_b_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
size_t v_i_boxed_1741_; size_t v_stop_boxed_1742_; lean_object* v_res_1743_; 
v_i_boxed_1741_ = lean_unbox_usize(v_i_1732_);
lean_dec(v_i_1732_);
v_stop_boxed_1742_ = lean_unbox_usize(v_stop_1733_);
lean_dec(v_stop_1733_);
v_res_1743_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6(v_as_1731_, v_i_boxed_1741_, v_stop_boxed_1742_, v_b_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v___y_1735_);
lean_dec_ref(v_as_1731_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13(lean_object* v_00_u03b2_1744_, lean_object* v_i_1745_, lean_object* v_source_1746_, lean_object* v_target_1747_){
_start:
{
lean_object* v___x_1748_; 
v___x_1748_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13___redArg(v_i_1745_, v_source_1746_, v_target_1747_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13_spec__14(lean_object* v_00_u03b2_1749_, lean_object* v_x_1750_, lean_object* v_x_1751_){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13_spec__14___redArg(v_x_1750_, v_x_1751_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___redArg(lean_object* v_e_1753_, lean_object* v___y_1754_){
_start:
{
uint8_t v___x_1756_; 
v___x_1756_ = l_Lean_Expr_hasMVar(v_e_1753_);
if (v___x_1756_ == 0)
{
lean_object* v___x_1757_; 
v___x_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1757_, 0, v_e_1753_);
return v___x_1757_;
}
else
{
lean_object* v___x_1758_; lean_object* v_mctx_1759_; lean_object* v___x_1760_; lean_object* v_fst_1761_; lean_object* v_snd_1762_; lean_object* v___x_1763_; lean_object* v_cache_1764_; lean_object* v_zetaDeltaFVarIds_1765_; lean_object* v_postponed_1766_; lean_object* v_diag_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1776_; 
v___x_1758_ = lean_st_ref_get(v___y_1754_);
v_mctx_1759_ = lean_ctor_get(v___x_1758_, 0);
lean_inc_ref(v_mctx_1759_);
lean_dec(v___x_1758_);
v___x_1760_ = l_Lean_instantiateMVarsCore(v_mctx_1759_, v_e_1753_);
v_fst_1761_ = lean_ctor_get(v___x_1760_, 0);
lean_inc(v_fst_1761_);
v_snd_1762_ = lean_ctor_get(v___x_1760_, 1);
lean_inc(v_snd_1762_);
lean_dec_ref(v___x_1760_);
v___x_1763_ = lean_st_ref_take(v___y_1754_);
v_cache_1764_ = lean_ctor_get(v___x_1763_, 1);
v_zetaDeltaFVarIds_1765_ = lean_ctor_get(v___x_1763_, 2);
v_postponed_1766_ = lean_ctor_get(v___x_1763_, 3);
v_diag_1767_ = lean_ctor_get(v___x_1763_, 4);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1776_ == 0)
{
lean_object* v_unused_1777_; 
v_unused_1777_ = lean_ctor_get(v___x_1763_, 0);
lean_dec(v_unused_1777_);
v___x_1769_ = v___x_1763_;
v_isShared_1770_ = v_isSharedCheck_1776_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_diag_1767_);
lean_inc(v_postponed_1766_);
lean_inc(v_zetaDeltaFVarIds_1765_);
lean_inc(v_cache_1764_);
lean_dec(v___x_1763_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1776_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 0, v_snd_1762_);
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_snd_1762_);
lean_ctor_set(v_reuseFailAlloc_1775_, 1, v_cache_1764_);
lean_ctor_set(v_reuseFailAlloc_1775_, 2, v_zetaDeltaFVarIds_1765_);
lean_ctor_set(v_reuseFailAlloc_1775_, 3, v_postponed_1766_);
lean_ctor_set(v_reuseFailAlloc_1775_, 4, v_diag_1767_);
v___x_1772_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1773_ = lean_st_ref_put(v___y_1754_, v___x_1772_);
v___x_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1774_, 0, v_fst_1761_);
return v___x_1774_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___redArg___boxed(lean_object* v_e_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___redArg(v_e_1778_, v___y_1779_);
lean_dec(v___y_1779_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0(lean_object* v_e_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v___x_1788_; 
v___x_1788_ = l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___redArg(v_e_1782_, v___y_1784_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___boxed(lean_object* v_e_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0(v_e_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertAfter_x27___lam__0(lean_object* v_type_1796_, lean_object* v_fvarId_1797_, lean_object* v_mvarId_1798_, lean_object* v_userName_1799_, lean_object* v_val_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v___x_1806_; lean_object* v_a_1807_; lean_object* v___x_1808_; 
v___x_1806_ = l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___redArg(v_type_1796_, v___y_1802_);
v_a_1807_ = lean_ctor_get(v___x_1806_, 0);
lean_inc(v_a_1807_);
lean_dec_ref(v___x_1806_);
v___x_1808_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1797_, v___y_1801_, v___y_1803_, v___y_1804_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_a_1809_);
lean_dec_ref_known(v___x_1808_, 1);
v___x_1810_ = lean_st_mk_ref(v_a_1809_);
lean_inc(v_a_1807_);
v___x_1811_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar(v_a_1807_, v___x_1810_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
lean_dec_ref_known(v___x_1811_, 1);
v___x_1812_ = lean_st_ref_get(v___x_1810_);
lean_dec(v___x_1810_);
v___x_1813_ = l_Lean_LocalDecl_fvarId(v___x_1812_);
lean_dec(v___x_1812_);
v___x_1814_ = l_Lean_MVarId_assertAfter(v_mvarId_1798_, v___x_1813_, v_userName_1799_, v_a_1807_, v_val_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
return v___x_1814_;
}
else
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1822_; 
lean_dec(v___x_1810_);
lean_dec(v_a_1807_);
lean_dec_ref(v_val_1800_);
lean_dec(v_userName_1799_);
lean_dec(v_mvarId_1798_);
v_a_1815_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1817_ = v___x_1811_;
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1811_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1820_; 
if (v_isShared_1818_ == 0)
{
v___x_1820_ = v___x_1817_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_a_1815_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
}
}
else
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1830_; 
lean_dec(v_a_1807_);
lean_dec_ref(v_val_1800_);
lean_dec(v_userName_1799_);
lean_dec(v_mvarId_1798_);
v_a_1823_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1825_ = v___x_1808_;
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1808_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1828_; 
if (v_isShared_1826_ == 0)
{
v___x_1828_ = v___x_1825_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_a_1823_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertAfter_x27___lam__0___boxed(lean_object* v_type_1831_, lean_object* v_fvarId_1832_, lean_object* v_mvarId_1833_, lean_object* v_userName_1834_, lean_object* v_val_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_Lean_MVarId_assertAfter_x27___lam__0(v_type_1831_, v_fvarId_1832_, v_mvarId_1833_, v_userName_1834_, v_val_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertAfter_x27(lean_object* v_mvarId_1842_, lean_object* v_fvarId_1843_, lean_object* v_userName_1844_, lean_object* v_type_1845_, lean_object* v_val_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_){
_start:
{
lean_object* v___f_1852_; lean_object* v___x_1853_; 
lean_inc(v_mvarId_1842_);
v___f_1852_ = lean_alloc_closure((void*)(l_Lean_MVarId_assertAfter_x27___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1852_, 0, v_type_1845_);
lean_closure_set(v___f_1852_, 1, v_fvarId_1843_);
lean_closure_set(v___f_1852_, 2, v_mvarId_1842_);
lean_closure_set(v___f_1852_, 3, v_userName_1844_);
lean_closure_set(v___f_1852_, 4, v_val_1846_);
v___x_1853_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(v_mvarId_1842_, v___f_1852_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertAfter_x27___boxed(lean_object* v_mvarId_1854_, lean_object* v_fvarId_1855_, lean_object* v_userName_1856_, lean_object* v_type_1857_, lean_object* v_val_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Lean_MVarId_assertAfter_x27(v_mvarId_1854_, v_fvarId_1855_, v_userName_1856_, v_type_1857_, v_val_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_);
lean_dec(v_a_1862_);
lean_dec_ref(v_a_1861_);
lean_dec(v_a_1860_);
lean_dec_ref(v_a_1859_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg(lean_object* v_mvarId_1865_, lean_object* v_f_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v___x_1869_; lean_object* v_mctx_1870_; lean_object* v_cache_1871_; lean_object* v_zetaDeltaFVarIds_1872_; lean_object* v_postponed_1873_; lean_object* v_diag_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1885_; 
v___x_1869_ = lean_st_ref_take(v___y_1867_);
v_mctx_1870_ = lean_ctor_get(v___x_1869_, 0);
v_cache_1871_ = lean_ctor_get(v___x_1869_, 1);
v_zetaDeltaFVarIds_1872_ = lean_ctor_get(v___x_1869_, 2);
v_postponed_1873_ = lean_ctor_get(v___x_1869_, 3);
v_diag_1874_ = lean_ctor_get(v___x_1869_, 4);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1876_ = v___x_1869_;
v_isShared_1877_ = v_isSharedCheck_1885_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_diag_1874_);
lean_inc(v_postponed_1873_);
lean_inc(v_zetaDeltaFVarIds_1872_);
lean_inc(v_cache_1871_);
lean_inc(v_mctx_1870_);
lean_dec(v___x_1869_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1885_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1881_; 
v___x_1878_ = lean_box(0);
v___x_1879_ = l_Lean_MetavarContext_modifyExprMVarLCtx(v_mctx_1870_, v_mvarId_1865_, v_f_1866_);
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 0, v___x_1879_);
v___x_1881_ = v___x_1876_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v___x_1879_);
lean_ctor_set(v_reuseFailAlloc_1884_, 1, v_cache_1871_);
lean_ctor_set(v_reuseFailAlloc_1884_, 2, v_zetaDeltaFVarIds_1872_);
lean_ctor_set(v_reuseFailAlloc_1884_, 3, v_postponed_1873_);
lean_ctor_set(v_reuseFailAlloc_1884_, 4, v_diag_1874_);
v___x_1881_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1882_ = lean_st_ref_put(v___y_1867_, v___x_1881_);
v___x_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1878_);
return v___x_1883_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg___boxed(lean_object* v_mvarId_1886_, lean_object* v_f_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg(v_mvarId_1886_, v_f_1887_, v___y_1888_);
lean_dec(v___y_1888_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1(lean_object* v_mvarId_1891_, lean_object* v_f_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v___x_1898_; 
v___x_1898_ = l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg(v_mvarId_1891_, v_f_1892_, v___y_1894_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___boxed(lean_object* v_mvarId_1899_, lean_object* v_f_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1(v_mvarId_1899_, v_f_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
return v_res_1906_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg___closed__0(void){
_start:
{
uint8_t v___x_1907_; lean_object* v___x_1908_; 
v___x_1907_ = 0;
v___x_1908_ = l_Lean_LocalDeclKind_ctorIdx(v___x_1907_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg(lean_object* v_upperBound_1909_, lean_object* v_hs_1910_, lean_object* v_fst_1911_, lean_object* v_a_1912_, lean_object* v_b_1913_){
_start:
{
lean_object* v_a_1915_; uint8_t v___x_1919_; 
v___x_1919_ = lean_nat_dec_lt(v_a_1912_, v_upperBound_1909_);
if (v___x_1919_ == 0)
{
lean_dec(v_a_1912_);
return v_b_1913_;
}
else
{
lean_object* v___x_1920_; uint8_t v_kind_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; uint8_t v___x_1924_; 
v___x_1920_ = lean_array_fget_borrowed(v_hs_1910_, v_a_1912_);
v_kind_1921_ = lean_ctor_get_uint8(v___x_1920_, sizeof(void*)*3 + 1);
v___x_1922_ = l_Lean_LocalDeclKind_ctorIdx(v_kind_1921_);
v___x_1923_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg___closed__0);
v___x_1924_ = lean_nat_dec_eq(v___x_1922_, v___x_1923_);
lean_dec(v___x_1922_);
if (v___x_1924_ == 0)
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1925_ = lean_box(0);
v___x_1926_ = lean_array_get_borrowed(v___x_1925_, v_fst_1911_, v_a_1912_);
lean_inc(v___x_1926_);
v___x_1927_ = l_Lean_LocalContext_setKind(v_b_1913_, v___x_1926_, v_kind_1921_);
v_a_1915_ = v___x_1927_;
goto v___jp_1914_;
}
else
{
v_a_1915_ = v_b_1913_;
goto v___jp_1914_;
}
}
v___jp_1914_:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1916_ = lean_unsigned_to_nat(1u);
v___x_1917_ = lean_nat_add(v_a_1912_, v___x_1916_);
lean_dec(v_a_1912_);
v_a_1912_ = v___x_1917_;
v_b_1913_ = v_a_1915_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg___boxed(lean_object* v_upperBound_1928_, lean_object* v_hs_1929_, lean_object* v_fst_1930_, lean_object* v_a_1931_, lean_object* v_b_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg(v_upperBound_1928_, v_hs_1929_, v_fst_1930_, v_a_1931_, v_b_1932_);
lean_dec_ref(v_fst_1930_);
lean_dec_ref(v_hs_1929_);
lean_dec(v_upperBound_1928_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___lam__0(lean_object* v___x_1934_, lean_object* v_hs_1935_, lean_object* v_fst_1936_, lean_object* v___x_1937_, lean_object* v_lctx_1938_){
_start:
{
lean_object* v___x_1939_; 
v___x_1939_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg(v___x_1934_, v_hs_1935_, v_fst_1936_, v___x_1937_, v_lctx_1938_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___lam__0___boxed(lean_object* v___x_1940_, lean_object* v_hs_1941_, lean_object* v_fst_1942_, lean_object* v___x_1943_, lean_object* v_lctx_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l_Lean_MVarId_assertHypotheses___lam__0(v___x_1940_, v_hs_1941_, v_fst_1942_, v___x_1943_, v_lctx_1944_);
lean_dec_ref(v_fst_1942_);
lean_dec_ref(v_hs_1941_);
lean_dec(v___x_1940_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__3(lean_object* v_as_1946_, size_t v_i_1947_, size_t v_stop_1948_, lean_object* v_b_1949_){
_start:
{
uint8_t v___x_1950_; 
v___x_1950_ = lean_usize_dec_eq(v_i_1947_, v_stop_1948_);
if (v___x_1950_ == 0)
{
size_t v___x_1951_; size_t v___x_1952_; lean_object* v___x_1953_; lean_object* v_userName_1954_; lean_object* v_type_1955_; uint8_t v_binderInfo_1956_; lean_object* v___x_1957_; 
v___x_1951_ = ((size_t)1ULL);
v___x_1952_ = lean_usize_sub(v_i_1947_, v___x_1951_);
v___x_1953_ = lean_array_uget_borrowed(v_as_1946_, v___x_1952_);
v_userName_1954_ = lean_ctor_get(v___x_1953_, 0);
v_type_1955_ = lean_ctor_get(v___x_1953_, 1);
v_binderInfo_1956_ = lean_ctor_get_uint8(v___x_1953_, sizeof(void*)*3);
lean_inc_ref(v_type_1955_);
lean_inc(v_userName_1954_);
v___x_1957_ = l_Lean_Expr_forallE___override(v_userName_1954_, v_type_1955_, v_b_1949_, v_binderInfo_1956_);
v_i_1947_ = v___x_1952_;
v_b_1949_ = v___x_1957_;
goto _start;
}
else
{
return v_b_1949_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__3___boxed(lean_object* v_as_1959_, lean_object* v_i_1960_, lean_object* v_stop_1961_, lean_object* v_b_1962_){
_start:
{
size_t v_i_boxed_1963_; size_t v_stop_boxed_1964_; lean_object* v_res_1965_; 
v_i_boxed_1963_ = lean_unbox_usize(v_i_1960_);
lean_dec(v_i_1960_);
v_stop_boxed_1964_ = lean_unbox_usize(v_stop_1961_);
lean_dec(v_stop_1961_);
v_res_1965_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__3(v_as_1959_, v_i_boxed_1963_, v_stop_boxed_1964_, v_b_1962_);
lean_dec_ref(v_as_1959_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2(lean_object* v_as_1966_, size_t v_i_1967_, size_t v_stop_1968_, lean_object* v_b_1969_){
_start:
{
uint8_t v___x_1970_; 
v___x_1970_ = lean_usize_dec_eq(v_i_1967_, v_stop_1968_);
if (v___x_1970_ == 0)
{
lean_object* v___x_1971_; lean_object* v_value_1972_; lean_object* v___x_1973_; size_t v___x_1974_; size_t v___x_1975_; 
v___x_1971_ = lean_array_uget_borrowed(v_as_1966_, v_i_1967_);
v_value_1972_ = lean_ctor_get(v___x_1971_, 2);
lean_inc_ref(v_value_1972_);
v___x_1973_ = l_Lean_Expr_app___override(v_b_1969_, v_value_1972_);
v___x_1974_ = ((size_t)1ULL);
v___x_1975_ = lean_usize_add(v_i_1967_, v___x_1974_);
v_i_1967_ = v___x_1975_;
v_b_1969_ = v___x_1973_;
goto _start;
}
else
{
return v_b_1969_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2___boxed(lean_object* v_as_1977_, lean_object* v_i_1978_, lean_object* v_stop_1979_, lean_object* v_b_1980_){
_start:
{
size_t v_i_boxed_1981_; size_t v_stop_boxed_1982_; lean_object* v_res_1983_; 
v_i_boxed_1981_ = lean_unbox_usize(v_i_1978_);
lean_dec(v_i_1978_);
v_stop_boxed_1982_ = lean_unbox_usize(v_stop_1979_);
lean_dec(v_stop_1979_);
v_res_1983_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2(v_as_1977_, v_i_boxed_1981_, v_stop_boxed_1982_, v_b_1980_);
lean_dec_ref(v_as_1977_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___lam__1(lean_object* v_mvarId_1984_, lean_object* v___x_1985_, uint8_t v___x_1986_, lean_object* v_hs_1987_, lean_object* v___x_1988_, lean_object* v___x_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_){
_start:
{
lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___x_2016_; 
lean_inc(v_mvarId_1984_);
v___x_2016_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1984_, v___x_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v___x_2017_; 
lean_dec_ref_known(v___x_2016_, 1);
lean_inc(v_mvarId_1984_);
v___x_2017_ = l_Lean_MVarId_getTag(v_mvarId_1984_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v_a_2018_; lean_object* v___x_2019_; 
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
lean_inc(v_a_2018_);
lean_dec_ref_known(v___x_2017_, 1);
lean_inc(v_mvarId_1984_);
v___x_2019_ = l_Lean_MVarId_getType(v_mvarId_1984_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2020_; lean_object* v___y_2022_; uint8_t v___x_2041_; 
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_a_2020_);
lean_dec_ref_known(v___x_2019_, 1);
v___x_2041_ = lean_nat_dec_lt(v___x_1988_, v___x_1985_);
if (v___x_2041_ == 0)
{
v___y_2022_ = v_a_2020_;
goto v___jp_2021_;
}
else
{
size_t v___x_2042_; size_t v___x_2043_; lean_object* v___x_2044_; 
v___x_2042_ = lean_usize_of_nat(v___x_1985_);
v___x_2043_ = ((size_t)0ULL);
v___x_2044_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__3(v_hs_1987_, v___x_2042_, v___x_2043_, v_a_2020_);
v___y_2022_ = v___x_2044_;
goto v___jp_2021_;
}
v___jp_2021_:
{
lean_object* v___x_2023_; 
v___x_2023_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_2022_, v_a_2018_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; uint8_t v___x_2025_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_a_2024_);
lean_dec_ref_known(v___x_2023_, 1);
v___x_2025_ = lean_nat_dec_lt(v___x_1988_, v___x_1985_);
if (v___x_2025_ == 0)
{
lean_inc(v_a_2024_);
v___y_1996_ = v_a_2024_;
v___y_1997_ = v_a_2024_;
goto v___jp_1995_;
}
else
{
uint8_t v___x_2026_; 
v___x_2026_ = lean_nat_dec_le(v___x_1985_, v___x_1985_);
if (v___x_2026_ == 0)
{
if (v___x_2025_ == 0)
{
lean_inc(v_a_2024_);
v___y_1996_ = v_a_2024_;
v___y_1997_ = v_a_2024_;
goto v___jp_1995_;
}
else
{
size_t v___x_2027_; size_t v___x_2028_; lean_object* v___x_2029_; 
v___x_2027_ = ((size_t)0ULL);
v___x_2028_ = lean_usize_of_nat(v___x_1985_);
lean_inc(v_a_2024_);
v___x_2029_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2(v_hs_1987_, v___x_2027_, v___x_2028_, v_a_2024_);
v___y_1996_ = v_a_2024_;
v___y_1997_ = v___x_2029_;
goto v___jp_1995_;
}
}
else
{
size_t v___x_2030_; size_t v___x_2031_; lean_object* v___x_2032_; 
v___x_2030_ = ((size_t)0ULL);
v___x_2031_ = lean_usize_of_nat(v___x_1985_);
lean_inc(v_a_2024_);
v___x_2032_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2(v_hs_1987_, v___x_2030_, v___x_2031_, v_a_2024_);
v___y_1996_ = v_a_2024_;
v___y_1997_ = v___x_2032_;
goto v___jp_1995_;
}
}
}
else
{
lean_object* v_a_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2040_; 
lean_dec(v___x_1988_);
lean_dec_ref(v_hs_1987_);
lean_dec(v___x_1985_);
lean_dec(v_mvarId_1984_);
v_a_2033_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2035_ = v___x_2023_;
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_a_2033_);
lean_dec(v___x_2023_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2038_; 
if (v_isShared_2036_ == 0)
{
v___x_2038_ = v___x_2035_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_a_2033_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
}
}
else
{
lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2052_; 
lean_dec(v_a_2018_);
lean_dec(v___x_1988_);
lean_dec_ref(v_hs_1987_);
lean_dec(v___x_1985_);
lean_dec(v_mvarId_1984_);
v_a_2045_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2047_ = v___x_2019_;
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_2019_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2048_ == 0)
{
v___x_2050_ = v___x_2047_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
else
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
lean_dec(v___x_1988_);
lean_dec_ref(v_hs_1987_);
lean_dec(v___x_1985_);
lean_dec(v_mvarId_1984_);
v_a_2053_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___x_2017_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_2017_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
else
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
lean_dec(v___x_1988_);
lean_dec_ref(v_hs_1987_);
lean_dec(v___x_1985_);
lean_dec(v_mvarId_1984_);
v_a_2061_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_2016_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2016_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_a_2061_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
v___jp_1995_:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; uint8_t v___x_2001_; lean_object* v___x_2002_; 
v___x_1998_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(v_mvarId_1984_, v___y_1997_, v___y_1991_);
lean_dec_ref(v___x_1998_);
v___x_1999_ = l_Lean_Expr_mvarId_x21(v___y_1996_);
lean_dec_ref(v___y_1996_);
v___x_2000_ = lean_box(0);
v___x_2001_ = 1;
lean_inc(v___x_1985_);
v___x_2002_ = l_Lean_Meta_introNCore(v___x_1999_, v___x_1985_, v___x_2000_, v___x_1986_, v___x_2001_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2003_; lean_object* v_fst_2004_; lean_object* v_snd_2005_; lean_object* v___f_2006_; lean_object* v___x_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2014_; 
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_a_2003_);
lean_dec_ref_known(v___x_2002_, 1);
v_fst_2004_ = lean_ctor_get(v_a_2003_, 0);
v_snd_2005_ = lean_ctor_get(v_a_2003_, 1);
lean_inc(v_fst_2004_);
v___f_2006_ = lean_alloc_closure((void*)(l_Lean_MVarId_assertHypotheses___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2006_, 0, v___x_1985_);
lean_closure_set(v___f_2006_, 1, v_hs_1987_);
lean_closure_set(v___f_2006_, 2, v_fst_2004_);
lean_closure_set(v___f_2006_, 3, v___x_1988_);
lean_inc(v_snd_2005_);
v___x_2007_ = l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg(v_snd_2005_, v___f_2006_, v___y_1991_);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2014_ == 0)
{
lean_object* v_unused_2015_; 
v_unused_2015_ = lean_ctor_get(v___x_2007_, 0);
lean_dec(v_unused_2015_);
v___x_2009_ = v___x_2007_;
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
else
{
lean_dec(v___x_2007_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2012_; 
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 0, v_a_2003_);
v___x_2012_ = v___x_2009_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_a_2003_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
else
{
lean_dec(v___x_1988_);
lean_dec_ref(v_hs_1987_);
lean_dec(v___x_1985_);
return v___x_2002_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___lam__1___boxed(lean_object* v_mvarId_2069_, lean_object* v___x_2070_, lean_object* v___x_2071_, lean_object* v_hs_2072_, lean_object* v___x_2073_, lean_object* v___x_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
uint8_t v___x_2897__boxed_2080_; lean_object* v_res_2081_; 
v___x_2897__boxed_2080_ = lean_unbox(v___x_2071_);
v_res_2081_ = l_Lean_MVarId_assertHypotheses___lam__1(v_mvarId_2069_, v___x_2070_, v___x_2897__boxed_2080_, v_hs_2072_, v___x_2073_, v___x_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses(lean_object* v_mvarId_2087_, lean_object* v_hs_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_){
_start:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; uint8_t v___x_2096_; 
v___x_2094_ = lean_array_get_size(v_hs_2088_);
v___x_2095_ = lean_unsigned_to_nat(0u);
v___x_2096_ = lean_nat_dec_eq(v___x_2094_, v___x_2095_);
if (v___x_2096_ == 0)
{
lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___f_2099_; lean_object* v___x_2100_; 
v___x_2097_ = ((lean_object*)(l_Lean_MVarId_assertHypotheses___closed__1));
v___x_2098_ = lean_box(v___x_2096_);
lean_inc(v_mvarId_2087_);
v___f_2099_ = lean_alloc_closure((void*)(l_Lean_MVarId_assertHypotheses___lam__1___boxed), 11, 6);
lean_closure_set(v___f_2099_, 0, v_mvarId_2087_);
lean_closure_set(v___f_2099_, 1, v___x_2094_);
lean_closure_set(v___f_2099_, 2, v___x_2098_);
lean_closure_set(v___f_2099_, 3, v_hs_2088_);
lean_closure_set(v___f_2099_, 4, v___x_2095_);
lean_closure_set(v___f_2099_, 5, v___x_2097_);
v___x_2100_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(v_mvarId_2087_, v___f_2099_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_);
return v___x_2100_;
}
else
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
lean_dec_ref(v_hs_2088_);
v___x_2101_ = ((lean_object*)(l_Lean_MVarId_assertHypotheses___closed__2));
v___x_2102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2101_);
lean_ctor_set(v___x_2102_, 1, v_mvarId_2087_);
v___x_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2102_);
return v___x_2103_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___boxed(lean_object* v_mvarId_2104_, lean_object* v_hs_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l_Lean_MVarId_assertHypotheses(v_mvarId_2104_, v_hs_2105_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_);
lean_dec(v_a_2109_);
lean_dec_ref(v_a_2108_);
lean_dec(v_a_2107_);
lean_dec_ref(v_a_2106_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0(lean_object* v_upperBound_2112_, lean_object* v_hs_2113_, lean_object* v_fst_2114_, lean_object* v_inst_2115_, lean_object* v_R_2116_, lean_object* v_a_2117_, lean_object* v_b_2118_, lean_object* v_c_2119_){
_start:
{
lean_object* v___x_2120_; 
v___x_2120_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg(v_upperBound_2112_, v_hs_2113_, v_fst_2114_, v_a_2117_, v_b_2118_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___boxed(lean_object* v_upperBound_2121_, lean_object* v_hs_2122_, lean_object* v_fst_2123_, lean_object* v_inst_2124_, lean_object* v_R_2125_, lean_object* v_a_2126_, lean_object* v_b_2127_, lean_object* v_c_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0(v_upperBound_2121_, v_hs_2122_, v_fst_2123_, v_inst_2124_, v_R_2125_, v_a_2126_, v_b_2127_, v_c_2128_);
lean_dec_ref(v_fst_2123_);
lean_dec_ref(v_hs_2122_);
lean_dec(v_upperBound_2121_);
return v_res_2129_;
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
