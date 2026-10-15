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
lean_object* lean_obj_tag_nat(lean_object*);
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
size_t v_x_1324__boxed_190_; size_t v_x_1325__boxed_191_; lean_object* v_res_192_; 
v_x_1324__boxed_190_ = lean_unbox_usize(v_x_186_);
lean_dec(v_x_186_);
v_x_1325__boxed_191_ = lean_unbox_usize(v_x_187_);
lean_dec(v_x_187_);
v_res_192_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(v_x_185_, v_x_1324__boxed_190_, v_x_1325__boxed_191_, v_x_188_, v_x_189_);
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
lean_object* v___x_204_; lean_object* v_mctx_205_; lean_object* v_cache_206_; lean_object* v_zetaDeltaFVarIds_207_; lean_object* v_postponed_208_; lean_object* v_diag_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_239_; 
v___x_204_ = lean_st_ref_take(v___y_202_);
v_mctx_205_ = lean_ctor_get(v___x_204_, 0);
v_cache_206_ = lean_ctor_get(v___x_204_, 1);
v_zetaDeltaFVarIds_207_ = lean_ctor_get(v___x_204_, 2);
v_postponed_208_ = lean_ctor_get(v___x_204_, 3);
v_diag_209_ = lean_ctor_get(v___x_204_, 4);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_239_ == 0)
{
v___x_211_ = v___x_204_;
v_isShared_212_ = v_isSharedCheck_239_;
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
v_isShared_212_ = v_isSharedCheck_239_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v_depth_213_; lean_object* v_levelAssignDepth_214_; lean_object* v_lmvarCounter_215_; lean_object* v_mvarCounter_216_; lean_object* v_lDecls_217_; lean_object* v_decls_218_; lean_object* v_userNames_219_; lean_object* v_lAssignment_220_; lean_object* v_eAssignment_221_; lean_object* v_dAssignment_222_; lean_object* v_instanceTypedMVars_223_; lean_object* v_synthNormMemo_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_238_; 
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
v_synthNormMemo_224_ = lean_ctor_get(v_mctx_205_, 11);
v_isSharedCheck_238_ = !lean_is_exclusive(v_mctx_205_);
if (v_isSharedCheck_238_ == 0)
{
v___x_226_ = v_mctx_205_;
v_isShared_227_ = v_isSharedCheck_238_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_synthNormMemo_224_);
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
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_238_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_231_; 
v___x_228_ = lean_box(0);
v___x_229_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0___redArg(v_eAssignment_221_, v_mvarId_200_, v_val_201_);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 8, v___x_229_);
v___x_231_ = v___x_226_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_depth_213_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v_levelAssignDepth_214_);
lean_ctor_set(v_reuseFailAlloc_237_, 2, v_lmvarCounter_215_);
lean_ctor_set(v_reuseFailAlloc_237_, 3, v_mvarCounter_216_);
lean_ctor_set(v_reuseFailAlloc_237_, 4, v_lDecls_217_);
lean_ctor_set(v_reuseFailAlloc_237_, 5, v_decls_218_);
lean_ctor_set(v_reuseFailAlloc_237_, 6, v_userNames_219_);
lean_ctor_set(v_reuseFailAlloc_237_, 7, v_lAssignment_220_);
lean_ctor_set(v_reuseFailAlloc_237_, 8, v___x_229_);
lean_ctor_set(v_reuseFailAlloc_237_, 9, v_dAssignment_222_);
lean_ctor_set(v_reuseFailAlloc_237_, 10, v_instanceTypedMVars_223_);
lean_ctor_set(v_reuseFailAlloc_237_, 11, v_synthNormMemo_224_);
v___x_231_ = v_reuseFailAlloc_237_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
lean_object* v___x_233_; 
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 0, v___x_231_);
v___x_233_ = v___x_211_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___x_231_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v_cache_206_);
lean_ctor_set(v_reuseFailAlloc_236_, 2, v_zetaDeltaFVarIds_207_);
lean_ctor_set(v_reuseFailAlloc_236_, 3, v_postponed_208_);
lean_ctor_set(v_reuseFailAlloc_236_, 4, v_diag_209_);
v___x_233_ = v_reuseFailAlloc_236_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = lean_st_ref_put(v___y_202_, v___x_233_);
v___x_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_228_);
return v___x_235_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg___boxed(lean_object* v_mvarId_240_, lean_object* v_val_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(v_mvarId_240_, v_val_241_, v___y_242_);
lean_dec(v___y_242_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assert___lam__0(lean_object* v_mvarId_245_, lean_object* v___x_246_, lean_object* v_name_247_, lean_object* v_type_248_, lean_object* v_val_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
lean_object* v___x_255_; 
lean_inc(v_mvarId_245_);
v___x_255_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_245_, v___x_246_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v___x_256_; 
lean_dec_ref_known(v___x_255_, 1);
lean_inc(v_mvarId_245_);
v___x_256_ = l_Lean_MVarId_getTag(v_mvarId_245_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v_a_257_; lean_object* v___x_258_; 
v_a_257_ = lean_ctor_get(v___x_256_, 0);
lean_inc(v_a_257_);
lean_dec_ref_known(v___x_256_, 1);
lean_inc(v_mvarId_245_);
v___x_258_ = l_Lean_MVarId_getType(v_mvarId_245_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v_a_259_; uint8_t v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v_a_259_ = lean_ctor_get(v___x_258_, 0);
lean_inc(v_a_259_);
lean_dec_ref_known(v___x_258_, 1);
v___x_260_ = 0;
v___x_261_ = l_Lean_mkForall(v_name_247_, v___x_260_, v_type_248_, v_a_259_);
v___x_262_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_261_, v_a_257_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v_a_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_273_; 
v_a_263_ = lean_ctor_get(v___x_262_, 0);
lean_inc_n(v_a_263_, 2);
lean_dec_ref_known(v___x_262_, 1);
v___x_264_ = l_Lean_Expr_app___override(v_a_263_, v_val_249_);
v___x_265_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(v_mvarId_245_, v___x_264_, v___y_251_);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_273_ == 0)
{
lean_object* v_unused_274_; 
v_unused_274_ = lean_ctor_get(v___x_265_, 0);
lean_dec(v_unused_274_);
v___x_267_ = v___x_265_;
v_isShared_268_ = v_isSharedCheck_273_;
goto v_resetjp_266_;
}
else
{
lean_dec(v___x_265_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_273_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_269_; lean_object* v___x_271_; 
v___x_269_ = l_Lean_Expr_mvarId_x21(v_a_263_);
lean_dec(v_a_263_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 0, v___x_269_);
v___x_271_ = v___x_267_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v___x_269_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
else
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_282_; 
lean_dec_ref(v_val_249_);
lean_dec(v_mvarId_245_);
v_a_275_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_282_ == 0)
{
v___x_277_ = v___x_262_;
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_262_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_280_; 
if (v_isShared_278_ == 0)
{
v___x_280_ = v___x_277_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_a_275_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
else
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_290_; 
lean_dec(v_a_257_);
lean_dec_ref(v_val_249_);
lean_dec_ref(v_type_248_);
lean_dec(v_name_247_);
lean_dec(v_mvarId_245_);
v_a_283_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_290_ == 0)
{
v___x_285_ = v___x_258_;
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_258_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_286_ == 0)
{
v___x_288_ = v___x_285_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_a_283_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
else
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
lean_dec_ref(v_val_249_);
lean_dec_ref(v_type_248_);
lean_dec(v_name_247_);
lean_dec(v_mvarId_245_);
v_a_291_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_298_ == 0)
{
v___x_293_ = v___x_256_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_256_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_a_291_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
else
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_306_; 
lean_dec_ref(v_val_249_);
lean_dec_ref(v_type_248_);
lean_dec(v_name_247_);
lean_dec(v_mvarId_245_);
v_a_299_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_306_ == 0)
{
v___x_301_ = v___x_255_;
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_255_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_304_; 
if (v_isShared_302_ == 0)
{
v___x_304_ = v___x_301_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_a_299_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assert___lam__0___boxed(lean_object* v_mvarId_307_, lean_object* v___x_308_, lean_object* v_name_309_, lean_object* v_type_310_, lean_object* v_val_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_MVarId_assert___lam__0(v_mvarId_307_, v___x_308_, v_name_309_, v_type_310_, v_val_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assert(lean_object* v_mvarId_321_, lean_object* v_name_322_, lean_object* v_type_323_, lean_object* v_val_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v___x_330_; lean_object* v___f_331_; lean_object* v___x_332_; 
v___x_330_ = ((lean_object*)(l_Lean_MVarId_assert___closed__1));
lean_inc(v_mvarId_321_);
v___f_331_ = lean_alloc_closure((void*)(l_Lean_MVarId_assert___lam__0___boxed), 10, 5);
lean_closure_set(v___f_331_, 0, v_mvarId_321_);
lean_closure_set(v___f_331_, 1, v___x_330_);
lean_closure_set(v___f_331_, 2, v_name_322_);
lean_closure_set(v___f_331_, 3, v_type_323_);
lean_closure_set(v___f_331_, 4, v_val_324_);
v___x_332_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(v_mvarId_321_, v___f_331_, v_a_325_, v_a_326_, v_a_327_, v_a_328_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assert___boxed(lean_object* v_mvarId_333_, lean_object* v_name_334_, lean_object* v_type_335_, lean_object* v_val_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_MVarId_assert(v_mvarId_333_, v_name_334_, v_type_335_, v_val_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_);
lean_dec(v_a_340_);
lean_dec_ref(v_a_339_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0(lean_object* v_mvarId_343_, lean_object* v_val_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(v_mvarId_343_, v_val_344_, v___y_346_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___boxed(lean_object* v_mvarId_351_, lean_object* v_val_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0(v_mvarId_351_, v_val_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0(lean_object* v_00_u03b2_359_, lean_object* v_x_360_, lean_object* v_x_361_, lean_object* v_x_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0___redArg(v_x_360_, v_x_361_, v_x_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_364_, lean_object* v_x_365_, size_t v_x_366_, size_t v_x_367_, lean_object* v_x_368_, lean_object* v_x_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(v_x_365_, v_x_366_, v_x_367_, v_x_368_, v_x_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_371_, lean_object* v_x_372_, lean_object* v_x_373_, lean_object* v_x_374_, lean_object* v_x_375_, lean_object* v_x_376_){
_start:
{
size_t v_x_1702__boxed_377_; size_t v_x_1703__boxed_378_; lean_object* v_res_379_; 
v_x_1702__boxed_377_ = lean_unbox_usize(v_x_373_);
lean_dec(v_x_373_);
v_x_1703__boxed_378_ = lean_unbox_usize(v_x_374_);
lean_dec(v_x_374_);
v_res_379_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2(v_00_u03b2_371_, v_x_372_, v_x_1702__boxed_377_, v_x_1703__boxed_378_, v_x_375_, v_x_376_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_380_, lean_object* v_n_381_, lean_object* v_k_382_, lean_object* v_v_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3___redArg(v_n_381_, v_k_382_, v_v_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_385_, size_t v_depth_386_, lean_object* v_keys_387_, lean_object* v_vals_388_, lean_object* v_heq_389_, lean_object* v_i_390_, lean_object* v_entries_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_386_, v_keys_387_, v_vals_388_, v_i_390_, v_entries_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_393_, lean_object* v_depth_394_, lean_object* v_keys_395_, lean_object* v_vals_396_, lean_object* v_heq_397_, lean_object* v_i_398_, lean_object* v_entries_399_){
_start:
{
size_t v_depth_boxed_400_; lean_object* v_res_401_; 
v_depth_boxed_400_ = lean_unbox_usize(v_depth_394_);
lean_dec(v_depth_394_);
v_res_401_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_393_, v_depth_boxed_400_, v_keys_395_, v_vals_396_, v_heq_397_, v_i_398_, v_entries_399_);
lean_dec_ref(v_vals_396_);
lean_dec_ref(v_keys_395_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_402_, lean_object* v_x_403_, lean_object* v_x_404_, lean_object* v_x_405_, lean_object* v_x_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_403_, v_x_404_, v_x_405_, v_x_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_note(lean_object* v_g_408_, lean_object* v_h_409_, lean_object* v_v_410_, lean_object* v_t_x3f_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
lean_object* v_____do__lift_418_; lean_object* v___y_419_; lean_object* v___y_420_; lean_object* v___y_421_; lean_object* v___y_422_; 
if (lean_obj_tag(v_t_x3f_411_) == 0)
{
lean_object* v___x_435_; 
lean_inc(v_a_415_);
lean_inc_ref(v_a_414_);
lean_inc(v_a_413_);
lean_inc_ref(v_a_412_);
lean_inc_ref(v_v_410_);
v___x_435_ = lean_infer_type(v_v_410_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_a_436_);
lean_dec_ref_known(v___x_435_, 1);
v_____do__lift_418_ = v_a_436_;
v___y_419_ = v_a_412_;
v___y_420_ = v_a_413_;
v___y_421_ = v_a_414_;
v___y_422_ = v_a_415_;
goto v___jp_417_;
}
else
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_444_; 
lean_dec_ref(v_v_410_);
lean_dec(v_h_409_);
lean_dec(v_g_408_);
v_a_437_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_444_ == 0)
{
v___x_439_ = v___x_435_;
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_435_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_442_; 
if (v_isShared_440_ == 0)
{
v___x_442_ = v___x_439_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_a_437_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
else
{
lean_object* v_val_445_; 
v_val_445_ = lean_ctor_get(v_t_x3f_411_, 0);
lean_inc(v_val_445_);
lean_dec_ref_known(v_t_x3f_411_, 1);
v_____do__lift_418_ = v_val_445_;
v___y_419_ = v_a_412_;
v___y_420_ = v_a_413_;
v___y_421_ = v_a_414_;
v___y_422_ = v_a_415_;
goto v___jp_417_;
}
v___jp_417_:
{
lean_object* v___x_423_; 
v___x_423_ = l_Lean_MVarId_assert(v_g_408_, v_h_409_, v_____do__lift_418_, v_v_410_, v___y_419_, v___y_420_, v___y_421_, v___y_422_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_a_424_; uint8_t v___x_425_; lean_object* v___x_426_; 
v_a_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_a_424_);
lean_dec_ref_known(v___x_423_, 1);
v___x_425_ = 1;
v___x_426_ = l_Lean_Meta_intro1Core(v_a_424_, v___x_425_, v___y_419_, v___y_420_, v___y_421_, v___y_422_);
return v___x_426_;
}
else
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_434_; 
v_a_427_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_434_ == 0)
{
v___x_429_ = v___x_423_;
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_423_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_430_ == 0)
{
v___x_432_ = v___x_429_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_a_427_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_note___boxed(lean_object* v_g_446_, lean_object* v_h_447_, lean_object* v_v_448_, lean_object* v_t_x3f_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lean_MVarId_note(v_g_446_, v_h_447_, v_v_448_, v_t_x3f_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_);
lean_dec(v_a_453_);
lean_dec_ref(v_a_452_);
lean_dec(v_a_451_);
lean_dec_ref(v_a_450_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_define___lam__0(lean_object* v_mvarId_456_, lean_object* v___x_457_, lean_object* v_name_458_, lean_object* v_type_459_, lean_object* v_val_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
lean_object* v___x_466_; 
lean_inc(v_mvarId_456_);
v___x_466_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_456_, v___x_457_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v___x_467_; 
lean_dec_ref_known(v___x_466_, 1);
lean_inc(v_mvarId_456_);
v___x_467_ = l_Lean_MVarId_getTag(v_mvarId_456_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v_a_468_; lean_object* v___x_469_; 
v_a_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_a_468_);
lean_dec_ref_known(v___x_467_, 1);
lean_inc(v_mvarId_456_);
v___x_469_ = l_Lean_MVarId_getType(v_mvarId_456_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; uint8_t v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_a_470_);
lean_dec_ref_known(v___x_469_, 1);
v___x_471_ = 0;
v___x_472_ = l_Lean_Expr_letE___override(v_name_458_, v_type_459_, v_val_460_, v_a_470_, v___x_471_);
v___x_473_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_472_, v_a_468_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; lean_object* v___x_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_483_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
lean_inc_n(v_a_474_, 2);
lean_dec_ref_known(v___x_473_, 1);
v___x_475_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(v_mvarId_456_, v_a_474_, v___y_462_);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_483_ == 0)
{
lean_object* v_unused_484_; 
v_unused_484_ = lean_ctor_get(v___x_475_, 0);
lean_dec(v_unused_484_);
v___x_477_ = v___x_475_;
v_isShared_478_ = v_isSharedCheck_483_;
goto v_resetjp_476_;
}
else
{
lean_dec(v___x_475_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_483_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_479_; lean_object* v___x_481_; 
v___x_479_ = l_Lean_Expr_mvarId_x21(v_a_474_);
lean_dec(v_a_474_);
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 0, v___x_479_);
v___x_481_ = v___x_477_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_479_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
else
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_492_; 
lean_dec(v_mvarId_456_);
v_a_485_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_492_ == 0)
{
v___x_487_ = v___x_473_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_473_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
if (v_isShared_488_ == 0)
{
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_485_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
else
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_500_; 
lean_dec(v_a_468_);
lean_dec_ref(v_val_460_);
lean_dec_ref(v_type_459_);
lean_dec(v_name_458_);
lean_dec(v_mvarId_456_);
v_a_493_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_500_ == 0)
{
v___x_495_ = v___x_469_;
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_469_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_498_; 
if (v_isShared_496_ == 0)
{
v___x_498_ = v___x_495_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_a_493_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
else
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_508_; 
lean_dec_ref(v_val_460_);
lean_dec_ref(v_type_459_);
lean_dec(v_name_458_);
lean_dec(v_mvarId_456_);
v_a_501_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_508_ == 0)
{
v___x_503_ = v___x_467_;
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_467_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_a_501_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
else
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_516_; 
lean_dec_ref(v_val_460_);
lean_dec_ref(v_type_459_);
lean_dec(v_name_458_);
lean_dec(v_mvarId_456_);
v_a_509_ = lean_ctor_get(v___x_466_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_516_ == 0)
{
v___x_511_ = v___x_466_;
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_466_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_512_ == 0)
{
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_509_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_define___lam__0___boxed(lean_object* v_mvarId_517_, lean_object* v___x_518_, lean_object* v_name_519_, lean_object* v_type_520_, lean_object* v_val_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_MVarId_define___lam__0(v_mvarId_517_, v___x_518_, v_name_519_, v_type_520_, v_val_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_define(lean_object* v_mvarId_531_, lean_object* v_name_532_, lean_object* v_type_533_, lean_object* v_val_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_){
_start:
{
lean_object* v___x_540_; lean_object* v___f_541_; lean_object* v___x_542_; 
v___x_540_ = ((lean_object*)(l_Lean_MVarId_define___closed__1));
lean_inc(v_mvarId_531_);
v___f_541_ = lean_alloc_closure((void*)(l_Lean_MVarId_define___lam__0___boxed), 10, 5);
lean_closure_set(v___f_541_, 0, v_mvarId_531_);
lean_closure_set(v___f_541_, 1, v___x_540_);
lean_closure_set(v___f_541_, 2, v_name_532_);
lean_closure_set(v___f_541_, 3, v_type_533_);
lean_closure_set(v___f_541_, 4, v_val_534_);
v___x_542_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(v_mvarId_531_, v___f_541_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_define___boxed(lean_object* v_mvarId_543_, lean_object* v_name_544_, lean_object* v_type_545_, lean_object* v_val_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_MVarId_define(v_mvarId_543_, v_name_544_, v_type_545_, v_val_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_);
lean_dec(v_a_550_);
lean_dec_ref(v_a_549_);
lean_dec(v_a_548_);
lean_dec_ref(v_a_547_);
return v_res_552_;
}
}
static lean_object* _init_l_Lean_MVarId_assertExt___lam__0___closed__2(void){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = lean_unsigned_to_nat(0u);
v___x_557_ = l_Lean_mkBVar(v___x_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertExt___lam__0(lean_object* v_mvarId_558_, lean_object* v___x_559_, lean_object* v_type_560_, lean_object* v_val_561_, lean_object* v_hName_562_, lean_object* v_name_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v___x_569_; 
lean_inc(v_mvarId_558_);
v___x_569_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_558_, v___x_559_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v___x_570_; 
lean_dec_ref_known(v___x_569_, 1);
lean_inc(v_mvarId_558_);
v___x_570_ = l_Lean_MVarId_getTag(v_mvarId_558_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_571_; lean_object* v___x_572_; 
v_a_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_a_571_);
lean_dec_ref_known(v___x_570_, 1);
lean_inc(v_mvarId_558_);
v___x_572_ = l_Lean_MVarId_getType(v_mvarId_558_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v___x_574_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_a_573_);
lean_dec_ref_known(v___x_572_, 1);
lean_inc_ref(v_type_560_);
v___x_574_ = l_Lean_Meta_getLevel(v_type_560_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; uint8_t v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_a_575_);
lean_dec_ref_known(v___x_574_, 1);
v___x_576_ = ((lean_object*)(l_Lean_MVarId_assertExt___lam__0___closed__1));
v___x_577_ = lean_box(0);
v___x_578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_578_, 0, v_a_575_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
v___x_579_ = l_Lean_mkConst(v___x_576_, v___x_578_);
v___x_580_ = lean_obj_once(&l_Lean_MVarId_assertExt___lam__0___closed__2, &l_Lean_MVarId_assertExt___lam__0___closed__2_once, _init_l_Lean_MVarId_assertExt___lam__0___closed__2);
lean_inc_ref(v_val_561_);
lean_inc_ref(v_type_560_);
v___x_581_ = l_Lean_mkApp3(v___x_579_, v_type_560_, v___x_580_, v_val_561_);
v___x_582_ = 0;
v___x_583_ = l_Lean_mkForall(v_hName_562_, v___x_582_, v___x_581_, v_a_573_);
v___x_584_ = l_Lean_mkForall(v_name_563_, v___x_582_, v_type_560_, v___x_583_);
v___x_585_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_584_, v_a_571_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; lean_object* v___x_587_; 
v_a_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc(v_a_586_);
lean_dec_ref_known(v___x_585_, 1);
lean_inc_ref(v_val_561_);
v___x_587_ = l_Lean_Meta_mkEqRefl(v_val_561_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_598_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_a_588_);
lean_dec_ref_known(v___x_587_, 1);
lean_inc(v_a_586_);
v___x_589_ = l_Lean_mkAppB(v_a_586_, v_val_561_, v_a_588_);
v___x_590_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(v_mvarId_558_, v___x_589_, v___y_565_);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_598_ == 0)
{
lean_object* v_unused_599_; 
v_unused_599_ = lean_ctor_get(v___x_590_, 0);
lean_dec(v_unused_599_);
v___x_592_ = v___x_590_;
v_isShared_593_ = v_isSharedCheck_598_;
goto v_resetjp_591_;
}
else
{
lean_dec(v___x_590_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_598_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_594_; lean_object* v___x_596_; 
v___x_594_ = l_Lean_Expr_mvarId_x21(v_a_586_);
lean_dec(v_a_586_);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 0, v___x_594_);
v___x_596_ = v___x_592_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_594_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
else
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_607_; 
lean_dec(v_a_586_);
lean_dec_ref(v_val_561_);
lean_dec(v_mvarId_558_);
v_a_600_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_607_ == 0)
{
v___x_602_ = v___x_587_;
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_587_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_600_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
else
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
lean_dec_ref(v_val_561_);
lean_dec(v_mvarId_558_);
v_a_608_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_615_ == 0)
{
v___x_610_ = v___x_585_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_585_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_a_608_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
else
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
lean_dec(v_a_573_);
lean_dec(v_a_571_);
lean_dec(v_name_563_);
lean_dec(v_hName_562_);
lean_dec_ref(v_val_561_);
lean_dec_ref(v_type_560_);
lean_dec(v_mvarId_558_);
v_a_616_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___x_574_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_574_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_a_616_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
else
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
lean_dec(v_a_571_);
lean_dec(v_name_563_);
lean_dec(v_hName_562_);
lean_dec_ref(v_val_561_);
lean_dec_ref(v_type_560_);
lean_dec(v_mvarId_558_);
v_a_624_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_572_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_572_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_624_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
else
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
lean_dec(v_name_563_);
lean_dec(v_hName_562_);
lean_dec_ref(v_val_561_);
lean_dec_ref(v_type_560_);
lean_dec(v_mvarId_558_);
v_a_632_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_639_ == 0)
{
v___x_634_ = v___x_570_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_570_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_a_632_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
lean_dec(v_name_563_);
lean_dec(v_hName_562_);
lean_dec_ref(v_val_561_);
lean_dec_ref(v_type_560_);
lean_dec(v_mvarId_558_);
v_a_640_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_569_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_569_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertExt___lam__0___boxed(lean_object* v_mvarId_648_, lean_object* v___x_649_, lean_object* v_type_650_, lean_object* v_val_651_, lean_object* v_hName_652_, lean_object* v_name_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lean_MVarId_assertExt___lam__0(v_mvarId_648_, v___x_649_, v_type_650_, v_val_651_, v_hName_652_, v_name_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertExt(lean_object* v_mvarId_660_, lean_object* v_name_661_, lean_object* v_type_662_, lean_object* v_val_663_, lean_object* v_hName_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_){
_start:
{
lean_object* v___x_670_; lean_object* v___f_671_; lean_object* v___x_672_; 
v___x_670_ = ((lean_object*)(l_Lean_MVarId_assert___closed__1));
lean_inc(v_mvarId_660_);
v___f_671_ = lean_alloc_closure((void*)(l_Lean_MVarId_assertExt___lam__0___boxed), 11, 6);
lean_closure_set(v___f_671_, 0, v_mvarId_660_);
lean_closure_set(v___f_671_, 1, v___x_670_);
lean_closure_set(v___f_671_, 2, v_type_662_);
lean_closure_set(v___f_671_, 3, v_val_663_);
lean_closure_set(v___f_671_, 4, v_hName_664_);
lean_closure_set(v___f_671_, 5, v_name_661_);
v___x_672_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(v_mvarId_660_, v___f_671_, v_a_665_, v_a_666_, v_a_667_, v_a_668_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertExt___boxed(lean_object* v_mvarId_673_, lean_object* v_name_674_, lean_object* v_type_675_, lean_object* v_val_676_, lean_object* v_hName_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lean_MVarId_assertExt(v_mvarId_673_, v_name_674_, v_type_675_, v_val_676_, v_hName_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_);
lean_dec(v_a_681_);
lean_dec_ref(v_a_680_);
lean_dec(v_a_679_);
lean_dec_ref(v_a_678_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___redArg(lean_object* v_t_684_, lean_object* v___y_685_){
_start:
{
lean_object* v___x_687_; lean_object* v_infoState_688_; uint8_t v_enabled_689_; 
v___x_687_ = lean_st_ref_get(v___y_685_);
v_infoState_688_ = lean_ctor_get(v___x_687_, 8);
lean_inc_ref(v_infoState_688_);
lean_dec(v___x_687_);
v_enabled_689_ = lean_ctor_get_uint8(v_infoState_688_, sizeof(void*)*3);
lean_dec_ref(v_infoState_688_);
if (v_enabled_689_ == 0)
{
lean_object* v___x_690_; lean_object* v___x_691_; 
lean_dec_ref(v_t_684_);
v___x_690_ = lean_box(0);
v___x_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
return v___x_691_;
}
else
{
lean_object* v___x_692_; lean_object* v_infoState_693_; lean_object* v_env_694_; lean_object* v_nextMacroScope_695_; lean_object* v_ngen_696_; lean_object* v_auxDeclNGen_697_; lean_object* v_traceState_698_; lean_object* v_cache_699_; lean_object* v_recordedDeps_700_; lean_object* v_messages_701_; lean_object* v_snapshotTasks_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_724_; 
v___x_692_ = lean_st_ref_take(v___y_685_);
v_infoState_693_ = lean_ctor_get(v___x_692_, 8);
v_env_694_ = lean_ctor_get(v___x_692_, 0);
v_nextMacroScope_695_ = lean_ctor_get(v___x_692_, 1);
v_ngen_696_ = lean_ctor_get(v___x_692_, 2);
v_auxDeclNGen_697_ = lean_ctor_get(v___x_692_, 3);
v_traceState_698_ = lean_ctor_get(v___x_692_, 4);
v_cache_699_ = lean_ctor_get(v___x_692_, 5);
v_recordedDeps_700_ = lean_ctor_get(v___x_692_, 6);
v_messages_701_ = lean_ctor_get(v___x_692_, 7);
v_snapshotTasks_702_ = lean_ctor_get(v___x_692_, 9);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_724_ == 0)
{
v___x_704_ = v___x_692_;
v_isShared_705_ = v_isSharedCheck_724_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_snapshotTasks_702_);
lean_inc(v_infoState_693_);
lean_inc(v_messages_701_);
lean_inc(v_recordedDeps_700_);
lean_inc(v_cache_699_);
lean_inc(v_traceState_698_);
lean_inc(v_auxDeclNGen_697_);
lean_inc(v_ngen_696_);
lean_inc(v_nextMacroScope_695_);
lean_inc(v_env_694_);
lean_dec(v___x_692_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_724_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
uint8_t v_enabled_706_; lean_object* v_assignment_707_; lean_object* v_lazyAssignment_708_; lean_object* v_trees_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_723_; 
v_enabled_706_ = lean_ctor_get_uint8(v_infoState_693_, sizeof(void*)*3);
v_assignment_707_ = lean_ctor_get(v_infoState_693_, 0);
v_lazyAssignment_708_ = lean_ctor_get(v_infoState_693_, 1);
v_trees_709_ = lean_ctor_get(v_infoState_693_, 2);
v_isSharedCheck_723_ = !lean_is_exclusive(v_infoState_693_);
if (v_isSharedCheck_723_ == 0)
{
v___x_711_ = v_infoState_693_;
v_isShared_712_ = v_isSharedCheck_723_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_trees_709_);
lean_inc(v_lazyAssignment_708_);
lean_inc(v_assignment_707_);
lean_dec(v_infoState_693_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_723_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_713_ = lean_box(0);
v___x_714_ = l_Lean_PersistentArray_push___redArg(v_trees_709_, v_t_684_);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 2, v___x_714_);
v___x_716_ = v___x_711_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_assignment_707_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_lazyAssignment_708_);
lean_ctor_set(v_reuseFailAlloc_722_, 2, v___x_714_);
lean_ctor_set_uint8(v_reuseFailAlloc_722_, sizeof(void*)*3, v_enabled_706_);
v___x_716_ = v_reuseFailAlloc_722_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_718_; 
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 8, v___x_716_);
v___x_718_ = v___x_704_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_env_694_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_nextMacroScope_695_);
lean_ctor_set(v_reuseFailAlloc_721_, 2, v_ngen_696_);
lean_ctor_set(v_reuseFailAlloc_721_, 3, v_auxDeclNGen_697_);
lean_ctor_set(v_reuseFailAlloc_721_, 4, v_traceState_698_);
lean_ctor_set(v_reuseFailAlloc_721_, 5, v_cache_699_);
lean_ctor_set(v_reuseFailAlloc_721_, 6, v_recordedDeps_700_);
lean_ctor_set(v_reuseFailAlloc_721_, 7, v_messages_701_);
lean_ctor_set(v_reuseFailAlloc_721_, 8, v___x_716_);
lean_ctor_set(v_reuseFailAlloc_721_, 9, v_snapshotTasks_702_);
v___x_718_ = v_reuseFailAlloc_721_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = lean_st_ref_put(v___y_685_, v___x_718_);
v___x_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_720_, 0, v___x_713_);
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
v_infoState_745_ = lean_ctor_get(v___x_744_, 8);
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
lean_object* v_a_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_792_; 
v_a_787_ = lean_array_uget_borrowed(v_as_760_, v_i_762_);
v___x_788_ = lean_array_fget(v_array_776_, v_start_777_);
v___x_789_ = lean_unsigned_to_nat(1u);
v___x_790_ = lean_nat_add(v_start_777_, v___x_789_);
lean_dec(v_start_777_);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 1, v___x_790_);
v___x_792_ = v___x_785_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_array_776_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_814_, 2, v_stop_778_);
v___x_792_ = v_reuseFailAlloc_814_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
lean_inc_n(v___x_788_, 2);
v___x_793_ = l_Lean_mkFVar(v___x_788_);
lean_inc_n(v_a_787_, 2);
v___x_794_ = l_Lean_Meta_FVarSubst_insert(v_fst_772_, v_a_787_, v___x_793_);
lean_inc_ref(v___x_759_);
v___x_795_ = l_Lean_LocalContext_get_x21(v___x_759_, v___x_788_);
v___x_796_ = l_Lean_LocalDecl_userName(v___x_795_);
lean_dec_ref(v___x_795_);
v___x_797_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
lean_ctor_set(v___x_797_, 1, v___x_788_);
lean_ctor_set(v___x_797_, 2, v_a_787_);
v___x_798_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
v___x_799_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0(v___x_798_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v___x_801_; 
lean_dec_ref_known(v___x_799_, 1);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 1, v___x_792_);
lean_ctor_set(v___x_774_, 0, v___x_794_);
v___x_801_ = v___x_774_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_794_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v___x_792_);
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
else
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
lean_dec(v___x_794_);
lean_dec_ref(v___x_792_);
lean_del_object(v___x_774_);
lean_dec_ref(v___x_759_);
v_a_806_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___x_799_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_799_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
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
lean_object* v_cs_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1118_; 
v_cs_1104_ = lean_ctor_get(v_x_1097_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v_x_1097_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1106_ = v_x_1097_;
v_isShared_1107_ = v_isSharedCheck_1118_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_cs_1104_);
lean_dec(v_x_1097_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1118_;
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
size_t v___x_1115_; size_t v___x_1116_; lean_object* v___x_1117_; 
lean_del_object(v___x_1106_);
v___x_1115_ = ((size_t)0ULL);
v___x_1116_ = lean_usize_of_nat(v___x_1109_);
v___x_1117_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4(v_cs_1104_, v___x_1115_, v___x_1116_, v___x_1110_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
lean_dec_ref(v_cs_1104_);
return v___x_1117_;
}
}
}
else
{
lean_object* v_vs_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1133_; 
v_vs_1119_ = lean_ctor_get(v_x_1097_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v_x_1097_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1121_ = v_x_1097_;
v_isShared_1122_ = v_isSharedCheck_1133_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_vs_1119_);
lean_dec(v_x_1097_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1133_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; uint8_t v___x_1126_; 
v___x_1123_ = lean_unsigned_to_nat(0u);
v___x_1124_ = lean_array_get_size(v_vs_1119_);
v___x_1125_ = lean_box(0);
v___x_1126_ = lean_nat_dec_lt(v___x_1123_, v___x_1124_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1128_; 
lean_dec_ref(v_vs_1119_);
if (v_isShared_1122_ == 0)
{
lean_ctor_set_tag(v___x_1121_, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1125_);
v___x_1128_ = v___x_1121_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1125_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
else
{
size_t v___x_1130_; size_t v___x_1131_; lean_object* v___x_1132_; 
lean_del_object(v___x_1121_);
v___x_1130_ = ((size_t)0ULL);
v___x_1131_ = lean_usize_of_nat(v___x_1124_);
v___x_1132_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_vs_1119_, v___x_1130_, v___x_1131_, v___x_1125_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
lean_dec_ref(v_vs_1119_);
return v___x_1132_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4(lean_object* v_as_1134_, size_t v_i_1135_, size_t v_stop_1136_, lean_object* v_b_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
uint8_t v___x_1144_; 
v___x_1144_ = lean_usize_dec_eq(v_i_1135_, v_stop_1136_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = lean_array_uget_borrowed(v_as_1134_, v_i_1135_);
lean_inc(v___x_1145_);
v___x_1146_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__3(v___x_1145_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; size_t v___x_1148_; size_t v___x_1149_; 
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
lean_inc(v_a_1147_);
lean_dec_ref_known(v___x_1146_, 1);
v___x_1148_ = ((size_t)1ULL);
v___x_1149_ = lean_usize_add(v_i_1135_, v___x_1148_);
v_i_1135_ = v___x_1149_;
v_b_1137_ = v_a_1147_;
goto _start;
}
else
{
return v___x_1146_;
}
}
else
{
lean_object* v___x_1151_; 
v___x_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1151_, 0, v_b_1137_);
return v___x_1151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_as_1152_, lean_object* v_i_1153_, lean_object* v_stop_1154_, lean_object* v_b_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
size_t v_i_boxed_1162_; size_t v_stop_boxed_1163_; lean_object* v_res_1164_; 
v_i_boxed_1162_ = lean_unbox_usize(v_i_1153_);
lean_dec(v_i_1153_);
v_stop_boxed_1163_ = lean_unbox_usize(v_stop_1154_);
lean_dec(v_stop_1154_);
v_res_1164_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4(v_as_1152_, v_i_boxed_1162_, v_stop_boxed_1163_, v_b_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec(v___y_1156_);
lean_dec_ref(v_as_1152_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__3(v_x_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__3(lean_object* v_t_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v_root_1180_; lean_object* v_tail_1181_; lean_object* v___x_1182_; 
v_root_1180_ = lean_ctor_get(v_t_1173_, 0);
lean_inc_ref(v_root_1180_);
v_tail_1181_ = lean_ctor_get(v_t_1173_, 1);
lean_inc_ref(v_tail_1181_);
lean_dec_ref(v_t_1173_);
v___x_1182_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__3(v_root_1180_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1196_; 
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1196_ == 0)
{
lean_object* v_unused_1197_; 
v_unused_1197_ = lean_ctor_get(v___x_1182_, 0);
lean_dec(v_unused_1197_);
v___x_1184_ = v___x_1182_;
v_isShared_1185_ = v_isSharedCheck_1196_;
goto v_resetjp_1183_;
}
else
{
lean_dec(v___x_1182_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1196_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; uint8_t v___x_1189_; 
v___x_1186_ = lean_unsigned_to_nat(0u);
v___x_1187_ = lean_array_get_size(v_tail_1181_);
v___x_1188_ = lean_box(0);
v___x_1189_ = lean_nat_dec_lt(v___x_1186_, v___x_1187_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1191_; 
lean_dec_ref(v_tail_1181_);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 0, v___x_1188_);
v___x_1191_ = v___x_1184_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1188_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
else
{
size_t v___x_1193_; size_t v___x_1194_; lean_object* v___x_1195_; 
lean_del_object(v___x_1184_);
v___x_1193_ = ((size_t)0ULL);
v___x_1194_ = lean_usize_of_nat(v___x_1187_);
v___x_1195_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_tail_1181_, v___x_1193_, v___x_1194_, v___x_1188_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
lean_dec_ref(v_tail_1181_);
return v___x_1195_;
}
}
}
else
{
lean_dec_ref(v_tail_1181_);
return v___x_1182_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__3___boxed(lean_object* v_t_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__3(v_t_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec(v___y_1199_);
return v_res_1205_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1(lean_object* v_x_1207_, size_t v_x_1208_, size_t v_x_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
if (lean_obj_tag(v_x_1207_) == 0)
{
lean_object* v_cs_1216_; lean_object* v___x_1217_; size_t v___x_1218_; lean_object* v_j_1219_; lean_object* v___x_1220_; size_t v___x_1221_; size_t v___x_1222_; size_t v___x_1223_; size_t v___x_1224_; size_t v___x_1225_; size_t v___x_1226_; lean_object* v___x_1227_; 
v_cs_1216_ = lean_ctor_get(v_x_1207_, 0);
lean_inc_ref(v_cs_1216_);
lean_dec_ref_known(v_x_1207_, 1);
v___x_1217_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___closed__0);
v___x_1218_ = lean_usize_shift_right(v_x_1208_, v_x_1209_);
v_j_1219_ = lean_usize_to_nat(v___x_1218_);
v___x_1220_ = lean_array_get_borrowed(v___x_1217_, v_cs_1216_, v_j_1219_);
v___x_1221_ = ((size_t)1ULL);
v___x_1222_ = lean_usize_shift_left(v___x_1221_, v_x_1209_);
v___x_1223_ = lean_usize_sub(v___x_1222_, v___x_1221_);
v___x_1224_ = lean_usize_land(v_x_1208_, v___x_1223_);
v___x_1225_ = ((size_t)5ULL);
v___x_1226_ = lean_usize_sub(v_x_1209_, v___x_1225_);
lean_inc(v___x_1220_);
v___x_1227_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1(v___x_1220_, v___x_1224_, v___x_1226_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1242_; 
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1242_ == 0)
{
lean_object* v_unused_1243_; 
v_unused_1243_ = lean_ctor_get(v___x_1227_, 0);
lean_dec(v_unused_1243_);
v___x_1229_ = v___x_1227_;
v_isShared_1230_ = v_isSharedCheck_1242_;
goto v_resetjp_1228_;
}
else
{
lean_dec(v___x_1227_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1242_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; uint8_t v___x_1235_; 
v___x_1231_ = lean_unsigned_to_nat(1u);
v___x_1232_ = lean_nat_add(v_j_1219_, v___x_1231_);
lean_dec(v_j_1219_);
v___x_1233_ = lean_array_get_size(v_cs_1216_);
v___x_1234_ = lean_box(0);
v___x_1235_ = lean_nat_dec_lt(v___x_1232_, v___x_1233_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1237_; 
lean_dec(v___x_1232_);
lean_dec_ref(v_cs_1216_);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 0, v___x_1234_);
v___x_1237_ = v___x_1229_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v___x_1234_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
else
{
size_t v___x_1239_; size_t v___x_1240_; lean_object* v___x_1241_; 
lean_del_object(v___x_1229_);
v___x_1239_ = lean_usize_of_nat(v___x_1232_);
lean_dec(v___x_1232_);
v___x_1240_ = lean_usize_of_nat(v___x_1233_);
v___x_1241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4(v_cs_1216_, v___x_1239_, v___x_1240_, v___x_1234_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
lean_dec_ref(v_cs_1216_);
return v___x_1241_;
}
}
}
else
{
lean_dec(v_j_1219_);
lean_dec_ref(v_cs_1216_);
return v___x_1227_;
}
}
else
{
lean_object* v_vs_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1258_; 
v_vs_1244_ = lean_ctor_get(v_x_1207_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v_x_1207_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1246_ = v_x_1207_;
v_isShared_1247_ = v_isSharedCheck_1258_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_vs_1244_);
lean_dec(v_x_1207_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1258_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
v___x_1248_ = lean_usize_to_nat(v_x_1208_);
v___x_1249_ = lean_array_get_size(v_vs_1244_);
v___x_1250_ = lean_box(0);
v___x_1251_ = lean_nat_dec_lt(v___x_1248_, v___x_1249_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1253_; 
lean_dec(v___x_1248_);
lean_dec_ref(v_vs_1244_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set_tag(v___x_1246_, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1250_);
v___x_1253_ = v___x_1246_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1250_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
else
{
size_t v___x_1255_; size_t v___x_1256_; lean_object* v___x_1257_; 
lean_del_object(v___x_1246_);
v___x_1255_ = lean_usize_of_nat(v___x_1248_);
lean_dec(v___x_1248_);
v___x_1256_ = lean_usize_of_nat(v___x_1249_);
v___x_1257_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_vs_1244_, v___x_1255_, v___x_1256_, v___x_1250_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
lean_dec_ref(v_vs_1244_);
return v___x_1257_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___boxed(lean_object* v_x_1259_, lean_object* v_x_1260_, lean_object* v_x_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
size_t v_x_8695__boxed_1268_; size_t v_x_8696__boxed_1269_; lean_object* v_res_1270_; 
v_x_8695__boxed_1268_ = lean_unbox_usize(v_x_1260_);
lean_dec(v_x_1260_);
v_x_8696__boxed_1269_ = lean_unbox_usize(v_x_1261_);
lean_dec(v_x_1261_);
v_res_1270_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1(v_x_1259_, v_x_8695__boxed_1268_, v_x_8696__boxed_1269_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec(v___y_1262_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0(lean_object* v_t_1271_, lean_object* v_start_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
lean_object* v___x_1279_; uint8_t v___x_1280_; 
v___x_1279_ = lean_unsigned_to_nat(0u);
v___x_1280_ = lean_nat_dec_eq(v_start_1272_, v___x_1279_);
if (v___x_1280_ == 0)
{
lean_object* v_root_1281_; lean_object* v_tail_1282_; size_t v_shift_1283_; lean_object* v_tailOff_1284_; uint8_t v___x_1285_; 
v_root_1281_ = lean_ctor_get(v_t_1271_, 0);
lean_inc_ref(v_root_1281_);
v_tail_1282_ = lean_ctor_get(v_t_1271_, 1);
lean_inc_ref(v_tail_1282_);
v_shift_1283_ = lean_ctor_get_usize(v_t_1271_, 4);
v_tailOff_1284_ = lean_ctor_get(v_t_1271_, 3);
lean_inc(v_tailOff_1284_);
lean_dec_ref(v_t_1271_);
v___x_1285_ = lean_nat_dec_le(v_tailOff_1284_, v_start_1272_);
if (v___x_1285_ == 0)
{
size_t v___x_1286_; lean_object* v___x_1287_; 
lean_dec(v_tailOff_1284_);
v___x_1286_ = lean_usize_of_nat(v_start_1272_);
v___x_1287_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1(v_root_1281_, v___x_1286_, v_shift_1283_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1300_; 
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1300_ == 0)
{
lean_object* v_unused_1301_; 
v_unused_1301_ = lean_ctor_get(v___x_1287_, 0);
lean_dec(v_unused_1301_);
v___x_1289_ = v___x_1287_;
v_isShared_1290_ = v_isSharedCheck_1300_;
goto v_resetjp_1288_;
}
else
{
lean_dec(v___x_1287_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1300_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; uint8_t v___x_1293_; 
v___x_1291_ = lean_array_get_size(v_tail_1282_);
v___x_1292_ = lean_box(0);
v___x_1293_ = lean_nat_dec_lt(v___x_1279_, v___x_1291_);
if (v___x_1293_ == 0)
{
lean_object* v___x_1295_; 
lean_dec_ref(v_tail_1282_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v___x_1292_);
v___x_1295_ = v___x_1289_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1292_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
else
{
size_t v___x_1297_; size_t v___x_1298_; lean_object* v___x_1299_; 
lean_del_object(v___x_1289_);
v___x_1297_ = ((size_t)0ULL);
v___x_1298_ = lean_usize_of_nat(v___x_1291_);
v___x_1299_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_tail_1282_, v___x_1297_, v___x_1298_, v___x_1292_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
lean_dec_ref(v_tail_1282_);
return v___x_1299_;
}
}
}
else
{
lean_dec_ref(v_tail_1282_);
return v___x_1287_;
}
}
else
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; uint8_t v___x_1305_; 
lean_dec_ref(v_root_1281_);
v___x_1302_ = lean_nat_sub(v_start_1272_, v_tailOff_1284_);
lean_dec(v_tailOff_1284_);
v___x_1303_ = lean_array_get_size(v_tail_1282_);
v___x_1304_ = lean_box(0);
v___x_1305_ = lean_nat_dec_lt(v___x_1302_, v___x_1303_);
if (v___x_1305_ == 0)
{
lean_object* v___x_1306_; 
lean_dec(v___x_1302_);
lean_dec_ref(v_tail_1282_);
v___x_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1304_);
return v___x_1306_;
}
else
{
size_t v___x_1307_; size_t v___x_1308_; lean_object* v___x_1309_; 
v___x_1307_ = lean_usize_of_nat(v___x_1302_);
lean_dec(v___x_1302_);
v___x_1308_ = lean_usize_of_nat(v___x_1303_);
v___x_1309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_tail_1282_, v___x_1307_, v___x_1308_, v___x_1304_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
lean_dec_ref(v_tail_1282_);
return v___x_1309_;
}
}
}
else
{
lean_object* v___x_1310_; 
v___x_1310_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__3(v_t_1271_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
return v___x_1310_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0___boxed(lean_object* v_t_1311_, lean_object* v_start_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0(v_t_1311_, v_start_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec(v___y_1313_);
lean_dec(v_start_1312_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0(lean_object* v_lctx_1320_, lean_object* v_start_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v_decls_1328_; lean_object* v___x_1329_; 
v_decls_1328_ = lean_ctor_get(v_lctx_1320_, 1);
lean_inc_ref(v_decls_1328_);
lean_dec_ref(v_lctx_1320_);
v___x_1329_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0(v_decls_1328_, v_start_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0___boxed(lean_object* v_lctx_1330_, lean_object* v_start_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l_Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0(v_lctx_1330_, v_start_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
lean_dec(v___y_1332_);
lean_dec(v_start_1331_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___lam__0(lean_object* v_e_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
if (lean_obj_tag(v_e_1339_) == 1)
{
lean_object* v_fvarId_1346_; lean_object* v___x_1347_; 
v_fvarId_1346_ = lean_ctor_get(v_e_1339_, 0);
lean_inc(v_fvarId_1346_);
lean_dec_ref_known(v_e_1339_, 1);
v___x_1347_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1346_, v___y_1341_, v___y_1343_, v___y_1344_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; lean_object* v___x_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1358_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_a_1348_);
lean_dec_ref_known(v___x_1347_, 1);
v___x_1349_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg(v_a_1348_, v___y_1340_);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1358_ == 0)
{
lean_object* v_unused_1359_; 
v_unused_1359_ = lean_ctor_get(v___x_1349_, 0);
lean_dec(v_unused_1359_);
v___x_1351_ = v___x_1349_;
v_isShared_1352_ = v_isSharedCheck_1358_;
goto v_resetjp_1350_;
}
else
{
lean_dec(v___x_1349_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1358_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
uint8_t v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1356_; 
v___x_1353_ = 0;
v___x_1354_ = lean_box(v___x_1353_);
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 0, v___x_1354_);
v___x_1356_ = v___x_1351_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___x_1354_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
v_a_1360_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1347_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1347_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
else
{
if (lean_obj_tag(v_e_1339_) == 2)
{
lean_object* v_mvarId_1368_; lean_object* v___x_1369_; 
v_mvarId_1368_ = lean_ctor_get(v_e_1339_, 0);
lean_inc(v_mvarId_1368_);
lean_dec_ref_known(v_e_1339_, 1);
v___x_1369_ = l_Lean_MVarId_getDecl(v_mvarId_1368_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_a_1370_; lean_object* v_lctx_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_a_1370_);
lean_dec_ref_known(v___x_1369_, 1);
v_lctx_1371_ = lean_ctor_get(v_a_1370_, 1);
lean_inc_ref(v_lctx_1371_);
lean_dec(v_a_1370_);
v___x_1372_ = lean_unsigned_to_nat(0u);
v___x_1373_ = l_Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0(v_lctx_1371_, v___x_1372_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1382_; 
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1382_ == 0)
{
lean_object* v_unused_1383_; 
v_unused_1383_ = lean_ctor_get(v___x_1373_, 0);
lean_dec(v_unused_1383_);
v___x_1375_ = v___x_1373_;
v_isShared_1376_ = v_isSharedCheck_1382_;
goto v_resetjp_1374_;
}
else
{
lean_dec(v___x_1373_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1382_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
uint8_t v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1380_; 
v___x_1377_ = 0;
v___x_1378_ = lean_box(v___x_1377_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 0, v___x_1378_);
v___x_1380_ = v___x_1375_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1378_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
else
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
v_a_1384_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1386_ = v___x_1373_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1373_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_a_1384_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
else
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1399_; 
v_a_1392_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1394_ = v___x_1369_;
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___x_1369_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1397_; 
if (v_isShared_1395_ == 0)
{
v___x_1397_ = v___x_1394_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_a_1392_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
}
else
{
uint8_t v___x_1400_; 
v___x_1400_ = l_Lean_Expr_hasFVar(v_e_1339_);
if (v___x_1400_ == 0)
{
uint8_t v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1401_ = l_Lean_Expr_hasExprMVar(v_e_1339_);
lean_dec_ref(v_e_1339_);
v___x_1402_ = lean_box(v___x_1401_);
v___x_1403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1402_);
return v___x_1403_;
}
else
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
lean_dec_ref(v_e_1339_);
v___x_1404_ = lean_box(v___x_1400_);
v___x_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1404_);
return v___x_1405_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___lam__0___boxed(lean_object* v_e_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___lam__0(v_e_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec(v___y_1407_);
return v_res_1413_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___redArg(lean_object* v_a_1414_, lean_object* v_x_1415_){
_start:
{
if (lean_obj_tag(v_x_1415_) == 0)
{
uint8_t v___x_1416_; 
v___x_1416_ = 0;
return v___x_1416_;
}
else
{
lean_object* v_key_1417_; lean_object* v_tail_1418_; uint8_t v___x_1419_; 
v_key_1417_ = lean_ctor_get(v_x_1415_, 0);
v_tail_1418_ = lean_ctor_get(v_x_1415_, 2);
v___x_1419_ = lean_expr_eqv(v_key_1417_, v_a_1414_);
if (v___x_1419_ == 0)
{
v_x_1415_ = v_tail_1418_;
goto _start;
}
else
{
return v___x_1419_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_a_1421_, lean_object* v_x_1422_){
_start:
{
uint8_t v_res_1423_; lean_object* v_r_1424_; 
v_res_1423_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___redArg(v_a_1421_, v_x_1422_);
lean_dec(v_x_1422_);
lean_dec_ref(v_a_1421_);
v_r_1424_ = lean_box(v_res_1423_);
return v_r_1424_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13_spec__14___redArg(lean_object* v_x_1425_, lean_object* v_x_1426_){
_start:
{
if (lean_obj_tag(v_x_1426_) == 0)
{
return v_x_1425_;
}
else
{
lean_object* v_key_1427_; lean_object* v_value_1428_; lean_object* v_tail_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1452_; 
v_key_1427_ = lean_ctor_get(v_x_1426_, 0);
v_value_1428_ = lean_ctor_get(v_x_1426_, 1);
v_tail_1429_ = lean_ctor_get(v_x_1426_, 2);
v_isSharedCheck_1452_ = !lean_is_exclusive(v_x_1426_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1431_ = v_x_1426_;
v_isShared_1432_ = v_isSharedCheck_1452_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_tail_1429_);
lean_inc(v_value_1428_);
lean_inc(v_key_1427_);
lean_dec(v_x_1426_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1452_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1433_; uint64_t v___x_1434_; uint64_t v___x_1435_; uint64_t v___x_1436_; uint64_t v_fold_1437_; uint64_t v___x_1438_; uint64_t v___x_1439_; uint64_t v___x_1440_; size_t v___x_1441_; size_t v___x_1442_; size_t v___x_1443_; size_t v___x_1444_; size_t v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1448_; 
v___x_1433_ = lean_array_get_size(v_x_1425_);
v___x_1434_ = l_Lean_Expr_hash(v_key_1427_);
v___x_1435_ = 32ULL;
v___x_1436_ = lean_uint64_shift_right(v___x_1434_, v___x_1435_);
v_fold_1437_ = lean_uint64_xor(v___x_1434_, v___x_1436_);
v___x_1438_ = 16ULL;
v___x_1439_ = lean_uint64_shift_right(v_fold_1437_, v___x_1438_);
v___x_1440_ = lean_uint64_xor(v_fold_1437_, v___x_1439_);
v___x_1441_ = lean_uint64_to_usize(v___x_1440_);
v___x_1442_ = lean_usize_of_nat(v___x_1433_);
v___x_1443_ = ((size_t)1ULL);
v___x_1444_ = lean_usize_sub(v___x_1442_, v___x_1443_);
v___x_1445_ = lean_usize_land(v___x_1441_, v___x_1444_);
v___x_1446_ = lean_array_uget_borrowed(v_x_1425_, v___x_1445_);
lean_inc(v___x_1446_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 2, v___x_1446_);
v___x_1448_ = v___x_1431_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_key_1427_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v_value_1428_);
lean_ctor_set(v_reuseFailAlloc_1451_, 2, v___x_1446_);
v___x_1448_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
lean_object* v___x_1449_; 
v___x_1449_ = lean_array_uset(v_x_1425_, v___x_1445_, v___x_1448_);
v_x_1425_ = v___x_1449_;
v_x_1426_ = v_tail_1429_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13___redArg(lean_object* v_i_1453_, lean_object* v_source_1454_, lean_object* v_target_1455_){
_start:
{
lean_object* v___x_1456_; uint8_t v___x_1457_; 
v___x_1456_ = lean_array_get_size(v_source_1454_);
v___x_1457_ = lean_nat_dec_lt(v_i_1453_, v___x_1456_);
if (v___x_1457_ == 0)
{
lean_dec_ref(v_source_1454_);
lean_dec(v_i_1453_);
return v_target_1455_;
}
else
{
lean_object* v_es_1458_; lean_object* v___x_1459_; lean_object* v_source_1460_; lean_object* v_target_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v_es_1458_ = lean_array_fget(v_source_1454_, v_i_1453_);
v___x_1459_ = lean_box(0);
v_source_1460_ = lean_array_fset(v_source_1454_, v_i_1453_, v___x_1459_);
v_target_1461_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13_spec__14___redArg(v_target_1455_, v_es_1458_);
v___x_1462_ = lean_unsigned_to_nat(1u);
v___x_1463_ = lean_nat_add(v_i_1453_, v___x_1462_);
lean_dec(v_i_1453_);
v_i_1453_ = v___x_1463_;
v_source_1454_ = v_source_1460_;
v_target_1455_ = v_target_1461_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9___redArg(lean_object* v_data_1465_){
_start:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v_nbuckets_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1466_ = lean_array_get_size(v_data_1465_);
v___x_1467_ = lean_unsigned_to_nat(2u);
v_nbuckets_1468_ = lean_nat_mul(v___x_1466_, v___x_1467_);
v___x_1469_ = lean_unsigned_to_nat(0u);
v___x_1470_ = lean_box(0);
v___x_1471_ = lean_mk_array(v_nbuckets_1468_, v___x_1470_);
v___x_1472_ = lean_array_propagate_mark(v_data_1465_, v___x_1471_);
v___x_1473_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13___redArg(v___x_1469_, v_data_1465_, v___x_1472_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__10___redArg(lean_object* v_a_1474_, lean_object* v_b_1475_, lean_object* v_x_1476_){
_start:
{
if (lean_obj_tag(v_x_1476_) == 0)
{
lean_dec(v_b_1475_);
lean_dec_ref(v_a_1474_);
return v_x_1476_;
}
else
{
lean_object* v_key_1477_; lean_object* v_value_1478_; lean_object* v_tail_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1491_; 
v_key_1477_ = lean_ctor_get(v_x_1476_, 0);
v_value_1478_ = lean_ctor_get(v_x_1476_, 1);
v_tail_1479_ = lean_ctor_get(v_x_1476_, 2);
v_isSharedCheck_1491_ = !lean_is_exclusive(v_x_1476_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1481_ = v_x_1476_;
v_isShared_1482_ = v_isSharedCheck_1491_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_tail_1479_);
lean_inc(v_value_1478_);
lean_inc(v_key_1477_);
lean_dec(v_x_1476_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1491_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
uint8_t v___x_1483_; 
v___x_1483_ = lean_expr_eqv(v_key_1477_, v_a_1474_);
if (v___x_1483_ == 0)
{
lean_object* v___x_1484_; lean_object* v___x_1486_; 
v___x_1484_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__10___redArg(v_a_1474_, v_b_1475_, v_tail_1479_);
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 2, v___x_1484_);
v___x_1486_ = v___x_1481_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_key_1477_);
lean_ctor_set(v_reuseFailAlloc_1487_, 1, v_value_1478_);
lean_ctor_set(v_reuseFailAlloc_1487_, 2, v___x_1484_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
else
{
lean_object* v___x_1489_; 
lean_dec(v_value_1478_);
lean_dec(v_key_1477_);
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 1, v_b_1475_);
lean_ctor_set(v___x_1481_, 0, v_a_1474_);
v___x_1489_ = v___x_1481_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_a_1474_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v_b_1475_);
lean_ctor_set(v_reuseFailAlloc_1490_, 2, v_tail_1479_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3___redArg(lean_object* v_m_1492_, lean_object* v_a_1493_, lean_object* v_b_1494_){
_start:
{
lean_object* v_size_1495_; lean_object* v_buckets_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1539_; 
v_size_1495_ = lean_ctor_get(v_m_1492_, 0);
v_buckets_1496_ = lean_ctor_get(v_m_1492_, 1);
v_isSharedCheck_1539_ = !lean_is_exclusive(v_m_1492_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1498_ = v_m_1492_;
v_isShared_1499_ = v_isSharedCheck_1539_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_buckets_1496_);
lean_inc(v_size_1495_);
lean_dec(v_m_1492_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1539_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1500_; uint64_t v___x_1501_; uint64_t v___x_1502_; uint64_t v___x_1503_; uint64_t v_fold_1504_; uint64_t v___x_1505_; uint64_t v___x_1506_; uint64_t v___x_1507_; size_t v___x_1508_; size_t v___x_1509_; size_t v___x_1510_; size_t v___x_1511_; size_t v___x_1512_; lean_object* v_bkt_1513_; uint8_t v___x_1514_; 
v___x_1500_ = lean_array_get_size(v_buckets_1496_);
v___x_1501_ = l_Lean_Expr_hash(v_a_1493_);
v___x_1502_ = 32ULL;
v___x_1503_ = lean_uint64_shift_right(v___x_1501_, v___x_1502_);
v_fold_1504_ = lean_uint64_xor(v___x_1501_, v___x_1503_);
v___x_1505_ = 16ULL;
v___x_1506_ = lean_uint64_shift_right(v_fold_1504_, v___x_1505_);
v___x_1507_ = lean_uint64_xor(v_fold_1504_, v___x_1506_);
v___x_1508_ = lean_uint64_to_usize(v___x_1507_);
v___x_1509_ = lean_usize_of_nat(v___x_1500_);
v___x_1510_ = ((size_t)1ULL);
v___x_1511_ = lean_usize_sub(v___x_1509_, v___x_1510_);
v___x_1512_ = lean_usize_land(v___x_1508_, v___x_1511_);
v_bkt_1513_ = lean_array_uget_borrowed(v_buckets_1496_, v___x_1512_);
v___x_1514_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___redArg(v_a_1493_, v_bkt_1513_);
if (v___x_1514_ == 0)
{
lean_object* v___x_1515_; lean_object* v_size_x27_1516_; lean_object* v___x_1517_; lean_object* v_buckets_x27_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; uint8_t v___x_1524_; 
v___x_1515_ = lean_unsigned_to_nat(1u);
v_size_x27_1516_ = lean_nat_add(v_size_1495_, v___x_1515_);
lean_dec(v_size_1495_);
lean_inc(v_bkt_1513_);
v___x_1517_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1517_, 0, v_a_1493_);
lean_ctor_set(v___x_1517_, 1, v_b_1494_);
lean_ctor_set(v___x_1517_, 2, v_bkt_1513_);
v_buckets_x27_1518_ = lean_array_uset(v_buckets_1496_, v___x_1512_, v___x_1517_);
v___x_1519_ = lean_unsigned_to_nat(4u);
v___x_1520_ = lean_nat_mul(v_size_x27_1516_, v___x_1519_);
v___x_1521_ = lean_unsigned_to_nat(3u);
v___x_1522_ = lean_nat_div(v___x_1520_, v___x_1521_);
lean_dec(v___x_1520_);
v___x_1523_ = lean_array_get_size(v_buckets_x27_1518_);
v___x_1524_ = lean_nat_dec_le(v___x_1522_, v___x_1523_);
lean_dec(v___x_1522_);
if (v___x_1524_ == 0)
{
lean_object* v_val_1525_; lean_object* v___x_1527_; 
v_val_1525_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9___redArg(v_buckets_x27_1518_);
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 1, v_val_1525_);
lean_ctor_set(v___x_1498_, 0, v_size_x27_1516_);
v___x_1527_ = v___x_1498_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_size_x27_1516_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v_val_1525_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
else
{
lean_object* v___x_1530_; 
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 1, v_buckets_x27_1518_);
lean_ctor_set(v___x_1498_, 0, v_size_x27_1516_);
v___x_1530_ = v___x_1498_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_size_x27_1516_);
lean_ctor_set(v_reuseFailAlloc_1531_, 1, v_buckets_x27_1518_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
else
{
lean_object* v___x_1532_; lean_object* v_buckets_x27_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1537_; 
lean_inc(v_bkt_1513_);
v___x_1532_ = lean_box(0);
v_buckets_x27_1533_ = lean_array_uset(v_buckets_1496_, v___x_1512_, v___x_1532_);
v___x_1534_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__10___redArg(v_a_1493_, v_b_1494_, v_bkt_1513_);
v___x_1535_ = lean_array_uset(v_buckets_x27_1533_, v___x_1512_, v___x_1534_);
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 1, v___x_1535_);
v___x_1537_ = v___x_1498_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_size_1495_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v___x_1535_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___redArg(lean_object* v_a_1540_, lean_object* v_x_1541_){
_start:
{
if (lean_obj_tag(v_x_1541_) == 0)
{
lean_object* v___x_1542_; 
v___x_1542_ = lean_box(0);
return v___x_1542_;
}
else
{
lean_object* v_key_1543_; lean_object* v_value_1544_; lean_object* v_tail_1545_; uint8_t v___x_1546_; 
v_key_1543_ = lean_ctor_get(v_x_1541_, 0);
v_value_1544_ = lean_ctor_get(v_x_1541_, 1);
v_tail_1545_ = lean_ctor_get(v_x_1541_, 2);
v___x_1546_ = lean_expr_eqv(v_key_1543_, v_a_1540_);
if (v___x_1546_ == 0)
{
v_x_1541_ = v_tail_1545_;
goto _start;
}
else
{
lean_object* v___x_1548_; 
lean_inc(v_value_1544_);
v___x_1548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1548_, 0, v_value_1544_);
return v___x_1548_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_a_1549_, lean_object* v_x_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___redArg(v_a_1549_, v_x_1550_);
lean_dec(v_x_1550_);
lean_dec_ref(v_a_1549_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___redArg(lean_object* v_m_1552_, lean_object* v_a_1553_){
_start:
{
lean_object* v_buckets_1554_; lean_object* v___x_1555_; uint64_t v___x_1556_; uint64_t v___x_1557_; uint64_t v___x_1558_; uint64_t v_fold_1559_; uint64_t v___x_1560_; uint64_t v___x_1561_; uint64_t v___x_1562_; size_t v___x_1563_; size_t v___x_1564_; size_t v___x_1565_; size_t v___x_1566_; size_t v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v_buckets_1554_ = lean_ctor_get(v_m_1552_, 1);
v___x_1555_ = lean_array_get_size(v_buckets_1554_);
v___x_1556_ = l_Lean_Expr_hash(v_a_1553_);
v___x_1557_ = 32ULL;
v___x_1558_ = lean_uint64_shift_right(v___x_1556_, v___x_1557_);
v_fold_1559_ = lean_uint64_xor(v___x_1556_, v___x_1558_);
v___x_1560_ = 16ULL;
v___x_1561_ = lean_uint64_shift_right(v_fold_1559_, v___x_1560_);
v___x_1562_ = lean_uint64_xor(v_fold_1559_, v___x_1561_);
v___x_1563_ = lean_uint64_to_usize(v___x_1562_);
v___x_1564_ = lean_usize_of_nat(v___x_1555_);
v___x_1565_ = ((size_t)1ULL);
v___x_1566_ = lean_usize_sub(v___x_1564_, v___x_1565_);
v___x_1567_ = lean_usize_land(v___x_1563_, v___x_1566_);
v___x_1568_ = lean_array_uget_borrowed(v_buckets_1554_, v___x_1567_);
v___x_1569_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___redArg(v_a_1553_, v___x_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___redArg___boxed(lean_object* v_m_1570_, lean_object* v_a_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___redArg(v_m_1570_, v_a_1571_);
lean_dec_ref(v_a_1571_);
lean_dec_ref(v_m_1570_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(lean_object* v_g_1573_, lean_object* v_e_1574_, lean_object* v_a_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
lean_object* v_a_1583_; lean_object* v___y_1589_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1591_ = lean_st_ref_get(v_a_1575_);
v___x_1592_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___redArg(v___x_1591_, v_e_1574_);
lean_dec(v___x_1591_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v___x_1593_; 
lean_inc_ref(v_g_1573_);
lean_inc(v___y_1580_);
lean_inc_ref(v___y_1579_);
lean_inc(v___y_1578_);
lean_inc_ref(v___y_1577_);
lean_inc(v___y_1576_);
lean_inc_ref(v_e_1574_);
v___x_1593_ = lean_apply_7(v_g_1573_, v_e_1574_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, lean_box(0));
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_a_1594_; lean_object* v_d_1596_; lean_object* v_b_1597_; lean_object* v___y_1598_; uint8_t v___x_1601_; 
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_a_1594_);
lean_dec_ref_known(v___x_1593_, 1);
v___x_1601_ = lean_unbox(v_a_1594_);
lean_dec(v_a_1594_);
if (v___x_1601_ == 0)
{
lean_object* v___x_1602_; 
lean_dec_ref(v_g_1573_);
v___x_1602_ = lean_box(0);
v_a_1583_ = v___x_1602_;
goto v___jp_1582_;
}
else
{
switch(lean_obj_tag(v_e_1574_))
{
case 7:
{
lean_object* v_binderType_1603_; lean_object* v_body_1604_; 
v_binderType_1603_ = lean_ctor_get(v_e_1574_, 1);
v_body_1604_ = lean_ctor_get(v_e_1574_, 2);
lean_inc_ref(v_body_1604_);
lean_inc_ref(v_binderType_1603_);
v_d_1596_ = v_binderType_1603_;
v_b_1597_ = v_body_1604_;
v___y_1598_ = v_a_1575_;
goto v___jp_1595_;
}
case 6:
{
lean_object* v_binderType_1605_; lean_object* v_body_1606_; 
v_binderType_1605_ = lean_ctor_get(v_e_1574_, 1);
v_body_1606_ = lean_ctor_get(v_e_1574_, 2);
lean_inc_ref(v_body_1606_);
lean_inc_ref(v_binderType_1605_);
v_d_1596_ = v_binderType_1605_;
v_b_1597_ = v_body_1606_;
v___y_1598_ = v_a_1575_;
goto v___jp_1595_;
}
case 8:
{
lean_object* v_type_1607_; lean_object* v_value_1608_; lean_object* v_body_1609_; lean_object* v___x_1610_; 
v_type_1607_ = lean_ctor_get(v_e_1574_, 1);
v_value_1608_ = lean_ctor_get(v_e_1574_, 2);
v_body_1609_ = lean_ctor_get(v_e_1574_, 3);
lean_inc_ref(v_type_1607_);
lean_inc_ref(v_g_1573_);
v___x_1610_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1573_, v_type_1607_, v_a_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v___x_1611_; 
lean_dec_ref_known(v___x_1610_, 1);
lean_inc_ref(v_value_1608_);
lean_inc_ref(v_g_1573_);
v___x_1611_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1573_, v_value_1608_, v_a_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_object* v___x_1612_; 
lean_dec_ref_known(v___x_1611_, 1);
lean_inc_ref(v_body_1609_);
v___x_1612_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1573_, v_body_1609_, v_a_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
v___y_1589_ = v___x_1612_;
goto v___jp_1588_;
}
else
{
lean_dec_ref(v_g_1573_);
v___y_1589_ = v___x_1611_;
goto v___jp_1588_;
}
}
else
{
lean_dec_ref(v_g_1573_);
v___y_1589_ = v___x_1610_;
goto v___jp_1588_;
}
}
case 5:
{
lean_object* v_fn_1613_; lean_object* v_arg_1614_; lean_object* v___x_1615_; 
v_fn_1613_ = lean_ctor_get(v_e_1574_, 0);
v_arg_1614_ = lean_ctor_get(v_e_1574_, 1);
lean_inc_ref(v_fn_1613_);
lean_inc_ref(v_g_1573_);
v___x_1615_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1573_, v_fn_1613_, v_a_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v___x_1616_; 
lean_dec_ref_known(v___x_1615_, 1);
lean_inc_ref(v_arg_1614_);
v___x_1616_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1573_, v_arg_1614_, v_a_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
v___y_1589_ = v___x_1616_;
goto v___jp_1588_;
}
else
{
lean_dec_ref(v_g_1573_);
v___y_1589_ = v___x_1615_;
goto v___jp_1588_;
}
}
case 10:
{
lean_object* v_expr_1617_; lean_object* v___x_1618_; 
v_expr_1617_ = lean_ctor_get(v_e_1574_, 1);
lean_inc_ref(v_expr_1617_);
v___x_1618_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1573_, v_expr_1617_, v_a_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
v___y_1589_ = v___x_1618_;
goto v___jp_1588_;
}
case 11:
{
lean_object* v_struct_1619_; lean_object* v___x_1620_; 
v_struct_1619_ = lean_ctor_get(v_e_1574_, 2);
lean_inc_ref(v_struct_1619_);
v___x_1620_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1573_, v_struct_1619_, v_a_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
v___y_1589_ = v___x_1620_;
goto v___jp_1588_;
}
default: 
{
lean_object* v___x_1621_; 
lean_dec_ref(v_g_1573_);
v___x_1621_ = lean_box(0);
v_a_1583_ = v___x_1621_;
goto v___jp_1582_;
}
}
}
v___jp_1595_:
{
lean_object* v___x_1599_; 
lean_inc_ref(v_g_1573_);
v___x_1599_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1573_, v_d_1596_, v___y_1598_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v___x_1600_; 
lean_dec_ref_known(v___x_1599_, 1);
v___x_1600_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1573_, v_b_1597_, v___y_1598_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
v___y_1589_ = v___x_1600_;
goto v___jp_1588_;
}
else
{
lean_dec_ref(v_b_1597_);
lean_dec_ref(v_g_1573_);
v___y_1589_ = v___x_1599_;
goto v___jp_1588_;
}
}
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
lean_dec_ref(v_e_1574_);
lean_dec_ref(v_g_1573_);
v_a_1622_ = lean_ctor_get(v___x_1593_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1593_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1593_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
else
{
lean_object* v_val_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
lean_dec_ref(v_e_1574_);
lean_dec_ref(v_g_1573_);
v_val_1630_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1592_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_val_1630_);
lean_dec(v___x_1592_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
lean_ctor_set_tag(v___x_1632_, 0);
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_val_1630_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
v___jp_1582_:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1584_ = lean_st_ref_take(v_a_1575_);
v___x_1585_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3___redArg(v___x_1584_, v_e_1574_, v_a_1583_);
v___x_1586_ = lean_st_ref_put(v_a_1575_, v___x_1585_);
v___x_1587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1587_, 0, v_a_1583_);
return v___x_1587_;
}
v___jp_1588_:
{
if (lean_obj_tag(v___y_1589_) == 0)
{
lean_object* v_a_1590_; 
v_a_1590_ = lean_ctor_get(v___y_1589_, 0);
lean_inc(v_a_1590_);
lean_dec_ref_known(v___y_1589_, 1);
v_a_1583_ = v_a_1590_;
goto v___jp_1582_;
}
else
{
lean_dec_ref(v_e_1574_);
return v___y_1589_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1___boxed(lean_object* v_g_1638_, lean_object* v_e_1639_, lean_object* v_a_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1638_, v_e_1639_, v_a_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
lean_dec(v_a_1640_);
return v_res_1647_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__1(void){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1649_ = lean_box(0);
v___x_1650_ = lean_unsigned_to_nat(16u);
v___x_1651_ = lean_mk_array(v___x_1650_, v___x_1649_);
return v___x_1651_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__2(void){
_start:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1652_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__1, &l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__1_once, _init_l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__1);
v___x_1653_ = lean_unsigned_to_nat(0u);
v___x_1654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
lean_ctor_set(v___x_1654_, 1, v___x_1652_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar(lean_object* v_e_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_){
_start:
{
lean_object* v___f_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___f_1662_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__0));
v___x_1663_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__2, &l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__2_once, _init_l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__2);
v___x_1664_ = lean_st_mk_ref(v___x_1663_);
v___x_1665_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v___f_1662_, v_e_1655_, v___x_1664_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1674_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1668_ = v___x_1665_;
v_isShared_1669_ = v_isSharedCheck_1674_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1665_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1674_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1670_; lean_object* v___x_1672_; 
v___x_1670_ = lean_st_ref_get(v___x_1664_);
lean_dec(v___x_1664_);
lean_dec(v___x_1670_);
if (v_isShared_1669_ == 0)
{
v___x_1672_ = v___x_1668_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_a_1666_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
else
{
lean_dec(v___x_1664_);
return v___x_1665_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___boxed(lean_object* v_e_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar(v_e_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_);
lean_dec(v_a_1680_);
lean_dec_ref(v_a_1679_);
lean_dec(v_a_1678_);
lean_dec_ref(v_a_1677_);
lean_dec(v_a_1676_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2(lean_object* v_00_u03b2_1683_, lean_object* v_m_1684_, lean_object* v_a_1685_){
_start:
{
lean_object* v___x_1686_; 
v___x_1686_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___redArg(v_m_1684_, v_a_1685_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1687_, lean_object* v_m_1688_, lean_object* v_a_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2(v_00_u03b2_1687_, v_m_1688_, v_a_1689_);
lean_dec_ref(v_a_1689_);
lean_dec_ref(v_m_1688_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3(lean_object* v_00_u03b2_1691_, lean_object* v_m_1692_, lean_object* v_a_1693_, lean_object* v_b_1694_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3___redArg(v_m_1692_, v_a_1693_, v_b_1694_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_1696_, lean_object* v_a_1697_, lean_object* v_x_1698_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___redArg(v_a_1697_, v_x_1698_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1700_, lean_object* v_a_1701_, lean_object* v_x_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6(v_00_u03b2_1700_, v_a_1701_, v_x_1702_);
lean_dec(v_x_1702_);
lean_dec_ref(v_a_1701_);
return v_res_1703_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_1704_, lean_object* v_a_1705_, lean_object* v_x_1706_){
_start:
{
uint8_t v___x_1707_; 
v___x_1707_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___redArg(v_a_1705_, v_x_1706_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___boxed(lean_object* v_00_u03b2_1708_, lean_object* v_a_1709_, lean_object* v_x_1710_){
_start:
{
uint8_t v_res_1711_; lean_object* v_r_1712_; 
v_res_1711_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8(v_00_u03b2_1708_, v_a_1709_, v_x_1710_);
lean_dec(v_x_1710_);
lean_dec_ref(v_a_1709_);
v_r_1712_ = lean_box(v_res_1711_);
return v_r_1712_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9(lean_object* v_00_u03b2_1713_, lean_object* v_data_1714_){
_start:
{
lean_object* v___x_1715_; 
v___x_1715_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9___redArg(v_data_1714_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__10(lean_object* v_00_u03b2_1716_, lean_object* v_a_1717_, lean_object* v_b_1718_, lean_object* v_x_1719_){
_start:
{
lean_object* v___x_1720_; 
v___x_1720_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__10___redArg(v_a_1717_, v_b_1718_, v_x_1719_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6(lean_object* v_as_1721_, size_t v_i_1722_, size_t v_stop_1723_, lean_object* v_b_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___redArg(v_as_1721_, v_i_1722_, v_stop_1723_, v_b_1724_, v___y_1725_, v___y_1726_, v___y_1728_, v___y_1729_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* v_as_1732_, lean_object* v_i_1733_, lean_object* v_stop_1734_, lean_object* v_b_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
size_t v_i_boxed_1742_; size_t v_stop_boxed_1743_; lean_object* v_res_1744_; 
v_i_boxed_1742_ = lean_unbox_usize(v_i_1733_);
lean_dec(v_i_1733_);
v_stop_boxed_1743_ = lean_unbox_usize(v_stop_1734_);
lean_dec(v_stop_1734_);
v_res_1744_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6(v_as_1732_, v_i_boxed_1742_, v_stop_boxed_1743_, v_b_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v___y_1736_);
lean_dec_ref(v_as_1732_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13(lean_object* v_00_u03b2_1745_, lean_object* v_i_1746_, lean_object* v_source_1747_, lean_object* v_target_1748_){
_start:
{
lean_object* v___x_1749_; 
v___x_1749_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13___redArg(v_i_1746_, v_source_1747_, v_target_1748_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13_spec__14(lean_object* v_00_u03b2_1750_, lean_object* v_x_1751_, lean_object* v_x_1752_){
_start:
{
lean_object* v___x_1753_; 
v___x_1753_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13_spec__14___redArg(v_x_1751_, v_x_1752_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___redArg(lean_object* v_e_1754_, lean_object* v___y_1755_){
_start:
{
uint8_t v___x_1757_; 
v___x_1757_ = l_Lean_Expr_hasMVar(v_e_1754_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; 
v___x_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1758_, 0, v_e_1754_);
return v___x_1758_;
}
else
{
lean_object* v___x_1759_; lean_object* v_mctx_1760_; lean_object* v___x_1761_; lean_object* v_fst_1762_; lean_object* v_snd_1763_; lean_object* v___x_1764_; lean_object* v_cache_1765_; lean_object* v_zetaDeltaFVarIds_1766_; lean_object* v_postponed_1767_; lean_object* v_diag_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1777_; 
v___x_1759_ = lean_st_ref_get(v___y_1755_);
v_mctx_1760_ = lean_ctor_get(v___x_1759_, 0);
lean_inc_ref(v_mctx_1760_);
lean_dec(v___x_1759_);
v___x_1761_ = l_Lean_instantiateMVarsCore(v_mctx_1760_, v_e_1754_);
v_fst_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_fst_1762_);
v_snd_1763_ = lean_ctor_get(v___x_1761_, 1);
lean_inc(v_snd_1763_);
lean_dec_ref(v___x_1761_);
v___x_1764_ = lean_st_ref_take(v___y_1755_);
v_cache_1765_ = lean_ctor_get(v___x_1764_, 1);
v_zetaDeltaFVarIds_1766_ = lean_ctor_get(v___x_1764_, 2);
v_postponed_1767_ = lean_ctor_get(v___x_1764_, 3);
v_diag_1768_ = lean_ctor_get(v___x_1764_, 4);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1777_ == 0)
{
lean_object* v_unused_1778_; 
v_unused_1778_ = lean_ctor_get(v___x_1764_, 0);
lean_dec(v_unused_1778_);
v___x_1770_ = v___x_1764_;
v_isShared_1771_ = v_isSharedCheck_1777_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_diag_1768_);
lean_inc(v_postponed_1767_);
lean_inc(v_zetaDeltaFVarIds_1766_);
lean_inc(v_cache_1765_);
lean_dec(v___x_1764_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1777_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 0, v_snd_1763_);
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_snd_1763_);
lean_ctor_set(v_reuseFailAlloc_1776_, 1, v_cache_1765_);
lean_ctor_set(v_reuseFailAlloc_1776_, 2, v_zetaDeltaFVarIds_1766_);
lean_ctor_set(v_reuseFailAlloc_1776_, 3, v_postponed_1767_);
lean_ctor_set(v_reuseFailAlloc_1776_, 4, v_diag_1768_);
v___x_1773_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = lean_st_ref_put(v___y_1755_, v___x_1773_);
v___x_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1775_, 0, v_fst_1762_);
return v___x_1775_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___redArg___boxed(lean_object* v_e_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___redArg(v_e_1779_, v___y_1780_);
lean_dec(v___y_1780_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0(lean_object* v_e_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v___x_1789_; 
v___x_1789_ = l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___redArg(v_e_1783_, v___y_1785_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___boxed(lean_object* v_e_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0(v_e_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertAfter_x27___lam__0(lean_object* v_type_1797_, lean_object* v_fvarId_1798_, lean_object* v_mvarId_1799_, lean_object* v_userName_1800_, lean_object* v_val_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v___x_1807_; lean_object* v_a_1808_; lean_object* v___x_1809_; 
v___x_1807_ = l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___redArg(v_type_1797_, v___y_1803_);
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
lean_inc(v_a_1808_);
lean_dec_ref(v___x_1807_);
v___x_1809_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1798_, v___y_1802_, v___y_1804_, v___y_1805_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_a_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
lean_inc(v_a_1810_);
lean_dec_ref_known(v___x_1809_, 1);
v___x_1811_ = lean_st_mk_ref(v_a_1810_);
lean_inc(v_a_1808_);
v___x_1812_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar(v_a_1808_, v___x_1811_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
lean_dec_ref_known(v___x_1812_, 1);
v___x_1813_ = lean_st_ref_get(v___x_1811_);
lean_dec(v___x_1811_);
v___x_1814_ = l_Lean_LocalDecl_fvarId(v___x_1813_);
lean_dec(v___x_1813_);
v___x_1815_ = l_Lean_MVarId_assertAfter(v_mvarId_1799_, v___x_1814_, v_userName_1800_, v_a_1808_, v_val_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
return v___x_1815_;
}
else
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1823_; 
lean_dec(v___x_1811_);
lean_dec(v_a_1808_);
lean_dec_ref(v_val_1801_);
lean_dec(v_userName_1800_);
lean_dec(v_mvarId_1799_);
v_a_1816_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1818_ = v___x_1812_;
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1812_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1821_; 
if (v_isShared_1819_ == 0)
{
v___x_1821_ = v___x_1818_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_a_1816_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
}
else
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
lean_dec(v_a_1808_);
lean_dec_ref(v_val_1801_);
lean_dec(v_userName_1800_);
lean_dec(v_mvarId_1799_);
v_a_1824_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1809_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1809_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertAfter_x27___lam__0___boxed(lean_object* v_type_1832_, lean_object* v_fvarId_1833_, lean_object* v_mvarId_1834_, lean_object* v_userName_1835_, lean_object* v_val_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l_Lean_MVarId_assertAfter_x27___lam__0(v_type_1832_, v_fvarId_1833_, v_mvarId_1834_, v_userName_1835_, v_val_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertAfter_x27(lean_object* v_mvarId_1843_, lean_object* v_fvarId_1844_, lean_object* v_userName_1845_, lean_object* v_type_1846_, lean_object* v_val_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_){
_start:
{
lean_object* v___f_1853_; lean_object* v___x_1854_; 
lean_inc(v_mvarId_1843_);
v___f_1853_ = lean_alloc_closure((void*)(l_Lean_MVarId_assertAfter_x27___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1853_, 0, v_type_1846_);
lean_closure_set(v___f_1853_, 1, v_fvarId_1844_);
lean_closure_set(v___f_1853_, 2, v_mvarId_1843_);
lean_closure_set(v___f_1853_, 3, v_userName_1845_);
lean_closure_set(v___f_1853_, 4, v_val_1847_);
v___x_1854_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(v_mvarId_1843_, v___f_1853_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertAfter_x27___boxed(lean_object* v_mvarId_1855_, lean_object* v_fvarId_1856_, lean_object* v_userName_1857_, lean_object* v_type_1858_, lean_object* v_val_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l_Lean_MVarId_assertAfter_x27(v_mvarId_1855_, v_fvarId_1856_, v_userName_1857_, v_type_1858_, v_val_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
lean_dec(v_a_1863_);
lean_dec_ref(v_a_1862_);
lean_dec(v_a_1861_);
lean_dec_ref(v_a_1860_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg(lean_object* v_mvarId_1866_, lean_object* v_f_1867_, lean_object* v___y_1868_){
_start:
{
lean_object* v___x_1870_; lean_object* v_mctx_1871_; lean_object* v_cache_1872_; lean_object* v_zetaDeltaFVarIds_1873_; lean_object* v_postponed_1874_; lean_object* v_diag_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1886_; 
v___x_1870_ = lean_st_ref_take(v___y_1868_);
v_mctx_1871_ = lean_ctor_get(v___x_1870_, 0);
v_cache_1872_ = lean_ctor_get(v___x_1870_, 1);
v_zetaDeltaFVarIds_1873_ = lean_ctor_get(v___x_1870_, 2);
v_postponed_1874_ = lean_ctor_get(v___x_1870_, 3);
v_diag_1875_ = lean_ctor_get(v___x_1870_, 4);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1877_ = v___x_1870_;
v_isShared_1878_ = v_isSharedCheck_1886_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_diag_1875_);
lean_inc(v_postponed_1874_);
lean_inc(v_zetaDeltaFVarIds_1873_);
lean_inc(v_cache_1872_);
lean_inc(v_mctx_1871_);
lean_dec(v___x_1870_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1886_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1882_; 
v___x_1879_ = lean_box(0);
v___x_1880_ = l_Lean_MetavarContext_modifyExprMVarLCtx(v_mctx_1871_, v_mvarId_1866_, v_f_1867_);
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 0, v___x_1880_);
v___x_1882_ = v___x_1877_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1880_);
lean_ctor_set(v_reuseFailAlloc_1885_, 1, v_cache_1872_);
lean_ctor_set(v_reuseFailAlloc_1885_, 2, v_zetaDeltaFVarIds_1873_);
lean_ctor_set(v_reuseFailAlloc_1885_, 3, v_postponed_1874_);
lean_ctor_set(v_reuseFailAlloc_1885_, 4, v_diag_1875_);
v___x_1882_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1883_ = lean_st_ref_put(v___y_1868_, v___x_1882_);
v___x_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1879_);
return v___x_1884_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg___boxed(lean_object* v_mvarId_1887_, lean_object* v_f_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg(v_mvarId_1887_, v_f_1888_, v___y_1889_);
lean_dec(v___y_1889_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1(lean_object* v_mvarId_1892_, lean_object* v_f_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v___x_1899_; 
v___x_1899_ = l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg(v_mvarId_1892_, v_f_1893_, v___y_1895_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___boxed(lean_object* v_mvarId_1900_, lean_object* v_f_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1(v_mvarId_1900_, v_f_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg(lean_object* v_upperBound_1908_, lean_object* v_hs_1909_, lean_object* v_fst_1910_, lean_object* v_a_1911_, lean_object* v_b_1912_){
_start:
{
lean_object* v_a_1914_; uint8_t v___x_1918_; 
v___x_1918_ = lean_nat_dec_lt(v_a_1911_, v_upperBound_1908_);
if (v___x_1918_ == 0)
{
lean_dec(v_a_1911_);
return v_b_1912_;
}
else
{
lean_object* v___x_1919_; uint8_t v_kind_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; uint8_t v___x_1924_; 
v___x_1919_ = lean_array_fget_borrowed(v_hs_1909_, v_a_1911_);
v_kind_1920_ = lean_ctor_get_uint8(v___x_1919_, sizeof(void*)*3 + 1);
v___x_1921_ = lean_box(v_kind_1920_);
v___x_1922_ = lean_obj_tag_nat(v___x_1921_);
lean_dec(v___x_1921_);
v___x_1923_ = lean_unsigned_to_nat(0u);
v___x_1924_ = lean_nat_dec_eq(v___x_1922_, v___x_1923_);
if (v___x_1924_ == 0)
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1925_ = lean_box(0);
v___x_1926_ = lean_array_get_borrowed(v___x_1925_, v_fst_1910_, v_a_1911_);
lean_inc(v___x_1926_);
v___x_1927_ = l_Lean_LocalContext_setKind(v_b_1912_, v___x_1926_, v_kind_1920_);
v_a_1914_ = v___x_1927_;
goto v___jp_1913_;
}
else
{
v_a_1914_ = v_b_1912_;
goto v___jp_1913_;
}
}
v___jp_1913_:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1915_ = lean_unsigned_to_nat(1u);
v___x_1916_ = lean_nat_add(v_a_1911_, v___x_1915_);
lean_dec(v_a_1911_);
v_a_1911_ = v___x_1916_;
v_b_1912_ = v_a_1914_;
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
uint8_t v___x_2879__boxed_2080_; lean_object* v_res_2081_; 
v___x_2879__boxed_2080_ = lean_unbox(v___x_2071_);
v_res_2081_ = l_Lean_MVarId_assertHypotheses___lam__1(v_mvarId_2069_, v___x_2070_, v___x_2879__boxed_2080_, v_hs_2072_, v___x_2073_, v___x_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
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
