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
lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(lean_object* v_mvarId_1_, lean_object* v_x_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_){
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
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v_res_25_;
v_res_25_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(v_mvarId_1_, v_x_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_);
stack->m_obj
 = v_res_25_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg___boxed(lean_object* v_mvarId_26_, lean_object* v_x_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(v_mvarId_26_, v_x_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_);
lean_dec(v___y_31_);
lean_dec_ref(v___y_30_);
lean_dec(v___y_29_);
lean_dec_ref(v___y_28_);
return v_res_33_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1(lean_object* v_00_u03b1_34_, lean_object* v_mvarId_35_, lean_object* v_x_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(v_mvarId_35_, v_x_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_);
return v___x_42_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_35_ = stack[1].m_obj;
lean_object* v_x_36_ = stack[2].m_obj;
lean_object* v___y_37_ = stack[3].m_obj;
lean_object* v___y_38_ = stack[4].m_obj;
lean_object* v___y_39_ = stack[5].m_obj;
lean_object* v___y_40_ = stack[6].m_obj;
lean_object* v_res_43_;
v_res_43_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1(lean_box(0), v_mvarId_35_, v_x_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_);
stack->m_obj
 = v_res_43_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___boxed(lean_object* v_00_u03b1_44_, lean_object* v_mvarId_45_, lean_object* v_x_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1(v_00_u03b1_44_, v_mvarId_45_, v_x_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(lean_object* v_x_53_, lean_object* v_x_54_, lean_object* v_x_55_, lean_object* v_x_56_){
_start:
{
lean_object* v_ks_57_; lean_object* v_vs_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_82_; 
v_ks_57_ = lean_ctor_get(v_x_53_, 0);
v_vs_58_ = lean_ctor_get(v_x_53_, 1);
v_isSharedCheck_82_ = !lean_is_exclusive(v_x_53_);
if (v_isSharedCheck_82_ == 0)
{
v___x_60_ = v_x_53_;
v_isShared_61_ = v_isSharedCheck_82_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_vs_58_);
lean_inc(v_ks_57_);
lean_dec(v_x_53_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_82_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v___x_62_; uint8_t v___x_63_; 
v___x_62_ = lean_array_get_size(v_ks_57_);
v___x_63_ = lean_nat_dec_lt(v_x_54_, v___x_62_);
if (v___x_63_ == 0)
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_67_; 
lean_dec(v_x_54_);
v___x_64_ = lean_array_push(v_ks_57_, v_x_55_);
v___x_65_ = lean_array_push(v_vs_58_, v_x_56_);
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 1, v___x_65_);
lean_ctor_set(v___x_60_, 0, v___x_64_);
v___x_67_ = v___x_60_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v___x_64_);
lean_ctor_set(v_reuseFailAlloc_68_, 1, v___x_65_);
v___x_67_ = v_reuseFailAlloc_68_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
return v___x_67_;
}
}
else
{
lean_object* v_k_x27_69_; uint8_t v___x_70_; 
v_k_x27_69_ = lean_array_fget_borrowed(v_ks_57_, v_x_54_);
v___x_70_ = l_Lean_instBEqMVarId_beq(v_x_55_, v_k_x27_69_);
if (v___x_70_ == 0)
{
lean_object* v___x_72_; 
if (v_isShared_61_ == 0)
{
v___x_72_ = v___x_60_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v_ks_57_);
lean_ctor_set(v_reuseFailAlloc_76_, 1, v_vs_58_);
v___x_72_ = v_reuseFailAlloc_76_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = lean_unsigned_to_nat(1u);
v___x_74_ = lean_nat_add(v_x_54_, v___x_73_);
lean_dec(v_x_54_);
v_x_53_ = v___x_72_;
v_x_54_ = v___x_74_;
goto _start;
}
}
else
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_80_; 
v___x_77_ = lean_array_fset(v_ks_57_, v_x_54_, v_x_55_);
v___x_78_ = lean_array_fset(v_vs_58_, v_x_54_, v_x_56_);
lean_dec(v_x_54_);
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 1, v___x_78_);
lean_ctor_set(v___x_60_, 0, v___x_77_);
v___x_80_ = v___x_60_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v___x_77_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v___x_78_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_n_83_, lean_object* v_k_84_, lean_object* v_v_85_){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = lean_unsigned_to_nat(0u);
v___x_87_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_n_83_, v___x_86_, v_k_84_, v_v_85_);
return v___x_87_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_88_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(lean_object* v_x_89_, size_t v_x_90_, size_t v_x_91_, lean_object* v_x_92_, lean_object* v_x_93_){
_start:
{
if (lean_obj_tag(v_x_89_) == 0)
{
lean_object* v_es_94_; size_t v___x_95_; size_t v___x_96_; lean_object* v_j_97_; lean_object* v___x_98_; uint8_t v___x_99_; 
v_es_94_ = lean_ctor_get(v_x_89_, 0);
v___x_95_ = ((size_t)31ULL);
v___x_96_ = lean_usize_land(v_x_90_, v___x_95_);
v_j_97_ = lean_usize_to_nat(v___x_96_);
v___x_98_ = lean_array_get_size(v_es_94_);
v___x_99_ = lean_nat_dec_lt(v_j_97_, v___x_98_);
if (v___x_99_ == 0)
{
lean_dec(v_j_97_);
lean_dec(v_x_93_);
lean_dec(v_x_92_);
return v_x_89_;
}
else
{
lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_138_; 
lean_inc_ref(v_es_94_);
v_isSharedCheck_138_ = !lean_is_exclusive(v_x_89_);
if (v_isSharedCheck_138_ == 0)
{
lean_object* v_unused_139_; 
v_unused_139_ = lean_ctor_get(v_x_89_, 0);
lean_dec(v_unused_139_);
v___x_101_ = v_x_89_;
v_isShared_102_ = v_isSharedCheck_138_;
goto v_resetjp_100_;
}
else
{
lean_dec(v_x_89_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_138_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v_v_103_; lean_object* v___x_104_; lean_object* v_xs_x27_105_; lean_object* v___y_107_; 
v_v_103_ = lean_array_fget(v_es_94_, v_j_97_);
v___x_104_ = lean_box(0);
v_xs_x27_105_ = lean_array_fset(v_es_94_, v_j_97_, v___x_104_);
switch(lean_obj_tag(v_v_103_))
{
case 0:
{
lean_object* v_key_112_; lean_object* v_val_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_123_; 
v_key_112_ = lean_ctor_get(v_v_103_, 0);
v_val_113_ = lean_ctor_get(v_v_103_, 1);
v_isSharedCheck_123_ = !lean_is_exclusive(v_v_103_);
if (v_isSharedCheck_123_ == 0)
{
v___x_115_ = v_v_103_;
v_isShared_116_ = v_isSharedCheck_123_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_val_113_);
lean_inc(v_key_112_);
lean_dec(v_v_103_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_123_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
uint8_t v___x_117_; 
v___x_117_ = l_Lean_instBEqMVarId_beq(v_x_92_, v_key_112_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; lean_object* v___x_119_; 
lean_del_object(v___x_115_);
v___x_118_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_112_, v_val_113_, v_x_92_, v_x_93_);
v___x_119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
v___y_107_ = v___x_119_;
goto v___jp_106_;
}
else
{
lean_object* v___x_121_; 
lean_dec(v_val_113_);
lean_dec(v_key_112_);
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 1, v_x_93_);
lean_ctor_set(v___x_115_, 0, v_x_92_);
v___x_121_ = v___x_115_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_x_92_);
lean_ctor_set(v_reuseFailAlloc_122_, 1, v_x_93_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
v___y_107_ = v___x_121_;
goto v___jp_106_;
}
}
}
}
case 1:
{
lean_object* v_node_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_136_; 
v_node_124_ = lean_ctor_get(v_v_103_, 0);
v_isSharedCheck_136_ = !lean_is_exclusive(v_v_103_);
if (v_isSharedCheck_136_ == 0)
{
v___x_126_ = v_v_103_;
v_isShared_127_ = v_isSharedCheck_136_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_node_124_);
lean_dec(v_v_103_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_136_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
size_t v___x_128_; size_t v___x_129_; size_t v___x_130_; size_t v___x_131_; lean_object* v___x_132_; lean_object* v___x_134_; 
v___x_128_ = ((size_t)5ULL);
v___x_129_ = lean_usize_shift_right(v_x_90_, v___x_128_);
v___x_130_ = ((size_t)1ULL);
v___x_131_ = lean_usize_add(v_x_91_, v___x_130_);
v___x_132_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(v_node_124_, v___x_129_, v___x_131_, v_x_92_, v_x_93_);
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 0, v___x_132_);
v___x_134_ = v___x_126_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_132_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
v___y_107_ = v___x_134_;
goto v___jp_106_;
}
}
}
default: 
{
lean_object* v___x_137_; 
v___x_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_137_, 0, v_x_92_);
lean_ctor_set(v___x_137_, 1, v_x_93_);
v___y_107_ = v___x_137_;
goto v___jp_106_;
}
}
v___jp_106_:
{
lean_object* v___x_108_; lean_object* v___x_110_; 
v___x_108_ = lean_array_fset(v_xs_x27_105_, v_j_97_, v___y_107_);
lean_dec(v_j_97_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 0, v___x_108_);
v___x_110_ = v___x_101_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v___x_108_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
}
}
}
else
{
lean_object* v_ks_140_; lean_object* v_vs_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_159_; 
v_ks_140_ = lean_ctor_get(v_x_89_, 0);
v_vs_141_ = lean_ctor_get(v_x_89_, 1);
v_isSharedCheck_159_ = !lean_is_exclusive(v_x_89_);
if (v_isSharedCheck_159_ == 0)
{
v___x_143_ = v_x_89_;
v_isShared_144_ = v_isSharedCheck_159_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_vs_141_);
lean_inc(v_ks_140_);
lean_dec(v_x_89_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_159_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_146_; 
if (v_isShared_144_ == 0)
{
v___x_146_ = v___x_143_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_ks_140_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v_vs_141_);
v___x_146_ = v_reuseFailAlloc_158_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
lean_object* v_newNode_147_; size_t v___x_148_; uint8_t v___x_149_; 
v_newNode_147_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3___redArg(v___x_146_, v_x_92_, v_x_93_);
v___x_148_ = ((size_t)7ULL);
v___x_149_ = lean_usize_dec_le(v___x_148_, v_x_91_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_150_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_147_);
v___x_151_ = lean_unsigned_to_nat(4u);
v___x_152_ = lean_nat_dec_lt(v___x_150_, v___x_151_);
lean_dec(v___x_150_);
if (v___x_152_ == 0)
{
lean_object* v_ks_153_; lean_object* v_vs_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v_ks_153_ = lean_ctor_get(v_newNode_147_, 0);
lean_inc_ref(v_ks_153_);
v_vs_154_ = lean_ctor_get(v_newNode_147_, 1);
lean_inc_ref(v_vs_154_);
lean_dec_ref(v_newNode_147_);
v___x_155_ = lean_unsigned_to_nat(0u);
v___x_156_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_157_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg(v_x_91_, v_ks_153_, v_vs_154_, v___x_155_, v___x_156_);
lean_dec_ref(v_vs_154_);
lean_dec_ref(v_ks_153_);
return v___x_157_;
}
else
{
return v_newNode_147_;
}
}
else
{
return v_newNode_147_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_89_ = stack[0].m_obj;
size_t v_x_90_ = stack[1].m_num;
size_t v_x_91_ = stack[2].m_num;
lean_object* v_x_92_ = stack[3].m_obj;
lean_object* v_x_93_ = stack[4].m_obj;
lean_object* v_res_160_;
v_res_160_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(v_x_89_, v_x_90_, v_x_91_, v_x_92_, v_x_93_);
stack->m_obj
 = v_res_160_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg(size_t v_depth_161_, lean_object* v_keys_162_, lean_object* v_vals_163_, lean_object* v_i_164_, lean_object* v_entries_165_){
_start:
{
lean_object* v___x_166_; uint8_t v___x_167_; 
v___x_166_ = lean_array_get_size(v_keys_162_);
v___x_167_ = lean_nat_dec_lt(v_i_164_, v___x_166_);
if (v___x_167_ == 0)
{
lean_dec(v_i_164_);
return v_entries_165_;
}
else
{
lean_object* v_k_168_; lean_object* v_v_169_; uint64_t v___x_170_; size_t v_h_171_; size_t v___x_172_; lean_object* v___x_173_; size_t v___x_174_; size_t v___x_175_; size_t v___x_176_; size_t v_h_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v_k_168_ = lean_array_fget_borrowed(v_keys_162_, v_i_164_);
v_v_169_ = lean_array_fget_borrowed(v_vals_163_, v_i_164_);
v___x_170_ = l_Lean_instHashableMVarId_hash(v_k_168_);
v_h_171_ = lean_uint64_to_usize(v___x_170_);
v___x_172_ = ((size_t)5ULL);
v___x_173_ = lean_unsigned_to_nat(1u);
v___x_174_ = ((size_t)1ULL);
v___x_175_ = lean_usize_sub(v_depth_161_, v___x_174_);
v___x_176_ = lean_usize_mul(v___x_172_, v___x_175_);
v_h_177_ = lean_usize_shift_right(v_h_171_, v___x_176_);
v___x_178_ = lean_nat_add(v_i_164_, v___x_173_);
lean_dec(v_i_164_);
lean_inc(v_v_169_);
lean_inc(v_k_168_);
v___x_179_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(v_entries_165_, v_h_177_, v_depth_161_, v_k_168_, v_v_169_);
v_i_164_ = v___x_178_;
v_entries_165_ = v___x_179_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_161_ = stack[0].m_num;
lean_object* v_keys_162_ = stack[1].m_obj;
lean_object* v_vals_163_ = stack[2].m_obj;
lean_object* v_i_164_ = stack[3].m_obj;
lean_object* v_entries_165_ = stack[4].m_obj;
lean_object* v_res_181_;
v_res_181_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_161_, v_keys_162_, v_vals_163_, v_i_164_, v_entries_165_);
stack->m_obj
 = v_res_181_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_depth_182_, lean_object* v_keys_183_, lean_object* v_vals_184_, lean_object* v_i_185_, lean_object* v_entries_186_){
_start:
{
size_t v_depth_boxed_187_; lean_object* v_res_188_; 
v_depth_boxed_187_ = lean_unbox_usize(v_depth_182_);
lean_dec(v_depth_182_);
v_res_188_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_187_, v_keys_183_, v_vals_184_, v_i_185_, v_entries_186_);
lean_dec_ref(v_vals_184_);
lean_dec_ref(v_keys_183_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_189_, lean_object* v_x_190_, lean_object* v_x_191_, lean_object* v_x_192_, lean_object* v_x_193_){
_start:
{
size_t v_x_1393__boxed_194_; size_t v_x_1394__boxed_195_; lean_object* v_res_196_; 
v_x_1393__boxed_194_ = lean_unbox_usize(v_x_190_);
lean_dec(v_x_190_);
v_x_1394__boxed_195_ = lean_unbox_usize(v_x_191_);
lean_dec(v_x_191_);
v_res_196_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(v_x_189_, v_x_1393__boxed_194_, v_x_1394__boxed_195_, v_x_192_, v_x_193_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0___redArg(lean_object* v_x_197_, lean_object* v_x_198_, lean_object* v_x_199_){
_start:
{
uint64_t v___x_200_; size_t v___x_201_; size_t v___x_202_; lean_object* v___x_203_; 
v___x_200_ = l_Lean_instHashableMVarId_hash(v_x_198_);
v___x_201_ = lean_uint64_to_usize(v___x_200_);
v___x_202_ = ((size_t)1ULL);
v___x_203_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(v_x_197_, v___x_201_, v___x_202_, v_x_198_, v_x_199_);
return v___x_203_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(lean_object* v_mvarId_204_, lean_object* v_val_205_, lean_object* v___y_206_){
_start:
{
lean_object* v___x_208_; lean_object* v_mctx_209_; lean_object* v_cache_210_; lean_object* v_zetaDeltaFVarIds_211_; lean_object* v_postponed_212_; lean_object* v_diag_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_243_; 
v___x_208_ = lean_st_ref_take(v___y_206_);
v_mctx_209_ = lean_ctor_get(v___x_208_, 0);
v_cache_210_ = lean_ctor_get(v___x_208_, 1);
v_zetaDeltaFVarIds_211_ = lean_ctor_get(v___x_208_, 2);
v_postponed_212_ = lean_ctor_get(v___x_208_, 3);
v_diag_213_ = lean_ctor_get(v___x_208_, 4);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_243_ == 0)
{
v___x_215_ = v___x_208_;
v_isShared_216_ = v_isSharedCheck_243_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_diag_213_);
lean_inc(v_postponed_212_);
lean_inc(v_zetaDeltaFVarIds_211_);
lean_inc(v_cache_210_);
lean_inc(v_mctx_209_);
lean_dec(v___x_208_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_243_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v_depth_217_; lean_object* v_levelAssignDepth_218_; lean_object* v_lmvarCounter_219_; lean_object* v_mvarCounter_220_; lean_object* v_lDecls_221_; lean_object* v_decls_222_; lean_object* v_userNames_223_; lean_object* v_lAssignment_224_; lean_object* v_eAssignment_225_; lean_object* v_dAssignment_226_; lean_object* v_instanceTypedMVars_227_; lean_object* v_synthNormMemo_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_242_; 
v_depth_217_ = lean_ctor_get(v_mctx_209_, 0);
v_levelAssignDepth_218_ = lean_ctor_get(v_mctx_209_, 1);
v_lmvarCounter_219_ = lean_ctor_get(v_mctx_209_, 2);
v_mvarCounter_220_ = lean_ctor_get(v_mctx_209_, 3);
v_lDecls_221_ = lean_ctor_get(v_mctx_209_, 4);
v_decls_222_ = lean_ctor_get(v_mctx_209_, 5);
v_userNames_223_ = lean_ctor_get(v_mctx_209_, 6);
v_lAssignment_224_ = lean_ctor_get(v_mctx_209_, 7);
v_eAssignment_225_ = lean_ctor_get(v_mctx_209_, 8);
v_dAssignment_226_ = lean_ctor_get(v_mctx_209_, 9);
v_instanceTypedMVars_227_ = lean_ctor_get(v_mctx_209_, 10);
v_synthNormMemo_228_ = lean_ctor_get(v_mctx_209_, 11);
v_isSharedCheck_242_ = !lean_is_exclusive(v_mctx_209_);
if (v_isSharedCheck_242_ == 0)
{
v___x_230_ = v_mctx_209_;
v_isShared_231_ = v_isSharedCheck_242_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_synthNormMemo_228_);
lean_inc(v_instanceTypedMVars_227_);
lean_inc(v_dAssignment_226_);
lean_inc(v_eAssignment_225_);
lean_inc(v_lAssignment_224_);
lean_inc(v_userNames_223_);
lean_inc(v_decls_222_);
lean_inc(v_lDecls_221_);
lean_inc(v_mvarCounter_220_);
lean_inc(v_lmvarCounter_219_);
lean_inc(v_levelAssignDepth_218_);
lean_inc(v_depth_217_);
lean_dec(v_mctx_209_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_242_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_235_; 
v___x_232_ = lean_box(0);
v___x_233_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0___redArg(v_eAssignment_225_, v_mvarId_204_, v_val_205_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 8, v___x_233_);
v___x_235_ = v___x_230_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_depth_217_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v_levelAssignDepth_218_);
lean_ctor_set(v_reuseFailAlloc_241_, 2, v_lmvarCounter_219_);
lean_ctor_set(v_reuseFailAlloc_241_, 3, v_mvarCounter_220_);
lean_ctor_set(v_reuseFailAlloc_241_, 4, v_lDecls_221_);
lean_ctor_set(v_reuseFailAlloc_241_, 5, v_decls_222_);
lean_ctor_set(v_reuseFailAlloc_241_, 6, v_userNames_223_);
lean_ctor_set(v_reuseFailAlloc_241_, 7, v_lAssignment_224_);
lean_ctor_set(v_reuseFailAlloc_241_, 8, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_241_, 9, v_dAssignment_226_);
lean_ctor_set(v_reuseFailAlloc_241_, 10, v_instanceTypedMVars_227_);
lean_ctor_set(v_reuseFailAlloc_241_, 11, v_synthNormMemo_228_);
v___x_235_ = v_reuseFailAlloc_241_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
lean_object* v___x_237_; 
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 0, v___x_235_);
v___x_237_ = v___x_215_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_235_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v_cache_210_);
lean_ctor_set(v_reuseFailAlloc_240_, 2, v_zetaDeltaFVarIds_211_);
lean_ctor_set(v_reuseFailAlloc_240_, 3, v_postponed_212_);
lean_ctor_set(v_reuseFailAlloc_240_, 4, v_diag_213_);
v___x_237_ = v_reuseFailAlloc_240_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = lean_st_ref_put(v___y_206_, v___x_237_);
v___x_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_239_, 0, v___x_232_);
return v___x_239_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_204_ = stack[0].m_obj;
lean_object* v_val_205_ = stack[1].m_obj;
lean_object* v___y_206_ = stack[2].m_obj;
lean_object* v_res_244_;
v_res_244_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(v_mvarId_204_, v_val_205_, v___y_206_);
stack->m_obj
 = v_res_244_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg___boxed(lean_object* v_mvarId_245_, lean_object* v_val_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(v_mvarId_245_, v_val_246_, v___y_247_);
lean_dec(v___y_247_);
return v_res_249_;
}
}
lean_object* l_Lean_MVarId_assert___lam__0(lean_object* v_mvarId_250_, lean_object* v___x_251_, lean_object* v_name_252_, lean_object* v_type_253_, lean_object* v_val_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v___x_260_; 
lean_inc(v_mvarId_250_);
v___x_260_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_250_, v___x_251_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v___x_261_; 
lean_dec_ref_known(v___x_260_, 1);
lean_inc(v_mvarId_250_);
v___x_261_ = l_Lean_MVarId_getTag(v_mvarId_250_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_a_262_; lean_object* v___x_263_; 
v_a_262_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_a_262_);
lean_dec_ref_known(v___x_261_, 1);
lean_inc(v_mvarId_250_);
v___x_263_ = l_Lean_MVarId_getType(v_mvarId_250_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v_a_264_; uint8_t v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v_a_264_ = lean_ctor_get(v___x_263_, 0);
lean_inc(v_a_264_);
lean_dec_ref_known(v___x_263_, 1);
v___x_265_ = 0;
v___x_266_ = l_Lean_mkForall(v_name_252_, v___x_265_, v_type_253_, v_a_264_);
v___x_267_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_266_, v_a_262_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v_a_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_278_; 
v_a_268_ = lean_ctor_get(v___x_267_, 0);
lean_inc_n(v_a_268_, 2);
lean_dec_ref_known(v___x_267_, 1);
v___x_269_ = l_Lean_Expr_app___override(v_a_268_, v_val_254_);
v___x_270_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(v_mvarId_250_, v___x_269_, v___y_256_);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_278_ == 0)
{
lean_object* v_unused_279_; 
v_unused_279_ = lean_ctor_get(v___x_270_, 0);
lean_dec(v_unused_279_);
v___x_272_ = v___x_270_;
v_isShared_273_ = v_isSharedCheck_278_;
goto v_resetjp_271_;
}
else
{
lean_dec(v___x_270_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_278_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_274_; lean_object* v___x_276_; 
v___x_274_ = l_Lean_Expr_mvarId_x21(v_a_268_);
lean_dec(v_a_268_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 0, v___x_274_);
v___x_276_ = v___x_272_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_274_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
else
{
lean_object* v_a_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_287_; 
lean_dec_ref(v_val_254_);
lean_dec(v_mvarId_250_);
v_a_280_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_287_ == 0)
{
v___x_282_ = v___x_267_;
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_a_280_);
lean_dec(v___x_267_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_285_; 
if (v_isShared_283_ == 0)
{
v___x_285_ = v___x_282_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_a_280_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
else
{
lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_295_; 
lean_dec(v_a_262_);
lean_dec_ref(v_val_254_);
lean_dec_ref(v_type_253_);
lean_dec(v_name_252_);
lean_dec(v_mvarId_250_);
v_a_288_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_295_ == 0)
{
v___x_290_ = v___x_263_;
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_263_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_293_; 
if (v_isShared_291_ == 0)
{
v___x_293_ = v___x_290_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_a_288_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
}
else
{
lean_object* v_a_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_303_; 
lean_dec_ref(v_val_254_);
lean_dec_ref(v_type_253_);
lean_dec(v_name_252_);
lean_dec(v_mvarId_250_);
v_a_296_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_303_ == 0)
{
v___x_298_ = v___x_261_;
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_a_296_);
lean_dec(v___x_261_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_301_; 
if (v_isShared_299_ == 0)
{
v___x_301_ = v___x_298_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_a_296_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
else
{
lean_object* v_a_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_311_; 
lean_dec_ref(v_val_254_);
lean_dec_ref(v_type_253_);
lean_dec(v_name_252_);
lean_dec(v_mvarId_250_);
v_a_304_ = lean_ctor_get(v___x_260_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_311_ == 0)
{
v___x_306_ = v___x_260_;
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_a_304_);
lean_dec(v___x_260_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_309_; 
if (v_isShared_307_ == 0)
{
v___x_309_ = v___x_306_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_a_304_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assert___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_250_ = stack[0].m_obj;
lean_object* v___x_251_ = stack[1].m_obj;
lean_object* v_name_252_ = stack[2].m_obj;
lean_object* v_type_253_ = stack[3].m_obj;
lean_object* v_val_254_ = stack[4].m_obj;
lean_object* v___y_255_ = stack[5].m_obj;
lean_object* v___y_256_ = stack[6].m_obj;
lean_object* v___y_257_ = stack[7].m_obj;
lean_object* v___y_258_ = stack[8].m_obj;
lean_object* v_res_312_;
v_res_312_ = l_Lean_MVarId_assert___lam__0(v_mvarId_250_, v___x_251_, v_name_252_, v_type_253_, v_val_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
stack->m_obj
 = v_res_312_;
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
lean_object* l_Lean_MVarId_assert(lean_object* v_mvarId_327_, lean_object* v_name_328_, lean_object* v_type_329_, lean_object* v_val_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_){
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
LEAN_EXPORT void l_Lean_MVarId_assert_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_327_ = stack[0].m_obj;
lean_object* v_name_328_ = stack[1].m_obj;
lean_object* v_type_329_ = stack[2].m_obj;
lean_object* v_val_330_ = stack[3].m_obj;
lean_object* v_a_331_ = stack[4].m_obj;
lean_object* v_a_332_ = stack[5].m_obj;
lean_object* v_a_333_ = stack[6].m_obj;
lean_object* v_a_334_ = stack[7].m_obj;
lean_object* v_res_339_;
v_res_339_ = l_Lean_MVarId_assert(v_mvarId_327_, v_name_328_, v_type_329_, v_val_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_);
stack->m_obj
 = v_res_339_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assert___boxed(lean_object* v_mvarId_340_, lean_object* v_name_341_, lean_object* v_type_342_, lean_object* v_val_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_MVarId_assert(v_mvarId_340_, v_name_341_, v_type_342_, v_val_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_);
lean_dec(v_a_347_);
lean_dec_ref(v_a_346_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
return v_res_349_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0(lean_object* v_mvarId_350_, lean_object* v_val_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(v_mvarId_350_, v_val_351_, v___y_353_);
return v___x_357_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_350_ = stack[0].m_obj;
lean_object* v_val_351_ = stack[1].m_obj;
lean_object* v___y_352_ = stack[2].m_obj;
lean_object* v___y_353_ = stack[3].m_obj;
lean_object* v___y_354_ = stack[4].m_obj;
lean_object* v___y_355_ = stack[5].m_obj;
lean_object* v_res_358_;
v_res_358_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0(v_mvarId_350_, v_val_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_);
stack->m_obj
 = v_res_358_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___boxed(lean_object* v_mvarId_359_, lean_object* v_val_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0(v_mvarId_359_, v_val_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0(lean_object* v_00_u03b2_367_, lean_object* v_x_368_, lean_object* v_x_369_, lean_object* v_x_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0___redArg(v_x_368_, v_x_369_, v_x_370_);
return v___x_371_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_372_, lean_object* v_x_373_, size_t v_x_374_, size_t v_x_375_, lean_object* v_x_376_, lean_object* v_x_377_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(v_x_373_, v_x_374_, v_x_375_, v_x_376_, v_x_377_);
return v___x_378_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_373_ = stack[1].m_obj;
size_t v_x_374_ = stack[2].m_num;
size_t v_x_375_ = stack[3].m_num;
lean_object* v_x_376_ = stack[4].m_obj;
lean_object* v_x_377_ = stack[5].m_obj;
lean_object* v_res_379_;
v_res_379_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2(lean_box(0), v_x_373_, v_x_374_, v_x_375_, v_x_376_, v_x_377_);
stack->m_obj
 = v_res_379_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_380_, lean_object* v_x_381_, lean_object* v_x_382_, lean_object* v_x_383_, lean_object* v_x_384_, lean_object* v_x_385_){
_start:
{
size_t v_x_1972__boxed_386_; size_t v_x_1973__boxed_387_; lean_object* v_res_388_; 
v_x_1972__boxed_386_ = lean_unbox_usize(v_x_382_);
lean_dec(v_x_382_);
v_x_1973__boxed_387_ = lean_unbox_usize(v_x_383_);
lean_dec(v_x_383_);
v_res_388_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2(v_00_u03b2_380_, v_x_381_, v_x_1972__boxed_386_, v_x_1973__boxed_387_, v_x_384_, v_x_385_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_389_, lean_object* v_n_390_, lean_object* v_k_391_, lean_object* v_v_392_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3___redArg(v_n_390_, v_k_391_, v_v_392_);
return v___x_393_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_394_, size_t v_depth_395_, lean_object* v_keys_396_, lean_object* v_vals_397_, lean_object* v_heq_398_, lean_object* v_i_399_, lean_object* v_entries_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_395_, v_keys_396_, v_vals_397_, v_i_399_, v_entries_400_);
return v___x_401_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
size_t v_depth_395_ = stack[1].m_num;
lean_object* v_keys_396_ = stack[2].m_obj;
lean_object* v_vals_397_ = stack[3].m_obj;
lean_object* v_i_399_ = stack[5].m_obj;
lean_object* v_entries_400_ = stack[6].m_obj;
lean_object* v_res_402_;
v_res_402_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4(lean_box(0), v_depth_395_, v_keys_396_, v_vals_397_, lean_box(0), v_i_399_, v_entries_400_);
stack->m_obj
 = v_res_402_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_403_, lean_object* v_depth_404_, lean_object* v_keys_405_, lean_object* v_vals_406_, lean_object* v_heq_407_, lean_object* v_i_408_, lean_object* v_entries_409_){
_start:
{
size_t v_depth_boxed_410_; lean_object* v_res_411_; 
v_depth_boxed_410_ = lean_unbox_usize(v_depth_404_);
lean_dec(v_depth_404_);
v_res_411_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_403_, v_depth_boxed_410_, v_keys_405_, v_vals_406_, v_heq_407_, v_i_408_, v_entries_409_);
lean_dec_ref(v_vals_406_);
lean_dec_ref(v_keys_405_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_412_, lean_object* v_x_413_, lean_object* v_x_414_, lean_object* v_x_415_, lean_object* v_x_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_413_, v_x_414_, v_x_415_, v_x_416_);
return v___x_417_;
}
}
lean_object* l_Lean_MVarId_note(lean_object* v_g_418_, lean_object* v_h_419_, lean_object* v_v_420_, lean_object* v_t_x3f_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
lean_object* v_____do__lift_428_; lean_object* v___y_429_; lean_object* v___y_430_; lean_object* v___y_431_; lean_object* v___y_432_; 
if (lean_obj_tag(v_t_x3f_421_) == 0)
{
lean_object* v___x_445_; 
lean_inc(v_a_425_);
lean_inc_ref(v_a_424_);
lean_inc(v_a_423_);
lean_inc_ref(v_a_422_);
lean_inc_ref(v_v_420_);
v___x_445_ = lean_infer_type(v_v_420_, v_a_422_, v_a_423_, v_a_424_, v_a_425_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_a_446_; 
v_a_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_a_446_);
lean_dec_ref_known(v___x_445_, 1);
v_____do__lift_428_ = v_a_446_;
v___y_429_ = v_a_422_;
v___y_430_ = v_a_423_;
v___y_431_ = v_a_424_;
v___y_432_ = v_a_425_;
goto v___jp_427_;
}
else
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
lean_dec_ref(v_v_420_);
lean_dec(v_h_419_);
lean_dec(v_g_418_);
v_a_447_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v___x_445_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_445_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
else
{
lean_object* v_val_455_; 
v_val_455_ = lean_ctor_get(v_t_x3f_421_, 0);
lean_inc(v_val_455_);
lean_dec_ref_known(v_t_x3f_421_, 1);
v_____do__lift_428_ = v_val_455_;
v___y_429_ = v_a_422_;
v___y_430_ = v_a_423_;
v___y_431_ = v_a_424_;
v___y_432_ = v_a_425_;
goto v___jp_427_;
}
v___jp_427_:
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_MVarId_assert(v_g_418_, v_h_419_, v_____do__lift_428_, v_v_420_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; uint8_t v___x_435_; lean_object* v___x_436_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_a_434_);
lean_dec_ref_known(v___x_433_, 1);
v___x_435_ = 1;
v___x_436_ = l_Lean_Meta_intro1Core(v_a_434_, v___x_435_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
return v___x_436_;
}
else
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_444_; 
v_a_437_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_444_ == 0)
{
v___x_439_ = v___x_433_;
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_433_);
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
}
}
LEAN_EXPORT void l_Lean_MVarId_note_0interp(lean_interpreter_value* stack)
{
lean_object* v_g_418_ = stack[0].m_obj;
lean_object* v_h_419_ = stack[1].m_obj;
lean_object* v_v_420_ = stack[2].m_obj;
lean_object* v_t_x3f_421_ = stack[3].m_obj;
lean_object* v_a_422_ = stack[4].m_obj;
lean_object* v_a_423_ = stack[5].m_obj;
lean_object* v_a_424_ = stack[6].m_obj;
lean_object* v_a_425_ = stack[7].m_obj;
lean_object* v_res_456_;
v_res_456_ = l_Lean_MVarId_note(v_g_418_, v_h_419_, v_v_420_, v_t_x3f_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_);
stack->m_obj
 = v_res_456_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_note___boxed(lean_object* v_g_457_, lean_object* v_h_458_, lean_object* v_v_459_, lean_object* v_t_x3f_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lean_MVarId_note(v_g_457_, v_h_458_, v_v_459_, v_t_x3f_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_);
lean_dec(v_a_464_);
lean_dec_ref(v_a_463_);
lean_dec(v_a_462_);
lean_dec_ref(v_a_461_);
return v_res_466_;
}
}
lean_object* l_Lean_MVarId_define___lam__0(lean_object* v_mvarId_467_, lean_object* v___x_468_, lean_object* v_name_469_, lean_object* v_type_470_, lean_object* v_val_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v___x_477_; 
lean_inc(v_mvarId_467_);
v___x_477_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_467_, v___x_468_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v___x_478_; 
lean_dec_ref_known(v___x_477_, 1);
lean_inc(v_mvarId_467_);
v___x_478_ = l_Lean_MVarId_getTag(v_mvarId_467_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; lean_object* v___x_480_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_a_479_);
lean_dec_ref_known(v___x_478_, 1);
lean_inc(v_mvarId_467_);
v___x_480_ = l_Lean_MVarId_getType(v_mvarId_467_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v_a_481_; uint8_t v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v_a_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc(v_a_481_);
lean_dec_ref_known(v___x_480_, 1);
v___x_482_ = 0;
v___x_483_ = l_Lean_Expr_letE___override(v_name_469_, v_type_470_, v_val_471_, v_a_481_, v___x_482_);
v___x_484_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_483_, v_a_479_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; lean_object* v___x_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_494_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
lean_inc_n(v_a_485_, 2);
lean_dec_ref_known(v___x_484_, 1);
v___x_486_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(v_mvarId_467_, v_a_485_, v___y_473_);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_494_ == 0)
{
lean_object* v_unused_495_; 
v_unused_495_ = lean_ctor_get(v___x_486_, 0);
lean_dec(v_unused_495_);
v___x_488_ = v___x_486_;
v_isShared_489_ = v_isSharedCheck_494_;
goto v_resetjp_487_;
}
else
{
lean_dec(v___x_486_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_494_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_490_; lean_object* v___x_492_; 
v___x_490_ = l_Lean_Expr_mvarId_x21(v_a_485_);
lean_dec(v_a_485_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 0, v___x_490_);
v___x_492_ = v___x_488_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_490_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
else
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
lean_dec(v_mvarId_467_);
v_a_496_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v___x_484_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_484_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_496_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
else
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_511_; 
lean_dec(v_a_479_);
lean_dec_ref(v_val_471_);
lean_dec_ref(v_type_470_);
lean_dec(v_name_469_);
lean_dec(v_mvarId_467_);
v_a_504_ = lean_ctor_get(v___x_480_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_511_ == 0)
{
v___x_506_ = v___x_480_;
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_480_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_509_; 
if (v_isShared_507_ == 0)
{
v___x_509_ = v___x_506_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_a_504_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
else
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
lean_dec_ref(v_val_471_);
lean_dec_ref(v_type_470_);
lean_dec(v_name_469_);
lean_dec(v_mvarId_467_);
v_a_512_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v___x_478_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_478_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_a_512_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
else
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_527_; 
lean_dec_ref(v_val_471_);
lean_dec_ref(v_type_470_);
lean_dec(v_name_469_);
lean_dec(v_mvarId_467_);
v_a_520_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_527_ == 0)
{
v___x_522_ = v___x_477_;
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_477_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_525_; 
if (v_isShared_523_ == 0)
{
v___x_525_ = v___x_522_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_a_520_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_define___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_467_ = stack[0].m_obj;
lean_object* v___x_468_ = stack[1].m_obj;
lean_object* v_name_469_ = stack[2].m_obj;
lean_object* v_type_470_ = stack[3].m_obj;
lean_object* v_val_471_ = stack[4].m_obj;
lean_object* v___y_472_ = stack[5].m_obj;
lean_object* v___y_473_ = stack[6].m_obj;
lean_object* v___y_474_ = stack[7].m_obj;
lean_object* v___y_475_ = stack[8].m_obj;
lean_object* v_res_528_;
v_res_528_ = l_Lean_MVarId_define___lam__0(v_mvarId_467_, v___x_468_, v_name_469_, v_type_470_, v_val_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
stack->m_obj
 = v_res_528_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_define___lam__0___boxed(lean_object* v_mvarId_529_, lean_object* v___x_530_, lean_object* v_name_531_, lean_object* v_type_532_, lean_object* v_val_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_MVarId_define___lam__0(v_mvarId_529_, v___x_530_, v_name_531_, v_type_532_, v_val_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
return v_res_539_;
}
}
lean_object* l_Lean_MVarId_define(lean_object* v_mvarId_543_, lean_object* v_name_544_, lean_object* v_type_545_, lean_object* v_val_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_){
_start:
{
lean_object* v___x_552_; lean_object* v___f_553_; lean_object* v___x_554_; 
v___x_552_ = ((lean_object*)(l_Lean_MVarId_define___closed__1));
lean_inc(v_mvarId_543_);
v___f_553_ = lean_alloc_closure((void*)(l_Lean_MVarId_define___lam__0___boxed), 10, 5);
lean_closure_set(v___f_553_, 0, v_mvarId_543_);
lean_closure_set(v___f_553_, 1, v___x_552_);
lean_closure_set(v___f_553_, 2, v_name_544_);
lean_closure_set(v___f_553_, 3, v_type_545_);
lean_closure_set(v___f_553_, 4, v_val_546_);
v___x_554_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(v_mvarId_543_, v___f_553_, v_a_547_, v_a_548_, v_a_549_, v_a_550_);
return v___x_554_;
}
}
LEAN_EXPORT void l_Lean_MVarId_define_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_543_ = stack[0].m_obj;
lean_object* v_name_544_ = stack[1].m_obj;
lean_object* v_type_545_ = stack[2].m_obj;
lean_object* v_val_546_ = stack[3].m_obj;
lean_object* v_a_547_ = stack[4].m_obj;
lean_object* v_a_548_ = stack[5].m_obj;
lean_object* v_a_549_ = stack[6].m_obj;
lean_object* v_a_550_ = stack[7].m_obj;
lean_object* v_res_555_;
v_res_555_ = l_Lean_MVarId_define(v_mvarId_543_, v_name_544_, v_type_545_, v_val_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_);
stack->m_obj
 = v_res_555_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_define___boxed(lean_object* v_mvarId_556_, lean_object* v_name_557_, lean_object* v_type_558_, lean_object* v_val_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Lean_MVarId_define(v_mvarId_556_, v_name_557_, v_type_558_, v_val_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
return v_res_565_;
}
}
static lean_object* _init_l_Lean_MVarId_assertExt___lam__0___closed__2(void){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = lean_unsigned_to_nat(0u);
v___x_570_ = l_Lean_mkBVar(v___x_569_);
return v___x_570_;
}
}
lean_object* l_Lean_MVarId_assertExt___lam__0(lean_object* v_mvarId_571_, lean_object* v___x_572_, lean_object* v_type_573_, lean_object* v_val_574_, lean_object* v_hName_575_, lean_object* v_name_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v___x_582_; 
lean_inc(v_mvarId_571_);
v___x_582_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_571_, v___x_572_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v___x_583_; 
lean_dec_ref_known(v___x_582_, 1);
lean_inc(v_mvarId_571_);
v___x_583_ = l_Lean_MVarId_getTag(v_mvarId_571_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_584_; lean_object* v___x_585_; 
v_a_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc(v_a_584_);
lean_dec_ref_known(v___x_583_, 1);
lean_inc(v_mvarId_571_);
v___x_585_ = l_Lean_MVarId_getType(v_mvarId_571_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; lean_object* v___x_587_; 
v_a_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc(v_a_586_);
lean_dec_ref_known(v___x_585_, 1);
lean_inc_ref(v_type_573_);
v___x_587_ = l_Lean_Meta_getLevel(v_type_573_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; uint8_t v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_a_588_);
lean_dec_ref_known(v___x_587_, 1);
v___x_589_ = ((lean_object*)(l_Lean_MVarId_assertExt___lam__0___closed__1));
v___x_590_ = lean_box(0);
v___x_591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_591_, 0, v_a_588_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
v___x_592_ = l_Lean_mkConst(v___x_589_, v___x_591_);
v___x_593_ = lean_obj_once(&l_Lean_MVarId_assertExt___lam__0___closed__2, &l_Lean_MVarId_assertExt___lam__0___closed__2_once, _init_l_Lean_MVarId_assertExt___lam__0___closed__2);
lean_inc_ref(v_val_574_);
lean_inc_ref(v_type_573_);
v___x_594_ = l_Lean_mkApp3(v___x_592_, v_type_573_, v___x_593_, v_val_574_);
v___x_595_ = 0;
v___x_596_ = l_Lean_mkForall(v_hName_575_, v___x_595_, v___x_594_, v_a_586_);
v___x_597_ = l_Lean_mkForall(v_name_576_, v___x_595_, v_type_573_, v___x_596_);
v___x_598_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_597_, v_a_584_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v_a_599_; lean_object* v___x_600_; 
v_a_599_ = lean_ctor_get(v___x_598_, 0);
lean_inc(v_a_599_);
lean_dec_ref_known(v___x_598_, 1);
lean_inc_ref(v_val_574_);
v___x_600_ = l_Lean_Meta_mkEqRefl(v_val_574_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_611_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_a_601_);
lean_dec_ref_known(v___x_600_, 1);
lean_inc(v_a_599_);
v___x_602_ = l_Lean_mkAppB(v_a_599_, v_val_574_, v_a_601_);
v___x_603_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(v_mvarId_571_, v___x_602_, v___y_578_);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_611_ == 0)
{
lean_object* v_unused_612_; 
v_unused_612_ = lean_ctor_get(v___x_603_, 0);
lean_dec(v_unused_612_);
v___x_605_ = v___x_603_;
v_isShared_606_ = v_isSharedCheck_611_;
goto v_resetjp_604_;
}
else
{
lean_dec(v___x_603_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_611_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_607_; lean_object* v___x_609_; 
v___x_607_ = l_Lean_Expr_mvarId_x21(v_a_599_);
lean_dec(v_a_599_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 0, v___x_607_);
v___x_609_ = v___x_605_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_607_);
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
lean_object* v_a_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_620_; 
lean_dec(v_a_599_);
lean_dec_ref(v_val_574_);
lean_dec(v_mvarId_571_);
v_a_613_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_620_ == 0)
{
v___x_615_ = v___x_600_;
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_a_613_);
lean_dec(v___x_600_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_618_; 
if (v_isShared_616_ == 0)
{
v___x_618_ = v___x_615_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_a_613_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
}
else
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
lean_dec_ref(v_val_574_);
lean_dec(v_mvarId_571_);
v_a_621_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_628_ == 0)
{
v___x_623_ = v___x_598_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_598_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_621_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
else
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_636_; 
lean_dec(v_a_586_);
lean_dec(v_a_584_);
lean_dec(v_name_576_);
lean_dec(v_hName_575_);
lean_dec_ref(v_val_574_);
lean_dec_ref(v_type_573_);
lean_dec(v_mvarId_571_);
v_a_629_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_636_ == 0)
{
v___x_631_ = v___x_587_;
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_587_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_634_; 
if (v_isShared_632_ == 0)
{
v___x_634_ = v___x_631_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_a_629_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
}
else
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
lean_dec(v_a_584_);
lean_dec(v_name_576_);
lean_dec(v_hName_575_);
lean_dec_ref(v_val_574_);
lean_dec_ref(v_type_573_);
lean_dec(v_mvarId_571_);
v_a_637_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_644_ == 0)
{
v___x_639_ = v___x_585_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_585_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_637_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
else
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
lean_dec(v_name_576_);
lean_dec(v_hName_575_);
lean_dec_ref(v_val_574_);
lean_dec_ref(v_type_573_);
lean_dec(v_mvarId_571_);
v_a_645_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_652_ == 0)
{
v___x_647_ = v___x_583_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_583_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_a_645_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
else
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_660_; 
lean_dec(v_name_576_);
lean_dec(v_hName_575_);
lean_dec_ref(v_val_574_);
lean_dec_ref(v_type_573_);
lean_dec(v_mvarId_571_);
v_a_653_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_660_ == 0)
{
v___x_655_ = v___x_582_;
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_582_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_a_653_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assertExt___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_571_ = stack[0].m_obj;
lean_object* v___x_572_ = stack[1].m_obj;
lean_object* v_type_573_ = stack[2].m_obj;
lean_object* v_val_574_ = stack[3].m_obj;
lean_object* v_hName_575_ = stack[4].m_obj;
lean_object* v_name_576_ = stack[5].m_obj;
lean_object* v___y_577_ = stack[6].m_obj;
lean_object* v___y_578_ = stack[7].m_obj;
lean_object* v___y_579_ = stack[8].m_obj;
lean_object* v___y_580_ = stack[9].m_obj;
lean_object* v_res_661_;
v_res_661_ = l_Lean_MVarId_assertExt___lam__0(v_mvarId_571_, v___x_572_, v_type_573_, v_val_574_, v_hName_575_, v_name_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
stack->m_obj
 = v_res_661_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertExt___lam__0___boxed(lean_object* v_mvarId_662_, lean_object* v___x_663_, lean_object* v_type_664_, lean_object* v_val_665_, lean_object* v_hName_666_, lean_object* v_name_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_MVarId_assertExt___lam__0(v_mvarId_662_, v___x_663_, v_type_664_, v_val_665_, v_hName_666_, v_name_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
return v_res_673_;
}
}
lean_object* l_Lean_MVarId_assertExt(lean_object* v_mvarId_674_, lean_object* v_name_675_, lean_object* v_type_676_, lean_object* v_val_677_, lean_object* v_hName_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
lean_object* v___x_684_; lean_object* v___f_685_; lean_object* v___x_686_; 
v___x_684_ = ((lean_object*)(l_Lean_MVarId_assert___closed__1));
lean_inc(v_mvarId_674_);
v___f_685_ = lean_alloc_closure((void*)(l_Lean_MVarId_assertExt___lam__0___boxed), 11, 6);
lean_closure_set(v___f_685_, 0, v_mvarId_674_);
lean_closure_set(v___f_685_, 1, v___x_684_);
lean_closure_set(v___f_685_, 2, v_type_676_);
lean_closure_set(v___f_685_, 3, v_val_677_);
lean_closure_set(v___f_685_, 4, v_hName_678_);
lean_closure_set(v___f_685_, 5, v_name_675_);
v___x_686_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(v_mvarId_674_, v___f_685_, v_a_679_, v_a_680_, v_a_681_, v_a_682_);
return v___x_686_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assertExt_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_674_ = stack[0].m_obj;
lean_object* v_name_675_ = stack[1].m_obj;
lean_object* v_type_676_ = stack[2].m_obj;
lean_object* v_val_677_ = stack[3].m_obj;
lean_object* v_hName_678_ = stack[4].m_obj;
lean_object* v_a_679_ = stack[5].m_obj;
lean_object* v_a_680_ = stack[6].m_obj;
lean_object* v_a_681_ = stack[7].m_obj;
lean_object* v_a_682_ = stack[8].m_obj;
lean_object* v_res_687_;
v_res_687_ = l_Lean_MVarId_assertExt(v_mvarId_674_, v_name_675_, v_type_676_, v_val_677_, v_hName_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_);
stack->m_obj
 = v_res_687_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertExt___boxed(lean_object* v_mvarId_688_, lean_object* v_name_689_, lean_object* v_type_690_, lean_object* v_val_691_, lean_object* v_hName_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Lean_MVarId_assertExt(v_mvarId_688_, v_name_689_, v_type_690_, v_val_691_, v_hName_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_);
lean_dec(v_a_696_);
lean_dec_ref(v_a_695_);
lean_dec(v_a_694_);
lean_dec_ref(v_a_693_);
return v_res_698_;
}
}
lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___redArg(lean_object* v_t_699_, lean_object* v___y_700_){
_start:
{
lean_object* v___x_702_; lean_object* v_infoState_703_; uint8_t v_enabled_704_; 
v___x_702_ = lean_st_ref_get(v___y_700_);
v_infoState_703_ = lean_ctor_get(v___x_702_, 8);
lean_inc_ref(v_infoState_703_);
lean_dec(v___x_702_);
v_enabled_704_ = lean_ctor_get_uint8(v_infoState_703_, sizeof(void*)*3);
lean_dec_ref(v_infoState_703_);
if (v_enabled_704_ == 0)
{
lean_object* v___x_705_; lean_object* v___x_706_; 
lean_dec_ref(v_t_699_);
v___x_705_ = lean_box(0);
v___x_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
return v___x_706_;
}
else
{
lean_object* v___x_707_; lean_object* v_infoState_708_; lean_object* v_env_709_; lean_object* v_nextMacroScope_710_; lean_object* v_ngen_711_; lean_object* v_auxDeclNGen_712_; lean_object* v_traceState_713_; lean_object* v_cache_714_; lean_object* v_recordedDeps_715_; lean_object* v_messages_716_; lean_object* v_snapshotTasks_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_739_; 
v___x_707_ = lean_st_ref_take(v___y_700_);
v_infoState_708_ = lean_ctor_get(v___x_707_, 8);
v_env_709_ = lean_ctor_get(v___x_707_, 0);
v_nextMacroScope_710_ = lean_ctor_get(v___x_707_, 1);
v_ngen_711_ = lean_ctor_get(v___x_707_, 2);
v_auxDeclNGen_712_ = lean_ctor_get(v___x_707_, 3);
v_traceState_713_ = lean_ctor_get(v___x_707_, 4);
v_cache_714_ = lean_ctor_get(v___x_707_, 5);
v_recordedDeps_715_ = lean_ctor_get(v___x_707_, 6);
v_messages_716_ = lean_ctor_get(v___x_707_, 7);
v_snapshotTasks_717_ = lean_ctor_get(v___x_707_, 9);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_739_ == 0)
{
v___x_719_ = v___x_707_;
v_isShared_720_ = v_isSharedCheck_739_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_snapshotTasks_717_);
lean_inc(v_infoState_708_);
lean_inc(v_messages_716_);
lean_inc(v_recordedDeps_715_);
lean_inc(v_cache_714_);
lean_inc(v_traceState_713_);
lean_inc(v_auxDeclNGen_712_);
lean_inc(v_ngen_711_);
lean_inc(v_nextMacroScope_710_);
lean_inc(v_env_709_);
lean_dec(v___x_707_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_739_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
uint8_t v_enabled_721_; lean_object* v_assignment_722_; lean_object* v_lazyAssignment_723_; lean_object* v_trees_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_738_; 
v_enabled_721_ = lean_ctor_get_uint8(v_infoState_708_, sizeof(void*)*3);
v_assignment_722_ = lean_ctor_get(v_infoState_708_, 0);
v_lazyAssignment_723_ = lean_ctor_get(v_infoState_708_, 1);
v_trees_724_ = lean_ctor_get(v_infoState_708_, 2);
v_isSharedCheck_738_ = !lean_is_exclusive(v_infoState_708_);
if (v_isSharedCheck_738_ == 0)
{
v___x_726_ = v_infoState_708_;
v_isShared_727_ = v_isSharedCheck_738_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_trees_724_);
lean_inc(v_lazyAssignment_723_);
lean_inc(v_assignment_722_);
lean_dec(v_infoState_708_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_738_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_731_; 
v___x_728_ = lean_box(0);
v___x_729_ = l_Lean_PersistentArray_push___redArg(v_trees_724_, v_t_699_);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 2, v___x_729_);
v___x_731_ = v___x_726_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_assignment_722_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_lazyAssignment_723_);
lean_ctor_set(v_reuseFailAlloc_737_, 2, v___x_729_);
lean_ctor_set_uint8(v_reuseFailAlloc_737_, sizeof(void*)*3, v_enabled_721_);
v___x_731_ = v_reuseFailAlloc_737_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
lean_object* v___x_733_; 
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 8, v___x_731_);
v___x_733_ = v___x_719_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_env_709_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v_nextMacroScope_710_);
lean_ctor_set(v_reuseFailAlloc_736_, 2, v_ngen_711_);
lean_ctor_set(v_reuseFailAlloc_736_, 3, v_auxDeclNGen_712_);
lean_ctor_set(v_reuseFailAlloc_736_, 4, v_traceState_713_);
lean_ctor_set(v_reuseFailAlloc_736_, 5, v_cache_714_);
lean_ctor_set(v_reuseFailAlloc_736_, 6, v_recordedDeps_715_);
lean_ctor_set(v_reuseFailAlloc_736_, 7, v_messages_716_);
lean_ctor_set(v_reuseFailAlloc_736_, 8, v___x_731_);
lean_ctor_set(v_reuseFailAlloc_736_, 9, v_snapshotTasks_717_);
v___x_733_ = v_reuseFailAlloc_736_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = lean_st_ref_put(v___y_700_, v___x_733_);
v___x_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_735_, 0, v___x_728_);
return v___x_735_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_699_ = stack[0].m_obj;
lean_object* v___y_700_ = stack[1].m_obj;
lean_object* v_res_740_;
v_res_740_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___redArg(v_t_699_, v___y_700_);
stack->m_obj
 = v_res_740_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___redArg___boxed(lean_object* v_t_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___redArg(v_t_741_, v___y_742_);
lean_dec(v___y_742_);
return v_res_744_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__0(void){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_745_ = lean_unsigned_to_nat(32u);
v___x_746_ = lean_mk_empty_array_with_capacity(v___x_745_);
v___x_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
return v___x_747_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__1(void){
_start:
{
size_t v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_748_ = ((size_t)5ULL);
v___x_749_ = lean_unsigned_to_nat(0u);
v___x_750_ = lean_unsigned_to_nat(32u);
v___x_751_ = lean_mk_empty_array_with_capacity(v___x_750_);
v___x_752_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__0);
v___x_753_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_753_, 0, v___x_752_);
lean_ctor_set(v___x_753_, 1, v___x_751_);
lean_ctor_set(v___x_753_, 2, v___x_749_);
lean_ctor_set(v___x_753_, 3, v___x_749_);
lean_ctor_set_usize(v___x_753_, 4, v___x_748_);
return v___x_753_;
}
}
lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0(lean_object* v_t_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v___x_760_; lean_object* v_infoState_761_; uint8_t v_enabled_762_; 
v___x_760_ = lean_st_ref_get(v___y_758_);
v_infoState_761_ = lean_ctor_get(v___x_760_, 8);
lean_inc_ref(v_infoState_761_);
lean_dec(v___x_760_);
v_enabled_762_ = lean_ctor_get_uint8(v_infoState_761_, sizeof(void*)*3);
lean_dec_ref(v_infoState_761_);
if (v_enabled_762_ == 0)
{
lean_object* v___x_763_; lean_object* v___x_764_; 
lean_dec_ref(v_t_754_);
v___x_763_ = lean_box(0);
v___x_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_764_, 0, v___x_763_);
return v___x_764_;
}
else
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_765_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__1);
v___x_766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_766_, 0, v_t_754_);
lean_ctor_set(v___x_766_, 1, v___x_765_);
v___x_767_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___redArg(v___x_766_, v___y_758_);
return v___x_767_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_754_ = stack[0].m_obj;
lean_object* v___y_755_ = stack[1].m_obj;
lean_object* v___y_756_ = stack[2].m_obj;
lean_object* v___y_757_ = stack[3].m_obj;
lean_object* v___y_758_ = stack[4].m_obj;
lean_object* v_res_768_;
v_res_768_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0(v_t_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
stack->m_obj
 = v_res_768_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___boxed(lean_object* v_t_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0(v_t_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
return v_res_775_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__1(lean_object* v___x_776_, lean_object* v_as_777_, size_t v_sz_778_, size_t v_i_779_, lean_object* v_b_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
uint8_t v___x_786_; 
v___x_786_ = lean_usize_dec_lt(v_i_779_, v_sz_778_);
if (v___x_786_ == 0)
{
lean_object* v___x_787_; 
lean_dec_ref(v___x_776_);
v___x_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_787_, 0, v_b_780_);
return v___x_787_;
}
else
{
lean_object* v_snd_788_; lean_object* v_fst_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_836_; 
v_snd_788_ = lean_ctor_get(v_b_780_, 1);
v_fst_789_ = lean_ctor_get(v_b_780_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v_b_780_);
if (v_isSharedCheck_836_ == 0)
{
v___x_791_ = v_b_780_;
v_isShared_792_ = v_isSharedCheck_836_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_snd_788_);
lean_inc(v_fst_789_);
lean_dec(v_b_780_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_836_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v_array_793_; lean_object* v_start_794_; lean_object* v_stop_795_; uint8_t v___x_796_; 
v_array_793_ = lean_ctor_get(v_snd_788_, 0);
v_start_794_ = lean_ctor_get(v_snd_788_, 1);
v_stop_795_ = lean_ctor_get(v_snd_788_, 2);
v___x_796_ = lean_nat_dec_lt(v_start_794_, v_stop_795_);
if (v___x_796_ == 0)
{
lean_object* v___x_798_; 
lean_dec_ref(v___x_776_);
if (v_isShared_792_ == 0)
{
v___x_798_ = v___x_791_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_fst_789_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v_snd_788_);
v___x_798_ = v_reuseFailAlloc_800_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
lean_object* v___x_799_; 
v___x_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
return v___x_799_;
}
}
else
{
lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_832_; 
lean_inc(v_stop_795_);
lean_inc(v_start_794_);
lean_inc_ref(v_array_793_);
v_isSharedCheck_832_ = !lean_is_exclusive(v_snd_788_);
if (v_isSharedCheck_832_ == 0)
{
lean_object* v_unused_833_; lean_object* v_unused_834_; lean_object* v_unused_835_; 
v_unused_833_ = lean_ctor_get(v_snd_788_, 2);
lean_dec(v_unused_833_);
v_unused_834_ = lean_ctor_get(v_snd_788_, 1);
lean_dec(v_unused_834_);
v_unused_835_ = lean_ctor_get(v_snd_788_, 0);
lean_dec(v_unused_835_);
v___x_802_ = v_snd_788_;
v_isShared_803_ = v_isSharedCheck_832_;
goto v_resetjp_801_;
}
else
{
lean_dec(v_snd_788_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_832_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v_a_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_809_; 
v_a_804_ = lean_array_uget_borrowed(v_as_777_, v_i_779_);
v___x_805_ = lean_array_fget(v_array_793_, v_start_794_);
v___x_806_ = lean_unsigned_to_nat(1u);
v___x_807_ = lean_nat_add(v_start_794_, v___x_806_);
lean_dec(v_start_794_);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 1, v___x_807_);
v___x_809_ = v___x_802_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_array_793_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v___x_807_);
lean_ctor_set(v_reuseFailAlloc_831_, 2, v_stop_795_);
v___x_809_ = v_reuseFailAlloc_831_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
lean_inc_n(v___x_805_, 2);
v___x_810_ = l_Lean_mkFVar(v___x_805_);
lean_inc_n(v_a_804_, 2);
v___x_811_ = l_Lean_Meta_FVarSubst_insert(v_fst_789_, v_a_804_, v___x_810_);
lean_inc_ref(v___x_776_);
v___x_812_ = l_Lean_LocalContext_get_x21(v___x_776_, v___x_805_);
v___x_813_ = l_Lean_LocalDecl_userName(v___x_812_);
lean_dec_ref(v___x_812_);
v___x_814_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
lean_ctor_set(v___x_814_, 1, v___x_805_);
lean_ctor_set(v___x_814_, 2, v_a_804_);
v___x_815_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
v___x_816_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0(v___x_815_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v___x_818_; 
lean_dec_ref_known(v___x_816_, 1);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 1, v___x_809_);
lean_ctor_set(v___x_791_, 0, v___x_811_);
v___x_818_ = v___x_791_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_811_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v___x_809_);
v___x_818_ = v_reuseFailAlloc_822_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
size_t v___x_819_; size_t v___x_820_; 
v___x_819_ = ((size_t)1ULL);
v___x_820_ = lean_usize_add(v_i_779_, v___x_819_);
v_i_779_ = v___x_820_;
v_b_780_ = v___x_818_;
goto _start;
}
}
else
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_830_; 
lean_dec(v___x_811_);
lean_dec_ref(v___x_809_);
lean_del_object(v___x_791_);
lean_dec_ref(v___x_776_);
v_a_823_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_830_ == 0)
{
v___x_825_ = v___x_816_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_816_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_823_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_776_ = stack[0].m_obj;
lean_object* v_as_777_ = stack[1].m_obj;
size_t v_sz_778_ = stack[2].m_num;
size_t v_i_779_ = stack[3].m_num;
lean_object* v_b_780_ = stack[4].m_obj;
lean_object* v___y_781_ = stack[5].m_obj;
lean_object* v___y_782_ = stack[6].m_obj;
lean_object* v___y_783_ = stack[7].m_obj;
lean_object* v___y_784_ = stack[8].m_obj;
lean_object* v_res_837_;
v_res_837_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__1(v___x_776_, v_as_777_, v_sz_778_, v_i_779_, v_b_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
stack->m_obj
 = v_res_837_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__1___boxed(lean_object* v___x_838_, lean_object* v_as_839_, lean_object* v_sz_840_, lean_object* v_i_841_, lean_object* v_b_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
size_t v_sz_boxed_848_; size_t v_i_boxed_849_; lean_object* v_res_850_; 
v_sz_boxed_848_ = lean_unbox_usize(v_sz_840_);
lean_dec(v_sz_840_);
v_i_boxed_849_ = lean_unbox_usize(v_i_841_);
lean_dec(v_i_841_);
v_res_850_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__1(v___x_838_, v_as_839_, v_sz_boxed_848_, v_i_boxed_849_, v_b_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec_ref(v_as_839_);
return v_res_850_;
}
}
lean_object* l_Lean_MVarId_assertAfter(lean_object* v_mvarId_854_, lean_object* v_fvarId_855_, lean_object* v_userName_856_, lean_object* v_type_857_, lean_object* v_val_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = ((lean_object*)(l_Lean_MVarId_assertAfter___closed__1));
lean_inc(v_mvarId_854_);
v___x_865_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_854_, v___x_864_, v_a_859_, v_a_860_, v_a_861_, v_a_862_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v___x_866_; 
lean_dec_ref_known(v___x_865_, 1);
v___x_866_ = l_Lean_MVarId_revertAfter(v_mvarId_854_, v_fvarId_855_, v_a_859_, v_a_860_, v_a_861_, v_a_862_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; lean_object* v_fst_868_; lean_object* v_snd_869_; lean_object* v___x_870_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_867_);
lean_dec_ref_known(v___x_866_, 1);
v_fst_868_ = lean_ctor_get(v_a_867_, 0);
lean_inc(v_fst_868_);
v_snd_869_ = lean_ctor_get(v_a_867_, 1);
lean_inc(v_snd_869_);
lean_dec(v_a_867_);
v___x_870_ = l_Lean_MVarId_assert(v_snd_869_, v_userName_856_, v_type_857_, v_val_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; uint8_t v___x_872_; lean_object* v___x_873_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
lean_inc(v_a_871_);
lean_dec_ref_known(v___x_870_, 1);
v___x_872_ = 1;
v___x_873_ = l_Lean_Meta_intro1Core(v_a_871_, v___x_872_, v_a_859_, v_a_860_, v_a_861_, v_a_862_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v_a_874_; lean_object* v_fst_875_; lean_object* v_snd_876_; lean_object* v___x_877_; lean_object* v___x_878_; uint8_t v___x_879_; lean_object* v___x_880_; 
v_a_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_a_874_);
lean_dec_ref_known(v___x_873_, 1);
v_fst_875_ = lean_ctor_get(v_a_874_, 0);
lean_inc(v_fst_875_);
v_snd_876_ = lean_ctor_get(v_a_874_, 1);
lean_inc(v_snd_876_);
lean_dec(v_a_874_);
v___x_877_ = lean_array_get_size(v_fst_868_);
v___x_878_ = lean_box(0);
v___x_879_ = 0;
v___x_880_ = l_Lean_Meta_introNCore(v_snd_876_, v___x_877_, v___x_878_, v___x_879_, v___x_872_, v_a_859_, v_a_860_, v_a_861_, v_a_862_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; lean_object* v_fst_882_; lean_object* v_snd_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_926_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_a_881_);
lean_dec_ref_known(v___x_880_, 1);
v_fst_882_ = lean_ctor_get(v_a_881_, 0);
v_snd_883_ = lean_ctor_get(v_a_881_, 1);
v_isSharedCheck_926_ = !lean_is_exclusive(v_a_881_);
if (v_isSharedCheck_926_ == 0)
{
v___x_885_ = v_a_881_;
v_isShared_886_ = v_isSharedCheck_926_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_snd_883_);
lean_inc(v_fst_882_);
lean_dec(v_a_881_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_926_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_887_; 
lean_inc(v_snd_883_);
v___x_887_ = l_Lean_MVarId_getDecl(v_snd_883_, v_a_859_, v_a_860_, v_a_861_, v_a_862_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; lean_object* v_lctx_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_895_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_a_888_);
lean_dec_ref_known(v___x_887_, 1);
v_lctx_889_ = lean_ctor_get(v_a_888_, 1);
lean_inc_ref(v_lctx_889_);
lean_dec(v_a_888_);
v___x_890_ = lean_box(0);
v___x_891_ = lean_unsigned_to_nat(0u);
v___x_892_ = lean_array_get_size(v_fst_882_);
v___x_893_ = l_Array_toSubarray___redArg(v_fst_882_, v___x_891_, v___x_892_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 1, v___x_893_);
lean_ctor_set(v___x_885_, 0, v___x_890_);
v___x_895_ = v___x_885_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_890_);
lean_ctor_set(v_reuseFailAlloc_917_, 1, v___x_893_);
v___x_895_ = v_reuseFailAlloc_917_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
size_t v_sz_896_; size_t v___x_897_; lean_object* v___x_898_; 
v_sz_896_ = lean_array_size(v_fst_868_);
v___x_897_ = ((size_t)0ULL);
v___x_898_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__1(v_lctx_889_, v_fst_868_, v_sz_896_, v___x_897_, v___x_895_, v_a_859_, v_a_860_, v_a_861_, v_a_862_);
lean_dec(v_fst_868_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_908_; 
v_a_899_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_908_ == 0)
{
v___x_901_ = v___x_898_;
v_isShared_902_ = v_isSharedCheck_908_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_898_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_908_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v_fst_903_; lean_object* v___x_904_; lean_object* v___x_906_; 
v_fst_903_ = lean_ctor_get(v_a_899_, 0);
lean_inc(v_fst_903_);
lean_dec(v_a_899_);
v___x_904_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_904_, 0, v_fst_875_);
lean_ctor_set(v___x_904_, 1, v_snd_883_);
lean_ctor_set(v___x_904_, 2, v_fst_903_);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 0, v___x_904_);
v___x_906_ = v___x_901_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_904_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
else
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_916_; 
lean_dec(v_snd_883_);
lean_dec(v_fst_875_);
v_a_909_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_916_ == 0)
{
v___x_911_ = v___x_898_;
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_898_);
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
}
else
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_925_; 
lean_del_object(v___x_885_);
lean_dec(v_snd_883_);
lean_dec(v_fst_882_);
lean_dec(v_fst_875_);
lean_dec(v_fst_868_);
v_a_918_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_925_ == 0)
{
v___x_920_ = v___x_887_;
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_887_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_923_; 
if (v_isShared_921_ == 0)
{
v___x_923_ = v___x_920_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_918_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
}
else
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
lean_dec(v_fst_875_);
lean_dec(v_fst_868_);
v_a_927_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_934_ == 0)
{
v___x_929_ = v___x_880_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_880_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_a_927_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
else
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_942_; 
lean_dec(v_fst_868_);
v_a_935_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_942_ == 0)
{
v___x_937_ = v___x_873_;
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_873_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_938_ == 0)
{
v___x_940_ = v___x_937_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_a_935_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
else
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_950_; 
lean_dec(v_fst_868_);
v_a_943_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_950_ == 0)
{
v___x_945_ = v___x_870_;
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_870_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_948_; 
if (v_isShared_946_ == 0)
{
v___x_948_ = v___x_945_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_a_943_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
else
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_958_; 
lean_dec_ref(v_val_858_);
lean_dec_ref(v_type_857_);
lean_dec(v_userName_856_);
v_a_951_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_958_ == 0)
{
v___x_953_ = v___x_866_;
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___x_866_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_956_; 
if (v_isShared_954_ == 0)
{
v___x_956_ = v___x_953_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_a_951_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
else
{
lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_966_; 
lean_dec_ref(v_val_858_);
lean_dec_ref(v_type_857_);
lean_dec(v_userName_856_);
lean_dec(v_fvarId_855_);
lean_dec(v_mvarId_854_);
v_a_959_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_966_ == 0)
{
v___x_961_ = v___x_865_;
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_865_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_964_; 
if (v_isShared_962_ == 0)
{
v___x_964_ = v___x_961_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_a_959_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assertAfter_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_854_ = stack[0].m_obj;
lean_object* v_fvarId_855_ = stack[1].m_obj;
lean_object* v_userName_856_ = stack[2].m_obj;
lean_object* v_type_857_ = stack[3].m_obj;
lean_object* v_val_858_ = stack[4].m_obj;
lean_object* v_a_859_ = stack[5].m_obj;
lean_object* v_a_860_ = stack[6].m_obj;
lean_object* v_a_861_ = stack[7].m_obj;
lean_object* v_a_862_ = stack[8].m_obj;
lean_object* v_res_967_;
v_res_967_ = l_Lean_MVarId_assertAfter(v_mvarId_854_, v_fvarId_855_, v_userName_856_, v_type_857_, v_val_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_);
stack->m_obj
 = v_res_967_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertAfter___boxed(lean_object* v_mvarId_968_, lean_object* v_fvarId_969_, lean_object* v_userName_970_, lean_object* v_type_971_, lean_object* v_val_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lean_MVarId_assertAfter(v_mvarId_968_, v_fvarId_969_, v_userName_970_, v_type_971_, v_val_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
return v_res_978_;
}
}
lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0(lean_object* v_t_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___redArg(v_t_979_, v___y_983_);
return v___x_985_;
}
}
LEAN_EXPORT void l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_979_ = stack[0].m_obj;
lean_object* v___y_980_ = stack[1].m_obj;
lean_object* v___y_981_ = stack[2].m_obj;
lean_object* v___y_982_ = stack[3].m_obj;
lean_object* v___y_983_ = stack[4].m_obj;
lean_object* v_res_986_;
v_res_986_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0(v_t_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_);
stack->m_obj
 = v_res_986_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___boxed(lean_object* v_t_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0(v_t_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
return v_res_993_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg(lean_object* v_ldecl_x27_994_, lean_object* v_a_995_){
_start:
{
lean_object* v___x_997_; lean_object* v_fst_999_; lean_object* v_snd_1000_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; uint8_t v___x_1006_; 
v___x_997_ = lean_st_ref_take(v_a_995_);
v___x_1003_ = lean_box(0);
v___x_1004_ = l_Lean_LocalDecl_index(v___x_997_);
v___x_1005_ = l_Lean_LocalDecl_index(v_ldecl_x27_994_);
v___x_1006_ = lean_nat_dec_lt(v___x_1004_, v___x_1005_);
lean_dec(v___x_1005_);
lean_dec(v___x_1004_);
if (v___x_1006_ == 0)
{
lean_dec_ref(v_ldecl_x27_994_);
v_fst_999_ = v___x_1003_;
v_snd_1000_ = v___x_997_;
goto v___jp_998_;
}
else
{
lean_dec(v___x_997_);
v_fst_999_ = v___x_1003_;
v_snd_1000_ = v_ldecl_x27_994_;
goto v___jp_998_;
}
v___jp_998_:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = lean_st_ref_put(v_a_995_, v_snd_1000_);
v___x_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1002_, 0, v_fst_999_);
return v___x_1002_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ldecl_x27_994_ = stack[0].m_obj;
lean_object* v_a_995_ = stack[1].m_obj;
lean_object* v_res_1007_;
v_res_1007_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg(v_ldecl_x27_994_, v_a_995_);
stack->m_obj
 = v_res_1007_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg___boxed(lean_object* v_ldecl_x27_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg(v_ldecl_x27_1008_, v_a_1009_);
lean_dec(v_a_1009_);
return v_res_1011_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl(lean_object* v_ldecl_x27_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg(v_ldecl_x27_1012_, v_a_1013_);
return v___x_1019_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_ldecl_x27_1012_ = stack[0].m_obj;
lean_object* v_a_1013_ = stack[1].m_obj;
lean_object* v_a_1014_ = stack[2].m_obj;
lean_object* v_a_1015_ = stack[3].m_obj;
lean_object* v_a_1016_ = stack[4].m_obj;
lean_object* v_a_1017_ = stack[5].m_obj;
lean_object* v_res_1020_;
v_res_1020_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl(v_ldecl_x27_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
stack->m_obj
 = v_res_1020_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___boxed(lean_object* v_ldecl_x27_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl(v_ldecl_x27_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_);
lean_dec(v_a_1026_);
lean_dec_ref(v_a_1025_);
lean_dec(v_a_1024_);
lean_dec_ref(v_a_1023_);
lean_dec(v_a_1022_);
return v_res_1028_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___redArg(lean_object* v_as_1029_, size_t v_i_1030_, size_t v_stop_1031_, lean_object* v_b_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_a_1039_; uint8_t v___x_1043_; 
v___x_1043_ = lean_usize_dec_eq(v_i_1030_, v_stop_1031_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; 
v___x_1044_ = lean_array_uget_borrowed(v_as_1029_, v_i_1030_);
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v___x_1045_; 
v___x_1045_ = lean_box(0);
v_a_1039_ = v___x_1045_;
goto v___jp_1038_;
}
else
{
lean_object* v_val_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v_val_1046_ = lean_ctor_get(v___x_1044_, 0);
v___x_1047_ = l_Lean_LocalDecl_fvarId(v_val_1046_);
v___x_1048_ = l_Lean_FVarId_getDecl___redArg(v___x_1047_, v___y_1034_, v___y_1035_, v___y_1036_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v_a_1049_; lean_object* v___x_1050_; 
v_a_1049_ = lean_ctor_get(v___x_1048_, 0);
lean_inc(v_a_1049_);
lean_dec_ref_known(v___x_1048_, 1);
v___x_1050_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg(v_a_1049_, v___y_1033_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_a_1051_; 
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_a_1051_);
lean_dec_ref_known(v___x_1050_, 1);
v_a_1039_ = v_a_1051_;
goto v___jp_1038_;
}
else
{
return v___x_1050_;
}
}
else
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
v_a_1052_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1048_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1048_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
}
else
{
lean_object* v___x_1060_; 
v___x_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1060_, 0, v_b_1032_);
return v___x_1060_;
}
v___jp_1038_:
{
size_t v___x_1040_; size_t v___x_1041_; 
v___x_1040_ = ((size_t)1ULL);
v___x_1041_ = lean_usize_add(v_i_1030_, v___x_1040_);
v_i_1030_ = v___x_1041_;
v_b_1032_ = v_a_1039_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1029_ = stack[0].m_obj;
size_t v_i_1030_ = stack[1].m_num;
size_t v_stop_1031_ = stack[2].m_num;
lean_object* v_b_1032_ = stack[3].m_obj;
lean_object* v___y_1033_ = stack[4].m_obj;
lean_object* v___y_1034_ = stack[5].m_obj;
lean_object* v___y_1035_ = stack[6].m_obj;
lean_object* v___y_1036_ = stack[7].m_obj;
lean_object* v_res_1061_;
v_res_1061_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___redArg(v_as_1029_, v_i_1030_, v_stop_1031_, v_b_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
stack->m_obj
 = v_res_1061_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_as_1062_, lean_object* v_i_1063_, lean_object* v_stop_1064_, lean_object* v_b_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
size_t v_i_boxed_1071_; size_t v_stop_boxed_1072_; lean_object* v_res_1073_; 
v_i_boxed_1071_ = lean_unbox_usize(v_i_1063_);
lean_dec(v_i_1063_);
v_stop_boxed_1072_ = lean_unbox_usize(v_stop_1064_);
lean_dec(v_stop_1064_);
v_res_1073_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___redArg(v_as_1062_, v_i_boxed_1071_, v_stop_boxed_1072_, v_b_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec(v___y_1066_);
lean_dec_ref(v_as_1062_);
return v_res_1073_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(lean_object* v_as_1074_, size_t v_i_1075_, size_t v_stop_1076_, lean_object* v_b_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v_a_1085_; uint8_t v___x_1089_; 
v___x_1089_ = lean_usize_dec_eq(v_i_1075_, v_stop_1076_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; 
v___x_1090_ = lean_array_uget_borrowed(v_as_1074_, v_i_1075_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v___x_1091_; 
v___x_1091_ = lean_box(0);
v_a_1085_ = v___x_1091_;
goto v___jp_1084_;
}
else
{
lean_object* v_val_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v_val_1092_ = lean_ctor_get(v___x_1090_, 0);
v___x_1093_ = l_Lean_LocalDecl_fvarId(v_val_1092_);
v___x_1094_ = l_Lean_FVarId_getDecl___redArg(v___x_1093_, v___y_1079_, v___y_1081_, v___y_1082_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v_a_1095_; lean_object* v___x_1096_; 
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
lean_inc(v_a_1095_);
lean_dec_ref_known(v___x_1094_, 1);
v___x_1096_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg(v_a_1095_, v___y_1078_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v_a_1097_; 
v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
lean_inc(v_a_1097_);
lean_dec_ref_known(v___x_1096_, 1);
v_a_1085_ = v_a_1097_;
goto v___jp_1084_;
}
else
{
return v___x_1096_;
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
v_a_1098_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1094_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1094_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
}
else
{
lean_object* v___x_1106_; 
v___x_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1106_, 0, v_b_1077_);
return v___x_1106_;
}
v___jp_1084_:
{
size_t v___x_1086_; size_t v___x_1087_; lean_object* v___x_1088_; 
v___x_1086_ = ((size_t)1ULL);
v___x_1087_ = lean_usize_add(v_i_1075_, v___x_1086_);
v___x_1088_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___redArg(v_as_1074_, v___x_1087_, v_stop_1076_, v_a_1085_, v___y_1078_, v___y_1079_, v___y_1081_, v___y_1082_);
return v___x_1088_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1074_ = stack[0].m_obj;
size_t v_i_1075_ = stack[1].m_num;
size_t v_stop_1076_ = stack[2].m_num;
lean_object* v_b_1077_ = stack[3].m_obj;
lean_object* v___y_1078_ = stack[4].m_obj;
lean_object* v___y_1079_ = stack[5].m_obj;
lean_object* v___y_1080_ = stack[6].m_obj;
lean_object* v___y_1081_ = stack[7].m_obj;
lean_object* v___y_1082_ = stack[8].m_obj;
lean_object* v_res_1107_;
v_res_1107_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_as_1074_, v_i_1075_, v_stop_1076_, v_b_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
stack->m_obj
 = v_res_1107_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2___boxed(lean_object* v_as_1108_, lean_object* v_i_1109_, lean_object* v_stop_1110_, lean_object* v_b_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
size_t v_i_boxed_1118_; size_t v_stop_boxed_1119_; lean_object* v_res_1120_; 
v_i_boxed_1118_ = lean_unbox_usize(v_i_1109_);
lean_dec(v_i_1109_);
v_stop_boxed_1119_ = lean_unbox_usize(v_stop_1110_);
lean_dec(v_stop_1110_);
v_res_1120_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_as_1108_, v_i_boxed_1118_, v_stop_boxed_1119_, v_b_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec(v___y_1112_);
lean_dec_ref(v_as_1108_);
return v_res_1120_;
}
}
lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
if (lean_obj_tag(v_x_1121_) == 0)
{
lean_object* v_cs_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1142_; 
v_cs_1128_ = lean_ctor_get(v_x_1121_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_x_1121_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1130_ = v_x_1121_;
v_isShared_1131_ = v_isSharedCheck_1142_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_cs_1128_);
lean_dec(v_x_1121_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1142_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; uint8_t v___x_1135_; 
v___x_1132_ = lean_unsigned_to_nat(0u);
v___x_1133_ = lean_array_get_size(v_cs_1128_);
v___x_1134_ = lean_box(0);
v___x_1135_ = lean_nat_dec_lt(v___x_1132_, v___x_1133_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1137_; 
lean_dec_ref(v_cs_1128_);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 0, v___x_1134_);
v___x_1137_ = v___x_1130_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1134_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
else
{
size_t v___x_1139_; size_t v___x_1140_; lean_object* v___x_1141_; 
lean_del_object(v___x_1130_);
v___x_1139_ = ((size_t)0ULL);
v___x_1140_ = lean_usize_of_nat(v___x_1133_);
v___x_1141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4(v_cs_1128_, v___x_1139_, v___x_1140_, v___x_1134_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
lean_dec_ref(v_cs_1128_);
return v___x_1141_;
}
}
}
else
{
lean_object* v_vs_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1157_; 
v_vs_1143_ = lean_ctor_get(v_x_1121_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v_x_1121_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1145_ = v_x_1121_;
v_isShared_1146_ = v_isSharedCheck_1157_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_vs_1143_);
lean_dec(v_x_1121_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1157_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; uint8_t v___x_1150_; 
v___x_1147_ = lean_unsigned_to_nat(0u);
v___x_1148_ = lean_array_get_size(v_vs_1143_);
v___x_1149_ = lean_box(0);
v___x_1150_ = lean_nat_dec_lt(v___x_1147_, v___x_1148_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1152_; 
lean_dec_ref(v_vs_1143_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set_tag(v___x_1145_, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1149_);
v___x_1152_ = v___x_1145_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1149_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
else
{
size_t v___x_1154_; size_t v___x_1155_; lean_object* v___x_1156_; 
lean_del_object(v___x_1145_);
v___x_1154_ = ((size_t)0ULL);
v___x_1155_ = lean_usize_of_nat(v___x_1148_);
v___x_1156_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_vs_1143_, v___x_1154_, v___x_1155_, v___x_1149_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
lean_dec_ref(v_vs_1143_);
return v___x_1156_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1121_ = stack[0].m_obj;
lean_object* v___y_1122_ = stack[1].m_obj;
lean_object* v___y_1123_ = stack[2].m_obj;
lean_object* v___y_1124_ = stack[3].m_obj;
lean_object* v___y_1125_ = stack[4].m_obj;
lean_object* v___y_1126_ = stack[5].m_obj;
lean_object* v_res_1158_;
v_res_1158_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__3(v_x_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
stack->m_obj
 = v_res_1158_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4(lean_object* v_as_1159_, size_t v_i_1160_, size_t v_stop_1161_, lean_object* v_b_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
uint8_t v___x_1169_; 
v___x_1169_ = lean_usize_dec_eq(v_i_1160_, v_stop_1161_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = lean_array_uget_borrowed(v_as_1159_, v_i_1160_);
lean_inc(v___x_1170_);
v___x_1171_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__3(v___x_1170_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v_a_1172_; size_t v___x_1173_; size_t v___x_1174_; 
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
lean_inc(v_a_1172_);
lean_dec_ref_known(v___x_1171_, 1);
v___x_1173_ = ((size_t)1ULL);
v___x_1174_ = lean_usize_add(v_i_1160_, v___x_1173_);
v_i_1160_ = v___x_1174_;
v_b_1162_ = v_a_1172_;
goto _start;
}
else
{
return v___x_1171_;
}
}
else
{
lean_object* v___x_1176_; 
v___x_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1176_, 0, v_b_1162_);
return v___x_1176_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1159_ = stack[0].m_obj;
size_t v_i_1160_ = stack[1].m_num;
size_t v_stop_1161_ = stack[2].m_num;
lean_object* v_b_1162_ = stack[3].m_obj;
lean_object* v___y_1163_ = stack[4].m_obj;
lean_object* v___y_1164_ = stack[5].m_obj;
lean_object* v___y_1165_ = stack[6].m_obj;
lean_object* v___y_1166_ = stack[7].m_obj;
lean_object* v___y_1167_ = stack[8].m_obj;
lean_object* v_res_1177_;
v_res_1177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4(v_as_1159_, v_i_1160_, v_stop_1161_, v_b_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
stack->m_obj
 = v_res_1177_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_as_1178_, lean_object* v_i_1179_, lean_object* v_stop_1180_, lean_object* v_b_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
size_t v_i_boxed_1188_; size_t v_stop_boxed_1189_; lean_object* v_res_1190_; 
v_i_boxed_1188_ = lean_unbox_usize(v_i_1179_);
lean_dec(v_i_1179_);
v_stop_boxed_1189_ = lean_unbox_usize(v_stop_1180_);
lean_dec(v_stop_1180_);
v_res_1190_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4(v_as_1178_, v_i_boxed_1188_, v_stop_boxed_1189_, v_b_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec_ref(v_as_1178_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__3(v_x_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
return v_res_1198_;
}
}
lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__3(lean_object* v_t_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
lean_object* v_root_1206_; lean_object* v_tail_1207_; lean_object* v___x_1208_; 
v_root_1206_ = lean_ctor_get(v_t_1199_, 0);
lean_inc_ref(v_root_1206_);
v_tail_1207_ = lean_ctor_get(v_t_1199_, 1);
lean_inc_ref(v_tail_1207_);
lean_dec_ref(v_t_1199_);
v___x_1208_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__3(v_root_1206_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1222_; 
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1222_ == 0)
{
lean_object* v_unused_1223_; 
v_unused_1223_ = lean_ctor_get(v___x_1208_, 0);
lean_dec(v_unused_1223_);
v___x_1210_ = v___x_1208_;
v_isShared_1211_ = v_isSharedCheck_1222_;
goto v_resetjp_1209_;
}
else
{
lean_dec(v___x_1208_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1222_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; uint8_t v___x_1215_; 
v___x_1212_ = lean_unsigned_to_nat(0u);
v___x_1213_ = lean_array_get_size(v_tail_1207_);
v___x_1214_ = lean_box(0);
v___x_1215_ = lean_nat_dec_lt(v___x_1212_, v___x_1213_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1217_; 
lean_dec_ref(v_tail_1207_);
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 0, v___x_1214_);
v___x_1217_ = v___x_1210_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1214_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
else
{
size_t v___x_1219_; size_t v___x_1220_; lean_object* v___x_1221_; 
lean_del_object(v___x_1210_);
v___x_1219_ = ((size_t)0ULL);
v___x_1220_ = lean_usize_of_nat(v___x_1213_);
v___x_1221_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_tail_1207_, v___x_1219_, v___x_1220_, v___x_1214_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
lean_dec_ref(v_tail_1207_);
return v___x_1221_;
}
}
}
else
{
lean_dec_ref(v_tail_1207_);
return v___x_1208_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1199_ = stack[0].m_obj;
lean_object* v___y_1200_ = stack[1].m_obj;
lean_object* v___y_1201_ = stack[2].m_obj;
lean_object* v___y_1202_ = stack[3].m_obj;
lean_object* v___y_1203_ = stack[4].m_obj;
lean_object* v___y_1204_ = stack[5].m_obj;
lean_object* v_res_1224_;
v_res_1224_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__3(v_t_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
stack->m_obj
 = v_res_1224_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__3___boxed(lean_object* v_t_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__3(v_t_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
return v_res_1232_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_1233_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1(lean_object* v_x_1234_, size_t v_x_1235_, size_t v_x_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
if (lean_obj_tag(v_x_1234_) == 0)
{
lean_object* v_cs_1243_; lean_object* v___x_1244_; size_t v___x_1245_; lean_object* v_j_1246_; lean_object* v___x_1247_; size_t v___x_1248_; size_t v___x_1249_; size_t v___x_1250_; size_t v___x_1251_; size_t v___x_1252_; size_t v___x_1253_; lean_object* v___x_1254_; 
v_cs_1243_ = lean_ctor_get(v_x_1234_, 0);
lean_inc_ref(v_cs_1243_);
lean_dec_ref_known(v_x_1234_, 1);
v___x_1244_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___closed__0);
v___x_1245_ = lean_usize_shift_right(v_x_1235_, v_x_1236_);
v_j_1246_ = lean_usize_to_nat(v___x_1245_);
v___x_1247_ = lean_array_get_borrowed(v___x_1244_, v_cs_1243_, v_j_1246_);
v___x_1248_ = ((size_t)1ULL);
v___x_1249_ = lean_usize_shift_left(v___x_1248_, v_x_1236_);
v___x_1250_ = lean_usize_sub(v___x_1249_, v___x_1248_);
v___x_1251_ = lean_usize_land(v_x_1235_, v___x_1250_);
v___x_1252_ = ((size_t)5ULL);
v___x_1253_ = lean_usize_sub(v_x_1236_, v___x_1252_);
lean_inc(v___x_1247_);
v___x_1254_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1(v___x_1247_, v___x_1251_, v___x_1253_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1269_; 
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1269_ == 0)
{
lean_object* v_unused_1270_; 
v_unused_1270_ = lean_ctor_get(v___x_1254_, 0);
lean_dec(v_unused_1270_);
v___x_1256_ = v___x_1254_;
v_isShared_1257_ = v_isSharedCheck_1269_;
goto v_resetjp_1255_;
}
else
{
lean_dec(v___x_1254_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1269_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; uint8_t v___x_1262_; 
v___x_1258_ = lean_unsigned_to_nat(1u);
v___x_1259_ = lean_nat_add(v_j_1246_, v___x_1258_);
lean_dec(v_j_1246_);
v___x_1260_ = lean_array_get_size(v_cs_1243_);
v___x_1261_ = lean_box(0);
v___x_1262_ = lean_nat_dec_lt(v___x_1259_, v___x_1260_);
if (v___x_1262_ == 0)
{
lean_object* v___x_1264_; 
lean_dec(v___x_1259_);
lean_dec_ref(v_cs_1243_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 0, v___x_1261_);
v___x_1264_ = v___x_1256_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1261_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
else
{
size_t v___x_1266_; size_t v___x_1267_; lean_object* v___x_1268_; 
lean_del_object(v___x_1256_);
v___x_1266_ = lean_usize_of_nat(v___x_1259_);
lean_dec(v___x_1259_);
v___x_1267_ = lean_usize_of_nat(v___x_1260_);
v___x_1268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4(v_cs_1243_, v___x_1266_, v___x_1267_, v___x_1261_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
lean_dec_ref(v_cs_1243_);
return v___x_1268_;
}
}
}
else
{
lean_dec(v_j_1246_);
lean_dec_ref(v_cs_1243_);
return v___x_1254_;
}
}
else
{
lean_object* v_vs_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1285_; 
v_vs_1271_ = lean_ctor_get(v_x_1234_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v_x_1234_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1273_ = v_x_1234_;
v_isShared_1274_ = v_isSharedCheck_1285_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_vs_1271_);
lean_dec(v_x_1234_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1285_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; uint8_t v___x_1278_; 
v___x_1275_ = lean_usize_to_nat(v_x_1235_);
v___x_1276_ = lean_array_get_size(v_vs_1271_);
v___x_1277_ = lean_box(0);
v___x_1278_ = lean_nat_dec_lt(v___x_1275_, v___x_1276_);
if (v___x_1278_ == 0)
{
lean_object* v___x_1280_; 
lean_dec(v___x_1275_);
lean_dec_ref(v_vs_1271_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set_tag(v___x_1273_, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1277_);
v___x_1280_ = v___x_1273_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1277_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
else
{
size_t v___x_1282_; size_t v___x_1283_; lean_object* v___x_1284_; 
lean_del_object(v___x_1273_);
v___x_1282_ = lean_usize_of_nat(v___x_1275_);
lean_dec(v___x_1275_);
v___x_1283_ = lean_usize_of_nat(v___x_1276_);
v___x_1284_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_vs_1271_, v___x_1282_, v___x_1283_, v___x_1277_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
lean_dec_ref(v_vs_1271_);
return v___x_1284_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1234_ = stack[0].m_obj;
size_t v_x_1235_ = stack[1].m_num;
size_t v_x_1236_ = stack[2].m_num;
lean_object* v___y_1237_ = stack[3].m_obj;
lean_object* v___y_1238_ = stack[4].m_obj;
lean_object* v___y_1239_ = stack[5].m_obj;
lean_object* v___y_1240_ = stack[6].m_obj;
lean_object* v___y_1241_ = stack[7].m_obj;
lean_object* v_res_1286_;
v_res_1286_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1(v_x_1234_, v_x_1235_, v_x_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
stack->m_obj
 = v_res_1286_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___boxed(lean_object* v_x_1287_, lean_object* v_x_1288_, lean_object* v_x_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
size_t v_x_8855__boxed_1296_; size_t v_x_8856__boxed_1297_; lean_object* v_res_1298_; 
v_x_8855__boxed_1296_ = lean_unbox_usize(v_x_1288_);
lean_dec(v_x_1288_);
v_x_8856__boxed_1297_ = lean_unbox_usize(v_x_1289_);
lean_dec(v_x_1289_);
v_res_1298_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1(v_x_1287_, v_x_8855__boxed_1296_, v_x_8856__boxed_1297_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
return v_res_1298_;
}
}
lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0(lean_object* v_t_1299_, lean_object* v_start_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v___x_1307_; uint8_t v___x_1308_; 
v___x_1307_ = lean_unsigned_to_nat(0u);
v___x_1308_ = lean_nat_dec_eq(v_start_1300_, v___x_1307_);
if (v___x_1308_ == 0)
{
lean_object* v_root_1309_; lean_object* v_tail_1310_; size_t v_shift_1311_; lean_object* v_tailOff_1312_; uint8_t v___x_1313_; 
v_root_1309_ = lean_ctor_get(v_t_1299_, 0);
lean_inc_ref(v_root_1309_);
v_tail_1310_ = lean_ctor_get(v_t_1299_, 1);
lean_inc_ref(v_tail_1310_);
v_shift_1311_ = lean_ctor_get_usize(v_t_1299_, 4);
v_tailOff_1312_ = lean_ctor_get(v_t_1299_, 3);
lean_inc(v_tailOff_1312_);
lean_dec_ref(v_t_1299_);
v___x_1313_ = lean_nat_dec_le(v_tailOff_1312_, v_start_1300_);
if (v___x_1313_ == 0)
{
size_t v___x_1314_; lean_object* v___x_1315_; 
lean_dec(v_tailOff_1312_);
v___x_1314_ = lean_usize_of_nat(v_start_1300_);
v___x_1315_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1(v_root_1309_, v___x_1314_, v_shift_1311_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1328_; 
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1328_ == 0)
{
lean_object* v_unused_1329_; 
v_unused_1329_ = lean_ctor_get(v___x_1315_, 0);
lean_dec(v_unused_1329_);
v___x_1317_ = v___x_1315_;
v_isShared_1318_ = v_isSharedCheck_1328_;
goto v_resetjp_1316_;
}
else
{
lean_dec(v___x_1315_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1328_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; uint8_t v___x_1321_; 
v___x_1319_ = lean_array_get_size(v_tail_1310_);
v___x_1320_ = lean_box(0);
v___x_1321_ = lean_nat_dec_lt(v___x_1307_, v___x_1319_);
if (v___x_1321_ == 0)
{
lean_object* v___x_1323_; 
lean_dec_ref(v_tail_1310_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 0, v___x_1320_);
v___x_1323_ = v___x_1317_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v___x_1320_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
else
{
size_t v___x_1325_; size_t v___x_1326_; lean_object* v___x_1327_; 
lean_del_object(v___x_1317_);
v___x_1325_ = ((size_t)0ULL);
v___x_1326_ = lean_usize_of_nat(v___x_1319_);
v___x_1327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_tail_1310_, v___x_1325_, v___x_1326_, v___x_1320_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
lean_dec_ref(v_tail_1310_);
return v___x_1327_;
}
}
}
else
{
lean_dec_ref(v_tail_1310_);
return v___x_1315_;
}
}
else
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; uint8_t v___x_1333_; 
lean_dec_ref(v_root_1309_);
v___x_1330_ = lean_nat_sub(v_start_1300_, v_tailOff_1312_);
lean_dec(v_tailOff_1312_);
v___x_1331_ = lean_array_get_size(v_tail_1310_);
v___x_1332_ = lean_box(0);
v___x_1333_ = lean_nat_dec_lt(v___x_1330_, v___x_1331_);
if (v___x_1333_ == 0)
{
lean_object* v___x_1334_; 
lean_dec(v___x_1330_);
lean_dec_ref(v_tail_1310_);
v___x_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1332_);
return v___x_1334_;
}
else
{
size_t v___x_1335_; size_t v___x_1336_; lean_object* v___x_1337_; 
v___x_1335_ = lean_usize_of_nat(v___x_1330_);
lean_dec(v___x_1330_);
v___x_1336_ = lean_usize_of_nat(v___x_1331_);
v___x_1337_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_tail_1310_, v___x_1335_, v___x_1336_, v___x_1332_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
lean_dec_ref(v_tail_1310_);
return v___x_1337_;
}
}
}
else
{
lean_object* v___x_1338_; 
v___x_1338_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__3(v_t_1299_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
return v___x_1338_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1299_ = stack[0].m_obj;
lean_object* v_start_1300_ = stack[1].m_obj;
lean_object* v___y_1301_ = stack[2].m_obj;
lean_object* v___y_1302_ = stack[3].m_obj;
lean_object* v___y_1303_ = stack[4].m_obj;
lean_object* v___y_1304_ = stack[5].m_obj;
lean_object* v___y_1305_ = stack[6].m_obj;
lean_object* v_res_1339_;
v_res_1339_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0(v_t_1299_, v_start_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
stack->m_obj
 = v_res_1339_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0___boxed(lean_object* v_t_1340_, lean_object* v_start_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0(v_t_1340_, v_start_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec(v_start_1341_);
return v_res_1348_;
}
}
lean_object* l_Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0(lean_object* v_lctx_1349_, lean_object* v_start_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v_decls_1357_; lean_object* v___x_1358_; 
v_decls_1357_ = lean_ctor_get(v_lctx_1349_, 1);
lean_inc_ref(v_decls_1357_);
lean_dec_ref(v_lctx_1349_);
v___x_1358_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0(v_decls_1357_, v_start_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
return v___x_1358_;
}
}
LEAN_EXPORT void l_Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_1349_ = stack[0].m_obj;
lean_object* v_start_1350_ = stack[1].m_obj;
lean_object* v___y_1351_ = stack[2].m_obj;
lean_object* v___y_1352_ = stack[3].m_obj;
lean_object* v___y_1353_ = stack[4].m_obj;
lean_object* v___y_1354_ = stack[5].m_obj;
lean_object* v___y_1355_ = stack[6].m_obj;
lean_object* v_res_1359_;
v_res_1359_ = l_Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0(v_lctx_1349_, v_start_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
stack->m_obj
 = v_res_1359_;
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0___boxed(lean_object* v_lctx_1360_, lean_object* v_start_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l_Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0(v_lctx_1360_, v_start_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
lean_dec(v___y_1362_);
lean_dec(v_start_1361_);
return v_res_1368_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___lam__0(lean_object* v_e_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
if (lean_obj_tag(v_e_1369_) == 1)
{
lean_object* v_fvarId_1376_; lean_object* v___x_1377_; 
v_fvarId_1376_ = lean_ctor_get(v_e_1369_, 0);
lean_inc(v_fvarId_1376_);
lean_dec_ref_known(v_e_1369_, 1);
v___x_1377_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1376_, v___y_1371_, v___y_1373_, v___y_1374_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; lean_object* v___x_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1388_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_a_1378_);
lean_dec_ref_known(v___x_1377_, 1);
v___x_1379_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg(v_a_1378_, v___y_1370_);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1388_ == 0)
{
lean_object* v_unused_1389_; 
v_unused_1389_ = lean_ctor_get(v___x_1379_, 0);
lean_dec(v_unused_1389_);
v___x_1381_ = v___x_1379_;
v_isShared_1382_ = v_isSharedCheck_1388_;
goto v_resetjp_1380_;
}
else
{
lean_dec(v___x_1379_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1388_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
uint8_t v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1386_; 
v___x_1383_ = 0;
v___x_1384_ = lean_box(v___x_1383_);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 0, v___x_1384_);
v___x_1386_ = v___x_1381_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1384_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
else
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1397_; 
v_a_1390_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1392_ = v___x_1377_;
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1377_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1395_; 
if (v_isShared_1393_ == 0)
{
v___x_1395_ = v___x_1392_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_a_1390_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
else
{
if (lean_obj_tag(v_e_1369_) == 2)
{
lean_object* v_mvarId_1398_; lean_object* v___x_1399_; 
v_mvarId_1398_ = lean_ctor_get(v_e_1369_, 0);
lean_inc(v_mvarId_1398_);
lean_dec_ref_known(v_e_1369_, 1);
v___x_1399_ = l_Lean_MVarId_getDecl(v_mvarId_1398_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v_a_1400_; lean_object* v_lctx_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
lean_inc(v_a_1400_);
lean_dec_ref_known(v___x_1399_, 1);
v_lctx_1401_ = lean_ctor_get(v_a_1400_, 1);
lean_inc_ref(v_lctx_1401_);
lean_dec(v_a_1400_);
v___x_1402_ = lean_unsigned_to_nat(0u);
v___x_1403_ = l_Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0(v_lctx_1401_, v___x_1402_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1412_; 
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1412_ == 0)
{
lean_object* v_unused_1413_; 
v_unused_1413_ = lean_ctor_get(v___x_1403_, 0);
lean_dec(v_unused_1413_);
v___x_1405_ = v___x_1403_;
v_isShared_1406_ = v_isSharedCheck_1412_;
goto v_resetjp_1404_;
}
else
{
lean_dec(v___x_1403_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1412_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
uint8_t v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1410_; 
v___x_1407_ = 0;
v___x_1408_ = lean_box(v___x_1407_);
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 0, v___x_1408_);
v___x_1410_ = v___x_1405_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___x_1408_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
else
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
v_a_1414_ = lean_ctor_get(v___x_1403_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1403_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1403_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1414_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
else
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
v_a_1422_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1424_ = v___x_1399_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1399_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1422_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
else
{
uint8_t v___x_1430_; 
v___x_1430_ = l_Lean_Expr_hasFVar(v_e_1369_);
if (v___x_1430_ == 0)
{
uint8_t v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1431_ = l_Lean_Expr_hasExprMVar(v_e_1369_);
lean_dec_ref(v_e_1369_);
v___x_1432_ = lean_box(v___x_1431_);
v___x_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
return v___x_1433_;
}
else
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
lean_dec_ref(v_e_1369_);
v___x_1434_ = lean_box(v___x_1430_);
v___x_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1434_);
return v___x_1435_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1369_ = stack[0].m_obj;
lean_object* v___y_1370_ = stack[1].m_obj;
lean_object* v___y_1371_ = stack[2].m_obj;
lean_object* v___y_1372_ = stack[3].m_obj;
lean_object* v___y_1373_ = stack[4].m_obj;
lean_object* v___y_1374_ = stack[5].m_obj;
lean_object* v_res_1436_;
v_res_1436_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___lam__0(v_e_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
stack->m_obj
 = v_res_1436_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___lam__0___boxed(lean_object* v_e_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___lam__0(v_e_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v___y_1438_);
return v_res_1444_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___redArg(lean_object* v_a_1445_, lean_object* v_x_1446_){
_start:
{
if (lean_obj_tag(v_x_1446_) == 0)
{
uint8_t v___x_1447_; 
v___x_1447_ = 0;
return v___x_1447_;
}
else
{
lean_object* v_key_1448_; lean_object* v_tail_1449_; uint8_t v___x_1450_; 
v_key_1448_ = lean_ctor_get(v_x_1446_, 0);
v_tail_1449_ = lean_ctor_get(v_x_1446_, 2);
v___x_1450_ = lean_expr_eqv(v_key_1448_, v_a_1445_);
if (v___x_1450_ == 0)
{
v_x_1446_ = v_tail_1449_;
goto _start;
}
else
{
return v___x_1450_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1445_ = stack[0].m_obj;
lean_object* v_x_1446_ = stack[1].m_obj;
uint8_t v_res_1452_;
v_res_1452_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___redArg(v_a_1445_, v_x_1446_);
stack->m_num = v_res_1452_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_a_1453_, lean_object* v_x_1454_){
_start:
{
uint8_t v_res_1455_; lean_object* v_r_1456_; 
v_res_1455_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___redArg(v_a_1453_, v_x_1454_);
lean_dec(v_x_1454_);
lean_dec_ref(v_a_1453_);
v_r_1456_ = lean_box(v_res_1455_);
return v_r_1456_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13_spec__14___redArg(lean_object* v_x_1457_, lean_object* v_x_1458_){
_start:
{
if (lean_obj_tag(v_x_1458_) == 0)
{
return v_x_1457_;
}
else
{
lean_object* v_key_1459_; lean_object* v_value_1460_; lean_object* v_tail_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1484_; 
v_key_1459_ = lean_ctor_get(v_x_1458_, 0);
v_value_1460_ = lean_ctor_get(v_x_1458_, 1);
v_tail_1461_ = lean_ctor_get(v_x_1458_, 2);
v_isSharedCheck_1484_ = !lean_is_exclusive(v_x_1458_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1463_ = v_x_1458_;
v_isShared_1464_ = v_isSharedCheck_1484_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_tail_1461_);
lean_inc(v_value_1460_);
lean_inc(v_key_1459_);
lean_dec(v_x_1458_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1484_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1465_; uint64_t v___x_1466_; uint64_t v___x_1467_; uint64_t v___x_1468_; uint64_t v_fold_1469_; uint64_t v___x_1470_; uint64_t v___x_1471_; uint64_t v___x_1472_; size_t v___x_1473_; size_t v___x_1474_; size_t v___x_1475_; size_t v___x_1476_; size_t v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1480_; 
v___x_1465_ = lean_array_get_size(v_x_1457_);
v___x_1466_ = l_Lean_Expr_hash(v_key_1459_);
v___x_1467_ = 32ULL;
v___x_1468_ = lean_uint64_shift_right(v___x_1466_, v___x_1467_);
v_fold_1469_ = lean_uint64_xor(v___x_1466_, v___x_1468_);
v___x_1470_ = 16ULL;
v___x_1471_ = lean_uint64_shift_right(v_fold_1469_, v___x_1470_);
v___x_1472_ = lean_uint64_xor(v_fold_1469_, v___x_1471_);
v___x_1473_ = lean_uint64_to_usize(v___x_1472_);
v___x_1474_ = lean_usize_of_nat(v___x_1465_);
v___x_1475_ = ((size_t)1ULL);
v___x_1476_ = lean_usize_sub(v___x_1474_, v___x_1475_);
v___x_1477_ = lean_usize_land(v___x_1473_, v___x_1476_);
v___x_1478_ = lean_array_uget_borrowed(v_x_1457_, v___x_1477_);
lean_inc(v___x_1478_);
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 2, v___x_1478_);
v___x_1480_ = v___x_1463_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_key_1459_);
lean_ctor_set(v_reuseFailAlloc_1483_, 1, v_value_1460_);
lean_ctor_set(v_reuseFailAlloc_1483_, 2, v___x_1478_);
v___x_1480_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
lean_object* v___x_1481_; 
v___x_1481_ = lean_array_uset(v_x_1457_, v___x_1477_, v___x_1480_);
v_x_1457_ = v___x_1481_;
v_x_1458_ = v_tail_1461_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13___redArg(lean_object* v_i_1485_, lean_object* v_source_1486_, lean_object* v_target_1487_){
_start:
{
lean_object* v___x_1488_; uint8_t v___x_1489_; 
v___x_1488_ = lean_array_get_size(v_source_1486_);
v___x_1489_ = lean_nat_dec_lt(v_i_1485_, v___x_1488_);
if (v___x_1489_ == 0)
{
lean_dec_ref(v_source_1486_);
lean_dec(v_i_1485_);
return v_target_1487_;
}
else
{
lean_object* v_es_1490_; lean_object* v___x_1491_; lean_object* v_source_1492_; lean_object* v_target_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v_es_1490_ = lean_array_fget(v_source_1486_, v_i_1485_);
v___x_1491_ = lean_box(0);
v_source_1492_ = lean_array_fset(v_source_1486_, v_i_1485_, v___x_1491_);
v_target_1493_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13_spec__14___redArg(v_target_1487_, v_es_1490_);
v___x_1494_ = lean_unsigned_to_nat(1u);
v___x_1495_ = lean_nat_add(v_i_1485_, v___x_1494_);
lean_dec(v_i_1485_);
v_i_1485_ = v___x_1495_;
v_source_1486_ = v_source_1492_;
v_target_1487_ = v_target_1493_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9___redArg(lean_object* v_data_1497_){
_start:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v_nbuckets_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1498_ = lean_array_get_size(v_data_1497_);
v___x_1499_ = lean_unsigned_to_nat(2u);
v_nbuckets_1500_ = lean_nat_mul(v___x_1498_, v___x_1499_);
v___x_1501_ = lean_unsigned_to_nat(0u);
v___x_1502_ = lean_box(0);
v___x_1503_ = lean_mk_array(v_nbuckets_1500_, v___x_1502_);
v___x_1504_ = lean_array_propagate_mark(v_data_1497_, v___x_1503_);
v___x_1505_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13___redArg(v___x_1501_, v_data_1497_, v___x_1504_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__10___redArg(lean_object* v_a_1506_, lean_object* v_b_1507_, lean_object* v_x_1508_){
_start:
{
if (lean_obj_tag(v_x_1508_) == 0)
{
lean_dec(v_b_1507_);
lean_dec_ref(v_a_1506_);
return v_x_1508_;
}
else
{
lean_object* v_key_1509_; lean_object* v_value_1510_; lean_object* v_tail_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1523_; 
v_key_1509_ = lean_ctor_get(v_x_1508_, 0);
v_value_1510_ = lean_ctor_get(v_x_1508_, 1);
v_tail_1511_ = lean_ctor_get(v_x_1508_, 2);
v_isSharedCheck_1523_ = !lean_is_exclusive(v_x_1508_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1513_ = v_x_1508_;
v_isShared_1514_ = v_isSharedCheck_1523_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_tail_1511_);
lean_inc(v_value_1510_);
lean_inc(v_key_1509_);
lean_dec(v_x_1508_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1523_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
uint8_t v___x_1515_; 
v___x_1515_ = lean_expr_eqv(v_key_1509_, v_a_1506_);
if (v___x_1515_ == 0)
{
lean_object* v___x_1516_; lean_object* v___x_1518_; 
v___x_1516_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__10___redArg(v_a_1506_, v_b_1507_, v_tail_1511_);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 2, v___x_1516_);
v___x_1518_ = v___x_1513_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_key_1509_);
lean_ctor_set(v_reuseFailAlloc_1519_, 1, v_value_1510_);
lean_ctor_set(v_reuseFailAlloc_1519_, 2, v___x_1516_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
else
{
lean_object* v___x_1521_; 
lean_dec(v_value_1510_);
lean_dec(v_key_1509_);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 1, v_b_1507_);
lean_ctor_set(v___x_1513_, 0, v_a_1506_);
v___x_1521_ = v___x_1513_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_a_1506_);
lean_ctor_set(v_reuseFailAlloc_1522_, 1, v_b_1507_);
lean_ctor_set(v_reuseFailAlloc_1522_, 2, v_tail_1511_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3___redArg(lean_object* v_m_1524_, lean_object* v_a_1525_, lean_object* v_b_1526_){
_start:
{
lean_object* v_size_1527_; lean_object* v_buckets_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1571_; 
v_size_1527_ = lean_ctor_get(v_m_1524_, 0);
v_buckets_1528_ = lean_ctor_get(v_m_1524_, 1);
v_isSharedCheck_1571_ = !lean_is_exclusive(v_m_1524_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1530_ = v_m_1524_;
v_isShared_1531_ = v_isSharedCheck_1571_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_buckets_1528_);
lean_inc(v_size_1527_);
lean_dec(v_m_1524_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1571_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1532_; uint64_t v___x_1533_; uint64_t v___x_1534_; uint64_t v___x_1535_; uint64_t v_fold_1536_; uint64_t v___x_1537_; uint64_t v___x_1538_; uint64_t v___x_1539_; size_t v___x_1540_; size_t v___x_1541_; size_t v___x_1542_; size_t v___x_1543_; size_t v___x_1544_; lean_object* v_bkt_1545_; uint8_t v___x_1546_; 
v___x_1532_ = lean_array_get_size(v_buckets_1528_);
v___x_1533_ = l_Lean_Expr_hash(v_a_1525_);
v___x_1534_ = 32ULL;
v___x_1535_ = lean_uint64_shift_right(v___x_1533_, v___x_1534_);
v_fold_1536_ = lean_uint64_xor(v___x_1533_, v___x_1535_);
v___x_1537_ = 16ULL;
v___x_1538_ = lean_uint64_shift_right(v_fold_1536_, v___x_1537_);
v___x_1539_ = lean_uint64_xor(v_fold_1536_, v___x_1538_);
v___x_1540_ = lean_uint64_to_usize(v___x_1539_);
v___x_1541_ = lean_usize_of_nat(v___x_1532_);
v___x_1542_ = ((size_t)1ULL);
v___x_1543_ = lean_usize_sub(v___x_1541_, v___x_1542_);
v___x_1544_ = lean_usize_land(v___x_1540_, v___x_1543_);
v_bkt_1545_ = lean_array_uget_borrowed(v_buckets_1528_, v___x_1544_);
v___x_1546_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___redArg(v_a_1525_, v_bkt_1545_);
if (v___x_1546_ == 0)
{
lean_object* v___x_1547_; lean_object* v_size_x27_1548_; lean_object* v___x_1549_; lean_object* v_buckets_x27_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; uint8_t v___x_1556_; 
v___x_1547_ = lean_unsigned_to_nat(1u);
v_size_x27_1548_ = lean_nat_add(v_size_1527_, v___x_1547_);
lean_dec(v_size_1527_);
lean_inc(v_bkt_1545_);
v___x_1549_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1549_, 0, v_a_1525_);
lean_ctor_set(v___x_1549_, 1, v_b_1526_);
lean_ctor_set(v___x_1549_, 2, v_bkt_1545_);
v_buckets_x27_1550_ = lean_array_uset(v_buckets_1528_, v___x_1544_, v___x_1549_);
v___x_1551_ = lean_unsigned_to_nat(4u);
v___x_1552_ = lean_nat_mul(v_size_x27_1548_, v___x_1551_);
v___x_1553_ = lean_unsigned_to_nat(3u);
v___x_1554_ = lean_nat_div(v___x_1552_, v___x_1553_);
lean_dec(v___x_1552_);
v___x_1555_ = lean_array_get_size(v_buckets_x27_1550_);
v___x_1556_ = lean_nat_dec_le(v___x_1554_, v___x_1555_);
lean_dec(v___x_1554_);
if (v___x_1556_ == 0)
{
lean_object* v_val_1557_; lean_object* v___x_1559_; 
v_val_1557_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9___redArg(v_buckets_x27_1550_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 1, v_val_1557_);
lean_ctor_set(v___x_1530_, 0, v_size_x27_1548_);
v___x_1559_ = v___x_1530_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_size_x27_1548_);
lean_ctor_set(v_reuseFailAlloc_1560_, 1, v_val_1557_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
else
{
lean_object* v___x_1562_; 
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 1, v_buckets_x27_1550_);
lean_ctor_set(v___x_1530_, 0, v_size_x27_1548_);
v___x_1562_ = v___x_1530_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_size_x27_1548_);
lean_ctor_set(v_reuseFailAlloc_1563_, 1, v_buckets_x27_1550_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
else
{
lean_object* v___x_1564_; lean_object* v_buckets_x27_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1569_; 
lean_inc(v_bkt_1545_);
v___x_1564_ = lean_box(0);
v_buckets_x27_1565_ = lean_array_uset(v_buckets_1528_, v___x_1544_, v___x_1564_);
v___x_1566_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__10___redArg(v_a_1525_, v_b_1526_, v_bkt_1545_);
v___x_1567_ = lean_array_uset(v_buckets_x27_1565_, v___x_1544_, v___x_1566_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 1, v___x_1567_);
v___x_1569_ = v___x_1530_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_size_1527_);
lean_ctor_set(v_reuseFailAlloc_1570_, 1, v___x_1567_);
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
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___redArg(lean_object* v_a_1572_, lean_object* v_x_1573_){
_start:
{
if (lean_obj_tag(v_x_1573_) == 0)
{
lean_object* v___x_1574_; 
v___x_1574_ = lean_box(0);
return v___x_1574_;
}
else
{
lean_object* v_key_1575_; lean_object* v_value_1576_; lean_object* v_tail_1577_; uint8_t v___x_1578_; 
v_key_1575_ = lean_ctor_get(v_x_1573_, 0);
v_value_1576_ = lean_ctor_get(v_x_1573_, 1);
v_tail_1577_ = lean_ctor_get(v_x_1573_, 2);
v___x_1578_ = lean_expr_eqv(v_key_1575_, v_a_1572_);
if (v___x_1578_ == 0)
{
v_x_1573_ = v_tail_1577_;
goto _start;
}
else
{
lean_object* v___x_1580_; 
lean_inc(v_value_1576_);
v___x_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1580_, 0, v_value_1576_);
return v___x_1580_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_a_1581_, lean_object* v_x_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___redArg(v_a_1581_, v_x_1582_);
lean_dec(v_x_1582_);
lean_dec_ref(v_a_1581_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___redArg(lean_object* v_m_1584_, lean_object* v_a_1585_){
_start:
{
lean_object* v_buckets_1586_; lean_object* v___x_1587_; uint64_t v___x_1588_; uint64_t v___x_1589_; uint64_t v___x_1590_; uint64_t v_fold_1591_; uint64_t v___x_1592_; uint64_t v___x_1593_; uint64_t v___x_1594_; size_t v___x_1595_; size_t v___x_1596_; size_t v___x_1597_; size_t v___x_1598_; size_t v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v_buckets_1586_ = lean_ctor_get(v_m_1584_, 1);
v___x_1587_ = lean_array_get_size(v_buckets_1586_);
v___x_1588_ = l_Lean_Expr_hash(v_a_1585_);
v___x_1589_ = 32ULL;
v___x_1590_ = lean_uint64_shift_right(v___x_1588_, v___x_1589_);
v_fold_1591_ = lean_uint64_xor(v___x_1588_, v___x_1590_);
v___x_1592_ = 16ULL;
v___x_1593_ = lean_uint64_shift_right(v_fold_1591_, v___x_1592_);
v___x_1594_ = lean_uint64_xor(v_fold_1591_, v___x_1593_);
v___x_1595_ = lean_uint64_to_usize(v___x_1594_);
v___x_1596_ = lean_usize_of_nat(v___x_1587_);
v___x_1597_ = ((size_t)1ULL);
v___x_1598_ = lean_usize_sub(v___x_1596_, v___x_1597_);
v___x_1599_ = lean_usize_land(v___x_1595_, v___x_1598_);
v___x_1600_ = lean_array_uget_borrowed(v_buckets_1586_, v___x_1599_);
v___x_1601_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___redArg(v_a_1585_, v___x_1600_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___redArg___boxed(lean_object* v_m_1602_, lean_object* v_a_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___redArg(v_m_1602_, v_a_1603_);
lean_dec_ref(v_a_1603_);
lean_dec_ref(v_m_1602_);
return v_res_1604_;
}
}
lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(lean_object* v_g_1605_, lean_object* v_e_1606_, lean_object* v_a_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v_a_1615_; lean_object* v___y_1621_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1623_ = lean_st_ref_get(v_a_1607_);
v___x_1624_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___redArg(v___x_1623_, v_e_1606_);
lean_dec(v___x_1623_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v___x_1625_; 
lean_inc_ref(v_g_1605_);
lean_inc(v___y_1612_);
lean_inc_ref(v___y_1611_);
lean_inc(v___y_1610_);
lean_inc_ref(v___y_1609_);
lean_inc(v___y_1608_);
lean_inc_ref(v_e_1606_);
v___x_1625_ = lean_apply_7(v_g_1605_, v_e_1606_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, lean_box(0));
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; lean_object* v_d_1628_; lean_object* v_b_1629_; lean_object* v___y_1630_; uint8_t v___x_1633_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_a_1626_);
lean_dec_ref_known(v___x_1625_, 1);
v___x_1633_ = lean_unbox(v_a_1626_);
lean_dec(v_a_1626_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1634_; 
lean_dec_ref(v_g_1605_);
v___x_1634_ = lean_box(0);
v_a_1615_ = v___x_1634_;
goto v___jp_1614_;
}
else
{
switch(lean_obj_tag(v_e_1606_))
{
case 7:
{
lean_object* v_binderType_1635_; lean_object* v_body_1636_; 
v_binderType_1635_ = lean_ctor_get(v_e_1606_, 1);
v_body_1636_ = lean_ctor_get(v_e_1606_, 2);
lean_inc_ref(v_body_1636_);
lean_inc_ref(v_binderType_1635_);
v_d_1628_ = v_binderType_1635_;
v_b_1629_ = v_body_1636_;
v___y_1630_ = v_a_1607_;
goto v___jp_1627_;
}
case 6:
{
lean_object* v_binderType_1637_; lean_object* v_body_1638_; 
v_binderType_1637_ = lean_ctor_get(v_e_1606_, 1);
v_body_1638_ = lean_ctor_get(v_e_1606_, 2);
lean_inc_ref(v_body_1638_);
lean_inc_ref(v_binderType_1637_);
v_d_1628_ = v_binderType_1637_;
v_b_1629_ = v_body_1638_;
v___y_1630_ = v_a_1607_;
goto v___jp_1627_;
}
case 8:
{
lean_object* v_type_1639_; lean_object* v_value_1640_; lean_object* v_body_1641_; lean_object* v___x_1642_; 
v_type_1639_ = lean_ctor_get(v_e_1606_, 1);
v_value_1640_ = lean_ctor_get(v_e_1606_, 2);
v_body_1641_ = lean_ctor_get(v_e_1606_, 3);
lean_inc_ref(v_type_1639_);
lean_inc_ref(v_g_1605_);
v___x_1642_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1605_, v_type_1639_, v_a_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v___x_1643_; 
lean_dec_ref_known(v___x_1642_, 1);
lean_inc_ref(v_value_1640_);
lean_inc_ref(v_g_1605_);
v___x_1643_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1605_, v_value_1640_, v_a_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v___x_1644_; 
lean_dec_ref_known(v___x_1643_, 1);
lean_inc_ref(v_body_1641_);
v___x_1644_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1605_, v_body_1641_, v_a_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
v___y_1621_ = v___x_1644_;
goto v___jp_1620_;
}
else
{
lean_dec_ref(v_g_1605_);
v___y_1621_ = v___x_1643_;
goto v___jp_1620_;
}
}
else
{
lean_dec_ref(v_g_1605_);
v___y_1621_ = v___x_1642_;
goto v___jp_1620_;
}
}
case 5:
{
lean_object* v_fn_1645_; lean_object* v_arg_1646_; lean_object* v___x_1647_; 
v_fn_1645_ = lean_ctor_get(v_e_1606_, 0);
v_arg_1646_ = lean_ctor_get(v_e_1606_, 1);
lean_inc_ref(v_fn_1645_);
lean_inc_ref(v_g_1605_);
v___x_1647_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1605_, v_fn_1645_, v_a_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v___x_1648_; 
lean_dec_ref_known(v___x_1647_, 1);
lean_inc_ref(v_arg_1646_);
v___x_1648_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1605_, v_arg_1646_, v_a_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
v___y_1621_ = v___x_1648_;
goto v___jp_1620_;
}
else
{
lean_dec_ref(v_g_1605_);
v___y_1621_ = v___x_1647_;
goto v___jp_1620_;
}
}
case 10:
{
lean_object* v_expr_1649_; lean_object* v___x_1650_; 
v_expr_1649_ = lean_ctor_get(v_e_1606_, 1);
lean_inc_ref(v_expr_1649_);
v___x_1650_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1605_, v_expr_1649_, v_a_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
v___y_1621_ = v___x_1650_;
goto v___jp_1620_;
}
case 11:
{
lean_object* v_struct_1651_; lean_object* v___x_1652_; 
v_struct_1651_ = lean_ctor_get(v_e_1606_, 2);
lean_inc_ref(v_struct_1651_);
v___x_1652_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1605_, v_struct_1651_, v_a_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
v___y_1621_ = v___x_1652_;
goto v___jp_1620_;
}
default: 
{
lean_object* v___x_1653_; 
lean_dec_ref(v_g_1605_);
v___x_1653_ = lean_box(0);
v_a_1615_ = v___x_1653_;
goto v___jp_1614_;
}
}
}
v___jp_1627_:
{
lean_object* v___x_1631_; 
lean_inc_ref(v_g_1605_);
v___x_1631_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1605_, v_d_1628_, v___y_1630_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v___x_1632_; 
lean_dec_ref_known(v___x_1631_, 1);
v___x_1632_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1605_, v_b_1629_, v___y_1630_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
v___y_1621_ = v___x_1632_;
goto v___jp_1620_;
}
else
{
lean_dec_ref(v_b_1629_);
lean_dec_ref(v_g_1605_);
v___y_1621_ = v___x_1631_;
goto v___jp_1620_;
}
}
}
else
{
lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1661_; 
lean_dec_ref(v_e_1606_);
lean_dec_ref(v_g_1605_);
v_a_1654_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1656_ = v___x_1625_;
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v___x_1625_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1659_; 
if (v_isShared_1657_ == 0)
{
v___x_1659_ = v___x_1656_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_a_1654_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
else
{
lean_object* v_val_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
lean_dec_ref(v_e_1606_);
lean_dec_ref(v_g_1605_);
v_val_1662_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1624_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_val_1662_);
lean_dec(v___x_1624_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
lean_ctor_set_tag(v___x_1664_, 0);
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_val_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
v___jp_1614_:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1616_ = lean_st_ref_take(v_a_1607_);
v___x_1617_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3___redArg(v___x_1616_, v_e_1606_, v_a_1615_);
v___x_1618_ = lean_st_ref_put(v_a_1607_, v___x_1617_);
v___x_1619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1619_, 0, v_a_1615_);
return v___x_1619_;
}
v___jp_1620_:
{
if (lean_obj_tag(v___y_1621_) == 0)
{
lean_object* v_a_1622_; 
v_a_1622_ = lean_ctor_get(v___y_1621_, 0);
lean_inc(v_a_1622_);
lean_dec_ref_known(v___y_1621_, 1);
v_a_1615_ = v_a_1622_;
goto v___jp_1614_;
}
else
{
lean_dec_ref(v_e_1606_);
return v___y_1621_;
}
}
}
}
LEAN_EXPORT void l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_g_1605_ = stack[0].m_obj;
lean_object* v_e_1606_ = stack[1].m_obj;
lean_object* v_a_1607_ = stack[2].m_obj;
lean_object* v___y_1608_ = stack[3].m_obj;
lean_object* v___y_1609_ = stack[4].m_obj;
lean_object* v___y_1610_ = stack[5].m_obj;
lean_object* v___y_1611_ = stack[6].m_obj;
lean_object* v___y_1612_ = stack[7].m_obj;
lean_object* v_res_1670_;
v_res_1670_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1605_, v_e_1606_, v_a_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
stack->m_obj
 = v_res_1670_;
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1___boxed(lean_object* v_g_1671_, lean_object* v_e_1672_, lean_object* v_a_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_1671_, v_e_1672_, v_a_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec(v_a_1673_);
return v_res_1680_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__1(void){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1682_ = lean_box(0);
v___x_1683_ = lean_unsigned_to_nat(16u);
v___x_1684_ = lean_mk_array(v___x_1683_, v___x_1682_);
return v___x_1684_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__2(void){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1685_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__1, &l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__1_once, _init_l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__1);
v___x_1686_ = lean_unsigned_to_nat(0u);
v___x_1687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1686_);
lean_ctor_set(v___x_1687_, 1, v___x_1685_);
return v___x_1687_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar(lean_object* v_e_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v___f_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___f_1695_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__0));
v___x_1696_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__2, &l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__2_once, _init_l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__2);
v___x_1697_ = lean_st_mk_ref(v___x_1696_);
v___x_1698_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v___f_1695_, v_e_1688_, v___x_1697_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1707_; 
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1701_ = v___x_1698_;
v_isShared_1702_ = v_isSharedCheck_1707_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1698_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1707_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1703_; lean_object* v___x_1705_; 
v___x_1703_ = lean_st_ref_get(v___x_1697_);
lean_dec(v___x_1697_);
lean_dec(v___x_1703_);
if (v_isShared_1702_ == 0)
{
v___x_1705_ = v___x_1701_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_a_1699_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
else
{
lean_dec(v___x_1697_);
return v___x_1698_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1688_ = stack[0].m_obj;
lean_object* v_a_1689_ = stack[1].m_obj;
lean_object* v_a_1690_ = stack[2].m_obj;
lean_object* v_a_1691_ = stack[3].m_obj;
lean_object* v_a_1692_ = stack[4].m_obj;
lean_object* v_a_1693_ = stack[5].m_obj;
lean_object* v_res_1708_;
v_res_1708_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar(v_e_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
stack->m_obj
 = v_res_1708_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___boxed(lean_object* v_e_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar(v_e_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_);
lean_dec(v_a_1714_);
lean_dec_ref(v_a_1713_);
lean_dec(v_a_1712_);
lean_dec_ref(v_a_1711_);
lean_dec(v_a_1710_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2(lean_object* v_00_u03b2_1717_, lean_object* v_m_1718_, lean_object* v_a_1719_){
_start:
{
lean_object* v___x_1720_; 
v___x_1720_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___redArg(v_m_1718_, v_a_1719_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1721_, lean_object* v_m_1722_, lean_object* v_a_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2(v_00_u03b2_1721_, v_m_1722_, v_a_1723_);
lean_dec_ref(v_a_1723_);
lean_dec_ref(v_m_1722_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3(lean_object* v_00_u03b2_1725_, lean_object* v_m_1726_, lean_object* v_a_1727_, lean_object* v_b_1728_){
_start:
{
lean_object* v___x_1729_; 
v___x_1729_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3___redArg(v_m_1726_, v_a_1727_, v_b_1728_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_1730_, lean_object* v_a_1731_, lean_object* v_x_1732_){
_start:
{
lean_object* v___x_1733_; 
v___x_1733_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___redArg(v_a_1731_, v_x_1732_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1734_, lean_object* v_a_1735_, lean_object* v_x_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6(v_00_u03b2_1734_, v_a_1735_, v_x_1736_);
lean_dec(v_x_1736_);
lean_dec_ref(v_a_1735_);
return v_res_1737_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_1738_, lean_object* v_a_1739_, lean_object* v_x_1740_){
_start:
{
uint8_t v___x_1741_; 
v___x_1741_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___redArg(v_a_1739_, v_x_1740_);
return v___x_1741_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1739_ = stack[1].m_obj;
lean_object* v_x_1740_ = stack[2].m_obj;
uint8_t v_res_1742_;
v_res_1742_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8(lean_box(0), v_a_1739_, v_x_1740_);
stack->m_num = v_res_1742_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___boxed(lean_object* v_00_u03b2_1743_, lean_object* v_a_1744_, lean_object* v_x_1745_){
_start:
{
uint8_t v_res_1746_; lean_object* v_r_1747_; 
v_res_1746_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8(v_00_u03b2_1743_, v_a_1744_, v_x_1745_);
lean_dec(v_x_1745_);
lean_dec_ref(v_a_1744_);
v_r_1747_ = lean_box(v_res_1746_);
return v_r_1747_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9(lean_object* v_00_u03b2_1748_, lean_object* v_data_1749_){
_start:
{
lean_object* v___x_1750_; 
v___x_1750_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9___redArg(v_data_1749_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__10(lean_object* v_00_u03b2_1751_, lean_object* v_a_1752_, lean_object* v_b_1753_, lean_object* v_x_1754_){
_start:
{
lean_object* v___x_1755_; 
v___x_1755_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__10___redArg(v_a_1752_, v_b_1753_, v_x_1754_);
return v___x_1755_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6(lean_object* v_as_1756_, size_t v_i_1757_, size_t v_stop_1758_, lean_object* v_b_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___redArg(v_as_1756_, v_i_1757_, v_stop_1758_, v_b_1759_, v___y_1760_, v___y_1761_, v___y_1763_, v___y_1764_);
return v___x_1766_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1756_ = stack[0].m_obj;
size_t v_i_1757_ = stack[1].m_num;
size_t v_stop_1758_ = stack[2].m_num;
lean_object* v_b_1759_ = stack[3].m_obj;
lean_object* v___y_1760_ = stack[4].m_obj;
lean_object* v___y_1761_ = stack[5].m_obj;
lean_object* v___y_1762_ = stack[6].m_obj;
lean_object* v___y_1763_ = stack[7].m_obj;
lean_object* v___y_1764_ = stack[8].m_obj;
lean_object* v_res_1767_;
v_res_1767_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6(v_as_1756_, v_i_1757_, v_stop_1758_, v_b_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
stack->m_obj
 = v_res_1767_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* v_as_1768_, lean_object* v_i_1769_, lean_object* v_stop_1770_, lean_object* v_b_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
size_t v_i_boxed_1778_; size_t v_stop_boxed_1779_; lean_object* v_res_1780_; 
v_i_boxed_1778_ = lean_unbox_usize(v_i_1769_);
lean_dec(v_i_1769_);
v_stop_boxed_1779_ = lean_unbox_usize(v_stop_1770_);
lean_dec(v_stop_1770_);
v_res_1780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6(v_as_1768_, v_i_boxed_1778_, v_stop_boxed_1779_, v_b_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
lean_dec(v___y_1772_);
lean_dec_ref(v_as_1768_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13(lean_object* v_00_u03b2_1781_, lean_object* v_i_1782_, lean_object* v_source_1783_, lean_object* v_target_1784_){
_start:
{
lean_object* v___x_1785_; 
v___x_1785_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13___redArg(v_i_1782_, v_source_1783_, v_target_1784_);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13_spec__14(lean_object* v_00_u03b2_1786_, lean_object* v_x_1787_, lean_object* v_x_1788_){
_start:
{
lean_object* v___x_1789_; 
v___x_1789_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13_spec__14___redArg(v_x_1787_, v_x_1788_);
return v___x_1789_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___redArg(lean_object* v_e_1790_, lean_object* v___y_1791_){
_start:
{
uint8_t v___x_1793_; 
v___x_1793_ = l_Lean_Expr_hasMVar(v_e_1790_);
if (v___x_1793_ == 0)
{
lean_object* v___x_1794_; 
v___x_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1794_, 0, v_e_1790_);
return v___x_1794_;
}
else
{
lean_object* v___x_1795_; lean_object* v_mctx_1796_; lean_object* v___x_1797_; lean_object* v_fst_1798_; lean_object* v_snd_1799_; lean_object* v___x_1800_; lean_object* v_cache_1801_; lean_object* v_zetaDeltaFVarIds_1802_; lean_object* v_postponed_1803_; lean_object* v_diag_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1813_; 
v___x_1795_ = lean_st_ref_get(v___y_1791_);
v_mctx_1796_ = lean_ctor_get(v___x_1795_, 0);
lean_inc_ref(v_mctx_1796_);
lean_dec(v___x_1795_);
v___x_1797_ = l_Lean_instantiateMVarsCore(v_mctx_1796_, v_e_1790_);
v_fst_1798_ = lean_ctor_get(v___x_1797_, 0);
lean_inc(v_fst_1798_);
v_snd_1799_ = lean_ctor_get(v___x_1797_, 1);
lean_inc(v_snd_1799_);
lean_dec_ref(v___x_1797_);
v___x_1800_ = lean_st_ref_take(v___y_1791_);
v_cache_1801_ = lean_ctor_get(v___x_1800_, 1);
v_zetaDeltaFVarIds_1802_ = lean_ctor_get(v___x_1800_, 2);
v_postponed_1803_ = lean_ctor_get(v___x_1800_, 3);
v_diag_1804_ = lean_ctor_get(v___x_1800_, 4);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1813_ == 0)
{
lean_object* v_unused_1814_; 
v_unused_1814_ = lean_ctor_get(v___x_1800_, 0);
lean_dec(v_unused_1814_);
v___x_1806_ = v___x_1800_;
v_isShared_1807_ = v_isSharedCheck_1813_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_diag_1804_);
lean_inc(v_postponed_1803_);
lean_inc(v_zetaDeltaFVarIds_1802_);
lean_inc(v_cache_1801_);
lean_dec(v___x_1800_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1813_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1809_; 
if (v_isShared_1807_ == 0)
{
lean_ctor_set(v___x_1806_, 0, v_snd_1799_);
v___x_1809_ = v___x_1806_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_snd_1799_);
lean_ctor_set(v_reuseFailAlloc_1812_, 1, v_cache_1801_);
lean_ctor_set(v_reuseFailAlloc_1812_, 2, v_zetaDeltaFVarIds_1802_);
lean_ctor_set(v_reuseFailAlloc_1812_, 3, v_postponed_1803_);
lean_ctor_set(v_reuseFailAlloc_1812_, 4, v_diag_1804_);
v___x_1809_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = lean_st_ref_put(v___y_1791_, v___x_1809_);
v___x_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1811_, 0, v_fst_1798_);
return v___x_1811_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1790_ = stack[0].m_obj;
lean_object* v___y_1791_ = stack[1].m_obj;
lean_object* v_res_1815_;
v_res_1815_ = l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___redArg(v_e_1790_, v___y_1791_);
stack->m_obj
 = v_res_1815_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___redArg___boxed(lean_object* v_e_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___redArg(v_e_1816_, v___y_1817_);
lean_dec(v___y_1817_);
return v_res_1819_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0(lean_object* v_e_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v___x_1826_; 
v___x_1826_ = l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___redArg(v_e_1820_, v___y_1822_);
return v___x_1826_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1820_ = stack[0].m_obj;
lean_object* v___y_1821_ = stack[1].m_obj;
lean_object* v___y_1822_ = stack[2].m_obj;
lean_object* v___y_1823_ = stack[3].m_obj;
lean_object* v___y_1824_ = stack[4].m_obj;
lean_object* v_res_1827_;
v_res_1827_ = l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0(v_e_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
stack->m_obj
 = v_res_1827_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___boxed(lean_object* v_e_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0(v_e_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
return v_res_1834_;
}
}
lean_object* l_Lean_MVarId_assertAfter_x27___lam__0(lean_object* v_type_1835_, lean_object* v_fvarId_1836_, lean_object* v_mvarId_1837_, lean_object* v_userName_1838_, lean_object* v_val_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v___x_1845_; lean_object* v_a_1846_; lean_object* v___x_1847_; 
v___x_1845_ = l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___redArg(v_type_1835_, v___y_1841_);
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
lean_inc(v_a_1846_);
lean_dec_ref(v___x_1845_);
v___x_1847_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1836_, v___y_1840_, v___y_1842_, v___y_1843_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
lean_inc(v_a_1848_);
lean_dec_ref_known(v___x_1847_, 1);
v___x_1849_ = lean_st_mk_ref(v_a_1848_);
lean_inc(v_a_1846_);
v___x_1850_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar(v_a_1846_, v___x_1849_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
lean_dec_ref_known(v___x_1850_, 1);
v___x_1851_ = lean_st_ref_get(v___x_1849_);
lean_dec(v___x_1849_);
v___x_1852_ = l_Lean_LocalDecl_fvarId(v___x_1851_);
lean_dec(v___x_1851_);
v___x_1853_ = l_Lean_MVarId_assertAfter(v_mvarId_1837_, v___x_1852_, v_userName_1838_, v_a_1846_, v_val_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
return v___x_1853_;
}
else
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
lean_dec(v___x_1849_);
lean_dec(v_a_1846_);
lean_dec_ref(v_val_1839_);
lean_dec(v_userName_1838_);
lean_dec(v_mvarId_1837_);
v_a_1854_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1856_ = v___x_1850_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1850_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_a_1854_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
}
else
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
lean_dec(v_a_1846_);
lean_dec_ref(v_val_1839_);
lean_dec(v_userName_1838_);
lean_dec(v_mvarId_1837_);
v_a_1862_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1847_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1847_);
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
}
LEAN_EXPORT void l_Lean_MVarId_assertAfter_x27___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1835_ = stack[0].m_obj;
lean_object* v_fvarId_1836_ = stack[1].m_obj;
lean_object* v_mvarId_1837_ = stack[2].m_obj;
lean_object* v_userName_1838_ = stack[3].m_obj;
lean_object* v_val_1839_ = stack[4].m_obj;
lean_object* v___y_1840_ = stack[5].m_obj;
lean_object* v___y_1841_ = stack[6].m_obj;
lean_object* v___y_1842_ = stack[7].m_obj;
lean_object* v___y_1843_ = stack[8].m_obj;
lean_object* v_res_1870_;
v_res_1870_ = l_Lean_MVarId_assertAfter_x27___lam__0(v_type_1835_, v_fvarId_1836_, v_mvarId_1837_, v_userName_1838_, v_val_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
stack->m_obj
 = v_res_1870_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertAfter_x27___lam__0___boxed(lean_object* v_type_1871_, lean_object* v_fvarId_1872_, lean_object* v_mvarId_1873_, lean_object* v_userName_1874_, lean_object* v_val_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_Lean_MVarId_assertAfter_x27___lam__0(v_type_1871_, v_fvarId_1872_, v_mvarId_1873_, v_userName_1874_, v_val_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
return v_res_1881_;
}
}
lean_object* l_Lean_MVarId_assertAfter_x27(lean_object* v_mvarId_1882_, lean_object* v_fvarId_1883_, lean_object* v_userName_1884_, lean_object* v_type_1885_, lean_object* v_val_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_){
_start:
{
lean_object* v___f_1892_; lean_object* v___x_1893_; 
lean_inc(v_mvarId_1882_);
v___f_1892_ = lean_alloc_closure((void*)(l_Lean_MVarId_assertAfter_x27___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1892_, 0, v_type_1885_);
lean_closure_set(v___f_1892_, 1, v_fvarId_1883_);
lean_closure_set(v___f_1892_, 2, v_mvarId_1882_);
lean_closure_set(v___f_1892_, 3, v_userName_1884_);
lean_closure_set(v___f_1892_, 4, v_val_1886_);
v___x_1893_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(v_mvarId_1882_, v___f_1892_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
return v___x_1893_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assertAfter_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1882_ = stack[0].m_obj;
lean_object* v_fvarId_1883_ = stack[1].m_obj;
lean_object* v_userName_1884_ = stack[2].m_obj;
lean_object* v_type_1885_ = stack[3].m_obj;
lean_object* v_val_1886_ = stack[4].m_obj;
lean_object* v_a_1887_ = stack[5].m_obj;
lean_object* v_a_1888_ = stack[6].m_obj;
lean_object* v_a_1889_ = stack[7].m_obj;
lean_object* v_a_1890_ = stack[8].m_obj;
lean_object* v_res_1894_;
v_res_1894_ = l_Lean_MVarId_assertAfter_x27(v_mvarId_1882_, v_fvarId_1883_, v_userName_1884_, v_type_1885_, v_val_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
stack->m_obj
 = v_res_1894_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertAfter_x27___boxed(lean_object* v_mvarId_1895_, lean_object* v_fvarId_1896_, lean_object* v_userName_1897_, lean_object* v_type_1898_, lean_object* v_val_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Lean_MVarId_assertAfter_x27(v_mvarId_1895_, v_fvarId_1896_, v_userName_1897_, v_type_1898_, v_val_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
lean_dec(v_a_1903_);
lean_dec_ref(v_a_1902_);
lean_dec(v_a_1901_);
lean_dec_ref(v_a_1900_);
return v_res_1905_;
}
}
lean_object* l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg(lean_object* v_mvarId_1906_, lean_object* v_f_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v___x_1910_; lean_object* v_mctx_1911_; lean_object* v_cache_1912_; lean_object* v_zetaDeltaFVarIds_1913_; lean_object* v_postponed_1914_; lean_object* v_diag_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1926_; 
v___x_1910_ = lean_st_ref_take(v___y_1908_);
v_mctx_1911_ = lean_ctor_get(v___x_1910_, 0);
v_cache_1912_ = lean_ctor_get(v___x_1910_, 1);
v_zetaDeltaFVarIds_1913_ = lean_ctor_get(v___x_1910_, 2);
v_postponed_1914_ = lean_ctor_get(v___x_1910_, 3);
v_diag_1915_ = lean_ctor_get(v___x_1910_, 4);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1917_ = v___x_1910_;
v_isShared_1918_ = v_isSharedCheck_1926_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_diag_1915_);
lean_inc(v_postponed_1914_);
lean_inc(v_zetaDeltaFVarIds_1913_);
lean_inc(v_cache_1912_);
lean_inc(v_mctx_1911_);
lean_dec(v___x_1910_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1926_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1922_; 
v___x_1919_ = lean_box(0);
v___x_1920_ = l_Lean_MetavarContext_modifyExprMVarLCtx(v_mctx_1911_, v_mvarId_1906_, v_f_1907_);
if (v_isShared_1918_ == 0)
{
lean_ctor_set(v___x_1917_, 0, v___x_1920_);
v___x_1922_ = v___x_1917_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v___x_1920_);
lean_ctor_set(v_reuseFailAlloc_1925_, 1, v_cache_1912_);
lean_ctor_set(v_reuseFailAlloc_1925_, 2, v_zetaDeltaFVarIds_1913_);
lean_ctor_set(v_reuseFailAlloc_1925_, 3, v_postponed_1914_);
lean_ctor_set(v_reuseFailAlloc_1925_, 4, v_diag_1915_);
v___x_1922_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1923_ = lean_st_ref_put(v___y_1908_, v___x_1922_);
v___x_1924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1919_);
return v___x_1924_;
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1906_ = stack[0].m_obj;
lean_object* v_f_1907_ = stack[1].m_obj;
lean_object* v___y_1908_ = stack[2].m_obj;
lean_object* v_res_1927_;
v_res_1927_ = l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg(v_mvarId_1906_, v_f_1907_, v___y_1908_);
stack->m_obj
 = v_res_1927_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg___boxed(lean_object* v_mvarId_1928_, lean_object* v_f_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg(v_mvarId_1928_, v_f_1929_, v___y_1930_);
lean_dec(v___y_1930_);
return v_res_1932_;
}
}
lean_object* l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1(lean_object* v_mvarId_1933_, lean_object* v_f_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v___x_1940_; 
v___x_1940_ = l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg(v_mvarId_1933_, v_f_1934_, v___y_1936_);
return v___x_1940_;
}
}
LEAN_EXPORT void l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1933_ = stack[0].m_obj;
lean_object* v_f_1934_ = stack[1].m_obj;
lean_object* v___y_1935_ = stack[2].m_obj;
lean_object* v___y_1936_ = stack[3].m_obj;
lean_object* v___y_1937_ = stack[4].m_obj;
lean_object* v___y_1938_ = stack[5].m_obj;
lean_object* v_res_1941_;
v_res_1941_ = l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1(v_mvarId_1933_, v_f_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
stack->m_obj
 = v_res_1941_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___boxed(lean_object* v_mvarId_1942_, lean_object* v_f_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1(v_mvarId_1942_, v_f_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg(lean_object* v_upperBound_1950_, lean_object* v_hs_1951_, lean_object* v_fst_1952_, lean_object* v_a_1953_, lean_object* v_b_1954_){
_start:
{
lean_object* v_a_1956_; uint8_t v___x_1960_; 
v___x_1960_ = lean_nat_dec_lt(v_a_1953_, v_upperBound_1950_);
if (v___x_1960_ == 0)
{
lean_dec(v_a_1953_);
return v_b_1954_;
}
else
{
lean_object* v___x_1961_; uint8_t v_kind_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; uint8_t v___x_1966_; 
v___x_1961_ = lean_array_fget_borrowed(v_hs_1951_, v_a_1953_);
v_kind_1962_ = lean_ctor_get_uint8(v___x_1961_, sizeof(void*)*3 + 1);
v___x_1963_ = lean_box(v_kind_1962_);
v___x_1964_ = lean_obj_tag_nat(v___x_1963_);
lean_dec(v___x_1963_);
v___x_1965_ = lean_unsigned_to_nat(0u);
v___x_1966_ = lean_nat_dec_eq(v___x_1964_, v___x_1965_);
if (v___x_1966_ == 0)
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1967_ = lean_box(0);
v___x_1968_ = lean_array_get_borrowed(v___x_1967_, v_fst_1952_, v_a_1953_);
lean_inc(v___x_1968_);
v___x_1969_ = l_Lean_LocalContext_setKind(v_b_1954_, v___x_1968_, v_kind_1962_);
v_a_1956_ = v___x_1969_;
goto v___jp_1955_;
}
else
{
v_a_1956_ = v_b_1954_;
goto v___jp_1955_;
}
}
v___jp_1955_:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1957_ = lean_unsigned_to_nat(1u);
v___x_1958_ = lean_nat_add(v_a_1953_, v___x_1957_);
lean_dec(v_a_1953_);
v_a_1953_ = v___x_1958_;
v_b_1954_ = v_a_1956_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg___boxed(lean_object* v_upperBound_1970_, lean_object* v_hs_1971_, lean_object* v_fst_1972_, lean_object* v_a_1973_, lean_object* v_b_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg(v_upperBound_1970_, v_hs_1971_, v_fst_1972_, v_a_1973_, v_b_1974_);
lean_dec_ref(v_fst_1972_);
lean_dec_ref(v_hs_1971_);
lean_dec(v_upperBound_1970_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___lam__0(lean_object* v___x_1976_, lean_object* v_hs_1977_, lean_object* v_fst_1978_, lean_object* v___x_1979_, lean_object* v_lctx_1980_){
_start:
{
lean_object* v___x_1981_; 
v___x_1981_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg(v___x_1976_, v_hs_1977_, v_fst_1978_, v___x_1979_, v_lctx_1980_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___lam__0___boxed(lean_object* v___x_1982_, lean_object* v_hs_1983_, lean_object* v_fst_1984_, lean_object* v___x_1985_, lean_object* v_lctx_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l_Lean_MVarId_assertHypotheses___lam__0(v___x_1982_, v_hs_1983_, v_fst_1984_, v___x_1985_, v_lctx_1986_);
lean_dec_ref(v_fst_1984_);
lean_dec_ref(v_hs_1983_);
lean_dec(v___x_1982_);
return v_res_1987_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__3(lean_object* v_as_1988_, size_t v_i_1989_, size_t v_stop_1990_, lean_object* v_b_1991_){
_start:
{
uint8_t v___x_1992_; 
v___x_1992_ = lean_usize_dec_eq(v_i_1989_, v_stop_1990_);
if (v___x_1992_ == 0)
{
size_t v___x_1993_; size_t v___x_1994_; lean_object* v___x_1995_; lean_object* v_userName_1996_; lean_object* v_type_1997_; uint8_t v_binderInfo_1998_; lean_object* v___x_1999_; 
v___x_1993_ = ((size_t)1ULL);
v___x_1994_ = lean_usize_sub(v_i_1989_, v___x_1993_);
v___x_1995_ = lean_array_uget_borrowed(v_as_1988_, v___x_1994_);
v_userName_1996_ = lean_ctor_get(v___x_1995_, 0);
v_type_1997_ = lean_ctor_get(v___x_1995_, 1);
v_binderInfo_1998_ = lean_ctor_get_uint8(v___x_1995_, sizeof(void*)*3);
lean_inc_ref(v_type_1997_);
lean_inc(v_userName_1996_);
v___x_1999_ = l_Lean_Expr_forallE___override(v_userName_1996_, v_type_1997_, v_b_1991_, v_binderInfo_1998_);
v_i_1989_ = v___x_1994_;
v_b_1991_ = v___x_1999_;
goto _start;
}
else
{
return v_b_1991_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1988_ = stack[0].m_obj;
size_t v_i_1989_ = stack[1].m_num;
size_t v_stop_1990_ = stack[2].m_num;
lean_object* v_b_1991_ = stack[3].m_obj;
lean_object* v_res_2001_;
v_res_2001_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__3(v_as_1988_, v_i_1989_, v_stop_1990_, v_b_1991_);
stack->m_obj
 = v_res_2001_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__3___boxed(lean_object* v_as_2002_, lean_object* v_i_2003_, lean_object* v_stop_2004_, lean_object* v_b_2005_){
_start:
{
size_t v_i_boxed_2006_; size_t v_stop_boxed_2007_; lean_object* v_res_2008_; 
v_i_boxed_2006_ = lean_unbox_usize(v_i_2003_);
lean_dec(v_i_2003_);
v_stop_boxed_2007_ = lean_unbox_usize(v_stop_2004_);
lean_dec(v_stop_2004_);
v_res_2008_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__3(v_as_2002_, v_i_boxed_2006_, v_stop_boxed_2007_, v_b_2005_);
lean_dec_ref(v_as_2002_);
return v_res_2008_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2(lean_object* v_as_2009_, size_t v_i_2010_, size_t v_stop_2011_, lean_object* v_b_2012_){
_start:
{
uint8_t v___x_2013_; 
v___x_2013_ = lean_usize_dec_eq(v_i_2010_, v_stop_2011_);
if (v___x_2013_ == 0)
{
lean_object* v___x_2014_; lean_object* v_value_2015_; lean_object* v___x_2016_; size_t v___x_2017_; size_t v___x_2018_; 
v___x_2014_ = lean_array_uget_borrowed(v_as_2009_, v_i_2010_);
v_value_2015_ = lean_ctor_get(v___x_2014_, 2);
lean_inc_ref(v_value_2015_);
v___x_2016_ = l_Lean_Expr_app___override(v_b_2012_, v_value_2015_);
v___x_2017_ = ((size_t)1ULL);
v___x_2018_ = lean_usize_add(v_i_2010_, v___x_2017_);
v_i_2010_ = v___x_2018_;
v_b_2012_ = v___x_2016_;
goto _start;
}
else
{
return v_b_2012_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2009_ = stack[0].m_obj;
size_t v_i_2010_ = stack[1].m_num;
size_t v_stop_2011_ = stack[2].m_num;
lean_object* v_b_2012_ = stack[3].m_obj;
lean_object* v_res_2020_;
v_res_2020_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2(v_as_2009_, v_i_2010_, v_stop_2011_, v_b_2012_);
stack->m_obj
 = v_res_2020_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2___boxed(lean_object* v_as_2021_, lean_object* v_i_2022_, lean_object* v_stop_2023_, lean_object* v_b_2024_){
_start:
{
size_t v_i_boxed_2025_; size_t v_stop_boxed_2026_; lean_object* v_res_2027_; 
v_i_boxed_2025_ = lean_unbox_usize(v_i_2022_);
lean_dec(v_i_2022_);
v_stop_boxed_2026_ = lean_unbox_usize(v_stop_2023_);
lean_dec(v_stop_2023_);
v_res_2027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2(v_as_2021_, v_i_boxed_2025_, v_stop_boxed_2026_, v_b_2024_);
lean_dec_ref(v_as_2021_);
return v_res_2027_;
}
}
lean_object* l_Lean_MVarId_assertHypotheses___lam__1(lean_object* v_mvarId_2028_, lean_object* v___x_2029_, uint8_t v___x_2030_, lean_object* v_hs_2031_, lean_object* v___x_2032_, lean_object* v___x_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_){
_start:
{
lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___x_2060_; 
lean_inc(v_mvarId_2028_);
v___x_2060_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2028_, v___x_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v___x_2061_; 
lean_dec_ref_known(v___x_2060_, 1);
lean_inc(v_mvarId_2028_);
v___x_2061_ = l_Lean_MVarId_getTag(v_mvarId_2028_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; lean_object* v___x_2063_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
lean_inc(v_a_2062_);
lean_dec_ref_known(v___x_2061_, 1);
lean_inc(v_mvarId_2028_);
v___x_2063_ = l_Lean_MVarId_getType(v_mvarId_2028_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v_a_2064_; lean_object* v___y_2066_; uint8_t v___x_2085_; 
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_a_2064_);
lean_dec_ref_known(v___x_2063_, 1);
v___x_2085_ = lean_nat_dec_lt(v___x_2032_, v___x_2029_);
if (v___x_2085_ == 0)
{
v___y_2066_ = v_a_2064_;
goto v___jp_2065_;
}
else
{
size_t v___x_2086_; size_t v___x_2087_; lean_object* v___x_2088_; 
v___x_2086_ = lean_usize_of_nat(v___x_2029_);
v___x_2087_ = ((size_t)0ULL);
v___x_2088_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__3(v_hs_2031_, v___x_2086_, v___x_2087_, v_a_2064_);
v___y_2066_ = v___x_2088_;
goto v___jp_2065_;
}
v___jp_2065_:
{
lean_object* v___x_2067_; 
v___x_2067_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_2066_, v_a_2062_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v_a_2068_; uint8_t v___x_2069_; 
v_a_2068_ = lean_ctor_get(v___x_2067_, 0);
lean_inc(v_a_2068_);
lean_dec_ref_known(v___x_2067_, 1);
v___x_2069_ = lean_nat_dec_lt(v___x_2032_, v___x_2029_);
if (v___x_2069_ == 0)
{
lean_inc(v_a_2068_);
v___y_2040_ = v_a_2068_;
v___y_2041_ = v_a_2068_;
goto v___jp_2039_;
}
else
{
uint8_t v___x_2070_; 
v___x_2070_ = lean_nat_dec_le(v___x_2029_, v___x_2029_);
if (v___x_2070_ == 0)
{
if (v___x_2069_ == 0)
{
lean_inc(v_a_2068_);
v___y_2040_ = v_a_2068_;
v___y_2041_ = v_a_2068_;
goto v___jp_2039_;
}
else
{
size_t v___x_2071_; size_t v___x_2072_; lean_object* v___x_2073_; 
v___x_2071_ = ((size_t)0ULL);
v___x_2072_ = lean_usize_of_nat(v___x_2029_);
lean_inc(v_a_2068_);
v___x_2073_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2(v_hs_2031_, v___x_2071_, v___x_2072_, v_a_2068_);
v___y_2040_ = v_a_2068_;
v___y_2041_ = v___x_2073_;
goto v___jp_2039_;
}
}
else
{
size_t v___x_2074_; size_t v___x_2075_; lean_object* v___x_2076_; 
v___x_2074_ = ((size_t)0ULL);
v___x_2075_ = lean_usize_of_nat(v___x_2029_);
lean_inc(v_a_2068_);
v___x_2076_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2(v_hs_2031_, v___x_2074_, v___x_2075_, v_a_2068_);
v___y_2040_ = v_a_2068_;
v___y_2041_ = v___x_2076_;
goto v___jp_2039_;
}
}
}
else
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2084_; 
lean_dec(v___x_2032_);
lean_dec_ref(v_hs_2031_);
lean_dec(v___x_2029_);
lean_dec(v_mvarId_2028_);
v_a_2077_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2079_ = v___x_2067_;
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_2067_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2082_; 
if (v_isShared_2080_ == 0)
{
v___x_2082_ = v___x_2079_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_a_2077_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
}
}
else
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
lean_dec(v_a_2062_);
lean_dec(v___x_2032_);
lean_dec_ref(v_hs_2031_);
lean_dec(v___x_2029_);
lean_dec(v_mvarId_2028_);
v_a_2089_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2063_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2063_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
else
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
lean_dec(v___x_2032_);
lean_dec_ref(v_hs_2031_);
lean_dec(v___x_2029_);
lean_dec(v_mvarId_2028_);
v_a_2097_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2099_ = v___x_2061_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2061_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2097_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
else
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
lean_dec(v___x_2032_);
lean_dec_ref(v_hs_2031_);
lean_dec(v___x_2029_);
lean_dec(v_mvarId_2028_);
v_a_2105_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2107_ = v___x_2060_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_2060_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2105_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
v___jp_2039_:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; uint8_t v___x_2045_; lean_object* v___x_2046_; 
v___x_2042_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(v_mvarId_2028_, v___y_2041_, v___y_2035_);
lean_dec_ref(v___x_2042_);
v___x_2043_ = l_Lean_Expr_mvarId_x21(v___y_2040_);
lean_dec_ref(v___y_2040_);
v___x_2044_ = lean_box(0);
v___x_2045_ = 1;
lean_inc(v___x_2029_);
v___x_2046_ = l_Lean_Meta_introNCore(v___x_2043_, v___x_2029_, v___x_2044_, v___x_2030_, v___x_2045_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_a_2047_; lean_object* v_fst_2048_; lean_object* v_snd_2049_; lean_object* v___f_2050_; lean_object* v___x_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_a_2047_);
lean_dec_ref_known(v___x_2046_, 1);
v_fst_2048_ = lean_ctor_get(v_a_2047_, 0);
v_snd_2049_ = lean_ctor_get(v_a_2047_, 1);
lean_inc(v_fst_2048_);
v___f_2050_ = lean_alloc_closure((void*)(l_Lean_MVarId_assertHypotheses___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2050_, 0, v___x_2029_);
lean_closure_set(v___f_2050_, 1, v_hs_2031_);
lean_closure_set(v___f_2050_, 2, v_fst_2048_);
lean_closure_set(v___f_2050_, 3, v___x_2032_);
lean_inc(v_snd_2049_);
v___x_2051_ = l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg(v_snd_2049_, v___f_2050_, v___y_2035_);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2058_ == 0)
{
lean_object* v_unused_2059_; 
v_unused_2059_ = lean_ctor_get(v___x_2051_, 0);
lean_dec(v_unused_2059_);
v___x_2053_ = v___x_2051_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_dec(v___x_2051_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 0, v_a_2047_);
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2047_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
else
{
lean_dec(v___x_2032_);
lean_dec_ref(v_hs_2031_);
lean_dec(v___x_2029_);
return v___x_2046_;
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assertHypotheses___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2028_ = stack[0].m_obj;
lean_object* v___x_2029_ = stack[1].m_obj;
uint8_t v___x_2030_ = stack[2].m_num;
lean_object* v_hs_2031_ = stack[3].m_obj;
lean_object* v___x_2032_ = stack[4].m_obj;
lean_object* v___x_2033_ = stack[5].m_obj;
lean_object* v___y_2034_ = stack[6].m_obj;
lean_object* v___y_2035_ = stack[7].m_obj;
lean_object* v___y_2036_ = stack[8].m_obj;
lean_object* v___y_2037_ = stack[9].m_obj;
lean_object* v_res_2113_;
v_res_2113_ = l_Lean_MVarId_assertHypotheses___lam__1(v_mvarId_2028_, v___x_2029_, v___x_2030_, v_hs_2031_, v___x_2032_, v___x_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
stack->m_obj
 = v_res_2113_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___lam__1___boxed(lean_object* v_mvarId_2114_, lean_object* v___x_2115_, lean_object* v___x_2116_, lean_object* v_hs_2117_, lean_object* v___x_2118_, lean_object* v___x_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
uint8_t v___x_2943__boxed_2125_; lean_object* v_res_2126_; 
v___x_2943__boxed_2125_ = lean_unbox(v___x_2116_);
v_res_2126_ = l_Lean_MVarId_assertHypotheses___lam__1(v_mvarId_2114_, v___x_2115_, v___x_2943__boxed_2125_, v_hs_2117_, v___x_2118_, v___x_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2122_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
return v_res_2126_;
}
}
lean_object* l_Lean_MVarId_assertHypotheses(lean_object* v_mvarId_2132_, lean_object* v_hs_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_){
_start:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; uint8_t v___x_2141_; 
v___x_2139_ = lean_array_get_size(v_hs_2133_);
v___x_2140_ = lean_unsigned_to_nat(0u);
v___x_2141_ = lean_nat_dec_eq(v___x_2139_, v___x_2140_);
if (v___x_2141_ == 0)
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___f_2144_; lean_object* v___x_2145_; 
v___x_2142_ = ((lean_object*)(l_Lean_MVarId_assertHypotheses___closed__1));
v___x_2143_ = lean_box(v___x_2141_);
lean_inc(v_mvarId_2132_);
v___f_2144_ = lean_alloc_closure((void*)(l_Lean_MVarId_assertHypotheses___lam__1___boxed), 11, 6);
lean_closure_set(v___f_2144_, 0, v_mvarId_2132_);
lean_closure_set(v___f_2144_, 1, v___x_2139_);
lean_closure_set(v___f_2144_, 2, v___x_2143_);
lean_closure_set(v___f_2144_, 3, v_hs_2133_);
lean_closure_set(v___f_2144_, 4, v___x_2140_);
lean_closure_set(v___f_2144_, 5, v___x_2142_);
v___x_2145_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(v_mvarId_2132_, v___f_2144_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_);
return v___x_2145_;
}
else
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
lean_dec_ref(v_hs_2133_);
v___x_2146_ = ((lean_object*)(l_Lean_MVarId_assertHypotheses___closed__2));
v___x_2147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2146_);
lean_ctor_set(v___x_2147_, 1, v_mvarId_2132_);
v___x_2148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2148_, 0, v___x_2147_);
return v___x_2148_;
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assertHypotheses_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2132_ = stack[0].m_obj;
lean_object* v_hs_2133_ = stack[1].m_obj;
lean_object* v_a_2134_ = stack[2].m_obj;
lean_object* v_a_2135_ = stack[3].m_obj;
lean_object* v_a_2136_ = stack[4].m_obj;
lean_object* v_a_2137_ = stack[5].m_obj;
lean_object* v_res_2149_;
v_res_2149_ = l_Lean_MVarId_assertHypotheses(v_mvarId_2132_, v_hs_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_);
stack->m_obj
 = v_res_2149_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___boxed(lean_object* v_mvarId_2150_, lean_object* v_hs_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l_Lean_MVarId_assertHypotheses(v_mvarId_2150_, v_hs_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_);
lean_dec(v_a_2155_);
lean_dec_ref(v_a_2154_);
lean_dec(v_a_2153_);
lean_dec_ref(v_a_2152_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0(lean_object* v_upperBound_2158_, lean_object* v_hs_2159_, lean_object* v_fst_2160_, lean_object* v_inst_2161_, lean_object* v_R_2162_, lean_object* v_a_2163_, lean_object* v_b_2164_, lean_object* v_c_2165_){
_start:
{
lean_object* v___x_2166_; 
v___x_2166_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg(v_upperBound_2158_, v_hs_2159_, v_fst_2160_, v_a_2163_, v_b_2164_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___boxed(lean_object* v_upperBound_2167_, lean_object* v_hs_2168_, lean_object* v_fst_2169_, lean_object* v_inst_2170_, lean_object* v_R_2171_, lean_object* v_a_2172_, lean_object* v_b_2173_, lean_object* v_c_2174_){
_start:
{
lean_object* v_res_2175_; 
v_res_2175_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0(v_upperBound_2167_, v_hs_2168_, v_fst_2169_, v_inst_2170_, v_R_2171_, v_a_2172_, v_b_2173_, v_c_2174_);
lean_dec_ref(v_fst_2169_);
lean_dec_ref(v_hs_2168_);
lean_dec(v_upperBound_2167_);
return v_res_2175_;
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
