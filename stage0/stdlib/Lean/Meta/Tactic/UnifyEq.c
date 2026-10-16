// Lean compiler output
// Module: Lean.Meta.Tactic.UnifyEq
// Imports: public import Lean.Meta.Tactic.Injection import Init.Data.Nat.Internal.Linear
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
lean_object* l_Lean_Meta_evalNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isOffset_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_MVarId_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
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
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_MVarId_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isHEq(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_MVarId_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Meta_isConstructorApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_injectionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_heqToEq_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_heqToEq_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "Dependent elimination failed: Failed to solve equation"};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "\nat case `"};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_unifyEq_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Meta_unifyEq_x3f___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_unifyEq_x3f___lam__0___closed__0_value;
static const lean_string_object l_Lean_Meta_unifyEq_x3f___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l_Lean_Meta_unifyEq_x3f___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_unifyEq_x3f___lam__0___closed__1_value;
static const lean_string_object l_Lean_Meta_unifyEq_x3f___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elimOffset"};
static const lean_object* l_Lean_Meta_unifyEq_x3f___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_unifyEq_x3f___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Meta_unifyEq_x3f___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_unifyEq_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_unifyEq_x3f___lam__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_unifyEq_x3f___lam__0___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_unifyEq_x3f___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(238, 85, 239, 193, 128, 115, 38, 143)}};
static const lean_ctor_object l_Lean_Meta_unifyEq_x3f___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_unifyEq_x3f___lam__0___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_unifyEq_x3f___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(94, 91, 22, 141, 221, 120, 153, 253)}};
static const lean_object* l_Lean_Meta_unifyEq_x3f___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_unifyEq_x3f___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_unifyEq_x3f___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_unifyEq_x3f___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_unifyEq_x3f___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Meta_unifyEq_x3f___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_unifyEq_x3f___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_unifyEq_x3f___lam__1___closed__1 = (const lean_object*)&l_Lean_Meta_unifyEq_x3f___lam__1___closed__1_value;
static const lean_string_object l_Lean_Meta_unifyEq_x3f___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Expected an equality, but found"};
static const lean_object* l_Lean_Meta_unifyEq_x3f___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_unifyEq_x3f___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Meta_unifyEq_x3f___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_unifyEq_x3f___lam__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_heqToEq_x27(lean_object* v_mvarId_1_, lean_object* v_eqDecl_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; uint8_t v___x_10_; lean_object* v___x_11_; 
v___x_8_ = l_Lean_LocalDecl_fvarId(v_eqDecl_2_);
lean_inc(v___x_8_);
v___x_9_ = l_Lean_mkFVar(v___x_8_);
v___x_10_ = 1;
v___x_11_ = l_Lean_Meta_mkEqOfHEq(v___x_9_, v___x_10_, v_a_3_, v_a_4_, v_a_5_, v_a_6_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v_a_12_; lean_object* v___x_13_; 
v_a_12_ = lean_ctor_get(v___x_11_, 0);
lean_inc_n(v_a_12_, 2);
lean_dec_ref_known(v___x_11_, 1);
lean_inc(v_a_6_);
lean_inc_ref(v_a_5_);
lean_inc(v_a_4_);
lean_inc_ref(v_a_3_);
v___x_13_ = lean_infer_type(v_a_12_, v_a_3_, v_a_4_, v_a_5_, v_a_6_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v_a_14_; lean_object* v___x_15_; 
v_a_14_ = lean_ctor_get(v___x_13_, 0);
lean_inc(v_a_14_);
lean_dec_ref_known(v___x_13_, 1);
lean_inc(v_a_6_);
lean_inc_ref(v_a_5_);
lean_inc(v_a_4_);
lean_inc_ref(v_a_3_);
v___x_15_ = lean_whnf(v_a_14_, v_a_3_, v_a_4_, v_a_5_, v_a_6_);
if (lean_obj_tag(v___x_15_) == 0)
{
lean_object* v_a_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v_a_16_ = lean_ctor_get(v___x_15_, 0);
lean_inc(v_a_16_);
lean_dec_ref_known(v___x_15_, 1);
v___x_17_ = l_Lean_LocalDecl_userName(v_eqDecl_2_);
v___x_18_ = l_Lean_MVarId_assert(v_mvarId_1_, v___x_17_, v_a_16_, v_a_12_, v_a_3_, v_a_4_, v_a_5_, v_a_6_);
if (lean_obj_tag(v___x_18_) == 0)
{
lean_object* v_a_19_; lean_object* v___x_20_; 
v_a_19_ = lean_ctor_get(v___x_18_, 0);
lean_inc(v_a_19_);
lean_dec_ref_known(v___x_18_, 1);
v___x_20_ = l_Lean_MVarId_clear(v_a_19_, v___x_8_, v_a_3_, v_a_4_, v_a_5_, v_a_6_);
return v___x_20_;
}
else
{
lean_dec(v___x_8_);
return v___x_18_;
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_a_12_);
lean_dec(v___x_8_);
lean_dec(v_mvarId_1_);
v_a_21_ = lean_ctor_get(v___x_15_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_15_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_15_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_15_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
else
{
lean_object* v_a_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_36_; 
lean_dec(v_a_12_);
lean_dec(v___x_8_);
lean_dec(v_mvarId_1_);
v_a_29_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_36_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_36_ == 0)
{
v___x_31_ = v___x_13_;
v_isShared_32_ = v_isSharedCheck_36_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_a_29_);
lean_dec(v___x_13_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_36_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
lean_object* v___x_34_; 
if (v_isShared_32_ == 0)
{
v___x_34_ = v___x_31_;
goto v_reusejp_33_;
}
else
{
lean_object* v_reuseFailAlloc_35_; 
v_reuseFailAlloc_35_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_35_, 0, v_a_29_);
v___x_34_ = v_reuseFailAlloc_35_;
goto v_reusejp_33_;
}
v_reusejp_33_:
{
return v___x_34_;
}
}
}
}
else
{
lean_object* v_a_37_; lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_44_; 
lean_dec(v___x_8_);
lean_dec(v_mvarId_1_);
v_a_37_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_44_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_44_ == 0)
{
v___x_39_ = v___x_11_;
v_isShared_40_ = v_isSharedCheck_44_;
goto v_resetjp_38_;
}
else
{
lean_inc(v_a_37_);
lean_dec(v___x_11_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_44_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
lean_object* v___x_42_; 
if (v_isShared_40_ == 0)
{
v___x_42_ = v___x_39_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v_a_37_);
v___x_42_ = v_reuseFailAlloc_43_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
return v___x_42_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_heqToEq_x27___boxed(lean_object* v_mvarId_45_, lean_object* v_eqDecl_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_heqToEq_x27(v_mvarId_45_, v_eqDecl_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
lean_dec(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_eqDecl_46_);
return v_res_52_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f___closed__0(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = lean_unsigned_to_nat(0u);
v___x_54_ = l_Lean_mkNatLit(v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f(lean_object* v_e_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_){
_start:
{
lean_object* v___x_61_; 
lean_inc_ref(v_e_55_);
v___x_61_ = l_Lean_Meta_evalNat(v_e_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_);
if (lean_obj_tag(v___x_61_) == 0)
{
lean_object* v_a_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_80_; 
v_a_62_ = lean_ctor_get(v___x_61_, 0);
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_61_);
if (v_isSharedCheck_80_ == 0)
{
v___x_64_ = v___x_61_;
v_isShared_65_ = v_isSharedCheck_80_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_a_62_);
lean_dec(v___x_61_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_80_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
if (lean_obj_tag(v_a_62_) == 0)
{
lean_object* v___x_66_; 
lean_del_object(v___x_64_);
v___x_66_ = l_Lean_Meta_isOffset_x3f(v_e_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_);
return v___x_66_;
}
else
{
lean_object* v_val_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_79_; 
lean_dec_ref(v_e_55_);
v_val_67_ = lean_ctor_get(v_a_62_, 0);
v_isSharedCheck_79_ = !lean_is_exclusive(v_a_62_);
if (v_isSharedCheck_79_ == 0)
{
v___x_69_ = v_a_62_;
v_isShared_70_ = v_isSharedCheck_79_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_val_67_);
lean_dec(v_a_62_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_79_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_74_; 
v___x_71_ = lean_obj_once(&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f___closed__0, &l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f___closed__0);
v___x_72_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
lean_ctor_set(v___x_72_, 1, v_val_67_);
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 0, v___x_72_);
v___x_74_ = v___x_69_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v___x_72_);
v___x_74_ = v_reuseFailAlloc_78_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
lean_object* v___x_76_; 
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 0, v___x_74_);
v___x_76_ = v___x_64_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v___x_74_);
v___x_76_ = v_reuseFailAlloc_77_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
return v___x_76_;
}
}
}
}
}
}
else
{
lean_object* v_a_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_88_; 
lean_dec_ref(v_e_55_);
v_a_81_ = lean_ctor_get(v___x_61_, 0);
v_isSharedCheck_88_ = !lean_is_exclusive(v___x_61_);
if (v_isSharedCheck_88_ == 0)
{
v___x_83_ = v___x_61_;
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_a_81_);
lean_dec(v___x_61_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_86_; 
if (v_isShared_84_ == 0)
{
v___x_86_ = v___x_83_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v_a_81_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f___boxed(lean_object* v_e_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f(v_e_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_);
lean_dec(v_a_93_);
lean_dec_ref(v_a_92_);
lean_dec(v_a_91_);
lean_dec_ref(v_a_90_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0___redArg(lean_object* v_x_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l_Lean_Meta_saveState___redArg(v___y_98_, v___y_100_);
if (lean_obj_tag(v___x_102_) == 0)
{
lean_object* v_a_103_; lean_object* v___x_104_; 
v_a_103_ = lean_ctor_get(v___x_102_, 0);
lean_inc(v_a_103_);
lean_dec_ref_known(v___x_102_, 1);
lean_inc(v___y_100_);
lean_inc_ref(v___y_99_);
lean_inc(v___y_98_);
lean_inc_ref(v___y_97_);
v___x_104_ = lean_apply_5(v_x_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, lean_box(0));
if (lean_obj_tag(v___x_104_) == 0)
{
lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_113_; 
lean_dec(v_a_103_);
v_a_105_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_113_ == 0)
{
v___x_107_ = v___x_104_;
v_isShared_108_ = v_isSharedCheck_113_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_dec(v___x_104_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_113_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_109_; lean_object* v___x_111_; 
v___x_109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_109_, 0, v_a_105_);
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 0, v___x_109_);
v___x_111_ = v___x_107_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_109_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
else
{
lean_object* v_a_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_144_; 
v_a_114_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_144_ == 0)
{
v___x_116_ = v___x_104_;
v_isShared_117_ = v_isSharedCheck_144_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_a_114_);
lean_dec(v___x_104_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_144_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
uint8_t v___x_118_; 
v___x_118_ = l_Lean_Exception_isInterrupt(v_a_114_);
if (v___x_118_ == 0)
{
uint8_t v___x_119_; 
lean_inc(v_a_114_);
v___x_119_ = l_Lean_Exception_isRuntime(v_a_114_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; 
lean_del_object(v___x_116_);
lean_dec(v_a_114_);
v___x_120_ = l_Lean_Meta_SavedState_restore___redArg(v_a_103_, v___y_98_, v___y_100_);
if (lean_obj_tag(v___x_120_) == 0)
{
lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_128_; 
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_128_ == 0)
{
lean_object* v_unused_129_; 
v_unused_129_ = lean_ctor_get(v___x_120_, 0);
lean_dec(v_unused_129_);
v___x_122_ = v___x_120_;
v_isShared_123_ = v_isSharedCheck_128_;
goto v_resetjp_121_;
}
else
{
lean_dec(v___x_120_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_128_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_124_; lean_object* v___x_126_; 
v___x_124_ = lean_box(0);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 0, v___x_124_);
v___x_126_ = v___x_122_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v___x_124_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
else
{
lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_137_; 
v_a_130_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_137_ == 0)
{
v___x_132_ = v___x_120_;
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_dec(v___x_120_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_135_; 
if (v_isShared_133_ == 0)
{
v___x_135_ = v___x_132_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_a_130_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
else
{
lean_object* v___x_139_; 
lean_dec(v_a_103_);
if (v_isShared_117_ == 0)
{
v___x_139_ = v___x_116_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_a_114_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
else
{
lean_object* v___x_142_; 
lean_dec(v_a_103_);
if (v_isShared_117_ == 0)
{
v___x_142_ = v___x_116_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_a_114_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
}
}
else
{
lean_object* v_a_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_152_; 
lean_dec_ref(v_x_96_);
v_a_145_ = lean_ctor_get(v___x_102_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_102_);
if (v_isSharedCheck_152_ == 0)
{
v___x_147_ = v___x_102_;
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_a_145_);
lean_dec(v___x_102_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_152_;
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
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_a_145_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0___redArg___boxed(lean_object* v_x_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0___redArg(v_x_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_);
lean_dec(v___y_157_);
lean_dec_ref(v___y_156_);
lean_dec(v___y_155_);
lean_dec_ref(v___y_154_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0(lean_object* v_00_u03b1_160_, lean_object* v_x_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0___redArg(v_x_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0___boxed(lean_object* v_00_u03b1_168_, lean_object* v_x_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0(v_00_u03b1_168_, v_x_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1_spec__1(lean_object* v_msgData_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_){
_start:
{
lean_object* v___x_182_; lean_object* v_env_183_; uint8_t v___x_184_; lean_object* v_env_185_; lean_object* v___x_186_; lean_object* v_toCold_187_; lean_object* v_mctx_188_; lean_object* v_lctx_189_; lean_object* v_options_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_182_ = lean_st_ref_get(v___y_180_);
v_env_183_ = lean_ctor_get(v___x_182_, 0);
lean_inc_ref(v_env_183_);
lean_dec(v___x_182_);
v___x_184_ = 0;
v_env_185_ = l_Lean_Environment_setRecordingDeps(v_env_183_, v___x_184_);
v___x_186_ = lean_st_ref_get(v___y_178_);
v_toCold_187_ = lean_ctor_get(v___y_179_, 0);
v_mctx_188_ = lean_ctor_get(v___x_186_, 0);
lean_inc_ref(v_mctx_188_);
lean_dec(v___x_186_);
v_lctx_189_ = lean_ctor_get(v___y_177_, 2);
v_options_190_ = lean_ctor_get(v_toCold_187_, 2);
lean_inc_ref(v_options_190_);
lean_inc_ref(v_lctx_189_);
v___x_191_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_191_, 0, v_env_185_);
lean_ctor_set(v___x_191_, 1, v_mctx_188_);
lean_ctor_set(v___x_191_, 2, v_lctx_189_);
lean_ctor_set(v___x_191_, 3, v_options_190_);
v___x_192_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v_msgData_176_);
v___x_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1_spec__1___boxed(lean_object* v_msgData_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1_spec__1(v_msgData_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(lean_object* v_msg_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v_ref_207_; lean_object* v___x_208_; lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_217_; 
v_ref_207_ = lean_ctor_get(v___y_204_, 2);
v___x_208_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1_spec__1(v_msg_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_);
v_a_209_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_217_ == 0)
{
v___x_211_ = v___x_208_;
v_isShared_212_ = v_isSharedCheck_217_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_dec(v___x_208_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_217_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_213_; lean_object* v___x_215_; 
lean_inc(v_ref_207_);
v___x_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_213_, 0, v_ref_207_);
lean_ctor_set(v___x_213_, 1, v_a_209_);
if (v_isShared_212_ == 0)
{
lean_ctor_set_tag(v___x_211_, 1);
lean_ctor_set(v___x_211_, 0, v___x_213_);
v___x_215_ = v___x_211_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_213_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg___boxed(lean_object* v_msg_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(v_msg_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
return v_res_224_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = ((lean_object*)(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__0));
v___x_227_ = l_Lean_stringToMessageData(v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq(lean_object* v_mvarId_228_, lean_object* v_eqFVarId_229_, lean_object* v_subst_230_, lean_object* v_acyclic_231_, lean_object* v_eqDecl_232_, lean_object* v_a_233_, lean_object* v_b_234_, uint8_t v_symm_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_){
_start:
{
uint8_t v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_241_ = 1;
v___x_242_ = lean_box(v_symm_235_);
v___x_243_ = lean_box(v___x_241_);
v___x_244_ = lean_box(v___x_241_);
lean_inc(v_subst_230_);
lean_inc(v_eqFVarId_229_);
lean_inc(v_mvarId_228_);
v___x_245_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___boxed), 11, 6);
lean_closure_set(v___x_245_, 0, v_mvarId_228_);
lean_closure_set(v___x_245_, 1, v_eqFVarId_229_);
lean_closure_set(v___x_245_, 2, v___x_242_);
lean_closure_set(v___x_245_, 3, v_subst_230_);
lean_closure_set(v___x_245_, 4, v___x_243_);
lean_closure_set(v___x_245_, 5, v___x_244_);
v___x_246_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0___redArg(v___x_245_, v_a_236_, v_a_237_, v_a_238_, v_a_239_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_322_; 
v_a_247_ = lean_ctor_get(v___x_246_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_322_ == 0)
{
v___x_249_ = v___x_246_;
v_isShared_250_ = v_isSharedCheck_322_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___x_246_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_322_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
if (lean_obj_tag(v_a_247_) == 1)
{
lean_object* v_val_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_265_; 
lean_dec_ref(v_b_234_);
lean_dec_ref(v_a_233_);
lean_dec_ref(v_acyclic_231_);
lean_dec(v_subst_230_);
lean_dec(v_eqFVarId_229_);
lean_dec(v_mvarId_228_);
v_val_251_ = lean_ctor_get(v_a_247_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v_a_247_);
if (v_isSharedCheck_265_ == 0)
{
v___x_253_ = v_a_247_;
v_isShared_254_ = v_isSharedCheck_265_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_val_251_);
lean_dec(v_a_247_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_265_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v_fst_255_; lean_object* v_snd_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_260_; 
v_fst_255_ = lean_ctor_get(v_val_251_, 0);
lean_inc(v_fst_255_);
v_snd_256_ = lean_ctor_get(v_val_251_, 1);
lean_inc(v_snd_256_);
lean_dec(v_val_251_);
v___x_257_ = lean_unsigned_to_nat(0u);
v___x_258_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_258_, 0, v_snd_256_);
lean_ctor_set(v___x_258_, 1, v_fst_255_);
lean_ctor_set(v___x_258_, 2, v___x_257_);
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 0, v___x_258_);
v___x_260_ = v___x_253_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_258_);
v___x_260_ = v_reuseFailAlloc_264_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
lean_object* v___x_262_; 
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 0, v___x_260_);
v___x_262_ = v___x_249_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_260_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
}
else
{
lean_object* v___x_266_; 
lean_del_object(v___x_249_);
lean_dec(v_a_247_);
v___x_266_ = l_Lean_Meta_isExprDefEq(v_a_233_, v_b_234_, v_a_236_, v_a_237_, v_a_238_, v_a_239_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v_a_267_; uint8_t v___x_268_; 
v_a_267_ = lean_ctor_get(v___x_266_, 0);
lean_inc(v_a_267_);
lean_dec_ref_known(v___x_266_, 1);
v___x_268_ = lean_unbox(v_a_267_);
lean_dec(v_a_267_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; lean_object* v___x_270_; 
lean_dec(v_subst_230_);
v___x_269_ = l_Lean_mkFVar(v_eqFVarId_229_);
lean_inc(v_a_239_);
lean_inc_ref(v_a_238_);
lean_inc(v_a_237_);
lean_inc_ref(v_a_236_);
v___x_270_ = lean_apply_7(v_acyclic_231_, v_mvarId_228_, v___x_269_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, lean_box(0));
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_a_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_285_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_285_ == 0)
{
v___x_273_ = v___x_270_;
v_isShared_274_ = v_isSharedCheck_285_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_a_271_);
lean_dec(v___x_270_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_285_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
uint8_t v___x_275_; 
v___x_275_ = lean_unbox(v_a_271_);
lean_dec(v_a_271_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
lean_del_object(v___x_273_);
v___x_276_ = lean_obj_once(&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1, &l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1_once, _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1);
v___x_277_ = l_Lean_LocalDecl_type(v_eqDecl_232_);
v___x_278_ = l_Lean_indentExpr(v___x_277_);
v___x_279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_276_);
lean_ctor_set(v___x_279_, 1, v___x_278_);
v___x_280_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(v___x_279_, v_a_236_, v_a_237_, v_a_238_, v_a_239_);
return v___x_280_;
}
else
{
lean_object* v___x_281_; lean_object* v___x_283_; 
v___x_281_ = lean_box(0);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 0, v___x_281_);
v___x_283_ = v___x_273_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_281_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
else
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
v_a_286_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_293_ == 0)
{
v___x_288_ = v___x_270_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_270_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_286_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
else
{
lean_object* v___x_294_; 
lean_dec_ref(v_acyclic_231_);
v___x_294_ = l_Lean_MVarId_clear(v_mvarId_228_, v_eqFVarId_229_, v_a_236_, v_a_237_, v_a_238_, v_a_239_);
if (lean_obj_tag(v___x_294_) == 0)
{
lean_object* v_a_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_305_; 
v_a_295_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_305_ == 0)
{
v___x_297_ = v___x_294_;
v_isShared_298_ = v_isSharedCheck_305_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_a_295_);
lean_dec(v___x_294_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_305_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_303_; 
v___x_299_ = lean_unsigned_to_nat(0u);
v___x_300_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_300_, 0, v_a_295_);
lean_ctor_set(v___x_300_, 1, v_subst_230_);
lean_ctor_set(v___x_300_, 2, v___x_299_);
v___x_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 0, v___x_301_);
v___x_303_ = v___x_297_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v___x_301_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
else
{
lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_313_; 
lean_dec(v_subst_230_);
v_a_306_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_313_ == 0)
{
v___x_308_ = v___x_294_;
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v___x_294_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_311_; 
if (v_isShared_309_ == 0)
{
v___x_311_ = v___x_308_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_a_306_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
}
else
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_321_; 
lean_dec_ref(v_acyclic_231_);
lean_dec(v_subst_230_);
lean_dec(v_eqFVarId_229_);
lean_dec(v_mvarId_228_);
v_a_314_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_321_ == 0)
{
v___x_316_ = v___x_266_;
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v___x_266_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_314_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
}
}
else
{
lean_object* v_a_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_330_; 
lean_dec_ref(v_b_234_);
lean_dec_ref(v_a_233_);
lean_dec_ref(v_acyclic_231_);
lean_dec(v_subst_230_);
lean_dec(v_eqFVarId_229_);
lean_dec(v_mvarId_228_);
v_a_323_ = lean_ctor_get(v___x_246_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_330_ == 0)
{
v___x_325_ = v___x_246_;
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_a_323_);
lean_dec(v___x_246_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_328_; 
if (v_isShared_326_ == 0)
{
v___x_328_ = v___x_325_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_a_323_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___boxed(lean_object* v_mvarId_331_, lean_object* v_eqFVarId_332_, lean_object* v_subst_333_, lean_object* v_acyclic_334_, lean_object* v_eqDecl_335_, lean_object* v_a_336_, lean_object* v_b_337_, lean_object* v_symm_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_){
_start:
{
uint8_t v_symm_boxed_344_; lean_object* v_res_345_; 
v_symm_boxed_344_ = lean_unbox(v_symm_338_);
v_res_345_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq(v_mvarId_331_, v_eqFVarId_332_, v_subst_333_, v_acyclic_334_, v_eqDecl_335_, v_a_336_, v_b_337_, v_symm_boxed_344_, v_a_339_, v_a_340_, v_a_341_, v_a_342_);
lean_dec(v_a_342_);
lean_dec_ref(v_a_341_);
lean_dec(v_a_340_);
lean_dec_ref(v_a_339_);
lean_dec_ref(v_eqDecl_335_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1(lean_object* v_00_u03b1_346_, lean_object* v_msg_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(v_msg_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___boxed(lean_object* v_00_u03b1_354_, lean_object* v_msg_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1(v_00_u03b1_354_, v_msg_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
return v_res_361_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__1(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = ((lean_object*)(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__0));
v___x_364_ = l_Lean_stringToMessageData(v___x_363_);
return v___x_364_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__3(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = ((lean_object*)(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__2));
v___x_367_ = l_Lean_stringToMessageData(v___x_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection(lean_object* v_mvarId_368_, lean_object* v_eqFVarId_369_, lean_object* v_subst_370_, lean_object* v_caseName_x3f_371_, lean_object* v_eqDecl_372_, lean_object* v_injectionOffset_x3f_373_, lean_object* v_a_374_, lean_object* v_b_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_){
_start:
{
lean_object* v___y_382_; lean_object* v___y_383_; uint8_t v_a_427_; lean_object* v___x_467_; 
lean_inc(v_a_379_);
lean_inc_ref(v_a_378_);
lean_inc(v_a_377_);
lean_inc_ref(v_a_376_);
lean_inc_ref(v_b_375_);
lean_inc_ref(v_a_374_);
v___x_467_ = lean_apply_7(v_injectionOffset_x3f_373_, v_a_374_, v_b_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, lean_box(0));
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_534_; 
v_a_468_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_534_ == 0)
{
v___x_470_ = v___x_467_;
v_isShared_471_ = v_isSharedCheck_534_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v___x_467_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_534_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
if (lean_obj_tag(v_a_468_) == 1)
{
lean_object* v_val_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_484_; 
lean_dec_ref(v_b_375_);
lean_dec_ref(v_a_374_);
lean_dec(v_caseName_x3f_371_);
lean_dec(v_eqFVarId_369_);
lean_dec(v_mvarId_368_);
v_val_472_ = lean_ctor_get(v_a_468_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v_a_468_);
if (v_isSharedCheck_484_ == 0)
{
v___x_474_ = v_a_468_;
v_isShared_475_ = v_isSharedCheck_484_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_val_472_);
lean_dec(v_a_468_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_484_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_479_; 
v___x_476_ = lean_unsigned_to_nat(1u);
v___x_477_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_477_, 0, v_val_472_);
lean_ctor_set(v___x_477_, 1, v_subst_370_);
lean_ctor_set(v___x_477_, 2, v___x_476_);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 0, v___x_477_);
v___x_479_ = v___x_474_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_477_);
v___x_479_ = v_reuseFailAlloc_483_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
lean_object* v___x_481_; 
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 0, v___x_479_);
v___x_481_ = v___x_470_;
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
}
else
{
lean_object* v___x_485_; 
lean_del_object(v___x_470_);
lean_dec(v_a_468_);
lean_inc_ref(v_a_374_);
v___x_485_ = l_Lean_Meta_isConstructorApp(v_a_374_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_a_486_; uint8_t v___x_487_; 
v_a_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_a_486_);
lean_dec_ref_known(v___x_485_, 1);
v___x_487_ = lean_unbox(v_a_486_);
if (v___x_487_ == 0)
{
uint8_t v___x_488_; 
v___x_488_ = lean_unbox(v_a_486_);
lean_dec(v_a_486_);
v_a_427_ = v___x_488_;
goto v___jp_426_;
}
else
{
lean_object* v___x_489_; 
lean_dec(v_a_486_);
lean_inc_ref(v_b_375_);
v___x_489_ = l_Lean_Meta_isConstructorApp(v_b_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; uint8_t v___x_491_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_a_490_);
lean_dec_ref_known(v___x_489_, 1);
v___x_491_ = lean_unbox(v_a_490_);
if (v___x_491_ == 0)
{
uint8_t v___x_492_; 
v___x_492_ = lean_unbox(v_a_490_);
lean_dec(v_a_490_);
v_a_427_ = v___x_492_;
goto v___jp_426_;
}
else
{
lean_object* v___x_493_; 
lean_dec(v_a_490_);
lean_dec_ref(v_b_375_);
lean_dec_ref(v_a_374_);
lean_dec(v_caseName_x3f_371_);
v___x_493_ = l_Lean_Meta_injectionCore(v_mvarId_368_, v_eqFVarId_369_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_509_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_509_ == 0)
{
v___x_496_ = v___x_493_;
v_isShared_497_ = v_isSharedCheck_509_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_493_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_509_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
if (lean_obj_tag(v_a_494_) == 0)
{
lean_object* v___x_498_; lean_object* v___x_500_; 
lean_dec(v_subst_370_);
v___x_498_ = lean_box(0);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v___x_498_);
v___x_500_ = v___x_496_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_498_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
else
{
lean_object* v_mvarId_502_; lean_object* v_numNewEqs_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_507_; 
v_mvarId_502_ = lean_ctor_get(v_a_494_, 0);
lean_inc(v_mvarId_502_);
v_numNewEqs_503_ = lean_ctor_get(v_a_494_, 1);
lean_inc(v_numNewEqs_503_);
lean_dec_ref_known(v_a_494_, 2);
v___x_504_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_504_, 0, v_mvarId_502_);
lean_ctor_set(v___x_504_, 1, v_subst_370_);
lean_ctor_set(v___x_504_, 2, v_numNewEqs_503_);
v___x_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v___x_505_);
v___x_507_ = v___x_496_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_505_);
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
lean_dec(v_subst_370_);
v_a_510_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_493_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_493_);
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
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
lean_dec_ref(v_b_375_);
lean_dec_ref(v_a_374_);
lean_dec(v_caseName_x3f_371_);
lean_dec(v_subst_370_);
lean_dec(v_eqFVarId_369_);
lean_dec(v_mvarId_368_);
v_a_518_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_489_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_489_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_518_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
}
else
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_533_; 
lean_dec_ref(v_b_375_);
lean_dec_ref(v_a_374_);
lean_dec(v_caseName_x3f_371_);
lean_dec(v_subst_370_);
lean_dec(v_eqFVarId_369_);
lean_dec(v_mvarId_368_);
v_a_526_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v___x_485_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_485_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_531_; 
if (v_isShared_529_ == 0)
{
v___x_531_ = v___x_528_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_a_526_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
}
}
else
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
lean_dec_ref(v_b_375_);
lean_dec_ref(v_a_374_);
lean_dec(v_caseName_x3f_371_);
lean_dec(v_subst_370_);
lean_dec(v_eqFVarId_369_);
lean_dec(v_mvarId_368_);
v_a_535_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_542_ == 0)
{
v___x_537_ = v___x_467_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_467_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_535_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
v___jp_381_:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
lean_inc(v_eqFVarId_369_);
v___x_384_ = l_Lean_mkFVar(v_eqFVarId_369_);
v___x_385_ = l_Lean_Meta_mkEq(v___y_383_, v___y_382_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v_a_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_a_386_);
lean_dec_ref_known(v___x_385_, 1);
v___x_387_ = l_Lean_LocalDecl_userName(v_eqDecl_372_);
v___x_388_ = l_Lean_MVarId_assert(v_mvarId_368_, v___x_387_, v_a_386_, v___x_384_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v_a_389_; lean_object* v___x_390_; 
v_a_389_ = lean_ctor_get(v___x_388_, 0);
lean_inc(v_a_389_);
lean_dec_ref_known(v___x_388_, 1);
v___x_390_ = l_Lean_MVarId_clear(v_a_389_, v_eqFVarId_369_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_401_; 
v_a_391_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_401_ == 0)
{
v___x_393_ = v___x_390_;
v_isShared_394_ = v_isSharedCheck_401_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_390_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_401_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_395_ = lean_unsigned_to_nat(1u);
v___x_396_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_396_, 0, v_a_391_);
lean_ctor_set(v___x_396_, 1, v_subst_370_);
lean_ctor_set(v___x_396_, 2, v___x_395_);
v___x_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 0, v___x_397_);
v___x_399_ = v___x_393_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_397_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
else
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_409_; 
lean_dec(v_subst_370_);
v_a_402_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_409_ == 0)
{
v___x_404_ = v___x_390_;
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_390_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
if (v_isShared_405_ == 0)
{
v___x_407_ = v___x_404_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_a_402_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
else
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_417_; 
lean_dec(v_subst_370_);
lean_dec(v_eqFVarId_369_);
v_a_410_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_417_ == 0)
{
v___x_412_ = v___x_388_;
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_388_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_415_; 
if (v_isShared_413_ == 0)
{
v___x_415_ = v___x_412_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_a_410_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
else
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_425_; 
lean_dec_ref(v___x_384_);
lean_dec(v_subst_370_);
lean_dec(v_eqFVarId_369_);
lean_dec(v_mvarId_368_);
v_a_418_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_425_ == 0)
{
v___x_420_ = v___x_385_;
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_385_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_418_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
v___jp_426_:
{
lean_object* v___x_428_; 
lean_inc(v_a_379_);
lean_inc_ref(v_a_378_);
lean_inc(v_a_377_);
lean_inc_ref(v_a_376_);
lean_inc_ref(v_a_374_);
v___x_428_ = lean_whnf(v_a_374_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; lean_object* v___x_430_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_a_429_);
lean_dec_ref_known(v___x_428_, 1);
lean_inc(v_a_379_);
lean_inc_ref(v_a_378_);
lean_inc(v_a_377_);
lean_inc_ref(v_a_376_);
lean_inc_ref(v_b_375_);
v___x_430_ = lean_whnf(v_b_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v_a_431_; uint8_t v___x_432_; 
v_a_431_ = lean_ctor_get(v___x_430_, 0);
lean_inc(v_a_431_);
lean_dec_ref_known(v___x_430_, 1);
v___x_432_ = lean_expr_eqv(v_a_429_, v_a_374_);
lean_dec_ref(v_a_374_);
if (v___x_432_ == 0)
{
lean_dec_ref(v_b_375_);
lean_dec(v_caseName_x3f_371_);
v___y_382_ = v_a_431_;
v___y_383_ = v_a_429_;
goto v___jp_381_;
}
else
{
if (v_a_427_ == 0)
{
uint8_t v___x_433_; 
v___x_433_ = lean_expr_eqv(v_a_431_, v_b_375_);
lean_dec_ref(v_b_375_);
if (v___x_433_ == 0)
{
lean_dec(v_caseName_x3f_371_);
v___y_382_ = v_a_431_;
v___y_383_ = v_a_429_;
goto v___jp_381_;
}
else
{
lean_dec(v_a_431_);
lean_dec(v_a_429_);
lean_dec(v_subst_370_);
lean_dec(v_eqFVarId_369_);
lean_dec(v_mvarId_368_);
if (lean_obj_tag(v_caseName_x3f_371_) == 0)
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_434_ = lean_obj_once(&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1, &l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1_once, _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1);
v___x_435_ = l_Lean_LocalDecl_type(v_eqDecl_372_);
v___x_436_ = l_Lean_indentExpr(v___x_435_);
v___x_437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_437_, 0, v___x_434_);
lean_ctor_set(v___x_437_, 1, v___x_436_);
v___x_438_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(v___x_437_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
return v___x_438_;
}
else
{
lean_object* v_val_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v_val_439_ = lean_ctor_get(v_caseName_x3f_371_, 0);
lean_inc(v_val_439_);
lean_dec_ref_known(v_caseName_x3f_371_, 1);
v___x_440_ = lean_obj_once(&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1, &l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1_once, _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1);
v___x_441_ = l_Lean_LocalDecl_type(v_eqDecl_372_);
v___x_442_ = l_Lean_indentExpr(v___x_441_);
v___x_443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_443_, 0, v___x_440_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
v___x_444_ = lean_obj_once(&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__1, &l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__1_once, _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__1);
v___x_445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_443_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
v___x_446_ = l_Lean_MessageData_ofConstName(v_val_439_, v_a_427_);
v___x_447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_445_);
lean_ctor_set(v___x_447_, 1, v___x_446_);
v___x_448_ = lean_obj_once(&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__3, &l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__3_once, _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__3);
v___x_449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_449_, 0, v___x_447_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
v___x_450_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(v___x_449_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
return v___x_450_;
}
}
}
else
{
lean_dec_ref(v_b_375_);
lean_dec(v_caseName_x3f_371_);
v___y_382_ = v_a_431_;
v___y_383_ = v_a_429_;
goto v___jp_381_;
}
}
}
else
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
lean_dec(v_a_429_);
lean_dec_ref(v_b_375_);
lean_dec_ref(v_a_374_);
lean_dec(v_caseName_x3f_371_);
lean_dec(v_subst_370_);
lean_dec(v_eqFVarId_369_);
lean_dec(v_mvarId_368_);
v_a_451_ = lean_ctor_get(v___x_430_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v___x_430_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_430_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_451_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
else
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_466_; 
lean_dec_ref(v_b_375_);
lean_dec_ref(v_a_374_);
lean_dec(v_caseName_x3f_371_);
lean_dec(v_subst_370_);
lean_dec(v_eqFVarId_369_);
lean_dec(v_mvarId_368_);
v_a_459_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_466_ == 0)
{
v___x_461_ = v___x_428_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_428_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
if (v_isShared_462_ == 0)
{
v___x_464_ = v___x_461_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_a_459_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___boxed(lean_object* v_mvarId_543_, lean_object* v_eqFVarId_544_, lean_object* v_subst_545_, lean_object* v_caseName_x3f_546_, lean_object* v_eqDecl_547_, lean_object* v_injectionOffset_x3f_548_, lean_object* v_a_549_, lean_object* v_b_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection(v_mvarId_543_, v_eqFVarId_544_, v_subst_545_, v_caseName_x3f_546_, v_eqDecl_547_, v_injectionOffset_x3f_548_, v_a_549_, v_b_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_);
lean_dec(v_a_554_);
lean_dec_ref(v_a_553_);
lean_dec(v_a_552_);
lean_dec_ref(v_a_551_);
lean_dec_ref(v_eqDecl_547_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__1___redArg(lean_object* v_e_557_, lean_object* v___y_558_){
_start:
{
uint8_t v___x_560_; 
v___x_560_ = l_Lean_Expr_hasMVar(v_e_557_);
if (v___x_560_ == 0)
{
lean_object* v___x_561_; 
v___x_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_561_, 0, v_e_557_);
return v___x_561_;
}
else
{
lean_object* v___x_562_; lean_object* v_mctx_563_; lean_object* v___x_564_; lean_object* v_fst_565_; lean_object* v_snd_566_; lean_object* v___x_567_; lean_object* v_cache_568_; lean_object* v_zetaDeltaFVarIds_569_; lean_object* v_postponed_570_; lean_object* v_diag_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_580_; 
v___x_562_ = lean_st_ref_get(v___y_558_);
v_mctx_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc_ref(v_mctx_563_);
lean_dec(v___x_562_);
v___x_564_ = l_Lean_instantiateMVarsCore(v_mctx_563_, v_e_557_);
v_fst_565_ = lean_ctor_get(v___x_564_, 0);
lean_inc(v_fst_565_);
v_snd_566_ = lean_ctor_get(v___x_564_, 1);
lean_inc(v_snd_566_);
lean_dec_ref(v___x_564_);
v___x_567_ = lean_st_ref_take(v___y_558_);
v_cache_568_ = lean_ctor_get(v___x_567_, 1);
v_zetaDeltaFVarIds_569_ = lean_ctor_get(v___x_567_, 2);
v_postponed_570_ = lean_ctor_get(v___x_567_, 3);
v_diag_571_ = lean_ctor_get(v___x_567_, 4);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_580_ == 0)
{
lean_object* v_unused_581_; 
v_unused_581_ = lean_ctor_get(v___x_567_, 0);
lean_dec(v_unused_581_);
v___x_573_ = v___x_567_;
v_isShared_574_ = v_isSharedCheck_580_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_diag_571_);
lean_inc(v_postponed_570_);
lean_inc(v_zetaDeltaFVarIds_569_);
lean_inc(v_cache_568_);
lean_dec(v___x_567_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_580_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 0, v_snd_566_);
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_snd_566_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_cache_568_);
lean_ctor_set(v_reuseFailAlloc_579_, 2, v_zetaDeltaFVarIds_569_);
lean_ctor_set(v_reuseFailAlloc_579_, 3, v_postponed_570_);
lean_ctor_set(v_reuseFailAlloc_579_, 4, v_diag_571_);
v___x_576_ = v_reuseFailAlloc_579_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = lean_st_ref_put(v___y_558_, v___x_576_);
v___x_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_578_, 0, v_fst_565_);
return v___x_578_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__1___redArg___boxed(lean_object* v_e_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__1___redArg(v_e_582_, v___y_583_);
lean_dec(v___y_583_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__1(lean_object* v_e_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__1___redArg(v_e_586_, v___y_588_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__1___boxed(lean_object* v_e_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__1(v_e_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___redArg(lean_object* v_mvarId_600_, lean_object* v_x_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_600_, v_x_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_615_ == 0)
{
v___x_610_ = v___x_607_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_607_);
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
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
v_a_616_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___x_607_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_607_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___redArg___boxed(lean_object* v_mvarId_624_, lean_object* v_x_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___redArg(v_mvarId_624_, v_x_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2(lean_object* v_00_u03b1_632_, lean_object* v_mvarId_633_, lean_object* v_x_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___redArg(v_mvarId_633_, v_x_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___boxed(lean_object* v_00_u03b1_641_, lean_object* v_mvarId_642_, lean_object* v_x_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2(v_00_u03b1_641_, v_mvarId_642_, v_x_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__4_spec__5___redArg(lean_object* v_x_650_, lean_object* v_x_651_, lean_object* v_x_652_, lean_object* v_x_653_){
_start:
{
lean_object* v_ks_654_; lean_object* v_vs_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_679_; 
v_ks_654_ = lean_ctor_get(v_x_650_, 0);
v_vs_655_ = lean_ctor_get(v_x_650_, 1);
v_isSharedCheck_679_ = !lean_is_exclusive(v_x_650_);
if (v_isSharedCheck_679_ == 0)
{
v___x_657_ = v_x_650_;
v_isShared_658_ = v_isSharedCheck_679_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_vs_655_);
lean_inc(v_ks_654_);
lean_dec(v_x_650_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_679_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_659_ = lean_array_get_size(v_ks_654_);
v___x_660_ = lean_nat_dec_lt(v_x_651_, v___x_659_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_664_; 
lean_dec(v_x_651_);
v___x_661_ = lean_array_push(v_ks_654_, v_x_652_);
v___x_662_ = lean_array_push(v_vs_655_, v_x_653_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 1, v___x_662_);
lean_ctor_set(v___x_657_, 0, v___x_661_);
v___x_664_ = v___x_657_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_661_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v___x_662_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
else
{
lean_object* v_k_x27_666_; uint8_t v___x_667_; 
v_k_x27_666_ = lean_array_fget_borrowed(v_ks_654_, v_x_651_);
v___x_667_ = l_Lean_instBEqMVarId_beq(v_x_652_, v_k_x27_666_);
if (v___x_667_ == 0)
{
lean_object* v___x_669_; 
if (v_isShared_658_ == 0)
{
v___x_669_ = v___x_657_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_ks_654_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v_vs_655_);
v___x_669_ = v_reuseFailAlloc_673_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = lean_unsigned_to_nat(1u);
v___x_671_ = lean_nat_add(v_x_651_, v___x_670_);
lean_dec(v_x_651_);
v_x_650_ = v___x_669_;
v_x_651_ = v___x_671_;
goto _start;
}
}
else
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_677_; 
v___x_674_ = lean_array_fset(v_ks_654_, v_x_651_, v_x_652_);
v___x_675_ = lean_array_fset(v_vs_655_, v_x_651_, v_x_653_);
lean_dec(v_x_651_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 1, v___x_675_);
lean_ctor_set(v___x_657_, 0, v___x_674_);
v___x_677_ = v___x_657_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_674_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v___x_675_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_n_680_, lean_object* v_k_681_, lean_object* v_v_682_){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = lean_unsigned_to_nat(0u);
v___x_684_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__4_spec__5___redArg(v_n_680_, v___x_683_, v_k_681_, v_v_682_);
return v___x_684_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3___redArg(lean_object* v_x_686_, size_t v_x_687_, size_t v_x_688_, lean_object* v_x_689_, lean_object* v_x_690_){
_start:
{
if (lean_obj_tag(v_x_686_) == 0)
{
lean_object* v_es_691_; size_t v___x_692_; size_t v___x_693_; lean_object* v_j_694_; lean_object* v___x_695_; uint8_t v___x_696_; 
v_es_691_ = lean_ctor_get(v_x_686_, 0);
v___x_692_ = ((size_t)31ULL);
v___x_693_ = lean_usize_land(v_x_687_, v___x_692_);
v_j_694_ = lean_usize_to_nat(v___x_693_);
v___x_695_ = lean_array_get_size(v_es_691_);
v___x_696_ = lean_nat_dec_lt(v_j_694_, v___x_695_);
if (v___x_696_ == 0)
{
lean_dec(v_j_694_);
lean_dec(v_x_690_);
lean_dec(v_x_689_);
return v_x_686_;
}
else
{
lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_735_; 
lean_inc_ref(v_es_691_);
v_isSharedCheck_735_ = !lean_is_exclusive(v_x_686_);
if (v_isSharedCheck_735_ == 0)
{
lean_object* v_unused_736_; 
v_unused_736_ = lean_ctor_get(v_x_686_, 0);
lean_dec(v_unused_736_);
v___x_698_ = v_x_686_;
v_isShared_699_ = v_isSharedCheck_735_;
goto v_resetjp_697_;
}
else
{
lean_dec(v_x_686_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_735_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v_v_700_; lean_object* v___x_701_; lean_object* v_xs_x27_702_; lean_object* v___y_704_; 
v_v_700_ = lean_array_fget(v_es_691_, v_j_694_);
v___x_701_ = lean_box(0);
v_xs_x27_702_ = lean_array_fset(v_es_691_, v_j_694_, v___x_701_);
switch(lean_obj_tag(v_v_700_))
{
case 0:
{
lean_object* v_key_709_; lean_object* v_val_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_720_; 
v_key_709_ = lean_ctor_get(v_v_700_, 0);
v_val_710_ = lean_ctor_get(v_v_700_, 1);
v_isSharedCheck_720_ = !lean_is_exclusive(v_v_700_);
if (v_isSharedCheck_720_ == 0)
{
v___x_712_ = v_v_700_;
v_isShared_713_ = v_isSharedCheck_720_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_val_710_);
lean_inc(v_key_709_);
lean_dec(v_v_700_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_720_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
uint8_t v___x_714_; 
v___x_714_ = l_Lean_instBEqMVarId_beq(v_x_689_, v_key_709_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; lean_object* v___x_716_; 
lean_del_object(v___x_712_);
v___x_715_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_709_, v_val_710_, v_x_689_, v_x_690_);
v___x_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_716_, 0, v___x_715_);
v___y_704_ = v___x_716_;
goto v___jp_703_;
}
else
{
lean_object* v___x_718_; 
lean_dec(v_val_710_);
lean_dec(v_key_709_);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 1, v_x_690_);
lean_ctor_set(v___x_712_, 0, v_x_689_);
v___x_718_ = v___x_712_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_x_689_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v_x_690_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
v___y_704_ = v___x_718_;
goto v___jp_703_;
}
}
}
}
case 1:
{
lean_object* v_node_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_733_; 
v_node_721_ = lean_ctor_get(v_v_700_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v_v_700_);
if (v_isSharedCheck_733_ == 0)
{
v___x_723_ = v_v_700_;
v_isShared_724_ = v_isSharedCheck_733_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_node_721_);
lean_dec(v_v_700_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_733_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
size_t v___x_725_; size_t v___x_726_; size_t v___x_727_; size_t v___x_728_; lean_object* v___x_729_; lean_object* v___x_731_; 
v___x_725_ = ((size_t)5ULL);
v___x_726_ = lean_usize_shift_right(v_x_687_, v___x_725_);
v___x_727_ = ((size_t)1ULL);
v___x_728_ = lean_usize_add(v_x_688_, v___x_727_);
v___x_729_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3___redArg(v_node_721_, v___x_726_, v___x_728_, v_x_689_, v_x_690_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 0, v___x_729_);
v___x_731_ = v___x_723_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_729_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
v___y_704_ = v___x_731_;
goto v___jp_703_;
}
}
}
default: 
{
lean_object* v___x_734_; 
v___x_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_734_, 0, v_x_689_);
lean_ctor_set(v___x_734_, 1, v_x_690_);
v___y_704_ = v___x_734_;
goto v___jp_703_;
}
}
v___jp_703_:
{
lean_object* v___x_705_; lean_object* v___x_707_; 
v___x_705_ = lean_array_fset(v_xs_x27_702_, v_j_694_, v___y_704_);
lean_dec(v_j_694_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v___x_705_);
v___x_707_ = v___x_698_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_705_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
}
else
{
lean_object* v_ks_737_; lean_object* v_vs_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_756_; 
v_ks_737_ = lean_ctor_get(v_x_686_, 0);
v_vs_738_ = lean_ctor_get(v_x_686_, 1);
v_isSharedCheck_756_ = !lean_is_exclusive(v_x_686_);
if (v_isSharedCheck_756_ == 0)
{
v___x_740_ = v_x_686_;
v_isShared_741_ = v_isSharedCheck_756_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_vs_738_);
lean_inc(v_ks_737_);
lean_dec(v_x_686_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_756_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_ks_737_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v_vs_738_);
v___x_743_ = v_reuseFailAlloc_755_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
lean_object* v_newNode_744_; size_t v___x_745_; uint8_t v___x_746_; 
v_newNode_744_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__4___redArg(v___x_743_, v_x_689_, v_x_690_);
v___x_745_ = ((size_t)7ULL);
v___x_746_ = lean_usize_dec_le(v___x_745_, v_x_688_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; lean_object* v___x_748_; uint8_t v___x_749_; 
v___x_747_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_744_);
v___x_748_ = lean_unsigned_to_nat(4u);
v___x_749_ = lean_nat_dec_lt(v___x_747_, v___x_748_);
lean_dec(v___x_747_);
if (v___x_749_ == 0)
{
lean_object* v_ks_750_; lean_object* v_vs_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v_ks_750_ = lean_ctor_get(v_newNode_744_, 0);
lean_inc_ref(v_ks_750_);
v_vs_751_ = lean_ctor_get(v_newNode_744_, 1);
lean_inc_ref(v_vs_751_);
lean_dec_ref(v_newNode_744_);
v___x_752_ = lean_unsigned_to_nat(0u);
v___x_753_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3___redArg___closed__0);
v___x_754_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__5___redArg(v_x_688_, v_ks_750_, v_vs_751_, v___x_752_, v___x_753_);
lean_dec_ref(v_vs_751_);
lean_dec_ref(v_ks_750_);
return v___x_754_;
}
else
{
return v_newNode_744_;
}
}
else
{
return v_newNode_744_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__5___redArg(size_t v_depth_757_, lean_object* v_keys_758_, lean_object* v_vals_759_, lean_object* v_i_760_, lean_object* v_entries_761_){
_start:
{
lean_object* v___x_762_; uint8_t v___x_763_; 
v___x_762_ = lean_array_get_size(v_keys_758_);
v___x_763_ = lean_nat_dec_lt(v_i_760_, v___x_762_);
if (v___x_763_ == 0)
{
lean_dec(v_i_760_);
return v_entries_761_;
}
else
{
lean_object* v_k_764_; lean_object* v_v_765_; uint64_t v___x_766_; size_t v_h_767_; size_t v___x_768_; lean_object* v___x_769_; size_t v___x_770_; size_t v___x_771_; size_t v___x_772_; size_t v_h_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v_k_764_ = lean_array_fget_borrowed(v_keys_758_, v_i_760_);
v_v_765_ = lean_array_fget_borrowed(v_vals_759_, v_i_760_);
v___x_766_ = l_Lean_instHashableMVarId_hash(v_k_764_);
v_h_767_ = lean_uint64_to_usize(v___x_766_);
v___x_768_ = ((size_t)5ULL);
v___x_769_ = lean_unsigned_to_nat(1u);
v___x_770_ = ((size_t)1ULL);
v___x_771_ = lean_usize_sub(v_depth_757_, v___x_770_);
v___x_772_ = lean_usize_mul(v___x_768_, v___x_771_);
v_h_773_ = lean_usize_shift_right(v_h_767_, v___x_772_);
v___x_774_ = lean_nat_add(v_i_760_, v___x_769_);
lean_dec(v_i_760_);
lean_inc(v_v_765_);
lean_inc(v_k_764_);
v___x_775_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3___redArg(v_entries_761_, v_h_773_, v_depth_757_, v_k_764_, v_v_765_);
v_i_760_ = v___x_774_;
v_entries_761_ = v___x_775_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__5___redArg___boxed(lean_object* v_depth_777_, lean_object* v_keys_778_, lean_object* v_vals_779_, lean_object* v_i_780_, lean_object* v_entries_781_){
_start:
{
size_t v_depth_boxed_782_; lean_object* v_res_783_; 
v_depth_boxed_782_ = lean_unbox_usize(v_depth_777_);
lean_dec(v_depth_777_);
v_res_783_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__5___redArg(v_depth_boxed_782_, v_keys_778_, v_vals_779_, v_i_780_, v_entries_781_);
lean_dec_ref(v_vals_779_);
lean_dec_ref(v_keys_778_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_x_784_, lean_object* v_x_785_, lean_object* v_x_786_, lean_object* v_x_787_, lean_object* v_x_788_){
_start:
{
size_t v_x_7889__boxed_789_; size_t v_x_7890__boxed_790_; lean_object* v_res_791_; 
v_x_7889__boxed_789_ = lean_unbox_usize(v_x_785_);
lean_dec(v_x_785_);
v_x_7890__boxed_790_ = lean_unbox_usize(v_x_786_);
lean_dec(v_x_786_);
v_res_791_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3___redArg(v_x_784_, v_x_7889__boxed_789_, v_x_7890__boxed_790_, v_x_787_, v_x_788_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0___redArg(lean_object* v_x_792_, lean_object* v_x_793_, lean_object* v_x_794_){
_start:
{
uint64_t v___x_795_; size_t v___x_796_; size_t v___x_797_; lean_object* v___x_798_; 
v___x_795_ = l_Lean_instHashableMVarId_hash(v_x_793_);
v___x_796_ = lean_uint64_to_usize(v___x_795_);
v___x_797_ = ((size_t)1ULL);
v___x_798_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3___redArg(v_x_792_, v___x_796_, v___x_797_, v_x_793_, v_x_794_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0___redArg(lean_object* v_mvarId_799_, lean_object* v_val_800_, lean_object* v___y_801_){
_start:
{
lean_object* v___x_803_; lean_object* v_mctx_804_; lean_object* v_cache_805_; lean_object* v_zetaDeltaFVarIds_806_; lean_object* v_postponed_807_; lean_object* v_diag_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_838_; 
v___x_803_ = lean_st_ref_take(v___y_801_);
v_mctx_804_ = lean_ctor_get(v___x_803_, 0);
v_cache_805_ = lean_ctor_get(v___x_803_, 1);
v_zetaDeltaFVarIds_806_ = lean_ctor_get(v___x_803_, 2);
v_postponed_807_ = lean_ctor_get(v___x_803_, 3);
v_diag_808_ = lean_ctor_get(v___x_803_, 4);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_838_ == 0)
{
v___x_810_ = v___x_803_;
v_isShared_811_ = v_isSharedCheck_838_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_diag_808_);
lean_inc(v_postponed_807_);
lean_inc(v_zetaDeltaFVarIds_806_);
lean_inc(v_cache_805_);
lean_inc(v_mctx_804_);
lean_dec(v___x_803_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_838_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v_depth_812_; lean_object* v_levelAssignDepth_813_; lean_object* v_lmvarCounter_814_; lean_object* v_mvarCounter_815_; lean_object* v_lDecls_816_; lean_object* v_decls_817_; lean_object* v_userNames_818_; lean_object* v_lAssignment_819_; lean_object* v_eAssignment_820_; lean_object* v_dAssignment_821_; lean_object* v_instanceTypedMVars_822_; lean_object* v_synthNormMemo_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_837_; 
v_depth_812_ = lean_ctor_get(v_mctx_804_, 0);
v_levelAssignDepth_813_ = lean_ctor_get(v_mctx_804_, 1);
v_lmvarCounter_814_ = lean_ctor_get(v_mctx_804_, 2);
v_mvarCounter_815_ = lean_ctor_get(v_mctx_804_, 3);
v_lDecls_816_ = lean_ctor_get(v_mctx_804_, 4);
v_decls_817_ = lean_ctor_get(v_mctx_804_, 5);
v_userNames_818_ = lean_ctor_get(v_mctx_804_, 6);
v_lAssignment_819_ = lean_ctor_get(v_mctx_804_, 7);
v_eAssignment_820_ = lean_ctor_get(v_mctx_804_, 8);
v_dAssignment_821_ = lean_ctor_get(v_mctx_804_, 9);
v_instanceTypedMVars_822_ = lean_ctor_get(v_mctx_804_, 10);
v_synthNormMemo_823_ = lean_ctor_get(v_mctx_804_, 11);
v_isSharedCheck_837_ = !lean_is_exclusive(v_mctx_804_);
if (v_isSharedCheck_837_ == 0)
{
v___x_825_ = v_mctx_804_;
v_isShared_826_ = v_isSharedCheck_837_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_synthNormMemo_823_);
lean_inc(v_instanceTypedMVars_822_);
lean_inc(v_dAssignment_821_);
lean_inc(v_eAssignment_820_);
lean_inc(v_lAssignment_819_);
lean_inc(v_userNames_818_);
lean_inc(v_decls_817_);
lean_inc(v_lDecls_816_);
lean_inc(v_mvarCounter_815_);
lean_inc(v_lmvarCounter_814_);
lean_inc(v_levelAssignDepth_813_);
lean_inc(v_depth_812_);
lean_dec(v_mctx_804_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_837_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_830_; 
v___x_827_ = lean_box(0);
v___x_828_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0___redArg(v_eAssignment_820_, v_mvarId_799_, v_val_800_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 8, v___x_828_);
v___x_830_ = v___x_825_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_depth_812_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v_levelAssignDepth_813_);
lean_ctor_set(v_reuseFailAlloc_836_, 2, v_lmvarCounter_814_);
lean_ctor_set(v_reuseFailAlloc_836_, 3, v_mvarCounter_815_);
lean_ctor_set(v_reuseFailAlloc_836_, 4, v_lDecls_816_);
lean_ctor_set(v_reuseFailAlloc_836_, 5, v_decls_817_);
lean_ctor_set(v_reuseFailAlloc_836_, 6, v_userNames_818_);
lean_ctor_set(v_reuseFailAlloc_836_, 7, v_lAssignment_819_);
lean_ctor_set(v_reuseFailAlloc_836_, 8, v___x_828_);
lean_ctor_set(v_reuseFailAlloc_836_, 9, v_dAssignment_821_);
lean_ctor_set(v_reuseFailAlloc_836_, 10, v_instanceTypedMVars_822_);
lean_ctor_set(v_reuseFailAlloc_836_, 11, v_synthNormMemo_823_);
v___x_830_ = v_reuseFailAlloc_836_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
lean_object* v___x_832_; 
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v___x_830_);
v___x_832_ = v___x_810_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_830_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v_cache_805_);
lean_ctor_set(v_reuseFailAlloc_835_, 2, v_zetaDeltaFVarIds_806_);
lean_ctor_set(v_reuseFailAlloc_835_, 3, v_postponed_807_);
lean_ctor_set(v_reuseFailAlloc_835_, 4, v_diag_808_);
v___x_832_ = v_reuseFailAlloc_835_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_833_ = lean_st_ref_put(v___y_801_, v___x_832_);
v___x_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_834_, 0, v___x_827_);
return v___x_834_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0___redArg___boxed(lean_object* v_mvarId_839_, lean_object* v_val_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0___redArg(v_mvarId_839_, v_val_840_, v___y_841_);
lean_dec(v___y_841_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__0(uint8_t v___x_851_, lean_object* v_mvarId_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_b_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v___x_861_; lean_object* v_env_862_; lean_object* v___x_863_; lean_object* v_fst_865_; lean_object* v_fst_866_; lean_object* v_snd_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; uint8_t v___x_974_; 
v___x_861_ = lean_st_ref_get(v___y_859_);
v_env_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc_ref(v_env_862_);
lean_dec(v___x_861_);
v___x_863_ = ((lean_object*)(l_Lean_Meta_unifyEq_x3f___lam__0___closed__3));
v___x_974_ = l_Lean_Environment_contains(v_env_862_, v___x_863_, v___x_851_);
if (v___x_974_ == 0)
{
lean_object* v___x_975_; lean_object* v___x_976_; 
lean_dec_ref(v_b_855_);
lean_dec_ref(v_a_854_);
lean_dec_ref(v_a_853_);
lean_dec(v_mvarId_852_);
v___x_975_ = lean_box(0);
v___x_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
return v___x_976_;
}
else
{
lean_object* v___x_977_; 
v___x_977_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f(v_a_854_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_1044_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_980_ = v___x_977_;
v_isShared_981_ = v_isSharedCheck_1044_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_977_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_1044_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
if (lean_obj_tag(v_a_978_) == 1)
{
lean_object* v_val_982_; lean_object* v_fst_983_; lean_object* v_snd_984_; lean_object* v___x_985_; 
v_val_982_ = lean_ctor_get(v_a_978_, 0);
lean_inc(v_val_982_);
lean_dec_ref_known(v_a_978_, 1);
v_fst_983_ = lean_ctor_get(v_val_982_, 0);
lean_inc(v_fst_983_);
v_snd_984_ = lean_ctor_get(v_val_982_, 1);
lean_inc(v_snd_984_);
lean_dec(v_val_982_);
v___x_985_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f(v_b_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1031_; 
v_a_986_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_988_ = v___x_985_;
v_isShared_989_ = v_isSharedCheck_1031_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_985_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1031_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
if (lean_obj_tag(v_a_986_) == 1)
{
lean_object* v_val_995_; lean_object* v_fst_996_; lean_object* v_snd_997_; lean_object* v___x_998_; uint8_t v___x_999_; 
lean_del_object(v___x_980_);
v_val_995_ = lean_ctor_get(v_a_986_, 0);
lean_inc(v_val_995_);
lean_dec_ref_known(v_a_986_, 1);
v_fst_996_ = lean_ctor_get(v_val_995_, 0);
lean_inc(v_fst_996_);
v_snd_997_ = lean_ctor_get(v_val_995_, 1);
lean_inc(v_snd_997_);
lean_dec(v_val_995_);
v___x_998_ = lean_unsigned_to_nat(0u);
v___x_999_ = lean_nat_dec_eq(v_snd_984_, v___x_998_);
if (v___x_999_ == 0)
{
uint8_t v___x_1000_; 
v___x_1000_ = lean_nat_dec_eq(v_snd_997_, v___x_998_);
if (v___x_1000_ == 0)
{
uint8_t v___x_1001_; 
lean_del_object(v___x_988_);
v___x_1001_ = lean_nat_dec_lt(v_snd_984_, v_snd_997_);
if (v___x_1001_ == 0)
{
uint8_t v___x_1002_; 
v___x_1002_ = lean_nat_dec_eq(v_snd_984_, v_snd_997_);
if (v___x_1002_ == 0)
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1003_ = lean_nat_sub(v_snd_984_, v_snd_997_);
lean_dec(v_snd_984_);
v___x_1004_ = l_Lean_mkNatLit(v___x_1003_);
v___x_1005_ = l_Lean_Meta_mkAdd(v_fst_983_, v___x_1004_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_a_1006_);
lean_dec_ref_known(v___x_1005_, 1);
v_fst_865_ = v_a_1006_;
v_fst_866_ = v_fst_996_;
v_snd_867_ = v_snd_997_;
v___y_868_ = v___y_856_;
v___y_869_ = v___y_857_;
v___y_870_ = v___y_858_;
v___y_871_ = v___y_859_;
goto v___jp_864_;
}
else
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
lean_dec(v_snd_997_);
lean_dec(v_fst_996_);
lean_dec_ref(v_a_853_);
lean_dec(v_mvarId_852_);
v_a_1007_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_1005_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_1005_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1007_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
else
{
lean_dec(v_snd_997_);
v_fst_865_ = v_fst_983_;
v_fst_866_ = v_fst_996_;
v_snd_867_ = v_snd_984_;
v___y_868_ = v___y_856_;
v___y_869_ = v___y_857_;
v___y_870_ = v___y_858_;
v___y_871_ = v___y_859_;
goto v___jp_864_;
}
}
else
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1015_ = lean_nat_sub(v_snd_997_, v_snd_984_);
lean_dec(v_snd_997_);
v___x_1016_ = l_Lean_mkNatLit(v___x_1015_);
v___x_1017_ = l_Lean_Meta_mkAdd(v_fst_996_, v___x_1016_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v_a_1018_; 
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc(v_a_1018_);
lean_dec_ref_known(v___x_1017_, 1);
v_fst_865_ = v_fst_983_;
v_fst_866_ = v_a_1018_;
v_snd_867_ = v_snd_984_;
v___y_868_ = v___y_856_;
v___y_869_ = v___y_857_;
v___y_870_ = v___y_858_;
v___y_871_ = v___y_859_;
goto v___jp_864_;
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
lean_dec(v_snd_984_);
lean_dec(v_fst_983_);
lean_dec_ref(v_a_853_);
lean_dec(v_mvarId_852_);
v_a_1019_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_1017_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1017_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
}
else
{
lean_dec(v_snd_997_);
lean_dec(v_fst_996_);
lean_dec(v_snd_984_);
lean_dec(v_fst_983_);
lean_dec_ref(v_a_853_);
lean_dec(v_mvarId_852_);
goto v___jp_990_;
}
}
else
{
lean_dec(v_snd_997_);
lean_dec(v_fst_996_);
lean_dec(v_snd_984_);
lean_dec(v_fst_983_);
lean_dec_ref(v_a_853_);
lean_dec(v_mvarId_852_);
goto v___jp_990_;
}
}
else
{
lean_object* v___x_1027_; lean_object* v___x_1029_; 
lean_del_object(v___x_988_);
lean_dec(v_a_986_);
lean_dec(v_snd_984_);
lean_dec(v_fst_983_);
lean_dec_ref(v_a_853_);
lean_dec(v_mvarId_852_);
v___x_1027_ = lean_box(0);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 0, v___x_1027_);
v___x_1029_ = v___x_980_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1027_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
v___jp_990_:
{
lean_object* v___x_991_; lean_object* v___x_993_; 
v___x_991_ = lean_box(0);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 0, v___x_991_);
v___x_993_ = v___x_988_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_991_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
lean_dec(v_snd_984_);
lean_dec(v_fst_983_);
lean_del_object(v___x_980_);
lean_dec_ref(v_a_853_);
lean_dec(v_mvarId_852_);
v_a_1032_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_985_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_985_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1032_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
else
{
lean_object* v___x_1040_; lean_object* v___x_1042_; 
lean_dec(v_a_978_);
lean_dec_ref(v_b_855_);
lean_dec_ref(v_a_853_);
lean_dec(v_mvarId_852_);
v___x_1040_ = lean_box(0);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 0, v___x_1040_);
v___x_1042_ = v___x_980_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1040_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
else
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
lean_dec_ref(v_b_855_);
lean_dec_ref(v_a_853_);
lean_dec(v_mvarId_852_);
v_a_1045_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___x_977_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_977_);
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
v___jp_864_:
{
lean_object* v___x_872_; 
lean_inc(v_mvarId_852_);
v___x_872_ = l_Lean_MVarId_getType(v_mvarId_852_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v_a_873_; lean_object* v___x_874_; 
v_a_873_ = lean_ctor_get(v___x_872_, 0);
lean_inc_n(v_a_873_, 2);
lean_dec_ref_known(v___x_872_, 1);
v___x_874_ = l_Lean_Meta_getLevel(v_a_873_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; lean_object* v___x_876_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_a_875_);
lean_dec_ref_known(v___x_874_, 1);
lean_inc_ref(v_fst_866_);
lean_inc_ref(v_fst_865_);
v___x_876_ = l_Lean_Meta_mkEq(v_fst_865_, v_fst_866_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v___x_878_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_a_877_);
lean_dec_ref_known(v___x_876_, 1);
lean_inc(v_a_873_);
v___x_878_ = l_Lean_mkArrow(v_a_877_, v_a_873_, v___y_870_, v___y_871_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; lean_object* v___x_880_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
lean_inc(v_a_879_);
lean_dec_ref_known(v___x_878_, 1);
lean_inc(v_mvarId_852_);
v___x_880_ = l_Lean_MVarId_getTag(v_mvarId_852_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; lean_object* v___x_882_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_a_881_);
lean_dec_ref_known(v___x_880_, 1);
v___x_882_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_879_, v_a_881_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_924_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc_n(v_a_883_, 2);
lean_dec_ref_known(v___x_882_, 1);
v___x_884_ = lean_box(0);
v___x_885_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_885_, 0, v_a_875_);
lean_ctor_set(v___x_885_, 1, v___x_884_);
v___x_886_ = l_Lean_mkConst(v___x_863_, v___x_885_);
v___x_887_ = l_Lean_mkNatLit(v_snd_867_);
lean_inc_ref(v_a_853_);
v___x_888_ = l_Lean_LocalDecl_toExpr(v_a_853_);
v___x_889_ = lean_unsigned_to_nat(6u);
v___x_890_ = lean_mk_empty_array_with_capacity(v___x_889_);
v___x_891_ = lean_array_push(v___x_890_, v_a_873_);
v___x_892_ = lean_array_push(v___x_891_, v_fst_865_);
v___x_893_ = lean_array_push(v___x_892_, v_fst_866_);
v___x_894_ = lean_array_push(v___x_893_, v___x_887_);
v___x_895_ = lean_array_push(v___x_894_, v___x_888_);
v___x_896_ = lean_array_push(v___x_895_, v_a_883_);
v___x_897_ = l_Lean_mkAppN(v___x_886_, v___x_896_);
lean_dec_ref(v___x_896_);
v___x_898_ = l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0___redArg(v_mvarId_852_, v___x_897_, v___y_869_);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_924_ == 0)
{
lean_object* v_unused_925_; 
v_unused_925_ = lean_ctor_get(v___x_898_, 0);
lean_dec(v_unused_925_);
v___x_900_ = v___x_898_;
v_isShared_901_ = v_isSharedCheck_924_;
goto v_resetjp_899_;
}
else
{
lean_dec(v___x_898_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_924_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_902_ = l_Lean_Expr_mvarId_x21(v_a_883_);
lean_dec(v_a_883_);
v___x_903_ = l_Lean_LocalDecl_fvarId(v_a_853_);
lean_dec_ref(v_a_853_);
v___x_904_ = l_Lean_MVarId_tryClear(v___x_902_, v___x_903_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_915_; 
v_a_905_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_915_ == 0)
{
v___x_907_ = v___x_904_;
v_isShared_908_ = v_isSharedCheck_915_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_904_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_915_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_901_ == 0)
{
lean_ctor_set_tag(v___x_900_, 1);
lean_ctor_set(v___x_900_, 0, v_a_905_);
v___x_910_ = v___x_900_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_a_905_);
v___x_910_ = v_reuseFailAlloc_914_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
lean_object* v___x_912_; 
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 0, v___x_910_);
v___x_912_ = v___x_907_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_910_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
else
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
lean_del_object(v___x_900_);
v_a_916_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_923_ == 0)
{
v___x_918_ = v___x_904_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_904_);
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
}
else
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
lean_dec(v_a_875_);
lean_dec(v_a_873_);
lean_dec(v_snd_867_);
lean_dec_ref(v_fst_866_);
lean_dec_ref(v_fst_865_);
lean_dec_ref(v_a_853_);
lean_dec(v_mvarId_852_);
v_a_926_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_882_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_882_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
else
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_941_; 
lean_dec(v_a_879_);
lean_dec(v_a_875_);
lean_dec(v_a_873_);
lean_dec(v_snd_867_);
lean_dec_ref(v_fst_866_);
lean_dec_ref(v_fst_865_);
lean_dec_ref(v_a_853_);
lean_dec(v_mvarId_852_);
v_a_934_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_941_ == 0)
{
v___x_936_ = v___x_880_;
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_880_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_934_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
lean_dec(v_a_875_);
lean_dec(v_a_873_);
lean_dec(v_snd_867_);
lean_dec_ref(v_fst_866_);
lean_dec_ref(v_fst_865_);
lean_dec_ref(v_a_853_);
lean_dec(v_mvarId_852_);
v_a_942_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_878_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_878_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
else
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
lean_dec(v_a_875_);
lean_dec(v_a_873_);
lean_dec(v_snd_867_);
lean_dec_ref(v_fst_866_);
lean_dec_ref(v_fst_865_);
lean_dec_ref(v_a_853_);
lean_dec(v_mvarId_852_);
v_a_950_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___x_876_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_876_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_950_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
else
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
lean_dec(v_a_873_);
lean_dec(v_snd_867_);
lean_dec_ref(v_fst_866_);
lean_dec_ref(v_fst_865_);
lean_dec_ref(v_a_853_);
lean_dec(v_mvarId_852_);
v_a_958_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_874_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_874_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
else
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
lean_dec(v_snd_867_);
lean_dec_ref(v_fst_866_);
lean_dec_ref(v_fst_865_);
lean_dec_ref(v_a_853_);
lean_dec(v_mvarId_852_);
v_a_966_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_973_ == 0)
{
v___x_968_ = v___x_872_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_872_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__0___boxed(lean_object* v___x_1053_, lean_object* v_mvarId_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_b_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
uint8_t v___x_8112__boxed_1063_; lean_object* v_res_1064_; 
v___x_8112__boxed_1063_ = lean_unbox(v___x_1053_);
v_res_1064_ = l_Lean_Meta_unifyEq_x3f___lam__0(v___x_8112__boxed_1063_, v_mvarId_1054_, v_a_1055_, v_a_1056_, v_b_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
return v_res_1064_;
}
}
static lean_object* _init_l_Lean_Meta_unifyEq_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = ((lean_object*)(l_Lean_Meta_unifyEq_x3f___lam__1___closed__2));
v___x_1070_ = l_Lean_stringToMessageData(v___x_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__1(lean_object* v_eqFVarId_1071_, lean_object* v_mvarId_1072_, lean_object* v_subst_1073_, lean_object* v_acyclic_1074_, lean_object* v_caseName_x3f_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v___x_1081_; 
lean_inc(v_eqFVarId_1071_);
v___x_1081_ = l_Lean_FVarId_getDecl___redArg(v_eqFVarId_1071_, v___y_1076_, v___y_1078_, v___y_1079_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; lean_object* v___x_1083_; uint8_t v___x_1084_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_a_1082_);
lean_dec_ref_known(v___x_1081_, 1);
v___x_1083_ = l_Lean_LocalDecl_type(v_a_1082_);
v___x_1084_ = l_Lean_Expr_isHEq(v___x_1083_);
if (v___x_1084_ == 0)
{
lean_object* v___x_1085_; lean_object* v___x_1086_; uint8_t v___x_1087_; 
v___x_1085_ = ((lean_object*)(l_Lean_Meta_unifyEq_x3f___lam__1___closed__1));
v___x_1086_ = lean_unsigned_to_nat(3u);
v___x_1087_ = l_Lean_Expr_isAppOfArity(v___x_1083_, v___x_1085_, v___x_1086_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
lean_dec(v_a_1082_);
lean_dec(v_caseName_x3f_1075_);
lean_dec_ref(v_acyclic_1074_);
lean_dec(v_subst_1073_);
lean_dec(v_mvarId_1072_);
lean_dec(v_eqFVarId_1071_);
v___x_1088_ = lean_obj_once(&l_Lean_Meta_unifyEq_x3f___lam__1___closed__3, &l_Lean_Meta_unifyEq_x3f___lam__1___closed__3_once, _init_l_Lean_Meta_unifyEq_x3f___lam__1___closed__3);
v___x_1089_ = l_Lean_indentExpr(v___x_1083_);
v___x_1090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1088_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
v___x_1091_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(v___x_1090_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
return v___x_1091_;
}
else
{
lean_object* v___x_1092_; lean_object* v___f_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v_a_1098_; lean_object* v___x_1099_; 
v___x_1092_ = lean_box(v___x_1087_);
lean_inc(v_a_1082_);
lean_inc(v_mvarId_1072_);
v___f_1093_ = lean_alloc_closure((void*)(l_Lean_Meta_unifyEq_x3f___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1093_, 0, v___x_1092_);
lean_closure_set(v___f_1093_, 1, v_mvarId_1072_);
lean_closure_set(v___f_1093_, 2, v_a_1082_);
v___x_1094_ = l_Lean_Expr_appFn_x21(v___x_1083_);
v___x_1095_ = l_Lean_Expr_appArg_x21(v___x_1094_);
lean_dec_ref(v___x_1094_);
v___x_1096_ = l_Lean_Expr_appArg_x21(v___x_1083_);
lean_dec_ref(v___x_1083_);
lean_inc_ref(v___x_1095_);
v___x_1097_ = l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__1___redArg(v___x_1095_, v___y_1077_);
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc(v_a_1098_);
lean_dec_ref(v___x_1097_);
lean_inc_ref(v___x_1096_);
v___x_1099_ = l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__1___redArg(v___x_1096_, v___y_1077_);
if (lean_obj_tag(v_a_1098_) == 1)
{
lean_object* v_a_1100_; 
lean_dec_ref(v___f_1093_);
lean_dec(v_caseName_x3f_1075_);
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_a_1100_);
lean_dec_ref(v___x_1099_);
if (lean_obj_tag(v_a_1100_) == 1)
{
lean_object* v_fvarId_1101_; lean_object* v_fvarId_1102_; lean_object* v___x_1103_; 
v_fvarId_1101_ = lean_ctor_get(v_a_1098_, 0);
lean_inc(v_fvarId_1101_);
lean_dec_ref_known(v_a_1098_, 1);
v_fvarId_1102_ = lean_ctor_get(v_a_1100_, 0);
lean_inc(v_fvarId_1102_);
lean_dec_ref_known(v_a_1100_, 1);
v___x_1103_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1101_, v___y_1076_, v___y_1078_, v___y_1079_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v_a_1104_; lean_object* v___x_1105_; 
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
lean_inc(v_a_1104_);
lean_dec_ref_known(v___x_1103_, 1);
v___x_1105_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1102_, v___y_1076_, v___y_1078_, v___y_1079_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_a_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; uint8_t v___x_1109_; lean_object* v___x_1110_; 
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_a_1106_);
lean_dec_ref_known(v___x_1105_, 1);
v___x_1107_ = l_Lean_LocalDecl_index(v_a_1104_);
lean_dec(v_a_1104_);
v___x_1108_ = l_Lean_LocalDecl_index(v_a_1106_);
lean_dec(v_a_1106_);
v___x_1109_ = lean_nat_dec_lt(v___x_1107_, v___x_1108_);
lean_dec(v___x_1108_);
lean_dec(v___x_1107_);
v___x_1110_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq(v_mvarId_1072_, v_eqFVarId_1071_, v_subst_1073_, v_acyclic_1074_, v_a_1082_, v___x_1095_, v___x_1096_, v___x_1109_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
lean_dec(v_a_1082_);
return v___x_1110_;
}
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_dec(v_a_1104_);
lean_dec_ref(v___x_1096_);
lean_dec_ref(v___x_1095_);
lean_dec(v_a_1082_);
lean_dec_ref(v_acyclic_1074_);
lean_dec(v_subst_1073_);
lean_dec(v_mvarId_1072_);
lean_dec(v_eqFVarId_1071_);
v_a_1111_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1105_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1105_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
else
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
lean_dec(v_fvarId_1102_);
lean_dec_ref(v___x_1096_);
lean_dec_ref(v___x_1095_);
lean_dec(v_a_1082_);
lean_dec_ref(v_acyclic_1074_);
lean_dec(v_subst_1073_);
lean_dec(v_mvarId_1072_);
lean_dec(v_eqFVarId_1071_);
v_a_1119_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___x_1103_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1103_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1119_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
else
{
lean_object* v___x_1127_; 
lean_dec_ref_known(v_a_1098_, 1);
lean_dec(v_a_1100_);
v___x_1127_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq(v_mvarId_1072_, v_eqFVarId_1071_, v_subst_1073_, v_acyclic_1074_, v_a_1082_, v___x_1095_, v___x_1096_, v___x_1084_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
lean_dec(v_a_1082_);
return v___x_1127_;
}
}
else
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1167_; 
v_a_1128_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1130_ = v___x_1099_;
v_isShared_1131_ = v_isSharedCheck_1167_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1099_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1167_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
if (lean_obj_tag(v_a_1128_) == 1)
{
lean_object* v___x_1132_; 
lean_dec_ref_known(v_a_1128_, 1);
lean_del_object(v___x_1130_);
lean_dec(v_a_1098_);
lean_dec_ref(v___f_1093_);
lean_dec(v_caseName_x3f_1075_);
v___x_1132_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq(v_mvarId_1072_, v_eqFVarId_1071_, v_subst_1073_, v_acyclic_1074_, v_a_1082_, v___x_1095_, v___x_1096_, v___x_1087_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
lean_dec(v_a_1082_);
return v___x_1132_;
}
else
{
lean_object* v___x_1133_; 
lean_dec_ref(v___x_1096_);
lean_dec_ref(v___x_1095_);
lean_dec_ref(v_acyclic_1074_);
lean_inc(v_a_1128_);
lean_inc(v_a_1098_);
v___x_1133_ = l_Lean_Meta_isExprDefEq(v_a_1098_, v_a_1128_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v_a_1134_; uint8_t v___x_1135_; 
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_a_1134_);
lean_dec_ref_known(v___x_1133_, 1);
v___x_1135_ = lean_unbox(v_a_1134_);
lean_dec(v_a_1134_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1136_; 
lean_del_object(v___x_1130_);
v___x_1136_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection(v_mvarId_1072_, v_eqFVarId_1071_, v_subst_1073_, v_caseName_x3f_1075_, v_a_1082_, v___f_1093_, v_a_1098_, v_a_1128_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
lean_dec(v_a_1082_);
return v___x_1136_;
}
else
{
lean_object* v___x_1137_; 
lean_dec(v_a_1128_);
lean_dec(v_a_1098_);
lean_dec_ref(v___f_1093_);
lean_dec(v_a_1082_);
lean_dec(v_caseName_x3f_1075_);
v___x_1137_ = l_Lean_MVarId_clear(v_mvarId_1072_, v_eqFVarId_1071_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1150_; 
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1140_ = v___x_1137_;
v_isShared_1141_ = v_isSharedCheck_1150_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1137_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1150_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1145_; 
v___x_1142_ = lean_unsigned_to_nat(0u);
v___x_1143_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1143_, 0, v_a_1138_);
lean_ctor_set(v___x_1143_, 1, v_subst_1073_);
lean_ctor_set(v___x_1143_, 2, v___x_1142_);
if (v_isShared_1131_ == 0)
{
lean_ctor_set_tag(v___x_1130_, 1);
lean_ctor_set(v___x_1130_, 0, v___x_1143_);
v___x_1145_ = v___x_1130_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1143_);
v___x_1145_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
lean_object* v___x_1147_; 
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 0, v___x_1145_);
v___x_1147_ = v___x_1140_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1145_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
else
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1158_; 
lean_del_object(v___x_1130_);
lean_dec(v_subst_1073_);
v_a_1151_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1153_ = v___x_1137_;
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1137_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1156_; 
if (v_isShared_1154_ == 0)
{
v___x_1156_ = v___x_1153_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_a_1151_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
}
else
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
lean_del_object(v___x_1130_);
lean_dec(v_a_1128_);
lean_dec(v_a_1098_);
lean_dec_ref(v___f_1093_);
lean_dec(v_a_1082_);
lean_dec(v_caseName_x3f_1075_);
lean_dec(v_subst_1073_);
lean_dec(v_mvarId_1072_);
lean_dec(v_eqFVarId_1071_);
v_a_1159_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v___x_1133_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1133_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1159_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_1168_; 
lean_dec_ref(v___x_1083_);
lean_dec(v_caseName_x3f_1075_);
lean_dec_ref(v_acyclic_1074_);
lean_dec(v_eqFVarId_1071_);
v___x_1168_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_heqToEq_x27(v_mvarId_1072_, v_a_1082_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
lean_dec(v_a_1082_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1179_; 
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1171_ = v___x_1168_;
v_isShared_1172_ = v_isSharedCheck_1179_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1168_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1179_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1173_ = lean_unsigned_to_nat(1u);
v___x_1174_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1174_, 0, v_a_1169_);
lean_ctor_set(v___x_1174_, 1, v_subst_1073_);
lean_ctor_set(v___x_1174_, 2, v___x_1173_);
v___x_1175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 0, v___x_1175_);
v___x_1177_ = v___x_1171_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1175_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
else
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
lean_dec(v_subst_1073_);
v_a_1180_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1168_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1168_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1180_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
}
else
{
lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1195_; 
lean_dec(v_caseName_x3f_1075_);
lean_dec_ref(v_acyclic_1074_);
lean_dec(v_subst_1073_);
lean_dec(v_mvarId_1072_);
lean_dec(v_eqFVarId_1071_);
v_a_1188_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1190_ = v___x_1081_;
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___x_1081_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1193_; 
if (v_isShared_1191_ == 0)
{
v___x_1193_ = v___x_1190_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1188_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__1___boxed(lean_object* v_eqFVarId_1196_, lean_object* v_mvarId_1197_, lean_object* v_subst_1198_, lean_object* v_acyclic_1199_, lean_object* v_caseName_x3f_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Lean_Meta_unifyEq_x3f___lam__1(v_eqFVarId_1196_, v_mvarId_1197_, v_subst_1198_, v_acyclic_1199_, v_caseName_x3f_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f(lean_object* v_mvarId_1207_, lean_object* v_eqFVarId_1208_, lean_object* v_subst_1209_, lean_object* v_acyclic_1210_, lean_object* v_caseName_x3f_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_){
_start:
{
lean_object* v___f_1217_; lean_object* v___x_1218_; 
lean_inc(v_mvarId_1207_);
v___f_1217_ = lean_alloc_closure((void*)(l_Lean_Meta_unifyEq_x3f___lam__1___boxed), 10, 5);
lean_closure_set(v___f_1217_, 0, v_eqFVarId_1208_);
lean_closure_set(v___f_1217_, 1, v_mvarId_1207_);
lean_closure_set(v___f_1217_, 2, v_subst_1209_);
lean_closure_set(v___f_1217_, 3, v_acyclic_1210_);
lean_closure_set(v___f_1217_, 4, v_caseName_x3f_1211_);
v___x_1218_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___redArg(v_mvarId_1207_, v___f_1217_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___boxed(lean_object* v_mvarId_1219_, lean_object* v_eqFVarId_1220_, lean_object* v_subst_1221_, lean_object* v_acyclic_1222_, lean_object* v_caseName_x3f_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_Lean_Meta_unifyEq_x3f(v_mvarId_1219_, v_eqFVarId_1220_, v_subst_1221_, v_acyclic_1222_, v_caseName_x3f_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_a_1225_);
lean_dec_ref(v_a_1224_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0(lean_object* v_mvarId_1230_, lean_object* v_val_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0___redArg(v_mvarId_1230_, v_val_1231_, v___y_1233_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0___boxed(lean_object* v_mvarId_1238_, lean_object* v_val_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0(v_mvarId_1238_, v_val_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1246_, lean_object* v_x_1247_, lean_object* v_x_1248_, lean_object* v_x_1249_){
_start:
{
lean_object* v___x_1250_; 
v___x_1250_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0___redArg(v_x_1247_, v_x_1248_, v_x_1249_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1251_, lean_object* v_x_1252_, size_t v_x_1253_, size_t v_x_1254_, lean_object* v_x_1255_, lean_object* v_x_1256_){
_start:
{
lean_object* v___x_1257_; 
v___x_1257_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3___redArg(v_x_1252_, v_x_1253_, v_x_1254_, v_x_1255_, v_x_1256_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1258_, lean_object* v_x_1259_, lean_object* v_x_1260_, lean_object* v_x_1261_, lean_object* v_x_1262_, lean_object* v_x_1263_){
_start:
{
size_t v_x_8823__boxed_1264_; size_t v_x_8824__boxed_1265_; lean_object* v_res_1266_; 
v_x_8823__boxed_1264_ = lean_unbox_usize(v_x_1260_);
lean_dec(v_x_1260_);
v_x_8824__boxed_1265_ = lean_unbox_usize(v_x_1261_);
lean_dec(v_x_1261_);
v_res_1266_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3(v_00_u03b2_1258_, v_x_1259_, v_x_8823__boxed_1264_, v_x_8824__boxed_1265_, v_x_1262_, v_x_1263_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_1267_, lean_object* v_n_1268_, lean_object* v_k_1269_, lean_object* v_v_1270_){
_start:
{
lean_object* v___x_1271_; 
v___x_1271_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__4___redArg(v_n_1268_, v_k_1269_, v_v_1270_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__5(lean_object* v_00_u03b2_1272_, size_t v_depth_1273_, lean_object* v_keys_1274_, lean_object* v_vals_1275_, lean_object* v_heq_1276_, lean_object* v_i_1277_, lean_object* v_entries_1278_){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__5___redArg(v_depth_1273_, v_keys_1274_, v_vals_1275_, v_i_1277_, v_entries_1278_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__5___boxed(lean_object* v_00_u03b2_1280_, lean_object* v_depth_1281_, lean_object* v_keys_1282_, lean_object* v_vals_1283_, lean_object* v_heq_1284_, lean_object* v_i_1285_, lean_object* v_entries_1286_){
_start:
{
size_t v_depth_boxed_1287_; lean_object* v_res_1288_; 
v_depth_boxed_1287_ = lean_unbox_usize(v_depth_1281_);
lean_dec(v_depth_1281_);
v_res_1288_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__5(v_00_u03b2_1280_, v_depth_boxed_1287_, v_keys_1282_, v_vals_1283_, v_heq_1284_, v_i_1285_, v_entries_1286_);
lean_dec_ref(v_vals_1283_);
lean_dec_ref(v_keys_1282_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_1289_, lean_object* v_x_1290_, lean_object* v_x_1291_, lean_object* v_x_1292_, lean_object* v_x_1293_){
_start:
{
lean_object* v___x_1294_; 
v___x_1294_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__4_spec__5___redArg(v_x_1290_, v_x_1291_, v_x_1292_, v_x_1293_);
return v___x_1294_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Injection(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_UnifyEq(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Injection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Internal_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_UnifyEq(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Injection(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_UnifyEq(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Injection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Internal_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_UnifyEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_UnifyEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_UnifyEq(builtin);
}
#ifdef __cplusplus
}
#endif
