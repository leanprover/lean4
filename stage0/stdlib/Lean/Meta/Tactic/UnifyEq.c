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
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
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
lean_object* l_Lean_Meta_injectionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isConstructorApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_heqToEq_x27(lean_object* v_mvarId_1_, lean_object* v_eqDecl_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_){
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_heqToEq_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1_ = stack[0].m_obj;
lean_object* v_eqDecl_2_ = stack[1].m_obj;
lean_object* v_a_3_ = stack[2].m_obj;
lean_object* v_a_4_ = stack[3].m_obj;
lean_object* v_a_5_ = stack[4].m_obj;
lean_object* v_a_6_ = stack[5].m_obj;
lean_object* v_res_45_;
v_res_45_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_heqToEq_x27(v_mvarId_1_, v_eqDecl_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_heqToEq_x27___boxed(lean_object* v_mvarId_46_, lean_object* v_eqDecl_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_heqToEq_x27(v_mvarId_46_, v_eqDecl_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_);
lean_dec(v_a_51_);
lean_dec_ref(v_a_50_);
lean_dec(v_a_49_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_eqDecl_47_);
return v_res_53_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f___closed__0(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = lean_unsigned_to_nat(0u);
v___x_55_ = l_Lean_mkNatLit(v___x_54_);
return v___x_55_;
}
}
lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f(lean_object* v_e_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_){
_start:
{
lean_object* v___x_62_; 
lean_inc_ref(v_e_56_);
v___x_62_ = l_Lean_Meta_evalNat(v_e_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_);
if (lean_obj_tag(v___x_62_) == 0)
{
lean_object* v_a_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_81_; 
v_a_63_ = lean_ctor_get(v___x_62_, 0);
v_isSharedCheck_81_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_81_ == 0)
{
v___x_65_ = v___x_62_;
v_isShared_66_ = v_isSharedCheck_81_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_a_63_);
lean_dec(v___x_62_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_81_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
if (lean_obj_tag(v_a_63_) == 0)
{
lean_object* v___x_67_; 
lean_del_object(v___x_65_);
v___x_67_ = l_Lean_Meta_isOffset_x3f(v_e_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_);
return v___x_67_;
}
else
{
lean_object* v_val_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_80_; 
lean_dec_ref(v_e_56_);
v_val_68_ = lean_ctor_get(v_a_63_, 0);
v_isSharedCheck_80_ = !lean_is_exclusive(v_a_63_);
if (v_isSharedCheck_80_ == 0)
{
v___x_70_ = v_a_63_;
v_isShared_71_ = v_isSharedCheck_80_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_val_68_);
lean_dec(v_a_63_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_80_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_75_; 
v___x_72_ = lean_obj_once(&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f___closed__0, &l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f___closed__0);
v___x_73_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set(v___x_73_, 1, v_val_68_);
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 0, v___x_73_);
v___x_75_ = v___x_70_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v___x_73_);
v___x_75_ = v_reuseFailAlloc_79_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
lean_object* v___x_77_; 
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 0, v___x_75_);
v___x_77_ = v___x_65_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v___x_75_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
return v___x_77_;
}
}
}
}
}
}
else
{
lean_object* v_a_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_89_; 
lean_dec_ref(v_e_56_);
v_a_82_ = lean_ctor_get(v___x_62_, 0);
v_isSharedCheck_89_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_89_ == 0)
{
v___x_84_ = v___x_62_;
v_isShared_85_ = v_isSharedCheck_89_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_a_82_);
lean_dec(v___x_62_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_89_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_87_; 
if (v_isShared_85_ == 0)
{
v___x_87_ = v___x_84_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v_a_82_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_56_ = stack[0].m_obj;
lean_object* v_a_57_ = stack[1].m_obj;
lean_object* v_a_58_ = stack[2].m_obj;
lean_object* v_a_59_ = stack[3].m_obj;
lean_object* v_a_60_ = stack[4].m_obj;
lean_object* v_res_90_;
v_res_90_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f(v_e_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_);
stack->m_obj
 = v_res_90_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f___boxed(lean_object* v_e_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f(v_e_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_);
lean_dec(v_a_95_);
lean_dec_ref(v_a_94_);
lean_dec(v_a_93_);
lean_dec_ref(v_a_92_);
return v_res_97_;
}
}
lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0___redArg(lean_object* v_x_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Lean_Meta_saveState___redArg(v___y_100_, v___y_102_);
if (lean_obj_tag(v___x_104_) == 0)
{
lean_object* v_a_105_; lean_object* v___x_106_; 
v_a_105_ = lean_ctor_get(v___x_104_, 0);
lean_inc(v_a_105_);
lean_dec_ref_known(v___x_104_, 1);
lean_inc(v___y_102_);
lean_inc_ref(v___y_101_);
lean_inc(v___y_100_);
lean_inc_ref(v___y_99_);
v___x_106_ = lean_apply_5(v_x_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_, lean_box(0));
if (lean_obj_tag(v___x_106_) == 0)
{
lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_115_; 
lean_dec(v_a_105_);
v_a_107_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_115_ == 0)
{
v___x_109_ = v___x_106_;
v_isShared_110_ = v_isSharedCheck_115_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_dec(v___x_106_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_115_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; lean_object* v___x_113_; 
v___x_111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_111_, 0, v_a_107_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 0, v___x_111_);
v___x_113_ = v___x_109_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v___x_111_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
else
{
lean_object* v_a_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_145_; 
v_a_116_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_145_ == 0)
{
v___x_118_ = v___x_106_;
v_isShared_119_ = v_isSharedCheck_145_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_dec(v___x_106_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_145_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
uint8_t v___y_121_; uint8_t v___x_143_; 
v___x_143_ = l_Lean_Exception_isInterrupt(v_a_116_);
if (v___x_143_ == 0)
{
uint8_t v___x_144_; 
lean_inc(v_a_116_);
v___x_144_ = l_Lean_Exception_isRuntime(v_a_116_);
v___y_121_ = v___x_144_;
goto v___jp_120_;
}
else
{
v___y_121_ = v___x_143_;
goto v___jp_120_;
}
v___jp_120_:
{
if (v___y_121_ == 0)
{
lean_object* v___x_122_; 
lean_del_object(v___x_118_);
lean_dec(v_a_116_);
v___x_122_ = l_Lean_Meta_SavedState_restore___redArg(v_a_105_, v___y_100_, v___y_102_);
if (lean_obj_tag(v___x_122_) == 0)
{
lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_130_; 
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_130_ == 0)
{
lean_object* v_unused_131_; 
v_unused_131_ = lean_ctor_get(v___x_122_, 0);
lean_dec(v_unused_131_);
v___x_124_ = v___x_122_;
v_isShared_125_ = v_isSharedCheck_130_;
goto v_resetjp_123_;
}
else
{
lean_dec(v___x_122_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_130_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_126_; lean_object* v___x_128_; 
v___x_126_ = lean_box(0);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 0, v___x_126_);
v___x_128_ = v___x_124_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v___x_126_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
else
{
lean_object* v_a_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_139_; 
v_a_132_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_139_ == 0)
{
v___x_134_ = v___x_122_;
v_isShared_135_ = v_isSharedCheck_139_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_a_132_);
lean_dec(v___x_122_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_139_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_137_; 
if (v_isShared_135_ == 0)
{
v___x_137_ = v___x_134_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_a_132_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
else
{
lean_object* v___x_141_; 
lean_dec(v_a_105_);
if (v_isShared_119_ == 0)
{
v___x_141_ = v___x_118_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_a_116_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
}
}
}
else
{
lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_153_; 
lean_dec_ref(v_x_98_);
v_a_146_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_153_ == 0)
{
v___x_148_ = v___x_104_;
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_dec(v___x_104_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_a_146_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_98_ = stack[0].m_obj;
lean_object* v___y_99_ = stack[1].m_obj;
lean_object* v___y_100_ = stack[2].m_obj;
lean_object* v___y_101_ = stack[3].m_obj;
lean_object* v___y_102_ = stack[4].m_obj;
lean_object* v_res_154_;
v_res_154_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0___redArg(v_x_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_);
stack->m_obj
 = v_res_154_;
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0___redArg___boxed(lean_object* v_x_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0___redArg(v_x_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_);
lean_dec(v___y_159_);
lean_dec_ref(v___y_158_);
lean_dec(v___y_157_);
lean_dec_ref(v___y_156_);
return v_res_161_;
}
}
lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0(lean_object* v_00_u03b1_162_, lean_object* v_x_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0___redArg(v_x_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_);
return v___x_169_;
}
}
LEAN_EXPORT void l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_163_ = stack[1].m_obj;
lean_object* v___y_164_ = stack[2].m_obj;
lean_object* v___y_165_ = stack[3].m_obj;
lean_object* v___y_166_ = stack[4].m_obj;
lean_object* v___y_167_ = stack[5].m_obj;
lean_object* v_res_170_;
v_res_170_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0(lean_box(0), v_x_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_);
stack->m_obj
 = v_res_170_;
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0___boxed(lean_object* v_00_u03b1_171_, lean_object* v_x_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0(v_00_u03b1_171_, v_x_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
return v_res_178_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1_spec__1(lean_object* v_msgData_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
lean_object* v___x_185_; lean_object* v_env_186_; uint8_t v___x_187_; lean_object* v_env_188_; lean_object* v___x_189_; lean_object* v_toCold_190_; lean_object* v_mctx_191_; lean_object* v_lctx_192_; lean_object* v_options_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_185_ = lean_st_ref_get(v___y_183_);
v_env_186_ = lean_ctor_get(v___x_185_, 0);
lean_inc_ref(v_env_186_);
lean_dec(v___x_185_);
v___x_187_ = 0;
v_env_188_ = l_Lean_Environment_setRecordingDeps(v_env_186_, v___x_187_);
v___x_189_ = lean_st_ref_get(v___y_181_);
v_toCold_190_ = lean_ctor_get(v___y_182_, 0);
v_mctx_191_ = lean_ctor_get(v___x_189_, 0);
lean_inc_ref(v_mctx_191_);
lean_dec(v___x_189_);
v_lctx_192_ = lean_ctor_get(v___y_180_, 2);
v_options_193_ = lean_ctor_get(v_toCold_190_, 2);
lean_inc_ref(v_options_193_);
lean_inc_ref(v_lctx_192_);
v___x_194_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_194_, 0, v_env_188_);
lean_ctor_set(v___x_194_, 1, v_mctx_191_);
lean_ctor_set(v___x_194_, 2, v_lctx_192_);
lean_ctor_set(v___x_194_, 3, v_options_193_);
v___x_195_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v_msgData_179_);
v___x_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
return v___x_196_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_179_ = stack[0].m_obj;
lean_object* v___y_180_ = stack[1].m_obj;
lean_object* v___y_181_ = stack[2].m_obj;
lean_object* v___y_182_ = stack[3].m_obj;
lean_object* v___y_183_ = stack[4].m_obj;
lean_object* v_res_197_;
v_res_197_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1_spec__1(v_msgData_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_);
stack->m_obj
 = v_res_197_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1_spec__1___boxed(lean_object* v_msgData_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1_spec__1(v_msgData_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
return v_res_204_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(lean_object* v_msg_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v_ref_211_; lean_object* v___x_212_; lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_221_; 
v_ref_211_ = lean_ctor_get(v___y_208_, 2);
v___x_212_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1_spec__1(v_msg_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_);
v_a_213_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_221_ == 0)
{
v___x_215_ = v___x_212_;
v_isShared_216_ = v_isSharedCheck_221_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_212_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_221_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_217_; lean_object* v___x_219_; 
lean_inc(v_ref_211_);
v___x_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_217_, 0, v_ref_211_);
lean_ctor_set(v___x_217_, 1, v_a_213_);
if (v_isShared_216_ == 0)
{
lean_ctor_set_tag(v___x_215_, 1);
lean_ctor_set(v___x_215_, 0, v___x_217_);
v___x_219_ = v___x_215_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v___x_217_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_205_ = stack[0].m_obj;
lean_object* v___y_206_ = stack[1].m_obj;
lean_object* v___y_207_ = stack[2].m_obj;
lean_object* v___y_208_ = stack[3].m_obj;
lean_object* v___y_209_ = stack[4].m_obj;
lean_object* v_res_222_;
v_res_222_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(v_msg_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_);
stack->m_obj
 = v_res_222_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg___boxed(lean_object* v_msg_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(v_msg_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
return v_res_229_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = ((lean_object*)(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__0));
v___x_232_ = l_Lean_stringToMessageData(v___x_231_);
return v___x_232_;
}
}
lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq(lean_object* v_mvarId_233_, lean_object* v_eqFVarId_234_, lean_object* v_subst_235_, lean_object* v_acyclic_236_, lean_object* v_eqDecl_237_, lean_object* v_a_238_, lean_object* v_b_239_, uint8_t v_symm_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_){
_start:
{
uint8_t v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_246_ = 1;
v___x_247_ = lean_box(v_symm_240_);
v___x_248_ = lean_box(v___x_246_);
v___x_249_ = lean_box(v___x_246_);
lean_inc(v_subst_235_);
lean_inc(v_eqFVarId_234_);
lean_inc(v_mvarId_233_);
v___x_250_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___boxed), 11, 6);
lean_closure_set(v___x_250_, 0, v_mvarId_233_);
lean_closure_set(v___x_250_, 1, v_eqFVarId_234_);
lean_closure_set(v___x_250_, 2, v___x_247_);
lean_closure_set(v___x_250_, 3, v_subst_235_);
lean_closure_set(v___x_250_, 4, v___x_248_);
lean_closure_set(v___x_250_, 5, v___x_249_);
v___x_251_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0___redArg(v___x_250_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
if (lean_obj_tag(v___x_251_) == 0)
{
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_327_; 
v_a_252_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_327_ == 0)
{
v___x_254_ = v___x_251_;
v_isShared_255_ = v_isSharedCheck_327_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_251_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_327_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
if (lean_obj_tag(v_a_252_) == 1)
{
lean_object* v_val_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_270_; 
lean_dec_ref(v_b_239_);
lean_dec_ref(v_a_238_);
lean_dec_ref(v_acyclic_236_);
lean_dec(v_subst_235_);
lean_dec(v_eqFVarId_234_);
lean_dec(v_mvarId_233_);
v_val_256_ = lean_ctor_get(v_a_252_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v_a_252_);
if (v_isSharedCheck_270_ == 0)
{
v___x_258_ = v_a_252_;
v_isShared_259_ = v_isSharedCheck_270_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_val_256_);
lean_dec(v_a_252_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_270_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v_fst_260_; lean_object* v_snd_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_265_; 
v_fst_260_ = lean_ctor_get(v_val_256_, 0);
lean_inc(v_fst_260_);
v_snd_261_ = lean_ctor_get(v_val_256_, 1);
lean_inc(v_snd_261_);
lean_dec(v_val_256_);
v___x_262_ = lean_unsigned_to_nat(0u);
v___x_263_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_263_, 0, v_snd_261_);
lean_ctor_set(v___x_263_, 1, v_fst_260_);
lean_ctor_set(v___x_263_, 2, v___x_262_);
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 0, v___x_263_);
v___x_265_ = v___x_258_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_263_);
v___x_265_ = v_reuseFailAlloc_269_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
lean_object* v___x_267_; 
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 0, v___x_265_);
v___x_267_ = v___x_254_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_265_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
else
{
lean_object* v___x_271_; 
lean_del_object(v___x_254_);
lean_dec(v_a_252_);
v___x_271_ = l_Lean_Meta_isExprDefEq(v_a_238_, v_b_239_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v_a_272_; uint8_t v___x_273_; 
v_a_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc(v_a_272_);
lean_dec_ref_known(v___x_271_, 1);
v___x_273_ = lean_unbox(v_a_272_);
lean_dec(v_a_272_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; lean_object* v___x_275_; 
lean_dec(v_subst_235_);
v___x_274_ = l_Lean_mkFVar(v_eqFVarId_234_);
lean_inc(v_a_244_);
lean_inc_ref(v_a_243_);
lean_inc(v_a_242_);
lean_inc_ref(v_a_241_);
v___x_275_ = lean_apply_7(v_acyclic_236_, v_mvarId_233_, v___x_274_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, lean_box(0));
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_290_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_290_ == 0)
{
v___x_278_ = v___x_275_;
v_isShared_279_ = v_isSharedCheck_290_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_275_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_290_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
uint8_t v___x_280_; 
v___x_280_ = lean_unbox(v_a_276_);
lean_dec(v_a_276_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
lean_del_object(v___x_278_);
v___x_281_ = lean_obj_once(&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1, &l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1_once, _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1);
v___x_282_ = l_Lean_LocalDecl_type(v_eqDecl_237_);
v___x_283_ = l_Lean_indentExpr(v___x_282_);
v___x_284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_281_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
v___x_285_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(v___x_284_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
return v___x_285_;
}
else
{
lean_object* v___x_286_; lean_object* v___x_288_; 
v___x_286_ = lean_box(0);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 0, v___x_286_);
v___x_288_ = v___x_278_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_286_);
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
v_a_291_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_298_ == 0)
{
v___x_293_ = v___x_275_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_275_);
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
lean_object* v___x_299_; 
lean_dec_ref(v_acyclic_236_);
v___x_299_ = l_Lean_MVarId_clear(v_mvarId_233_, v_eqFVarId_234_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_310_; 
v_a_300_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_310_ == 0)
{
v___x_302_ = v___x_299_;
v_isShared_303_ = v_isSharedCheck_310_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_299_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_310_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_308_; 
v___x_304_ = lean_unsigned_to_nat(0u);
v___x_305_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_305_, 0, v_a_300_);
lean_ctor_set(v___x_305_, 1, v_subst_235_);
lean_ctor_set(v___x_305_, 2, v___x_304_);
v___x_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 0, v___x_306_);
v___x_308_ = v___x_302_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v___x_306_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
else
{
lean_object* v_a_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_318_; 
lean_dec(v_subst_235_);
v_a_311_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_318_ == 0)
{
v___x_313_ = v___x_299_;
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_a_311_);
lean_dec(v___x_299_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_316_; 
if (v_isShared_314_ == 0)
{
v___x_316_ = v___x_313_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_a_311_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
}
else
{
lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_326_; 
lean_dec_ref(v_acyclic_236_);
lean_dec(v_subst_235_);
lean_dec(v_eqFVarId_234_);
lean_dec(v_mvarId_233_);
v_a_319_ = lean_ctor_get(v___x_271_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_326_ == 0)
{
v___x_321_ = v___x_271_;
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v___x_271_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_322_ == 0)
{
v___x_324_ = v___x_321_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_a_319_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
}
}
else
{
lean_object* v_a_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_335_; 
lean_dec_ref(v_b_239_);
lean_dec_ref(v_a_238_);
lean_dec_ref(v_acyclic_236_);
lean_dec(v_subst_235_);
lean_dec(v_eqFVarId_234_);
lean_dec(v_mvarId_233_);
v_a_328_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_335_ == 0)
{
v___x_330_ = v___x_251_;
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_a_328_);
lean_dec(v___x_251_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
if (v_isShared_331_ == 0)
{
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_a_328_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_233_ = stack[0].m_obj;
lean_object* v_eqFVarId_234_ = stack[1].m_obj;
lean_object* v_subst_235_ = stack[2].m_obj;
lean_object* v_acyclic_236_ = stack[3].m_obj;
lean_object* v_eqDecl_237_ = stack[4].m_obj;
lean_object* v_a_238_ = stack[5].m_obj;
lean_object* v_b_239_ = stack[6].m_obj;
uint8_t v_symm_240_ = stack[7].m_num;
lean_object* v_a_241_ = stack[8].m_obj;
lean_object* v_a_242_ = stack[9].m_obj;
lean_object* v_a_243_ = stack[10].m_obj;
lean_object* v_a_244_ = stack[11].m_obj;
lean_object* v_res_336_;
v_res_336_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq(v_mvarId_233_, v_eqFVarId_234_, v_subst_235_, v_acyclic_236_, v_eqDecl_237_, v_a_238_, v_b_239_, v_symm_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
stack->m_obj
 = v_res_336_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___boxed(lean_object* v_mvarId_337_, lean_object* v_eqFVarId_338_, lean_object* v_subst_339_, lean_object* v_acyclic_340_, lean_object* v_eqDecl_341_, lean_object* v_a_342_, lean_object* v_b_343_, lean_object* v_symm_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_){
_start:
{
uint8_t v_symm_boxed_350_; lean_object* v_res_351_; 
v_symm_boxed_350_ = lean_unbox(v_symm_344_);
v_res_351_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq(v_mvarId_337_, v_eqFVarId_338_, v_subst_339_, v_acyclic_340_, v_eqDecl_341_, v_a_342_, v_b_343_, v_symm_boxed_350_, v_a_345_, v_a_346_, v_a_347_, v_a_348_);
lean_dec(v_a_348_);
lean_dec_ref(v_a_347_);
lean_dec(v_a_346_);
lean_dec_ref(v_a_345_);
lean_dec_ref(v_eqDecl_341_);
return v_res_351_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1(lean_object* v_00_u03b1_352_, lean_object* v_msg_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(v_msg_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
return v___x_359_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_353_ = stack[1].m_obj;
lean_object* v___y_354_ = stack[2].m_obj;
lean_object* v___y_355_ = stack[3].m_obj;
lean_object* v___y_356_ = stack[4].m_obj;
lean_object* v___y_357_ = stack[5].m_obj;
lean_object* v_res_360_;
v_res_360_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1(lean_box(0), v_msg_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
stack->m_obj
 = v_res_360_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___boxed(lean_object* v_00_u03b1_361_, lean_object* v_msg_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1(v_00_u03b1_361_, v_msg_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
return v_res_368_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__1(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = ((lean_object*)(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__0));
v___x_371_ = l_Lean_stringToMessageData(v___x_370_);
return v___x_371_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__3(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = ((lean_object*)(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__2));
v___x_374_ = l_Lean_stringToMessageData(v___x_373_);
return v___x_374_;
}
}
lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection(lean_object* v_mvarId_375_, lean_object* v_eqFVarId_376_, lean_object* v_subst_377_, lean_object* v_caseName_x3f_378_, lean_object* v_eqDecl_379_, lean_object* v_injectionOffset_x3f_380_, lean_object* v_a_381_, lean_object* v_b_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_){
_start:
{
lean_object* v___y_389_; lean_object* v___y_390_; lean_object* v___y_434_; lean_object* v___x_510_; 
lean_inc(v_a_386_);
lean_inc_ref(v_a_385_);
lean_inc(v_a_384_);
lean_inc_ref(v_a_383_);
lean_inc_ref(v_b_382_);
lean_inc_ref(v_a_381_);
v___x_510_ = lean_apply_7(v_injectionOffset_x3f_380_, v_a_381_, v_b_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, lean_box(0));
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_532_; 
v_a_511_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_532_ == 0)
{
v___x_513_ = v___x_510_;
v_isShared_514_ = v_isSharedCheck_532_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_510_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_532_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
if (lean_obj_tag(v_a_511_) == 1)
{
lean_object* v_val_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_527_; 
lean_dec_ref(v_b_382_);
lean_dec_ref(v_a_381_);
lean_dec(v_caseName_x3f_378_);
lean_dec(v_eqFVarId_376_);
lean_dec(v_mvarId_375_);
v_val_515_ = lean_ctor_get(v_a_511_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v_a_511_);
if (v_isSharedCheck_527_ == 0)
{
v___x_517_ = v_a_511_;
v_isShared_518_ = v_isSharedCheck_527_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_val_515_);
lean_dec(v_a_511_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_527_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_522_; 
v___x_519_ = lean_unsigned_to_nat(1u);
v___x_520_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_520_, 0, v_val_515_);
lean_ctor_set(v___x_520_, 1, v_subst_377_);
lean_ctor_set(v___x_520_, 2, v___x_519_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v___x_520_);
v___x_522_ = v___x_517_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_520_);
v___x_522_ = v_reuseFailAlloc_526_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_524_; 
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 0, v___x_522_);
v___x_524_ = v___x_513_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_522_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
else
{
lean_object* v___x_528_; 
lean_del_object(v___x_513_);
lean_dec(v_a_511_);
lean_inc_ref(v_a_381_);
v___x_528_ = l_Lean_Meta_isConstructorApp(v_a_381_, v_a_383_, v_a_384_, v_a_385_, v_a_386_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v_a_529_; uint8_t v___x_530_; 
v_a_529_ = lean_ctor_get(v___x_528_, 0);
v___x_530_ = lean_unbox(v_a_529_);
if (v___x_530_ == 0)
{
v___y_434_ = v___x_528_;
goto v___jp_433_;
}
else
{
lean_object* v___x_531_; 
lean_dec_ref_known(v___x_528_, 1);
lean_inc_ref(v_b_382_);
v___x_531_ = l_Lean_Meta_isConstructorApp(v_b_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_);
v___y_434_ = v___x_531_;
goto v___jp_433_;
}
}
else
{
v___y_434_ = v___x_528_;
goto v___jp_433_;
}
}
}
}
else
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_540_; 
lean_dec_ref(v_b_382_);
lean_dec_ref(v_a_381_);
lean_dec(v_caseName_x3f_378_);
lean_dec(v_subst_377_);
lean_dec(v_eqFVarId_376_);
lean_dec(v_mvarId_375_);
v_a_533_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_540_ == 0)
{
v___x_535_ = v___x_510_;
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_510_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_533_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
v___jp_388_:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
lean_inc(v_eqFVarId_376_);
v___x_391_ = l_Lean_mkFVar(v_eqFVarId_376_);
v___x_392_ = l_Lean_Meta_mkEq(v___y_389_, v___y_390_, v_a_383_, v_a_384_, v_a_385_, v_a_386_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v_a_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v_a_393_ = lean_ctor_get(v___x_392_, 0);
lean_inc(v_a_393_);
lean_dec_ref_known(v___x_392_, 1);
v___x_394_ = l_Lean_LocalDecl_userName(v_eqDecl_379_);
v___x_395_ = l_Lean_MVarId_assert(v_mvarId_375_, v___x_394_, v_a_393_, v___x_391_, v_a_383_, v_a_384_, v_a_385_, v_a_386_);
if (lean_obj_tag(v___x_395_) == 0)
{
lean_object* v_a_396_; lean_object* v___x_397_; 
v_a_396_ = lean_ctor_get(v___x_395_, 0);
lean_inc(v_a_396_);
lean_dec_ref_known(v___x_395_, 1);
v___x_397_ = l_Lean_MVarId_clear(v_a_396_, v_eqFVarId_376_, v_a_383_, v_a_384_, v_a_385_, v_a_386_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_408_; 
v_a_398_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_408_ == 0)
{
v___x_400_ = v___x_397_;
v_isShared_401_ = v_isSharedCheck_408_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_397_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_408_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_402_ = lean_unsigned_to_nat(1u);
v___x_403_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_403_, 0, v_a_398_);
lean_ctor_set(v___x_403_, 1, v_subst_377_);
lean_ctor_set(v___x_403_, 2, v___x_402_);
v___x_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v___x_404_);
v___x_406_ = v___x_400_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_404_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
else
{
lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_416_; 
lean_dec(v_subst_377_);
v_a_409_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_416_ == 0)
{
v___x_411_ = v___x_397_;
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_dec(v___x_397_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_414_; 
if (v_isShared_412_ == 0)
{
v___x_414_ = v___x_411_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_a_409_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
}
else
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_424_; 
lean_dec(v_subst_377_);
lean_dec(v_eqFVarId_376_);
v_a_417_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_424_ == 0)
{
v___x_419_ = v___x_395_;
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_395_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_422_; 
if (v_isShared_420_ == 0)
{
v___x_422_ = v___x_419_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_a_417_);
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
else
{
lean_object* v_a_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_432_; 
lean_dec_ref(v___x_391_);
lean_dec(v_subst_377_);
lean_dec(v_eqFVarId_376_);
lean_dec(v_mvarId_375_);
v_a_425_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_432_ == 0)
{
v___x_427_ = v___x_392_;
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_dec(v___x_392_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_430_; 
if (v_isShared_428_ == 0)
{
v___x_430_ = v___x_427_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_a_425_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
v___jp_433_:
{
if (lean_obj_tag(v___y_434_) == 0)
{
lean_object* v_a_435_; uint8_t v___x_436_; 
v_a_435_ = lean_ctor_get(v___y_434_, 0);
lean_inc(v_a_435_);
lean_dec_ref_known(v___y_434_, 1);
v___x_436_ = lean_unbox(v_a_435_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; 
lean_inc(v_a_386_);
lean_inc_ref(v_a_385_);
lean_inc(v_a_384_);
lean_inc_ref(v_a_383_);
lean_inc_ref(v_a_381_);
v___x_437_ = lean_whnf(v_a_381_, v_a_383_, v_a_384_, v_a_385_, v_a_386_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v___x_439_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_a_438_);
lean_dec_ref_known(v___x_437_, 1);
lean_inc(v_a_386_);
lean_inc_ref(v_a_385_);
lean_inc(v_a_384_);
lean_inc_ref(v_a_383_);
lean_inc_ref(v_b_382_);
v___x_439_ = lean_whnf(v_b_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; uint8_t v___x_441_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_a_440_);
lean_dec_ref_known(v___x_439_, 1);
v___x_441_ = lean_expr_eqv(v_a_438_, v_a_381_);
lean_dec_ref(v_a_381_);
if (v___x_441_ == 0)
{
lean_dec(v_a_435_);
lean_dec_ref(v_b_382_);
lean_dec(v_caseName_x3f_378_);
v___y_389_ = v_a_438_;
v___y_390_ = v_a_440_;
goto v___jp_388_;
}
else
{
uint8_t v___x_442_; 
v___x_442_ = lean_expr_eqv(v_a_440_, v_b_382_);
lean_dec_ref(v_b_382_);
if (v___x_442_ == 0)
{
lean_dec(v_a_435_);
lean_dec(v_caseName_x3f_378_);
v___y_389_ = v_a_438_;
v___y_390_ = v_a_440_;
goto v___jp_388_;
}
else
{
lean_dec(v_a_440_);
lean_dec(v_a_438_);
lean_dec(v_subst_377_);
lean_dec(v_eqFVarId_376_);
lean_dec(v_mvarId_375_);
if (lean_obj_tag(v_caseName_x3f_378_) == 0)
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
lean_dec(v_a_435_);
v___x_443_ = lean_obj_once(&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1, &l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1_once, _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1);
v___x_444_ = l_Lean_LocalDecl_type(v_eqDecl_379_);
v___x_445_ = l_Lean_indentExpr(v___x_444_);
v___x_446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_446_, 0, v___x_443_);
lean_ctor_set(v___x_446_, 1, v___x_445_);
v___x_447_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(v___x_446_, v_a_383_, v_a_384_, v_a_385_, v_a_386_);
return v___x_447_;
}
else
{
lean_object* v_val_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; uint8_t v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v_val_448_ = lean_ctor_get(v_caseName_x3f_378_, 0);
lean_inc(v_val_448_);
lean_dec_ref_known(v_caseName_x3f_378_, 1);
v___x_449_ = lean_obj_once(&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1, &l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1_once, _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1);
v___x_450_ = l_Lean_LocalDecl_type(v_eqDecl_379_);
v___x_451_ = l_Lean_indentExpr(v___x_450_);
v___x_452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_452_, 0, v___x_449_);
lean_ctor_set(v___x_452_, 1, v___x_451_);
v___x_453_ = lean_obj_once(&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__1, &l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__1_once, _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__1);
v___x_454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_452_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
v___x_455_ = lean_unbox(v_a_435_);
lean_dec(v_a_435_);
v___x_456_ = l_Lean_MessageData_ofConstName(v_val_448_, v___x_455_);
v___x_457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_454_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
v___x_458_ = lean_obj_once(&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__3, &l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__3_once, _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__3);
v___x_459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_457_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
v___x_460_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(v___x_459_, v_a_383_, v_a_384_, v_a_385_, v_a_386_);
return v___x_460_;
}
}
}
}
else
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
lean_dec(v_a_438_);
lean_dec(v_a_435_);
lean_dec_ref(v_b_382_);
lean_dec_ref(v_a_381_);
lean_dec(v_caseName_x3f_378_);
lean_dec(v_subst_377_);
lean_dec(v_eqFVarId_376_);
lean_dec(v_mvarId_375_);
v_a_461_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_468_ == 0)
{
v___x_463_ = v___x_439_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_439_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_461_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
else
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_476_; 
lean_dec(v_a_435_);
lean_dec_ref(v_b_382_);
lean_dec_ref(v_a_381_);
lean_dec(v_caseName_x3f_378_);
lean_dec(v_subst_377_);
lean_dec(v_eqFVarId_376_);
lean_dec(v_mvarId_375_);
v_a_469_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_476_ == 0)
{
v___x_471_ = v___x_437_;
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_437_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_474_; 
if (v_isShared_472_ == 0)
{
v___x_474_ = v___x_471_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_469_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
else
{
lean_object* v___x_477_; 
lean_dec(v_a_435_);
lean_dec_ref(v_b_382_);
lean_dec_ref(v_a_381_);
lean_dec(v_caseName_x3f_378_);
v___x_477_ = l_Lean_Meta_injectionCore(v_mvarId_375_, v_eqFVarId_376_, v_a_383_, v_a_384_, v_a_385_, v_a_386_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_a_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_493_; 
v_a_478_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_493_ == 0)
{
v___x_480_ = v___x_477_;
v_isShared_481_ = v_isSharedCheck_493_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_a_478_);
lean_dec(v___x_477_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_493_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
if (lean_obj_tag(v_a_478_) == 0)
{
lean_object* v___x_482_; lean_object* v___x_484_; 
lean_dec(v_subst_377_);
v___x_482_ = lean_box(0);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 0, v___x_482_);
v___x_484_ = v___x_480_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v___x_482_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
else
{
lean_object* v_mvarId_486_; lean_object* v_numNewEqs_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_491_; 
v_mvarId_486_ = lean_ctor_get(v_a_478_, 0);
lean_inc(v_mvarId_486_);
v_numNewEqs_487_ = lean_ctor_get(v_a_478_, 1);
lean_inc(v_numNewEqs_487_);
lean_dec_ref_known(v_a_478_, 2);
v___x_488_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_488_, 0, v_mvarId_486_);
lean_ctor_set(v___x_488_, 1, v_subst_377_);
lean_ctor_set(v___x_488_, 2, v_numNewEqs_487_);
v___x_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 0, v___x_489_);
v___x_491_ = v___x_480_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_489_);
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
lean_dec(v_subst_377_);
v_a_494_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_477_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_477_);
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
}
else
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_509_; 
lean_dec_ref(v_b_382_);
lean_dec_ref(v_a_381_);
lean_dec(v_caseName_x3f_378_);
lean_dec(v_subst_377_);
lean_dec(v_eqFVarId_376_);
lean_dec(v_mvarId_375_);
v_a_502_ = lean_ctor_get(v___y_434_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___y_434_);
if (v_isSharedCheck_509_ == 0)
{
v___x_504_ = v___y_434_;
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___y_434_);
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
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_375_ = stack[0].m_obj;
lean_object* v_eqFVarId_376_ = stack[1].m_obj;
lean_object* v_subst_377_ = stack[2].m_obj;
lean_object* v_caseName_x3f_378_ = stack[3].m_obj;
lean_object* v_eqDecl_379_ = stack[4].m_obj;
lean_object* v_injectionOffset_x3f_380_ = stack[5].m_obj;
lean_object* v_a_381_ = stack[6].m_obj;
lean_object* v_b_382_ = stack[7].m_obj;
lean_object* v_a_383_ = stack[8].m_obj;
lean_object* v_a_384_ = stack[9].m_obj;
lean_object* v_a_385_ = stack[10].m_obj;
lean_object* v_a_386_ = stack[11].m_obj;
lean_object* v_res_541_;
v_res_541_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection(v_mvarId_375_, v_eqFVarId_376_, v_subst_377_, v_caseName_x3f_378_, v_eqDecl_379_, v_injectionOffset_x3f_380_, v_a_381_, v_b_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_);
stack->m_obj
 = v_res_541_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___boxed(lean_object* v_mvarId_542_, lean_object* v_eqFVarId_543_, lean_object* v_subst_544_, lean_object* v_caseName_x3f_545_, lean_object* v_eqDecl_546_, lean_object* v_injectionOffset_x3f_547_, lean_object* v_a_548_, lean_object* v_b_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection(v_mvarId_542_, v_eqFVarId_543_, v_subst_544_, v_caseName_x3f_545_, v_eqDecl_546_, v_injectionOffset_x3f_547_, v_a_548_, v_b_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_);
lean_dec(v_a_553_);
lean_dec_ref(v_a_552_);
lean_dec(v_a_551_);
lean_dec_ref(v_a_550_);
lean_dec_ref(v_eqDecl_546_);
return v_res_555_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__1___redArg(lean_object* v_e_556_, lean_object* v___y_557_){
_start:
{
uint8_t v___x_559_; 
v___x_559_ = l_Lean_Expr_hasMVar(v_e_556_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; 
v___x_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_560_, 0, v_e_556_);
return v___x_560_;
}
else
{
lean_object* v___x_561_; lean_object* v_mctx_562_; lean_object* v___x_563_; lean_object* v_fst_564_; lean_object* v_snd_565_; lean_object* v___x_566_; lean_object* v_cache_567_; lean_object* v_zetaDeltaFVarIds_568_; lean_object* v_postponed_569_; lean_object* v_diag_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_579_; 
v___x_561_ = lean_st_ref_get(v___y_557_);
v_mctx_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc_ref(v_mctx_562_);
lean_dec(v___x_561_);
v___x_563_ = l_Lean_instantiateMVarsCore(v_mctx_562_, v_e_556_);
v_fst_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_fst_564_);
v_snd_565_ = lean_ctor_get(v___x_563_, 1);
lean_inc(v_snd_565_);
lean_dec_ref(v___x_563_);
v___x_566_ = lean_st_ref_take(v___y_557_);
v_cache_567_ = lean_ctor_get(v___x_566_, 1);
v_zetaDeltaFVarIds_568_ = lean_ctor_get(v___x_566_, 2);
v_postponed_569_ = lean_ctor_get(v___x_566_, 3);
v_diag_570_ = lean_ctor_get(v___x_566_, 4);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_579_ == 0)
{
lean_object* v_unused_580_; 
v_unused_580_ = lean_ctor_get(v___x_566_, 0);
lean_dec(v_unused_580_);
v___x_572_ = v___x_566_;
v_isShared_573_ = v_isSharedCheck_579_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_diag_570_);
lean_inc(v_postponed_569_);
lean_inc(v_zetaDeltaFVarIds_568_);
lean_inc(v_cache_567_);
lean_dec(v___x_566_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_579_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 0, v_snd_565_);
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_snd_565_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v_cache_567_);
lean_ctor_set(v_reuseFailAlloc_578_, 2, v_zetaDeltaFVarIds_568_);
lean_ctor_set(v_reuseFailAlloc_578_, 3, v_postponed_569_);
lean_ctor_set(v_reuseFailAlloc_578_, 4, v_diag_570_);
v___x_575_ = v_reuseFailAlloc_578_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = lean_st_ref_put(v___y_557_, v___x_575_);
v___x_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_577_, 0, v_fst_564_);
return v___x_577_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_556_ = stack[0].m_obj;
lean_object* v___y_557_ = stack[1].m_obj;
lean_object* v_res_581_;
v_res_581_ = l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__1___redArg(v_e_556_, v___y_557_);
stack->m_obj
 = v_res_581_;
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
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__1(lean_object* v_e_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__1___redArg(v_e_586_, v___y_588_);
return v___x_592_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_586_ = stack[0].m_obj;
lean_object* v___y_587_ = stack[1].m_obj;
lean_object* v___y_588_ = stack[2].m_obj;
lean_object* v___y_589_ = stack[3].m_obj;
lean_object* v___y_590_ = stack[4].m_obj;
lean_object* v_res_593_;
v_res_593_ = l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__1(v_e_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
stack->m_obj
 = v_res_593_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__1___boxed(lean_object* v_e_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__1(v_e_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
return v_res_600_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___redArg(lean_object* v_mvarId_601_, lean_object* v_x_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_601_, v_x_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
v_a_609_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_616_ == 0)
{
v___x_611_ = v___x_608_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_608_);
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
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_624_; 
v_a_617_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_624_ == 0)
{
v___x_619_ = v___x_608_;
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_dec(v___x_608_);
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
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_601_ = stack[0].m_obj;
lean_object* v_x_602_ = stack[1].m_obj;
lean_object* v___y_603_ = stack[2].m_obj;
lean_object* v___y_604_ = stack[3].m_obj;
lean_object* v___y_605_ = stack[4].m_obj;
lean_object* v___y_606_ = stack[5].m_obj;
lean_object* v_res_625_;
v_res_625_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___redArg(v_mvarId_601_, v_x_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
stack->m_obj
 = v_res_625_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___redArg___boxed(lean_object* v_mvarId_626_, lean_object* v_x_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___redArg(v_mvarId_626_, v_x_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
return v_res_633_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2(lean_object* v_00_u03b1_634_, lean_object* v_mvarId_635_, lean_object* v_x_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___redArg(v_mvarId_635_, v_x_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
return v___x_642_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_635_ = stack[1].m_obj;
lean_object* v_x_636_ = stack[2].m_obj;
lean_object* v___y_637_ = stack[3].m_obj;
lean_object* v___y_638_ = stack[4].m_obj;
lean_object* v___y_639_ = stack[5].m_obj;
lean_object* v___y_640_ = stack[6].m_obj;
lean_object* v_res_643_;
v_res_643_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2(lean_box(0), v_mvarId_635_, v_x_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
stack->m_obj
 = v_res_643_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___boxed(lean_object* v_00_u03b1_644_, lean_object* v_mvarId_645_, lean_object* v_x_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2(v_00_u03b1_644_, v_mvarId_645_, v_x_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__4_spec__5___redArg(lean_object* v_x_653_, lean_object* v_x_654_, lean_object* v_x_655_, lean_object* v_x_656_){
_start:
{
lean_object* v_ks_657_; lean_object* v_vs_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_682_; 
v_ks_657_ = lean_ctor_get(v_x_653_, 0);
v_vs_658_ = lean_ctor_get(v_x_653_, 1);
v_isSharedCheck_682_ = !lean_is_exclusive(v_x_653_);
if (v_isSharedCheck_682_ == 0)
{
v___x_660_ = v_x_653_;
v_isShared_661_ = v_isSharedCheck_682_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_vs_658_);
lean_inc(v_ks_657_);
lean_dec(v_x_653_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_682_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_662_ = lean_array_get_size(v_ks_657_);
v___x_663_ = lean_nat_dec_lt(v_x_654_, v___x_662_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_667_; 
lean_dec(v_x_654_);
v___x_664_ = lean_array_push(v_ks_657_, v_x_655_);
v___x_665_ = lean_array_push(v_vs_658_, v_x_656_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 1, v___x_665_);
lean_ctor_set(v___x_660_, 0, v___x_664_);
v___x_667_ = v___x_660_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_664_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v___x_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
else
{
lean_object* v_k_x27_669_; uint8_t v___x_670_; 
v_k_x27_669_ = lean_array_fget_borrowed(v_ks_657_, v_x_654_);
v___x_670_ = l_Lean_instBEqMVarId_beq(v_x_655_, v_k_x27_669_);
if (v___x_670_ == 0)
{
lean_object* v___x_672_; 
if (v_isShared_661_ == 0)
{
v___x_672_ = v___x_660_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_ks_657_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v_vs_658_);
v___x_672_ = v_reuseFailAlloc_676_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_unsigned_to_nat(1u);
v___x_674_ = lean_nat_add(v_x_654_, v___x_673_);
lean_dec(v_x_654_);
v_x_653_ = v___x_672_;
v_x_654_ = v___x_674_;
goto _start;
}
}
else
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_680_; 
v___x_677_ = lean_array_fset(v_ks_657_, v_x_654_, v_x_655_);
v___x_678_ = lean_array_fset(v_vs_658_, v_x_654_, v_x_656_);
lean_dec(v_x_654_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 1, v___x_678_);
lean_ctor_set(v___x_660_, 0, v___x_677_);
v___x_680_ = v___x_660_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_677_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v___x_678_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_n_683_, lean_object* v_k_684_, lean_object* v_v_685_){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = lean_unsigned_to_nat(0u);
v___x_687_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__4_spec__5___redArg(v_n_683_, v___x_686_, v_k_684_, v_v_685_);
return v___x_687_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_688_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3___redArg(lean_object* v_x_689_, size_t v_x_690_, size_t v_x_691_, lean_object* v_x_692_, lean_object* v_x_693_){
_start:
{
if (lean_obj_tag(v_x_689_) == 0)
{
lean_object* v_es_694_; size_t v___x_695_; size_t v___x_696_; lean_object* v_j_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
v_es_694_ = lean_ctor_get(v_x_689_, 0);
v___x_695_ = ((size_t)31ULL);
v___x_696_ = lean_usize_land(v_x_690_, v___x_695_);
v_j_697_ = lean_usize_to_nat(v___x_696_);
v___x_698_ = lean_array_get_size(v_es_694_);
v___x_699_ = lean_nat_dec_lt(v_j_697_, v___x_698_);
if (v___x_699_ == 0)
{
lean_dec(v_j_697_);
lean_dec(v_x_693_);
lean_dec(v_x_692_);
return v_x_689_;
}
else
{
lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_738_; 
lean_inc_ref(v_es_694_);
v_isSharedCheck_738_ = !lean_is_exclusive(v_x_689_);
if (v_isSharedCheck_738_ == 0)
{
lean_object* v_unused_739_; 
v_unused_739_ = lean_ctor_get(v_x_689_, 0);
lean_dec(v_unused_739_);
v___x_701_ = v_x_689_;
v_isShared_702_ = v_isSharedCheck_738_;
goto v_resetjp_700_;
}
else
{
lean_dec(v_x_689_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_738_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v_v_703_; lean_object* v___x_704_; lean_object* v_xs_x27_705_; lean_object* v___y_707_; 
v_v_703_ = lean_array_fget(v_es_694_, v_j_697_);
v___x_704_ = lean_box(0);
v_xs_x27_705_ = lean_array_fset(v_es_694_, v_j_697_, v___x_704_);
switch(lean_obj_tag(v_v_703_))
{
case 0:
{
lean_object* v_key_712_; lean_object* v_val_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_723_; 
v_key_712_ = lean_ctor_get(v_v_703_, 0);
v_val_713_ = lean_ctor_get(v_v_703_, 1);
v_isSharedCheck_723_ = !lean_is_exclusive(v_v_703_);
if (v_isSharedCheck_723_ == 0)
{
v___x_715_ = v_v_703_;
v_isShared_716_ = v_isSharedCheck_723_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_val_713_);
lean_inc(v_key_712_);
lean_dec(v_v_703_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_723_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
uint8_t v___x_717_; 
v___x_717_ = l_Lean_instBEqMVarId_beq(v_x_692_, v_key_712_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; lean_object* v___x_719_; 
lean_del_object(v___x_715_);
v___x_718_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_712_, v_val_713_, v_x_692_, v_x_693_);
v___x_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
v___y_707_ = v___x_719_;
goto v___jp_706_;
}
else
{
lean_object* v___x_721_; 
lean_dec(v_val_713_);
lean_dec(v_key_712_);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 1, v_x_693_);
lean_ctor_set(v___x_715_, 0, v_x_692_);
v___x_721_ = v___x_715_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_x_692_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_x_693_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
v___y_707_ = v___x_721_;
goto v___jp_706_;
}
}
}
}
case 1:
{
lean_object* v_node_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_736_; 
v_node_724_ = lean_ctor_get(v_v_703_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v_v_703_);
if (v_isSharedCheck_736_ == 0)
{
v___x_726_ = v_v_703_;
v_isShared_727_ = v_isSharedCheck_736_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_node_724_);
lean_dec(v_v_703_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_736_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
size_t v___x_728_; size_t v___x_729_; size_t v___x_730_; size_t v___x_731_; lean_object* v___x_732_; lean_object* v___x_734_; 
v___x_728_ = ((size_t)5ULL);
v___x_729_ = lean_usize_shift_right(v_x_690_, v___x_728_);
v___x_730_ = ((size_t)1ULL);
v___x_731_ = lean_usize_add(v_x_691_, v___x_730_);
v___x_732_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3___redArg(v_node_724_, v___x_729_, v___x_731_, v_x_692_, v_x_693_);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 0, v___x_732_);
v___x_734_ = v___x_726_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_732_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
v___y_707_ = v___x_734_;
goto v___jp_706_;
}
}
}
default: 
{
lean_object* v___x_737_; 
v___x_737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_737_, 0, v_x_692_);
lean_ctor_set(v___x_737_, 1, v_x_693_);
v___y_707_ = v___x_737_;
goto v___jp_706_;
}
}
v___jp_706_:
{
lean_object* v___x_708_; lean_object* v___x_710_; 
v___x_708_ = lean_array_fset(v_xs_x27_705_, v_j_697_, v___y_707_);
lean_dec(v_j_697_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 0, v___x_708_);
v___x_710_ = v___x_701_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_708_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
}
else
{
lean_object* v_ks_740_; lean_object* v_vs_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_759_; 
v_ks_740_ = lean_ctor_get(v_x_689_, 0);
v_vs_741_ = lean_ctor_get(v_x_689_, 1);
v_isSharedCheck_759_ = !lean_is_exclusive(v_x_689_);
if (v_isSharedCheck_759_ == 0)
{
v___x_743_ = v_x_689_;
v_isShared_744_ = v_isSharedCheck_759_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_vs_741_);
lean_inc(v_ks_740_);
lean_dec(v_x_689_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_759_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
if (v_isShared_744_ == 0)
{
v___x_746_ = v___x_743_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_ks_740_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v_vs_741_);
v___x_746_ = v_reuseFailAlloc_758_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
lean_object* v_newNode_747_; size_t v___x_748_; uint8_t v___x_749_; 
v_newNode_747_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__4___redArg(v___x_746_, v_x_692_, v_x_693_);
v___x_748_ = ((size_t)7ULL);
v___x_749_ = lean_usize_dec_le(v___x_748_, v_x_691_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_750_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_747_);
v___x_751_ = lean_unsigned_to_nat(4u);
v___x_752_ = lean_nat_dec_lt(v___x_750_, v___x_751_);
lean_dec(v___x_750_);
if (v___x_752_ == 0)
{
lean_object* v_ks_753_; lean_object* v_vs_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v_ks_753_ = lean_ctor_get(v_newNode_747_, 0);
lean_inc_ref(v_ks_753_);
v_vs_754_ = lean_ctor_get(v_newNode_747_, 1);
lean_inc_ref(v_vs_754_);
lean_dec_ref(v_newNode_747_);
v___x_755_ = lean_unsigned_to_nat(0u);
v___x_756_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3___redArg___closed__0);
v___x_757_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__5___redArg(v_x_691_, v_ks_753_, v_vs_754_, v___x_755_, v___x_756_);
lean_dec_ref(v_vs_754_);
lean_dec_ref(v_ks_753_);
return v___x_757_;
}
else
{
return v_newNode_747_;
}
}
else
{
return v_newNode_747_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_689_ = stack[0].m_obj;
size_t v_x_690_ = stack[1].m_num;
size_t v_x_691_ = stack[2].m_num;
lean_object* v_x_692_ = stack[3].m_obj;
lean_object* v_x_693_ = stack[4].m_obj;
lean_object* v_res_760_;
v_res_760_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3___redArg(v_x_689_, v_x_690_, v_x_691_, v_x_692_, v_x_693_);
stack->m_obj
 = v_res_760_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__5___redArg(size_t v_depth_761_, lean_object* v_keys_762_, lean_object* v_vals_763_, lean_object* v_i_764_, lean_object* v_entries_765_){
_start:
{
lean_object* v___x_766_; uint8_t v___x_767_; 
v___x_766_ = lean_array_get_size(v_keys_762_);
v___x_767_ = lean_nat_dec_lt(v_i_764_, v___x_766_);
if (v___x_767_ == 0)
{
lean_dec(v_i_764_);
return v_entries_765_;
}
else
{
lean_object* v_k_768_; lean_object* v_v_769_; uint64_t v___x_770_; size_t v_h_771_; size_t v___x_772_; lean_object* v___x_773_; size_t v___x_774_; size_t v___x_775_; size_t v___x_776_; size_t v_h_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v_k_768_ = lean_array_fget_borrowed(v_keys_762_, v_i_764_);
v_v_769_ = lean_array_fget_borrowed(v_vals_763_, v_i_764_);
v___x_770_ = l_Lean_instHashableMVarId_hash(v_k_768_);
v_h_771_ = lean_uint64_to_usize(v___x_770_);
v___x_772_ = ((size_t)5ULL);
v___x_773_ = lean_unsigned_to_nat(1u);
v___x_774_ = ((size_t)1ULL);
v___x_775_ = lean_usize_sub(v_depth_761_, v___x_774_);
v___x_776_ = lean_usize_mul(v___x_772_, v___x_775_);
v_h_777_ = lean_usize_shift_right(v_h_771_, v___x_776_);
v___x_778_ = lean_nat_add(v_i_764_, v___x_773_);
lean_dec(v_i_764_);
lean_inc(v_v_769_);
lean_inc(v_k_768_);
v___x_779_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3___redArg(v_entries_765_, v_h_777_, v_depth_761_, v_k_768_, v_v_769_);
v_i_764_ = v___x_778_;
v_entries_765_ = v___x_779_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_761_ = stack[0].m_num;
lean_object* v_keys_762_ = stack[1].m_obj;
lean_object* v_vals_763_ = stack[2].m_obj;
lean_object* v_i_764_ = stack[3].m_obj;
lean_object* v_entries_765_ = stack[4].m_obj;
lean_object* v_res_781_;
v_res_781_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__5___redArg(v_depth_761_, v_keys_762_, v_vals_763_, v_i_764_, v_entries_765_);
stack->m_obj
 = v_res_781_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__5___redArg___boxed(lean_object* v_depth_782_, lean_object* v_keys_783_, lean_object* v_vals_784_, lean_object* v_i_785_, lean_object* v_entries_786_){
_start:
{
size_t v_depth_boxed_787_; lean_object* v_res_788_; 
v_depth_boxed_787_ = lean_unbox_usize(v_depth_782_);
lean_dec(v_depth_782_);
v_res_788_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__5___redArg(v_depth_boxed_787_, v_keys_783_, v_vals_784_, v_i_785_, v_entries_786_);
lean_dec_ref(v_vals_784_);
lean_dec_ref(v_keys_783_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_x_789_, lean_object* v_x_790_, lean_object* v_x_791_, lean_object* v_x_792_, lean_object* v_x_793_){
_start:
{
size_t v_x_7990__boxed_794_; size_t v_x_7991__boxed_795_; lean_object* v_res_796_; 
v_x_7990__boxed_794_ = lean_unbox_usize(v_x_790_);
lean_dec(v_x_790_);
v_x_7991__boxed_795_ = lean_unbox_usize(v_x_791_);
lean_dec(v_x_791_);
v_res_796_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3___redArg(v_x_789_, v_x_7990__boxed_794_, v_x_7991__boxed_795_, v_x_792_, v_x_793_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0___redArg(lean_object* v_x_797_, lean_object* v_x_798_, lean_object* v_x_799_){
_start:
{
uint64_t v___x_800_; size_t v___x_801_; size_t v___x_802_; lean_object* v___x_803_; 
v___x_800_ = l_Lean_instHashableMVarId_hash(v_x_798_);
v___x_801_ = lean_uint64_to_usize(v___x_800_);
v___x_802_ = ((size_t)1ULL);
v___x_803_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3___redArg(v_x_797_, v___x_801_, v___x_802_, v_x_798_, v_x_799_);
return v___x_803_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0___redArg(lean_object* v_mvarId_804_, lean_object* v_val_805_, lean_object* v___y_806_){
_start:
{
lean_object* v___x_808_; lean_object* v_mctx_809_; lean_object* v_cache_810_; lean_object* v_zetaDeltaFVarIds_811_; lean_object* v_postponed_812_; lean_object* v_diag_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_843_; 
v___x_808_ = lean_st_ref_take(v___y_806_);
v_mctx_809_ = lean_ctor_get(v___x_808_, 0);
v_cache_810_ = lean_ctor_get(v___x_808_, 1);
v_zetaDeltaFVarIds_811_ = lean_ctor_get(v___x_808_, 2);
v_postponed_812_ = lean_ctor_get(v___x_808_, 3);
v_diag_813_ = lean_ctor_get(v___x_808_, 4);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_843_ == 0)
{
v___x_815_ = v___x_808_;
v_isShared_816_ = v_isSharedCheck_843_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_diag_813_);
lean_inc(v_postponed_812_);
lean_inc(v_zetaDeltaFVarIds_811_);
lean_inc(v_cache_810_);
lean_inc(v_mctx_809_);
lean_dec(v___x_808_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_843_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v_depth_817_; lean_object* v_levelAssignDepth_818_; lean_object* v_lmvarCounter_819_; lean_object* v_mvarCounter_820_; lean_object* v_lDecls_821_; lean_object* v_decls_822_; lean_object* v_userNames_823_; lean_object* v_lAssignment_824_; lean_object* v_eAssignment_825_; lean_object* v_dAssignment_826_; lean_object* v_instanceTypedMVars_827_; lean_object* v_synthNormMemo_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_842_; 
v_depth_817_ = lean_ctor_get(v_mctx_809_, 0);
v_levelAssignDepth_818_ = lean_ctor_get(v_mctx_809_, 1);
v_lmvarCounter_819_ = lean_ctor_get(v_mctx_809_, 2);
v_mvarCounter_820_ = lean_ctor_get(v_mctx_809_, 3);
v_lDecls_821_ = lean_ctor_get(v_mctx_809_, 4);
v_decls_822_ = lean_ctor_get(v_mctx_809_, 5);
v_userNames_823_ = lean_ctor_get(v_mctx_809_, 6);
v_lAssignment_824_ = lean_ctor_get(v_mctx_809_, 7);
v_eAssignment_825_ = lean_ctor_get(v_mctx_809_, 8);
v_dAssignment_826_ = lean_ctor_get(v_mctx_809_, 9);
v_instanceTypedMVars_827_ = lean_ctor_get(v_mctx_809_, 10);
v_synthNormMemo_828_ = lean_ctor_get(v_mctx_809_, 11);
v_isSharedCheck_842_ = !lean_is_exclusive(v_mctx_809_);
if (v_isSharedCheck_842_ == 0)
{
v___x_830_ = v_mctx_809_;
v_isShared_831_ = v_isSharedCheck_842_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_synthNormMemo_828_);
lean_inc(v_instanceTypedMVars_827_);
lean_inc(v_dAssignment_826_);
lean_inc(v_eAssignment_825_);
lean_inc(v_lAssignment_824_);
lean_inc(v_userNames_823_);
lean_inc(v_decls_822_);
lean_inc(v_lDecls_821_);
lean_inc(v_mvarCounter_820_);
lean_inc(v_lmvarCounter_819_);
lean_inc(v_levelAssignDepth_818_);
lean_inc(v_depth_817_);
lean_dec(v_mctx_809_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_842_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_835_; 
v___x_832_ = lean_box(0);
v___x_833_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0___redArg(v_eAssignment_825_, v_mvarId_804_, v_val_805_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 8, v___x_833_);
v___x_835_ = v___x_830_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_depth_817_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v_levelAssignDepth_818_);
lean_ctor_set(v_reuseFailAlloc_841_, 2, v_lmvarCounter_819_);
lean_ctor_set(v_reuseFailAlloc_841_, 3, v_mvarCounter_820_);
lean_ctor_set(v_reuseFailAlloc_841_, 4, v_lDecls_821_);
lean_ctor_set(v_reuseFailAlloc_841_, 5, v_decls_822_);
lean_ctor_set(v_reuseFailAlloc_841_, 6, v_userNames_823_);
lean_ctor_set(v_reuseFailAlloc_841_, 7, v_lAssignment_824_);
lean_ctor_set(v_reuseFailAlloc_841_, 8, v___x_833_);
lean_ctor_set(v_reuseFailAlloc_841_, 9, v_dAssignment_826_);
lean_ctor_set(v_reuseFailAlloc_841_, 10, v_instanceTypedMVars_827_);
lean_ctor_set(v_reuseFailAlloc_841_, 11, v_synthNormMemo_828_);
v___x_835_ = v_reuseFailAlloc_841_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
lean_object* v___x_837_; 
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v___x_835_);
v___x_837_ = v___x_815_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_835_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_cache_810_);
lean_ctor_set(v_reuseFailAlloc_840_, 2, v_zetaDeltaFVarIds_811_);
lean_ctor_set(v_reuseFailAlloc_840_, 3, v_postponed_812_);
lean_ctor_set(v_reuseFailAlloc_840_, 4, v_diag_813_);
v___x_837_ = v_reuseFailAlloc_840_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_838_ = lean_st_ref_put(v___y_806_, v___x_837_);
v___x_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_839_, 0, v___x_832_);
return v___x_839_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_804_ = stack[0].m_obj;
lean_object* v_val_805_ = stack[1].m_obj;
lean_object* v___y_806_ = stack[2].m_obj;
lean_object* v_res_844_;
v_res_844_ = l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0___redArg(v_mvarId_804_, v_val_805_, v___y_806_);
stack->m_obj
 = v_res_844_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0___redArg___boxed(lean_object* v_mvarId_845_, lean_object* v_val_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0___redArg(v_mvarId_845_, v_val_846_, v___y_847_);
lean_dec(v___y_847_);
return v_res_849_;
}
}
lean_object* l_Lean_Meta_unifyEq_x3f___lam__0(uint8_t v___x_857_, lean_object* v_mvarId_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_b_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v___x_867_; lean_object* v_env_868_; lean_object* v___x_869_; lean_object* v_fst_871_; lean_object* v_fst_872_; lean_object* v_snd_873_; lean_object* v___y_874_; lean_object* v___y_875_; lean_object* v___y_876_; lean_object* v___y_877_; uint8_t v___x_980_; 
v___x_867_ = lean_st_ref_get(v___y_865_);
v_env_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc_ref(v_env_868_);
lean_dec(v___x_867_);
v___x_869_ = ((lean_object*)(l_Lean_Meta_unifyEq_x3f___lam__0___closed__3));
v___x_980_ = l_Lean_Environment_contains(v_env_868_, v___x_869_, v___x_857_);
if (v___x_980_ == 0)
{
lean_object* v___x_981_; lean_object* v___x_982_; 
lean_dec_ref(v_b_861_);
lean_dec_ref(v_a_860_);
lean_dec_ref(v_a_859_);
lean_dec(v_mvarId_858_);
v___x_981_ = lean_box(0);
v___x_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
return v___x_982_;
}
else
{
lean_object* v___x_983_; 
v___x_983_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f(v_a_860_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_1050_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_986_ = v___x_983_;
v_isShared_987_ = v_isSharedCheck_1050_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_983_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_1050_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
if (lean_obj_tag(v_a_984_) == 1)
{
lean_object* v_val_988_; lean_object* v_fst_989_; lean_object* v_snd_990_; lean_object* v___x_991_; 
v_val_988_ = lean_ctor_get(v_a_984_, 0);
lean_inc(v_val_988_);
lean_dec_ref_known(v_a_984_, 1);
v_fst_989_ = lean_ctor_get(v_val_988_, 0);
lean_inc(v_fst_989_);
v_snd_990_ = lean_ctor_get(v_val_988_, 1);
lean_inc(v_snd_990_);
lean_dec(v_val_988_);
v___x_991_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f(v_b_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1037_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_994_ = v___x_991_;
v_isShared_995_ = v_isSharedCheck_1037_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_991_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1037_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
if (lean_obj_tag(v_a_992_) == 1)
{
lean_object* v_val_1001_; lean_object* v_fst_1002_; lean_object* v_snd_1003_; lean_object* v___x_1004_; uint8_t v___x_1005_; 
lean_del_object(v___x_986_);
v_val_1001_ = lean_ctor_get(v_a_992_, 0);
lean_inc(v_val_1001_);
lean_dec_ref_known(v_a_992_, 1);
v_fst_1002_ = lean_ctor_get(v_val_1001_, 0);
lean_inc(v_fst_1002_);
v_snd_1003_ = lean_ctor_get(v_val_1001_, 1);
lean_inc(v_snd_1003_);
lean_dec(v_val_1001_);
v___x_1004_ = lean_unsigned_to_nat(0u);
v___x_1005_ = lean_nat_dec_eq(v_snd_990_, v___x_1004_);
if (v___x_1005_ == 0)
{
uint8_t v___x_1006_; 
v___x_1006_ = lean_nat_dec_eq(v_snd_1003_, v___x_1004_);
if (v___x_1006_ == 0)
{
uint8_t v___x_1007_; 
lean_del_object(v___x_994_);
v___x_1007_ = lean_nat_dec_lt(v_snd_990_, v_snd_1003_);
if (v___x_1007_ == 0)
{
uint8_t v___x_1008_; 
v___x_1008_ = lean_nat_dec_eq(v_snd_990_, v_snd_1003_);
if (v___x_1008_ == 0)
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1009_ = lean_nat_sub(v_snd_990_, v_snd_1003_);
lean_dec(v_snd_990_);
v___x_1010_ = l_Lean_mkNatLit(v___x_1009_);
v___x_1011_ = l_Lean_Meta_mkAdd(v_fst_989_, v___x_1010_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_a_1012_);
lean_dec_ref_known(v___x_1011_, 1);
v_fst_871_ = v_a_1012_;
v_fst_872_ = v_fst_1002_;
v_snd_873_ = v_snd_1003_;
v___y_874_ = v___y_862_;
v___y_875_ = v___y_863_;
v___y_876_ = v___y_864_;
v___y_877_ = v___y_865_;
goto v___jp_870_;
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
lean_dec(v_snd_1003_);
lean_dec(v_fst_1002_);
lean_dec_ref(v_a_859_);
lean_dec(v_mvarId_858_);
v_a_1013_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_1011_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_1011_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1013_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
else
{
lean_dec(v_snd_1003_);
v_fst_871_ = v_fst_989_;
v_fst_872_ = v_fst_1002_;
v_snd_873_ = v_snd_990_;
v___y_874_ = v___y_862_;
v___y_875_ = v___y_863_;
v___y_876_ = v___y_864_;
v___y_877_ = v___y_865_;
goto v___jp_870_;
}
}
else
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1021_ = lean_nat_sub(v_snd_1003_, v_snd_990_);
lean_dec(v_snd_1003_);
v___x_1022_ = l_Lean_mkNatLit(v___x_1021_);
v___x_1023_ = l_Lean_Meta_mkAdd(v_fst_1002_, v___x_1022_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_a_1024_);
lean_dec_ref_known(v___x_1023_, 1);
v_fst_871_ = v_fst_989_;
v_fst_872_ = v_a_1024_;
v_snd_873_ = v_snd_990_;
v___y_874_ = v___y_862_;
v___y_875_ = v___y_863_;
v___y_876_ = v___y_864_;
v___y_877_ = v___y_865_;
goto v___jp_870_;
}
else
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1032_; 
lean_dec(v_snd_990_);
lean_dec(v_fst_989_);
lean_dec_ref(v_a_859_);
lean_dec(v_mvarId_858_);
v_a_1025_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1027_ = v___x_1023_;
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1023_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1030_; 
if (v_isShared_1028_ == 0)
{
v___x_1030_ = v___x_1027_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_a_1025_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
}
else
{
lean_dec(v_snd_1003_);
lean_dec(v_fst_1002_);
lean_dec(v_snd_990_);
lean_dec(v_fst_989_);
lean_dec_ref(v_a_859_);
lean_dec(v_mvarId_858_);
goto v___jp_996_;
}
}
else
{
lean_dec(v_snd_1003_);
lean_dec(v_fst_1002_);
lean_dec(v_snd_990_);
lean_dec(v_fst_989_);
lean_dec_ref(v_a_859_);
lean_dec(v_mvarId_858_);
goto v___jp_996_;
}
}
else
{
lean_object* v___x_1033_; lean_object* v___x_1035_; 
lean_del_object(v___x_994_);
lean_dec(v_a_992_);
lean_dec(v_snd_990_);
lean_dec(v_fst_989_);
lean_dec_ref(v_a_859_);
lean_dec(v_mvarId_858_);
v___x_1033_ = lean_box(0);
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 0, v___x_1033_);
v___x_1035_ = v___x_986_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1033_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
v___jp_996_:
{
lean_object* v___x_997_; lean_object* v___x_999_; 
v___x_997_ = lean_box(0);
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 0, v___x_997_);
v___x_999_ = v___x_994_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
lean_dec(v_snd_990_);
lean_dec(v_fst_989_);
lean_del_object(v___x_986_);
lean_dec_ref(v_a_859_);
lean_dec(v_mvarId_858_);
v_a_1038_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___x_991_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_991_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1038_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
else
{
lean_object* v___x_1046_; lean_object* v___x_1048_; 
lean_dec(v_a_984_);
lean_dec_ref(v_b_861_);
lean_dec_ref(v_a_859_);
lean_dec(v_mvarId_858_);
v___x_1046_ = lean_box(0);
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 0, v___x_1046_);
v___x_1048_ = v___x_986_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1046_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
else
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
lean_dec_ref(v_b_861_);
lean_dec_ref(v_a_859_);
lean_dec(v_mvarId_858_);
v_a_1051_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v___x_983_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_983_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1051_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
v___jp_870_:
{
lean_object* v___x_878_; 
lean_inc(v_mvarId_858_);
v___x_878_ = l_Lean_MVarId_getType(v_mvarId_858_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; lean_object* v___x_880_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
lean_inc_n(v_a_879_, 2);
lean_dec_ref_known(v___x_878_, 1);
v___x_880_ = l_Lean_Meta_getLevel(v_a_879_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; lean_object* v___x_882_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_a_881_);
lean_dec_ref_known(v___x_880_, 1);
lean_inc_ref(v_fst_872_);
lean_inc_ref(v_fst_871_);
v___x_882_ = l_Lean_Meta_mkEq(v_fst_871_, v_fst_872_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; lean_object* v___x_884_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_a_883_);
lean_dec_ref_known(v___x_882_, 1);
lean_inc(v_a_879_);
v___x_884_ = l_Lean_mkArrow(v_a_883_, v_a_879_, v___y_876_, v___y_877_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_a_885_; lean_object* v___x_886_; 
v_a_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_a_885_);
lean_dec_ref_known(v___x_884_, 1);
lean_inc(v_mvarId_858_);
v___x_886_ = l_Lean_MVarId_getTag(v_mvarId_858_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v_a_887_; lean_object* v___x_888_; 
v_a_887_ = lean_ctor_get(v___x_886_, 0);
lean_inc(v_a_887_);
lean_dec_ref_known(v___x_886_, 1);
v___x_888_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_885_, v_a_887_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_930_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc_n(v_a_889_, 2);
lean_dec_ref_known(v___x_888_, 1);
v___x_890_ = lean_box(0);
v___x_891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_891_, 0, v_a_881_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v___x_892_ = l_Lean_mkConst(v___x_869_, v___x_891_);
v___x_893_ = l_Lean_mkNatLit(v_snd_873_);
lean_inc_ref(v_a_859_);
v___x_894_ = l_Lean_LocalDecl_toExpr(v_a_859_);
v___x_895_ = lean_unsigned_to_nat(6u);
v___x_896_ = lean_mk_empty_array_with_capacity(v___x_895_);
v___x_897_ = lean_array_push(v___x_896_, v_a_879_);
v___x_898_ = lean_array_push(v___x_897_, v_fst_871_);
v___x_899_ = lean_array_push(v___x_898_, v_fst_872_);
v___x_900_ = lean_array_push(v___x_899_, v___x_893_);
v___x_901_ = lean_array_push(v___x_900_, v___x_894_);
v___x_902_ = lean_array_push(v___x_901_, v_a_889_);
v___x_903_ = l_Lean_mkAppN(v___x_892_, v___x_902_);
lean_dec_ref(v___x_902_);
v___x_904_ = l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0___redArg(v_mvarId_858_, v___x_903_, v___y_875_);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_930_ == 0)
{
lean_object* v_unused_931_; 
v_unused_931_ = lean_ctor_get(v___x_904_, 0);
lean_dec(v_unused_931_);
v___x_906_ = v___x_904_;
v_isShared_907_ = v_isSharedCheck_930_;
goto v_resetjp_905_;
}
else
{
lean_dec(v___x_904_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_930_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_908_ = l_Lean_Expr_mvarId_x21(v_a_889_);
lean_dec(v_a_889_);
v___x_909_ = l_Lean_LocalDecl_fvarId(v_a_859_);
lean_dec_ref(v_a_859_);
v___x_910_ = l_Lean_MVarId_tryClear(v___x_908_, v___x_909_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_921_; 
v_a_911_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_921_ == 0)
{
v___x_913_ = v___x_910_;
v_isShared_914_ = v_isSharedCheck_921_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_910_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_921_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_907_ == 0)
{
lean_ctor_set_tag(v___x_906_, 1);
lean_ctor_set(v___x_906_, 0, v_a_911_);
v___x_916_ = v___x_906_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_a_911_);
v___x_916_ = v_reuseFailAlloc_920_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
lean_object* v___x_918_; 
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 0, v___x_916_);
v___x_918_ = v___x_913_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_916_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
lean_del_object(v___x_906_);
v_a_922_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_910_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_910_);
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
}
else
{
lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_939_; 
lean_dec(v_a_881_);
lean_dec(v_a_879_);
lean_dec(v_snd_873_);
lean_dec_ref(v_fst_872_);
lean_dec_ref(v_fst_871_);
lean_dec_ref(v_a_859_);
lean_dec(v_mvarId_858_);
v_a_932_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_939_ == 0)
{
v___x_934_ = v___x_888_;
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_888_);
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
lean_dec(v_a_885_);
lean_dec(v_a_881_);
lean_dec(v_a_879_);
lean_dec(v_snd_873_);
lean_dec_ref(v_fst_872_);
lean_dec_ref(v_fst_871_);
lean_dec_ref(v_a_859_);
lean_dec(v_mvarId_858_);
v_a_940_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_886_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_886_);
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
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
lean_dec(v_a_881_);
lean_dec(v_a_879_);
lean_dec(v_snd_873_);
lean_dec_ref(v_fst_872_);
lean_dec_ref(v_fst_871_);
lean_dec_ref(v_a_859_);
lean_dec(v_mvarId_858_);
v_a_948_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_884_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_884_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
else
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
lean_dec(v_a_881_);
lean_dec(v_a_879_);
lean_dec(v_snd_873_);
lean_dec_ref(v_fst_872_);
lean_dec_ref(v_fst_871_);
lean_dec_ref(v_a_859_);
lean_dec(v_mvarId_858_);
v_a_956_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_963_ == 0)
{
v___x_958_ = v___x_882_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_882_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_956_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
else
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_971_; 
lean_dec(v_a_879_);
lean_dec(v_snd_873_);
lean_dec_ref(v_fst_872_);
lean_dec_ref(v_fst_871_);
lean_dec_ref(v_a_859_);
lean_dec(v_mvarId_858_);
v_a_964_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_971_ == 0)
{
v___x_966_ = v___x_880_;
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_880_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_969_; 
if (v_isShared_967_ == 0)
{
v___x_969_ = v___x_966_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_a_964_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
}
else
{
lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_979_; 
lean_dec(v_snd_873_);
lean_dec_ref(v_fst_872_);
lean_dec_ref(v_fst_871_);
lean_dec_ref(v_a_859_);
lean_dec(v_mvarId_858_);
v_a_972_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_979_ == 0)
{
v___x_974_ = v___x_878_;
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v___x_878_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_977_; 
if (v_isShared_975_ == 0)
{
v___x_977_ = v___x_974_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_a_972_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_unifyEq_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_857_ = stack[0].m_num;
lean_object* v_mvarId_858_ = stack[1].m_obj;
lean_object* v_a_859_ = stack[2].m_obj;
lean_object* v_a_860_ = stack[3].m_obj;
lean_object* v_b_861_ = stack[4].m_obj;
lean_object* v___y_862_ = stack[5].m_obj;
lean_object* v___y_863_ = stack[6].m_obj;
lean_object* v___y_864_ = stack[7].m_obj;
lean_object* v___y_865_ = stack[8].m_obj;
lean_object* v_res_1059_;
v_res_1059_ = l_Lean_Meta_unifyEq_x3f___lam__0(v___x_857_, v_mvarId_858_, v_a_859_, v_a_860_, v_b_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
stack->m_obj
 = v_res_1059_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__0___boxed(lean_object* v___x_1060_, lean_object* v_mvarId_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_b_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
uint8_t v___x_8327__boxed_1070_; lean_object* v_res_1071_; 
v___x_8327__boxed_1070_ = lean_unbox(v___x_1060_);
v_res_1071_ = l_Lean_Meta_unifyEq_x3f___lam__0(v___x_8327__boxed_1070_, v_mvarId_1061_, v_a_1062_, v_a_1063_, v_b_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
return v_res_1071_;
}
}
static lean_object* _init_l_Lean_Meta_unifyEq_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = ((lean_object*)(l_Lean_Meta_unifyEq_x3f___lam__1___closed__2));
v___x_1077_ = l_Lean_stringToMessageData(v___x_1076_);
return v___x_1077_;
}
}
lean_object* l_Lean_Meta_unifyEq_x3f___lam__1(lean_object* v_eqFVarId_1078_, lean_object* v_mvarId_1079_, lean_object* v_subst_1080_, lean_object* v_acyclic_1081_, lean_object* v_caseName_x3f_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
lean_object* v___x_1088_; 
lean_inc(v_eqFVarId_1078_);
v___x_1088_ = l_Lean_FVarId_getDecl___redArg(v_eqFVarId_1078_, v___y_1083_, v___y_1085_, v___y_1086_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v_a_1089_; lean_object* v___x_1090_; uint8_t v___x_1091_; 
v_a_1089_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_a_1089_);
lean_dec_ref_known(v___x_1088_, 1);
v___x_1090_ = l_Lean_LocalDecl_type(v_a_1089_);
v___x_1091_ = l_Lean_Expr_isHEq(v___x_1090_);
if (v___x_1091_ == 0)
{
lean_object* v___x_1092_; lean_object* v___x_1093_; uint8_t v___x_1094_; 
v___x_1092_ = ((lean_object*)(l_Lean_Meta_unifyEq_x3f___lam__1___closed__1));
v___x_1093_ = lean_unsigned_to_nat(3u);
v___x_1094_ = l_Lean_Expr_isAppOfArity(v___x_1090_, v___x_1092_, v___x_1093_);
if (v___x_1094_ == 0)
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
lean_dec(v_a_1089_);
lean_dec(v_caseName_x3f_1082_);
lean_dec_ref(v_acyclic_1081_);
lean_dec(v_subst_1080_);
lean_dec(v_mvarId_1079_);
lean_dec(v_eqFVarId_1078_);
v___x_1095_ = lean_obj_once(&l_Lean_Meta_unifyEq_x3f___lam__1___closed__3, &l_Lean_Meta_unifyEq_x3f___lam__1___closed__3_once, _init_l_Lean_Meta_unifyEq_x3f___lam__1___closed__3);
v___x_1096_ = l_Lean_indentExpr(v___x_1090_);
v___x_1097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1095_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
v___x_1098_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(v___x_1097_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
return v___x_1098_;
}
else
{
lean_object* v___x_1099_; lean_object* v___f_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v_a_1105_; lean_object* v___x_1106_; 
v___x_1099_ = lean_box(v___x_1094_);
lean_inc(v_a_1089_);
lean_inc(v_mvarId_1079_);
v___f_1100_ = lean_alloc_closure((void*)(l_Lean_Meta_unifyEq_x3f___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1100_, 0, v___x_1099_);
lean_closure_set(v___f_1100_, 1, v_mvarId_1079_);
lean_closure_set(v___f_1100_, 2, v_a_1089_);
v___x_1101_ = l_Lean_Expr_appFn_x21(v___x_1090_);
v___x_1102_ = l_Lean_Expr_appArg_x21(v___x_1101_);
lean_dec_ref(v___x_1101_);
v___x_1103_ = l_Lean_Expr_appArg_x21(v___x_1090_);
lean_dec_ref(v___x_1090_);
lean_inc_ref(v___x_1102_);
v___x_1104_ = l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__1___redArg(v___x_1102_, v___y_1084_);
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_a_1105_);
lean_dec_ref(v___x_1104_);
lean_inc_ref(v___x_1103_);
v___x_1106_ = l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__1___redArg(v___x_1103_, v___y_1084_);
if (lean_obj_tag(v_a_1105_) == 1)
{
lean_object* v_a_1107_; 
lean_dec_ref(v___f_1100_);
lean_dec(v_caseName_x3f_1082_);
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
lean_inc(v_a_1107_);
lean_dec_ref(v___x_1106_);
if (lean_obj_tag(v_a_1107_) == 1)
{
lean_object* v_fvarId_1108_; lean_object* v_fvarId_1109_; lean_object* v___x_1110_; 
v_fvarId_1108_ = lean_ctor_get(v_a_1105_, 0);
lean_inc(v_fvarId_1108_);
lean_dec_ref_known(v_a_1105_, 1);
v_fvarId_1109_ = lean_ctor_get(v_a_1107_, 0);
lean_inc(v_fvarId_1109_);
lean_dec_ref_known(v_a_1107_, 1);
v___x_1110_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1108_, v___y_1083_, v___y_1085_, v___y_1086_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; lean_object* v___x_1112_; 
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
lean_inc(v_a_1111_);
lean_dec_ref_known(v___x_1110_, 1);
v___x_1112_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1109_, v___y_1083_, v___y_1085_, v___y_1086_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; uint8_t v___x_1116_; lean_object* v___x_1117_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_a_1113_);
lean_dec_ref_known(v___x_1112_, 1);
v___x_1114_ = l_Lean_LocalDecl_index(v_a_1111_);
lean_dec(v_a_1111_);
v___x_1115_ = l_Lean_LocalDecl_index(v_a_1113_);
lean_dec(v_a_1113_);
v___x_1116_ = lean_nat_dec_lt(v___x_1114_, v___x_1115_);
lean_dec(v___x_1115_);
lean_dec(v___x_1114_);
v___x_1117_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq(v_mvarId_1079_, v_eqFVarId_1078_, v_subst_1080_, v_acyclic_1081_, v_a_1089_, v___x_1102_, v___x_1103_, v___x_1116_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
lean_dec(v_a_1089_);
return v___x_1117_;
}
else
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
lean_dec(v_a_1111_);
lean_dec_ref(v___x_1103_);
lean_dec_ref(v___x_1102_);
lean_dec(v_a_1089_);
lean_dec_ref(v_acyclic_1081_);
lean_dec(v_subst_1080_);
lean_dec(v_mvarId_1079_);
lean_dec(v_eqFVarId_1078_);
v_a_1118_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1112_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1112_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
else
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
lean_dec(v_fvarId_1109_);
lean_dec_ref(v___x_1103_);
lean_dec_ref(v___x_1102_);
lean_dec(v_a_1089_);
lean_dec_ref(v_acyclic_1081_);
lean_dec(v_subst_1080_);
lean_dec(v_mvarId_1079_);
lean_dec(v_eqFVarId_1078_);
v_a_1126_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v___x_1110_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1110_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1126_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
else
{
lean_object* v___x_1134_; 
lean_dec(v_a_1107_);
lean_dec_ref_known(v_a_1105_, 1);
v___x_1134_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq(v_mvarId_1079_, v_eqFVarId_1078_, v_subst_1080_, v_acyclic_1081_, v_a_1089_, v___x_1102_, v___x_1103_, v___x_1091_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
lean_dec(v_a_1089_);
return v___x_1134_;
}
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1174_; 
v_a_1135_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1137_ = v___x_1106_;
v_isShared_1138_ = v_isSharedCheck_1174_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1106_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1174_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
if (lean_obj_tag(v_a_1135_) == 1)
{
lean_object* v___x_1139_; 
lean_dec_ref_known(v_a_1135_, 1);
lean_del_object(v___x_1137_);
lean_dec(v_a_1105_);
lean_dec_ref(v___f_1100_);
lean_dec(v_caseName_x3f_1082_);
v___x_1139_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq(v_mvarId_1079_, v_eqFVarId_1078_, v_subst_1080_, v_acyclic_1081_, v_a_1089_, v___x_1102_, v___x_1103_, v___x_1094_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
lean_dec(v_a_1089_);
return v___x_1139_;
}
else
{
lean_object* v___x_1140_; 
lean_dec_ref(v___x_1103_);
lean_dec_ref(v___x_1102_);
lean_dec_ref(v_acyclic_1081_);
lean_inc(v_a_1135_);
lean_inc(v_a_1105_);
v___x_1140_ = l_Lean_Meta_isExprDefEq(v_a_1105_, v_a_1135_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v_a_1141_; uint8_t v___x_1142_; 
v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
lean_inc(v_a_1141_);
lean_dec_ref_known(v___x_1140_, 1);
v___x_1142_ = lean_unbox(v_a_1141_);
lean_dec(v_a_1141_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; 
lean_del_object(v___x_1137_);
v___x_1143_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection(v_mvarId_1079_, v_eqFVarId_1078_, v_subst_1080_, v_caseName_x3f_1082_, v_a_1089_, v___f_1100_, v_a_1105_, v_a_1135_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
lean_dec(v_a_1089_);
return v___x_1143_;
}
else
{
lean_object* v___x_1144_; 
lean_dec(v_a_1135_);
lean_dec(v_a_1105_);
lean_dec_ref(v___f_1100_);
lean_dec(v_a_1089_);
lean_dec(v_caseName_x3f_1082_);
v___x_1144_ = l_Lean_MVarId_clear(v_mvarId_1079_, v_eqFVarId_1078_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1157_; 
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1147_ = v___x_1144_;
v_isShared_1148_ = v_isSharedCheck_1157_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1144_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1157_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1152_; 
v___x_1149_ = lean_unsigned_to_nat(0u);
v___x_1150_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1150_, 0, v_a_1145_);
lean_ctor_set(v___x_1150_, 1, v_subst_1080_);
lean_ctor_set(v___x_1150_, 2, v___x_1149_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set_tag(v___x_1137_, 1);
lean_ctor_set(v___x_1137_, 0, v___x_1150_);
v___x_1152_ = v___x_1137_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1150_);
v___x_1152_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
lean_object* v___x_1154_; 
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 0, v___x_1152_);
v___x_1154_ = v___x_1147_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v___x_1152_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
else
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
lean_del_object(v___x_1137_);
lean_dec(v_subst_1080_);
v_a_1158_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1144_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1144_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
}
else
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
lean_del_object(v___x_1137_);
lean_dec(v_a_1135_);
lean_dec(v_a_1105_);
lean_dec_ref(v___f_1100_);
lean_dec(v_a_1089_);
lean_dec(v_caseName_x3f_1082_);
lean_dec(v_subst_1080_);
lean_dec(v_mvarId_1079_);
lean_dec(v_eqFVarId_1078_);
v_a_1166_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1168_ = v___x_1140_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1140_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1166_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
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
lean_object* v___x_1175_; 
lean_dec_ref(v___x_1090_);
lean_dec(v_caseName_x3f_1082_);
lean_dec_ref(v_acyclic_1081_);
lean_dec(v_eqFVarId_1078_);
v___x_1175_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_heqToEq_x27(v_mvarId_1079_, v_a_1089_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
lean_dec(v_a_1089_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1186_; 
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1178_ = v___x_1175_;
v_isShared_1179_ = v_isSharedCheck_1186_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1175_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1186_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1184_; 
v___x_1180_ = lean_unsigned_to_nat(1u);
v___x_1181_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1181_, 0, v_a_1176_);
lean_ctor_set(v___x_1181_, 1, v_subst_1080_);
lean_ctor_set(v___x_1181_, 2, v___x_1180_);
v___x_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1181_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v___x_1182_);
v___x_1184_ = v___x_1178_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1182_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
else
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
lean_dec(v_subst_1080_);
v_a_1187_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_1175_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1175_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1187_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
}
else
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1202_; 
lean_dec(v_caseName_x3f_1082_);
lean_dec_ref(v_acyclic_1081_);
lean_dec(v_subst_1080_);
lean_dec(v_mvarId_1079_);
lean_dec(v_eqFVarId_1078_);
v_a_1195_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1197_ = v___x_1088_;
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1088_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1200_; 
if (v_isShared_1198_ == 0)
{
v___x_1200_ = v___x_1197_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_a_1195_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_unifyEq_x3f___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_eqFVarId_1078_ = stack[0].m_obj;
lean_object* v_mvarId_1079_ = stack[1].m_obj;
lean_object* v_subst_1080_ = stack[2].m_obj;
lean_object* v_acyclic_1081_ = stack[3].m_obj;
lean_object* v_caseName_x3f_1082_ = stack[4].m_obj;
lean_object* v___y_1083_ = stack[5].m_obj;
lean_object* v___y_1084_ = stack[6].m_obj;
lean_object* v___y_1085_ = stack[7].m_obj;
lean_object* v___y_1086_ = stack[8].m_obj;
lean_object* v_res_1203_;
v_res_1203_ = l_Lean_Meta_unifyEq_x3f___lam__1(v_eqFVarId_1078_, v_mvarId_1079_, v_subst_1080_, v_acyclic_1081_, v_caseName_x3f_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
stack->m_obj
 = v_res_1203_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__1___boxed(lean_object* v_eqFVarId_1204_, lean_object* v_mvarId_1205_, lean_object* v_subst_1206_, lean_object* v_acyclic_1207_, lean_object* v_caseName_x3f_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Lean_Meta_unifyEq_x3f___lam__1(v_eqFVarId_1204_, v_mvarId_1205_, v_subst_1206_, v_acyclic_1207_, v_caseName_x3f_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
return v_res_1214_;
}
}
lean_object* l_Lean_Meta_unifyEq_x3f(lean_object* v_mvarId_1215_, lean_object* v_eqFVarId_1216_, lean_object* v_subst_1217_, lean_object* v_acyclic_1218_, lean_object* v_caseName_x3f_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_){
_start:
{
lean_object* v___f_1225_; lean_object* v___x_1226_; 
lean_inc(v_mvarId_1215_);
v___f_1225_ = lean_alloc_closure((void*)(l_Lean_Meta_unifyEq_x3f___lam__1___boxed), 10, 5);
lean_closure_set(v___f_1225_, 0, v_eqFVarId_1216_);
lean_closure_set(v___f_1225_, 1, v_mvarId_1215_);
lean_closure_set(v___f_1225_, 2, v_subst_1217_);
lean_closure_set(v___f_1225_, 3, v_acyclic_1218_);
lean_closure_set(v___f_1225_, 4, v_caseName_x3f_1219_);
v___x_1226_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___redArg(v_mvarId_1215_, v___f_1225_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_);
return v___x_1226_;
}
}
LEAN_EXPORT void l_Lean_Meta_unifyEq_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1215_ = stack[0].m_obj;
lean_object* v_eqFVarId_1216_ = stack[1].m_obj;
lean_object* v_subst_1217_ = stack[2].m_obj;
lean_object* v_acyclic_1218_ = stack[3].m_obj;
lean_object* v_caseName_x3f_1219_ = stack[4].m_obj;
lean_object* v_a_1220_ = stack[5].m_obj;
lean_object* v_a_1221_ = stack[6].m_obj;
lean_object* v_a_1222_ = stack[7].m_obj;
lean_object* v_a_1223_ = stack[8].m_obj;
lean_object* v_res_1227_;
v_res_1227_ = l_Lean_Meta_unifyEq_x3f(v_mvarId_1215_, v_eqFVarId_1216_, v_subst_1217_, v_acyclic_1218_, v_caseName_x3f_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_);
stack->m_obj
 = v_res_1227_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___boxed(lean_object* v_mvarId_1228_, lean_object* v_eqFVarId_1229_, lean_object* v_subst_1230_, lean_object* v_acyclic_1231_, lean_object* v_caseName_x3f_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Lean_Meta_unifyEq_x3f(v_mvarId_1228_, v_eqFVarId_1229_, v_subst_1230_, v_acyclic_1231_, v_caseName_x3f_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_);
lean_dec(v_a_1236_);
lean_dec_ref(v_a_1235_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
return v_res_1238_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0(lean_object* v_mvarId_1239_, lean_object* v_val_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v___x_1246_; 
v___x_1246_ = l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0___redArg(v_mvarId_1239_, v_val_1240_, v___y_1242_);
return v___x_1246_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1239_ = stack[0].m_obj;
lean_object* v_val_1240_ = stack[1].m_obj;
lean_object* v___y_1241_ = stack[2].m_obj;
lean_object* v___y_1242_ = stack[3].m_obj;
lean_object* v___y_1243_ = stack[4].m_obj;
lean_object* v___y_1244_ = stack[5].m_obj;
lean_object* v_res_1247_;
v_res_1247_ = l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0(v_mvarId_1239_, v_val_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
stack->m_obj
 = v_res_1247_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0___boxed(lean_object* v_mvarId_1248_, lean_object* v_val_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0(v_mvarId_1248_, v_val_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1256_, lean_object* v_x_1257_, lean_object* v_x_1258_, lean_object* v_x_1259_){
_start:
{
lean_object* v___x_1260_; 
v___x_1260_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0___redArg(v_x_1257_, v_x_1258_, v_x_1259_);
return v___x_1260_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1261_, lean_object* v_x_1262_, size_t v_x_1263_, size_t v_x_1264_, lean_object* v_x_1265_, lean_object* v_x_1266_){
_start:
{
lean_object* v___x_1267_; 
v___x_1267_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3___redArg(v_x_1262_, v_x_1263_, v_x_1264_, v_x_1265_, v_x_1266_);
return v___x_1267_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1262_ = stack[1].m_obj;
size_t v_x_1263_ = stack[2].m_num;
size_t v_x_1264_ = stack[3].m_num;
lean_object* v_x_1265_ = stack[4].m_obj;
lean_object* v_x_1266_ = stack[5].m_obj;
lean_object* v_res_1268_;
v_res_1268_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3(lean_box(0), v_x_1262_, v_x_1263_, v_x_1264_, v_x_1265_, v_x_1266_);
stack->m_obj
 = v_res_1268_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1269_, lean_object* v_x_1270_, lean_object* v_x_1271_, lean_object* v_x_1272_, lean_object* v_x_1273_, lean_object* v_x_1274_){
_start:
{
size_t v_x_9400__boxed_1275_; size_t v_x_9401__boxed_1276_; lean_object* v_res_1277_; 
v_x_9400__boxed_1275_ = lean_unbox_usize(v_x_1271_);
lean_dec(v_x_1271_);
v_x_9401__boxed_1276_ = lean_unbox_usize(v_x_1272_);
lean_dec(v_x_1272_);
v_res_1277_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3(v_00_u03b2_1269_, v_x_1270_, v_x_9400__boxed_1275_, v_x_9401__boxed_1276_, v_x_1273_, v_x_1274_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_1278_, lean_object* v_n_1279_, lean_object* v_k_1280_, lean_object* v_v_1281_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__4___redArg(v_n_1279_, v_k_1280_, v_v_1281_);
return v___x_1282_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__5(lean_object* v_00_u03b2_1283_, size_t v_depth_1284_, lean_object* v_keys_1285_, lean_object* v_vals_1286_, lean_object* v_heq_1287_, lean_object* v_i_1288_, lean_object* v_entries_1289_){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__5___redArg(v_depth_1284_, v_keys_1285_, v_vals_1286_, v_i_1288_, v_entries_1289_);
return v___x_1290_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1284_ = stack[1].m_num;
lean_object* v_keys_1285_ = stack[2].m_obj;
lean_object* v_vals_1286_ = stack[3].m_obj;
lean_object* v_i_1288_ = stack[5].m_obj;
lean_object* v_entries_1289_ = stack[6].m_obj;
lean_object* v_res_1291_;
v_res_1291_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__5(lean_box(0), v_depth_1284_, v_keys_1285_, v_vals_1286_, lean_box(0), v_i_1288_, v_entries_1289_);
stack->m_obj
 = v_res_1291_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__5___boxed(lean_object* v_00_u03b2_1292_, lean_object* v_depth_1293_, lean_object* v_keys_1294_, lean_object* v_vals_1295_, lean_object* v_heq_1296_, lean_object* v_i_1297_, lean_object* v_entries_1298_){
_start:
{
size_t v_depth_boxed_1299_; lean_object* v_res_1300_; 
v_depth_boxed_1299_ = lean_unbox_usize(v_depth_1293_);
lean_dec(v_depth_1293_);
v_res_1300_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__5(v_00_u03b2_1292_, v_depth_boxed_1299_, v_keys_1294_, v_vals_1295_, v_heq_1296_, v_i_1297_, v_entries_1298_);
lean_dec_ref(v_vals_1295_);
lean_dec_ref(v_keys_1294_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_1301_, lean_object* v_x_1302_, lean_object* v_x_1303_, lean_object* v_x_1304_, lean_object* v_x_1305_){
_start:
{
lean_object* v___x_1306_; 
v___x_1306_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__0_spec__0_spec__3_spec__4_spec__5___redArg(v_x_1302_, v_x_1303_, v_x_1304_, v_x_1305_);
return v___x_1306_;
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
