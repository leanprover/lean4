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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_evalNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isOffset_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Meta_substCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
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
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_MVarId_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
uint8_t lean_bool_not(uint8_t);
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_a_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_143_; 
v_a_114_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_143_ == 0)
{
v___x_116_ = v___x_104_;
v_isShared_117_ = v_isSharedCheck_143_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_a_114_);
lean_dec(v___x_104_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_143_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
uint8_t v___y_119_; uint8_t v___x_141_; 
v___x_141_ = l_Lean_Exception_isInterrupt(v_a_114_);
if (v___x_141_ == 0)
{
uint8_t v___x_142_; 
lean_inc(v_a_114_);
v___x_142_ = l_Lean_Exception_isRuntime(v_a_114_);
v___y_119_ = v___x_142_;
goto v___jp_118_;
}
else
{
v___y_119_ = v___x_141_;
goto v___jp_118_;
}
v___jp_118_:
{
if (v___y_119_ == 0)
{
lean_object* v___x_120_; 
lean_del_object(v___x_116_);
lean_dec(v_a_114_);
v___x_120_ = l_Lean_Meta_SavedState_restore___redArg(v_a_103_, v___y_98_, v___y_100_);
lean_dec(v_a_103_);
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
}
}
}
else
{
lean_object* v_a_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_151_; 
lean_dec_ref(v_x_96_);
v_a_144_ = lean_ctor_get(v___x_102_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_102_);
if (v_isSharedCheck_151_ == 0)
{
v___x_146_ = v___x_102_;
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_a_144_);
lean_dec(v___x_102_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_149_; 
if (v_isShared_147_ == 0)
{
v___x_149_ = v___x_146_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_a_144_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0___redArg___boxed(lean_object* v_x_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0___redArg(v_x_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
lean_dec(v___y_156_);
lean_dec_ref(v___y_155_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0(lean_object* v_00_u03b1_159_, lean_object* v_x_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0___redArg(v_x_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0___boxed(lean_object* v_00_u03b1_167_, lean_object* v_x_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0(v_00_u03b1_167_, v_x_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1_spec__1(lean_object* v_msgData_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v___x_181_; lean_object* v_env_182_; lean_object* v___x_183_; lean_object* v_mctx_184_; lean_object* v_lctx_185_; lean_object* v_options_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_181_ = lean_st_ref_get(v___y_179_);
v_env_182_ = lean_ctor_get(v___x_181_, 0);
lean_inc_ref(v_env_182_);
lean_dec(v___x_181_);
v___x_183_ = lean_st_ref_get(v___y_177_);
v_mctx_184_ = lean_ctor_get(v___x_183_, 0);
lean_inc_ref(v_mctx_184_);
lean_dec(v___x_183_);
v_lctx_185_ = lean_ctor_get(v___y_176_, 2);
v_options_186_ = lean_ctor_get(v___y_178_, 2);
lean_inc_ref(v_options_186_);
lean_inc_ref(v_lctx_185_);
v___x_187_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_187_, 0, v_env_182_);
lean_ctor_set(v___x_187_, 1, v_mctx_184_);
lean_ctor_set(v___x_187_, 2, v_lctx_185_);
lean_ctor_set(v___x_187_, 3, v_options_186_);
v___x_188_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
lean_ctor_set(v___x_188_, 1, v_msgData_175_);
v___x_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1_spec__1___boxed(lean_object* v_msgData_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1_spec__1(v_msgData_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(lean_object* v_msg_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v_ref_203_; lean_object* v___x_204_; lean_object* v_a_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_213_; 
v_ref_203_ = lean_ctor_get(v___y_200_, 5);
v___x_204_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1_spec__1(v_msg_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_);
v_a_205_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_213_ == 0)
{
v___x_207_ = v___x_204_;
v_isShared_208_ = v_isSharedCheck_213_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_a_205_);
lean_dec(v___x_204_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_213_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_209_; lean_object* v___x_211_; 
lean_inc(v_ref_203_);
v___x_209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_209_, 0, v_ref_203_);
lean_ctor_set(v___x_209_, 1, v_a_205_);
if (v_isShared_208_ == 0)
{
lean_ctor_set_tag(v___x_207_, 1);
lean_ctor_set(v___x_207_, 0, v___x_209_);
v___x_211_ = v___x_207_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_209_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg___boxed(lean_object* v_msg_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(v_msg_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_);
lean_dec(v___y_218_);
lean_dec_ref(v___y_217_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
return v_res_220_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = ((lean_object*)(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__0));
v___x_223_ = l_Lean_stringToMessageData(v___x_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq(lean_object* v_mvarId_224_, lean_object* v_eqFVarId_225_, lean_object* v_subst_226_, lean_object* v_acyclic_227_, lean_object* v_eqDecl_228_, lean_object* v_a_229_, lean_object* v_b_230_, uint8_t v_symm_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_){
_start:
{
uint8_t v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_237_ = 1;
v___x_238_ = lean_box(v_symm_231_);
v___x_239_ = lean_box(v___x_237_);
v___x_240_ = lean_box(v___x_237_);
lean_inc(v_subst_226_);
lean_inc(v_eqFVarId_225_);
lean_inc(v_mvarId_224_);
v___x_241_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___boxed), 11, 6);
lean_closure_set(v___x_241_, 0, v_mvarId_224_);
lean_closure_set(v___x_241_, 1, v_eqFVarId_225_);
lean_closure_set(v___x_241_, 2, v___x_238_);
lean_closure_set(v___x_241_, 3, v_subst_226_);
lean_closure_set(v___x_241_, 4, v___x_239_);
lean_closure_set(v___x_241_, 5, v___x_240_);
v___x_242_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0___redArg(v___x_241_, v_a_232_, v_a_233_, v_a_234_, v_a_235_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_318_; 
v_a_243_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_318_ == 0)
{
v___x_245_ = v___x_242_;
v_isShared_246_ = v_isSharedCheck_318_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_242_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_318_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
if (lean_obj_tag(v_a_243_) == 1)
{
lean_object* v_val_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_261_; 
lean_dec_ref(v_b_230_);
lean_dec_ref(v_a_229_);
lean_dec_ref(v_acyclic_227_);
lean_dec(v_subst_226_);
lean_dec(v_eqFVarId_225_);
lean_dec(v_mvarId_224_);
v_val_247_ = lean_ctor_get(v_a_243_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v_a_243_);
if (v_isSharedCheck_261_ == 0)
{
v___x_249_ = v_a_243_;
v_isShared_250_ = v_isSharedCheck_261_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_val_247_);
lean_dec(v_a_243_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_261_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v_fst_251_; lean_object* v_snd_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_256_; 
v_fst_251_ = lean_ctor_get(v_val_247_, 0);
lean_inc(v_fst_251_);
v_snd_252_ = lean_ctor_get(v_val_247_, 1);
lean_inc(v_snd_252_);
lean_dec(v_val_247_);
v___x_253_ = lean_unsigned_to_nat(0u);
v___x_254_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_254_, 0, v_snd_252_);
lean_ctor_set(v___x_254_, 1, v_fst_251_);
lean_ctor_set(v___x_254_, 2, v___x_253_);
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 0, v___x_254_);
v___x_256_ = v___x_249_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_254_);
v___x_256_ = v_reuseFailAlloc_260_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v___x_258_; 
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v___x_256_);
v___x_258_ = v___x_245_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_256_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
else
{
lean_object* v___x_262_; 
lean_del_object(v___x_245_);
lean_dec(v_a_243_);
v___x_262_ = l_Lean_Meta_isExprDefEq(v_a_229_, v_b_230_, v_a_232_, v_a_233_, v_a_234_, v_a_235_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v_a_263_; uint8_t v___x_264_; 
v_a_263_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_a_263_);
lean_dec_ref_known(v___x_262_, 1);
v___x_264_ = lean_unbox(v_a_263_);
lean_dec(v_a_263_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; lean_object* v___x_266_; 
lean_dec(v_subst_226_);
v___x_265_ = l_Lean_mkFVar(v_eqFVarId_225_);
lean_inc(v_a_235_);
lean_inc_ref(v_a_234_);
lean_inc(v_a_233_);
lean_inc_ref(v_a_232_);
v___x_266_ = lean_apply_7(v_acyclic_227_, v_mvarId_224_, v___x_265_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, lean_box(0));
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_281_; 
v_a_267_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_281_ == 0)
{
v___x_269_ = v___x_266_;
v_isShared_270_ = v_isSharedCheck_281_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_266_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_281_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
uint8_t v___x_271_; 
v___x_271_ = lean_unbox(v_a_267_);
lean_dec(v_a_267_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
lean_del_object(v___x_269_);
v___x_272_ = lean_obj_once(&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1, &l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1_once, _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1);
v___x_273_ = l_Lean_LocalDecl_type(v_eqDecl_228_);
v___x_274_ = l_Lean_indentExpr(v___x_273_);
v___x_275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_272_);
lean_ctor_set(v___x_275_, 1, v___x_274_);
v___x_276_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(v___x_275_, v_a_232_, v_a_233_, v_a_234_, v_a_235_);
return v___x_276_;
}
else
{
lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_277_ = lean_box(0);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 0, v___x_277_);
v___x_279_ = v___x_269_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_277_);
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
v_a_282_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_289_ == 0)
{
v___x_284_ = v___x_266_;
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_a_282_);
lean_dec(v___x_266_);
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
lean_object* v___x_290_; 
lean_dec_ref(v_acyclic_227_);
v___x_290_ = l_Lean_MVarId_clear(v_mvarId_224_, v_eqFVarId_225_, v_a_232_, v_a_233_, v_a_234_, v_a_235_);
if (lean_obj_tag(v___x_290_) == 0)
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_301_; 
v_a_291_ = lean_ctor_get(v___x_290_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_301_ == 0)
{
v___x_293_ = v___x_290_;
v_isShared_294_ = v_isSharedCheck_301_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_290_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_301_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_299_; 
v___x_295_ = lean_unsigned_to_nat(0u);
v___x_296_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_296_, 0, v_a_291_);
lean_ctor_set(v___x_296_, 1, v_subst_226_);
lean_ctor_set(v___x_296_, 2, v___x_295_);
v___x_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 0, v___x_297_);
v___x_299_ = v___x_293_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_297_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
else
{
lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_309_; 
lean_dec(v_subst_226_);
v_a_302_ = lean_ctor_get(v___x_290_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_309_ == 0)
{
v___x_304_ = v___x_290_;
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___x_290_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_307_; 
if (v_isShared_305_ == 0)
{
v___x_307_ = v___x_304_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_a_302_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
}
else
{
lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_317_; 
lean_dec_ref(v_acyclic_227_);
lean_dec(v_subst_226_);
lean_dec(v_eqFVarId_225_);
lean_dec(v_mvarId_224_);
v_a_310_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_317_ == 0)
{
v___x_312_ = v___x_262_;
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v___x_262_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_315_; 
if (v_isShared_313_ == 0)
{
v___x_315_ = v___x_312_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_a_310_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
}
}
else
{
lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_326_; 
lean_dec_ref(v_b_230_);
lean_dec_ref(v_a_229_);
lean_dec_ref(v_acyclic_227_);
lean_dec(v_subst_226_);
lean_dec(v_eqFVarId_225_);
lean_dec(v_mvarId_224_);
v_a_319_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_326_ == 0)
{
v___x_321_ = v___x_242_;
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v___x_242_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___boxed(lean_object* v_mvarId_327_, lean_object* v_eqFVarId_328_, lean_object* v_subst_329_, lean_object* v_acyclic_330_, lean_object* v_eqDecl_331_, lean_object* v_a_332_, lean_object* v_b_333_, lean_object* v_symm_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_){
_start:
{
uint8_t v_symm_boxed_340_; lean_object* v_res_341_; 
v_symm_boxed_340_ = lean_unbox(v_symm_334_);
v_res_341_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq(v_mvarId_327_, v_eqFVarId_328_, v_subst_329_, v_acyclic_330_, v_eqDecl_331_, v_a_332_, v_b_333_, v_symm_boxed_340_, v_a_335_, v_a_336_, v_a_337_, v_a_338_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
lean_dec_ref(v_eqDecl_331_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1(lean_object* v_00_u03b1_342_, lean_object* v_msg_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(v_msg_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___boxed(lean_object* v_00_u03b1_350_, lean_object* v_msg_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1(v_00_u03b1_350_, v_msg_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
return v_res_357_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__1(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = ((lean_object*)(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__0));
v___x_360_ = l_Lean_stringToMessageData(v___x_359_);
return v___x_360_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__3(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = ((lean_object*)(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__2));
v___x_363_ = l_Lean_stringToMessageData(v___x_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection(lean_object* v_mvarId_364_, lean_object* v_eqFVarId_365_, lean_object* v_subst_366_, lean_object* v_caseName_x3f_367_, lean_object* v_eqDecl_368_, lean_object* v_injectionOffset_x3f_369_, lean_object* v_a_370_, lean_object* v_b_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_){
_start:
{
lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_423_; lean_object* v___x_501_; 
lean_inc(v_a_375_);
lean_inc_ref(v_a_374_);
lean_inc(v_a_373_);
lean_inc_ref(v_a_372_);
lean_inc_ref(v_b_371_);
lean_inc_ref(v_a_370_);
v___x_501_ = lean_apply_7(v_injectionOffset_x3f_369_, v_a_370_, v_b_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, lean_box(0));
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_523_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_523_ == 0)
{
v___x_504_ = v___x_501_;
v_isShared_505_ = v_isSharedCheck_523_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_501_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_523_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
if (lean_obj_tag(v_a_502_) == 1)
{
lean_object* v_val_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_518_; 
lean_dec_ref(v_b_371_);
lean_dec_ref(v_a_370_);
lean_dec(v_caseName_x3f_367_);
lean_dec(v_eqFVarId_365_);
lean_dec(v_mvarId_364_);
v_val_506_ = lean_ctor_get(v_a_502_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v_a_502_);
if (v_isSharedCheck_518_ == 0)
{
v___x_508_ = v_a_502_;
v_isShared_509_ = v_isSharedCheck_518_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_val_506_);
lean_dec(v_a_502_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_518_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_510_ = lean_unsigned_to_nat(1u);
v___x_511_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_511_, 0, v_val_506_);
lean_ctor_set(v___x_511_, 1, v_subst_366_);
lean_ctor_set(v___x_511_, 2, v___x_510_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_511_);
v___x_513_ = v___x_508_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_511_);
v___x_513_ = v_reuseFailAlloc_517_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
lean_object* v___x_515_; 
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 0, v___x_513_);
v___x_515_ = v___x_504_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_513_);
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
else
{
lean_object* v___x_519_; 
lean_del_object(v___x_504_);
lean_dec(v_a_502_);
lean_inc_ref(v_a_370_);
v___x_519_ = l_Lean_Meta_isConstructorApp(v_a_370_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; uint8_t v___x_521_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_a_520_);
v___x_521_ = lean_unbox(v_a_520_);
lean_dec(v_a_520_);
if (v___x_521_ == 0)
{
v___y_423_ = v___x_519_;
goto v___jp_422_;
}
else
{
lean_object* v___x_522_; 
lean_dec_ref_known(v___x_519_, 1);
lean_inc_ref(v_b_371_);
v___x_522_ = l_Lean_Meta_isConstructorApp(v_b_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
v___y_423_ = v___x_522_;
goto v___jp_422_;
}
}
else
{
v___y_423_ = v___x_519_;
goto v___jp_422_;
}
}
}
}
else
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_531_; 
lean_dec_ref(v_b_371_);
lean_dec_ref(v_a_370_);
lean_dec(v_caseName_x3f_367_);
lean_dec(v_subst_366_);
lean_dec(v_eqFVarId_365_);
lean_dec(v_mvarId_364_);
v_a_524_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_531_ == 0)
{
v___x_526_ = v___x_501_;
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_501_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_a_524_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
v___jp_377_:
{
lean_object* v___x_380_; 
v___x_380_ = l_Lean_Meta_mkEq(v___y_378_, v___y_379_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v_a_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_a_381_);
lean_dec_ref_known(v___x_380_, 1);
lean_inc(v_eqFVarId_365_);
v___x_382_ = l_Lean_mkFVar(v_eqFVarId_365_);
v___x_383_ = l_Lean_LocalDecl_userName(v_eqDecl_368_);
v___x_384_ = l_Lean_MVarId_assert(v_mvarId_364_, v___x_383_, v_a_381_, v___x_382_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; lean_object* v___x_386_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_a_385_);
lean_dec_ref_known(v___x_384_, 1);
v___x_386_ = l_Lean_MVarId_clear(v_a_385_, v_eqFVarId_365_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_397_; 
v_a_387_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_397_ == 0)
{
v___x_389_ = v___x_386_;
v_isShared_390_ = v_isSharedCheck_397_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_386_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_397_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_395_; 
v___x_391_ = lean_unsigned_to_nat(1u);
v___x_392_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_392_, 0, v_a_387_);
lean_ctor_set(v___x_392_, 1, v_subst_366_);
lean_ctor_set(v___x_392_, 2, v___x_391_);
v___x_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v___x_393_);
v___x_395_ = v___x_389_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_393_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
else
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_405_; 
lean_dec(v_subst_366_);
v_a_398_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_405_ == 0)
{
v___x_400_ = v___x_386_;
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_386_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_403_; 
if (v_isShared_401_ == 0)
{
v___x_403_ = v___x_400_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_398_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
else
{
lean_object* v_a_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_413_; 
lean_dec(v_subst_366_);
lean_dec(v_eqFVarId_365_);
v_a_406_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_413_ == 0)
{
v___x_408_ = v___x_384_;
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_a_406_);
lean_dec(v___x_384_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_411_; 
if (v_isShared_409_ == 0)
{
v___x_411_ = v___x_408_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_a_406_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
else
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
lean_dec(v_subst_366_);
lean_dec(v_eqFVarId_365_);
lean_dec(v_mvarId_364_);
v_a_414_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_421_ == 0)
{
v___x_416_ = v___x_380_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_380_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_414_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
v___jp_422_:
{
if (lean_obj_tag(v___y_423_) == 0)
{
lean_object* v_a_424_; uint8_t v___x_425_; 
v_a_424_ = lean_ctor_get(v___y_423_, 0);
lean_inc(v_a_424_);
lean_dec_ref_known(v___y_423_, 1);
v___x_425_ = lean_unbox(v_a_424_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; 
lean_inc(v_a_375_);
lean_inc_ref(v_a_374_);
lean_inc(v_a_373_);
lean_inc_ref(v_a_372_);
lean_inc_ref(v_a_370_);
v___x_426_ = lean_whnf(v_a_370_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_a_427_; lean_object* v___x_428_; 
v_a_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_a_427_);
lean_dec_ref_known(v___x_426_, 1);
lean_inc(v_a_375_);
lean_inc_ref(v_a_374_);
lean_inc(v_a_373_);
lean_inc_ref(v_a_372_);
lean_inc_ref(v_b_371_);
v___x_428_ = lean_whnf(v_b_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; uint8_t v___x_430_; uint8_t v___x_431_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_a_429_);
lean_dec_ref_known(v___x_428_, 1);
v___x_430_ = lean_expr_eqv(v_a_427_, v_a_370_);
lean_dec_ref(v_a_370_);
v___x_431_ = lean_bool_not(v___x_430_);
if (v___x_431_ == 0)
{
uint8_t v___x_432_; uint8_t v___x_433_; 
v___x_432_ = lean_expr_eqv(v_a_429_, v_b_371_);
lean_dec_ref(v_b_371_);
v___x_433_ = lean_bool_not(v___x_432_);
if (v___x_433_ == 0)
{
lean_dec(v_a_429_);
lean_dec(v_a_427_);
lean_dec(v_subst_366_);
lean_dec(v_eqFVarId_365_);
lean_dec(v_mvarId_364_);
if (lean_obj_tag(v_caseName_x3f_367_) == 0)
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
lean_dec(v_a_424_);
v___x_434_ = lean_obj_once(&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1, &l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1_once, _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1);
v___x_435_ = l_Lean_LocalDecl_type(v_eqDecl_368_);
v___x_436_ = l_Lean_indentExpr(v___x_435_);
v___x_437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_437_, 0, v___x_434_);
lean_ctor_set(v___x_437_, 1, v___x_436_);
v___x_438_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(v___x_437_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
return v___x_438_;
}
else
{
lean_object* v_val_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; uint8_t v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v_val_439_ = lean_ctor_get(v_caseName_x3f_367_, 0);
lean_inc(v_val_439_);
lean_dec_ref_known(v_caseName_x3f_367_, 1);
v___x_440_ = lean_obj_once(&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1, &l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1_once, _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1);
v___x_441_ = l_Lean_LocalDecl_type(v_eqDecl_368_);
v___x_442_ = l_Lean_indentExpr(v___x_441_);
v___x_443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_443_, 0, v___x_440_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
v___x_444_ = lean_obj_once(&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__1, &l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__1_once, _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__1);
v___x_445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_443_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
v___x_446_ = lean_unbox(v_a_424_);
lean_dec(v_a_424_);
v___x_447_ = l_Lean_MessageData_ofConstName(v_val_439_, v___x_446_);
v___x_448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_445_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
v___x_449_ = lean_obj_once(&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__3, &l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__3_once, _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__3);
v___x_450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_450_, 0, v___x_448_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
v___x_451_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(v___x_450_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
return v___x_451_;
}
}
else
{
lean_dec(v_a_424_);
lean_dec(v_caseName_x3f_367_);
v___y_378_ = v_a_427_;
v___y_379_ = v_a_429_;
goto v___jp_377_;
}
}
else
{
lean_dec(v_a_424_);
lean_dec_ref(v_b_371_);
lean_dec(v_caseName_x3f_367_);
v___y_378_ = v_a_427_;
v___y_379_ = v_a_429_;
goto v___jp_377_;
}
}
else
{
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_459_; 
lean_dec(v_a_427_);
lean_dec(v_a_424_);
lean_dec_ref(v_b_371_);
lean_dec_ref(v_a_370_);
lean_dec(v_caseName_x3f_367_);
lean_dec(v_subst_366_);
lean_dec(v_eqFVarId_365_);
lean_dec(v_mvarId_364_);
v_a_452_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_459_ == 0)
{
v___x_454_ = v___x_428_;
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_428_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
if (v_isShared_455_ == 0)
{
v___x_457_ = v___x_454_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_a_452_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
else
{
lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_467_; 
lean_dec(v_a_424_);
lean_dec_ref(v_b_371_);
lean_dec_ref(v_a_370_);
lean_dec(v_caseName_x3f_367_);
lean_dec(v_subst_366_);
lean_dec(v_eqFVarId_365_);
lean_dec(v_mvarId_364_);
v_a_460_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_467_ == 0)
{
v___x_462_ = v___x_426_;
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v___x_426_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_465_; 
if (v_isShared_463_ == 0)
{
v___x_465_ = v___x_462_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_a_460_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
else
{
lean_object* v___x_468_; 
lean_dec(v_a_424_);
lean_dec_ref(v_b_371_);
lean_dec_ref(v_a_370_);
lean_dec(v_caseName_x3f_367_);
v___x_468_ = l_Lean_Meta_injectionCore(v_mvarId_364_, v_eqFVarId_365_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_484_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_484_ == 0)
{
v___x_471_ = v___x_468_;
v_isShared_472_ = v_isSharedCheck_484_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_468_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_484_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
if (lean_obj_tag(v_a_469_) == 0)
{
lean_object* v___x_473_; lean_object* v___x_475_; 
lean_dec(v_subst_366_);
v___x_473_ = lean_box(0);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 0, v___x_473_);
v___x_475_ = v___x_471_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___x_473_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
else
{
lean_object* v_mvarId_477_; lean_object* v_numNewEqs_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_482_; 
v_mvarId_477_ = lean_ctor_get(v_a_469_, 0);
lean_inc(v_mvarId_477_);
v_numNewEqs_478_ = lean_ctor_get(v_a_469_, 1);
lean_inc(v_numNewEqs_478_);
lean_dec_ref_known(v_a_469_, 2);
v___x_479_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_479_, 0, v_mvarId_477_);
lean_ctor_set(v___x_479_, 1, v_subst_366_);
lean_ctor_set(v___x_479_, 2, v_numNewEqs_478_);
v___x_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 0, v___x_480_);
v___x_482_ = v___x_471_;
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
}
else
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_492_; 
lean_dec(v_subst_366_);
v_a_485_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_492_ == 0)
{
v___x_487_ = v___x_468_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_468_);
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
}
else
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_500_; 
lean_dec_ref(v_b_371_);
lean_dec_ref(v_a_370_);
lean_dec(v_caseName_x3f_367_);
lean_dec(v_subst_366_);
lean_dec(v_eqFVarId_365_);
lean_dec(v_mvarId_364_);
v_a_493_ = lean_ctor_get(v___y_423_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v___y_423_);
if (v_isSharedCheck_500_ == 0)
{
v___x_495_ = v___y_423_;
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___y_423_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___boxed(lean_object* v_mvarId_532_, lean_object* v_eqFVarId_533_, lean_object* v_subst_534_, lean_object* v_caseName_x3f_535_, lean_object* v_eqDecl_536_, lean_object* v_injectionOffset_x3f_537_, lean_object* v_a_538_, lean_object* v_b_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection(v_mvarId_532_, v_eqFVarId_533_, v_subst_534_, v_caseName_x3f_535_, v_eqDecl_536_, v_injectionOffset_x3f_537_, v_a_538_, v_b_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_);
lean_dec(v_a_543_);
lean_dec_ref(v_a_542_);
lean_dec(v_a_541_);
lean_dec_ref(v_a_540_);
lean_dec_ref(v_eqDecl_536_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__0___redArg(lean_object* v_e_546_, lean_object* v___y_547_){
_start:
{
uint8_t v___x_549_; uint8_t v___x_550_; 
v___x_549_ = l_Lean_Expr_hasMVar(v_e_546_);
v___x_550_ = lean_bool_not(v___x_549_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; lean_object* v_mctx_552_; lean_object* v___x_553_; lean_object* v_fst_554_; lean_object* v_snd_555_; lean_object* v___x_556_; lean_object* v_cache_557_; lean_object* v_zetaDeltaFVarIds_558_; lean_object* v_postponed_559_; lean_object* v_diag_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_569_; 
v___x_551_ = lean_st_ref_get(v___y_547_);
v_mctx_552_ = lean_ctor_get(v___x_551_, 0);
lean_inc_ref(v_mctx_552_);
lean_dec(v___x_551_);
v___x_553_ = l_Lean_instantiateMVarsCore(v_mctx_552_, v_e_546_);
v_fst_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_fst_554_);
v_snd_555_ = lean_ctor_get(v___x_553_, 1);
lean_inc(v_snd_555_);
lean_dec_ref(v___x_553_);
v___x_556_ = lean_st_ref_take(v___y_547_);
v_cache_557_ = lean_ctor_get(v___x_556_, 1);
v_zetaDeltaFVarIds_558_ = lean_ctor_get(v___x_556_, 2);
v_postponed_559_ = lean_ctor_get(v___x_556_, 3);
v_diag_560_ = lean_ctor_get(v___x_556_, 4);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_569_ == 0)
{
lean_object* v_unused_570_; 
v_unused_570_ = lean_ctor_get(v___x_556_, 0);
lean_dec(v_unused_570_);
v___x_562_ = v___x_556_;
v_isShared_563_ = v_isSharedCheck_569_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_diag_560_);
lean_inc(v_postponed_559_);
lean_inc(v_zetaDeltaFVarIds_558_);
lean_inc(v_cache_557_);
lean_dec(v___x_556_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_569_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 0, v_snd_555_);
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_snd_555_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v_cache_557_);
lean_ctor_set(v_reuseFailAlloc_568_, 2, v_zetaDeltaFVarIds_558_);
lean_ctor_set(v_reuseFailAlloc_568_, 3, v_postponed_559_);
lean_ctor_set(v_reuseFailAlloc_568_, 4, v_diag_560_);
v___x_565_ = v_reuseFailAlloc_568_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = lean_st_ref_set(v___y_547_, v___x_565_);
v___x_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_567_, 0, v_fst_554_);
return v___x_567_;
}
}
}
else
{
lean_object* v___x_571_; 
v___x_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_571_, 0, v_e_546_);
return v___x_571_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__0___redArg___boxed(lean_object* v_e_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__0___redArg(v_e_572_, v___y_573_);
lean_dec(v___y_573_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__0(lean_object* v_e_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__0___redArg(v_e_576_, v___y_578_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__0___boxed(lean_object* v_e_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__0(v_e_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___redArg(lean_object* v_mvarId_590_, lean_object* v_x_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_590_, v_x_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_597_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_597_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_598_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
v_a_606_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_597_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_597_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___redArg___boxed(lean_object* v_mvarId_614_, lean_object* v_x_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___redArg(v_mvarId_614_, v_x_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2(lean_object* v_00_u03b1_622_, lean_object* v_mvarId_623_, lean_object* v_x_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___redArg(v_mvarId_623_, v_x_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___boxed(lean_object* v_00_u03b1_631_, lean_object* v_mvarId_632_, lean_object* v_x_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2(v_00_u03b1_631_, v_mvarId_632_, v_x_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_640_, lean_object* v_x_641_, lean_object* v_x_642_, lean_object* v_x_643_){
_start:
{
lean_object* v_ks_644_; lean_object* v_vs_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_669_; 
v_ks_644_ = lean_ctor_get(v_x_640_, 0);
v_vs_645_ = lean_ctor_get(v_x_640_, 1);
v_isSharedCheck_669_ = !lean_is_exclusive(v_x_640_);
if (v_isSharedCheck_669_ == 0)
{
v___x_647_ = v_x_640_;
v_isShared_648_ = v_isSharedCheck_669_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_vs_645_);
lean_inc(v_ks_644_);
lean_dec(v_x_640_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_669_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_649_; uint8_t v___x_650_; 
v___x_649_ = lean_array_get_size(v_ks_644_);
v___x_650_ = lean_nat_dec_lt(v_x_641_, v___x_649_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_654_; 
lean_dec(v_x_641_);
v___x_651_ = lean_array_push(v_ks_644_, v_x_642_);
v___x_652_ = lean_array_push(v_vs_645_, v_x_643_);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 1, v___x_652_);
lean_ctor_set(v___x_647_, 0, v___x_651_);
v___x_654_ = v___x_647_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v___x_652_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
else
{
lean_object* v_k_x27_656_; uint8_t v___x_657_; 
v_k_x27_656_ = lean_array_fget_borrowed(v_ks_644_, v_x_641_);
v___x_657_ = l_Lean_instBEqMVarId_beq(v_x_642_, v_k_x27_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_659_; 
if (v_isShared_648_ == 0)
{
v___x_659_ = v___x_647_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_ks_644_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v_vs_645_);
v___x_659_ = v_reuseFailAlloc_663_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = lean_unsigned_to_nat(1u);
v___x_661_ = lean_nat_add(v_x_641_, v___x_660_);
lean_dec(v_x_641_);
v_x_640_ = v___x_659_;
v_x_641_ = v___x_661_;
goto _start;
}
}
else
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_667_; 
v___x_664_ = lean_array_fset(v_ks_644_, v_x_641_, v_x_642_);
v___x_665_ = lean_array_fset(v_vs_645_, v_x_641_, v_x_643_);
lean_dec(v_x_641_);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 1, v___x_665_);
lean_ctor_set(v___x_647_, 0, v___x_664_);
v___x_667_ = v___x_647_;
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__4___redArg(lean_object* v_n_670_, lean_object* v_k_671_, lean_object* v_v_672_){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_unsigned_to_nat(0u);
v___x_674_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(v_n_670_, v___x_673_, v_k_671_, v_v_672_);
return v___x_674_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg(lean_object* v_x_676_, size_t v_x_677_, size_t v_x_678_, lean_object* v_x_679_, lean_object* v_x_680_){
_start:
{
if (lean_obj_tag(v_x_676_) == 0)
{
lean_object* v_es_681_; size_t v___x_682_; size_t v___x_683_; lean_object* v_j_684_; lean_object* v___x_685_; uint8_t v___x_686_; 
v_es_681_ = lean_ctor_get(v_x_676_, 0);
v___x_682_ = ((size_t)31ULL);
v___x_683_ = lean_usize_land(v_x_677_, v___x_682_);
v_j_684_ = lean_usize_to_nat(v___x_683_);
v___x_685_ = lean_array_get_size(v_es_681_);
v___x_686_ = lean_nat_dec_lt(v_j_684_, v___x_685_);
if (v___x_686_ == 0)
{
lean_dec(v_j_684_);
lean_dec(v_x_680_);
lean_dec(v_x_679_);
return v_x_676_;
}
else
{
lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_725_; 
lean_inc_ref(v_es_681_);
v_isSharedCheck_725_ = !lean_is_exclusive(v_x_676_);
if (v_isSharedCheck_725_ == 0)
{
lean_object* v_unused_726_; 
v_unused_726_ = lean_ctor_get(v_x_676_, 0);
lean_dec(v_unused_726_);
v___x_688_ = v_x_676_;
v_isShared_689_ = v_isSharedCheck_725_;
goto v_resetjp_687_;
}
else
{
lean_dec(v_x_676_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_725_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v_v_690_; lean_object* v___x_691_; lean_object* v_xs_x27_692_; lean_object* v___y_694_; 
v_v_690_ = lean_array_fget(v_es_681_, v_j_684_);
v___x_691_ = lean_box(0);
v_xs_x27_692_ = lean_array_fset(v_es_681_, v_j_684_, v___x_691_);
switch(lean_obj_tag(v_v_690_))
{
case 0:
{
lean_object* v_key_699_; lean_object* v_val_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_710_; 
v_key_699_ = lean_ctor_get(v_v_690_, 0);
v_val_700_ = lean_ctor_get(v_v_690_, 1);
v_isSharedCheck_710_ = !lean_is_exclusive(v_v_690_);
if (v_isSharedCheck_710_ == 0)
{
v___x_702_ = v_v_690_;
v_isShared_703_ = v_isSharedCheck_710_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_val_700_);
lean_inc(v_key_699_);
lean_dec(v_v_690_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_710_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
uint8_t v___x_704_; 
v___x_704_ = l_Lean_instBEqMVarId_beq(v_x_679_, v_key_699_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; lean_object* v___x_706_; 
lean_del_object(v___x_702_);
v___x_705_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_699_, v_val_700_, v_x_679_, v_x_680_);
v___x_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
v___y_694_ = v___x_706_;
goto v___jp_693_;
}
else
{
lean_object* v___x_708_; 
lean_dec(v_val_700_);
lean_dec(v_key_699_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 1, v_x_680_);
lean_ctor_set(v___x_702_, 0, v_x_679_);
v___x_708_ = v___x_702_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_x_679_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v_x_680_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
v___y_694_ = v___x_708_;
goto v___jp_693_;
}
}
}
}
case 1:
{
lean_object* v_node_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_723_; 
v_node_711_ = lean_ctor_get(v_v_690_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v_v_690_);
if (v_isSharedCheck_723_ == 0)
{
v___x_713_ = v_v_690_;
v_isShared_714_ = v_isSharedCheck_723_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_node_711_);
lean_dec(v_v_690_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_723_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
size_t v___x_715_; size_t v___x_716_; size_t v___x_717_; size_t v___x_718_; lean_object* v___x_719_; lean_object* v___x_721_; 
v___x_715_ = ((size_t)5ULL);
v___x_716_ = lean_usize_shift_right(v_x_677_, v___x_715_);
v___x_717_ = ((size_t)1ULL);
v___x_718_ = lean_usize_add(v_x_678_, v___x_717_);
v___x_719_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg(v_node_711_, v___x_716_, v___x_718_, v_x_679_, v_x_680_);
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 0, v___x_719_);
v___x_721_ = v___x_713_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_719_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
v___y_694_ = v___x_721_;
goto v___jp_693_;
}
}
}
default: 
{
lean_object* v___x_724_; 
v___x_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_724_, 0, v_x_679_);
lean_ctor_set(v___x_724_, 1, v_x_680_);
v___y_694_ = v___x_724_;
goto v___jp_693_;
}
}
v___jp_693_:
{
lean_object* v___x_695_; lean_object* v___x_697_; 
v___x_695_ = lean_array_fset(v_xs_x27_692_, v_j_684_, v___y_694_);
lean_dec(v_j_684_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v___x_695_);
v___x_697_ = v___x_688_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_695_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
}
else
{
lean_object* v_ks_727_; lean_object* v_vs_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_748_; 
v_ks_727_ = lean_ctor_get(v_x_676_, 0);
v_vs_728_ = lean_ctor_get(v_x_676_, 1);
v_isSharedCheck_748_ = !lean_is_exclusive(v_x_676_);
if (v_isSharedCheck_748_ == 0)
{
v___x_730_ = v_x_676_;
v_isShared_731_ = v_isSharedCheck_748_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_vs_728_);
lean_inc(v_ks_727_);
lean_dec(v_x_676_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_748_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_ks_727_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_vs_728_);
v___x_733_ = v_reuseFailAlloc_747_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v_newNode_734_; uint8_t v___y_736_; size_t v___x_742_; uint8_t v___x_743_; 
v_newNode_734_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__4___redArg(v___x_733_, v_x_679_, v_x_680_);
v___x_742_ = ((size_t)7ULL);
v___x_743_ = lean_usize_dec_le(v___x_742_, v_x_678_);
if (v___x_743_ == 0)
{
lean_object* v___x_744_; lean_object* v___x_745_; uint8_t v___x_746_; 
v___x_744_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_734_);
v___x_745_ = lean_unsigned_to_nat(4u);
v___x_746_ = lean_nat_dec_lt(v___x_744_, v___x_745_);
lean_dec(v___x_744_);
v___y_736_ = v___x_746_;
goto v___jp_735_;
}
else
{
v___y_736_ = v___x_743_;
goto v___jp_735_;
}
v___jp_735_:
{
if (v___y_736_ == 0)
{
lean_object* v_ks_737_; lean_object* v_vs_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v_ks_737_ = lean_ctor_get(v_newNode_734_, 0);
lean_inc_ref(v_ks_737_);
v_vs_738_ = lean_ctor_get(v_newNode_734_, 1);
lean_inc_ref(v_vs_738_);
lean_dec_ref(v_newNode_734_);
v___x_739_ = lean_unsigned_to_nat(0u);
v___x_740_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_741_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_x_678_, v_ks_737_, v_vs_738_, v___x_739_, v___x_740_);
lean_dec_ref(v_vs_738_);
lean_dec_ref(v_ks_737_);
return v___x_741_;
}
else
{
return v_newNode_734_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__5___redArg(size_t v_depth_749_, lean_object* v_keys_750_, lean_object* v_vals_751_, lean_object* v_i_752_, lean_object* v_entries_753_){
_start:
{
lean_object* v___x_754_; uint8_t v___x_755_; 
v___x_754_ = lean_array_get_size(v_keys_750_);
v___x_755_ = lean_nat_dec_lt(v_i_752_, v___x_754_);
if (v___x_755_ == 0)
{
lean_dec(v_i_752_);
return v_entries_753_;
}
else
{
lean_object* v_k_756_; lean_object* v_v_757_; uint64_t v___x_758_; size_t v_h_759_; size_t v___x_760_; lean_object* v___x_761_; size_t v___x_762_; size_t v___x_763_; size_t v___x_764_; size_t v_h_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v_k_756_ = lean_array_fget_borrowed(v_keys_750_, v_i_752_);
v_v_757_ = lean_array_fget_borrowed(v_vals_751_, v_i_752_);
v___x_758_ = l_Lean_instHashableMVarId_hash(v_k_756_);
v_h_759_ = lean_uint64_to_usize(v___x_758_);
v___x_760_ = ((size_t)5ULL);
v___x_761_ = lean_unsigned_to_nat(1u);
v___x_762_ = ((size_t)1ULL);
v___x_763_ = lean_usize_sub(v_depth_749_, v___x_762_);
v___x_764_ = lean_usize_mul(v___x_760_, v___x_763_);
v_h_765_ = lean_usize_shift_right(v_h_759_, v___x_764_);
v___x_766_ = lean_nat_add(v_i_752_, v___x_761_);
lean_dec(v_i_752_);
lean_inc(v_v_757_);
lean_inc(v_k_756_);
v___x_767_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg(v_entries_753_, v_h_765_, v_depth_749_, v_k_756_, v_v_757_);
v_i_752_ = v___x_766_;
v_entries_753_ = v___x_767_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_depth_769_, lean_object* v_keys_770_, lean_object* v_vals_771_, lean_object* v_i_772_, lean_object* v_entries_773_){
_start:
{
size_t v_depth_boxed_774_; lean_object* v_res_775_; 
v_depth_boxed_774_ = lean_unbox_usize(v_depth_769_);
lean_dec(v_depth_769_);
v_res_775_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_depth_boxed_774_, v_keys_770_, v_vals_771_, v_i_772_, v_entries_773_);
lean_dec_ref(v_vals_771_);
lean_dec_ref(v_keys_770_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_776_, lean_object* v_x_777_, lean_object* v_x_778_, lean_object* v_x_779_, lean_object* v_x_780_){
_start:
{
size_t v_x_9336__boxed_781_; size_t v_x_9337__boxed_782_; lean_object* v_res_783_; 
v_x_9336__boxed_781_ = lean_unbox_usize(v_x_777_);
lean_dec(v_x_777_);
v_x_9337__boxed_782_ = lean_unbox_usize(v_x_778_);
lean_dec(v_x_778_);
v_res_783_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg(v_x_776_, v_x_9336__boxed_781_, v_x_9337__boxed_782_, v_x_779_, v_x_780_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1___redArg(lean_object* v_x_784_, lean_object* v_x_785_, lean_object* v_x_786_){
_start:
{
uint64_t v___x_787_; size_t v___x_788_; size_t v___x_789_; lean_object* v___x_790_; 
v___x_787_ = l_Lean_instHashableMVarId_hash(v_x_785_);
v___x_788_ = lean_uint64_to_usize(v___x_787_);
v___x_789_ = ((size_t)1ULL);
v___x_790_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg(v_x_784_, v___x_788_, v___x_789_, v_x_785_, v_x_786_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1___redArg(lean_object* v_mvarId_791_, lean_object* v_val_792_, lean_object* v___y_793_){
_start:
{
lean_object* v___x_795_; lean_object* v_mctx_796_; lean_object* v_cache_797_; lean_object* v_zetaDeltaFVarIds_798_; lean_object* v_postponed_799_; lean_object* v_diag_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_828_; 
v___x_795_ = lean_st_ref_take(v___y_793_);
v_mctx_796_ = lean_ctor_get(v___x_795_, 0);
v_cache_797_ = lean_ctor_get(v___x_795_, 1);
v_zetaDeltaFVarIds_798_ = lean_ctor_get(v___x_795_, 2);
v_postponed_799_ = lean_ctor_get(v___x_795_, 3);
v_diag_800_ = lean_ctor_get(v___x_795_, 4);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_828_ == 0)
{
v___x_802_ = v___x_795_;
v_isShared_803_ = v_isSharedCheck_828_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_diag_800_);
lean_inc(v_postponed_799_);
lean_inc(v_zetaDeltaFVarIds_798_);
lean_inc(v_cache_797_);
lean_inc(v_mctx_796_);
lean_dec(v___x_795_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_828_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v_depth_804_; lean_object* v_levelAssignDepth_805_; lean_object* v_lmvarCounter_806_; lean_object* v_mvarCounter_807_; lean_object* v_lDecls_808_; lean_object* v_decls_809_; lean_object* v_userNames_810_; lean_object* v_lAssignment_811_; lean_object* v_eAssignment_812_; lean_object* v_dAssignment_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_827_; 
v_depth_804_ = lean_ctor_get(v_mctx_796_, 0);
v_levelAssignDepth_805_ = lean_ctor_get(v_mctx_796_, 1);
v_lmvarCounter_806_ = lean_ctor_get(v_mctx_796_, 2);
v_mvarCounter_807_ = lean_ctor_get(v_mctx_796_, 3);
v_lDecls_808_ = lean_ctor_get(v_mctx_796_, 4);
v_decls_809_ = lean_ctor_get(v_mctx_796_, 5);
v_userNames_810_ = lean_ctor_get(v_mctx_796_, 6);
v_lAssignment_811_ = lean_ctor_get(v_mctx_796_, 7);
v_eAssignment_812_ = lean_ctor_get(v_mctx_796_, 8);
v_dAssignment_813_ = lean_ctor_get(v_mctx_796_, 9);
v_isSharedCheck_827_ = !lean_is_exclusive(v_mctx_796_);
if (v_isSharedCheck_827_ == 0)
{
v___x_815_ = v_mctx_796_;
v_isShared_816_ = v_isSharedCheck_827_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_dAssignment_813_);
lean_inc(v_eAssignment_812_);
lean_inc(v_lAssignment_811_);
lean_inc(v_userNames_810_);
lean_inc(v_decls_809_);
lean_inc(v_lDecls_808_);
lean_inc(v_mvarCounter_807_);
lean_inc(v_lmvarCounter_806_);
lean_inc(v_levelAssignDepth_805_);
lean_inc(v_depth_804_);
lean_dec(v_mctx_796_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_827_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_817_; lean_object* v___x_819_; 
v___x_817_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1___redArg(v_eAssignment_812_, v_mvarId_791_, v_val_792_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 8, v___x_817_);
v___x_819_ = v___x_815_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_depth_804_);
lean_ctor_set(v_reuseFailAlloc_826_, 1, v_levelAssignDepth_805_);
lean_ctor_set(v_reuseFailAlloc_826_, 2, v_lmvarCounter_806_);
lean_ctor_set(v_reuseFailAlloc_826_, 3, v_mvarCounter_807_);
lean_ctor_set(v_reuseFailAlloc_826_, 4, v_lDecls_808_);
lean_ctor_set(v_reuseFailAlloc_826_, 5, v_decls_809_);
lean_ctor_set(v_reuseFailAlloc_826_, 6, v_userNames_810_);
lean_ctor_set(v_reuseFailAlloc_826_, 7, v_lAssignment_811_);
lean_ctor_set(v_reuseFailAlloc_826_, 8, v___x_817_);
lean_ctor_set(v_reuseFailAlloc_826_, 9, v_dAssignment_813_);
v___x_819_ = v_reuseFailAlloc_826_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
lean_object* v___x_821_; 
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 0, v___x_819_);
v___x_821_ = v___x_802_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_819_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v_cache_797_);
lean_ctor_set(v_reuseFailAlloc_825_, 2, v_zetaDeltaFVarIds_798_);
lean_ctor_set(v_reuseFailAlloc_825_, 3, v_postponed_799_);
lean_ctor_set(v_reuseFailAlloc_825_, 4, v_diag_800_);
v___x_821_ = v_reuseFailAlloc_825_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_822_ = lean_st_ref_set(v___y_793_, v___x_821_);
v___x_823_ = lean_box(0);
v___x_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_824_, 0, v___x_823_);
return v___x_824_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1___redArg___boxed(lean_object* v_mvarId_829_, lean_object* v_val_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1___redArg(v_mvarId_829_, v_val_830_, v___y_831_);
lean_dec(v___y_831_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__0(uint8_t v___x_841_, lean_object* v_mvarId_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_b_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v___x_851_; lean_object* v_env_852_; lean_object* v___x_853_; lean_object* v_fst_855_; lean_object* v_fst_856_; lean_object* v_snd_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; uint8_t v___x_964_; 
v___x_851_ = lean_st_ref_get(v___y_849_);
v_env_852_ = lean_ctor_get(v___x_851_, 0);
lean_inc_ref(v_env_852_);
lean_dec(v___x_851_);
v___x_853_ = ((lean_object*)(l_Lean_Meta_unifyEq_x3f___lam__0___closed__3));
v___x_964_ = l_Lean_Environment_contains(v_env_852_, v___x_853_, v___x_841_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; lean_object* v___x_966_; 
lean_dec_ref(v_b_845_);
lean_dec_ref(v_a_844_);
lean_dec_ref(v_a_843_);
lean_dec(v_mvarId_842_);
v___x_965_ = lean_box(0);
v___x_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
return v___x_966_;
}
else
{
lean_object* v___x_967_; 
v___x_967_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f(v_a_844_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_1034_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_970_ = v___x_967_;
v_isShared_971_ = v_isSharedCheck_1034_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_967_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_1034_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
if (lean_obj_tag(v_a_968_) == 1)
{
lean_object* v_val_972_; lean_object* v_fst_973_; lean_object* v_snd_974_; lean_object* v___x_975_; 
v_val_972_ = lean_ctor_get(v_a_968_, 0);
lean_inc(v_val_972_);
lean_dec_ref_known(v_a_968_, 1);
v_fst_973_ = lean_ctor_get(v_val_972_, 0);
lean_inc(v_fst_973_);
v_snd_974_ = lean_ctor_get(v_val_972_, 1);
lean_inc(v_snd_974_);
lean_dec(v_val_972_);
v___x_975_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f(v_b_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_1021_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_978_ = v___x_975_;
v_isShared_979_ = v_isSharedCheck_1021_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_975_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_1021_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
if (lean_obj_tag(v_a_976_) == 1)
{
lean_object* v_val_985_; lean_object* v_fst_986_; lean_object* v_snd_987_; lean_object* v___x_988_; uint8_t v___x_989_; 
lean_del_object(v___x_970_);
v_val_985_ = lean_ctor_get(v_a_976_, 0);
lean_inc(v_val_985_);
lean_dec_ref_known(v_a_976_, 1);
v_fst_986_ = lean_ctor_get(v_val_985_, 0);
lean_inc(v_fst_986_);
v_snd_987_ = lean_ctor_get(v_val_985_, 1);
lean_inc(v_snd_987_);
lean_dec(v_val_985_);
v___x_988_ = lean_unsigned_to_nat(0u);
v___x_989_ = lean_nat_dec_eq(v_snd_974_, v___x_988_);
if (v___x_989_ == 0)
{
uint8_t v___x_990_; 
v___x_990_ = lean_nat_dec_eq(v_snd_987_, v___x_988_);
if (v___x_990_ == 0)
{
uint8_t v___x_991_; 
lean_del_object(v___x_978_);
v___x_991_ = lean_nat_dec_lt(v_snd_974_, v_snd_987_);
if (v___x_991_ == 0)
{
uint8_t v___x_992_; 
v___x_992_ = lean_nat_dec_eq(v_snd_974_, v_snd_987_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_993_ = lean_nat_sub(v_snd_974_, v_snd_987_);
lean_dec(v_snd_974_);
v___x_994_ = l_Lean_mkNatLit(v___x_993_);
v___x_995_ = l_Lean_Meta_mkAdd(v_fst_973_, v___x_994_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_object* v_a_996_; 
v_a_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc(v_a_996_);
lean_dec_ref_known(v___x_995_, 1);
v_fst_855_ = v_a_996_;
v_fst_856_ = v_fst_986_;
v_snd_857_ = v_snd_987_;
v___y_858_ = v___y_846_;
v___y_859_ = v___y_847_;
v___y_860_ = v___y_848_;
v___y_861_ = v___y_849_;
goto v___jp_854_;
}
else
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1004_; 
lean_dec(v_snd_987_);
lean_dec(v_fst_986_);
lean_dec_ref(v_a_843_);
lean_dec(v_mvarId_842_);
v_a_997_ = lean_ctor_get(v___x_995_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_999_ = v___x_995_;
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_995_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1002_; 
if (v_isShared_1000_ == 0)
{
v___x_1002_ = v___x_999_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_a_997_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
}
else
{
lean_dec(v_snd_987_);
v_fst_855_ = v_fst_973_;
v_fst_856_ = v_fst_986_;
v_snd_857_ = v_snd_974_;
v___y_858_ = v___y_846_;
v___y_859_ = v___y_847_;
v___y_860_ = v___y_848_;
v___y_861_ = v___y_849_;
goto v___jp_854_;
}
}
else
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1005_ = lean_nat_sub(v_snd_987_, v_snd_974_);
lean_dec(v_snd_987_);
v___x_1006_ = l_Lean_mkNatLit(v___x_1005_);
v___x_1007_ = l_Lean_Meta_mkAdd(v_fst_986_, v___x_1006_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_a_1008_);
lean_dec_ref_known(v___x_1007_, 1);
v_fst_855_ = v_fst_973_;
v_fst_856_ = v_a_1008_;
v_snd_857_ = v_snd_974_;
v___y_858_ = v___y_846_;
v___y_859_ = v___y_847_;
v___y_860_ = v___y_848_;
v___y_861_ = v___y_849_;
goto v___jp_854_;
}
else
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
lean_dec(v_snd_974_);
lean_dec(v_fst_973_);
lean_dec_ref(v_a_843_);
lean_dec(v_mvarId_842_);
v_a_1009_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1011_ = v___x_1007_;
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_1007_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_a_1009_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
}
else
{
lean_dec(v_snd_987_);
lean_dec(v_fst_986_);
lean_dec(v_snd_974_);
lean_dec(v_fst_973_);
lean_dec_ref(v_a_843_);
lean_dec(v_mvarId_842_);
goto v___jp_980_;
}
}
else
{
lean_dec(v_snd_987_);
lean_dec(v_fst_986_);
lean_dec(v_snd_974_);
lean_dec(v_fst_973_);
lean_dec_ref(v_a_843_);
lean_dec(v_mvarId_842_);
goto v___jp_980_;
}
}
else
{
lean_object* v___x_1017_; lean_object* v___x_1019_; 
lean_del_object(v___x_978_);
lean_dec(v_a_976_);
lean_dec(v_snd_974_);
lean_dec(v_fst_973_);
lean_dec_ref(v_a_843_);
lean_dec(v_mvarId_842_);
v___x_1017_ = lean_box(0);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 0, v___x_1017_);
v___x_1019_ = v___x_970_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1017_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
v___jp_980_:
{
lean_object* v___x_981_; lean_object* v___x_983_; 
v___x_981_ = lean_box(0);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v___x_981_);
v___x_983_ = v___x_978_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_981_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
lean_dec(v_snd_974_);
lean_dec(v_fst_973_);
lean_del_object(v___x_970_);
lean_dec_ref(v_a_843_);
lean_dec(v_mvarId_842_);
v_a_1022_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_975_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_975_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
else
{
lean_object* v___x_1030_; lean_object* v___x_1032_; 
lean_dec(v_a_968_);
lean_dec_ref(v_b_845_);
lean_dec_ref(v_a_843_);
lean_dec(v_mvarId_842_);
v___x_1030_ = lean_box(0);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 0, v___x_1030_);
v___x_1032_ = v___x_970_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1030_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
else
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
lean_dec_ref(v_b_845_);
lean_dec_ref(v_a_843_);
lean_dec(v_mvarId_842_);
v_a_1035_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1037_ = v___x_967_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_967_);
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
v___jp_854_:
{
lean_object* v___x_862_; 
lean_inc(v_mvarId_842_);
v___x_862_ = l_Lean_MVarId_getType(v_mvarId_842_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; lean_object* v___x_864_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc_n(v_a_863_, 2);
lean_dec_ref_known(v___x_862_, 1);
v___x_864_ = l_Lean_Meta_getLevel(v_a_863_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; lean_object* v___x_866_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_a_865_);
lean_dec_ref_known(v___x_864_, 1);
lean_inc_ref(v_fst_856_);
lean_inc_ref(v_fst_855_);
v___x_866_ = l_Lean_Meta_mkEq(v_fst_855_, v_fst_856_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; lean_object* v___x_868_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_867_);
lean_dec_ref_known(v___x_866_, 1);
lean_inc(v_a_863_);
v___x_868_ = l_Lean_mkArrow(v_a_867_, v_a_863_, v___y_860_, v___y_861_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; lean_object* v___x_870_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_a_869_);
lean_dec_ref_known(v___x_868_, 1);
lean_inc(v_mvarId_842_);
v___x_870_ = l_Lean_MVarId_getTag(v_mvarId_842_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_872_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
lean_inc(v_a_871_);
lean_dec_ref_known(v___x_870_, 1);
v___x_872_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_869_, v_a_871_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v_a_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_914_; 
v_a_873_ = lean_ctor_get(v___x_872_, 0);
lean_inc_n(v_a_873_, 2);
lean_dec_ref_known(v___x_872_, 1);
v___x_874_ = lean_box(0);
v___x_875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_875_, 0, v_a_865_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
v___x_876_ = l_Lean_mkConst(v___x_853_, v___x_875_);
v___x_877_ = l_Lean_mkNatLit(v_snd_857_);
lean_inc_ref(v_a_843_);
v___x_878_ = l_Lean_LocalDecl_toExpr(v_a_843_);
v___x_879_ = lean_unsigned_to_nat(6u);
v___x_880_ = lean_mk_empty_array_with_capacity(v___x_879_);
v___x_881_ = lean_array_push(v___x_880_, v_a_863_);
v___x_882_ = lean_array_push(v___x_881_, v_fst_855_);
v___x_883_ = lean_array_push(v___x_882_, v_fst_856_);
v___x_884_ = lean_array_push(v___x_883_, v___x_877_);
v___x_885_ = lean_array_push(v___x_884_, v___x_878_);
v___x_886_ = lean_array_push(v___x_885_, v_a_873_);
v___x_887_ = l_Lean_mkAppN(v___x_876_, v___x_886_);
lean_dec_ref(v___x_886_);
v___x_888_ = l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1___redArg(v_mvarId_842_, v___x_887_, v___y_859_);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_914_ == 0)
{
lean_object* v_unused_915_; 
v_unused_915_ = lean_ctor_get(v___x_888_, 0);
lean_dec(v_unused_915_);
v___x_890_ = v___x_888_;
v_isShared_891_ = v_isSharedCheck_914_;
goto v_resetjp_889_;
}
else
{
lean_dec(v___x_888_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_914_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_892_ = l_Lean_Expr_mvarId_x21(v_a_873_);
lean_dec(v_a_873_);
v___x_893_ = l_Lean_LocalDecl_fvarId(v_a_843_);
lean_dec_ref(v_a_843_);
v___x_894_ = l_Lean_MVarId_tryClear(v___x_892_, v___x_893_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_905_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_905_ == 0)
{
v___x_897_ = v___x_894_;
v_isShared_898_ = v_isSharedCheck_905_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_894_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_905_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_891_ == 0)
{
lean_ctor_set_tag(v___x_890_, 1);
lean_ctor_set(v___x_890_, 0, v_a_895_);
v___x_900_ = v___x_890_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_a_895_);
v___x_900_ = v_reuseFailAlloc_904_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
lean_object* v___x_902_; 
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v___x_900_);
v___x_902_ = v___x_897_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_900_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
else
{
lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_913_; 
lean_del_object(v___x_890_);
v_a_906_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_913_ == 0)
{
v___x_908_ = v___x_894_;
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v___x_894_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_911_; 
if (v_isShared_909_ == 0)
{
v___x_911_ = v___x_908_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_a_906_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
}
}
else
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
lean_dec(v_a_865_);
lean_dec(v_a_863_);
lean_dec(v_snd_857_);
lean_dec_ref(v_fst_856_);
lean_dec_ref(v_fst_855_);
lean_dec_ref(v_a_843_);
lean_dec(v_mvarId_842_);
v_a_916_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_923_ == 0)
{
v___x_918_ = v___x_872_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_872_);
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
lean_dec(v_a_869_);
lean_dec(v_a_865_);
lean_dec(v_a_863_);
lean_dec(v_snd_857_);
lean_dec_ref(v_fst_856_);
lean_dec_ref(v_fst_855_);
lean_dec_ref(v_a_843_);
lean_dec(v_mvarId_842_);
v_a_924_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_870_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_870_);
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
lean_dec(v_a_865_);
lean_dec(v_a_863_);
lean_dec(v_snd_857_);
lean_dec_ref(v_fst_856_);
lean_dec_ref(v_fst_855_);
lean_dec_ref(v_a_843_);
lean_dec(v_mvarId_842_);
v_a_932_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_939_ == 0)
{
v___x_934_ = v___x_868_;
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_868_);
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
lean_dec(v_a_865_);
lean_dec(v_a_863_);
lean_dec(v_snd_857_);
lean_dec_ref(v_fst_856_);
lean_dec_ref(v_fst_855_);
lean_dec_ref(v_a_843_);
lean_dec(v_mvarId_842_);
v_a_940_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_866_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_866_);
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
lean_dec(v_a_863_);
lean_dec(v_snd_857_);
lean_dec_ref(v_fst_856_);
lean_dec_ref(v_fst_855_);
lean_dec_ref(v_a_843_);
lean_dec(v_mvarId_842_);
v_a_948_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_864_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_864_);
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
lean_dec(v_snd_857_);
lean_dec_ref(v_fst_856_);
lean_dec_ref(v_fst_855_);
lean_dec_ref(v_a_843_);
lean_dec(v_mvarId_842_);
v_a_956_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_963_ == 0)
{
v___x_958_ = v___x_862_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_862_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__0___boxed(lean_object* v___x_1043_, lean_object* v_mvarId_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_b_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
uint8_t v___x_9563__boxed_1053_; lean_object* v_res_1054_; 
v___x_9563__boxed_1053_ = lean_unbox(v___x_1043_);
v_res_1054_ = l_Lean_Meta_unifyEq_x3f___lam__0(v___x_9563__boxed_1053_, v_mvarId_1044_, v_a_1045_, v_a_1046_, v_b_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
return v_res_1054_;
}
}
static lean_object* _init_l_Lean_Meta_unifyEq_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = ((lean_object*)(l_Lean_Meta_unifyEq_x3f___lam__1___closed__2));
v___x_1060_ = l_Lean_stringToMessageData(v___x_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__1(lean_object* v_eqFVarId_1061_, lean_object* v_mvarId_1062_, lean_object* v_subst_1063_, lean_object* v_acyclic_1064_, lean_object* v_caseName_x3f_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v___x_1071_; 
lean_inc(v_eqFVarId_1061_);
v___x_1071_ = l_Lean_FVarId_getDecl___redArg(v_eqFVarId_1061_, v___y_1066_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_a_1072_);
lean_dec_ref_known(v___x_1071_, 1);
v___x_1073_ = l_Lean_LocalDecl_type(v_a_1072_);
v___x_1074_ = l_Lean_Expr_isHEq(v___x_1073_);
if (v___x_1074_ == 0)
{
lean_object* v___x_1075_; lean_object* v___x_1076_; uint8_t v___x_1077_; 
v___x_1075_ = ((lean_object*)(l_Lean_Meta_unifyEq_x3f___lam__1___closed__1));
v___x_1076_ = lean_unsigned_to_nat(3u);
v___x_1077_ = l_Lean_Expr_isAppOfArity(v___x_1073_, v___x_1075_, v___x_1076_);
if (v___x_1077_ == 0)
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
lean_dec(v_a_1072_);
lean_dec(v_caseName_x3f_1065_);
lean_dec_ref(v_acyclic_1064_);
lean_dec(v_subst_1063_);
lean_dec(v_mvarId_1062_);
lean_dec(v_eqFVarId_1061_);
v___x_1078_ = lean_obj_once(&l_Lean_Meta_unifyEq_x3f___lam__1___closed__3, &l_Lean_Meta_unifyEq_x3f___lam__1___closed__3_once, _init_l_Lean_Meta_unifyEq_x3f___lam__1___closed__3);
v___x_1079_ = l_Lean_indentExpr(v___x_1073_);
v___x_1080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1078_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(v___x_1080_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1081_;
}
else
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v_a_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1082_ = l_Lean_Expr_appFn_x21(v___x_1073_);
v___x_1083_ = l_Lean_Expr_appArg_x21(v___x_1082_);
lean_dec_ref(v___x_1082_);
lean_inc_ref(v___x_1083_);
v___x_1084_ = l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__0___redArg(v___x_1083_, v___y_1067_);
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_a_1085_);
lean_dec_ref(v___x_1084_);
v___x_1086_ = l_Lean_Expr_appArg_x21(v___x_1073_);
lean_dec_ref(v___x_1073_);
lean_inc_ref(v___x_1086_);
v___x_1087_ = l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__0___redArg(v___x_1086_, v___y_1067_);
if (lean_obj_tag(v_a_1085_) == 1)
{
lean_object* v_a_1088_; 
lean_dec(v_caseName_x3f_1065_);
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_a_1088_);
lean_dec_ref(v___x_1087_);
if (lean_obj_tag(v_a_1088_) == 1)
{
lean_object* v_fvarId_1089_; lean_object* v_fvarId_1090_; lean_object* v___x_1091_; 
v_fvarId_1089_ = lean_ctor_get(v_a_1085_, 0);
lean_inc(v_fvarId_1089_);
lean_dec_ref_known(v_a_1085_, 1);
v_fvarId_1090_ = lean_ctor_get(v_a_1088_, 0);
lean_inc(v_fvarId_1090_);
lean_dec_ref_known(v_a_1088_, 1);
v___x_1091_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1089_, v___y_1066_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; lean_object* v___x_1093_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc(v_a_1092_);
lean_dec_ref_known(v___x_1091_, 1);
v___x_1093_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1090_, v___y_1066_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_a_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; uint8_t v___x_1097_; lean_object* v___x_1098_; 
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
lean_inc(v_a_1094_);
lean_dec_ref_known(v___x_1093_, 1);
v___x_1095_ = l_Lean_LocalDecl_index(v_a_1092_);
lean_dec(v_a_1092_);
v___x_1096_ = l_Lean_LocalDecl_index(v_a_1094_);
lean_dec(v_a_1094_);
v___x_1097_ = lean_nat_dec_lt(v___x_1095_, v___x_1096_);
lean_dec(v___x_1096_);
lean_dec(v___x_1095_);
v___x_1098_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq(v_mvarId_1062_, v_eqFVarId_1061_, v_subst_1063_, v_acyclic_1064_, v_a_1072_, v___x_1083_, v___x_1086_, v___x_1097_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
lean_dec(v_a_1072_);
return v___x_1098_;
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
lean_dec(v_a_1092_);
lean_dec_ref(v___x_1086_);
lean_dec_ref(v___x_1083_);
lean_dec(v_a_1072_);
lean_dec_ref(v_acyclic_1064_);
lean_dec(v_subst_1063_);
lean_dec(v_mvarId_1062_);
lean_dec(v_eqFVarId_1061_);
v_a_1099_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_1093_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1093_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
lean_dec(v_fvarId_1090_);
lean_dec_ref(v___x_1086_);
lean_dec_ref(v___x_1083_);
lean_dec(v_a_1072_);
lean_dec_ref(v_acyclic_1064_);
lean_dec(v_subst_1063_);
lean_dec(v_mvarId_1062_);
lean_dec(v_eqFVarId_1061_);
v_a_1107_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1091_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1091_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
else
{
lean_object* v___x_1115_; 
lean_dec(v_a_1088_);
lean_dec_ref_known(v_a_1085_, 1);
v___x_1115_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq(v_mvarId_1062_, v_eqFVarId_1061_, v_subst_1063_, v_acyclic_1064_, v_a_1072_, v___x_1083_, v___x_1086_, v___x_1074_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
lean_dec(v_a_1072_);
return v___x_1115_;
}
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1157_; 
v_a_1116_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1118_ = v___x_1087_;
v_isShared_1119_ = v_isSharedCheck_1157_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1087_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1157_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
if (lean_obj_tag(v_a_1116_) == 1)
{
lean_object* v___x_1120_; 
lean_dec_ref_known(v_a_1116_, 1);
lean_del_object(v___x_1118_);
lean_dec(v_a_1085_);
lean_dec(v_caseName_x3f_1065_);
v___x_1120_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq(v_mvarId_1062_, v_eqFVarId_1061_, v_subst_1063_, v_acyclic_1064_, v_a_1072_, v___x_1083_, v___x_1086_, v___x_1077_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
lean_dec(v_a_1072_);
return v___x_1120_;
}
else
{
lean_object* v___x_1121_; 
lean_dec_ref(v___x_1086_);
lean_dec_ref(v___x_1083_);
lean_dec_ref(v_acyclic_1064_);
lean_inc(v_a_1116_);
lean_inc(v_a_1085_);
v___x_1121_ = l_Lean_Meta_isExprDefEq(v_a_1085_, v_a_1116_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_a_1122_; uint8_t v___x_1123_; 
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_a_1122_);
lean_dec_ref_known(v___x_1121_, 1);
v___x_1123_ = lean_unbox(v_a_1122_);
lean_dec(v_a_1122_);
if (v___x_1123_ == 0)
{
lean_object* v___x_1124_; lean_object* v___f_1125_; lean_object* v___x_1126_; 
lean_del_object(v___x_1118_);
v___x_1124_ = lean_box(v___x_1077_);
lean_inc(v_a_1072_);
lean_inc(v_mvarId_1062_);
v___f_1125_ = lean_alloc_closure((void*)(l_Lean_Meta_unifyEq_x3f___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1125_, 0, v___x_1124_);
lean_closure_set(v___f_1125_, 1, v_mvarId_1062_);
lean_closure_set(v___f_1125_, 2, v_a_1072_);
v___x_1126_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection(v_mvarId_1062_, v_eqFVarId_1061_, v_subst_1063_, v_caseName_x3f_1065_, v_a_1072_, v___f_1125_, v_a_1085_, v_a_1116_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
lean_dec(v_a_1072_);
return v___x_1126_;
}
else
{
lean_object* v___x_1127_; 
lean_dec(v_a_1116_);
lean_dec(v_a_1085_);
lean_dec(v_a_1072_);
lean_dec(v_caseName_x3f_1065_);
v___x_1127_ = l_Lean_MVarId_clear(v_mvarId_1062_, v_eqFVarId_1061_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1140_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1130_ = v___x_1127_;
v_isShared_1131_ = v_isSharedCheck_1140_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1127_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1140_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1135_; 
v___x_1132_ = lean_unsigned_to_nat(0u);
v___x_1133_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1133_, 0, v_a_1128_);
lean_ctor_set(v___x_1133_, 1, v_subst_1063_);
lean_ctor_set(v___x_1133_, 2, v___x_1132_);
if (v_isShared_1119_ == 0)
{
lean_ctor_set_tag(v___x_1118_, 1);
lean_ctor_set(v___x_1118_, 0, v___x_1133_);
v___x_1135_ = v___x_1118_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1133_);
v___x_1135_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
lean_object* v___x_1137_; 
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 0, v___x_1135_);
v___x_1137_ = v___x_1130_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1135_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
else
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
lean_del_object(v___x_1118_);
lean_dec(v_subst_1063_);
v_a_1141_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1127_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1127_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1141_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
}
else
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1156_; 
lean_del_object(v___x_1118_);
lean_dec(v_a_1116_);
lean_dec(v_a_1085_);
lean_dec(v_a_1072_);
lean_dec(v_caseName_x3f_1065_);
lean_dec(v_subst_1063_);
lean_dec(v_mvarId_1062_);
lean_dec(v_eqFVarId_1061_);
v_a_1149_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1151_ = v___x_1121_;
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1121_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1152_ == 0)
{
v___x_1154_ = v___x_1151_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1149_);
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
}
}
}
}
else
{
lean_object* v___x_1158_; 
lean_dec_ref(v___x_1073_);
lean_dec(v_caseName_x3f_1065_);
lean_dec_ref(v_acyclic_1064_);
lean_dec(v_eqFVarId_1061_);
v___x_1158_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_heqToEq_x27(v_mvarId_1062_, v_a_1072_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
lean_dec(v_a_1072_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1169_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1161_ = v___x_1158_;
v_isShared_1162_ = v_isSharedCheck_1169_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1158_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1169_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1167_; 
v___x_1163_ = lean_unsigned_to_nat(1u);
v___x_1164_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1164_, 0, v_a_1159_);
lean_ctor_set(v___x_1164_, 1, v_subst_1063_);
lean_ctor_set(v___x_1164_, 2, v___x_1163_);
v___x_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 0, v___x_1165_);
v___x_1167_ = v___x_1161_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1165_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
else
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1177_; 
lean_dec(v_subst_1063_);
v_a_1170_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1172_ = v___x_1158_;
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1158_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_a_1170_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
}
else
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
lean_dec(v_caseName_x3f_1065_);
lean_dec_ref(v_acyclic_1064_);
lean_dec(v_subst_1063_);
lean_dec(v_mvarId_1062_);
lean_dec(v_eqFVarId_1061_);
v_a_1178_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1071_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1071_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__1___boxed(lean_object* v_eqFVarId_1186_, lean_object* v_mvarId_1187_, lean_object* v_subst_1188_, lean_object* v_acyclic_1189_, lean_object* v_caseName_x3f_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Lean_Meta_unifyEq_x3f___lam__1(v_eqFVarId_1186_, v_mvarId_1187_, v_subst_1188_, v_acyclic_1189_, v_caseName_x3f_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f(lean_object* v_mvarId_1197_, lean_object* v_eqFVarId_1198_, lean_object* v_subst_1199_, lean_object* v_acyclic_1200_, lean_object* v_caseName_x3f_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v___f_1207_; lean_object* v___x_1208_; 
lean_inc(v_mvarId_1197_);
v___f_1207_ = lean_alloc_closure((void*)(l_Lean_Meta_unifyEq_x3f___lam__1___boxed), 10, 5);
lean_closure_set(v___f_1207_, 0, v_eqFVarId_1198_);
lean_closure_set(v___f_1207_, 1, v_mvarId_1197_);
lean_closure_set(v___f_1207_, 2, v_subst_1199_);
lean_closure_set(v___f_1207_, 3, v_acyclic_1200_);
lean_closure_set(v___f_1207_, 4, v_caseName_x3f_1201_);
v___x_1208_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___redArg(v_mvarId_1197_, v___f_1207_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___boxed(lean_object* v_mvarId_1209_, lean_object* v_eqFVarId_1210_, lean_object* v_subst_1211_, lean_object* v_acyclic_1212_, lean_object* v_caseName_x3f_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_Lean_Meta_unifyEq_x3f(v_mvarId_1209_, v_eqFVarId_1210_, v_subst_1211_, v_acyclic_1212_, v_caseName_x3f_1213_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_);
lean_dec(v_a_1217_);
lean_dec_ref(v_a_1216_);
lean_dec(v_a_1215_);
lean_dec_ref(v_a_1214_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1(lean_object* v_mvarId_1220_, lean_object* v_val_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1___redArg(v_mvarId_1220_, v_val_1221_, v___y_1223_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1___boxed(lean_object* v_mvarId_1228_, lean_object* v_val_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1(v_mvarId_1228_, v_val_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1(lean_object* v_00_u03b2_1236_, lean_object* v_x_1237_, lean_object* v_x_1238_, lean_object* v_x_1239_){
_start:
{
lean_object* v___x_1240_; 
v___x_1240_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1___redArg(v_x_1237_, v_x_1238_, v_x_1239_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_1241_, lean_object* v_x_1242_, size_t v_x_1243_, size_t v_x_1244_, lean_object* v_x_1245_, lean_object* v_x_1246_){
_start:
{
lean_object* v___x_1247_; 
v___x_1247_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg(v_x_1242_, v_x_1243_, v_x_1244_, v_x_1245_, v_x_1246_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1248_, lean_object* v_x_1249_, lean_object* v_x_1250_, lean_object* v_x_1251_, lean_object* v_x_1252_, lean_object* v_x_1253_){
_start:
{
size_t v_x_10274__boxed_1254_; size_t v_x_10275__boxed_1255_; lean_object* v_res_1256_; 
v_x_10274__boxed_1254_ = lean_unbox_usize(v_x_1250_);
lean_dec(v_x_1250_);
v_x_10275__boxed_1255_ = lean_unbox_usize(v_x_1251_);
lean_dec(v_x_1251_);
v_res_1256_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3(v_00_u03b2_1248_, v_x_1249_, v_x_10274__boxed_1254_, v_x_10275__boxed_1255_, v_x_1252_, v_x_1253_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1257_, lean_object* v_n_1258_, lean_object* v_k_1259_, lean_object* v_v_1260_){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__4___redArg(v_n_1258_, v_k_1259_, v_v_1260_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_1262_, size_t v_depth_1263_, lean_object* v_keys_1264_, lean_object* v_vals_1265_, lean_object* v_heq_1266_, lean_object* v_i_1267_, lean_object* v_entries_1268_){
_start:
{
lean_object* v___x_1269_; 
v___x_1269_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_depth_1263_, v_keys_1264_, v_vals_1265_, v_i_1267_, v_entries_1268_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b2_1270_, lean_object* v_depth_1271_, lean_object* v_keys_1272_, lean_object* v_vals_1273_, lean_object* v_heq_1274_, lean_object* v_i_1275_, lean_object* v_entries_1276_){
_start:
{
size_t v_depth_boxed_1277_; lean_object* v_res_1278_; 
v_depth_boxed_1277_ = lean_unbox_usize(v_depth_1271_);
lean_dec(v_depth_1271_);
v_res_1278_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__5(v_00_u03b2_1270_, v_depth_boxed_1277_, v_keys_1272_, v_vals_1273_, v_heq_1274_, v_i_1275_, v_entries_1276_);
lean_dec_ref(v_vals_1273_);
lean_dec_ref(v_keys_1272_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_1279_, lean_object* v_x_1280_, lean_object* v_x_1281_, lean_object* v_x_1282_, lean_object* v_x_1283_){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(v_x_1280_, v_x_1281_, v_x_1282_, v_x_1283_);
return v___x_1284_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Injection(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_UnifyEq(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
