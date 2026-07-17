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
lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_423_; lean_object* v___x_499_; 
lean_inc(v_a_375_);
lean_inc_ref(v_a_374_);
lean_inc(v_a_373_);
lean_inc_ref(v_a_372_);
lean_inc_ref(v_b_371_);
lean_inc_ref(v_a_370_);
v___x_499_ = lean_apply_7(v_injectionOffset_x3f_369_, v_a_370_, v_b_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, lean_box(0));
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_521_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_521_ == 0)
{
v___x_502_ = v___x_499_;
v_isShared_503_ = v_isSharedCheck_521_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_499_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_521_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
if (lean_obj_tag(v_a_500_) == 1)
{
lean_object* v_val_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_516_; 
lean_dec_ref(v_b_371_);
lean_dec_ref(v_a_370_);
lean_dec(v_caseName_x3f_367_);
lean_dec(v_eqFVarId_365_);
lean_dec(v_mvarId_364_);
v_val_504_ = lean_ctor_get(v_a_500_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v_a_500_);
if (v_isSharedCheck_516_ == 0)
{
v___x_506_ = v_a_500_;
v_isShared_507_ = v_isSharedCheck_516_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_val_504_);
lean_dec(v_a_500_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_516_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_511_; 
v___x_508_ = lean_unsigned_to_nat(1u);
v___x_509_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_509_, 0, v_val_504_);
lean_ctor_set(v___x_509_, 1, v_subst_366_);
lean_ctor_set(v___x_509_, 2, v___x_508_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v___x_509_);
v___x_511_ = v___x_506_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_509_);
v___x_511_ = v_reuseFailAlloc_515_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
lean_object* v___x_513_; 
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_511_);
v___x_513_ = v___x_502_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_511_);
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
else
{
lean_object* v___x_517_; 
lean_del_object(v___x_502_);
lean_dec(v_a_500_);
lean_inc_ref(v_a_370_);
v___x_517_ = l_Lean_Meta_isConstructorApp(v_a_370_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_518_; uint8_t v___x_519_; 
v_a_518_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_a_518_);
v___x_519_ = lean_unbox(v_a_518_);
lean_dec(v_a_518_);
if (v___x_519_ == 0)
{
v___y_423_ = v___x_517_;
goto v___jp_422_;
}
else
{
lean_object* v___x_520_; 
lean_dec_ref_known(v___x_517_, 1);
lean_inc_ref(v_b_371_);
v___x_520_ = l_Lean_Meta_isConstructorApp(v_b_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
v___y_423_ = v___x_520_;
goto v___jp_422_;
}
}
else
{
v___y_423_ = v___x_517_;
goto v___jp_422_;
}
}
}
}
else
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
lean_dec_ref(v_b_371_);
lean_dec_ref(v_a_370_);
lean_dec(v_caseName_x3f_367_);
lean_dec(v_subst_366_);
lean_dec(v_eqFVarId_365_);
lean_dec(v_mvarId_364_);
v_a_522_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_529_ == 0)
{
v___x_524_ = v___x_499_;
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_499_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_a_522_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
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
lean_object* v_a_429_; uint8_t v___x_430_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_a_429_);
lean_dec_ref_known(v___x_428_, 1);
v___x_430_ = lean_expr_eqv(v_a_427_, v_a_370_);
lean_dec_ref(v_a_370_);
if (v___x_430_ == 0)
{
lean_dec(v_a_424_);
lean_dec_ref(v_b_371_);
lean_dec(v_caseName_x3f_367_);
v___y_378_ = v_a_427_;
v___y_379_ = v_a_429_;
goto v___jp_377_;
}
else
{
uint8_t v___x_431_; 
v___x_431_ = lean_expr_eqv(v_a_429_, v_b_371_);
lean_dec_ref(v_b_371_);
if (v___x_431_ == 0)
{
lean_dec(v_a_424_);
lean_dec(v_caseName_x3f_367_);
v___y_378_ = v_a_427_;
v___y_379_ = v_a_429_;
goto v___jp_377_;
}
else
{
lean_dec(v_a_429_);
lean_dec(v_a_427_);
lean_dec(v_subst_366_);
lean_dec(v_eqFVarId_365_);
lean_dec(v_mvarId_364_);
if (lean_obj_tag(v_caseName_x3f_367_) == 0)
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
lean_dec(v_a_424_);
v___x_432_ = lean_obj_once(&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1, &l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1_once, _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1);
v___x_433_ = l_Lean_LocalDecl_type(v_eqDecl_368_);
v___x_434_ = l_Lean_indentExpr(v___x_433_);
v___x_435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_435_, 0, v___x_432_);
lean_ctor_set(v___x_435_, 1, v___x_434_);
v___x_436_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(v___x_435_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
return v___x_436_;
}
else
{
lean_object* v_val_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; uint8_t v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v_val_437_ = lean_ctor_get(v_caseName_x3f_367_, 0);
lean_inc(v_val_437_);
lean_dec_ref_known(v_caseName_x3f_367_, 1);
v___x_438_ = lean_obj_once(&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1, &l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1_once, _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1);
v___x_439_ = l_Lean_LocalDecl_type(v_eqDecl_368_);
v___x_440_ = l_Lean_indentExpr(v___x_439_);
v___x_441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_438_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
v___x_442_ = lean_obj_once(&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__1, &l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__1_once, _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__1);
v___x_443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_443_, 0, v___x_441_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
v___x_444_ = lean_unbox(v_a_424_);
lean_dec(v_a_424_);
v___x_445_ = l_Lean_MessageData_ofConstName(v_val_437_, v___x_444_);
v___x_446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_446_, 0, v___x_443_);
lean_ctor_set(v___x_446_, 1, v___x_445_);
v___x_447_ = lean_obj_once(&l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__3, &l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__3_once, _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__3);
v___x_448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_446_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
v___x_449_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(v___x_448_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
return v___x_449_;
}
}
}
}
else
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_457_; 
lean_dec(v_a_427_);
lean_dec(v_a_424_);
lean_dec_ref(v_b_371_);
lean_dec_ref(v_a_370_);
lean_dec(v_caseName_x3f_367_);
lean_dec(v_subst_366_);
lean_dec(v_eqFVarId_365_);
lean_dec(v_mvarId_364_);
v_a_450_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_457_ == 0)
{
v___x_452_ = v___x_428_;
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_428_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_455_; 
if (v_isShared_453_ == 0)
{
v___x_455_ = v___x_452_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_450_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
else
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_465_; 
lean_dec(v_a_424_);
lean_dec_ref(v_b_371_);
lean_dec_ref(v_a_370_);
lean_dec(v_caseName_x3f_367_);
lean_dec(v_subst_366_);
lean_dec(v_eqFVarId_365_);
lean_dec(v_mvarId_364_);
v_a_458_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_465_ == 0)
{
v___x_460_ = v___x_426_;
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_426_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_463_; 
if (v_isShared_461_ == 0)
{
v___x_463_ = v___x_460_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_a_458_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
else
{
lean_object* v___x_466_; 
lean_dec(v_a_424_);
lean_dec_ref(v_b_371_);
lean_dec_ref(v_a_370_);
lean_dec(v_caseName_x3f_367_);
v___x_466_ = l_Lean_Meta_injectionCore(v_mvarId_364_, v_eqFVarId_365_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_482_; 
v_a_467_ = lean_ctor_get(v___x_466_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_482_ == 0)
{
v___x_469_ = v___x_466_;
v_isShared_470_ = v_isSharedCheck_482_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_466_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_482_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
if (lean_obj_tag(v_a_467_) == 0)
{
lean_object* v___x_471_; lean_object* v___x_473_; 
lean_dec(v_subst_366_);
v___x_471_ = lean_box(0);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 0, v___x_471_);
v___x_473_ = v___x_469_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v___x_471_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
else
{
lean_object* v_mvarId_475_; lean_object* v_numNewEqs_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_480_; 
v_mvarId_475_ = lean_ctor_get(v_a_467_, 0);
lean_inc(v_mvarId_475_);
v_numNewEqs_476_ = lean_ctor_get(v_a_467_, 1);
lean_inc(v_numNewEqs_476_);
lean_dec_ref_known(v_a_467_, 2);
v___x_477_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_477_, 0, v_mvarId_475_);
lean_ctor_set(v___x_477_, 1, v_subst_366_);
lean_ctor_set(v___x_477_, 2, v_numNewEqs_476_);
v___x_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 0, v___x_478_);
v___x_480_ = v___x_469_;
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
}
else
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_490_; 
lean_dec(v_subst_366_);
v_a_483_ = lean_ctor_get(v___x_466_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_490_ == 0)
{
v___x_485_ = v___x_466_;
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_466_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_488_; 
if (v_isShared_486_ == 0)
{
v___x_488_ = v___x_485_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_a_483_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
}
else
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
lean_dec_ref(v_b_371_);
lean_dec_ref(v_a_370_);
lean_dec(v_caseName_x3f_367_);
lean_dec(v_subst_366_);
lean_dec(v_eqFVarId_365_);
lean_dec(v_mvarId_364_);
v_a_491_ = lean_ctor_get(v___y_423_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___y_423_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___y_423_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___y_423_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___boxed(lean_object* v_mvarId_530_, lean_object* v_eqFVarId_531_, lean_object* v_subst_532_, lean_object* v_caseName_x3f_533_, lean_object* v_eqDecl_534_, lean_object* v_injectionOffset_x3f_535_, lean_object* v_a_536_, lean_object* v_b_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection(v_mvarId_530_, v_eqFVarId_531_, v_subst_532_, v_caseName_x3f_533_, v_eqDecl_534_, v_injectionOffset_x3f_535_, v_a_536_, v_b_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_);
lean_dec(v_a_541_);
lean_dec_ref(v_a_540_);
lean_dec(v_a_539_);
lean_dec_ref(v_a_538_);
lean_dec_ref(v_eqDecl_534_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__0___redArg(lean_object* v_e_544_, lean_object* v___y_545_){
_start:
{
uint8_t v___x_547_; 
v___x_547_ = l_Lean_Expr_hasMVar(v_e_544_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; 
v___x_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_548_, 0, v_e_544_);
return v___x_548_;
}
else
{
lean_object* v___x_549_; lean_object* v_mctx_550_; lean_object* v___x_551_; lean_object* v_fst_552_; lean_object* v_snd_553_; lean_object* v___x_554_; lean_object* v_cache_555_; lean_object* v_zetaDeltaFVarIds_556_; lean_object* v_postponed_557_; lean_object* v_diag_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_567_; 
v___x_549_ = lean_st_ref_get(v___y_545_);
v_mctx_550_ = lean_ctor_get(v___x_549_, 0);
lean_inc_ref(v_mctx_550_);
lean_dec(v___x_549_);
v___x_551_ = l_Lean_instantiateMVarsCore(v_mctx_550_, v_e_544_);
v_fst_552_ = lean_ctor_get(v___x_551_, 0);
lean_inc(v_fst_552_);
v_snd_553_ = lean_ctor_get(v___x_551_, 1);
lean_inc(v_snd_553_);
lean_dec_ref(v___x_551_);
v___x_554_ = lean_st_ref_take(v___y_545_);
v_cache_555_ = lean_ctor_get(v___x_554_, 1);
v_zetaDeltaFVarIds_556_ = lean_ctor_get(v___x_554_, 2);
v_postponed_557_ = lean_ctor_get(v___x_554_, 3);
v_diag_558_ = lean_ctor_get(v___x_554_, 4);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_567_ == 0)
{
lean_object* v_unused_568_; 
v_unused_568_ = lean_ctor_get(v___x_554_, 0);
lean_dec(v_unused_568_);
v___x_560_ = v___x_554_;
v_isShared_561_ = v_isSharedCheck_567_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_diag_558_);
lean_inc(v_postponed_557_);
lean_inc(v_zetaDeltaFVarIds_556_);
lean_inc(v_cache_555_);
lean_dec(v___x_554_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_567_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_563_; 
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 0, v_snd_553_);
v___x_563_ = v___x_560_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_snd_553_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_cache_555_);
lean_ctor_set(v_reuseFailAlloc_566_, 2, v_zetaDeltaFVarIds_556_);
lean_ctor_set(v_reuseFailAlloc_566_, 3, v_postponed_557_);
lean_ctor_set(v_reuseFailAlloc_566_, 4, v_diag_558_);
v___x_563_ = v_reuseFailAlloc_566_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = lean_st_ref_set(v___y_545_, v___x_563_);
v___x_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_565_, 0, v_fst_552_);
return v___x_565_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__0___redArg___boxed(lean_object* v_e_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__0___redArg(v_e_569_, v___y_570_);
lean_dec(v___y_570_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__0(lean_object* v_e_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__0___redArg(v_e_573_, v___y_575_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__0___boxed(lean_object* v_e_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__0(v_e_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___redArg(lean_object* v_mvarId_587_, lean_object* v_x_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_587_, v_x_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
v_a_595_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v___x_594_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_594_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_595_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
else
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
v_a_603_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v___x_594_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_594_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_603_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___redArg___boxed(lean_object* v_mvarId_611_, lean_object* v_x_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___redArg(v_mvarId_611_, v_x_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2(lean_object* v_00_u03b1_619_, lean_object* v_mvarId_620_, lean_object* v_x_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___redArg(v_mvarId_620_, v_x_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___boxed(lean_object* v_00_u03b1_628_, lean_object* v_mvarId_629_, lean_object* v_x_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2(v_00_u03b1_628_, v_mvarId_629_, v_x_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_637_, lean_object* v_x_638_, lean_object* v_x_639_, lean_object* v_x_640_){
_start:
{
lean_object* v_ks_641_; lean_object* v_vs_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_666_; 
v_ks_641_ = lean_ctor_get(v_x_637_, 0);
v_vs_642_ = lean_ctor_get(v_x_637_, 1);
v_isSharedCheck_666_ = !lean_is_exclusive(v_x_637_);
if (v_isSharedCheck_666_ == 0)
{
v___x_644_ = v_x_637_;
v_isShared_645_ = v_isSharedCheck_666_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_vs_642_);
lean_inc(v_ks_641_);
lean_dec(v_x_637_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_666_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_646_; uint8_t v___x_647_; 
v___x_646_ = lean_array_get_size(v_ks_641_);
v___x_647_ = lean_nat_dec_lt(v_x_638_, v___x_646_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_651_; 
lean_dec(v_x_638_);
v___x_648_ = lean_array_push(v_ks_641_, v_x_639_);
v___x_649_ = lean_array_push(v_vs_642_, v_x_640_);
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 1, v___x_649_);
lean_ctor_set(v___x_644_, 0, v___x_648_);
v___x_651_ = v___x_644_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_648_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v___x_649_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
else
{
lean_object* v_k_x27_653_; uint8_t v___x_654_; 
v_k_x27_653_ = lean_array_fget_borrowed(v_ks_641_, v_x_638_);
v___x_654_ = l_Lean_instBEqMVarId_beq(v_x_639_, v_k_x27_653_);
if (v___x_654_ == 0)
{
lean_object* v___x_656_; 
if (v_isShared_645_ == 0)
{
v___x_656_ = v___x_644_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_ks_641_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v_vs_642_);
v___x_656_ = v_reuseFailAlloc_660_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = lean_unsigned_to_nat(1u);
v___x_658_ = lean_nat_add(v_x_638_, v___x_657_);
lean_dec(v_x_638_);
v_x_637_ = v___x_656_;
v_x_638_ = v___x_658_;
goto _start;
}
}
else
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_664_; 
v___x_661_ = lean_array_fset(v_ks_641_, v_x_638_, v_x_639_);
v___x_662_ = lean_array_fset(v_vs_642_, v_x_638_, v_x_640_);
lean_dec(v_x_638_);
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 1, v___x_662_);
lean_ctor_set(v___x_644_, 0, v___x_661_);
v___x_664_ = v___x_644_;
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__4___redArg(lean_object* v_n_667_, lean_object* v_k_668_, lean_object* v_v_669_){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = lean_unsigned_to_nat(0u);
v___x_671_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(v_n_667_, v___x_670_, v_k_668_, v_v_669_);
return v___x_671_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg(lean_object* v_x_673_, size_t v_x_674_, size_t v_x_675_, lean_object* v_x_676_, lean_object* v_x_677_){
_start:
{
if (lean_obj_tag(v_x_673_) == 0)
{
lean_object* v_es_678_; size_t v___x_679_; size_t v___x_680_; lean_object* v_j_681_; lean_object* v___x_682_; uint8_t v___x_683_; 
v_es_678_ = lean_ctor_get(v_x_673_, 0);
v___x_679_ = ((size_t)31ULL);
v___x_680_ = lean_usize_land(v_x_674_, v___x_679_);
v_j_681_ = lean_usize_to_nat(v___x_680_);
v___x_682_ = lean_array_get_size(v_es_678_);
v___x_683_ = lean_nat_dec_lt(v_j_681_, v___x_682_);
if (v___x_683_ == 0)
{
lean_dec(v_j_681_);
lean_dec(v_x_677_);
lean_dec(v_x_676_);
return v_x_673_;
}
else
{
lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_722_; 
lean_inc_ref(v_es_678_);
v_isSharedCheck_722_ = !lean_is_exclusive(v_x_673_);
if (v_isSharedCheck_722_ == 0)
{
lean_object* v_unused_723_; 
v_unused_723_ = lean_ctor_get(v_x_673_, 0);
lean_dec(v_unused_723_);
v___x_685_ = v_x_673_;
v_isShared_686_ = v_isSharedCheck_722_;
goto v_resetjp_684_;
}
else
{
lean_dec(v_x_673_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_722_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v_v_687_; lean_object* v___x_688_; lean_object* v_xs_x27_689_; lean_object* v___y_691_; 
v_v_687_ = lean_array_fget(v_es_678_, v_j_681_);
v___x_688_ = lean_box(0);
v_xs_x27_689_ = lean_array_fset(v_es_678_, v_j_681_, v___x_688_);
switch(lean_obj_tag(v_v_687_))
{
case 0:
{
lean_object* v_key_696_; lean_object* v_val_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_707_; 
v_key_696_ = lean_ctor_get(v_v_687_, 0);
v_val_697_ = lean_ctor_get(v_v_687_, 1);
v_isSharedCheck_707_ = !lean_is_exclusive(v_v_687_);
if (v_isSharedCheck_707_ == 0)
{
v___x_699_ = v_v_687_;
v_isShared_700_ = v_isSharedCheck_707_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_val_697_);
lean_inc(v_key_696_);
lean_dec(v_v_687_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_707_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
uint8_t v___x_701_; 
v___x_701_ = l_Lean_instBEqMVarId_beq(v_x_676_, v_key_696_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; lean_object* v___x_703_; 
lean_del_object(v___x_699_);
v___x_702_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_696_, v_val_697_, v_x_676_, v_x_677_);
v___x_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
v___y_691_ = v___x_703_;
goto v___jp_690_;
}
else
{
lean_object* v___x_705_; 
lean_dec(v_val_697_);
lean_dec(v_key_696_);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 1, v_x_677_);
lean_ctor_set(v___x_699_, 0, v_x_676_);
v___x_705_ = v___x_699_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_x_676_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v_x_677_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
v___y_691_ = v___x_705_;
goto v___jp_690_;
}
}
}
}
case 1:
{
lean_object* v_node_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_720_; 
v_node_708_ = lean_ctor_get(v_v_687_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v_v_687_);
if (v_isSharedCheck_720_ == 0)
{
v___x_710_ = v_v_687_;
v_isShared_711_ = v_isSharedCheck_720_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_node_708_);
lean_dec(v_v_687_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_720_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
size_t v___x_712_; size_t v___x_713_; size_t v___x_714_; size_t v___x_715_; lean_object* v___x_716_; lean_object* v___x_718_; 
v___x_712_ = ((size_t)5ULL);
v___x_713_ = lean_usize_shift_right(v_x_674_, v___x_712_);
v___x_714_ = ((size_t)1ULL);
v___x_715_ = lean_usize_add(v_x_675_, v___x_714_);
v___x_716_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg(v_node_708_, v___x_713_, v___x_715_, v_x_676_, v_x_677_);
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 0, v___x_716_);
v___x_718_ = v___x_710_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_716_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
v___y_691_ = v___x_718_;
goto v___jp_690_;
}
}
}
default: 
{
lean_object* v___x_721_; 
v___x_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_721_, 0, v_x_676_);
lean_ctor_set(v___x_721_, 1, v_x_677_);
v___y_691_ = v___x_721_;
goto v___jp_690_;
}
}
v___jp_690_:
{
lean_object* v___x_692_; lean_object* v___x_694_; 
v___x_692_ = lean_array_fset(v_xs_x27_689_, v_j_681_, v___y_691_);
lean_dec(v_j_681_);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 0, v___x_692_);
v___x_694_ = v___x_685_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_692_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
}
else
{
lean_object* v_ks_724_; lean_object* v_vs_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_745_; 
v_ks_724_ = lean_ctor_get(v_x_673_, 0);
v_vs_725_ = lean_ctor_get(v_x_673_, 1);
v_isSharedCheck_745_ = !lean_is_exclusive(v_x_673_);
if (v_isSharedCheck_745_ == 0)
{
v___x_727_ = v_x_673_;
v_isShared_728_ = v_isSharedCheck_745_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_vs_725_);
lean_inc(v_ks_724_);
lean_dec(v_x_673_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_745_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_ks_724_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v_vs_725_);
v___x_730_ = v_reuseFailAlloc_744_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
lean_object* v_newNode_731_; uint8_t v___y_733_; size_t v___x_739_; uint8_t v___x_740_; 
v_newNode_731_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__4___redArg(v___x_730_, v_x_676_, v_x_677_);
v___x_739_ = ((size_t)7ULL);
v___x_740_ = lean_usize_dec_le(v___x_739_, v_x_675_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; lean_object* v___x_742_; uint8_t v___x_743_; 
v___x_741_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_731_);
v___x_742_ = lean_unsigned_to_nat(4u);
v___x_743_ = lean_nat_dec_lt(v___x_741_, v___x_742_);
lean_dec(v___x_741_);
v___y_733_ = v___x_743_;
goto v___jp_732_;
}
else
{
v___y_733_ = v___x_740_;
goto v___jp_732_;
}
v___jp_732_:
{
if (v___y_733_ == 0)
{
lean_object* v_ks_734_; lean_object* v_vs_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v_ks_734_ = lean_ctor_get(v_newNode_731_, 0);
lean_inc_ref(v_ks_734_);
v_vs_735_ = lean_ctor_get(v_newNode_731_, 1);
lean_inc_ref(v_vs_735_);
lean_dec_ref(v_newNode_731_);
v___x_736_ = lean_unsigned_to_nat(0u);
v___x_737_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_738_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_x_675_, v_ks_734_, v_vs_735_, v___x_736_, v___x_737_);
lean_dec_ref(v_vs_735_);
lean_dec_ref(v_ks_734_);
return v___x_738_;
}
else
{
return v_newNode_731_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__5___redArg(size_t v_depth_746_, lean_object* v_keys_747_, lean_object* v_vals_748_, lean_object* v_i_749_, lean_object* v_entries_750_){
_start:
{
lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_751_ = lean_array_get_size(v_keys_747_);
v___x_752_ = lean_nat_dec_lt(v_i_749_, v___x_751_);
if (v___x_752_ == 0)
{
lean_dec(v_i_749_);
return v_entries_750_;
}
else
{
lean_object* v_k_753_; lean_object* v_v_754_; uint64_t v___x_755_; size_t v_h_756_; size_t v___x_757_; lean_object* v___x_758_; size_t v___x_759_; size_t v___x_760_; size_t v___x_761_; size_t v_h_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v_k_753_ = lean_array_fget_borrowed(v_keys_747_, v_i_749_);
v_v_754_ = lean_array_fget_borrowed(v_vals_748_, v_i_749_);
v___x_755_ = l_Lean_instHashableMVarId_hash(v_k_753_);
v_h_756_ = lean_uint64_to_usize(v___x_755_);
v___x_757_ = ((size_t)5ULL);
v___x_758_ = lean_unsigned_to_nat(1u);
v___x_759_ = ((size_t)1ULL);
v___x_760_ = lean_usize_sub(v_depth_746_, v___x_759_);
v___x_761_ = lean_usize_mul(v___x_757_, v___x_760_);
v_h_762_ = lean_usize_shift_right(v_h_756_, v___x_761_);
v___x_763_ = lean_nat_add(v_i_749_, v___x_758_);
lean_dec(v_i_749_);
lean_inc(v_v_754_);
lean_inc(v_k_753_);
v___x_764_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg(v_entries_750_, v_h_762_, v_depth_746_, v_k_753_, v_v_754_);
v_i_749_ = v___x_763_;
v_entries_750_ = v___x_764_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_depth_766_, lean_object* v_keys_767_, lean_object* v_vals_768_, lean_object* v_i_769_, lean_object* v_entries_770_){
_start:
{
size_t v_depth_boxed_771_; lean_object* v_res_772_; 
v_depth_boxed_771_ = lean_unbox_usize(v_depth_766_);
lean_dec(v_depth_766_);
v_res_772_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_depth_boxed_771_, v_keys_767_, v_vals_768_, v_i_769_, v_entries_770_);
lean_dec_ref(v_vals_768_);
lean_dec_ref(v_keys_767_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_773_, lean_object* v_x_774_, lean_object* v_x_775_, lean_object* v_x_776_, lean_object* v_x_777_){
_start:
{
size_t v_x_9332__boxed_778_; size_t v_x_9333__boxed_779_; lean_object* v_res_780_; 
v_x_9332__boxed_778_ = lean_unbox_usize(v_x_774_);
lean_dec(v_x_774_);
v_x_9333__boxed_779_ = lean_unbox_usize(v_x_775_);
lean_dec(v_x_775_);
v_res_780_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg(v_x_773_, v_x_9332__boxed_778_, v_x_9333__boxed_779_, v_x_776_, v_x_777_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1___redArg(lean_object* v_x_781_, lean_object* v_x_782_, lean_object* v_x_783_){
_start:
{
uint64_t v___x_784_; size_t v___x_785_; size_t v___x_786_; lean_object* v___x_787_; 
v___x_784_ = l_Lean_instHashableMVarId_hash(v_x_782_);
v___x_785_ = lean_uint64_to_usize(v___x_784_);
v___x_786_ = ((size_t)1ULL);
v___x_787_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg(v_x_781_, v___x_785_, v___x_786_, v_x_782_, v_x_783_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1___redArg(lean_object* v_mvarId_788_, lean_object* v_val_789_, lean_object* v___y_790_){
_start:
{
lean_object* v___x_792_; lean_object* v_mctx_793_; lean_object* v_cache_794_; lean_object* v_zetaDeltaFVarIds_795_; lean_object* v_postponed_796_; lean_object* v_diag_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_825_; 
v___x_792_ = lean_st_ref_take(v___y_790_);
v_mctx_793_ = lean_ctor_get(v___x_792_, 0);
v_cache_794_ = lean_ctor_get(v___x_792_, 1);
v_zetaDeltaFVarIds_795_ = lean_ctor_get(v___x_792_, 2);
v_postponed_796_ = lean_ctor_get(v___x_792_, 3);
v_diag_797_ = lean_ctor_get(v___x_792_, 4);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_825_ == 0)
{
v___x_799_ = v___x_792_;
v_isShared_800_ = v_isSharedCheck_825_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_diag_797_);
lean_inc(v_postponed_796_);
lean_inc(v_zetaDeltaFVarIds_795_);
lean_inc(v_cache_794_);
lean_inc(v_mctx_793_);
lean_dec(v___x_792_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_825_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v_depth_801_; lean_object* v_levelAssignDepth_802_; lean_object* v_lmvarCounter_803_; lean_object* v_mvarCounter_804_; lean_object* v_lDecls_805_; lean_object* v_decls_806_; lean_object* v_userNames_807_; lean_object* v_lAssignment_808_; lean_object* v_eAssignment_809_; lean_object* v_dAssignment_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_824_; 
v_depth_801_ = lean_ctor_get(v_mctx_793_, 0);
v_levelAssignDepth_802_ = lean_ctor_get(v_mctx_793_, 1);
v_lmvarCounter_803_ = lean_ctor_get(v_mctx_793_, 2);
v_mvarCounter_804_ = lean_ctor_get(v_mctx_793_, 3);
v_lDecls_805_ = lean_ctor_get(v_mctx_793_, 4);
v_decls_806_ = lean_ctor_get(v_mctx_793_, 5);
v_userNames_807_ = lean_ctor_get(v_mctx_793_, 6);
v_lAssignment_808_ = lean_ctor_get(v_mctx_793_, 7);
v_eAssignment_809_ = lean_ctor_get(v_mctx_793_, 8);
v_dAssignment_810_ = lean_ctor_get(v_mctx_793_, 9);
v_isSharedCheck_824_ = !lean_is_exclusive(v_mctx_793_);
if (v_isSharedCheck_824_ == 0)
{
v___x_812_ = v_mctx_793_;
v_isShared_813_ = v_isSharedCheck_824_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_dAssignment_810_);
lean_inc(v_eAssignment_809_);
lean_inc(v_lAssignment_808_);
lean_inc(v_userNames_807_);
lean_inc(v_decls_806_);
lean_inc(v_lDecls_805_);
lean_inc(v_mvarCounter_804_);
lean_inc(v_lmvarCounter_803_);
lean_inc(v_levelAssignDepth_802_);
lean_inc(v_depth_801_);
lean_dec(v_mctx_793_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_824_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_814_; lean_object* v___x_816_; 
v___x_814_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1___redArg(v_eAssignment_809_, v_mvarId_788_, v_val_789_);
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 8, v___x_814_);
v___x_816_ = v___x_812_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_depth_801_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v_levelAssignDepth_802_);
lean_ctor_set(v_reuseFailAlloc_823_, 2, v_lmvarCounter_803_);
lean_ctor_set(v_reuseFailAlloc_823_, 3, v_mvarCounter_804_);
lean_ctor_set(v_reuseFailAlloc_823_, 4, v_lDecls_805_);
lean_ctor_set(v_reuseFailAlloc_823_, 5, v_decls_806_);
lean_ctor_set(v_reuseFailAlloc_823_, 6, v_userNames_807_);
lean_ctor_set(v_reuseFailAlloc_823_, 7, v_lAssignment_808_);
lean_ctor_set(v_reuseFailAlloc_823_, 8, v___x_814_);
lean_ctor_set(v_reuseFailAlloc_823_, 9, v_dAssignment_810_);
v___x_816_ = v_reuseFailAlloc_823_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_object* v___x_818_; 
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v___x_816_);
v___x_818_ = v___x_799_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_816_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v_cache_794_);
lean_ctor_set(v_reuseFailAlloc_822_, 2, v_zetaDeltaFVarIds_795_);
lean_ctor_set(v_reuseFailAlloc_822_, 3, v_postponed_796_);
lean_ctor_set(v_reuseFailAlloc_822_, 4, v_diag_797_);
v___x_818_ = v_reuseFailAlloc_822_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_819_ = lean_st_ref_set(v___y_790_, v___x_818_);
v___x_820_ = lean_box(0);
v___x_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
return v___x_821_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1___redArg___boxed(lean_object* v_mvarId_826_, lean_object* v_val_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1___redArg(v_mvarId_826_, v_val_827_, v___y_828_);
lean_dec(v___y_828_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__0(uint8_t v___x_838_, lean_object* v_mvarId_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_b_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v___x_848_; lean_object* v_env_849_; lean_object* v___x_850_; lean_object* v_fst_852_; lean_object* v_fst_853_; lean_object* v_snd_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; uint8_t v___x_961_; 
v___x_848_ = lean_st_ref_get(v___y_846_);
v_env_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc_ref(v_env_849_);
lean_dec(v___x_848_);
v___x_850_ = ((lean_object*)(l_Lean_Meta_unifyEq_x3f___lam__0___closed__3));
v___x_961_ = l_Lean_Environment_contains(v_env_849_, v___x_850_, v___x_838_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; lean_object* v___x_963_; 
lean_dec_ref(v_b_842_);
lean_dec_ref(v_a_841_);
lean_dec_ref(v_a_840_);
lean_dec(v_mvarId_839_);
v___x_962_ = lean_box(0);
v___x_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
return v___x_963_;
}
else
{
lean_object* v___x_964_; 
v___x_964_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f(v_a_841_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_1031_; 
v_a_965_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_967_ = v___x_964_;
v_isShared_968_ = v_isSharedCheck_1031_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_964_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_1031_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
if (lean_obj_tag(v_a_965_) == 1)
{
lean_object* v_val_969_; lean_object* v_fst_970_; lean_object* v_snd_971_; lean_object* v___x_972_; 
v_val_969_ = lean_ctor_get(v_a_965_, 0);
lean_inc(v_val_969_);
lean_dec_ref_known(v_a_965_, 1);
v_fst_970_ = lean_ctor_get(v_val_969_, 0);
lean_inc(v_fst_970_);
v_snd_971_ = lean_ctor_get(v_val_969_, 1);
lean_inc(v_snd_971_);
lean_dec(v_val_969_);
v___x_972_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f(v_b_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_1018_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_975_ = v___x_972_;
v_isShared_976_ = v_isSharedCheck_1018_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_972_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_1018_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
if (lean_obj_tag(v_a_973_) == 1)
{
lean_object* v_val_982_; lean_object* v_fst_983_; lean_object* v_snd_984_; lean_object* v___x_985_; uint8_t v___x_986_; 
lean_del_object(v___x_967_);
v_val_982_ = lean_ctor_get(v_a_973_, 0);
lean_inc(v_val_982_);
lean_dec_ref_known(v_a_973_, 1);
v_fst_983_ = lean_ctor_get(v_val_982_, 0);
lean_inc(v_fst_983_);
v_snd_984_ = lean_ctor_get(v_val_982_, 1);
lean_inc(v_snd_984_);
lean_dec(v_val_982_);
v___x_985_ = lean_unsigned_to_nat(0u);
v___x_986_ = lean_nat_dec_eq(v_snd_971_, v___x_985_);
if (v___x_986_ == 0)
{
uint8_t v___x_987_; 
v___x_987_ = lean_nat_dec_eq(v_snd_984_, v___x_985_);
if (v___x_987_ == 0)
{
uint8_t v___x_988_; 
lean_del_object(v___x_975_);
v___x_988_ = lean_nat_dec_lt(v_snd_971_, v_snd_984_);
if (v___x_988_ == 0)
{
uint8_t v___x_989_; 
v___x_989_ = lean_nat_dec_eq(v_snd_971_, v_snd_984_);
if (v___x_989_ == 0)
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_990_ = lean_nat_sub(v_snd_971_, v_snd_984_);
lean_dec(v_snd_971_);
v___x_991_ = l_Lean_mkNatLit(v___x_990_);
v___x_992_ = l_Lean_Meta_mkAdd(v_fst_970_, v___x_991_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
lean_inc(v_a_993_);
lean_dec_ref_known(v___x_992_, 1);
v_fst_852_ = v_a_993_;
v_fst_853_ = v_fst_983_;
v_snd_854_ = v_snd_984_;
v___y_855_ = v___y_843_;
v___y_856_ = v___y_844_;
v___y_857_ = v___y_845_;
v___y_858_ = v___y_846_;
goto v___jp_851_;
}
else
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1001_; 
lean_dec(v_snd_984_);
lean_dec(v_fst_983_);
lean_dec_ref(v_a_840_);
lean_dec(v_mvarId_839_);
v_a_994_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_996_ = v___x_992_;
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_992_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_999_; 
if (v_isShared_997_ == 0)
{
v___x_999_ = v___x_996_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_a_994_);
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
lean_dec(v_snd_984_);
v_fst_852_ = v_fst_970_;
v_fst_853_ = v_fst_983_;
v_snd_854_ = v_snd_971_;
v___y_855_ = v___y_843_;
v___y_856_ = v___y_844_;
v___y_857_ = v___y_845_;
v___y_858_ = v___y_846_;
goto v___jp_851_;
}
}
else
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1002_ = lean_nat_sub(v_snd_984_, v_snd_971_);
lean_dec(v_snd_984_);
v___x_1003_ = l_Lean_mkNatLit(v___x_1002_);
v___x_1004_ = l_Lean_Meta_mkAdd(v_fst_983_, v___x_1003_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1005_; 
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_a_1005_);
lean_dec_ref_known(v___x_1004_, 1);
v_fst_852_ = v_fst_970_;
v_fst_853_ = v_a_1005_;
v_snd_854_ = v_snd_971_;
v___y_855_ = v___y_843_;
v___y_856_ = v___y_844_;
v___y_857_ = v___y_845_;
v___y_858_ = v___y_846_;
goto v___jp_851_;
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
lean_dec(v_snd_971_);
lean_dec(v_fst_970_);
lean_dec_ref(v_a_840_);
lean_dec(v_mvarId_839_);
v_a_1006_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_1004_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_1004_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_a_1006_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
}
else
{
lean_dec(v_snd_984_);
lean_dec(v_fst_983_);
lean_dec(v_snd_971_);
lean_dec(v_fst_970_);
lean_dec_ref(v_a_840_);
lean_dec(v_mvarId_839_);
goto v___jp_977_;
}
}
else
{
lean_dec(v_snd_984_);
lean_dec(v_fst_983_);
lean_dec(v_snd_971_);
lean_dec(v_fst_970_);
lean_dec_ref(v_a_840_);
lean_dec(v_mvarId_839_);
goto v___jp_977_;
}
}
else
{
lean_object* v___x_1014_; lean_object* v___x_1016_; 
lean_del_object(v___x_975_);
lean_dec(v_a_973_);
lean_dec(v_snd_971_);
lean_dec(v_fst_970_);
lean_dec_ref(v_a_840_);
lean_dec(v_mvarId_839_);
v___x_1014_ = lean_box(0);
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 0, v___x_1014_);
v___x_1016_ = v___x_967_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1014_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
v___jp_977_:
{
lean_object* v___x_978_; lean_object* v___x_980_; 
v___x_978_ = lean_box(0);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v___x_978_);
v___x_980_ = v___x_975_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v___x_978_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
lean_dec(v_snd_971_);
lean_dec(v_fst_970_);
lean_del_object(v___x_967_);
lean_dec_ref(v_a_840_);
lean_dec(v_mvarId_839_);
v_a_1019_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_972_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_972_);
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
else
{
lean_object* v___x_1027_; lean_object* v___x_1029_; 
lean_dec(v_a_965_);
lean_dec_ref(v_b_842_);
lean_dec_ref(v_a_840_);
lean_dec(v_mvarId_839_);
v___x_1027_ = lean_box(0);
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 0, v___x_1027_);
v___x_1029_ = v___x_967_;
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
}
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
lean_dec_ref(v_b_842_);
lean_dec_ref(v_a_840_);
lean_dec(v_mvarId_839_);
v_a_1032_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_964_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_964_);
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
v___jp_851_:
{
lean_object* v___x_859_; 
lean_inc(v_mvarId_839_);
v___x_859_ = l_Lean_MVarId_getType(v_mvarId_839_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v___x_861_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc_n(v_a_860_, 2);
lean_dec_ref_known(v___x_859_, 1);
v___x_861_ = l_Lean_Meta_getLevel(v_a_860_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; lean_object* v___x_863_; 
v_a_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_a_862_);
lean_dec_ref_known(v___x_861_, 1);
lean_inc_ref(v_fst_853_);
lean_inc_ref(v_fst_852_);
v___x_863_ = l_Lean_Meta_mkEq(v_fst_852_, v_fst_853_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_864_; lean_object* v___x_865_; 
v_a_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_a_864_);
lean_dec_ref_known(v___x_863_, 1);
lean_inc(v_a_860_);
v___x_865_ = l_Lean_mkArrow(v_a_864_, v_a_860_, v___y_857_, v___y_858_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; lean_object* v___x_867_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
lean_inc(v_a_866_);
lean_dec_ref_known(v___x_865_, 1);
lean_inc(v_mvarId_839_);
v___x_867_ = l_Lean_MVarId_getTag(v_mvarId_839_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v___x_869_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_868_);
lean_dec_ref_known(v___x_867_, 1);
v___x_869_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_866_, v_a_868_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_911_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
lean_inc_n(v_a_870_, 2);
lean_dec_ref_known(v___x_869_, 1);
v___x_871_ = lean_box(0);
v___x_872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_872_, 0, v_a_862_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
v___x_873_ = l_Lean_mkConst(v___x_850_, v___x_872_);
v___x_874_ = l_Lean_mkNatLit(v_snd_854_);
lean_inc_ref(v_a_840_);
v___x_875_ = l_Lean_LocalDecl_toExpr(v_a_840_);
v___x_876_ = lean_unsigned_to_nat(6u);
v___x_877_ = lean_mk_empty_array_with_capacity(v___x_876_);
v___x_878_ = lean_array_push(v___x_877_, v_a_860_);
v___x_879_ = lean_array_push(v___x_878_, v_fst_852_);
v___x_880_ = lean_array_push(v___x_879_, v_fst_853_);
v___x_881_ = lean_array_push(v___x_880_, v___x_874_);
v___x_882_ = lean_array_push(v___x_881_, v___x_875_);
v___x_883_ = lean_array_push(v___x_882_, v_a_870_);
v___x_884_ = l_Lean_mkAppN(v___x_873_, v___x_883_);
lean_dec_ref(v___x_883_);
v___x_885_ = l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1___redArg(v_mvarId_839_, v___x_884_, v___y_856_);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_911_ == 0)
{
lean_object* v_unused_912_; 
v_unused_912_ = lean_ctor_get(v___x_885_, 0);
lean_dec(v_unused_912_);
v___x_887_ = v___x_885_;
v_isShared_888_ = v_isSharedCheck_911_;
goto v_resetjp_886_;
}
else
{
lean_dec(v___x_885_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_911_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_889_ = l_Lean_Expr_mvarId_x21(v_a_870_);
lean_dec(v_a_870_);
v___x_890_ = l_Lean_LocalDecl_fvarId(v_a_840_);
lean_dec_ref(v_a_840_);
v___x_891_ = l_Lean_MVarId_tryClear(v___x_889_, v___x_890_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_902_; 
v_a_892_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_902_ == 0)
{
v___x_894_ = v___x_891_;
v_isShared_895_ = v_isSharedCheck_902_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_891_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_902_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_888_ == 0)
{
lean_ctor_set_tag(v___x_887_, 1);
lean_ctor_set(v___x_887_, 0, v_a_892_);
v___x_897_ = v___x_887_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_892_);
v___x_897_ = v_reuseFailAlloc_901_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
lean_object* v___x_899_; 
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 0, v___x_897_);
v___x_899_ = v___x_894_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_897_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_del_object(v___x_887_);
v_a_903_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_891_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_891_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_903_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
}
else
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
lean_dec(v_a_862_);
lean_dec(v_a_860_);
lean_dec(v_snd_854_);
lean_dec_ref(v_fst_853_);
lean_dec_ref(v_fst_852_);
lean_dec_ref(v_a_840_);
lean_dec(v_mvarId_839_);
v_a_913_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_920_ == 0)
{
v___x_915_ = v___x_869_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_869_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_a_913_);
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
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_928_; 
lean_dec(v_a_866_);
lean_dec(v_a_862_);
lean_dec(v_a_860_);
lean_dec(v_snd_854_);
lean_dec_ref(v_fst_853_);
lean_dec_ref(v_fst_852_);
lean_dec_ref(v_a_840_);
lean_dec(v_mvarId_839_);
v_a_921_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_928_ == 0)
{
v___x_923_ = v___x_867_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_867_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_926_; 
if (v_isShared_924_ == 0)
{
v___x_926_ = v___x_923_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_921_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
else
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_936_; 
lean_dec(v_a_862_);
lean_dec(v_a_860_);
lean_dec(v_snd_854_);
lean_dec_ref(v_fst_853_);
lean_dec_ref(v_fst_852_);
lean_dec_ref(v_a_840_);
lean_dec(v_mvarId_839_);
v_a_929_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_936_ == 0)
{
v___x_931_ = v___x_865_;
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_865_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_929_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
else
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
lean_dec(v_a_862_);
lean_dec(v_a_860_);
lean_dec(v_snd_854_);
lean_dec_ref(v_fst_853_);
lean_dec_ref(v_fst_852_);
lean_dec_ref(v_a_840_);
lean_dec(v_mvarId_839_);
v_a_937_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_863_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_863_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
else
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
lean_dec(v_a_860_);
lean_dec(v_snd_854_);
lean_dec_ref(v_fst_853_);
lean_dec_ref(v_fst_852_);
lean_dec_ref(v_a_840_);
lean_dec(v_mvarId_839_);
v_a_945_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_952_ == 0)
{
v___x_947_ = v___x_861_;
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_861_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_a_945_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
else
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
lean_dec(v_snd_854_);
lean_dec_ref(v_fst_853_);
lean_dec_ref(v_fst_852_);
lean_dec_ref(v_a_840_);
lean_dec(v_mvarId_839_);
v_a_953_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_960_ == 0)
{
v___x_955_ = v___x_859_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_859_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_956_ == 0)
{
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_953_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__0___boxed(lean_object* v___x_1040_, lean_object* v_mvarId_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_b_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
uint8_t v___x_9559__boxed_1050_; lean_object* v_res_1051_; 
v___x_9559__boxed_1050_ = lean_unbox(v___x_1040_);
v_res_1051_ = l_Lean_Meta_unifyEq_x3f___lam__0(v___x_9559__boxed_1050_, v_mvarId_1041_, v_a_1042_, v_a_1043_, v_b_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
return v_res_1051_;
}
}
static lean_object* _init_l_Lean_Meta_unifyEq_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = ((lean_object*)(l_Lean_Meta_unifyEq_x3f___lam__1___closed__2));
v___x_1057_ = l_Lean_stringToMessageData(v___x_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__1(lean_object* v_eqFVarId_1058_, lean_object* v_mvarId_1059_, lean_object* v_subst_1060_, lean_object* v_acyclic_1061_, lean_object* v_caseName_x3f_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v___x_1068_; 
lean_inc(v_eqFVarId_1058_);
v___x_1068_ = l_Lean_FVarId_getDecl___redArg(v_eqFVarId_1058_, v___y_1063_, v___y_1065_, v___y_1066_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; lean_object* v___x_1070_; uint8_t v___x_1071_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1069_);
lean_dec_ref_known(v___x_1068_, 1);
v___x_1070_ = l_Lean_LocalDecl_type(v_a_1069_);
v___x_1071_ = l_Lean_Expr_isHEq(v___x_1070_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; 
v___x_1072_ = ((lean_object*)(l_Lean_Meta_unifyEq_x3f___lam__1___closed__1));
v___x_1073_ = lean_unsigned_to_nat(3u);
v___x_1074_ = l_Lean_Expr_isAppOfArity(v___x_1070_, v___x_1072_, v___x_1073_);
if (v___x_1074_ == 0)
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
lean_dec(v_a_1069_);
lean_dec(v_caseName_x3f_1062_);
lean_dec_ref(v_acyclic_1061_);
lean_dec(v_subst_1060_);
lean_dec(v_mvarId_1059_);
lean_dec(v_eqFVarId_1058_);
v___x_1075_ = lean_obj_once(&l_Lean_Meta_unifyEq_x3f___lam__1___closed__3, &l_Lean_Meta_unifyEq_x3f___lam__1___closed__3_once, _init_l_Lean_Meta_unifyEq_x3f___lam__1___closed__3);
v___x_1076_ = l_Lean_indentExpr(v___x_1070_);
v___x_1077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1075_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
v___x_1078_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(v___x_1077_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
return v___x_1078_;
}
else
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v_a_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1079_ = l_Lean_Expr_appFn_x21(v___x_1070_);
v___x_1080_ = l_Lean_Expr_appArg_x21(v___x_1079_);
lean_dec_ref(v___x_1079_);
lean_inc_ref(v___x_1080_);
v___x_1081_ = l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__0___redArg(v___x_1080_, v___y_1064_);
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_a_1082_);
lean_dec_ref(v___x_1081_);
v___x_1083_ = l_Lean_Expr_appArg_x21(v___x_1070_);
lean_dec_ref(v___x_1070_);
lean_inc_ref(v___x_1083_);
v___x_1084_ = l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__0___redArg(v___x_1083_, v___y_1064_);
if (lean_obj_tag(v_a_1082_) == 1)
{
lean_object* v_a_1085_; 
lean_dec(v_caseName_x3f_1062_);
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_a_1085_);
lean_dec_ref(v___x_1084_);
if (lean_obj_tag(v_a_1085_) == 1)
{
lean_object* v_fvarId_1086_; lean_object* v_fvarId_1087_; lean_object* v___x_1088_; 
v_fvarId_1086_ = lean_ctor_get(v_a_1082_, 0);
lean_inc(v_fvarId_1086_);
lean_dec_ref_known(v_a_1082_, 1);
v_fvarId_1087_ = lean_ctor_get(v_a_1085_, 0);
lean_inc(v_fvarId_1087_);
lean_dec_ref_known(v_a_1085_, 1);
v___x_1088_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1086_, v___y_1063_, v___y_1065_, v___y_1066_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v_a_1089_; lean_object* v___x_1090_; 
v_a_1089_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_a_1089_);
lean_dec_ref_known(v___x_1088_, 1);
v___x_1090_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1087_, v___y_1063_, v___y_1065_, v___y_1066_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v_a_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; uint8_t v___x_1094_; lean_object* v___x_1095_; 
v_a_1091_ = lean_ctor_get(v___x_1090_, 0);
lean_inc(v_a_1091_);
lean_dec_ref_known(v___x_1090_, 1);
v___x_1092_ = l_Lean_LocalDecl_index(v_a_1089_);
lean_dec(v_a_1089_);
v___x_1093_ = l_Lean_LocalDecl_index(v_a_1091_);
lean_dec(v_a_1091_);
v___x_1094_ = lean_nat_dec_lt(v___x_1092_, v___x_1093_);
lean_dec(v___x_1093_);
lean_dec(v___x_1092_);
v___x_1095_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq(v_mvarId_1059_, v_eqFVarId_1058_, v_subst_1060_, v_acyclic_1061_, v_a_1069_, v___x_1080_, v___x_1083_, v___x_1094_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
lean_dec(v_a_1069_);
return v___x_1095_;
}
else
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
lean_dec(v_a_1089_);
lean_dec_ref(v___x_1083_);
lean_dec_ref(v___x_1080_);
lean_dec(v_a_1069_);
lean_dec_ref(v_acyclic_1061_);
lean_dec(v_subst_1060_);
lean_dec(v_mvarId_1059_);
lean_dec(v_eqFVarId_1058_);
v_a_1096_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_1090_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1090_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
lean_dec(v_fvarId_1087_);
lean_dec_ref(v___x_1083_);
lean_dec_ref(v___x_1080_);
lean_dec(v_a_1069_);
lean_dec_ref(v_acyclic_1061_);
lean_dec(v_subst_1060_);
lean_dec(v_mvarId_1059_);
lean_dec(v_eqFVarId_1058_);
v_a_1104_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1088_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1088_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
else
{
lean_object* v___x_1112_; 
lean_dec_ref_known(v_a_1082_, 1);
lean_dec(v_a_1085_);
v___x_1112_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq(v_mvarId_1059_, v_eqFVarId_1058_, v_subst_1060_, v_acyclic_1061_, v_a_1069_, v___x_1080_, v___x_1083_, v___x_1071_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
lean_dec(v_a_1069_);
return v___x_1112_;
}
}
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1154_; 
v_a_1113_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1115_ = v___x_1084_;
v_isShared_1116_ = v_isSharedCheck_1154_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1084_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1154_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
if (lean_obj_tag(v_a_1113_) == 1)
{
lean_object* v___x_1117_; 
lean_dec_ref_known(v_a_1113_, 1);
lean_del_object(v___x_1115_);
lean_dec(v_a_1082_);
lean_dec(v_caseName_x3f_1062_);
v___x_1117_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq(v_mvarId_1059_, v_eqFVarId_1058_, v_subst_1060_, v_acyclic_1061_, v_a_1069_, v___x_1080_, v___x_1083_, v___x_1074_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
lean_dec(v_a_1069_);
return v___x_1117_;
}
else
{
lean_object* v___x_1118_; 
lean_dec_ref(v___x_1083_);
lean_dec_ref(v___x_1080_);
lean_dec_ref(v_acyclic_1061_);
lean_inc(v_a_1113_);
lean_inc(v_a_1082_);
v___x_1118_ = l_Lean_Meta_isExprDefEq(v_a_1082_, v_a_1113_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; uint8_t v___x_1120_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_a_1119_);
lean_dec_ref_known(v___x_1118_, 1);
v___x_1120_ = lean_unbox(v_a_1119_);
lean_dec(v_a_1119_);
if (v___x_1120_ == 0)
{
lean_object* v___x_1121_; lean_object* v___f_1122_; lean_object* v___x_1123_; 
lean_del_object(v___x_1115_);
v___x_1121_ = lean_box(v___x_1074_);
lean_inc(v_a_1069_);
lean_inc(v_mvarId_1059_);
v___f_1122_ = lean_alloc_closure((void*)(l_Lean_Meta_unifyEq_x3f___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1122_, 0, v___x_1121_);
lean_closure_set(v___f_1122_, 1, v_mvarId_1059_);
lean_closure_set(v___f_1122_, 2, v_a_1069_);
v___x_1123_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection(v_mvarId_1059_, v_eqFVarId_1058_, v_subst_1060_, v_caseName_x3f_1062_, v_a_1069_, v___f_1122_, v_a_1082_, v_a_1113_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
lean_dec(v_a_1069_);
return v___x_1123_;
}
else
{
lean_object* v___x_1124_; 
lean_dec(v_a_1113_);
lean_dec(v_a_1082_);
lean_dec(v_a_1069_);
lean_dec(v_caseName_x3f_1062_);
v___x_1124_ = l_Lean_MVarId_clear(v_mvarId_1059_, v_eqFVarId_1058_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1137_; 
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1127_ = v___x_1124_;
v_isShared_1128_ = v_isSharedCheck_1137_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1124_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1137_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1132_; 
v___x_1129_ = lean_unsigned_to_nat(0u);
v___x_1130_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1130_, 0, v_a_1125_);
lean_ctor_set(v___x_1130_, 1, v_subst_1060_);
lean_ctor_set(v___x_1130_, 2, v___x_1129_);
if (v_isShared_1116_ == 0)
{
lean_ctor_set_tag(v___x_1115_, 1);
lean_ctor_set(v___x_1115_, 0, v___x_1130_);
v___x_1132_ = v___x_1115_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
lean_object* v___x_1134_; 
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v___x_1132_);
v___x_1134_ = v___x_1127_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1132_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
else
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1145_; 
lean_del_object(v___x_1115_);
lean_dec(v_subst_1060_);
v_a_1138_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1140_ = v___x_1124_;
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1124_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1143_; 
if (v_isShared_1141_ == 0)
{
v___x_1143_ = v___x_1140_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_a_1138_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
}
}
else
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
lean_del_object(v___x_1115_);
lean_dec(v_a_1113_);
lean_dec(v_a_1082_);
lean_dec(v_a_1069_);
lean_dec(v_caseName_x3f_1062_);
lean_dec(v_subst_1060_);
lean_dec(v_mvarId_1059_);
lean_dec(v_eqFVarId_1058_);
v_a_1146_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1148_ = v___x_1118_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1118_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1146_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
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
lean_object* v___x_1155_; 
lean_dec_ref(v___x_1070_);
lean_dec(v_caseName_x3f_1062_);
lean_dec_ref(v_acyclic_1061_);
lean_dec(v_eqFVarId_1058_);
v___x_1155_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_heqToEq_x27(v_mvarId_1059_, v_a_1069_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
lean_dec(v_a_1069_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1166_; 
v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1158_ = v___x_1155_;
v_isShared_1159_ = v_isSharedCheck_1166_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1155_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1166_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1164_; 
v___x_1160_ = lean_unsigned_to_nat(1u);
v___x_1161_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1161_, 0, v_a_1156_);
lean_ctor_set(v___x_1161_, 1, v_subst_1060_);
lean_ctor_set(v___x_1161_, 2, v___x_1160_);
v___x_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 0, v___x_1162_);
v___x_1164_ = v___x_1158_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v___x_1162_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
lean_dec(v_subst_1060_);
v_a_1167_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v___x_1155_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1155_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
}
else
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1182_; 
lean_dec(v_caseName_x3f_1062_);
lean_dec_ref(v_acyclic_1061_);
lean_dec(v_subst_1060_);
lean_dec(v_mvarId_1059_);
lean_dec(v_eqFVarId_1058_);
v_a_1175_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1177_ = v___x_1068_;
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1068_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1180_; 
if (v_isShared_1178_ == 0)
{
v___x_1180_ = v___x_1177_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_a_1175_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__1___boxed(lean_object* v_eqFVarId_1183_, lean_object* v_mvarId_1184_, lean_object* v_subst_1185_, lean_object* v_acyclic_1186_, lean_object* v_caseName_x3f_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Lean_Meta_unifyEq_x3f___lam__1(v_eqFVarId_1183_, v_mvarId_1184_, v_subst_1185_, v_acyclic_1186_, v_caseName_x3f_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f(lean_object* v_mvarId_1194_, lean_object* v_eqFVarId_1195_, lean_object* v_subst_1196_, lean_object* v_acyclic_1197_, lean_object* v_caseName_x3f_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_){
_start:
{
lean_object* v___f_1204_; lean_object* v___x_1205_; 
lean_inc(v_mvarId_1194_);
v___f_1204_ = lean_alloc_closure((void*)(l_Lean_Meta_unifyEq_x3f___lam__1___boxed), 10, 5);
lean_closure_set(v___f_1204_, 0, v_eqFVarId_1195_);
lean_closure_set(v___f_1204_, 1, v_mvarId_1194_);
lean_closure_set(v___f_1204_, 2, v_subst_1196_);
lean_closure_set(v___f_1204_, 3, v_acyclic_1197_);
lean_closure_set(v___f_1204_, 4, v_caseName_x3f_1198_);
v___x_1205_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___redArg(v_mvarId_1194_, v___f_1204_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___boxed(lean_object* v_mvarId_1206_, lean_object* v_eqFVarId_1207_, lean_object* v_subst_1208_, lean_object* v_acyclic_1209_, lean_object* v_caseName_x3f_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Lean_Meta_unifyEq_x3f(v_mvarId_1206_, v_eqFVarId_1207_, v_subst_1208_, v_acyclic_1209_, v_caseName_x3f_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_);
lean_dec(v_a_1214_);
lean_dec_ref(v_a_1213_);
lean_dec(v_a_1212_);
lean_dec_ref(v_a_1211_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1(lean_object* v_mvarId_1217_, lean_object* v_val_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v___x_1224_; 
v___x_1224_ = l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1___redArg(v_mvarId_1217_, v_val_1218_, v___y_1220_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1___boxed(lean_object* v_mvarId_1225_, lean_object* v_val_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1(v_mvarId_1225_, v_val_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1(lean_object* v_00_u03b2_1233_, lean_object* v_x_1234_, lean_object* v_x_1235_, lean_object* v_x_1236_){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1___redArg(v_x_1234_, v_x_1235_, v_x_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_1238_, lean_object* v_x_1239_, size_t v_x_1240_, size_t v_x_1241_, lean_object* v_x_1242_, lean_object* v_x_1243_){
_start:
{
lean_object* v___x_1244_; 
v___x_1244_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg(v_x_1239_, v_x_1240_, v_x_1241_, v_x_1242_, v_x_1243_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1245_, lean_object* v_x_1246_, lean_object* v_x_1247_, lean_object* v_x_1248_, lean_object* v_x_1249_, lean_object* v_x_1250_){
_start:
{
size_t v_x_10270__boxed_1251_; size_t v_x_10271__boxed_1252_; lean_object* v_res_1253_; 
v_x_10270__boxed_1251_ = lean_unbox_usize(v_x_1247_);
lean_dec(v_x_1247_);
v_x_10271__boxed_1252_ = lean_unbox_usize(v_x_1248_);
lean_dec(v_x_1248_);
v_res_1253_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3(v_00_u03b2_1245_, v_x_1246_, v_x_10270__boxed_1251_, v_x_10271__boxed_1252_, v_x_1249_, v_x_1250_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1254_, lean_object* v_n_1255_, lean_object* v_k_1256_, lean_object* v_v_1257_){
_start:
{
lean_object* v___x_1258_; 
v___x_1258_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__4___redArg(v_n_1255_, v_k_1256_, v_v_1257_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_1259_, size_t v_depth_1260_, lean_object* v_keys_1261_, lean_object* v_vals_1262_, lean_object* v_heq_1263_, lean_object* v_i_1264_, lean_object* v_entries_1265_){
_start:
{
lean_object* v___x_1266_; 
v___x_1266_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_depth_1260_, v_keys_1261_, v_vals_1262_, v_i_1264_, v_entries_1265_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b2_1267_, lean_object* v_depth_1268_, lean_object* v_keys_1269_, lean_object* v_vals_1270_, lean_object* v_heq_1271_, lean_object* v_i_1272_, lean_object* v_entries_1273_){
_start:
{
size_t v_depth_boxed_1274_; lean_object* v_res_1275_; 
v_depth_boxed_1274_ = lean_unbox_usize(v_depth_1268_);
lean_dec(v_depth_1268_);
v_res_1275_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__5(v_00_u03b2_1267_, v_depth_boxed_1274_, v_keys_1269_, v_vals_1270_, v_heq_1271_, v_i_1272_, v_entries_1273_);
lean_dec_ref(v_vals_1270_);
lean_dec_ref(v_keys_1269_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_1276_, lean_object* v_x_1277_, lean_object* v_x_1278_, lean_object* v_x_1279_, lean_object* v_x_1280_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(v_x_1277_, v_x_1278_, v_x_1279_, v_x_1280_);
return v___x_1281_;
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
