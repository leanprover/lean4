// Lean compiler output
// Module: Lean.Meta.Tactic.Injection
// Imports: public import Lean.Meta.Tactic.Subst
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
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
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_isConstructorApp_x27_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_heqToEq(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_intro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchEqHEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t l_Lean_Expr_isRawNatLit(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_LocalContext_getFVarIds(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCtorNumPropFields_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCtorNumPropFields_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCtorNumPropFields_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCtorNumPropFields_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResultCore_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResultCore_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResultCore_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResultCore_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResultCore_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResultCore_solved_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResultCore_solved_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResultCore_subgoal_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResultCore_subgoal_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_injectionCore___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_injectionCore___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_injectionCore___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_injectionCore___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_injectionCore___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_injectionCore___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "ill-formed noConfusion auxiliary construction"};
static const lean_object* l_Lean_Meta_injectionCore___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Meta_injectionCore___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__0_value)}};
static const lean_object* l_Lean_Meta_injectionCore___lam__1___closed__1 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__1_value;
static lean_once_cell_t l_Lean_Meta_injectionCore___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_injectionCore___lam__1___closed__2;
static lean_once_cell_t l_Lean_Meta_injectionCore___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_injectionCore___lam__1___closed__3;
static const lean_string_object l_Lean_Meta_injectionCore___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "equality of constructor applications expected"};
static const lean_object* l_Lean_Meta_injectionCore___lam__1___closed__4 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__4_value;
static const lean_ctor_object l_Lean_Meta_injectionCore___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__4_value)}};
static const lean_object* l_Lean_Meta_injectionCore___lam__1___closed__5 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__5_value;
static lean_once_cell_t l_Lean_Meta_injectionCore___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_injectionCore___lam__1___closed__6;
static lean_once_cell_t l_Lean_Meta_injectionCore___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_injectionCore___lam__1___closed__7;
static const lean_string_object l_Lean_Meta_injectionCore___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "subgoal with "};
static const lean_object* l_Lean_Meta_injectionCore___lam__1___closed__8 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__8_value;
static lean_once_cell_t l_Lean_Meta_injectionCore___lam__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_injectionCore___lam__1___closed__9;
static const lean_string_object l_Lean_Meta_injectionCore___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " fields:\n"};
static const lean_object* l_Lean_Meta_injectionCore___lam__1___closed__10 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__10_value;
static lean_once_cell_t l_Lean_Meta_injectionCore___lam__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_injectionCore___lam__1___closed__11;
static const lean_string_object l_Lean_Meta_injectionCore___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "ill-formed noConfusion auxiliary construction with type:"};
static const lean_object* l_Lean_Meta_injectionCore___lam__1___closed__12 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__12_value;
static lean_once_cell_t l_Lean_Meta_injectionCore___lam__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_injectionCore___lam__1___closed__13;
static const lean_string_object l_Lean_Meta_injectionCore___lam__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "got no-confusion principle"};
static const lean_object* l_Lean_Meta_injectionCore___lam__1___closed__14 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__14_value;
static lean_once_cell_t l_Lean_Meta_injectionCore___lam__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_injectionCore___lam__1___closed__15;
static const lean_string_object l_Lean_Meta_injectionCore___lam__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "\nof type"};
static const lean_object* l_Lean_Meta_injectionCore___lam__1___closed__16 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__16_value;
static lean_once_cell_t l_Lean_Meta_injectionCore___lam__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_injectionCore___lam__1___closed__17;
static const lean_string_object l_Lean_Meta_injectionCore___lam__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_injectionCore___lam__1___closed__18 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__18_value;
static const lean_ctor_object l_Lean_Meta_injectionCore___lam__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_injectionCore___lam__1___closed__19 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__19_value;
static const lean_string_object l_Lean_Meta_injectionCore___lam__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "equality expected"};
static const lean_object* l_Lean_Meta_injectionCore___lam__1___closed__20 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__20_value;
static const lean_ctor_object l_Lean_Meta_injectionCore___lam__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__20_value)}};
static const lean_object* l_Lean_Meta_injectionCore___lam__1___closed__21 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__21_value;
static lean_once_cell_t l_Lean_Meta_injectionCore___lam__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_injectionCore___lam__1___closed__22;
static lean_once_cell_t l_Lean_Meta_injectionCore___lam__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_injectionCore___lam__1___closed__23;
static const lean_string_object l_Lean_Meta_injectionCore___lam__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_injectionCore___lam__1___closed__24 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__24_value;
static const lean_string_object l_Lean_Meta_injectionCore___lam__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_injectionCore___lam__1___closed__25 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__25_value;
static const lean_string_object l_Lean_Meta_injectionCore___lam__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "applying noConfusion to "};
static const lean_object* l_Lean_Meta_injectionCore___lam__1___closed__26 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__26_value;
static lean_once_cell_t l_Lean_Meta_injectionCore___lam__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_injectionCore___lam__1___closed__27;
static const lean_string_object l_Lean_Meta_injectionCore___lam__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " at\n"};
static const lean_object* l_Lean_Meta_injectionCore___lam__1___closed__28 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__28_value;
static lean_once_cell_t l_Lean_Meta_injectionCore___lam__1___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_injectionCore___lam__1___closed__29;
static const lean_string_object l_Lean_Meta_injectionCore___lam__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HEq"};
static const lean_object* l_Lean_Meta_injectionCore___lam__1___closed__30 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__30_value;
static const lean_ctor_object l_Lean_Meta_injectionCore___lam__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_object* l_Lean_Meta_injectionCore___lam__1___closed__31 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__31_value;
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_injectionCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "injection"};
static const lean_object* l_Lean_Meta_injectionCore___closed__0 = (const lean_object*)&l_Lean_Meta_injectionCore___closed__0_value;
static const lean_ctor_object l_Lean_Meta_injectionCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_injectionCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(191, 140, 244, 245, 189, 133, 170, 178)}};
static const lean_object* l_Lean_Meta_injectionCore___closed__1 = (const lean_object*)&l_Lean_Meta_injectionCore___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_solved_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_solved_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_subgoal_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_subgoal_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_injectionIntro___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_injectionIntro___closed__0 = (const lean_object*)&l_Lean_Meta_injectionIntro___closed__0_value;
static const lean_ctor_object l_Lean_Meta_injectionIntro___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_injectionIntro___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_injectionIntro___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Meta_injectionIntro___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_injectionIntro___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_injectionCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 78, 14, 229, 214, 232, 184, 172)}};
static const lean_object* l_Lean_Meta_injectionIntro___closed__1 = (const lean_object*)&l_Lean_Meta_injectionIntro___closed__1_value;
static lean_once_cell_t l_Lean_Meta_injectionIntro___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_injectionIntro___closed__2;
static const lean_string_object l_Lean_Meta_injectionIntro___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "introducing "};
static const lean_object* l_Lean_Meta_injectionIntro___closed__3 = (const lean_object*)&l_Lean_Meta_injectionIntro___closed__3_value;
static lean_once_cell_t l_Lean_Meta_injectionIntro___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_injectionIntro___closed__4;
static const lean_string_object l_Lean_Meta_injectionIntro___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = " new equalities at\n"};
static const lean_object* l_Lean_Meta_injectionIntro___closed__5 = (const lean_object*)&l_Lean_Meta_injectionIntro___closed__5_value;
static lean_once_cell_t l_Lean_Meta_injectionIntro___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_injectionIntro___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_solved_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_solved_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_subgoal_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_subgoal_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "injections"};
static const lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 237, 111, 89, 101, 171, 168, 71)}};
static const lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "recursion depth exceeded"};
static const lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__2_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injections___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injections___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injections(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injections___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__0_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__0_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__0_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__1_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__0_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__1_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__1_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__2_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__2_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__2_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__3_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__1_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__2_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__3_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__3_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__4_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__3_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__4_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__4_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__5_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__4_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__5_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__5_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__6_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Injection"};
static const lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__6_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__6_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__7_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__5_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__6_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(128, 18, 156, 80, 55, 88, 126, 30)}};
static const lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__7_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__7_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__8_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__7_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(57, 64, 14, 1, 190, 235, 26, 3)}};
static const lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__8_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__8_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__9_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__9_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__9_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__10_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__8_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__9_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(224, 33, 26, 150, 69, 11, 116, 228)}};
static const lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__10_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__10_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__11_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__11_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__11_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__12_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__10_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__11_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(65, 96, 206, 69, 56, 251, 244, 183)}};
static const lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__12_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__12_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__13_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__12_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__2_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(228, 4, 144, 92, 179, 114, 100, 3)}};
static const lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__13_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__13_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__14_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__13_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(120, 246, 74, 246, 83, 217, 223, 61)}};
static const lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__14_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__14_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__15_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__14_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(101, 249, 16, 135, 154, 231, 101, 58)}};
static const lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__15_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__15_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__16_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__15_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__6_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 101, 151, 212, 249, 10, 45, 237)}};
static const lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__16_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__16_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__17_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__16_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1583609249) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(44, 24, 14, 24, 81, 49, 141, 56)}};
static const lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__17_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__17_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__18_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__18_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__18_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__19_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__17_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__18_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(227, 116, 5, 78, 38, 203, 85, 222)}};
static const lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__19_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__19_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__20_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__20_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__20_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__21_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__19_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__20_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(131, 146, 13, 244, 3, 59, 172, 83)}};
static const lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__21_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__21_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__22_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__21_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(70, 93, 108, 76, 37, 26, 40, 93)}};
static const lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__22_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__22_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg___lam__0(lean_object* v_k_1_, lean_object* v_b_2_, lean_object* v_c_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_){
_start:
{
lean_object* v___x_9_; 
lean_inc(v___y_7_);
lean_inc_ref(v___y_6_);
lean_inc(v___y_5_);
lean_inc_ref(v___y_4_);
v___x_9_ = lean_apply_7(v_k_1_, v_b_2_, v_c_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, lean_box(0));
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg___lam__0___boxed(lean_object* v_k_10_, lean_object* v_b_11_, lean_object* v_c_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg___lam__0(v_k_10_, v_b_11_, v_c_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
lean_dec(v___y_14_);
lean_dec_ref(v___y_13_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg(lean_object* v_type_19_, lean_object* v_k_20_, uint8_t v_cleanupAnnotations_21_, uint8_t v_whnfType_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_){
_start:
{
lean_object* v___f_28_; lean_object* v___x_29_; 
v___f_28_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_28_, 0, v_k_20_);
v___x_29_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_19_, v___f_28_, v_cleanupAnnotations_21_, v_whnfType_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
if (lean_obj_tag(v___x_29_) == 0)
{
lean_object* v_a_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_37_; 
v_a_30_ = lean_ctor_get(v___x_29_, 0);
v_isSharedCheck_37_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_37_ == 0)
{
v___x_32_ = v___x_29_;
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_a_30_);
lean_dec(v___x_29_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___x_35_; 
if (v_isShared_33_ == 0)
{
v___x_35_ = v___x_32_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v_a_30_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
}
}
}
else
{
lean_object* v_a_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_45_; 
v_a_38_ = lean_ctor_get(v___x_29_, 0);
v_isSharedCheck_45_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_45_ == 0)
{
v___x_40_ = v___x_29_;
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_a_38_);
lean_dec(v___x_29_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___x_43_; 
if (v_isShared_41_ == 0)
{
v___x_43_ = v___x_40_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_a_38_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
return v___x_43_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg___boxed(lean_object* v_type_46_, lean_object* v_k_47_, lean_object* v_cleanupAnnotations_48_, lean_object* v_whnfType_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_55_; uint8_t v_whnfType_boxed_56_; lean_object* v_res_57_; 
v_cleanupAnnotations_boxed_55_ = lean_unbox(v_cleanupAnnotations_48_);
v_whnfType_boxed_56_ = lean_unbox(v_whnfType_49_);
v_res_57_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg(v_type_46_, v_k_47_, v_cleanupAnnotations_boxed_55_, v_whnfType_boxed_56_, v___y_50_, v___y_51_, v___y_52_, v___y_53_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1(lean_object* v_00_u03b1_58_, lean_object* v_type_59_, lean_object* v_k_60_, uint8_t v_cleanupAnnotations_61_, uint8_t v_whnfType_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg(v_type_59_, v_k_60_, v_cleanupAnnotations_61_, v_whnfType_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___boxed(lean_object* v_00_u03b1_69_, lean_object* v_type_70_, lean_object* v_k_71_, lean_object* v_cleanupAnnotations_72_, lean_object* v_whnfType_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_79_; uint8_t v_whnfType_boxed_80_; lean_object* v_res_81_; 
v_cleanupAnnotations_boxed_79_ = lean_unbox(v_cleanupAnnotations_72_);
v_whnfType_boxed_80_ = lean_unbox(v_whnfType_73_);
v_res_81_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1(v_00_u03b1_69_, v_type_70_, v_k_71_, v_cleanupAnnotations_boxed_79_, v_whnfType_boxed_80_, v___y_74_, v___y_75_, v___y_76_, v___y_77_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCtorNumPropFields_spec__0___redArg(lean_object* v_upperBound_82_, lean_object* v_ctorInfo_83_, lean_object* v_xs_84_, lean_object* v_a_85_, lean_object* v_b_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
uint8_t v___x_92_; 
v___x_92_ = lean_nat_dec_lt(v_a_85_, v_upperBound_82_);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; 
lean_dec(v_a_85_);
v___x_93_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_93_, 0, v_b_86_);
return v___x_93_;
}
else
{
lean_object* v_numParams_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v_numParams_94_ = lean_ctor_get(v_ctorInfo_83_, 3);
v___x_95_ = l_Lean_instInhabitedExpr;
v___x_96_ = lean_nat_add(v_numParams_94_, v_a_85_);
v___x_97_ = lean_array_get_borrowed(v___x_95_, v_xs_84_, v___x_96_);
lean_dec(v___x_96_);
lean_inc(v___y_90_);
lean_inc_ref(v___y_89_);
lean_inc(v___y_88_);
lean_inc_ref(v___y_87_);
lean_inc(v___x_97_);
v___x_98_ = lean_infer_type(v___x_97_, v___y_87_, v___y_88_, v___y_89_, v___y_90_);
if (lean_obj_tag(v___x_98_) == 0)
{
lean_object* v_a_99_; lean_object* v___x_100_; 
v_a_99_ = lean_ctor_get(v___x_98_, 0);
lean_inc(v_a_99_);
lean_dec_ref_known(v___x_98_, 1);
v___x_100_ = l_Lean_Meta_isProp(v_a_99_, v___y_87_, v___y_88_, v___y_89_, v___y_90_);
if (lean_obj_tag(v___x_100_) == 0)
{
lean_object* v_a_101_; lean_object* v_a_103_; uint8_t v___x_107_; 
v_a_101_ = lean_ctor_get(v___x_100_, 0);
lean_inc(v_a_101_);
lean_dec_ref_known(v___x_100_, 1);
v___x_107_ = lean_unbox(v_a_101_);
lean_dec(v_a_101_);
if (v___x_107_ == 0)
{
v_a_103_ = v_b_86_;
goto v___jp_102_;
}
else
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = lean_unsigned_to_nat(1u);
v___x_109_ = lean_nat_add(v_b_86_, v___x_108_);
lean_dec(v_b_86_);
v_a_103_ = v___x_109_;
goto v___jp_102_;
}
v___jp_102_:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = lean_unsigned_to_nat(1u);
v___x_105_ = lean_nat_add(v_a_85_, v___x_104_);
lean_dec(v_a_85_);
v_a_85_ = v___x_105_;
v_b_86_ = v_a_103_;
goto _start;
}
}
else
{
lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_117_; 
lean_dec(v_b_86_);
lean_dec(v_a_85_);
v_a_110_ = lean_ctor_get(v___x_100_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_117_ == 0)
{
v___x_112_ = v___x_100_;
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v___x_100_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_115_; 
if (v_isShared_113_ == 0)
{
v___x_115_ = v___x_112_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_a_110_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
else
{
lean_object* v_a_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_125_; 
lean_dec(v_b_86_);
lean_dec(v_a_85_);
v_a_118_ = lean_ctor_get(v___x_98_, 0);
v_isSharedCheck_125_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_125_ == 0)
{
v___x_120_ = v___x_98_;
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_dec(v___x_98_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_123_; 
if (v_isShared_121_ == 0)
{
v___x_123_ = v___x_120_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_a_118_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCtorNumPropFields_spec__0___redArg___boxed(lean_object* v_upperBound_126_, lean_object* v_ctorInfo_127_, lean_object* v_xs_128_, lean_object* v_a_129_, lean_object* v_b_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCtorNumPropFields_spec__0___redArg(v_upperBound_126_, v_ctorInfo_127_, v_xs_128_, v_a_129_, v_b_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
lean_dec_ref(v_xs_128_);
lean_dec_ref(v_ctorInfo_127_);
lean_dec(v_upperBound_126_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields___lam__0(lean_object* v_numFields_137_, lean_object* v_ctorInfo_138_, lean_object* v_xs_139_, lean_object* v_x_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = lean_unsigned_to_nat(0u);
v___x_147_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCtorNumPropFields_spec__0___redArg(v_numFields_137_, v_ctorInfo_138_, v_xs_139_, v___x_146_, v___x_146_, v___y_141_, v___y_142_, v___y_143_, v___y_144_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields___lam__0___boxed(lean_object* v_numFields_148_, lean_object* v_ctorInfo_149_, lean_object* v_xs_150_, lean_object* v_x_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Lean_Meta_getCtorNumPropFields___lam__0(v_numFields_148_, v_ctorInfo_149_, v_xs_150_, v_x_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_);
lean_dec(v___y_155_);
lean_dec_ref(v___y_154_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_152_);
lean_dec_ref(v_x_151_);
lean_dec_ref(v_xs_150_);
lean_dec_ref(v_ctorInfo_149_);
lean_dec(v_numFields_148_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields(lean_object* v_ctorInfo_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_){
_start:
{
lean_object* v_toConstantVal_164_; lean_object* v_numFields_165_; lean_object* v_type_166_; lean_object* v___f_167_; uint8_t v___x_168_; lean_object* v___x_169_; 
v_toConstantVal_164_ = lean_ctor_get(v_ctorInfo_158_, 0);
v_numFields_165_ = lean_ctor_get(v_ctorInfo_158_, 4);
lean_inc(v_numFields_165_);
v_type_166_ = lean_ctor_get(v_toConstantVal_164_, 2);
lean_inc_ref(v_type_166_);
v___f_167_ = lean_alloc_closure((void*)(l_Lean_Meta_getCtorNumPropFields___lam__0___boxed), 9, 2);
lean_closure_set(v___f_167_, 0, v_numFields_165_);
lean_closure_set(v___f_167_, 1, v_ctorInfo_158_);
v___x_168_ = 0;
v___x_169_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg(v_type_166_, v___f_167_, v___x_168_, v___x_168_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields___boxed(lean_object* v_ctorInfo_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_Meta_getCtorNumPropFields(v_ctorInfo_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_);
lean_dec(v_a_174_);
lean_dec_ref(v_a_173_);
lean_dec(v_a_172_);
lean_dec_ref(v_a_171_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCtorNumPropFields_spec__0(lean_object* v_upperBound_177_, lean_object* v_ctorInfo_178_, lean_object* v_xs_179_, lean_object* v_inst_180_, lean_object* v_R_181_, lean_object* v_a_182_, lean_object* v_b_183_, lean_object* v_c_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCtorNumPropFields_spec__0___redArg(v_upperBound_177_, v_ctorInfo_178_, v_xs_179_, v_a_182_, v_b_183_, v___y_185_, v___y_186_, v___y_187_, v___y_188_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCtorNumPropFields_spec__0___boxed(lean_object* v_upperBound_191_, lean_object* v_ctorInfo_192_, lean_object* v_xs_193_, lean_object* v_inst_194_, lean_object* v_R_195_, lean_object* v_a_196_, lean_object* v_b_197_, lean_object* v_c_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCtorNumPropFields_spec__0(v_upperBound_191_, v_ctorInfo_192_, v_xs_193_, v_inst_194_, v_R_195_, v_a_196_, v_b_197_, v_c_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec_ref(v_xs_193_);
lean_dec_ref(v_ctorInfo_192_);
lean_dec(v_upperBound_191_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResultCore_ctorIdx(lean_object* v_x_205_){
_start:
{
if (lean_obj_tag(v_x_205_) == 0)
{
lean_object* v___x_206_; 
v___x_206_ = lean_unsigned_to_nat(0u);
return v___x_206_;
}
else
{
lean_object* v___x_207_; 
v___x_207_ = lean_unsigned_to_nat(1u);
return v___x_207_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResultCore_ctorIdx___boxed(lean_object* v_x_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_Meta_InjectionResultCore_ctorIdx(v_x_208_);
lean_dec(v_x_208_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResultCore_ctorElim___redArg(lean_object* v_t_210_, lean_object* v_k_211_){
_start:
{
if (lean_obj_tag(v_t_210_) == 0)
{
return v_k_211_;
}
else
{
lean_object* v_mvarId_212_; lean_object* v_numNewEqs_213_; lean_object* v___x_214_; 
v_mvarId_212_ = lean_ctor_get(v_t_210_, 0);
lean_inc(v_mvarId_212_);
v_numNewEqs_213_ = lean_ctor_get(v_t_210_, 1);
lean_inc(v_numNewEqs_213_);
lean_dec_ref_known(v_t_210_, 2);
v___x_214_ = lean_apply_2(v_k_211_, v_mvarId_212_, v_numNewEqs_213_);
return v___x_214_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResultCore_ctorElim(lean_object* v_motive_215_, lean_object* v_ctorIdx_216_, lean_object* v_t_217_, lean_object* v_h_218_, lean_object* v_k_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Lean_Meta_InjectionResultCore_ctorElim___redArg(v_t_217_, v_k_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResultCore_ctorElim___boxed(lean_object* v_motive_221_, lean_object* v_ctorIdx_222_, lean_object* v_t_223_, lean_object* v_h_224_, lean_object* v_k_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lean_Meta_InjectionResultCore_ctorElim(v_motive_221_, v_ctorIdx_222_, v_t_223_, v_h_224_, v_k_225_);
lean_dec(v_ctorIdx_222_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResultCore_solved_elim___redArg(lean_object* v_t_227_, lean_object* v_solved_228_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l_Lean_Meta_InjectionResultCore_ctorElim___redArg(v_t_227_, v_solved_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResultCore_solved_elim(lean_object* v_motive_230_, lean_object* v_t_231_, lean_object* v_h_232_, lean_object* v_solved_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Lean_Meta_InjectionResultCore_ctorElim___redArg(v_t_231_, v_solved_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResultCore_subgoal_elim___redArg(lean_object* v_t_235_, lean_object* v_subgoal_236_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_Meta_InjectionResultCore_ctorElim___redArg(v_t_235_, v_subgoal_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResultCore_subgoal_elim(lean_object* v_motive_238_, lean_object* v_t_239_, lean_object* v_h_240_, lean_object* v_subgoal_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Lean_Meta_InjectionResultCore_ctorElim___redArg(v_t_239_, v_subgoal_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg(lean_object* v_mvarId_243_, lean_object* v_x_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_243_, v_x_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_);
if (lean_obj_tag(v___x_250_) == 0)
{
lean_object* v_a_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_258_; 
v_a_251_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_258_ == 0)
{
v___x_253_ = v___x_250_;
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_a_251_);
lean_dec(v___x_250_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_256_; 
if (v_isShared_254_ == 0)
{
v___x_256_ = v___x_253_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_a_251_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
else
{
lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_266_; 
v_a_259_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_266_ == 0)
{
v___x_261_ = v___x_250_;
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___x_250_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_262_ == 0)
{
v___x_264_ = v___x_261_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_a_259_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg___boxed(lean_object* v_mvarId_267_, lean_object* v_x_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg(v_mvarId_267_, v_x_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
lean_dec(v___y_270_);
lean_dec_ref(v___y_269_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2(lean_object* v_00_u03b1_275_, lean_object* v_mvarId_276_, lean_object* v_x_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg(v_mvarId_276_, v_x_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___boxed(lean_object* v_00_u03b1_284_, lean_object* v_mvarId_285_, lean_object* v_x_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2(v_00_u03b1_284_, v_mvarId_285_, v_x_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___lam__0(lean_object* v___x_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v_options_302_; uint8_t v_hasTrace_303_; 
v_options_302_ = lean_ctor_get(v___y_299_, 2);
v_hasTrace_303_ = lean_ctor_get_uint8(v_options_302_, sizeof(void*)*1);
if (v_hasTrace_303_ == 0)
{
lean_object* v___x_304_; lean_object* v___x_305_; 
lean_dec(v___x_296_);
v___x_304_ = lean_box(v_hasTrace_303_);
v___x_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
return v___x_305_;
}
else
{
lean_object* v_inheritedTraceOptions_306_; lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v_inheritedTraceOptions_306_ = lean_ctor_get(v___y_299_, 13);
v___x_307_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__0___closed__1));
v___x_308_ = l_Lean_Name_append(v___x_307_, v___x_296_);
v___x_309_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_306_, v_options_302_, v___x_308_);
lean_dec(v___x_308_);
v___x_310_ = lean_box(v___x_309_);
v___x_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
return v___x_311_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___lam__0___boxed(lean_object* v___x_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lean_Meta_injectionCore___lam__0(v___x_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1_spec__2(lean_object* v_msgData_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
lean_object* v___x_325_; lean_object* v_env_326_; lean_object* v___x_327_; lean_object* v_mctx_328_; lean_object* v_lctx_329_; lean_object* v_options_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_325_ = lean_st_ref_get(v___y_323_);
v_env_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc_ref(v_env_326_);
lean_dec(v___x_325_);
v___x_327_ = lean_st_ref_get(v___y_321_);
v_mctx_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc_ref(v_mctx_328_);
lean_dec(v___x_327_);
v_lctx_329_ = lean_ctor_get(v___y_320_, 2);
v_options_330_ = lean_ctor_get(v___y_322_, 2);
lean_inc_ref(v_options_330_);
lean_inc_ref(v_lctx_329_);
v___x_331_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_331_, 0, v_env_326_);
lean_ctor_set(v___x_331_, 1, v_mctx_328_);
lean_ctor_set(v___x_331_, 2, v_lctx_329_);
lean_ctor_set(v___x_331_, 3, v_options_330_);
v___x_332_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
lean_ctor_set(v___x_332_, 1, v_msgData_319_);
v___x_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1_spec__2___boxed(lean_object* v_msgData_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1_spec__2(v_msgData_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
return v_res_340_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__0(void){
_start:
{
lean_object* v___x_341_; double v___x_342_; 
v___x_341_ = lean_unsigned_to_nat(0u);
v___x_342_ = lean_float_of_nat(v___x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(lean_object* v_cls_346_, lean_object* v_msg_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_){
_start:
{
lean_object* v_ref_353_; lean_object* v___x_354_; lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_399_; 
v_ref_353_ = lean_ctor_get(v___y_350_, 5);
v___x_354_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1_spec__2(v_msg_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_);
v_a_355_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_399_ == 0)
{
v___x_357_ = v___x_354_;
v_isShared_358_ = v_isSharedCheck_399_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v___x_354_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_399_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_359_; lean_object* v_traceState_360_; lean_object* v_env_361_; lean_object* v_nextMacroScope_362_; lean_object* v_ngen_363_; lean_object* v_auxDeclNGen_364_; lean_object* v_cache_365_; lean_object* v_messages_366_; lean_object* v_infoState_367_; lean_object* v_snapshotTasks_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_398_; 
v___x_359_ = lean_st_ref_take(v___y_351_);
v_traceState_360_ = lean_ctor_get(v___x_359_, 4);
v_env_361_ = lean_ctor_get(v___x_359_, 0);
v_nextMacroScope_362_ = lean_ctor_get(v___x_359_, 1);
v_ngen_363_ = lean_ctor_get(v___x_359_, 2);
v_auxDeclNGen_364_ = lean_ctor_get(v___x_359_, 3);
v_cache_365_ = lean_ctor_get(v___x_359_, 5);
v_messages_366_ = lean_ctor_get(v___x_359_, 6);
v_infoState_367_ = lean_ctor_get(v___x_359_, 7);
v_snapshotTasks_368_ = lean_ctor_get(v___x_359_, 8);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_398_ == 0)
{
v___x_370_ = v___x_359_;
v_isShared_371_ = v_isSharedCheck_398_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_snapshotTasks_368_);
lean_inc(v_infoState_367_);
lean_inc(v_messages_366_);
lean_inc(v_cache_365_);
lean_inc(v_traceState_360_);
lean_inc(v_auxDeclNGen_364_);
lean_inc(v_ngen_363_);
lean_inc(v_nextMacroScope_362_);
lean_inc(v_env_361_);
lean_dec(v___x_359_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_398_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
uint64_t v_tid_372_; lean_object* v_traces_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_397_; 
v_tid_372_ = lean_ctor_get_uint64(v_traceState_360_, sizeof(void*)*1);
v_traces_373_ = lean_ctor_get(v_traceState_360_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v_traceState_360_);
if (v_isSharedCheck_397_ == 0)
{
v___x_375_ = v_traceState_360_;
v_isShared_376_ = v_isSharedCheck_397_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_traces_373_);
lean_dec(v_traceState_360_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_397_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_377_; double v___x_378_; uint8_t v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_387_; 
v___x_377_ = lean_box(0);
v___x_378_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__0);
v___x_379_ = 0;
v___x_380_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__1));
v___x_381_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_381_, 0, v_cls_346_);
lean_ctor_set(v___x_381_, 1, v___x_377_);
lean_ctor_set(v___x_381_, 2, v___x_380_);
lean_ctor_set_float(v___x_381_, sizeof(void*)*3, v___x_378_);
lean_ctor_set_float(v___x_381_, sizeof(void*)*3 + 8, v___x_378_);
lean_ctor_set_uint8(v___x_381_, sizeof(void*)*3 + 16, v___x_379_);
v___x_382_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__2));
v___x_383_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_383_, 0, v___x_381_);
lean_ctor_set(v___x_383_, 1, v_a_355_);
lean_ctor_set(v___x_383_, 2, v___x_382_);
lean_inc(v_ref_353_);
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v_ref_353_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
v___x_385_ = l_Lean_PersistentArray_push___redArg(v_traces_373_, v___x_384_);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 0, v___x_385_);
v___x_387_ = v___x_375_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_385_);
lean_ctor_set_uint64(v_reuseFailAlloc_396_, sizeof(void*)*1, v_tid_372_);
v___x_387_ = v_reuseFailAlloc_396_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
lean_object* v___x_389_; 
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 4, v___x_387_);
v___x_389_ = v___x_370_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_env_361_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_nextMacroScope_362_);
lean_ctor_set(v_reuseFailAlloc_395_, 2, v_ngen_363_);
lean_ctor_set(v_reuseFailAlloc_395_, 3, v_auxDeclNGen_364_);
lean_ctor_set(v_reuseFailAlloc_395_, 4, v___x_387_);
lean_ctor_set(v_reuseFailAlloc_395_, 5, v_cache_365_);
lean_ctor_set(v_reuseFailAlloc_395_, 6, v_messages_366_);
lean_ctor_set(v_reuseFailAlloc_395_, 7, v_infoState_367_);
lean_ctor_set(v_reuseFailAlloc_395_, 8, v_snapshotTasks_368_);
v___x_389_ = v_reuseFailAlloc_395_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_393_; 
v___x_390_ = lean_st_ref_put(v___y_351_, v___x_389_);
v___x_391_ = lean_box(0);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 0, v___x_391_);
v___x_393_ = v___x_357_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_391_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___boxed(lean_object* v_cls_400_, lean_object* v_msg_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v_cls_400_, v_msg_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(lean_object* v_x_408_, lean_object* v_x_409_, lean_object* v_x_410_, lean_object* v_x_411_){
_start:
{
lean_object* v_ks_412_; lean_object* v_vs_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_437_; 
v_ks_412_ = lean_ctor_get(v_x_408_, 0);
v_vs_413_ = lean_ctor_get(v_x_408_, 1);
v_isSharedCheck_437_ = !lean_is_exclusive(v_x_408_);
if (v_isSharedCheck_437_ == 0)
{
v___x_415_ = v_x_408_;
v_isShared_416_ = v_isSharedCheck_437_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_vs_413_);
lean_inc(v_ks_412_);
lean_dec(v_x_408_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_437_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_417_; uint8_t v___x_418_; 
v___x_417_ = lean_array_get_size(v_ks_412_);
v___x_418_ = lean_nat_dec_lt(v_x_409_, v___x_417_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_422_; 
lean_dec(v_x_409_);
v___x_419_ = lean_array_push(v_ks_412_, v_x_410_);
v___x_420_ = lean_array_push(v_vs_413_, v_x_411_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 1, v___x_420_);
lean_ctor_set(v___x_415_, 0, v___x_419_);
v___x_422_ = v___x_415_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_419_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v___x_420_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
else
{
lean_object* v_k_x27_424_; uint8_t v___x_425_; 
v_k_x27_424_ = lean_array_fget_borrowed(v_ks_412_, v_x_409_);
v___x_425_ = l_Lean_instBEqMVarId_beq(v_x_410_, v_k_x27_424_);
if (v___x_425_ == 0)
{
lean_object* v___x_427_; 
if (v_isShared_416_ == 0)
{
v___x_427_ = v___x_415_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_ks_412_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v_vs_413_);
v___x_427_ = v_reuseFailAlloc_431_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = lean_unsigned_to_nat(1u);
v___x_429_ = lean_nat_add(v_x_409_, v___x_428_);
lean_dec(v_x_409_);
v_x_408_ = v___x_427_;
v_x_409_ = v___x_429_;
goto _start;
}
}
else
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_435_; 
v___x_432_ = lean_array_fset(v_ks_412_, v_x_409_, v_x_410_);
v___x_433_ = lean_array_fset(v_vs_413_, v_x_409_, v_x_411_);
lean_dec(v_x_409_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 1, v___x_433_);
lean_ctor_set(v___x_415_, 0, v___x_432_);
v___x_435_ = v___x_415_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_432_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v___x_433_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_n_438_, lean_object* v_k_439_, lean_object* v_v_440_){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = lean_unsigned_to_nat(0u);
v___x_442_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(v_n_438_, v___x_441_, v_k_439_, v_v_440_);
return v___x_442_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(lean_object* v_x_444_, size_t v_x_445_, size_t v_x_446_, lean_object* v_x_447_, lean_object* v_x_448_){
_start:
{
if (lean_obj_tag(v_x_444_) == 0)
{
lean_object* v_es_449_; size_t v___x_450_; size_t v___x_451_; lean_object* v_j_452_; lean_object* v___x_453_; uint8_t v___x_454_; 
v_es_449_ = lean_ctor_get(v_x_444_, 0);
v___x_450_ = ((size_t)31ULL);
v___x_451_ = lean_usize_land(v_x_445_, v___x_450_);
v_j_452_ = lean_usize_to_nat(v___x_451_);
v___x_453_ = lean_array_get_size(v_es_449_);
v___x_454_ = lean_nat_dec_lt(v_j_452_, v___x_453_);
if (v___x_454_ == 0)
{
lean_dec(v_j_452_);
lean_dec(v_x_448_);
lean_dec(v_x_447_);
return v_x_444_;
}
else
{
lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_493_; 
lean_inc_ref(v_es_449_);
v_isSharedCheck_493_ = !lean_is_exclusive(v_x_444_);
if (v_isSharedCheck_493_ == 0)
{
lean_object* v_unused_494_; 
v_unused_494_ = lean_ctor_get(v_x_444_, 0);
lean_dec(v_unused_494_);
v___x_456_ = v_x_444_;
v_isShared_457_ = v_isSharedCheck_493_;
goto v_resetjp_455_;
}
else
{
lean_dec(v_x_444_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_493_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v_v_458_; lean_object* v___x_459_; lean_object* v_xs_x27_460_; lean_object* v___y_462_; 
v_v_458_ = lean_array_fget(v_es_449_, v_j_452_);
v___x_459_ = lean_box(0);
v_xs_x27_460_ = lean_array_fset(v_es_449_, v_j_452_, v___x_459_);
switch(lean_obj_tag(v_v_458_))
{
case 0:
{
lean_object* v_key_467_; lean_object* v_val_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_478_; 
v_key_467_ = lean_ctor_get(v_v_458_, 0);
v_val_468_ = lean_ctor_get(v_v_458_, 1);
v_isSharedCheck_478_ = !lean_is_exclusive(v_v_458_);
if (v_isSharedCheck_478_ == 0)
{
v___x_470_ = v_v_458_;
v_isShared_471_ = v_isSharedCheck_478_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_val_468_);
lean_inc(v_key_467_);
lean_dec(v_v_458_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_478_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
uint8_t v___x_472_; 
v___x_472_ = l_Lean_instBEqMVarId_beq(v_x_447_, v_key_467_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; lean_object* v___x_474_; 
lean_del_object(v___x_470_);
v___x_473_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_467_, v_val_468_, v_x_447_, v_x_448_);
v___x_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
v___y_462_ = v___x_474_;
goto v___jp_461_;
}
else
{
lean_object* v___x_476_; 
lean_dec(v_val_468_);
lean_dec(v_key_467_);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 1, v_x_448_);
lean_ctor_set(v___x_470_, 0, v_x_447_);
v___x_476_ = v___x_470_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_x_447_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v_x_448_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
v___y_462_ = v___x_476_;
goto v___jp_461_;
}
}
}
}
case 1:
{
lean_object* v_node_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_491_; 
v_node_479_ = lean_ctor_get(v_v_458_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v_v_458_);
if (v_isSharedCheck_491_ == 0)
{
v___x_481_ = v_v_458_;
v_isShared_482_ = v_isSharedCheck_491_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_node_479_);
lean_dec(v_v_458_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_491_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
size_t v___x_483_; size_t v___x_484_; size_t v___x_485_; size_t v___x_486_; lean_object* v___x_487_; lean_object* v___x_489_; 
v___x_483_ = ((size_t)5ULL);
v___x_484_ = lean_usize_shift_right(v_x_445_, v___x_483_);
v___x_485_ = ((size_t)1ULL);
v___x_486_ = lean_usize_add(v_x_446_, v___x_485_);
v___x_487_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(v_node_479_, v___x_484_, v___x_486_, v_x_447_, v_x_448_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v___x_487_);
v___x_489_ = v___x_481_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_487_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
v___y_462_ = v___x_489_;
goto v___jp_461_;
}
}
}
default: 
{
lean_object* v___x_492_; 
v___x_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_492_, 0, v_x_447_);
lean_ctor_set(v___x_492_, 1, v_x_448_);
v___y_462_ = v___x_492_;
goto v___jp_461_;
}
}
v___jp_461_:
{
lean_object* v___x_463_; lean_object* v___x_465_; 
v___x_463_ = lean_array_fset(v_xs_x27_460_, v_j_452_, v___y_462_);
lean_dec(v_j_452_);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 0, v___x_463_);
v___x_465_ = v___x_456_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_463_);
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
}
else
{
lean_object* v_ks_495_; lean_object* v_vs_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_516_; 
v_ks_495_ = lean_ctor_get(v_x_444_, 0);
v_vs_496_ = lean_ctor_get(v_x_444_, 1);
v_isSharedCheck_516_ = !lean_is_exclusive(v_x_444_);
if (v_isSharedCheck_516_ == 0)
{
v___x_498_ = v_x_444_;
v_isShared_499_ = v_isSharedCheck_516_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_vs_496_);
lean_inc(v_ks_495_);
lean_dec(v_x_444_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_516_;
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
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_ks_495_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_vs_496_);
v___x_501_ = v_reuseFailAlloc_515_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
lean_object* v_newNode_502_; uint8_t v___y_504_; size_t v___x_510_; uint8_t v___x_511_; 
v_newNode_502_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5___redArg(v___x_501_, v_x_447_, v_x_448_);
v___x_510_ = ((size_t)7ULL);
v___x_511_ = lean_usize_dec_le(v___x_510_, v_x_446_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_512_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_502_);
v___x_513_ = lean_unsigned_to_nat(4u);
v___x_514_ = lean_nat_dec_lt(v___x_512_, v___x_513_);
lean_dec(v___x_512_);
v___y_504_ = v___x_514_;
goto v___jp_503_;
}
else
{
v___y_504_ = v___x_511_;
goto v___jp_503_;
}
v___jp_503_:
{
if (v___y_504_ == 0)
{
lean_object* v_ks_505_; lean_object* v_vs_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v_ks_505_ = lean_ctor_get(v_newNode_502_, 0);
lean_inc_ref(v_ks_505_);
v_vs_506_ = lean_ctor_get(v_newNode_502_, 1);
lean_inc_ref(v_vs_506_);
lean_dec_ref(v_newNode_502_);
v___x_507_ = lean_unsigned_to_nat(0u);
v___x_508_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_509_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___redArg(v_x_446_, v_ks_505_, v_vs_506_, v___x_507_, v___x_508_);
lean_dec_ref(v_vs_506_);
lean_dec_ref(v_ks_505_);
return v___x_509_;
}
else
{
return v_newNode_502_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___redArg(size_t v_depth_517_, lean_object* v_keys_518_, lean_object* v_vals_519_, lean_object* v_i_520_, lean_object* v_entries_521_){
_start:
{
lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_522_ = lean_array_get_size(v_keys_518_);
v___x_523_ = lean_nat_dec_lt(v_i_520_, v___x_522_);
if (v___x_523_ == 0)
{
lean_dec(v_i_520_);
return v_entries_521_;
}
else
{
lean_object* v_k_524_; lean_object* v_v_525_; uint64_t v___x_526_; size_t v_h_527_; size_t v___x_528_; lean_object* v___x_529_; size_t v___x_530_; size_t v___x_531_; size_t v___x_532_; size_t v_h_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v_k_524_ = lean_array_fget_borrowed(v_keys_518_, v_i_520_);
v_v_525_ = lean_array_fget_borrowed(v_vals_519_, v_i_520_);
v___x_526_ = l_Lean_instHashableMVarId_hash(v_k_524_);
v_h_527_ = lean_uint64_to_usize(v___x_526_);
v___x_528_ = ((size_t)5ULL);
v___x_529_ = lean_unsigned_to_nat(1u);
v___x_530_ = ((size_t)1ULL);
v___x_531_ = lean_usize_sub(v_depth_517_, v___x_530_);
v___x_532_ = lean_usize_mul(v___x_528_, v___x_531_);
v_h_533_ = lean_usize_shift_right(v_h_527_, v___x_532_);
v___x_534_ = lean_nat_add(v_i_520_, v___x_529_);
lean_dec(v_i_520_);
lean_inc(v_v_525_);
lean_inc(v_k_524_);
v___x_535_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(v_entries_521_, v_h_533_, v_depth_517_, v_k_524_, v_v_525_);
v_i_520_ = v___x_534_;
v_entries_521_ = v___x_535_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_depth_537_, lean_object* v_keys_538_, lean_object* v_vals_539_, lean_object* v_i_540_, lean_object* v_entries_541_){
_start:
{
size_t v_depth_boxed_542_; lean_object* v_res_543_; 
v_depth_boxed_542_ = lean_unbox_usize(v_depth_537_);
lean_dec(v_depth_537_);
v_res_543_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___redArg(v_depth_boxed_542_, v_keys_538_, v_vals_539_, v_i_540_, v_entries_541_);
lean_dec_ref(v_vals_539_);
lean_dec_ref(v_keys_538_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_544_, lean_object* v_x_545_, lean_object* v_x_546_, lean_object* v_x_547_, lean_object* v_x_548_){
_start:
{
size_t v_x_16064__boxed_549_; size_t v_x_16065__boxed_550_; lean_object* v_res_551_; 
v_x_16064__boxed_549_ = lean_unbox_usize(v_x_545_);
lean_dec(v_x_545_);
v_x_16065__boxed_550_ = lean_unbox_usize(v_x_546_);
lean_dec(v_x_546_);
v_res_551_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(v_x_544_, v_x_16064__boxed_549_, v_x_16065__boxed_550_, v_x_547_, v_x_548_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0___redArg(lean_object* v_x_552_, lean_object* v_x_553_, lean_object* v_x_554_){
_start:
{
uint64_t v___x_555_; size_t v___x_556_; size_t v___x_557_; lean_object* v___x_558_; 
v___x_555_ = l_Lean_instHashableMVarId_hash(v_x_553_);
v___x_556_ = lean_uint64_to_usize(v___x_555_);
v___x_557_ = ((size_t)1ULL);
v___x_558_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(v_x_552_, v___x_556_, v___x_557_, v_x_553_, v_x_554_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(lean_object* v_mvarId_559_, lean_object* v_val_560_, lean_object* v___y_561_){
_start:
{
lean_object* v___x_563_; lean_object* v_mctx_564_; lean_object* v_cache_565_; lean_object* v_zetaDeltaFVarIds_566_; lean_object* v_postponed_567_; lean_object* v_diag_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_597_; 
v___x_563_ = lean_st_ref_take(v___y_561_);
v_mctx_564_ = lean_ctor_get(v___x_563_, 0);
v_cache_565_ = lean_ctor_get(v___x_563_, 1);
v_zetaDeltaFVarIds_566_ = lean_ctor_get(v___x_563_, 2);
v_postponed_567_ = lean_ctor_get(v___x_563_, 3);
v_diag_568_ = lean_ctor_get(v___x_563_, 4);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_597_ == 0)
{
v___x_570_ = v___x_563_;
v_isShared_571_ = v_isSharedCheck_597_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_diag_568_);
lean_inc(v_postponed_567_);
lean_inc(v_zetaDeltaFVarIds_566_);
lean_inc(v_cache_565_);
lean_inc(v_mctx_564_);
lean_dec(v___x_563_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_597_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v_depth_572_; lean_object* v_levelAssignDepth_573_; lean_object* v_lmvarCounter_574_; lean_object* v_mvarCounter_575_; lean_object* v_lDecls_576_; lean_object* v_decls_577_; lean_object* v_userNames_578_; lean_object* v_lAssignment_579_; lean_object* v_eAssignment_580_; lean_object* v_dAssignment_581_; lean_object* v_instanceTypedMVars_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_596_; 
v_depth_572_ = lean_ctor_get(v_mctx_564_, 0);
v_levelAssignDepth_573_ = lean_ctor_get(v_mctx_564_, 1);
v_lmvarCounter_574_ = lean_ctor_get(v_mctx_564_, 2);
v_mvarCounter_575_ = lean_ctor_get(v_mctx_564_, 3);
v_lDecls_576_ = lean_ctor_get(v_mctx_564_, 4);
v_decls_577_ = lean_ctor_get(v_mctx_564_, 5);
v_userNames_578_ = lean_ctor_get(v_mctx_564_, 6);
v_lAssignment_579_ = lean_ctor_get(v_mctx_564_, 7);
v_eAssignment_580_ = lean_ctor_get(v_mctx_564_, 8);
v_dAssignment_581_ = lean_ctor_get(v_mctx_564_, 9);
v_instanceTypedMVars_582_ = lean_ctor_get(v_mctx_564_, 10);
v_isSharedCheck_596_ = !lean_is_exclusive(v_mctx_564_);
if (v_isSharedCheck_596_ == 0)
{
v___x_584_ = v_mctx_564_;
v_isShared_585_ = v_isSharedCheck_596_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_instanceTypedMVars_582_);
lean_inc(v_dAssignment_581_);
lean_inc(v_eAssignment_580_);
lean_inc(v_lAssignment_579_);
lean_inc(v_userNames_578_);
lean_inc(v_decls_577_);
lean_inc(v_lDecls_576_);
lean_inc(v_mvarCounter_575_);
lean_inc(v_lmvarCounter_574_);
lean_inc(v_levelAssignDepth_573_);
lean_inc(v_depth_572_);
lean_dec(v_mctx_564_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_596_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_586_; lean_object* v___x_588_; 
v___x_586_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0___redArg(v_eAssignment_580_, v_mvarId_559_, v_val_560_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 8, v___x_586_);
v___x_588_ = v___x_584_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_depth_572_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v_levelAssignDepth_573_);
lean_ctor_set(v_reuseFailAlloc_595_, 2, v_lmvarCounter_574_);
lean_ctor_set(v_reuseFailAlloc_595_, 3, v_mvarCounter_575_);
lean_ctor_set(v_reuseFailAlloc_595_, 4, v_lDecls_576_);
lean_ctor_set(v_reuseFailAlloc_595_, 5, v_decls_577_);
lean_ctor_set(v_reuseFailAlloc_595_, 6, v_userNames_578_);
lean_ctor_set(v_reuseFailAlloc_595_, 7, v_lAssignment_579_);
lean_ctor_set(v_reuseFailAlloc_595_, 8, v___x_586_);
lean_ctor_set(v_reuseFailAlloc_595_, 9, v_dAssignment_581_);
lean_ctor_set(v_reuseFailAlloc_595_, 10, v_instanceTypedMVars_582_);
v___x_588_ = v_reuseFailAlloc_595_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
lean_object* v___x_590_; 
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v___x_588_);
v___x_590_ = v___x_570_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_588_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_cache_565_);
lean_ctor_set(v_reuseFailAlloc_594_, 2, v_zetaDeltaFVarIds_566_);
lean_ctor_set(v_reuseFailAlloc_594_, 3, v_postponed_567_);
lean_ctor_set(v_reuseFailAlloc_594_, 4, v_diag_568_);
v___x_590_ = v_reuseFailAlloc_594_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_591_ = lean_st_ref_put(v___y_561_, v___x_590_);
v___x_592_ = lean_box(0);
v___x_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
return v___x_593_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg___boxed(lean_object* v_mvarId_598_, lean_object* v_val_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(v_mvarId_598_, v_val_599_, v___y_600_);
lean_dec(v___y_600_);
return v_res_602_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__2(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__1));
v___x_607_ = l_Lean_MessageData_ofFormat(v___x_606_);
return v___x_607_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__3(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__2, &l_Lean_Meta_injectionCore___lam__1___closed__2_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__2);
v___x_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
return v___x_609_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__6(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__5));
v___x_614_ = l_Lean_MessageData_ofFormat(v___x_613_);
return v___x_614_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__7(void){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__6, &l_Lean_Meta_injectionCore___lam__1___closed__6_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__6);
v___x_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
return v___x_616_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__9(void){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__8));
v___x_619_ = l_Lean_stringToMessageData(v___x_618_);
return v___x_619_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__11(void){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__10));
v___x_622_ = l_Lean_stringToMessageData(v___x_621_);
return v___x_622_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__13(void){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__12));
v___x_625_ = l_Lean_stringToMessageData(v___x_624_);
return v___x_625_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__15(void){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__14));
v___x_628_ = l_Lean_stringToMessageData(v___x_627_);
return v___x_628_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__17(void){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__16));
v___x_631_ = l_Lean_stringToMessageData(v___x_630_);
return v___x_631_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__22(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__21));
v___x_639_ = l_Lean_MessageData_ofFormat(v___x_638_);
return v___x_639_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__23(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__22, &l_Lean_Meta_injectionCore___lam__1___closed__22_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__22);
v___x_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
return v___x_641_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__27(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__26));
v___x_646_ = l_Lean_stringToMessageData(v___x_645_);
return v___x_646_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__29(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__28));
v___x_649_ = l_Lean_stringToMessageData(v___x_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___lam__1(lean_object* v_mvarId_653_, lean_object* v___x_654_, lean_object* v_fvarId_655_, lean_object* v___x_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v_type_900_; lean_object* v_prf_901_; lean_object* v___y_902_; lean_object* v___y_903_; lean_object* v___y_904_; lean_object* v___y_905_; lean_object* v___x_985_; 
lean_inc(v___x_654_);
lean_inc(v_mvarId_653_);
v___x_985_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_653_, v___x_654_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v___x_986_; 
lean_dec_ref_known(v___x_985_, 1);
lean_inc(v_fvarId_655_);
v___x_986_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_655_, v___y_657_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v_a_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_a_987_);
lean_dec_ref_known(v___x_986_, 1);
v___x_988_ = l_Lean_LocalDecl_type(v_a_987_);
lean_dec(v_a_987_);
lean_inc(v___y_660_);
lean_inc_ref(v___y_659_);
lean_inc(v___y_658_);
lean_inc_ref(v___y_657_);
v___x_989_ = lean_whnf(v___x_988_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; uint8_t v___x_994_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_a_990_);
lean_dec_ref_known(v___x_989_, 1);
lean_inc(v_fvarId_655_);
v___x_991_ = l_Lean_mkFVar(v_fvarId_655_);
v___x_992_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__31));
v___x_993_ = lean_unsigned_to_nat(4u);
v___x_994_ = l_Lean_Expr_isAppOfArity(v_a_990_, v___x_992_, v___x_993_);
if (v___x_994_ == 0)
{
v_type_900_ = v_a_990_;
v_prf_901_ = v___x_991_;
v___y_902_ = v___y_657_;
v___y_903_ = v___y_658_;
v___y_904_ = v___y_659_;
v___y_905_ = v___y_660_;
goto v___jp_899_;
}
else
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_995_ = l_Lean_Expr_appFn_x21(v_a_990_);
v___x_996_ = l_Lean_Expr_appFn_x21(v___x_995_);
v___x_997_ = l_Lean_Expr_appFn_x21(v___x_996_);
v___x_998_ = l_Lean_Expr_appArg_x21(v___x_997_);
lean_dec_ref(v___x_997_);
v___x_999_ = l_Lean_Expr_appArg_x21(v___x_995_);
lean_dec_ref(v___x_995_);
v___x_1000_ = l_Lean_Meta_isExprDefEq(v___x_998_, v___x_999_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; uint8_t v___x_1002_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_1000_, 1);
v___x_1002_ = lean_unbox(v_a_1001_);
lean_dec(v_a_1001_);
if (v___x_1002_ == 0)
{
lean_dec_ref(v___x_996_);
v_type_900_ = v_a_990_;
v_prf_901_ = v___x_991_;
v___y_902_ = v___y_657_;
v___y_903_ = v___y_658_;
v___y_904_ = v___y_659_;
v___y_905_ = v___y_660_;
goto v___jp_899_;
}
else
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1003_ = l_Lean_Expr_appArg_x21(v___x_996_);
lean_dec_ref(v___x_996_);
v___x_1004_ = l_Lean_Expr_appArg_x21(v_a_990_);
lean_dec(v_a_990_);
v___x_1005_ = l_Lean_Meta_mkEq(v___x_1003_, v___x_1004_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1007_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_a_1006_);
lean_dec_ref_known(v___x_1005_, 1);
v___x_1007_ = l_Lean_Meta_mkEqOfHEq(v___x_991_, v___x_994_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_a_1008_);
lean_dec_ref_known(v___x_1007_, 1);
v_type_900_ = v_a_1006_;
v_prf_901_ = v_a_1008_;
v___y_902_ = v___y_657_;
v___y_903_ = v___y_658_;
v___y_904_ = v___y_659_;
v___y_905_ = v___y_660_;
goto v___jp_899_;
}
else
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
lean_dec(v_a_1006_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec_ref(v___x_656_);
lean_dec(v_fvarId_655_);
lean_dec(v___x_654_);
lean_dec(v_mvarId_653_);
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
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
lean_dec_ref(v___x_991_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec_ref(v___x_656_);
lean_dec(v_fvarId_655_);
lean_dec(v___x_654_);
lean_dec(v_mvarId_653_);
v_a_1017_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_1005_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_1005_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1017_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
}
else
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1032_; 
lean_dec_ref(v___x_996_);
lean_dec_ref(v___x_991_);
lean_dec(v_a_990_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec_ref(v___x_656_);
lean_dec(v_fvarId_655_);
lean_dec(v___x_654_);
lean_dec(v_mvarId_653_);
v_a_1025_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1027_ = v___x_1000_;
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1000_);
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
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1040_; 
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec_ref(v___x_656_);
lean_dec(v_fvarId_655_);
lean_dec(v___x_654_);
lean_dec(v_mvarId_653_);
v_a_1033_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1035_ = v___x_989_;
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_989_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1038_; 
if (v_isShared_1036_ == 0)
{
v___x_1038_ = v___x_1035_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1033_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
else
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1048_; 
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec_ref(v___x_656_);
lean_dec(v_fvarId_655_);
lean_dec(v___x_654_);
lean_dec(v_mvarId_653_);
v_a_1041_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1043_ = v___x_986_;
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_986_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1041_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
else
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1056_; 
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec_ref(v___x_656_);
lean_dec(v_fvarId_655_);
lean_dec(v___x_654_);
lean_dec(v_mvarId_653_);
v_a_1049_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1051_ = v___x_985_;
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_985_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1052_ == 0)
{
v___x_1054_ = v___x_1051_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1049_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
v___jp_662_:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__3, &l_Lean_Meta_injectionCore___lam__1___closed__3_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__3);
v___x_668_ = l_Lean_Meta_throwTacticEx___redArg(v___x_654_, v_mvarId_653_, v___x_667_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
return v___x_668_;
}
v___jp_669_:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__7, &l_Lean_Meta_injectionCore___lam__1___closed__7_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__7);
v___x_675_ = l_Lean_Meta_throwTacticEx___redArg(v___x_654_, v_mvarId_653_, v___x_674_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
return v___x_675_;
}
v___jp_676_:
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_679_, 0, v___y_678_);
lean_ctor_set(v___x_679_, 1, v___y_677_);
v___x_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
return v___x_680_;
}
v___jp_681_:
{
lean_object* v_toConstantVal_691_; lean_object* v_toConstantVal_692_; lean_object* v_numFields_693_; lean_object* v_name_694_; lean_object* v_name_695_; uint8_t v___x_696_; 
v_toConstantVal_691_ = lean_ctor_get(v___y_683_, 0);
v_toConstantVal_692_ = lean_ctor_get(v___y_685_, 0);
lean_inc_ref(v_toConstantVal_692_);
lean_dec_ref(v___y_685_);
v_numFields_693_ = lean_ctor_get(v___y_683_, 4);
lean_inc(v_numFields_693_);
v_name_694_ = lean_ctor_get(v_toConstantVal_691_, 0);
v_name_695_ = lean_ctor_get(v_toConstantVal_692_, 0);
lean_inc(v_name_695_);
lean_dec_ref(v_toConstantVal_692_);
v___x_696_ = lean_name_eq(v_name_694_, v_name_695_);
lean_dec(v_name_695_);
if (v___x_696_ == 0)
{
lean_object* v___x_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_705_; 
lean_dec(v_numFields_693_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec_ref(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec(v_fvarId_655_);
lean_dec(v___x_654_);
v___x_697_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(v_mvarId_653_, v___y_684_, v___y_688_);
lean_dec(v___y_688_);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_705_ == 0)
{
lean_object* v_unused_706_; 
v_unused_706_ = lean_ctor_get(v___x_697_, 0);
lean_dec(v_unused_706_);
v___x_699_ = v___x_697_;
v_isShared_700_ = v_isSharedCheck_705_;
goto v_resetjp_698_;
}
else
{
lean_dec(v___x_697_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_705_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_701_; lean_object* v___x_703_; 
v___x_701_ = lean_box(0);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 0, v___x_701_);
v___x_703_ = v___x_699_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_701_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
else
{
lean_object* v___x_707_; 
lean_inc(v___y_690_);
lean_inc_ref(v___y_689_);
lean_inc(v___y_688_);
lean_inc_ref(v___y_687_);
lean_inc_ref(v___y_684_);
v___x_707_ = lean_infer_type(v___y_684_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_708_; lean_object* v___x_709_; 
v_a_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_a_708_);
lean_dec_ref_known(v___x_707_, 1);
v___x_709_ = l_Lean_Meta_whnfD(v_a_708_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_710_);
lean_dec_ref_known(v___x_709_, 1);
if (lean_obj_tag(v_a_710_) == 7)
{
lean_object* v_binderType_711_; lean_object* v___x_712_; 
lean_dec_ref(v___y_686_);
lean_dec(v___x_654_);
v_binderType_711_ = lean_ctor_get(v_a_710_, 1);
lean_inc_ref(v_binderType_711_);
lean_dec_ref_known(v_a_710_, 3);
lean_inc(v_mvarId_653_);
v___x_712_ = l_Lean_MVarId_getTag(v_mvarId_653_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v_a_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v_a_713_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_a_713_);
lean_dec_ref_known(v___x_712_, 1);
v___x_714_ = l_Lean_Expr_headBeta(v_binderType_711_);
v___x_715_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_714_, v_a_713_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_a_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_770_; 
v_a_716_ = lean_ctor_get(v___x_715_, 0);
lean_inc_n(v_a_716_, 2);
lean_dec_ref_known(v___x_715_, 1);
v___x_717_ = l_Lean_Expr_app___override(v___y_684_, v_a_716_);
v___x_718_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(v_mvarId_653_, v___x_717_, v___y_688_);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_770_ == 0)
{
lean_object* v_unused_771_; 
v_unused_771_ = lean_ctor_get(v___x_718_, 0);
lean_dec(v_unused_771_);
v___x_720_ = v___x_718_;
v_isShared_721_ = v_isSharedCheck_770_;
goto v_resetjp_719_;
}
else
{
lean_dec(v___x_718_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_770_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_722_ = l_Lean_Expr_mvarId_x21(v_a_716_);
lean_dec(v_a_716_);
v___x_723_ = l_Lean_MVarId_tryClear(v___x_722_, v_fvarId_655_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; lean_object* v___x_725_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_a_724_);
lean_dec_ref_known(v___x_723_, 1);
v___x_725_ = l_Lean_Meta_getCtorNumPropFields(v___y_683_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_options_726_; lean_object* v_a_727_; lean_object* v_inheritedTraceOptions_728_; uint8_t v_hasTrace_729_; lean_object* v___x_730_; 
v_options_726_ = lean_ctor_get(v___y_689_, 2);
v_a_727_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_a_727_);
lean_dec_ref_known(v___x_725_, 1);
v_inheritedTraceOptions_728_ = lean_ctor_get(v___y_689_, 13);
v_hasTrace_729_ = lean_ctor_get_uint8(v_options_726_, sizeof(void*)*1);
v___x_730_ = lean_nat_sub(v_numFields_693_, v_a_727_);
lean_dec(v_a_727_);
lean_dec(v_numFields_693_);
if (v_hasTrace_729_ == 0)
{
lean_del_object(v___x_720_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_682_);
v___y_677_ = v___x_730_;
v___y_678_ = v_a_724_;
goto v___jp_676_;
}
else
{
lean_object* v___x_731_; lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_731_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__0___closed__1));
lean_inc(v___y_682_);
v___x_732_ = l_Lean_Name_append(v___x_731_, v___y_682_);
v___x_733_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_728_, v_options_726_, v___x_732_);
lean_dec(v___x_732_);
if (v___x_733_ == 0)
{
lean_del_object(v___x_720_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_682_);
v___y_677_ = v___x_730_;
v___y_678_ = v_a_724_;
goto v___jp_676_;
}
else
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_737_; 
v___x_734_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__9, &l_Lean_Meta_injectionCore___lam__1___closed__9_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__9);
lean_inc(v___x_730_);
v___x_735_ = l_Nat_reprFast(v___x_730_);
if (v_isShared_721_ == 0)
{
lean_ctor_set_tag(v___x_720_, 3);
lean_ctor_set(v___x_720_, 0, v___x_735_);
v___x_737_ = v___x_720_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_735_);
v___x_737_ = v_reuseFailAlloc_753_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_738_ = l_Lean_MessageData_ofFormat(v___x_737_);
v___x_739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_734_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
v___x_740_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__11, &l_Lean_Meta_injectionCore___lam__1___closed__11_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__11);
v___x_741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_739_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
lean_inc(v_a_724_);
v___x_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_742_, 0, v_a_724_);
v___x_743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_741_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
v___x_744_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v___y_682_, v___x_743_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_dec_ref_known(v___x_744_, 1);
v___y_677_ = v___x_730_;
v___y_678_ = v_a_724_;
goto v___jp_676_;
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_dec(v___x_730_);
lean_dec(v_a_724_);
v_a_745_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_744_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_744_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
lean_dec(v_a_724_);
lean_del_object(v___x_720_);
lean_dec(v_numFields_693_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_682_);
v_a_754_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_725_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_725_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
else
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
lean_del_object(v___x_720_);
lean_dec(v_numFields_693_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
v_a_762_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_723_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_723_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_762_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
}
else
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
lean_dec(v_numFields_693_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec_ref(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec(v_fvarId_655_);
lean_dec(v_mvarId_653_);
v_a_772_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_779_ == 0)
{
v___x_774_ = v___x_715_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_715_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_772_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
else
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_787_; 
lean_dec_ref(v_binderType_711_);
lean_dec(v_numFields_693_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec_ref(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec(v_fvarId_655_);
lean_dec(v_mvarId_653_);
v_a_780_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_787_ == 0)
{
v___x_782_ = v___x_712_;
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_712_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_a_780_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
else
{
lean_object* v___x_788_; 
lean_dec(v_numFields_693_);
lean_dec_ref(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v_fvarId_655_);
lean_inc(v___y_690_);
lean_inc_ref(v___y_689_);
lean_inc(v___y_688_);
lean_inc_ref(v___y_687_);
v___x_788_ = lean_apply_5(v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, lean_box(0));
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; uint8_t v___x_790_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_a_789_);
lean_dec_ref_known(v___x_788_, 1);
v___x_790_ = lean_unbox(v_a_789_);
lean_dec(v_a_789_);
if (v___x_790_ == 0)
{
lean_dec(v_a_710_);
lean_dec(v___y_682_);
v___y_663_ = v___y_687_;
v___y_664_ = v___y_688_;
v___y_665_ = v___y_689_;
v___y_666_ = v___y_690_;
goto v___jp_662_;
}
else
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_791_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__13, &l_Lean_Meta_injectionCore___lam__1___closed__13_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__13);
v___x_792_ = l_Lean_indentExpr(v_a_710_);
v___x_793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_791_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
v___x_794_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v___y_682_, v___x_793_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_dec_ref_known(v___x_794_, 1);
v___y_663_ = v___y_687_;
v___y_664_ = v___y_688_;
v___y_665_ = v___y_689_;
v___y_666_ = v___y_690_;
goto v___jp_662_;
}
else
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___x_654_);
lean_dec(v_mvarId_653_);
v_a_795_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_794_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_794_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_795_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
}
else
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_810_; 
lean_dec(v_a_710_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_682_);
lean_dec(v___x_654_);
lean_dec(v_mvarId_653_);
v_a_803_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_810_ == 0)
{
v___x_805_ = v___x_788_;
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_788_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_808_; 
if (v_isShared_806_ == 0)
{
v___x_808_ = v___x_805_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_a_803_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
}
else
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_818_; 
lean_dec(v_numFields_693_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec_ref(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec(v_fvarId_655_);
lean_dec(v___x_654_);
lean_dec(v_mvarId_653_);
v_a_811_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_818_ == 0)
{
v___x_813_ = v___x_709_;
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_709_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_a_811_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
lean_dec(v_numFields_693_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec_ref(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec(v_fvarId_655_);
lean_dec(v___x_654_);
lean_dec(v_mvarId_653_);
v_a_819_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_707_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_707_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
}
v___jp_827_:
{
lean_object* v_keyedConfig_838_; uint8_t v_trackZetaDelta_839_; lean_object* v_zetaDeltaSet_840_; lean_object* v_lctx_841_; lean_object* v_localInstances_842_; lean_object* v_defEqCtx_x3f_843_; lean_object* v_synthPendingDepth_844_; lean_object* v_customCanUnfoldPredicate_x3f_845_; uint8_t v_univApprox_846_; uint8_t v_inTypeClassResolution_847_; uint8_t v_cacheInferType_848_; uint8_t v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v_keyedConfig_838_ = lean_ctor_get(v___y_834_, 0);
v_trackZetaDelta_839_ = lean_ctor_get_uint8(v___y_834_, sizeof(void*)*7);
v_zetaDeltaSet_840_ = lean_ctor_get(v___y_834_, 1);
v_lctx_841_ = lean_ctor_get(v___y_834_, 2);
v_localInstances_842_ = lean_ctor_get(v___y_834_, 3);
v_defEqCtx_x3f_843_ = lean_ctor_get(v___y_834_, 4);
v_synthPendingDepth_844_ = lean_ctor_get(v___y_834_, 5);
v_customCanUnfoldPredicate_x3f_845_ = lean_ctor_get(v___y_834_, 6);
v_univApprox_846_ = lean_ctor_get_uint8(v___y_834_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_847_ = lean_ctor_get_uint8(v___y_834_, sizeof(void*)*7 + 2);
v_cacheInferType_848_ = lean_ctor_get_uint8(v___y_834_, sizeof(void*)*7 + 3);
v___x_849_ = 1;
lean_inc_ref(v_keyedConfig_838_);
v___x_850_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_849_, v_keyedConfig_838_);
lean_inc(v_customCanUnfoldPredicate_x3f_845_);
lean_inc(v_synthPendingDepth_844_);
lean_inc(v_defEqCtx_x3f_843_);
lean_inc_ref(v_localInstances_842_);
lean_inc_ref(v_lctx_841_);
lean_inc(v_zetaDeltaSet_840_);
v___x_851_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_851_, 0, v___x_850_);
lean_ctor_set(v___x_851_, 1, v_zetaDeltaSet_840_);
lean_ctor_set(v___x_851_, 2, v_lctx_841_);
lean_ctor_set(v___x_851_, 3, v_localInstances_842_);
lean_ctor_set(v___x_851_, 4, v_defEqCtx_x3f_843_);
lean_ctor_set(v___x_851_, 5, v_synthPendingDepth_844_);
lean_ctor_set(v___x_851_, 6, v_customCanUnfoldPredicate_x3f_845_);
lean_ctor_set_uint8(v___x_851_, sizeof(void*)*7, v_trackZetaDelta_839_);
lean_ctor_set_uint8(v___x_851_, sizeof(void*)*7 + 1, v_univApprox_846_);
lean_ctor_set_uint8(v___x_851_, sizeof(void*)*7 + 2, v_inTypeClassResolution_847_);
lean_ctor_set_uint8(v___x_851_, sizeof(void*)*7 + 3, v_cacheInferType_848_);
v___x_852_ = l_Lean_Meta_mkNoConfusion(v___y_833_, v___y_832_, v___x_851_, v___y_835_, v___y_836_, v___y_837_);
lean_dec_ref_known(v___x_851_, 7);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v___x_854_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_a_853_);
lean_dec_ref_known(v___x_852_, 1);
lean_inc_ref(v___y_831_);
lean_inc(v___y_837_);
lean_inc_ref(v___y_836_);
lean_inc(v___y_835_);
lean_inc_ref(v___y_834_);
v___x_854_ = lean_apply_5(v___y_831_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, lean_box(0));
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; uint8_t v___x_856_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_855_);
lean_dec_ref_known(v___x_854_, 1);
v___x_856_ = lean_unbox(v_a_855_);
lean_dec(v_a_855_);
if (v___x_856_ == 0)
{
v___y_682_ = v___y_829_;
v___y_683_ = v___y_828_;
v___y_684_ = v_a_853_;
v___y_685_ = v___y_830_;
v___y_686_ = v___y_831_;
v___y_687_ = v___y_834_;
v___y_688_ = v___y_835_;
v___y_689_ = v___y_836_;
v___y_690_ = v___y_837_;
goto v___jp_681_;
}
else
{
lean_object* v___x_857_; 
lean_inc(v___y_837_);
lean_inc_ref(v___y_836_);
lean_inc(v___y_835_);
lean_inc_ref(v___y_834_);
lean_inc(v_a_853_);
v___x_857_ = lean_infer_type(v_a_853_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_a_858_);
lean_dec_ref_known(v___x_857_, 1);
v___x_859_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__15, &l_Lean_Meta_injectionCore___lam__1___closed__15_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__15);
lean_inc(v_a_853_);
v___x_860_ = l_Lean_indentExpr(v_a_853_);
v___x_861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_859_);
lean_ctor_set(v___x_861_, 1, v___x_860_);
v___x_862_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__17, &l_Lean_Meta_injectionCore___lam__1___closed__17_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__17);
v___x_863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_861_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
v___x_864_ = l_Lean_indentExpr(v_a_858_);
v___x_865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_863_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
lean_inc(v___y_829_);
v___x_866_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v___y_829_, v___x_865_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_dec_ref_known(v___x_866_, 1);
v___y_682_ = v___y_829_;
v___y_683_ = v___y_828_;
v___y_684_ = v_a_853_;
v___y_685_ = v___y_830_;
v___y_686_ = v___y_831_;
v___y_687_ = v___y_834_;
v___y_688_ = v___y_835_;
v___y_689_ = v___y_836_;
v___y_690_ = v___y_837_;
goto v___jp_681_;
}
else
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_874_; 
lean_dec(v_a_853_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec_ref(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec(v_fvarId_655_);
lean_dec(v___x_654_);
lean_dec(v_mvarId_653_);
v_a_867_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_874_ == 0)
{
v___x_869_ = v___x_866_;
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_866_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_872_; 
if (v_isShared_870_ == 0)
{
v___x_872_ = v___x_869_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_867_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
else
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
lean_dec(v_a_853_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec_ref(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec(v_fvarId_655_);
lean_dec(v___x_654_);
lean_dec(v_mvarId_653_);
v_a_875_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_857_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_857_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
}
else
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
lean_dec(v_a_853_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec_ref(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec(v_fvarId_655_);
lean_dec(v___x_654_);
lean_dec(v_mvarId_653_);
v_a_883_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_890_ == 0)
{
v___x_885_ = v___x_854_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_854_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_883_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
else
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_898_; 
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec_ref(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec(v_fvarId_655_);
lean_dec(v___x_654_);
lean_dec(v_mvarId_653_);
v_a_891_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_898_ == 0)
{
v___x_893_ = v___x_852_;
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_852_);
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
v___jp_899_:
{
lean_object* v___x_906_; lean_object* v___x_907_; uint8_t v___x_908_; 
v___x_906_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__19));
v___x_907_ = lean_unsigned_to_nat(3u);
v___x_908_ = l_Lean_Expr_isAppOfArity(v_type_900_, v___x_906_, v___x_907_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; lean_object* v___x_910_; 
lean_dec_ref(v_prf_901_);
lean_dec_ref(v_type_900_);
lean_dec_ref(v___x_656_);
lean_dec(v_fvarId_655_);
v___x_909_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__23, &l_Lean_Meta_injectionCore___lam__1___closed__23_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__23);
v___x_910_ = l_Lean_Meta_throwTacticEx___redArg(v___x_654_, v_mvarId_653_, v___x_909_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
return v___x_910_;
}
else
{
lean_object* v___x_911_; 
lean_inc(v_mvarId_653_);
v___x_911_ = l_Lean_MVarId_getType(v_mvarId_653_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc(v_a_912_);
lean_dec_ref_known(v___x_911_, 1);
v___x_913_ = l_Lean_Expr_appFn_x21(v_type_900_);
v___x_914_ = l_Lean_Expr_appArg_x21(v___x_913_);
lean_dec_ref(v___x_913_);
v___x_915_ = l_Lean_Meta_isConstructorApp_x27_x3f(v___x_914_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_a_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v_a_916_ = lean_ctor_get(v___x_915_, 0);
lean_inc(v_a_916_);
lean_dec_ref_known(v___x_915_, 1);
v___x_917_ = l_Lean_Expr_appArg_x21(v_type_900_);
lean_dec_ref(v_type_900_);
v___x_918_ = l_Lean_Meta_isConstructorApp_x27_x3f(v___x_917_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
if (lean_obj_tag(v___x_918_) == 0)
{
if (lean_obj_tag(v_a_916_) == 1)
{
lean_object* v_a_919_; 
v_a_919_ = lean_ctor_get(v___x_918_, 0);
lean_inc(v_a_919_);
lean_dec_ref_known(v___x_918_, 1);
if (lean_obj_tag(v_a_919_) == 1)
{
lean_object* v_val_920_; lean_object* v_val_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___f_925_; lean_object* v___x_926_; lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_960_; 
v_val_920_ = lean_ctor_get(v_a_916_, 0);
lean_inc(v_val_920_);
lean_dec_ref_known(v_a_916_, 1);
v_val_921_ = lean_ctor_get(v_a_919_, 0);
lean_inc(v_val_921_);
lean_dec_ref_known(v_a_919_, 1);
v___x_922_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__24));
v___x_923_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__25));
v___x_924_ = l_Lean_Name_mkStr3(v___x_922_, v___x_923_, v___x_656_);
lean_inc_n(v___x_924_, 2);
v___f_925_ = lean_alloc_closure((void*)(l_Lean_Meta_injectionCore___lam__0___boxed), 6, 1);
lean_closure_set(v___f_925_, 0, v___x_924_);
v___x_926_ = l_Lean_Meta_injectionCore___lam__0(v___x_924_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
v_a_927_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_960_ == 0)
{
v___x_929_ = v___x_926_;
v_isShared_930_ = v_isSharedCheck_960_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_926_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_960_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
uint8_t v___x_931_; 
v___x_931_ = lean_unbox(v_a_927_);
lean_dec(v_a_927_);
if (v___x_931_ == 0)
{
lean_del_object(v___x_929_);
v___y_828_ = v_val_920_;
v___y_829_ = v___x_924_;
v___y_830_ = v_val_921_;
v___y_831_ = v___f_925_;
v___y_832_ = v_prf_901_;
v___y_833_ = v_a_912_;
v___y_834_ = v___y_902_;
v___y_835_ = v___y_903_;
v___y_836_ = v___y_904_;
v___y_837_ = v___y_905_;
goto v___jp_827_;
}
else
{
lean_object* v___x_932_; 
lean_inc(v___y_905_);
lean_inc_ref(v___y_904_);
lean_inc(v___y_903_);
lean_inc_ref(v___y_902_);
lean_inc_ref(v_prf_901_);
v___x_932_ = lean_infer_type(v_prf_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_a_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_940_; 
v_a_933_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_a_933_);
lean_dec_ref_known(v___x_932_, 1);
v___x_934_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__27, &l_Lean_Meta_injectionCore___lam__1___closed__27_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__27);
v___x_935_ = l_Lean_MessageData_ofExpr(v_a_933_);
v___x_936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_934_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v___x_937_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__29, &l_Lean_Meta_injectionCore___lam__1___closed__29_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__29);
v___x_938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_936_);
lean_ctor_set(v___x_938_, 1, v___x_937_);
lean_inc(v_mvarId_653_);
if (v_isShared_930_ == 0)
{
lean_ctor_set_tag(v___x_929_, 1);
lean_ctor_set(v___x_929_, 0, v_mvarId_653_);
v___x_940_ = v___x_929_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_mvarId_653_);
v___x_940_ = v_reuseFailAlloc_951_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_938_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
lean_inc(v___x_924_);
v___x_942_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v___x_924_, v___x_941_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_dec_ref_known(v___x_942_, 1);
v___y_828_ = v_val_920_;
v___y_829_ = v___x_924_;
v___y_830_ = v_val_921_;
v___y_831_ = v___f_925_;
v___y_832_ = v_prf_901_;
v___y_833_ = v_a_912_;
v___y_834_ = v___y_902_;
v___y_835_ = v___y_903_;
v___y_836_ = v___y_904_;
v___y_837_ = v___y_905_;
goto v___jp_827_;
}
else
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_950_; 
lean_dec_ref(v___f_925_);
lean_dec(v___x_924_);
lean_dec(v_val_921_);
lean_dec(v_val_920_);
lean_dec(v_a_912_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec_ref(v_prf_901_);
lean_dec(v_fvarId_655_);
lean_dec(v___x_654_);
lean_dec(v_mvarId_653_);
v_a_943_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_950_ == 0)
{
v___x_945_ = v___x_942_;
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_942_);
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
}
else
{
lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
lean_del_object(v___x_929_);
lean_dec_ref(v___f_925_);
lean_dec(v___x_924_);
lean_dec(v_val_921_);
lean_dec(v_val_920_);
lean_dec(v_a_912_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec_ref(v_prf_901_);
lean_dec(v_fvarId_655_);
lean_dec(v___x_654_);
lean_dec(v_mvarId_653_);
v_a_952_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_959_ == 0)
{
v___x_954_ = v___x_932_;
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_dec(v___x_932_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_952_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_a_916_, 1);
lean_dec(v_a_919_);
lean_dec(v_a_912_);
lean_dec_ref(v_prf_901_);
lean_dec_ref(v___x_656_);
lean_dec(v_fvarId_655_);
v___y_670_ = v___y_902_;
v___y_671_ = v___y_903_;
v___y_672_ = v___y_904_;
v___y_673_ = v___y_905_;
goto v___jp_669_;
}
}
else
{
lean_dec_ref_known(v___x_918_, 1);
lean_dec(v_a_916_);
lean_dec(v_a_912_);
lean_dec_ref(v_prf_901_);
lean_dec_ref(v___x_656_);
lean_dec(v_fvarId_655_);
v___y_670_ = v___y_902_;
v___y_671_ = v___y_903_;
v___y_672_ = v___y_904_;
v___y_673_ = v___y_905_;
goto v___jp_669_;
}
}
else
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_968_; 
lean_dec(v_a_916_);
lean_dec(v_a_912_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec_ref(v_prf_901_);
lean_dec_ref(v___x_656_);
lean_dec(v_fvarId_655_);
lean_dec(v___x_654_);
lean_dec(v_mvarId_653_);
v_a_961_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_968_ == 0)
{
v___x_963_ = v___x_918_;
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_918_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_964_ == 0)
{
v___x_966_ = v___x_963_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_a_961_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
else
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_976_; 
lean_dec(v_a_912_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec_ref(v_prf_901_);
lean_dec_ref(v_type_900_);
lean_dec_ref(v___x_656_);
lean_dec(v_fvarId_655_);
lean_dec(v___x_654_);
lean_dec(v_mvarId_653_);
v_a_969_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_976_ == 0)
{
v___x_971_ = v___x_915_;
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_915_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_974_; 
if (v_isShared_972_ == 0)
{
v___x_974_ = v___x_971_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_a_969_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
else
{
lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_984_; 
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec_ref(v_prf_901_);
lean_dec_ref(v_type_900_);
lean_dec_ref(v___x_656_);
lean_dec(v_fvarId_655_);
lean_dec(v___x_654_);
lean_dec(v_mvarId_653_);
v_a_977_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_984_ == 0)
{
v___x_979_ = v___x_911_;
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v___x_911_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_a_977_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___lam__1___boxed(lean_object* v_mvarId_1057_, lean_object* v___x_1058_, lean_object* v_fvarId_1059_, lean_object* v___x_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Lean_Meta_injectionCore___lam__1(v_mvarId_1057_, v___x_1058_, v_fvarId_1059_, v___x_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore(lean_object* v_mvarId_1070_, lean_object* v_fvarId_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___f_1079_; lean_object* v___x_1080_; 
v___x_1077_ = ((lean_object*)(l_Lean_Meta_injectionCore___closed__0));
v___x_1078_ = ((lean_object*)(l_Lean_Meta_injectionCore___closed__1));
lean_inc(v_mvarId_1070_);
v___f_1079_ = lean_alloc_closure((void*)(l_Lean_Meta_injectionCore___lam__1___boxed), 9, 4);
lean_closure_set(v___f_1079_, 0, v_mvarId_1070_);
lean_closure_set(v___f_1079_, 1, v___x_1078_);
lean_closure_set(v___f_1079_, 2, v_fvarId_1071_);
lean_closure_set(v___f_1079_, 3, v___x_1077_);
v___x_1080_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg(v_mvarId_1070_, v___f_1079_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___boxed(lean_object* v_mvarId_1081_, lean_object* v_fvarId_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_Meta_injectionCore(v_mvarId_1081_, v_fvarId_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
lean_dec(v_a_1086_);
lean_dec_ref(v_a_1085_);
lean_dec(v_a_1084_);
lean_dec_ref(v_a_1083_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0(lean_object* v_mvarId_1089_, lean_object* v_val_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v___x_1096_; 
v___x_1096_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(v_mvarId_1089_, v_val_1090_, v___y_1092_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___boxed(lean_object* v_mvarId_1097_, lean_object* v_val_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0(v_mvarId_1097_, v_val_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0(lean_object* v_00_u03b2_1105_, lean_object* v_x_1106_, lean_object* v_x_1107_, lean_object* v_x_1108_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0___redArg(v_x_1106_, v_x_1107_, v_x_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1110_, lean_object* v_x_1111_, size_t v_x_1112_, size_t v_x_1113_, lean_object* v_x_1114_, lean_object* v_x_1115_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(v_x_1111_, v_x_1112_, v_x_1113_, v_x_1114_, v_x_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1117_, lean_object* v_x_1118_, lean_object* v_x_1119_, lean_object* v_x_1120_, lean_object* v_x_1121_, lean_object* v_x_1122_){
_start:
{
size_t v_x_17258__boxed_1123_; size_t v_x_17259__boxed_1124_; lean_object* v_res_1125_; 
v_x_17258__boxed_1123_ = lean_unbox_usize(v_x_1119_);
lean_dec(v_x_1119_);
v_x_17259__boxed_1124_ = lean_unbox_usize(v_x_1120_);
lean_dec(v_x_1120_);
v_res_1125_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2(v_00_u03b2_1117_, v_x_1118_, v_x_17258__boxed_1123_, v_x_17259__boxed_1124_, v_x_1121_, v_x_1122_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1126_, lean_object* v_n_1127_, lean_object* v_k_1128_, lean_object* v_v_1129_){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5___redArg(v_n_1127_, v_k_1128_, v_v_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_1131_, size_t v_depth_1132_, lean_object* v_keys_1133_, lean_object* v_vals_1134_, lean_object* v_heq_1135_, lean_object* v_i_1136_, lean_object* v_entries_1137_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___redArg(v_depth_1132_, v_keys_1133_, v_vals_1134_, v_i_1136_, v_entries_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1139_, lean_object* v_depth_1140_, lean_object* v_keys_1141_, lean_object* v_vals_1142_, lean_object* v_heq_1143_, lean_object* v_i_1144_, lean_object* v_entries_1145_){
_start:
{
size_t v_depth_boxed_1146_; lean_object* v_res_1147_; 
v_depth_boxed_1146_ = lean_unbox_usize(v_depth_1140_);
lean_dec(v_depth_1140_);
v_res_1147_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6(v_00_u03b2_1139_, v_depth_boxed_1146_, v_keys_1141_, v_vals_1142_, v_heq_1143_, v_i_1144_, v_entries_1145_);
lean_dec_ref(v_vals_1142_);
lean_dec_ref(v_keys_1141_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5_spec__6(lean_object* v_00_u03b2_1148_, lean_object* v_x_1149_, lean_object* v_x_1150_, lean_object* v_x_1151_, lean_object* v_x_1152_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(v_x_1149_, v_x_1150_, v_x_1151_, v_x_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorIdx(lean_object* v_x_1154_){
_start:
{
if (lean_obj_tag(v_x_1154_) == 0)
{
lean_object* v___x_1155_; 
v___x_1155_ = lean_unsigned_to_nat(0u);
return v___x_1155_;
}
else
{
lean_object* v___x_1156_; 
v___x_1156_ = lean_unsigned_to_nat(1u);
return v___x_1156_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorIdx___boxed(lean_object* v_x_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_Lean_Meta_InjectionResult_ctorIdx(v_x_1157_);
lean_dec(v_x_1157_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorElim___redArg(lean_object* v_t_1159_, lean_object* v_k_1160_){
_start:
{
if (lean_obj_tag(v_t_1159_) == 0)
{
return v_k_1160_;
}
else
{
lean_object* v_mvarId_1161_; lean_object* v_newEqs_1162_; lean_object* v_remainingNames_1163_; lean_object* v___x_1164_; 
v_mvarId_1161_ = lean_ctor_get(v_t_1159_, 0);
lean_inc(v_mvarId_1161_);
v_newEqs_1162_ = lean_ctor_get(v_t_1159_, 1);
lean_inc_ref(v_newEqs_1162_);
v_remainingNames_1163_ = lean_ctor_get(v_t_1159_, 2);
lean_inc(v_remainingNames_1163_);
lean_dec_ref_known(v_t_1159_, 3);
v___x_1164_ = lean_apply_3(v_k_1160_, v_mvarId_1161_, v_newEqs_1162_, v_remainingNames_1163_);
return v___x_1164_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorElim(lean_object* v_motive_1165_, lean_object* v_ctorIdx_1166_, lean_object* v_t_1167_, lean_object* v_h_1168_, lean_object* v_k_1169_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_1167_, v_k_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorElim___boxed(lean_object* v_motive_1171_, lean_object* v_ctorIdx_1172_, lean_object* v_t_1173_, lean_object* v_h_1174_, lean_object* v_k_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Lean_Meta_InjectionResult_ctorElim(v_motive_1171_, v_ctorIdx_1172_, v_t_1173_, v_h_1174_, v_k_1175_);
lean_dec(v_ctorIdx_1172_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_solved_elim___redArg(lean_object* v_t_1177_, lean_object* v_solved_1178_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_1177_, v_solved_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_solved_elim(lean_object* v_motive_1180_, lean_object* v_t_1181_, lean_object* v_h_1182_, lean_object* v_solved_1183_){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_1181_, v_solved_1183_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_subgoal_elim___redArg(lean_object* v_t_1185_, lean_object* v_subgoal_1186_){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_1185_, v_subgoal_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_subgoal_elim(lean_object* v_motive_1188_, lean_object* v_t_1189_, lean_object* v_h_1190_, lean_object* v_subgoal_1191_){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_1189_, v_subgoal_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go(uint8_t v_tryToClear_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_){
_start:
{
lean_object* v_zero_1203_; uint8_t v_isZero_1204_; 
v_zero_1203_ = lean_unsigned_to_nat(0u);
v_isZero_1204_ = lean_nat_dec_eq(v_a_1194_, v_zero_1203_);
if (v_isZero_1204_ == 1)
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
lean_dec(v_a_1194_);
v___x_1205_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1205_, 0, v_a_1195_);
lean_ctor_set(v___x_1205_, 1, v_a_1196_);
lean_ctor_set(v___x_1205_, 2, v_a_1197_);
v___x_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
return v___x_1206_;
}
else
{
lean_object* v_one_1207_; lean_object* v_n_1208_; 
v_one_1207_ = lean_unsigned_to_nat(1u);
v_n_1208_ = lean_nat_sub(v_a_1194_, v_one_1207_);
lean_dec(v_a_1194_);
if (lean_obj_tag(v_a_1197_) == 0)
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Lean_Meta_intro1Core(v_a_1195_, v_isZero_1204_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_a_1210_; lean_object* v_fst_1211_; lean_object* v_snd_1212_; lean_object* v___x_1213_; 
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_a_1210_);
lean_dec_ref_known(v___x_1209_, 1);
v_fst_1211_ = lean_ctor_get(v_a_1210_, 0);
lean_inc(v_fst_1211_);
v_snd_1212_ = lean_ctor_get(v_a_1210_, 1);
lean_inc(v_snd_1212_);
lean_dec(v_a_1210_);
v___x_1213_ = l_Lean_Meta_heqToEq(v_snd_1212_, v_fst_1211_, v_tryToClear_1193_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v_a_1214_; lean_object* v_fst_1215_; lean_object* v_snd_1216_; lean_object* v___x_1217_; 
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_a_1214_);
lean_dec_ref_known(v___x_1213_, 1);
v_fst_1215_ = lean_ctor_get(v_a_1214_, 0);
lean_inc(v_fst_1215_);
v_snd_1216_ = lean_ctor_get(v_a_1214_, 1);
lean_inc(v_snd_1216_);
lean_dec(v_a_1214_);
v___x_1217_ = lean_array_push(v_a_1196_, v_fst_1215_);
v_a_1194_ = v_n_1208_;
v_a_1195_ = v_snd_1216_;
v_a_1196_ = v___x_1217_;
goto _start;
}
else
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1226_; 
lean_dec(v_n_1208_);
lean_dec_ref(v_a_1196_);
v_a_1219_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1221_ = v___x_1213_;
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1213_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1224_; 
if (v_isShared_1222_ == 0)
{
v___x_1224_ = v___x_1221_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_a_1219_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
else
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1234_; 
lean_dec(v_n_1208_);
lean_dec_ref(v_a_1196_);
v_a_1227_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1229_ = v___x_1209_;
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1209_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1230_ == 0)
{
v___x_1232_ = v___x_1229_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1227_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
else
{
lean_object* v_head_1235_; lean_object* v_tail_1236_; lean_object* v___x_1237_; 
v_head_1235_ = lean_ctor_get(v_a_1197_, 0);
lean_inc(v_head_1235_);
v_tail_1236_ = lean_ctor_get(v_a_1197_, 1);
lean_inc(v_tail_1236_);
lean_dec_ref_known(v_a_1197_, 2);
v___x_1237_ = l_Lean_MVarId_intro(v_a_1195_, v_head_1235_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_);
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_object* v_a_1238_; lean_object* v_fst_1239_; lean_object* v_snd_1240_; lean_object* v___x_1241_; 
v_a_1238_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_a_1238_);
lean_dec_ref_known(v___x_1237_, 1);
v_fst_1239_ = lean_ctor_get(v_a_1238_, 0);
lean_inc(v_fst_1239_);
v_snd_1240_ = lean_ctor_get(v_a_1238_, 1);
lean_inc(v_snd_1240_);
lean_dec(v_a_1238_);
v___x_1241_ = l_Lean_Meta_heqToEq(v_snd_1240_, v_fst_1239_, v_tryToClear_1193_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; lean_object* v_fst_1243_; lean_object* v_snd_1244_; lean_object* v___x_1245_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_a_1242_);
lean_dec_ref_known(v___x_1241_, 1);
v_fst_1243_ = lean_ctor_get(v_a_1242_, 0);
lean_inc(v_fst_1243_);
v_snd_1244_ = lean_ctor_get(v_a_1242_, 1);
lean_inc(v_snd_1244_);
lean_dec(v_a_1242_);
v___x_1245_ = lean_array_push(v_a_1196_, v_fst_1243_);
v_a_1194_ = v_n_1208_;
v_a_1195_ = v_snd_1244_;
v_a_1196_ = v___x_1245_;
v_a_1197_ = v_tail_1236_;
goto _start;
}
else
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1254_; 
lean_dec(v_tail_1236_);
lean_dec(v_n_1208_);
lean_dec_ref(v_a_1196_);
v_a_1247_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1249_ = v___x_1241_;
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1241_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1252_; 
if (v_isShared_1250_ == 0)
{
v___x_1252_ = v___x_1249_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_a_1247_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
}
else
{
lean_object* v_a_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1262_; 
lean_dec(v_tail_1236_);
lean_dec(v_n_1208_);
lean_dec_ref(v_a_1196_);
v_a_1255_ = lean_ctor_get(v___x_1237_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1257_ = v___x_1237_;
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_a_1255_);
lean_dec(v___x_1237_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1260_; 
if (v_isShared_1258_ == 0)
{
v___x_1260_ = v___x_1257_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_a_1255_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go___boxed(lean_object* v_tryToClear_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_){
_start:
{
uint8_t v_tryToClear_boxed_1273_; lean_object* v_res_1274_; 
v_tryToClear_boxed_1273_ = lean_unbox(v_tryToClear_1263_);
v_res_1274_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go(v_tryToClear_boxed_1273_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_);
lean_dec(v_a_1271_);
lean_dec_ref(v_a_1270_);
lean_dec(v_a_1269_);
lean_dec_ref(v_a_1268_);
return v_res_1274_;
}
}
static lean_object* _init_l_Lean_Meta_injectionIntro___closed__2(void){
_start:
{
lean_object* v_cls_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v_cls_1281_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__1));
v___x_1282_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__0___closed__1));
v___x_1283_ = l_Lean_Name_append(v___x_1282_, v_cls_1281_);
return v___x_1283_;
}
}
static lean_object* _init_l_Lean_Meta_injectionIntro___closed__4(void){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__3));
v___x_1286_ = l_Lean_stringToMessageData(v___x_1285_);
return v___x_1286_;
}
}
static lean_object* _init_l_Lean_Meta_injectionIntro___closed__6(void){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1288_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__5));
v___x_1289_ = l_Lean_stringToMessageData(v___x_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro(lean_object* v_mvarId_1290_, lean_object* v_numEqs_1291_, lean_object* v_newNames_1292_, uint8_t v_tryToClear_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_){
_start:
{
lean_object* v___y_1300_; lean_object* v___y_1301_; lean_object* v___y_1302_; lean_object* v___y_1303_; lean_object* v_options_1306_; uint8_t v_hasTrace_1307_; 
v_options_1306_ = lean_ctor_get(v_a_1296_, 2);
v_hasTrace_1307_ = lean_ctor_get_uint8(v_options_1306_, sizeof(void*)*1);
if (v_hasTrace_1307_ == 0)
{
v___y_1300_ = v_a_1294_;
v___y_1301_ = v_a_1295_;
v___y_1302_ = v_a_1296_;
v___y_1303_ = v_a_1297_;
goto v___jp_1299_;
}
else
{
lean_object* v_inheritedTraceOptions_1308_; lean_object* v_cls_1309_; lean_object* v___x_1310_; uint8_t v___x_1311_; 
v_inheritedTraceOptions_1308_ = lean_ctor_get(v_a_1296_, 13);
v_cls_1309_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__1));
v___x_1310_ = lean_obj_once(&l_Lean_Meta_injectionIntro___closed__2, &l_Lean_Meta_injectionIntro___closed__2_once, _init_l_Lean_Meta_injectionIntro___closed__2);
v___x_1311_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1308_, v_options_1306_, v___x_1310_);
if (v___x_1311_ == 0)
{
v___y_1300_ = v_a_1294_;
v___y_1301_ = v_a_1295_;
v___y_1302_ = v_a_1296_;
v___y_1303_ = v_a_1297_;
goto v___jp_1299_;
}
else
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1312_ = lean_obj_once(&l_Lean_Meta_injectionIntro___closed__4, &l_Lean_Meta_injectionIntro___closed__4_once, _init_l_Lean_Meta_injectionIntro___closed__4);
lean_inc(v_numEqs_1291_);
v___x_1313_ = l_Nat_reprFast(v_numEqs_1291_);
v___x_1314_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1313_);
v___x_1315_ = l_Lean_MessageData_ofFormat(v___x_1314_);
v___x_1316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1312_);
lean_ctor_set(v___x_1316_, 1, v___x_1315_);
v___x_1317_ = lean_obj_once(&l_Lean_Meta_injectionIntro___closed__6, &l_Lean_Meta_injectionIntro___closed__6_once, _init_l_Lean_Meta_injectionIntro___closed__6);
v___x_1318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1316_);
lean_ctor_set(v___x_1318_, 1, v___x_1317_);
lean_inc(v_mvarId_1290_);
v___x_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1319_, 0, v_mvarId_1290_);
v___x_1320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1318_);
lean_ctor_set(v___x_1320_, 1, v___x_1319_);
v___x_1321_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v_cls_1309_, v___x_1320_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_dec_ref_known(v___x_1321_, 1);
v___y_1300_ = v_a_1294_;
v___y_1301_ = v_a_1295_;
v___y_1302_ = v_a_1296_;
v___y_1303_ = v_a_1297_;
goto v___jp_1299_;
}
else
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1329_; 
lean_dec(v_newNames_1292_);
lean_dec(v_numEqs_1291_);
lean_dec(v_mvarId_1290_);
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1324_ = v___x_1321_;
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1321_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1327_; 
if (v_isShared_1325_ == 0)
{
v___x_1327_ = v___x_1324_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1322_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
}
}
v___jp_1299_:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__0));
v___x_1305_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go(v_tryToClear_1293_, v_numEqs_1291_, v_mvarId_1290_, v___x_1304_, v_newNames_1292_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
return v___x_1305_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro___boxed(lean_object* v_mvarId_1330_, lean_object* v_numEqs_1331_, lean_object* v_newNames_1332_, lean_object* v_tryToClear_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_){
_start:
{
uint8_t v_tryToClear_boxed_1339_; lean_object* v_res_1340_; 
v_tryToClear_boxed_1339_ = lean_unbox(v_tryToClear_1333_);
v_res_1340_ = l_Lean_Meta_injectionIntro(v_mvarId_1330_, v_numEqs_1331_, v_newNames_1332_, v_tryToClear_boxed_1339_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_);
lean_dec(v_a_1337_);
lean_dec_ref(v_a_1336_);
lean_dec(v_a_1335_);
lean_dec_ref(v_a_1334_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injection(lean_object* v_mvarId_1341_, lean_object* v_fvarId_1342_, lean_object* v_newNames_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = l_Lean_Meta_injectionCore(v_mvarId_1341_, v_fvarId_1342_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1362_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1352_ = v___x_1349_;
v_isShared_1353_ = v_isSharedCheck_1362_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1349_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1362_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
if (lean_obj_tag(v_a_1350_) == 0)
{
lean_object* v___x_1354_; lean_object* v___x_1356_; 
lean_dec(v_newNames_1343_);
v___x_1354_ = lean_box(0);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 0, v___x_1354_);
v___x_1356_ = v___x_1352_;
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
else
{
lean_object* v_mvarId_1358_; lean_object* v_numNewEqs_1359_; uint8_t v___x_1360_; lean_object* v___x_1361_; 
lean_del_object(v___x_1352_);
v_mvarId_1358_ = lean_ctor_get(v_a_1350_, 0);
lean_inc(v_mvarId_1358_);
v_numNewEqs_1359_ = lean_ctor_get(v_a_1350_, 1);
lean_inc(v_numNewEqs_1359_);
lean_dec_ref_known(v_a_1350_, 2);
v___x_1360_ = 1;
v___x_1361_ = l_Lean_Meta_injectionIntro(v_mvarId_1358_, v_numNewEqs_1359_, v_newNames_1343_, v___x_1360_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_);
return v___x_1361_;
}
}
}
else
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
lean_dec(v_newNames_1343_);
v_a_1363_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1349_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1349_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1363_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injection___boxed(lean_object* v_mvarId_1371_, lean_object* v_fvarId_1372_, lean_object* v_newNames_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Lean_Meta_injection(v_mvarId_1371_, v_fvarId_1372_, v_newNames_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
lean_dec(v_a_1377_);
lean_dec_ref(v_a_1376_);
lean_dec(v_a_1375_);
lean_dec_ref(v_a_1374_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorIdx(lean_object* v_x_1380_){
_start:
{
if (lean_obj_tag(v_x_1380_) == 0)
{
lean_object* v___x_1381_; 
v___x_1381_ = lean_unsigned_to_nat(0u);
return v___x_1381_;
}
else
{
lean_object* v___x_1382_; 
v___x_1382_ = lean_unsigned_to_nat(1u);
return v___x_1382_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorIdx___boxed(lean_object* v_x_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Lean_Meta_InjectionsResult_ctorIdx(v_x_1383_);
lean_dec(v_x_1383_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorElim___redArg(lean_object* v_t_1385_, lean_object* v_k_1386_){
_start:
{
if (lean_obj_tag(v_t_1385_) == 0)
{
return v_k_1386_;
}
else
{
lean_object* v_mvarId_1387_; lean_object* v_remainingNames_1388_; lean_object* v_forbidden_1389_; lean_object* v___x_1390_; 
v_mvarId_1387_ = lean_ctor_get(v_t_1385_, 0);
lean_inc(v_mvarId_1387_);
v_remainingNames_1388_ = lean_ctor_get(v_t_1385_, 1);
lean_inc(v_remainingNames_1388_);
v_forbidden_1389_ = lean_ctor_get(v_t_1385_, 2);
lean_inc(v_forbidden_1389_);
lean_dec_ref_known(v_t_1385_, 3);
v___x_1390_ = lean_apply_3(v_k_1386_, v_mvarId_1387_, v_remainingNames_1388_, v_forbidden_1389_);
return v___x_1390_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorElim(lean_object* v_motive_1391_, lean_object* v_ctorIdx_1392_, lean_object* v_t_1393_, lean_object* v_h_1394_, lean_object* v_k_1395_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1393_, v_k_1395_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorElim___boxed(lean_object* v_motive_1397_, lean_object* v_ctorIdx_1398_, lean_object* v_t_1399_, lean_object* v_h_1400_, lean_object* v_k_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Lean_Meta_InjectionsResult_ctorElim(v_motive_1397_, v_ctorIdx_1398_, v_t_1399_, v_h_1400_, v_k_1401_);
lean_dec(v_ctorIdx_1398_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_solved_elim___redArg(lean_object* v_t_1403_, lean_object* v_solved_1404_){
_start:
{
lean_object* v___x_1405_; 
v___x_1405_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1403_, v_solved_1404_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_solved_elim(lean_object* v_motive_1406_, lean_object* v_t_1407_, lean_object* v_h_1408_, lean_object* v_solved_1409_){
_start:
{
lean_object* v___x_1410_; 
v___x_1410_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1407_, v_solved_1409_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_subgoal_elim___redArg(lean_object* v_t_1411_, lean_object* v_subgoal_1412_){
_start:
{
lean_object* v___x_1413_; 
v___x_1413_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1411_, v_subgoal_1412_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_subgoal_elim(lean_object* v_motive_1414_, lean_object* v_t_1415_, lean_object* v_h_1416_, lean_object* v_subgoal_1417_){
_start:
{
lean_object* v___x_1418_; 
v___x_1418_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1415_, v_subgoal_1417_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(lean_object* v_x_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v___x_1425_; 
v___x_1425_ = l_Lean_Meta_saveState___redArg(v___y_1421_, v___y_1423_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_a_1426_; lean_object* v___x_1427_; 
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
lean_inc(v_a_1426_);
lean_dec_ref_known(v___x_1425_, 1);
lean_inc(v___y_1423_);
lean_inc_ref(v___y_1422_);
lean_inc(v___y_1421_);
lean_inc_ref(v___y_1420_);
v___x_1427_ = lean_apply_5(v_x_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, lean_box(0));
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_dec(v_a_1426_);
return v___x_1427_;
}
else
{
lean_object* v_a_1428_; uint8_t v___y_1430_; uint8_t v___x_1448_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
lean_inc(v_a_1428_);
v___x_1448_ = l_Lean_Exception_isInterrupt(v_a_1428_);
if (v___x_1448_ == 0)
{
uint8_t v___x_1449_; 
lean_inc(v_a_1428_);
v___x_1449_ = l_Lean_Exception_isRuntime(v_a_1428_);
v___y_1430_ = v___x_1449_;
goto v___jp_1429_;
}
else
{
v___y_1430_ = v___x_1448_;
goto v___jp_1429_;
}
v___jp_1429_:
{
if (v___y_1430_ == 0)
{
lean_object* v___x_1431_; 
lean_dec_ref_known(v___x_1427_, 1);
v___x_1431_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1426_, v___y_1421_, v___y_1423_);
lean_dec(v_a_1426_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1438_ == 0)
{
lean_object* v_unused_1439_; 
v_unused_1439_ = lean_ctor_get(v___x_1431_, 0);
lean_dec(v_unused_1439_);
v___x_1433_ = v___x_1431_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_dec(v___x_1431_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
lean_ctor_set_tag(v___x_1433_, 1);
lean_ctor_set(v___x_1433_, 0, v_a_1428_);
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1428_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
lean_dec(v_a_1428_);
v_a_1440_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1431_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1431_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1440_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
}
else
{
lean_dec(v_a_1428_);
lean_dec(v_a_1426_);
return v___x_1427_;
}
}
}
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
lean_dec_ref(v_x_1419_);
v_a_1450_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1425_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1425_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg___boxed(lean_object* v_x_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(v_x_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1(lean_object* v_00_u03b1_1465_, lean_object* v_x_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(v_x_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___boxed(lean_object* v_00_u03b1_1473_, lean_object* v_x_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1(v_00_u03b1_1473_, v_x_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
return v_res_1480_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(lean_object* v_k_1481_, lean_object* v_t_1482_){
_start:
{
if (lean_obj_tag(v_t_1482_) == 0)
{
lean_object* v_k_1483_; lean_object* v_l_1484_; lean_object* v_r_1485_; uint8_t v___x_1486_; 
v_k_1483_ = lean_ctor_get(v_t_1482_, 1);
v_l_1484_ = lean_ctor_get(v_t_1482_, 3);
v_r_1485_ = lean_ctor_get(v_t_1482_, 4);
v___x_1486_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1481_, v_k_1483_);
switch(v___x_1486_)
{
case 0:
{
v_t_1482_ = v_l_1484_;
goto _start;
}
case 1:
{
uint8_t v___x_1488_; 
v___x_1488_ = 1;
return v___x_1488_;
}
default: 
{
v_t_1482_ = v_r_1485_;
goto _start;
}
}
}
else
{
uint8_t v___x_1490_; 
v___x_1490_ = 0;
return v___x_1490_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg___boxed(lean_object* v_k_1491_, lean_object* v_t_1492_){
_start:
{
uint8_t v_res_1493_; lean_object* v_r_1494_; 
v_res_1493_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(v_k_1491_, v_t_1492_);
lean_dec(v_t_1492_);
lean_dec(v_k_1491_);
v_r_1494_ = lean_box(v_res_1493_);
return v_r_1494_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4(void){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1501_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__3));
v___x_1502_ = l_Lean_MessageData_ofFormat(v___x_1501_);
return v___x_1502_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5(void){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1503_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4, &l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4_once, _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4);
v___x_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1503_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0___boxed(lean_object* v_mvarId_1505_, lean_object* v_head_1506_, lean_object* v_newNames_1507_, lean_object* v_tail_1508_, lean_object* v_forbidden_1509_, lean_object* v_n_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0(v_mvarId_1505_, v_head_1506_, v_newNames_1507_, v_tail_1508_, v_forbidden_1509_, v_n_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
return v_res_1516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go(lean_object* v_depth_1517_, lean_object* v_fvarIds_1518_, lean_object* v_mvarId_1519_, lean_object* v_newNames_1520_, lean_object* v_forbidden_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_){
_start:
{
lean_object* v_zero_1527_; uint8_t v_isZero_1528_; 
v_zero_1527_ = lean_unsigned_to_nat(0u);
v_isZero_1528_ = lean_nat_dec_eq(v_depth_1517_, v_zero_1527_);
if (v_isZero_1528_ == 1)
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
lean_dec(v_forbidden_1521_);
lean_dec(v_newNames_1520_);
lean_dec(v_fvarIds_1518_);
lean_dec(v_depth_1517_);
v___x_1529_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__1));
v___x_1530_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5, &l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5_once, _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5);
v___x_1531_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1529_, v_mvarId_1519_, v___x_1530_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_);
return v___x_1531_;
}
else
{
if (lean_obj_tag(v_fvarIds_1518_) == 0)
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
lean_dec(v_depth_1517_);
v___x_1532_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1532_, 0, v_mvarId_1519_);
lean_ctor_set(v___x_1532_, 1, v_newNames_1520_);
lean_ctor_set(v___x_1532_, 2, v_forbidden_1521_);
v___x_1533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
return v___x_1533_;
}
else
{
lean_object* v_head_1534_; lean_object* v_tail_1535_; lean_object* v_one_1536_; lean_object* v_n_1537_; lean_object* v___x_1538_; lean_object* v___y_1540_; uint8_t v___y_1541_; uint8_t v___x_1543_; 
v_head_1534_ = lean_ctor_get(v_fvarIds_1518_, 0);
lean_inc(v_head_1534_);
v_tail_1535_ = lean_ctor_get(v_fvarIds_1518_, 1);
lean_inc(v_tail_1535_);
lean_dec_ref_known(v_fvarIds_1518_, 2);
v_one_1536_ = lean_unsigned_to_nat(1u);
v_n_1537_ = lean_nat_sub(v_depth_1517_, v_one_1536_);
lean_dec(v_depth_1517_);
v___x_1538_ = lean_nat_add(v_n_1537_, v_one_1536_);
v___x_1543_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(v_head_1534_, v_forbidden_1521_);
if (v___x_1543_ == 0)
{
lean_object* v___x_1544_; 
lean_inc(v_head_1534_);
v___x_1544_ = l_Lean_FVarId_getType___redArg(v_head_1534_, v_a_1522_, v_a_1524_, v_a_1525_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; lean_object* v___x_1546_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1545_);
lean_dec_ref_known(v___x_1544_, 1);
v___x_1546_ = l_Lean_Meta_matchEqHEq_x3f(v_a_1545_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_a_1547_);
lean_dec_ref_known(v___x_1546_, 1);
if (lean_obj_tag(v_a_1547_) == 1)
{
lean_object* v_val_1548_; lean_object* v_snd_1549_; lean_object* v_fst_1550_; lean_object* v_snd_1551_; lean_object* v___x_1552_; 
v_val_1548_ = lean_ctor_get(v_a_1547_, 0);
lean_inc(v_val_1548_);
lean_dec_ref_known(v_a_1547_, 1);
v_snd_1549_ = lean_ctor_get(v_val_1548_, 1);
lean_inc(v_snd_1549_);
lean_dec(v_val_1548_);
v_fst_1550_ = lean_ctor_get(v_snd_1549_, 0);
lean_inc(v_fst_1550_);
v_snd_1551_ = lean_ctor_get(v_snd_1549_, 1);
lean_inc(v_snd_1551_);
lean_dec(v_snd_1549_);
lean_inc(v_a_1525_);
lean_inc_ref(v_a_1524_);
lean_inc(v_a_1523_);
lean_inc_ref(v_a_1522_);
v___x_1552_ = lean_whnf(v_fst_1550_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v___x_1554_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_a_1553_);
lean_dec_ref_known(v___x_1552_, 1);
lean_inc(v_a_1525_);
lean_inc_ref(v_a_1524_);
lean_inc(v_a_1523_);
lean_inc_ref(v_a_1522_);
v___x_1554_ = lean_whnf(v_snd_1551_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; lean_object* v___f_1556_; uint8_t v___y_1558_; uint8_t v___x_1564_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1555_);
lean_dec_ref_known(v___x_1554_, 1);
lean_inc(v_forbidden_1521_);
lean_inc(v_tail_1535_);
lean_inc(v_newNames_1520_);
lean_inc(v_mvarId_1519_);
v___f_1556_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0___boxed), 11, 6);
lean_closure_set(v___f_1556_, 0, v_mvarId_1519_);
lean_closure_set(v___f_1556_, 1, v_head_1534_);
lean_closure_set(v___f_1556_, 2, v_newNames_1520_);
lean_closure_set(v___f_1556_, 3, v_tail_1535_);
lean_closure_set(v___f_1556_, 4, v_forbidden_1521_);
lean_closure_set(v___f_1556_, 5, v_n_1537_);
v___x_1564_ = l_Lean_Expr_isRawNatLit(v_a_1553_);
lean_dec(v_a_1553_);
if (v___x_1564_ == 0)
{
lean_dec(v_a_1555_);
v___y_1558_ = v___x_1564_;
goto v___jp_1557_;
}
else
{
uint8_t v___x_1565_; 
v___x_1565_ = l_Lean_Expr_isRawNatLit(v_a_1555_);
lean_dec(v_a_1555_);
v___y_1558_ = v___x_1565_;
goto v___jp_1557_;
}
v___jp_1557_:
{
if (v___y_1558_ == 0)
{
lean_object* v___x_1559_; 
v___x_1559_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(v___f_1556_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_dec(v___x_1538_);
lean_dec(v_tail_1535_);
lean_dec(v_forbidden_1521_);
lean_dec(v_newNames_1520_);
lean_dec(v_mvarId_1519_);
return v___x_1559_;
}
else
{
lean_object* v_a_1560_; uint8_t v___x_1561_; 
v_a_1560_ = lean_ctor_get(v___x_1559_, 0);
lean_inc(v_a_1560_);
v___x_1561_ = l_Lean_Exception_isInterrupt(v_a_1560_);
if (v___x_1561_ == 0)
{
uint8_t v___x_1562_; 
v___x_1562_ = l_Lean_Exception_isRuntime(v_a_1560_);
v___y_1540_ = v___x_1559_;
v___y_1541_ = v___x_1562_;
goto v___jp_1539_;
}
else
{
lean_dec(v_a_1560_);
v___y_1540_ = v___x_1559_;
v___y_1541_ = v___x_1561_;
goto v___jp_1539_;
}
}
}
else
{
lean_dec_ref(v___f_1556_);
v_depth_1517_ = v___x_1538_;
v_fvarIds_1518_ = v_tail_1535_;
goto _start;
}
}
}
else
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
lean_dec(v_a_1553_);
lean_dec(v___x_1538_);
lean_dec(v_n_1537_);
lean_dec(v_tail_1535_);
lean_dec(v_head_1534_);
lean_dec(v_forbidden_1521_);
lean_dec(v_newNames_1520_);
lean_dec(v_mvarId_1519_);
v_a_1566_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1568_ = v___x_1554_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1554_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1571_; 
if (v_isShared_1569_ == 0)
{
v___x_1571_ = v___x_1568_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1566_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
else
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1581_; 
lean_dec(v_snd_1551_);
lean_dec(v___x_1538_);
lean_dec(v_n_1537_);
lean_dec(v_tail_1535_);
lean_dec(v_head_1534_);
lean_dec(v_forbidden_1521_);
lean_dec(v_newNames_1520_);
lean_dec(v_mvarId_1519_);
v_a_1574_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___x_1552_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1552_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1577_ == 0)
{
v___x_1579_ = v___x_1576_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
else
{
lean_dec(v_a_1547_);
lean_dec(v_n_1537_);
lean_dec(v_head_1534_);
v_depth_1517_ = v___x_1538_;
v_fvarIds_1518_ = v_tail_1535_;
goto _start;
}
}
else
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1590_; 
lean_dec(v___x_1538_);
lean_dec(v_n_1537_);
lean_dec(v_tail_1535_);
lean_dec(v_head_1534_);
lean_dec(v_forbidden_1521_);
lean_dec(v_newNames_1520_);
lean_dec(v_mvarId_1519_);
v_a_1583_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1585_ = v___x_1546_;
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1546_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1586_ == 0)
{
v___x_1588_ = v___x_1585_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_a_1583_);
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
else
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1598_; 
lean_dec(v___x_1538_);
lean_dec(v_n_1537_);
lean_dec(v_tail_1535_);
lean_dec(v_head_1534_);
lean_dec(v_forbidden_1521_);
lean_dec(v_newNames_1520_);
lean_dec(v_mvarId_1519_);
v_a_1591_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1593_ = v___x_1544_;
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1544_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1594_ == 0)
{
v___x_1596_ = v___x_1593_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1591_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
}
else
{
lean_dec(v_n_1537_);
lean_dec(v_head_1534_);
v_depth_1517_ = v___x_1538_;
v_fvarIds_1518_ = v_tail_1535_;
goto _start;
}
v___jp_1539_:
{
if (v___y_1541_ == 0)
{
lean_dec_ref(v___y_1540_);
v_depth_1517_ = v___x_1538_;
v_fvarIds_1518_ = v_tail_1535_;
goto _start;
}
else
{
lean_dec(v___x_1538_);
lean_dec(v_tail_1535_);
lean_dec(v_forbidden_1521_);
lean_dec(v_newNames_1520_);
lean_dec(v_mvarId_1519_);
return v___y_1540_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___boxed(lean_object* v_depth_1600_, lean_object* v_fvarIds_1601_, lean_object* v_mvarId_1602_, lean_object* v_newNames_1603_, lean_object* v_forbidden_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go(v_depth_1600_, v_fvarIds_1601_, v_mvarId_1602_, v_newNames_1603_, v_forbidden_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_);
lean_dec(v_a_1608_);
lean_dec_ref(v_a_1607_);
lean_dec(v_a_1606_);
lean_dec_ref(v_a_1605_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0(lean_object* v_mvarId_1611_, lean_object* v_head_1612_, lean_object* v_newNames_1613_, lean_object* v_tail_1614_, lean_object* v_forbidden_1615_, lean_object* v_n_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
lean_object* v___x_1622_; 
lean_inc(v_head_1612_);
v___x_1622_ = l_Lean_Meta_injection(v_mvarId_1611_, v_head_1612_, v_newNames_1613_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1639_; 
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1625_ = v___x_1622_;
v_isShared_1626_ = v_isSharedCheck_1639_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1622_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1639_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
if (lean_obj_tag(v_a_1623_) == 0)
{
lean_object* v___x_1627_; lean_object* v___x_1629_; 
lean_dec(v_n_1616_);
lean_dec(v_forbidden_1615_);
lean_dec(v_tail_1614_);
lean_dec(v_head_1612_);
v___x_1627_ = lean_box(0);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 0, v___x_1627_);
v___x_1629_ = v___x_1625_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1627_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
else
{
lean_object* v_mvarId_1631_; lean_object* v_newEqs_1632_; lean_object* v_remainingNames_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
lean_del_object(v___x_1625_);
v_mvarId_1631_ = lean_ctor_get(v_a_1623_, 0);
lean_inc_n(v_mvarId_1631_, 2);
v_newEqs_1632_ = lean_ctor_get(v_a_1623_, 1);
lean_inc_ref(v_newEqs_1632_);
v_remainingNames_1633_ = lean_ctor_get(v_a_1623_, 2);
lean_inc(v_remainingNames_1633_);
lean_dec_ref_known(v_a_1623_, 3);
v___x_1634_ = lean_array_to_list(v_newEqs_1632_);
v___x_1635_ = l_List_appendTR___redArg(v___x_1634_, v_tail_1614_);
v___x_1636_ = l_Lean_FVarIdSet_insert(v_forbidden_1615_, v_head_1612_);
v___x_1637_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___boxed), 10, 5);
lean_closure_set(v___x_1637_, 0, v_n_1616_);
lean_closure_set(v___x_1637_, 1, v___x_1635_);
lean_closure_set(v___x_1637_, 2, v_mvarId_1631_);
lean_closure_set(v___x_1637_, 3, v_remainingNames_1633_);
lean_closure_set(v___x_1637_, 4, v___x_1636_);
v___x_1638_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg(v_mvarId_1631_, v___x_1637_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
return v___x_1638_;
}
}
}
else
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1647_; 
lean_dec(v_n_1616_);
lean_dec(v_forbidden_1615_);
lean_dec(v_tail_1614_);
lean_dec(v_head_1612_);
v_a_1640_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1642_ = v___x_1622_;
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1622_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1645_; 
if (v_isShared_1643_ == 0)
{
v___x_1645_ = v___x_1642_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_a_1640_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0(lean_object* v_00_u03b2_1648_, lean_object* v_k_1649_, lean_object* v_t_1650_){
_start:
{
uint8_t v___x_1651_; 
v___x_1651_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(v_k_1649_, v_t_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___boxed(lean_object* v_00_u03b2_1652_, lean_object* v_k_1653_, lean_object* v_t_1654_){
_start:
{
uint8_t v_res_1655_; lean_object* v_r_1656_; 
v_res_1655_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0(v_00_u03b2_1652_, v_k_1653_, v_t_1654_);
lean_dec(v_t_1654_);
lean_dec(v_k_1653_);
v_r_1656_ = lean_box(v_res_1655_);
return v_r_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections___lam__0(lean_object* v_maxDepth_1657_, lean_object* v_mvarId_1658_, lean_object* v_newNames_1659_, lean_object* v_forbidden_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
lean_object* v_lctx_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v_lctx_1666_ = lean_ctor_get(v___y_1661_, 2);
v___x_1667_ = l_Lean_LocalContext_getFVarIds(v_lctx_1666_);
v___x_1668_ = lean_array_to_list(v___x_1667_);
v___x_1669_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go(v_maxDepth_1657_, v___x_1668_, v_mvarId_1658_, v_newNames_1659_, v_forbidden_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections___lam__0___boxed(lean_object* v_maxDepth_1670_, lean_object* v_mvarId_1671_, lean_object* v_newNames_1672_, lean_object* v_forbidden_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_Lean_Meta_injections___lam__0(v_maxDepth_1670_, v_mvarId_1671_, v_newNames_1672_, v_forbidden_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections(lean_object* v_mvarId_1680_, lean_object* v_newNames_1681_, lean_object* v_maxDepth_1682_, lean_object* v_forbidden_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_){
_start:
{
lean_object* v___f_1689_; lean_object* v___x_1690_; 
lean_inc(v_mvarId_1680_);
v___f_1689_ = lean_alloc_closure((void*)(l_Lean_Meta_injections___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1689_, 0, v_maxDepth_1682_);
lean_closure_set(v___f_1689_, 1, v_mvarId_1680_);
lean_closure_set(v___f_1689_, 2, v_newNames_1681_);
lean_closure_set(v___f_1689_, 3, v_forbidden_1683_);
v___x_1690_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg(v_mvarId_1680_, v___f_1689_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections___boxed(lean_object* v_mvarId_1691_, lean_object* v_newNames_1692_, lean_object* v_maxDepth_1693_, lean_object* v_forbidden_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Lean_Meta_injections(v_mvarId_1691_, v_newNames_1692_, v_maxDepth_1693_, v_forbidden_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
lean_dec(v_a_1696_);
lean_dec_ref(v_a_1695_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1757_; uint8_t v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1757_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__1));
v___x_1758_ = 0;
v___x_1759_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__22_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_));
v___x_1760_ = l_Lean_registerTraceClass(v___x_1757_, v___x_1758_, v___x_1759_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2____boxed(lean_object* v_a_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l___private_Lean_Meta_Tactic_Injection_0__initFn_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_();
return v_res_1762_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Subst(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Injection(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Subst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Injection_0__initFn_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Injection(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Subst(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Injection(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Subst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Injection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Injection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Injection(builtin);
}
#ifdef __cplusplus
}
#endif
