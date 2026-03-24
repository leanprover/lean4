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
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_injectionCore_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_injectionCore_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_injectionCore_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_injectionCore_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_injectionCore_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_injectionCore_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_injectionCore_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_injectionCore_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_injectionCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_injectionCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_injectionCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_injectionCore_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_injectionCore_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__2___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__2___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__2___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__2___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__2___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3_spec__7___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_injectionCore___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "ill-formed noConfusion auxiliary construction"};
static const lean_object* l_Lean_Meta_injectionCore___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_injectionCore___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_injectionCore___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Meta_injectionCore___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Meta_injectionCore___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_injectionCore___lam__0___closed__2;
static lean_once_cell_t l_Lean_Meta_injectionCore___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_injectionCore___lam__0___closed__3;
static const lean_string_object l_Lean_Meta_injectionCore___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "equality of constructor applications expected"};
static const lean_object* l_Lean_Meta_injectionCore___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Meta_injectionCore___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_injectionCore___lam__0___closed__4_value)}};
static const lean_object* l_Lean_Meta_injectionCore___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_Meta_injectionCore___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_injectionCore___lam__0___closed__6;
static lean_once_cell_t l_Lean_Meta_injectionCore___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_injectionCore___lam__0___closed__7;
static const lean_string_object l_Lean_Meta_injectionCore___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "subgoal with "};
static const lean_object* l_Lean_Meta_injectionCore___lam__0___closed__8 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_Meta_injectionCore___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_injectionCore___lam__0___closed__9;
static const lean_string_object l_Lean_Meta_injectionCore___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " fields:\n"};
static const lean_object* l_Lean_Meta_injectionCore___lam__0___closed__10 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__0___closed__10_value;
static lean_once_cell_t l_Lean_Meta_injectionCore___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_injectionCore___lam__0___closed__11;
static const lean_string_object l_Lean_Meta_injectionCore___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "ill-formed noConfusion auxiliary construction with type:"};
static const lean_object* l_Lean_Meta_injectionCore___lam__0___closed__12 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__0___closed__12_value;
static lean_once_cell_t l_Lean_Meta_injectionCore___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_injectionCore___lam__0___closed__13;
static lean_once_cell_t l_Lean_Meta_injectionCore___lam__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_injectionCore___lam__0___closed__14;
static const lean_string_object l_Lean_Meta_injectionCore___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "got no-confusion principle"};
static const lean_object* l_Lean_Meta_injectionCore___lam__0___closed__15 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__0___closed__15_value;
static lean_once_cell_t l_Lean_Meta_injectionCore___lam__0___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_injectionCore___lam__0___closed__16;
static const lean_string_object l_Lean_Meta_injectionCore___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "\nof type"};
static const lean_object* l_Lean_Meta_injectionCore___lam__0___closed__17 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__0___closed__17_value;
static lean_once_cell_t l_Lean_Meta_injectionCore___lam__0___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_injectionCore___lam__0___closed__18;
static const lean_string_object l_Lean_Meta_injectionCore___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_injectionCore___lam__0___closed__19 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__0___closed__19_value;
static const lean_ctor_object l_Lean_Meta_injectionCore___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_injectionCore___lam__0___closed__19_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_injectionCore___lam__0___closed__20 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__0___closed__20_value;
static const lean_string_object l_Lean_Meta_injectionCore___lam__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "equality expected"};
static const lean_object* l_Lean_Meta_injectionCore___lam__0___closed__21 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__0___closed__21_value;
static const lean_ctor_object l_Lean_Meta_injectionCore___lam__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_injectionCore___lam__0___closed__21_value)}};
static const lean_object* l_Lean_Meta_injectionCore___lam__0___closed__22 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__0___closed__22_value;
static lean_once_cell_t l_Lean_Meta_injectionCore___lam__0___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_injectionCore___lam__0___closed__23;
static lean_once_cell_t l_Lean_Meta_injectionCore___lam__0___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_injectionCore___lam__0___closed__24;
static const lean_string_object l_Lean_Meta_injectionCore___lam__0___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_injectionCore___lam__0___closed__25 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__0___closed__25_value;
static const lean_string_object l_Lean_Meta_injectionCore___lam__0___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_injectionCore___lam__0___closed__26 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__0___closed__26_value;
static const lean_string_object l_Lean_Meta_injectionCore___lam__0___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "applying noConfusion to "};
static const lean_object* l_Lean_Meta_injectionCore___lam__0___closed__27 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__0___closed__27_value;
static lean_once_cell_t l_Lean_Meta_injectionCore___lam__0___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_injectionCore___lam__0___closed__28;
static const lean_string_object l_Lean_Meta_injectionCore___lam__0___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " at\n"};
static const lean_object* l_Lean_Meta_injectionCore___lam__0___closed__29 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__0___closed__29_value;
static lean_once_cell_t l_Lean_Meta_injectionCore___lam__0___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_injectionCore___lam__0___closed__30;
static const lean_string_object l_Lean_Meta_injectionCore___lam__0___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HEq"};
static const lean_object* l_Lean_Meta_injectionCore___lam__0___closed__31 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__0___closed__31_value;
static const lean_ctor_object l_Lean_Meta_injectionCore___lam__0___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_injectionCore___lam__0___closed__31_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_object* l_Lean_Meta_injectionCore___lam__0___closed__32 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__0___closed__32_value;
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_injectionCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "injection"};
static const lean_object* l_Lean_Meta_injectionCore___closed__0 = (const lean_object*)&l_Lean_Meta_injectionCore___closed__0_value;
static const lean_ctor_object l_Lean_Meta_injectionCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_injectionCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(191, 140, 244, 245, 189, 133, 170, 178)}};
static const lean_object* l_Lean_Meta_injectionCore___closed__1 = (const lean_object*)&l_Lean_Meta_injectionCore___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3_spec__7(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Meta_injectionIntro___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_injectionCore___lam__0___closed__25_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_injectionIntro___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_injectionIntro___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_injectionCore___lam__0___closed__26_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Meta_injectionIntro___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_injectionIntro___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_injectionCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 78, 14, 229, 214, 232, 184, 172)}};
static const lean_object* l_Lean_Meta_injectionIntro___closed__1 = (const lean_object*)&l_Lean_Meta_injectionIntro___closed__1_value;
static const lean_string_object l_Lean_Meta_injectionIntro___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "introducing "};
static const lean_object* l_Lean_Meta_injectionIntro___closed__2 = (const lean_object*)&l_Lean_Meta_injectionIntro___closed__2_value;
static lean_once_cell_t l_Lean_Meta_injectionIntro___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_injectionIntro___closed__3;
static const lean_string_object l_Lean_Meta_injectionIntro___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = " new equalities at\n"};
static const lean_object* l_Lean_Meta_injectionIntro___closed__4 = (const lean_object*)&l_Lean_Meta_injectionIntro___closed__4_value;
static lean_once_cell_t l_Lean_Meta_injectionIntro___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_injectionIntro___closed__5;
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__4_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__3_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_injectionCore___lam__0___closed__25_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__4_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__4_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__5_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__4_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_injectionCore___lam__0___closed__26_value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__14_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__13_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_injectionCore___lam__0___closed__25_value),LEAN_SCALAR_PTR_LITERAL(120, 246, 74, 246, 83, 217, 223, 61)}};
static const lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__14_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__14_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__15_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__14_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_injectionCore___lam__0___closed__26_value),LEAN_SCALAR_PTR_LITERAL(101, 249, 16, 135, 154, 231, 101, 58)}};
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
lean_dec_ref(v___x_98_);
v___x_100_ = l_Lean_Meta_isProp(v_a_99_, v___y_87_, v___y_88_, v___y_89_, v___y_90_);
if (lean_obj_tag(v___x_100_) == 0)
{
lean_object* v_a_101_; lean_object* v_a_103_; uint8_t v___x_107_; 
v_a_101_ = lean_ctor_get(v___x_100_, 0);
lean_inc(v_a_101_);
lean_dec_ref(v___x_100_);
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
lean_dec_ref(v_t_210_);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_injectionCore_spec__1___redArg(lean_object* v_cls_246_, lean_object* v___y_247_){
_start:
{
lean_object* v_options_249_; uint8_t v_hasTrace_250_; 
v_options_249_ = lean_ctor_get(v___y_247_, 2);
v_hasTrace_250_ = lean_ctor_get_uint8(v_options_249_, sizeof(void*)*1);
if (v_hasTrace_250_ == 0)
{
lean_object* v___x_251_; lean_object* v___x_252_; 
lean_dec(v_cls_246_);
v___x_251_ = lean_box(v_hasTrace_250_);
v___x_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
return v___x_252_;
}
else
{
lean_object* v_inheritedTraceOptions_253_; lean_object* v___x_254_; lean_object* v___x_255_; uint8_t v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v_inheritedTraceOptions_253_ = lean_ctor_get(v___y_247_, 13);
v___x_254_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_injectionCore_spec__1___redArg___closed__1));
v___x_255_ = l_Lean_Name_append(v___x_254_, v_cls_246_);
v___x_256_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_253_, v_options_249_, v___x_255_);
lean_dec(v___x_255_);
v___x_257_ = lean_box(v___x_256_);
v___x_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
return v___x_258_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_injectionCore_spec__1___redArg___boxed(lean_object* v_cls_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_injectionCore_spec__1___redArg(v_cls_259_, v___y_260_);
lean_dec_ref(v___y_260_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_injectionCore_spec__1(lean_object* v_cls_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_injectionCore_spec__1___redArg(v_cls_263_, v___y_266_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_injectionCore_spec__1___boxed(lean_object* v_cls_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_injectionCore_spec__1(v_cls_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__3___redArg(lean_object* v_mvarId_277_, lean_object* v_x_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_277_, v_x_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_292_; 
v_a_285_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_292_ == 0)
{
v___x_287_ = v___x_284_;
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v___x_284_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_290_; 
if (v_isShared_288_ == 0)
{
v___x_290_ = v___x_287_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_a_285_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
else
{
lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_300_; 
v_a_293_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_300_ == 0)
{
v___x_295_ = v___x_284_;
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_dec(v___x_284_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_298_; 
if (v_isShared_296_ == 0)
{
v___x_298_ = v___x_295_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_a_293_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__3___redArg___boxed(lean_object* v_mvarId_301_, lean_object* v_x_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__3___redArg(v_mvarId_301_, v_x_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__3(lean_object* v_00_u03b1_309_, lean_object* v_mvarId_310_, lean_object* v_x_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__3___redArg(v_mvarId_310_, v_x_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__3___boxed(lean_object* v_00_u03b1_318_, lean_object* v_mvarId_319_, lean_object* v_x_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__3(v_00_u03b1_318_, v_mvarId_319_, v_x_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_injectionCore_spec__2_spec__3(lean_object* v_msgData_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
lean_object* v___x_333_; lean_object* v_env_334_; lean_object* v___x_335_; lean_object* v_mctx_336_; lean_object* v_lctx_337_; lean_object* v_options_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_333_ = lean_st_ref_get(v___y_331_);
v_env_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc_ref(v_env_334_);
lean_dec(v___x_333_);
v___x_335_ = lean_st_ref_get(v___y_329_);
v_mctx_336_ = lean_ctor_get(v___x_335_, 0);
lean_inc_ref(v_mctx_336_);
lean_dec(v___x_335_);
v_lctx_337_ = lean_ctor_get(v___y_328_, 2);
v_options_338_ = lean_ctor_get(v___y_330_, 2);
lean_inc_ref(v_options_338_);
lean_inc_ref(v_lctx_337_);
v___x_339_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_339_, 0, v_env_334_);
lean_ctor_set(v___x_339_, 1, v_mctx_336_);
lean_ctor_set(v___x_339_, 2, v_lctx_337_);
lean_ctor_set(v___x_339_, 3, v_options_338_);
v___x_340_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v_msgData_327_);
v___x_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_injectionCore_spec__2_spec__3___boxed(lean_object* v_msgData_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_injectionCore_spec__2_spec__3(v_msgData_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
return v_res_348_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__2___closed__0(void){
_start:
{
lean_object* v___x_349_; double v___x_350_; 
v___x_349_ = lean_unsigned_to_nat(0u);
v___x_350_ = lean_float_of_nat(v___x_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__2(lean_object* v_cls_354_, lean_object* v_msg_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v_ref_361_; lean_object* v___x_362_; lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_407_; 
v_ref_361_ = lean_ctor_get(v___y_358_, 5);
v___x_362_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_injectionCore_spec__2_spec__3(v_msg_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_);
v_a_363_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_407_ == 0)
{
v___x_365_ = v___x_362_;
v_isShared_366_ = v_isSharedCheck_407_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_362_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_407_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_367_; lean_object* v_traceState_368_; lean_object* v_env_369_; lean_object* v_nextMacroScope_370_; lean_object* v_ngen_371_; lean_object* v_auxDeclNGen_372_; lean_object* v_cache_373_; lean_object* v_messages_374_; lean_object* v_infoState_375_; lean_object* v_snapshotTasks_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_406_; 
v___x_367_ = lean_st_ref_take(v___y_359_);
v_traceState_368_ = lean_ctor_get(v___x_367_, 4);
v_env_369_ = lean_ctor_get(v___x_367_, 0);
v_nextMacroScope_370_ = lean_ctor_get(v___x_367_, 1);
v_ngen_371_ = lean_ctor_get(v___x_367_, 2);
v_auxDeclNGen_372_ = lean_ctor_get(v___x_367_, 3);
v_cache_373_ = lean_ctor_get(v___x_367_, 5);
v_messages_374_ = lean_ctor_get(v___x_367_, 6);
v_infoState_375_ = lean_ctor_get(v___x_367_, 7);
v_snapshotTasks_376_ = lean_ctor_get(v___x_367_, 8);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_406_ == 0)
{
v___x_378_ = v___x_367_;
v_isShared_379_ = v_isSharedCheck_406_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_snapshotTasks_376_);
lean_inc(v_infoState_375_);
lean_inc(v_messages_374_);
lean_inc(v_cache_373_);
lean_inc(v_traceState_368_);
lean_inc(v_auxDeclNGen_372_);
lean_inc(v_ngen_371_);
lean_inc(v_nextMacroScope_370_);
lean_inc(v_env_369_);
lean_dec(v___x_367_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_406_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
uint64_t v_tid_380_; lean_object* v_traces_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_405_; 
v_tid_380_ = lean_ctor_get_uint64(v_traceState_368_, sizeof(void*)*1);
v_traces_381_ = lean_ctor_get(v_traceState_368_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v_traceState_368_);
if (v_isSharedCheck_405_ == 0)
{
v___x_383_ = v_traceState_368_;
v_isShared_384_ = v_isSharedCheck_405_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_traces_381_);
lean_dec(v_traceState_368_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_405_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_385_; double v___x_386_; uint8_t v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_395_; 
v___x_385_ = lean_box(0);
v___x_386_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__2___closed__0);
v___x_387_ = 0;
v___x_388_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__2___closed__1));
v___x_389_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_389_, 0, v_cls_354_);
lean_ctor_set(v___x_389_, 1, v___x_385_);
lean_ctor_set(v___x_389_, 2, v___x_388_);
lean_ctor_set_float(v___x_389_, sizeof(void*)*3, v___x_386_);
lean_ctor_set_float(v___x_389_, sizeof(void*)*3 + 8, v___x_386_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*3 + 16, v___x_387_);
v___x_390_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__2___closed__2));
v___x_391_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_391_, 0, v___x_389_);
lean_ctor_set(v___x_391_, 1, v_a_363_);
lean_ctor_set(v___x_391_, 2, v___x_390_);
lean_inc(v_ref_361_);
v___x_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_392_, 0, v_ref_361_);
lean_ctor_set(v___x_392_, 1, v___x_391_);
v___x_393_ = l_Lean_PersistentArray_push___redArg(v_traces_381_, v___x_392_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 0, v___x_393_);
v___x_395_ = v___x_383_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_393_);
lean_ctor_set_uint64(v_reuseFailAlloc_404_, sizeof(void*)*1, v_tid_380_);
v___x_395_ = v_reuseFailAlloc_404_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
lean_object* v___x_397_; 
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 4, v___x_395_);
v___x_397_ = v___x_378_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_env_369_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v_nextMacroScope_370_);
lean_ctor_set(v_reuseFailAlloc_403_, 2, v_ngen_371_);
lean_ctor_set(v_reuseFailAlloc_403_, 3, v_auxDeclNGen_372_);
lean_ctor_set(v_reuseFailAlloc_403_, 4, v___x_395_);
lean_ctor_set(v_reuseFailAlloc_403_, 5, v_cache_373_);
lean_ctor_set(v_reuseFailAlloc_403_, 6, v_messages_374_);
lean_ctor_set(v_reuseFailAlloc_403_, 7, v_infoState_375_);
lean_ctor_set(v_reuseFailAlloc_403_, 8, v_snapshotTasks_376_);
v___x_397_ = v_reuseFailAlloc_403_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_401_; 
v___x_398_ = lean_st_ref_set(v___y_359_, v___x_397_);
v___x_399_ = lean_box(0);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 0, v___x_399_);
v___x_401_ = v___x_365_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_399_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__2___boxed(lean_object* v_cls_408_, lean_object* v_msg_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__2(v_cls_408_, v_msg_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3_spec__6_spec__7___redArg(lean_object* v_x_416_, lean_object* v_x_417_, lean_object* v_x_418_, lean_object* v_x_419_){
_start:
{
lean_object* v_ks_420_; lean_object* v_vs_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_445_; 
v_ks_420_ = lean_ctor_get(v_x_416_, 0);
v_vs_421_ = lean_ctor_get(v_x_416_, 1);
v_isSharedCheck_445_ = !lean_is_exclusive(v_x_416_);
if (v_isSharedCheck_445_ == 0)
{
v___x_423_ = v_x_416_;
v_isShared_424_ = v_isSharedCheck_445_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_vs_421_);
lean_inc(v_ks_420_);
lean_dec(v_x_416_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_445_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_425_; uint8_t v___x_426_; 
v___x_425_ = lean_array_get_size(v_ks_420_);
v___x_426_ = lean_nat_dec_lt(v_x_417_, v___x_425_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_430_; 
lean_dec(v_x_417_);
v___x_427_ = lean_array_push(v_ks_420_, v_x_418_);
v___x_428_ = lean_array_push(v_vs_421_, v_x_419_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 1, v___x_428_);
lean_ctor_set(v___x_423_, 0, v___x_427_);
v___x_430_ = v___x_423_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v___x_427_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v___x_428_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
else
{
lean_object* v_k_x27_432_; uint8_t v___x_433_; 
v_k_x27_432_ = lean_array_fget_borrowed(v_ks_420_, v_x_417_);
v___x_433_ = l_Lean_instBEqMVarId_beq(v_x_418_, v_k_x27_432_);
if (v___x_433_ == 0)
{
lean_object* v___x_435_; 
if (v_isShared_424_ == 0)
{
v___x_435_ = v___x_423_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_ks_420_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v_vs_421_);
v___x_435_ = v_reuseFailAlloc_439_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = lean_unsigned_to_nat(1u);
v___x_437_ = lean_nat_add(v_x_417_, v___x_436_);
lean_dec(v_x_417_);
v_x_416_ = v___x_435_;
v_x_417_ = v___x_437_;
goto _start;
}
}
else
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_440_ = lean_array_fset(v_ks_420_, v_x_417_, v_x_418_);
v___x_441_ = lean_array_fset(v_vs_421_, v_x_417_, v_x_419_);
lean_dec(v_x_417_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 1, v___x_441_);
lean_ctor_set(v___x_423_, 0, v___x_440_);
v___x_443_ = v___x_423_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_440_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v___x_441_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3_spec__6___redArg(lean_object* v_n_446_, lean_object* v_k_447_, lean_object* v_v_448_){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = lean_unsigned_to_nat(0u);
v___x_450_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3_spec__6_spec__7___redArg(v_n_446_, v___x_449_, v_k_447_, v_v_448_);
return v___x_450_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_451_; size_t v___x_452_; size_t v___x_453_; 
v___x_451_ = ((size_t)5ULL);
v___x_452_ = ((size_t)1ULL);
v___x_453_ = lean_usize_shift_left(v___x_452_, v___x_451_);
return v___x_453_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_454_; size_t v___x_455_; size_t v___x_456_; 
v___x_454_ = ((size_t)1ULL);
v___x_455_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3___redArg___closed__0);
v___x_456_ = lean_usize_sub(v___x_455_, v___x_454_);
return v___x_456_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3___redArg(lean_object* v_x_458_, size_t v_x_459_, size_t v_x_460_, lean_object* v_x_461_, lean_object* v_x_462_){
_start:
{
if (lean_obj_tag(v_x_458_) == 0)
{
lean_object* v_es_463_; size_t v___x_464_; size_t v___x_465_; size_t v___x_466_; size_t v___x_467_; lean_object* v_j_468_; lean_object* v___x_469_; uint8_t v___x_470_; 
v_es_463_ = lean_ctor_get(v_x_458_, 0);
v___x_464_ = ((size_t)5ULL);
v___x_465_ = ((size_t)1ULL);
v___x_466_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3___redArg___closed__1);
v___x_467_ = lean_usize_land(v_x_459_, v___x_466_);
v_j_468_ = lean_usize_to_nat(v___x_467_);
v___x_469_ = lean_array_get_size(v_es_463_);
v___x_470_ = lean_nat_dec_lt(v_j_468_, v___x_469_);
if (v___x_470_ == 0)
{
lean_dec(v_j_468_);
lean_dec(v_x_462_);
lean_dec(v_x_461_);
return v_x_458_;
}
else
{
lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_507_; 
lean_inc_ref(v_es_463_);
v_isSharedCheck_507_ = !lean_is_exclusive(v_x_458_);
if (v_isSharedCheck_507_ == 0)
{
lean_object* v_unused_508_; 
v_unused_508_ = lean_ctor_get(v_x_458_, 0);
lean_dec(v_unused_508_);
v___x_472_ = v_x_458_;
v_isShared_473_ = v_isSharedCheck_507_;
goto v_resetjp_471_;
}
else
{
lean_dec(v_x_458_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_507_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v_v_474_; lean_object* v___x_475_; lean_object* v_xs_x27_476_; lean_object* v___y_478_; 
v_v_474_ = lean_array_fget(v_es_463_, v_j_468_);
v___x_475_ = lean_box(0);
v_xs_x27_476_ = lean_array_fset(v_es_463_, v_j_468_, v___x_475_);
switch(lean_obj_tag(v_v_474_))
{
case 0:
{
lean_object* v_key_483_; lean_object* v_val_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_494_; 
v_key_483_ = lean_ctor_get(v_v_474_, 0);
v_val_484_ = lean_ctor_get(v_v_474_, 1);
v_isSharedCheck_494_ = !lean_is_exclusive(v_v_474_);
if (v_isSharedCheck_494_ == 0)
{
v___x_486_ = v_v_474_;
v_isShared_487_ = v_isSharedCheck_494_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_val_484_);
lean_inc(v_key_483_);
lean_dec(v_v_474_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_494_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
uint8_t v___x_488_; 
v___x_488_ = l_Lean_instBEqMVarId_beq(v_x_461_, v_key_483_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; lean_object* v___x_490_; 
lean_del_object(v___x_486_);
v___x_489_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_483_, v_val_484_, v_x_461_, v_x_462_);
v___x_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
v___y_478_ = v___x_490_;
goto v___jp_477_;
}
else
{
lean_object* v___x_492_; 
lean_dec(v_val_484_);
lean_dec(v_key_483_);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 1, v_x_462_);
lean_ctor_set(v___x_486_, 0, v_x_461_);
v___x_492_ = v___x_486_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_x_461_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_x_462_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
v___y_478_ = v___x_492_;
goto v___jp_477_;
}
}
}
}
case 1:
{
lean_object* v_node_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_505_; 
v_node_495_ = lean_ctor_get(v_v_474_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v_v_474_);
if (v_isSharedCheck_505_ == 0)
{
v___x_497_ = v_v_474_;
v_isShared_498_ = v_isSharedCheck_505_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_node_495_);
lean_dec(v_v_474_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_505_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
size_t v___x_499_; size_t v___x_500_; lean_object* v___x_501_; lean_object* v___x_503_; 
v___x_499_ = lean_usize_shift_right(v_x_459_, v___x_464_);
v___x_500_ = lean_usize_add(v_x_460_, v___x_465_);
v___x_501_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3___redArg(v_node_495_, v___x_499_, v___x_500_, v_x_461_, v_x_462_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v___x_501_);
v___x_503_ = v___x_497_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_501_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
v___y_478_ = v___x_503_;
goto v___jp_477_;
}
}
}
default: 
{
lean_object* v___x_506_; 
v___x_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_506_, 0, v_x_461_);
lean_ctor_set(v___x_506_, 1, v_x_462_);
v___y_478_ = v___x_506_;
goto v___jp_477_;
}
}
v___jp_477_:
{
lean_object* v___x_479_; lean_object* v___x_481_; 
v___x_479_ = lean_array_fset(v_xs_x27_476_, v_j_468_, v___y_478_);
lean_dec(v_j_468_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 0, v___x_479_);
v___x_481_ = v___x_472_;
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
}
else
{
lean_object* v_ks_509_; lean_object* v_vs_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_530_; 
v_ks_509_ = lean_ctor_get(v_x_458_, 0);
v_vs_510_ = lean_ctor_get(v_x_458_, 1);
v_isSharedCheck_530_ = !lean_is_exclusive(v_x_458_);
if (v_isSharedCheck_530_ == 0)
{
v___x_512_ = v_x_458_;
v_isShared_513_ = v_isSharedCheck_530_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_vs_510_);
lean_inc(v_ks_509_);
lean_dec(v_x_458_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_530_;
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
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_ks_509_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v_vs_510_);
v___x_515_ = v_reuseFailAlloc_529_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
lean_object* v_newNode_516_; uint8_t v___y_518_; size_t v___x_524_; uint8_t v___x_525_; 
v_newNode_516_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3_spec__6___redArg(v___x_515_, v_x_461_, v_x_462_);
v___x_524_ = ((size_t)7ULL);
v___x_525_ = lean_usize_dec_le(v___x_524_, v_x_460_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_526_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_516_);
v___x_527_ = lean_unsigned_to_nat(4u);
v___x_528_ = lean_nat_dec_lt(v___x_526_, v___x_527_);
lean_dec(v___x_526_);
v___y_518_ = v___x_528_;
goto v___jp_517_;
}
else
{
v___y_518_ = v___x_525_;
goto v___jp_517_;
}
v___jp_517_:
{
if (v___y_518_ == 0)
{
lean_object* v_ks_519_; lean_object* v_vs_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v_ks_519_ = lean_ctor_get(v_newNode_516_, 0);
lean_inc_ref(v_ks_519_);
v_vs_520_ = lean_ctor_get(v_newNode_516_, 1);
lean_inc_ref(v_vs_520_);
lean_dec_ref(v_newNode_516_);
v___x_521_ = lean_unsigned_to_nat(0u);
v___x_522_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3___redArg___closed__2);
v___x_523_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3_spec__7___redArg(v_x_460_, v_ks_519_, v_vs_520_, v___x_521_, v___x_522_);
lean_dec_ref(v_vs_520_);
lean_dec_ref(v_ks_519_);
return v___x_523_;
}
else
{
return v_newNode_516_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3_spec__7___redArg(size_t v_depth_531_, lean_object* v_keys_532_, lean_object* v_vals_533_, lean_object* v_i_534_, lean_object* v_entries_535_){
_start:
{
lean_object* v___x_536_; uint8_t v___x_537_; 
v___x_536_ = lean_array_get_size(v_keys_532_);
v___x_537_ = lean_nat_dec_lt(v_i_534_, v___x_536_);
if (v___x_537_ == 0)
{
lean_dec(v_i_534_);
return v_entries_535_;
}
else
{
lean_object* v_k_538_; lean_object* v_v_539_; uint64_t v___x_540_; size_t v_h_541_; size_t v___x_542_; lean_object* v___x_543_; size_t v___x_544_; size_t v___x_545_; size_t v___x_546_; size_t v_h_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v_k_538_ = lean_array_fget_borrowed(v_keys_532_, v_i_534_);
v_v_539_ = lean_array_fget_borrowed(v_vals_533_, v_i_534_);
v___x_540_ = l_Lean_instHashableMVarId_hash(v_k_538_);
v_h_541_ = lean_uint64_to_usize(v___x_540_);
v___x_542_ = ((size_t)5ULL);
v___x_543_ = lean_unsigned_to_nat(1u);
v___x_544_ = ((size_t)1ULL);
v___x_545_ = lean_usize_sub(v_depth_531_, v___x_544_);
v___x_546_ = lean_usize_mul(v___x_542_, v___x_545_);
v_h_547_ = lean_usize_shift_right(v_h_541_, v___x_546_);
v___x_548_ = lean_nat_add(v_i_534_, v___x_543_);
lean_dec(v_i_534_);
lean_inc(v_v_539_);
lean_inc(v_k_538_);
v___x_549_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3___redArg(v_entries_535_, v_h_547_, v_depth_531_, v_k_538_, v_v_539_);
v_i_534_ = v___x_548_;
v_entries_535_ = v___x_549_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3_spec__7___redArg___boxed(lean_object* v_depth_551_, lean_object* v_keys_552_, lean_object* v_vals_553_, lean_object* v_i_554_, lean_object* v_entries_555_){
_start:
{
size_t v_depth_boxed_556_; lean_object* v_res_557_; 
v_depth_boxed_556_ = lean_unbox_usize(v_depth_551_);
lean_dec(v_depth_551_);
v_res_557_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3_spec__7___redArg(v_depth_boxed_556_, v_keys_552_, v_vals_553_, v_i_554_, v_entries_555_);
lean_dec_ref(v_vals_553_);
lean_dec_ref(v_keys_552_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_x_558_, lean_object* v_x_559_, lean_object* v_x_560_, lean_object* v_x_561_, lean_object* v_x_562_){
_start:
{
size_t v_x_15740__boxed_563_; size_t v_x_15741__boxed_564_; lean_object* v_res_565_; 
v_x_15740__boxed_563_ = lean_unbox_usize(v_x_559_);
lean_dec(v_x_559_);
v_x_15741__boxed_564_ = lean_unbox_usize(v_x_560_);
lean_dec(v_x_560_);
v_res_565_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3___redArg(v_x_558_, v_x_15740__boxed_563_, v_x_15741__boxed_564_, v_x_561_, v_x_562_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0___redArg(lean_object* v_x_566_, lean_object* v_x_567_, lean_object* v_x_568_){
_start:
{
uint64_t v___x_569_; size_t v___x_570_; size_t v___x_571_; lean_object* v___x_572_; 
v___x_569_ = l_Lean_instHashableMVarId_hash(v_x_567_);
v___x_570_ = lean_uint64_to_usize(v___x_569_);
v___x_571_ = ((size_t)1ULL);
v___x_572_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3___redArg(v_x_566_, v___x_570_, v___x_571_, v_x_567_, v_x_568_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(lean_object* v_mvarId_573_, lean_object* v_val_574_, lean_object* v___y_575_){
_start:
{
lean_object* v___x_577_; lean_object* v_mctx_578_; lean_object* v_cache_579_; lean_object* v_zetaDeltaFVarIds_580_; lean_object* v_postponed_581_; lean_object* v_diag_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_609_; 
v___x_577_ = lean_st_ref_take(v___y_575_);
v_mctx_578_ = lean_ctor_get(v___x_577_, 0);
v_cache_579_ = lean_ctor_get(v___x_577_, 1);
v_zetaDeltaFVarIds_580_ = lean_ctor_get(v___x_577_, 2);
v_postponed_581_ = lean_ctor_get(v___x_577_, 3);
v_diag_582_ = lean_ctor_get(v___x_577_, 4);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_609_ == 0)
{
v___x_584_ = v___x_577_;
v_isShared_585_ = v_isSharedCheck_609_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_diag_582_);
lean_inc(v_postponed_581_);
lean_inc(v_zetaDeltaFVarIds_580_);
lean_inc(v_cache_579_);
lean_inc(v_mctx_578_);
lean_dec(v___x_577_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_609_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v_depth_586_; lean_object* v_levelAssignDepth_587_; lean_object* v_mvarCounter_588_; lean_object* v_lDepth_589_; lean_object* v_decls_590_; lean_object* v_userNames_591_; lean_object* v_lAssignment_592_; lean_object* v_eAssignment_593_; lean_object* v_dAssignment_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_608_; 
v_depth_586_ = lean_ctor_get(v_mctx_578_, 0);
v_levelAssignDepth_587_ = lean_ctor_get(v_mctx_578_, 1);
v_mvarCounter_588_ = lean_ctor_get(v_mctx_578_, 2);
v_lDepth_589_ = lean_ctor_get(v_mctx_578_, 3);
v_decls_590_ = lean_ctor_get(v_mctx_578_, 4);
v_userNames_591_ = lean_ctor_get(v_mctx_578_, 5);
v_lAssignment_592_ = lean_ctor_get(v_mctx_578_, 6);
v_eAssignment_593_ = lean_ctor_get(v_mctx_578_, 7);
v_dAssignment_594_ = lean_ctor_get(v_mctx_578_, 8);
v_isSharedCheck_608_ = !lean_is_exclusive(v_mctx_578_);
if (v_isSharedCheck_608_ == 0)
{
v___x_596_ = v_mctx_578_;
v_isShared_597_ = v_isSharedCheck_608_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_dAssignment_594_);
lean_inc(v_eAssignment_593_);
lean_inc(v_lAssignment_592_);
lean_inc(v_userNames_591_);
lean_inc(v_decls_590_);
lean_inc(v_lDepth_589_);
lean_inc(v_mvarCounter_588_);
lean_inc(v_levelAssignDepth_587_);
lean_inc(v_depth_586_);
lean_dec(v_mctx_578_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_608_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_598_; lean_object* v___x_600_; 
v___x_598_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0___redArg(v_eAssignment_593_, v_mvarId_573_, v_val_574_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 7, v___x_598_);
v___x_600_ = v___x_596_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_depth_586_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v_levelAssignDepth_587_);
lean_ctor_set(v_reuseFailAlloc_607_, 2, v_mvarCounter_588_);
lean_ctor_set(v_reuseFailAlloc_607_, 3, v_lDepth_589_);
lean_ctor_set(v_reuseFailAlloc_607_, 4, v_decls_590_);
lean_ctor_set(v_reuseFailAlloc_607_, 5, v_userNames_591_);
lean_ctor_set(v_reuseFailAlloc_607_, 6, v_lAssignment_592_);
lean_ctor_set(v_reuseFailAlloc_607_, 7, v___x_598_);
lean_ctor_set(v_reuseFailAlloc_607_, 8, v_dAssignment_594_);
v___x_600_ = v_reuseFailAlloc_607_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_object* v___x_602_; 
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v___x_600_);
v___x_602_ = v___x_584_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_600_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v_cache_579_);
lean_ctor_set(v_reuseFailAlloc_606_, 2, v_zetaDeltaFVarIds_580_);
lean_ctor_set(v_reuseFailAlloc_606_, 3, v_postponed_581_);
lean_ctor_set(v_reuseFailAlloc_606_, 4, v_diag_582_);
v___x_602_ = v_reuseFailAlloc_606_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_603_ = lean_st_ref_set(v___y_575_, v___x_602_);
v___x_604_ = lean_box(0);
v___x_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
return v___x_605_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg___boxed(lean_object* v_mvarId_610_, lean_object* v_val_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(v_mvarId_610_, v_val_611_, v___y_612_);
lean_dec(v___y_612_);
return v_res_614_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__0___closed__2(void){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__0___closed__1));
v___x_619_ = l_Lean_MessageData_ofFormat(v___x_618_);
return v___x_619_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__0___closed__3(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__0___closed__2, &l_Lean_Meta_injectionCore___lam__0___closed__2_once, _init_l_Lean_Meta_injectionCore___lam__0___closed__2);
v___x_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
return v___x_621_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__0___closed__6(void){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__0___closed__5));
v___x_626_ = l_Lean_MessageData_ofFormat(v___x_625_);
return v___x_626_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__0___closed__7(void){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__0___closed__6, &l_Lean_Meta_injectionCore___lam__0___closed__6_once, _init_l_Lean_Meta_injectionCore___lam__0___closed__6);
v___x_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
return v___x_628_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__0___closed__9(void){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__0___closed__8));
v___x_631_ = l_Lean_stringToMessageData(v___x_630_);
return v___x_631_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__0___closed__11(void){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__0___closed__10));
v___x_634_ = l_Lean_stringToMessageData(v___x_633_);
return v___x_634_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__0___closed__13(void){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__0___closed__12));
v___x_637_ = l_Lean_stringToMessageData(v___x_636_);
return v___x_637_;
}
}
static uint64_t _init_l_Lean_Meta_injectionCore___lam__0___closed__14(void){
_start:
{
uint8_t v___x_638_; uint64_t v___x_639_; 
v___x_638_ = 1;
v___x_639_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_638_);
return v___x_639_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__0___closed__16(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__0___closed__15));
v___x_642_ = l_Lean_stringToMessageData(v___x_641_);
return v___x_642_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__0___closed__18(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__0___closed__17));
v___x_645_ = l_Lean_stringToMessageData(v___x_644_);
return v___x_645_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__0___closed__23(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__0___closed__22));
v___x_653_ = l_Lean_MessageData_ofFormat(v___x_652_);
return v___x_653_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__0___closed__24(void){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__0___closed__23, &l_Lean_Meta_injectionCore___lam__0___closed__23_once, _init_l_Lean_Meta_injectionCore___lam__0___closed__23);
v___x_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
return v___x_655_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__0___closed__28(void){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__0___closed__27));
v___x_660_ = l_Lean_stringToMessageData(v___x_659_);
return v___x_660_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__0___closed__30(void){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__0___closed__29));
v___x_663_ = l_Lean_stringToMessageData(v___x_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___lam__0(lean_object* v_mvarId_667_, lean_object* v___x_668_, lean_object* v_fvarId_669_, lean_object* v___x_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v_type_930_; lean_object* v_prf_931_; lean_object* v___y_932_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___x_1014_; 
lean_inc(v___x_668_);
lean_inc(v_mvarId_667_);
v___x_1014_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_667_, v___x_668_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v___x_1015_; 
lean_dec_ref(v___x_1014_);
lean_inc_ref(v___y_671_);
lean_inc(v_fvarId_669_);
v___x_1015_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_669_, v___y_671_, v___y_673_, v___y_674_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_a_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_a_1016_);
lean_dec_ref(v___x_1015_);
v___x_1017_ = l_Lean_LocalDecl_type(v_a_1016_);
lean_dec(v_a_1016_);
lean_inc(v___y_674_);
lean_inc_ref(v___y_673_);
lean_inc(v___y_672_);
lean_inc_ref(v___y_671_);
v___x_1018_ = lean_whnf(v___x_1017_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; uint8_t v___x_1023_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_a_1019_);
lean_dec_ref(v___x_1018_);
lean_inc(v_fvarId_669_);
v___x_1020_ = l_Lean_mkFVar(v_fvarId_669_);
v___x_1021_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__0___closed__32));
v___x_1022_ = lean_unsigned_to_nat(4u);
v___x_1023_ = l_Lean_Expr_isAppOfArity(v_a_1019_, v___x_1021_, v___x_1022_);
if (v___x_1023_ == 0)
{
v_type_930_ = v_a_1019_;
v_prf_931_ = v___x_1020_;
v___y_932_ = v___y_671_;
v___y_933_ = v___y_672_;
v___y_934_ = v___y_673_;
v___y_935_ = v___y_674_;
goto v___jp_929_;
}
else
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1024_ = l_Lean_Expr_appFn_x21(v_a_1019_);
v___x_1025_ = l_Lean_Expr_appFn_x21(v___x_1024_);
v___x_1026_ = l_Lean_Expr_appFn_x21(v___x_1025_);
v___x_1027_ = l_Lean_Expr_appArg_x21(v___x_1026_);
lean_dec_ref(v___x_1026_);
v___x_1028_ = l_Lean_Expr_appArg_x21(v___x_1024_);
lean_dec_ref(v___x_1024_);
v___x_1029_ = l_Lean_Meta_isExprDefEq(v___x_1027_, v___x_1028_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v_a_1030_; uint8_t v___x_1031_; 
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_a_1030_);
lean_dec_ref(v___x_1029_);
v___x_1031_ = lean_unbox(v_a_1030_);
lean_dec(v_a_1030_);
if (v___x_1031_ == 0)
{
lean_dec_ref(v___x_1025_);
v_type_930_ = v_a_1019_;
v_prf_931_ = v___x_1020_;
v___y_932_ = v___y_671_;
v___y_933_ = v___y_672_;
v___y_934_ = v___y_673_;
v___y_935_ = v___y_674_;
goto v___jp_929_;
}
else
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1032_ = l_Lean_Expr_appArg_x21(v___x_1025_);
lean_dec_ref(v___x_1025_);
v___x_1033_ = l_Lean_Expr_appArg_x21(v_a_1019_);
lean_dec(v_a_1019_);
v___x_1034_ = l_Lean_Meta_mkEq(v___x_1032_, v___x_1033_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v_a_1035_; lean_object* v___x_1036_; 
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_a_1035_);
lean_dec_ref(v___x_1034_);
v___x_1036_ = l_Lean_Meta_mkEqOfHEq(v___x_1020_, v___x_1023_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_a_1037_; 
v_a_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc(v_a_1037_);
lean_dec_ref(v___x_1036_);
v_type_930_ = v_a_1035_;
v_prf_931_ = v_a_1037_;
v___y_932_ = v___y_671_;
v___y_933_ = v___y_672_;
v___y_934_ = v___y_673_;
v___y_935_ = v___y_674_;
goto v___jp_929_;
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
lean_dec(v_a_1035_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec_ref(v___x_670_);
lean_dec(v_fvarId_669_);
lean_dec(v___x_668_);
lean_dec(v_mvarId_667_);
v_a_1038_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___x_1036_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1036_);
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
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1053_; 
lean_dec_ref(v___x_1020_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec_ref(v___x_670_);
lean_dec(v_fvarId_669_);
lean_dec(v___x_668_);
lean_dec(v_mvarId_667_);
v_a_1046_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1048_ = v___x_1034_;
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1034_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1051_; 
if (v_isShared_1049_ == 0)
{
v___x_1051_ = v___x_1048_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_a_1046_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
}
else
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1061_; 
lean_dec_ref(v___x_1025_);
lean_dec_ref(v___x_1020_);
lean_dec(v_a_1019_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec_ref(v___x_670_);
lean_dec(v_fvarId_669_);
lean_dec(v___x_668_);
lean_dec(v_mvarId_667_);
v_a_1054_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1056_ = v___x_1029_;
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1029_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1059_; 
if (v_isShared_1057_ == 0)
{
v___x_1059_ = v___x_1056_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1054_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec_ref(v___x_670_);
lean_dec(v_fvarId_669_);
lean_dec(v___x_668_);
lean_dec(v_mvarId_667_);
v_a_1062_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v___x_1018_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1018_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_a_1062_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
else
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1077_; 
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec_ref(v___x_670_);
lean_dec(v_fvarId_669_);
lean_dec(v___x_668_);
lean_dec(v_mvarId_667_);
v_a_1070_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1072_ = v___x_1015_;
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1015_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1075_; 
if (v_isShared_1073_ == 0)
{
v___x_1075_ = v___x_1072_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_a_1070_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
}
else
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec_ref(v___x_670_);
lean_dec(v_fvarId_669_);
lean_dec(v___x_668_);
lean_dec(v_mvarId_667_);
v_a_1078_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___x_1014_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1014_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
v___jp_676_:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__0___closed__3, &l_Lean_Meta_injectionCore___lam__0___closed__3_once, _init_l_Lean_Meta_injectionCore___lam__0___closed__3);
v___x_682_ = l_Lean_Meta_throwTacticEx___redArg(v___x_668_, v_mvarId_667_, v___x_681_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
return v___x_682_;
}
v___jp_683_:
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__0___closed__7, &l_Lean_Meta_injectionCore___lam__0___closed__7_once, _init_l_Lean_Meta_injectionCore___lam__0___closed__7);
v___x_689_ = l_Lean_Meta_throwTacticEx___redArg(v___x_668_, v_mvarId_667_, v___x_688_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
return v___x_689_;
}
v___jp_690_:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_693_, 0, v___y_692_);
lean_ctor_set(v___x_693_, 1, v___y_691_);
v___x_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
return v___x_694_;
}
v___jp_695_:
{
lean_object* v_toConstantVal_704_; lean_object* v_toConstantVal_705_; lean_object* v_numFields_706_; lean_object* v_name_707_; lean_object* v_name_708_; uint8_t v___x_709_; 
v_toConstantVal_704_ = lean_ctor_get(v___y_697_, 0);
v_toConstantVal_705_ = lean_ctor_get(v___y_698_, 0);
lean_inc_ref(v_toConstantVal_705_);
lean_dec_ref(v___y_698_);
v_numFields_706_ = lean_ctor_get(v___y_697_, 4);
lean_inc(v_numFields_706_);
v_name_707_ = lean_ctor_get(v_toConstantVal_704_, 0);
v_name_708_ = lean_ctor_get(v_toConstantVal_705_, 0);
lean_inc(v_name_708_);
lean_dec_ref(v_toConstantVal_705_);
v___x_709_ = lean_name_eq(v_name_707_, v_name_708_);
lean_dec(v_name_708_);
if (v___x_709_ == 0)
{
lean_object* v___x_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_718_; 
lean_dec(v_numFields_706_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec_ref(v___y_700_);
lean_dec_ref(v___y_697_);
lean_dec(v___y_696_);
lean_dec(v_fvarId_669_);
lean_dec(v___x_668_);
v___x_710_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(v_mvarId_667_, v___y_699_, v___y_701_);
lean_dec(v___y_701_);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_718_ == 0)
{
lean_object* v_unused_719_; 
v_unused_719_ = lean_ctor_get(v___x_710_, 0);
lean_dec(v_unused_719_);
v___x_712_ = v___x_710_;
v_isShared_713_ = v_isSharedCheck_718_;
goto v_resetjp_711_;
}
else
{
lean_dec(v___x_710_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_718_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_714_ = lean_box(0);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 0, v___x_714_);
v___x_716_ = v___x_712_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_714_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
else
{
lean_object* v___x_720_; 
lean_inc(v___y_703_);
lean_inc_ref(v___y_702_);
lean_inc(v___y_701_);
lean_inc_ref(v___y_700_);
lean_inc_ref(v___y_699_);
v___x_720_ = lean_infer_type(v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_721_; lean_object* v___x_722_; 
v_a_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_a_721_);
lean_dec_ref(v___x_720_);
v___x_722_ = l_Lean_Meta_whnfD(v_a_721_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc(v_a_723_);
lean_dec_ref(v___x_722_);
if (lean_obj_tag(v_a_723_) == 7)
{
lean_object* v_binderType_724_; lean_object* v___x_725_; 
lean_dec(v___x_668_);
v_binderType_724_ = lean_ctor_get(v_a_723_, 1);
lean_inc_ref(v_binderType_724_);
lean_dec_ref(v_a_723_);
lean_inc(v_mvarId_667_);
v___x_725_ = l_Lean_MVarId_getTag(v_mvarId_667_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_a_726_);
lean_dec_ref(v___x_725_);
v___x_727_ = l_Lean_Expr_headBeta(v_binderType_724_);
v___x_728_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_727_, v_a_726_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_a_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_786_; 
v_a_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_a_729_);
lean_dec_ref(v___x_728_);
lean_inc(v_a_729_);
v___x_730_ = l_Lean_Expr_app___override(v___y_699_, v_a_729_);
v___x_731_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(v_mvarId_667_, v___x_730_, v___y_701_);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_786_ == 0)
{
lean_object* v_unused_787_; 
v_unused_787_ = lean_ctor_get(v___x_731_, 0);
lean_dec(v_unused_787_);
v___x_733_ = v___x_731_;
v_isShared_734_ = v_isSharedCheck_786_;
goto v_resetjp_732_;
}
else
{
lean_dec(v___x_731_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_786_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = l_Lean_Expr_mvarId_x21(v_a_729_);
lean_dec(v_a_729_);
v___x_736_ = l_Lean_MVarId_tryClear(v___x_735_, v_fvarId_669_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_a_737_; lean_object* v___x_738_; 
v_a_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_a_737_);
lean_dec_ref(v___x_736_);
v___x_738_ = l_Lean_Meta_getCtorNumPropFields(v___y_697_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v___x_740_; lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_769_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_739_);
lean_dec_ref(v___x_738_);
lean_inc(v___y_696_);
v___x_740_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_injectionCore_spec__1___redArg(v___y_696_, v___y_702_);
v_a_741_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_769_ == 0)
{
v___x_743_ = v___x_740_;
v_isShared_744_ = v_isSharedCheck_769_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_740_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_769_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_745_; uint8_t v___x_746_; 
v___x_745_ = lean_nat_sub(v_numFields_706_, v_a_739_);
lean_dec(v_a_739_);
lean_dec(v_numFields_706_);
v___x_746_ = lean_unbox(v_a_741_);
lean_dec(v_a_741_);
if (v___x_746_ == 0)
{
lean_del_object(v___x_743_);
lean_del_object(v___x_733_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v___y_696_);
v___y_691_ = v___x_745_;
v___y_692_ = v_a_737_;
goto v___jp_690_;
}
else
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_750_; 
v___x_747_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__0___closed__9, &l_Lean_Meta_injectionCore___lam__0___closed__9_once, _init_l_Lean_Meta_injectionCore___lam__0___closed__9);
lean_inc(v___x_745_);
v___x_748_ = l_Nat_reprFast(v___x_745_);
if (v_isShared_744_ == 0)
{
lean_ctor_set_tag(v___x_743_, 3);
lean_ctor_set(v___x_743_, 0, v___x_748_);
v___x_750_ = v___x_743_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v___x_748_);
v___x_750_ = v_reuseFailAlloc_768_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_756_; 
v___x_751_ = l_Lean_MessageData_ofFormat(v___x_750_);
v___x_752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_747_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v___x_753_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__0___closed__11, &l_Lean_Meta_injectionCore___lam__0___closed__11_once, _init_l_Lean_Meta_injectionCore___lam__0___closed__11);
v___x_754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_752_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
lean_inc(v_a_737_);
if (v_isShared_734_ == 0)
{
lean_ctor_set_tag(v___x_733_, 1);
lean_ctor_set(v___x_733_, 0, v_a_737_);
v___x_756_ = v___x_733_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_737_);
v___x_756_ = v_reuseFailAlloc_767_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_757_, 0, v___x_754_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
v___x_758_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__2(v___y_696_, v___x_757_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_dec_ref(v___x_758_);
v___y_691_ = v___x_745_;
v___y_692_ = v_a_737_;
goto v___jp_690_;
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
lean_dec(v___x_745_);
lean_dec(v_a_737_);
v_a_759_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_758_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_758_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
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
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
lean_dec(v_a_737_);
lean_del_object(v___x_733_);
lean_dec(v_numFields_706_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v___y_696_);
v_a_770_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_738_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_738_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
else
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
lean_del_object(v___x_733_);
lean_dec(v_numFields_706_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec_ref(v___y_697_);
lean_dec(v___y_696_);
v_a_778_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_736_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_736_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
lean_dec(v_numFields_706_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec_ref(v___y_697_);
lean_dec(v___y_696_);
lean_dec(v_fvarId_669_);
lean_dec(v_mvarId_667_);
v_a_788_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_728_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_728_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
lean_dec_ref(v_binderType_724_);
lean_dec(v_numFields_706_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec_ref(v___y_697_);
lean_dec(v___y_696_);
lean_dec(v_fvarId_669_);
lean_dec(v_mvarId_667_);
v_a_796_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_725_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_725_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
else
{
lean_object* v___x_804_; lean_object* v_a_805_; uint8_t v___x_806_; 
lean_dec(v_numFields_706_);
lean_dec_ref(v___y_699_);
lean_dec_ref(v___y_697_);
lean_dec(v_fvarId_669_);
lean_inc(v___y_696_);
v___x_804_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_injectionCore_spec__1___redArg(v___y_696_, v___y_702_);
v_a_805_ = lean_ctor_get(v___x_804_, 0);
lean_inc(v_a_805_);
lean_dec_ref(v___x_804_);
v___x_806_ = lean_unbox(v_a_805_);
lean_dec(v_a_805_);
if (v___x_806_ == 0)
{
lean_dec(v_a_723_);
lean_dec(v___y_696_);
v___y_677_ = v___y_700_;
v___y_678_ = v___y_701_;
v___y_679_ = v___y_702_;
v___y_680_ = v___y_703_;
goto v___jp_676_;
}
else
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_807_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__0___closed__13, &l_Lean_Meta_injectionCore___lam__0___closed__13_once, _init_l_Lean_Meta_injectionCore___lam__0___closed__13);
v___x_808_ = l_Lean_indentExpr(v_a_723_);
v___x_809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_807_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
v___x_810_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__2(v___y_696_, v___x_809_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_dec_ref(v___x_810_);
v___y_677_ = v___y_700_;
v___y_678_ = v___y_701_;
v___y_679_ = v___y_702_;
v___y_680_ = v___y_703_;
goto v___jp_676_;
}
else
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_818_; 
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v___x_668_);
lean_dec(v_mvarId_667_);
v_a_811_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_818_ == 0)
{
v___x_813_ = v___x_810_;
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_810_);
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
}
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
lean_dec(v_numFields_706_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec_ref(v___y_697_);
lean_dec(v___y_696_);
lean_dec(v_fvarId_669_);
lean_dec(v___x_668_);
lean_dec(v_mvarId_667_);
v_a_819_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_722_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_722_);
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
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_dec(v_numFields_706_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec_ref(v___y_697_);
lean_dec(v___y_696_);
lean_dec(v_fvarId_669_);
lean_dec(v___x_668_);
lean_dec(v_mvarId_667_);
v_a_827_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_720_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_720_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
}
v___jp_835_:
{
lean_object* v___x_845_; uint8_t v_foApprox_846_; uint8_t v_ctxApprox_847_; uint8_t v_quasiPatternApprox_848_; uint8_t v_constApprox_849_; uint8_t v_isDefEqStuckEx_850_; uint8_t v_unificationHints_851_; uint8_t v_proofIrrelevance_852_; uint8_t v_assignSyntheticOpaque_853_; uint8_t v_offsetCnstrs_854_; uint8_t v_etaStruct_855_; uint8_t v_univApprox_856_; uint8_t v_iota_857_; uint8_t v_beta_858_; uint8_t v_proj_859_; uint8_t v_zeta_860_; uint8_t v_zetaDelta_861_; uint8_t v_zetaUnused_862_; uint8_t v_zetaHave_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_928_; 
v___x_845_ = l_Lean_Meta_Context_config(v___y_841_);
v_foApprox_846_ = lean_ctor_get_uint8(v___x_845_, 0);
v_ctxApprox_847_ = lean_ctor_get_uint8(v___x_845_, 1);
v_quasiPatternApprox_848_ = lean_ctor_get_uint8(v___x_845_, 2);
v_constApprox_849_ = lean_ctor_get_uint8(v___x_845_, 3);
v_isDefEqStuckEx_850_ = lean_ctor_get_uint8(v___x_845_, 4);
v_unificationHints_851_ = lean_ctor_get_uint8(v___x_845_, 5);
v_proofIrrelevance_852_ = lean_ctor_get_uint8(v___x_845_, 6);
v_assignSyntheticOpaque_853_ = lean_ctor_get_uint8(v___x_845_, 7);
v_offsetCnstrs_854_ = lean_ctor_get_uint8(v___x_845_, 8);
v_etaStruct_855_ = lean_ctor_get_uint8(v___x_845_, 10);
v_univApprox_856_ = lean_ctor_get_uint8(v___x_845_, 11);
v_iota_857_ = lean_ctor_get_uint8(v___x_845_, 12);
v_beta_858_ = lean_ctor_get_uint8(v___x_845_, 13);
v_proj_859_ = lean_ctor_get_uint8(v___x_845_, 14);
v_zeta_860_ = lean_ctor_get_uint8(v___x_845_, 15);
v_zetaDelta_861_ = lean_ctor_get_uint8(v___x_845_, 16);
v_zetaUnused_862_ = lean_ctor_get_uint8(v___x_845_, 17);
v_zetaHave_863_ = lean_ctor_get_uint8(v___x_845_, 18);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_928_ == 0)
{
v___x_865_ = v___x_845_;
v_isShared_866_ = v_isSharedCheck_928_;
goto v_resetjp_864_;
}
else
{
lean_dec(v___x_845_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_928_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
uint8_t v_trackZetaDelta_867_; lean_object* v_zetaDeltaSet_868_; lean_object* v_lctx_869_; lean_object* v_localInstances_870_; lean_object* v_defEqCtx_x3f_871_; lean_object* v_synthPendingDepth_872_; lean_object* v_canUnfold_x3f_873_; uint8_t v_univApprox_874_; uint8_t v_inTypeClassResolution_875_; uint8_t v_cacheInferType_876_; uint8_t v___x_877_; lean_object* v_config_879_; 
v_trackZetaDelta_867_ = lean_ctor_get_uint8(v___y_841_, sizeof(void*)*7);
v_zetaDeltaSet_868_ = lean_ctor_get(v___y_841_, 1);
v_lctx_869_ = lean_ctor_get(v___y_841_, 2);
v_localInstances_870_ = lean_ctor_get(v___y_841_, 3);
v_defEqCtx_x3f_871_ = lean_ctor_get(v___y_841_, 4);
v_synthPendingDepth_872_ = lean_ctor_get(v___y_841_, 5);
v_canUnfold_x3f_873_ = lean_ctor_get(v___y_841_, 6);
v_univApprox_874_ = lean_ctor_get_uint8(v___y_841_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_875_ = lean_ctor_get_uint8(v___y_841_, sizeof(void*)*7 + 2);
v_cacheInferType_876_ = lean_ctor_get_uint8(v___y_841_, sizeof(void*)*7 + 3);
v___x_877_ = 1;
if (v_isShared_866_ == 0)
{
v_config_879_ = v___x_865_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_927_, 0, v_foApprox_846_);
lean_ctor_set_uint8(v_reuseFailAlloc_927_, 1, v_ctxApprox_847_);
lean_ctor_set_uint8(v_reuseFailAlloc_927_, 2, v_quasiPatternApprox_848_);
lean_ctor_set_uint8(v_reuseFailAlloc_927_, 3, v_constApprox_849_);
lean_ctor_set_uint8(v_reuseFailAlloc_927_, 4, v_isDefEqStuckEx_850_);
lean_ctor_set_uint8(v_reuseFailAlloc_927_, 5, v_unificationHints_851_);
lean_ctor_set_uint8(v_reuseFailAlloc_927_, 6, v_proofIrrelevance_852_);
lean_ctor_set_uint8(v_reuseFailAlloc_927_, 7, v_assignSyntheticOpaque_853_);
lean_ctor_set_uint8(v_reuseFailAlloc_927_, 8, v_offsetCnstrs_854_);
lean_ctor_set_uint8(v_reuseFailAlloc_927_, 10, v_etaStruct_855_);
lean_ctor_set_uint8(v_reuseFailAlloc_927_, 11, v_univApprox_856_);
lean_ctor_set_uint8(v_reuseFailAlloc_927_, 12, v_iota_857_);
lean_ctor_set_uint8(v_reuseFailAlloc_927_, 13, v_beta_858_);
lean_ctor_set_uint8(v_reuseFailAlloc_927_, 14, v_proj_859_);
lean_ctor_set_uint8(v_reuseFailAlloc_927_, 15, v_zeta_860_);
lean_ctor_set_uint8(v_reuseFailAlloc_927_, 16, v_zetaDelta_861_);
lean_ctor_set_uint8(v_reuseFailAlloc_927_, 17, v_zetaUnused_862_);
lean_ctor_set_uint8(v_reuseFailAlloc_927_, 18, v_zetaHave_863_);
v_config_879_ = v_reuseFailAlloc_927_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
uint64_t v___x_880_; uint64_t v___x_881_; uint64_t v___x_882_; uint64_t v___x_883_; uint64_t v___x_884_; uint64_t v_key_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
lean_ctor_set_uint8(v_config_879_, 9, v___x_877_);
v___x_880_ = l_Lean_Meta_Context_configKey(v___y_841_);
v___x_881_ = 2ULL;
v___x_882_ = lean_uint64_shift_right(v___x_880_, v___x_881_);
v___x_883_ = lean_uint64_shift_left(v___x_882_, v___x_881_);
v___x_884_ = lean_uint64_once(&l_Lean_Meta_injectionCore___lam__0___closed__14, &l_Lean_Meta_injectionCore___lam__0___closed__14_once, _init_l_Lean_Meta_injectionCore___lam__0___closed__14);
v_key_885_ = lean_uint64_lor(v___x_883_, v___x_884_);
v___x_886_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_886_, 0, v_config_879_);
lean_ctor_set_uint64(v___x_886_, sizeof(void*)*1, v_key_885_);
lean_inc(v_canUnfold_x3f_873_);
lean_inc(v_synthPendingDepth_872_);
lean_inc(v_defEqCtx_x3f_871_);
lean_inc_ref(v_localInstances_870_);
lean_inc_ref(v_lctx_869_);
lean_inc(v_zetaDeltaSet_868_);
v___x_887_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_887_, 0, v___x_886_);
lean_ctor_set(v___x_887_, 1, v_zetaDeltaSet_868_);
lean_ctor_set(v___x_887_, 2, v_lctx_869_);
lean_ctor_set(v___x_887_, 3, v_localInstances_870_);
lean_ctor_set(v___x_887_, 4, v_defEqCtx_x3f_871_);
lean_ctor_set(v___x_887_, 5, v_synthPendingDepth_872_);
lean_ctor_set(v___x_887_, 6, v_canUnfold_x3f_873_);
lean_ctor_set_uint8(v___x_887_, sizeof(void*)*7, v_trackZetaDelta_867_);
lean_ctor_set_uint8(v___x_887_, sizeof(void*)*7 + 1, v_univApprox_874_);
lean_ctor_set_uint8(v___x_887_, sizeof(void*)*7 + 2, v_inTypeClassResolution_875_);
lean_ctor_set_uint8(v___x_887_, sizeof(void*)*7 + 3, v_cacheInferType_876_);
v___x_888_ = l_Lean_Meta_mkNoConfusion(v___y_839_, v___y_837_, v___x_887_, v___y_842_, v___y_843_, v___y_844_);
lean_dec_ref(v___x_887_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_890_; lean_object* v_a_891_; uint8_t v___x_892_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc(v_a_889_);
lean_dec_ref(v___x_888_);
lean_inc(v___y_836_);
v___x_890_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_injectionCore_spec__1___redArg(v___y_836_, v___y_843_);
v_a_891_ = lean_ctor_get(v___x_890_, 0);
lean_inc(v_a_891_);
lean_dec_ref(v___x_890_);
v___x_892_ = lean_unbox(v_a_891_);
lean_dec(v_a_891_);
if (v___x_892_ == 0)
{
v___y_696_ = v___y_836_;
v___y_697_ = v___y_838_;
v___y_698_ = v___y_840_;
v___y_699_ = v_a_889_;
v___y_700_ = v___y_841_;
v___y_701_ = v___y_842_;
v___y_702_ = v___y_843_;
v___y_703_ = v___y_844_;
goto v___jp_695_;
}
else
{
lean_object* v___x_893_; 
lean_inc(v___y_844_);
lean_inc_ref(v___y_843_);
lean_inc(v___y_842_);
lean_inc_ref(v___y_841_);
lean_inc(v_a_889_);
v___x_893_ = lean_infer_type(v_a_889_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v_a_894_ = lean_ctor_get(v___x_893_, 0);
lean_inc(v_a_894_);
lean_dec_ref(v___x_893_);
v___x_895_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__0___closed__16, &l_Lean_Meta_injectionCore___lam__0___closed__16_once, _init_l_Lean_Meta_injectionCore___lam__0___closed__16);
lean_inc(v_a_889_);
v___x_896_ = l_Lean_indentExpr(v_a_889_);
v___x_897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_895_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
v___x_898_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__0___closed__18, &l_Lean_Meta_injectionCore___lam__0___closed__18_once, _init_l_Lean_Meta_injectionCore___lam__0___closed__18);
v___x_899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_897_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
v___x_900_ = l_Lean_indentExpr(v_a_894_);
v___x_901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_899_);
lean_ctor_set(v___x_901_, 1, v___x_900_);
lean_inc(v___y_836_);
v___x_902_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__2(v___y_836_, v___x_901_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_dec_ref(v___x_902_);
v___y_696_ = v___y_836_;
v___y_697_ = v___y_838_;
v___y_698_ = v___y_840_;
v___y_699_ = v_a_889_;
v___y_700_ = v___y_841_;
v___y_701_ = v___y_842_;
v___y_702_ = v___y_843_;
v___y_703_ = v___y_844_;
goto v___jp_695_;
}
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_dec(v_a_889_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_836_);
lean_dec(v_fvarId_669_);
lean_dec(v___x_668_);
lean_dec(v_mvarId_667_);
v_a_903_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_902_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_902_);
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
else
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
lean_dec(v_a_889_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_836_);
lean_dec(v_fvarId_669_);
lean_dec(v___x_668_);
lean_dec(v_mvarId_667_);
v_a_911_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v___x_893_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_893_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_911_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
}
else
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_926_; 
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_836_);
lean_dec(v_fvarId_669_);
lean_dec(v___x_668_);
lean_dec(v_mvarId_667_);
v_a_919_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_926_ == 0)
{
v___x_921_ = v___x_888_;
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_888_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_924_; 
if (v_isShared_922_ == 0)
{
v___x_924_ = v___x_921_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_a_919_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
}
}
v___jp_929_:
{
lean_object* v___x_936_; lean_object* v___x_937_; uint8_t v___x_938_; 
v___x_936_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__0___closed__20));
v___x_937_ = lean_unsigned_to_nat(3u);
v___x_938_ = l_Lean_Expr_isAppOfArity(v_type_930_, v___x_936_, v___x_937_);
if (v___x_938_ == 0)
{
lean_object* v___x_939_; lean_object* v___x_940_; 
lean_dec_ref(v_prf_931_);
lean_dec_ref(v_type_930_);
lean_dec_ref(v___x_670_);
lean_dec(v_fvarId_669_);
v___x_939_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__0___closed__24, &l_Lean_Meta_injectionCore___lam__0___closed__24_once, _init_l_Lean_Meta_injectionCore___lam__0___closed__24);
v___x_940_ = l_Lean_Meta_throwTacticEx___redArg(v___x_668_, v_mvarId_667_, v___x_939_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
return v___x_940_;
}
else
{
lean_object* v___x_941_; 
lean_inc(v_mvarId_667_);
v___x_941_ = l_Lean_MVarId_getType(v_mvarId_667_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v_a_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v_a_942_ = lean_ctor_get(v___x_941_, 0);
lean_inc(v_a_942_);
lean_dec_ref(v___x_941_);
v___x_943_ = l_Lean_Expr_appFn_x21(v_type_930_);
v___x_944_ = l_Lean_Expr_appArg_x21(v___x_943_);
lean_dec_ref(v___x_943_);
v___x_945_ = l_Lean_Meta_isConstructorApp_x27_x3f(v___x_944_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v_a_946_ = lean_ctor_get(v___x_945_, 0);
lean_inc(v_a_946_);
lean_dec_ref(v___x_945_);
v___x_947_ = l_Lean_Expr_appArg_x21(v_type_930_);
lean_dec_ref(v_type_930_);
v___x_948_ = l_Lean_Meta_isConstructorApp_x27_x3f(v___x_947_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_948_) == 0)
{
if (lean_obj_tag(v_a_946_) == 1)
{
lean_object* v_a_949_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc(v_a_949_);
lean_dec_ref(v___x_948_);
if (lean_obj_tag(v_a_949_) == 1)
{
lean_object* v_val_950_; lean_object* v_val_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_989_; 
v_val_950_ = lean_ctor_get(v_a_946_, 0);
lean_inc(v_val_950_);
lean_dec_ref(v_a_946_);
v_val_951_ = lean_ctor_get(v_a_949_, 0);
lean_inc(v_val_951_);
lean_dec_ref(v_a_949_);
v___x_952_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__0___closed__25));
v___x_953_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__0___closed__26));
v___x_954_ = l_Lean_Name_mkStr3(v___x_952_, v___x_953_, v___x_670_);
lean_inc(v___x_954_);
v___x_955_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_injectionCore_spec__1___redArg(v___x_954_, v___y_934_);
v_a_956_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_989_ == 0)
{
v___x_958_ = v___x_955_;
v_isShared_959_ = v_isSharedCheck_989_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_955_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_989_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
uint8_t v___x_960_; 
v___x_960_ = lean_unbox(v_a_956_);
lean_dec(v_a_956_);
if (v___x_960_ == 0)
{
lean_del_object(v___x_958_);
v___y_836_ = v___x_954_;
v___y_837_ = v_prf_931_;
v___y_838_ = v_val_950_;
v___y_839_ = v_a_942_;
v___y_840_ = v_val_951_;
v___y_841_ = v___y_932_;
v___y_842_ = v___y_933_;
v___y_843_ = v___y_934_;
v___y_844_ = v___y_935_;
goto v___jp_835_;
}
else
{
lean_object* v___x_961_; 
lean_inc(v___y_935_);
lean_inc_ref(v___y_934_);
lean_inc(v___y_933_);
lean_inc_ref(v___y_932_);
lean_inc_ref(v_prf_931_);
v___x_961_ = lean_infer_type(v_prf_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_a_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_969_; 
v_a_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_a_962_);
lean_dec_ref(v___x_961_);
v___x_963_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__0___closed__28, &l_Lean_Meta_injectionCore___lam__0___closed__28_once, _init_l_Lean_Meta_injectionCore___lam__0___closed__28);
v___x_964_ = l_Lean_MessageData_ofExpr(v_a_962_);
v___x_965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_963_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___x_966_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__0___closed__30, &l_Lean_Meta_injectionCore___lam__0___closed__30_once, _init_l_Lean_Meta_injectionCore___lam__0___closed__30);
v___x_967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_965_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
lean_inc(v_mvarId_667_);
if (v_isShared_959_ == 0)
{
lean_ctor_set_tag(v___x_958_, 1);
lean_ctor_set(v___x_958_, 0, v_mvarId_667_);
v___x_969_ = v___x_958_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_mvarId_667_);
v___x_969_ = v_reuseFailAlloc_980_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_967_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
lean_inc(v___x_954_);
v___x_971_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__2(v___x_954_, v___x_970_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_dec_ref(v___x_971_);
v___y_836_ = v___x_954_;
v___y_837_ = v_prf_931_;
v___y_838_ = v_val_950_;
v___y_839_ = v_a_942_;
v___y_840_ = v_val_951_;
v___y_841_ = v___y_932_;
v___y_842_ = v___y_933_;
v___y_843_ = v___y_934_;
v___y_844_ = v___y_935_;
goto v___jp_835_;
}
else
{
lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_979_; 
lean_dec(v___x_954_);
lean_dec(v_val_951_);
lean_dec(v_val_950_);
lean_dec(v_a_942_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec_ref(v_prf_931_);
lean_dec(v_fvarId_669_);
lean_dec(v___x_668_);
lean_dec(v_mvarId_667_);
v_a_972_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_979_ == 0)
{
v___x_974_ = v___x_971_;
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v___x_971_);
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
else
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_988_; 
lean_del_object(v___x_958_);
lean_dec(v___x_954_);
lean_dec(v_val_951_);
lean_dec(v_val_950_);
lean_dec(v_a_942_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec_ref(v_prf_931_);
lean_dec(v_fvarId_669_);
lean_dec(v___x_668_);
lean_dec(v_mvarId_667_);
v_a_981_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_988_ == 0)
{
v___x_983_ = v___x_961_;
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_961_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_981_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_a_946_);
lean_dec(v_a_949_);
lean_dec(v_a_942_);
lean_dec_ref(v_prf_931_);
lean_dec_ref(v___x_670_);
lean_dec(v_fvarId_669_);
v___y_684_ = v___y_932_;
v___y_685_ = v___y_933_;
v___y_686_ = v___y_934_;
v___y_687_ = v___y_935_;
goto v___jp_683_;
}
}
else
{
lean_dec_ref(v___x_948_);
lean_dec(v_a_946_);
lean_dec(v_a_942_);
lean_dec_ref(v_prf_931_);
lean_dec_ref(v___x_670_);
lean_dec(v_fvarId_669_);
v___y_684_ = v___y_932_;
v___y_685_ = v___y_933_;
v___y_686_ = v___y_934_;
v___y_687_ = v___y_935_;
goto v___jp_683_;
}
}
else
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
lean_dec(v_a_946_);
lean_dec(v_a_942_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec_ref(v_prf_931_);
lean_dec_ref(v___x_670_);
lean_dec(v_fvarId_669_);
lean_dec(v___x_668_);
lean_dec(v_mvarId_667_);
v_a_990_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_948_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_948_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_a_990_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
else
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1005_; 
lean_dec(v_a_942_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec_ref(v_prf_931_);
lean_dec_ref(v_type_930_);
lean_dec_ref(v___x_670_);
lean_dec(v_fvarId_669_);
lean_dec(v___x_668_);
lean_dec(v_mvarId_667_);
v_a_998_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_1000_ = v___x_945_;
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_945_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1003_; 
if (v_isShared_1001_ == 0)
{
v___x_1003_ = v___x_1000_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_998_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec_ref(v_prf_931_);
lean_dec_ref(v_type_930_);
lean_dec_ref(v___x_670_);
lean_dec(v_fvarId_669_);
lean_dec(v___x_668_);
lean_dec(v_mvarId_667_);
v_a_1006_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_941_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_941_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___lam__0___boxed(lean_object* v_mvarId_1086_, lean_object* v___x_1087_, lean_object* v_fvarId_1088_, lean_object* v___x_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Lean_Meta_injectionCore___lam__0(v_mvarId_1086_, v___x_1087_, v_fvarId_1088_, v___x_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore(lean_object* v_mvarId_1099_, lean_object* v_fvarId_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___f_1108_; lean_object* v___x_1109_; 
v___x_1106_ = ((lean_object*)(l_Lean_Meta_injectionCore___closed__0));
v___x_1107_ = ((lean_object*)(l_Lean_Meta_injectionCore___closed__1));
lean_inc(v_mvarId_1099_);
v___f_1108_ = lean_alloc_closure((void*)(l_Lean_Meta_injectionCore___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1108_, 0, v_mvarId_1099_);
lean_closure_set(v___f_1108_, 1, v___x_1107_);
lean_closure_set(v___f_1108_, 2, v_fvarId_1100_);
lean_closure_set(v___f_1108_, 3, v___x_1106_);
v___x_1109_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__3___redArg(v_mvarId_1099_, v___f_1108_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___boxed(lean_object* v_mvarId_1110_, lean_object* v_fvarId_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lean_Meta_injectionCore(v_mvarId_1110_, v_fvarId_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
lean_dec(v_a_1115_);
lean_dec_ref(v_a_1114_);
lean_dec(v_a_1113_);
lean_dec_ref(v_a_1112_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0(lean_object* v_mvarId_1118_, lean_object* v_val_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(v_mvarId_1118_, v_val_1119_, v___y_1121_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___boxed(lean_object* v_mvarId_1126_, lean_object* v_val_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0(v_mvarId_1126_, v_val_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0(lean_object* v_00_u03b2_1134_, lean_object* v_x_1135_, lean_object* v_x_1136_, lean_object* v_x_1137_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0___redArg(v_x_1135_, v_x_1136_, v_x_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1139_, lean_object* v_x_1140_, size_t v_x_1141_, size_t v_x_1142_, lean_object* v_x_1143_, lean_object* v_x_1144_){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3___redArg(v_x_1140_, v_x_1141_, v_x_1142_, v_x_1143_, v_x_1144_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1146_, lean_object* v_x_1147_, lean_object* v_x_1148_, lean_object* v_x_1149_, lean_object* v_x_1150_, lean_object* v_x_1151_){
_start:
{
size_t v_x_16944__boxed_1152_; size_t v_x_16945__boxed_1153_; lean_object* v_res_1154_; 
v_x_16944__boxed_1152_ = lean_unbox_usize(v_x_1148_);
lean_dec(v_x_1148_);
v_x_16945__boxed_1153_ = lean_unbox_usize(v_x_1149_);
lean_dec(v_x_1149_);
v_res_1154_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3(v_00_u03b2_1146_, v_x_1147_, v_x_16944__boxed_1152_, v_x_16945__boxed_1153_, v_x_1150_, v_x_1151_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3_spec__6(lean_object* v_00_u03b2_1155_, lean_object* v_n_1156_, lean_object* v_k_1157_, lean_object* v_v_1158_){
_start:
{
lean_object* v___x_1159_; 
v___x_1159_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3_spec__6___redArg(v_n_1156_, v_k_1157_, v_v_1158_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3_spec__7(lean_object* v_00_u03b2_1160_, size_t v_depth_1161_, lean_object* v_keys_1162_, lean_object* v_vals_1163_, lean_object* v_heq_1164_, lean_object* v_i_1165_, lean_object* v_entries_1166_){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3_spec__7___redArg(v_depth_1161_, v_keys_1162_, v_vals_1163_, v_i_1165_, v_entries_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3_spec__7___boxed(lean_object* v_00_u03b2_1168_, lean_object* v_depth_1169_, lean_object* v_keys_1170_, lean_object* v_vals_1171_, lean_object* v_heq_1172_, lean_object* v_i_1173_, lean_object* v_entries_1174_){
_start:
{
size_t v_depth_boxed_1175_; lean_object* v_res_1176_; 
v_depth_boxed_1175_ = lean_unbox_usize(v_depth_1169_);
lean_dec(v_depth_1169_);
v_res_1176_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3_spec__7(v_00_u03b2_1168_, v_depth_boxed_1175_, v_keys_1170_, v_vals_1171_, v_heq_1172_, v_i_1173_, v_entries_1174_);
lean_dec_ref(v_vals_1171_);
lean_dec_ref(v_keys_1170_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3_spec__6_spec__7(lean_object* v_00_u03b2_1177_, lean_object* v_x_1178_, lean_object* v_x_1179_, lean_object* v_x_1180_, lean_object* v_x_1181_){
_start:
{
lean_object* v___x_1182_; 
v___x_1182_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__3_spec__6_spec__7___redArg(v_x_1178_, v_x_1179_, v_x_1180_, v_x_1181_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorIdx(lean_object* v_x_1183_){
_start:
{
if (lean_obj_tag(v_x_1183_) == 0)
{
lean_object* v___x_1184_; 
v___x_1184_ = lean_unsigned_to_nat(0u);
return v___x_1184_;
}
else
{
lean_object* v___x_1185_; 
v___x_1185_ = lean_unsigned_to_nat(1u);
return v___x_1185_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorIdx___boxed(lean_object* v_x_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Lean_Meta_InjectionResult_ctorIdx(v_x_1186_);
lean_dec(v_x_1186_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorElim___redArg(lean_object* v_t_1188_, lean_object* v_k_1189_){
_start:
{
if (lean_obj_tag(v_t_1188_) == 0)
{
return v_k_1189_;
}
else
{
lean_object* v_mvarId_1190_; lean_object* v_newEqs_1191_; lean_object* v_remainingNames_1192_; lean_object* v___x_1193_; 
v_mvarId_1190_ = lean_ctor_get(v_t_1188_, 0);
lean_inc(v_mvarId_1190_);
v_newEqs_1191_ = lean_ctor_get(v_t_1188_, 1);
lean_inc_ref(v_newEqs_1191_);
v_remainingNames_1192_ = lean_ctor_get(v_t_1188_, 2);
lean_inc(v_remainingNames_1192_);
lean_dec_ref(v_t_1188_);
v___x_1193_ = lean_apply_3(v_k_1189_, v_mvarId_1190_, v_newEqs_1191_, v_remainingNames_1192_);
return v___x_1193_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorElim(lean_object* v_motive_1194_, lean_object* v_ctorIdx_1195_, lean_object* v_t_1196_, lean_object* v_h_1197_, lean_object* v_k_1198_){
_start:
{
lean_object* v___x_1199_; 
v___x_1199_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_1196_, v_k_1198_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorElim___boxed(lean_object* v_motive_1200_, lean_object* v_ctorIdx_1201_, lean_object* v_t_1202_, lean_object* v_h_1203_, lean_object* v_k_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Lean_Meta_InjectionResult_ctorElim(v_motive_1200_, v_ctorIdx_1201_, v_t_1202_, v_h_1203_, v_k_1204_);
lean_dec(v_ctorIdx_1201_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_solved_elim___redArg(lean_object* v_t_1206_, lean_object* v_solved_1207_){
_start:
{
lean_object* v___x_1208_; 
v___x_1208_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_1206_, v_solved_1207_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_solved_elim(lean_object* v_motive_1209_, lean_object* v_t_1210_, lean_object* v_h_1211_, lean_object* v_solved_1212_){
_start:
{
lean_object* v___x_1213_; 
v___x_1213_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_1210_, v_solved_1212_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_subgoal_elim___redArg(lean_object* v_t_1214_, lean_object* v_subgoal_1215_){
_start:
{
lean_object* v___x_1216_; 
v___x_1216_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_1214_, v_subgoal_1215_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_subgoal_elim(lean_object* v_motive_1217_, lean_object* v_t_1218_, lean_object* v_h_1219_, lean_object* v_subgoal_1220_){
_start:
{
lean_object* v___x_1221_; 
v___x_1221_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_1218_, v_subgoal_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go(uint8_t v_tryToClear_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_){
_start:
{
lean_object* v_zero_1232_; uint8_t v_isZero_1233_; 
v_zero_1232_ = lean_unsigned_to_nat(0u);
v_isZero_1233_ = lean_nat_dec_eq(v_a_1223_, v_zero_1232_);
if (v_isZero_1233_ == 1)
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
lean_dec(v_a_1223_);
v___x_1234_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1234_, 0, v_a_1224_);
lean_ctor_set(v___x_1234_, 1, v_a_1225_);
lean_ctor_set(v___x_1234_, 2, v_a_1226_);
v___x_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1234_);
return v___x_1235_;
}
else
{
lean_object* v_one_1236_; lean_object* v_n_1237_; 
v_one_1236_ = lean_unsigned_to_nat(1u);
v_n_1237_ = lean_nat_sub(v_a_1223_, v_one_1236_);
lean_dec(v_a_1223_);
if (lean_obj_tag(v_a_1226_) == 0)
{
lean_object* v___x_1238_; 
v___x_1238_ = l_Lean_Meta_intro1Core(v_a_1224_, v_isZero_1233_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; lean_object* v_fst_1240_; lean_object* v_snd_1241_; lean_object* v___x_1242_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1239_);
lean_dec_ref(v___x_1238_);
v_fst_1240_ = lean_ctor_get(v_a_1239_, 0);
lean_inc(v_fst_1240_);
v_snd_1241_ = lean_ctor_get(v_a_1239_, 1);
lean_inc(v_snd_1241_);
lean_dec(v_a_1239_);
v___x_1242_ = l_Lean_Meta_heqToEq(v_snd_1241_, v_fst_1240_, v_tryToClear_1222_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v_a_1243_; lean_object* v_fst_1244_; lean_object* v_snd_1245_; lean_object* v___x_1246_; 
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
lean_inc(v_a_1243_);
lean_dec_ref(v___x_1242_);
v_fst_1244_ = lean_ctor_get(v_a_1243_, 0);
lean_inc(v_fst_1244_);
v_snd_1245_ = lean_ctor_get(v_a_1243_, 1);
lean_inc(v_snd_1245_);
lean_dec(v_a_1243_);
v___x_1246_ = lean_array_push(v_a_1225_, v_fst_1244_);
v_a_1223_ = v_n_1237_;
v_a_1224_ = v_snd_1245_;
v_a_1225_ = v___x_1246_;
goto _start;
}
else
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
lean_dec(v_n_1237_);
lean_dec_ref(v_a_1225_);
v_a_1248_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v___x_1242_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1242_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1248_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
else
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
lean_dec(v_n_1237_);
lean_dec_ref(v_a_1225_);
v_a_1256_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1238_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1238_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1256_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
else
{
lean_object* v_head_1264_; lean_object* v_tail_1265_; lean_object* v___x_1266_; 
v_head_1264_ = lean_ctor_get(v_a_1226_, 0);
lean_inc(v_head_1264_);
v_tail_1265_ = lean_ctor_get(v_a_1226_, 1);
lean_inc(v_tail_1265_);
lean_dec_ref(v_a_1226_);
v___x_1266_ = l_Lean_MVarId_intro(v_a_1224_, v_head_1264_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v_a_1267_; lean_object* v_fst_1268_; lean_object* v_snd_1269_; lean_object* v___x_1270_; 
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_a_1267_);
lean_dec_ref(v___x_1266_);
v_fst_1268_ = lean_ctor_get(v_a_1267_, 0);
lean_inc(v_fst_1268_);
v_snd_1269_ = lean_ctor_get(v_a_1267_, 1);
lean_inc(v_snd_1269_);
lean_dec(v_a_1267_);
v___x_1270_ = l_Lean_Meta_heqToEq(v_snd_1269_, v_fst_1268_, v_tryToClear_1222_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v_a_1271_; lean_object* v_fst_1272_; lean_object* v_snd_1273_; lean_object* v___x_1274_; 
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_a_1271_);
lean_dec_ref(v___x_1270_);
v_fst_1272_ = lean_ctor_get(v_a_1271_, 0);
lean_inc(v_fst_1272_);
v_snd_1273_ = lean_ctor_get(v_a_1271_, 1);
lean_inc(v_snd_1273_);
lean_dec(v_a_1271_);
v___x_1274_ = lean_array_push(v_a_1225_, v_fst_1272_);
v_a_1223_ = v_n_1237_;
v_a_1224_ = v_snd_1273_;
v_a_1225_ = v___x_1274_;
v_a_1226_ = v_tail_1265_;
goto _start;
}
else
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
lean_dec(v_tail_1265_);
lean_dec(v_n_1237_);
lean_dec_ref(v_a_1225_);
v_a_1276_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v___x_1270_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1270_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
lean_dec(v_tail_1265_);
lean_dec(v_n_1237_);
lean_dec_ref(v_a_1225_);
v_a_1284_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1266_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1266_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go___boxed(lean_object* v_tryToClear_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_){
_start:
{
uint8_t v_tryToClear_boxed_1302_; lean_object* v_res_1303_; 
v_tryToClear_boxed_1302_ = lean_unbox(v_tryToClear_1292_);
v_res_1303_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go(v_tryToClear_boxed_1302_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
lean_dec(v_a_1298_);
lean_dec_ref(v_a_1297_);
return v_res_1303_;
}
}
static lean_object* _init_l_Lean_Meta_injectionIntro___closed__3(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__2));
v___x_1312_ = l_Lean_stringToMessageData(v___x_1311_);
return v___x_1312_;
}
}
static lean_object* _init_l_Lean_Meta_injectionIntro___closed__5(void){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__4));
v___x_1315_ = l_Lean_stringToMessageData(v___x_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro(lean_object* v_mvarId_1316_, lean_object* v_numEqs_1317_, lean_object* v_newNames_1318_, uint8_t v_tryToClear_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_){
_start:
{
lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v_cls_1332_; lean_object* v___x_1333_; lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1359_; 
v_cls_1332_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__1));
v___x_1333_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_injectionCore_spec__1___redArg(v_cls_1332_, v_a_1322_);
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1336_ = v___x_1333_;
v_isShared_1337_ = v_isSharedCheck_1359_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1333_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1359_;
goto v_resetjp_1335_;
}
v___jp_1325_:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1330_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__0));
v___x_1331_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go(v_tryToClear_1319_, v_numEqs_1317_, v_mvarId_1316_, v___x_1330_, v_newNames_1318_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
return v___x_1331_;
}
v_resetjp_1335_:
{
uint8_t v___x_1338_; 
v___x_1338_ = lean_unbox(v_a_1334_);
lean_dec(v_a_1334_);
if (v___x_1338_ == 0)
{
lean_del_object(v___x_1336_);
v___y_1326_ = v_a_1320_;
v___y_1327_ = v_a_1321_;
v___y_1328_ = v_a_1322_;
v___y_1329_ = v_a_1323_;
goto v___jp_1325_;
}
else
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1342_; 
v___x_1339_ = lean_obj_once(&l_Lean_Meta_injectionIntro___closed__3, &l_Lean_Meta_injectionIntro___closed__3_once, _init_l_Lean_Meta_injectionIntro___closed__3);
lean_inc(v_numEqs_1317_);
v___x_1340_ = l_Nat_reprFast(v_numEqs_1317_);
if (v_isShared_1337_ == 0)
{
lean_ctor_set_tag(v___x_1336_, 3);
lean_ctor_set(v___x_1336_, 0, v___x_1340_);
v___x_1342_ = v___x_1336_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v___x_1340_);
v___x_1342_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1343_ = l_Lean_MessageData_ofFormat(v___x_1342_);
v___x_1344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1339_);
lean_ctor_set(v___x_1344_, 1, v___x_1343_);
v___x_1345_ = lean_obj_once(&l_Lean_Meta_injectionIntro___closed__5, &l_Lean_Meta_injectionIntro___closed__5_once, _init_l_Lean_Meta_injectionIntro___closed__5);
v___x_1346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1344_);
lean_ctor_set(v___x_1346_, 1, v___x_1345_);
lean_inc(v_mvarId_1316_);
v___x_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1347_, 0, v_mvarId_1316_);
v___x_1348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1346_);
lean_ctor_set(v___x_1348_, 1, v___x_1347_);
v___x_1349_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__2(v_cls_1332_, v___x_1348_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_dec_ref(v___x_1349_);
v___y_1326_ = v_a_1320_;
v___y_1327_ = v_a_1321_;
v___y_1328_ = v_a_1322_;
v___y_1329_ = v_a_1323_;
goto v___jp_1325_;
}
else
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
lean_dec(v_newNames_1318_);
lean_dec(v_numEqs_1317_);
lean_dec(v_mvarId_1316_);
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1352_ = v___x_1349_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1349_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1350_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro___boxed(lean_object* v_mvarId_1360_, lean_object* v_numEqs_1361_, lean_object* v_newNames_1362_, lean_object* v_tryToClear_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_){
_start:
{
uint8_t v_tryToClear_boxed_1369_; lean_object* v_res_1370_; 
v_tryToClear_boxed_1369_ = lean_unbox(v_tryToClear_1363_);
v_res_1370_ = l_Lean_Meta_injectionIntro(v_mvarId_1360_, v_numEqs_1361_, v_newNames_1362_, v_tryToClear_boxed_1369_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injection(lean_object* v_mvarId_1371_, lean_object* v_fvarId_1372_, lean_object* v_newNames_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_){
_start:
{
lean_object* v___x_1379_; 
v___x_1379_ = l_Lean_Meta_injectionCore(v_mvarId_1371_, v_fvarId_1372_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1392_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1382_ = v___x_1379_;
v_isShared_1383_ = v_isSharedCheck_1392_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1379_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1392_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
if (lean_obj_tag(v_a_1380_) == 0)
{
lean_object* v___x_1384_; lean_object* v___x_1386_; 
lean_dec(v_newNames_1373_);
v___x_1384_ = lean_box(0);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 0, v___x_1384_);
v___x_1386_ = v___x_1382_;
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
else
{
lean_object* v_mvarId_1388_; lean_object* v_numNewEqs_1389_; uint8_t v___x_1390_; lean_object* v___x_1391_; 
lean_del_object(v___x_1382_);
v_mvarId_1388_ = lean_ctor_get(v_a_1380_, 0);
lean_inc(v_mvarId_1388_);
v_numNewEqs_1389_ = lean_ctor_get(v_a_1380_, 1);
lean_inc(v_numNewEqs_1389_);
lean_dec_ref(v_a_1380_);
v___x_1390_ = 1;
v___x_1391_ = l_Lean_Meta_injectionIntro(v_mvarId_1388_, v_numNewEqs_1389_, v_newNames_1373_, v___x_1390_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
return v___x_1391_;
}
}
}
else
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
lean_dec(v_newNames_1373_);
v_a_1393_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1395_ = v___x_1379_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1379_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
if (v_isShared_1396_ == 0)
{
v___x_1398_ = v___x_1395_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_a_1393_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injection___boxed(lean_object* v_mvarId_1401_, lean_object* v_fvarId_1402_, lean_object* v_newNames_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l_Lean_Meta_injection(v_mvarId_1401_, v_fvarId_1402_, v_newNames_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_);
lean_dec(v_a_1407_);
lean_dec_ref(v_a_1406_);
lean_dec(v_a_1405_);
lean_dec_ref(v_a_1404_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorIdx(lean_object* v_x_1410_){
_start:
{
if (lean_obj_tag(v_x_1410_) == 0)
{
lean_object* v___x_1411_; 
v___x_1411_ = lean_unsigned_to_nat(0u);
return v___x_1411_;
}
else
{
lean_object* v___x_1412_; 
v___x_1412_ = lean_unsigned_to_nat(1u);
return v___x_1412_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorIdx___boxed(lean_object* v_x_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l_Lean_Meta_InjectionsResult_ctorIdx(v_x_1413_);
lean_dec(v_x_1413_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorElim___redArg(lean_object* v_t_1415_, lean_object* v_k_1416_){
_start:
{
if (lean_obj_tag(v_t_1415_) == 0)
{
return v_k_1416_;
}
else
{
lean_object* v_mvarId_1417_; lean_object* v_remainingNames_1418_; lean_object* v_forbidden_1419_; lean_object* v___x_1420_; 
v_mvarId_1417_ = lean_ctor_get(v_t_1415_, 0);
lean_inc(v_mvarId_1417_);
v_remainingNames_1418_ = lean_ctor_get(v_t_1415_, 1);
lean_inc(v_remainingNames_1418_);
v_forbidden_1419_ = lean_ctor_get(v_t_1415_, 2);
lean_inc(v_forbidden_1419_);
lean_dec_ref(v_t_1415_);
v___x_1420_ = lean_apply_3(v_k_1416_, v_mvarId_1417_, v_remainingNames_1418_, v_forbidden_1419_);
return v___x_1420_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorElim(lean_object* v_motive_1421_, lean_object* v_ctorIdx_1422_, lean_object* v_t_1423_, lean_object* v_h_1424_, lean_object* v_k_1425_){
_start:
{
lean_object* v___x_1426_; 
v___x_1426_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1423_, v_k_1425_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorElim___boxed(lean_object* v_motive_1427_, lean_object* v_ctorIdx_1428_, lean_object* v_t_1429_, lean_object* v_h_1430_, lean_object* v_k_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_Lean_Meta_InjectionsResult_ctorElim(v_motive_1427_, v_ctorIdx_1428_, v_t_1429_, v_h_1430_, v_k_1431_);
lean_dec(v_ctorIdx_1428_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_solved_elim___redArg(lean_object* v_t_1433_, lean_object* v_solved_1434_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1433_, v_solved_1434_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_solved_elim(lean_object* v_motive_1436_, lean_object* v_t_1437_, lean_object* v_h_1438_, lean_object* v_solved_1439_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1437_, v_solved_1439_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_subgoal_elim___redArg(lean_object* v_t_1441_, lean_object* v_subgoal_1442_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1441_, v_subgoal_1442_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_subgoal_elim(lean_object* v_motive_1444_, lean_object* v_t_1445_, lean_object* v_h_1446_, lean_object* v_subgoal_1447_){
_start:
{
lean_object* v___x_1448_; 
v___x_1448_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1445_, v_subgoal_1447_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(lean_object* v_x_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = l_Lean_Meta_saveState___redArg(v___y_1451_, v___y_1453_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v_a_1456_; lean_object* v___x_1457_; 
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_a_1456_);
lean_dec_ref(v___x_1455_);
lean_inc(v___y_1453_);
lean_inc_ref(v___y_1452_);
lean_inc(v___y_1451_);
lean_inc_ref(v___y_1450_);
v___x_1457_ = lean_apply_5(v_x_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, lean_box(0));
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_dec(v_a_1456_);
return v___x_1457_;
}
else
{
lean_object* v_a_1458_; uint8_t v___y_1460_; uint8_t v___x_1478_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_a_1458_);
v___x_1478_ = l_Lean_Exception_isInterrupt(v_a_1458_);
if (v___x_1478_ == 0)
{
uint8_t v___x_1479_; 
lean_inc(v_a_1458_);
v___x_1479_ = l_Lean_Exception_isRuntime(v_a_1458_);
v___y_1460_ = v___x_1479_;
goto v___jp_1459_;
}
else
{
v___y_1460_ = v___x_1478_;
goto v___jp_1459_;
}
v___jp_1459_:
{
if (v___y_1460_ == 0)
{
lean_object* v___x_1461_; 
lean_dec_ref(v___x_1457_);
v___x_1461_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1456_, v___y_1451_, v___y_1453_);
lean_dec(v_a_1456_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1468_ == 0)
{
lean_object* v_unused_1469_; 
v_unused_1469_ = lean_ctor_get(v___x_1461_, 0);
lean_dec(v_unused_1469_);
v___x_1463_ = v___x_1461_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_dec(v___x_1461_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
lean_ctor_set_tag(v___x_1463_, 1);
lean_ctor_set(v___x_1463_, 0, v_a_1458_);
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1458_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
else
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
lean_dec(v_a_1458_);
v_a_1470_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___x_1461_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1461_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1470_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
else
{
lean_dec(v_a_1458_);
lean_dec(v_a_1456_);
return v___x_1457_;
}
}
}
}
else
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
lean_dec_ref(v_x_1449_);
v_a_1480_ = lean_ctor_get(v___x_1455_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1455_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1455_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg___boxed(lean_object* v_x_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(v_x_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1(lean_object* v_00_u03b1_1495_, lean_object* v_x_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(v_x_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___boxed(lean_object* v_00_u03b1_1503_, lean_object* v_x_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1(v_00_u03b1_1503_, v_x_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
return v_res_1510_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(lean_object* v_k_1511_, lean_object* v_t_1512_){
_start:
{
if (lean_obj_tag(v_t_1512_) == 0)
{
lean_object* v_k_1513_; lean_object* v_l_1514_; lean_object* v_r_1515_; uint8_t v___x_1516_; 
v_k_1513_ = lean_ctor_get(v_t_1512_, 1);
v_l_1514_ = lean_ctor_get(v_t_1512_, 3);
v_r_1515_ = lean_ctor_get(v_t_1512_, 4);
v___x_1516_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1511_, v_k_1513_);
switch(v___x_1516_)
{
case 0:
{
v_t_1512_ = v_l_1514_;
goto _start;
}
case 1:
{
uint8_t v___x_1518_; 
v___x_1518_ = 1;
return v___x_1518_;
}
default: 
{
v_t_1512_ = v_r_1515_;
goto _start;
}
}
}
else
{
uint8_t v___x_1520_; 
v___x_1520_ = 0;
return v___x_1520_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg___boxed(lean_object* v_k_1521_, lean_object* v_t_1522_){
_start:
{
uint8_t v_res_1523_; lean_object* v_r_1524_; 
v_res_1523_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(v_k_1521_, v_t_1522_);
lean_dec(v_t_1522_);
lean_dec(v_k_1521_);
v_r_1524_ = lean_box(v_res_1523_);
return v_r_1524_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4(void){
_start:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1531_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__3));
v___x_1532_ = l_Lean_MessageData_ofFormat(v___x_1531_);
return v___x_1532_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5(void){
_start:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1533_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4, &l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4_once, _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4);
v___x_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1533_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0___boxed(lean_object* v_mvarId_1535_, lean_object* v_head_1536_, lean_object* v_newNames_1537_, lean_object* v_tail_1538_, lean_object* v_forbidden_1539_, lean_object* v_n_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0(v_mvarId_1535_, v_head_1536_, v_newNames_1537_, v_tail_1538_, v_forbidden_1539_, v_n_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go(lean_object* v_depth_1547_, lean_object* v_fvarIds_1548_, lean_object* v_mvarId_1549_, lean_object* v_newNames_1550_, lean_object* v_forbidden_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_){
_start:
{
lean_object* v_zero_1557_; uint8_t v_isZero_1558_; 
v_zero_1557_ = lean_unsigned_to_nat(0u);
v_isZero_1558_ = lean_nat_dec_eq(v_depth_1547_, v_zero_1557_);
if (v_isZero_1558_ == 1)
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
lean_dec(v_forbidden_1551_);
lean_dec(v_newNames_1550_);
lean_dec(v_fvarIds_1548_);
lean_dec(v_depth_1547_);
v___x_1559_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__1));
v___x_1560_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5, &l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5_once, _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5);
v___x_1561_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1559_, v_mvarId_1549_, v___x_1560_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
return v___x_1561_;
}
else
{
if (lean_obj_tag(v_fvarIds_1548_) == 0)
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
lean_dec(v_depth_1547_);
v___x_1562_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1562_, 0, v_mvarId_1549_);
lean_ctor_set(v___x_1562_, 1, v_newNames_1550_);
lean_ctor_set(v___x_1562_, 2, v_forbidden_1551_);
v___x_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
return v___x_1563_;
}
else
{
lean_object* v_head_1564_; lean_object* v_tail_1565_; lean_object* v_one_1566_; lean_object* v_n_1567_; lean_object* v___x_1568_; lean_object* v___y_1570_; uint8_t v___y_1571_; uint8_t v___x_1573_; 
v_head_1564_ = lean_ctor_get(v_fvarIds_1548_, 0);
lean_inc(v_head_1564_);
v_tail_1565_ = lean_ctor_get(v_fvarIds_1548_, 1);
lean_inc(v_tail_1565_);
lean_dec_ref(v_fvarIds_1548_);
v_one_1566_ = lean_unsigned_to_nat(1u);
v_n_1567_ = lean_nat_sub(v_depth_1547_, v_one_1566_);
lean_dec(v_depth_1547_);
v___x_1568_ = lean_nat_add(v_n_1567_, v_one_1566_);
v___x_1573_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(v_head_1564_, v_forbidden_1551_);
if (v___x_1573_ == 0)
{
lean_object* v___x_1574_; 
lean_inc(v_head_1564_);
v___x_1574_ = l_Lean_FVarId_getType___redArg(v_head_1564_, v_a_1552_, v_a_1554_, v_a_1555_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v_a_1575_; lean_object* v___x_1576_; 
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_a_1575_);
lean_dec_ref(v___x_1574_);
v___x_1576_ = l_Lean_Meta_matchEqHEq_x3f(v_a_1575_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v_a_1577_; 
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
lean_inc(v_a_1577_);
lean_dec_ref(v___x_1576_);
if (lean_obj_tag(v_a_1577_) == 1)
{
lean_object* v_val_1578_; lean_object* v_snd_1579_; lean_object* v_fst_1580_; lean_object* v_snd_1581_; lean_object* v___x_1582_; 
v_val_1578_ = lean_ctor_get(v_a_1577_, 0);
lean_inc(v_val_1578_);
lean_dec_ref(v_a_1577_);
v_snd_1579_ = lean_ctor_get(v_val_1578_, 1);
lean_inc(v_snd_1579_);
lean_dec(v_val_1578_);
v_fst_1580_ = lean_ctor_get(v_snd_1579_, 0);
lean_inc(v_fst_1580_);
v_snd_1581_ = lean_ctor_get(v_snd_1579_, 1);
lean_inc(v_snd_1581_);
lean_dec(v_snd_1579_);
lean_inc(v_a_1555_);
lean_inc_ref(v_a_1554_);
lean_inc(v_a_1553_);
lean_inc_ref(v_a_1552_);
v___x_1582_ = lean_whnf(v_fst_1580_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1584_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1583_);
lean_dec_ref(v___x_1582_);
lean_inc(v_a_1555_);
lean_inc_ref(v_a_1554_);
lean_inc(v_a_1553_);
lean_inc_ref(v_a_1552_);
v___x_1584_ = lean_whnf(v_snd_1581_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___f_1586_; uint8_t v___y_1588_; uint8_t v___x_1594_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref(v___x_1584_);
lean_inc(v_forbidden_1551_);
lean_inc(v_tail_1565_);
lean_inc(v_newNames_1550_);
lean_inc(v_mvarId_1549_);
v___f_1586_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0___boxed), 11, 6);
lean_closure_set(v___f_1586_, 0, v_mvarId_1549_);
lean_closure_set(v___f_1586_, 1, v_head_1564_);
lean_closure_set(v___f_1586_, 2, v_newNames_1550_);
lean_closure_set(v___f_1586_, 3, v_tail_1565_);
lean_closure_set(v___f_1586_, 4, v_forbidden_1551_);
lean_closure_set(v___f_1586_, 5, v_n_1567_);
v___x_1594_ = l_Lean_Expr_isRawNatLit(v_a_1583_);
lean_dec(v_a_1583_);
if (v___x_1594_ == 0)
{
lean_dec(v_a_1585_);
v___y_1588_ = v___x_1594_;
goto v___jp_1587_;
}
else
{
uint8_t v___x_1595_; 
v___x_1595_ = l_Lean_Expr_isRawNatLit(v_a_1585_);
lean_dec(v_a_1585_);
v___y_1588_ = v___x_1595_;
goto v___jp_1587_;
}
v___jp_1587_:
{
if (v___y_1588_ == 0)
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(v___f_1586_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_dec(v___x_1568_);
lean_dec(v_tail_1565_);
lean_dec(v_forbidden_1551_);
lean_dec(v_newNames_1550_);
lean_dec(v_mvarId_1549_);
return v___x_1589_;
}
else
{
lean_object* v_a_1590_; uint8_t v___x_1591_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1590_);
v___x_1591_ = l_Lean_Exception_isInterrupt(v_a_1590_);
if (v___x_1591_ == 0)
{
uint8_t v___x_1592_; 
v___x_1592_ = l_Lean_Exception_isRuntime(v_a_1590_);
v___y_1570_ = v___x_1589_;
v___y_1571_ = v___x_1592_;
goto v___jp_1569_;
}
else
{
lean_dec(v_a_1590_);
v___y_1570_ = v___x_1589_;
v___y_1571_ = v___x_1591_;
goto v___jp_1569_;
}
}
}
else
{
lean_dec_ref(v___f_1586_);
v_depth_1547_ = v___x_1568_;
v_fvarIds_1548_ = v_tail_1565_;
goto _start;
}
}
}
else
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
lean_dec(v_a_1583_);
lean_dec(v___x_1568_);
lean_dec(v_n_1567_);
lean_dec(v_tail_1565_);
lean_dec(v_head_1564_);
lean_dec(v_forbidden_1551_);
lean_dec(v_newNames_1550_);
lean_dec(v_mvarId_1549_);
v_a_1596_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1584_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1584_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1596_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
else
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
lean_dec(v_snd_1581_);
lean_dec(v___x_1568_);
lean_dec(v_n_1567_);
lean_dec(v_tail_1565_);
lean_dec(v_head_1564_);
lean_dec(v_forbidden_1551_);
lean_dec(v_newNames_1550_);
lean_dec(v_mvarId_1549_);
v_a_1604_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v___x_1582_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1582_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1604_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
else
{
lean_dec(v_a_1577_);
lean_dec(v_n_1567_);
lean_dec(v_head_1564_);
v_depth_1547_ = v___x_1568_;
v_fvarIds_1548_ = v_tail_1565_;
goto _start;
}
}
else
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
lean_dec(v___x_1568_);
lean_dec(v_n_1567_);
lean_dec(v_tail_1565_);
lean_dec(v_head_1564_);
lean_dec(v_forbidden_1551_);
lean_dec(v_newNames_1550_);
lean_dec(v_mvarId_1549_);
v_a_1613_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v___x_1576_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1576_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1618_; 
if (v_isShared_1616_ == 0)
{
v___x_1618_ = v___x_1615_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1613_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
else
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
lean_dec(v___x_1568_);
lean_dec(v_n_1567_);
lean_dec(v_tail_1565_);
lean_dec(v_head_1564_);
lean_dec(v_forbidden_1551_);
lean_dec(v_newNames_1550_);
lean_dec(v_mvarId_1549_);
v_a_1621_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1623_ = v___x_1574_;
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1574_);
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
lean_dec(v_n_1567_);
lean_dec(v_head_1564_);
v_depth_1547_ = v___x_1568_;
v_fvarIds_1548_ = v_tail_1565_;
goto _start;
}
v___jp_1569_:
{
if (v___y_1571_ == 0)
{
lean_dec_ref(v___y_1570_);
v_depth_1547_ = v___x_1568_;
v_fvarIds_1548_ = v_tail_1565_;
goto _start;
}
else
{
lean_dec(v___x_1568_);
lean_dec(v_tail_1565_);
lean_dec(v_forbidden_1551_);
lean_dec(v_newNames_1550_);
lean_dec(v_mvarId_1549_);
return v___y_1570_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___boxed(lean_object* v_depth_1630_, lean_object* v_fvarIds_1631_, lean_object* v_mvarId_1632_, lean_object* v_newNames_1633_, lean_object* v_forbidden_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go(v_depth_1630_, v_fvarIds_1631_, v_mvarId_1632_, v_newNames_1633_, v_forbidden_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_);
lean_dec(v_a_1638_);
lean_dec_ref(v_a_1637_);
lean_dec(v_a_1636_);
lean_dec_ref(v_a_1635_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0(lean_object* v_mvarId_1641_, lean_object* v_head_1642_, lean_object* v_newNames_1643_, lean_object* v_tail_1644_, lean_object* v_forbidden_1645_, lean_object* v_n_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v___x_1652_; 
lean_inc(v_head_1642_);
v___x_1652_ = l_Lean_Meta_injection(v_mvarId_1641_, v_head_1642_, v_newNames_1643_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1669_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1655_ = v___x_1652_;
v_isShared_1656_ = v_isSharedCheck_1669_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1652_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1669_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
if (lean_obj_tag(v_a_1653_) == 0)
{
lean_object* v___x_1657_; lean_object* v___x_1659_; 
lean_dec(v_n_1646_);
lean_dec(v_forbidden_1645_);
lean_dec(v_tail_1644_);
lean_dec(v_head_1642_);
v___x_1657_ = lean_box(0);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 0, v___x_1657_);
v___x_1659_ = v___x_1655_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1657_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
else
{
lean_object* v_mvarId_1661_; lean_object* v_newEqs_1662_; lean_object* v_remainingNames_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
lean_del_object(v___x_1655_);
v_mvarId_1661_ = lean_ctor_get(v_a_1653_, 0);
lean_inc(v_mvarId_1661_);
v_newEqs_1662_ = lean_ctor_get(v_a_1653_, 1);
lean_inc_ref(v_newEqs_1662_);
v_remainingNames_1663_ = lean_ctor_get(v_a_1653_, 2);
lean_inc(v_remainingNames_1663_);
lean_dec_ref(v_a_1653_);
v___x_1664_ = lean_array_to_list(v_newEqs_1662_);
v___x_1665_ = l_List_appendTR___redArg(v___x_1664_, v_tail_1644_);
v___x_1666_ = l_Lean_FVarIdSet_insert(v_forbidden_1645_, v_head_1642_);
lean_inc(v_mvarId_1661_);
v___x_1667_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___boxed), 10, 5);
lean_closure_set(v___x_1667_, 0, v_n_1646_);
lean_closure_set(v___x_1667_, 1, v___x_1665_);
lean_closure_set(v___x_1667_, 2, v_mvarId_1661_);
lean_closure_set(v___x_1667_, 3, v_remainingNames_1663_);
lean_closure_set(v___x_1667_, 4, v___x_1666_);
v___x_1668_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__3___redArg(v_mvarId_1661_, v___x_1667_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
return v___x_1668_;
}
}
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
lean_dec(v_n_1646_);
lean_dec(v_forbidden_1645_);
lean_dec(v_tail_1644_);
lean_dec(v_head_1642_);
v_a_1670_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1652_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1652_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0(lean_object* v_00_u03b2_1678_, lean_object* v_k_1679_, lean_object* v_t_1680_){
_start:
{
uint8_t v___x_1681_; 
v___x_1681_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(v_k_1679_, v_t_1680_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___boxed(lean_object* v_00_u03b2_1682_, lean_object* v_k_1683_, lean_object* v_t_1684_){
_start:
{
uint8_t v_res_1685_; lean_object* v_r_1686_; 
v_res_1685_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0(v_00_u03b2_1682_, v_k_1683_, v_t_1684_);
lean_dec(v_t_1684_);
lean_dec(v_k_1683_);
v_r_1686_ = lean_box(v_res_1685_);
return v_r_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections___lam__0(lean_object* v_maxDepth_1687_, lean_object* v_mvarId_1688_, lean_object* v_newNames_1689_, lean_object* v_forbidden_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v_lctx_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v_lctx_1696_ = lean_ctor_get(v___y_1691_, 2);
v___x_1697_ = l_Lean_LocalContext_getFVarIds(v_lctx_1696_);
v___x_1698_ = lean_array_to_list(v___x_1697_);
v___x_1699_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go(v_maxDepth_1687_, v___x_1698_, v_mvarId_1688_, v_newNames_1689_, v_forbidden_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections___lam__0___boxed(lean_object* v_maxDepth_1700_, lean_object* v_mvarId_1701_, lean_object* v_newNames_1702_, lean_object* v_forbidden_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Lean_Meta_injections___lam__0(v_maxDepth_1700_, v_mvarId_1701_, v_newNames_1702_, v_forbidden_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections(lean_object* v_mvarId_1710_, lean_object* v_newNames_1711_, lean_object* v_maxDepth_1712_, lean_object* v_forbidden_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_){
_start:
{
lean_object* v___f_1719_; lean_object* v___x_1720_; 
lean_inc(v_mvarId_1710_);
v___f_1719_ = lean_alloc_closure((void*)(l_Lean_Meta_injections___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1719_, 0, v_maxDepth_1712_);
lean_closure_set(v___f_1719_, 1, v_mvarId_1710_);
lean_closure_set(v___f_1719_, 2, v_newNames_1711_);
lean_closure_set(v___f_1719_, 3, v_forbidden_1713_);
v___x_1720_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__3___redArg(v_mvarId_1710_, v___f_1719_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections___boxed(lean_object* v_mvarId_1721_, lean_object* v_newNames_1722_, lean_object* v_maxDepth_1723_, lean_object* v_forbidden_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Lean_Meta_injections(v_mvarId_1721_, v_newNames_1722_, v_maxDepth_1723_, v_forbidden_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_);
lean_dec(v_a_1728_);
lean_dec_ref(v_a_1727_);
lean_dec(v_a_1726_);
lean_dec_ref(v_a_1725_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1787_; uint8_t v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1787_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__1));
v___x_1788_ = 0;
v___x_1789_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__22_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_));
v___x_1790_ = l_Lean_registerTraceClass(v___x_1787_, v___x_1788_, v___x_1789_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2____boxed(lean_object* v_a_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l___private_Lean_Meta_Tactic_Injection_0__initFn_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_();
return v_res_1792_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Subst(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Injection(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
