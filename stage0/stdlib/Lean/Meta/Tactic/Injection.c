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
uint8_t lean_bool_not(uint8_t);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Meta_injectionCore___lam__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_injectionCore___lam__1___closed__14;
static const lean_string_object l_Lean_Meta_injectionCore___lam__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "got no-confusion principle"};
static const lean_object* l_Lean_Meta_injectionCore___lam__1___closed__15 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__15_value;
static lean_once_cell_t l_Lean_Meta_injectionCore___lam__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_injectionCore___lam__1___closed__16;
static const lean_string_object l_Lean_Meta_injectionCore___lam__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "\nof type"};
static const lean_object* l_Lean_Meta_injectionCore___lam__1___closed__17 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__17_value;
static lean_once_cell_t l_Lean_Meta_injectionCore___lam__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_injectionCore___lam__1___closed__18;
static const lean_string_object l_Lean_Meta_injectionCore___lam__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_injectionCore___lam__1___closed__19 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__19_value;
static const lean_ctor_object l_Lean_Meta_injectionCore___lam__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_injectionCore___lam__1___closed__20 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__20_value;
static const lean_string_object l_Lean_Meta_injectionCore___lam__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "equality expected"};
static const lean_object* l_Lean_Meta_injectionCore___lam__1___closed__21 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__21_value;
static const lean_ctor_object l_Lean_Meta_injectionCore___lam__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__21_value)}};
static const lean_object* l_Lean_Meta_injectionCore___lam__1___closed__22 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__22_value;
static lean_once_cell_t l_Lean_Meta_injectionCore___lam__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_injectionCore___lam__1___closed__23;
static lean_once_cell_t l_Lean_Meta_injectionCore___lam__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_injectionCore___lam__1___closed__24;
static const lean_string_object l_Lean_Meta_injectionCore___lam__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_injectionCore___lam__1___closed__25 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__25_value;
static const lean_string_object l_Lean_Meta_injectionCore___lam__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_injectionCore___lam__1___closed__26 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__26_value;
static const lean_string_object l_Lean_Meta_injectionCore___lam__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "applying noConfusion to "};
static const lean_object* l_Lean_Meta_injectionCore___lam__1___closed__27 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__27_value;
static lean_once_cell_t l_Lean_Meta_injectionCore___lam__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_injectionCore___lam__1___closed__28;
static const lean_string_object l_Lean_Meta_injectionCore___lam__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " at\n"};
static const lean_object* l_Lean_Meta_injectionCore___lam__1___closed__29 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__29_value;
static lean_once_cell_t l_Lean_Meta_injectionCore___lam__1___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_injectionCore___lam__1___closed__30;
static const lean_string_object l_Lean_Meta_injectionCore___lam__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HEq"};
static const lean_object* l_Lean_Meta_injectionCore___lam__1___closed__31 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__31_value;
static const lean_ctor_object l_Lean_Meta_injectionCore___lam__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__31_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_object* l_Lean_Meta_injectionCore___lam__1___closed__32 = (const lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__32_value;
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
static const lean_ctor_object l_Lean_Meta_injectionIntro___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_injectionIntro___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_injectionIntro___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__4_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__3_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__4_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__4_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__5_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__4_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__14_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__13_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(120, 246, 74, 246, 83, 217, 223, 61)}};
static const lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__14_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__14_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__15_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__14_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_injectionCore___lam__1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(101, 249, 16, 135, 154, 231, 101, 58)}};
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
v___x_390_ = lean_st_ref_set(v___y_351_, v___x_389_);
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
size_t v_x_16301__boxed_549_; size_t v_x_16302__boxed_550_; lean_object* v_res_551_; 
v_x_16301__boxed_549_ = lean_unbox_usize(v_x_545_);
lean_dec(v_x_545_);
v_x_16302__boxed_550_ = lean_unbox_usize(v_x_546_);
lean_dec(v_x_546_);
v_res_551_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(v_x_544_, v_x_16301__boxed_549_, v_x_16302__boxed_550_, v_x_547_, v_x_548_);
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
lean_object* v___x_563_; lean_object* v_mctx_564_; lean_object* v_cache_565_; lean_object* v_zetaDeltaFVarIds_566_; lean_object* v_postponed_567_; lean_object* v_diag_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_596_; 
v___x_563_ = lean_st_ref_take(v___y_561_);
v_mctx_564_ = lean_ctor_get(v___x_563_, 0);
v_cache_565_ = lean_ctor_get(v___x_563_, 1);
v_zetaDeltaFVarIds_566_ = lean_ctor_get(v___x_563_, 2);
v_postponed_567_ = lean_ctor_get(v___x_563_, 3);
v_diag_568_ = lean_ctor_get(v___x_563_, 4);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_596_ == 0)
{
v___x_570_ = v___x_563_;
v_isShared_571_ = v_isSharedCheck_596_;
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
v_isShared_571_ = v_isSharedCheck_596_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v_depth_572_; lean_object* v_levelAssignDepth_573_; lean_object* v_lmvarCounter_574_; lean_object* v_mvarCounter_575_; lean_object* v_lDecls_576_; lean_object* v_decls_577_; lean_object* v_userNames_578_; lean_object* v_lAssignment_579_; lean_object* v_eAssignment_580_; lean_object* v_dAssignment_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_595_; 
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
v_isSharedCheck_595_ = !lean_is_exclusive(v_mctx_564_);
if (v_isSharedCheck_595_ == 0)
{
v___x_583_ = v_mctx_564_;
v_isShared_584_ = v_isSharedCheck_595_;
goto v_resetjp_582_;
}
else
{
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
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_595_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_585_; lean_object* v___x_587_; 
v___x_585_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0___redArg(v_eAssignment_580_, v_mvarId_559_, v_val_560_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 8, v___x_585_);
v___x_587_ = v___x_583_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_depth_572_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_levelAssignDepth_573_);
lean_ctor_set(v_reuseFailAlloc_594_, 2, v_lmvarCounter_574_);
lean_ctor_set(v_reuseFailAlloc_594_, 3, v_mvarCounter_575_);
lean_ctor_set(v_reuseFailAlloc_594_, 4, v_lDecls_576_);
lean_ctor_set(v_reuseFailAlloc_594_, 5, v_decls_577_);
lean_ctor_set(v_reuseFailAlloc_594_, 6, v_userNames_578_);
lean_ctor_set(v_reuseFailAlloc_594_, 7, v_lAssignment_579_);
lean_ctor_set(v_reuseFailAlloc_594_, 8, v___x_585_);
lean_ctor_set(v_reuseFailAlloc_594_, 9, v_dAssignment_581_);
v___x_587_ = v_reuseFailAlloc_594_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
lean_object* v___x_589_; 
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v___x_587_);
v___x_589_ = v___x_570_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_587_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v_cache_565_);
lean_ctor_set(v_reuseFailAlloc_593_, 2, v_zetaDeltaFVarIds_566_);
lean_ctor_set(v_reuseFailAlloc_593_, 3, v_postponed_567_);
lean_ctor_set(v_reuseFailAlloc_593_, 4, v_diag_568_);
v___x_589_ = v_reuseFailAlloc_593_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_590_ = lean_st_ref_set(v___y_561_, v___x_589_);
v___x_591_ = lean_box(0);
v___x_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
return v___x_592_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg___boxed(lean_object* v_mvarId_597_, lean_object* v_val_598_, lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(v_mvarId_597_, v_val_598_, v___y_599_);
lean_dec(v___y_599_);
return v_res_601_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__2(void){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__1));
v___x_606_ = l_Lean_MessageData_ofFormat(v___x_605_);
return v___x_606_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__3(void){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__2, &l_Lean_Meta_injectionCore___lam__1___closed__2_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__2);
v___x_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
return v___x_608_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__6(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__5));
v___x_613_ = l_Lean_MessageData_ofFormat(v___x_612_);
return v___x_613_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__7(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__6, &l_Lean_Meta_injectionCore___lam__1___closed__6_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__6);
v___x_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
return v___x_615_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__9(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__8));
v___x_618_ = l_Lean_stringToMessageData(v___x_617_);
return v___x_618_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__11(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__10));
v___x_621_ = l_Lean_stringToMessageData(v___x_620_);
return v___x_621_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__13(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__12));
v___x_624_ = l_Lean_stringToMessageData(v___x_623_);
return v___x_624_;
}
}
static uint64_t _init_l_Lean_Meta_injectionCore___lam__1___closed__14(void){
_start:
{
uint8_t v___x_625_; uint64_t v___x_626_; 
v___x_625_ = 1;
v___x_626_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_625_);
return v___x_626_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__16(void){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__15));
v___x_629_ = l_Lean_stringToMessageData(v___x_628_);
return v___x_629_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__18(void){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__17));
v___x_632_ = l_Lean_stringToMessageData(v___x_631_);
return v___x_632_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__23(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__22));
v___x_640_ = l_Lean_MessageData_ofFormat(v___x_639_);
return v___x_640_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__24(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__23, &l_Lean_Meta_injectionCore___lam__1___closed__23_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__23);
v___x_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
return v___x_642_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__28(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__27));
v___x_647_ = l_Lean_stringToMessageData(v___x_646_);
return v___x_647_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__30(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__29));
v___x_650_ = l_Lean_stringToMessageData(v___x_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___lam__1(lean_object* v_mvarId_654_, lean_object* v___x_655_, lean_object* v_fvarId_656_, lean_object* v___x_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v_type_933_; lean_object* v_prf_934_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___y_937_; lean_object* v___y_938_; lean_object* v___x_1018_; 
lean_inc(v___x_655_);
lean_inc(v_mvarId_654_);
v___x_1018_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_654_, v___x_655_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v___x_1019_; 
lean_dec_ref_known(v___x_1018_, 1);
lean_inc(v_fvarId_656_);
v___x_1019_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_656_, v___y_658_, v___y_660_, v___y_661_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
lean_inc(v_a_1020_);
lean_dec_ref_known(v___x_1019_, 1);
v___x_1021_ = l_Lean_LocalDecl_type(v_a_1020_);
lean_dec(v_a_1020_);
lean_inc(v___y_661_);
lean_inc_ref(v___y_660_);
lean_inc(v___y_659_);
lean_inc_ref(v___y_658_);
v___x_1022_ = lean_whnf(v___x_1021_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v_a_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; uint8_t v___x_1027_; 
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
lean_inc(v_a_1023_);
lean_dec_ref_known(v___x_1022_, 1);
lean_inc(v_fvarId_656_);
v___x_1024_ = l_Lean_mkFVar(v_fvarId_656_);
v___x_1025_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__32));
v___x_1026_ = lean_unsigned_to_nat(4u);
v___x_1027_ = l_Lean_Expr_isAppOfArity(v_a_1023_, v___x_1025_, v___x_1026_);
if (v___x_1027_ == 0)
{
v_type_933_ = v_a_1023_;
v_prf_934_ = v___x_1024_;
v___y_935_ = v___y_658_;
v___y_936_ = v___y_659_;
v___y_937_ = v___y_660_;
v___y_938_ = v___y_661_;
goto v___jp_932_;
}
else
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1028_ = l_Lean_Expr_appFn_x21(v_a_1023_);
v___x_1029_ = l_Lean_Expr_appFn_x21(v___x_1028_);
v___x_1030_ = l_Lean_Expr_appFn_x21(v___x_1029_);
v___x_1031_ = l_Lean_Expr_appArg_x21(v___x_1030_);
lean_dec_ref(v___x_1030_);
v___x_1032_ = l_Lean_Expr_appArg_x21(v___x_1028_);
lean_dec_ref(v___x_1028_);
v___x_1033_ = l_Lean_Meta_isExprDefEq(v___x_1031_, v___x_1032_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v_a_1034_; uint8_t v___x_1035_; 
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
lean_inc(v_a_1034_);
lean_dec_ref_known(v___x_1033_, 1);
v___x_1035_ = lean_unbox(v_a_1034_);
lean_dec(v_a_1034_);
if (v___x_1035_ == 0)
{
lean_dec_ref(v___x_1029_);
v_type_933_ = v_a_1023_;
v_prf_934_ = v___x_1024_;
v___y_935_ = v___y_658_;
v___y_936_ = v___y_659_;
v___y_937_ = v___y_660_;
v___y_938_ = v___y_661_;
goto v___jp_932_;
}
else
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1036_ = l_Lean_Expr_appArg_x21(v___x_1029_);
lean_dec_ref(v___x_1029_);
v___x_1037_ = l_Lean_Expr_appArg_x21(v_a_1023_);
lean_dec(v_a_1023_);
v___x_1038_ = l_Lean_Meta_mkEq(v___x_1036_, v___x_1037_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v_a_1039_; lean_object* v___x_1040_; 
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_a_1039_);
lean_dec_ref_known(v___x_1038_, 1);
v___x_1040_ = l_Lean_Meta_mkEqOfHEq(v___x_1024_, v___x_1027_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v_a_1041_; 
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
lean_inc(v_a_1041_);
lean_dec_ref_known(v___x_1040_, 1);
v_type_933_ = v_a_1039_;
v_prf_934_ = v_a_1041_;
v___y_935_ = v___y_658_;
v___y_936_ = v___y_659_;
v___y_937_ = v___y_660_;
v___y_938_ = v___y_661_;
goto v___jp_932_;
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_dec(v_a_1039_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec_ref(v___x_657_);
lean_dec(v_fvarId_656_);
lean_dec(v___x_655_);
lean_dec(v_mvarId_654_);
v_a_1042_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_1040_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1040_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
else
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
lean_dec_ref(v___x_1024_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec_ref(v___x_657_);
lean_dec(v_fvarId_656_);
lean_dec(v___x_655_);
lean_dec(v_mvarId_654_);
v_a_1050_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___x_1038_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1038_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1050_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
lean_dec_ref(v___x_1029_);
lean_dec_ref(v___x_1024_);
lean_dec(v_a_1023_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec_ref(v___x_657_);
lean_dec(v_fvarId_656_);
lean_dec(v___x_655_);
lean_dec(v_mvarId_654_);
v_a_1058_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v___x_1033_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1033_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_a_1058_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
}
else
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec_ref(v___x_657_);
lean_dec(v_fvarId_656_);
lean_dec(v___x_655_);
lean_dec(v_mvarId_654_);
v_a_1066_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v___x_1022_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1022_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
else
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1081_; 
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec_ref(v___x_657_);
lean_dec(v_fvarId_656_);
lean_dec(v___x_655_);
lean_dec(v_mvarId_654_);
v_a_1074_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1076_ = v___x_1019_;
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1019_);
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
else
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec_ref(v___x_657_);
lean_dec(v_fvarId_656_);
lean_dec(v___x_655_);
lean_dec(v_mvarId_654_);
v_a_1082_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1018_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1018_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
v___jp_663_:
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__3, &l_Lean_Meta_injectionCore___lam__1___closed__3_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__3);
v___x_669_ = l_Lean_Meta_throwTacticEx___redArg(v___x_655_, v_mvarId_654_, v___x_668_, v___y_664_, v___y_665_, v___y_666_, v___y_667_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
return v___x_669_;
}
v___jp_670_:
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__7, &l_Lean_Meta_injectionCore___lam__1___closed__7_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__7);
v___x_676_ = l_Lean_Meta_throwTacticEx___redArg(v___x_655_, v_mvarId_654_, v___x_675_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
return v___x_676_;
}
v___jp_677_:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_680_, 0, v___y_679_);
lean_ctor_set(v___x_680_, 1, v___y_678_);
v___x_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
return v___x_681_;
}
v___jp_682_:
{
lean_object* v_toConstantVal_692_; lean_object* v_toConstantVal_693_; lean_object* v_numFields_694_; lean_object* v_name_695_; lean_object* v_name_696_; uint8_t v___x_697_; uint8_t v___x_698_; 
v_toConstantVal_692_ = lean_ctor_get(v___y_685_, 0);
v_toConstantVal_693_ = lean_ctor_get(v___y_686_, 0);
lean_inc_ref(v_toConstantVal_693_);
lean_dec_ref(v___y_686_);
v_numFields_694_ = lean_ctor_get(v___y_685_, 4);
lean_inc(v_numFields_694_);
v_name_695_ = lean_ctor_get(v_toConstantVal_692_, 0);
v_name_696_ = lean_ctor_get(v_toConstantVal_693_, 0);
lean_inc(v_name_696_);
lean_dec_ref(v_toConstantVal_693_);
v___x_697_ = lean_name_eq(v_name_695_, v_name_696_);
lean_dec(v_name_696_);
v___x_698_ = lean_bool_not(v___x_697_);
if (v___x_698_ == 0)
{
lean_object* v___x_699_; 
lean_inc(v___y_691_);
lean_inc_ref(v___y_690_);
lean_inc(v___y_689_);
lean_inc_ref(v___y_688_);
lean_inc_ref(v___y_684_);
v___x_699_ = lean_infer_type(v___y_684_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; lean_object* v___x_701_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_a_700_);
lean_dec_ref_known(v___x_699_, 1);
v___x_701_ = l_Lean_Meta_whnfD(v_a_700_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v_a_702_; 
v_a_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_a_702_);
lean_dec_ref_known(v___x_701_, 1);
if (lean_obj_tag(v_a_702_) == 7)
{
lean_object* v_binderType_703_; lean_object* v___x_704_; 
lean_dec_ref(v___y_687_);
lean_dec(v___x_655_);
v_binderType_703_ = lean_ctor_get(v_a_702_, 1);
lean_inc_ref(v_binderType_703_);
lean_dec_ref_known(v_a_702_, 3);
lean_inc(v_mvarId_654_);
v___x_704_ = l_Lean_MVarId_getTag(v_mvarId_654_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_a_705_);
lean_dec_ref_known(v___x_704_, 1);
v___x_706_ = l_Lean_Expr_headBeta(v_binderType_703_);
v___x_707_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_706_, v_a_705_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_762_; 
v_a_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc_n(v_a_708_, 2);
lean_dec_ref_known(v___x_707_, 1);
v___x_709_ = l_Lean_Expr_app___override(v___y_684_, v_a_708_);
v___x_710_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(v_mvarId_654_, v___x_709_, v___y_689_);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_762_ == 0)
{
lean_object* v_unused_763_; 
v_unused_763_ = lean_ctor_get(v___x_710_, 0);
lean_dec(v_unused_763_);
v___x_712_ = v___x_710_;
v_isShared_713_ = v_isSharedCheck_762_;
goto v_resetjp_711_;
}
else
{
lean_dec(v___x_710_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_762_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = l_Lean_Expr_mvarId_x21(v_a_708_);
lean_dec(v_a_708_);
v___x_715_ = l_Lean_MVarId_tryClear(v___x_714_, v_fvarId_656_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_a_716_; lean_object* v___x_717_; 
v_a_716_ = lean_ctor_get(v___x_715_, 0);
lean_inc(v_a_716_);
lean_dec_ref_known(v___x_715_, 1);
v___x_717_ = l_Lean_Meta_getCtorNumPropFields(v___y_685_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_options_718_; lean_object* v_a_719_; lean_object* v_inheritedTraceOptions_720_; uint8_t v_hasTrace_721_; lean_object* v___x_722_; 
v_options_718_ = lean_ctor_get(v___y_690_, 2);
v_a_719_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_719_);
lean_dec_ref_known(v___x_717_, 1);
v_inheritedTraceOptions_720_ = lean_ctor_get(v___y_690_, 13);
v_hasTrace_721_ = lean_ctor_get_uint8(v_options_718_, sizeof(void*)*1);
v___x_722_ = lean_nat_sub(v_numFields_694_, v_a_719_);
lean_dec(v_a_719_);
lean_dec(v_numFields_694_);
if (v_hasTrace_721_ == 0)
{
lean_del_object(v___x_712_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_683_);
v___y_678_ = v___x_722_;
v___y_679_ = v_a_716_;
goto v___jp_677_;
}
else
{
lean_object* v___x_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_723_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__0___closed__1));
lean_inc(v___y_683_);
v___x_724_ = l_Lean_Name_append(v___x_723_, v___y_683_);
v___x_725_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_720_, v_options_718_, v___x_724_);
lean_dec(v___x_724_);
if (v___x_725_ == 0)
{
lean_del_object(v___x_712_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_683_);
v___y_678_ = v___x_722_;
v___y_679_ = v_a_716_;
goto v___jp_677_;
}
else
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_729_; 
v___x_726_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__9, &l_Lean_Meta_injectionCore___lam__1___closed__9_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__9);
lean_inc(v___x_722_);
v___x_727_ = l_Nat_reprFast(v___x_722_);
if (v_isShared_713_ == 0)
{
lean_ctor_set_tag(v___x_712_, 3);
lean_ctor_set(v___x_712_, 0, v___x_727_);
v___x_729_ = v___x_712_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_727_);
v___x_729_ = v_reuseFailAlloc_745_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_730_ = l_Lean_MessageData_ofFormat(v___x_729_);
v___x_731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_726_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
v___x_732_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__11, &l_Lean_Meta_injectionCore___lam__1___closed__11_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__11);
v___x_733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_731_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
lean_inc(v_a_716_);
v___x_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_734_, 0, v_a_716_);
v___x_735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_733_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
v___x_736_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v___y_683_, v___x_735_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_dec_ref_known(v___x_736_, 1);
v___y_678_ = v___x_722_;
v___y_679_ = v_a_716_;
goto v___jp_677_;
}
else
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
lean_dec(v___x_722_);
lean_dec(v_a_716_);
v_a_737_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_744_ == 0)
{
v___x_739_ = v___x_736_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_736_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_737_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
lean_dec(v_a_716_);
lean_del_object(v___x_712_);
lean_dec(v_numFields_694_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_683_);
v_a_746_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_717_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_717_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_746_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
else
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
lean_del_object(v___x_712_);
lean_dec(v_numFields_694_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_683_);
v_a_754_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_715_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_715_);
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
}
else
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
lean_dec(v_numFields_694_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec_ref(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec(v_fvarId_656_);
lean_dec(v_mvarId_654_);
v_a_764_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_707_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_707_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_764_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
else
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
lean_dec_ref(v_binderType_703_);
lean_dec(v_numFields_694_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec_ref(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec(v_fvarId_656_);
lean_dec(v_mvarId_654_);
v_a_772_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_779_ == 0)
{
v___x_774_ = v___x_704_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_704_);
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
lean_object* v___x_780_; 
lean_dec(v_numFields_694_);
lean_dec_ref(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v_fvarId_656_);
lean_inc(v___y_691_);
lean_inc_ref(v___y_690_);
lean_inc(v___y_689_);
lean_inc_ref(v___y_688_);
v___x_780_ = lean_apply_5(v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, lean_box(0));
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v_a_781_; uint8_t v___x_782_; 
v_a_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_a_781_);
lean_dec_ref_known(v___x_780_, 1);
v___x_782_ = lean_unbox(v_a_781_);
lean_dec(v_a_781_);
if (v___x_782_ == 0)
{
lean_dec(v_a_702_);
lean_dec(v___y_683_);
v___y_664_ = v___y_688_;
v___y_665_ = v___y_689_;
v___y_666_ = v___y_690_;
v___y_667_ = v___y_691_;
goto v___jp_663_;
}
else
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_783_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__13, &l_Lean_Meta_injectionCore___lam__1___closed__13_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__13);
v___x_784_ = l_Lean_indentExpr(v_a_702_);
v___x_785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_783_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
v___x_786_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v___y_683_, v___x_785_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_dec_ref_known(v___x_786_, 1);
v___y_664_ = v___y_688_;
v___y_665_ = v___y_689_;
v___y_666_ = v___y_690_;
v___y_667_ = v___y_691_;
goto v___jp_663_;
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___x_655_);
lean_dec(v_mvarId_654_);
v_a_787_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_786_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_786_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
}
else
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
lean_dec(v_a_702_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_683_);
lean_dec(v___x_655_);
lean_dec(v_mvarId_654_);
v_a_795_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_780_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_780_);
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
lean_dec(v_numFields_694_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec_ref(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec(v_fvarId_656_);
lean_dec(v___x_655_);
lean_dec(v_mvarId_654_);
v_a_803_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_810_ == 0)
{
v___x_805_ = v___x_701_;
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_701_);
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
else
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_818_; 
lean_dec(v_numFields_694_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec_ref(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec(v_fvarId_656_);
lean_dec(v___x_655_);
lean_dec(v_mvarId_654_);
v_a_811_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_818_ == 0)
{
v___x_813_ = v___x_699_;
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_699_);
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
lean_object* v___x_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_827_; 
lean_dec(v_numFields_694_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec_ref(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_683_);
lean_dec(v_fvarId_656_);
lean_dec(v___x_655_);
v___x_819_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(v_mvarId_654_, v___y_684_, v___y_689_);
lean_dec(v___y_689_);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_827_ == 0)
{
lean_object* v_unused_828_; 
v_unused_828_ = lean_ctor_get(v___x_819_, 0);
lean_dec(v_unused_828_);
v___x_821_ = v___x_819_;
v_isShared_822_ = v_isSharedCheck_827_;
goto v_resetjp_820_;
}
else
{
lean_dec(v___x_819_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_827_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_823_; lean_object* v___x_825_; 
v___x_823_ = lean_box(0);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v___x_823_);
v___x_825_ = v___x_821_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_823_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
v___jp_829_:
{
lean_object* v___x_840_; uint8_t v_foApprox_841_; uint8_t v_ctxApprox_842_; uint8_t v_quasiPatternApprox_843_; uint8_t v_constApprox_844_; uint8_t v_isDefEqStuckEx_845_; uint8_t v_unificationHints_846_; uint8_t v_proofIrrelevance_847_; uint8_t v_assignSyntheticOpaque_848_; uint8_t v_offsetCnstrs_849_; uint8_t v_etaStruct_850_; uint8_t v_univApprox_851_; uint8_t v_iota_852_; uint8_t v_beta_853_; uint8_t v_proj_854_; uint8_t v_zeta_855_; uint8_t v_zetaDelta_856_; uint8_t v_zetaUnused_857_; uint8_t v_zetaHave_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_931_; 
v___x_840_ = l_Lean_Meta_Context_config(v___y_836_);
v_foApprox_841_ = lean_ctor_get_uint8(v___x_840_, 0);
v_ctxApprox_842_ = lean_ctor_get_uint8(v___x_840_, 1);
v_quasiPatternApprox_843_ = lean_ctor_get_uint8(v___x_840_, 2);
v_constApprox_844_ = lean_ctor_get_uint8(v___x_840_, 3);
v_isDefEqStuckEx_845_ = lean_ctor_get_uint8(v___x_840_, 4);
v_unificationHints_846_ = lean_ctor_get_uint8(v___x_840_, 5);
v_proofIrrelevance_847_ = lean_ctor_get_uint8(v___x_840_, 6);
v_assignSyntheticOpaque_848_ = lean_ctor_get_uint8(v___x_840_, 7);
v_offsetCnstrs_849_ = lean_ctor_get_uint8(v___x_840_, 8);
v_etaStruct_850_ = lean_ctor_get_uint8(v___x_840_, 10);
v_univApprox_851_ = lean_ctor_get_uint8(v___x_840_, 11);
v_iota_852_ = lean_ctor_get_uint8(v___x_840_, 12);
v_beta_853_ = lean_ctor_get_uint8(v___x_840_, 13);
v_proj_854_ = lean_ctor_get_uint8(v___x_840_, 14);
v_zeta_855_ = lean_ctor_get_uint8(v___x_840_, 15);
v_zetaDelta_856_ = lean_ctor_get_uint8(v___x_840_, 16);
v_zetaUnused_857_ = lean_ctor_get_uint8(v___x_840_, 17);
v_zetaHave_858_ = lean_ctor_get_uint8(v___x_840_, 18);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_931_ == 0)
{
v___x_860_ = v___x_840_;
v_isShared_861_ = v_isSharedCheck_931_;
goto v_resetjp_859_;
}
else
{
lean_dec(v___x_840_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_931_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
uint8_t v_trackZetaDelta_862_; lean_object* v_zetaDeltaSet_863_; lean_object* v_lctx_864_; lean_object* v_localInstances_865_; lean_object* v_defEqCtx_x3f_866_; lean_object* v_synthPendingDepth_867_; lean_object* v_canUnfold_x3f_868_; uint8_t v_univApprox_869_; uint8_t v_inTypeClassResolution_870_; uint8_t v_cacheInferType_871_; uint8_t v___x_872_; lean_object* v_config_874_; 
v_trackZetaDelta_862_ = lean_ctor_get_uint8(v___y_836_, sizeof(void*)*7);
v_zetaDeltaSet_863_ = lean_ctor_get(v___y_836_, 1);
v_lctx_864_ = lean_ctor_get(v___y_836_, 2);
v_localInstances_865_ = lean_ctor_get(v___y_836_, 3);
v_defEqCtx_x3f_866_ = lean_ctor_get(v___y_836_, 4);
v_synthPendingDepth_867_ = lean_ctor_get(v___y_836_, 5);
v_canUnfold_x3f_868_ = lean_ctor_get(v___y_836_, 6);
v_univApprox_869_ = lean_ctor_get_uint8(v___y_836_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_870_ = lean_ctor_get_uint8(v___y_836_, sizeof(void*)*7 + 2);
v_cacheInferType_871_ = lean_ctor_get_uint8(v___y_836_, sizeof(void*)*7 + 3);
v___x_872_ = 1;
if (v_isShared_861_ == 0)
{
v_config_874_ = v___x_860_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_930_, 0, v_foApprox_841_);
lean_ctor_set_uint8(v_reuseFailAlloc_930_, 1, v_ctxApprox_842_);
lean_ctor_set_uint8(v_reuseFailAlloc_930_, 2, v_quasiPatternApprox_843_);
lean_ctor_set_uint8(v_reuseFailAlloc_930_, 3, v_constApprox_844_);
lean_ctor_set_uint8(v_reuseFailAlloc_930_, 4, v_isDefEqStuckEx_845_);
lean_ctor_set_uint8(v_reuseFailAlloc_930_, 5, v_unificationHints_846_);
lean_ctor_set_uint8(v_reuseFailAlloc_930_, 6, v_proofIrrelevance_847_);
lean_ctor_set_uint8(v_reuseFailAlloc_930_, 7, v_assignSyntheticOpaque_848_);
lean_ctor_set_uint8(v_reuseFailAlloc_930_, 8, v_offsetCnstrs_849_);
lean_ctor_set_uint8(v_reuseFailAlloc_930_, 10, v_etaStruct_850_);
lean_ctor_set_uint8(v_reuseFailAlloc_930_, 11, v_univApprox_851_);
lean_ctor_set_uint8(v_reuseFailAlloc_930_, 12, v_iota_852_);
lean_ctor_set_uint8(v_reuseFailAlloc_930_, 13, v_beta_853_);
lean_ctor_set_uint8(v_reuseFailAlloc_930_, 14, v_proj_854_);
lean_ctor_set_uint8(v_reuseFailAlloc_930_, 15, v_zeta_855_);
lean_ctor_set_uint8(v_reuseFailAlloc_930_, 16, v_zetaDelta_856_);
lean_ctor_set_uint8(v_reuseFailAlloc_930_, 17, v_zetaUnused_857_);
lean_ctor_set_uint8(v_reuseFailAlloc_930_, 18, v_zetaHave_858_);
v_config_874_ = v_reuseFailAlloc_930_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
uint64_t v___x_875_; uint64_t v___x_876_; uint64_t v___x_877_; uint64_t v___x_878_; uint64_t v___x_879_; uint64_t v_key_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
lean_ctor_set_uint8(v_config_874_, 9, v___x_872_);
v___x_875_ = l_Lean_Meta_Context_configKey(v___y_836_);
v___x_876_ = 3ULL;
v___x_877_ = lean_uint64_shift_right(v___x_875_, v___x_876_);
v___x_878_ = lean_uint64_shift_left(v___x_877_, v___x_876_);
v___x_879_ = lean_uint64_once(&l_Lean_Meta_injectionCore___lam__1___closed__14, &l_Lean_Meta_injectionCore___lam__1___closed__14_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__14);
v_key_880_ = lean_uint64_lor(v___x_878_, v___x_879_);
v___x_881_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_881_, 0, v_config_874_);
lean_ctor_set_uint64(v___x_881_, sizeof(void*)*1, v_key_880_);
lean_inc(v_canUnfold_x3f_868_);
lean_inc(v_synthPendingDepth_867_);
lean_inc(v_defEqCtx_x3f_866_);
lean_inc_ref(v_localInstances_865_);
lean_inc_ref(v_lctx_864_);
lean_inc(v_zetaDeltaSet_863_);
v___x_882_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_882_, 0, v___x_881_);
lean_ctor_set(v___x_882_, 1, v_zetaDeltaSet_863_);
lean_ctor_set(v___x_882_, 2, v_lctx_864_);
lean_ctor_set(v___x_882_, 3, v_localInstances_865_);
lean_ctor_set(v___x_882_, 4, v_defEqCtx_x3f_866_);
lean_ctor_set(v___x_882_, 5, v_synthPendingDepth_867_);
lean_ctor_set(v___x_882_, 6, v_canUnfold_x3f_868_);
lean_ctor_set_uint8(v___x_882_, sizeof(void*)*7, v_trackZetaDelta_862_);
lean_ctor_set_uint8(v___x_882_, sizeof(void*)*7 + 1, v_univApprox_869_);
lean_ctor_set_uint8(v___x_882_, sizeof(void*)*7 + 2, v_inTypeClassResolution_870_);
lean_ctor_set_uint8(v___x_882_, sizeof(void*)*7 + 3, v_cacheInferType_871_);
v___x_883_ = l_Lean_Meta_mkNoConfusion(v___y_833_, v___y_832_, v___x_882_, v___y_837_, v___y_838_, v___y_839_);
lean_dec_ref_known(v___x_882_, 7);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___x_885_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_884_);
lean_dec_ref_known(v___x_883_, 1);
lean_inc_ref(v___y_835_);
lean_inc(v___y_839_);
lean_inc_ref(v___y_838_);
lean_inc(v___y_837_);
lean_inc_ref(v___y_836_);
v___x_885_ = lean_apply_5(v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, lean_box(0));
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; uint8_t v___x_887_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_886_);
lean_dec_ref_known(v___x_885_, 1);
v___x_887_ = lean_unbox(v_a_886_);
lean_dec(v_a_886_);
if (v___x_887_ == 0)
{
v___y_683_ = v___y_830_;
v___y_684_ = v_a_884_;
v___y_685_ = v___y_831_;
v___y_686_ = v___y_834_;
v___y_687_ = v___y_835_;
v___y_688_ = v___y_836_;
v___y_689_ = v___y_837_;
v___y_690_ = v___y_838_;
v___y_691_ = v___y_839_;
goto v___jp_682_;
}
else
{
lean_object* v___x_888_; 
lean_inc(v___y_839_);
lean_inc_ref(v___y_838_);
lean_inc(v___y_837_);
lean_inc_ref(v___y_836_);
lean_inc(v_a_884_);
v___x_888_ = lean_infer_type(v_a_884_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc(v_a_889_);
lean_dec_ref_known(v___x_888_, 1);
v___x_890_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__16, &l_Lean_Meta_injectionCore___lam__1___closed__16_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__16);
lean_inc(v_a_884_);
v___x_891_ = l_Lean_indentExpr(v_a_884_);
v___x_892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_892_, 0, v___x_890_);
lean_ctor_set(v___x_892_, 1, v___x_891_);
v___x_893_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__18, &l_Lean_Meta_injectionCore___lam__1___closed__18_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__18);
v___x_894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_892_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
v___x_895_ = l_Lean_indentExpr(v_a_889_);
v___x_896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_894_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
lean_inc(v___y_830_);
v___x_897_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v___y_830_, v___x_896_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_dec_ref_known(v___x_897_, 1);
v___y_683_ = v___y_830_;
v___y_684_ = v_a_884_;
v___y_685_ = v___y_831_;
v___y_686_ = v___y_834_;
v___y_687_ = v___y_835_;
v___y_688_ = v___y_836_;
v___y_689_ = v___y_837_;
v___y_690_ = v___y_838_;
v___y_691_ = v___y_839_;
goto v___jp_682_;
}
else
{
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_905_; 
lean_dec(v_a_884_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec(v_fvarId_656_);
lean_dec(v___x_655_);
lean_dec(v_mvarId_654_);
v_a_898_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_905_ == 0)
{
v___x_900_ = v___x_897_;
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_897_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_903_; 
if (v_isShared_901_ == 0)
{
v___x_903_ = v___x_900_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_a_898_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
else
{
lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_913_; 
lean_dec(v_a_884_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec(v_fvarId_656_);
lean_dec(v___x_655_);
lean_dec(v_mvarId_654_);
v_a_906_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_913_ == 0)
{
v___x_908_ = v___x_888_;
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v___x_888_);
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
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_921_; 
lean_dec(v_a_884_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec(v_fvarId_656_);
lean_dec(v___x_655_);
lean_dec(v_mvarId_654_);
v_a_914_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_921_ == 0)
{
v___x_916_ = v___x_885_;
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_885_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_917_ == 0)
{
v___x_919_ = v___x_916_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_a_914_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec(v_fvarId_656_);
lean_dec(v___x_655_);
lean_dec(v_mvarId_654_);
v_a_922_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_883_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_883_);
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
}
v___jp_932_:
{
lean_object* v___x_939_; lean_object* v___x_940_; uint8_t v___x_941_; 
v___x_939_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__20));
v___x_940_ = lean_unsigned_to_nat(3u);
v___x_941_ = l_Lean_Expr_isAppOfArity(v_type_933_, v___x_939_, v___x_940_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; lean_object* v___x_943_; 
lean_dec_ref(v_prf_934_);
lean_dec_ref(v_type_933_);
lean_dec_ref(v___x_657_);
lean_dec(v_fvarId_656_);
v___x_942_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__24, &l_Lean_Meta_injectionCore___lam__1___closed__24_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__24);
v___x_943_ = l_Lean_Meta_throwTacticEx___redArg(v___x_655_, v_mvarId_654_, v___x_942_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
return v___x_943_;
}
else
{
lean_object* v___x_944_; 
lean_inc(v_mvarId_654_);
v___x_944_ = l_Lean_MVarId_getType(v_mvarId_654_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v_a_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v_a_945_ = lean_ctor_get(v___x_944_, 0);
lean_inc(v_a_945_);
lean_dec_ref_known(v___x_944_, 1);
v___x_946_ = l_Lean_Expr_appFn_x21(v_type_933_);
v___x_947_ = l_Lean_Expr_appArg_x21(v___x_946_);
lean_dec_ref(v___x_946_);
v___x_948_ = l_Lean_Meta_isConstructorApp_x27_x3f(v___x_947_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc(v_a_949_);
lean_dec_ref_known(v___x_948_, 1);
v___x_950_ = l_Lean_Expr_appArg_x21(v_type_933_);
lean_dec_ref(v_type_933_);
v___x_951_ = l_Lean_Meta_isConstructorApp_x27_x3f(v___x_950_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
if (lean_obj_tag(v___x_951_) == 0)
{
if (lean_obj_tag(v_a_949_) == 1)
{
lean_object* v_a_952_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_a_952_);
lean_dec_ref_known(v___x_951_, 1);
if (lean_obj_tag(v_a_952_) == 1)
{
lean_object* v_val_953_; lean_object* v_val_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___f_958_; lean_object* v___x_959_; lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_993_; 
v_val_953_ = lean_ctor_get(v_a_949_, 0);
lean_inc(v_val_953_);
lean_dec_ref_known(v_a_949_, 1);
v_val_954_ = lean_ctor_get(v_a_952_, 0);
lean_inc(v_val_954_);
lean_dec_ref_known(v_a_952_, 1);
v___x_955_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__25));
v___x_956_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__26));
v___x_957_ = l_Lean_Name_mkStr3(v___x_955_, v___x_956_, v___x_657_);
lean_inc_n(v___x_957_, 2);
v___f_958_ = lean_alloc_closure((void*)(l_Lean_Meta_injectionCore___lam__0___boxed), 6, 1);
lean_closure_set(v___f_958_, 0, v___x_957_);
v___x_959_ = l_Lean_Meta_injectionCore___lam__0(v___x_957_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
v_a_960_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_993_ == 0)
{
v___x_962_ = v___x_959_;
v_isShared_963_ = v_isSharedCheck_993_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v___x_959_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_993_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
uint8_t v___x_964_; 
v___x_964_ = lean_unbox(v_a_960_);
lean_dec(v_a_960_);
if (v___x_964_ == 0)
{
lean_del_object(v___x_962_);
v___y_830_ = v___x_957_;
v___y_831_ = v_val_953_;
v___y_832_ = v_prf_934_;
v___y_833_ = v_a_945_;
v___y_834_ = v_val_954_;
v___y_835_ = v___f_958_;
v___y_836_ = v___y_935_;
v___y_837_ = v___y_936_;
v___y_838_ = v___y_937_;
v___y_839_ = v___y_938_;
goto v___jp_829_;
}
else
{
lean_object* v___x_965_; 
lean_inc(v___y_938_);
lean_inc_ref(v___y_937_);
lean_inc(v___y_936_);
lean_inc_ref(v___y_935_);
lean_inc_ref(v_prf_934_);
v___x_965_ = lean_infer_type(v_prf_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v_a_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_973_; 
v_a_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc(v_a_966_);
lean_dec_ref_known(v___x_965_, 1);
v___x_967_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__28, &l_Lean_Meta_injectionCore___lam__1___closed__28_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__28);
v___x_968_ = l_Lean_MessageData_ofExpr(v_a_966_);
v___x_969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_967_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
v___x_970_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__30, &l_Lean_Meta_injectionCore___lam__1___closed__30_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__30);
v___x_971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_969_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
lean_inc(v_mvarId_654_);
if (v_isShared_963_ == 0)
{
lean_ctor_set_tag(v___x_962_, 1);
lean_ctor_set(v___x_962_, 0, v_mvarId_654_);
v___x_973_ = v___x_962_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_mvarId_654_);
v___x_973_ = v_reuseFailAlloc_984_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_971_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
lean_inc(v___x_957_);
v___x_975_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v___x_957_, v___x_974_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_dec_ref_known(v___x_975_, 1);
v___y_830_ = v___x_957_;
v___y_831_ = v_val_953_;
v___y_832_ = v_prf_934_;
v___y_833_ = v_a_945_;
v___y_834_ = v_val_954_;
v___y_835_ = v___f_958_;
v___y_836_ = v___y_935_;
v___y_837_ = v___y_936_;
v___y_838_ = v___y_937_;
v___y_839_ = v___y_938_;
goto v___jp_829_;
}
else
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_983_; 
lean_dec_ref(v___f_958_);
lean_dec(v___x_957_);
lean_dec(v_val_954_);
lean_dec(v_val_953_);
lean_dec(v_a_945_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec_ref(v_prf_934_);
lean_dec(v_fvarId_656_);
lean_dec(v___x_655_);
lean_dec(v_mvarId_654_);
v_a_976_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_983_ == 0)
{
v___x_978_ = v___x_975_;
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_975_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_a_976_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
}
}
else
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_992_; 
lean_del_object(v___x_962_);
lean_dec_ref(v___f_958_);
lean_dec(v___x_957_);
lean_dec(v_val_954_);
lean_dec(v_val_953_);
lean_dec(v_a_945_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec_ref(v_prf_934_);
lean_dec(v_fvarId_656_);
lean_dec(v___x_655_);
lean_dec(v_mvarId_654_);
v_a_985_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_992_ == 0)
{
v___x_987_ = v___x_965_;
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_965_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_985_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
}
}
else
{
lean_dec(v_a_952_);
lean_dec_ref_known(v_a_949_, 1);
lean_dec(v_a_945_);
lean_dec_ref(v_prf_934_);
lean_dec_ref(v___x_657_);
lean_dec(v_fvarId_656_);
v___y_671_ = v___y_935_;
v___y_672_ = v___y_936_;
v___y_673_ = v___y_937_;
v___y_674_ = v___y_938_;
goto v___jp_670_;
}
}
else
{
lean_dec_ref_known(v___x_951_, 1);
lean_dec(v_a_949_);
lean_dec(v_a_945_);
lean_dec_ref(v_prf_934_);
lean_dec_ref(v___x_657_);
lean_dec(v_fvarId_656_);
v___y_671_ = v___y_935_;
v___y_672_ = v___y_936_;
v___y_673_ = v___y_937_;
v___y_674_ = v___y_938_;
goto v___jp_670_;
}
}
else
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1001_; 
lean_dec(v_a_949_);
lean_dec(v_a_945_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec_ref(v_prf_934_);
lean_dec_ref(v___x_657_);
lean_dec(v_fvarId_656_);
lean_dec(v___x_655_);
lean_dec(v_mvarId_654_);
v_a_994_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_996_ = v___x_951_;
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_951_);
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
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
lean_dec(v_a_945_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec_ref(v_prf_934_);
lean_dec_ref(v_type_933_);
lean_dec_ref(v___x_657_);
lean_dec(v_fvarId_656_);
lean_dec(v___x_655_);
lean_dec(v_mvarId_654_);
v_a_1002_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_948_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_948_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1002_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec_ref(v_prf_934_);
lean_dec_ref(v_type_933_);
lean_dec_ref(v___x_657_);
lean_dec(v_fvarId_656_);
lean_dec(v___x_655_);
lean_dec(v_mvarId_654_);
v_a_1010_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_944_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_944_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___lam__1___boxed(lean_object* v_mvarId_1090_, lean_object* v___x_1091_, lean_object* v_fvarId_1092_, lean_object* v___x_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Lean_Meta_injectionCore___lam__1(v_mvarId_1090_, v___x_1091_, v_fvarId_1092_, v___x_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore(lean_object* v_mvarId_1103_, lean_object* v_fvarId_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___f_1112_; lean_object* v___x_1113_; 
v___x_1110_ = ((lean_object*)(l_Lean_Meta_injectionCore___closed__0));
v___x_1111_ = ((lean_object*)(l_Lean_Meta_injectionCore___closed__1));
lean_inc(v_mvarId_1103_);
v___f_1112_ = lean_alloc_closure((void*)(l_Lean_Meta_injectionCore___lam__1___boxed), 9, 4);
lean_closure_set(v___f_1112_, 0, v_mvarId_1103_);
lean_closure_set(v___f_1112_, 1, v___x_1111_);
lean_closure_set(v___f_1112_, 2, v_fvarId_1104_);
lean_closure_set(v___f_1112_, 3, v___x_1110_);
v___x_1113_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg(v_mvarId_1103_, v___f_1112_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___boxed(lean_object* v_mvarId_1114_, lean_object* v_fvarId_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Lean_Meta_injectionCore(v_mvarId_1114_, v_fvarId_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0(lean_object* v_mvarId_1122_, lean_object* v_val_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v___x_1129_; 
v___x_1129_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(v_mvarId_1122_, v_val_1123_, v___y_1125_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___boxed(lean_object* v_mvarId_1130_, lean_object* v_val_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0(v_mvarId_1130_, v_val_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0(lean_object* v_00_u03b2_1138_, lean_object* v_x_1139_, lean_object* v_x_1140_, lean_object* v_x_1141_){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0___redArg(v_x_1139_, v_x_1140_, v_x_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1143_, lean_object* v_x_1144_, size_t v_x_1145_, size_t v_x_1146_, lean_object* v_x_1147_, lean_object* v_x_1148_){
_start:
{
lean_object* v___x_1149_; 
v___x_1149_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(v_x_1144_, v_x_1145_, v_x_1146_, v_x_1147_, v_x_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1150_, lean_object* v_x_1151_, lean_object* v_x_1152_, lean_object* v_x_1153_, lean_object* v_x_1154_, lean_object* v_x_1155_){
_start:
{
size_t v_x_17527__boxed_1156_; size_t v_x_17528__boxed_1157_; lean_object* v_res_1158_; 
v_x_17527__boxed_1156_ = lean_unbox_usize(v_x_1152_);
lean_dec(v_x_1152_);
v_x_17528__boxed_1157_ = lean_unbox_usize(v_x_1153_);
lean_dec(v_x_1153_);
v_res_1158_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2(v_00_u03b2_1150_, v_x_1151_, v_x_17527__boxed_1156_, v_x_17528__boxed_1157_, v_x_1154_, v_x_1155_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1159_, lean_object* v_n_1160_, lean_object* v_k_1161_, lean_object* v_v_1162_){
_start:
{
lean_object* v___x_1163_; 
v___x_1163_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5___redArg(v_n_1160_, v_k_1161_, v_v_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_1164_, size_t v_depth_1165_, lean_object* v_keys_1166_, lean_object* v_vals_1167_, lean_object* v_heq_1168_, lean_object* v_i_1169_, lean_object* v_entries_1170_){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___redArg(v_depth_1165_, v_keys_1166_, v_vals_1167_, v_i_1169_, v_entries_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1172_, lean_object* v_depth_1173_, lean_object* v_keys_1174_, lean_object* v_vals_1175_, lean_object* v_heq_1176_, lean_object* v_i_1177_, lean_object* v_entries_1178_){
_start:
{
size_t v_depth_boxed_1179_; lean_object* v_res_1180_; 
v_depth_boxed_1179_ = lean_unbox_usize(v_depth_1173_);
lean_dec(v_depth_1173_);
v_res_1180_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6(v_00_u03b2_1172_, v_depth_boxed_1179_, v_keys_1174_, v_vals_1175_, v_heq_1176_, v_i_1177_, v_entries_1178_);
lean_dec_ref(v_vals_1175_);
lean_dec_ref(v_keys_1174_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5_spec__6(lean_object* v_00_u03b2_1181_, lean_object* v_x_1182_, lean_object* v_x_1183_, lean_object* v_x_1184_, lean_object* v_x_1185_){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(v_x_1182_, v_x_1183_, v_x_1184_, v_x_1185_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorIdx(lean_object* v_x_1187_){
_start:
{
if (lean_obj_tag(v_x_1187_) == 0)
{
lean_object* v___x_1188_; 
v___x_1188_ = lean_unsigned_to_nat(0u);
return v___x_1188_;
}
else
{
lean_object* v___x_1189_; 
v___x_1189_ = lean_unsigned_to_nat(1u);
return v___x_1189_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorIdx___boxed(lean_object* v_x_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Lean_Meta_InjectionResult_ctorIdx(v_x_1190_);
lean_dec(v_x_1190_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorElim___redArg(lean_object* v_t_1192_, lean_object* v_k_1193_){
_start:
{
if (lean_obj_tag(v_t_1192_) == 0)
{
return v_k_1193_;
}
else
{
lean_object* v_mvarId_1194_; lean_object* v_newEqs_1195_; lean_object* v_remainingNames_1196_; lean_object* v___x_1197_; 
v_mvarId_1194_ = lean_ctor_get(v_t_1192_, 0);
lean_inc(v_mvarId_1194_);
v_newEqs_1195_ = lean_ctor_get(v_t_1192_, 1);
lean_inc_ref(v_newEqs_1195_);
v_remainingNames_1196_ = lean_ctor_get(v_t_1192_, 2);
lean_inc(v_remainingNames_1196_);
lean_dec_ref_known(v_t_1192_, 3);
v___x_1197_ = lean_apply_3(v_k_1193_, v_mvarId_1194_, v_newEqs_1195_, v_remainingNames_1196_);
return v___x_1197_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorElim(lean_object* v_motive_1198_, lean_object* v_ctorIdx_1199_, lean_object* v_t_1200_, lean_object* v_h_1201_, lean_object* v_k_1202_){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_1200_, v_k_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorElim___boxed(lean_object* v_motive_1204_, lean_object* v_ctorIdx_1205_, lean_object* v_t_1206_, lean_object* v_h_1207_, lean_object* v_k_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Lean_Meta_InjectionResult_ctorElim(v_motive_1204_, v_ctorIdx_1205_, v_t_1206_, v_h_1207_, v_k_1208_);
lean_dec(v_ctorIdx_1205_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_solved_elim___redArg(lean_object* v_t_1210_, lean_object* v_solved_1211_){
_start:
{
lean_object* v___x_1212_; 
v___x_1212_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_1210_, v_solved_1211_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_solved_elim(lean_object* v_motive_1213_, lean_object* v_t_1214_, lean_object* v_h_1215_, lean_object* v_solved_1216_){
_start:
{
lean_object* v___x_1217_; 
v___x_1217_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_1214_, v_solved_1216_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_subgoal_elim___redArg(lean_object* v_t_1218_, lean_object* v_subgoal_1219_){
_start:
{
lean_object* v___x_1220_; 
v___x_1220_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_1218_, v_subgoal_1219_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_subgoal_elim(lean_object* v_motive_1221_, lean_object* v_t_1222_, lean_object* v_h_1223_, lean_object* v_subgoal_1224_){
_start:
{
lean_object* v___x_1225_; 
v___x_1225_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_1222_, v_subgoal_1224_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go(uint8_t v_tryToClear_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_){
_start:
{
lean_object* v_zero_1236_; uint8_t v_isZero_1237_; 
v_zero_1236_ = lean_unsigned_to_nat(0u);
v_isZero_1237_ = lean_nat_dec_eq(v_a_1227_, v_zero_1236_);
if (v_isZero_1237_ == 1)
{
lean_object* v___x_1238_; lean_object* v___x_1239_; 
lean_dec(v_a_1227_);
v___x_1238_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1238_, 0, v_a_1228_);
lean_ctor_set(v___x_1238_, 1, v_a_1229_);
lean_ctor_set(v___x_1238_, 2, v_a_1230_);
v___x_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1238_);
return v___x_1239_;
}
else
{
lean_object* v_one_1240_; lean_object* v_n_1241_; 
v_one_1240_ = lean_unsigned_to_nat(1u);
v_n_1241_ = lean_nat_sub(v_a_1227_, v_one_1240_);
lean_dec(v_a_1227_);
if (lean_obj_tag(v_a_1230_) == 0)
{
lean_object* v___x_1242_; 
v___x_1242_ = l_Lean_Meta_intro1Core(v_a_1228_, v_isZero_1237_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v_a_1243_; lean_object* v_fst_1244_; lean_object* v_snd_1245_; lean_object* v___x_1246_; 
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
lean_inc(v_a_1243_);
lean_dec_ref_known(v___x_1242_, 1);
v_fst_1244_ = lean_ctor_get(v_a_1243_, 0);
lean_inc(v_fst_1244_);
v_snd_1245_ = lean_ctor_get(v_a_1243_, 1);
lean_inc(v_snd_1245_);
lean_dec(v_a_1243_);
v___x_1246_ = l_Lean_Meta_heqToEq(v_snd_1245_, v_fst_1244_, v_tryToClear_1226_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; lean_object* v_fst_1248_; lean_object* v_snd_1249_; lean_object* v___x_1250_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_a_1247_);
lean_dec_ref_known(v___x_1246_, 1);
v_fst_1248_ = lean_ctor_get(v_a_1247_, 0);
lean_inc(v_fst_1248_);
v_snd_1249_ = lean_ctor_get(v_a_1247_, 1);
lean_inc(v_snd_1249_);
lean_dec(v_a_1247_);
v___x_1250_ = lean_array_push(v_a_1229_, v_fst_1248_);
v_a_1227_ = v_n_1241_;
v_a_1228_ = v_snd_1249_;
v_a_1229_ = v___x_1250_;
goto _start;
}
else
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1259_; 
lean_dec(v_n_1241_);
lean_dec_ref(v_a_1229_);
v_a_1252_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1254_ = v___x_1246_;
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1246_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1257_; 
if (v_isShared_1255_ == 0)
{
v___x_1257_ = v___x_1254_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_a_1252_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
else
{
lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1267_; 
lean_dec(v_n_1241_);
lean_dec_ref(v_a_1229_);
v_a_1260_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1262_ = v___x_1242_;
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v___x_1242_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1265_; 
if (v_isShared_1263_ == 0)
{
v___x_1265_ = v___x_1262_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_a_1260_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
}
else
{
lean_object* v_head_1268_; lean_object* v_tail_1269_; lean_object* v___x_1270_; 
v_head_1268_ = lean_ctor_get(v_a_1230_, 0);
lean_inc(v_head_1268_);
v_tail_1269_ = lean_ctor_get(v_a_1230_, 1);
lean_inc(v_tail_1269_);
lean_dec_ref_known(v_a_1230_, 2);
v___x_1270_ = l_Lean_MVarId_intro(v_a_1228_, v_head_1268_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v_a_1271_; lean_object* v_fst_1272_; lean_object* v_snd_1273_; lean_object* v___x_1274_; 
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_a_1271_);
lean_dec_ref_known(v___x_1270_, 1);
v_fst_1272_ = lean_ctor_get(v_a_1271_, 0);
lean_inc(v_fst_1272_);
v_snd_1273_ = lean_ctor_get(v_a_1271_, 1);
lean_inc(v_snd_1273_);
lean_dec(v_a_1271_);
v___x_1274_ = l_Lean_Meta_heqToEq(v_snd_1273_, v_fst_1272_, v_tryToClear_1226_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; lean_object* v_fst_1276_; lean_object* v_snd_1277_; lean_object* v___x_1278_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_a_1275_);
lean_dec_ref_known(v___x_1274_, 1);
v_fst_1276_ = lean_ctor_get(v_a_1275_, 0);
lean_inc(v_fst_1276_);
v_snd_1277_ = lean_ctor_get(v_a_1275_, 1);
lean_inc(v_snd_1277_);
lean_dec(v_a_1275_);
v___x_1278_ = lean_array_push(v_a_1229_, v_fst_1276_);
v_a_1227_ = v_n_1241_;
v_a_1228_ = v_snd_1277_;
v_a_1229_ = v___x_1278_;
v_a_1230_ = v_tail_1269_;
goto _start;
}
else
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
lean_dec(v_tail_1269_);
lean_dec(v_n_1241_);
lean_dec_ref(v_a_1229_);
v_a_1280_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1282_ = v___x_1274_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1274_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1283_ == 0)
{
v___x_1285_ = v___x_1282_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1280_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec(v_tail_1269_);
lean_dec(v_n_1241_);
lean_dec_ref(v_a_1229_);
v_a_1288_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1270_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1270_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go___boxed(lean_object* v_tryToClear_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_){
_start:
{
uint8_t v_tryToClear_boxed_1306_; lean_object* v_res_1307_; 
v_tryToClear_boxed_1306_ = lean_unbox(v_tryToClear_1296_);
v_res_1307_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go(v_tryToClear_boxed_1306_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
lean_dec(v_a_1304_);
lean_dec_ref(v_a_1303_);
lean_dec(v_a_1302_);
lean_dec_ref(v_a_1301_);
return v_res_1307_;
}
}
static lean_object* _init_l_Lean_Meta_injectionIntro___closed__2(void){
_start:
{
lean_object* v_cls_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v_cls_1314_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__1));
v___x_1315_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__0___closed__1));
v___x_1316_ = l_Lean_Name_append(v___x_1315_, v_cls_1314_);
return v___x_1316_;
}
}
static lean_object* _init_l_Lean_Meta_injectionIntro___closed__4(void){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__3));
v___x_1319_ = l_Lean_stringToMessageData(v___x_1318_);
return v___x_1319_;
}
}
static lean_object* _init_l_Lean_Meta_injectionIntro___closed__6(void){
_start:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1321_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__5));
v___x_1322_ = l_Lean_stringToMessageData(v___x_1321_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro(lean_object* v_mvarId_1323_, lean_object* v_numEqs_1324_, lean_object* v_newNames_1325_, uint8_t v_tryToClear_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_){
_start:
{
lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v_options_1339_; uint8_t v_hasTrace_1340_; 
v_options_1339_ = lean_ctor_get(v_a_1329_, 2);
v_hasTrace_1340_ = lean_ctor_get_uint8(v_options_1339_, sizeof(void*)*1);
if (v_hasTrace_1340_ == 0)
{
v___y_1333_ = v_a_1327_;
v___y_1334_ = v_a_1328_;
v___y_1335_ = v_a_1329_;
v___y_1336_ = v_a_1330_;
goto v___jp_1332_;
}
else
{
lean_object* v_inheritedTraceOptions_1341_; lean_object* v_cls_1342_; lean_object* v___x_1343_; uint8_t v___x_1344_; 
v_inheritedTraceOptions_1341_ = lean_ctor_get(v_a_1329_, 13);
v_cls_1342_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__1));
v___x_1343_ = lean_obj_once(&l_Lean_Meta_injectionIntro___closed__2, &l_Lean_Meta_injectionIntro___closed__2_once, _init_l_Lean_Meta_injectionIntro___closed__2);
v___x_1344_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1341_, v_options_1339_, v___x_1343_);
if (v___x_1344_ == 0)
{
v___y_1333_ = v_a_1327_;
v___y_1334_ = v_a_1328_;
v___y_1335_ = v_a_1329_;
v___y_1336_ = v_a_1330_;
goto v___jp_1332_;
}
else
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1345_ = lean_obj_once(&l_Lean_Meta_injectionIntro___closed__4, &l_Lean_Meta_injectionIntro___closed__4_once, _init_l_Lean_Meta_injectionIntro___closed__4);
lean_inc(v_numEqs_1324_);
v___x_1346_ = l_Nat_reprFast(v_numEqs_1324_);
v___x_1347_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1346_);
v___x_1348_ = l_Lean_MessageData_ofFormat(v___x_1347_);
v___x_1349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1345_);
lean_ctor_set(v___x_1349_, 1, v___x_1348_);
v___x_1350_ = lean_obj_once(&l_Lean_Meta_injectionIntro___closed__6, &l_Lean_Meta_injectionIntro___closed__6_once, _init_l_Lean_Meta_injectionIntro___closed__6);
v___x_1351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1349_);
lean_ctor_set(v___x_1351_, 1, v___x_1350_);
lean_inc(v_mvarId_1323_);
v___x_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1352_, 0, v_mvarId_1323_);
v___x_1353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1351_);
lean_ctor_set(v___x_1353_, 1, v___x_1352_);
v___x_1354_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v_cls_1342_, v___x_1353_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_dec_ref_known(v___x_1354_, 1);
v___y_1333_ = v_a_1327_;
v___y_1334_ = v_a_1328_;
v___y_1335_ = v_a_1329_;
v___y_1336_ = v_a_1330_;
goto v___jp_1332_;
}
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
lean_dec(v_newNames_1325_);
lean_dec(v_numEqs_1324_);
lean_dec(v_mvarId_1323_);
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___x_1354_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1354_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
}
v___jp_1332_:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1337_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__0));
v___x_1338_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go(v_tryToClear_1326_, v_numEqs_1324_, v_mvarId_1323_, v___x_1337_, v_newNames_1325_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
return v___x_1338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro___boxed(lean_object* v_mvarId_1363_, lean_object* v_numEqs_1364_, lean_object* v_newNames_1365_, lean_object* v_tryToClear_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_){
_start:
{
uint8_t v_tryToClear_boxed_1372_; lean_object* v_res_1373_; 
v_tryToClear_boxed_1372_ = lean_unbox(v_tryToClear_1366_);
v_res_1373_ = l_Lean_Meta_injectionIntro(v_mvarId_1363_, v_numEqs_1364_, v_newNames_1365_, v_tryToClear_boxed_1372_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_);
lean_dec(v_a_1370_);
lean_dec_ref(v_a_1369_);
lean_dec(v_a_1368_);
lean_dec_ref(v_a_1367_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injection(lean_object* v_mvarId_1374_, lean_object* v_fvarId_1375_, lean_object* v_newNames_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_){
_start:
{
lean_object* v___x_1382_; 
v___x_1382_ = l_Lean_Meta_injectionCore(v_mvarId_1374_, v_fvarId_1375_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1395_; 
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1385_ = v___x_1382_;
v_isShared_1386_ = v_isSharedCheck_1395_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1382_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1395_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
if (lean_obj_tag(v_a_1383_) == 0)
{
lean_object* v___x_1387_; lean_object* v___x_1389_; 
lean_dec(v_newNames_1376_);
v___x_1387_ = lean_box(0);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v___x_1387_);
v___x_1389_ = v___x_1385_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1387_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
else
{
lean_object* v_mvarId_1391_; lean_object* v_numNewEqs_1392_; uint8_t v___x_1393_; lean_object* v___x_1394_; 
lean_del_object(v___x_1385_);
v_mvarId_1391_ = lean_ctor_get(v_a_1383_, 0);
lean_inc(v_mvarId_1391_);
v_numNewEqs_1392_ = lean_ctor_get(v_a_1383_, 1);
lean_inc(v_numNewEqs_1392_);
lean_dec_ref_known(v_a_1383_, 2);
v___x_1393_ = 1;
v___x_1394_ = l_Lean_Meta_injectionIntro(v_mvarId_1391_, v_numNewEqs_1392_, v_newNames_1376_, v___x_1393_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
return v___x_1394_;
}
}
}
else
{
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1403_; 
lean_dec(v_newNames_1376_);
v_a_1396_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1398_ = v___x_1382_;
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1382_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1401_; 
if (v_isShared_1399_ == 0)
{
v___x_1401_ = v___x_1398_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_a_1396_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injection___boxed(lean_object* v_mvarId_1404_, lean_object* v_fvarId_1405_, lean_object* v_newNames_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_Lean_Meta_injection(v_mvarId_1404_, v_fvarId_1405_, v_newNames_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_);
lean_dec(v_a_1410_);
lean_dec_ref(v_a_1409_);
lean_dec(v_a_1408_);
lean_dec_ref(v_a_1407_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorIdx(lean_object* v_x_1413_){
_start:
{
if (lean_obj_tag(v_x_1413_) == 0)
{
lean_object* v___x_1414_; 
v___x_1414_ = lean_unsigned_to_nat(0u);
return v___x_1414_;
}
else
{
lean_object* v___x_1415_; 
v___x_1415_ = lean_unsigned_to_nat(1u);
return v___x_1415_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorIdx___boxed(lean_object* v_x_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_Lean_Meta_InjectionsResult_ctorIdx(v_x_1416_);
lean_dec(v_x_1416_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorElim___redArg(lean_object* v_t_1418_, lean_object* v_k_1419_){
_start:
{
if (lean_obj_tag(v_t_1418_) == 0)
{
return v_k_1419_;
}
else
{
lean_object* v_mvarId_1420_; lean_object* v_remainingNames_1421_; lean_object* v_forbidden_1422_; lean_object* v___x_1423_; 
v_mvarId_1420_ = lean_ctor_get(v_t_1418_, 0);
lean_inc(v_mvarId_1420_);
v_remainingNames_1421_ = lean_ctor_get(v_t_1418_, 1);
lean_inc(v_remainingNames_1421_);
v_forbidden_1422_ = lean_ctor_get(v_t_1418_, 2);
lean_inc(v_forbidden_1422_);
lean_dec_ref_known(v_t_1418_, 3);
v___x_1423_ = lean_apply_3(v_k_1419_, v_mvarId_1420_, v_remainingNames_1421_, v_forbidden_1422_);
return v___x_1423_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorElim(lean_object* v_motive_1424_, lean_object* v_ctorIdx_1425_, lean_object* v_t_1426_, lean_object* v_h_1427_, lean_object* v_k_1428_){
_start:
{
lean_object* v___x_1429_; 
v___x_1429_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1426_, v_k_1428_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorElim___boxed(lean_object* v_motive_1430_, lean_object* v_ctorIdx_1431_, lean_object* v_t_1432_, lean_object* v_h_1433_, lean_object* v_k_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l_Lean_Meta_InjectionsResult_ctorElim(v_motive_1430_, v_ctorIdx_1431_, v_t_1432_, v_h_1433_, v_k_1434_);
lean_dec(v_ctorIdx_1431_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_solved_elim___redArg(lean_object* v_t_1436_, lean_object* v_solved_1437_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1436_, v_solved_1437_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_solved_elim(lean_object* v_motive_1439_, lean_object* v_t_1440_, lean_object* v_h_1441_, lean_object* v_solved_1442_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1440_, v_solved_1442_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_subgoal_elim___redArg(lean_object* v_t_1444_, lean_object* v_subgoal_1445_){
_start:
{
lean_object* v___x_1446_; 
v___x_1446_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1444_, v_subgoal_1445_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_subgoal_elim(lean_object* v_motive_1447_, lean_object* v_t_1448_, lean_object* v_h_1449_, lean_object* v_subgoal_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1448_, v_subgoal_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(lean_object* v_x_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v___x_1458_; 
v___x_1458_ = l_Lean_Meta_saveState___redArg(v___y_1454_, v___y_1456_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v_a_1459_; lean_object* v___x_1460_; 
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
lean_inc(v_a_1459_);
lean_dec_ref_known(v___x_1458_, 1);
lean_inc(v___y_1456_);
lean_inc_ref(v___y_1455_);
lean_inc(v___y_1454_);
lean_inc_ref(v___y_1453_);
v___x_1460_ = lean_apply_5(v_x_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, lean_box(0));
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_dec(v_a_1459_);
return v___x_1460_;
}
else
{
lean_object* v_a_1461_; uint8_t v___y_1463_; uint8_t v___x_1481_; 
v_a_1461_ = lean_ctor_get(v___x_1460_, 0);
lean_inc(v_a_1461_);
v___x_1481_ = l_Lean_Exception_isInterrupt(v_a_1461_);
if (v___x_1481_ == 0)
{
uint8_t v___x_1482_; 
lean_inc(v_a_1461_);
v___x_1482_ = l_Lean_Exception_isRuntime(v_a_1461_);
v___y_1463_ = v___x_1482_;
goto v___jp_1462_;
}
else
{
v___y_1463_ = v___x_1481_;
goto v___jp_1462_;
}
v___jp_1462_:
{
if (v___y_1463_ == 0)
{
lean_object* v___x_1464_; 
lean_dec_ref_known(v___x_1460_, 1);
v___x_1464_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1459_, v___y_1454_, v___y_1456_);
lean_dec(v_a_1459_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1471_ == 0)
{
lean_object* v_unused_1472_; 
v_unused_1472_ = lean_ctor_get(v___x_1464_, 0);
lean_dec(v_unused_1472_);
v___x_1466_ = v___x_1464_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_dec(v___x_1464_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
lean_ctor_set_tag(v___x_1466_, 1);
lean_ctor_set(v___x_1466_, 0, v_a_1461_);
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_a_1461_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
else
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
lean_dec(v_a_1461_);
v_a_1473_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1464_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1464_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
else
{
lean_dec(v_a_1461_);
lean_dec(v_a_1459_);
return v___x_1460_;
}
}
}
}
else
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1490_; 
lean_dec_ref(v_x_1452_);
v_a_1483_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1485_ = v___x_1458_;
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1458_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1486_ == 0)
{
v___x_1488_ = v___x_1485_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1483_);
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
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg___boxed(lean_object* v_x_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
lean_object* v_res_1497_; 
v_res_1497_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(v_x_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1(lean_object* v_00_u03b1_1498_, lean_object* v_x_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
lean_object* v___x_1505_; 
v___x_1505_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(v_x_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___boxed(lean_object* v_00_u03b1_1506_, lean_object* v_x_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1(v_00_u03b1_1506_, v_x_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
return v_res_1513_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(lean_object* v_k_1514_, lean_object* v_t_1515_){
_start:
{
if (lean_obj_tag(v_t_1515_) == 0)
{
lean_object* v_k_1516_; lean_object* v_l_1517_; lean_object* v_r_1518_; uint8_t v___x_1519_; 
v_k_1516_ = lean_ctor_get(v_t_1515_, 1);
v_l_1517_ = lean_ctor_get(v_t_1515_, 3);
v_r_1518_ = lean_ctor_get(v_t_1515_, 4);
v___x_1519_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1514_, v_k_1516_);
switch(v___x_1519_)
{
case 0:
{
v_t_1515_ = v_l_1517_;
goto _start;
}
case 1:
{
uint8_t v___x_1521_; 
v___x_1521_ = 1;
return v___x_1521_;
}
default: 
{
v_t_1515_ = v_r_1518_;
goto _start;
}
}
}
else
{
uint8_t v___x_1523_; 
v___x_1523_ = 0;
return v___x_1523_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg___boxed(lean_object* v_k_1524_, lean_object* v_t_1525_){
_start:
{
uint8_t v_res_1526_; lean_object* v_r_1527_; 
v_res_1526_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(v_k_1524_, v_t_1525_);
lean_dec(v_t_1525_);
lean_dec(v_k_1524_);
v_r_1527_ = lean_box(v_res_1526_);
return v_r_1527_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4(void){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__3));
v___x_1535_ = l_Lean_MessageData_ofFormat(v___x_1534_);
return v___x_1535_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5(void){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1536_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4, &l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4_once, _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4);
v___x_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1536_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0___boxed(lean_object* v_mvarId_1538_, lean_object* v_head_1539_, lean_object* v_newNames_1540_, lean_object* v_tail_1541_, lean_object* v_forbidden_1542_, lean_object* v_n_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0(v_mvarId_1538_, v_head_1539_, v_newNames_1540_, v_tail_1541_, v_forbidden_1542_, v_n_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go(lean_object* v_depth_1550_, lean_object* v_fvarIds_1551_, lean_object* v_mvarId_1552_, lean_object* v_newNames_1553_, lean_object* v_forbidden_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_){
_start:
{
lean_object* v_zero_1560_; uint8_t v_isZero_1561_; 
v_zero_1560_ = lean_unsigned_to_nat(0u);
v_isZero_1561_ = lean_nat_dec_eq(v_depth_1550_, v_zero_1560_);
if (v_isZero_1561_ == 1)
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
lean_dec(v_forbidden_1554_);
lean_dec(v_newNames_1553_);
lean_dec(v_fvarIds_1551_);
lean_dec(v_depth_1550_);
v___x_1562_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__1));
v___x_1563_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5, &l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5_once, _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5);
v___x_1564_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1562_, v_mvarId_1552_, v___x_1563_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_);
return v___x_1564_;
}
else
{
if (lean_obj_tag(v_fvarIds_1551_) == 0)
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
lean_dec(v_depth_1550_);
v___x_1565_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1565_, 0, v_mvarId_1552_);
lean_ctor_set(v___x_1565_, 1, v_newNames_1553_);
lean_ctor_set(v___x_1565_, 2, v_forbidden_1554_);
v___x_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
return v___x_1566_;
}
else
{
lean_object* v_head_1567_; lean_object* v_tail_1568_; lean_object* v_one_1569_; lean_object* v_n_1570_; lean_object* v___x_1571_; lean_object* v___y_1573_; uint8_t v___y_1574_; uint8_t v___x_1576_; 
v_head_1567_ = lean_ctor_get(v_fvarIds_1551_, 0);
lean_inc(v_head_1567_);
v_tail_1568_ = lean_ctor_get(v_fvarIds_1551_, 1);
lean_inc(v_tail_1568_);
lean_dec_ref_known(v_fvarIds_1551_, 2);
v_one_1569_ = lean_unsigned_to_nat(1u);
v_n_1570_ = lean_nat_sub(v_depth_1550_, v_one_1569_);
lean_dec(v_depth_1550_);
v___x_1571_ = lean_nat_add(v_n_1570_, v_one_1569_);
v___x_1576_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(v_head_1567_, v_forbidden_1554_);
if (v___x_1576_ == 0)
{
lean_object* v___x_1577_; 
lean_inc(v_head_1567_);
v___x_1577_ = l_Lean_FVarId_getType___redArg(v_head_1567_, v_a_1555_, v_a_1557_, v_a_1558_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; lean_object* v___x_1579_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1578_);
lean_dec_ref_known(v___x_1577_, 1);
v___x_1579_ = l_Lean_Meta_matchEqHEq_x3f(v_a_1578_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
lean_dec_ref_known(v___x_1579_, 1);
if (lean_obj_tag(v_a_1580_) == 1)
{
lean_object* v_val_1581_; lean_object* v_snd_1582_; lean_object* v_fst_1583_; lean_object* v_snd_1584_; lean_object* v___x_1585_; 
v_val_1581_ = lean_ctor_get(v_a_1580_, 0);
lean_inc(v_val_1581_);
lean_dec_ref_known(v_a_1580_, 1);
v_snd_1582_ = lean_ctor_get(v_val_1581_, 1);
lean_inc(v_snd_1582_);
lean_dec(v_val_1581_);
v_fst_1583_ = lean_ctor_get(v_snd_1582_, 0);
lean_inc(v_fst_1583_);
v_snd_1584_ = lean_ctor_get(v_snd_1582_, 1);
lean_inc(v_snd_1584_);
lean_dec(v_snd_1582_);
lean_inc(v_a_1558_);
lean_inc_ref(v_a_1557_);
lean_inc(v_a_1556_);
lean_inc_ref(v_a_1555_);
v___x_1585_ = lean_whnf(v_fst_1583_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; lean_object* v___x_1587_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_a_1586_);
lean_dec_ref_known(v___x_1585_, 1);
lean_inc(v_a_1558_);
lean_inc_ref(v_a_1557_);
lean_inc(v_a_1556_);
lean_inc_ref(v_a_1555_);
v___x_1587_ = lean_whnf(v_snd_1584_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v___f_1589_; uint8_t v___y_1591_; uint8_t v___x_1597_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_a_1588_);
lean_dec_ref_known(v___x_1587_, 1);
lean_inc(v_forbidden_1554_);
lean_inc(v_tail_1568_);
lean_inc(v_newNames_1553_);
lean_inc(v_mvarId_1552_);
v___f_1589_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0___boxed), 11, 6);
lean_closure_set(v___f_1589_, 0, v_mvarId_1552_);
lean_closure_set(v___f_1589_, 1, v_head_1567_);
lean_closure_set(v___f_1589_, 2, v_newNames_1553_);
lean_closure_set(v___f_1589_, 3, v_tail_1568_);
lean_closure_set(v___f_1589_, 4, v_forbidden_1554_);
lean_closure_set(v___f_1589_, 5, v_n_1570_);
v___x_1597_ = l_Lean_Expr_isRawNatLit(v_a_1586_);
lean_dec(v_a_1586_);
if (v___x_1597_ == 0)
{
lean_dec(v_a_1588_);
v___y_1591_ = v___x_1597_;
goto v___jp_1590_;
}
else
{
uint8_t v___x_1598_; 
v___x_1598_ = l_Lean_Expr_isRawNatLit(v_a_1588_);
lean_dec(v_a_1588_);
v___y_1591_ = v___x_1598_;
goto v___jp_1590_;
}
v___jp_1590_:
{
if (v___y_1591_ == 0)
{
lean_object* v___x_1592_; 
v___x_1592_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(v___f_1589_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_dec(v___x_1571_);
lean_dec(v_tail_1568_);
lean_dec(v_forbidden_1554_);
lean_dec(v_newNames_1553_);
lean_dec(v_mvarId_1552_);
return v___x_1592_;
}
else
{
lean_object* v_a_1593_; uint8_t v___x_1594_; 
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
lean_inc(v_a_1593_);
v___x_1594_ = l_Lean_Exception_isInterrupt(v_a_1593_);
if (v___x_1594_ == 0)
{
uint8_t v___x_1595_; 
v___x_1595_ = l_Lean_Exception_isRuntime(v_a_1593_);
v___y_1573_ = v___x_1592_;
v___y_1574_ = v___x_1595_;
goto v___jp_1572_;
}
else
{
lean_dec(v_a_1593_);
v___y_1573_ = v___x_1592_;
v___y_1574_ = v___x_1594_;
goto v___jp_1572_;
}
}
}
else
{
lean_dec_ref(v___f_1589_);
v_depth_1550_ = v___x_1571_;
v_fvarIds_1551_ = v_tail_1568_;
goto _start;
}
}
}
else
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
lean_dec(v_a_1586_);
lean_dec(v___x_1571_);
lean_dec(v_n_1570_);
lean_dec(v_tail_1568_);
lean_dec(v_head_1567_);
lean_dec(v_forbidden_1554_);
lean_dec(v_newNames_1553_);
lean_dec(v_mvarId_1552_);
v_a_1599_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___x_1587_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1587_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1599_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
else
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
lean_dec(v_snd_1584_);
lean_dec(v___x_1571_);
lean_dec(v_n_1570_);
lean_dec(v_tail_1568_);
lean_dec(v_head_1567_);
lean_dec(v_forbidden_1554_);
lean_dec(v_newNames_1553_);
lean_dec(v_mvarId_1552_);
v_a_1607_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1585_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1585_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
else
{
lean_dec(v_a_1580_);
lean_dec(v_n_1570_);
lean_dec(v_head_1567_);
v_depth_1550_ = v___x_1571_;
v_fvarIds_1551_ = v_tail_1568_;
goto _start;
}
}
else
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1623_; 
lean_dec(v___x_1571_);
lean_dec(v_n_1570_);
lean_dec(v_tail_1568_);
lean_dec(v_head_1567_);
lean_dec(v_forbidden_1554_);
lean_dec(v_newNames_1553_);
lean_dec(v_mvarId_1552_);
v_a_1616_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1618_ = v___x_1579_;
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1579_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1619_ == 0)
{
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1616_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
else
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
lean_dec(v___x_1571_);
lean_dec(v_n_1570_);
lean_dec(v_tail_1568_);
lean_dec(v_head_1567_);
lean_dec(v_forbidden_1554_);
lean_dec(v_newNames_1553_);
lean_dec(v_mvarId_1552_);
v_a_1624_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1626_ = v___x_1577_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1577_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1624_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
else
{
lean_dec(v_n_1570_);
lean_dec(v_head_1567_);
v_depth_1550_ = v___x_1571_;
v_fvarIds_1551_ = v_tail_1568_;
goto _start;
}
v___jp_1572_:
{
if (v___y_1574_ == 0)
{
lean_dec_ref(v___y_1573_);
v_depth_1550_ = v___x_1571_;
v_fvarIds_1551_ = v_tail_1568_;
goto _start;
}
else
{
lean_dec(v___x_1571_);
lean_dec(v_tail_1568_);
lean_dec(v_forbidden_1554_);
lean_dec(v_newNames_1553_);
lean_dec(v_mvarId_1552_);
return v___y_1573_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___boxed(lean_object* v_depth_1633_, lean_object* v_fvarIds_1634_, lean_object* v_mvarId_1635_, lean_object* v_newNames_1636_, lean_object* v_forbidden_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go(v_depth_1633_, v_fvarIds_1634_, v_mvarId_1635_, v_newNames_1636_, v_forbidden_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_);
lean_dec(v_a_1641_);
lean_dec_ref(v_a_1640_);
lean_dec(v_a_1639_);
lean_dec_ref(v_a_1638_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0(lean_object* v_mvarId_1644_, lean_object* v_head_1645_, lean_object* v_newNames_1646_, lean_object* v_tail_1647_, lean_object* v_forbidden_1648_, lean_object* v_n_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
lean_object* v___x_1655_; 
lean_inc(v_head_1645_);
v___x_1655_ = l_Lean_Meta_injection(v_mvarId_1644_, v_head_1645_, v_newNames_1646_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1672_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1658_ = v___x_1655_;
v_isShared_1659_ = v_isSharedCheck_1672_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1655_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1672_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
if (lean_obj_tag(v_a_1656_) == 0)
{
lean_object* v___x_1660_; lean_object* v___x_1662_; 
lean_dec(v_n_1649_);
lean_dec(v_forbidden_1648_);
lean_dec(v_tail_1647_);
lean_dec(v_head_1645_);
v___x_1660_ = lean_box(0);
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 0, v___x_1660_);
v___x_1662_ = v___x_1658_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v___x_1660_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
else
{
lean_object* v_mvarId_1664_; lean_object* v_newEqs_1665_; lean_object* v_remainingNames_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
lean_del_object(v___x_1658_);
v_mvarId_1664_ = lean_ctor_get(v_a_1656_, 0);
lean_inc_n(v_mvarId_1664_, 2);
v_newEqs_1665_ = lean_ctor_get(v_a_1656_, 1);
lean_inc_ref(v_newEqs_1665_);
v_remainingNames_1666_ = lean_ctor_get(v_a_1656_, 2);
lean_inc(v_remainingNames_1666_);
lean_dec_ref_known(v_a_1656_, 3);
v___x_1667_ = lean_array_to_list(v_newEqs_1665_);
v___x_1668_ = l_List_appendTR___redArg(v___x_1667_, v_tail_1647_);
v___x_1669_ = l_Lean_FVarIdSet_insert(v_forbidden_1648_, v_head_1645_);
v___x_1670_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___boxed), 10, 5);
lean_closure_set(v___x_1670_, 0, v_n_1649_);
lean_closure_set(v___x_1670_, 1, v___x_1668_);
lean_closure_set(v___x_1670_, 2, v_mvarId_1664_);
lean_closure_set(v___x_1670_, 3, v_remainingNames_1666_);
lean_closure_set(v___x_1670_, 4, v___x_1669_);
v___x_1671_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg(v_mvarId_1664_, v___x_1670_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
return v___x_1671_;
}
}
}
else
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1680_; 
lean_dec(v_n_1649_);
lean_dec(v_forbidden_1648_);
lean_dec(v_tail_1647_);
lean_dec(v_head_1645_);
v_a_1673_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1675_ = v___x_1655_;
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1655_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1676_ == 0)
{
v___x_1678_ = v___x_1675_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1673_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0(lean_object* v_00_u03b2_1681_, lean_object* v_k_1682_, lean_object* v_t_1683_){
_start:
{
uint8_t v___x_1684_; 
v___x_1684_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(v_k_1682_, v_t_1683_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___boxed(lean_object* v_00_u03b2_1685_, lean_object* v_k_1686_, lean_object* v_t_1687_){
_start:
{
uint8_t v_res_1688_; lean_object* v_r_1689_; 
v_res_1688_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0(v_00_u03b2_1685_, v_k_1686_, v_t_1687_);
lean_dec(v_t_1687_);
lean_dec(v_k_1686_);
v_r_1689_ = lean_box(v_res_1688_);
return v_r_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections___lam__0(lean_object* v_maxDepth_1690_, lean_object* v_mvarId_1691_, lean_object* v_newNames_1692_, lean_object* v_forbidden_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
lean_object* v_lctx_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
v_lctx_1699_ = lean_ctor_get(v___y_1694_, 2);
v___x_1700_ = l_Lean_LocalContext_getFVarIds(v_lctx_1699_);
v___x_1701_ = lean_array_to_list(v___x_1700_);
v___x_1702_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go(v_maxDepth_1690_, v___x_1701_, v_mvarId_1691_, v_newNames_1692_, v_forbidden_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections___lam__0___boxed(lean_object* v_maxDepth_1703_, lean_object* v_mvarId_1704_, lean_object* v_newNames_1705_, lean_object* v_forbidden_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Lean_Meta_injections___lam__0(v_maxDepth_1703_, v_mvarId_1704_, v_newNames_1705_, v_forbidden_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections(lean_object* v_mvarId_1713_, lean_object* v_newNames_1714_, lean_object* v_maxDepth_1715_, lean_object* v_forbidden_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_){
_start:
{
lean_object* v___f_1722_; lean_object* v___x_1723_; 
lean_inc(v_mvarId_1713_);
v___f_1722_ = lean_alloc_closure((void*)(l_Lean_Meta_injections___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1722_, 0, v_maxDepth_1715_);
lean_closure_set(v___f_1722_, 1, v_mvarId_1713_);
lean_closure_set(v___f_1722_, 2, v_newNames_1714_);
lean_closure_set(v___f_1722_, 3, v_forbidden_1716_);
v___x_1723_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg(v_mvarId_1713_, v___f_1722_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections___boxed(lean_object* v_mvarId_1724_, lean_object* v_newNames_1725_, lean_object* v_maxDepth_1726_, lean_object* v_forbidden_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l_Lean_Meta_injections(v_mvarId_1724_, v_newNames_1725_, v_maxDepth_1726_, v_forbidden_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_);
lean_dec(v_a_1731_);
lean_dec_ref(v_a_1730_);
lean_dec(v_a_1729_);
lean_dec_ref(v_a_1728_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1790_; uint8_t v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1790_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__1));
v___x_1791_ = 0;
v___x_1792_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__22_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_));
v___x_1793_ = l_Lean_registerTraceClass(v___x_1790_, v___x_1791_, v___x_1792_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2____boxed(lean_object* v_a_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l___private_Lean_Meta_Tactic_Injection_0__initFn_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_();
return v_res_1795_;
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
