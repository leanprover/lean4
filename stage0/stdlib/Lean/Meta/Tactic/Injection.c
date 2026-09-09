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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
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
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
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
lean_object* v_toCold_302_; lean_object* v_options_303_; uint8_t v_hasTrace_304_; 
v_toCold_302_ = lean_ctor_get(v___y_299_, 0);
v_options_303_ = lean_ctor_get(v_toCold_302_, 2);
v_hasTrace_304_ = lean_ctor_get_uint8(v_options_303_, sizeof(void*)*1);
if (v_hasTrace_304_ == 0)
{
lean_object* v___x_305_; lean_object* v___x_306_; 
lean_dec(v___x_296_);
v___x_305_ = lean_box(v_hasTrace_304_);
v___x_306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
return v___x_306_;
}
else
{
lean_object* v_inheritedTraceOptions_307_; lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v_inheritedTraceOptions_307_ = lean_ctor_get(v_toCold_302_, 11);
v___x_308_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__0___closed__1));
v___x_309_ = l_Lean_Name_append(v___x_308_, v___x_296_);
v___x_310_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_307_, v_options_303_, v___x_309_);
lean_dec(v___x_309_);
v___x_311_ = lean_box(v___x_310_);
v___x_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
return v___x_312_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___lam__0___boxed(lean_object* v___x_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_Meta_injectionCore___lam__0(v___x_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1_spec__2(lean_object* v_msgData_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v___x_326_; lean_object* v_env_327_; lean_object* v___x_328_; lean_object* v_toCold_329_; lean_object* v_mctx_330_; lean_object* v_lctx_331_; lean_object* v_options_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_326_ = lean_st_ref_get(v___y_324_);
v_env_327_ = lean_ctor_get(v___x_326_, 0);
lean_inc_ref(v_env_327_);
lean_dec(v___x_326_);
v___x_328_ = lean_st_ref_get(v___y_322_);
v_toCold_329_ = lean_ctor_get(v___y_323_, 0);
v_mctx_330_ = lean_ctor_get(v___x_328_, 0);
lean_inc_ref(v_mctx_330_);
lean_dec(v___x_328_);
v_lctx_331_ = lean_ctor_get(v___y_321_, 2);
v_options_332_ = lean_ctor_get(v_toCold_329_, 2);
lean_inc_ref(v_options_332_);
lean_inc_ref(v_lctx_331_);
v___x_333_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_333_, 0, v_env_327_);
lean_ctor_set(v___x_333_, 1, v_mctx_330_);
lean_ctor_set(v___x_333_, 2, v_lctx_331_);
lean_ctor_set(v___x_333_, 3, v_options_332_);
v___x_334_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
lean_ctor_set(v___x_334_, 1, v_msgData_320_);
v___x_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1_spec__2___boxed(lean_object* v_msgData_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1_spec__2(v_msgData_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
return v_res_342_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__0(void){
_start:
{
lean_object* v___x_343_; double v___x_344_; 
v___x_343_ = lean_unsigned_to_nat(0u);
v___x_344_ = lean_float_of_nat(v___x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(lean_object* v_cls_348_, lean_object* v_msg_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v_ref_355_; lean_object* v___x_356_; lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_401_; 
v_ref_355_ = lean_ctor_get(v___y_352_, 2);
v___x_356_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1_spec__2(v_msg_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_);
v_a_357_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_401_ == 0)
{
v___x_359_ = v___x_356_;
v_isShared_360_ = v_isSharedCheck_401_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_356_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_401_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_361_; lean_object* v_traceState_362_; lean_object* v_env_363_; lean_object* v_nextMacroScope_364_; lean_object* v_ngen_365_; lean_object* v_auxDeclNGen_366_; lean_object* v_cache_367_; lean_object* v_messages_368_; lean_object* v_infoState_369_; lean_object* v_snapshotTasks_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_400_; 
v___x_361_ = lean_st_ref_take(v___y_353_);
v_traceState_362_ = lean_ctor_get(v___x_361_, 4);
v_env_363_ = lean_ctor_get(v___x_361_, 0);
v_nextMacroScope_364_ = lean_ctor_get(v___x_361_, 1);
v_ngen_365_ = lean_ctor_get(v___x_361_, 2);
v_auxDeclNGen_366_ = lean_ctor_get(v___x_361_, 3);
v_cache_367_ = lean_ctor_get(v___x_361_, 5);
v_messages_368_ = lean_ctor_get(v___x_361_, 6);
v_infoState_369_ = lean_ctor_get(v___x_361_, 7);
v_snapshotTasks_370_ = lean_ctor_get(v___x_361_, 8);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_400_ == 0)
{
v___x_372_ = v___x_361_;
v_isShared_373_ = v_isSharedCheck_400_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_snapshotTasks_370_);
lean_inc(v_infoState_369_);
lean_inc(v_messages_368_);
lean_inc(v_cache_367_);
lean_inc(v_traceState_362_);
lean_inc(v_auxDeclNGen_366_);
lean_inc(v_ngen_365_);
lean_inc(v_nextMacroScope_364_);
lean_inc(v_env_363_);
lean_dec(v___x_361_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_400_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
uint64_t v_tid_374_; lean_object* v_traces_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_399_; 
v_tid_374_ = lean_ctor_get_uint64(v_traceState_362_, sizeof(void*)*1);
v_traces_375_ = lean_ctor_get(v_traceState_362_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v_traceState_362_);
if (v_isSharedCheck_399_ == 0)
{
v___x_377_ = v_traceState_362_;
v_isShared_378_ = v_isSharedCheck_399_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_traces_375_);
lean_dec(v_traceState_362_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_399_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_379_; double v___x_380_; uint8_t v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_389_; 
v___x_379_ = lean_box(0);
v___x_380_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__0);
v___x_381_ = 0;
v___x_382_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__1));
v___x_383_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_383_, 0, v_cls_348_);
lean_ctor_set(v___x_383_, 1, v___x_379_);
lean_ctor_set(v___x_383_, 2, v___x_382_);
lean_ctor_set_float(v___x_383_, sizeof(void*)*3, v___x_380_);
lean_ctor_set_float(v___x_383_, sizeof(void*)*3 + 8, v___x_380_);
lean_ctor_set_uint8(v___x_383_, sizeof(void*)*3 + 16, v___x_381_);
v___x_384_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__2));
v___x_385_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_385_, 0, v___x_383_);
lean_ctor_set(v___x_385_, 1, v_a_357_);
lean_ctor_set(v___x_385_, 2, v___x_384_);
lean_inc(v_ref_355_);
v___x_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_386_, 0, v_ref_355_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
v___x_387_ = l_Lean_PersistentArray_push___redArg(v_traces_375_, v___x_386_);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 0, v___x_387_);
v___x_389_ = v___x_377_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_387_);
lean_ctor_set_uint64(v_reuseFailAlloc_398_, sizeof(void*)*1, v_tid_374_);
v___x_389_ = v_reuseFailAlloc_398_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
lean_object* v___x_391_; 
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 4, v___x_389_);
v___x_391_ = v___x_372_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_env_363_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v_nextMacroScope_364_);
lean_ctor_set(v_reuseFailAlloc_397_, 2, v_ngen_365_);
lean_ctor_set(v_reuseFailAlloc_397_, 3, v_auxDeclNGen_366_);
lean_ctor_set(v_reuseFailAlloc_397_, 4, v___x_389_);
lean_ctor_set(v_reuseFailAlloc_397_, 5, v_cache_367_);
lean_ctor_set(v_reuseFailAlloc_397_, 6, v_messages_368_);
lean_ctor_set(v_reuseFailAlloc_397_, 7, v_infoState_369_);
lean_ctor_set(v_reuseFailAlloc_397_, 8, v_snapshotTasks_370_);
v___x_391_ = v_reuseFailAlloc_397_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_395_; 
v___x_392_ = lean_st_ref_put(v___y_353_, v___x_391_);
v___x_393_ = lean_box(0);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 0, v___x_393_);
v___x_395_ = v___x_359_;
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
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___boxed(lean_object* v_cls_402_, lean_object* v_msg_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v_cls_402_, v_msg_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(lean_object* v_x_410_, lean_object* v_x_411_, lean_object* v_x_412_, lean_object* v_x_413_){
_start:
{
lean_object* v_ks_414_; lean_object* v_vs_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_439_; 
v_ks_414_ = lean_ctor_get(v_x_410_, 0);
v_vs_415_ = lean_ctor_get(v_x_410_, 1);
v_isSharedCheck_439_ = !lean_is_exclusive(v_x_410_);
if (v_isSharedCheck_439_ == 0)
{
v___x_417_ = v_x_410_;
v_isShared_418_ = v_isSharedCheck_439_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_vs_415_);
lean_inc(v_ks_414_);
lean_dec(v_x_410_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_439_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; uint8_t v___x_420_; 
v___x_419_ = lean_array_get_size(v_ks_414_);
v___x_420_ = lean_nat_dec_lt(v_x_411_, v___x_419_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_424_; 
lean_dec(v_x_411_);
v___x_421_ = lean_array_push(v_ks_414_, v_x_412_);
v___x_422_ = lean_array_push(v_vs_415_, v_x_413_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 1, v___x_422_);
lean_ctor_set(v___x_417_, 0, v___x_421_);
v___x_424_ = v___x_417_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_421_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v___x_422_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
else
{
lean_object* v_k_x27_426_; uint8_t v___x_427_; 
v_k_x27_426_ = lean_array_fget_borrowed(v_ks_414_, v_x_411_);
v___x_427_ = l_Lean_instBEqMVarId_beq(v_x_412_, v_k_x27_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_429_; 
if (v_isShared_418_ == 0)
{
v___x_429_ = v___x_417_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_ks_414_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_vs_415_);
v___x_429_ = v_reuseFailAlloc_433_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = lean_unsigned_to_nat(1u);
v___x_431_ = lean_nat_add(v_x_411_, v___x_430_);
lean_dec(v_x_411_);
v_x_410_ = v___x_429_;
v_x_411_ = v___x_431_;
goto _start;
}
}
else
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_437_; 
v___x_434_ = lean_array_fset(v_ks_414_, v_x_411_, v_x_412_);
v___x_435_ = lean_array_fset(v_vs_415_, v_x_411_, v_x_413_);
lean_dec(v_x_411_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 1, v___x_435_);
lean_ctor_set(v___x_417_, 0, v___x_434_);
v___x_437_ = v___x_417_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v___x_434_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v___x_435_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_n_440_, lean_object* v_k_441_, lean_object* v_v_442_){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = lean_unsigned_to_nat(0u);
v___x_444_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(v_n_440_, v___x_443_, v_k_441_, v_v_442_);
return v___x_444_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(lean_object* v_x_446_, size_t v_x_447_, size_t v_x_448_, lean_object* v_x_449_, lean_object* v_x_450_){
_start:
{
if (lean_obj_tag(v_x_446_) == 0)
{
lean_object* v_es_451_; size_t v___x_452_; size_t v___x_453_; lean_object* v_j_454_; lean_object* v___x_455_; uint8_t v___x_456_; 
v_es_451_ = lean_ctor_get(v_x_446_, 0);
v___x_452_ = ((size_t)31ULL);
v___x_453_ = lean_usize_land(v_x_447_, v___x_452_);
v_j_454_ = lean_usize_to_nat(v___x_453_);
v___x_455_ = lean_array_get_size(v_es_451_);
v___x_456_ = lean_nat_dec_lt(v_j_454_, v___x_455_);
if (v___x_456_ == 0)
{
lean_dec(v_j_454_);
lean_dec(v_x_450_);
lean_dec(v_x_449_);
return v_x_446_;
}
else
{
lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_495_; 
lean_inc_ref(v_es_451_);
v_isSharedCheck_495_ = !lean_is_exclusive(v_x_446_);
if (v_isSharedCheck_495_ == 0)
{
lean_object* v_unused_496_; 
v_unused_496_ = lean_ctor_get(v_x_446_, 0);
lean_dec(v_unused_496_);
v___x_458_ = v_x_446_;
v_isShared_459_ = v_isSharedCheck_495_;
goto v_resetjp_457_;
}
else
{
lean_dec(v_x_446_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_495_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v_v_460_; lean_object* v___x_461_; lean_object* v_xs_x27_462_; lean_object* v___y_464_; 
v_v_460_ = lean_array_fget(v_es_451_, v_j_454_);
v___x_461_ = lean_box(0);
v_xs_x27_462_ = lean_array_fset(v_es_451_, v_j_454_, v___x_461_);
switch(lean_obj_tag(v_v_460_))
{
case 0:
{
lean_object* v_key_469_; lean_object* v_val_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_480_; 
v_key_469_ = lean_ctor_get(v_v_460_, 0);
v_val_470_ = lean_ctor_get(v_v_460_, 1);
v_isSharedCheck_480_ = !lean_is_exclusive(v_v_460_);
if (v_isSharedCheck_480_ == 0)
{
v___x_472_ = v_v_460_;
v_isShared_473_ = v_isSharedCheck_480_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_val_470_);
lean_inc(v_key_469_);
lean_dec(v_v_460_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_480_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
uint8_t v___x_474_; 
v___x_474_ = l_Lean_instBEqMVarId_beq(v_x_449_, v_key_469_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; lean_object* v___x_476_; 
lean_del_object(v___x_472_);
v___x_475_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_469_, v_val_470_, v_x_449_, v_x_450_);
v___x_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
v___y_464_ = v___x_476_;
goto v___jp_463_;
}
else
{
lean_object* v___x_478_; 
lean_dec(v_val_470_);
lean_dec(v_key_469_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 1, v_x_450_);
lean_ctor_set(v___x_472_, 0, v_x_449_);
v___x_478_ = v___x_472_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_x_449_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v_x_450_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
v___y_464_ = v___x_478_;
goto v___jp_463_;
}
}
}
}
case 1:
{
lean_object* v_node_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_493_; 
v_node_481_ = lean_ctor_get(v_v_460_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v_v_460_);
if (v_isSharedCheck_493_ == 0)
{
v___x_483_ = v_v_460_;
v_isShared_484_ = v_isSharedCheck_493_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_node_481_);
lean_dec(v_v_460_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_493_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
size_t v___x_485_; size_t v___x_486_; size_t v___x_487_; size_t v___x_488_; lean_object* v___x_489_; lean_object* v___x_491_; 
v___x_485_ = ((size_t)5ULL);
v___x_486_ = lean_usize_shift_right(v_x_447_, v___x_485_);
v___x_487_ = ((size_t)1ULL);
v___x_488_ = lean_usize_add(v_x_448_, v___x_487_);
v___x_489_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(v_node_481_, v___x_486_, v___x_488_, v_x_449_, v_x_450_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 0, v___x_489_);
v___x_491_ = v___x_483_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_489_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
v___y_464_ = v___x_491_;
goto v___jp_463_;
}
}
}
default: 
{
lean_object* v___x_494_; 
v___x_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_494_, 0, v_x_449_);
lean_ctor_set(v___x_494_, 1, v_x_450_);
v___y_464_ = v___x_494_;
goto v___jp_463_;
}
}
v___jp_463_:
{
lean_object* v___x_465_; lean_object* v___x_467_; 
v___x_465_ = lean_array_fset(v_xs_x27_462_, v_j_454_, v___y_464_);
lean_dec(v_j_454_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 0, v___x_465_);
v___x_467_ = v___x_458_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_465_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
}
else
{
lean_object* v_ks_497_; lean_object* v_vs_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_516_; 
v_ks_497_ = lean_ctor_get(v_x_446_, 0);
v_vs_498_ = lean_ctor_get(v_x_446_, 1);
v_isSharedCheck_516_ = !lean_is_exclusive(v_x_446_);
if (v_isSharedCheck_516_ == 0)
{
v___x_500_ = v_x_446_;
v_isShared_501_ = v_isSharedCheck_516_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_vs_498_);
lean_inc(v_ks_497_);
lean_dec(v_x_446_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_516_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_ks_497_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_vs_498_);
v___x_503_ = v_reuseFailAlloc_515_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
lean_object* v_newNode_504_; size_t v___x_505_; uint8_t v___x_506_; 
v_newNode_504_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5___redArg(v___x_503_, v_x_449_, v_x_450_);
v___x_505_ = ((size_t)7ULL);
v___x_506_ = lean_usize_dec_le(v___x_505_, v_x_448_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; lean_object* v___x_508_; uint8_t v___x_509_; 
v___x_507_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_504_);
v___x_508_ = lean_unsigned_to_nat(4u);
v___x_509_ = lean_nat_dec_lt(v___x_507_, v___x_508_);
lean_dec(v___x_507_);
if (v___x_509_ == 0)
{
lean_object* v_ks_510_; lean_object* v_vs_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v_ks_510_ = lean_ctor_get(v_newNode_504_, 0);
lean_inc_ref(v_ks_510_);
v_vs_511_ = lean_ctor_get(v_newNode_504_, 1);
lean_inc_ref(v_vs_511_);
lean_dec_ref(v_newNode_504_);
v___x_512_ = lean_unsigned_to_nat(0u);
v___x_513_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_514_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___redArg(v_x_448_, v_ks_510_, v_vs_511_, v___x_512_, v___x_513_);
lean_dec_ref(v_vs_511_);
lean_dec_ref(v_ks_510_);
return v___x_514_;
}
else
{
return v_newNode_504_;
}
}
else
{
return v_newNode_504_;
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
size_t v_x_14490__boxed_549_; size_t v_x_14491__boxed_550_; lean_object* v_res_551_; 
v_x_14490__boxed_549_ = lean_unbox_usize(v_x_545_);
lean_dec(v_x_545_);
v_x_14491__boxed_550_ = lean_unbox_usize(v_x_546_);
lean_dec(v_x_546_);
v_res_551_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(v_x_544_, v_x_14490__boxed_549_, v_x_14491__boxed_550_, v_x_547_, v_x_548_);
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
lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v_type_915_; lean_object* v_prf_916_; lean_object* v___y_917_; lean_object* v___y_918_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___x_1000_; 
lean_inc(v___x_654_);
lean_inc(v_mvarId_653_);
v___x_1000_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_653_, v___x_654_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v___x_1001_; 
lean_dec_ref_known(v___x_1000_, 1);
lean_inc(v_fvarId_655_);
v___x_1001_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_655_, v___y_657_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_a_1002_);
lean_dec_ref_known(v___x_1001_, 1);
v___x_1003_ = l_Lean_LocalDecl_type(v_a_1002_);
lean_dec(v_a_1002_);
lean_inc(v___y_660_);
lean_inc_ref(v___y_659_);
lean_inc(v___y_658_);
lean_inc_ref(v___y_657_);
v___x_1004_ = lean_whnf(v___x_1003_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; uint8_t v___x_1009_; 
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_a_1005_);
lean_dec_ref_known(v___x_1004_, 1);
lean_inc(v_fvarId_655_);
v___x_1006_ = l_Lean_mkFVar(v_fvarId_655_);
v___x_1007_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__31));
v___x_1008_ = lean_unsigned_to_nat(4u);
v___x_1009_ = l_Lean_Expr_isAppOfArity(v_a_1005_, v___x_1007_, v___x_1008_);
if (v___x_1009_ == 0)
{
v_type_915_ = v_a_1005_;
v_prf_916_ = v___x_1006_;
v___y_917_ = v___y_657_;
v___y_918_ = v___y_658_;
v___y_919_ = v___y_659_;
v___y_920_ = v___y_660_;
goto v___jp_914_;
}
else
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1010_ = l_Lean_Expr_appFn_x21(v_a_1005_);
v___x_1011_ = l_Lean_Expr_appFn_x21(v___x_1010_);
v___x_1012_ = l_Lean_Expr_appFn_x21(v___x_1011_);
v___x_1013_ = l_Lean_Expr_appArg_x21(v___x_1012_);
lean_dec_ref(v___x_1012_);
v___x_1014_ = l_Lean_Expr_appArg_x21(v___x_1010_);
lean_dec_ref(v___x_1010_);
v___x_1015_ = l_Lean_Meta_isExprDefEq(v___x_1013_, v___x_1014_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_a_1016_; uint8_t v___x_1017_; 
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_a_1016_);
lean_dec_ref_known(v___x_1015_, 1);
v___x_1017_ = lean_unbox(v_a_1016_);
lean_dec(v_a_1016_);
if (v___x_1017_ == 0)
{
lean_dec_ref(v___x_1011_);
v_type_915_ = v_a_1005_;
v_prf_916_ = v___x_1006_;
v___y_917_ = v___y_657_;
v___y_918_ = v___y_658_;
v___y_919_ = v___y_659_;
v___y_920_ = v___y_660_;
goto v___jp_914_;
}
else
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1018_ = l_Lean_Expr_appArg_x21(v___x_1011_);
lean_dec_ref(v___x_1011_);
v___x_1019_ = l_Lean_Expr_appArg_x21(v_a_1005_);
lean_dec(v_a_1005_);
v___x_1020_ = l_Lean_Meta_mkEq(v___x_1018_, v___x_1019_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v___x_1022_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_a_1021_);
lean_dec_ref_known(v___x_1020_, 1);
v___x_1022_ = l_Lean_Meta_mkEqOfHEq(v___x_1006_, v___x_1009_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v_a_1023_; 
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
lean_inc(v_a_1023_);
lean_dec_ref_known(v___x_1022_, 1);
v_type_915_ = v_a_1021_;
v_prf_916_ = v_a_1023_;
v___y_917_ = v___y_657_;
v___y_918_ = v___y_658_;
v___y_919_ = v___y_659_;
v___y_920_ = v___y_660_;
goto v___jp_914_;
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
lean_dec(v_a_1021_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec_ref(v___x_656_);
lean_dec(v_fvarId_655_);
lean_dec(v___x_654_);
lean_dec(v_mvarId_653_);
v_a_1024_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_1022_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1022_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
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
lean_dec_ref(v___x_1006_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec_ref(v___x_656_);
lean_dec(v_fvarId_655_);
lean_dec(v___x_654_);
lean_dec(v_mvarId_653_);
v_a_1032_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_1020_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1020_);
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
}
else
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1047_; 
lean_dec_ref(v___x_1011_);
lean_dec_ref(v___x_1006_);
lean_dec(v_a_1005_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec_ref(v___x_656_);
lean_dec(v_fvarId_655_);
lean_dec(v___x_654_);
lean_dec(v_mvarId_653_);
v_a_1040_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1042_ = v___x_1015_;
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_1015_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1045_; 
if (v_isShared_1043_ == 0)
{
v___x_1045_ = v___x_1042_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_a_1040_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
}
else
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec_ref(v___x_656_);
lean_dec(v_fvarId_655_);
lean_dec(v___x_654_);
lean_dec(v_mvarId_653_);
v_a_1048_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1050_ = v___x_1004_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_1004_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1051_ == 0)
{
v___x_1053_ = v___x_1050_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1048_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec_ref(v___x_656_);
lean_dec(v_fvarId_655_);
lean_dec(v___x_654_);
lean_dec(v_mvarId_653_);
v_a_1056_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1001_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1001_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec_ref(v___x_656_);
lean_dec(v_fvarId_655_);
lean_dec(v___x_654_);
lean_dec(v_mvarId_653_);
v_a_1064_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1000_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1000_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
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
v_toConstantVal_691_ = lean_ctor_get(v___y_686_, 0);
v_toConstantVal_692_ = lean_ctor_get(v___y_683_, 0);
lean_inc_ref(v_toConstantVal_692_);
lean_dec_ref(v___y_683_);
v_numFields_693_ = lean_ctor_get(v___y_686_, 4);
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
lean_dec_ref(v___y_685_);
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
lean_inc(v___y_684_);
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
lean_dec_ref(v___y_685_);
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
lean_object* v_a_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_771_; 
v_a_716_ = lean_ctor_get(v___x_715_, 0);
lean_inc_n(v_a_716_, 2);
lean_dec_ref_known(v___x_715_, 1);
v___x_717_ = l_Lean_Expr_app___override(v___y_684_, v_a_716_);
v___x_718_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(v_mvarId_653_, v___x_717_, v___y_688_);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_771_ == 0)
{
lean_object* v_unused_772_; 
v_unused_772_ = lean_ctor_get(v___x_718_, 0);
lean_dec(v_unused_772_);
v___x_720_ = v___x_718_;
v_isShared_721_ = v_isSharedCheck_771_;
goto v_resetjp_719_;
}
else
{
lean_dec(v___x_718_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_771_;
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
v___x_725_ = l_Lean_Meta_getCtorNumPropFields(v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_toCold_726_; lean_object* v_options_727_; lean_object* v_a_728_; lean_object* v_inheritedTraceOptions_729_; uint8_t v_hasTrace_730_; lean_object* v___x_731_; 
v_toCold_726_ = lean_ctor_get(v___y_689_, 0);
v_options_727_ = lean_ctor_get(v_toCold_726_, 2);
v_a_728_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_a_728_);
lean_dec_ref_known(v___x_725_, 1);
v_inheritedTraceOptions_729_ = lean_ctor_get(v_toCold_726_, 11);
v_hasTrace_730_ = lean_ctor_get_uint8(v_options_727_, sizeof(void*)*1);
v___x_731_ = lean_nat_sub(v_numFields_693_, v_a_728_);
lean_dec(v_a_728_);
lean_dec(v_numFields_693_);
if (v_hasTrace_730_ == 0)
{
lean_del_object(v___x_720_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_682_);
v___y_677_ = v___x_731_;
v___y_678_ = v_a_724_;
goto v___jp_676_;
}
else
{
lean_object* v___x_732_; lean_object* v___x_733_; uint8_t v___x_734_; 
v___x_732_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__0___closed__1));
lean_inc(v___y_682_);
v___x_733_ = l_Lean_Name_append(v___x_732_, v___y_682_);
v___x_734_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_729_, v_options_727_, v___x_733_);
lean_dec(v___x_733_);
if (v___x_734_ == 0)
{
lean_del_object(v___x_720_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_682_);
v___y_677_ = v___x_731_;
v___y_678_ = v_a_724_;
goto v___jp_676_;
}
else
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_738_; 
v___x_735_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__9, &l_Lean_Meta_injectionCore___lam__1___closed__9_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__9);
lean_inc(v___x_731_);
v___x_736_ = l_Nat_reprFast(v___x_731_);
if (v_isShared_721_ == 0)
{
lean_ctor_set_tag(v___x_720_, 3);
lean_ctor_set(v___x_720_, 0, v___x_736_);
v___x_738_ = v___x_720_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_736_);
v___x_738_ = v_reuseFailAlloc_754_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_739_ = l_Lean_MessageData_ofFormat(v___x_738_);
v___x_740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_735_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
v___x_741_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__11, &l_Lean_Meta_injectionCore___lam__1___closed__11_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__11);
v___x_742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_740_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
lean_inc(v_a_724_);
v___x_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_743_, 0, v_a_724_);
v___x_744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_742_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
v___x_745_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v___y_682_, v___x_744_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_dec_ref_known(v___x_745_, 1);
v___y_677_ = v___x_731_;
v___y_678_ = v_a_724_;
goto v___jp_676_;
}
else
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
lean_dec(v___x_731_);
lean_dec(v_a_724_);
v_a_746_ = lean_ctor_get(v___x_745_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_745_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_745_);
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
}
}
}
else
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
lean_dec(v_a_724_);
lean_del_object(v___x_720_);
lean_dec(v_numFields_693_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_682_);
v_a_755_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_762_ == 0)
{
v___x_757_ = v___x_725_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_725_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_a_755_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
else
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
lean_del_object(v___x_720_);
lean_dec(v_numFields_693_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_682_);
v_a_763_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_723_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_723_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_766_ == 0)
{
v___x_768_ = v___x_765_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_763_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
}
else
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
lean_dec(v_numFields_693_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_684_);
lean_dec(v___y_682_);
lean_dec(v_fvarId_655_);
lean_dec(v_mvarId_653_);
v_a_773_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_715_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_715_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
else
{
lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_788_; 
lean_dec_ref(v_binderType_711_);
lean_dec(v_numFields_693_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_684_);
lean_dec(v___y_682_);
lean_dec(v_fvarId_655_);
lean_dec(v_mvarId_653_);
v_a_781_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_788_ == 0)
{
v___x_783_ = v___x_712_;
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_712_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_a_781_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
else
{
lean_object* v___x_789_; 
lean_dec(v_numFields_693_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_684_);
lean_dec(v_fvarId_655_);
lean_inc(v___y_690_);
lean_inc_ref(v___y_689_);
lean_inc(v___y_688_);
lean_inc_ref(v___y_687_);
v___x_789_ = lean_apply_5(v___y_685_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, lean_box(0));
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v_a_790_; uint8_t v___x_791_; 
v_a_790_ = lean_ctor_get(v___x_789_, 0);
lean_inc(v_a_790_);
lean_dec_ref_known(v___x_789_, 1);
v___x_791_ = lean_unbox(v_a_790_);
lean_dec(v_a_790_);
if (v___x_791_ == 0)
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
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_792_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__13, &l_Lean_Meta_injectionCore___lam__1___closed__13_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__13);
v___x_793_ = l_Lean_indentExpr(v_a_710_);
v___x_794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_794_, 0, v___x_792_);
lean_ctor_set(v___x_794_, 1, v___x_793_);
v___x_795_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v___y_682_, v___x_794_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_dec_ref_known(v___x_795_, 1);
v___y_663_ = v___y_687_;
v___y_664_ = v___y_688_;
v___y_665_ = v___y_689_;
v___y_666_ = v___y_690_;
goto v___jp_662_;
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___x_654_);
lean_dec(v_mvarId_653_);
v_a_796_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_795_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_795_);
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
}
else
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
lean_dec(v_a_710_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_682_);
lean_dec(v___x_654_);
lean_dec(v_mvarId_653_);
v_a_804_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v___x_789_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_789_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_a_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_dec(v_numFields_693_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_684_);
lean_dec(v___y_682_);
lean_dec(v_fvarId_655_);
lean_dec(v___x_654_);
lean_dec(v_mvarId_653_);
v_a_812_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_709_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_709_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
else
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
lean_dec(v_numFields_693_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_684_);
lean_dec(v___y_682_);
lean_dec(v_fvarId_655_);
lean_dec(v___x_654_);
lean_dec(v_mvarId_653_);
v_a_820_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_827_ == 0)
{
v___x_822_ = v___x_707_;
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_707_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_a_820_);
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
}
v___jp_828_:
{
if (lean_obj_tag(v___y_837_) == 0)
{
lean_object* v_a_838_; lean_object* v___x_839_; 
v_a_838_ = lean_ctor_get(v___y_837_, 0);
lean_inc(v_a_838_);
lean_dec_ref_known(v___y_837_, 1);
lean_inc_ref(v___y_835_);
lean_inc(v___y_829_);
lean_inc_ref(v___y_833_);
lean_inc(v___y_834_);
lean_inc_ref(v___y_831_);
v___x_839_ = lean_apply_5(v___y_835_, v___y_831_, v___y_834_, v___y_833_, v___y_829_, lean_box(0));
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; uint8_t v___x_841_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_a_840_);
lean_dec_ref_known(v___x_839_, 1);
v___x_841_ = lean_unbox(v_a_840_);
lean_dec(v_a_840_);
if (v___x_841_ == 0)
{
v___y_682_ = v___y_830_;
v___y_683_ = v___y_832_;
v___y_684_ = v_a_838_;
v___y_685_ = v___y_835_;
v___y_686_ = v___y_836_;
v___y_687_ = v___y_831_;
v___y_688_ = v___y_834_;
v___y_689_ = v___y_833_;
v___y_690_ = v___y_829_;
goto v___jp_681_;
}
else
{
lean_object* v___x_842_; 
lean_inc(v___y_829_);
lean_inc_ref(v___y_833_);
lean_inc(v___y_834_);
lean_inc_ref(v___y_831_);
lean_inc(v_a_838_);
v___x_842_ = lean_infer_type(v_a_838_, v___y_831_, v___y_834_, v___y_833_, v___y_829_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v_a_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_a_843_);
lean_dec_ref_known(v___x_842_, 1);
v___x_844_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__15, &l_Lean_Meta_injectionCore___lam__1___closed__15_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__15);
lean_inc(v_a_838_);
v___x_845_ = l_Lean_indentExpr(v_a_838_);
v___x_846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_846_, 0, v___x_844_);
lean_ctor_set(v___x_846_, 1, v___x_845_);
v___x_847_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__17, &l_Lean_Meta_injectionCore___lam__1___closed__17_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__17);
v___x_848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_846_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
v___x_849_ = l_Lean_indentExpr(v_a_843_);
v___x_850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_848_);
lean_ctor_set(v___x_850_, 1, v___x_849_);
lean_inc(v___y_830_);
v___x_851_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v___y_830_, v___x_850_, v___y_831_, v___y_834_, v___y_833_, v___y_829_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_dec_ref_known(v___x_851_, 1);
v___y_682_ = v___y_830_;
v___y_683_ = v___y_832_;
v___y_684_ = v_a_838_;
v___y_685_ = v___y_835_;
v___y_686_ = v___y_836_;
v___y_687_ = v___y_831_;
v___y_688_ = v___y_834_;
v___y_689_ = v___y_833_;
v___y_690_ = v___y_829_;
goto v___jp_681_;
}
else
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
lean_dec(v_a_838_);
lean_dec_ref(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec(v___y_829_);
lean_dec(v_fvarId_655_);
lean_dec(v___x_654_);
lean_dec(v_mvarId_653_);
v_a_852_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_851_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_851_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_852_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
else
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
lean_dec(v_a_838_);
lean_dec_ref(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec(v___y_829_);
lean_dec(v_fvarId_655_);
lean_dec(v___x_654_);
lean_dec(v_mvarId_653_);
v_a_860_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_867_ == 0)
{
v___x_862_ = v___x_842_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_842_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_860_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
}
else
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
lean_dec(v_a_838_);
lean_dec_ref(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec(v___y_829_);
lean_dec(v_fvarId_655_);
lean_dec(v___x_654_);
lean_dec(v_mvarId_653_);
v_a_868_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_839_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_839_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_868_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
lean_dec_ref(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec(v___y_829_);
lean_dec(v_fvarId_655_);
lean_dec(v___x_654_);
lean_dec(v_mvarId_653_);
v_a_876_ = lean_ctor_get(v___y_837_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___y_837_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___y_837_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___y_837_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
v___jp_884_:
{
lean_object* v___x_895_; uint8_t v_transparency_896_; uint8_t v___x_897_; uint8_t v___x_898_; 
v___x_895_ = l_Lean_Meta_Context_config(v___y_891_);
v_transparency_896_ = lean_ctor_get_uint8(v___x_895_, 9);
lean_dec_ref(v___x_895_);
v___x_897_ = 1;
v___x_898_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_896_, v___x_897_);
if (v___x_898_ == 0)
{
lean_object* v_keyedConfig_899_; uint8_t v_trackZetaDelta_900_; lean_object* v_zetaDeltaSet_901_; lean_object* v_lctx_902_; lean_object* v_localInstances_903_; lean_object* v_defEqCtx_x3f_904_; lean_object* v_synthPendingDepth_905_; lean_object* v_customCanUnfoldPredicate_x3f_906_; uint8_t v_univApprox_907_; uint8_t v_inTypeClassResolution_908_; uint8_t v_cacheInferType_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v_keyedConfig_899_ = lean_ctor_get(v___y_891_, 0);
v_trackZetaDelta_900_ = lean_ctor_get_uint8(v___y_891_, sizeof(void*)*7);
v_zetaDeltaSet_901_ = lean_ctor_get(v___y_891_, 1);
v_lctx_902_ = lean_ctor_get(v___y_891_, 2);
v_localInstances_903_ = lean_ctor_get(v___y_891_, 3);
v_defEqCtx_x3f_904_ = lean_ctor_get(v___y_891_, 4);
v_synthPendingDepth_905_ = lean_ctor_get(v___y_891_, 5);
v_customCanUnfoldPredicate_x3f_906_ = lean_ctor_get(v___y_891_, 6);
v_univApprox_907_ = lean_ctor_get_uint8(v___y_891_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_908_ = lean_ctor_get_uint8(v___y_891_, sizeof(void*)*7 + 2);
v_cacheInferType_909_ = lean_ctor_get_uint8(v___y_891_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_899_);
v___x_910_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_897_, v_keyedConfig_899_);
lean_inc(v_customCanUnfoldPredicate_x3f_906_);
lean_inc(v_synthPendingDepth_905_);
lean_inc(v_defEqCtx_x3f_904_);
lean_inc_ref(v_localInstances_903_);
lean_inc_ref(v_lctx_902_);
lean_inc(v_zetaDeltaSet_901_);
v___x_911_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_911_, 0, v___x_910_);
lean_ctor_set(v___x_911_, 1, v_zetaDeltaSet_901_);
lean_ctor_set(v___x_911_, 2, v_lctx_902_);
lean_ctor_set(v___x_911_, 3, v_localInstances_903_);
lean_ctor_set(v___x_911_, 4, v_defEqCtx_x3f_904_);
lean_ctor_set(v___x_911_, 5, v_synthPendingDepth_905_);
lean_ctor_set(v___x_911_, 6, v_customCanUnfoldPredicate_x3f_906_);
lean_ctor_set_uint8(v___x_911_, sizeof(void*)*7, v_trackZetaDelta_900_);
lean_ctor_set_uint8(v___x_911_, sizeof(void*)*7 + 1, v_univApprox_907_);
lean_ctor_set_uint8(v___x_911_, sizeof(void*)*7 + 2, v_inTypeClassResolution_908_);
lean_ctor_set_uint8(v___x_911_, sizeof(void*)*7 + 3, v_cacheInferType_909_);
v___x_912_ = l_Lean_Meta_mkNoConfusion(v___y_887_, v___y_888_, v___x_911_, v___y_892_, v___y_893_, v___y_894_);
lean_dec_ref_known(v___x_911_, 7);
v___y_829_ = v___y_894_;
v___y_830_ = v___y_885_;
v___y_831_ = v___y_891_;
v___y_832_ = v___y_886_;
v___y_833_ = v___y_893_;
v___y_834_ = v___y_892_;
v___y_835_ = v___y_889_;
v___y_836_ = v___y_890_;
v___y_837_ = v___x_912_;
goto v___jp_828_;
}
else
{
lean_object* v___x_913_; 
v___x_913_ = l_Lean_Meta_mkNoConfusion(v___y_887_, v___y_888_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
v___y_829_ = v___y_894_;
v___y_830_ = v___y_885_;
v___y_831_ = v___y_891_;
v___y_832_ = v___y_886_;
v___y_833_ = v___y_893_;
v___y_834_ = v___y_892_;
v___y_835_ = v___y_889_;
v___y_836_ = v___y_890_;
v___y_837_ = v___x_913_;
goto v___jp_828_;
}
}
v___jp_914_:
{
lean_object* v___x_921_; lean_object* v___x_922_; uint8_t v___x_923_; 
v___x_921_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__19));
v___x_922_ = lean_unsigned_to_nat(3u);
v___x_923_ = l_Lean_Expr_isAppOfArity(v_type_915_, v___x_921_, v___x_922_);
if (v___x_923_ == 0)
{
lean_object* v___x_924_; lean_object* v___x_925_; 
lean_dec_ref(v_prf_916_);
lean_dec_ref(v_type_915_);
lean_dec_ref(v___x_656_);
lean_dec(v_fvarId_655_);
v___x_924_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__23, &l_Lean_Meta_injectionCore___lam__1___closed__23_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__23);
v___x_925_ = l_Lean_Meta_throwTacticEx___redArg(v___x_654_, v_mvarId_653_, v___x_924_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
return v___x_925_;
}
else
{
lean_object* v___x_926_; 
lean_inc(v_mvarId_653_);
v___x_926_ = l_Lean_MVarId_getType(v_mvarId_653_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v_a_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v_a_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_a_927_);
lean_dec_ref_known(v___x_926_, 1);
v___x_928_ = l_Lean_Expr_appFn_x21(v_type_915_);
v___x_929_ = l_Lean_Expr_appArg_x21(v___x_928_);
lean_dec_ref(v___x_928_);
v___x_930_ = l_Lean_Meta_isConstructorApp_x27_x3f(v___x_929_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v_a_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v_a_931_ = lean_ctor_get(v___x_930_, 0);
lean_inc(v_a_931_);
lean_dec_ref_known(v___x_930_, 1);
v___x_932_ = l_Lean_Expr_appArg_x21(v_type_915_);
lean_dec_ref(v_type_915_);
v___x_933_ = l_Lean_Meta_isConstructorApp_x27_x3f(v___x_932_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
if (lean_obj_tag(v___x_933_) == 0)
{
if (lean_obj_tag(v_a_931_) == 1)
{
lean_object* v_a_934_; 
v_a_934_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_a_934_);
lean_dec_ref_known(v___x_933_, 1);
if (lean_obj_tag(v_a_934_) == 1)
{
lean_object* v_val_935_; lean_object* v_val_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___f_940_; lean_object* v___x_941_; lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_975_; 
v_val_935_ = lean_ctor_get(v_a_931_, 0);
lean_inc(v_val_935_);
lean_dec_ref_known(v_a_931_, 1);
v_val_936_ = lean_ctor_get(v_a_934_, 0);
lean_inc(v_val_936_);
lean_dec_ref_known(v_a_934_, 1);
v___x_937_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__24));
v___x_938_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__25));
v___x_939_ = l_Lean_Name_mkStr3(v___x_937_, v___x_938_, v___x_656_);
lean_inc_n(v___x_939_, 2);
v___f_940_ = lean_alloc_closure((void*)(l_Lean_Meta_injectionCore___lam__0___boxed), 6, 1);
lean_closure_set(v___f_940_, 0, v___x_939_);
v___x_941_ = l_Lean_Meta_injectionCore___lam__0(v___x_939_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
v_a_942_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_975_ == 0)
{
v___x_944_ = v___x_941_;
v_isShared_945_ = v_isSharedCheck_975_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_941_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_975_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
uint8_t v___x_946_; 
v___x_946_ = lean_unbox(v_a_942_);
lean_dec(v_a_942_);
if (v___x_946_ == 0)
{
lean_del_object(v___x_944_);
v___y_885_ = v___x_939_;
v___y_886_ = v_val_936_;
v___y_887_ = v_a_927_;
v___y_888_ = v_prf_916_;
v___y_889_ = v___f_940_;
v___y_890_ = v_val_935_;
v___y_891_ = v___y_917_;
v___y_892_ = v___y_918_;
v___y_893_ = v___y_919_;
v___y_894_ = v___y_920_;
goto v___jp_884_;
}
else
{
lean_object* v___x_947_; 
lean_inc(v___y_920_);
lean_inc_ref(v___y_919_);
lean_inc(v___y_918_);
lean_inc_ref(v___y_917_);
lean_inc_ref(v_prf_916_);
v___x_947_ = lean_infer_type(v_prf_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
if (lean_obj_tag(v___x_947_) == 0)
{
lean_object* v_a_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_955_; 
v_a_948_ = lean_ctor_get(v___x_947_, 0);
lean_inc(v_a_948_);
lean_dec_ref_known(v___x_947_, 1);
v___x_949_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__27, &l_Lean_Meta_injectionCore___lam__1___closed__27_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__27);
v___x_950_ = l_Lean_MessageData_ofExpr(v_a_948_);
v___x_951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_949_);
lean_ctor_set(v___x_951_, 1, v___x_950_);
v___x_952_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__29, &l_Lean_Meta_injectionCore___lam__1___closed__29_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__29);
v___x_953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_951_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
lean_inc(v_mvarId_653_);
if (v_isShared_945_ == 0)
{
lean_ctor_set_tag(v___x_944_, 1);
lean_ctor_set(v___x_944_, 0, v_mvarId_653_);
v___x_955_ = v___x_944_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_mvarId_653_);
v___x_955_ = v_reuseFailAlloc_966_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_953_);
lean_ctor_set(v___x_956_, 1, v___x_955_);
lean_inc(v___x_939_);
v___x_957_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v___x_939_, v___x_956_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_dec_ref_known(v___x_957_, 1);
v___y_885_ = v___x_939_;
v___y_886_ = v_val_936_;
v___y_887_ = v_a_927_;
v___y_888_ = v_prf_916_;
v___y_889_ = v___f_940_;
v___y_890_ = v_val_935_;
v___y_891_ = v___y_917_;
v___y_892_ = v___y_918_;
v___y_893_ = v___y_919_;
v___y_894_ = v___y_920_;
goto v___jp_884_;
}
else
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
lean_dec_ref(v___f_940_);
lean_dec(v___x_939_);
lean_dec(v_val_936_);
lean_dec(v_val_935_);
lean_dec(v_a_927_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec_ref(v_prf_916_);
lean_dec(v_fvarId_655_);
lean_dec(v___x_654_);
lean_dec(v_mvarId_653_);
v_a_958_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_957_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_957_);
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
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
lean_del_object(v___x_944_);
lean_dec_ref(v___f_940_);
lean_dec(v___x_939_);
lean_dec(v_val_936_);
lean_dec(v_val_935_);
lean_dec(v_a_927_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec_ref(v_prf_916_);
lean_dec(v_fvarId_655_);
lean_dec(v___x_654_);
lean_dec(v_mvarId_653_);
v_a_967_ = lean_ctor_get(v___x_947_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_947_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_947_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
}
}
else
{
lean_dec(v_a_934_);
lean_dec_ref_known(v_a_931_, 1);
lean_dec(v_a_927_);
lean_dec_ref(v_prf_916_);
lean_dec_ref(v___x_656_);
lean_dec(v_fvarId_655_);
v___y_670_ = v___y_917_;
v___y_671_ = v___y_918_;
v___y_672_ = v___y_919_;
v___y_673_ = v___y_920_;
goto v___jp_669_;
}
}
else
{
lean_dec_ref_known(v___x_933_, 1);
lean_dec(v_a_931_);
lean_dec(v_a_927_);
lean_dec_ref(v_prf_916_);
lean_dec_ref(v___x_656_);
lean_dec(v_fvarId_655_);
v___y_670_ = v___y_917_;
v___y_671_ = v___y_918_;
v___y_672_ = v___y_919_;
v___y_673_ = v___y_920_;
goto v___jp_669_;
}
}
else
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_983_; 
lean_dec(v_a_931_);
lean_dec(v_a_927_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec_ref(v_prf_916_);
lean_dec_ref(v___x_656_);
lean_dec(v_fvarId_655_);
lean_dec(v___x_654_);
lean_dec(v_mvarId_653_);
v_a_976_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_983_ == 0)
{
v___x_978_ = v___x_933_;
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_933_);
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
else
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
lean_dec(v_a_927_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec_ref(v_prf_916_);
lean_dec_ref(v_type_915_);
lean_dec_ref(v___x_656_);
lean_dec(v_fvarId_655_);
lean_dec(v___x_654_);
lean_dec(v_mvarId_653_);
v_a_984_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v___x_930_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_930_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_a_984_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
else
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_999_; 
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec_ref(v_prf_916_);
lean_dec_ref(v_type_915_);
lean_dec_ref(v___x_656_);
lean_dec(v_fvarId_655_);
lean_dec(v___x_654_);
lean_dec(v_mvarId_653_);
v_a_992_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_999_ == 0)
{
v___x_994_ = v___x_926_;
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_926_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
if (v_isShared_995_ == 0)
{
v___x_997_ = v___x_994_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_a_992_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___lam__1___boxed(lean_object* v_mvarId_1072_, lean_object* v___x_1073_, lean_object* v_fvarId_1074_, lean_object* v___x_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Lean_Meta_injectionCore___lam__1(v_mvarId_1072_, v___x_1073_, v_fvarId_1074_, v___x_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore(lean_object* v_mvarId_1085_, lean_object* v_fvarId_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___f_1094_; lean_object* v___x_1095_; 
v___x_1092_ = ((lean_object*)(l_Lean_Meta_injectionCore___closed__0));
v___x_1093_ = ((lean_object*)(l_Lean_Meta_injectionCore___closed__1));
lean_inc(v_mvarId_1085_);
v___f_1094_ = lean_alloc_closure((void*)(l_Lean_Meta_injectionCore___lam__1___boxed), 9, 4);
lean_closure_set(v___f_1094_, 0, v_mvarId_1085_);
lean_closure_set(v___f_1094_, 1, v___x_1093_);
lean_closure_set(v___f_1094_, 2, v_fvarId_1086_);
lean_closure_set(v___f_1094_, 3, v___x_1092_);
v___x_1095_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg(v_mvarId_1085_, v___f_1094_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___boxed(lean_object* v_mvarId_1096_, lean_object* v_fvarId_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Lean_Meta_injectionCore(v_mvarId_1096_, v_fvarId_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_);
lean_dec(v_a_1101_);
lean_dec_ref(v_a_1100_);
lean_dec(v_a_1099_);
lean_dec_ref(v_a_1098_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0(lean_object* v_mvarId_1104_, lean_object* v_val_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(v_mvarId_1104_, v_val_1105_, v___y_1107_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___boxed(lean_object* v_mvarId_1112_, lean_object* v_val_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0(v_mvarId_1112_, v_val_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0(lean_object* v_00_u03b2_1120_, lean_object* v_x_1121_, lean_object* v_x_1122_, lean_object* v_x_1123_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0___redArg(v_x_1121_, v_x_1122_, v_x_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1125_, lean_object* v_x_1126_, size_t v_x_1127_, size_t v_x_1128_, lean_object* v_x_1129_, lean_object* v_x_1130_){
_start:
{
lean_object* v___x_1131_; 
v___x_1131_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(v_x_1126_, v_x_1127_, v_x_1128_, v_x_1129_, v_x_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1132_, lean_object* v_x_1133_, lean_object* v_x_1134_, lean_object* v_x_1135_, lean_object* v_x_1136_, lean_object* v_x_1137_){
_start:
{
size_t v_x_15706__boxed_1138_; size_t v_x_15707__boxed_1139_; lean_object* v_res_1140_; 
v_x_15706__boxed_1138_ = lean_unbox_usize(v_x_1134_);
lean_dec(v_x_1134_);
v_x_15707__boxed_1139_ = lean_unbox_usize(v_x_1135_);
lean_dec(v_x_1135_);
v_res_1140_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2(v_00_u03b2_1132_, v_x_1133_, v_x_15706__boxed_1138_, v_x_15707__boxed_1139_, v_x_1136_, v_x_1137_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1141_, lean_object* v_n_1142_, lean_object* v_k_1143_, lean_object* v_v_1144_){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5___redArg(v_n_1142_, v_k_1143_, v_v_1144_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_1146_, size_t v_depth_1147_, lean_object* v_keys_1148_, lean_object* v_vals_1149_, lean_object* v_heq_1150_, lean_object* v_i_1151_, lean_object* v_entries_1152_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___redArg(v_depth_1147_, v_keys_1148_, v_vals_1149_, v_i_1151_, v_entries_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1154_, lean_object* v_depth_1155_, lean_object* v_keys_1156_, lean_object* v_vals_1157_, lean_object* v_heq_1158_, lean_object* v_i_1159_, lean_object* v_entries_1160_){
_start:
{
size_t v_depth_boxed_1161_; lean_object* v_res_1162_; 
v_depth_boxed_1161_ = lean_unbox_usize(v_depth_1155_);
lean_dec(v_depth_1155_);
v_res_1162_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6(v_00_u03b2_1154_, v_depth_boxed_1161_, v_keys_1156_, v_vals_1157_, v_heq_1158_, v_i_1159_, v_entries_1160_);
lean_dec_ref(v_vals_1157_);
lean_dec_ref(v_keys_1156_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5_spec__6(lean_object* v_00_u03b2_1163_, lean_object* v_x_1164_, lean_object* v_x_1165_, lean_object* v_x_1166_, lean_object* v_x_1167_){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(v_x_1164_, v_x_1165_, v_x_1166_, v_x_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorIdx(lean_object* v_x_1169_){
_start:
{
if (lean_obj_tag(v_x_1169_) == 0)
{
lean_object* v___x_1170_; 
v___x_1170_ = lean_unsigned_to_nat(0u);
return v___x_1170_;
}
else
{
lean_object* v___x_1171_; 
v___x_1171_ = lean_unsigned_to_nat(1u);
return v___x_1171_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorIdx___boxed(lean_object* v_x_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Lean_Meta_InjectionResult_ctorIdx(v_x_1172_);
lean_dec(v_x_1172_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorElim___redArg(lean_object* v_t_1174_, lean_object* v_k_1175_){
_start:
{
if (lean_obj_tag(v_t_1174_) == 0)
{
return v_k_1175_;
}
else
{
lean_object* v_mvarId_1176_; lean_object* v_newEqs_1177_; lean_object* v_remainingNames_1178_; lean_object* v___x_1179_; 
v_mvarId_1176_ = lean_ctor_get(v_t_1174_, 0);
lean_inc(v_mvarId_1176_);
v_newEqs_1177_ = lean_ctor_get(v_t_1174_, 1);
lean_inc_ref(v_newEqs_1177_);
v_remainingNames_1178_ = lean_ctor_get(v_t_1174_, 2);
lean_inc(v_remainingNames_1178_);
lean_dec_ref_known(v_t_1174_, 3);
v___x_1179_ = lean_apply_3(v_k_1175_, v_mvarId_1176_, v_newEqs_1177_, v_remainingNames_1178_);
return v___x_1179_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorElim(lean_object* v_motive_1180_, lean_object* v_ctorIdx_1181_, lean_object* v_t_1182_, lean_object* v_h_1183_, lean_object* v_k_1184_){
_start:
{
lean_object* v___x_1185_; 
v___x_1185_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_1182_, v_k_1184_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorElim___boxed(lean_object* v_motive_1186_, lean_object* v_ctorIdx_1187_, lean_object* v_t_1188_, lean_object* v_h_1189_, lean_object* v_k_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Lean_Meta_InjectionResult_ctorElim(v_motive_1186_, v_ctorIdx_1187_, v_t_1188_, v_h_1189_, v_k_1190_);
lean_dec(v_ctorIdx_1187_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_solved_elim___redArg(lean_object* v_t_1192_, lean_object* v_solved_1193_){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_1192_, v_solved_1193_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_solved_elim(lean_object* v_motive_1195_, lean_object* v_t_1196_, lean_object* v_h_1197_, lean_object* v_solved_1198_){
_start:
{
lean_object* v___x_1199_; 
v___x_1199_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_1196_, v_solved_1198_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_subgoal_elim___redArg(lean_object* v_t_1200_, lean_object* v_subgoal_1201_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_1200_, v_subgoal_1201_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_subgoal_elim(lean_object* v_motive_1203_, lean_object* v_t_1204_, lean_object* v_h_1205_, lean_object* v_subgoal_1206_){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_1204_, v_subgoal_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go(uint8_t v_tryToClear_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_){
_start:
{
lean_object* v_zero_1218_; uint8_t v_isZero_1219_; 
v_zero_1218_ = lean_unsigned_to_nat(0u);
v_isZero_1219_ = lean_nat_dec_eq(v_a_1209_, v_zero_1218_);
if (v_isZero_1219_ == 1)
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
lean_dec(v_a_1209_);
v___x_1220_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1220_, 0, v_a_1210_);
lean_ctor_set(v___x_1220_, 1, v_a_1211_);
lean_ctor_set(v___x_1220_, 2, v_a_1212_);
v___x_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
return v___x_1221_;
}
else
{
lean_object* v_one_1222_; lean_object* v_n_1223_; 
v_one_1222_ = lean_unsigned_to_nat(1u);
v_n_1223_ = lean_nat_sub(v_a_1209_, v_one_1222_);
lean_dec(v_a_1209_);
if (lean_obj_tag(v_a_1212_) == 0)
{
lean_object* v___x_1224_; 
v___x_1224_ = l_Lean_Meta_intro1Core(v_a_1210_, v_isZero_1219_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v_a_1225_; lean_object* v_fst_1226_; lean_object* v_snd_1227_; lean_object* v___x_1228_; 
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_a_1225_);
lean_dec_ref_known(v___x_1224_, 1);
v_fst_1226_ = lean_ctor_get(v_a_1225_, 0);
lean_inc(v_fst_1226_);
v_snd_1227_ = lean_ctor_get(v_a_1225_, 1);
lean_inc(v_snd_1227_);
lean_dec(v_a_1225_);
v___x_1228_ = l_Lean_Meta_heqToEq(v_snd_1227_, v_fst_1226_, v_tryToClear_1208_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v_a_1229_; lean_object* v_fst_1230_; lean_object* v_snd_1231_; lean_object* v___x_1232_; 
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_a_1229_);
lean_dec_ref_known(v___x_1228_, 1);
v_fst_1230_ = lean_ctor_get(v_a_1229_, 0);
lean_inc(v_fst_1230_);
v_snd_1231_ = lean_ctor_get(v_a_1229_, 1);
lean_inc(v_snd_1231_);
lean_dec(v_a_1229_);
v___x_1232_ = lean_array_push(v_a_1211_, v_fst_1230_);
v_a_1209_ = v_n_1223_;
v_a_1210_ = v_snd_1231_;
v_a_1211_ = v___x_1232_;
goto _start;
}
else
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1241_; 
lean_dec(v_n_1223_);
lean_dec_ref(v_a_1211_);
v_a_1234_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1236_ = v___x_1228_;
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1228_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
if (v_isShared_1237_ == 0)
{
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_a_1234_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
}
else
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1249_; 
lean_dec(v_n_1223_);
lean_dec_ref(v_a_1211_);
v_a_1242_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1244_ = v___x_1224_;
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1224_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1247_; 
if (v_isShared_1245_ == 0)
{
v___x_1247_ = v___x_1244_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1242_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
else
{
lean_object* v_head_1250_; lean_object* v_tail_1251_; lean_object* v___x_1252_; 
v_head_1250_ = lean_ctor_get(v_a_1212_, 0);
lean_inc(v_head_1250_);
v_tail_1251_ = lean_ctor_get(v_a_1212_, 1);
lean_inc(v_tail_1251_);
lean_dec_ref_known(v_a_1212_, 2);
v___x_1252_ = l_Lean_MVarId_intro(v_a_1210_, v_head_1250_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v_a_1253_; lean_object* v_fst_1254_; lean_object* v_snd_1255_; lean_object* v___x_1256_; 
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
lean_inc(v_a_1253_);
lean_dec_ref_known(v___x_1252_, 1);
v_fst_1254_ = lean_ctor_get(v_a_1253_, 0);
lean_inc(v_fst_1254_);
v_snd_1255_ = lean_ctor_get(v_a_1253_, 1);
lean_inc(v_snd_1255_);
lean_dec(v_a_1253_);
v___x_1256_ = l_Lean_Meta_heqToEq(v_snd_1255_, v_fst_1254_, v_tryToClear_1208_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; lean_object* v_fst_1258_; lean_object* v_snd_1259_; lean_object* v___x_1260_; 
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_a_1257_);
lean_dec_ref_known(v___x_1256_, 1);
v_fst_1258_ = lean_ctor_get(v_a_1257_, 0);
lean_inc(v_fst_1258_);
v_snd_1259_ = lean_ctor_get(v_a_1257_, 1);
lean_inc(v_snd_1259_);
lean_dec(v_a_1257_);
v___x_1260_ = lean_array_push(v_a_1211_, v_fst_1258_);
v_a_1209_ = v_n_1223_;
v_a_1210_ = v_snd_1259_;
v_a_1211_ = v___x_1260_;
v_a_1212_ = v_tail_1251_;
goto _start;
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
lean_dec(v_tail_1251_);
lean_dec(v_n_1223_);
lean_dec_ref(v_a_1211_);
v_a_1262_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1256_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1256_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1262_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
else
{
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1277_; 
lean_dec(v_tail_1251_);
lean_dec(v_n_1223_);
lean_dec_ref(v_a_1211_);
v_a_1270_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1272_ = v___x_1252_;
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1252_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_a_1270_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go___boxed(lean_object* v_tryToClear_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_){
_start:
{
uint8_t v_tryToClear_boxed_1288_; lean_object* v_res_1289_; 
v_tryToClear_boxed_1288_ = lean_unbox(v_tryToClear_1278_);
v_res_1289_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go(v_tryToClear_boxed_1288_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_);
lean_dec(v_a_1286_);
lean_dec_ref(v_a_1285_);
lean_dec(v_a_1284_);
lean_dec_ref(v_a_1283_);
return v_res_1289_;
}
}
static lean_object* _init_l_Lean_Meta_injectionIntro___closed__2(void){
_start:
{
lean_object* v_cls_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v_cls_1296_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__1));
v___x_1297_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__0___closed__1));
v___x_1298_ = l_Lean_Name_append(v___x_1297_, v_cls_1296_);
return v___x_1298_;
}
}
static lean_object* _init_l_Lean_Meta_injectionIntro___closed__4(void){
_start:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1300_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__3));
v___x_1301_ = l_Lean_stringToMessageData(v___x_1300_);
return v___x_1301_;
}
}
static lean_object* _init_l_Lean_Meta_injectionIntro___closed__6(void){
_start:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1303_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__5));
v___x_1304_ = l_Lean_stringToMessageData(v___x_1303_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro(lean_object* v_mvarId_1305_, lean_object* v_numEqs_1306_, lean_object* v_newNames_1307_, uint8_t v_tryToClear_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_){
_start:
{
lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v_toCold_1321_; lean_object* v_options_1322_; uint8_t v_hasTrace_1323_; 
v_toCold_1321_ = lean_ctor_get(v_a_1311_, 0);
v_options_1322_ = lean_ctor_get(v_toCold_1321_, 2);
v_hasTrace_1323_ = lean_ctor_get_uint8(v_options_1322_, sizeof(void*)*1);
if (v_hasTrace_1323_ == 0)
{
v___y_1315_ = v_a_1309_;
v___y_1316_ = v_a_1310_;
v___y_1317_ = v_a_1311_;
v___y_1318_ = v_a_1312_;
goto v___jp_1314_;
}
else
{
lean_object* v_inheritedTraceOptions_1324_; lean_object* v_cls_1325_; lean_object* v___x_1326_; uint8_t v___x_1327_; 
v_inheritedTraceOptions_1324_ = lean_ctor_get(v_toCold_1321_, 11);
v_cls_1325_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__1));
v___x_1326_ = lean_obj_once(&l_Lean_Meta_injectionIntro___closed__2, &l_Lean_Meta_injectionIntro___closed__2_once, _init_l_Lean_Meta_injectionIntro___closed__2);
v___x_1327_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1324_, v_options_1322_, v___x_1326_);
if (v___x_1327_ == 0)
{
v___y_1315_ = v_a_1309_;
v___y_1316_ = v_a_1310_;
v___y_1317_ = v_a_1311_;
v___y_1318_ = v_a_1312_;
goto v___jp_1314_;
}
else
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1328_ = lean_obj_once(&l_Lean_Meta_injectionIntro___closed__4, &l_Lean_Meta_injectionIntro___closed__4_once, _init_l_Lean_Meta_injectionIntro___closed__4);
lean_inc(v_numEqs_1306_);
v___x_1329_ = l_Nat_reprFast(v_numEqs_1306_);
v___x_1330_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1329_);
v___x_1331_ = l_Lean_MessageData_ofFormat(v___x_1330_);
v___x_1332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1328_);
lean_ctor_set(v___x_1332_, 1, v___x_1331_);
v___x_1333_ = lean_obj_once(&l_Lean_Meta_injectionIntro___closed__6, &l_Lean_Meta_injectionIntro___closed__6_once, _init_l_Lean_Meta_injectionIntro___closed__6);
v___x_1334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1332_);
lean_ctor_set(v___x_1334_, 1, v___x_1333_);
lean_inc(v_mvarId_1305_);
v___x_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1335_, 0, v_mvarId_1305_);
v___x_1336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1334_);
lean_ctor_set(v___x_1336_, 1, v___x_1335_);
v___x_1337_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v_cls_1325_, v___x_1336_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_dec_ref_known(v___x_1337_, 1);
v___y_1315_ = v_a_1309_;
v___y_1316_ = v_a_1310_;
v___y_1317_ = v_a_1311_;
v___y_1318_ = v_a_1312_;
goto v___jp_1314_;
}
else
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1345_; 
lean_dec(v_newNames_1307_);
lean_dec(v_numEqs_1306_);
lean_dec(v_mvarId_1305_);
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1340_ = v___x_1337_;
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1337_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1343_; 
if (v_isShared_1341_ == 0)
{
v___x_1343_ = v___x_1340_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_a_1338_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
}
v___jp_1314_:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1319_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__0));
v___x_1320_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go(v_tryToClear_1308_, v_numEqs_1306_, v_mvarId_1305_, v___x_1319_, v_newNames_1307_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
return v___x_1320_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro___boxed(lean_object* v_mvarId_1346_, lean_object* v_numEqs_1347_, lean_object* v_newNames_1348_, lean_object* v_tryToClear_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
uint8_t v_tryToClear_boxed_1355_; lean_object* v_res_1356_; 
v_tryToClear_boxed_1355_ = lean_unbox(v_tryToClear_1349_);
v_res_1356_ = l_Lean_Meta_injectionIntro(v_mvarId_1346_, v_numEqs_1347_, v_newNames_1348_, v_tryToClear_boxed_1355_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
lean_dec(v_a_1353_);
lean_dec_ref(v_a_1352_);
lean_dec(v_a_1351_);
lean_dec_ref(v_a_1350_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injection(lean_object* v_mvarId_1357_, lean_object* v_fvarId_1358_, lean_object* v_newNames_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_){
_start:
{
lean_object* v___x_1365_; 
v___x_1365_ = l_Lean_Meta_injectionCore(v_mvarId_1357_, v_fvarId_1358_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1378_; 
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1368_ = v___x_1365_;
v_isShared_1369_ = v_isSharedCheck_1378_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1365_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1378_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
if (lean_obj_tag(v_a_1366_) == 0)
{
lean_object* v___x_1370_; lean_object* v___x_1372_; 
lean_dec(v_newNames_1359_);
v___x_1370_ = lean_box(0);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 0, v___x_1370_);
v___x_1372_ = v___x_1368_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1370_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
else
{
lean_object* v_mvarId_1374_; lean_object* v_numNewEqs_1375_; uint8_t v___x_1376_; lean_object* v___x_1377_; 
lean_del_object(v___x_1368_);
v_mvarId_1374_ = lean_ctor_get(v_a_1366_, 0);
lean_inc(v_mvarId_1374_);
v_numNewEqs_1375_ = lean_ctor_get(v_a_1366_, 1);
lean_inc(v_numNewEqs_1375_);
lean_dec_ref_known(v_a_1366_, 2);
v___x_1376_ = 1;
v___x_1377_ = l_Lean_Meta_injectionIntro(v_mvarId_1374_, v_numNewEqs_1375_, v_newNames_1359_, v___x_1376_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
return v___x_1377_;
}
}
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
lean_dec(v_newNames_1359_);
v_a_1379_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v___x_1365_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1365_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1382_ == 0)
{
v___x_1384_ = v___x_1381_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_a_1379_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injection___boxed(lean_object* v_mvarId_1387_, lean_object* v_fvarId_1388_, lean_object* v_newNames_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Lean_Meta_injection(v_mvarId_1387_, v_fvarId_1388_, v_newNames_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
lean_dec(v_a_1393_);
lean_dec_ref(v_a_1392_);
lean_dec(v_a_1391_);
lean_dec_ref(v_a_1390_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorIdx(lean_object* v_x_1396_){
_start:
{
if (lean_obj_tag(v_x_1396_) == 0)
{
lean_object* v___x_1397_; 
v___x_1397_ = lean_unsigned_to_nat(0u);
return v___x_1397_;
}
else
{
lean_object* v___x_1398_; 
v___x_1398_ = lean_unsigned_to_nat(1u);
return v___x_1398_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorIdx___boxed(lean_object* v_x_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_Lean_Meta_InjectionsResult_ctorIdx(v_x_1399_);
lean_dec(v_x_1399_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorElim___redArg(lean_object* v_t_1401_, lean_object* v_k_1402_){
_start:
{
if (lean_obj_tag(v_t_1401_) == 0)
{
return v_k_1402_;
}
else
{
lean_object* v_mvarId_1403_; lean_object* v_remainingNames_1404_; lean_object* v_forbidden_1405_; lean_object* v___x_1406_; 
v_mvarId_1403_ = lean_ctor_get(v_t_1401_, 0);
lean_inc(v_mvarId_1403_);
v_remainingNames_1404_ = lean_ctor_get(v_t_1401_, 1);
lean_inc(v_remainingNames_1404_);
v_forbidden_1405_ = lean_ctor_get(v_t_1401_, 2);
lean_inc(v_forbidden_1405_);
lean_dec_ref_known(v_t_1401_, 3);
v___x_1406_ = lean_apply_3(v_k_1402_, v_mvarId_1403_, v_remainingNames_1404_, v_forbidden_1405_);
return v___x_1406_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorElim(lean_object* v_motive_1407_, lean_object* v_ctorIdx_1408_, lean_object* v_t_1409_, lean_object* v_h_1410_, lean_object* v_k_1411_){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1409_, v_k_1411_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorElim___boxed(lean_object* v_motive_1413_, lean_object* v_ctorIdx_1414_, lean_object* v_t_1415_, lean_object* v_h_1416_, lean_object* v_k_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_Lean_Meta_InjectionsResult_ctorElim(v_motive_1413_, v_ctorIdx_1414_, v_t_1415_, v_h_1416_, v_k_1417_);
lean_dec(v_ctorIdx_1414_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_solved_elim___redArg(lean_object* v_t_1419_, lean_object* v_solved_1420_){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1419_, v_solved_1420_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_solved_elim(lean_object* v_motive_1422_, lean_object* v_t_1423_, lean_object* v_h_1424_, lean_object* v_solved_1425_){
_start:
{
lean_object* v___x_1426_; 
v___x_1426_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1423_, v_solved_1425_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_subgoal_elim___redArg(lean_object* v_t_1427_, lean_object* v_subgoal_1428_){
_start:
{
lean_object* v___x_1429_; 
v___x_1429_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1427_, v_subgoal_1428_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_subgoal_elim(lean_object* v_motive_1430_, lean_object* v_t_1431_, lean_object* v_h_1432_, lean_object* v_subgoal_1433_){
_start:
{
lean_object* v___x_1434_; 
v___x_1434_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1431_, v_subgoal_1433_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(lean_object* v_x_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
lean_object* v___x_1441_; 
v___x_1441_ = l_Lean_Meta_saveState___redArg(v___y_1437_, v___y_1439_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v_a_1442_; lean_object* v___x_1443_; 
v_a_1442_ = lean_ctor_get(v___x_1441_, 0);
lean_inc(v_a_1442_);
lean_dec_ref_known(v___x_1441_, 1);
lean_inc(v___y_1439_);
lean_inc_ref(v___y_1438_);
lean_inc(v___y_1437_);
lean_inc_ref(v___y_1436_);
v___x_1443_ = lean_apply_5(v_x_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, lean_box(0));
if (lean_obj_tag(v___x_1443_) == 0)
{
lean_dec(v_a_1442_);
return v___x_1443_;
}
else
{
lean_object* v_a_1444_; uint8_t v___y_1446_; uint8_t v___x_1464_; 
v_a_1444_ = lean_ctor_get(v___x_1443_, 0);
lean_inc(v_a_1444_);
v___x_1464_ = l_Lean_Exception_isInterrupt(v_a_1444_);
if (v___x_1464_ == 0)
{
uint8_t v___x_1465_; 
lean_inc(v_a_1444_);
v___x_1465_ = l_Lean_Exception_isRuntime(v_a_1444_);
v___y_1446_ = v___x_1465_;
goto v___jp_1445_;
}
else
{
v___y_1446_ = v___x_1464_;
goto v___jp_1445_;
}
v___jp_1445_:
{
if (v___y_1446_ == 0)
{
lean_object* v___x_1447_; 
lean_dec_ref_known(v___x_1443_, 1);
v___x_1447_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1442_, v___y_1437_, v___y_1439_);
lean_dec(v_a_1442_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1454_ == 0)
{
lean_object* v_unused_1455_; 
v_unused_1455_ = lean_ctor_get(v___x_1447_, 0);
lean_dec(v_unused_1455_);
v___x_1449_ = v___x_1447_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_dec(v___x_1447_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
lean_ctor_set_tag(v___x_1449_, 1);
lean_ctor_set(v___x_1449_, 0, v_a_1444_);
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1444_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
else
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
lean_dec(v_a_1444_);
v_a_1456_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1458_ = v___x_1447_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1447_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1461_; 
if (v_isShared_1459_ == 0)
{
v___x_1461_ = v___x_1458_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1456_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
else
{
lean_dec(v_a_1444_);
lean_dec(v_a_1442_);
return v___x_1443_;
}
}
}
}
else
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1473_; 
lean_dec_ref(v_x_1435_);
v_a_1466_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1468_ = v___x_1441_;
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1441_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1471_; 
if (v_isShared_1469_ == 0)
{
v___x_1471_ = v___x_1468_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_a_1466_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg___boxed(lean_object* v_x_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(v_x_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1(lean_object* v_00_u03b1_1481_, lean_object* v_x_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(v_x_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___boxed(lean_object* v_00_u03b1_1489_, lean_object* v_x_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1(v_00_u03b1_1489_, v_x_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
return v_res_1496_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(lean_object* v_k_1497_, lean_object* v_t_1498_){
_start:
{
if (lean_obj_tag(v_t_1498_) == 0)
{
lean_object* v_k_1499_; lean_object* v_l_1500_; lean_object* v_r_1501_; uint8_t v___x_1502_; 
v_k_1499_ = lean_ctor_get(v_t_1498_, 1);
v_l_1500_ = lean_ctor_get(v_t_1498_, 3);
v_r_1501_ = lean_ctor_get(v_t_1498_, 4);
v___x_1502_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1497_, v_k_1499_);
switch(v___x_1502_)
{
case 0:
{
v_t_1498_ = v_l_1500_;
goto _start;
}
case 1:
{
uint8_t v___x_1504_; 
v___x_1504_ = 1;
return v___x_1504_;
}
default: 
{
v_t_1498_ = v_r_1501_;
goto _start;
}
}
}
else
{
uint8_t v___x_1506_; 
v___x_1506_ = 0;
return v___x_1506_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg___boxed(lean_object* v_k_1507_, lean_object* v_t_1508_){
_start:
{
uint8_t v_res_1509_; lean_object* v_r_1510_; 
v_res_1509_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(v_k_1507_, v_t_1508_);
lean_dec(v_t_1508_);
lean_dec(v_k_1507_);
v_r_1510_ = lean_box(v_res_1509_);
return v_r_1510_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4(void){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1517_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__3));
v___x_1518_ = l_Lean_MessageData_ofFormat(v___x_1517_);
return v___x_1518_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5(void){
_start:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1519_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4, &l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4_once, _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4);
v___x_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1519_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0___boxed(lean_object* v_mvarId_1521_, lean_object* v_head_1522_, lean_object* v_newNames_1523_, lean_object* v_tail_1524_, lean_object* v_forbidden_1525_, lean_object* v_n_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0(v_mvarId_1521_, v_head_1522_, v_newNames_1523_, v_tail_1524_, v_forbidden_1525_, v_n_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go(lean_object* v_depth_1533_, lean_object* v_fvarIds_1534_, lean_object* v_mvarId_1535_, lean_object* v_newNames_1536_, lean_object* v_forbidden_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_){
_start:
{
lean_object* v_zero_1543_; uint8_t v_isZero_1544_; 
v_zero_1543_ = lean_unsigned_to_nat(0u);
v_isZero_1544_ = lean_nat_dec_eq(v_depth_1533_, v_zero_1543_);
if (v_isZero_1544_ == 1)
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
lean_dec(v_forbidden_1537_);
lean_dec(v_newNames_1536_);
lean_dec(v_fvarIds_1534_);
lean_dec(v_depth_1533_);
v___x_1545_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__1));
v___x_1546_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5, &l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5_once, _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5);
v___x_1547_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1545_, v_mvarId_1535_, v___x_1546_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_);
return v___x_1547_;
}
else
{
if (lean_obj_tag(v_fvarIds_1534_) == 0)
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
lean_dec(v_depth_1533_);
v___x_1548_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1548_, 0, v_mvarId_1535_);
lean_ctor_set(v___x_1548_, 1, v_newNames_1536_);
lean_ctor_set(v___x_1548_, 2, v_forbidden_1537_);
v___x_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1548_);
return v___x_1549_;
}
else
{
lean_object* v_head_1550_; lean_object* v_tail_1551_; lean_object* v_one_1552_; lean_object* v_n_1553_; lean_object* v___x_1554_; lean_object* v___y_1556_; uint8_t v___y_1557_; uint8_t v___x_1559_; 
v_head_1550_ = lean_ctor_get(v_fvarIds_1534_, 0);
lean_inc(v_head_1550_);
v_tail_1551_ = lean_ctor_get(v_fvarIds_1534_, 1);
lean_inc(v_tail_1551_);
lean_dec_ref_known(v_fvarIds_1534_, 2);
v_one_1552_ = lean_unsigned_to_nat(1u);
v_n_1553_ = lean_nat_sub(v_depth_1533_, v_one_1552_);
lean_dec(v_depth_1533_);
v___x_1554_ = lean_nat_add(v_n_1553_, v_one_1552_);
v___x_1559_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(v_head_1550_, v_forbidden_1537_);
if (v___x_1559_ == 0)
{
lean_object* v___x_1560_; 
lean_inc(v_head_1550_);
v___x_1560_ = l_Lean_FVarId_getType___redArg(v_head_1550_, v_a_1538_, v_a_1540_, v_a_1541_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; lean_object* v___x_1562_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1561_);
lean_dec_ref_known(v___x_1560_, 1);
v___x_1562_ = l_Lean_Meta_matchEqHEq_x3f(v_a_1561_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; 
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
lean_inc(v_a_1563_);
lean_dec_ref_known(v___x_1562_, 1);
if (lean_obj_tag(v_a_1563_) == 1)
{
lean_object* v_val_1564_; lean_object* v_snd_1565_; lean_object* v_fst_1566_; lean_object* v_snd_1567_; lean_object* v___x_1568_; 
v_val_1564_ = lean_ctor_get(v_a_1563_, 0);
lean_inc(v_val_1564_);
lean_dec_ref_known(v_a_1563_, 1);
v_snd_1565_ = lean_ctor_get(v_val_1564_, 1);
lean_inc(v_snd_1565_);
lean_dec(v_val_1564_);
v_fst_1566_ = lean_ctor_get(v_snd_1565_, 0);
lean_inc(v_fst_1566_);
v_snd_1567_ = lean_ctor_get(v_snd_1565_, 1);
lean_inc(v_snd_1567_);
lean_dec(v_snd_1565_);
lean_inc(v_a_1541_);
lean_inc_ref(v_a_1540_);
lean_inc(v_a_1539_);
lean_inc_ref(v_a_1538_);
v___x_1568_ = lean_whnf(v_fst_1566_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v___x_1570_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_a_1569_);
lean_dec_ref_known(v___x_1568_, 1);
lean_inc(v_a_1541_);
lean_inc_ref(v_a_1540_);
lean_inc(v_a_1539_);
lean_inc_ref(v_a_1538_);
v___x_1570_ = lean_whnf(v_snd_1567_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; lean_object* v___f_1572_; uint8_t v___y_1574_; uint8_t v___x_1580_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_a_1571_);
lean_dec_ref_known(v___x_1570_, 1);
lean_inc(v_forbidden_1537_);
lean_inc(v_tail_1551_);
lean_inc(v_newNames_1536_);
lean_inc(v_mvarId_1535_);
v___f_1572_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0___boxed), 11, 6);
lean_closure_set(v___f_1572_, 0, v_mvarId_1535_);
lean_closure_set(v___f_1572_, 1, v_head_1550_);
lean_closure_set(v___f_1572_, 2, v_newNames_1536_);
lean_closure_set(v___f_1572_, 3, v_tail_1551_);
lean_closure_set(v___f_1572_, 4, v_forbidden_1537_);
lean_closure_set(v___f_1572_, 5, v_n_1553_);
v___x_1580_ = l_Lean_Expr_isRawNatLit(v_a_1569_);
lean_dec(v_a_1569_);
if (v___x_1580_ == 0)
{
lean_dec(v_a_1571_);
v___y_1574_ = v___x_1559_;
goto v___jp_1573_;
}
else
{
uint8_t v___x_1581_; 
v___x_1581_ = l_Lean_Expr_isRawNatLit(v_a_1571_);
lean_dec(v_a_1571_);
v___y_1574_ = v___x_1581_;
goto v___jp_1573_;
}
v___jp_1573_:
{
if (v___y_1574_ == 0)
{
lean_object* v___x_1575_; 
v___x_1575_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(v___f_1572_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_dec(v___x_1554_);
lean_dec(v_tail_1551_);
lean_dec(v_forbidden_1537_);
lean_dec(v_newNames_1536_);
lean_dec(v_mvarId_1535_);
return v___x_1575_;
}
else
{
lean_object* v_a_1576_; uint8_t v___x_1577_; 
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_a_1576_);
v___x_1577_ = l_Lean_Exception_isInterrupt(v_a_1576_);
if (v___x_1577_ == 0)
{
uint8_t v___x_1578_; 
v___x_1578_ = l_Lean_Exception_isRuntime(v_a_1576_);
v___y_1556_ = v___x_1575_;
v___y_1557_ = v___x_1578_;
goto v___jp_1555_;
}
else
{
lean_dec(v_a_1576_);
v___y_1556_ = v___x_1575_;
v___y_1557_ = v___x_1577_;
goto v___jp_1555_;
}
}
}
else
{
lean_dec_ref(v___f_1572_);
v_depth_1533_ = v___x_1554_;
v_fvarIds_1534_ = v_tail_1551_;
goto _start;
}
}
}
else
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
lean_dec(v_a_1569_);
lean_dec(v___x_1554_);
lean_dec(v_n_1553_);
lean_dec(v_tail_1551_);
lean_dec(v_head_1550_);
lean_dec(v_forbidden_1537_);
lean_dec(v_newNames_1536_);
lean_dec(v_mvarId_1535_);
v_a_1582_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1570_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1570_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
else
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
lean_dec(v_snd_1567_);
lean_dec(v___x_1554_);
lean_dec(v_n_1553_);
lean_dec(v_tail_1551_);
lean_dec(v_head_1550_);
lean_dec(v_forbidden_1537_);
lean_dec(v_newNames_1536_);
lean_dec(v_mvarId_1535_);
v_a_1590_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1592_ = v___x_1568_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1568_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1590_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
else
{
lean_dec(v_a_1563_);
lean_dec(v_n_1553_);
lean_dec(v_head_1550_);
v_depth_1533_ = v___x_1554_;
v_fvarIds_1534_ = v_tail_1551_;
goto _start;
}
}
else
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
lean_dec(v___x_1554_);
lean_dec(v_n_1553_);
lean_dec(v_tail_1551_);
lean_dec(v_head_1550_);
lean_dec(v_forbidden_1537_);
lean_dec(v_newNames_1536_);
lean_dec(v_mvarId_1535_);
v_a_1599_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___x_1562_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1562_);
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
lean_dec(v___x_1554_);
lean_dec(v_n_1553_);
lean_dec(v_tail_1551_);
lean_dec(v_head_1550_);
lean_dec(v_forbidden_1537_);
lean_dec(v_newNames_1536_);
lean_dec(v_mvarId_1535_);
v_a_1607_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1560_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1560_);
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
lean_dec(v_n_1553_);
lean_dec(v_head_1550_);
v_depth_1533_ = v___x_1554_;
v_fvarIds_1534_ = v_tail_1551_;
goto _start;
}
v___jp_1555_:
{
if (v___y_1557_ == 0)
{
lean_dec_ref(v___y_1556_);
v_depth_1533_ = v___x_1554_;
v_fvarIds_1534_ = v_tail_1551_;
goto _start;
}
else
{
lean_dec(v___x_1554_);
lean_dec(v_tail_1551_);
lean_dec(v_forbidden_1537_);
lean_dec(v_newNames_1536_);
lean_dec(v_mvarId_1535_);
return v___y_1556_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___boxed(lean_object* v_depth_1616_, lean_object* v_fvarIds_1617_, lean_object* v_mvarId_1618_, lean_object* v_newNames_1619_, lean_object* v_forbidden_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go(v_depth_1616_, v_fvarIds_1617_, v_mvarId_1618_, v_newNames_1619_, v_forbidden_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_);
lean_dec(v_a_1624_);
lean_dec_ref(v_a_1623_);
lean_dec(v_a_1622_);
lean_dec_ref(v_a_1621_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0(lean_object* v_mvarId_1627_, lean_object* v_head_1628_, lean_object* v_newNames_1629_, lean_object* v_tail_1630_, lean_object* v_forbidden_1631_, lean_object* v_n_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v___x_1638_; 
lean_inc(v_head_1628_);
v___x_1638_ = l_Lean_Meta_injection(v_mvarId_1627_, v_head_1628_, v_newNames_1629_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1655_; 
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1641_ = v___x_1638_;
v_isShared_1642_ = v_isSharedCheck_1655_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1638_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1655_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
if (lean_obj_tag(v_a_1639_) == 0)
{
lean_object* v___x_1643_; lean_object* v___x_1645_; 
lean_dec(v_n_1632_);
lean_dec(v_forbidden_1631_);
lean_dec(v_tail_1630_);
lean_dec(v_head_1628_);
v___x_1643_ = lean_box(0);
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 0, v___x_1643_);
v___x_1645_ = v___x_1641_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1643_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
else
{
lean_object* v_mvarId_1647_; lean_object* v_newEqs_1648_; lean_object* v_remainingNames_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
lean_del_object(v___x_1641_);
v_mvarId_1647_ = lean_ctor_get(v_a_1639_, 0);
lean_inc_n(v_mvarId_1647_, 2);
v_newEqs_1648_ = lean_ctor_get(v_a_1639_, 1);
lean_inc_ref(v_newEqs_1648_);
v_remainingNames_1649_ = lean_ctor_get(v_a_1639_, 2);
lean_inc(v_remainingNames_1649_);
lean_dec_ref_known(v_a_1639_, 3);
v___x_1650_ = lean_array_to_list(v_newEqs_1648_);
v___x_1651_ = l_List_appendTR___redArg(v___x_1650_, v_tail_1630_);
v___x_1652_ = l_Lean_FVarIdSet_insert(v_forbidden_1631_, v_head_1628_);
v___x_1653_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___boxed), 10, 5);
lean_closure_set(v___x_1653_, 0, v_n_1632_);
lean_closure_set(v___x_1653_, 1, v___x_1651_);
lean_closure_set(v___x_1653_, 2, v_mvarId_1647_);
lean_closure_set(v___x_1653_, 3, v_remainingNames_1649_);
lean_closure_set(v___x_1653_, 4, v___x_1652_);
v___x_1654_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg(v_mvarId_1647_, v___x_1653_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
return v___x_1654_;
}
}
}
else
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
lean_dec(v_n_1632_);
lean_dec(v_forbidden_1631_);
lean_dec(v_tail_1630_);
lean_dec(v_head_1628_);
v_a_1656_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1638_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1638_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1656_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0(lean_object* v_00_u03b2_1664_, lean_object* v_k_1665_, lean_object* v_t_1666_){
_start:
{
uint8_t v___x_1667_; 
v___x_1667_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(v_k_1665_, v_t_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___boxed(lean_object* v_00_u03b2_1668_, lean_object* v_k_1669_, lean_object* v_t_1670_){
_start:
{
uint8_t v_res_1671_; lean_object* v_r_1672_; 
v_res_1671_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0(v_00_u03b2_1668_, v_k_1669_, v_t_1670_);
lean_dec(v_t_1670_);
lean_dec(v_k_1669_);
v_r_1672_ = lean_box(v_res_1671_);
return v_r_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections___lam__0(lean_object* v_maxDepth_1673_, lean_object* v_mvarId_1674_, lean_object* v_newNames_1675_, lean_object* v_forbidden_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v_lctx_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v_lctx_1682_ = lean_ctor_get(v___y_1677_, 2);
v___x_1683_ = l_Lean_LocalContext_getFVarIds(v_lctx_1682_);
v___x_1684_ = lean_array_to_list(v___x_1683_);
v___x_1685_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go(v_maxDepth_1673_, v___x_1684_, v_mvarId_1674_, v_newNames_1675_, v_forbidden_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections___lam__0___boxed(lean_object* v_maxDepth_1686_, lean_object* v_mvarId_1687_, lean_object* v_newNames_1688_, lean_object* v_forbidden_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lean_Meta_injections___lam__0(v_maxDepth_1686_, v_mvarId_1687_, v_newNames_1688_, v_forbidden_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections(lean_object* v_mvarId_1696_, lean_object* v_newNames_1697_, lean_object* v_maxDepth_1698_, lean_object* v_forbidden_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_){
_start:
{
lean_object* v___f_1705_; lean_object* v___x_1706_; 
lean_inc(v_mvarId_1696_);
v___f_1705_ = lean_alloc_closure((void*)(l_Lean_Meta_injections___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1705_, 0, v_maxDepth_1698_);
lean_closure_set(v___f_1705_, 1, v_mvarId_1696_);
lean_closure_set(v___f_1705_, 2, v_newNames_1697_);
lean_closure_set(v___f_1705_, 3, v_forbidden_1699_);
v___x_1706_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg(v_mvarId_1696_, v___f_1705_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections___boxed(lean_object* v_mvarId_1707_, lean_object* v_newNames_1708_, lean_object* v_maxDepth_1709_, lean_object* v_forbidden_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Lean_Meta_injections(v_mvarId_1707_, v_newNames_1708_, v_maxDepth_1709_, v_forbidden_1710_, v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_);
lean_dec(v_a_1714_);
lean_dec_ref(v_a_1713_);
lean_dec(v_a_1712_);
lean_dec_ref(v_a_1711_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1773_; uint8_t v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1773_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__1));
v___x_1774_ = 0;
v___x_1775_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__22_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_));
v___x_1776_ = l_Lean_registerTraceClass(v___x_1773_, v___x_1774_, v___x_1775_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2____boxed(lean_object* v_a_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l___private_Lean_Meta_Tactic_Injection_0__initFn_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_();
return v_res_1778_;
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
