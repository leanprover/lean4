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
lean_object* v_options_302_; uint8_t v_hasTrace_303_; 
v_options_302_ = lean_ctor_get(v___y_299_, 1);
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
lean_object* v_toCold_306_; lean_object* v_inheritedTraceOptions_307_; lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v_toCold_306_ = lean_ctor_get(v___y_299_, 0);
v_inheritedTraceOptions_307_ = lean_ctor_get(v_toCold_306_, 4);
v___x_308_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__0___closed__1));
v___x_309_ = l_Lean_Name_append(v___x_308_, v___x_296_);
v___x_310_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_307_, v_options_302_, v___x_309_);
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
lean_object* v___x_326_; lean_object* v_env_327_; lean_object* v___x_328_; lean_object* v_mctx_329_; lean_object* v_lctx_330_; lean_object* v_options_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_326_ = lean_st_ref_get(v___y_324_);
v_env_327_ = lean_ctor_get(v___x_326_, 0);
lean_inc_ref(v_env_327_);
lean_dec(v___x_326_);
v___x_328_ = lean_st_ref_get(v___y_322_);
v_mctx_329_ = lean_ctor_get(v___x_328_, 0);
lean_inc_ref(v_mctx_329_);
lean_dec(v___x_328_);
v_lctx_330_ = lean_ctor_get(v___y_321_, 2);
v_options_331_ = lean_ctor_get(v___y_323_, 1);
lean_inc_ref(v_options_331_);
lean_inc_ref(v_lctx_330_);
v___x_332_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_332_, 0, v_env_327_);
lean_ctor_set(v___x_332_, 1, v_mctx_329_);
lean_ctor_set(v___x_332_, 2, v_lctx_330_);
lean_ctor_set(v___x_332_, 3, v_options_331_);
v___x_333_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v_msgData_320_);
v___x_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1_spec__2___boxed(lean_object* v_msgData_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1_spec__2(v_msgData_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
return v_res_341_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__0(void){
_start:
{
lean_object* v___x_342_; double v___x_343_; 
v___x_342_ = lean_unsigned_to_nat(0u);
v___x_343_ = lean_float_of_nat(v___x_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(lean_object* v_cls_347_, lean_object* v_msg_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
lean_object* v_ref_354_; lean_object* v___x_355_; lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_400_; 
v_ref_354_ = lean_ctor_get(v___y_351_, 4);
v___x_355_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1_spec__2(v_msg_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
v_a_356_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_400_ == 0)
{
v___x_358_ = v___x_355_;
v_isShared_359_ = v_isSharedCheck_400_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_355_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_400_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_360_; lean_object* v_traceState_361_; lean_object* v_env_362_; lean_object* v_nextMacroScope_363_; lean_object* v_ngen_364_; lean_object* v_auxDeclNGen_365_; lean_object* v_cache_366_; lean_object* v_messages_367_; lean_object* v_infoState_368_; lean_object* v_snapshotTasks_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_399_; 
v___x_360_ = lean_st_ref_take(v___y_352_);
v_traceState_361_ = lean_ctor_get(v___x_360_, 4);
v_env_362_ = lean_ctor_get(v___x_360_, 0);
v_nextMacroScope_363_ = lean_ctor_get(v___x_360_, 1);
v_ngen_364_ = lean_ctor_get(v___x_360_, 2);
v_auxDeclNGen_365_ = lean_ctor_get(v___x_360_, 3);
v_cache_366_ = lean_ctor_get(v___x_360_, 5);
v_messages_367_ = lean_ctor_get(v___x_360_, 6);
v_infoState_368_ = lean_ctor_get(v___x_360_, 7);
v_snapshotTasks_369_ = lean_ctor_get(v___x_360_, 8);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_399_ == 0)
{
v___x_371_ = v___x_360_;
v_isShared_372_ = v_isSharedCheck_399_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_snapshotTasks_369_);
lean_inc(v_infoState_368_);
lean_inc(v_messages_367_);
lean_inc(v_cache_366_);
lean_inc(v_traceState_361_);
lean_inc(v_auxDeclNGen_365_);
lean_inc(v_ngen_364_);
lean_inc(v_nextMacroScope_363_);
lean_inc(v_env_362_);
lean_dec(v___x_360_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_399_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
uint64_t v_tid_373_; lean_object* v_traces_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_398_; 
v_tid_373_ = lean_ctor_get_uint64(v_traceState_361_, sizeof(void*)*1);
v_traces_374_ = lean_ctor_get(v_traceState_361_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v_traceState_361_);
if (v_isSharedCheck_398_ == 0)
{
v___x_376_ = v_traceState_361_;
v_isShared_377_ = v_isSharedCheck_398_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_traces_374_);
lean_dec(v_traceState_361_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_398_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_378_; double v___x_379_; uint8_t v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_378_ = lean_box(0);
v___x_379_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__0);
v___x_380_ = 0;
v___x_381_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__1));
v___x_382_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_382_, 0, v_cls_347_);
lean_ctor_set(v___x_382_, 1, v___x_378_);
lean_ctor_set(v___x_382_, 2, v___x_381_);
lean_ctor_set_float(v___x_382_, sizeof(void*)*3, v___x_379_);
lean_ctor_set_float(v___x_382_, sizeof(void*)*3 + 8, v___x_379_);
lean_ctor_set_uint8(v___x_382_, sizeof(void*)*3 + 16, v___x_380_);
v___x_383_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__2));
v___x_384_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_384_, 0, v___x_382_);
lean_ctor_set(v___x_384_, 1, v_a_356_);
lean_ctor_set(v___x_384_, 2, v___x_383_);
lean_inc(v_ref_354_);
v___x_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_385_, 0, v_ref_354_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
v___x_386_ = l_Lean_PersistentArray_push___redArg(v_traces_374_, v___x_385_);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v___x_386_);
v___x_388_ = v___x_376_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_386_);
lean_ctor_set_uint64(v_reuseFailAlloc_397_, sizeof(void*)*1, v_tid_373_);
v___x_388_ = v_reuseFailAlloc_397_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
lean_object* v___x_390_; 
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 4, v___x_388_);
v___x_390_ = v___x_371_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_env_362_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v_nextMacroScope_363_);
lean_ctor_set(v_reuseFailAlloc_396_, 2, v_ngen_364_);
lean_ctor_set(v_reuseFailAlloc_396_, 3, v_auxDeclNGen_365_);
lean_ctor_set(v_reuseFailAlloc_396_, 4, v___x_388_);
lean_ctor_set(v_reuseFailAlloc_396_, 5, v_cache_366_);
lean_ctor_set(v_reuseFailAlloc_396_, 6, v_messages_367_);
lean_ctor_set(v_reuseFailAlloc_396_, 7, v_infoState_368_);
lean_ctor_set(v_reuseFailAlloc_396_, 8, v_snapshotTasks_369_);
v___x_390_ = v_reuseFailAlloc_396_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_391_ = lean_st_ref_put(v___y_352_, v___x_390_);
v___x_392_ = lean_box(0);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v___x_392_);
v___x_394_ = v___x_358_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_392_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___boxed(lean_object* v_cls_401_, lean_object* v_msg_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v_cls_401_, v_msg_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(lean_object* v_x_409_, lean_object* v_x_410_, lean_object* v_x_411_, lean_object* v_x_412_){
_start:
{
lean_object* v_ks_413_; lean_object* v_vs_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_438_; 
v_ks_413_ = lean_ctor_get(v_x_409_, 0);
v_vs_414_ = lean_ctor_get(v_x_409_, 1);
v_isSharedCheck_438_ = !lean_is_exclusive(v_x_409_);
if (v_isSharedCheck_438_ == 0)
{
v___x_416_ = v_x_409_;
v_isShared_417_ = v_isSharedCheck_438_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_vs_414_);
lean_inc(v_ks_413_);
lean_dec(v_x_409_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_438_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_418_; uint8_t v___x_419_; 
v___x_418_ = lean_array_get_size(v_ks_413_);
v___x_419_ = lean_nat_dec_lt(v_x_410_, v___x_418_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_423_; 
lean_dec(v_x_410_);
v___x_420_ = lean_array_push(v_ks_413_, v_x_411_);
v___x_421_ = lean_array_push(v_vs_414_, v_x_412_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 1, v___x_421_);
lean_ctor_set(v___x_416_, 0, v___x_420_);
v___x_423_ = v___x_416_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_420_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v___x_421_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
else
{
lean_object* v_k_x27_425_; uint8_t v___x_426_; 
v_k_x27_425_ = lean_array_fget_borrowed(v_ks_413_, v_x_410_);
v___x_426_ = l_Lean_instBEqMVarId_beq(v_x_411_, v_k_x27_425_);
if (v___x_426_ == 0)
{
lean_object* v___x_428_; 
if (v_isShared_417_ == 0)
{
v___x_428_ = v___x_416_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_ks_413_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v_vs_414_);
v___x_428_ = v_reuseFailAlloc_432_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = lean_unsigned_to_nat(1u);
v___x_430_ = lean_nat_add(v_x_410_, v___x_429_);
lean_dec(v_x_410_);
v_x_409_ = v___x_428_;
v_x_410_ = v___x_430_;
goto _start;
}
}
else
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_436_; 
v___x_433_ = lean_array_fset(v_ks_413_, v_x_410_, v_x_411_);
v___x_434_ = lean_array_fset(v_vs_414_, v_x_410_, v_x_412_);
lean_dec(v_x_410_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 1, v___x_434_);
lean_ctor_set(v___x_416_, 0, v___x_433_);
v___x_436_ = v___x_416_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v___x_434_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_n_439_, lean_object* v_k_440_, lean_object* v_v_441_){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = lean_unsigned_to_nat(0u);
v___x_443_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(v_n_439_, v___x_442_, v_k_440_, v_v_441_);
return v___x_443_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(lean_object* v_x_445_, size_t v_x_446_, size_t v_x_447_, lean_object* v_x_448_, lean_object* v_x_449_){
_start:
{
if (lean_obj_tag(v_x_445_) == 0)
{
lean_object* v_es_450_; size_t v___x_451_; size_t v___x_452_; lean_object* v_j_453_; lean_object* v___x_454_; uint8_t v___x_455_; 
v_es_450_ = lean_ctor_get(v_x_445_, 0);
v___x_451_ = ((size_t)31ULL);
v___x_452_ = lean_usize_land(v_x_446_, v___x_451_);
v_j_453_ = lean_usize_to_nat(v___x_452_);
v___x_454_ = lean_array_get_size(v_es_450_);
v___x_455_ = lean_nat_dec_lt(v_j_453_, v___x_454_);
if (v___x_455_ == 0)
{
lean_dec(v_j_453_);
lean_dec(v_x_449_);
lean_dec(v_x_448_);
return v_x_445_;
}
else
{
lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_494_; 
lean_inc_ref(v_es_450_);
v_isSharedCheck_494_ = !lean_is_exclusive(v_x_445_);
if (v_isSharedCheck_494_ == 0)
{
lean_object* v_unused_495_; 
v_unused_495_ = lean_ctor_get(v_x_445_, 0);
lean_dec(v_unused_495_);
v___x_457_ = v_x_445_;
v_isShared_458_ = v_isSharedCheck_494_;
goto v_resetjp_456_;
}
else
{
lean_dec(v_x_445_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_494_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v_v_459_; lean_object* v___x_460_; lean_object* v_xs_x27_461_; lean_object* v___y_463_; 
v_v_459_ = lean_array_fget(v_es_450_, v_j_453_);
v___x_460_ = lean_box(0);
v_xs_x27_461_ = lean_array_fset(v_es_450_, v_j_453_, v___x_460_);
switch(lean_obj_tag(v_v_459_))
{
case 0:
{
lean_object* v_key_468_; lean_object* v_val_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_479_; 
v_key_468_ = lean_ctor_get(v_v_459_, 0);
v_val_469_ = lean_ctor_get(v_v_459_, 1);
v_isSharedCheck_479_ = !lean_is_exclusive(v_v_459_);
if (v_isSharedCheck_479_ == 0)
{
v___x_471_ = v_v_459_;
v_isShared_472_ = v_isSharedCheck_479_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_val_469_);
lean_inc(v_key_468_);
lean_dec(v_v_459_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_479_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
uint8_t v___x_473_; 
v___x_473_ = l_Lean_instBEqMVarId_beq(v_x_448_, v_key_468_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; lean_object* v___x_475_; 
lean_del_object(v___x_471_);
v___x_474_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_468_, v_val_469_, v_x_448_, v_x_449_);
v___x_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
v___y_463_ = v___x_475_;
goto v___jp_462_;
}
else
{
lean_object* v___x_477_; 
lean_dec(v_val_469_);
lean_dec(v_key_468_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 1, v_x_449_);
lean_ctor_set(v___x_471_, 0, v_x_448_);
v___x_477_ = v___x_471_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_x_448_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v_x_449_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
v___y_463_ = v___x_477_;
goto v___jp_462_;
}
}
}
}
case 1:
{
lean_object* v_node_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_492_; 
v_node_480_ = lean_ctor_get(v_v_459_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v_v_459_);
if (v_isSharedCheck_492_ == 0)
{
v___x_482_ = v_v_459_;
v_isShared_483_ = v_isSharedCheck_492_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_node_480_);
lean_dec(v_v_459_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_492_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
size_t v___x_484_; size_t v___x_485_; size_t v___x_486_; size_t v___x_487_; lean_object* v___x_488_; lean_object* v___x_490_; 
v___x_484_ = ((size_t)5ULL);
v___x_485_ = lean_usize_shift_right(v_x_446_, v___x_484_);
v___x_486_ = ((size_t)1ULL);
v___x_487_ = lean_usize_add(v_x_447_, v___x_486_);
v___x_488_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(v_node_480_, v___x_485_, v___x_487_, v_x_448_, v_x_449_);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 0, v___x_488_);
v___x_490_ = v___x_482_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_488_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
v___y_463_ = v___x_490_;
goto v___jp_462_;
}
}
}
default: 
{
lean_object* v___x_493_; 
v___x_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_493_, 0, v_x_448_);
lean_ctor_set(v___x_493_, 1, v_x_449_);
v___y_463_ = v___x_493_;
goto v___jp_462_;
}
}
v___jp_462_:
{
lean_object* v___x_464_; lean_object* v___x_466_; 
v___x_464_ = lean_array_fset(v_xs_x27_461_, v_j_453_, v___y_463_);
lean_dec(v_j_453_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 0, v___x_464_);
v___x_466_ = v___x_457_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_464_);
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
}
else
{
lean_object* v_ks_496_; lean_object* v_vs_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_515_; 
v_ks_496_ = lean_ctor_get(v_x_445_, 0);
v_vs_497_ = lean_ctor_get(v_x_445_, 1);
v_isSharedCheck_515_ = !lean_is_exclusive(v_x_445_);
if (v_isSharedCheck_515_ == 0)
{
v___x_499_ = v_x_445_;
v_isShared_500_ = v_isSharedCheck_515_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_vs_497_);
lean_inc(v_ks_496_);
lean_dec(v_x_445_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_515_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_ks_496_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v_vs_497_);
v___x_502_ = v_reuseFailAlloc_514_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
lean_object* v_newNode_503_; size_t v___x_504_; uint8_t v___x_505_; 
v_newNode_503_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5___redArg(v___x_502_, v_x_448_, v_x_449_);
v___x_504_ = ((size_t)7ULL);
v___x_505_ = lean_usize_dec_le(v___x_504_, v_x_447_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v___x_506_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_503_);
v___x_507_ = lean_unsigned_to_nat(4u);
v___x_508_ = lean_nat_dec_lt(v___x_506_, v___x_507_);
lean_dec(v___x_506_);
if (v___x_508_ == 0)
{
lean_object* v_ks_509_; lean_object* v_vs_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v_ks_509_ = lean_ctor_get(v_newNode_503_, 0);
lean_inc_ref(v_ks_509_);
v_vs_510_ = lean_ctor_get(v_newNode_503_, 1);
lean_inc_ref(v_vs_510_);
lean_dec_ref(v_newNode_503_);
v___x_511_ = lean_unsigned_to_nat(0u);
v___x_512_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_513_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___redArg(v_x_447_, v_ks_509_, v_vs_510_, v___x_511_, v___x_512_);
lean_dec_ref(v_vs_510_);
lean_dec_ref(v_ks_509_);
return v___x_513_;
}
else
{
return v_newNode_503_;
}
}
else
{
return v_newNode_503_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___redArg(size_t v_depth_516_, lean_object* v_keys_517_, lean_object* v_vals_518_, lean_object* v_i_519_, lean_object* v_entries_520_){
_start:
{
lean_object* v___x_521_; uint8_t v___x_522_; 
v___x_521_ = lean_array_get_size(v_keys_517_);
v___x_522_ = lean_nat_dec_lt(v_i_519_, v___x_521_);
if (v___x_522_ == 0)
{
lean_dec(v_i_519_);
return v_entries_520_;
}
else
{
lean_object* v_k_523_; lean_object* v_v_524_; uint64_t v___x_525_; size_t v_h_526_; size_t v___x_527_; lean_object* v___x_528_; size_t v___x_529_; size_t v___x_530_; size_t v___x_531_; size_t v_h_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v_k_523_ = lean_array_fget_borrowed(v_keys_517_, v_i_519_);
v_v_524_ = lean_array_fget_borrowed(v_vals_518_, v_i_519_);
v___x_525_ = l_Lean_instHashableMVarId_hash(v_k_523_);
v_h_526_ = lean_uint64_to_usize(v___x_525_);
v___x_527_ = ((size_t)5ULL);
v___x_528_ = lean_unsigned_to_nat(1u);
v___x_529_ = ((size_t)1ULL);
v___x_530_ = lean_usize_sub(v_depth_516_, v___x_529_);
v___x_531_ = lean_usize_mul(v___x_527_, v___x_530_);
v_h_532_ = lean_usize_shift_right(v_h_526_, v___x_531_);
v___x_533_ = lean_nat_add(v_i_519_, v___x_528_);
lean_dec(v_i_519_);
lean_inc(v_v_524_);
lean_inc(v_k_523_);
v___x_534_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(v_entries_520_, v_h_532_, v_depth_516_, v_k_523_, v_v_524_);
v_i_519_ = v___x_533_;
v_entries_520_ = v___x_534_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_depth_536_, lean_object* v_keys_537_, lean_object* v_vals_538_, lean_object* v_i_539_, lean_object* v_entries_540_){
_start:
{
size_t v_depth_boxed_541_; lean_object* v_res_542_; 
v_depth_boxed_541_ = lean_unbox_usize(v_depth_536_);
lean_dec(v_depth_536_);
v_res_542_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___redArg(v_depth_boxed_541_, v_keys_537_, v_vals_538_, v_i_539_, v_entries_540_);
lean_dec_ref(v_vals_538_);
lean_dec_ref(v_keys_537_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_543_, lean_object* v_x_544_, lean_object* v_x_545_, lean_object* v_x_546_, lean_object* v_x_547_){
_start:
{
size_t v_x_14423__boxed_548_; size_t v_x_14424__boxed_549_; lean_object* v_res_550_; 
v_x_14423__boxed_548_ = lean_unbox_usize(v_x_544_);
lean_dec(v_x_544_);
v_x_14424__boxed_549_ = lean_unbox_usize(v_x_545_);
lean_dec(v_x_545_);
v_res_550_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(v_x_543_, v_x_14423__boxed_548_, v_x_14424__boxed_549_, v_x_546_, v_x_547_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0___redArg(lean_object* v_x_551_, lean_object* v_x_552_, lean_object* v_x_553_){
_start:
{
uint64_t v___x_554_; size_t v___x_555_; size_t v___x_556_; lean_object* v___x_557_; 
v___x_554_ = l_Lean_instHashableMVarId_hash(v_x_552_);
v___x_555_ = lean_uint64_to_usize(v___x_554_);
v___x_556_ = ((size_t)1ULL);
v___x_557_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(v_x_551_, v___x_555_, v___x_556_, v_x_552_, v_x_553_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(lean_object* v_mvarId_558_, lean_object* v_val_559_, lean_object* v___y_560_){
_start:
{
lean_object* v___x_562_; lean_object* v_mctx_563_; lean_object* v_cache_564_; lean_object* v_zetaDeltaFVarIds_565_; lean_object* v_postponed_566_; lean_object* v_diag_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_596_; 
v___x_562_ = lean_st_ref_take(v___y_560_);
v_mctx_563_ = lean_ctor_get(v___x_562_, 0);
v_cache_564_ = lean_ctor_get(v___x_562_, 1);
v_zetaDeltaFVarIds_565_ = lean_ctor_get(v___x_562_, 2);
v_postponed_566_ = lean_ctor_get(v___x_562_, 3);
v_diag_567_ = lean_ctor_get(v___x_562_, 4);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_596_ == 0)
{
v___x_569_ = v___x_562_;
v_isShared_570_ = v_isSharedCheck_596_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_diag_567_);
lean_inc(v_postponed_566_);
lean_inc(v_zetaDeltaFVarIds_565_);
lean_inc(v_cache_564_);
lean_inc(v_mctx_563_);
lean_dec(v___x_562_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_596_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v_depth_571_; lean_object* v_levelAssignDepth_572_; lean_object* v_lmvarCounter_573_; lean_object* v_mvarCounter_574_; lean_object* v_lDecls_575_; lean_object* v_decls_576_; lean_object* v_userNames_577_; lean_object* v_lAssignment_578_; lean_object* v_eAssignment_579_; lean_object* v_dAssignment_580_; lean_object* v_instanceTypedMVars_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_595_; 
v_depth_571_ = lean_ctor_get(v_mctx_563_, 0);
v_levelAssignDepth_572_ = lean_ctor_get(v_mctx_563_, 1);
v_lmvarCounter_573_ = lean_ctor_get(v_mctx_563_, 2);
v_mvarCounter_574_ = lean_ctor_get(v_mctx_563_, 3);
v_lDecls_575_ = lean_ctor_get(v_mctx_563_, 4);
v_decls_576_ = lean_ctor_get(v_mctx_563_, 5);
v_userNames_577_ = lean_ctor_get(v_mctx_563_, 6);
v_lAssignment_578_ = lean_ctor_get(v_mctx_563_, 7);
v_eAssignment_579_ = lean_ctor_get(v_mctx_563_, 8);
v_dAssignment_580_ = lean_ctor_get(v_mctx_563_, 9);
v_instanceTypedMVars_581_ = lean_ctor_get(v_mctx_563_, 10);
v_isSharedCheck_595_ = !lean_is_exclusive(v_mctx_563_);
if (v_isSharedCheck_595_ == 0)
{
v___x_583_ = v_mctx_563_;
v_isShared_584_ = v_isSharedCheck_595_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_instanceTypedMVars_581_);
lean_inc(v_dAssignment_580_);
lean_inc(v_eAssignment_579_);
lean_inc(v_lAssignment_578_);
lean_inc(v_userNames_577_);
lean_inc(v_decls_576_);
lean_inc(v_lDecls_575_);
lean_inc(v_mvarCounter_574_);
lean_inc(v_lmvarCounter_573_);
lean_inc(v_levelAssignDepth_572_);
lean_inc(v_depth_571_);
lean_dec(v_mctx_563_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_595_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_585_; lean_object* v___x_587_; 
v___x_585_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0___redArg(v_eAssignment_579_, v_mvarId_558_, v_val_559_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 8, v___x_585_);
v___x_587_ = v___x_583_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_depth_571_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_levelAssignDepth_572_);
lean_ctor_set(v_reuseFailAlloc_594_, 2, v_lmvarCounter_573_);
lean_ctor_set(v_reuseFailAlloc_594_, 3, v_mvarCounter_574_);
lean_ctor_set(v_reuseFailAlloc_594_, 4, v_lDecls_575_);
lean_ctor_set(v_reuseFailAlloc_594_, 5, v_decls_576_);
lean_ctor_set(v_reuseFailAlloc_594_, 6, v_userNames_577_);
lean_ctor_set(v_reuseFailAlloc_594_, 7, v_lAssignment_578_);
lean_ctor_set(v_reuseFailAlloc_594_, 8, v___x_585_);
lean_ctor_set(v_reuseFailAlloc_594_, 9, v_dAssignment_580_);
lean_ctor_set(v_reuseFailAlloc_594_, 10, v_instanceTypedMVars_581_);
v___x_587_ = v_reuseFailAlloc_594_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
lean_object* v___x_589_; 
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 0, v___x_587_);
v___x_589_ = v___x_569_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_587_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v_cache_564_);
lean_ctor_set(v_reuseFailAlloc_593_, 2, v_zetaDeltaFVarIds_565_);
lean_ctor_set(v_reuseFailAlloc_593_, 3, v_postponed_566_);
lean_ctor_set(v_reuseFailAlloc_593_, 4, v_diag_567_);
v___x_589_ = v_reuseFailAlloc_593_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_590_ = lean_st_ref_put(v___y_560_, v___x_589_);
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
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__15(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__14));
v___x_627_ = l_Lean_stringToMessageData(v___x_626_);
return v___x_627_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__17(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__16));
v___x_630_ = l_Lean_stringToMessageData(v___x_629_);
return v___x_630_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__22(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__21));
v___x_638_ = l_Lean_MessageData_ofFormat(v___x_637_);
return v___x_638_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__23(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__22, &l_Lean_Meta_injectionCore___lam__1___closed__22_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__22);
v___x_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
return v___x_640_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__27(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__26));
v___x_645_ = l_Lean_stringToMessageData(v___x_644_);
return v___x_645_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__29(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__28));
v___x_648_ = l_Lean_stringToMessageData(v___x_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___lam__1(lean_object* v_mvarId_652_, lean_object* v___x_653_, lean_object* v_fvarId_654_, lean_object* v___x_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_669_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; lean_object* v___y_893_; lean_object* v_type_914_; lean_object* v_prf_915_; lean_object* v___y_916_; lean_object* v___y_917_; lean_object* v___y_918_; lean_object* v___y_919_; lean_object* v___x_999_; 
lean_inc(v___x_653_);
lean_inc(v_mvarId_652_);
v___x_999_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_652_, v___x_653_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v___x_1000_; 
lean_dec_ref_known(v___x_999_, 1);
lean_inc(v_fvarId_654_);
v___x_1000_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_654_, v___y_656_, v___y_658_, v___y_659_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_1000_, 1);
v___x_1002_ = l_Lean_LocalDecl_type(v_a_1001_);
lean_dec(v_a_1001_);
lean_inc(v___y_659_);
lean_inc_ref(v___y_658_);
lean_inc(v___y_657_);
lean_inc_ref(v___y_656_);
v___x_1003_ = lean_whnf(v___x_1002_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; uint8_t v___x_1008_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref_known(v___x_1003_, 1);
lean_inc(v_fvarId_654_);
v___x_1005_ = l_Lean_mkFVar(v_fvarId_654_);
v___x_1006_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__31));
v___x_1007_ = lean_unsigned_to_nat(4u);
v___x_1008_ = l_Lean_Expr_isAppOfArity(v_a_1004_, v___x_1006_, v___x_1007_);
if (v___x_1008_ == 0)
{
v_type_914_ = v_a_1004_;
v_prf_915_ = v___x_1005_;
v___y_916_ = v___y_656_;
v___y_917_ = v___y_657_;
v___y_918_ = v___y_658_;
v___y_919_ = v___y_659_;
goto v___jp_913_;
}
else
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1009_ = l_Lean_Expr_appFn_x21(v_a_1004_);
v___x_1010_ = l_Lean_Expr_appFn_x21(v___x_1009_);
v___x_1011_ = l_Lean_Expr_appFn_x21(v___x_1010_);
v___x_1012_ = l_Lean_Expr_appArg_x21(v___x_1011_);
lean_dec_ref(v___x_1011_);
v___x_1013_ = l_Lean_Expr_appArg_x21(v___x_1009_);
lean_dec_ref(v___x_1009_);
v___x_1014_ = l_Lean_Meta_isExprDefEq(v___x_1012_, v___x_1013_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; uint8_t v___x_1016_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_a_1015_);
lean_dec_ref_known(v___x_1014_, 1);
v___x_1016_ = lean_unbox(v_a_1015_);
lean_dec(v_a_1015_);
if (v___x_1016_ == 0)
{
lean_dec_ref(v___x_1010_);
v_type_914_ = v_a_1004_;
v_prf_915_ = v___x_1005_;
v___y_916_ = v___y_656_;
v___y_917_ = v___y_657_;
v___y_918_ = v___y_658_;
v___y_919_ = v___y_659_;
goto v___jp_913_;
}
else
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1017_ = l_Lean_Expr_appArg_x21(v___x_1010_);
lean_dec_ref(v___x_1010_);
v___x_1018_ = l_Lean_Expr_appArg_x21(v_a_1004_);
lean_dec(v_a_1004_);
v___x_1019_ = l_Lean_Meta_mkEq(v___x_1017_, v___x_1018_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1020_; lean_object* v___x_1021_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
lean_inc(v_a_1020_);
lean_dec_ref_known(v___x_1019_, 1);
v___x_1021_ = l_Lean_Meta_mkEqOfHEq(v___x_1005_, v___x_1008_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1022_);
lean_dec_ref_known(v___x_1021_, 1);
v_type_914_ = v_a_1020_;
v_prf_915_ = v_a_1022_;
v___y_916_ = v___y_656_;
v___y_917_ = v___y_657_;
v___y_918_ = v___y_658_;
v___y_919_ = v___y_659_;
goto v___jp_913_;
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_dec(v_a_1020_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec_ref(v___x_655_);
lean_dec(v_fvarId_654_);
lean_dec(v___x_653_);
lean_dec(v_mvarId_652_);
v_a_1023_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_1021_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1021_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
lean_dec_ref(v___x_1005_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec_ref(v___x_655_);
lean_dec(v_fvarId_654_);
lean_dec(v___x_653_);
lean_dec(v_mvarId_652_);
v_a_1031_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_1019_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1019_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
}
else
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
lean_dec_ref(v___x_1010_);
lean_dec_ref(v___x_1005_);
lean_dec(v_a_1004_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec_ref(v___x_655_);
lean_dec(v_fvarId_654_);
lean_dec(v___x_653_);
lean_dec(v_mvarId_652_);
v_a_1039_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_1014_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1014_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1039_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec_ref(v___x_655_);
lean_dec(v_fvarId_654_);
lean_dec(v___x_653_);
lean_dec(v_mvarId_652_);
v_a_1047_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_1003_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1003_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec_ref(v___x_655_);
lean_dec(v_fvarId_654_);
lean_dec(v___x_653_);
lean_dec(v_mvarId_652_);
v_a_1055_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___x_1000_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1000_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1055_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec_ref(v___x_655_);
lean_dec(v_fvarId_654_);
lean_dec(v___x_653_);
lean_dec(v_mvarId_652_);
v_a_1063_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v___x_999_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_999_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1068_; 
if (v_isShared_1066_ == 0)
{
v___x_1068_ = v___x_1065_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1063_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
v___jp_661_:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__3, &l_Lean_Meta_injectionCore___lam__1___closed__3_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__3);
v___x_667_ = l_Lean_Meta_throwTacticEx___redArg(v___x_653_, v_mvarId_652_, v___x_666_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
return v___x_667_;
}
v___jp_668_:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__7, &l_Lean_Meta_injectionCore___lam__1___closed__7_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__7);
v___x_674_ = l_Lean_Meta_throwTacticEx___redArg(v___x_653_, v_mvarId_652_, v___x_673_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
return v___x_674_;
}
v___jp_675_:
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_678_, 0, v___y_676_);
lean_ctor_set(v___x_678_, 1, v___y_677_);
v___x_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
return v___x_679_;
}
v___jp_680_:
{
lean_object* v_toConstantVal_690_; lean_object* v_toConstantVal_691_; lean_object* v_numFields_692_; lean_object* v_name_693_; lean_object* v_name_694_; uint8_t v___x_695_; 
v_toConstantVal_690_ = lean_ctor_get(v___y_682_, 0);
v_toConstantVal_691_ = lean_ctor_get(v___y_684_, 0);
lean_inc_ref(v_toConstantVal_691_);
lean_dec_ref(v___y_684_);
v_numFields_692_ = lean_ctor_get(v___y_682_, 4);
lean_inc(v_numFields_692_);
v_name_693_ = lean_ctor_get(v_toConstantVal_690_, 0);
v_name_694_ = lean_ctor_get(v_toConstantVal_691_, 0);
lean_inc(v_name_694_);
lean_dec_ref(v_toConstantVal_691_);
v___x_695_ = lean_name_eq(v_name_693_, v_name_694_);
lean_dec(v_name_694_);
if (v___x_695_ == 0)
{
lean_object* v___x_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_704_; 
lean_dec(v_numFields_692_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec_ref(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v_fvarId_654_);
lean_dec(v___x_653_);
v___x_696_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(v_mvarId_652_, v___y_681_, v___y_687_);
lean_dec(v___y_687_);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_704_ == 0)
{
lean_object* v_unused_705_; 
v_unused_705_ = lean_ctor_get(v___x_696_, 0);
lean_dec(v_unused_705_);
v___x_698_ = v___x_696_;
v_isShared_699_ = v_isSharedCheck_704_;
goto v_resetjp_697_;
}
else
{
lean_dec(v___x_696_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_704_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; lean_object* v___x_702_; 
v___x_700_ = lean_box(0);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v___x_700_);
v___x_702_ = v___x_698_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_700_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
else
{
lean_object* v___x_706_; 
lean_inc(v___y_689_);
lean_inc_ref(v___y_688_);
lean_inc(v___y_687_);
lean_inc_ref(v___y_686_);
lean_inc(v___y_681_);
v___x_706_ = lean_infer_type(v___y_681_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; lean_object* v___x_708_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_707_);
lean_dec_ref_known(v___x_706_, 1);
v___x_708_ = l_Lean_Meta_whnfD(v_a_707_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_a_709_);
lean_dec_ref_known(v___x_708_, 1);
if (lean_obj_tag(v_a_709_) == 7)
{
lean_object* v_binderType_710_; lean_object* v___x_711_; 
lean_dec_ref(v___y_685_);
lean_dec(v___x_653_);
v_binderType_710_ = lean_ctor_get(v_a_709_, 1);
lean_inc_ref(v_binderType_710_);
lean_dec_ref_known(v_a_709_, 3);
lean_inc(v_mvarId_652_);
v___x_711_ = l_Lean_MVarId_getTag(v_mvarId_652_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v_a_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v_a_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_a_712_);
lean_dec_ref_known(v___x_711_, 1);
v___x_713_ = l_Lean_Expr_headBeta(v_binderType_710_);
v___x_714_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_713_, v_a_712_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_770_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc_n(v_a_715_, 2);
lean_dec_ref_known(v___x_714_, 1);
v___x_716_ = l_Lean_Expr_app___override(v___y_681_, v_a_715_);
v___x_717_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(v_mvarId_652_, v___x_716_, v___y_687_);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_770_ == 0)
{
lean_object* v_unused_771_; 
v_unused_771_ = lean_ctor_get(v___x_717_, 0);
lean_dec(v_unused_771_);
v___x_719_ = v___x_717_;
v_isShared_720_ = v_isSharedCheck_770_;
goto v_resetjp_718_;
}
else
{
lean_dec(v___x_717_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_770_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = l_Lean_Expr_mvarId_x21(v_a_715_);
lean_dec(v_a_715_);
v___x_722_ = l_Lean_MVarId_tryClear(v___x_721_, v_fvarId_654_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; lean_object* v___x_724_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc(v_a_723_);
lean_dec_ref_known(v___x_722_, 1);
v___x_724_ = l_Lean_Meta_getCtorNumPropFields(v___y_682_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_options_725_; lean_object* v_a_726_; lean_object* v_toCold_727_; uint8_t v_hasTrace_728_; lean_object* v___x_729_; 
v_options_725_ = lean_ctor_get(v___y_688_, 1);
v_a_726_ = lean_ctor_get(v___x_724_, 0);
lean_inc(v_a_726_);
lean_dec_ref_known(v___x_724_, 1);
v_toCold_727_ = lean_ctor_get(v___y_688_, 0);
v_hasTrace_728_ = lean_ctor_get_uint8(v_options_725_, sizeof(void*)*1);
v___x_729_ = lean_nat_sub(v_numFields_692_, v_a_726_);
lean_dec(v_a_726_);
lean_dec(v_numFields_692_);
if (v_hasTrace_728_ == 0)
{
lean_del_object(v___x_719_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_683_);
v___y_676_ = v_a_723_;
v___y_677_ = v___x_729_;
goto v___jp_675_;
}
else
{
lean_object* v_inheritedTraceOptions_730_; lean_object* v___x_731_; lean_object* v___x_732_; uint8_t v___x_733_; 
v_inheritedTraceOptions_730_ = lean_ctor_get(v_toCold_727_, 4);
v___x_731_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__0___closed__1));
lean_inc(v___y_683_);
v___x_732_ = l_Lean_Name_append(v___x_731_, v___y_683_);
v___x_733_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_730_, v_options_725_, v___x_732_);
lean_dec(v___x_732_);
if (v___x_733_ == 0)
{
lean_del_object(v___x_719_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_683_);
v___y_676_ = v_a_723_;
v___y_677_ = v___x_729_;
goto v___jp_675_;
}
else
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_737_; 
v___x_734_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__9, &l_Lean_Meta_injectionCore___lam__1___closed__9_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__9);
lean_inc(v___x_729_);
v___x_735_ = l_Nat_reprFast(v___x_729_);
if (v_isShared_720_ == 0)
{
lean_ctor_set_tag(v___x_719_, 3);
lean_ctor_set(v___x_719_, 0, v___x_735_);
v___x_737_ = v___x_719_;
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
lean_inc(v_a_723_);
v___x_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_742_, 0, v_a_723_);
v___x_743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_741_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
v___x_744_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v___y_683_, v___x_743_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_dec_ref_known(v___x_744_, 1);
v___y_676_ = v_a_723_;
v___y_677_ = v___x_729_;
goto v___jp_675_;
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_dec(v___x_729_);
lean_dec(v_a_723_);
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
lean_dec(v_a_723_);
lean_del_object(v___x_719_);
lean_dec(v_numFields_692_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_683_);
v_a_754_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_724_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_724_);
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
lean_del_object(v___x_719_);
lean_dec(v_numFields_692_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
v_a_762_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_722_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_722_);
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
lean_dec(v_numFields_692_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec(v_fvarId_654_);
lean_dec(v_mvarId_652_);
v_a_772_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_779_ == 0)
{
v___x_774_ = v___x_714_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_714_);
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
lean_dec_ref(v_binderType_710_);
lean_dec(v_numFields_692_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec(v_fvarId_654_);
lean_dec(v_mvarId_652_);
v_a_780_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_787_ == 0)
{
v___x_782_ = v___x_711_;
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_711_);
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
lean_dec(v_numFields_692_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec(v_fvarId_654_);
lean_inc(v___y_689_);
lean_inc_ref(v___y_688_);
lean_inc(v___y_687_);
lean_inc_ref(v___y_686_);
v___x_788_ = lean_apply_5(v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, lean_box(0));
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
lean_dec(v_a_709_);
lean_dec(v___y_683_);
v___y_662_ = v___y_686_;
v___y_663_ = v___y_687_;
v___y_664_ = v___y_688_;
v___y_665_ = v___y_689_;
goto v___jp_661_;
}
else
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_791_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__13, &l_Lean_Meta_injectionCore___lam__1___closed__13_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__13);
v___x_792_ = l_Lean_indentExpr(v_a_709_);
v___x_793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_791_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
v___x_794_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v___y_683_, v___x_793_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_dec_ref_known(v___x_794_, 1);
v___y_662_ = v___y_686_;
v___y_663_ = v___y_687_;
v___y_664_ = v___y_688_;
v___y_665_ = v___y_689_;
goto v___jp_661_;
}
else
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___x_653_);
lean_dec(v_mvarId_652_);
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
lean_dec(v_a_709_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_683_);
lean_dec(v___x_653_);
lean_dec(v_mvarId_652_);
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
lean_dec(v_numFields_692_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec(v_fvarId_654_);
lean_dec(v___x_653_);
lean_dec(v_mvarId_652_);
v_a_811_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_818_ == 0)
{
v___x_813_ = v___x_708_;
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_708_);
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
lean_dec(v_numFields_692_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec(v_fvarId_654_);
lean_dec(v___x_653_);
lean_dec(v_mvarId_652_);
v_a_819_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_706_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_706_);
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
if (lean_obj_tag(v___y_836_) == 0)
{
lean_object* v_a_837_; lean_object* v___x_838_; 
v_a_837_ = lean_ctor_get(v___y_836_, 0);
lean_inc(v_a_837_);
lean_dec_ref_known(v___y_836_, 1);
lean_inc_ref(v___y_834_);
lean_inc(v___y_828_);
lean_inc_ref(v___y_830_);
lean_inc(v___y_835_);
lean_inc_ref(v___y_832_);
v___x_838_ = lean_apply_5(v___y_834_, v___y_832_, v___y_835_, v___y_830_, v___y_828_, lean_box(0));
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v_a_839_; uint8_t v___x_840_; 
v_a_839_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_a_839_);
lean_dec_ref_known(v___x_838_, 1);
v___x_840_ = lean_unbox(v_a_839_);
lean_dec(v_a_839_);
if (v___x_840_ == 0)
{
v___y_681_ = v_a_837_;
v___y_682_ = v___y_829_;
v___y_683_ = v___y_831_;
v___y_684_ = v___y_833_;
v___y_685_ = v___y_834_;
v___y_686_ = v___y_832_;
v___y_687_ = v___y_835_;
v___y_688_ = v___y_830_;
v___y_689_ = v___y_828_;
goto v___jp_680_;
}
else
{
lean_object* v___x_841_; 
lean_inc(v___y_828_);
lean_inc_ref(v___y_830_);
lean_inc(v___y_835_);
lean_inc_ref(v___y_832_);
lean_inc(v_a_837_);
v___x_841_ = lean_infer_type(v_a_837_, v___y_832_, v___y_835_, v___y_830_, v___y_828_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
lean_inc(v_a_842_);
lean_dec_ref_known(v___x_841_, 1);
v___x_843_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__15, &l_Lean_Meta_injectionCore___lam__1___closed__15_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__15);
lean_inc(v_a_837_);
v___x_844_ = l_Lean_indentExpr(v_a_837_);
v___x_845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_845_, 0, v___x_843_);
lean_ctor_set(v___x_845_, 1, v___x_844_);
v___x_846_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__17, &l_Lean_Meta_injectionCore___lam__1___closed__17_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__17);
v___x_847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_845_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
v___x_848_ = l_Lean_indentExpr(v_a_842_);
v___x_849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_847_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
lean_inc(v___y_831_);
v___x_850_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v___y_831_, v___x_849_, v___y_832_, v___y_835_, v___y_830_, v___y_828_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_dec_ref_known(v___x_850_, 1);
v___y_681_ = v_a_837_;
v___y_682_ = v___y_829_;
v___y_683_ = v___y_831_;
v___y_684_ = v___y_833_;
v___y_685_ = v___y_834_;
v___y_686_ = v___y_832_;
v___y_687_ = v___y_835_;
v___y_688_ = v___y_830_;
v___y_689_ = v___y_828_;
goto v___jp_680_;
}
else
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
lean_dec(v_a_837_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec(v_fvarId_654_);
lean_dec(v___x_653_);
lean_dec(v_mvarId_652_);
v_a_851_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_850_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_850_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_851_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
else
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_866_; 
lean_dec(v_a_837_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec(v_fvarId_654_);
lean_dec(v___x_653_);
lean_dec(v_mvarId_652_);
v_a_859_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_866_ == 0)
{
v___x_861_ = v___x_841_;
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_841_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_864_; 
if (v_isShared_862_ == 0)
{
v___x_864_ = v___x_861_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_a_859_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
}
else
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_874_; 
lean_dec(v_a_837_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec(v_fvarId_654_);
lean_dec(v___x_653_);
lean_dec(v_mvarId_652_);
v_a_867_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_874_ == 0)
{
v___x_869_ = v___x_838_;
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_838_);
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
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec(v_fvarId_654_);
lean_dec(v___x_653_);
lean_dec(v_mvarId_652_);
v_a_875_ = lean_ctor_get(v___y_836_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___y_836_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___y_836_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___y_836_);
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
v___jp_883_:
{
lean_object* v___x_894_; uint8_t v_transparency_895_; uint8_t v___x_896_; uint8_t v___x_897_; 
v___x_894_ = l_Lean_Meta_Context_config(v___y_890_);
v_transparency_895_ = lean_ctor_get_uint8(v___x_894_, 9);
lean_dec_ref(v___x_894_);
v___x_896_ = 1;
v___x_897_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_895_, v___x_896_);
if (v___x_897_ == 0)
{
lean_object* v_keyedConfig_898_; uint8_t v_trackZetaDelta_899_; lean_object* v_zetaDeltaSet_900_; lean_object* v_lctx_901_; lean_object* v_localInstances_902_; lean_object* v_defEqCtx_x3f_903_; lean_object* v_synthPendingDepth_904_; lean_object* v_customCanUnfoldPredicate_x3f_905_; uint8_t v_univApprox_906_; uint8_t v_inTypeClassResolution_907_; uint8_t v_cacheInferType_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v_keyedConfig_898_ = lean_ctor_get(v___y_890_, 0);
v_trackZetaDelta_899_ = lean_ctor_get_uint8(v___y_890_, sizeof(void*)*7);
v_zetaDeltaSet_900_ = lean_ctor_get(v___y_890_, 1);
v_lctx_901_ = lean_ctor_get(v___y_890_, 2);
v_localInstances_902_ = lean_ctor_get(v___y_890_, 3);
v_defEqCtx_x3f_903_ = lean_ctor_get(v___y_890_, 4);
v_synthPendingDepth_904_ = lean_ctor_get(v___y_890_, 5);
v_customCanUnfoldPredicate_x3f_905_ = lean_ctor_get(v___y_890_, 6);
v_univApprox_906_ = lean_ctor_get_uint8(v___y_890_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_907_ = lean_ctor_get_uint8(v___y_890_, sizeof(void*)*7 + 2);
v_cacheInferType_908_ = lean_ctor_get_uint8(v___y_890_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_898_);
v___x_909_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_896_, v_keyedConfig_898_);
lean_inc(v_customCanUnfoldPredicate_x3f_905_);
lean_inc(v_synthPendingDepth_904_);
lean_inc(v_defEqCtx_x3f_903_);
lean_inc_ref(v_localInstances_902_);
lean_inc_ref(v_lctx_901_);
lean_inc(v_zetaDeltaSet_900_);
v___x_910_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_910_, 0, v___x_909_);
lean_ctor_set(v___x_910_, 1, v_zetaDeltaSet_900_);
lean_ctor_set(v___x_910_, 2, v_lctx_901_);
lean_ctor_set(v___x_910_, 3, v_localInstances_902_);
lean_ctor_set(v___x_910_, 4, v_defEqCtx_x3f_903_);
lean_ctor_set(v___x_910_, 5, v_synthPendingDepth_904_);
lean_ctor_set(v___x_910_, 6, v_customCanUnfoldPredicate_x3f_905_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*7, v_trackZetaDelta_899_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*7 + 1, v_univApprox_906_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*7 + 2, v_inTypeClassResolution_907_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*7 + 3, v_cacheInferType_908_);
v___x_911_ = l_Lean_Meta_mkNoConfusion(v___y_885_, v___y_889_, v___x_910_, v___y_891_, v___y_892_, v___y_893_);
lean_dec_ref_known(v___x_910_, 7);
v___y_828_ = v___y_893_;
v___y_829_ = v___y_884_;
v___y_830_ = v___y_892_;
v___y_831_ = v___y_886_;
v___y_832_ = v___y_890_;
v___y_833_ = v___y_887_;
v___y_834_ = v___y_888_;
v___y_835_ = v___y_891_;
v___y_836_ = v___x_911_;
goto v___jp_827_;
}
else
{
lean_object* v___x_912_; 
v___x_912_ = l_Lean_Meta_mkNoConfusion(v___y_885_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
v___y_828_ = v___y_893_;
v___y_829_ = v___y_884_;
v___y_830_ = v___y_892_;
v___y_831_ = v___y_886_;
v___y_832_ = v___y_890_;
v___y_833_ = v___y_887_;
v___y_834_ = v___y_888_;
v___y_835_ = v___y_891_;
v___y_836_ = v___x_912_;
goto v___jp_827_;
}
}
v___jp_913_:
{
lean_object* v___x_920_; lean_object* v___x_921_; uint8_t v___x_922_; 
v___x_920_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__19));
v___x_921_ = lean_unsigned_to_nat(3u);
v___x_922_ = l_Lean_Expr_isAppOfArity(v_type_914_, v___x_920_, v___x_921_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; lean_object* v___x_924_; 
lean_dec_ref(v_prf_915_);
lean_dec_ref(v_type_914_);
lean_dec_ref(v___x_655_);
lean_dec(v_fvarId_654_);
v___x_923_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__23, &l_Lean_Meta_injectionCore___lam__1___closed__23_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__23);
v___x_924_ = l_Lean_Meta_throwTacticEx___redArg(v___x_653_, v_mvarId_652_, v___x_923_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
return v___x_924_;
}
else
{
lean_object* v___x_925_; 
lean_inc(v_mvarId_652_);
v___x_925_ = l_Lean_MVarId_getType(v_mvarId_652_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v_a_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v_a_926_ = lean_ctor_get(v___x_925_, 0);
lean_inc(v_a_926_);
lean_dec_ref_known(v___x_925_, 1);
v___x_927_ = l_Lean_Expr_appFn_x21(v_type_914_);
v___x_928_ = l_Lean_Expr_appArg_x21(v___x_927_);
lean_dec_ref(v___x_927_);
v___x_929_ = l_Lean_Meta_isConstructorApp_x27_x3f(v___x_928_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v_a_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v_a_930_ = lean_ctor_get(v___x_929_, 0);
lean_inc(v_a_930_);
lean_dec_ref_known(v___x_929_, 1);
v___x_931_ = l_Lean_Expr_appArg_x21(v_type_914_);
lean_dec_ref(v_type_914_);
v___x_932_ = l_Lean_Meta_isConstructorApp_x27_x3f(v___x_931_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
if (lean_obj_tag(v___x_932_) == 0)
{
if (lean_obj_tag(v_a_930_) == 1)
{
lean_object* v_a_933_; 
v_a_933_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_a_933_);
lean_dec_ref_known(v___x_932_, 1);
if (lean_obj_tag(v_a_933_) == 1)
{
lean_object* v_val_934_; lean_object* v_val_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___f_939_; lean_object* v___x_940_; lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_974_; 
v_val_934_ = lean_ctor_get(v_a_930_, 0);
lean_inc(v_val_934_);
lean_dec_ref_known(v_a_930_, 1);
v_val_935_ = lean_ctor_get(v_a_933_, 0);
lean_inc(v_val_935_);
lean_dec_ref_known(v_a_933_, 1);
v___x_936_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__24));
v___x_937_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__25));
v___x_938_ = l_Lean_Name_mkStr3(v___x_936_, v___x_937_, v___x_655_);
lean_inc_n(v___x_938_, 2);
v___f_939_ = lean_alloc_closure((void*)(l_Lean_Meta_injectionCore___lam__0___boxed), 6, 1);
lean_closure_set(v___f_939_, 0, v___x_938_);
v___x_940_ = l_Lean_Meta_injectionCore___lam__0(v___x_938_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
v_a_941_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_974_ == 0)
{
v___x_943_ = v___x_940_;
v_isShared_944_ = v_isSharedCheck_974_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_940_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_974_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
uint8_t v___x_945_; 
v___x_945_ = lean_unbox(v_a_941_);
lean_dec(v_a_941_);
if (v___x_945_ == 0)
{
lean_del_object(v___x_943_);
v___y_884_ = v_val_934_;
v___y_885_ = v_a_926_;
v___y_886_ = v___x_938_;
v___y_887_ = v_val_935_;
v___y_888_ = v___f_939_;
v___y_889_ = v_prf_915_;
v___y_890_ = v___y_916_;
v___y_891_ = v___y_917_;
v___y_892_ = v___y_918_;
v___y_893_ = v___y_919_;
goto v___jp_883_;
}
else
{
lean_object* v___x_946_; 
lean_inc(v___y_919_);
lean_inc_ref(v___y_918_);
lean_inc(v___y_917_);
lean_inc_ref(v___y_916_);
lean_inc_ref(v_prf_915_);
v___x_946_ = lean_infer_type(v_prf_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_a_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_954_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc(v_a_947_);
lean_dec_ref_known(v___x_946_, 1);
v___x_948_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__27, &l_Lean_Meta_injectionCore___lam__1___closed__27_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__27);
v___x_949_ = l_Lean_MessageData_ofExpr(v_a_947_);
v___x_950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_948_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___x_951_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__29, &l_Lean_Meta_injectionCore___lam__1___closed__29_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__29);
v___x_952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_950_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
lean_inc(v_mvarId_652_);
if (v_isShared_944_ == 0)
{
lean_ctor_set_tag(v___x_943_, 1);
lean_ctor_set(v___x_943_, 0, v_mvarId_652_);
v___x_954_ = v___x_943_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_mvarId_652_);
v___x_954_ = v_reuseFailAlloc_965_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_952_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
lean_inc(v___x_938_);
v___x_956_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v___x_938_, v___x_955_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_dec_ref_known(v___x_956_, 1);
v___y_884_ = v_val_934_;
v___y_885_ = v_a_926_;
v___y_886_ = v___x_938_;
v___y_887_ = v_val_935_;
v___y_888_ = v___f_939_;
v___y_889_ = v_prf_915_;
v___y_890_ = v___y_916_;
v___y_891_ = v___y_917_;
v___y_892_ = v___y_918_;
v___y_893_ = v___y_919_;
goto v___jp_883_;
}
else
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
lean_dec_ref(v___f_939_);
lean_dec(v___x_938_);
lean_dec(v_val_935_);
lean_dec(v_val_934_);
lean_dec(v_a_926_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec_ref(v_prf_915_);
lean_dec(v_fvarId_654_);
lean_dec(v___x_653_);
lean_dec(v_mvarId_652_);
v_a_957_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_964_ == 0)
{
v___x_959_ = v___x_956_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_957_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
}
else
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
lean_del_object(v___x_943_);
lean_dec_ref(v___f_939_);
lean_dec(v___x_938_);
lean_dec(v_val_935_);
lean_dec(v_val_934_);
lean_dec(v_a_926_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec_ref(v_prf_915_);
lean_dec(v_fvarId_654_);
lean_dec(v___x_653_);
lean_dec(v_mvarId_652_);
v_a_966_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_973_ == 0)
{
v___x_968_ = v___x_946_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_946_);
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
else
{
lean_dec_ref_known(v_a_930_, 1);
lean_dec(v_a_933_);
lean_dec(v_a_926_);
lean_dec_ref(v_prf_915_);
lean_dec_ref(v___x_655_);
lean_dec(v_fvarId_654_);
v___y_669_ = v___y_916_;
v___y_670_ = v___y_917_;
v___y_671_ = v___y_918_;
v___y_672_ = v___y_919_;
goto v___jp_668_;
}
}
else
{
lean_dec_ref_known(v___x_932_, 1);
lean_dec(v_a_930_);
lean_dec(v_a_926_);
lean_dec_ref(v_prf_915_);
lean_dec_ref(v___x_655_);
lean_dec(v_fvarId_654_);
v___y_669_ = v___y_916_;
v___y_670_ = v___y_917_;
v___y_671_ = v___y_918_;
v___y_672_ = v___y_919_;
goto v___jp_668_;
}
}
else
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
lean_dec(v_a_930_);
lean_dec(v_a_926_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec_ref(v_prf_915_);
lean_dec_ref(v___x_655_);
lean_dec(v_fvarId_654_);
lean_dec(v___x_653_);
lean_dec(v_mvarId_652_);
v_a_975_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___x_932_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_932_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_975_);
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
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
lean_dec(v_a_926_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec_ref(v_prf_915_);
lean_dec_ref(v_type_914_);
lean_dec_ref(v___x_655_);
lean_dec(v_fvarId_654_);
lean_dec(v___x_653_);
lean_dec(v_mvarId_652_);
v_a_983_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_929_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_929_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_986_ == 0)
{
v___x_988_ = v___x_985_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_983_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec_ref(v_prf_915_);
lean_dec_ref(v_type_914_);
lean_dec_ref(v___x_655_);
lean_dec(v_fvarId_654_);
lean_dec(v___x_653_);
lean_dec(v_mvarId_652_);
v_a_991_ = lean_ctor_get(v___x_925_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_925_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_925_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___lam__1___boxed(lean_object* v_mvarId_1071_, lean_object* v___x_1072_, lean_object* v_fvarId_1073_, lean_object* v___x_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Lean_Meta_injectionCore___lam__1(v_mvarId_1071_, v___x_1072_, v_fvarId_1073_, v___x_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore(lean_object* v_mvarId_1084_, lean_object* v_fvarId_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___f_1093_; lean_object* v___x_1094_; 
v___x_1091_ = ((lean_object*)(l_Lean_Meta_injectionCore___closed__0));
v___x_1092_ = ((lean_object*)(l_Lean_Meta_injectionCore___closed__1));
lean_inc(v_mvarId_1084_);
v___f_1093_ = lean_alloc_closure((void*)(l_Lean_Meta_injectionCore___lam__1___boxed), 9, 4);
lean_closure_set(v___f_1093_, 0, v_mvarId_1084_);
lean_closure_set(v___f_1093_, 1, v___x_1092_);
lean_closure_set(v___f_1093_, 2, v_fvarId_1085_);
lean_closure_set(v___f_1093_, 3, v___x_1091_);
v___x_1094_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg(v_mvarId_1084_, v___f_1093_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___boxed(lean_object* v_mvarId_1095_, lean_object* v_fvarId_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Lean_Meta_injectionCore(v_mvarId_1095_, v_fvarId_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
lean_dec(v_a_1100_);
lean_dec_ref(v_a_1099_);
lean_dec(v_a_1098_);
lean_dec_ref(v_a_1097_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0(lean_object* v_mvarId_1103_, lean_object* v_val_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v___x_1110_; 
v___x_1110_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(v_mvarId_1103_, v_val_1104_, v___y_1106_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___boxed(lean_object* v_mvarId_1111_, lean_object* v_val_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0(v_mvarId_1111_, v_val_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0(lean_object* v_00_u03b2_1119_, lean_object* v_x_1120_, lean_object* v_x_1121_, lean_object* v_x_1122_){
_start:
{
lean_object* v___x_1123_; 
v___x_1123_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0___redArg(v_x_1120_, v_x_1121_, v_x_1122_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1124_, lean_object* v_x_1125_, size_t v_x_1126_, size_t v_x_1127_, lean_object* v_x_1128_, lean_object* v_x_1129_){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(v_x_1125_, v_x_1126_, v_x_1127_, v_x_1128_, v_x_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1131_, lean_object* v_x_1132_, lean_object* v_x_1133_, lean_object* v_x_1134_, lean_object* v_x_1135_, lean_object* v_x_1136_){
_start:
{
size_t v_x_15639__boxed_1137_; size_t v_x_15640__boxed_1138_; lean_object* v_res_1139_; 
v_x_15639__boxed_1137_ = lean_unbox_usize(v_x_1133_);
lean_dec(v_x_1133_);
v_x_15640__boxed_1138_ = lean_unbox_usize(v_x_1134_);
lean_dec(v_x_1134_);
v_res_1139_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2(v_00_u03b2_1131_, v_x_1132_, v_x_15639__boxed_1137_, v_x_15640__boxed_1138_, v_x_1135_, v_x_1136_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1140_, lean_object* v_n_1141_, lean_object* v_k_1142_, lean_object* v_v_1143_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5___redArg(v_n_1141_, v_k_1142_, v_v_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_1145_, size_t v_depth_1146_, lean_object* v_keys_1147_, lean_object* v_vals_1148_, lean_object* v_heq_1149_, lean_object* v_i_1150_, lean_object* v_entries_1151_){
_start:
{
lean_object* v___x_1152_; 
v___x_1152_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___redArg(v_depth_1146_, v_keys_1147_, v_vals_1148_, v_i_1150_, v_entries_1151_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1153_, lean_object* v_depth_1154_, lean_object* v_keys_1155_, lean_object* v_vals_1156_, lean_object* v_heq_1157_, lean_object* v_i_1158_, lean_object* v_entries_1159_){
_start:
{
size_t v_depth_boxed_1160_; lean_object* v_res_1161_; 
v_depth_boxed_1160_ = lean_unbox_usize(v_depth_1154_);
lean_dec(v_depth_1154_);
v_res_1161_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6(v_00_u03b2_1153_, v_depth_boxed_1160_, v_keys_1155_, v_vals_1156_, v_heq_1157_, v_i_1158_, v_entries_1159_);
lean_dec_ref(v_vals_1156_);
lean_dec_ref(v_keys_1155_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5_spec__6(lean_object* v_00_u03b2_1162_, lean_object* v_x_1163_, lean_object* v_x_1164_, lean_object* v_x_1165_, lean_object* v_x_1166_){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(v_x_1163_, v_x_1164_, v_x_1165_, v_x_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorIdx(lean_object* v_x_1168_){
_start:
{
if (lean_obj_tag(v_x_1168_) == 0)
{
lean_object* v___x_1169_; 
v___x_1169_ = lean_unsigned_to_nat(0u);
return v___x_1169_;
}
else
{
lean_object* v___x_1170_; 
v___x_1170_ = lean_unsigned_to_nat(1u);
return v___x_1170_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorIdx___boxed(lean_object* v_x_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Lean_Meta_InjectionResult_ctorIdx(v_x_1171_);
lean_dec(v_x_1171_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorElim___redArg(lean_object* v_t_1173_, lean_object* v_k_1174_){
_start:
{
if (lean_obj_tag(v_t_1173_) == 0)
{
return v_k_1174_;
}
else
{
lean_object* v_mvarId_1175_; lean_object* v_newEqs_1176_; lean_object* v_remainingNames_1177_; lean_object* v___x_1178_; 
v_mvarId_1175_ = lean_ctor_get(v_t_1173_, 0);
lean_inc(v_mvarId_1175_);
v_newEqs_1176_ = lean_ctor_get(v_t_1173_, 1);
lean_inc_ref(v_newEqs_1176_);
v_remainingNames_1177_ = lean_ctor_get(v_t_1173_, 2);
lean_inc(v_remainingNames_1177_);
lean_dec_ref_known(v_t_1173_, 3);
v___x_1178_ = lean_apply_3(v_k_1174_, v_mvarId_1175_, v_newEqs_1176_, v_remainingNames_1177_);
return v___x_1178_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorElim(lean_object* v_motive_1179_, lean_object* v_ctorIdx_1180_, lean_object* v_t_1181_, lean_object* v_h_1182_, lean_object* v_k_1183_){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_1181_, v_k_1183_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorElim___boxed(lean_object* v_motive_1185_, lean_object* v_ctorIdx_1186_, lean_object* v_t_1187_, lean_object* v_h_1188_, lean_object* v_k_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Lean_Meta_InjectionResult_ctorElim(v_motive_1185_, v_ctorIdx_1186_, v_t_1187_, v_h_1188_, v_k_1189_);
lean_dec(v_ctorIdx_1186_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_solved_elim___redArg(lean_object* v_t_1191_, lean_object* v_solved_1192_){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_1191_, v_solved_1192_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_solved_elim(lean_object* v_motive_1194_, lean_object* v_t_1195_, lean_object* v_h_1196_, lean_object* v_solved_1197_){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_1195_, v_solved_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_subgoal_elim___redArg(lean_object* v_t_1199_, lean_object* v_subgoal_1200_){
_start:
{
lean_object* v___x_1201_; 
v___x_1201_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_1199_, v_subgoal_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_subgoal_elim(lean_object* v_motive_1202_, lean_object* v_t_1203_, lean_object* v_h_1204_, lean_object* v_subgoal_1205_){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_1203_, v_subgoal_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go(uint8_t v_tryToClear_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_){
_start:
{
lean_object* v_zero_1217_; uint8_t v_isZero_1218_; 
v_zero_1217_ = lean_unsigned_to_nat(0u);
v_isZero_1218_ = lean_nat_dec_eq(v_a_1208_, v_zero_1217_);
if (v_isZero_1218_ == 1)
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
lean_dec(v_a_1208_);
v___x_1219_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1219_, 0, v_a_1209_);
lean_ctor_set(v___x_1219_, 1, v_a_1210_);
lean_ctor_set(v___x_1219_, 2, v_a_1211_);
v___x_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
return v___x_1220_;
}
else
{
lean_object* v_one_1221_; lean_object* v_n_1222_; 
v_one_1221_ = lean_unsigned_to_nat(1u);
v_n_1222_ = lean_nat_sub(v_a_1208_, v_one_1221_);
lean_dec(v_a_1208_);
if (lean_obj_tag(v_a_1211_) == 0)
{
lean_object* v___x_1223_; 
v___x_1223_ = l_Lean_Meta_intro1Core(v_a_1209_, v_isZero_1218_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_);
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_object* v_a_1224_; lean_object* v_fst_1225_; lean_object* v_snd_1226_; lean_object* v___x_1227_; 
v_a_1224_ = lean_ctor_get(v___x_1223_, 0);
lean_inc(v_a_1224_);
lean_dec_ref_known(v___x_1223_, 1);
v_fst_1225_ = lean_ctor_get(v_a_1224_, 0);
lean_inc(v_fst_1225_);
v_snd_1226_ = lean_ctor_get(v_a_1224_, 1);
lean_inc(v_snd_1226_);
lean_dec(v_a_1224_);
v___x_1227_ = l_Lean_Meta_heqToEq(v_snd_1226_, v_fst_1225_, v_tryToClear_1207_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v_a_1228_; lean_object* v_fst_1229_; lean_object* v_snd_1230_; lean_object* v___x_1231_; 
v_a_1228_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_a_1228_);
lean_dec_ref_known(v___x_1227_, 1);
v_fst_1229_ = lean_ctor_get(v_a_1228_, 0);
lean_inc(v_fst_1229_);
v_snd_1230_ = lean_ctor_get(v_a_1228_, 1);
lean_inc(v_snd_1230_);
lean_dec(v_a_1228_);
v___x_1231_ = lean_array_push(v_a_1210_, v_fst_1229_);
v_a_1208_ = v_n_1222_;
v_a_1209_ = v_snd_1230_;
v_a_1210_ = v___x_1231_;
goto _start;
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
lean_dec(v_n_1222_);
lean_dec_ref(v_a_1210_);
v_a_1233_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1227_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1227_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1233_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
else
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
lean_dec(v_n_1222_);
lean_dec_ref(v_a_1210_);
v_a_1241_ = lean_ctor_get(v___x_1223_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1243_ = v___x_1223_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1223_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_a_1241_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
else
{
lean_object* v_head_1249_; lean_object* v_tail_1250_; lean_object* v___x_1251_; 
v_head_1249_ = lean_ctor_get(v_a_1211_, 0);
lean_inc(v_head_1249_);
v_tail_1250_ = lean_ctor_get(v_a_1211_, 1);
lean_inc(v_tail_1250_);
lean_dec_ref_known(v_a_1211_, 2);
v___x_1251_ = l_Lean_MVarId_intro(v_a_1209_, v_head_1249_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v_a_1252_; lean_object* v_fst_1253_; lean_object* v_snd_1254_; lean_object* v___x_1255_; 
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_a_1252_);
lean_dec_ref_known(v___x_1251_, 1);
v_fst_1253_ = lean_ctor_get(v_a_1252_, 0);
lean_inc(v_fst_1253_);
v_snd_1254_ = lean_ctor_get(v_a_1252_, 1);
lean_inc(v_snd_1254_);
lean_dec(v_a_1252_);
v___x_1255_ = l_Lean_Meta_heqToEq(v_snd_1254_, v_fst_1253_, v_tryToClear_1207_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v_a_1256_; lean_object* v_fst_1257_; lean_object* v_snd_1258_; lean_object* v___x_1259_; 
v_a_1256_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_a_1256_);
lean_dec_ref_known(v___x_1255_, 1);
v_fst_1257_ = lean_ctor_get(v_a_1256_, 0);
lean_inc(v_fst_1257_);
v_snd_1258_ = lean_ctor_get(v_a_1256_, 1);
lean_inc(v_snd_1258_);
lean_dec(v_a_1256_);
v___x_1259_ = lean_array_push(v_a_1210_, v_fst_1257_);
v_a_1208_ = v_n_1222_;
v_a_1209_ = v_snd_1258_;
v_a_1210_ = v___x_1259_;
v_a_1211_ = v_tail_1250_;
goto _start;
}
else
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1268_; 
lean_dec(v_tail_1250_);
lean_dec(v_n_1222_);
lean_dec_ref(v_a_1210_);
v_a_1261_ = lean_ctor_get(v___x_1255_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1263_ = v___x_1255_;
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1255_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_a_1261_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
else
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
lean_dec(v_tail_1250_);
lean_dec(v_n_1222_);
lean_dec_ref(v_a_1210_);
v_a_1269_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v___x_1251_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1251_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1272_ == 0)
{
v___x_1274_ = v___x_1271_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_a_1269_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go___boxed(lean_object* v_tryToClear_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_){
_start:
{
uint8_t v_tryToClear_boxed_1287_; lean_object* v_res_1288_; 
v_tryToClear_boxed_1287_ = lean_unbox(v_tryToClear_1277_);
v_res_1288_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go(v_tryToClear_boxed_1287_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_);
lean_dec(v_a_1285_);
lean_dec_ref(v_a_1284_);
lean_dec(v_a_1283_);
lean_dec_ref(v_a_1282_);
return v_res_1288_;
}
}
static lean_object* _init_l_Lean_Meta_injectionIntro___closed__2(void){
_start:
{
lean_object* v_cls_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v_cls_1295_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__1));
v___x_1296_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__0___closed__1));
v___x_1297_ = l_Lean_Name_append(v___x_1296_, v_cls_1295_);
return v___x_1297_;
}
}
static lean_object* _init_l_Lean_Meta_injectionIntro___closed__4(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__3));
v___x_1300_ = l_Lean_stringToMessageData(v___x_1299_);
return v___x_1300_;
}
}
static lean_object* _init_l_Lean_Meta_injectionIntro___closed__6(void){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__5));
v___x_1303_ = l_Lean_stringToMessageData(v___x_1302_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro(lean_object* v_mvarId_1304_, lean_object* v_numEqs_1305_, lean_object* v_newNames_1306_, uint8_t v_tryToClear_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_){
_start:
{
lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v_options_1320_; uint8_t v_hasTrace_1321_; 
v_options_1320_ = lean_ctor_get(v_a_1310_, 1);
v_hasTrace_1321_ = lean_ctor_get_uint8(v_options_1320_, sizeof(void*)*1);
if (v_hasTrace_1321_ == 0)
{
v___y_1314_ = v_a_1308_;
v___y_1315_ = v_a_1309_;
v___y_1316_ = v_a_1310_;
v___y_1317_ = v_a_1311_;
goto v___jp_1313_;
}
else
{
lean_object* v_toCold_1322_; lean_object* v_inheritedTraceOptions_1323_; lean_object* v_cls_1324_; lean_object* v___x_1325_; uint8_t v___x_1326_; 
v_toCold_1322_ = lean_ctor_get(v_a_1310_, 0);
v_inheritedTraceOptions_1323_ = lean_ctor_get(v_toCold_1322_, 4);
v_cls_1324_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__1));
v___x_1325_ = lean_obj_once(&l_Lean_Meta_injectionIntro___closed__2, &l_Lean_Meta_injectionIntro___closed__2_once, _init_l_Lean_Meta_injectionIntro___closed__2);
v___x_1326_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1323_, v_options_1320_, v___x_1325_);
if (v___x_1326_ == 0)
{
v___y_1314_ = v_a_1308_;
v___y_1315_ = v_a_1309_;
v___y_1316_ = v_a_1310_;
v___y_1317_ = v_a_1311_;
goto v___jp_1313_;
}
else
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1327_ = lean_obj_once(&l_Lean_Meta_injectionIntro___closed__4, &l_Lean_Meta_injectionIntro___closed__4_once, _init_l_Lean_Meta_injectionIntro___closed__4);
lean_inc(v_numEqs_1305_);
v___x_1328_ = l_Nat_reprFast(v_numEqs_1305_);
v___x_1329_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1328_);
v___x_1330_ = l_Lean_MessageData_ofFormat(v___x_1329_);
v___x_1331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1327_);
lean_ctor_set(v___x_1331_, 1, v___x_1330_);
v___x_1332_ = lean_obj_once(&l_Lean_Meta_injectionIntro___closed__6, &l_Lean_Meta_injectionIntro___closed__6_once, _init_l_Lean_Meta_injectionIntro___closed__6);
v___x_1333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1331_);
lean_ctor_set(v___x_1333_, 1, v___x_1332_);
lean_inc(v_mvarId_1304_);
v___x_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1334_, 0, v_mvarId_1304_);
v___x_1335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1333_);
lean_ctor_set(v___x_1335_, 1, v___x_1334_);
v___x_1336_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v_cls_1324_, v___x_1335_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_dec_ref_known(v___x_1336_, 1);
v___y_1314_ = v_a_1308_;
v___y_1315_ = v_a_1309_;
v___y_1316_ = v_a_1310_;
v___y_1317_ = v_a_1311_;
goto v___jp_1313_;
}
else
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1344_; 
lean_dec(v_newNames_1306_);
lean_dec(v_numEqs_1305_);
lean_dec(v_mvarId_1304_);
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1339_ = v___x_1336_;
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1336_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1342_; 
if (v_isShared_1340_ == 0)
{
v___x_1342_ = v___x_1339_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_a_1337_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
}
v___jp_1313_:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__0));
v___x_1319_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go(v_tryToClear_1307_, v_numEqs_1305_, v_mvarId_1304_, v___x_1318_, v_newNames_1306_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
return v___x_1319_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro___boxed(lean_object* v_mvarId_1345_, lean_object* v_numEqs_1346_, lean_object* v_newNames_1347_, lean_object* v_tryToClear_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_){
_start:
{
uint8_t v_tryToClear_boxed_1354_; lean_object* v_res_1355_; 
v_tryToClear_boxed_1354_ = lean_unbox(v_tryToClear_1348_);
v_res_1355_ = l_Lean_Meta_injectionIntro(v_mvarId_1345_, v_numEqs_1346_, v_newNames_1347_, v_tryToClear_boxed_1354_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
lean_dec(v_a_1352_);
lean_dec_ref(v_a_1351_);
lean_dec(v_a_1350_);
lean_dec_ref(v_a_1349_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injection(lean_object* v_mvarId_1356_, lean_object* v_fvarId_1357_, lean_object* v_newNames_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_){
_start:
{
lean_object* v___x_1364_; 
v___x_1364_ = l_Lean_Meta_injectionCore(v_mvarId_1356_, v_fvarId_1357_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1377_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1367_ = v___x_1364_;
v_isShared_1368_ = v_isSharedCheck_1377_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1364_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1377_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
if (lean_obj_tag(v_a_1365_) == 0)
{
lean_object* v___x_1369_; lean_object* v___x_1371_; 
lean_dec(v_newNames_1358_);
v___x_1369_ = lean_box(0);
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 0, v___x_1369_);
v___x_1371_ = v___x_1367_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1369_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
else
{
lean_object* v_mvarId_1373_; lean_object* v_numNewEqs_1374_; uint8_t v___x_1375_; lean_object* v___x_1376_; 
lean_del_object(v___x_1367_);
v_mvarId_1373_ = lean_ctor_get(v_a_1365_, 0);
lean_inc(v_mvarId_1373_);
v_numNewEqs_1374_ = lean_ctor_get(v_a_1365_, 1);
lean_inc(v_numNewEqs_1374_);
lean_dec_ref_known(v_a_1365_, 2);
v___x_1375_ = 1;
v___x_1376_ = l_Lean_Meta_injectionIntro(v_mvarId_1373_, v_numNewEqs_1374_, v_newNames_1358_, v___x_1375_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
return v___x_1376_;
}
}
}
else
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1385_; 
lean_dec(v_newNames_1358_);
v_a_1378_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1380_ = v___x_1364_;
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1364_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1383_; 
if (v_isShared_1381_ == 0)
{
v___x_1383_ = v___x_1380_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_a_1378_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injection___boxed(lean_object* v_mvarId_1386_, lean_object* v_fvarId_1387_, lean_object* v_newNames_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l_Lean_Meta_injection(v_mvarId_1386_, v_fvarId_1387_, v_newNames_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_);
lean_dec(v_a_1392_);
lean_dec_ref(v_a_1391_);
lean_dec(v_a_1390_);
lean_dec_ref(v_a_1389_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorIdx(lean_object* v_x_1395_){
_start:
{
if (lean_obj_tag(v_x_1395_) == 0)
{
lean_object* v___x_1396_; 
v___x_1396_ = lean_unsigned_to_nat(0u);
return v___x_1396_;
}
else
{
lean_object* v___x_1397_; 
v___x_1397_ = lean_unsigned_to_nat(1u);
return v___x_1397_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorIdx___boxed(lean_object* v_x_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Lean_Meta_InjectionsResult_ctorIdx(v_x_1398_);
lean_dec(v_x_1398_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorElim___redArg(lean_object* v_t_1400_, lean_object* v_k_1401_){
_start:
{
if (lean_obj_tag(v_t_1400_) == 0)
{
return v_k_1401_;
}
else
{
lean_object* v_mvarId_1402_; lean_object* v_remainingNames_1403_; lean_object* v_forbidden_1404_; lean_object* v___x_1405_; 
v_mvarId_1402_ = lean_ctor_get(v_t_1400_, 0);
lean_inc(v_mvarId_1402_);
v_remainingNames_1403_ = lean_ctor_get(v_t_1400_, 1);
lean_inc(v_remainingNames_1403_);
v_forbidden_1404_ = lean_ctor_get(v_t_1400_, 2);
lean_inc(v_forbidden_1404_);
lean_dec_ref_known(v_t_1400_, 3);
v___x_1405_ = lean_apply_3(v_k_1401_, v_mvarId_1402_, v_remainingNames_1403_, v_forbidden_1404_);
return v___x_1405_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorElim(lean_object* v_motive_1406_, lean_object* v_ctorIdx_1407_, lean_object* v_t_1408_, lean_object* v_h_1409_, lean_object* v_k_1410_){
_start:
{
lean_object* v___x_1411_; 
v___x_1411_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1408_, v_k_1410_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorElim___boxed(lean_object* v_motive_1412_, lean_object* v_ctorIdx_1413_, lean_object* v_t_1414_, lean_object* v_h_1415_, lean_object* v_k_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_Lean_Meta_InjectionsResult_ctorElim(v_motive_1412_, v_ctorIdx_1413_, v_t_1414_, v_h_1415_, v_k_1416_);
lean_dec(v_ctorIdx_1413_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_solved_elim___redArg(lean_object* v_t_1418_, lean_object* v_solved_1419_){
_start:
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1418_, v_solved_1419_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_solved_elim(lean_object* v_motive_1421_, lean_object* v_t_1422_, lean_object* v_h_1423_, lean_object* v_solved_1424_){
_start:
{
lean_object* v___x_1425_; 
v___x_1425_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1422_, v_solved_1424_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_subgoal_elim___redArg(lean_object* v_t_1426_, lean_object* v_subgoal_1427_){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1426_, v_subgoal_1427_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_subgoal_elim(lean_object* v_motive_1429_, lean_object* v_t_1430_, lean_object* v_h_1431_, lean_object* v_subgoal_1432_){
_start:
{
lean_object* v___x_1433_; 
v___x_1433_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1430_, v_subgoal_1432_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(lean_object* v_x_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = l_Lean_Meta_saveState___redArg(v___y_1436_, v___y_1438_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v_a_1441_; lean_object* v___x_1442_; 
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_a_1441_);
lean_dec_ref_known(v___x_1440_, 1);
lean_inc(v___y_1438_);
lean_inc_ref(v___y_1437_);
lean_inc(v___y_1436_);
lean_inc_ref(v___y_1435_);
v___x_1442_ = lean_apply_5(v_x_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, lean_box(0));
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_dec(v_a_1441_);
return v___x_1442_;
}
else
{
lean_object* v_a_1443_; uint8_t v___y_1445_; uint8_t v___x_1463_; 
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
lean_inc(v_a_1443_);
v___x_1463_ = l_Lean_Exception_isInterrupt(v_a_1443_);
if (v___x_1463_ == 0)
{
uint8_t v___x_1464_; 
lean_inc(v_a_1443_);
v___x_1464_ = l_Lean_Exception_isRuntime(v_a_1443_);
v___y_1445_ = v___x_1464_;
goto v___jp_1444_;
}
else
{
v___y_1445_ = v___x_1463_;
goto v___jp_1444_;
}
v___jp_1444_:
{
if (v___y_1445_ == 0)
{
lean_object* v___x_1446_; 
lean_dec_ref_known(v___x_1442_, 1);
v___x_1446_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1441_, v___y_1436_, v___y_1438_);
lean_dec(v_a_1441_);
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1453_ == 0)
{
lean_object* v_unused_1454_; 
v_unused_1454_ = lean_ctor_get(v___x_1446_, 0);
lean_dec(v_unused_1454_);
v___x_1448_ = v___x_1446_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_dec(v___x_1446_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
lean_ctor_set_tag(v___x_1448_, 1);
lean_ctor_set(v___x_1448_, 0, v_a_1443_);
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_a_1443_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
else
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1462_; 
lean_dec(v_a_1443_);
v_a_1455_ = lean_ctor_get(v___x_1446_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1457_ = v___x_1446_;
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1446_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1460_; 
if (v_isShared_1458_ == 0)
{
v___x_1460_ = v___x_1457_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_a_1455_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
else
{
lean_dec(v_a_1443_);
lean_dec(v_a_1441_);
return v___x_1442_;
}
}
}
}
else
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1472_; 
lean_dec_ref(v_x_1434_);
v_a_1465_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1467_ = v___x_1440_;
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1440_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1468_ == 0)
{
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1465_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg___boxed(lean_object* v_x_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(v_x_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1(lean_object* v_00_u03b1_1480_, lean_object* v_x_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v___x_1487_; 
v___x_1487_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(v_x_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___boxed(lean_object* v_00_u03b1_1488_, lean_object* v_x_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1(v_00_u03b1_1488_, v_x_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
return v_res_1495_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(lean_object* v_k_1496_, lean_object* v_t_1497_){
_start:
{
if (lean_obj_tag(v_t_1497_) == 0)
{
lean_object* v_k_1498_; lean_object* v_l_1499_; lean_object* v_r_1500_; uint8_t v___x_1501_; 
v_k_1498_ = lean_ctor_get(v_t_1497_, 1);
v_l_1499_ = lean_ctor_get(v_t_1497_, 3);
v_r_1500_ = lean_ctor_get(v_t_1497_, 4);
v___x_1501_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1496_, v_k_1498_);
switch(v___x_1501_)
{
case 0:
{
v_t_1497_ = v_l_1499_;
goto _start;
}
case 1:
{
uint8_t v___x_1503_; 
v___x_1503_ = 1;
return v___x_1503_;
}
default: 
{
v_t_1497_ = v_r_1500_;
goto _start;
}
}
}
else
{
uint8_t v___x_1505_; 
v___x_1505_ = 0;
return v___x_1505_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg___boxed(lean_object* v_k_1506_, lean_object* v_t_1507_){
_start:
{
uint8_t v_res_1508_; lean_object* v_r_1509_; 
v_res_1508_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(v_k_1506_, v_t_1507_);
lean_dec(v_t_1507_);
lean_dec(v_k_1506_);
v_r_1509_ = lean_box(v_res_1508_);
return v_r_1509_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4(void){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1516_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__3));
v___x_1517_ = l_Lean_MessageData_ofFormat(v___x_1516_);
return v___x_1517_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5(void){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1518_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4, &l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4_once, _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4);
v___x_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1518_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0___boxed(lean_object* v_mvarId_1520_, lean_object* v_head_1521_, lean_object* v_newNames_1522_, lean_object* v_tail_1523_, lean_object* v_forbidden_1524_, lean_object* v_n_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0(v_mvarId_1520_, v_head_1521_, v_newNames_1522_, v_tail_1523_, v_forbidden_1524_, v_n_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go(lean_object* v_depth_1532_, lean_object* v_fvarIds_1533_, lean_object* v_mvarId_1534_, lean_object* v_newNames_1535_, lean_object* v_forbidden_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_){
_start:
{
lean_object* v_zero_1542_; uint8_t v_isZero_1543_; 
v_zero_1542_ = lean_unsigned_to_nat(0u);
v_isZero_1543_ = lean_nat_dec_eq(v_depth_1532_, v_zero_1542_);
if (v_isZero_1543_ == 1)
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
lean_dec(v_forbidden_1536_);
lean_dec(v_newNames_1535_);
lean_dec(v_fvarIds_1533_);
lean_dec(v_depth_1532_);
v___x_1544_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__1));
v___x_1545_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5, &l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5_once, _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5);
v___x_1546_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1544_, v_mvarId_1534_, v___x_1545_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_);
return v___x_1546_;
}
else
{
if (lean_obj_tag(v_fvarIds_1533_) == 0)
{
lean_object* v___x_1547_; lean_object* v___x_1548_; 
lean_dec(v_depth_1532_);
v___x_1547_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1547_, 0, v_mvarId_1534_);
lean_ctor_set(v___x_1547_, 1, v_newNames_1535_);
lean_ctor_set(v___x_1547_, 2, v_forbidden_1536_);
v___x_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1547_);
return v___x_1548_;
}
else
{
lean_object* v_head_1549_; lean_object* v_tail_1550_; lean_object* v_one_1551_; lean_object* v_n_1552_; lean_object* v___x_1553_; lean_object* v___y_1555_; uint8_t v___y_1556_; uint8_t v___x_1558_; 
v_head_1549_ = lean_ctor_get(v_fvarIds_1533_, 0);
lean_inc(v_head_1549_);
v_tail_1550_ = lean_ctor_get(v_fvarIds_1533_, 1);
lean_inc(v_tail_1550_);
lean_dec_ref_known(v_fvarIds_1533_, 2);
v_one_1551_ = lean_unsigned_to_nat(1u);
v_n_1552_ = lean_nat_sub(v_depth_1532_, v_one_1551_);
lean_dec(v_depth_1532_);
v___x_1553_ = lean_nat_add(v_n_1552_, v_one_1551_);
v___x_1558_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(v_head_1549_, v_forbidden_1536_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1559_; 
lean_inc(v_head_1549_);
v___x_1559_ = l_Lean_FVarId_getType___redArg(v_head_1549_, v_a_1537_, v_a_1539_, v_a_1540_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v_a_1560_; lean_object* v___x_1561_; 
v_a_1560_ = lean_ctor_get(v___x_1559_, 0);
lean_inc(v_a_1560_);
lean_dec_ref_known(v___x_1559_, 1);
v___x_1561_ = l_Lean_Meta_matchEqHEq_x3f(v_a_1560_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; 
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
lean_inc(v_a_1562_);
lean_dec_ref_known(v___x_1561_, 1);
if (lean_obj_tag(v_a_1562_) == 1)
{
lean_object* v_val_1563_; lean_object* v_snd_1564_; lean_object* v_fst_1565_; lean_object* v_snd_1566_; lean_object* v___x_1567_; 
v_val_1563_ = lean_ctor_get(v_a_1562_, 0);
lean_inc(v_val_1563_);
lean_dec_ref_known(v_a_1562_, 1);
v_snd_1564_ = lean_ctor_get(v_val_1563_, 1);
lean_inc(v_snd_1564_);
lean_dec(v_val_1563_);
v_fst_1565_ = lean_ctor_get(v_snd_1564_, 0);
lean_inc(v_fst_1565_);
v_snd_1566_ = lean_ctor_get(v_snd_1564_, 1);
lean_inc(v_snd_1566_);
lean_dec(v_snd_1564_);
lean_inc(v_a_1540_);
lean_inc_ref(v_a_1539_);
lean_inc(v_a_1538_);
lean_inc_ref(v_a_1537_);
v___x_1567_ = lean_whnf(v_fst_1565_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v___x_1569_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_a_1568_);
lean_dec_ref_known(v___x_1567_, 1);
lean_inc(v_a_1540_);
lean_inc_ref(v_a_1539_);
lean_inc(v_a_1538_);
lean_inc_ref(v_a_1537_);
v___x_1569_ = lean_whnf(v_snd_1566_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v___f_1571_; uint8_t v___y_1573_; uint8_t v___x_1579_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_a_1570_);
lean_dec_ref_known(v___x_1569_, 1);
lean_inc(v_forbidden_1536_);
lean_inc(v_tail_1550_);
lean_inc(v_newNames_1535_);
lean_inc(v_mvarId_1534_);
v___f_1571_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0___boxed), 11, 6);
lean_closure_set(v___f_1571_, 0, v_mvarId_1534_);
lean_closure_set(v___f_1571_, 1, v_head_1549_);
lean_closure_set(v___f_1571_, 2, v_newNames_1535_);
lean_closure_set(v___f_1571_, 3, v_tail_1550_);
lean_closure_set(v___f_1571_, 4, v_forbidden_1536_);
lean_closure_set(v___f_1571_, 5, v_n_1552_);
v___x_1579_ = l_Lean_Expr_isRawNatLit(v_a_1568_);
lean_dec(v_a_1568_);
if (v___x_1579_ == 0)
{
lean_dec(v_a_1570_);
v___y_1573_ = v___x_1558_;
goto v___jp_1572_;
}
else
{
uint8_t v___x_1580_; 
v___x_1580_ = l_Lean_Expr_isRawNatLit(v_a_1570_);
lean_dec(v_a_1570_);
v___y_1573_ = v___x_1580_;
goto v___jp_1572_;
}
v___jp_1572_:
{
if (v___y_1573_ == 0)
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(v___f_1571_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_dec(v___x_1553_);
lean_dec(v_tail_1550_);
lean_dec(v_forbidden_1536_);
lean_dec(v_newNames_1535_);
lean_dec(v_mvarId_1534_);
return v___x_1574_;
}
else
{
lean_object* v_a_1575_; uint8_t v___x_1576_; 
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_a_1575_);
v___x_1576_ = l_Lean_Exception_isInterrupt(v_a_1575_);
if (v___x_1576_ == 0)
{
uint8_t v___x_1577_; 
v___x_1577_ = l_Lean_Exception_isRuntime(v_a_1575_);
v___y_1555_ = v___x_1574_;
v___y_1556_ = v___x_1577_;
goto v___jp_1554_;
}
else
{
lean_dec(v_a_1575_);
v___y_1555_ = v___x_1574_;
v___y_1556_ = v___x_1576_;
goto v___jp_1554_;
}
}
}
else
{
lean_dec_ref(v___f_1571_);
v_depth_1532_ = v___x_1553_;
v_fvarIds_1533_ = v_tail_1550_;
goto _start;
}
}
}
else
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1588_; 
lean_dec(v_a_1568_);
lean_dec(v___x_1553_);
lean_dec(v_n_1552_);
lean_dec(v_tail_1550_);
lean_dec(v_head_1549_);
lean_dec(v_forbidden_1536_);
lean_dec(v_newNames_1535_);
lean_dec(v_mvarId_1534_);
v_a_1581_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1583_ = v___x_1569_;
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1569_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1586_; 
if (v_isShared_1584_ == 0)
{
v___x_1586_ = v___x_1583_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_a_1581_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
}
else
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1596_; 
lean_dec(v_snd_1566_);
lean_dec(v___x_1553_);
lean_dec(v_n_1552_);
lean_dec(v_tail_1550_);
lean_dec(v_head_1549_);
lean_dec(v_forbidden_1536_);
lean_dec(v_newNames_1535_);
lean_dec(v_mvarId_1534_);
v_a_1589_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1591_ = v___x_1567_;
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1567_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1589_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
else
{
lean_dec(v_a_1562_);
lean_dec(v_n_1552_);
lean_dec(v_head_1549_);
v_depth_1532_ = v___x_1553_;
v_fvarIds_1533_ = v_tail_1550_;
goto _start;
}
}
else
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
lean_dec(v___x_1553_);
lean_dec(v_n_1552_);
lean_dec(v_tail_1550_);
lean_dec(v_head_1549_);
lean_dec(v_forbidden_1536_);
lean_dec(v_newNames_1535_);
lean_dec(v_mvarId_1534_);
v_a_1598_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1600_ = v___x_1561_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1561_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1598_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
else
{
lean_object* v_a_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1613_; 
lean_dec(v___x_1553_);
lean_dec(v_n_1552_);
lean_dec(v_tail_1550_);
lean_dec(v_head_1549_);
lean_dec(v_forbidden_1536_);
lean_dec(v_newNames_1535_);
lean_dec(v_mvarId_1534_);
v_a_1606_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1608_ = v___x_1559_;
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_a_1606_);
lean_dec(v___x_1559_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1611_; 
if (v_isShared_1609_ == 0)
{
v___x_1611_ = v___x_1608_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_a_1606_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
}
else
{
lean_dec(v_n_1552_);
lean_dec(v_head_1549_);
v_depth_1532_ = v___x_1553_;
v_fvarIds_1533_ = v_tail_1550_;
goto _start;
}
v___jp_1554_:
{
if (v___y_1556_ == 0)
{
lean_dec_ref(v___y_1555_);
v_depth_1532_ = v___x_1553_;
v_fvarIds_1533_ = v_tail_1550_;
goto _start;
}
else
{
lean_dec(v___x_1553_);
lean_dec(v_tail_1550_);
lean_dec(v_forbidden_1536_);
lean_dec(v_newNames_1535_);
lean_dec(v_mvarId_1534_);
return v___y_1555_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___boxed(lean_object* v_depth_1615_, lean_object* v_fvarIds_1616_, lean_object* v_mvarId_1617_, lean_object* v_newNames_1618_, lean_object* v_forbidden_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go(v_depth_1615_, v_fvarIds_1616_, v_mvarId_1617_, v_newNames_1618_, v_forbidden_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_);
lean_dec(v_a_1623_);
lean_dec_ref(v_a_1622_);
lean_dec(v_a_1621_);
lean_dec_ref(v_a_1620_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0(lean_object* v_mvarId_1626_, lean_object* v_head_1627_, lean_object* v_newNames_1628_, lean_object* v_tail_1629_, lean_object* v_forbidden_1630_, lean_object* v_n_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v___x_1637_; 
lean_inc(v_head_1627_);
v___x_1637_ = l_Lean_Meta_injection(v_mvarId_1626_, v_head_1627_, v_newNames_1628_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1654_; 
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1640_ = v___x_1637_;
v_isShared_1641_ = v_isSharedCheck_1654_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1637_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1654_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
if (lean_obj_tag(v_a_1638_) == 0)
{
lean_object* v___x_1642_; lean_object* v___x_1644_; 
lean_dec(v_n_1631_);
lean_dec(v_forbidden_1630_);
lean_dec(v_tail_1629_);
lean_dec(v_head_1627_);
v___x_1642_ = lean_box(0);
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 0, v___x_1642_);
v___x_1644_ = v___x_1640_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1642_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
else
{
lean_object* v_mvarId_1646_; lean_object* v_newEqs_1647_; lean_object* v_remainingNames_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
lean_del_object(v___x_1640_);
v_mvarId_1646_ = lean_ctor_get(v_a_1638_, 0);
lean_inc_n(v_mvarId_1646_, 2);
v_newEqs_1647_ = lean_ctor_get(v_a_1638_, 1);
lean_inc_ref(v_newEqs_1647_);
v_remainingNames_1648_ = lean_ctor_get(v_a_1638_, 2);
lean_inc(v_remainingNames_1648_);
lean_dec_ref_known(v_a_1638_, 3);
v___x_1649_ = lean_array_to_list(v_newEqs_1647_);
v___x_1650_ = l_List_appendTR___redArg(v___x_1649_, v_tail_1629_);
v___x_1651_ = l_Lean_FVarIdSet_insert(v_forbidden_1630_, v_head_1627_);
v___x_1652_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___boxed), 10, 5);
lean_closure_set(v___x_1652_, 0, v_n_1631_);
lean_closure_set(v___x_1652_, 1, v___x_1650_);
lean_closure_set(v___x_1652_, 2, v_mvarId_1646_);
lean_closure_set(v___x_1652_, 3, v_remainingNames_1648_);
lean_closure_set(v___x_1652_, 4, v___x_1651_);
v___x_1653_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg(v_mvarId_1646_, v___x_1652_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
return v___x_1653_;
}
}
}
else
{
lean_object* v_a_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1662_; 
lean_dec(v_n_1631_);
lean_dec(v_forbidden_1630_);
lean_dec(v_tail_1629_);
lean_dec(v_head_1627_);
v_a_1655_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1657_ = v___x_1637_;
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_dec(v___x_1637_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1660_; 
if (v_isShared_1658_ == 0)
{
v___x_1660_ = v___x_1657_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_a_1655_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0(lean_object* v_00_u03b2_1663_, lean_object* v_k_1664_, lean_object* v_t_1665_){
_start:
{
uint8_t v___x_1666_; 
v___x_1666_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(v_k_1664_, v_t_1665_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___boxed(lean_object* v_00_u03b2_1667_, lean_object* v_k_1668_, lean_object* v_t_1669_){
_start:
{
uint8_t v_res_1670_; lean_object* v_r_1671_; 
v_res_1670_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0(v_00_u03b2_1667_, v_k_1668_, v_t_1669_);
lean_dec(v_t_1669_);
lean_dec(v_k_1668_);
v_r_1671_ = lean_box(v_res_1670_);
return v_r_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections___lam__0(lean_object* v_maxDepth_1672_, lean_object* v_mvarId_1673_, lean_object* v_newNames_1674_, lean_object* v_forbidden_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v_lctx_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v_lctx_1681_ = lean_ctor_get(v___y_1676_, 2);
v___x_1682_ = l_Lean_LocalContext_getFVarIds(v_lctx_1681_);
v___x_1683_ = lean_array_to_list(v___x_1682_);
v___x_1684_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go(v_maxDepth_1672_, v___x_1683_, v_mvarId_1673_, v_newNames_1674_, v_forbidden_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections___lam__0___boxed(lean_object* v_maxDepth_1685_, lean_object* v_mvarId_1686_, lean_object* v_newNames_1687_, lean_object* v_forbidden_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Lean_Meta_injections___lam__0(v_maxDepth_1685_, v_mvarId_1686_, v_newNames_1687_, v_forbidden_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections(lean_object* v_mvarId_1695_, lean_object* v_newNames_1696_, lean_object* v_maxDepth_1697_, lean_object* v_forbidden_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_){
_start:
{
lean_object* v___f_1704_; lean_object* v___x_1705_; 
lean_inc(v_mvarId_1695_);
v___f_1704_ = lean_alloc_closure((void*)(l_Lean_Meta_injections___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1704_, 0, v_maxDepth_1697_);
lean_closure_set(v___f_1704_, 1, v_mvarId_1695_);
lean_closure_set(v___f_1704_, 2, v_newNames_1696_);
lean_closure_set(v___f_1704_, 3, v_forbidden_1698_);
v___x_1705_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg(v_mvarId_1695_, v___f_1704_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections___boxed(lean_object* v_mvarId_1706_, lean_object* v_newNames_1707_, lean_object* v_maxDepth_1708_, lean_object* v_forbidden_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_Lean_Meta_injections(v_mvarId_1706_, v_newNames_1707_, v_maxDepth_1708_, v_forbidden_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_);
lean_dec(v_a_1713_);
lean_dec_ref(v_a_1712_);
lean_dec(v_a_1711_);
lean_dec_ref(v_a_1710_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1772_; uint8_t v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1772_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__1));
v___x_1773_ = 0;
v___x_1774_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__22_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_));
v___x_1775_ = l_Lean_registerTraceClass(v___x_1772_, v___x_1773_, v___x_1774_);
return v___x_1775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2____boxed(lean_object* v_a_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l___private_Lean_Meta_Tactic_Injection_0__initFn_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_();
return v_res_1777_;
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
