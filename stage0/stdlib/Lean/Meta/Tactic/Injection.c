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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_a_93_; uint8_t v___x_97_; 
v___x_97_ = lean_nat_dec_lt(v_a_85_, v_upperBound_82_);
if (v___x_97_ == 0)
{
lean_object* v___x_98_; 
lean_dec(v_a_85_);
v___x_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_98_, 0, v_b_86_);
return v___x_98_;
}
else
{
lean_object* v_numParams_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v_numParams_99_ = lean_ctor_get(v_ctorInfo_83_, 3);
v___x_100_ = l_Lean_instInhabitedExpr;
v___x_101_ = lean_nat_add(v_numParams_99_, v_a_85_);
v___x_102_ = lean_array_get_borrowed(v___x_100_, v_xs_84_, v___x_101_);
lean_dec(v___x_101_);
lean_inc(v___y_90_);
lean_inc_ref(v___y_89_);
lean_inc(v___y_88_);
lean_inc_ref(v___y_87_);
lean_inc(v___x_102_);
v___x_103_ = lean_infer_type(v___x_102_, v___y_87_, v___y_88_, v___y_89_, v___y_90_);
if (lean_obj_tag(v___x_103_) == 0)
{
lean_object* v_a_104_; lean_object* v___x_105_; 
v_a_104_ = lean_ctor_get(v___x_103_, 0);
lean_inc(v_a_104_);
lean_dec_ref_known(v___x_103_, 1);
v___x_105_ = l_Lean_Meta_isProp(v_a_104_, v___y_87_, v___y_88_, v___y_89_, v___y_90_);
if (lean_obj_tag(v___x_105_) == 0)
{
lean_object* v_a_106_; uint8_t v___x_107_; 
v_a_106_ = lean_ctor_get(v___x_105_, 0);
lean_inc(v_a_106_);
lean_dec_ref_known(v___x_105_, 1);
v___x_107_ = lean_unbox(v_a_106_);
lean_dec(v_a_106_);
if (v___x_107_ == 0)
{
v_a_93_ = v_b_86_;
goto v___jp_92_;
}
else
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = lean_unsigned_to_nat(1u);
v___x_109_ = lean_nat_add(v_b_86_, v___x_108_);
lean_dec(v_b_86_);
v_a_93_ = v___x_109_;
goto v___jp_92_;
}
}
else
{
lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_117_; 
lean_dec(v_b_86_);
lean_dec(v_a_85_);
v_a_110_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_117_ == 0)
{
v___x_112_ = v___x_105_;
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v___x_105_);
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
v_a_118_ = lean_ctor_get(v___x_103_, 0);
v_isSharedCheck_125_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_125_ == 0)
{
v___x_120_ = v___x_103_;
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_dec(v___x_103_);
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
v___jp_92_:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = lean_unsigned_to_nat(1u);
v___x_95_ = lean_nat_add(v_a_85_, v___x_94_);
lean_dec(v_a_85_);
v_a_85_ = v___x_95_;
v_b_86_ = v_a_93_;
goto _start;
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
lean_object* v___x_379_; lean_object* v___x_380_; double v___x_381_; uint8_t v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_390_; 
v___x_379_ = lean_box(0);
v___x_380_ = lean_box(0);
v___x_381_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__0);
v___x_382_ = 0;
v___x_383_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__1));
v___x_384_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_384_, 0, v_cls_348_);
lean_ctor_set(v___x_384_, 1, v___x_380_);
lean_ctor_set(v___x_384_, 2, v___x_383_);
lean_ctor_set_float(v___x_384_, sizeof(void*)*3, v___x_381_);
lean_ctor_set_float(v___x_384_, sizeof(void*)*3 + 8, v___x_381_);
lean_ctor_set_uint8(v___x_384_, sizeof(void*)*3 + 16, v___x_382_);
v___x_385_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__2));
v___x_386_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_386_, 0, v___x_384_);
lean_ctor_set(v___x_386_, 1, v_a_357_);
lean_ctor_set(v___x_386_, 2, v___x_385_);
lean_inc(v_ref_355_);
v___x_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_387_, 0, v_ref_355_);
lean_ctor_set(v___x_387_, 1, v___x_386_);
v___x_388_ = l_Lean_PersistentArray_push___redArg(v_traces_375_, v___x_387_);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 0, v___x_388_);
v___x_390_ = v___x_377_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_388_);
lean_ctor_set_uint64(v_reuseFailAlloc_398_, sizeof(void*)*1, v_tid_374_);
v___x_390_ = v_reuseFailAlloc_398_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
lean_object* v___x_392_; 
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 4, v___x_390_);
v___x_392_ = v___x_372_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_env_363_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v_nextMacroScope_364_);
lean_ctor_set(v_reuseFailAlloc_397_, 2, v_ngen_365_);
lean_ctor_set(v_reuseFailAlloc_397_, 3, v_auxDeclNGen_366_);
lean_ctor_set(v_reuseFailAlloc_397_, 4, v___x_390_);
lean_ctor_set(v_reuseFailAlloc_397_, 5, v_cache_367_);
lean_ctor_set(v_reuseFailAlloc_397_, 6, v_messages_368_);
lean_ctor_set(v_reuseFailAlloc_397_, 7, v_infoState_369_);
lean_ctor_set(v_reuseFailAlloc_397_, 8, v_snapshotTasks_370_);
v___x_392_ = v_reuseFailAlloc_397_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
lean_object* v___x_393_; lean_object* v___x_395_; 
v___x_393_ = lean_st_ref_put(v___y_353_, v___x_392_);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 0, v___x_379_);
v___x_395_ = v___x_359_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_379_);
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
v___x_445_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
size_t v_x_14494__boxed_549_; size_t v_x_14495__boxed_550_; lean_object* v_res_551_; 
v_x_14494__boxed_549_ = lean_unbox_usize(v_x_545_);
lean_dec(v_x_545_);
v_x_14495__boxed_550_ = lean_unbox_usize(v_x_546_);
lean_dec(v_x_546_);
v_res_551_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(v_x_544_, v_x_14494__boxed_549_, v_x_14495__boxed_550_, v_x_547_, v_x_548_);
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
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_589_; 
v___x_586_ = lean_box(0);
v___x_587_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0___redArg(v_eAssignment_580_, v_mvarId_559_, v_val_560_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 8, v___x_587_);
v___x_589_ = v___x_584_;
goto v_reusejp_588_;
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
lean_ctor_set(v_reuseFailAlloc_595_, 8, v___x_587_);
lean_ctor_set(v_reuseFailAlloc_595_, 9, v_dAssignment_581_);
lean_ctor_set(v_reuseFailAlloc_595_, 10, v_instanceTypedMVars_582_);
v___x_589_ = v_reuseFailAlloc_595_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_object* v___x_591_; 
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v___x_589_);
v___x_591_ = v___x_570_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_589_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_cache_565_);
lean_ctor_set(v_reuseFailAlloc_594_, 2, v_zetaDeltaFVarIds_566_);
lean_ctor_set(v_reuseFailAlloc_594_, 3, v_postponed_567_);
lean_ctor_set(v_reuseFailAlloc_594_, 4, v_diag_568_);
v___x_591_ = v_reuseFailAlloc_594_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = lean_st_ref_put(v___y_561_, v___x_591_);
v___x_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_586_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___lam__1(lean_object* v___x_653_, lean_object* v_mvarId_654_, lean_object* v_fvarId_655_, lean_object* v___x_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v_type_915_; lean_object* v_prf_916_; lean_object* v___x_996_; 
lean_inc(v___x_653_);
lean_inc(v_mvarId_654_);
v___x_996_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_654_, v___x_653_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v___x_997_; 
lean_dec_ref_known(v___x_996_, 1);
lean_inc(v_fvarId_655_);
v___x_997_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_655_, v___y_657_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_a_998_);
lean_dec_ref_known(v___x_997_, 1);
v___x_999_ = l_Lean_LocalDecl_type(v_a_998_);
lean_dec(v_a_998_);
lean_inc(v___y_660_);
lean_inc_ref(v___y_659_);
lean_inc(v___y_658_);
lean_inc_ref(v___y_657_);
v___x_1000_ = lean_whnf(v___x_999_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; uint8_t v___x_1005_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_1000_, 1);
lean_inc(v_fvarId_655_);
v___x_1002_ = l_Lean_mkFVar(v_fvarId_655_);
v___x_1003_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__31));
v___x_1004_ = lean_unsigned_to_nat(4u);
v___x_1005_ = l_Lean_Expr_isAppOfArity(v_a_1001_, v___x_1003_, v___x_1004_);
if (v___x_1005_ == 0)
{
v_type_915_ = v_a_1001_;
v_prf_916_ = v___x_1002_;
goto v___jp_914_;
}
else
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1006_ = l_Lean_Expr_appFn_x21(v_a_1001_);
v___x_1007_ = l_Lean_Expr_appFn_x21(v___x_1006_);
v___x_1008_ = l_Lean_Expr_appFn_x21(v___x_1007_);
v___x_1009_ = l_Lean_Expr_appArg_x21(v___x_1008_);
lean_dec_ref(v___x_1008_);
v___x_1010_ = l_Lean_Expr_appArg_x21(v___x_1007_);
lean_dec_ref(v___x_1007_);
v___x_1011_ = l_Lean_Expr_appArg_x21(v___x_1006_);
lean_dec_ref(v___x_1006_);
v___x_1012_ = l_Lean_Expr_appArg_x21(v_a_1001_);
v___x_1013_ = l_Lean_Meta_isExprDefEq(v___x_1009_, v___x_1011_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v_a_1014_; uint8_t v___x_1015_; 
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc(v_a_1014_);
lean_dec_ref_known(v___x_1013_, 1);
v___x_1015_ = lean_unbox(v_a_1014_);
lean_dec(v_a_1014_);
if (v___x_1015_ == 0)
{
lean_dec_ref(v___x_1012_);
lean_dec_ref(v___x_1010_);
v_type_915_ = v_a_1001_;
v_prf_916_ = v___x_1002_;
goto v___jp_914_;
}
else
{
lean_object* v___x_1016_; 
lean_dec(v_a_1001_);
v___x_1016_ = l_Lean_Meta_mkEq(v___x_1010_, v___x_1012_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; lean_object* v___x_1018_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_a_1017_);
lean_dec_ref_known(v___x_1016_, 1);
v___x_1018_ = l_Lean_Meta_mkEqOfHEq(v___x_1002_, v___x_1005_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_a_1019_);
lean_dec_ref_known(v___x_1018_, 1);
v_type_915_ = v_a_1017_;
v_prf_916_ = v_a_1019_;
goto v___jp_914_;
}
else
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1027_; 
lean_dec(v_a_1017_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec_ref(v___x_656_);
lean_dec(v_fvarId_655_);
lean_dec(v_mvarId_654_);
lean_dec(v___x_653_);
v_a_1020_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1022_ = v___x_1018_;
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_1018_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1025_; 
if (v_isShared_1023_ == 0)
{
v___x_1025_ = v___x_1022_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_a_1020_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
}
else
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
lean_dec_ref(v___x_1002_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec_ref(v___x_656_);
lean_dec(v_fvarId_655_);
lean_dec(v_mvarId_654_);
lean_dec(v___x_653_);
v_a_1028_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_1016_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1016_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1031_ == 0)
{
v___x_1033_ = v___x_1030_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_a_1028_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
}
}
else
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
lean_dec_ref(v___x_1012_);
lean_dec_ref(v___x_1010_);
lean_dec_ref(v___x_1002_);
lean_dec(v_a_1001_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec_ref(v___x_656_);
lean_dec(v_fvarId_655_);
lean_dec(v_mvarId_654_);
lean_dec(v___x_653_);
v_a_1036_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1038_ = v___x_1013_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1013_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_a_1036_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
}
else
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1051_; 
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec_ref(v___x_656_);
lean_dec(v_fvarId_655_);
lean_dec(v_mvarId_654_);
lean_dec(v___x_653_);
v_a_1044_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1046_ = v___x_1000_;
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1000_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1044_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
else
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec_ref(v___x_656_);
lean_dec(v_fvarId_655_);
lean_dec(v_mvarId_654_);
lean_dec(v___x_653_);
v_a_1052_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_997_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_997_);
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
else
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec_ref(v___x_656_);
lean_dec(v_fvarId_655_);
lean_dec(v_mvarId_654_);
lean_dec(v___x_653_);
v_a_1060_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1062_ = v___x_996_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_996_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1060_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
v___jp_662_:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__3, &l_Lean_Meta_injectionCore___lam__1___closed__3_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__3);
v___x_668_ = l_Lean_Meta_throwTacticEx___redArg(v___x_653_, v_mvarId_654_, v___x_667_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
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
v___x_675_ = l_Lean_Meta_throwTacticEx___redArg(v___x_653_, v_mvarId_654_, v___x_674_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
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
lean_dec(v___x_653_);
v___x_697_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(v_mvarId_654_, v___y_684_, v___y_688_);
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
lean_object* v_binderType_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
lean_dec_ref(v___y_685_);
lean_dec(v___x_653_);
v_binderType_711_ = lean_ctor_get(v_a_710_, 1);
lean_inc_ref(v_binderType_711_);
lean_dec_ref_known(v_a_710_, 3);
v___x_712_ = l_Lean_Expr_headBeta(v_binderType_711_);
lean_inc(v_mvarId_654_);
v___x_713_ = l_Lean_MVarId_getTag(v_mvarId_654_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v_a_714_; lean_object* v___x_715_; 
v_a_714_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_a_714_);
lean_dec_ref_known(v___x_713_, 1);
v___x_715_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_712_, v_a_714_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_a_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_771_; 
v_a_716_ = lean_ctor_get(v___x_715_, 0);
lean_inc_n(v_a_716_, 2);
lean_dec_ref_known(v___x_715_, 1);
v___x_717_ = l_Lean_Expr_app___override(v___y_684_, v_a_716_);
v___x_718_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(v_mvarId_654_, v___x_717_, v___y_688_);
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
lean_dec(v_mvarId_654_);
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
lean_dec_ref(v___x_712_);
lean_dec(v_numFields_693_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_684_);
lean_dec(v___y_682_);
lean_dec(v_fvarId_655_);
lean_dec(v_mvarId_654_);
v_a_781_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_788_ == 0)
{
v___x_783_ = v___x_713_;
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_713_);
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
lean_dec(v_mvarId_654_);
lean_dec(v___x_653_);
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
lean_dec(v_mvarId_654_);
lean_dec(v___x_653_);
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
lean_dec(v_mvarId_654_);
lean_dec(v___x_653_);
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
lean_dec(v_mvarId_654_);
lean_dec(v___x_653_);
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
lean_dec(v_mvarId_654_);
lean_dec(v___x_653_);
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
lean_dec(v_mvarId_654_);
lean_dec(v___x_653_);
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
lean_dec(v_mvarId_654_);
lean_dec(v___x_653_);
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
lean_dec(v_mvarId_654_);
lean_dec(v___x_653_);
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
lean_object* v___x_917_; lean_object* v___x_918_; uint8_t v___x_919_; 
v___x_917_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__19));
v___x_918_ = lean_unsigned_to_nat(3u);
v___x_919_ = l_Lean_Expr_isAppOfArity(v_type_915_, v___x_917_, v___x_918_);
if (v___x_919_ == 0)
{
lean_object* v___x_920_; lean_object* v___x_921_; 
lean_dec_ref(v_prf_916_);
lean_dec_ref(v_type_915_);
lean_dec_ref(v___x_656_);
lean_dec(v_fvarId_655_);
v___x_920_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__23, &l_Lean_Meta_injectionCore___lam__1___closed__23_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__23);
v___x_921_ = l_Lean_Meta_throwTacticEx___redArg(v___x_653_, v_mvarId_654_, v___x_920_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
return v___x_921_;
}
else
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_922_ = l_Lean_Expr_appFn_x21(v_type_915_);
v___x_923_ = l_Lean_Expr_appArg_x21(v___x_922_);
lean_dec_ref(v___x_922_);
v___x_924_ = l_Lean_Expr_appArg_x21(v_type_915_);
lean_dec_ref(v_type_915_);
lean_inc(v_mvarId_654_);
v___x_925_ = l_Lean_MVarId_getType(v_mvarId_654_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v_a_926_; lean_object* v___x_927_; 
v_a_926_ = lean_ctor_get(v___x_925_, 0);
lean_inc(v_a_926_);
lean_dec_ref_known(v___x_925_, 1);
v___x_927_ = l_Lean_Meta_isConstructorApp_x27_x3f(v___x_923_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v_a_928_; lean_object* v___x_929_; 
v_a_928_ = lean_ctor_get(v___x_927_, 0);
lean_inc(v_a_928_);
lean_dec_ref_known(v___x_927_, 1);
v___x_929_ = l_Lean_Meta_isConstructorApp_x27_x3f(v___x_924_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_929_) == 0)
{
if (lean_obj_tag(v_a_928_) == 1)
{
lean_object* v_a_930_; 
v_a_930_ = lean_ctor_get(v___x_929_, 0);
lean_inc(v_a_930_);
lean_dec_ref_known(v___x_929_, 1);
if (lean_obj_tag(v_a_930_) == 1)
{
lean_object* v_val_931_; lean_object* v_val_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___f_936_; lean_object* v___x_937_; lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_971_; 
v_val_931_ = lean_ctor_get(v_a_928_, 0);
lean_inc(v_val_931_);
lean_dec_ref_known(v_a_928_, 1);
v_val_932_ = lean_ctor_get(v_a_930_, 0);
lean_inc(v_val_932_);
lean_dec_ref_known(v_a_930_, 1);
v___x_933_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__24));
v___x_934_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__25));
v___x_935_ = l_Lean_Name_mkStr3(v___x_933_, v___x_934_, v___x_656_);
lean_inc_n(v___x_935_, 2);
v___f_936_ = lean_alloc_closure((void*)(l_Lean_Meta_injectionCore___lam__0___boxed), 6, 1);
lean_closure_set(v___f_936_, 0, v___x_935_);
v___x_937_ = l_Lean_Meta_injectionCore___lam__0(v___x_935_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
v_a_938_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_971_ == 0)
{
v___x_940_ = v___x_937_;
v_isShared_941_ = v_isSharedCheck_971_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_937_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_971_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
uint8_t v___x_942_; 
v___x_942_ = lean_unbox(v_a_938_);
lean_dec(v_a_938_);
if (v___x_942_ == 0)
{
lean_del_object(v___x_940_);
v___y_885_ = v___x_935_;
v___y_886_ = v_val_932_;
v___y_887_ = v_a_926_;
v___y_888_ = v_prf_916_;
v___y_889_ = v___f_936_;
v___y_890_ = v_val_931_;
v___y_891_ = v___y_657_;
v___y_892_ = v___y_658_;
v___y_893_ = v___y_659_;
v___y_894_ = v___y_660_;
goto v___jp_884_;
}
else
{
lean_object* v___x_943_; 
lean_inc(v___y_660_);
lean_inc_ref(v___y_659_);
lean_inc(v___y_658_);
lean_inc_ref(v___y_657_);
lean_inc_ref(v_prf_916_);
v___x_943_ = lean_infer_type(v_prf_916_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_a_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_951_; 
v_a_944_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_a_944_);
lean_dec_ref_known(v___x_943_, 1);
v___x_945_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__27, &l_Lean_Meta_injectionCore___lam__1___closed__27_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__27);
v___x_946_ = l_Lean_MessageData_ofExpr(v_a_944_);
v___x_947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_945_);
lean_ctor_set(v___x_947_, 1, v___x_946_);
v___x_948_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__29, &l_Lean_Meta_injectionCore___lam__1___closed__29_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__29);
v___x_949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_947_);
lean_ctor_set(v___x_949_, 1, v___x_948_);
lean_inc(v_mvarId_654_);
if (v_isShared_941_ == 0)
{
lean_ctor_set_tag(v___x_940_, 1);
lean_ctor_set(v___x_940_, 0, v_mvarId_654_);
v___x_951_ = v___x_940_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_mvarId_654_);
v___x_951_ = v_reuseFailAlloc_962_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_949_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
lean_inc(v___x_935_);
v___x_953_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v___x_935_, v___x_952_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_dec_ref_known(v___x_953_, 1);
v___y_885_ = v___x_935_;
v___y_886_ = v_val_932_;
v___y_887_ = v_a_926_;
v___y_888_ = v_prf_916_;
v___y_889_ = v___f_936_;
v___y_890_ = v_val_931_;
v___y_891_ = v___y_657_;
v___y_892_ = v___y_658_;
v___y_893_ = v___y_659_;
v___y_894_ = v___y_660_;
goto v___jp_884_;
}
else
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_961_; 
lean_dec_ref(v___f_936_);
lean_dec(v___x_935_);
lean_dec(v_val_932_);
lean_dec(v_val_931_);
lean_dec(v_a_926_);
lean_dec_ref(v_prf_916_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v_fvarId_655_);
lean_dec(v_mvarId_654_);
lean_dec(v___x_653_);
v_a_954_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_961_ == 0)
{
v___x_956_ = v___x_953_;
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_953_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_959_; 
if (v_isShared_957_ == 0)
{
v___x_959_ = v___x_956_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_954_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
}
else
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_970_; 
lean_del_object(v___x_940_);
lean_dec_ref(v___f_936_);
lean_dec(v___x_935_);
lean_dec(v_val_932_);
lean_dec(v_val_931_);
lean_dec(v_a_926_);
lean_dec_ref(v_prf_916_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v_fvarId_655_);
lean_dec(v_mvarId_654_);
lean_dec(v___x_653_);
v_a_963_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_970_ == 0)
{
v___x_965_ = v___x_943_;
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_943_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_968_; 
if (v_isShared_966_ == 0)
{
v___x_968_ = v___x_965_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_963_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_a_928_, 1);
lean_dec(v_a_930_);
lean_dec(v_a_926_);
lean_dec_ref(v_prf_916_);
lean_dec_ref(v___x_656_);
lean_dec(v_fvarId_655_);
v___y_670_ = v___y_657_;
v___y_671_ = v___y_658_;
v___y_672_ = v___y_659_;
v___y_673_ = v___y_660_;
goto v___jp_669_;
}
}
else
{
lean_dec_ref_known(v___x_929_, 1);
lean_dec(v_a_928_);
lean_dec(v_a_926_);
lean_dec_ref(v_prf_916_);
lean_dec_ref(v___x_656_);
lean_dec(v_fvarId_655_);
v___y_670_ = v___y_657_;
v___y_671_ = v___y_658_;
v___y_672_ = v___y_659_;
v___y_673_ = v___y_660_;
goto v___jp_669_;
}
}
else
{
lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_979_; 
lean_dec(v_a_928_);
lean_dec(v_a_926_);
lean_dec_ref(v_prf_916_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec_ref(v___x_656_);
lean_dec(v_fvarId_655_);
lean_dec(v_mvarId_654_);
lean_dec(v___x_653_);
v_a_972_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_979_ == 0)
{
v___x_974_ = v___x_929_;
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v___x_929_);
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
else
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
lean_dec(v_a_926_);
lean_dec_ref(v___x_924_);
lean_dec_ref(v_prf_916_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec_ref(v___x_656_);
lean_dec(v_fvarId_655_);
lean_dec(v_mvarId_654_);
lean_dec(v___x_653_);
v_a_980_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_927_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_927_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_980_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
lean_dec_ref(v___x_924_);
lean_dec_ref(v___x_923_);
lean_dec_ref(v_prf_916_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec_ref(v___x_656_);
lean_dec(v_fvarId_655_);
lean_dec(v_mvarId_654_);
lean_dec(v___x_653_);
v_a_988_ = lean_ctor_get(v___x_925_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_925_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_925_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___lam__1___boxed(lean_object* v___x_1068_, lean_object* v_mvarId_1069_, lean_object* v_fvarId_1070_, lean_object* v___x_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Lean_Meta_injectionCore___lam__1(v___x_1068_, v_mvarId_1069_, v_fvarId_1070_, v___x_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore(lean_object* v_mvarId_1081_, lean_object* v_fvarId_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___f_1090_; lean_object* v___x_1091_; 
v___x_1088_ = ((lean_object*)(l_Lean_Meta_injectionCore___closed__0));
v___x_1089_ = ((lean_object*)(l_Lean_Meta_injectionCore___closed__1));
lean_inc(v_mvarId_1081_);
v___f_1090_ = lean_alloc_closure((void*)(l_Lean_Meta_injectionCore___lam__1___boxed), 9, 4);
lean_closure_set(v___f_1090_, 0, v___x_1089_);
lean_closure_set(v___f_1090_, 1, v_mvarId_1081_);
lean_closure_set(v___f_1090_, 2, v_fvarId_1082_);
lean_closure_set(v___f_1090_, 3, v___x_1088_);
v___x_1091_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg(v_mvarId_1081_, v___f_1090_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___boxed(lean_object* v_mvarId_1092_, lean_object* v_fvarId_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Lean_Meta_injectionCore(v_mvarId_1092_, v_fvarId_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_);
lean_dec(v_a_1097_);
lean_dec_ref(v_a_1096_);
lean_dec(v_a_1095_);
lean_dec_ref(v_a_1094_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0(lean_object* v_mvarId_1100_, lean_object* v_val_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v___x_1107_; 
v___x_1107_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(v_mvarId_1100_, v_val_1101_, v___y_1103_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___boxed(lean_object* v_mvarId_1108_, lean_object* v_val_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0(v_mvarId_1108_, v_val_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0(lean_object* v_00_u03b2_1116_, lean_object* v_x_1117_, lean_object* v_x_1118_, lean_object* v_x_1119_){
_start:
{
lean_object* v___x_1120_; 
v___x_1120_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0___redArg(v_x_1117_, v_x_1118_, v_x_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1121_, lean_object* v_x_1122_, size_t v_x_1123_, size_t v_x_1124_, lean_object* v_x_1125_, lean_object* v_x_1126_){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(v_x_1122_, v_x_1123_, v_x_1124_, v_x_1125_, v_x_1126_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1128_, lean_object* v_x_1129_, lean_object* v_x_1130_, lean_object* v_x_1131_, lean_object* v_x_1132_, lean_object* v_x_1133_){
_start:
{
size_t v_x_15702__boxed_1134_; size_t v_x_15703__boxed_1135_; lean_object* v_res_1136_; 
v_x_15702__boxed_1134_ = lean_unbox_usize(v_x_1130_);
lean_dec(v_x_1130_);
v_x_15703__boxed_1135_ = lean_unbox_usize(v_x_1131_);
lean_dec(v_x_1131_);
v_res_1136_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2(v_00_u03b2_1128_, v_x_1129_, v_x_15702__boxed_1134_, v_x_15703__boxed_1135_, v_x_1132_, v_x_1133_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1137_, lean_object* v_n_1138_, lean_object* v_k_1139_, lean_object* v_v_1140_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5___redArg(v_n_1138_, v_k_1139_, v_v_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_1142_, size_t v_depth_1143_, lean_object* v_keys_1144_, lean_object* v_vals_1145_, lean_object* v_heq_1146_, lean_object* v_i_1147_, lean_object* v_entries_1148_){
_start:
{
lean_object* v___x_1149_; 
v___x_1149_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___redArg(v_depth_1143_, v_keys_1144_, v_vals_1145_, v_i_1147_, v_entries_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1150_, lean_object* v_depth_1151_, lean_object* v_keys_1152_, lean_object* v_vals_1153_, lean_object* v_heq_1154_, lean_object* v_i_1155_, lean_object* v_entries_1156_){
_start:
{
size_t v_depth_boxed_1157_; lean_object* v_res_1158_; 
v_depth_boxed_1157_ = lean_unbox_usize(v_depth_1151_);
lean_dec(v_depth_1151_);
v_res_1158_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6(v_00_u03b2_1150_, v_depth_boxed_1157_, v_keys_1152_, v_vals_1153_, v_heq_1154_, v_i_1155_, v_entries_1156_);
lean_dec_ref(v_vals_1153_);
lean_dec_ref(v_keys_1152_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5_spec__6(lean_object* v_00_u03b2_1159_, lean_object* v_x_1160_, lean_object* v_x_1161_, lean_object* v_x_1162_, lean_object* v_x_1163_){
_start:
{
lean_object* v___x_1164_; 
v___x_1164_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(v_x_1160_, v_x_1161_, v_x_1162_, v_x_1163_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorIdx(lean_object* v_x_1165_){
_start:
{
if (lean_obj_tag(v_x_1165_) == 0)
{
lean_object* v___x_1166_; 
v___x_1166_ = lean_unsigned_to_nat(0u);
return v___x_1166_;
}
else
{
lean_object* v___x_1167_; 
v___x_1167_ = lean_unsigned_to_nat(1u);
return v___x_1167_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorIdx___boxed(lean_object* v_x_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Lean_Meta_InjectionResult_ctorIdx(v_x_1168_);
lean_dec(v_x_1168_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorElim___redArg(lean_object* v_t_1170_, lean_object* v_k_1171_){
_start:
{
if (lean_obj_tag(v_t_1170_) == 0)
{
return v_k_1171_;
}
else
{
lean_object* v_mvarId_1172_; lean_object* v_newEqs_1173_; lean_object* v_remainingNames_1174_; lean_object* v___x_1175_; 
v_mvarId_1172_ = lean_ctor_get(v_t_1170_, 0);
lean_inc(v_mvarId_1172_);
v_newEqs_1173_ = lean_ctor_get(v_t_1170_, 1);
lean_inc_ref(v_newEqs_1173_);
v_remainingNames_1174_ = lean_ctor_get(v_t_1170_, 2);
lean_inc(v_remainingNames_1174_);
lean_dec_ref_known(v_t_1170_, 3);
v___x_1175_ = lean_apply_3(v_k_1171_, v_mvarId_1172_, v_newEqs_1173_, v_remainingNames_1174_);
return v___x_1175_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorElim(lean_object* v_motive_1176_, lean_object* v_ctorIdx_1177_, lean_object* v_t_1178_, lean_object* v_h_1179_, lean_object* v_k_1180_){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_1178_, v_k_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorElim___boxed(lean_object* v_motive_1182_, lean_object* v_ctorIdx_1183_, lean_object* v_t_1184_, lean_object* v_h_1185_, lean_object* v_k_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Lean_Meta_InjectionResult_ctorElim(v_motive_1182_, v_ctorIdx_1183_, v_t_1184_, v_h_1185_, v_k_1186_);
lean_dec(v_ctorIdx_1183_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_solved_elim___redArg(lean_object* v_t_1188_, lean_object* v_solved_1189_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_1188_, v_solved_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_solved_elim(lean_object* v_motive_1191_, lean_object* v_t_1192_, lean_object* v_h_1193_, lean_object* v_solved_1194_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_1192_, v_solved_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_subgoal_elim___redArg(lean_object* v_t_1196_, lean_object* v_subgoal_1197_){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_1196_, v_subgoal_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_subgoal_elim(lean_object* v_motive_1199_, lean_object* v_t_1200_, lean_object* v_h_1201_, lean_object* v_subgoal_1202_){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_1200_, v_subgoal_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go(uint8_t v_tryToClear_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_){
_start:
{
lean_object* v_zero_1214_; uint8_t v_isZero_1215_; 
v_zero_1214_ = lean_unsigned_to_nat(0u);
v_isZero_1215_ = lean_nat_dec_eq(v_a_1205_, v_zero_1214_);
if (v_isZero_1215_ == 1)
{
lean_object* v___x_1216_; lean_object* v___x_1217_; 
lean_dec(v_a_1205_);
v___x_1216_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1216_, 0, v_a_1206_);
lean_ctor_set(v___x_1216_, 1, v_a_1207_);
lean_ctor_set(v___x_1216_, 2, v_a_1208_);
v___x_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
return v___x_1217_;
}
else
{
lean_object* v_one_1218_; lean_object* v_n_1219_; 
v_one_1218_ = lean_unsigned_to_nat(1u);
v_n_1219_ = lean_nat_sub(v_a_1205_, v_one_1218_);
lean_dec(v_a_1205_);
if (lean_obj_tag(v_a_1208_) == 0)
{
lean_object* v___x_1220_; 
v___x_1220_ = l_Lean_Meta_intro1Core(v_a_1206_, v_isZero_1215_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v_a_1221_; lean_object* v_fst_1222_; lean_object* v_snd_1223_; lean_object* v___x_1224_; 
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
lean_inc(v_a_1221_);
lean_dec_ref_known(v___x_1220_, 1);
v_fst_1222_ = lean_ctor_get(v_a_1221_, 0);
lean_inc(v_fst_1222_);
v_snd_1223_ = lean_ctor_get(v_a_1221_, 1);
lean_inc(v_snd_1223_);
lean_dec(v_a_1221_);
v___x_1224_ = l_Lean_Meta_heqToEq(v_snd_1223_, v_fst_1222_, v_tryToClear_1204_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_);
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
v___x_1228_ = lean_array_push(v_a_1207_, v_fst_1226_);
v_a_1205_ = v_n_1219_;
v_a_1206_ = v_snd_1227_;
v_a_1207_ = v___x_1228_;
goto _start;
}
else
{
lean_object* v_a_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1237_; 
lean_dec(v_n_1219_);
lean_dec_ref(v_a_1207_);
v_a_1230_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1232_ = v___x_1224_;
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_a_1230_);
lean_dec(v___x_1224_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1235_; 
if (v_isShared_1233_ == 0)
{
v___x_1235_ = v___x_1232_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_a_1230_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
}
else
{
lean_object* v_a_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1245_; 
lean_dec(v_n_1219_);
lean_dec_ref(v_a_1207_);
v_a_1238_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1240_ = v___x_1220_;
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_a_1238_);
lean_dec(v___x_1220_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
if (v_isShared_1241_ == 0)
{
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_a_1238_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
}
else
{
lean_object* v_head_1246_; lean_object* v_tail_1247_; lean_object* v___x_1248_; 
v_head_1246_ = lean_ctor_get(v_a_1208_, 0);
lean_inc(v_head_1246_);
v_tail_1247_ = lean_ctor_get(v_a_1208_, 1);
lean_inc(v_tail_1247_);
lean_dec_ref_known(v_a_1208_, 2);
v___x_1248_ = l_Lean_MVarId_intro(v_a_1206_, v_head_1246_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; lean_object* v_fst_1250_; lean_object* v_snd_1251_; lean_object* v___x_1252_; 
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc(v_a_1249_);
lean_dec_ref_known(v___x_1248_, 1);
v_fst_1250_ = lean_ctor_get(v_a_1249_, 0);
lean_inc(v_fst_1250_);
v_snd_1251_ = lean_ctor_get(v_a_1249_, 1);
lean_inc(v_snd_1251_);
lean_dec(v_a_1249_);
v___x_1252_ = l_Lean_Meta_heqToEq(v_snd_1251_, v_fst_1250_, v_tryToClear_1204_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_);
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
v___x_1256_ = lean_array_push(v_a_1207_, v_fst_1254_);
v_a_1205_ = v_n_1219_;
v_a_1206_ = v_snd_1255_;
v_a_1207_ = v___x_1256_;
v_a_1208_ = v_tail_1247_;
goto _start;
}
else
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1265_; 
lean_dec(v_tail_1247_);
lean_dec(v_n_1219_);
lean_dec_ref(v_a_1207_);
v_a_1258_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1260_ = v___x_1252_;
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1252_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1263_; 
if (v_isShared_1261_ == 0)
{
v___x_1263_ = v___x_1260_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1258_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec(v_tail_1247_);
lean_dec(v_n_1219_);
lean_dec_ref(v_a_1207_);
v_a_1266_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1248_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1248_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go___boxed(lean_object* v_tryToClear_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_){
_start:
{
uint8_t v_tryToClear_boxed_1284_; lean_object* v_res_1285_; 
v_tryToClear_boxed_1284_ = lean_unbox(v_tryToClear_1274_);
v_res_1285_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go(v_tryToClear_boxed_1284_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
lean_dec(v_a_1282_);
lean_dec_ref(v_a_1281_);
lean_dec(v_a_1280_);
lean_dec_ref(v_a_1279_);
return v_res_1285_;
}
}
static lean_object* _init_l_Lean_Meta_injectionIntro___closed__2(void){
_start:
{
lean_object* v_cls_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v_cls_1292_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__1));
v___x_1293_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__0___closed__1));
v___x_1294_ = l_Lean_Name_append(v___x_1293_, v_cls_1292_);
return v___x_1294_;
}
}
static lean_object* _init_l_Lean_Meta_injectionIntro___closed__4(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__3));
v___x_1297_ = l_Lean_stringToMessageData(v___x_1296_);
return v___x_1297_;
}
}
static lean_object* _init_l_Lean_Meta_injectionIntro___closed__6(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__5));
v___x_1300_ = l_Lean_stringToMessageData(v___x_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro(lean_object* v_mvarId_1301_, lean_object* v_numEqs_1302_, lean_object* v_newNames_1303_, uint8_t v_tryToClear_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_){
_start:
{
lean_object* v___y_1311_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v_toCold_1317_; lean_object* v_options_1318_; uint8_t v_hasTrace_1319_; 
v_toCold_1317_ = lean_ctor_get(v_a_1307_, 0);
v_options_1318_ = lean_ctor_get(v_toCold_1317_, 2);
v_hasTrace_1319_ = lean_ctor_get_uint8(v_options_1318_, sizeof(void*)*1);
if (v_hasTrace_1319_ == 0)
{
v___y_1311_ = v_a_1305_;
v___y_1312_ = v_a_1306_;
v___y_1313_ = v_a_1307_;
v___y_1314_ = v_a_1308_;
goto v___jp_1310_;
}
else
{
lean_object* v_inheritedTraceOptions_1320_; lean_object* v_cls_1321_; lean_object* v___x_1322_; uint8_t v___x_1323_; 
v_inheritedTraceOptions_1320_ = lean_ctor_get(v_toCold_1317_, 11);
v_cls_1321_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__1));
v___x_1322_ = lean_obj_once(&l_Lean_Meta_injectionIntro___closed__2, &l_Lean_Meta_injectionIntro___closed__2_once, _init_l_Lean_Meta_injectionIntro___closed__2);
v___x_1323_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1320_, v_options_1318_, v___x_1322_);
if (v___x_1323_ == 0)
{
v___y_1311_ = v_a_1305_;
v___y_1312_ = v_a_1306_;
v___y_1313_ = v_a_1307_;
v___y_1314_ = v_a_1308_;
goto v___jp_1310_;
}
else
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1324_ = lean_obj_once(&l_Lean_Meta_injectionIntro___closed__4, &l_Lean_Meta_injectionIntro___closed__4_once, _init_l_Lean_Meta_injectionIntro___closed__4);
lean_inc(v_numEqs_1302_);
v___x_1325_ = l_Nat_reprFast(v_numEqs_1302_);
v___x_1326_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1325_);
v___x_1327_ = l_Lean_MessageData_ofFormat(v___x_1326_);
v___x_1328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1324_);
lean_ctor_set(v___x_1328_, 1, v___x_1327_);
v___x_1329_ = lean_obj_once(&l_Lean_Meta_injectionIntro___closed__6, &l_Lean_Meta_injectionIntro___closed__6_once, _init_l_Lean_Meta_injectionIntro___closed__6);
v___x_1330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1328_);
lean_ctor_set(v___x_1330_, 1, v___x_1329_);
lean_inc(v_mvarId_1301_);
v___x_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1331_, 0, v_mvarId_1301_);
v___x_1332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1330_);
lean_ctor_set(v___x_1332_, 1, v___x_1331_);
v___x_1333_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v_cls_1321_, v___x_1332_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_dec_ref_known(v___x_1333_, 1);
v___y_1311_ = v_a_1305_;
v___y_1312_ = v_a_1306_;
v___y_1313_ = v_a_1307_;
v___y_1314_ = v_a_1308_;
goto v___jp_1310_;
}
else
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1341_; 
lean_dec(v_newNames_1303_);
lean_dec(v_numEqs_1302_);
lean_dec(v_mvarId_1301_);
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1336_ = v___x_1333_;
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1333_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1339_; 
if (v_isShared_1337_ == 0)
{
v___x_1339_ = v___x_1336_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_a_1334_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
}
v___jp_1310_:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__0));
v___x_1316_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go(v_tryToClear_1304_, v_numEqs_1302_, v_mvarId_1301_, v___x_1315_, v_newNames_1303_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
return v___x_1316_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro___boxed(lean_object* v_mvarId_1342_, lean_object* v_numEqs_1343_, lean_object* v_newNames_1344_, lean_object* v_tryToClear_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_){
_start:
{
uint8_t v_tryToClear_boxed_1351_; lean_object* v_res_1352_; 
v_tryToClear_boxed_1351_ = lean_unbox(v_tryToClear_1345_);
v_res_1352_ = l_Lean_Meta_injectionIntro(v_mvarId_1342_, v_numEqs_1343_, v_newNames_1344_, v_tryToClear_boxed_1351_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
lean_dec(v_a_1349_);
lean_dec_ref(v_a_1348_);
lean_dec(v_a_1347_);
lean_dec_ref(v_a_1346_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injection(lean_object* v_mvarId_1353_, lean_object* v_fvarId_1354_, lean_object* v_newNames_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_){
_start:
{
lean_object* v___x_1361_; 
v___x_1361_ = l_Lean_Meta_injectionCore(v_mvarId_1353_, v_fvarId_1354_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1374_; 
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1364_ = v___x_1361_;
v_isShared_1365_ = v_isSharedCheck_1374_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1361_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1374_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
if (lean_obj_tag(v_a_1362_) == 0)
{
lean_object* v___x_1366_; lean_object* v___x_1368_; 
lean_dec(v_newNames_1355_);
v___x_1366_ = lean_box(0);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 0, v___x_1366_);
v___x_1368_ = v___x_1364_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1366_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
else
{
lean_object* v_mvarId_1370_; lean_object* v_numNewEqs_1371_; uint8_t v___x_1372_; lean_object* v___x_1373_; 
lean_del_object(v___x_1364_);
v_mvarId_1370_ = lean_ctor_get(v_a_1362_, 0);
lean_inc(v_mvarId_1370_);
v_numNewEqs_1371_ = lean_ctor_get(v_a_1362_, 1);
lean_inc(v_numNewEqs_1371_);
lean_dec_ref_known(v_a_1362_, 2);
v___x_1372_ = 1;
v___x_1373_ = l_Lean_Meta_injectionIntro(v_mvarId_1370_, v_numNewEqs_1371_, v_newNames_1355_, v___x_1372_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_);
return v___x_1373_;
}
}
}
else
{
lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1382_; 
lean_dec(v_newNames_1355_);
v_a_1375_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1377_ = v___x_1361_;
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v___x_1361_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1380_; 
if (v_isShared_1378_ == 0)
{
v___x_1380_ = v___x_1377_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_a_1375_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injection___boxed(lean_object* v_mvarId_1383_, lean_object* v_fvarId_1384_, lean_object* v_newNames_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l_Lean_Meta_injection(v_mvarId_1383_, v_fvarId_1384_, v_newNames_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_);
lean_dec(v_a_1389_);
lean_dec_ref(v_a_1388_);
lean_dec(v_a_1387_);
lean_dec_ref(v_a_1386_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorIdx(lean_object* v_x_1392_){
_start:
{
if (lean_obj_tag(v_x_1392_) == 0)
{
lean_object* v___x_1393_; 
v___x_1393_ = lean_unsigned_to_nat(0u);
return v___x_1393_;
}
else
{
lean_object* v___x_1394_; 
v___x_1394_ = lean_unsigned_to_nat(1u);
return v___x_1394_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorIdx___boxed(lean_object* v_x_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Lean_Meta_InjectionsResult_ctorIdx(v_x_1395_);
lean_dec(v_x_1395_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorElim___redArg(lean_object* v_t_1397_, lean_object* v_k_1398_){
_start:
{
if (lean_obj_tag(v_t_1397_) == 0)
{
return v_k_1398_;
}
else
{
lean_object* v_mvarId_1399_; lean_object* v_remainingNames_1400_; lean_object* v_forbidden_1401_; lean_object* v___x_1402_; 
v_mvarId_1399_ = lean_ctor_get(v_t_1397_, 0);
lean_inc(v_mvarId_1399_);
v_remainingNames_1400_ = lean_ctor_get(v_t_1397_, 1);
lean_inc(v_remainingNames_1400_);
v_forbidden_1401_ = lean_ctor_get(v_t_1397_, 2);
lean_inc(v_forbidden_1401_);
lean_dec_ref_known(v_t_1397_, 3);
v___x_1402_ = lean_apply_3(v_k_1398_, v_mvarId_1399_, v_remainingNames_1400_, v_forbidden_1401_);
return v___x_1402_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorElim(lean_object* v_motive_1403_, lean_object* v_ctorIdx_1404_, lean_object* v_t_1405_, lean_object* v_h_1406_, lean_object* v_k_1407_){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1405_, v_k_1407_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorElim___boxed(lean_object* v_motive_1409_, lean_object* v_ctorIdx_1410_, lean_object* v_t_1411_, lean_object* v_h_1412_, lean_object* v_k_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l_Lean_Meta_InjectionsResult_ctorElim(v_motive_1409_, v_ctorIdx_1410_, v_t_1411_, v_h_1412_, v_k_1413_);
lean_dec(v_ctorIdx_1410_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_solved_elim___redArg(lean_object* v_t_1415_, lean_object* v_solved_1416_){
_start:
{
lean_object* v___x_1417_; 
v___x_1417_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1415_, v_solved_1416_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_solved_elim(lean_object* v_motive_1418_, lean_object* v_t_1419_, lean_object* v_h_1420_, lean_object* v_solved_1421_){
_start:
{
lean_object* v___x_1422_; 
v___x_1422_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1419_, v_solved_1421_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_subgoal_elim___redArg(lean_object* v_t_1423_, lean_object* v_subgoal_1424_){
_start:
{
lean_object* v___x_1425_; 
v___x_1425_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1423_, v_subgoal_1424_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_subgoal_elim(lean_object* v_motive_1426_, lean_object* v_t_1427_, lean_object* v_h_1428_, lean_object* v_subgoal_1429_){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1427_, v_subgoal_1429_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(lean_object* v_x_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = l_Lean_Meta_saveState___redArg(v___y_1433_, v___y_1435_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1438_; lean_object* v___x_1439_; 
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc(v_a_1438_);
lean_dec_ref_known(v___x_1437_, 1);
lean_inc(v___y_1435_);
lean_inc_ref(v___y_1434_);
lean_inc(v___y_1433_);
lean_inc_ref(v___y_1432_);
v___x_1439_ = lean_apply_5(v_x_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, lean_box(0));
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_dec(v_a_1438_);
return v___x_1439_;
}
else
{
lean_object* v_a_1440_; uint8_t v___y_1442_; uint8_t v___x_1460_; 
v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_a_1440_);
v___x_1460_ = l_Lean_Exception_isInterrupt(v_a_1440_);
if (v___x_1460_ == 0)
{
uint8_t v___x_1461_; 
lean_inc(v_a_1440_);
v___x_1461_ = l_Lean_Exception_isRuntime(v_a_1440_);
v___y_1442_ = v___x_1461_;
goto v___jp_1441_;
}
else
{
v___y_1442_ = v___x_1460_;
goto v___jp_1441_;
}
v___jp_1441_:
{
if (v___y_1442_ == 0)
{
lean_object* v___x_1443_; 
lean_dec_ref_known(v___x_1439_, 1);
v___x_1443_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1438_, v___y_1433_, v___y_1435_);
lean_dec(v_a_1438_);
if (lean_obj_tag(v___x_1443_) == 0)
{
lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1450_ == 0)
{
lean_object* v_unused_1451_; 
v_unused_1451_ = lean_ctor_get(v___x_1443_, 0);
lean_dec(v_unused_1451_);
v___x_1445_ = v___x_1443_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_dec(v___x_1443_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
lean_ctor_set_tag(v___x_1445_, 1);
lean_ctor_set(v___x_1445_, 0, v_a_1440_);
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1440_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
else
{
lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1459_; 
lean_dec(v_a_1440_);
v_a_1452_ = lean_ctor_get(v___x_1443_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1454_ = v___x_1443_;
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1443_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
if (v_isShared_1455_ == 0)
{
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_a_1452_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
}
else
{
lean_dec(v_a_1440_);
lean_dec(v_a_1438_);
return v___x_1439_;
}
}
}
}
else
{
lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1469_; 
lean_dec_ref(v_x_1431_);
v_a_1462_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1464_ = v___x_1437_;
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_dec(v___x_1437_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1467_; 
if (v_isShared_1465_ == 0)
{
v___x_1467_ = v___x_1464_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_a_1462_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg___boxed(lean_object* v_x_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(v_x_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1(lean_object* v_00_u03b1_1477_, lean_object* v_x_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v___x_1484_; 
v___x_1484_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(v_x_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___boxed(lean_object* v_00_u03b1_1485_, lean_object* v_x_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1(v_00_u03b1_1485_, v_x_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
return v_res_1492_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(lean_object* v_k_1493_, lean_object* v_t_1494_){
_start:
{
if (lean_obj_tag(v_t_1494_) == 0)
{
lean_object* v_k_1495_; lean_object* v_l_1496_; lean_object* v_r_1497_; uint8_t v___x_1498_; 
v_k_1495_ = lean_ctor_get(v_t_1494_, 1);
v_l_1496_ = lean_ctor_get(v_t_1494_, 3);
v_r_1497_ = lean_ctor_get(v_t_1494_, 4);
v___x_1498_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1493_, v_k_1495_);
switch(v___x_1498_)
{
case 0:
{
v_t_1494_ = v_l_1496_;
goto _start;
}
case 1:
{
uint8_t v___x_1500_; 
v___x_1500_ = 1;
return v___x_1500_;
}
default: 
{
v_t_1494_ = v_r_1497_;
goto _start;
}
}
}
else
{
uint8_t v___x_1502_; 
v___x_1502_ = 0;
return v___x_1502_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg___boxed(lean_object* v_k_1503_, lean_object* v_t_1504_){
_start:
{
uint8_t v_res_1505_; lean_object* v_r_1506_; 
v_res_1505_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(v_k_1503_, v_t_1504_);
lean_dec(v_t_1504_);
lean_dec(v_k_1503_);
v_r_1506_ = lean_box(v_res_1505_);
return v_r_1506_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4(void){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1513_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__3));
v___x_1514_ = l_Lean_MessageData_ofFormat(v___x_1513_);
return v___x_1514_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5(void){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1515_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4, &l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4_once, _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4);
v___x_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1515_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0___boxed(lean_object* v_mvarId_1517_, lean_object* v_head_1518_, lean_object* v_newNames_1519_, lean_object* v_tail_1520_, lean_object* v_forbidden_1521_, lean_object* v_n_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0(v_mvarId_1517_, v_head_1518_, v_newNames_1519_, v_tail_1520_, v_forbidden_1521_, v_n_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go(lean_object* v_depth_1529_, lean_object* v_fvarIds_1530_, lean_object* v_mvarId_1531_, lean_object* v_newNames_1532_, lean_object* v_forbidden_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_){
_start:
{
lean_object* v_zero_1539_; uint8_t v_isZero_1540_; 
v_zero_1539_ = lean_unsigned_to_nat(0u);
v_isZero_1540_ = lean_nat_dec_eq(v_depth_1529_, v_zero_1539_);
if (v_isZero_1540_ == 1)
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
lean_dec(v_forbidden_1533_);
lean_dec(v_newNames_1532_);
lean_dec(v_fvarIds_1530_);
lean_dec(v_depth_1529_);
v___x_1541_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__1));
v___x_1542_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5, &l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5_once, _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5);
v___x_1543_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1541_, v_mvarId_1531_, v___x_1542_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_);
return v___x_1543_;
}
else
{
if (lean_obj_tag(v_fvarIds_1530_) == 0)
{
lean_object* v___x_1544_; lean_object* v___x_1545_; 
lean_dec(v_depth_1529_);
v___x_1544_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1544_, 0, v_mvarId_1531_);
lean_ctor_set(v___x_1544_, 1, v_newNames_1532_);
lean_ctor_set(v___x_1544_, 2, v_forbidden_1533_);
v___x_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1544_);
return v___x_1545_;
}
else
{
lean_object* v_head_1546_; lean_object* v_tail_1547_; lean_object* v_one_1548_; lean_object* v_n_1549_; lean_object* v___x_1550_; lean_object* v___y_1552_; uint8_t v___y_1553_; uint8_t v___x_1555_; 
v_head_1546_ = lean_ctor_get(v_fvarIds_1530_, 0);
lean_inc(v_head_1546_);
v_tail_1547_ = lean_ctor_get(v_fvarIds_1530_, 1);
lean_inc(v_tail_1547_);
lean_dec_ref_known(v_fvarIds_1530_, 2);
v_one_1548_ = lean_unsigned_to_nat(1u);
v_n_1549_ = lean_nat_sub(v_depth_1529_, v_one_1548_);
lean_dec(v_depth_1529_);
v___x_1550_ = lean_nat_add(v_n_1549_, v_one_1548_);
v___x_1555_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(v_head_1546_, v_forbidden_1533_);
if (v___x_1555_ == 0)
{
lean_object* v___f_1556_; lean_object* v___x_1557_; 
lean_inc(v_forbidden_1533_);
lean_inc(v_tail_1547_);
lean_inc(v_newNames_1532_);
lean_inc(v_head_1546_);
lean_inc(v_mvarId_1531_);
v___f_1556_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0___boxed), 11, 6);
lean_closure_set(v___f_1556_, 0, v_mvarId_1531_);
lean_closure_set(v___f_1556_, 1, v_head_1546_);
lean_closure_set(v___f_1556_, 2, v_newNames_1532_);
lean_closure_set(v___f_1556_, 3, v_tail_1547_);
lean_closure_set(v___f_1556_, 4, v_forbidden_1533_);
lean_closure_set(v___f_1556_, 5, v_n_1549_);
v___x_1557_ = l_Lean_FVarId_getType___redArg(v_head_1546_, v_a_1534_, v_a_1536_, v_a_1537_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; lean_object* v___x_1559_; 
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_a_1558_);
lean_dec_ref_known(v___x_1557_, 1);
v___x_1559_ = l_Lean_Meta_matchEqHEq_x3f(v_a_1558_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v_a_1560_; 
v_a_1560_ = lean_ctor_get(v___x_1559_, 0);
lean_inc(v_a_1560_);
lean_dec_ref_known(v___x_1559_, 1);
if (lean_obj_tag(v_a_1560_) == 1)
{
lean_object* v_val_1561_; lean_object* v_snd_1562_; lean_object* v_fst_1563_; lean_object* v_snd_1564_; lean_object* v___x_1565_; 
v_val_1561_ = lean_ctor_get(v_a_1560_, 0);
lean_inc(v_val_1561_);
lean_dec_ref_known(v_a_1560_, 1);
v_snd_1562_ = lean_ctor_get(v_val_1561_, 1);
lean_inc(v_snd_1562_);
lean_dec(v_val_1561_);
v_fst_1563_ = lean_ctor_get(v_snd_1562_, 0);
lean_inc(v_fst_1563_);
v_snd_1564_ = lean_ctor_get(v_snd_1562_, 1);
lean_inc(v_snd_1564_);
lean_dec(v_snd_1562_);
lean_inc(v_a_1537_);
lean_inc_ref(v_a_1536_);
lean_inc(v_a_1535_);
lean_inc_ref(v_a_1534_);
v___x_1565_ = lean_whnf(v_fst_1563_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; lean_object* v___x_1567_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_a_1566_);
lean_dec_ref_known(v___x_1565_, 1);
lean_inc(v_a_1537_);
lean_inc_ref(v_a_1536_);
lean_inc(v_a_1535_);
lean_inc_ref(v_a_1534_);
v___x_1567_ = lean_whnf(v_snd_1564_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; uint8_t v___y_1570_; uint8_t v___x_1576_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_a_1568_);
lean_dec_ref_known(v___x_1567_, 1);
v___x_1576_ = l_Lean_Expr_isRawNatLit(v_a_1566_);
lean_dec(v_a_1566_);
if (v___x_1576_ == 0)
{
lean_dec(v_a_1568_);
v___y_1570_ = v___x_1555_;
goto v___jp_1569_;
}
else
{
uint8_t v___x_1577_; 
v___x_1577_ = l_Lean_Expr_isRawNatLit(v_a_1568_);
lean_dec(v_a_1568_);
v___y_1570_ = v___x_1577_;
goto v___jp_1569_;
}
v___jp_1569_:
{
if (v___y_1570_ == 0)
{
lean_object* v___x_1571_; 
v___x_1571_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(v___f_1556_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_dec(v___x_1550_);
lean_dec(v_tail_1547_);
lean_dec(v_forbidden_1533_);
lean_dec(v_newNames_1532_);
lean_dec(v_mvarId_1531_);
return v___x_1571_;
}
else
{
lean_object* v_a_1572_; uint8_t v___x_1573_; 
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
lean_inc(v_a_1572_);
v___x_1573_ = l_Lean_Exception_isInterrupt(v_a_1572_);
if (v___x_1573_ == 0)
{
uint8_t v___x_1574_; 
v___x_1574_ = l_Lean_Exception_isRuntime(v_a_1572_);
v___y_1552_ = v___x_1571_;
v___y_1553_ = v___x_1574_;
goto v___jp_1551_;
}
else
{
lean_dec(v_a_1572_);
v___y_1552_ = v___x_1571_;
v___y_1553_ = v___x_1573_;
goto v___jp_1551_;
}
}
}
else
{
lean_dec_ref(v___f_1556_);
v_depth_1529_ = v___x_1550_;
v_fvarIds_1530_ = v_tail_1547_;
goto _start;
}
}
}
else
{
lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1585_; 
lean_dec(v_a_1566_);
lean_dec_ref(v___f_1556_);
lean_dec(v___x_1550_);
lean_dec(v_tail_1547_);
lean_dec(v_forbidden_1533_);
lean_dec(v_newNames_1532_);
lean_dec(v_mvarId_1531_);
v_a_1578_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1580_ = v___x_1567_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1567_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1583_; 
if (v_isShared_1581_ == 0)
{
v___x_1583_ = v___x_1580_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_a_1578_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
else
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
lean_dec(v_snd_1564_);
lean_dec_ref(v___f_1556_);
lean_dec(v___x_1550_);
lean_dec(v_tail_1547_);
lean_dec(v_forbidden_1533_);
lean_dec(v_newNames_1532_);
lean_dec(v_mvarId_1531_);
v_a_1586_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1588_ = v___x_1565_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1565_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1589_ == 0)
{
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1586_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
}
else
{
lean_dec(v_a_1560_);
lean_dec_ref(v___f_1556_);
v_depth_1529_ = v___x_1550_;
v_fvarIds_1530_ = v_tail_1547_;
goto _start;
}
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
lean_dec_ref(v___f_1556_);
lean_dec(v___x_1550_);
lean_dec(v_tail_1547_);
lean_dec(v_forbidden_1533_);
lean_dec(v_newNames_1532_);
lean_dec(v_mvarId_1531_);
v_a_1595_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1597_ = v___x_1559_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1559_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1595_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
else
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
lean_dec_ref(v___f_1556_);
lean_dec(v___x_1550_);
lean_dec(v_tail_1547_);
lean_dec(v_forbidden_1533_);
lean_dec(v_newNames_1532_);
lean_dec(v_mvarId_1531_);
v_a_1603_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1557_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1557_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
else
{
lean_dec(v_n_1549_);
lean_dec(v_head_1546_);
v_depth_1529_ = v___x_1550_;
v_fvarIds_1530_ = v_tail_1547_;
goto _start;
}
v___jp_1551_:
{
if (v___y_1553_ == 0)
{
lean_dec_ref(v___y_1552_);
v_depth_1529_ = v___x_1550_;
v_fvarIds_1530_ = v_tail_1547_;
goto _start;
}
else
{
lean_dec(v___x_1550_);
lean_dec(v_tail_1547_);
lean_dec(v_forbidden_1533_);
lean_dec(v_newNames_1532_);
lean_dec(v_mvarId_1531_);
return v___y_1552_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___boxed(lean_object* v_depth_1612_, lean_object* v_fvarIds_1613_, lean_object* v_mvarId_1614_, lean_object* v_newNames_1615_, lean_object* v_forbidden_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go(v_depth_1612_, v_fvarIds_1613_, v_mvarId_1614_, v_newNames_1615_, v_forbidden_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_);
lean_dec(v_a_1620_);
lean_dec_ref(v_a_1619_);
lean_dec(v_a_1618_);
lean_dec_ref(v_a_1617_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0(lean_object* v_mvarId_1623_, lean_object* v_head_1624_, lean_object* v_newNames_1625_, lean_object* v_tail_1626_, lean_object* v_forbidden_1627_, lean_object* v_n_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
lean_object* v___x_1634_; 
lean_inc(v_head_1624_);
v___x_1634_ = l_Lean_Meta_injection(v_mvarId_1623_, v_head_1624_, v_newNames_1625_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1651_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1637_ = v___x_1634_;
v_isShared_1638_ = v_isSharedCheck_1651_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1634_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1651_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
if (lean_obj_tag(v_a_1635_) == 0)
{
lean_object* v___x_1639_; lean_object* v___x_1641_; 
lean_dec(v_n_1628_);
lean_dec(v_forbidden_1627_);
lean_dec(v_tail_1626_);
lean_dec(v_head_1624_);
v___x_1639_ = lean_box(0);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v___x_1639_);
v___x_1641_ = v___x_1637_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1639_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
else
{
lean_object* v_mvarId_1643_; lean_object* v_newEqs_1644_; lean_object* v_remainingNames_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
lean_del_object(v___x_1637_);
v_mvarId_1643_ = lean_ctor_get(v_a_1635_, 0);
lean_inc_n(v_mvarId_1643_, 2);
v_newEqs_1644_ = lean_ctor_get(v_a_1635_, 1);
lean_inc_ref(v_newEqs_1644_);
v_remainingNames_1645_ = lean_ctor_get(v_a_1635_, 2);
lean_inc(v_remainingNames_1645_);
lean_dec_ref_known(v_a_1635_, 3);
v___x_1646_ = lean_array_to_list(v_newEqs_1644_);
v___x_1647_ = l_List_appendTR___redArg(v___x_1646_, v_tail_1626_);
v___x_1648_ = l_Lean_FVarIdSet_insert(v_forbidden_1627_, v_head_1624_);
v___x_1649_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___boxed), 10, 5);
lean_closure_set(v___x_1649_, 0, v_n_1628_);
lean_closure_set(v___x_1649_, 1, v___x_1647_);
lean_closure_set(v___x_1649_, 2, v_mvarId_1643_);
lean_closure_set(v___x_1649_, 3, v_remainingNames_1645_);
lean_closure_set(v___x_1649_, 4, v___x_1648_);
v___x_1650_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg(v_mvarId_1643_, v___x_1649_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
return v___x_1650_;
}
}
}
else
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_dec(v_n_1628_);
lean_dec(v_forbidden_1627_);
lean_dec(v_tail_1626_);
lean_dec(v_head_1624_);
v_a_1652_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1634_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1634_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0(lean_object* v_00_u03b2_1660_, lean_object* v_k_1661_, lean_object* v_t_1662_){
_start:
{
uint8_t v___x_1663_; 
v___x_1663_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(v_k_1661_, v_t_1662_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___boxed(lean_object* v_00_u03b2_1664_, lean_object* v_k_1665_, lean_object* v_t_1666_){
_start:
{
uint8_t v_res_1667_; lean_object* v_r_1668_; 
v_res_1667_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0(v_00_u03b2_1664_, v_k_1665_, v_t_1666_);
lean_dec(v_t_1666_);
lean_dec(v_k_1665_);
v_r_1668_ = lean_box(v_res_1667_);
return v_r_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections___lam__0(lean_object* v_maxDepth_1669_, lean_object* v_mvarId_1670_, lean_object* v_newNames_1671_, lean_object* v_forbidden_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
lean_object* v_lctx_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v_lctx_1678_ = lean_ctor_get(v___y_1673_, 2);
v___x_1679_ = l_Lean_LocalContext_getFVarIds(v_lctx_1678_);
v___x_1680_ = lean_array_to_list(v___x_1679_);
v___x_1681_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go(v_maxDepth_1669_, v___x_1680_, v_mvarId_1670_, v_newNames_1671_, v_forbidden_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections___lam__0___boxed(lean_object* v_maxDepth_1682_, lean_object* v_mvarId_1683_, lean_object* v_newNames_1684_, lean_object* v_forbidden_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_Lean_Meta_injections___lam__0(v_maxDepth_1682_, v_mvarId_1683_, v_newNames_1684_, v_forbidden_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections(lean_object* v_mvarId_1692_, lean_object* v_newNames_1693_, lean_object* v_maxDepth_1694_, lean_object* v_forbidden_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_){
_start:
{
lean_object* v___f_1701_; lean_object* v___x_1702_; 
lean_inc(v_mvarId_1692_);
v___f_1701_ = lean_alloc_closure((void*)(l_Lean_Meta_injections___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1701_, 0, v_maxDepth_1694_);
lean_closure_set(v___f_1701_, 1, v_mvarId_1692_);
lean_closure_set(v___f_1701_, 2, v_newNames_1693_);
lean_closure_set(v___f_1701_, 3, v_forbidden_1695_);
v___x_1702_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg(v_mvarId_1692_, v___f_1701_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections___boxed(lean_object* v_mvarId_1703_, lean_object* v_newNames_1704_, lean_object* v_maxDepth_1705_, lean_object* v_forbidden_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Lean_Meta_injections(v_mvarId_1703_, v_newNames_1704_, v_maxDepth_1705_, v_forbidden_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
lean_dec(v_a_1710_);
lean_dec_ref(v_a_1709_);
lean_dec(v_a_1708_);
lean_dec_ref(v_a_1707_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1769_; uint8_t v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1769_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__1));
v___x_1770_ = 0;
v___x_1771_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__22_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_));
v___x_1772_ = l_Lean_registerTraceClass(v___x_1769_, v___x_1770_, v___x_1771_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2____boxed(lean_object* v_a_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l___private_Lean_Meta_Tactic_Injection_0__initFn_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_();
return v_res_1774_;
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
