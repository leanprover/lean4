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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResultCore_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResultCore_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorIdx___impl___boxed(lean_object*);
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
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg___lam__0(lean_object* v_k_1_, lean_object* v_b_2_, lean_object* v_c_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_){
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
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1_ = stack[0].m_obj;
lean_object* v_b_2_ = stack[1].m_obj;
lean_object* v_c_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v___y_7_ = stack[6].m_obj;
lean_object* v_res_10_;
v_res_10_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg___lam__0(v_k_1_, v_b_2_, v_c_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_);
stack->m_obj
 = v_res_10_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg___lam__0___boxed(lean_object* v_k_11_, lean_object* v_b_12_, lean_object* v_c_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg___lam__0(v_k_11_, v_b_12_, v_c_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_);
lean_dec(v___y_17_);
lean_dec_ref(v___y_16_);
lean_dec(v___y_15_);
lean_dec_ref(v___y_14_);
return v_res_19_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg(lean_object* v_type_20_, lean_object* v_k_21_, uint8_t v_cleanupAnnotations_22_, uint8_t v_whnfType_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v___f_29_; lean_object* v___x_30_; 
v___f_29_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_29_, 0, v_k_21_);
v___x_30_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_20_, v___f_29_, v_cleanupAnnotations_22_, v_whnfType_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
if (lean_obj_tag(v___x_30_) == 0)
{
lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_38_; 
v_a_31_ = lean_ctor_get(v___x_30_, 0);
v_isSharedCheck_38_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_38_ == 0)
{
v___x_33_ = v___x_30_;
v_isShared_34_ = v_isSharedCheck_38_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_a_31_);
lean_dec(v___x_30_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_38_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_36_; 
if (v_isShared_34_ == 0)
{
v___x_36_ = v___x_33_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v_a_31_);
v___x_36_ = v_reuseFailAlloc_37_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
return v___x_36_;
}
}
}
else
{
lean_object* v_a_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_46_; 
v_a_39_ = lean_ctor_get(v___x_30_, 0);
v_isSharedCheck_46_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_46_ == 0)
{
v___x_41_ = v___x_30_;
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_a_39_);
lean_dec(v___x_30_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___x_44_; 
if (v_isShared_42_ == 0)
{
v___x_44_ = v___x_41_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_a_39_);
v___x_44_ = v_reuseFailAlloc_45_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
return v___x_44_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_20_ = stack[0].m_obj;
lean_object* v_k_21_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_22_ = stack[2].m_num;
uint8_t v_whnfType_23_ = stack[3].m_num;
lean_object* v___y_24_ = stack[4].m_obj;
lean_object* v___y_25_ = stack[5].m_obj;
lean_object* v___y_26_ = stack[6].m_obj;
lean_object* v___y_27_ = stack[7].m_obj;
lean_object* v_res_47_;
v_res_47_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg(v_type_20_, v_k_21_, v_cleanupAnnotations_22_, v_whnfType_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
stack->m_obj
 = v_res_47_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg___boxed(lean_object* v_type_48_, lean_object* v_k_49_, lean_object* v_cleanupAnnotations_50_, lean_object* v_whnfType_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_57_; uint8_t v_whnfType_boxed_58_; lean_object* v_res_59_; 
v_cleanupAnnotations_boxed_57_ = lean_unbox(v_cleanupAnnotations_50_);
v_whnfType_boxed_58_ = lean_unbox(v_whnfType_51_);
v_res_59_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg(v_type_48_, v_k_49_, v_cleanupAnnotations_boxed_57_, v_whnfType_boxed_58_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
return v_res_59_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1(lean_object* v_00_u03b1_60_, lean_object* v_type_61_, lean_object* v_k_62_, uint8_t v_cleanupAnnotations_63_, uint8_t v_whnfType_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg(v_type_61_, v_k_62_, v_cleanupAnnotations_63_, v_whnfType_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_);
return v___x_70_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_61_ = stack[1].m_obj;
lean_object* v_k_62_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_63_ = stack[3].m_num;
uint8_t v_whnfType_64_ = stack[4].m_num;
lean_object* v___y_65_ = stack[5].m_obj;
lean_object* v___y_66_ = stack[6].m_obj;
lean_object* v___y_67_ = stack[7].m_obj;
lean_object* v___y_68_ = stack[8].m_obj;
lean_object* v_res_71_;
v_res_71_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1(lean_box(0), v_type_61_, v_k_62_, v_cleanupAnnotations_63_, v_whnfType_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_);
stack->m_obj
 = v_res_71_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___boxed(lean_object* v_00_u03b1_72_, lean_object* v_type_73_, lean_object* v_k_74_, lean_object* v_cleanupAnnotations_75_, lean_object* v_whnfType_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_82_; uint8_t v_whnfType_boxed_83_; lean_object* v_res_84_; 
v_cleanupAnnotations_boxed_82_ = lean_unbox(v_cleanupAnnotations_75_);
v_whnfType_boxed_83_ = lean_unbox(v_whnfType_76_);
v_res_84_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1(v_00_u03b1_72_, v_type_73_, v_k_74_, v_cleanupAnnotations_boxed_82_, v_whnfType_boxed_83_, v___y_77_, v___y_78_, v___y_79_, v___y_80_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
lean_dec(v___y_78_);
lean_dec_ref(v___y_77_);
return v_res_84_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCtorNumPropFields_spec__0___redArg(lean_object* v_upperBound_85_, lean_object* v_ctorInfo_86_, lean_object* v_xs_87_, lean_object* v_a_88_, lean_object* v_b_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
lean_object* v_a_96_; uint8_t v___x_100_; 
v___x_100_ = lean_nat_dec_lt(v_a_88_, v_upperBound_85_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; 
lean_dec(v_a_88_);
v___x_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_101_, 0, v_b_89_);
return v___x_101_;
}
else
{
lean_object* v_numParams_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v_numParams_102_ = lean_ctor_get(v_ctorInfo_86_, 3);
v___x_103_ = l_Lean_instInhabitedExpr;
v___x_104_ = lean_nat_add(v_numParams_102_, v_a_88_);
v___x_105_ = lean_array_get_borrowed(v___x_103_, v_xs_87_, v___x_104_);
lean_dec(v___x_104_);
lean_inc(v___y_93_);
lean_inc_ref(v___y_92_);
lean_inc(v___y_91_);
lean_inc_ref(v___y_90_);
lean_inc(v___x_105_);
v___x_106_ = lean_infer_type(v___x_105_, v___y_90_, v___y_91_, v___y_92_, v___y_93_);
if (lean_obj_tag(v___x_106_) == 0)
{
lean_object* v_a_107_; lean_object* v___x_108_; 
v_a_107_ = lean_ctor_get(v___x_106_, 0);
lean_inc(v_a_107_);
lean_dec_ref_known(v___x_106_, 1);
v___x_108_ = l_Lean_Meta_isProp(v_a_107_, v___y_90_, v___y_91_, v___y_92_, v___y_93_);
if (lean_obj_tag(v___x_108_) == 0)
{
lean_object* v_a_109_; uint8_t v___x_110_; 
v_a_109_ = lean_ctor_get(v___x_108_, 0);
lean_inc(v_a_109_);
lean_dec_ref_known(v___x_108_, 1);
v___x_110_ = lean_unbox(v_a_109_);
lean_dec(v_a_109_);
if (v___x_110_ == 0)
{
v_a_96_ = v_b_89_;
goto v___jp_95_;
}
else
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = lean_unsigned_to_nat(1u);
v___x_112_ = lean_nat_add(v_b_89_, v___x_111_);
lean_dec(v_b_89_);
v_a_96_ = v___x_112_;
goto v___jp_95_;
}
}
else
{
lean_object* v_a_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_120_; 
lean_dec(v_b_89_);
lean_dec(v_a_88_);
v_a_113_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_120_ == 0)
{
v___x_115_ = v___x_108_;
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_a_113_);
lean_dec(v___x_108_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_118_; 
if (v_isShared_116_ == 0)
{
v___x_118_ = v___x_115_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_a_113_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
}
else
{
lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_128_; 
lean_dec(v_b_89_);
lean_dec(v_a_88_);
v_a_121_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_128_ == 0)
{
v___x_123_ = v___x_106_;
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_106_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_126_; 
if (v_isShared_124_ == 0)
{
v___x_126_ = v___x_123_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_a_121_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
v___jp_95_:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = lean_unsigned_to_nat(1u);
v___x_98_ = lean_nat_add(v_a_88_, v___x_97_);
lean_dec(v_a_88_);
v_a_88_ = v___x_98_;
v_b_89_ = v_a_96_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCtorNumPropFields_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_85_ = stack[0].m_obj;
lean_object* v_ctorInfo_86_ = stack[1].m_obj;
lean_object* v_xs_87_ = stack[2].m_obj;
lean_object* v_a_88_ = stack[3].m_obj;
lean_object* v_b_89_ = stack[4].m_obj;
lean_object* v___y_90_ = stack[5].m_obj;
lean_object* v___y_91_ = stack[6].m_obj;
lean_object* v___y_92_ = stack[7].m_obj;
lean_object* v___y_93_ = stack[8].m_obj;
lean_object* v_res_129_;
v_res_129_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCtorNumPropFields_spec__0___redArg(v_upperBound_85_, v_ctorInfo_86_, v_xs_87_, v_a_88_, v_b_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_);
stack->m_obj
 = v_res_129_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCtorNumPropFields_spec__0___redArg___boxed(lean_object* v_upperBound_130_, lean_object* v_ctorInfo_131_, lean_object* v_xs_132_, lean_object* v_a_133_, lean_object* v_b_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCtorNumPropFields_spec__0___redArg(v_upperBound_130_, v_ctorInfo_131_, v_xs_132_, v_a_133_, v_b_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec_ref(v_xs_132_);
lean_dec_ref(v_ctorInfo_131_);
lean_dec(v_upperBound_130_);
return v_res_140_;
}
}
lean_object* l_Lean_Meta_getCtorNumPropFields___lam__0(lean_object* v_numFields_141_, lean_object* v_ctorInfo_142_, lean_object* v_xs_143_, lean_object* v_x_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = lean_unsigned_to_nat(0u);
v___x_151_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCtorNumPropFields_spec__0___redArg(v_numFields_141_, v_ctorInfo_142_, v_xs_143_, v___x_150_, v___x_150_, v___y_145_, v___y_146_, v___y_147_, v___y_148_);
return v___x_151_;
}
}
LEAN_EXPORT void l_Lean_Meta_getCtorNumPropFields___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_numFields_141_ = stack[0].m_obj;
lean_object* v_ctorInfo_142_ = stack[1].m_obj;
lean_object* v_xs_143_ = stack[2].m_obj;
lean_object* v_x_144_ = stack[3].m_obj;
lean_object* v___y_145_ = stack[4].m_obj;
lean_object* v___y_146_ = stack[5].m_obj;
lean_object* v___y_147_ = stack[6].m_obj;
lean_object* v___y_148_ = stack[7].m_obj;
lean_object* v_res_152_;
v_res_152_ = l_Lean_Meta_getCtorNumPropFields___lam__0(v_numFields_141_, v_ctorInfo_142_, v_xs_143_, v_x_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_);
stack->m_obj
 = v_res_152_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields___lam__0___boxed(lean_object* v_numFields_153_, lean_object* v_ctorInfo_154_, lean_object* v_xs_155_, lean_object* v_x_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lean_Meta_getCtorNumPropFields___lam__0(v_numFields_153_, v_ctorInfo_154_, v_xs_155_, v_x_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
lean_dec(v___y_158_);
lean_dec_ref(v___y_157_);
lean_dec_ref(v_x_156_);
lean_dec_ref(v_xs_155_);
lean_dec_ref(v_ctorInfo_154_);
lean_dec(v_numFields_153_);
return v_res_162_;
}
}
lean_object* l_Lean_Meta_getCtorNumPropFields(lean_object* v_ctorInfo_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_){
_start:
{
lean_object* v_toConstantVal_169_; lean_object* v_numFields_170_; lean_object* v_type_171_; lean_object* v___f_172_; uint8_t v___x_173_; lean_object* v___x_174_; 
v_toConstantVal_169_ = lean_ctor_get(v_ctorInfo_163_, 0);
v_numFields_170_ = lean_ctor_get(v_ctorInfo_163_, 4);
lean_inc(v_numFields_170_);
v_type_171_ = lean_ctor_get(v_toConstantVal_169_, 2);
lean_inc_ref(v_type_171_);
v___f_172_ = lean_alloc_closure((void*)(l_Lean_Meta_getCtorNumPropFields___lam__0___boxed), 9, 2);
lean_closure_set(v___f_172_, 0, v_numFields_170_);
lean_closure_set(v___f_172_, 1, v_ctorInfo_163_);
v___x_173_ = 0;
v___x_174_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg(v_type_171_, v___f_172_, v___x_173_, v___x_173_, v_a_164_, v_a_165_, v_a_166_, v_a_167_);
return v___x_174_;
}
}
LEAN_EXPORT void l_Lean_Meta_getCtorNumPropFields_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorInfo_163_ = stack[0].m_obj;
lean_object* v_a_164_ = stack[1].m_obj;
lean_object* v_a_165_ = stack[2].m_obj;
lean_object* v_a_166_ = stack[3].m_obj;
lean_object* v_a_167_ = stack[4].m_obj;
lean_object* v_res_175_;
v_res_175_ = l_Lean_Meta_getCtorNumPropFields(v_ctorInfo_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_);
stack->m_obj
 = v_res_175_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields___boxed(lean_object* v_ctorInfo_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Lean_Meta_getCtorNumPropFields(v_ctorInfo_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_);
lean_dec(v_a_180_);
lean_dec_ref(v_a_179_);
lean_dec(v_a_178_);
lean_dec_ref(v_a_177_);
return v_res_182_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCtorNumPropFields_spec__0(lean_object* v_upperBound_183_, lean_object* v_ctorInfo_184_, lean_object* v_xs_185_, lean_object* v_inst_186_, lean_object* v_R_187_, lean_object* v_a_188_, lean_object* v_b_189_, lean_object* v_c_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCtorNumPropFields_spec__0___redArg(v_upperBound_183_, v_ctorInfo_184_, v_xs_185_, v_a_188_, v_b_189_, v___y_191_, v___y_192_, v___y_193_, v___y_194_);
return v___x_196_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCtorNumPropFields_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_183_ = stack[0].m_obj;
lean_object* v_ctorInfo_184_ = stack[1].m_obj;
lean_object* v_xs_185_ = stack[2].m_obj;
lean_object* v_a_188_ = stack[5].m_obj;
lean_object* v_b_189_ = stack[6].m_obj;
lean_object* v___y_191_ = stack[8].m_obj;
lean_object* v___y_192_ = stack[9].m_obj;
lean_object* v___y_193_ = stack[10].m_obj;
lean_object* v___y_194_ = stack[11].m_obj;
lean_object* v_res_197_;
v_res_197_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCtorNumPropFields_spec__0(v_upperBound_183_, v_ctorInfo_184_, v_xs_185_, lean_box(0), lean_box(0), v_a_188_, v_b_189_, lean_box(0), v___y_191_, v___y_192_, v___y_193_, v___y_194_);
stack->m_obj
 = v_res_197_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCtorNumPropFields_spec__0___boxed(lean_object* v_upperBound_198_, lean_object* v_ctorInfo_199_, lean_object* v_xs_200_, lean_object* v_inst_201_, lean_object* v_R_202_, lean_object* v_a_203_, lean_object* v_b_204_, lean_object* v_c_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCtorNumPropFields_spec__0(v_upperBound_198_, v_ctorInfo_199_, v_xs_200_, v_inst_201_, v_R_202_, v_a_203_, v_b_204_, v_c_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
lean_dec_ref(v_xs_200_);
lean_dec_ref(v_ctorInfo_199_);
lean_dec(v_upperBound_198_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResultCore_ctorIdx___impl(lean_object* v_x_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = lean_obj_tag_nat(v_x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResultCore_ctorIdx___impl___boxed(lean_object* v_x_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lean_Meta_InjectionResultCore_ctorIdx___impl(v_x_214_);
lean_dec(v_x_214_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResultCore_ctorElim___redArg(lean_object* v_t_216_, lean_object* v_k_217_){
_start:
{
if (lean_obj_tag(v_t_216_) == 0)
{
return v_k_217_;
}
else
{
lean_object* v_mvarId_218_; lean_object* v_numNewEqs_219_; lean_object* v___x_220_; 
v_mvarId_218_ = lean_ctor_get(v_t_216_, 0);
lean_inc(v_mvarId_218_);
v_numNewEqs_219_ = lean_ctor_get(v_t_216_, 1);
lean_inc(v_numNewEqs_219_);
lean_dec_ref_known(v_t_216_, 2);
v___x_220_ = lean_apply_2(v_k_217_, v_mvarId_218_, v_numNewEqs_219_);
return v___x_220_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResultCore_ctorElim(lean_object* v_motive_221_, lean_object* v_ctorIdx_222_, lean_object* v_t_223_, lean_object* v_h_224_, lean_object* v_k_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_Lean_Meta_InjectionResultCore_ctorElim___redArg(v_t_223_, v_k_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResultCore_ctorElim___boxed(lean_object* v_motive_227_, lean_object* v_ctorIdx_228_, lean_object* v_t_229_, lean_object* v_h_230_, lean_object* v_k_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_Meta_InjectionResultCore_ctorElim(v_motive_227_, v_ctorIdx_228_, v_t_229_, v_h_230_, v_k_231_);
lean_dec(v_ctorIdx_228_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResultCore_solved_elim___redArg(lean_object* v_t_233_, lean_object* v_solved_234_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = l_Lean_Meta_InjectionResultCore_ctorElim___redArg(v_t_233_, v_solved_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResultCore_solved_elim(lean_object* v_motive_236_, lean_object* v_t_237_, lean_object* v_h_238_, lean_object* v_solved_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l_Lean_Meta_InjectionResultCore_ctorElim___redArg(v_t_237_, v_solved_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResultCore_subgoal_elim___redArg(lean_object* v_t_241_, lean_object* v_subgoal_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_Lean_Meta_InjectionResultCore_ctorElim___redArg(v_t_241_, v_subgoal_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResultCore_subgoal_elim(lean_object* v_motive_244_, lean_object* v_t_245_, lean_object* v_h_246_, lean_object* v_subgoal_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l_Lean_Meta_InjectionResultCore_ctorElim___redArg(v_t_245_, v_subgoal_247_);
return v___x_248_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg(lean_object* v_mvarId_249_, lean_object* v_x_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_249_, v_x_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_264_; 
v_a_257_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_264_ == 0)
{
v___x_259_ = v___x_256_;
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_256_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_262_; 
if (v_isShared_260_ == 0)
{
v___x_262_ = v___x_259_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_a_257_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
else
{
lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_272_; 
v_a_265_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_272_ == 0)
{
v___x_267_ = v___x_256_;
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v___x_256_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_270_; 
if (v_isShared_268_ == 0)
{
v___x_270_ = v___x_267_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_a_265_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_249_ = stack[0].m_obj;
lean_object* v_x_250_ = stack[1].m_obj;
lean_object* v___y_251_ = stack[2].m_obj;
lean_object* v___y_252_ = stack[3].m_obj;
lean_object* v___y_253_ = stack[4].m_obj;
lean_object* v___y_254_ = stack[5].m_obj;
lean_object* v_res_273_;
v_res_273_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg(v_mvarId_249_, v_x_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_);
stack->m_obj
 = v_res_273_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg___boxed(lean_object* v_mvarId_274_, lean_object* v_x_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg(v_mvarId_274_, v_x_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
return v_res_281_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2(lean_object* v_00_u03b1_282_, lean_object* v_mvarId_283_, lean_object* v_x_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg(v_mvarId_283_, v_x_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
return v___x_290_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_283_ = stack[1].m_obj;
lean_object* v_x_284_ = stack[2].m_obj;
lean_object* v___y_285_ = stack[3].m_obj;
lean_object* v___y_286_ = stack[4].m_obj;
lean_object* v___y_287_ = stack[5].m_obj;
lean_object* v___y_288_ = stack[6].m_obj;
lean_object* v_res_291_;
v_res_291_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2(lean_box(0), v_mvarId_283_, v_x_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
stack->m_obj
 = v_res_291_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___boxed(lean_object* v_00_u03b1_292_, lean_object* v_mvarId_293_, lean_object* v_x_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2(v_00_u03b1_292_, v_mvarId_293_, v_x_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
return v_res_300_;
}
}
lean_object* l_Lean_Meta_injectionCore___lam__0(lean_object* v___x_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_toCold_310_; lean_object* v_options_311_; uint8_t v_hasTrace_312_; 
v_toCold_310_ = lean_ctor_get(v___y_307_, 0);
v_options_311_ = lean_ctor_get(v_toCold_310_, 2);
v_hasTrace_312_ = lean_ctor_get_uint8(v_options_311_, sizeof(void*)*1);
if (v_hasTrace_312_ == 0)
{
lean_object* v___x_313_; lean_object* v___x_314_; 
lean_dec(v___x_304_);
v___x_313_ = lean_box(v_hasTrace_312_);
v___x_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
return v___x_314_;
}
else
{
lean_object* v_inheritedTraceOptions_315_; lean_object* v___x_316_; lean_object* v___x_317_; uint8_t v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v_inheritedTraceOptions_315_ = lean_ctor_get(v_toCold_310_, 11);
v___x_316_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__0___closed__1));
v___x_317_ = l_Lean_Name_append(v___x_316_, v___x_304_);
v___x_318_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_315_, v_options_311_, v___x_317_);
lean_dec(v___x_317_);
v___x_319_ = lean_box(v___x_318_);
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
return v___x_320_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_injectionCore___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_304_ = stack[0].m_obj;
lean_object* v___y_305_ = stack[1].m_obj;
lean_object* v___y_306_ = stack[2].m_obj;
lean_object* v___y_307_ = stack[3].m_obj;
lean_object* v___y_308_ = stack[4].m_obj;
lean_object* v_res_321_;
v_res_321_ = l_Lean_Meta_injectionCore___lam__0(v___x_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
stack->m_obj
 = v_res_321_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___lam__0___boxed(lean_object* v___x_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lean_Meta_injectionCore___lam__0(v___x_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
return v_res_328_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1_spec__2(lean_object* v_msgData_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v___x_335_; lean_object* v_env_336_; uint8_t v___x_337_; lean_object* v_env_338_; lean_object* v___x_339_; lean_object* v_toCold_340_; lean_object* v_mctx_341_; lean_object* v_lctx_342_; lean_object* v_options_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_335_ = lean_st_ref_get(v___y_333_);
v_env_336_ = lean_ctor_get(v___x_335_, 0);
lean_inc_ref(v_env_336_);
lean_dec(v___x_335_);
v___x_337_ = 0;
v_env_338_ = l_Lean_Environment_setRecordingDeps(v_env_336_, v___x_337_);
v___x_339_ = lean_st_ref_get(v___y_331_);
v_toCold_340_ = lean_ctor_get(v___y_332_, 0);
v_mctx_341_ = lean_ctor_get(v___x_339_, 0);
lean_inc_ref(v_mctx_341_);
lean_dec(v___x_339_);
v_lctx_342_ = lean_ctor_get(v___y_330_, 2);
v_options_343_ = lean_ctor_get(v_toCold_340_, 2);
lean_inc_ref(v_options_343_);
lean_inc_ref(v_lctx_342_);
v___x_344_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_344_, 0, v_env_338_);
lean_ctor_set(v___x_344_, 1, v_mctx_341_);
lean_ctor_set(v___x_344_, 2, v_lctx_342_);
lean_ctor_set(v___x_344_, 3, v_options_343_);
v___x_345_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v_msgData_329_);
v___x_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
return v___x_346_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_329_ = stack[0].m_obj;
lean_object* v___y_330_ = stack[1].m_obj;
lean_object* v___y_331_ = stack[2].m_obj;
lean_object* v___y_332_ = stack[3].m_obj;
lean_object* v___y_333_ = stack[4].m_obj;
lean_object* v_res_347_;
v_res_347_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1_spec__2(v_msgData_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_);
stack->m_obj
 = v_res_347_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1_spec__2___boxed(lean_object* v_msgData_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1_spec__2(v_msgData_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
return v_res_354_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__0(void){
_start:
{
lean_object* v___x_355_; double v___x_356_; 
v___x_355_ = lean_unsigned_to_nat(0u);
v___x_356_ = lean_float_of_nat(v___x_355_);
return v___x_356_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(lean_object* v_cls_360_, lean_object* v_msg_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
lean_object* v_ref_367_; lean_object* v___x_368_; lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_414_; 
v_ref_367_ = lean_ctor_get(v___y_364_, 2);
v___x_368_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1_spec__2(v_msg_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
v_a_369_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_414_ == 0)
{
v___x_371_ = v___x_368_;
v_isShared_372_ = v_isSharedCheck_414_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_368_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_414_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_373_; lean_object* v_traceState_374_; lean_object* v_env_375_; lean_object* v_nextMacroScope_376_; lean_object* v_ngen_377_; lean_object* v_auxDeclNGen_378_; lean_object* v_cache_379_; lean_object* v_recordedDeps_380_; lean_object* v_messages_381_; lean_object* v_infoState_382_; lean_object* v_snapshotTasks_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_413_; 
v___x_373_ = lean_st_ref_take(v___y_365_);
v_traceState_374_ = lean_ctor_get(v___x_373_, 4);
v_env_375_ = lean_ctor_get(v___x_373_, 0);
v_nextMacroScope_376_ = lean_ctor_get(v___x_373_, 1);
v_ngen_377_ = lean_ctor_get(v___x_373_, 2);
v_auxDeclNGen_378_ = lean_ctor_get(v___x_373_, 3);
v_cache_379_ = lean_ctor_get(v___x_373_, 5);
v_recordedDeps_380_ = lean_ctor_get(v___x_373_, 6);
v_messages_381_ = lean_ctor_get(v___x_373_, 7);
v_infoState_382_ = lean_ctor_get(v___x_373_, 8);
v_snapshotTasks_383_ = lean_ctor_get(v___x_373_, 9);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_413_ == 0)
{
v___x_385_ = v___x_373_;
v_isShared_386_ = v_isSharedCheck_413_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_snapshotTasks_383_);
lean_inc(v_infoState_382_);
lean_inc(v_messages_381_);
lean_inc(v_recordedDeps_380_);
lean_inc(v_cache_379_);
lean_inc(v_traceState_374_);
lean_inc(v_auxDeclNGen_378_);
lean_inc(v_ngen_377_);
lean_inc(v_nextMacroScope_376_);
lean_inc(v_env_375_);
lean_dec(v___x_373_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_413_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
uint64_t v_tid_387_; lean_object* v_traces_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_412_; 
v_tid_387_ = lean_ctor_get_uint64(v_traceState_374_, sizeof(void*)*1);
v_traces_388_ = lean_ctor_get(v_traceState_374_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v_traceState_374_);
if (v_isSharedCheck_412_ == 0)
{
v___x_390_ = v_traceState_374_;
v_isShared_391_ = v_isSharedCheck_412_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_traces_388_);
lean_dec(v_traceState_374_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_412_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_392_; lean_object* v___x_393_; double v___x_394_; uint8_t v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_392_ = lean_box(0);
v___x_393_ = lean_box(0);
v___x_394_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__0);
v___x_395_ = 0;
v___x_396_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__1));
v___x_397_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_397_, 0, v_cls_360_);
lean_ctor_set(v___x_397_, 1, v___x_393_);
lean_ctor_set(v___x_397_, 2, v___x_396_);
lean_ctor_set_float(v___x_397_, sizeof(void*)*3, v___x_394_);
lean_ctor_set_float(v___x_397_, sizeof(void*)*3 + 8, v___x_394_);
lean_ctor_set_uint8(v___x_397_, sizeof(void*)*3 + 16, v___x_395_);
v___x_398_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__2));
v___x_399_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_399_, 0, v___x_397_);
lean_ctor_set(v___x_399_, 1, v_a_369_);
lean_ctor_set(v___x_399_, 2, v___x_398_);
lean_inc(v_ref_367_);
v___x_400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_400_, 0, v_ref_367_);
lean_ctor_set(v___x_400_, 1, v___x_399_);
v___x_401_ = l_Lean_PersistentArray_push___redArg(v_traces_388_, v___x_400_);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 0, v___x_401_);
v___x_403_ = v___x_390_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_401_);
lean_ctor_set_uint64(v_reuseFailAlloc_411_, sizeof(void*)*1, v_tid_387_);
v___x_403_ = v_reuseFailAlloc_411_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_405_; 
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 4, v___x_403_);
v___x_405_ = v___x_385_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_env_375_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_nextMacroScope_376_);
lean_ctor_set(v_reuseFailAlloc_410_, 2, v_ngen_377_);
lean_ctor_set(v_reuseFailAlloc_410_, 3, v_auxDeclNGen_378_);
lean_ctor_set(v_reuseFailAlloc_410_, 4, v___x_403_);
lean_ctor_set(v_reuseFailAlloc_410_, 5, v_cache_379_);
lean_ctor_set(v_reuseFailAlloc_410_, 6, v_recordedDeps_380_);
lean_ctor_set(v_reuseFailAlloc_410_, 7, v_messages_381_);
lean_ctor_set(v_reuseFailAlloc_410_, 8, v_infoState_382_);
lean_ctor_set(v_reuseFailAlloc_410_, 9, v_snapshotTasks_383_);
v___x_405_ = v_reuseFailAlloc_410_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_406_ = lean_st_ref_put(v___y_365_, v___x_405_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 0, v___x_392_);
v___x_408_ = v___x_371_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_392_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_360_ = stack[0].m_obj;
lean_object* v_msg_361_ = stack[1].m_obj;
lean_object* v___y_362_ = stack[2].m_obj;
lean_object* v___y_363_ = stack[3].m_obj;
lean_object* v___y_364_ = stack[4].m_obj;
lean_object* v___y_365_ = stack[5].m_obj;
lean_object* v_res_415_;
v_res_415_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v_cls_360_, v_msg_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
stack->m_obj
 = v_res_415_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___boxed(lean_object* v_cls_416_, lean_object* v_msg_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v_cls_416_, v_msg_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(lean_object* v_x_424_, lean_object* v_x_425_, lean_object* v_x_426_, lean_object* v_x_427_){
_start:
{
lean_object* v_ks_428_; lean_object* v_vs_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_453_; 
v_ks_428_ = lean_ctor_get(v_x_424_, 0);
v_vs_429_ = lean_ctor_get(v_x_424_, 1);
v_isSharedCheck_453_ = !lean_is_exclusive(v_x_424_);
if (v_isSharedCheck_453_ == 0)
{
v___x_431_ = v_x_424_;
v_isShared_432_ = v_isSharedCheck_453_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_vs_429_);
lean_inc(v_ks_428_);
lean_dec(v_x_424_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_453_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_433_; uint8_t v___x_434_; 
v___x_433_ = lean_array_get_size(v_ks_428_);
v___x_434_ = lean_nat_dec_lt(v_x_425_, v___x_433_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_438_; 
lean_dec(v_x_425_);
v___x_435_ = lean_array_push(v_ks_428_, v_x_426_);
v___x_436_ = lean_array_push(v_vs_429_, v_x_427_);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 1, v___x_436_);
lean_ctor_set(v___x_431_, 0, v___x_435_);
v___x_438_ = v___x_431_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_435_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v___x_436_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
else
{
lean_object* v_k_x27_440_; uint8_t v___x_441_; 
v_k_x27_440_ = lean_array_fget_borrowed(v_ks_428_, v_x_425_);
v___x_441_ = l_Lean_instBEqMVarId_beq(v_x_426_, v_k_x27_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_443_; 
if (v_isShared_432_ == 0)
{
v___x_443_ = v___x_431_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_ks_428_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v_vs_429_);
v___x_443_ = v_reuseFailAlloc_447_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = lean_unsigned_to_nat(1u);
v___x_445_ = lean_nat_add(v_x_425_, v___x_444_);
lean_dec(v_x_425_);
v_x_424_ = v___x_443_;
v_x_425_ = v___x_445_;
goto _start;
}
}
else
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_451_; 
v___x_448_ = lean_array_fset(v_ks_428_, v_x_425_, v_x_426_);
v___x_449_ = lean_array_fset(v_vs_429_, v_x_425_, v_x_427_);
lean_dec(v_x_425_);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 1, v___x_449_);
lean_ctor_set(v___x_431_, 0, v___x_448_);
v___x_451_ = v___x_431_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_448_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v___x_449_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_n_454_, lean_object* v_k_455_, lean_object* v_v_456_){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = lean_unsigned_to_nat(0u);
v___x_458_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(v_n_454_, v___x_457_, v_k_455_, v_v_456_);
return v___x_458_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_459_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(lean_object* v_x_460_, size_t v_x_461_, size_t v_x_462_, lean_object* v_x_463_, lean_object* v_x_464_){
_start:
{
if (lean_obj_tag(v_x_460_) == 0)
{
lean_object* v_es_465_; size_t v___x_466_; size_t v___x_467_; lean_object* v_j_468_; lean_object* v___x_469_; uint8_t v___x_470_; 
v_es_465_ = lean_ctor_get(v_x_460_, 0);
v___x_466_ = ((size_t)31ULL);
v___x_467_ = lean_usize_land(v_x_461_, v___x_466_);
v_j_468_ = lean_usize_to_nat(v___x_467_);
v___x_469_ = lean_array_get_size(v_es_465_);
v___x_470_ = lean_nat_dec_lt(v_j_468_, v___x_469_);
if (v___x_470_ == 0)
{
lean_dec(v_j_468_);
lean_dec(v_x_464_);
lean_dec(v_x_463_);
return v_x_460_;
}
else
{
lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_509_; 
lean_inc_ref(v_es_465_);
v_isSharedCheck_509_ = !lean_is_exclusive(v_x_460_);
if (v_isSharedCheck_509_ == 0)
{
lean_object* v_unused_510_; 
v_unused_510_ = lean_ctor_get(v_x_460_, 0);
lean_dec(v_unused_510_);
v___x_472_ = v_x_460_;
v_isShared_473_ = v_isSharedCheck_509_;
goto v_resetjp_471_;
}
else
{
lean_dec(v_x_460_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_509_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v_v_474_; lean_object* v___x_475_; lean_object* v_xs_x27_476_; lean_object* v___y_478_; 
v_v_474_ = lean_array_fget(v_es_465_, v_j_468_);
v___x_475_ = lean_box(0);
v_xs_x27_476_ = lean_array_fset(v_es_465_, v_j_468_, v___x_475_);
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
v___x_488_ = l_Lean_instBEqMVarId_beq(v_x_463_, v_key_483_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; lean_object* v___x_490_; 
lean_del_object(v___x_486_);
v___x_489_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_483_, v_val_484_, v_x_463_, v_x_464_);
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
lean_ctor_set(v___x_486_, 1, v_x_464_);
lean_ctor_set(v___x_486_, 0, v_x_463_);
v___x_492_ = v___x_486_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_x_463_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_x_464_);
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
lean_object* v_node_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_507_; 
v_node_495_ = lean_ctor_get(v_v_474_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v_v_474_);
if (v_isSharedCheck_507_ == 0)
{
v___x_497_ = v_v_474_;
v_isShared_498_ = v_isSharedCheck_507_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_node_495_);
lean_dec(v_v_474_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_507_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
size_t v___x_499_; size_t v___x_500_; size_t v___x_501_; size_t v___x_502_; lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_499_ = ((size_t)5ULL);
v___x_500_ = lean_usize_shift_right(v_x_461_, v___x_499_);
v___x_501_ = ((size_t)1ULL);
v___x_502_ = lean_usize_add(v_x_462_, v___x_501_);
v___x_503_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(v_node_495_, v___x_500_, v___x_502_, v_x_463_, v_x_464_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v___x_503_);
v___x_505_ = v___x_497_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_503_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
v___y_478_ = v___x_505_;
goto v___jp_477_;
}
}
}
default: 
{
lean_object* v___x_508_; 
v___x_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_508_, 0, v_x_463_);
lean_ctor_set(v___x_508_, 1, v_x_464_);
v___y_478_ = v___x_508_;
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
lean_object* v_ks_511_; lean_object* v_vs_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_530_; 
v_ks_511_ = lean_ctor_get(v_x_460_, 0);
v_vs_512_ = lean_ctor_get(v_x_460_, 1);
v_isSharedCheck_530_ = !lean_is_exclusive(v_x_460_);
if (v_isSharedCheck_530_ == 0)
{
v___x_514_ = v_x_460_;
v_isShared_515_ = v_isSharedCheck_530_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_vs_512_);
lean_inc(v_ks_511_);
lean_dec(v_x_460_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_530_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_ks_511_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v_vs_512_);
v___x_517_ = v_reuseFailAlloc_529_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
lean_object* v_newNode_518_; size_t v___x_519_; uint8_t v___x_520_; 
v_newNode_518_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5___redArg(v___x_517_, v_x_463_, v_x_464_);
v___x_519_ = ((size_t)7ULL);
v___x_520_ = lean_usize_dec_le(v___x_519_, v_x_462_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_521_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_518_);
v___x_522_ = lean_unsigned_to_nat(4u);
v___x_523_ = lean_nat_dec_lt(v___x_521_, v___x_522_);
lean_dec(v___x_521_);
if (v___x_523_ == 0)
{
lean_object* v_ks_524_; lean_object* v_vs_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v_ks_524_ = lean_ctor_get(v_newNode_518_, 0);
lean_inc_ref(v_ks_524_);
v_vs_525_ = lean_ctor_get(v_newNode_518_, 1);
lean_inc_ref(v_vs_525_);
lean_dec_ref(v_newNode_518_);
v___x_526_ = lean_unsigned_to_nat(0u);
v___x_527_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_528_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___redArg(v_x_462_, v_ks_524_, v_vs_525_, v___x_526_, v___x_527_);
lean_dec_ref(v_vs_525_);
lean_dec_ref(v_ks_524_);
return v___x_528_;
}
else
{
return v_newNode_518_;
}
}
else
{
return v_newNode_518_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_460_ = stack[0].m_obj;
size_t v_x_461_ = stack[1].m_num;
size_t v_x_462_ = stack[2].m_num;
lean_object* v_x_463_ = stack[3].m_obj;
lean_object* v_x_464_ = stack[4].m_obj;
lean_object* v_res_531_;
v_res_531_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(v_x_460_, v_x_461_, v_x_462_, v_x_463_, v_x_464_);
stack->m_obj
 = v_res_531_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___redArg(size_t v_depth_532_, lean_object* v_keys_533_, lean_object* v_vals_534_, lean_object* v_i_535_, lean_object* v_entries_536_){
_start:
{
lean_object* v___x_537_; uint8_t v___x_538_; 
v___x_537_ = lean_array_get_size(v_keys_533_);
v___x_538_ = lean_nat_dec_lt(v_i_535_, v___x_537_);
if (v___x_538_ == 0)
{
lean_dec(v_i_535_);
return v_entries_536_;
}
else
{
lean_object* v_k_539_; lean_object* v_v_540_; uint64_t v___x_541_; size_t v_h_542_; size_t v___x_543_; lean_object* v___x_544_; size_t v___x_545_; size_t v___x_546_; size_t v___x_547_; size_t v_h_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v_k_539_ = lean_array_fget_borrowed(v_keys_533_, v_i_535_);
v_v_540_ = lean_array_fget_borrowed(v_vals_534_, v_i_535_);
v___x_541_ = l_Lean_instHashableMVarId_hash(v_k_539_);
v_h_542_ = lean_uint64_to_usize(v___x_541_);
v___x_543_ = ((size_t)5ULL);
v___x_544_ = lean_unsigned_to_nat(1u);
v___x_545_ = ((size_t)1ULL);
v___x_546_ = lean_usize_sub(v_depth_532_, v___x_545_);
v___x_547_ = lean_usize_mul(v___x_543_, v___x_546_);
v_h_548_ = lean_usize_shift_right(v_h_542_, v___x_547_);
v___x_549_ = lean_nat_add(v_i_535_, v___x_544_);
lean_dec(v_i_535_);
lean_inc(v_v_540_);
lean_inc(v_k_539_);
v___x_550_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(v_entries_536_, v_h_548_, v_depth_532_, v_k_539_, v_v_540_);
v_i_535_ = v___x_549_;
v_entries_536_ = v___x_550_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_532_ = stack[0].m_num;
lean_object* v_keys_533_ = stack[1].m_obj;
lean_object* v_vals_534_ = stack[2].m_obj;
lean_object* v_i_535_ = stack[3].m_obj;
lean_object* v_entries_536_ = stack[4].m_obj;
lean_object* v_res_552_;
v_res_552_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___redArg(v_depth_532_, v_keys_533_, v_vals_534_, v_i_535_, v_entries_536_);
stack->m_obj
 = v_res_552_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_depth_553_, lean_object* v_keys_554_, lean_object* v_vals_555_, lean_object* v_i_556_, lean_object* v_entries_557_){
_start:
{
size_t v_depth_boxed_558_; lean_object* v_res_559_; 
v_depth_boxed_558_ = lean_unbox_usize(v_depth_553_);
lean_dec(v_depth_553_);
v_res_559_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___redArg(v_depth_boxed_558_, v_keys_554_, v_vals_555_, v_i_556_, v_entries_557_);
lean_dec_ref(v_vals_555_);
lean_dec_ref(v_keys_554_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_560_, lean_object* v_x_561_, lean_object* v_x_562_, lean_object* v_x_563_, lean_object* v_x_564_){
_start:
{
size_t v_x_14702__boxed_565_; size_t v_x_14703__boxed_566_; lean_object* v_res_567_; 
v_x_14702__boxed_565_ = lean_unbox_usize(v_x_561_);
lean_dec(v_x_561_);
v_x_14703__boxed_566_ = lean_unbox_usize(v_x_562_);
lean_dec(v_x_562_);
v_res_567_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(v_x_560_, v_x_14702__boxed_565_, v_x_14703__boxed_566_, v_x_563_, v_x_564_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0___redArg(lean_object* v_x_568_, lean_object* v_x_569_, lean_object* v_x_570_){
_start:
{
uint64_t v___x_571_; size_t v___x_572_; size_t v___x_573_; lean_object* v___x_574_; 
v___x_571_ = l_Lean_instHashableMVarId_hash(v_x_569_);
v___x_572_ = lean_uint64_to_usize(v___x_571_);
v___x_573_ = ((size_t)1ULL);
v___x_574_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(v_x_568_, v___x_572_, v___x_573_, v_x_569_, v_x_570_);
return v___x_574_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(lean_object* v_mvarId_575_, lean_object* v_val_576_, lean_object* v___y_577_){
_start:
{
lean_object* v___x_579_; lean_object* v_mctx_580_; lean_object* v_cache_581_; lean_object* v_zetaDeltaFVarIds_582_; lean_object* v_postponed_583_; lean_object* v_diag_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_614_; 
v___x_579_ = lean_st_ref_take(v___y_577_);
v_mctx_580_ = lean_ctor_get(v___x_579_, 0);
v_cache_581_ = lean_ctor_get(v___x_579_, 1);
v_zetaDeltaFVarIds_582_ = lean_ctor_get(v___x_579_, 2);
v_postponed_583_ = lean_ctor_get(v___x_579_, 3);
v_diag_584_ = lean_ctor_get(v___x_579_, 4);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_614_ == 0)
{
v___x_586_ = v___x_579_;
v_isShared_587_ = v_isSharedCheck_614_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_diag_584_);
lean_inc(v_postponed_583_);
lean_inc(v_zetaDeltaFVarIds_582_);
lean_inc(v_cache_581_);
lean_inc(v_mctx_580_);
lean_dec(v___x_579_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_614_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v_depth_588_; lean_object* v_levelAssignDepth_589_; lean_object* v_lmvarCounter_590_; lean_object* v_mvarCounter_591_; lean_object* v_lDecls_592_; lean_object* v_decls_593_; lean_object* v_userNames_594_; lean_object* v_lAssignment_595_; lean_object* v_eAssignment_596_; lean_object* v_dAssignment_597_; lean_object* v_instanceTypedMVars_598_; lean_object* v_synthNormMemo_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_613_; 
v_depth_588_ = lean_ctor_get(v_mctx_580_, 0);
v_levelAssignDepth_589_ = lean_ctor_get(v_mctx_580_, 1);
v_lmvarCounter_590_ = lean_ctor_get(v_mctx_580_, 2);
v_mvarCounter_591_ = lean_ctor_get(v_mctx_580_, 3);
v_lDecls_592_ = lean_ctor_get(v_mctx_580_, 4);
v_decls_593_ = lean_ctor_get(v_mctx_580_, 5);
v_userNames_594_ = lean_ctor_get(v_mctx_580_, 6);
v_lAssignment_595_ = lean_ctor_get(v_mctx_580_, 7);
v_eAssignment_596_ = lean_ctor_get(v_mctx_580_, 8);
v_dAssignment_597_ = lean_ctor_get(v_mctx_580_, 9);
v_instanceTypedMVars_598_ = lean_ctor_get(v_mctx_580_, 10);
v_synthNormMemo_599_ = lean_ctor_get(v_mctx_580_, 11);
v_isSharedCheck_613_ = !lean_is_exclusive(v_mctx_580_);
if (v_isSharedCheck_613_ == 0)
{
v___x_601_ = v_mctx_580_;
v_isShared_602_ = v_isSharedCheck_613_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_synthNormMemo_599_);
lean_inc(v_instanceTypedMVars_598_);
lean_inc(v_dAssignment_597_);
lean_inc(v_eAssignment_596_);
lean_inc(v_lAssignment_595_);
lean_inc(v_userNames_594_);
lean_inc(v_decls_593_);
lean_inc(v_lDecls_592_);
lean_inc(v_mvarCounter_591_);
lean_inc(v_lmvarCounter_590_);
lean_inc(v_levelAssignDepth_589_);
lean_inc(v_depth_588_);
lean_dec(v_mctx_580_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_613_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_606_; 
v___x_603_ = lean_box(0);
v___x_604_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0___redArg(v_eAssignment_596_, v_mvarId_575_, v_val_576_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 8, v___x_604_);
v___x_606_ = v___x_601_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_depth_588_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_levelAssignDepth_589_);
lean_ctor_set(v_reuseFailAlloc_612_, 2, v_lmvarCounter_590_);
lean_ctor_set(v_reuseFailAlloc_612_, 3, v_mvarCounter_591_);
lean_ctor_set(v_reuseFailAlloc_612_, 4, v_lDecls_592_);
lean_ctor_set(v_reuseFailAlloc_612_, 5, v_decls_593_);
lean_ctor_set(v_reuseFailAlloc_612_, 6, v_userNames_594_);
lean_ctor_set(v_reuseFailAlloc_612_, 7, v_lAssignment_595_);
lean_ctor_set(v_reuseFailAlloc_612_, 8, v___x_604_);
lean_ctor_set(v_reuseFailAlloc_612_, 9, v_dAssignment_597_);
lean_ctor_set(v_reuseFailAlloc_612_, 10, v_instanceTypedMVars_598_);
lean_ctor_set(v_reuseFailAlloc_612_, 11, v_synthNormMemo_599_);
v___x_606_ = v_reuseFailAlloc_612_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
lean_object* v___x_608_; 
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v___x_606_);
v___x_608_ = v___x_586_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_606_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v_cache_581_);
lean_ctor_set(v_reuseFailAlloc_611_, 2, v_zetaDeltaFVarIds_582_);
lean_ctor_set(v_reuseFailAlloc_611_, 3, v_postponed_583_);
lean_ctor_set(v_reuseFailAlloc_611_, 4, v_diag_584_);
v___x_608_ = v_reuseFailAlloc_611_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = lean_st_ref_put(v___y_577_, v___x_608_);
v___x_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_610_, 0, v___x_603_);
return v___x_610_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_575_ = stack[0].m_obj;
lean_object* v_val_576_ = stack[1].m_obj;
lean_object* v___y_577_ = stack[2].m_obj;
lean_object* v_res_615_;
v_res_615_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(v_mvarId_575_, v_val_576_, v___y_577_);
stack->m_obj
 = v_res_615_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg___boxed(lean_object* v_mvarId_616_, lean_object* v_val_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(v_mvarId_616_, v_val_617_, v___y_618_);
lean_dec(v___y_618_);
return v_res_620_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__2(void){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__1));
v___x_625_ = l_Lean_MessageData_ofFormat(v___x_624_);
return v___x_625_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__3(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__2, &l_Lean_Meta_injectionCore___lam__1___closed__2_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__2);
v___x_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
return v___x_627_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__6(void){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__5));
v___x_632_ = l_Lean_MessageData_ofFormat(v___x_631_);
return v___x_632_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__7(void){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__6, &l_Lean_Meta_injectionCore___lam__1___closed__6_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__6);
v___x_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
return v___x_634_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__9(void){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__8));
v___x_637_ = l_Lean_stringToMessageData(v___x_636_);
return v___x_637_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__11(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__10));
v___x_640_ = l_Lean_stringToMessageData(v___x_639_);
return v___x_640_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__13(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__12));
v___x_643_ = l_Lean_stringToMessageData(v___x_642_);
return v___x_643_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__15(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__14));
v___x_646_ = l_Lean_stringToMessageData(v___x_645_);
return v___x_646_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__17(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__16));
v___x_649_ = l_Lean_stringToMessageData(v___x_648_);
return v___x_649_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__22(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__21));
v___x_657_ = l_Lean_MessageData_ofFormat(v___x_656_);
return v___x_657_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__23(void){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__22, &l_Lean_Meta_injectionCore___lam__1___closed__22_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__22);
v___x_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
return v___x_659_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__27(void){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__26));
v___x_664_ = l_Lean_stringToMessageData(v___x_663_);
return v___x_664_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__29(void){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__28));
v___x_667_ = l_Lean_stringToMessageData(v___x_666_);
return v___x_667_;
}
}
lean_object* l_Lean_Meta_injectionCore___lam__1(lean_object* v___x_671_, lean_object* v_mvarId_672_, lean_object* v_fvarId_673_, lean_object* v___x_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_903_; lean_object* v___y_904_; lean_object* v___y_905_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v_type_933_; lean_object* v_prf_934_; lean_object* v___x_1014_; 
lean_inc(v___x_671_);
lean_inc(v_mvarId_672_);
v___x_1014_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_672_, v___x_671_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v___x_1015_; 
lean_dec_ref_known(v___x_1014_, 1);
lean_inc(v_fvarId_673_);
v___x_1015_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_673_, v___y_675_, v___y_677_, v___y_678_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_a_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_a_1016_);
lean_dec_ref_known(v___x_1015_, 1);
v___x_1017_ = l_Lean_LocalDecl_type(v_a_1016_);
lean_dec(v_a_1016_);
lean_inc(v___y_678_);
lean_inc_ref(v___y_677_);
lean_inc(v___y_676_);
lean_inc_ref(v___y_675_);
v___x_1018_ = lean_whnf(v___x_1017_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; uint8_t v___x_1023_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_a_1019_);
lean_dec_ref_known(v___x_1018_, 1);
lean_inc(v_fvarId_673_);
v___x_1020_ = l_Lean_mkFVar(v_fvarId_673_);
v___x_1021_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__31));
v___x_1022_ = lean_unsigned_to_nat(4u);
v___x_1023_ = l_Lean_Expr_isAppOfArity(v_a_1019_, v___x_1021_, v___x_1022_);
if (v___x_1023_ == 0)
{
v_type_933_ = v_a_1019_;
v_prf_934_ = v___x_1020_;
goto v___jp_932_;
}
else
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1024_ = l_Lean_Expr_appFn_x21(v_a_1019_);
v___x_1025_ = l_Lean_Expr_appFn_x21(v___x_1024_);
v___x_1026_ = l_Lean_Expr_appFn_x21(v___x_1025_);
v___x_1027_ = l_Lean_Expr_appArg_x21(v___x_1026_);
lean_dec_ref(v___x_1026_);
v___x_1028_ = l_Lean_Expr_appArg_x21(v___x_1025_);
lean_dec_ref(v___x_1025_);
v___x_1029_ = l_Lean_Expr_appArg_x21(v___x_1024_);
lean_dec_ref(v___x_1024_);
v___x_1030_ = l_Lean_Expr_appArg_x21(v_a_1019_);
v___x_1031_ = l_Lean_Meta_isExprDefEq(v___x_1027_, v___x_1029_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; uint8_t v___x_1033_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_a_1032_);
lean_dec_ref_known(v___x_1031_, 1);
v___x_1033_ = lean_unbox(v_a_1032_);
lean_dec(v_a_1032_);
if (v___x_1033_ == 0)
{
lean_dec_ref(v___x_1030_);
lean_dec_ref(v___x_1028_);
v_type_933_ = v_a_1019_;
v_prf_934_ = v___x_1020_;
goto v___jp_932_;
}
else
{
lean_object* v___x_1034_; 
lean_dec(v_a_1019_);
v___x_1034_ = l_Lean_Meta_mkEq(v___x_1028_, v___x_1030_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v_a_1035_; lean_object* v___x_1036_; 
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_a_1035_);
lean_dec_ref_known(v___x_1034_, 1);
v___x_1036_ = l_Lean_Meta_mkEqOfHEq(v___x_1020_, v___x_1023_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_a_1037_; 
v_a_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc(v_a_1037_);
lean_dec_ref_known(v___x_1036_, 1);
v_type_933_ = v_a_1035_;
v_prf_934_ = v_a_1037_;
goto v___jp_932_;
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
lean_dec(v_a_1035_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec_ref(v___x_674_);
lean_dec(v_fvarId_673_);
lean_dec(v_mvarId_672_);
lean_dec(v___x_671_);
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
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec_ref(v___x_674_);
lean_dec(v_fvarId_673_);
lean_dec(v_mvarId_672_);
lean_dec(v___x_671_);
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
lean_dec_ref(v___x_1030_);
lean_dec_ref(v___x_1028_);
lean_dec_ref(v___x_1020_);
lean_dec(v_a_1019_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec_ref(v___x_674_);
lean_dec(v_fvarId_673_);
lean_dec(v_mvarId_672_);
lean_dec(v___x_671_);
v_a_1054_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1056_ = v___x_1031_;
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1031_);
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
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec_ref(v___x_674_);
lean_dec(v_fvarId_673_);
lean_dec(v_mvarId_672_);
lean_dec(v___x_671_);
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
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec_ref(v___x_674_);
lean_dec(v_fvarId_673_);
lean_dec(v_mvarId_672_);
lean_dec(v___x_671_);
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
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec_ref(v___x_674_);
lean_dec(v_fvarId_673_);
lean_dec(v_mvarId_672_);
lean_dec(v___x_671_);
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
v___jp_680_:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__3, &l_Lean_Meta_injectionCore___lam__1___closed__3_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__3);
v___x_686_ = l_Lean_Meta_throwTacticEx___redArg(v___x_671_, v_mvarId_672_, v___x_685_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
return v___x_686_;
}
v___jp_687_:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__7, &l_Lean_Meta_injectionCore___lam__1___closed__7_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__7);
v___x_693_ = l_Lean_Meta_throwTacticEx___redArg(v___x_671_, v_mvarId_672_, v___x_692_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
return v___x_693_;
}
v___jp_694_:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_697_, 0, v___y_695_);
lean_ctor_set(v___x_697_, 1, v___y_696_);
v___x_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
return v___x_698_;
}
v___jp_699_:
{
lean_object* v_toConstantVal_709_; lean_object* v_toConstantVal_710_; lean_object* v_numFields_711_; lean_object* v_name_712_; lean_object* v_name_713_; uint8_t v___x_714_; 
v_toConstantVal_709_ = lean_ctor_get(v___y_700_, 0);
v_toConstantVal_710_ = lean_ctor_get(v___y_703_, 0);
lean_inc_ref(v_toConstantVal_710_);
lean_dec_ref(v___y_703_);
v_numFields_711_ = lean_ctor_get(v___y_700_, 4);
lean_inc(v_numFields_711_);
v_name_712_ = lean_ctor_get(v_toConstantVal_709_, 0);
v_name_713_ = lean_ctor_get(v_toConstantVal_710_, 0);
lean_inc(v_name_713_);
lean_dec_ref(v_toConstantVal_710_);
v___x_714_ = lean_name_eq(v_name_712_, v_name_713_);
lean_dec(v_name_713_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_723_; 
lean_dec(v_numFields_711_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec_ref(v___y_705_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v_fvarId_673_);
lean_dec(v___x_671_);
v___x_715_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(v_mvarId_672_, v___y_704_, v___y_706_);
lean_dec(v___y_706_);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_723_ == 0)
{
lean_object* v_unused_724_; 
v_unused_724_ = lean_ctor_get(v___x_715_, 0);
lean_dec(v_unused_724_);
v___x_717_ = v___x_715_;
v_isShared_718_ = v_isSharedCheck_723_;
goto v_resetjp_716_;
}
else
{
lean_dec(v___x_715_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_723_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_719_; lean_object* v___x_721_; 
v___x_719_ = lean_box(0);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v___x_719_);
v___x_721_ = v___x_717_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_719_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
else
{
lean_object* v___x_725_; 
lean_inc(v___y_708_);
lean_inc_ref(v___y_707_);
lean_inc(v___y_706_);
lean_inc_ref(v___y_705_);
lean_inc(v___y_704_);
v___x_725_ = lean_infer_type(v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_727_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_a_726_);
lean_dec_ref_known(v___x_725_, 1);
v___x_727_ = l_Lean_Meta_whnfD(v_a_726_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_728_; 
v_a_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_a_728_);
lean_dec_ref_known(v___x_727_, 1);
if (lean_obj_tag(v_a_728_) == 7)
{
lean_object* v_binderType_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
lean_dec_ref(v___y_702_);
lean_dec(v___x_671_);
v_binderType_729_ = lean_ctor_get(v_a_728_, 1);
lean_inc_ref(v_binderType_729_);
lean_dec_ref_known(v_a_728_, 3);
v___x_730_ = l_Lean_Expr_headBeta(v_binderType_729_);
lean_inc(v_mvarId_672_);
v___x_731_ = l_Lean_MVarId_getTag(v_mvarId_672_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v_a_732_; lean_object* v___x_733_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_a_732_);
lean_dec_ref_known(v___x_731_, 1);
v___x_733_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_730_, v_a_732_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_789_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc_n(v_a_734_, 2);
lean_dec_ref_known(v___x_733_, 1);
v___x_735_ = l_Lean_Expr_app___override(v___y_704_, v_a_734_);
v___x_736_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(v_mvarId_672_, v___x_735_, v___y_706_);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_789_ == 0)
{
lean_object* v_unused_790_; 
v_unused_790_ = lean_ctor_get(v___x_736_, 0);
lean_dec(v_unused_790_);
v___x_738_ = v___x_736_;
v_isShared_739_ = v_isSharedCheck_789_;
goto v_resetjp_737_;
}
else
{
lean_dec(v___x_736_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_789_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = l_Lean_Expr_mvarId_x21(v_a_734_);
lean_dec(v_a_734_);
v___x_741_ = l_Lean_MVarId_tryClear(v___x_740_, v_fvarId_673_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v_a_742_; lean_object* v___x_743_; 
v_a_742_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_a_742_);
lean_dec_ref_known(v___x_741_, 1);
v___x_743_ = l_Lean_Meta_getCtorNumPropFields(v___y_700_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_toCold_744_; lean_object* v_options_745_; lean_object* v_a_746_; lean_object* v_inheritedTraceOptions_747_; uint8_t v_hasTrace_748_; lean_object* v___x_749_; 
v_toCold_744_ = lean_ctor_get(v___y_707_, 0);
v_options_745_ = lean_ctor_get(v_toCold_744_, 2);
v_a_746_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_a_746_);
lean_dec_ref_known(v___x_743_, 1);
v_inheritedTraceOptions_747_ = lean_ctor_get(v_toCold_744_, 11);
v_hasTrace_748_ = lean_ctor_get_uint8(v_options_745_, sizeof(void*)*1);
v___x_749_ = lean_nat_sub(v_numFields_711_, v_a_746_);
lean_dec(v_a_746_);
lean_dec(v_numFields_711_);
if (v_hasTrace_748_ == 0)
{
lean_del_object(v___x_738_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_701_);
v___y_695_ = v_a_742_;
v___y_696_ = v___x_749_;
goto v___jp_694_;
}
else
{
lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_750_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__0___closed__1));
lean_inc(v___y_701_);
v___x_751_ = l_Lean_Name_append(v___x_750_, v___y_701_);
v___x_752_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_747_, v_options_745_, v___x_751_);
lean_dec(v___x_751_);
if (v___x_752_ == 0)
{
lean_del_object(v___x_738_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_701_);
v___y_695_ = v_a_742_;
v___y_696_ = v___x_749_;
goto v___jp_694_;
}
else
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_756_; 
v___x_753_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__9, &l_Lean_Meta_injectionCore___lam__1___closed__9_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__9);
lean_inc(v___x_749_);
v___x_754_ = l_Nat_reprFast(v___x_749_);
if (v_isShared_739_ == 0)
{
lean_ctor_set_tag(v___x_738_, 3);
lean_ctor_set(v___x_738_, 0, v___x_754_);
v___x_756_ = v___x_738_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_754_);
v___x_756_ = v_reuseFailAlloc_772_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_757_ = l_Lean_MessageData_ofFormat(v___x_756_);
v___x_758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_753_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
v___x_759_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__11, &l_Lean_Meta_injectionCore___lam__1___closed__11_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__11);
v___x_760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_760_, 0, v___x_758_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
lean_inc(v_a_742_);
v___x_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_761_, 0, v_a_742_);
v___x_762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_762_, 0, v___x_760_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
v___x_763_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v___y_701_, v___x_762_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_dec_ref_known(v___x_763_, 1);
v___y_695_ = v_a_742_;
v___y_696_ = v___x_749_;
goto v___jp_694_;
}
else
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
lean_dec(v___x_749_);
lean_dec(v_a_742_);
v_a_764_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_763_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_763_);
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
}
}
}
else
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
lean_dec(v_a_742_);
lean_del_object(v___x_738_);
lean_dec(v_numFields_711_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_701_);
v_a_773_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_743_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_743_);
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
lean_del_object(v___x_738_);
lean_dec(v_numFields_711_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
v_a_781_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_788_ == 0)
{
v___x_783_ = v___x_741_;
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_741_);
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
}
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
lean_dec(v_numFields_711_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_704_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v_fvarId_673_);
lean_dec(v_mvarId_672_);
v_a_791_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_733_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_733_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_dec_ref(v___x_730_);
lean_dec(v_numFields_711_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_704_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v_fvarId_673_);
lean_dec(v_mvarId_672_);
v_a_799_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_731_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_731_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
else
{
lean_object* v___x_807_; 
lean_dec(v_numFields_711_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_700_);
lean_dec(v_fvarId_673_);
lean_inc(v___y_708_);
lean_inc_ref(v___y_707_);
lean_inc(v___y_706_);
lean_inc_ref(v___y_705_);
v___x_807_ = lean_apply_5(v___y_702_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, lean_box(0));
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; uint8_t v___x_809_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_a_808_);
lean_dec_ref_known(v___x_807_, 1);
v___x_809_ = lean_unbox(v_a_808_);
lean_dec(v_a_808_);
if (v___x_809_ == 0)
{
lean_dec(v_a_728_);
lean_dec(v___y_701_);
v___y_681_ = v___y_705_;
v___y_682_ = v___y_706_;
v___y_683_ = v___y_707_;
v___y_684_ = v___y_708_;
goto v___jp_680_;
}
else
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_810_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__13, &l_Lean_Meta_injectionCore___lam__1___closed__13_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__13);
v___x_811_ = l_Lean_indentExpr(v_a_728_);
v___x_812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_810_);
lean_ctor_set(v___x_812_, 1, v___x_811_);
v___x_813_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v___y_701_, v___x_812_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_dec_ref_known(v___x_813_, 1);
v___y_681_ = v___y_705_;
v___y_682_ = v___y_706_;
v___y_683_ = v___y_707_;
v___y_684_ = v___y_708_;
goto v___jp_680_;
}
else
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v_mvarId_672_);
lean_dec(v___x_671_);
v_a_814_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___x_813_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_813_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_a_814_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
}
else
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
lean_dec(v_a_728_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_701_);
lean_dec(v_mvarId_672_);
lean_dec(v___x_671_);
v_a_822_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_807_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_807_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_822_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
}
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
lean_dec(v_numFields_711_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v_fvarId_673_);
lean_dec(v_mvarId_672_);
lean_dec(v___x_671_);
v_a_830_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_727_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_727_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
else
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_845_; 
lean_dec(v_numFields_711_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v_fvarId_673_);
lean_dec(v_mvarId_672_);
lean_dec(v___x_671_);
v_a_838_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_845_ == 0)
{
v___x_840_ = v___x_725_;
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_725_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_843_; 
if (v_isShared_841_ == 0)
{
v___x_843_ = v___x_840_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_a_838_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
}
v___jp_846_:
{
if (lean_obj_tag(v___y_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_857_; 
v_a_856_ = lean_ctor_get(v___y_855_, 0);
lean_inc(v_a_856_);
lean_dec_ref_known(v___y_855_, 1);
lean_inc_ref(v___y_854_);
lean_inc(v___y_847_);
lean_inc_ref(v___y_852_);
lean_inc(v___y_848_);
lean_inc_ref(v___y_849_);
v___x_857_ = lean_apply_5(v___y_854_, v___y_849_, v___y_848_, v___y_852_, v___y_847_, lean_box(0));
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; uint8_t v___x_859_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_a_858_);
lean_dec_ref_known(v___x_857_, 1);
v___x_859_ = lean_unbox(v_a_858_);
lean_dec(v_a_858_);
if (v___x_859_ == 0)
{
v___y_700_ = v___y_850_;
v___y_701_ = v___y_851_;
v___y_702_ = v___y_854_;
v___y_703_ = v___y_853_;
v___y_704_ = v_a_856_;
v___y_705_ = v___y_849_;
v___y_706_ = v___y_848_;
v___y_707_ = v___y_852_;
v___y_708_ = v___y_847_;
goto v___jp_699_;
}
else
{
lean_object* v___x_860_; 
lean_inc(v___y_847_);
lean_inc_ref(v___y_852_);
lean_inc(v___y_848_);
lean_inc_ref(v___y_849_);
lean_inc(v_a_856_);
v___x_860_ = lean_infer_type(v_a_856_, v___y_849_, v___y_848_, v___y_852_, v___y_847_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_a_861_);
lean_dec_ref_known(v___x_860_, 1);
v___x_862_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__15, &l_Lean_Meta_injectionCore___lam__1___closed__15_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__15);
lean_inc(v_a_856_);
v___x_863_ = l_Lean_indentExpr(v_a_856_);
v___x_864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_862_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v___x_865_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__17, &l_Lean_Meta_injectionCore___lam__1___closed__17_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__17);
v___x_866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_864_);
lean_ctor_set(v___x_866_, 1, v___x_865_);
v___x_867_ = l_Lean_indentExpr(v_a_861_);
v___x_868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_866_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
lean_inc(v___y_851_);
v___x_869_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v___y_851_, v___x_868_, v___y_849_, v___y_848_, v___y_852_, v___y_847_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_dec_ref_known(v___x_869_, 1);
v___y_700_ = v___y_850_;
v___y_701_ = v___y_851_;
v___y_702_ = v___y_854_;
v___y_703_ = v___y_853_;
v___y_704_ = v_a_856_;
v___y_705_ = v___y_849_;
v___y_706_ = v___y_848_;
v___y_707_ = v___y_852_;
v___y_708_ = v___y_847_;
goto v___jp_699_;
}
else
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
lean_dec(v_a_856_);
lean_dec_ref(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec(v___y_847_);
lean_dec(v_fvarId_673_);
lean_dec(v_mvarId_672_);
lean_dec(v___x_671_);
v_a_870_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v___x_869_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_869_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_870_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
else
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
lean_dec(v_a_856_);
lean_dec_ref(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec(v___y_847_);
lean_dec(v_fvarId_673_);
lean_dec(v_mvarId_672_);
lean_dec(v___x_671_);
v_a_878_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_885_ == 0)
{
v___x_880_ = v___x_860_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_860_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_878_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
}
else
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
lean_dec(v_a_856_);
lean_dec_ref(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec(v___y_847_);
lean_dec(v_fvarId_673_);
lean_dec(v_mvarId_672_);
lean_dec(v___x_671_);
v_a_886_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_857_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_857_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_886_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
else
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
lean_dec_ref(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec(v___y_847_);
lean_dec(v_fvarId_673_);
lean_dec(v_mvarId_672_);
lean_dec(v___x_671_);
v_a_894_ = lean_ctor_get(v___y_855_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___y_855_);
if (v_isSharedCheck_901_ == 0)
{
v___x_896_ = v___y_855_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___y_855_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
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
v___jp_902_:
{
lean_object* v___x_913_; uint8_t v_transparency_914_; uint8_t v___x_915_; uint8_t v___x_916_; 
v___x_913_ = l_Lean_Meta_Context_config(v___y_909_);
v_transparency_914_ = lean_ctor_get_uint8(v___x_913_, 9);
lean_dec_ref(v___x_913_);
v___x_915_ = 1;
v___x_916_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_914_, v___x_915_);
if (v___x_916_ == 0)
{
lean_object* v_keyedConfig_917_; uint8_t v_trackZetaDelta_918_; lean_object* v_zetaDeltaSet_919_; lean_object* v_lctx_920_; lean_object* v_localInstances_921_; lean_object* v_defEqCtx_x3f_922_; lean_object* v_synthPendingDepth_923_; lean_object* v_customCanUnfoldPredicate_x3f_924_; uint8_t v_univApprox_925_; uint8_t v_inTypeClassResolution_926_; uint8_t v_cacheInferType_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v_keyedConfig_917_ = lean_ctor_get(v___y_909_, 0);
v_trackZetaDelta_918_ = lean_ctor_get_uint8(v___y_909_, sizeof(void*)*7);
v_zetaDeltaSet_919_ = lean_ctor_get(v___y_909_, 1);
v_lctx_920_ = lean_ctor_get(v___y_909_, 2);
v_localInstances_921_ = lean_ctor_get(v___y_909_, 3);
v_defEqCtx_x3f_922_ = lean_ctor_get(v___y_909_, 4);
v_synthPendingDepth_923_ = lean_ctor_get(v___y_909_, 5);
v_customCanUnfoldPredicate_x3f_924_ = lean_ctor_get(v___y_909_, 6);
v_univApprox_925_ = lean_ctor_get_uint8(v___y_909_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_926_ = lean_ctor_get_uint8(v___y_909_, sizeof(void*)*7 + 2);
v_cacheInferType_927_ = lean_ctor_get_uint8(v___y_909_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_917_);
v___x_928_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_915_, v_keyedConfig_917_);
lean_inc(v_customCanUnfoldPredicate_x3f_924_);
lean_inc(v_synthPendingDepth_923_);
lean_inc(v_defEqCtx_x3f_922_);
lean_inc_ref(v_localInstances_921_);
lean_inc_ref(v_lctx_920_);
lean_inc(v_zetaDeltaSet_919_);
v___x_929_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_929_, 0, v___x_928_);
lean_ctor_set(v___x_929_, 1, v_zetaDeltaSet_919_);
lean_ctor_set(v___x_929_, 2, v_lctx_920_);
lean_ctor_set(v___x_929_, 3, v_localInstances_921_);
lean_ctor_set(v___x_929_, 4, v_defEqCtx_x3f_922_);
lean_ctor_set(v___x_929_, 5, v_synthPendingDepth_923_);
lean_ctor_set(v___x_929_, 6, v_customCanUnfoldPredicate_x3f_924_);
lean_ctor_set_uint8(v___x_929_, sizeof(void*)*7, v_trackZetaDelta_918_);
lean_ctor_set_uint8(v___x_929_, sizeof(void*)*7 + 1, v_univApprox_925_);
lean_ctor_set_uint8(v___x_929_, sizeof(void*)*7 + 2, v_inTypeClassResolution_926_);
lean_ctor_set_uint8(v___x_929_, sizeof(void*)*7 + 3, v_cacheInferType_927_);
v___x_930_ = l_Lean_Meta_mkNoConfusion(v___y_903_, v___y_908_, v___x_929_, v___y_910_, v___y_911_, v___y_912_);
lean_dec_ref_known(v___x_929_, 7);
v___y_847_ = v___y_912_;
v___y_848_ = v___y_910_;
v___y_849_ = v___y_909_;
v___y_850_ = v___y_904_;
v___y_851_ = v___y_905_;
v___y_852_ = v___y_911_;
v___y_853_ = v___y_907_;
v___y_854_ = v___y_906_;
v___y_855_ = v___x_930_;
goto v___jp_846_;
}
else
{
lean_object* v___x_931_; 
v___x_931_ = l_Lean_Meta_mkNoConfusion(v___y_903_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
v___y_847_ = v___y_912_;
v___y_848_ = v___y_910_;
v___y_849_ = v___y_909_;
v___y_850_ = v___y_904_;
v___y_851_ = v___y_905_;
v___y_852_ = v___y_911_;
v___y_853_ = v___y_907_;
v___y_854_ = v___y_906_;
v___y_855_ = v___x_931_;
goto v___jp_846_;
}
}
v___jp_932_:
{
lean_object* v___x_935_; lean_object* v___x_936_; uint8_t v___x_937_; 
v___x_935_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__19));
v___x_936_ = lean_unsigned_to_nat(3u);
v___x_937_ = l_Lean_Expr_isAppOfArity(v_type_933_, v___x_935_, v___x_936_);
if (v___x_937_ == 0)
{
lean_object* v___x_938_; lean_object* v___x_939_; 
lean_dec_ref(v_prf_934_);
lean_dec_ref(v_type_933_);
lean_dec_ref(v___x_674_);
lean_dec(v_fvarId_673_);
v___x_938_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__23, &l_Lean_Meta_injectionCore___lam__1___closed__23_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__23);
v___x_939_ = l_Lean_Meta_throwTacticEx___redArg(v___x_671_, v_mvarId_672_, v___x_938_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
return v___x_939_;
}
else
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_940_ = l_Lean_Expr_appFn_x21(v_type_933_);
v___x_941_ = l_Lean_Expr_appArg_x21(v___x_940_);
lean_dec_ref(v___x_940_);
v___x_942_ = l_Lean_Expr_appArg_x21(v_type_933_);
lean_dec_ref(v_type_933_);
lean_inc(v_mvarId_672_);
v___x_943_ = l_Lean_MVarId_getType(v_mvarId_672_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_a_944_; lean_object* v___x_945_; 
v_a_944_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_a_944_);
lean_dec_ref_known(v___x_943_, 1);
v___x_945_ = l_Lean_Meta_isConstructorApp_x27_x3f(v___x_941_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_946_; lean_object* v___x_947_; 
v_a_946_ = lean_ctor_get(v___x_945_, 0);
lean_inc(v_a_946_);
lean_dec_ref_known(v___x_945_, 1);
v___x_947_ = l_Lean_Meta_isConstructorApp_x27_x3f(v___x_942_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
if (lean_obj_tag(v___x_947_) == 0)
{
if (lean_obj_tag(v_a_946_) == 1)
{
lean_object* v_a_948_; 
v_a_948_ = lean_ctor_get(v___x_947_, 0);
lean_inc(v_a_948_);
lean_dec_ref_known(v___x_947_, 1);
if (lean_obj_tag(v_a_948_) == 1)
{
lean_object* v_val_949_; lean_object* v_val_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___f_954_; lean_object* v___x_955_; lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_989_; 
v_val_949_ = lean_ctor_get(v_a_946_, 0);
lean_inc(v_val_949_);
lean_dec_ref_known(v_a_946_, 1);
v_val_950_ = lean_ctor_get(v_a_948_, 0);
lean_inc(v_val_950_);
lean_dec_ref_known(v_a_948_, 1);
v___x_951_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__24));
v___x_952_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__25));
v___x_953_ = l_Lean_Name_mkStr3(v___x_951_, v___x_952_, v___x_674_);
lean_inc_n(v___x_953_, 2);
v___f_954_ = lean_alloc_closure((void*)(l_Lean_Meta_injectionCore___lam__0___boxed), 6, 1);
lean_closure_set(v___f_954_, 0, v___x_953_);
v___x_955_ = l_Lean_Meta_injectionCore___lam__0(v___x_953_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
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
v___y_903_ = v_a_944_;
v___y_904_ = v_val_949_;
v___y_905_ = v___x_953_;
v___y_906_ = v___f_954_;
v___y_907_ = v_val_950_;
v___y_908_ = v_prf_934_;
v___y_909_ = v___y_675_;
v___y_910_ = v___y_676_;
v___y_911_ = v___y_677_;
v___y_912_ = v___y_678_;
goto v___jp_902_;
}
else
{
lean_object* v___x_961_; 
lean_inc(v___y_678_);
lean_inc_ref(v___y_677_);
lean_inc(v___y_676_);
lean_inc_ref(v___y_675_);
lean_inc_ref(v_prf_934_);
v___x_961_ = lean_infer_type(v_prf_934_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_a_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_969_; 
v_a_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_a_962_);
lean_dec_ref_known(v___x_961_, 1);
v___x_963_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__27, &l_Lean_Meta_injectionCore___lam__1___closed__27_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__27);
v___x_964_ = l_Lean_MessageData_ofExpr(v_a_962_);
v___x_965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_963_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___x_966_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__29, &l_Lean_Meta_injectionCore___lam__1___closed__29_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__29);
v___x_967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_965_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
lean_inc(v_mvarId_672_);
if (v_isShared_959_ == 0)
{
lean_ctor_set_tag(v___x_958_, 1);
lean_ctor_set(v___x_958_, 0, v_mvarId_672_);
v___x_969_ = v___x_958_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_mvarId_672_);
v___x_969_ = v_reuseFailAlloc_980_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_967_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
lean_inc(v___x_953_);
v___x_971_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v___x_953_, v___x_970_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_dec_ref_known(v___x_971_, 1);
v___y_903_ = v_a_944_;
v___y_904_ = v_val_949_;
v___y_905_ = v___x_953_;
v___y_906_ = v___f_954_;
v___y_907_ = v_val_950_;
v___y_908_ = v_prf_934_;
v___y_909_ = v___y_675_;
v___y_910_ = v___y_676_;
v___y_911_ = v___y_677_;
v___y_912_ = v___y_678_;
goto v___jp_902_;
}
else
{
lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_979_; 
lean_dec_ref(v___f_954_);
lean_dec(v___x_953_);
lean_dec(v_val_950_);
lean_dec(v_val_949_);
lean_dec(v_a_944_);
lean_dec_ref(v_prf_934_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v_fvarId_673_);
lean_dec(v_mvarId_672_);
lean_dec(v___x_671_);
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
lean_dec_ref(v___f_954_);
lean_dec(v___x_953_);
lean_dec(v_val_950_);
lean_dec(v_val_949_);
lean_dec(v_a_944_);
lean_dec_ref(v_prf_934_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v_fvarId_673_);
lean_dec(v_mvarId_672_);
lean_dec(v___x_671_);
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
lean_dec_ref_known(v_a_946_, 1);
lean_dec(v_a_948_);
lean_dec(v_a_944_);
lean_dec_ref(v_prf_934_);
lean_dec_ref(v___x_674_);
lean_dec(v_fvarId_673_);
v___y_688_ = v___y_675_;
v___y_689_ = v___y_676_;
v___y_690_ = v___y_677_;
v___y_691_ = v___y_678_;
goto v___jp_687_;
}
}
else
{
lean_dec_ref_known(v___x_947_, 1);
lean_dec(v_a_946_);
lean_dec(v_a_944_);
lean_dec_ref(v_prf_934_);
lean_dec_ref(v___x_674_);
lean_dec(v_fvarId_673_);
v___y_688_ = v___y_675_;
v___y_689_ = v___y_676_;
v___y_690_ = v___y_677_;
v___y_691_ = v___y_678_;
goto v___jp_687_;
}
}
else
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
lean_dec(v_a_946_);
lean_dec(v_a_944_);
lean_dec_ref(v_prf_934_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec_ref(v___x_674_);
lean_dec(v_fvarId_673_);
lean_dec(v_mvarId_672_);
lean_dec(v___x_671_);
v_a_990_ = lean_ctor_get(v___x_947_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_947_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_947_);
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
lean_dec(v_a_944_);
lean_dec_ref(v___x_942_);
lean_dec_ref(v_prf_934_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec_ref(v___x_674_);
lean_dec(v_fvarId_673_);
lean_dec(v_mvarId_672_);
lean_dec(v___x_671_);
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
lean_dec_ref(v___x_942_);
lean_dec_ref(v___x_941_);
lean_dec_ref(v_prf_934_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec_ref(v___x_674_);
lean_dec(v_fvarId_673_);
lean_dec(v_mvarId_672_);
lean_dec(v___x_671_);
v_a_1006_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_943_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_943_);
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
LEAN_EXPORT void l_Lean_Meta_injectionCore___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_671_ = stack[0].m_obj;
lean_object* v_mvarId_672_ = stack[1].m_obj;
lean_object* v_fvarId_673_ = stack[2].m_obj;
lean_object* v___x_674_ = stack[3].m_obj;
lean_object* v___y_675_ = stack[4].m_obj;
lean_object* v___y_676_ = stack[5].m_obj;
lean_object* v___y_677_ = stack[6].m_obj;
lean_object* v___y_678_ = stack[7].m_obj;
lean_object* v_res_1086_;
v_res_1086_ = l_Lean_Meta_injectionCore___lam__1(v___x_671_, v_mvarId_672_, v_fvarId_673_, v___x_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
stack->m_obj
 = v_res_1086_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___lam__1___boxed(lean_object* v___x_1087_, lean_object* v_mvarId_1088_, lean_object* v_fvarId_1089_, lean_object* v___x_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_Lean_Meta_injectionCore___lam__1(v___x_1087_, v_mvarId_1088_, v_fvarId_1089_, v___x_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
return v_res_1096_;
}
}
lean_object* l_Lean_Meta_injectionCore(lean_object* v_mvarId_1100_, lean_object* v_fvarId_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___f_1109_; lean_object* v___x_1110_; 
v___x_1107_ = ((lean_object*)(l_Lean_Meta_injectionCore___closed__0));
v___x_1108_ = ((lean_object*)(l_Lean_Meta_injectionCore___closed__1));
lean_inc(v_mvarId_1100_);
v___f_1109_ = lean_alloc_closure((void*)(l_Lean_Meta_injectionCore___lam__1___boxed), 9, 4);
lean_closure_set(v___f_1109_, 0, v___x_1108_);
lean_closure_set(v___f_1109_, 1, v_mvarId_1100_);
lean_closure_set(v___f_1109_, 2, v_fvarId_1101_);
lean_closure_set(v___f_1109_, 3, v___x_1107_);
v___x_1110_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg(v_mvarId_1100_, v___f_1109_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
return v___x_1110_;
}
}
LEAN_EXPORT void l_Lean_Meta_injectionCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1100_ = stack[0].m_obj;
lean_object* v_fvarId_1101_ = stack[1].m_obj;
lean_object* v_a_1102_ = stack[2].m_obj;
lean_object* v_a_1103_ = stack[3].m_obj;
lean_object* v_a_1104_ = stack[4].m_obj;
lean_object* v_a_1105_ = stack[5].m_obj;
lean_object* v_res_1111_;
v_res_1111_ = l_Lean_Meta_injectionCore(v_mvarId_1100_, v_fvarId_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
stack->m_obj
 = v_res_1111_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___boxed(lean_object* v_mvarId_1112_, lean_object* v_fvarId_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lean_Meta_injectionCore(v_mvarId_1112_, v_fvarId_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
lean_dec(v_a_1115_);
lean_dec_ref(v_a_1114_);
return v_res_1119_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0(lean_object* v_mvarId_1120_, lean_object* v_val_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(v_mvarId_1120_, v_val_1121_, v___y_1123_);
return v___x_1127_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1120_ = stack[0].m_obj;
lean_object* v_val_1121_ = stack[1].m_obj;
lean_object* v___y_1122_ = stack[2].m_obj;
lean_object* v___y_1123_ = stack[3].m_obj;
lean_object* v___y_1124_ = stack[4].m_obj;
lean_object* v___y_1125_ = stack[5].m_obj;
lean_object* v_res_1128_;
v_res_1128_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0(v_mvarId_1120_, v_val_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
stack->m_obj
 = v_res_1128_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___boxed(lean_object* v_mvarId_1129_, lean_object* v_val_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0(v_mvarId_1129_, v_val_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0(lean_object* v_00_u03b2_1137_, lean_object* v_x_1138_, lean_object* v_x_1139_, lean_object* v_x_1140_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0___redArg(v_x_1138_, v_x_1139_, v_x_1140_);
return v___x_1141_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1142_, lean_object* v_x_1143_, size_t v_x_1144_, size_t v_x_1145_, lean_object* v_x_1146_, lean_object* v_x_1147_){
_start:
{
lean_object* v___x_1148_; 
v___x_1148_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(v_x_1143_, v_x_1144_, v_x_1145_, v_x_1146_, v_x_1147_);
return v___x_1148_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1143_ = stack[1].m_obj;
size_t v_x_1144_ = stack[2].m_num;
size_t v_x_1145_ = stack[3].m_num;
lean_object* v_x_1146_ = stack[4].m_obj;
lean_object* v_x_1147_ = stack[5].m_obj;
lean_object* v_res_1149_;
v_res_1149_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2(lean_box(0), v_x_1143_, v_x_1144_, v_x_1145_, v_x_1146_, v_x_1147_);
stack->m_obj
 = v_res_1149_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1150_, lean_object* v_x_1151_, lean_object* v_x_1152_, lean_object* v_x_1153_, lean_object* v_x_1154_, lean_object* v_x_1155_){
_start:
{
size_t v_x_16495__boxed_1156_; size_t v_x_16496__boxed_1157_; lean_object* v_res_1158_; 
v_x_16495__boxed_1156_ = lean_unbox_usize(v_x_1152_);
lean_dec(v_x_1152_);
v_x_16496__boxed_1157_ = lean_unbox_usize(v_x_1153_);
lean_dec(v_x_1153_);
v_res_1158_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2(v_00_u03b2_1150_, v_x_1151_, v_x_16495__boxed_1156_, v_x_16496__boxed_1157_, v_x_1154_, v_x_1155_);
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
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_1164_, size_t v_depth_1165_, lean_object* v_keys_1166_, lean_object* v_vals_1167_, lean_object* v_heq_1168_, lean_object* v_i_1169_, lean_object* v_entries_1170_){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___redArg(v_depth_1165_, v_keys_1166_, v_vals_1167_, v_i_1169_, v_entries_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1165_ = stack[1].m_num;
lean_object* v_keys_1166_ = stack[2].m_obj;
lean_object* v_vals_1167_ = stack[3].m_obj;
lean_object* v_i_1169_ = stack[5].m_obj;
lean_object* v_entries_1170_ = stack[6].m_obj;
lean_object* v_res_1172_;
v_res_1172_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6(lean_box(0), v_depth_1165_, v_keys_1166_, v_vals_1167_, lean_box(0), v_i_1169_, v_entries_1170_);
stack->m_obj
 = v_res_1172_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1173_, lean_object* v_depth_1174_, lean_object* v_keys_1175_, lean_object* v_vals_1176_, lean_object* v_heq_1177_, lean_object* v_i_1178_, lean_object* v_entries_1179_){
_start:
{
size_t v_depth_boxed_1180_; lean_object* v_res_1181_; 
v_depth_boxed_1180_ = lean_unbox_usize(v_depth_1174_);
lean_dec(v_depth_1174_);
v_res_1181_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6(v_00_u03b2_1173_, v_depth_boxed_1180_, v_keys_1175_, v_vals_1176_, v_heq_1177_, v_i_1178_, v_entries_1179_);
lean_dec_ref(v_vals_1176_);
lean_dec_ref(v_keys_1175_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5_spec__6(lean_object* v_00_u03b2_1182_, lean_object* v_x_1183_, lean_object* v_x_1184_, lean_object* v_x_1185_, lean_object* v_x_1186_){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(v_x_1183_, v_x_1184_, v_x_1185_, v_x_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorIdx___impl(lean_object* v_x_1188_){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = lean_obj_tag_nat(v_x_1188_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorIdx___impl___boxed(lean_object* v_x_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Lean_Meta_InjectionResult_ctorIdx___impl(v_x_1190_);
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
lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go(uint8_t v_tryToClear_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_){
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go_0interp(lean_interpreter_value* stack)
{
uint8_t v_tryToClear_1226_ = stack[0].m_num;
lean_object* v_a_1227_ = stack[1].m_obj;
lean_object* v_a_1228_ = stack[2].m_obj;
lean_object* v_a_1229_ = stack[3].m_obj;
lean_object* v_a_1230_ = stack[4].m_obj;
lean_object* v_a_1231_ = stack[5].m_obj;
lean_object* v_a_1232_ = stack[6].m_obj;
lean_object* v_a_1233_ = stack[7].m_obj;
lean_object* v_a_1234_ = stack[8].m_obj;
lean_object* v_res_1296_;
v_res_1296_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go(v_tryToClear_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_);
stack->m_obj
 = v_res_1296_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go___boxed(lean_object* v_tryToClear_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_){
_start:
{
uint8_t v_tryToClear_boxed_1307_; lean_object* v_res_1308_; 
v_tryToClear_boxed_1307_ = lean_unbox(v_tryToClear_1297_);
v_res_1308_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go(v_tryToClear_boxed_1307_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_);
lean_dec(v_a_1305_);
lean_dec_ref(v_a_1304_);
lean_dec(v_a_1303_);
lean_dec_ref(v_a_1302_);
return v_res_1308_;
}
}
static lean_object* _init_l_Lean_Meta_injectionIntro___closed__2(void){
_start:
{
lean_object* v_cls_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
v_cls_1315_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__1));
v___x_1316_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__0___closed__1));
v___x_1317_ = l_Lean_Name_append(v___x_1316_, v_cls_1315_);
return v___x_1317_;
}
}
static lean_object* _init_l_Lean_Meta_injectionIntro___closed__4(void){
_start:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1319_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__3));
v___x_1320_ = l_Lean_stringToMessageData(v___x_1319_);
return v___x_1320_;
}
}
static lean_object* _init_l_Lean_Meta_injectionIntro___closed__6(void){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1322_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__5));
v___x_1323_ = l_Lean_stringToMessageData(v___x_1322_);
return v___x_1323_;
}
}
lean_object* l_Lean_Meta_injectionIntro(lean_object* v_mvarId_1324_, lean_object* v_numEqs_1325_, lean_object* v_newNames_1326_, uint8_t v_tryToClear_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_){
_start:
{
lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v_toCold_1340_; lean_object* v_options_1341_; uint8_t v_hasTrace_1342_; 
v_toCold_1340_ = lean_ctor_get(v_a_1330_, 0);
v_options_1341_ = lean_ctor_get(v_toCold_1340_, 2);
v_hasTrace_1342_ = lean_ctor_get_uint8(v_options_1341_, sizeof(void*)*1);
if (v_hasTrace_1342_ == 0)
{
v___y_1334_ = v_a_1328_;
v___y_1335_ = v_a_1329_;
v___y_1336_ = v_a_1330_;
v___y_1337_ = v_a_1331_;
goto v___jp_1333_;
}
else
{
lean_object* v_inheritedTraceOptions_1343_; lean_object* v_cls_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; 
v_inheritedTraceOptions_1343_ = lean_ctor_get(v_toCold_1340_, 11);
v_cls_1344_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__1));
v___x_1345_ = lean_obj_once(&l_Lean_Meta_injectionIntro___closed__2, &l_Lean_Meta_injectionIntro___closed__2_once, _init_l_Lean_Meta_injectionIntro___closed__2);
v___x_1346_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1343_, v_options_1341_, v___x_1345_);
if (v___x_1346_ == 0)
{
v___y_1334_ = v_a_1328_;
v___y_1335_ = v_a_1329_;
v___y_1336_ = v_a_1330_;
v___y_1337_ = v_a_1331_;
goto v___jp_1333_;
}
else
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1347_ = lean_obj_once(&l_Lean_Meta_injectionIntro___closed__4, &l_Lean_Meta_injectionIntro___closed__4_once, _init_l_Lean_Meta_injectionIntro___closed__4);
lean_inc(v_numEqs_1325_);
v___x_1348_ = l_Nat_reprFast(v_numEqs_1325_);
v___x_1349_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1348_);
v___x_1350_ = l_Lean_MessageData_ofFormat(v___x_1349_);
v___x_1351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1347_);
lean_ctor_set(v___x_1351_, 1, v___x_1350_);
v___x_1352_ = lean_obj_once(&l_Lean_Meta_injectionIntro___closed__6, &l_Lean_Meta_injectionIntro___closed__6_once, _init_l_Lean_Meta_injectionIntro___closed__6);
v___x_1353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1351_);
lean_ctor_set(v___x_1353_, 1, v___x_1352_);
lean_inc(v_mvarId_1324_);
v___x_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1354_, 0, v_mvarId_1324_);
v___x_1355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1353_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
v___x_1356_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v_cls_1344_, v___x_1355_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_dec_ref_known(v___x_1356_, 1);
v___y_1334_ = v_a_1328_;
v___y_1335_ = v_a_1329_;
v___y_1336_ = v_a_1330_;
v___y_1337_ = v_a_1331_;
goto v___jp_1333_;
}
else
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
lean_dec(v_newNames_1326_);
lean_dec(v_numEqs_1325_);
lean_dec(v_mvarId_1324_);
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___x_1356_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1356_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
}
v___jp_1333_:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1338_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__0));
v___x_1339_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go(v_tryToClear_1327_, v_numEqs_1325_, v_mvarId_1324_, v___x_1338_, v_newNames_1326_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
return v___x_1339_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_injectionIntro_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1324_ = stack[0].m_obj;
lean_object* v_numEqs_1325_ = stack[1].m_obj;
lean_object* v_newNames_1326_ = stack[2].m_obj;
uint8_t v_tryToClear_1327_ = stack[3].m_num;
lean_object* v_a_1328_ = stack[4].m_obj;
lean_object* v_a_1329_ = stack[5].m_obj;
lean_object* v_a_1330_ = stack[6].m_obj;
lean_object* v_a_1331_ = stack[7].m_obj;
lean_object* v_res_1365_;
v_res_1365_ = l_Lean_Meta_injectionIntro(v_mvarId_1324_, v_numEqs_1325_, v_newNames_1326_, v_tryToClear_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_);
stack->m_obj
 = v_res_1365_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro___boxed(lean_object* v_mvarId_1366_, lean_object* v_numEqs_1367_, lean_object* v_newNames_1368_, lean_object* v_tryToClear_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_){
_start:
{
uint8_t v_tryToClear_boxed_1375_; lean_object* v_res_1376_; 
v_tryToClear_boxed_1375_ = lean_unbox(v_tryToClear_1369_);
v_res_1376_ = l_Lean_Meta_injectionIntro(v_mvarId_1366_, v_numEqs_1367_, v_newNames_1368_, v_tryToClear_boxed_1375_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_);
lean_dec(v_a_1373_);
lean_dec_ref(v_a_1372_);
lean_dec(v_a_1371_);
lean_dec_ref(v_a_1370_);
return v_res_1376_;
}
}
lean_object* l_Lean_Meta_injection(lean_object* v_mvarId_1377_, lean_object* v_fvarId_1378_, lean_object* v_newNames_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_){
_start:
{
lean_object* v___x_1385_; 
v___x_1385_ = l_Lean_Meta_injectionCore(v_mvarId_1377_, v_fvarId_1378_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1398_; 
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1388_ = v___x_1385_;
v_isShared_1389_ = v_isSharedCheck_1398_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1385_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1398_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
if (lean_obj_tag(v_a_1386_) == 0)
{
lean_object* v___x_1390_; lean_object* v___x_1392_; 
lean_dec(v_newNames_1379_);
v___x_1390_ = lean_box(0);
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 0, v___x_1390_);
v___x_1392_ = v___x_1388_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1390_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
else
{
lean_object* v_mvarId_1394_; lean_object* v_numNewEqs_1395_; uint8_t v___x_1396_; lean_object* v___x_1397_; 
lean_del_object(v___x_1388_);
v_mvarId_1394_ = lean_ctor_get(v_a_1386_, 0);
lean_inc(v_mvarId_1394_);
v_numNewEqs_1395_ = lean_ctor_get(v_a_1386_, 1);
lean_inc(v_numNewEqs_1395_);
lean_dec_ref_known(v_a_1386_, 2);
v___x_1396_ = 1;
v___x_1397_ = l_Lean_Meta_injectionIntro(v_mvarId_1394_, v_numNewEqs_1395_, v_newNames_1379_, v___x_1396_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
return v___x_1397_;
}
}
}
else
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1406_; 
lean_dec(v_newNames_1379_);
v_a_1399_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1401_ = v___x_1385_;
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1385_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1402_ == 0)
{
v___x_1404_ = v___x_1401_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1399_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_injection_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1377_ = stack[0].m_obj;
lean_object* v_fvarId_1378_ = stack[1].m_obj;
lean_object* v_newNames_1379_ = stack[2].m_obj;
lean_object* v_a_1380_ = stack[3].m_obj;
lean_object* v_a_1381_ = stack[4].m_obj;
lean_object* v_a_1382_ = stack[5].m_obj;
lean_object* v_a_1383_ = stack[6].m_obj;
lean_object* v_res_1407_;
v_res_1407_ = l_Lean_Meta_injection(v_mvarId_1377_, v_fvarId_1378_, v_newNames_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
stack->m_obj
 = v_res_1407_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_injection___boxed(lean_object* v_mvarId_1408_, lean_object* v_fvarId_1409_, lean_object* v_newNames_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_Meta_injection(v_mvarId_1408_, v_fvarId_1409_, v_newNames_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_);
lean_dec(v_a_1414_);
lean_dec_ref(v_a_1413_);
lean_dec(v_a_1412_);
lean_dec_ref(v_a_1411_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorIdx___impl(lean_object* v_x_1417_){
_start:
{
lean_object* v___x_1418_; 
v___x_1418_ = lean_obj_tag_nat(v_x_1417_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorIdx___impl___boxed(lean_object* v_x_1419_){
_start:
{
lean_object* v_res_1420_; 
v_res_1420_ = l_Lean_Meta_InjectionsResult_ctorIdx___impl(v_x_1419_);
lean_dec(v_x_1419_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorElim___redArg(lean_object* v_t_1421_, lean_object* v_k_1422_){
_start:
{
if (lean_obj_tag(v_t_1421_) == 0)
{
return v_k_1422_;
}
else
{
lean_object* v_mvarId_1423_; lean_object* v_remainingNames_1424_; lean_object* v_forbidden_1425_; lean_object* v___x_1426_; 
v_mvarId_1423_ = lean_ctor_get(v_t_1421_, 0);
lean_inc(v_mvarId_1423_);
v_remainingNames_1424_ = lean_ctor_get(v_t_1421_, 1);
lean_inc(v_remainingNames_1424_);
v_forbidden_1425_ = lean_ctor_get(v_t_1421_, 2);
lean_inc(v_forbidden_1425_);
lean_dec_ref_known(v_t_1421_, 3);
v___x_1426_ = lean_apply_3(v_k_1422_, v_mvarId_1423_, v_remainingNames_1424_, v_forbidden_1425_);
return v___x_1426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorElim(lean_object* v_motive_1427_, lean_object* v_ctorIdx_1428_, lean_object* v_t_1429_, lean_object* v_h_1430_, lean_object* v_k_1431_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1429_, v_k_1431_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorElim___boxed(lean_object* v_motive_1433_, lean_object* v_ctorIdx_1434_, lean_object* v_t_1435_, lean_object* v_h_1436_, lean_object* v_k_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l_Lean_Meta_InjectionsResult_ctorElim(v_motive_1433_, v_ctorIdx_1434_, v_t_1435_, v_h_1436_, v_k_1437_);
lean_dec(v_ctorIdx_1434_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_solved_elim___redArg(lean_object* v_t_1439_, lean_object* v_solved_1440_){
_start:
{
lean_object* v___x_1441_; 
v___x_1441_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1439_, v_solved_1440_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_solved_elim(lean_object* v_motive_1442_, lean_object* v_t_1443_, lean_object* v_h_1444_, lean_object* v_solved_1445_){
_start:
{
lean_object* v___x_1446_; 
v___x_1446_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1443_, v_solved_1445_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_subgoal_elim___redArg(lean_object* v_t_1447_, lean_object* v_subgoal_1448_){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1447_, v_subgoal_1448_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_subgoal_elim(lean_object* v_motive_1450_, lean_object* v_t_1451_, lean_object* v_h_1452_, lean_object* v_subgoal_1453_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1451_, v_subgoal_1453_);
return v___x_1454_;
}
}
lean_object* l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(lean_object* v_x_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
lean_object* v___x_1461_; 
v___x_1461_ = l_Lean_Meta_saveState___redArg(v___y_1457_, v___y_1459_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v_a_1462_; lean_object* v___x_1463_; 
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
lean_inc(v_a_1462_);
lean_dec_ref_known(v___x_1461_, 1);
lean_inc(v___y_1459_);
lean_inc_ref(v___y_1458_);
lean_inc(v___y_1457_);
lean_inc_ref(v___y_1456_);
v___x_1463_ = lean_apply_5(v_x_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, lean_box(0));
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_dec(v_a_1462_);
return v___x_1463_;
}
else
{
lean_object* v_a_1464_; uint8_t v___y_1466_; uint8_t v___x_1484_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
lean_inc(v_a_1464_);
v___x_1484_ = l_Lean_Exception_isInterrupt(v_a_1464_);
if (v___x_1484_ == 0)
{
uint8_t v___x_1485_; 
lean_inc(v_a_1464_);
v___x_1485_ = l_Lean_Exception_isRuntime(v_a_1464_);
v___y_1466_ = v___x_1485_;
goto v___jp_1465_;
}
else
{
v___y_1466_ = v___x_1484_;
goto v___jp_1465_;
}
v___jp_1465_:
{
if (v___y_1466_ == 0)
{
lean_object* v___x_1467_; 
lean_dec_ref_known(v___x_1463_, 1);
v___x_1467_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1462_, v___y_1457_, v___y_1459_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1474_; 
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1474_ == 0)
{
lean_object* v_unused_1475_; 
v_unused_1475_ = lean_ctor_get(v___x_1467_, 0);
lean_dec(v_unused_1475_);
v___x_1469_ = v___x_1467_;
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
else
{
lean_dec(v___x_1467_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
lean_ctor_set_tag(v___x_1469_, 1);
lean_ctor_set(v___x_1469_, 0, v_a_1464_);
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1464_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
else
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
lean_dec(v_a_1464_);
v_a_1476_ = lean_ctor_get(v___x_1467_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1467_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1467_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1481_; 
if (v_isShared_1479_ == 0)
{
v___x_1481_ = v___x_1478_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1476_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
}
else
{
lean_dec(v_a_1464_);
lean_dec(v_a_1462_);
return v___x_1463_;
}
}
}
}
else
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1493_; 
lean_dec_ref(v_x_1455_);
v_a_1486_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1488_ = v___x_1461_;
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1461_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1491_; 
if (v_isShared_1489_ == 0)
{
v___x_1491_ = v___x_1488_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_a_1486_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1455_ = stack[0].m_obj;
lean_object* v___y_1456_ = stack[1].m_obj;
lean_object* v___y_1457_ = stack[2].m_obj;
lean_object* v___y_1458_ = stack[3].m_obj;
lean_object* v___y_1459_ = stack[4].m_obj;
lean_object* v_res_1494_;
v_res_1494_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(v_x_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
stack->m_obj
 = v_res_1494_;
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg___boxed(lean_object* v_x_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(v_x_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
return v_res_1501_;
}
}
lean_object* l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1(lean_object* v_00_u03b1_1502_, lean_object* v_x_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(v_x_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
return v___x_1509_;
}
}
LEAN_EXPORT void l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1503_ = stack[1].m_obj;
lean_object* v___y_1504_ = stack[2].m_obj;
lean_object* v___y_1505_ = stack[3].m_obj;
lean_object* v___y_1506_ = stack[4].m_obj;
lean_object* v___y_1507_ = stack[5].m_obj;
lean_object* v_res_1510_;
v_res_1510_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1(lean_box(0), v_x_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
stack->m_obj
 = v_res_1510_;
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___boxed(lean_object* v_00_u03b1_1511_, lean_object* v_x_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1(v_00_u03b1_1511_, v_x_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
return v_res_1518_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(lean_object* v_k_1519_, lean_object* v_t_1520_){
_start:
{
if (lean_obj_tag(v_t_1520_) == 0)
{
lean_object* v_k_1521_; lean_object* v_l_1522_; lean_object* v_r_1523_; uint8_t v___x_1524_; 
v_k_1521_ = lean_ctor_get(v_t_1520_, 1);
v_l_1522_ = lean_ctor_get(v_t_1520_, 3);
v_r_1523_ = lean_ctor_get(v_t_1520_, 4);
v___x_1524_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1519_, v_k_1521_);
switch(v___x_1524_)
{
case 0:
{
v_t_1520_ = v_l_1522_;
goto _start;
}
case 1:
{
uint8_t v___x_1526_; 
v___x_1526_ = 1;
return v___x_1526_;
}
default: 
{
v_t_1520_ = v_r_1523_;
goto _start;
}
}
}
else
{
uint8_t v___x_1528_; 
v___x_1528_ = 0;
return v___x_1528_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1519_ = stack[0].m_obj;
lean_object* v_t_1520_ = stack[1].m_obj;
uint8_t v_res_1529_;
v_res_1529_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(v_k_1519_, v_t_1520_);
stack->m_num = v_res_1529_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg___boxed(lean_object* v_k_1530_, lean_object* v_t_1531_){
_start:
{
uint8_t v_res_1532_; lean_object* v_r_1533_; 
v_res_1532_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(v_k_1530_, v_t_1531_);
lean_dec(v_t_1531_);
lean_dec(v_k_1530_);
v_r_1533_ = lean_box(v_res_1532_);
return v_r_1533_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4(void){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__3));
v___x_1541_ = l_Lean_MessageData_ofFormat(v___x_1540_);
return v___x_1541_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5(void){
_start:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4, &l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4_once, _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4);
v___x_1543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0___boxed(lean_object* v_mvarId_1544_, lean_object* v_head_1545_, lean_object* v_newNames_1546_, lean_object* v_tail_1547_, lean_object* v_forbidden_1548_, lean_object* v_n_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0(v_mvarId_1544_, v_head_1545_, v_newNames_1546_, v_tail_1547_, v_forbidden_1548_, v_n_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
return v_res_1555_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go(lean_object* v_depth_1556_, lean_object* v_fvarIds_1557_, lean_object* v_mvarId_1558_, lean_object* v_newNames_1559_, lean_object* v_forbidden_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_){
_start:
{
lean_object* v_zero_1566_; uint8_t v_isZero_1567_; 
v_zero_1566_ = lean_unsigned_to_nat(0u);
v_isZero_1567_ = lean_nat_dec_eq(v_depth_1556_, v_zero_1566_);
if (v_isZero_1567_ == 1)
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
lean_dec(v_forbidden_1560_);
lean_dec(v_newNames_1559_);
lean_dec(v_fvarIds_1557_);
lean_dec(v_depth_1556_);
v___x_1568_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__1));
v___x_1569_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5, &l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5_once, _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5);
v___x_1570_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1568_, v_mvarId_1558_, v___x_1569_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_);
return v___x_1570_;
}
else
{
if (lean_obj_tag(v_fvarIds_1557_) == 0)
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
lean_dec(v_depth_1556_);
v___x_1571_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1571_, 0, v_mvarId_1558_);
lean_ctor_set(v___x_1571_, 1, v_newNames_1559_);
lean_ctor_set(v___x_1571_, 2, v_forbidden_1560_);
v___x_1572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
return v___x_1572_;
}
else
{
lean_object* v_head_1573_; lean_object* v_tail_1574_; lean_object* v_one_1575_; lean_object* v_n_1576_; lean_object* v___x_1577_; lean_object* v___y_1579_; uint8_t v___y_1580_; uint8_t v___x_1582_; 
v_head_1573_ = lean_ctor_get(v_fvarIds_1557_, 0);
lean_inc(v_head_1573_);
v_tail_1574_ = lean_ctor_get(v_fvarIds_1557_, 1);
lean_inc(v_tail_1574_);
lean_dec_ref_known(v_fvarIds_1557_, 2);
v_one_1575_ = lean_unsigned_to_nat(1u);
v_n_1576_ = lean_nat_sub(v_depth_1556_, v_one_1575_);
lean_dec(v_depth_1556_);
v___x_1577_ = lean_nat_add(v_n_1576_, v_one_1575_);
v___x_1582_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(v_head_1573_, v_forbidden_1560_);
if (v___x_1582_ == 0)
{
lean_object* v___f_1583_; lean_object* v___x_1584_; 
lean_inc(v_forbidden_1560_);
lean_inc(v_tail_1574_);
lean_inc(v_newNames_1559_);
lean_inc(v_head_1573_);
lean_inc(v_mvarId_1558_);
v___f_1583_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0___boxed), 11, 6);
lean_closure_set(v___f_1583_, 0, v_mvarId_1558_);
lean_closure_set(v___f_1583_, 1, v_head_1573_);
lean_closure_set(v___f_1583_, 2, v_newNames_1559_);
lean_closure_set(v___f_1583_, 3, v_tail_1574_);
lean_closure_set(v___f_1583_, 4, v_forbidden_1560_);
lean_closure_set(v___f_1583_, 5, v_n_1576_);
v___x_1584_ = l_Lean_FVarId_getType___redArg(v_head_1573_, v_a_1561_, v_a_1563_, v_a_1564_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1586_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref_known(v___x_1584_, 1);
v___x_1586_ = l_Lean_Meta_matchEqHEq_x3f(v_a_1585_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_a_1587_);
lean_dec_ref_known(v___x_1586_, 1);
if (lean_obj_tag(v_a_1587_) == 1)
{
lean_object* v_val_1588_; lean_object* v_snd_1589_; lean_object* v_fst_1590_; lean_object* v_snd_1591_; lean_object* v___x_1592_; 
v_val_1588_ = lean_ctor_get(v_a_1587_, 0);
lean_inc(v_val_1588_);
lean_dec_ref_known(v_a_1587_, 1);
v_snd_1589_ = lean_ctor_get(v_val_1588_, 1);
lean_inc(v_snd_1589_);
lean_dec(v_val_1588_);
v_fst_1590_ = lean_ctor_get(v_snd_1589_, 0);
lean_inc(v_fst_1590_);
v_snd_1591_ = lean_ctor_get(v_snd_1589_, 1);
lean_inc(v_snd_1591_);
lean_dec(v_snd_1589_);
lean_inc(v_a_1564_);
lean_inc_ref(v_a_1563_);
lean_inc(v_a_1562_);
lean_inc_ref(v_a_1561_);
v___x_1592_ = lean_whnf(v_fst_1590_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v_a_1593_; lean_object* v___x_1594_; 
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
lean_inc(v_a_1593_);
lean_dec_ref_known(v___x_1592_, 1);
lean_inc(v_a_1564_);
lean_inc_ref(v_a_1563_);
lean_inc(v_a_1562_);
lean_inc_ref(v_a_1561_);
v___x_1594_ = lean_whnf(v_snd_1591_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_a_1595_; uint8_t v___y_1597_; uint8_t v___x_1603_; 
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_a_1595_);
lean_dec_ref_known(v___x_1594_, 1);
v___x_1603_ = l_Lean_Expr_isRawNatLit(v_a_1593_);
lean_dec(v_a_1593_);
if (v___x_1603_ == 0)
{
lean_dec(v_a_1595_);
v___y_1597_ = v___x_1582_;
goto v___jp_1596_;
}
else
{
uint8_t v___x_1604_; 
v___x_1604_ = l_Lean_Expr_isRawNatLit(v_a_1595_);
lean_dec(v_a_1595_);
v___y_1597_ = v___x_1604_;
goto v___jp_1596_;
}
v___jp_1596_:
{
if (v___y_1597_ == 0)
{
lean_object* v___x_1598_; 
v___x_1598_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(v___f_1583_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_dec(v___x_1577_);
lean_dec(v_tail_1574_);
lean_dec(v_forbidden_1560_);
lean_dec(v_newNames_1559_);
lean_dec(v_mvarId_1558_);
return v___x_1598_;
}
else
{
lean_object* v_a_1599_; uint8_t v___x_1600_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
v___x_1600_ = l_Lean_Exception_isInterrupt(v_a_1599_);
if (v___x_1600_ == 0)
{
uint8_t v___x_1601_; 
lean_inc(v_a_1599_);
v___x_1601_ = l_Lean_Exception_isRuntime(v_a_1599_);
v___y_1579_ = v___x_1598_;
v___y_1580_ = v___x_1601_;
goto v___jp_1578_;
}
else
{
v___y_1579_ = v___x_1598_;
v___y_1580_ = v___x_1600_;
goto v___jp_1578_;
}
}
}
else
{
lean_dec_ref(v___f_1583_);
v_depth_1556_ = v___x_1577_;
v_fvarIds_1557_ = v_tail_1574_;
goto _start;
}
}
}
else
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
lean_dec(v_a_1593_);
lean_dec_ref(v___f_1583_);
lean_dec(v___x_1577_);
lean_dec(v_tail_1574_);
lean_dec(v_forbidden_1560_);
lean_dec(v_newNames_1559_);
lean_dec(v_mvarId_1558_);
v_a_1605_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1607_ = v___x_1594_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1594_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1605_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
}
else
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
lean_dec(v_snd_1591_);
lean_dec_ref(v___f_1583_);
lean_dec(v___x_1577_);
lean_dec(v_tail_1574_);
lean_dec(v_forbidden_1560_);
lean_dec(v_newNames_1559_);
lean_dec(v_mvarId_1558_);
v_a_1613_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v___x_1592_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1592_);
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
lean_dec(v_a_1587_);
lean_dec_ref(v___f_1583_);
v_depth_1556_ = v___x_1577_;
v_fvarIds_1557_ = v_tail_1574_;
goto _start;
}
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
lean_dec_ref(v___f_1583_);
lean_dec(v___x_1577_);
lean_dec(v_tail_1574_);
lean_dec(v_forbidden_1560_);
lean_dec(v_newNames_1559_);
lean_dec(v_mvarId_1558_);
v_a_1622_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1586_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1586_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
else
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
lean_dec_ref(v___f_1583_);
lean_dec(v___x_1577_);
lean_dec(v_tail_1574_);
lean_dec(v_forbidden_1560_);
lean_dec(v_newNames_1559_);
lean_dec(v_mvarId_1558_);
v_a_1630_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1584_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1584_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
else
{
lean_dec(v_n_1576_);
lean_dec(v_head_1573_);
v_depth_1556_ = v___x_1577_;
v_fvarIds_1557_ = v_tail_1574_;
goto _start;
}
v___jp_1578_:
{
if (v___y_1580_ == 0)
{
lean_dec_ref(v___y_1579_);
v_depth_1556_ = v___x_1577_;
v_fvarIds_1557_ = v_tail_1574_;
goto _start;
}
else
{
lean_dec(v___x_1577_);
lean_dec(v_tail_1574_);
lean_dec(v_forbidden_1560_);
lean_dec(v_newNames_1559_);
lean_dec(v_mvarId_1558_);
return v___y_1579_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_depth_1556_ = stack[0].m_obj;
lean_object* v_fvarIds_1557_ = stack[1].m_obj;
lean_object* v_mvarId_1558_ = stack[2].m_obj;
lean_object* v_newNames_1559_ = stack[3].m_obj;
lean_object* v_forbidden_1560_ = stack[4].m_obj;
lean_object* v_a_1561_ = stack[5].m_obj;
lean_object* v_a_1562_ = stack[6].m_obj;
lean_object* v_a_1563_ = stack[7].m_obj;
lean_object* v_a_1564_ = stack[8].m_obj;
lean_object* v_res_1639_;
v_res_1639_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go(v_depth_1556_, v_fvarIds_1557_, v_mvarId_1558_, v_newNames_1559_, v_forbidden_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_);
stack->m_obj
 = v_res_1639_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___boxed(lean_object* v_depth_1640_, lean_object* v_fvarIds_1641_, lean_object* v_mvarId_1642_, lean_object* v_newNames_1643_, lean_object* v_forbidden_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go(v_depth_1640_, v_fvarIds_1641_, v_mvarId_1642_, v_newNames_1643_, v_forbidden_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_);
lean_dec(v_a_1648_);
lean_dec_ref(v_a_1647_);
lean_dec(v_a_1646_);
lean_dec_ref(v_a_1645_);
return v_res_1650_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0(lean_object* v_mvarId_1651_, lean_object* v_head_1652_, lean_object* v_newNames_1653_, lean_object* v_tail_1654_, lean_object* v_forbidden_1655_, lean_object* v_n_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
lean_object* v___x_1662_; 
lean_inc(v_head_1652_);
v___x_1662_ = l_Lean_Meta_injection(v_mvarId_1651_, v_head_1652_, v_newNames_1653_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1679_; 
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1665_ = v___x_1662_;
v_isShared_1666_ = v_isSharedCheck_1679_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1662_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1679_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
if (lean_obj_tag(v_a_1663_) == 0)
{
lean_object* v___x_1667_; lean_object* v___x_1669_; 
lean_dec(v_n_1656_);
lean_dec(v_forbidden_1655_);
lean_dec(v_tail_1654_);
lean_dec(v_head_1652_);
v___x_1667_ = lean_box(0);
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 0, v___x_1667_);
v___x_1669_ = v___x_1665_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v___x_1667_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
else
{
lean_object* v_mvarId_1671_; lean_object* v_newEqs_1672_; lean_object* v_remainingNames_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
lean_del_object(v___x_1665_);
v_mvarId_1671_ = lean_ctor_get(v_a_1663_, 0);
lean_inc_n(v_mvarId_1671_, 2);
v_newEqs_1672_ = lean_ctor_get(v_a_1663_, 1);
lean_inc_ref(v_newEqs_1672_);
v_remainingNames_1673_ = lean_ctor_get(v_a_1663_, 2);
lean_inc(v_remainingNames_1673_);
lean_dec_ref_known(v_a_1663_, 3);
v___x_1674_ = lean_array_to_list(v_newEqs_1672_);
v___x_1675_ = l_List_appendTR___redArg(v___x_1674_, v_tail_1654_);
v___x_1676_ = l_Lean_FVarIdSet_insert(v_forbidden_1655_, v_head_1652_);
v___x_1677_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___boxed), 10, 5);
lean_closure_set(v___x_1677_, 0, v_n_1656_);
lean_closure_set(v___x_1677_, 1, v___x_1675_);
lean_closure_set(v___x_1677_, 2, v_mvarId_1671_);
lean_closure_set(v___x_1677_, 3, v_remainingNames_1673_);
lean_closure_set(v___x_1677_, 4, v___x_1676_);
v___x_1678_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg(v_mvarId_1671_, v___x_1677_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
return v___x_1678_;
}
}
}
else
{
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1687_; 
lean_dec(v_n_1656_);
lean_dec(v_forbidden_1655_);
lean_dec(v_tail_1654_);
lean_dec(v_head_1652_);
v_a_1680_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1682_ = v___x_1662_;
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1662_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1685_; 
if (v_isShared_1683_ == 0)
{
v___x_1685_ = v___x_1682_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_a_1680_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1651_ = stack[0].m_obj;
lean_object* v_head_1652_ = stack[1].m_obj;
lean_object* v_newNames_1653_ = stack[2].m_obj;
lean_object* v_tail_1654_ = stack[3].m_obj;
lean_object* v_forbidden_1655_ = stack[4].m_obj;
lean_object* v_n_1656_ = stack[5].m_obj;
lean_object* v___y_1657_ = stack[6].m_obj;
lean_object* v___y_1658_ = stack[7].m_obj;
lean_object* v___y_1659_ = stack[8].m_obj;
lean_object* v___y_1660_ = stack[9].m_obj;
lean_object* v_res_1688_;
v_res_1688_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0(v_mvarId_1651_, v_head_1652_, v_newNames_1653_, v_tail_1654_, v_forbidden_1655_, v_n_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
stack->m_obj
 = v_res_1688_;
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0(lean_object* v_00_u03b2_1689_, lean_object* v_k_1690_, lean_object* v_t_1691_){
_start:
{
uint8_t v___x_1692_; 
v___x_1692_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(v_k_1690_, v_t_1691_);
return v___x_1692_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1690_ = stack[1].m_obj;
lean_object* v_t_1691_ = stack[2].m_obj;
uint8_t v_res_1693_;
v_res_1693_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0(lean_box(0), v_k_1690_, v_t_1691_);
stack->m_num = v_res_1693_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___boxed(lean_object* v_00_u03b2_1694_, lean_object* v_k_1695_, lean_object* v_t_1696_){
_start:
{
uint8_t v_res_1697_; lean_object* v_r_1698_; 
v_res_1697_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0(v_00_u03b2_1694_, v_k_1695_, v_t_1696_);
lean_dec(v_t_1696_);
lean_dec(v_k_1695_);
v_r_1698_ = lean_box(v_res_1697_);
return v_r_1698_;
}
}
lean_object* l_Lean_Meta_injections___lam__0(lean_object* v_maxDepth_1699_, lean_object* v_mvarId_1700_, lean_object* v_newNames_1701_, lean_object* v_forbidden_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v_lctx_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
v_lctx_1708_ = lean_ctor_get(v___y_1703_, 2);
v___x_1709_ = l_Lean_LocalContext_getFVarIds(v_lctx_1708_);
v___x_1710_ = lean_array_to_list(v___x_1709_);
v___x_1711_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go(v_maxDepth_1699_, v___x_1710_, v_mvarId_1700_, v_newNames_1701_, v_forbidden_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
return v___x_1711_;
}
}
LEAN_EXPORT void l_Lean_Meta_injections___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_maxDepth_1699_ = stack[0].m_obj;
lean_object* v_mvarId_1700_ = stack[1].m_obj;
lean_object* v_newNames_1701_ = stack[2].m_obj;
lean_object* v_forbidden_1702_ = stack[3].m_obj;
lean_object* v___y_1703_ = stack[4].m_obj;
lean_object* v___y_1704_ = stack[5].m_obj;
lean_object* v___y_1705_ = stack[6].m_obj;
lean_object* v___y_1706_ = stack[7].m_obj;
lean_object* v_res_1712_;
v_res_1712_ = l_Lean_Meta_injections___lam__0(v_maxDepth_1699_, v_mvarId_1700_, v_newNames_1701_, v_forbidden_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
stack->m_obj
 = v_res_1712_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections___lam__0___boxed(lean_object* v_maxDepth_1713_, lean_object* v_mvarId_1714_, lean_object* v_newNames_1715_, lean_object* v_forbidden_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_Lean_Meta_injections___lam__0(v_maxDepth_1713_, v_mvarId_1714_, v_newNames_1715_, v_forbidden_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
return v_res_1722_;
}
}
lean_object* l_Lean_Meta_injections(lean_object* v_mvarId_1723_, lean_object* v_newNames_1724_, lean_object* v_maxDepth_1725_, lean_object* v_forbidden_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_){
_start:
{
lean_object* v___f_1732_; lean_object* v___x_1733_; 
lean_inc(v_mvarId_1723_);
v___f_1732_ = lean_alloc_closure((void*)(l_Lean_Meta_injections___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1732_, 0, v_maxDepth_1725_);
lean_closure_set(v___f_1732_, 1, v_mvarId_1723_);
lean_closure_set(v___f_1732_, 2, v_newNames_1724_);
lean_closure_set(v___f_1732_, 3, v_forbidden_1726_);
v___x_1733_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg(v_mvarId_1723_, v___f_1732_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_);
return v___x_1733_;
}
}
LEAN_EXPORT void l_Lean_Meta_injections_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1723_ = stack[0].m_obj;
lean_object* v_newNames_1724_ = stack[1].m_obj;
lean_object* v_maxDepth_1725_ = stack[2].m_obj;
lean_object* v_forbidden_1726_ = stack[3].m_obj;
lean_object* v_a_1727_ = stack[4].m_obj;
lean_object* v_a_1728_ = stack[5].m_obj;
lean_object* v_a_1729_ = stack[6].m_obj;
lean_object* v_a_1730_ = stack[7].m_obj;
lean_object* v_res_1734_;
v_res_1734_ = l_Lean_Meta_injections(v_mvarId_1723_, v_newNames_1724_, v_maxDepth_1725_, v_forbidden_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_);
stack->m_obj
 = v_res_1734_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections___boxed(lean_object* v_mvarId_1735_, lean_object* v_newNames_1736_, lean_object* v_maxDepth_1737_, lean_object* v_forbidden_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l_Lean_Meta_injections(v_mvarId_1735_, v_newNames_1736_, v_maxDepth_1737_, v_forbidden_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_);
lean_dec(v_a_1742_);
lean_dec_ref(v_a_1741_);
lean_dec(v_a_1740_);
lean_dec_ref(v_a_1739_);
return v_res_1744_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1801_; uint8_t v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1801_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__1));
v___x_1802_ = 0;
v___x_1803_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__22_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_));
v___x_1804_ = l_Lean_registerTraceClass(v___x_1801_, v___x_1802_, v___x_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Injection_0__initFn_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1805_;
v_res_1805_ = l___private_Lean_Meta_Tactic_Injection_0__initFn_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1805_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2____boxed(lean_object* v_a_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l___private_Lean_Meta_Tactic_Injection_0__initFn_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_();
return v_res_1807_;
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
