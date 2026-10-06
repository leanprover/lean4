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
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResultCore_ctorIdx___impl(lean_object* v_x_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = lean_obj_tag_nat(v_x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResultCore_ctorIdx___impl___boxed(lean_object* v_x_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lean_Meta_InjectionResultCore_ctorIdx___impl(v_x_207_);
lean_dec(v_x_207_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResultCore_ctorElim___redArg(lean_object* v_t_209_, lean_object* v_k_210_){
_start:
{
if (lean_obj_tag(v_t_209_) == 0)
{
return v_k_210_;
}
else
{
lean_object* v_mvarId_211_; lean_object* v_numNewEqs_212_; lean_object* v___x_213_; 
v_mvarId_211_ = lean_ctor_get(v_t_209_, 0);
lean_inc(v_mvarId_211_);
v_numNewEqs_212_ = lean_ctor_get(v_t_209_, 1);
lean_inc(v_numNewEqs_212_);
lean_dec_ref_known(v_t_209_, 2);
v___x_213_ = lean_apply_2(v_k_210_, v_mvarId_211_, v_numNewEqs_212_);
return v___x_213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResultCore_ctorElim(lean_object* v_motive_214_, lean_object* v_ctorIdx_215_, lean_object* v_t_216_, lean_object* v_h_217_, lean_object* v_k_218_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l_Lean_Meta_InjectionResultCore_ctorElim___redArg(v_t_216_, v_k_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResultCore_ctorElim___boxed(lean_object* v_motive_220_, lean_object* v_ctorIdx_221_, lean_object* v_t_222_, lean_object* v_h_223_, lean_object* v_k_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_Meta_InjectionResultCore_ctorElim(v_motive_220_, v_ctorIdx_221_, v_t_222_, v_h_223_, v_k_224_);
lean_dec(v_ctorIdx_221_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResultCore_solved_elim___redArg(lean_object* v_t_226_, lean_object* v_solved_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_Meta_InjectionResultCore_ctorElim___redArg(v_t_226_, v_solved_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResultCore_solved_elim(lean_object* v_motive_229_, lean_object* v_t_230_, lean_object* v_h_231_, lean_object* v_solved_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l_Lean_Meta_InjectionResultCore_ctorElim___redArg(v_t_230_, v_solved_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResultCore_subgoal_elim___redArg(lean_object* v_t_234_, lean_object* v_subgoal_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Lean_Meta_InjectionResultCore_ctorElim___redArg(v_t_234_, v_subgoal_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResultCore_subgoal_elim(lean_object* v_motive_237_, lean_object* v_t_238_, lean_object* v_h_239_, lean_object* v_subgoal_240_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = l_Lean_Meta_InjectionResultCore_ctorElim___redArg(v_t_238_, v_subgoal_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg(lean_object* v_mvarId_242_, lean_object* v_x_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_242_, v_x_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_257_; 
v_a_250_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_257_ == 0)
{
v___x_252_ = v___x_249_;
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_249_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_255_; 
if (v_isShared_253_ == 0)
{
v___x_255_ = v___x_252_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_a_250_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
}
else
{
lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_265_; 
v_a_258_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_265_ == 0)
{
v___x_260_ = v___x_249_;
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_a_258_);
lean_dec(v___x_249_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_263_; 
if (v_isShared_261_ == 0)
{
v___x_263_ = v___x_260_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_a_258_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg___boxed(lean_object* v_mvarId_266_, lean_object* v_x_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg(v_mvarId_266_, v_x_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2(lean_object* v_00_u03b1_274_, lean_object* v_mvarId_275_, lean_object* v_x_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg(v_mvarId_275_, v_x_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___boxed(lean_object* v_00_u03b1_283_, lean_object* v_mvarId_284_, lean_object* v_x_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2(v_00_u03b1_283_, v_mvarId_284_, v_x_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___lam__0(lean_object* v___x_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v_toCold_301_; lean_object* v_options_302_; uint8_t v_hasTrace_303_; 
v_toCold_301_ = lean_ctor_get(v___y_298_, 0);
v_options_302_ = lean_ctor_get(v_toCold_301_, 2);
v_hasTrace_303_ = lean_ctor_get_uint8(v_options_302_, sizeof(void*)*1);
if (v_hasTrace_303_ == 0)
{
lean_object* v___x_304_; lean_object* v___x_305_; 
lean_dec(v___x_295_);
v___x_304_ = lean_box(v_hasTrace_303_);
v___x_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
return v___x_305_;
}
else
{
lean_object* v_inheritedTraceOptions_306_; lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v_inheritedTraceOptions_306_ = lean_ctor_get(v_toCold_301_, 11);
v___x_307_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__0___closed__1));
v___x_308_ = l_Lean_Name_append(v___x_307_, v___x_295_);
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
lean_object* v___x_325_; lean_object* v_env_326_; uint8_t v___x_327_; lean_object* v_env_328_; lean_object* v___x_329_; lean_object* v_toCold_330_; lean_object* v_mctx_331_; lean_object* v_lctx_332_; lean_object* v_options_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_325_ = lean_st_ref_get(v___y_323_);
v_env_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc_ref(v_env_326_);
lean_dec(v___x_325_);
v___x_327_ = 0;
v_env_328_ = l_Lean_Environment_setRecordingDeps(v_env_326_, v___x_327_);
v___x_329_ = lean_st_ref_get(v___y_321_);
v_toCold_330_ = lean_ctor_get(v___y_322_, 0);
v_mctx_331_ = lean_ctor_get(v___x_329_, 0);
lean_inc_ref(v_mctx_331_);
lean_dec(v___x_329_);
v_lctx_332_ = lean_ctor_get(v___y_320_, 2);
v_options_333_ = lean_ctor_get(v_toCold_330_, 2);
lean_inc_ref(v_options_333_);
lean_inc_ref(v_lctx_332_);
v___x_334_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_334_, 0, v_env_328_);
lean_ctor_set(v___x_334_, 1, v_mctx_331_);
lean_ctor_set(v___x_334_, 2, v_lctx_332_);
lean_ctor_set(v___x_334_, 3, v_options_333_);
v___x_335_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v_msgData_319_);
v___x_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1_spec__2___boxed(lean_object* v_msgData_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1_spec__2(v_msgData_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
return v_res_343_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__0(void){
_start:
{
lean_object* v___x_344_; double v___x_345_; 
v___x_344_ = lean_unsigned_to_nat(0u);
v___x_345_ = lean_float_of_nat(v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(lean_object* v_cls_349_, lean_object* v_msg_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v_ref_356_; lean_object* v___x_357_; lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_403_; 
v_ref_356_ = lean_ctor_get(v___y_353_, 2);
v___x_357_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1_spec__2(v_msg_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_);
v_a_358_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_403_ == 0)
{
v___x_360_ = v___x_357_;
v_isShared_361_ = v_isSharedCheck_403_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_357_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_403_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_362_; lean_object* v_traceState_363_; lean_object* v_env_364_; lean_object* v_nextMacroScope_365_; lean_object* v_ngen_366_; lean_object* v_auxDeclNGen_367_; lean_object* v_cache_368_; lean_object* v_recordedDeps_369_; lean_object* v_messages_370_; lean_object* v_infoState_371_; lean_object* v_snapshotTasks_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_402_; 
v___x_362_ = lean_st_ref_take(v___y_354_);
v_traceState_363_ = lean_ctor_get(v___x_362_, 4);
v_env_364_ = lean_ctor_get(v___x_362_, 0);
v_nextMacroScope_365_ = lean_ctor_get(v___x_362_, 1);
v_ngen_366_ = lean_ctor_get(v___x_362_, 2);
v_auxDeclNGen_367_ = lean_ctor_get(v___x_362_, 3);
v_cache_368_ = lean_ctor_get(v___x_362_, 5);
v_recordedDeps_369_ = lean_ctor_get(v___x_362_, 6);
v_messages_370_ = lean_ctor_get(v___x_362_, 7);
v_infoState_371_ = lean_ctor_get(v___x_362_, 8);
v_snapshotTasks_372_ = lean_ctor_get(v___x_362_, 9);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_402_ == 0)
{
v___x_374_ = v___x_362_;
v_isShared_375_ = v_isSharedCheck_402_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_snapshotTasks_372_);
lean_inc(v_infoState_371_);
lean_inc(v_messages_370_);
lean_inc(v_recordedDeps_369_);
lean_inc(v_cache_368_);
lean_inc(v_traceState_363_);
lean_inc(v_auxDeclNGen_367_);
lean_inc(v_ngen_366_);
lean_inc(v_nextMacroScope_365_);
lean_inc(v_env_364_);
lean_dec(v___x_362_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_402_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
uint64_t v_tid_376_; lean_object* v_traces_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_401_; 
v_tid_376_ = lean_ctor_get_uint64(v_traceState_363_, sizeof(void*)*1);
v_traces_377_ = lean_ctor_get(v_traceState_363_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v_traceState_363_);
if (v_isSharedCheck_401_ == 0)
{
v___x_379_ = v_traceState_363_;
v_isShared_380_ = v_isSharedCheck_401_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_traces_377_);
lean_dec(v_traceState_363_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_401_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_381_; lean_object* v___x_382_; double v___x_383_; uint8_t v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_392_; 
v___x_381_ = lean_box(0);
v___x_382_ = lean_box(0);
v___x_383_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__0);
v___x_384_ = 0;
v___x_385_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__1));
v___x_386_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_386_, 0, v_cls_349_);
lean_ctor_set(v___x_386_, 1, v___x_382_);
lean_ctor_set(v___x_386_, 2, v___x_385_);
lean_ctor_set_float(v___x_386_, sizeof(void*)*3, v___x_383_);
lean_ctor_set_float(v___x_386_, sizeof(void*)*3 + 8, v___x_383_);
lean_ctor_set_uint8(v___x_386_, sizeof(void*)*3 + 16, v___x_384_);
v___x_387_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__2));
v___x_388_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_388_, 0, v___x_386_);
lean_ctor_set(v___x_388_, 1, v_a_358_);
lean_ctor_set(v___x_388_, 2, v___x_387_);
lean_inc(v_ref_356_);
v___x_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_389_, 0, v_ref_356_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
v___x_390_ = l_Lean_PersistentArray_push___redArg(v_traces_377_, v___x_389_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 0, v___x_390_);
v___x_392_ = v___x_379_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_390_);
lean_ctor_set_uint64(v_reuseFailAlloc_400_, sizeof(void*)*1, v_tid_376_);
v___x_392_ = v_reuseFailAlloc_400_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
lean_object* v___x_394_; 
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 4, v___x_392_);
v___x_394_ = v___x_374_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_env_364_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v_nextMacroScope_365_);
lean_ctor_set(v_reuseFailAlloc_399_, 2, v_ngen_366_);
lean_ctor_set(v_reuseFailAlloc_399_, 3, v_auxDeclNGen_367_);
lean_ctor_set(v_reuseFailAlloc_399_, 4, v___x_392_);
lean_ctor_set(v_reuseFailAlloc_399_, 5, v_cache_368_);
lean_ctor_set(v_reuseFailAlloc_399_, 6, v_recordedDeps_369_);
lean_ctor_set(v_reuseFailAlloc_399_, 7, v_messages_370_);
lean_ctor_set(v_reuseFailAlloc_399_, 8, v_infoState_371_);
lean_ctor_set(v_reuseFailAlloc_399_, 9, v_snapshotTasks_372_);
v___x_394_ = v_reuseFailAlloc_399_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v___x_395_; lean_object* v___x_397_; 
v___x_395_ = lean_st_ref_put(v___y_354_, v___x_394_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 0, v___x_381_);
v___x_397_ = v___x_360_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_381_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___boxed(lean_object* v_cls_404_, lean_object* v_msg_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v_cls_404_, v_msg_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(lean_object* v_x_412_, lean_object* v_x_413_, lean_object* v_x_414_, lean_object* v_x_415_){
_start:
{
lean_object* v_ks_416_; lean_object* v_vs_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_441_; 
v_ks_416_ = lean_ctor_get(v_x_412_, 0);
v_vs_417_ = lean_ctor_get(v_x_412_, 1);
v_isSharedCheck_441_ = !lean_is_exclusive(v_x_412_);
if (v_isSharedCheck_441_ == 0)
{
v___x_419_ = v_x_412_;
v_isShared_420_ = v_isSharedCheck_441_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_vs_417_);
lean_inc(v_ks_416_);
lean_dec(v_x_412_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_441_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_421_; uint8_t v___x_422_; 
v___x_421_ = lean_array_get_size(v_ks_416_);
v___x_422_ = lean_nat_dec_lt(v_x_413_, v___x_421_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_426_; 
lean_dec(v_x_413_);
v___x_423_ = lean_array_push(v_ks_416_, v_x_414_);
v___x_424_ = lean_array_push(v_vs_417_, v_x_415_);
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 1, v___x_424_);
lean_ctor_set(v___x_419_, 0, v___x_423_);
v___x_426_ = v___x_419_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v___x_423_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v___x_424_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
else
{
lean_object* v_k_x27_428_; uint8_t v___x_429_; 
v_k_x27_428_ = lean_array_fget_borrowed(v_ks_416_, v_x_413_);
v___x_429_ = l_Lean_instBEqMVarId_beq(v_x_414_, v_k_x27_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_431_; 
if (v_isShared_420_ == 0)
{
v___x_431_ = v___x_419_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_ks_416_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v_vs_417_);
v___x_431_ = v_reuseFailAlloc_435_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = lean_unsigned_to_nat(1u);
v___x_433_ = lean_nat_add(v_x_413_, v___x_432_);
lean_dec(v_x_413_);
v_x_412_ = v___x_431_;
v_x_413_ = v___x_433_;
goto _start;
}
}
else
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_439_; 
v___x_436_ = lean_array_fset(v_ks_416_, v_x_413_, v_x_414_);
v___x_437_ = lean_array_fset(v_vs_417_, v_x_413_, v_x_415_);
lean_dec(v_x_413_);
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 1, v___x_437_);
lean_ctor_set(v___x_419_, 0, v___x_436_);
v___x_439_ = v___x_419_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_436_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v___x_437_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_n_442_, lean_object* v_k_443_, lean_object* v_v_444_){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = lean_unsigned_to_nat(0u);
v___x_446_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(v_n_442_, v___x_445_, v_k_443_, v_v_444_);
return v___x_446_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(lean_object* v_x_448_, size_t v_x_449_, size_t v_x_450_, lean_object* v_x_451_, lean_object* v_x_452_){
_start:
{
if (lean_obj_tag(v_x_448_) == 0)
{
lean_object* v_es_453_; size_t v___x_454_; size_t v___x_455_; lean_object* v_j_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v_es_453_ = lean_ctor_get(v_x_448_, 0);
v___x_454_ = ((size_t)31ULL);
v___x_455_ = lean_usize_land(v_x_449_, v___x_454_);
v_j_456_ = lean_usize_to_nat(v___x_455_);
v___x_457_ = lean_array_get_size(v_es_453_);
v___x_458_ = lean_nat_dec_lt(v_j_456_, v___x_457_);
if (v___x_458_ == 0)
{
lean_dec(v_j_456_);
lean_dec(v_x_452_);
lean_dec(v_x_451_);
return v_x_448_;
}
else
{
lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_497_; 
lean_inc_ref(v_es_453_);
v_isSharedCheck_497_ = !lean_is_exclusive(v_x_448_);
if (v_isSharedCheck_497_ == 0)
{
lean_object* v_unused_498_; 
v_unused_498_ = lean_ctor_get(v_x_448_, 0);
lean_dec(v_unused_498_);
v___x_460_ = v_x_448_;
v_isShared_461_ = v_isSharedCheck_497_;
goto v_resetjp_459_;
}
else
{
lean_dec(v_x_448_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_497_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v_v_462_; lean_object* v___x_463_; lean_object* v_xs_x27_464_; lean_object* v___y_466_; 
v_v_462_ = lean_array_fget(v_es_453_, v_j_456_);
v___x_463_ = lean_box(0);
v_xs_x27_464_ = lean_array_fset(v_es_453_, v_j_456_, v___x_463_);
switch(lean_obj_tag(v_v_462_))
{
case 0:
{
lean_object* v_key_471_; lean_object* v_val_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_482_; 
v_key_471_ = lean_ctor_get(v_v_462_, 0);
v_val_472_ = lean_ctor_get(v_v_462_, 1);
v_isSharedCheck_482_ = !lean_is_exclusive(v_v_462_);
if (v_isSharedCheck_482_ == 0)
{
v___x_474_ = v_v_462_;
v_isShared_475_ = v_isSharedCheck_482_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_val_472_);
lean_inc(v_key_471_);
lean_dec(v_v_462_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_482_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
uint8_t v___x_476_; 
v___x_476_ = l_Lean_instBEqMVarId_beq(v_x_451_, v_key_471_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; lean_object* v___x_478_; 
lean_del_object(v___x_474_);
v___x_477_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_471_, v_val_472_, v_x_451_, v_x_452_);
v___x_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
v___y_466_ = v___x_478_;
goto v___jp_465_;
}
else
{
lean_object* v___x_480_; 
lean_dec(v_val_472_);
lean_dec(v_key_471_);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 1, v_x_452_);
lean_ctor_set(v___x_474_, 0, v_x_451_);
v___x_480_ = v___x_474_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_x_451_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_x_452_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
v___y_466_ = v___x_480_;
goto v___jp_465_;
}
}
}
}
case 1:
{
lean_object* v_node_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_495_; 
v_node_483_ = lean_ctor_get(v_v_462_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v_v_462_);
if (v_isSharedCheck_495_ == 0)
{
v___x_485_ = v_v_462_;
v_isShared_486_ = v_isSharedCheck_495_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_node_483_);
lean_dec(v_v_462_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_495_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
size_t v___x_487_; size_t v___x_488_; size_t v___x_489_; size_t v___x_490_; lean_object* v___x_491_; lean_object* v___x_493_; 
v___x_487_ = ((size_t)5ULL);
v___x_488_ = lean_usize_shift_right(v_x_449_, v___x_487_);
v___x_489_ = ((size_t)1ULL);
v___x_490_ = lean_usize_add(v_x_450_, v___x_489_);
v___x_491_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(v_node_483_, v___x_488_, v___x_490_, v_x_451_, v_x_452_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 0, v___x_491_);
v___x_493_ = v___x_485_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_491_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
v___y_466_ = v___x_493_;
goto v___jp_465_;
}
}
}
default: 
{
lean_object* v___x_496_; 
v___x_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_496_, 0, v_x_451_);
lean_ctor_set(v___x_496_, 1, v_x_452_);
v___y_466_ = v___x_496_;
goto v___jp_465_;
}
}
v___jp_465_:
{
lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_467_ = lean_array_fset(v_xs_x27_464_, v_j_456_, v___y_466_);
lean_dec(v_j_456_);
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 0, v___x_467_);
v___x_469_ = v___x_460_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_467_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
}
else
{
lean_object* v_ks_499_; lean_object* v_vs_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_518_; 
v_ks_499_ = lean_ctor_get(v_x_448_, 0);
v_vs_500_ = lean_ctor_get(v_x_448_, 1);
v_isSharedCheck_518_ = !lean_is_exclusive(v_x_448_);
if (v_isSharedCheck_518_ == 0)
{
v___x_502_ = v_x_448_;
v_isShared_503_ = v_isSharedCheck_518_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_vs_500_);
lean_inc(v_ks_499_);
lean_dec(v_x_448_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_518_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_505_; 
if (v_isShared_503_ == 0)
{
v___x_505_ = v___x_502_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_ks_499_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_vs_500_);
v___x_505_ = v_reuseFailAlloc_517_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
lean_object* v_newNode_506_; size_t v___x_507_; uint8_t v___x_508_; 
v_newNode_506_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5___redArg(v___x_505_, v_x_451_, v_x_452_);
v___x_507_ = ((size_t)7ULL);
v___x_508_ = lean_usize_dec_le(v___x_507_, v_x_450_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_509_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_506_);
v___x_510_ = lean_unsigned_to_nat(4u);
v___x_511_ = lean_nat_dec_lt(v___x_509_, v___x_510_);
lean_dec(v___x_509_);
if (v___x_511_ == 0)
{
lean_object* v_ks_512_; lean_object* v_vs_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v_ks_512_ = lean_ctor_get(v_newNode_506_, 0);
lean_inc_ref(v_ks_512_);
v_vs_513_ = lean_ctor_get(v_newNode_506_, 1);
lean_inc_ref(v_vs_513_);
lean_dec_ref(v_newNode_506_);
v___x_514_ = lean_unsigned_to_nat(0u);
v___x_515_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_516_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___redArg(v_x_450_, v_ks_512_, v_vs_513_, v___x_514_, v___x_515_);
lean_dec_ref(v_vs_513_);
lean_dec_ref(v_ks_512_);
return v___x_516_;
}
else
{
return v_newNode_506_;
}
}
else
{
return v_newNode_506_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___redArg(size_t v_depth_519_, lean_object* v_keys_520_, lean_object* v_vals_521_, lean_object* v_i_522_, lean_object* v_entries_523_){
_start:
{
lean_object* v___x_524_; uint8_t v___x_525_; 
v___x_524_ = lean_array_get_size(v_keys_520_);
v___x_525_ = lean_nat_dec_lt(v_i_522_, v___x_524_);
if (v___x_525_ == 0)
{
lean_dec(v_i_522_);
return v_entries_523_;
}
else
{
lean_object* v_k_526_; lean_object* v_v_527_; uint64_t v___x_528_; size_t v_h_529_; size_t v___x_530_; lean_object* v___x_531_; size_t v___x_532_; size_t v___x_533_; size_t v___x_534_; size_t v_h_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v_k_526_ = lean_array_fget_borrowed(v_keys_520_, v_i_522_);
v_v_527_ = lean_array_fget_borrowed(v_vals_521_, v_i_522_);
v___x_528_ = l_Lean_instHashableMVarId_hash(v_k_526_);
v_h_529_ = lean_uint64_to_usize(v___x_528_);
v___x_530_ = ((size_t)5ULL);
v___x_531_ = lean_unsigned_to_nat(1u);
v___x_532_ = ((size_t)1ULL);
v___x_533_ = lean_usize_sub(v_depth_519_, v___x_532_);
v___x_534_ = lean_usize_mul(v___x_530_, v___x_533_);
v_h_535_ = lean_usize_shift_right(v_h_529_, v___x_534_);
v___x_536_ = lean_nat_add(v_i_522_, v___x_531_);
lean_dec(v_i_522_);
lean_inc(v_v_527_);
lean_inc(v_k_526_);
v___x_537_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(v_entries_523_, v_h_535_, v_depth_519_, v_k_526_, v_v_527_);
v_i_522_ = v___x_536_;
v_entries_523_ = v___x_537_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_depth_539_, lean_object* v_keys_540_, lean_object* v_vals_541_, lean_object* v_i_542_, lean_object* v_entries_543_){
_start:
{
size_t v_depth_boxed_544_; lean_object* v_res_545_; 
v_depth_boxed_544_ = lean_unbox_usize(v_depth_539_);
lean_dec(v_depth_539_);
v_res_545_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___redArg(v_depth_boxed_544_, v_keys_540_, v_vals_541_, v_i_542_, v_entries_543_);
lean_dec_ref(v_vals_541_);
lean_dec_ref(v_keys_540_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_546_, lean_object* v_x_547_, lean_object* v_x_548_, lean_object* v_x_549_, lean_object* v_x_550_){
_start:
{
size_t v_x_14545__boxed_551_; size_t v_x_14546__boxed_552_; lean_object* v_res_553_; 
v_x_14545__boxed_551_ = lean_unbox_usize(v_x_547_);
lean_dec(v_x_547_);
v_x_14546__boxed_552_ = lean_unbox_usize(v_x_548_);
lean_dec(v_x_548_);
v_res_553_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(v_x_546_, v_x_14545__boxed_551_, v_x_14546__boxed_552_, v_x_549_, v_x_550_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0___redArg(lean_object* v_x_554_, lean_object* v_x_555_, lean_object* v_x_556_){
_start:
{
uint64_t v___x_557_; size_t v___x_558_; size_t v___x_559_; lean_object* v___x_560_; 
v___x_557_ = l_Lean_instHashableMVarId_hash(v_x_555_);
v___x_558_ = lean_uint64_to_usize(v___x_557_);
v___x_559_ = ((size_t)1ULL);
v___x_560_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(v_x_554_, v___x_558_, v___x_559_, v_x_555_, v_x_556_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(lean_object* v_mvarId_561_, lean_object* v_val_562_, lean_object* v___y_563_){
_start:
{
lean_object* v___x_565_; lean_object* v_mctx_566_; lean_object* v_cache_567_; lean_object* v_zetaDeltaFVarIds_568_; lean_object* v_postponed_569_; lean_object* v_diag_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_600_; 
v___x_565_ = lean_st_ref_take(v___y_563_);
v_mctx_566_ = lean_ctor_get(v___x_565_, 0);
v_cache_567_ = lean_ctor_get(v___x_565_, 1);
v_zetaDeltaFVarIds_568_ = lean_ctor_get(v___x_565_, 2);
v_postponed_569_ = lean_ctor_get(v___x_565_, 3);
v_diag_570_ = lean_ctor_get(v___x_565_, 4);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_600_ == 0)
{
v___x_572_ = v___x_565_;
v_isShared_573_ = v_isSharedCheck_600_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_diag_570_);
lean_inc(v_postponed_569_);
lean_inc(v_zetaDeltaFVarIds_568_);
lean_inc(v_cache_567_);
lean_inc(v_mctx_566_);
lean_dec(v___x_565_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_600_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v_depth_574_; lean_object* v_levelAssignDepth_575_; lean_object* v_lmvarCounter_576_; lean_object* v_mvarCounter_577_; lean_object* v_lDecls_578_; lean_object* v_decls_579_; lean_object* v_userNames_580_; lean_object* v_lAssignment_581_; lean_object* v_eAssignment_582_; lean_object* v_dAssignment_583_; lean_object* v_instanceTypedMVars_584_; lean_object* v_synthNormMemo_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_599_; 
v_depth_574_ = lean_ctor_get(v_mctx_566_, 0);
v_levelAssignDepth_575_ = lean_ctor_get(v_mctx_566_, 1);
v_lmvarCounter_576_ = lean_ctor_get(v_mctx_566_, 2);
v_mvarCounter_577_ = lean_ctor_get(v_mctx_566_, 3);
v_lDecls_578_ = lean_ctor_get(v_mctx_566_, 4);
v_decls_579_ = lean_ctor_get(v_mctx_566_, 5);
v_userNames_580_ = lean_ctor_get(v_mctx_566_, 6);
v_lAssignment_581_ = lean_ctor_get(v_mctx_566_, 7);
v_eAssignment_582_ = lean_ctor_get(v_mctx_566_, 8);
v_dAssignment_583_ = lean_ctor_get(v_mctx_566_, 9);
v_instanceTypedMVars_584_ = lean_ctor_get(v_mctx_566_, 10);
v_synthNormMemo_585_ = lean_ctor_get(v_mctx_566_, 11);
v_isSharedCheck_599_ = !lean_is_exclusive(v_mctx_566_);
if (v_isSharedCheck_599_ == 0)
{
v___x_587_ = v_mctx_566_;
v_isShared_588_ = v_isSharedCheck_599_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_synthNormMemo_585_);
lean_inc(v_instanceTypedMVars_584_);
lean_inc(v_dAssignment_583_);
lean_inc(v_eAssignment_582_);
lean_inc(v_lAssignment_581_);
lean_inc(v_userNames_580_);
lean_inc(v_decls_579_);
lean_inc(v_lDecls_578_);
lean_inc(v_mvarCounter_577_);
lean_inc(v_lmvarCounter_576_);
lean_inc(v_levelAssignDepth_575_);
lean_inc(v_depth_574_);
lean_dec(v_mctx_566_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_599_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_592_; 
v___x_589_ = lean_box(0);
v___x_590_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0___redArg(v_eAssignment_582_, v_mvarId_561_, v_val_562_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 8, v___x_590_);
v___x_592_ = v___x_587_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_depth_574_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_levelAssignDepth_575_);
lean_ctor_set(v_reuseFailAlloc_598_, 2, v_lmvarCounter_576_);
lean_ctor_set(v_reuseFailAlloc_598_, 3, v_mvarCounter_577_);
lean_ctor_set(v_reuseFailAlloc_598_, 4, v_lDecls_578_);
lean_ctor_set(v_reuseFailAlloc_598_, 5, v_decls_579_);
lean_ctor_set(v_reuseFailAlloc_598_, 6, v_userNames_580_);
lean_ctor_set(v_reuseFailAlloc_598_, 7, v_lAssignment_581_);
lean_ctor_set(v_reuseFailAlloc_598_, 8, v___x_590_);
lean_ctor_set(v_reuseFailAlloc_598_, 9, v_dAssignment_583_);
lean_ctor_set(v_reuseFailAlloc_598_, 10, v_instanceTypedMVars_584_);
lean_ctor_set(v_reuseFailAlloc_598_, 11, v_synthNormMemo_585_);
v___x_592_ = v_reuseFailAlloc_598_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
lean_object* v___x_594_; 
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 0, v___x_592_);
v___x_594_ = v___x_572_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_592_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v_cache_567_);
lean_ctor_set(v_reuseFailAlloc_597_, 2, v_zetaDeltaFVarIds_568_);
lean_ctor_set(v_reuseFailAlloc_597_, 3, v_postponed_569_);
lean_ctor_set(v_reuseFailAlloc_597_, 4, v_diag_570_);
v___x_594_ = v_reuseFailAlloc_597_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = lean_st_ref_put(v___y_563_, v___x_594_);
v___x_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_596_, 0, v___x_589_);
return v___x_596_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg___boxed(lean_object* v_mvarId_601_, lean_object* v_val_602_, lean_object* v___y_603_, lean_object* v___y_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(v_mvarId_601_, v_val_602_, v___y_603_);
lean_dec(v___y_603_);
return v_res_605_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__2(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__1));
v___x_610_ = l_Lean_MessageData_ofFormat(v___x_609_);
return v___x_610_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__3(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__2, &l_Lean_Meta_injectionCore___lam__1___closed__2_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__2);
v___x_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
return v___x_612_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__6(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__5));
v___x_617_ = l_Lean_MessageData_ofFormat(v___x_616_);
return v___x_617_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__7(void){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__6, &l_Lean_Meta_injectionCore___lam__1___closed__6_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__6);
v___x_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
return v___x_619_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__9(void){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__8));
v___x_622_ = l_Lean_stringToMessageData(v___x_621_);
return v___x_622_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__11(void){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__10));
v___x_625_ = l_Lean_stringToMessageData(v___x_624_);
return v___x_625_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__13(void){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__12));
v___x_628_ = l_Lean_stringToMessageData(v___x_627_);
return v___x_628_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__15(void){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__14));
v___x_631_ = l_Lean_stringToMessageData(v___x_630_);
return v___x_631_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__17(void){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__16));
v___x_634_ = l_Lean_stringToMessageData(v___x_633_);
return v___x_634_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__22(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__21));
v___x_642_ = l_Lean_MessageData_ofFormat(v___x_641_);
return v___x_642_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__23(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__22, &l_Lean_Meta_injectionCore___lam__1___closed__22_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__22);
v___x_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
return v___x_644_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__27(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__26));
v___x_649_ = l_Lean_stringToMessageData(v___x_648_);
return v___x_649_;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__1___closed__29(void){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__28));
v___x_652_ = l_Lean_stringToMessageData(v___x_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___lam__1(lean_object* v___x_656_, lean_object* v_mvarId_657_, lean_object* v_fvarId_658_, lean_object* v___x_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_897_; lean_object* v_type_918_; lean_object* v_prf_919_; lean_object* v___x_999_; 
lean_inc(v___x_656_);
lean_inc(v_mvarId_657_);
v___x_999_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_657_, v___x_656_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v___x_1000_; 
lean_dec_ref_known(v___x_999_, 1);
lean_inc(v_fvarId_658_);
v___x_1000_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_658_, v___y_660_, v___y_662_, v___y_663_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_1000_, 1);
v___x_1002_ = l_Lean_LocalDecl_type(v_a_1001_);
lean_dec(v_a_1001_);
lean_inc(v___y_663_);
lean_inc_ref(v___y_662_);
lean_inc(v___y_661_);
lean_inc_ref(v___y_660_);
v___x_1003_ = lean_whnf(v___x_1002_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; uint8_t v___x_1008_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref_known(v___x_1003_, 1);
lean_inc(v_fvarId_658_);
v___x_1005_ = l_Lean_mkFVar(v_fvarId_658_);
v___x_1006_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__31));
v___x_1007_ = lean_unsigned_to_nat(4u);
v___x_1008_ = l_Lean_Expr_isAppOfArity(v_a_1004_, v___x_1006_, v___x_1007_);
if (v___x_1008_ == 0)
{
v_type_918_ = v_a_1004_;
v_prf_919_ = v___x_1005_;
goto v___jp_917_;
}
else
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1009_ = l_Lean_Expr_appFn_x21(v_a_1004_);
v___x_1010_ = l_Lean_Expr_appFn_x21(v___x_1009_);
v___x_1011_ = l_Lean_Expr_appFn_x21(v___x_1010_);
v___x_1012_ = l_Lean_Expr_appArg_x21(v___x_1011_);
lean_dec_ref(v___x_1011_);
v___x_1013_ = l_Lean_Expr_appArg_x21(v___x_1010_);
lean_dec_ref(v___x_1010_);
v___x_1014_ = l_Lean_Expr_appArg_x21(v___x_1009_);
lean_dec_ref(v___x_1009_);
v___x_1015_ = l_Lean_Expr_appArg_x21(v_a_1004_);
v___x_1016_ = l_Lean_Meta_isExprDefEq(v___x_1012_, v___x_1014_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; uint8_t v___x_1018_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_a_1017_);
lean_dec_ref_known(v___x_1016_, 1);
v___x_1018_ = lean_unbox(v_a_1017_);
lean_dec(v_a_1017_);
if (v___x_1018_ == 0)
{
lean_dec_ref(v___x_1015_);
lean_dec_ref(v___x_1013_);
v_type_918_ = v_a_1004_;
v_prf_919_ = v___x_1005_;
goto v___jp_917_;
}
else
{
lean_object* v___x_1019_; 
lean_dec(v_a_1004_);
v___x_1019_ = l_Lean_Meta_mkEq(v___x_1013_, v___x_1015_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1020_; lean_object* v___x_1021_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
lean_inc(v_a_1020_);
lean_dec_ref_known(v___x_1019_, 1);
v___x_1021_ = l_Lean_Meta_mkEqOfHEq(v___x_1005_, v___x_1008_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1022_);
lean_dec_ref_known(v___x_1021_, 1);
v_type_918_ = v_a_1020_;
v_prf_919_ = v_a_1022_;
goto v___jp_917_;
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_dec(v_a_1020_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec_ref(v___x_659_);
lean_dec(v_fvarId_658_);
lean_dec(v_mvarId_657_);
lean_dec(v___x_656_);
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
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec_ref(v___x_659_);
lean_dec(v_fvarId_658_);
lean_dec(v_mvarId_657_);
lean_dec(v___x_656_);
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
lean_dec_ref(v___x_1015_);
lean_dec_ref(v___x_1013_);
lean_dec_ref(v___x_1005_);
lean_dec(v_a_1004_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec_ref(v___x_659_);
lean_dec(v_fvarId_658_);
lean_dec(v_mvarId_657_);
lean_dec(v___x_656_);
v_a_1039_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_1016_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1016_);
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
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec_ref(v___x_659_);
lean_dec(v_fvarId_658_);
lean_dec(v_mvarId_657_);
lean_dec(v___x_656_);
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
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec_ref(v___x_659_);
lean_dec(v_fvarId_658_);
lean_dec(v_mvarId_657_);
lean_dec(v___x_656_);
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
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec_ref(v___x_659_);
lean_dec(v_fvarId_658_);
lean_dec(v_mvarId_657_);
lean_dec(v___x_656_);
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
v___jp_665_:
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__3, &l_Lean_Meta_injectionCore___lam__1___closed__3_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__3);
v___x_671_ = l_Lean_Meta_throwTacticEx___redArg(v___x_656_, v_mvarId_657_, v___x_670_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
return v___x_671_;
}
v___jp_672_:
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__7, &l_Lean_Meta_injectionCore___lam__1___closed__7_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__7);
v___x_678_ = l_Lean_Meta_throwTacticEx___redArg(v___x_656_, v_mvarId_657_, v___x_677_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
return v___x_678_;
}
v___jp_679_:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_682_, 0, v___y_680_);
lean_ctor_set(v___x_682_, 1, v___y_681_);
v___x_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
return v___x_683_;
}
v___jp_684_:
{
lean_object* v_toConstantVal_694_; lean_object* v_toConstantVal_695_; lean_object* v_numFields_696_; lean_object* v_name_697_; lean_object* v_name_698_; uint8_t v___x_699_; 
v_toConstantVal_694_ = lean_ctor_get(v___y_685_, 0);
v_toConstantVal_695_ = lean_ctor_get(v___y_688_, 0);
lean_inc_ref(v_toConstantVal_695_);
lean_dec_ref(v___y_688_);
v_numFields_696_ = lean_ctor_get(v___y_685_, 4);
lean_inc(v_numFields_696_);
v_name_697_ = lean_ctor_get(v_toConstantVal_694_, 0);
v_name_698_ = lean_ctor_get(v_toConstantVal_695_, 0);
lean_inc(v_name_698_);
lean_dec_ref(v_toConstantVal_695_);
v___x_699_ = lean_name_eq(v_name_697_, v_name_698_);
lean_dec(v_name_698_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_708_; 
lean_dec(v_numFields_696_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec_ref(v___y_690_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v_fvarId_658_);
lean_dec(v___x_656_);
v___x_700_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(v_mvarId_657_, v___y_689_, v___y_691_);
lean_dec(v___y_691_);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_708_ == 0)
{
lean_object* v_unused_709_; 
v_unused_709_ = lean_ctor_get(v___x_700_, 0);
lean_dec(v_unused_709_);
v___x_702_ = v___x_700_;
v_isShared_703_ = v_isSharedCheck_708_;
goto v_resetjp_701_;
}
else
{
lean_dec(v___x_700_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_708_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_704_; lean_object* v___x_706_; 
v___x_704_ = lean_box(0);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 0, v___x_704_);
v___x_706_ = v___x_702_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_704_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
else
{
lean_object* v___x_710_; 
lean_inc(v___y_693_);
lean_inc_ref(v___y_692_);
lean_inc(v___y_691_);
lean_inc_ref(v___y_690_);
lean_inc(v___y_689_);
v___x_710_ = lean_infer_type(v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_object* v_a_711_; lean_object* v___x_712_; 
v_a_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_a_711_);
lean_dec_ref_known(v___x_710_, 1);
v___x_712_ = l_Lean_Meta_whnfD(v_a_711_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v_a_713_; 
v_a_713_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_a_713_);
lean_dec_ref_known(v___x_712_, 1);
if (lean_obj_tag(v_a_713_) == 7)
{
lean_object* v_binderType_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
lean_dec_ref(v___y_687_);
lean_dec(v___x_656_);
v_binderType_714_ = lean_ctor_get(v_a_713_, 1);
lean_inc_ref(v_binderType_714_);
lean_dec_ref_known(v_a_713_, 3);
v___x_715_ = l_Lean_Expr_headBeta(v_binderType_714_);
lean_inc(v_mvarId_657_);
v___x_716_ = l_Lean_MVarId_getTag(v_mvarId_657_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; lean_object* v___x_718_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_a_717_);
lean_dec_ref_known(v___x_716_, 1);
v___x_718_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_715_, v_a_717_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_774_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc_n(v_a_719_, 2);
lean_dec_ref_known(v___x_718_, 1);
v___x_720_ = l_Lean_Expr_app___override(v___y_689_, v_a_719_);
v___x_721_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(v_mvarId_657_, v___x_720_, v___y_691_);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_774_ == 0)
{
lean_object* v_unused_775_; 
v_unused_775_ = lean_ctor_get(v___x_721_, 0);
lean_dec(v_unused_775_);
v___x_723_ = v___x_721_;
v_isShared_724_ = v_isSharedCheck_774_;
goto v_resetjp_722_;
}
else
{
lean_dec(v___x_721_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_774_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_725_ = l_Lean_Expr_mvarId_x21(v_a_719_);
lean_dec(v_a_719_);
v___x_726_ = l_Lean_MVarId_tryClear(v___x_725_, v_fvarId_658_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; lean_object* v___x_728_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_a_727_);
lean_dec_ref_known(v___x_726_, 1);
v___x_728_ = l_Lean_Meta_getCtorNumPropFields(v___y_685_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_toCold_729_; lean_object* v_options_730_; lean_object* v_a_731_; lean_object* v_inheritedTraceOptions_732_; uint8_t v_hasTrace_733_; lean_object* v___x_734_; 
v_toCold_729_ = lean_ctor_get(v___y_692_, 0);
v_options_730_ = lean_ctor_get(v_toCold_729_, 2);
v_a_731_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_a_731_);
lean_dec_ref_known(v___x_728_, 1);
v_inheritedTraceOptions_732_ = lean_ctor_get(v_toCold_729_, 11);
v_hasTrace_733_ = lean_ctor_get_uint8(v_options_730_, sizeof(void*)*1);
v___x_734_ = lean_nat_sub(v_numFields_696_, v_a_731_);
lean_dec(v_a_731_);
lean_dec(v_numFields_696_);
if (v_hasTrace_733_ == 0)
{
lean_del_object(v___x_723_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_686_);
v___y_680_ = v_a_727_;
v___y_681_ = v___x_734_;
goto v___jp_679_;
}
else
{
lean_object* v___x_735_; lean_object* v___x_736_; uint8_t v___x_737_; 
v___x_735_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__0___closed__1));
lean_inc(v___y_686_);
v___x_736_ = l_Lean_Name_append(v___x_735_, v___y_686_);
v___x_737_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_732_, v_options_730_, v___x_736_);
lean_dec(v___x_736_);
if (v___x_737_ == 0)
{
lean_del_object(v___x_723_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_686_);
v___y_680_ = v_a_727_;
v___y_681_ = v___x_734_;
goto v___jp_679_;
}
else
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_741_; 
v___x_738_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__9, &l_Lean_Meta_injectionCore___lam__1___closed__9_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__9);
lean_inc(v___x_734_);
v___x_739_ = l_Nat_reprFast(v___x_734_);
if (v_isShared_724_ == 0)
{
lean_ctor_set_tag(v___x_723_, 3);
lean_ctor_set(v___x_723_, 0, v___x_739_);
v___x_741_ = v___x_723_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_739_);
v___x_741_ = v_reuseFailAlloc_757_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_742_ = l_Lean_MessageData_ofFormat(v___x_741_);
v___x_743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_738_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
v___x_744_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__11, &l_Lean_Meta_injectionCore___lam__1___closed__11_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__11);
v___x_745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_743_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
lean_inc(v_a_727_);
v___x_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_746_, 0, v_a_727_);
v___x_747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_745_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
v___x_748_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v___y_686_, v___x_747_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_dec_ref_known(v___x_748_, 1);
v___y_680_ = v_a_727_;
v___y_681_ = v___x_734_;
goto v___jp_679_;
}
else
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_756_; 
lean_dec(v___x_734_);
lean_dec(v_a_727_);
v_a_749_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_756_ == 0)
{
v___x_751_ = v___x_748_;
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_748_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_754_; 
if (v_isShared_752_ == 0)
{
v___x_754_ = v___x_751_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_a_749_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
lean_dec(v_a_727_);
lean_del_object(v___x_723_);
lean_dec(v_numFields_696_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_686_);
v_a_758_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_728_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_728_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_del_object(v___x_723_);
lean_dec(v_numFields_696_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
v_a_766_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_726_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_726_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_dec(v_numFields_696_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v_fvarId_658_);
lean_dec(v_mvarId_657_);
v_a_776_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_718_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_718_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
else
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
lean_dec_ref(v___x_715_);
lean_dec(v_numFields_696_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v_fvarId_658_);
lean_dec(v_mvarId_657_);
v_a_784_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___x_716_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_716_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_784_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
else
{
lean_object* v___x_792_; 
lean_dec(v_numFields_696_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_685_);
lean_dec(v_fvarId_658_);
lean_inc(v___y_693_);
lean_inc_ref(v___y_692_);
lean_inc(v___y_691_);
lean_inc_ref(v___y_690_);
v___x_792_ = lean_apply_5(v___y_687_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, lean_box(0));
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v_a_793_; uint8_t v___x_794_; 
v_a_793_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_a_793_);
lean_dec_ref_known(v___x_792_, 1);
v___x_794_ = lean_unbox(v_a_793_);
lean_dec(v_a_793_);
if (v___x_794_ == 0)
{
lean_dec(v_a_713_);
lean_dec(v___y_686_);
v___y_666_ = v___y_690_;
v___y_667_ = v___y_691_;
v___y_668_ = v___y_692_;
v___y_669_ = v___y_693_;
goto v___jp_665_;
}
else
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_795_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__13, &l_Lean_Meta_injectionCore___lam__1___closed__13_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__13);
v___x_796_ = l_Lean_indentExpr(v_a_713_);
v___x_797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_797_, 0, v___x_795_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
v___x_798_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v___y_686_, v___x_797_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_dec_ref_known(v___x_798_, 1);
v___y_666_ = v___y_690_;
v___y_667_ = v___y_691_;
v___y_668_ = v___y_692_;
v___y_669_ = v___y_693_;
goto v___jp_665_;
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v_mvarId_657_);
lean_dec(v___x_656_);
v_a_799_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_798_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_798_);
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
}
else
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_814_; 
lean_dec(v_a_713_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_686_);
lean_dec(v_mvarId_657_);
lean_dec(v___x_656_);
v_a_807_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_814_ == 0)
{
v___x_809_ = v___x_792_;
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_792_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
if (v_isShared_810_ == 0)
{
v___x_812_ = v___x_809_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_807_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
}
else
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_822_; 
lean_dec(v_numFields_696_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v_fvarId_658_);
lean_dec(v_mvarId_657_);
lean_dec(v___x_656_);
v_a_815_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_822_ == 0)
{
v___x_817_ = v___x_712_;
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_712_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_818_ == 0)
{
v___x_820_ = v___x_817_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_815_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
else
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_830_; 
lean_dec(v_numFields_696_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v_fvarId_658_);
lean_dec(v_mvarId_657_);
lean_dec(v___x_656_);
v_a_823_ = lean_ctor_get(v___x_710_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_830_ == 0)
{
v___x_825_ = v___x_710_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_710_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_823_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
}
v___jp_831_:
{
if (lean_obj_tag(v___y_840_) == 0)
{
lean_object* v_a_841_; lean_object* v___x_842_; 
v_a_841_ = lean_ctor_get(v___y_840_, 0);
lean_inc(v_a_841_);
lean_dec_ref_known(v___y_840_, 1);
lean_inc_ref(v___y_839_);
lean_inc(v___y_832_);
lean_inc_ref(v___y_837_);
lean_inc(v___y_833_);
lean_inc_ref(v___y_834_);
v___x_842_ = lean_apply_5(v___y_839_, v___y_834_, v___y_833_, v___y_837_, v___y_832_, lean_box(0));
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; uint8_t v___x_844_; 
v_a_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_a_843_);
lean_dec_ref_known(v___x_842_, 1);
v___x_844_ = lean_unbox(v_a_843_);
lean_dec(v_a_843_);
if (v___x_844_ == 0)
{
v___y_685_ = v___y_835_;
v___y_686_ = v___y_836_;
v___y_687_ = v___y_839_;
v___y_688_ = v___y_838_;
v___y_689_ = v_a_841_;
v___y_690_ = v___y_834_;
v___y_691_ = v___y_833_;
v___y_692_ = v___y_837_;
v___y_693_ = v___y_832_;
goto v___jp_684_;
}
else
{
lean_object* v___x_845_; 
lean_inc(v___y_832_);
lean_inc_ref(v___y_837_);
lean_inc(v___y_833_);
lean_inc_ref(v___y_834_);
lean_inc(v_a_841_);
v___x_845_ = lean_infer_type(v_a_841_, v___y_834_, v___y_833_, v___y_837_, v___y_832_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_a_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v_a_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_a_846_);
lean_dec_ref_known(v___x_845_, 1);
v___x_847_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__15, &l_Lean_Meta_injectionCore___lam__1___closed__15_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__15);
lean_inc(v_a_841_);
v___x_848_ = l_Lean_indentExpr(v_a_841_);
v___x_849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_847_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
v___x_850_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__17, &l_Lean_Meta_injectionCore___lam__1___closed__17_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__17);
v___x_851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_849_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
v___x_852_ = l_Lean_indentExpr(v_a_846_);
v___x_853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_851_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
lean_inc(v___y_836_);
v___x_854_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v___y_836_, v___x_853_, v___y_834_, v___y_833_, v___y_837_, v___y_832_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_dec_ref_known(v___x_854_, 1);
v___y_685_ = v___y_835_;
v___y_686_ = v___y_836_;
v___y_687_ = v___y_839_;
v___y_688_ = v___y_838_;
v___y_689_ = v_a_841_;
v___y_690_ = v___y_834_;
v___y_691_ = v___y_833_;
v___y_692_ = v___y_837_;
v___y_693_ = v___y_832_;
goto v___jp_684_;
}
else
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
lean_dec(v_a_841_);
lean_dec_ref(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_833_);
lean_dec(v___y_832_);
lean_dec(v_fvarId_658_);
lean_dec(v_mvarId_657_);
lean_dec(v___x_656_);
v_a_855_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v___x_854_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_854_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_855_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
else
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_870_; 
lean_dec(v_a_841_);
lean_dec_ref(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_833_);
lean_dec(v___y_832_);
lean_dec(v_fvarId_658_);
lean_dec(v_mvarId_657_);
lean_dec(v___x_656_);
v_a_863_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_870_ == 0)
{
v___x_865_ = v___x_845_;
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_845_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_a_863_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
}
else
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_878_; 
lean_dec(v_a_841_);
lean_dec_ref(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_833_);
lean_dec(v___y_832_);
lean_dec(v_fvarId_658_);
lean_dec(v_mvarId_657_);
lean_dec(v___x_656_);
v_a_871_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_878_ == 0)
{
v___x_873_ = v___x_842_;
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_842_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_876_; 
if (v_isShared_874_ == 0)
{
v___x_876_ = v___x_873_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_871_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
else
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
lean_dec_ref(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_833_);
lean_dec(v___y_832_);
lean_dec(v_fvarId_658_);
lean_dec(v_mvarId_657_);
lean_dec(v___x_656_);
v_a_879_ = lean_ctor_get(v___y_840_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___y_840_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___y_840_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___y_840_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
v___jp_887_:
{
lean_object* v___x_898_; uint8_t v_transparency_899_; uint8_t v___x_900_; uint8_t v___x_901_; 
v___x_898_ = l_Lean_Meta_Context_config(v___y_894_);
v_transparency_899_ = lean_ctor_get_uint8(v___x_898_, 9);
lean_dec_ref(v___x_898_);
v___x_900_ = 1;
v___x_901_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_899_, v___x_900_);
if (v___x_901_ == 0)
{
lean_object* v_keyedConfig_902_; uint8_t v_trackZetaDelta_903_; lean_object* v_zetaDeltaSet_904_; lean_object* v_lctx_905_; lean_object* v_localInstances_906_; lean_object* v_defEqCtx_x3f_907_; lean_object* v_synthPendingDepth_908_; lean_object* v_customCanUnfoldPredicate_x3f_909_; uint8_t v_univApprox_910_; uint8_t v_inTypeClassResolution_911_; uint8_t v_cacheInferType_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v_keyedConfig_902_ = lean_ctor_get(v___y_894_, 0);
v_trackZetaDelta_903_ = lean_ctor_get_uint8(v___y_894_, sizeof(void*)*7);
v_zetaDeltaSet_904_ = lean_ctor_get(v___y_894_, 1);
v_lctx_905_ = lean_ctor_get(v___y_894_, 2);
v_localInstances_906_ = lean_ctor_get(v___y_894_, 3);
v_defEqCtx_x3f_907_ = lean_ctor_get(v___y_894_, 4);
v_synthPendingDepth_908_ = lean_ctor_get(v___y_894_, 5);
v_customCanUnfoldPredicate_x3f_909_ = lean_ctor_get(v___y_894_, 6);
v_univApprox_910_ = lean_ctor_get_uint8(v___y_894_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_911_ = lean_ctor_get_uint8(v___y_894_, sizeof(void*)*7 + 2);
v_cacheInferType_912_ = lean_ctor_get_uint8(v___y_894_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_902_);
v___x_913_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_900_, v_keyedConfig_902_);
lean_inc(v_customCanUnfoldPredicate_x3f_909_);
lean_inc(v_synthPendingDepth_908_);
lean_inc(v_defEqCtx_x3f_907_);
lean_inc_ref(v_localInstances_906_);
lean_inc_ref(v_lctx_905_);
lean_inc(v_zetaDeltaSet_904_);
v___x_914_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_914_, 0, v___x_913_);
lean_ctor_set(v___x_914_, 1, v_zetaDeltaSet_904_);
lean_ctor_set(v___x_914_, 2, v_lctx_905_);
lean_ctor_set(v___x_914_, 3, v_localInstances_906_);
lean_ctor_set(v___x_914_, 4, v_defEqCtx_x3f_907_);
lean_ctor_set(v___x_914_, 5, v_synthPendingDepth_908_);
lean_ctor_set(v___x_914_, 6, v_customCanUnfoldPredicate_x3f_909_);
lean_ctor_set_uint8(v___x_914_, sizeof(void*)*7, v_trackZetaDelta_903_);
lean_ctor_set_uint8(v___x_914_, sizeof(void*)*7 + 1, v_univApprox_910_);
lean_ctor_set_uint8(v___x_914_, sizeof(void*)*7 + 2, v_inTypeClassResolution_911_);
lean_ctor_set_uint8(v___x_914_, sizeof(void*)*7 + 3, v_cacheInferType_912_);
v___x_915_ = l_Lean_Meta_mkNoConfusion(v___y_888_, v___y_893_, v___x_914_, v___y_895_, v___y_896_, v___y_897_);
lean_dec_ref_known(v___x_914_, 7);
v___y_832_ = v___y_897_;
v___y_833_ = v___y_895_;
v___y_834_ = v___y_894_;
v___y_835_ = v___y_889_;
v___y_836_ = v___y_890_;
v___y_837_ = v___y_896_;
v___y_838_ = v___y_892_;
v___y_839_ = v___y_891_;
v___y_840_ = v___x_915_;
goto v___jp_831_;
}
else
{
lean_object* v___x_916_; 
v___x_916_ = l_Lean_Meta_mkNoConfusion(v___y_888_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
v___y_832_ = v___y_897_;
v___y_833_ = v___y_895_;
v___y_834_ = v___y_894_;
v___y_835_ = v___y_889_;
v___y_836_ = v___y_890_;
v___y_837_ = v___y_896_;
v___y_838_ = v___y_892_;
v___y_839_ = v___y_891_;
v___y_840_ = v___x_916_;
goto v___jp_831_;
}
}
v___jp_917_:
{
lean_object* v___x_920_; lean_object* v___x_921_; uint8_t v___x_922_; 
v___x_920_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__19));
v___x_921_ = lean_unsigned_to_nat(3u);
v___x_922_ = l_Lean_Expr_isAppOfArity(v_type_918_, v___x_920_, v___x_921_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; lean_object* v___x_924_; 
lean_dec_ref(v_prf_919_);
lean_dec_ref(v_type_918_);
lean_dec_ref(v___x_659_);
lean_dec(v_fvarId_658_);
v___x_923_ = lean_obj_once(&l_Lean_Meta_injectionCore___lam__1___closed__23, &l_Lean_Meta_injectionCore___lam__1___closed__23_once, _init_l_Lean_Meta_injectionCore___lam__1___closed__23);
v___x_924_ = l_Lean_Meta_throwTacticEx___redArg(v___x_656_, v_mvarId_657_, v___x_923_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
return v___x_924_;
}
else
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_925_ = l_Lean_Expr_appFn_x21(v_type_918_);
v___x_926_ = l_Lean_Expr_appArg_x21(v___x_925_);
lean_dec_ref(v___x_925_);
v___x_927_ = l_Lean_Expr_appArg_x21(v_type_918_);
lean_dec_ref(v_type_918_);
lean_inc(v_mvarId_657_);
v___x_928_ = l_Lean_MVarId_getType(v_mvarId_657_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; lean_object* v___x_930_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_a_929_);
lean_dec_ref_known(v___x_928_, 1);
v___x_930_ = l_Lean_Meta_isConstructorApp_x27_x3f(v___x_926_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v_a_931_; lean_object* v___x_932_; 
v_a_931_ = lean_ctor_get(v___x_930_, 0);
lean_inc(v_a_931_);
lean_dec_ref_known(v___x_930_, 1);
v___x_932_ = l_Lean_Meta_isConstructorApp_x27_x3f(v___x_927_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
if (lean_obj_tag(v___x_932_) == 0)
{
if (lean_obj_tag(v_a_931_) == 1)
{
lean_object* v_a_933_; 
v_a_933_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_a_933_);
lean_dec_ref_known(v___x_932_, 1);
if (lean_obj_tag(v_a_933_) == 1)
{
lean_object* v_val_934_; lean_object* v_val_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___f_939_; lean_object* v___x_940_; lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_974_; 
v_val_934_ = lean_ctor_get(v_a_931_, 0);
lean_inc(v_val_934_);
lean_dec_ref_known(v_a_931_, 1);
v_val_935_ = lean_ctor_get(v_a_933_, 0);
lean_inc(v_val_935_);
lean_dec_ref_known(v_a_933_, 1);
v___x_936_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__24));
v___x_937_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__1___closed__25));
v___x_938_ = l_Lean_Name_mkStr3(v___x_936_, v___x_937_, v___x_659_);
lean_inc_n(v___x_938_, 2);
v___f_939_ = lean_alloc_closure((void*)(l_Lean_Meta_injectionCore___lam__0___boxed), 6, 1);
lean_closure_set(v___f_939_, 0, v___x_938_);
v___x_940_ = l_Lean_Meta_injectionCore___lam__0(v___x_938_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
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
v___y_888_ = v_a_929_;
v___y_889_ = v_val_934_;
v___y_890_ = v___x_938_;
v___y_891_ = v___f_939_;
v___y_892_ = v_val_935_;
v___y_893_ = v_prf_919_;
v___y_894_ = v___y_660_;
v___y_895_ = v___y_661_;
v___y_896_ = v___y_662_;
v___y_897_ = v___y_663_;
goto v___jp_887_;
}
else
{
lean_object* v___x_946_; 
lean_inc(v___y_663_);
lean_inc_ref(v___y_662_);
lean_inc(v___y_661_);
lean_inc_ref(v___y_660_);
lean_inc_ref(v_prf_919_);
v___x_946_ = lean_infer_type(v_prf_919_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
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
lean_inc(v_mvarId_657_);
if (v_isShared_944_ == 0)
{
lean_ctor_set_tag(v___x_943_, 1);
lean_ctor_set(v___x_943_, 0, v_mvarId_657_);
v___x_954_ = v___x_943_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_mvarId_657_);
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
v___x_956_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v___x_938_, v___x_955_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_dec_ref_known(v___x_956_, 1);
v___y_888_ = v_a_929_;
v___y_889_ = v_val_934_;
v___y_890_ = v___x_938_;
v___y_891_ = v___f_939_;
v___y_892_ = v_val_935_;
v___y_893_ = v_prf_919_;
v___y_894_ = v___y_660_;
v___y_895_ = v___y_661_;
v___y_896_ = v___y_662_;
v___y_897_ = v___y_663_;
goto v___jp_887_;
}
else
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
lean_dec_ref(v___f_939_);
lean_dec(v___x_938_);
lean_dec(v_val_935_);
lean_dec(v_val_934_);
lean_dec(v_a_929_);
lean_dec_ref(v_prf_919_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v_fvarId_658_);
lean_dec(v_mvarId_657_);
lean_dec(v___x_656_);
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
lean_dec(v_a_929_);
lean_dec_ref(v_prf_919_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v_fvarId_658_);
lean_dec(v_mvarId_657_);
lean_dec(v___x_656_);
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
lean_dec(v_a_933_);
lean_dec_ref_known(v_a_931_, 1);
lean_dec(v_a_929_);
lean_dec_ref(v_prf_919_);
lean_dec_ref(v___x_659_);
lean_dec(v_fvarId_658_);
v___y_673_ = v___y_660_;
v___y_674_ = v___y_661_;
v___y_675_ = v___y_662_;
v___y_676_ = v___y_663_;
goto v___jp_672_;
}
}
else
{
lean_dec_ref_known(v___x_932_, 1);
lean_dec(v_a_931_);
lean_dec(v_a_929_);
lean_dec_ref(v_prf_919_);
lean_dec_ref(v___x_659_);
lean_dec(v_fvarId_658_);
v___y_673_ = v___y_660_;
v___y_674_ = v___y_661_;
v___y_675_ = v___y_662_;
v___y_676_ = v___y_663_;
goto v___jp_672_;
}
}
else
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
lean_dec(v_a_931_);
lean_dec(v_a_929_);
lean_dec_ref(v_prf_919_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec_ref(v___x_659_);
lean_dec(v_fvarId_658_);
lean_dec(v_mvarId_657_);
lean_dec(v___x_656_);
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
lean_dec(v_a_929_);
lean_dec_ref(v___x_927_);
lean_dec_ref(v_prf_919_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec_ref(v___x_659_);
lean_dec(v_fvarId_658_);
lean_dec(v_mvarId_657_);
lean_dec(v___x_656_);
v_a_983_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_930_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_930_);
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
lean_dec_ref(v___x_927_);
lean_dec_ref(v___x_926_);
lean_dec_ref(v_prf_919_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec_ref(v___x_659_);
lean_dec(v_fvarId_658_);
lean_dec(v_mvarId_657_);
lean_dec(v___x_656_);
v_a_991_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_928_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_928_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___lam__1___boxed(lean_object* v___x_1071_, lean_object* v_mvarId_1072_, lean_object* v_fvarId_1073_, lean_object* v___x_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Lean_Meta_injectionCore___lam__1(v___x_1071_, v_mvarId_1072_, v_fvarId_1073_, v___x_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
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
lean_closure_set(v___f_1093_, 0, v___x_1092_);
lean_closure_set(v___f_1093_, 1, v_mvarId_1084_);
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
size_t v_x_15753__boxed_1137_; size_t v_x_15754__boxed_1138_; lean_object* v_res_1139_; 
v_x_15753__boxed_1137_ = lean_unbox_usize(v_x_1133_);
lean_dec(v_x_1133_);
v_x_15754__boxed_1138_ = lean_unbox_usize(v_x_1134_);
lean_dec(v_x_1134_);
v_res_1139_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2(v_00_u03b2_1131_, v_x_1132_, v_x_15753__boxed_1137_, v_x_15754__boxed_1138_, v_x_1135_, v_x_1136_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorIdx___impl(lean_object* v_x_1168_){
_start:
{
lean_object* v___x_1169_; 
v___x_1169_ = lean_obj_tag_nat(v_x_1168_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorIdx___impl___boxed(lean_object* v_x_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Lean_Meta_InjectionResult_ctorIdx___impl(v_x_1170_);
lean_dec(v_x_1170_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorElim___redArg(lean_object* v_t_1172_, lean_object* v_k_1173_){
_start:
{
if (lean_obj_tag(v_t_1172_) == 0)
{
return v_k_1173_;
}
else
{
lean_object* v_mvarId_1174_; lean_object* v_newEqs_1175_; lean_object* v_remainingNames_1176_; lean_object* v___x_1177_; 
v_mvarId_1174_ = lean_ctor_get(v_t_1172_, 0);
lean_inc(v_mvarId_1174_);
v_newEqs_1175_ = lean_ctor_get(v_t_1172_, 1);
lean_inc_ref(v_newEqs_1175_);
v_remainingNames_1176_ = lean_ctor_get(v_t_1172_, 2);
lean_inc(v_remainingNames_1176_);
lean_dec_ref_known(v_t_1172_, 3);
v___x_1177_ = lean_apply_3(v_k_1173_, v_mvarId_1174_, v_newEqs_1175_, v_remainingNames_1176_);
return v___x_1177_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorElim(lean_object* v_motive_1178_, lean_object* v_ctorIdx_1179_, lean_object* v_t_1180_, lean_object* v_h_1181_, lean_object* v_k_1182_){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_1180_, v_k_1182_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_ctorElim___boxed(lean_object* v_motive_1184_, lean_object* v_ctorIdx_1185_, lean_object* v_t_1186_, lean_object* v_h_1187_, lean_object* v_k_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Lean_Meta_InjectionResult_ctorElim(v_motive_1184_, v_ctorIdx_1185_, v_t_1186_, v_h_1187_, v_k_1188_);
lean_dec(v_ctorIdx_1185_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_solved_elim___redArg(lean_object* v_t_1190_, lean_object* v_solved_1191_){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_1190_, v_solved_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_solved_elim(lean_object* v_motive_1193_, lean_object* v_t_1194_, lean_object* v_h_1195_, lean_object* v_solved_1196_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_1194_, v_solved_1196_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_subgoal_elim___redArg(lean_object* v_t_1198_, lean_object* v_subgoal_1199_){
_start:
{
lean_object* v___x_1200_; 
v___x_1200_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_1198_, v_subgoal_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionResult_subgoal_elim(lean_object* v_motive_1201_, lean_object* v_t_1202_, lean_object* v_h_1203_, lean_object* v_subgoal_1204_){
_start:
{
lean_object* v___x_1205_; 
v___x_1205_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_1202_, v_subgoal_1204_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go(uint8_t v_tryToClear_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_){
_start:
{
lean_object* v_zero_1216_; uint8_t v_isZero_1217_; 
v_zero_1216_ = lean_unsigned_to_nat(0u);
v_isZero_1217_ = lean_nat_dec_eq(v_a_1207_, v_zero_1216_);
if (v_isZero_1217_ == 1)
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
lean_dec(v_a_1207_);
v___x_1218_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1218_, 0, v_a_1208_);
lean_ctor_set(v___x_1218_, 1, v_a_1209_);
lean_ctor_set(v___x_1218_, 2, v_a_1210_);
v___x_1219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1218_);
return v___x_1219_;
}
else
{
lean_object* v_one_1220_; lean_object* v_n_1221_; 
v_one_1220_ = lean_unsigned_to_nat(1u);
v_n_1221_ = lean_nat_sub(v_a_1207_, v_one_1220_);
lean_dec(v_a_1207_);
if (lean_obj_tag(v_a_1210_) == 0)
{
lean_object* v___x_1222_; 
v___x_1222_ = l_Lean_Meta_intro1Core(v_a_1208_, v_isZero_1217_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v_a_1223_; lean_object* v_fst_1224_; lean_object* v_snd_1225_; lean_object* v___x_1226_; 
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc(v_a_1223_);
lean_dec_ref_known(v___x_1222_, 1);
v_fst_1224_ = lean_ctor_get(v_a_1223_, 0);
lean_inc(v_fst_1224_);
v_snd_1225_ = lean_ctor_get(v_a_1223_, 1);
lean_inc(v_snd_1225_);
lean_dec(v_a_1223_);
v___x_1226_ = l_Lean_Meta_heqToEq(v_snd_1225_, v_fst_1224_, v_tryToClear_1206_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v_a_1227_; lean_object* v_fst_1228_; lean_object* v_snd_1229_; lean_object* v___x_1230_; 
v_a_1227_ = lean_ctor_get(v___x_1226_, 0);
lean_inc(v_a_1227_);
lean_dec_ref_known(v___x_1226_, 1);
v_fst_1228_ = lean_ctor_get(v_a_1227_, 0);
lean_inc(v_fst_1228_);
v_snd_1229_ = lean_ctor_get(v_a_1227_, 1);
lean_inc(v_snd_1229_);
lean_dec(v_a_1227_);
v___x_1230_ = lean_array_push(v_a_1209_, v_fst_1228_);
v_a_1207_ = v_n_1221_;
v_a_1208_ = v_snd_1229_;
v_a_1209_ = v___x_1230_;
goto _start;
}
else
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1239_; 
lean_dec(v_n_1221_);
lean_dec_ref(v_a_1209_);
v_a_1232_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1234_ = v___x_1226_;
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1226_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1237_; 
if (v_isShared_1235_ == 0)
{
v___x_1237_ = v___x_1234_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_a_1232_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
lean_dec(v_n_1221_);
lean_dec_ref(v_a_1209_);
v_a_1240_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1222_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1222_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
else
{
lean_object* v_head_1248_; lean_object* v_tail_1249_; lean_object* v___x_1250_; 
v_head_1248_ = lean_ctor_get(v_a_1210_, 0);
lean_inc(v_head_1248_);
v_tail_1249_ = lean_ctor_get(v_a_1210_, 1);
lean_inc(v_tail_1249_);
lean_dec_ref_known(v_a_1210_, 2);
v___x_1250_ = l_Lean_MVarId_intro(v_a_1208_, v_head_1248_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v_a_1251_; lean_object* v_fst_1252_; lean_object* v_snd_1253_; lean_object* v___x_1254_; 
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
lean_inc(v_a_1251_);
lean_dec_ref_known(v___x_1250_, 1);
v_fst_1252_ = lean_ctor_get(v_a_1251_, 0);
lean_inc(v_fst_1252_);
v_snd_1253_ = lean_ctor_get(v_a_1251_, 1);
lean_inc(v_snd_1253_);
lean_dec(v_a_1251_);
v___x_1254_ = l_Lean_Meta_heqToEq(v_snd_1253_, v_fst_1252_, v_tryToClear_1206_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; lean_object* v_fst_1256_; lean_object* v_snd_1257_; lean_object* v___x_1258_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_a_1255_);
lean_dec_ref_known(v___x_1254_, 1);
v_fst_1256_ = lean_ctor_get(v_a_1255_, 0);
lean_inc(v_fst_1256_);
v_snd_1257_ = lean_ctor_get(v_a_1255_, 1);
lean_inc(v_snd_1257_);
lean_dec(v_a_1255_);
v___x_1258_ = lean_array_push(v_a_1209_, v_fst_1256_);
v_a_1207_ = v_n_1221_;
v_a_1208_ = v_snd_1257_;
v_a_1209_ = v___x_1258_;
v_a_1210_ = v_tail_1249_;
goto _start;
}
else
{
lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1267_; 
lean_dec(v_tail_1249_);
lean_dec(v_n_1221_);
lean_dec_ref(v_a_1209_);
v_a_1260_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1262_ = v___x_1254_;
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v___x_1254_);
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
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1275_; 
lean_dec(v_tail_1249_);
lean_dec(v_n_1221_);
lean_dec_ref(v_a_1209_);
v_a_1268_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1270_ = v___x_1250_;
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1250_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1268_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go___boxed(lean_object* v_tryToClear_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_){
_start:
{
uint8_t v_tryToClear_boxed_1286_; lean_object* v_res_1287_; 
v_tryToClear_boxed_1286_ = lean_unbox(v_tryToClear_1276_);
v_res_1287_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go(v_tryToClear_boxed_1286_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_);
lean_dec(v_a_1284_);
lean_dec_ref(v_a_1283_);
lean_dec(v_a_1282_);
lean_dec_ref(v_a_1281_);
return v_res_1287_;
}
}
static lean_object* _init_l_Lean_Meta_injectionIntro___closed__2(void){
_start:
{
lean_object* v_cls_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v_cls_1294_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__1));
v___x_1295_ = ((lean_object*)(l_Lean_Meta_injectionCore___lam__0___closed__1));
v___x_1296_ = l_Lean_Name_append(v___x_1295_, v_cls_1294_);
return v___x_1296_;
}
}
static lean_object* _init_l_Lean_Meta_injectionIntro___closed__4(void){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__3));
v___x_1299_ = l_Lean_stringToMessageData(v___x_1298_);
return v___x_1299_;
}
}
static lean_object* _init_l_Lean_Meta_injectionIntro___closed__6(void){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__5));
v___x_1302_ = l_Lean_stringToMessageData(v___x_1301_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro(lean_object* v_mvarId_1303_, lean_object* v_numEqs_1304_, lean_object* v_newNames_1305_, uint8_t v_tryToClear_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_){
_start:
{
lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v_toCold_1319_; lean_object* v_options_1320_; uint8_t v_hasTrace_1321_; 
v_toCold_1319_ = lean_ctor_get(v_a_1309_, 0);
v_options_1320_ = lean_ctor_get(v_toCold_1319_, 2);
v_hasTrace_1321_ = lean_ctor_get_uint8(v_options_1320_, sizeof(void*)*1);
if (v_hasTrace_1321_ == 0)
{
v___y_1313_ = v_a_1307_;
v___y_1314_ = v_a_1308_;
v___y_1315_ = v_a_1309_;
v___y_1316_ = v_a_1310_;
goto v___jp_1312_;
}
else
{
lean_object* v_inheritedTraceOptions_1322_; lean_object* v_cls_1323_; lean_object* v___x_1324_; uint8_t v___x_1325_; 
v_inheritedTraceOptions_1322_ = lean_ctor_get(v_toCold_1319_, 11);
v_cls_1323_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__1));
v___x_1324_ = lean_obj_once(&l_Lean_Meta_injectionIntro___closed__2, &l_Lean_Meta_injectionIntro___closed__2_once, _init_l_Lean_Meta_injectionIntro___closed__2);
v___x_1325_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1322_, v_options_1320_, v___x_1324_);
if (v___x_1325_ == 0)
{
v___y_1313_ = v_a_1307_;
v___y_1314_ = v_a_1308_;
v___y_1315_ = v_a_1309_;
v___y_1316_ = v_a_1310_;
goto v___jp_1312_;
}
else
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1326_ = lean_obj_once(&l_Lean_Meta_injectionIntro___closed__4, &l_Lean_Meta_injectionIntro___closed__4_once, _init_l_Lean_Meta_injectionIntro___closed__4);
lean_inc(v_numEqs_1304_);
v___x_1327_ = l_Nat_reprFast(v_numEqs_1304_);
v___x_1328_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1327_);
v___x_1329_ = l_Lean_MessageData_ofFormat(v___x_1328_);
v___x_1330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1326_);
lean_ctor_set(v___x_1330_, 1, v___x_1329_);
v___x_1331_ = lean_obj_once(&l_Lean_Meta_injectionIntro___closed__6, &l_Lean_Meta_injectionIntro___closed__6_once, _init_l_Lean_Meta_injectionIntro___closed__6);
v___x_1332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1330_);
lean_ctor_set(v___x_1332_, 1, v___x_1331_);
lean_inc(v_mvarId_1303_);
v___x_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1333_, 0, v_mvarId_1303_);
v___x_1334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1332_);
lean_ctor_set(v___x_1334_, 1, v___x_1333_);
v___x_1335_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v_cls_1323_, v___x_1334_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_dec_ref_known(v___x_1335_, 1);
v___y_1313_ = v_a_1307_;
v___y_1314_ = v_a_1308_;
v___y_1315_ = v_a_1309_;
v___y_1316_ = v_a_1310_;
goto v___jp_1312_;
}
else
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1343_; 
lean_dec(v_newNames_1305_);
lean_dec(v_numEqs_1304_);
lean_dec(v_mvarId_1303_);
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1338_ = v___x_1335_;
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1335_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1341_; 
if (v_isShared_1339_ == 0)
{
v___x_1341_ = v___x_1338_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_a_1336_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
}
v___jp_1312_:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1317_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__0));
v___x_1318_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go(v_tryToClear_1306_, v_numEqs_1304_, v_mvarId_1303_, v___x_1317_, v_newNames_1305_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
return v___x_1318_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro___boxed(lean_object* v_mvarId_1344_, lean_object* v_numEqs_1345_, lean_object* v_newNames_1346_, lean_object* v_tryToClear_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_){
_start:
{
uint8_t v_tryToClear_boxed_1353_; lean_object* v_res_1354_; 
v_tryToClear_boxed_1353_ = lean_unbox(v_tryToClear_1347_);
v_res_1354_ = l_Lean_Meta_injectionIntro(v_mvarId_1344_, v_numEqs_1345_, v_newNames_1346_, v_tryToClear_boxed_1353_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_);
lean_dec(v_a_1351_);
lean_dec_ref(v_a_1350_);
lean_dec(v_a_1349_);
lean_dec_ref(v_a_1348_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injection(lean_object* v_mvarId_1355_, lean_object* v_fvarId_1356_, lean_object* v_newNames_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_){
_start:
{
lean_object* v___x_1363_; 
v___x_1363_ = l_Lean_Meta_injectionCore(v_mvarId_1355_, v_fvarId_1356_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1376_; 
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1366_ = v___x_1363_;
v_isShared_1367_ = v_isSharedCheck_1376_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1363_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1376_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
if (lean_obj_tag(v_a_1364_) == 0)
{
lean_object* v___x_1368_; lean_object* v___x_1370_; 
lean_dec(v_newNames_1357_);
v___x_1368_ = lean_box(0);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 0, v___x_1368_);
v___x_1370_ = v___x_1366_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1368_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
else
{
lean_object* v_mvarId_1372_; lean_object* v_numNewEqs_1373_; uint8_t v___x_1374_; lean_object* v___x_1375_; 
lean_del_object(v___x_1366_);
v_mvarId_1372_ = lean_ctor_get(v_a_1364_, 0);
lean_inc(v_mvarId_1372_);
v_numNewEqs_1373_ = lean_ctor_get(v_a_1364_, 1);
lean_inc(v_numNewEqs_1373_);
lean_dec_ref_known(v_a_1364_, 2);
v___x_1374_ = 1;
v___x_1375_ = l_Lean_Meta_injectionIntro(v_mvarId_1372_, v_numNewEqs_1373_, v_newNames_1357_, v___x_1374_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_);
return v___x_1375_;
}
}
}
else
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
lean_dec(v_newNames_1357_);
v_a_1377_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1379_ = v___x_1363_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1363_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1377_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injection___boxed(lean_object* v_mvarId_1385_, lean_object* v_fvarId_1386_, lean_object* v_newNames_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l_Lean_Meta_injection(v_mvarId_1385_, v_fvarId_1386_, v_newNames_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_);
lean_dec(v_a_1391_);
lean_dec_ref(v_a_1390_);
lean_dec(v_a_1389_);
lean_dec_ref(v_a_1388_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorIdx___impl(lean_object* v_x_1394_){
_start:
{
lean_object* v___x_1395_; 
v___x_1395_ = lean_obj_tag_nat(v_x_1394_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorIdx___impl___boxed(lean_object* v_x_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Lean_Meta_InjectionsResult_ctorIdx___impl(v_x_1396_);
lean_dec(v_x_1396_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorElim___redArg(lean_object* v_t_1398_, lean_object* v_k_1399_){
_start:
{
if (lean_obj_tag(v_t_1398_) == 0)
{
return v_k_1399_;
}
else
{
lean_object* v_mvarId_1400_; lean_object* v_remainingNames_1401_; lean_object* v_forbidden_1402_; lean_object* v___x_1403_; 
v_mvarId_1400_ = lean_ctor_get(v_t_1398_, 0);
lean_inc(v_mvarId_1400_);
v_remainingNames_1401_ = lean_ctor_get(v_t_1398_, 1);
lean_inc(v_remainingNames_1401_);
v_forbidden_1402_ = lean_ctor_get(v_t_1398_, 2);
lean_inc(v_forbidden_1402_);
lean_dec_ref_known(v_t_1398_, 3);
v___x_1403_ = lean_apply_3(v_k_1399_, v_mvarId_1400_, v_remainingNames_1401_, v_forbidden_1402_);
return v___x_1403_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorElim(lean_object* v_motive_1404_, lean_object* v_ctorIdx_1405_, lean_object* v_t_1406_, lean_object* v_h_1407_, lean_object* v_k_1408_){
_start:
{
lean_object* v___x_1409_; 
v___x_1409_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1406_, v_k_1408_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_ctorElim___boxed(lean_object* v_motive_1410_, lean_object* v_ctorIdx_1411_, lean_object* v_t_1412_, lean_object* v_h_1413_, lean_object* v_k_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Lean_Meta_InjectionsResult_ctorElim(v_motive_1410_, v_ctorIdx_1411_, v_t_1412_, v_h_1413_, v_k_1414_);
lean_dec(v_ctorIdx_1411_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_solved_elim___redArg(lean_object* v_t_1416_, lean_object* v_solved_1417_){
_start:
{
lean_object* v___x_1418_; 
v___x_1418_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1416_, v_solved_1417_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_solved_elim(lean_object* v_motive_1419_, lean_object* v_t_1420_, lean_object* v_h_1421_, lean_object* v_solved_1422_){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1420_, v_solved_1422_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_subgoal_elim___redArg(lean_object* v_t_1424_, lean_object* v_subgoal_1425_){
_start:
{
lean_object* v___x_1426_; 
v___x_1426_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1424_, v_subgoal_1425_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InjectionsResult_subgoal_elim(lean_object* v_motive_1427_, lean_object* v_t_1428_, lean_object* v_h_1429_, lean_object* v_subgoal_1430_){
_start:
{
lean_object* v___x_1431_; 
v___x_1431_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_1428_, v_subgoal_1430_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(lean_object* v_x_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Lean_Meta_saveState___redArg(v___y_1434_, v___y_1436_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v_a_1439_; lean_object* v___x_1440_; 
v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
lean_inc(v_a_1439_);
lean_dec_ref_known(v___x_1438_, 1);
lean_inc(v___y_1436_);
lean_inc_ref(v___y_1435_);
lean_inc(v___y_1434_);
lean_inc_ref(v___y_1433_);
v___x_1440_ = lean_apply_5(v_x_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, lean_box(0));
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_dec(v_a_1439_);
return v___x_1440_;
}
else
{
lean_object* v_a_1441_; uint8_t v___y_1443_; uint8_t v___x_1461_; 
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_a_1441_);
v___x_1461_ = l_Lean_Exception_isInterrupt(v_a_1441_);
if (v___x_1461_ == 0)
{
uint8_t v___x_1462_; 
lean_inc(v_a_1441_);
v___x_1462_ = l_Lean_Exception_isRuntime(v_a_1441_);
v___y_1443_ = v___x_1462_;
goto v___jp_1442_;
}
else
{
v___y_1443_ = v___x_1461_;
goto v___jp_1442_;
}
v___jp_1442_:
{
if (v___y_1443_ == 0)
{
lean_object* v___x_1444_; 
lean_dec_ref_known(v___x_1440_, 1);
v___x_1444_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1439_, v___y_1434_, v___y_1436_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1451_; 
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1451_ == 0)
{
lean_object* v_unused_1452_; 
v_unused_1452_ = lean_ctor_get(v___x_1444_, 0);
lean_dec(v_unused_1452_);
v___x_1446_ = v___x_1444_;
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
else
{
lean_dec(v___x_1444_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1449_; 
if (v_isShared_1447_ == 0)
{
lean_ctor_set_tag(v___x_1446_, 1);
lean_ctor_set(v___x_1446_, 0, v_a_1441_);
v___x_1449_ = v___x_1446_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_a_1441_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
else
{
lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1460_; 
lean_dec(v_a_1441_);
v_a_1453_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1455_ = v___x_1444_;
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1444_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1458_; 
if (v_isShared_1456_ == 0)
{
v___x_1458_ = v___x_1455_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_a_1453_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
}
else
{
lean_dec(v_a_1441_);
lean_dec(v_a_1439_);
return v___x_1440_;
}
}
}
}
else
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
lean_dec_ref(v_x_1432_);
v_a_1463_ = lean_ctor_get(v___x_1438_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1465_ = v___x_1438_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1438_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1463_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg___boxed(lean_object* v_x_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(v_x_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1(lean_object* v_00_u03b1_1478_, lean_object* v_x_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v___x_1485_; 
v___x_1485_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(v_x_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___boxed(lean_object* v_00_u03b1_1486_, lean_object* v_x_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1(v_00_u03b1_1486_, v_x_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
return v_res_1493_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(lean_object* v_k_1494_, lean_object* v_t_1495_){
_start:
{
if (lean_obj_tag(v_t_1495_) == 0)
{
lean_object* v_k_1496_; lean_object* v_l_1497_; lean_object* v_r_1498_; uint8_t v___x_1499_; 
v_k_1496_ = lean_ctor_get(v_t_1495_, 1);
v_l_1497_ = lean_ctor_get(v_t_1495_, 3);
v_r_1498_ = lean_ctor_get(v_t_1495_, 4);
v___x_1499_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1494_, v_k_1496_);
switch(v___x_1499_)
{
case 0:
{
v_t_1495_ = v_l_1497_;
goto _start;
}
case 1:
{
uint8_t v___x_1501_; 
v___x_1501_ = 1;
return v___x_1501_;
}
default: 
{
v_t_1495_ = v_r_1498_;
goto _start;
}
}
}
else
{
uint8_t v___x_1503_; 
v___x_1503_ = 0;
return v___x_1503_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg___boxed(lean_object* v_k_1504_, lean_object* v_t_1505_){
_start:
{
uint8_t v_res_1506_; lean_object* v_r_1507_; 
v_res_1506_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(v_k_1504_, v_t_1505_);
lean_dec(v_t_1505_);
lean_dec(v_k_1504_);
v_r_1507_ = lean_box(v_res_1506_);
return v_r_1507_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4(void){
_start:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1514_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__3));
v___x_1515_ = l_Lean_MessageData_ofFormat(v___x_1514_);
return v___x_1515_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5(void){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1516_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4, &l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4_once, _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4);
v___x_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1516_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0___boxed(lean_object* v_mvarId_1518_, lean_object* v_head_1519_, lean_object* v_newNames_1520_, lean_object* v_tail_1521_, lean_object* v_forbidden_1522_, lean_object* v_n_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0(v_mvarId_1518_, v_head_1519_, v_newNames_1520_, v_tail_1521_, v_forbidden_1522_, v_n_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go(lean_object* v_depth_1530_, lean_object* v_fvarIds_1531_, lean_object* v_mvarId_1532_, lean_object* v_newNames_1533_, lean_object* v_forbidden_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_){
_start:
{
lean_object* v_zero_1540_; uint8_t v_isZero_1541_; 
v_zero_1540_ = lean_unsigned_to_nat(0u);
v_isZero_1541_ = lean_nat_dec_eq(v_depth_1530_, v_zero_1540_);
if (v_isZero_1541_ == 1)
{
lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
lean_dec(v_forbidden_1534_);
lean_dec(v_newNames_1533_);
lean_dec(v_fvarIds_1531_);
lean_dec(v_depth_1530_);
v___x_1542_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__1));
v___x_1543_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5, &l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5_once, _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5);
v___x_1544_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1542_, v_mvarId_1532_, v___x_1543_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_);
return v___x_1544_;
}
else
{
if (lean_obj_tag(v_fvarIds_1531_) == 0)
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
lean_dec(v_depth_1530_);
v___x_1545_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1545_, 0, v_mvarId_1532_);
lean_ctor_set(v___x_1545_, 1, v_newNames_1533_);
lean_ctor_set(v___x_1545_, 2, v_forbidden_1534_);
v___x_1546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1545_);
return v___x_1546_;
}
else
{
lean_object* v_head_1547_; lean_object* v_tail_1548_; lean_object* v_one_1549_; lean_object* v_n_1550_; lean_object* v___x_1551_; lean_object* v___y_1553_; uint8_t v___y_1554_; uint8_t v___x_1556_; 
v_head_1547_ = lean_ctor_get(v_fvarIds_1531_, 0);
lean_inc(v_head_1547_);
v_tail_1548_ = lean_ctor_get(v_fvarIds_1531_, 1);
lean_inc(v_tail_1548_);
lean_dec_ref_known(v_fvarIds_1531_, 2);
v_one_1549_ = lean_unsigned_to_nat(1u);
v_n_1550_ = lean_nat_sub(v_depth_1530_, v_one_1549_);
lean_dec(v_depth_1530_);
v___x_1551_ = lean_nat_add(v_n_1550_, v_one_1549_);
v___x_1556_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(v_head_1547_, v_forbidden_1534_);
if (v___x_1556_ == 0)
{
lean_object* v___f_1557_; lean_object* v___x_1558_; 
lean_inc(v_forbidden_1534_);
lean_inc(v_tail_1548_);
lean_inc(v_newNames_1533_);
lean_inc(v_head_1547_);
lean_inc(v_mvarId_1532_);
v___f_1557_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0___boxed), 11, 6);
lean_closure_set(v___f_1557_, 0, v_mvarId_1532_);
lean_closure_set(v___f_1557_, 1, v_head_1547_);
lean_closure_set(v___f_1557_, 2, v_newNames_1533_);
lean_closure_set(v___f_1557_, 3, v_tail_1548_);
lean_closure_set(v___f_1557_, 4, v_forbidden_1534_);
lean_closure_set(v___f_1557_, 5, v_n_1550_);
v___x_1558_ = l_Lean_FVarId_getType___redArg(v_head_1547_, v_a_1535_, v_a_1537_, v_a_1538_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; lean_object* v___x_1560_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_a_1559_);
lean_dec_ref_known(v___x_1558_, 1);
v___x_1560_ = l_Lean_Meta_matchEqHEq_x3f(v_a_1559_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1561_);
lean_dec_ref_known(v___x_1560_, 1);
if (lean_obj_tag(v_a_1561_) == 1)
{
lean_object* v_val_1562_; lean_object* v_snd_1563_; lean_object* v_fst_1564_; lean_object* v_snd_1565_; lean_object* v___x_1566_; 
v_val_1562_ = lean_ctor_get(v_a_1561_, 0);
lean_inc(v_val_1562_);
lean_dec_ref_known(v_a_1561_, 1);
v_snd_1563_ = lean_ctor_get(v_val_1562_, 1);
lean_inc(v_snd_1563_);
lean_dec(v_val_1562_);
v_fst_1564_ = lean_ctor_get(v_snd_1563_, 0);
lean_inc(v_fst_1564_);
v_snd_1565_ = lean_ctor_get(v_snd_1563_, 1);
lean_inc(v_snd_1565_);
lean_dec(v_snd_1563_);
lean_inc(v_a_1538_);
lean_inc_ref(v_a_1537_);
lean_inc(v_a_1536_);
lean_inc_ref(v_a_1535_);
v___x_1566_ = lean_whnf(v_fst_1564_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v_a_1567_; lean_object* v___x_1568_; 
v_a_1567_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_a_1567_);
lean_dec_ref_known(v___x_1566_, 1);
lean_inc(v_a_1538_);
lean_inc_ref(v_a_1537_);
lean_inc(v_a_1536_);
lean_inc_ref(v_a_1535_);
v___x_1568_ = lean_whnf(v_snd_1565_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; uint8_t v___y_1571_; uint8_t v___x_1577_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_a_1569_);
lean_dec_ref_known(v___x_1568_, 1);
v___x_1577_ = l_Lean_Expr_isRawNatLit(v_a_1567_);
lean_dec(v_a_1567_);
if (v___x_1577_ == 0)
{
lean_dec(v_a_1569_);
v___y_1571_ = v___x_1556_;
goto v___jp_1570_;
}
else
{
uint8_t v___x_1578_; 
v___x_1578_ = l_Lean_Expr_isRawNatLit(v_a_1569_);
lean_dec(v_a_1569_);
v___y_1571_ = v___x_1578_;
goto v___jp_1570_;
}
v___jp_1570_:
{
if (v___y_1571_ == 0)
{
lean_object* v___x_1572_; 
v___x_1572_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(v___f_1557_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_dec(v___x_1551_);
lean_dec(v_tail_1548_);
lean_dec(v_forbidden_1534_);
lean_dec(v_newNames_1533_);
lean_dec(v_mvarId_1532_);
return v___x_1572_;
}
else
{
lean_object* v_a_1573_; uint8_t v___x_1574_; 
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
v___x_1574_ = l_Lean_Exception_isInterrupt(v_a_1573_);
if (v___x_1574_ == 0)
{
uint8_t v___x_1575_; 
lean_inc(v_a_1573_);
v___x_1575_ = l_Lean_Exception_isRuntime(v_a_1573_);
v___y_1553_ = v___x_1572_;
v___y_1554_ = v___x_1575_;
goto v___jp_1552_;
}
else
{
v___y_1553_ = v___x_1572_;
v___y_1554_ = v___x_1574_;
goto v___jp_1552_;
}
}
}
else
{
lean_dec_ref(v___f_1557_);
v_depth_1530_ = v___x_1551_;
v_fvarIds_1531_ = v_tail_1548_;
goto _start;
}
}
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
lean_dec(v_a_1567_);
lean_dec_ref(v___f_1557_);
lean_dec(v___x_1551_);
lean_dec(v_tail_1548_);
lean_dec(v_forbidden_1534_);
lean_dec(v_newNames_1533_);
lean_dec(v_mvarId_1532_);
v_a_1579_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1581_ = v___x_1568_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1568_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
if (v_isShared_1582_ == 0)
{
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_a_1579_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
else
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
lean_dec(v_snd_1565_);
lean_dec_ref(v___f_1557_);
lean_dec(v___x_1551_);
lean_dec(v_tail_1548_);
lean_dec(v_forbidden_1534_);
lean_dec(v_newNames_1533_);
lean_dec(v_mvarId_1532_);
v_a_1587_ = lean_ctor_get(v___x_1566_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1566_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1566_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1587_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
else
{
lean_dec(v_a_1561_);
lean_dec_ref(v___f_1557_);
v_depth_1530_ = v___x_1551_;
v_fvarIds_1531_ = v_tail_1548_;
goto _start;
}
}
else
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
lean_dec_ref(v___f_1557_);
lean_dec(v___x_1551_);
lean_dec(v_tail_1548_);
lean_dec(v_forbidden_1534_);
lean_dec(v_newNames_1533_);
lean_dec(v_mvarId_1532_);
v_a_1596_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1560_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1560_);
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
lean_dec_ref(v___f_1557_);
lean_dec(v___x_1551_);
lean_dec(v_tail_1548_);
lean_dec(v_forbidden_1534_);
lean_dec(v_newNames_1533_);
lean_dec(v_mvarId_1532_);
v_a_1604_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v___x_1558_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1558_);
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
lean_dec(v_n_1550_);
lean_dec(v_head_1547_);
v_depth_1530_ = v___x_1551_;
v_fvarIds_1531_ = v_tail_1548_;
goto _start;
}
v___jp_1552_:
{
if (v___y_1554_ == 0)
{
lean_dec_ref(v___y_1553_);
v_depth_1530_ = v___x_1551_;
v_fvarIds_1531_ = v_tail_1548_;
goto _start;
}
else
{
lean_dec(v___x_1551_);
lean_dec(v_tail_1548_);
lean_dec(v_forbidden_1534_);
lean_dec(v_newNames_1533_);
lean_dec(v_mvarId_1532_);
return v___y_1553_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___boxed(lean_object* v_depth_1613_, lean_object* v_fvarIds_1614_, lean_object* v_mvarId_1615_, lean_object* v_newNames_1616_, lean_object* v_forbidden_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go(v_depth_1613_, v_fvarIds_1614_, v_mvarId_1615_, v_newNames_1616_, v_forbidden_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_);
lean_dec(v_a_1621_);
lean_dec_ref(v_a_1620_);
lean_dec(v_a_1619_);
lean_dec_ref(v_a_1618_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0(lean_object* v_mvarId_1624_, lean_object* v_head_1625_, lean_object* v_newNames_1626_, lean_object* v_tail_1627_, lean_object* v_forbidden_1628_, lean_object* v_n_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
lean_object* v___x_1635_; 
lean_inc(v_head_1625_);
v___x_1635_ = l_Lean_Meta_injection(v_mvarId_1624_, v_head_1625_, v_newNames_1626_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1652_; 
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1638_ = v___x_1635_;
v_isShared_1639_ = v_isSharedCheck_1652_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1635_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1652_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
if (lean_obj_tag(v_a_1636_) == 0)
{
lean_object* v___x_1640_; lean_object* v___x_1642_; 
lean_dec(v_n_1629_);
lean_dec(v_forbidden_1628_);
lean_dec(v_tail_1627_);
lean_dec(v_head_1625_);
v___x_1640_ = lean_box(0);
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 0, v___x_1640_);
v___x_1642_ = v___x_1638_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1640_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
else
{
lean_object* v_mvarId_1644_; lean_object* v_newEqs_1645_; lean_object* v_remainingNames_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
lean_del_object(v___x_1638_);
v_mvarId_1644_ = lean_ctor_get(v_a_1636_, 0);
lean_inc_n(v_mvarId_1644_, 2);
v_newEqs_1645_ = lean_ctor_get(v_a_1636_, 1);
lean_inc_ref(v_newEqs_1645_);
v_remainingNames_1646_ = lean_ctor_get(v_a_1636_, 2);
lean_inc(v_remainingNames_1646_);
lean_dec_ref_known(v_a_1636_, 3);
v___x_1647_ = lean_array_to_list(v_newEqs_1645_);
v___x_1648_ = l_List_appendTR___redArg(v___x_1647_, v_tail_1627_);
v___x_1649_ = l_Lean_FVarIdSet_insert(v_forbidden_1628_, v_head_1625_);
v___x_1650_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___boxed), 10, 5);
lean_closure_set(v___x_1650_, 0, v_n_1629_);
lean_closure_set(v___x_1650_, 1, v___x_1648_);
lean_closure_set(v___x_1650_, 2, v_mvarId_1644_);
lean_closure_set(v___x_1650_, 3, v_remainingNames_1646_);
lean_closure_set(v___x_1650_, 4, v___x_1649_);
v___x_1651_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg(v_mvarId_1644_, v___x_1650_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
return v___x_1651_;
}
}
}
else
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
lean_dec(v_n_1629_);
lean_dec(v_forbidden_1628_);
lean_dec(v_tail_1627_);
lean_dec(v_head_1625_);
v_a_1653_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1635_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1635_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1653_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0(lean_object* v_00_u03b2_1661_, lean_object* v_k_1662_, lean_object* v_t_1663_){
_start:
{
uint8_t v___x_1664_; 
v___x_1664_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(v_k_1662_, v_t_1663_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___boxed(lean_object* v_00_u03b2_1665_, lean_object* v_k_1666_, lean_object* v_t_1667_){
_start:
{
uint8_t v_res_1668_; lean_object* v_r_1669_; 
v_res_1668_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0(v_00_u03b2_1665_, v_k_1666_, v_t_1667_);
lean_dec(v_t_1667_);
lean_dec(v_k_1666_);
v_r_1669_ = lean_box(v_res_1668_);
return v_r_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections___lam__0(lean_object* v_maxDepth_1670_, lean_object* v_mvarId_1671_, lean_object* v_newNames_1672_, lean_object* v_forbidden_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v_lctx_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v_lctx_1679_ = lean_ctor_get(v___y_1674_, 2);
v___x_1680_ = l_Lean_LocalContext_getFVarIds(v_lctx_1679_);
v___x_1681_ = lean_array_to_list(v___x_1680_);
v___x_1682_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go(v_maxDepth_1670_, v___x_1681_, v_mvarId_1671_, v_newNames_1672_, v_forbidden_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections___lam__0___boxed(lean_object* v_maxDepth_1683_, lean_object* v_mvarId_1684_, lean_object* v_newNames_1685_, lean_object* v_forbidden_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_Lean_Meta_injections___lam__0(v_maxDepth_1683_, v_mvarId_1684_, v_newNames_1685_, v_forbidden_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections(lean_object* v_mvarId_1693_, lean_object* v_newNames_1694_, lean_object* v_maxDepth_1695_, lean_object* v_forbidden_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v___f_1702_; lean_object* v___x_1703_; 
lean_inc(v_mvarId_1693_);
v___f_1702_ = lean_alloc_closure((void*)(l_Lean_Meta_injections___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1702_, 0, v_maxDepth_1695_);
lean_closure_set(v___f_1702_, 1, v_mvarId_1693_);
lean_closure_set(v___f_1702_, 2, v_newNames_1694_);
lean_closure_set(v___f_1702_, 3, v_forbidden_1696_);
v___x_1703_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg(v_mvarId_1693_, v___f_1702_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections___boxed(lean_object* v_mvarId_1704_, lean_object* v_newNames_1705_, lean_object* v_maxDepth_1706_, lean_object* v_forbidden_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_Lean_Meta_injections(v_mvarId_1704_, v_newNames_1705_, v_maxDepth_1706_, v_forbidden_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
lean_dec(v_a_1711_);
lean_dec_ref(v_a_1710_);
lean_dec(v_a_1709_);
lean_dec_ref(v_a_1708_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1770_; uint8_t v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1770_ = ((lean_object*)(l_Lean_Meta_injectionIntro___closed__1));
v___x_1771_ = 0;
v___x_1772_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__22_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_));
v___x_1773_ = l_Lean_registerTraceClass(v___x_1770_, v___x_1771_, v___x_1772_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Injection_0__initFn_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2____boxed(lean_object* v_a_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l___private_Lean_Meta_Tactic_Injection_0__initFn_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_();
return v_res_1775_;
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
