// Lean compiler output
// Module: Lean.Meta.Tactic.Apply
// Imports: public import Lean.Meta.Tactic.Util public import Lean.PrettyPrinter import Lean.Meta.AppBuilder import Init.Omega
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_headBetaType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l_Lean_Meta_appendTag(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_setTag___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarsNoDelayed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Meta_addPPExplicitToExposeDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_mkUnfoldAxiomsNote(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofLazyM(lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaBoundedTelescope(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_List_get___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgsAux___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgsAux___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_getExpectedNumArgsAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_getExpectedNumArgsAux___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_getExpectedNumArgsAux___closed__0 = (const lean_object*)&l_Lean_Meta_getExpectedNumArgsAux___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "\nwith the goal"};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "could not unify the "};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "the term"};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__6_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8;
static const lean_string_object l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "type"};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "conclusion"};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__10_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " is"};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "The full type of "};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "apply"};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(171, 239, 198, 100, 229, 128, 136, 1)}};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "failed to assign synthesized instance"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__1_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_appendParentTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_appendParentTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_postprocessAppMVars(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_postprocessAppMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__0_value),((lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_apply_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_apply_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_MVarId_apply_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_MVarId_apply_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_applyConst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_MVarId_applyConst___closed__0 = (const lean_object*)&l_Lean_MVarId_applyConst___closed__0_value;
static lean_once_cell_t l_Lean_MVarId_applyConst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_applyConst___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_applyConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_applyConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_applyN___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Type mismatch: target is"};
static const lean_object* l_Lean_MVarId_applyN___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_applyN___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_MVarId_applyN___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_applyN___lam__0___closed__1;
static const lean_string_object l_Lean_MVarId_applyN___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "\nbut applied expression has type"};
static const lean_object* l_Lean_MVarId_applyN___lam__0___closed__2 = (const lean_object*)&l_Lean_MVarId_applyN___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_MVarId_applyN___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_applyN___lam__0___closed__3;
static const lean_string_object l_Lean_MVarId_applyN___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "\nafter applying "};
static const lean_object* l_Lean_MVarId_applyN___lam__0___closed__4 = (const lean_object*)&l_Lean_MVarId_applyN___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_MVarId_applyN___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_applyN___lam__0___closed__5;
static const lean_string_object l_Lean_MVarId_applyN___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = " arguments."};
static const lean_object* l_Lean_MVarId_applyN___lam__0___closed__6 = (const lean_object*)&l_Lean_MVarId_applyN___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_MVarId_applyN___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_applyN___lam__0___closed__7;
static const lean_string_object l_Lean_MVarId_applyN___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Applied type takes fewer than "};
static const lean_object* l_Lean_MVarId_applyN___lam__0___closed__8 = (const lean_object*)&l_Lean_MVarId_applyN___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_MVarId_applyN___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_applyN___lam__0___closed__9;
static const lean_string_object l_Lean_MVarId_applyN___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = " arguments:\n"};
static const lean_object* l_Lean_MVarId_applyN___lam__0___closed__10 = (const lean_object*)&l_Lean_MVarId_applyN___lam__0___closed__10_value;
static lean_once_cell_t l_Lean_MVarId_applyN___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_applyN___lam__0___closed__11;
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(58, 46, 244, 208, 18, 71, 77, 162)}};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_splitAndCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "splitAnd"};
static const lean_object* l_Lean_MVarId_splitAndCore___closed__0 = (const lean_object*)&l_Lean_MVarId_splitAndCore___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_splitAndCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_splitAndCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(17, 13, 24, 72, 20, 48, 2, 32)}};
static const lean_object* l_Lean_MVarId_splitAndCore___closed__1 = (const lean_object*)&l_Lean_MVarId_splitAndCore___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAnd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAnd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_exfalso___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l_Lean_MVarId_exfalso___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_exfalso___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_exfalso___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_exfalso___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l_Lean_MVarId_exfalso___lam__0___closed__1 = (const lean_object*)&l_Lean_MVarId_exfalso___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_MVarId_exfalso___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_exfalso___lam__0___closed__2;
static const lean_string_object l_Lean_MVarId_exfalso___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "elim"};
static const lean_object* l_Lean_MVarId_exfalso___lam__0___closed__3 = (const lean_object*)&l_Lean_MVarId_exfalso___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_MVarId_exfalso___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_exfalso___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_ctor_object l_Lean_MVarId_exfalso___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MVarId_exfalso___lam__0___closed__4_value_aux_0),((lean_object*)&l_Lean_MVarId_exfalso___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 114, 54, 50, 40, 156, 62, 47)}};
static const lean_object* l_Lean_MVarId_exfalso___lam__0___closed__4 = (const lean_object*)&l_Lean_MVarId_exfalso___lam__0___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_exfalso___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "exfalso"};
static const lean_object* l_Lean_MVarId_exfalso___closed__0 = (const lean_object*)&l_Lean_MVarId_exfalso___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_exfalso___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_exfalso___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 71, 194, 225, 45, 41, 69, 140)}};
static const lean_object* l_Lean_MVarId_exfalso___closed__1 = (const lean_object*)&l_Lean_MVarId_exfalso___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_nthConstructor___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "target is not an inductive datatype"};
static const lean_object* l_Lean_MVarId_nthConstructor___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_nthConstructor___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_nthConstructor___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MVarId_nthConstructor___lam__0___closed__0_value)}};
static const lean_object* l_Lean_MVarId_nthConstructor___lam__0___closed__1 = (const lean_object*)&l_Lean_MVarId_nthConstructor___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_MVarId_nthConstructor___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_nthConstructor___lam__0___closed__2;
static lean_once_cell_t l_Lean_MVarId_nthConstructor___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_nthConstructor___lam__0___closed__3;
static const lean_string_object l_Lean_MVarId_nthConstructor___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "index "};
static const lean_object* l_Lean_MVarId_nthConstructor___lam__0___closed__4 = (const lean_object*)&l_Lean_MVarId_nthConstructor___lam__0___closed__4_value;
static const lean_string_object l_Lean_MVarId_nthConstructor___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = " out of bounds, only "};
static const lean_object* l_Lean_MVarId_nthConstructor___lam__0___closed__5 = (const lean_object*)&l_Lean_MVarId_nthConstructor___lam__0___closed__5_value;
static const lean_string_object l_Lean_MVarId_nthConstructor___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " constructors"};
static const lean_object* l_Lean_MVarId_nthConstructor___lam__0___closed__6 = (const lean_object*)&l_Lean_MVarId_nthConstructor___lam__0___closed__6_value;
static const lean_string_object l_Lean_MVarId_nthConstructor___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = " tactic works for inductive types with exactly "};
static const lean_object* l_Lean_MVarId_nthConstructor___lam__0___closed__7 = (const lean_object*)&l_Lean_MVarId_nthConstructor___lam__0___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_iffOfEq___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l_Lean_MVarId_iffOfEq___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_iffOfEq___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_MVarId_iffOfEq___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_iffOfEq___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_iffOfEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "iff_of_eq"};
static const lean_object* l_Lean_MVarId_iffOfEq___closed__0 = (const lean_object*)&l_Lean_MVarId_iffOfEq___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_iffOfEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_iffOfEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(186, 65, 13, 14, 191, 127, 32, 251)}};
static const lean_object* l_Lean_MVarId_iffOfEq___closed__1 = (const lean_object*)&l_Lean_MVarId_iffOfEq___closed__1_value;
static lean_once_cell_t l_Lean_MVarId_iffOfEq___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_iffOfEq___closed__2;
static const lean_ctor_object l_Lean_MVarId_iffOfEq___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 1, 0, 0, 0, 0)}};
static const lean_object* l_Lean_MVarId_iffOfEq___closed__3 = (const lean_object*)&l_Lean_MVarId_iffOfEq___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_propext___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "propext"};
static const lean_object* l_Lean_MVarId_propext___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_propext___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_propext___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_propext___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(53, 150, 49, 30, 125, 3, 39, 172)}};
static const lean_object* l_Lean_MVarId_propext___lam__0___closed__1 = (const lean_object*)&l_Lean_MVarId_propext___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_MVarId_propext___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_propext___lam__0___closed__2;
static const lean_string_object l_Lean_MVarId_propext___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_MVarId_propext___lam__0___closed__3 = (const lean_object*)&l_Lean_MVarId_propext___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_MVarId_propext___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_propext___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_MVarId_propext___lam__0___closed__4 = (const lean_object*)&l_Lean_MVarId_propext___lam__0___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_propext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HEq"};
static const lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_proofIrrelHeq___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0___closed__1 = (const lean_object*)&l_Lean_MVarId_proofIrrelHeq___lam__0___closed__1_value;
static const lean_string_object l_Lean_MVarId_proofIrrelHeq___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "proof_irrel_heq"};
static const lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0___closed__2 = (const lean_object*)&l_Lean_MVarId_proofIrrelHeq___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_MVarId_proofIrrelHeq___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_proofIrrelHeq___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(180, 105, 248, 247, 187, 48, 190, 226)}};
static const lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0___closed__3 = (const lean_object*)&l_Lean_MVarId_proofIrrelHeq___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_proofIrrelHeq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "proofIrrelHeq"};
static const lean_object* l_Lean_MVarId_proofIrrelHeq___closed__0 = (const lean_object*)&l_Lean_MVarId_proofIrrelHeq___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_proofIrrelHeq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_proofIrrelHeq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 31, 69, 85, 58, 186, 233, 113)}};
static const lean_object* l_Lean_MVarId_proofIrrelHeq___closed__1 = (const lean_object*)&l_Lean_MVarId_proofIrrelHeq___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_subsingletonElim___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Subsingleton"};
static const lean_object* l_Lean_MVarId_subsingletonElim___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_subsingletonElim___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_subsingletonElim___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_subsingletonElim___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(23, 130, 42, 228, 248, 162, 23, 186)}};
static const lean_ctor_object l_Lean_MVarId_subsingletonElim___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MVarId_subsingletonElim___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_MVarId_exfalso___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(79, 85, 152, 16, 239, 41, 62, 212)}};
static const lean_object* l_Lean_MVarId_subsingletonElim___lam__0___closed__1 = (const lean_object*)&l_Lean_MVarId_subsingletonElim___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_subsingletonElim___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "subsingletonElim"};
static const lean_object* l_Lean_MVarId_subsingletonElim___closed__0 = (const lean_object*)&l_Lean_MVarId_subsingletonElim___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_subsingletonElim___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_subsingletonElim___closed__0_value),LEAN_SCALAR_PTR_LITERAL(73, 225, 81, 216, 132, 143, 62, 229)}};
static const lean_object* l_Lean_MVarId_subsingletonElim___closed__1 = (const lean_object*)&l_Lean_MVarId_subsingletonElim___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg___lam__0(lean_object* v_k_1_, lean_object* v_b_2_, lean_object* v_c_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_){
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
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1_ = stack[0].m_obj;
lean_object* v_b_2_ = stack[1].m_obj;
lean_object* v_c_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v___y_7_ = stack[6].m_obj;
lean_object* v_res_10_;
v_res_10_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg___lam__0(v_k_1_, v_b_2_, v_c_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_);
stack->m_obj
 = v_res_10_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg___lam__0___boxed(lean_object* v_k_11_, lean_object* v_b_12_, lean_object* v_c_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg___lam__0(v_k_11_, v_b_12_, v_c_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_);
lean_dec(v___y_17_);
lean_dec_ref(v___y_16_);
lean_dec(v___y_15_);
lean_dec_ref(v___y_14_);
return v_res_19_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg(lean_object* v_type_20_, lean_object* v_k_21_, uint8_t v_cleanupAnnotations_22_, uint8_t v_whnfType_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v___f_29_; lean_object* v___x_30_; 
v___f_29_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg___lam__0___boxed), 8, 1);
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
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg_0interp(lean_interpreter_value* stack)
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
v_res_47_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg(v_type_20_, v_k_21_, v_cleanupAnnotations_22_, v_whnfType_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
stack->m_obj
 = v_res_47_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg___boxed(lean_object* v_type_48_, lean_object* v_k_49_, lean_object* v_cleanupAnnotations_50_, lean_object* v_whnfType_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_57_; uint8_t v_whnfType_boxed_58_; lean_object* v_res_59_; 
v_cleanupAnnotations_boxed_57_ = lean_unbox(v_cleanupAnnotations_50_);
v_whnfType_boxed_58_ = lean_unbox(v_whnfType_51_);
v_res_59_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg(v_type_48_, v_k_49_, v_cleanupAnnotations_boxed_57_, v_whnfType_boxed_58_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
return v_res_59_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0(lean_object* v_00_u03b1_60_, lean_object* v_type_61_, lean_object* v_k_62_, uint8_t v_cleanupAnnotations_63_, uint8_t v_whnfType_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg(v_type_61_, v_k_62_, v_cleanupAnnotations_63_, v_whnfType_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_);
return v___x_70_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0_0interp(lean_interpreter_value* stack)
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
v_res_71_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0(lean_box(0), v_type_61_, v_k_62_, v_cleanupAnnotations_63_, v_whnfType_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_);
stack->m_obj
 = v_res_71_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___boxed(lean_object* v_00_u03b1_72_, lean_object* v_type_73_, lean_object* v_k_74_, lean_object* v_cleanupAnnotations_75_, lean_object* v_whnfType_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_82_; uint8_t v_whnfType_boxed_83_; lean_object* v_res_84_; 
v_cleanupAnnotations_boxed_82_ = lean_unbox(v_cleanupAnnotations_75_);
v_whnfType_boxed_83_ = lean_unbox(v_whnfType_76_);
v_res_84_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0(v_00_u03b1_72_, v_type_73_, v_k_74_, v_cleanupAnnotations_boxed_82_, v_whnfType_boxed_83_, v___y_77_, v___y_78_, v___y_79_, v___y_80_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
lean_dec(v___y_78_);
lean_dec_ref(v___y_77_);
return v_res_84_;
}
}
lean_object* l_Lean_Meta_getExpectedNumArgsAux___lam__0(lean_object* v_xs_85_, lean_object* v_body_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; uint8_t v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_92_ = lean_array_get_size(v_xs_85_);
v___x_93_ = l_Lean_Expr_getAppFn(v_body_86_);
v___x_94_ = l_Lean_Expr_isMVar(v___x_93_);
lean_dec_ref(v___x_93_);
v___x_95_ = lean_box(v___x_94_);
v___x_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_96_, 0, v___x_92_);
lean_ctor_set(v___x_96_, 1, v___x_95_);
v___x_97_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
return v___x_97_;
}
}
LEAN_EXPORT void l_Lean_Meta_getExpectedNumArgsAux___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_85_ = stack[0].m_obj;
lean_object* v_body_86_ = stack[1].m_obj;
lean_object* v___y_87_ = stack[2].m_obj;
lean_object* v___y_88_ = stack[3].m_obj;
lean_object* v___y_89_ = stack[4].m_obj;
lean_object* v___y_90_ = stack[5].m_obj;
lean_object* v_res_98_;
v_res_98_ = l_Lean_Meta_getExpectedNumArgsAux___lam__0(v_xs_85_, v_body_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_);
stack->m_obj
 = v_res_98_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgsAux___lam__0___boxed(lean_object* v_xs_99_, lean_object* v_body_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Lean_Meta_getExpectedNumArgsAux___lam__0(v_xs_99_, v_body_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
lean_dec_ref(v_body_100_);
lean_dec_ref(v_xs_99_);
return v_res_106_;
}
}
lean_object* l_Lean_Meta_getExpectedNumArgsAux(lean_object* v_e_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
lean_object* v___y_115_; lean_object* v___x_132_; uint8_t v_transparency_133_; lean_object* v___f_134_; uint8_t v___x_135_; uint8_t v___x_136_; uint8_t v___x_137_; 
v___x_132_ = l_Lean_Meta_Context_config(v_a_109_);
v_transparency_133_ = lean_ctor_get_uint8(v___x_132_, 9);
lean_dec_ref(v___x_132_);
v___f_134_ = ((lean_object*)(l_Lean_Meta_getExpectedNumArgsAux___closed__0));
v___x_135_ = 0;
v___x_136_ = 1;
v___x_137_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_133_, v___x_136_);
if (v___x_137_ == 0)
{
lean_object* v_keyedConfig_138_; uint8_t v_trackZetaDelta_139_; lean_object* v_zetaDeltaSet_140_; lean_object* v_lctx_141_; lean_object* v_localInstances_142_; lean_object* v_defEqCtx_x3f_143_; lean_object* v_synthPendingDepth_144_; lean_object* v_customCanUnfoldPredicate_x3f_145_; uint8_t v_univApprox_146_; uint8_t v_inTypeClassResolution_147_; uint8_t v_cacheInferType_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v_keyedConfig_138_ = lean_ctor_get(v_a_109_, 0);
v_trackZetaDelta_139_ = lean_ctor_get_uint8(v_a_109_, sizeof(void*)*7);
v_zetaDeltaSet_140_ = lean_ctor_get(v_a_109_, 1);
v_lctx_141_ = lean_ctor_get(v_a_109_, 2);
v_localInstances_142_ = lean_ctor_get(v_a_109_, 3);
v_defEqCtx_x3f_143_ = lean_ctor_get(v_a_109_, 4);
v_synthPendingDepth_144_ = lean_ctor_get(v_a_109_, 5);
v_customCanUnfoldPredicate_x3f_145_ = lean_ctor_get(v_a_109_, 6);
v_univApprox_146_ = lean_ctor_get_uint8(v_a_109_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_147_ = lean_ctor_get_uint8(v_a_109_, sizeof(void*)*7 + 2);
v_cacheInferType_148_ = lean_ctor_get_uint8(v_a_109_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_138_);
v___x_149_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_136_, v_keyedConfig_138_);
lean_inc(v_customCanUnfoldPredicate_x3f_145_);
lean_inc(v_synthPendingDepth_144_);
lean_inc(v_defEqCtx_x3f_143_);
lean_inc_ref(v_localInstances_142_);
lean_inc_ref(v_lctx_141_);
lean_inc(v_zetaDeltaSet_140_);
v___x_150_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_150_, 0, v___x_149_);
lean_ctor_set(v___x_150_, 1, v_zetaDeltaSet_140_);
lean_ctor_set(v___x_150_, 2, v_lctx_141_);
lean_ctor_set(v___x_150_, 3, v_localInstances_142_);
lean_ctor_set(v___x_150_, 4, v_defEqCtx_x3f_143_);
lean_ctor_set(v___x_150_, 5, v_synthPendingDepth_144_);
lean_ctor_set(v___x_150_, 6, v_customCanUnfoldPredicate_x3f_145_);
lean_ctor_set_uint8(v___x_150_, sizeof(void*)*7, v_trackZetaDelta_139_);
lean_ctor_set_uint8(v___x_150_, sizeof(void*)*7 + 1, v_univApprox_146_);
lean_ctor_set_uint8(v___x_150_, sizeof(void*)*7 + 2, v_inTypeClassResolution_147_);
lean_ctor_set_uint8(v___x_150_, sizeof(void*)*7 + 3, v_cacheInferType_148_);
v___x_151_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg(v_e_108_, v___f_134_, v___x_135_, v___x_135_, v___x_150_, v_a_110_, v_a_111_, v_a_112_);
lean_dec_ref_known(v___x_150_, 7);
v___y_115_ = v___x_151_;
goto v___jp_114_;
}
else
{
lean_object* v___x_152_; 
v___x_152_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg(v_e_108_, v___f_134_, v___x_135_, v___x_135_, v_a_109_, v_a_110_, v_a_111_, v_a_112_);
v___y_115_ = v___x_152_;
goto v___jp_114_;
}
v___jp_114_:
{
if (lean_obj_tag(v___y_115_) == 0)
{
lean_object* v_a_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_123_; 
v_a_116_ = lean_ctor_get(v___y_115_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v___y_115_);
if (v_isSharedCheck_123_ == 0)
{
v___x_118_ = v___y_115_;
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_dec(v___y_115_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_121_; 
if (v_isShared_119_ == 0)
{
v___x_121_ = v___x_118_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_a_116_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
else
{
lean_object* v_a_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_131_; 
v_a_124_ = lean_ctor_get(v___y_115_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v___y_115_);
if (v_isSharedCheck_131_ == 0)
{
v___x_126_ = v___y_115_;
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_a_124_);
lean_dec(v___y_115_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_129_; 
if (v_isShared_127_ == 0)
{
v___x_129_ = v___x_126_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_a_124_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_getExpectedNumArgsAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_108_ = stack[0].m_obj;
lean_object* v_a_109_ = stack[1].m_obj;
lean_object* v_a_110_ = stack[2].m_obj;
lean_object* v_a_111_ = stack[3].m_obj;
lean_object* v_a_112_ = stack[4].m_obj;
lean_object* v_res_153_;
v_res_153_ = l_Lean_Meta_getExpectedNumArgsAux(v_e_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_);
stack->m_obj
 = v_res_153_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgsAux___boxed(lean_object* v_e_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Lean_Meta_getExpectedNumArgsAux(v_e_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_);
lean_dec(v_a_158_);
lean_dec_ref(v_a_157_);
lean_dec(v_a_156_);
lean_dec_ref(v_a_155_);
return v_res_160_;
}
}
lean_object* l_Lean_Meta_getExpectedNumArgs(lean_object* v_e_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Lean_Meta_getExpectedNumArgsAux(v_e_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_);
if (lean_obj_tag(v___x_167_) == 0)
{
lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_176_; 
v_a_168_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_176_ == 0)
{
v___x_170_ = v___x_167_;
v_isShared_171_ = v_isSharedCheck_176_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_dec(v___x_167_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_176_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v_fst_172_; lean_object* v___x_174_; 
v_fst_172_ = lean_ctor_get(v_a_168_, 0);
lean_inc(v_fst_172_);
lean_dec(v_a_168_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 0, v_fst_172_);
v___x_174_ = v___x_170_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_fst_172_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
else
{
lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_184_; 
v_a_177_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_184_ == 0)
{
v___x_179_ = v___x_167_;
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_dec(v___x_167_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_182_; 
if (v_isShared_180_ == 0)
{
v___x_182_ = v___x_179_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_a_177_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_getExpectedNumArgs_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_161_ = stack[0].m_obj;
lean_object* v_a_162_ = stack[1].m_obj;
lean_object* v_a_163_ = stack[2].m_obj;
lean_object* v_a_164_ = stack[3].m_obj;
lean_object* v_a_165_ = stack[4].m_obj;
lean_object* v_res_185_;
v_res_185_ = l_Lean_Meta_getExpectedNumArgs(v_e_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_);
stack->m_obj
 = v_res_185_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgs___boxed(lean_object* v_e_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_Meta_getExpectedNumArgs(v_e_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_);
lean_dec(v_a_190_);
lean_dec_ref(v_a_189_);
lean_dec(v_a_188_);
lean_dec_ref(v_a_187_);
return v_res_192_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__0));
v___x_195_ = l_Lean_stringToMessageData(v___x_194_);
return v___x_195_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__2));
v___x_198_ = l_Lean_stringToMessageData(v___x_197_);
return v___x_198_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__4));
v___x_201_ = l_Lean_stringToMessageData(v___x_200_);
return v___x_201_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__7));
v___x_206_ = l_Lean_MessageData_ofFormat(v___x_205_);
return v___x_206_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0(lean_object* v_config_209_, lean_object* v___y_210_, lean_object* v_targetType_211_, lean_object* v___y_212_, lean_object* v_term_x3f_213_, lean_object* v_conclusionType_x3f_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
uint8_t v_trackZetaDelta_220_; lean_object* v_zetaDeltaSet_221_; lean_object* v_lctx_222_; lean_object* v_localInstances_223_; lean_object* v_defEqCtx_x3f_224_; lean_object* v_synthPendingDepth_225_; lean_object* v_customCanUnfoldPredicate_x3f_226_; uint8_t v_univApprox_227_; uint8_t v_inTypeClassResolution_228_; uint8_t v_cacheInferType_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_289_; 
v_trackZetaDelta_220_ = lean_ctor_get_uint8(v___y_215_, sizeof(void*)*7);
v_zetaDeltaSet_221_ = lean_ctor_get(v___y_215_, 1);
v_lctx_222_ = lean_ctor_get(v___y_215_, 2);
v_localInstances_223_ = lean_ctor_get(v___y_215_, 3);
v_defEqCtx_x3f_224_ = lean_ctor_get(v___y_215_, 4);
v_synthPendingDepth_225_ = lean_ctor_get(v___y_215_, 5);
v_customCanUnfoldPredicate_x3f_226_ = lean_ctor_get(v___y_215_, 6);
v_univApprox_227_ = lean_ctor_get_uint8(v___y_215_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_228_ = lean_ctor_get_uint8(v___y_215_, sizeof(void*)*7 + 2);
v_cacheInferType_229_ = lean_ctor_get_uint8(v___y_215_, sizeof(void*)*7 + 3);
v_isSharedCheck_289_ = !lean_is_exclusive(v___y_215_);
if (v_isSharedCheck_289_ == 0)
{
lean_object* v_unused_290_; 
v_unused_290_ = lean_ctor_get(v___y_215_, 0);
lean_dec(v_unused_290_);
v___x_231_ = v___y_215_;
v_isShared_232_ = v_isSharedCheck_289_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_226_);
lean_inc(v_synthPendingDepth_225_);
lean_inc(v_defEqCtx_x3f_224_);
lean_inc(v_localInstances_223_);
lean_inc(v_lctx_222_);
lean_inc(v_zetaDeltaSet_221_);
lean_dec(v___y_215_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_289_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
uint64_t v___x_233_; lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_233_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_209_);
v___x_234_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_234_, 0, v_config_209_);
lean_ctor_set_uint64(v___x_234_, sizeof(void*)*1, v___x_233_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 0, v___x_234_);
v___x_236_ = v___x_231_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v_zetaDeltaSet_221_);
lean_ctor_set(v_reuseFailAlloc_288_, 2, v_lctx_222_);
lean_ctor_set(v_reuseFailAlloc_288_, 3, v_localInstances_223_);
lean_ctor_set(v_reuseFailAlloc_288_, 4, v_defEqCtx_x3f_224_);
lean_ctor_set(v_reuseFailAlloc_288_, 5, v_synthPendingDepth_225_);
lean_ctor_set(v_reuseFailAlloc_288_, 6, v_customCanUnfoldPredicate_x3f_226_);
lean_ctor_set_uint8(v_reuseFailAlloc_288_, sizeof(void*)*7, v_trackZetaDelta_220_);
lean_ctor_set_uint8(v_reuseFailAlloc_288_, sizeof(void*)*7 + 1, v_univApprox_227_);
lean_ctor_set_uint8(v_reuseFailAlloc_288_, sizeof(void*)*7 + 2, v_inTypeClassResolution_228_);
lean_ctor_set_uint8(v_reuseFailAlloc_288_, sizeof(void*)*7 + 3, v_cacheInferType_229_);
v___x_236_ = v_reuseFailAlloc_288_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_Meta_addPPExplicitToExposeDiff(v___y_210_, v_targetType_211_, v___x_236_, v___y_216_, v___y_217_, v___y_218_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_279_; 
v_a_238_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_279_ == 0)
{
v___x_240_ = v___x_237_;
v_isShared_241_ = v_isSharedCheck_279_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_237_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_279_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v_fst_242_; lean_object* v_snd_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_278_; 
v_fst_242_ = lean_ctor_get(v_a_238_, 0);
v_snd_243_ = lean_ctor_get(v_a_238_, 1);
v_isSharedCheck_278_ = !lean_is_exclusive(v_a_238_);
if (v_isSharedCheck_278_ == 0)
{
v___x_245_ = v_a_238_;
v_isShared_246_ = v_isSharedCheck_278_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_snd_243_);
lean_inc(v_fst_242_);
lean_dec(v_a_238_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_278_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___y_248_; lean_object* v___y_249_; lean_object* v___y_250_; lean_object* v___y_266_; 
if (lean_obj_tag(v_conclusionType_x3f_214_) == 0)
{
lean_object* v___x_276_; 
v___x_276_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__9));
v___y_266_ = v___x_276_;
goto v___jp_265_;
}
else
{
lean_object* v___x_277_; 
v___x_277_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__10));
v___y_266_ = v___x_277_;
goto v___jp_265_;
}
v___jp_247_:
{
lean_object* v___x_252_; 
if (v_isShared_246_ == 0)
{
lean_ctor_set_tag(v___x_245_, 7);
lean_ctor_set(v___x_245_, 1, v___y_250_);
lean_ctor_set(v___x_245_, 0, v___y_249_);
v___x_252_ = v___x_245_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___y_249_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v___y_250_);
v___x_252_ = v_reuseFailAlloc_264_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_262_; 
v___x_253_ = l_Lean_indentExpr(v_fst_242_);
v___x_254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_252_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
v___x_255_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1);
v___x_256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_254_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = l_Lean_indentExpr(v_snd_243_);
v___x_258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_256_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
v___x_259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
lean_ctor_set(v___x_259_, 1, v___y_212_);
v___x_260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
lean_ctor_set(v___x_260_, 1, v___y_248_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v___x_260_);
v___x_262_ = v___x_240_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_260_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
v___jp_265_:
{
lean_object* v___x_267_; 
lean_inc(v_snd_243_);
lean_inc(v_fst_242_);
v___x_267_ = l_Lean_Meta_mkUnfoldAxiomsNote(v_fst_242_, v_snd_243_, v___x_236_, v___y_216_, v___y_217_, v___y_218_);
lean_dec_ref(v___x_236_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v_a_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v_a_268_ = lean_ctor_get(v___x_267_, 0);
lean_inc(v_a_268_);
lean_dec_ref_known(v___x_267_, 1);
v___x_269_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3);
lean_inc_ref(v___y_266_);
v___x_270_ = l_Lean_stringToMessageData(v___y_266_);
v___x_271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_269_);
lean_ctor_set(v___x_271_, 1, v___x_270_);
v___x_272_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5);
v___x_273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_271_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
if (lean_obj_tag(v_term_x3f_213_) == 0)
{
lean_object* v___x_274_; 
v___x_274_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8);
v___y_248_ = v_a_268_;
v___y_249_ = v___x_273_;
v___y_250_ = v___x_274_;
goto v___jp_247_;
}
else
{
lean_object* v_val_275_; 
v_val_275_ = lean_ctor_get(v_term_x3f_213_, 0);
lean_inc(v_val_275_);
lean_dec_ref_known(v_term_x3f_213_, 1);
v___y_248_ = v_a_268_;
v___y_249_ = v___x_273_;
v___y_250_ = v_val_275_;
goto v___jp_247_;
}
}
else
{
lean_del_object(v___x_245_);
lean_dec(v_snd_243_);
lean_dec(v_fst_242_);
lean_del_object(v___x_240_);
lean_dec(v_term_x3f_213_);
lean_dec_ref(v___y_212_);
return v___x_267_;
}
}
}
}
}
else
{
lean_object* v_a_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_287_; 
lean_dec_ref(v___x_236_);
lean_dec(v_term_x3f_213_);
lean_dec_ref(v___y_212_);
v_a_280_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_287_ == 0)
{
v___x_282_ = v___x_237_;
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_a_280_);
lean_dec(v___x_237_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_285_; 
if (v_isShared_283_ == 0)
{
v___x_285_ = v___x_282_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_a_280_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_config_209_ = stack[0].m_obj;
lean_object* v___y_210_ = stack[1].m_obj;
lean_object* v_targetType_211_ = stack[2].m_obj;
lean_object* v___y_212_ = stack[3].m_obj;
lean_object* v_term_x3f_213_ = stack[4].m_obj;
lean_object* v_conclusionType_x3f_214_ = stack[5].m_obj;
lean_object* v___y_215_ = stack[6].m_obj;
lean_object* v___y_216_ = stack[7].m_obj;
lean_object* v___y_217_ = stack[8].m_obj;
lean_object* v___y_218_ = stack[9].m_obj;
lean_object* v_res_291_;
v_res_291_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0(v_config_209_, v___y_210_, v_targetType_211_, v___y_212_, v_term_x3f_213_, v_conclusionType_x3f_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_);
stack->m_obj
 = v_res_291_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___boxed(lean_object* v_config_292_, lean_object* v___y_293_, lean_object* v_targetType_294_, lean_object* v___y_295_, lean_object* v_term_x3f_296_, lean_object* v_conclusionType_x3f_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0(v_config_292_, v___y_293_, v_targetType_294_, v___y_295_, v_term_x3f_296_, v_conclusionType_x3f_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec(v_conclusionType_x3f_297_);
return v_res_303_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__0));
v___x_306_ = l_Lean_stringToMessageData(v___x_305_);
return v___x_306_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__2));
v___x_309_ = l_Lean_stringToMessageData(v___x_308_);
return v___x_309_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__4));
v___x_312_ = l_Lean_stringToMessageData(v___x_311_);
return v___x_312_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(lean_object* v_mvarId_316_, lean_object* v_eType_317_, lean_object* v_conclusionType_x3f_318_, lean_object* v_targetType_319_, lean_object* v_term_x3f_320_, uint8_t v_approx_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___y_331_; lean_object* v___y_332_; lean_object* v___y_333_; lean_object* v___y_334_; lean_object* v___y_335_; lean_object* v___y_345_; lean_object* v___y_346_; lean_object* v___y_347_; lean_object* v___y_348_; lean_object* v___y_349_; lean_object* v___y_350_; lean_object* v___y_351_; lean_object* v___y_352_; lean_object* v___y_353_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_367_; lean_object* v_config_373_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_376_; lean_object* v___y_377_; 
if (v_approx_321_ == 0)
{
lean_object* v___x_380_; 
v___x_380_ = l_Lean_Meta_Context_config(v_a_322_);
v_config_373_ = v___x_380_;
v___y_374_ = v_a_322_;
v___y_375_ = v_a_323_;
v___y_376_ = v_a_324_;
v___y_377_ = v_a_325_;
goto v___jp_372_;
}
else
{
lean_object* v___x_381_; uint8_t v_constApprox_382_; uint8_t v_isDefEqStuckEx_383_; uint8_t v_unificationHints_384_; uint8_t v_proofIrrelevance_385_; uint8_t v_assignSyntheticOpaque_386_; uint8_t v_offsetCnstrs_387_; uint8_t v_transparency_388_; uint8_t v_etaStruct_389_; uint8_t v_univApprox_390_; uint8_t v_iota_391_; uint8_t v_beta_392_; uint8_t v_proj_393_; uint8_t v_zeta_394_; uint8_t v_zetaDelta_395_; uint8_t v_zetaUnused_396_; uint8_t v_zetaHave_397_; uint8_t v_canUnfoldPredicateConfig_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_419_; 
v___x_381_ = l_Lean_Meta_Context_config(v_a_322_);
v_constApprox_382_ = lean_ctor_get_uint8(v___x_381_, 3);
v_isDefEqStuckEx_383_ = lean_ctor_get_uint8(v___x_381_, 4);
v_unificationHints_384_ = lean_ctor_get_uint8(v___x_381_, 5);
v_proofIrrelevance_385_ = lean_ctor_get_uint8(v___x_381_, 6);
v_assignSyntheticOpaque_386_ = lean_ctor_get_uint8(v___x_381_, 7);
v_offsetCnstrs_387_ = lean_ctor_get_uint8(v___x_381_, 8);
v_transparency_388_ = lean_ctor_get_uint8(v___x_381_, 9);
v_etaStruct_389_ = lean_ctor_get_uint8(v___x_381_, 10);
v_univApprox_390_ = lean_ctor_get_uint8(v___x_381_, 11);
v_iota_391_ = lean_ctor_get_uint8(v___x_381_, 12);
v_beta_392_ = lean_ctor_get_uint8(v___x_381_, 13);
v_proj_393_ = lean_ctor_get_uint8(v___x_381_, 14);
v_zeta_394_ = lean_ctor_get_uint8(v___x_381_, 15);
v_zetaDelta_395_ = lean_ctor_get_uint8(v___x_381_, 16);
v_zetaUnused_396_ = lean_ctor_get_uint8(v___x_381_, 17);
v_zetaHave_397_ = lean_ctor_get_uint8(v___x_381_, 18);
v_canUnfoldPredicateConfig_398_ = lean_ctor_get_uint8(v___x_381_, 19);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_419_ == 0)
{
v___x_400_ = v___x_381_;
v_isShared_401_ = v_isSharedCheck_419_;
goto v_resetjp_399_;
}
else
{
lean_dec(v___x_381_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_419_;
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
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_418_, 3, v_constApprox_382_);
lean_ctor_set_uint8(v_reuseFailAlloc_418_, 4, v_isDefEqStuckEx_383_);
lean_ctor_set_uint8(v_reuseFailAlloc_418_, 5, v_unificationHints_384_);
lean_ctor_set_uint8(v_reuseFailAlloc_418_, 6, v_proofIrrelevance_385_);
lean_ctor_set_uint8(v_reuseFailAlloc_418_, 7, v_assignSyntheticOpaque_386_);
lean_ctor_set_uint8(v_reuseFailAlloc_418_, 8, v_offsetCnstrs_387_);
lean_ctor_set_uint8(v_reuseFailAlloc_418_, 9, v_transparency_388_);
lean_ctor_set_uint8(v_reuseFailAlloc_418_, 10, v_etaStruct_389_);
lean_ctor_set_uint8(v_reuseFailAlloc_418_, 11, v_univApprox_390_);
lean_ctor_set_uint8(v_reuseFailAlloc_418_, 12, v_iota_391_);
lean_ctor_set_uint8(v_reuseFailAlloc_418_, 13, v_beta_392_);
lean_ctor_set_uint8(v_reuseFailAlloc_418_, 14, v_proj_393_);
lean_ctor_set_uint8(v_reuseFailAlloc_418_, 15, v_zeta_394_);
lean_ctor_set_uint8(v_reuseFailAlloc_418_, 16, v_zetaDelta_395_);
lean_ctor_set_uint8(v_reuseFailAlloc_418_, 17, v_zetaUnused_396_);
lean_ctor_set_uint8(v_reuseFailAlloc_418_, 18, v_zetaHave_397_);
lean_ctor_set_uint8(v_reuseFailAlloc_418_, 19, v_canUnfoldPredicateConfig_398_);
v___x_403_ = v_reuseFailAlloc_418_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
uint8_t v_trackZetaDelta_404_; lean_object* v_zetaDeltaSet_405_; lean_object* v_lctx_406_; lean_object* v_localInstances_407_; lean_object* v_defEqCtx_x3f_408_; lean_object* v_synthPendingDepth_409_; lean_object* v_customCanUnfoldPredicate_x3f_410_; uint8_t v_univApprox_411_; uint8_t v_inTypeClassResolution_412_; uint8_t v_cacheInferType_413_; uint64_t v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
lean_ctor_set_uint8(v___x_403_, 0, v_approx_321_);
lean_ctor_set_uint8(v___x_403_, 1, v_approx_321_);
lean_ctor_set_uint8(v___x_403_, 2, v_approx_321_);
v_trackZetaDelta_404_ = lean_ctor_get_uint8(v_a_322_, sizeof(void*)*7);
v_zetaDeltaSet_405_ = lean_ctor_get(v_a_322_, 1);
v_lctx_406_ = lean_ctor_get(v_a_322_, 2);
v_localInstances_407_ = lean_ctor_get(v_a_322_, 3);
v_defEqCtx_x3f_408_ = lean_ctor_get(v_a_322_, 4);
v_synthPendingDepth_409_ = lean_ctor_get(v_a_322_, 5);
v_customCanUnfoldPredicate_x3f_410_ = lean_ctor_get(v_a_322_, 6);
v_univApprox_411_ = lean_ctor_get_uint8(v_a_322_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_412_ = lean_ctor_get_uint8(v_a_322_, sizeof(void*)*7 + 2);
v_cacheInferType_413_ = lean_ctor_get_uint8(v_a_322_, sizeof(void*)*7 + 3);
v___x_414_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_403_);
v___x_415_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_415_, 0, v___x_403_);
lean_ctor_set_uint64(v___x_415_, sizeof(void*)*1, v___x_414_);
lean_inc(v_customCanUnfoldPredicate_x3f_410_);
lean_inc(v_synthPendingDepth_409_);
lean_inc(v_defEqCtx_x3f_408_);
lean_inc_ref(v_localInstances_407_);
lean_inc_ref(v_lctx_406_);
lean_inc(v_zetaDeltaSet_405_);
v___x_416_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_416_, 0, v___x_415_);
lean_ctor_set(v___x_416_, 1, v_zetaDeltaSet_405_);
lean_ctor_set(v___x_416_, 2, v_lctx_406_);
lean_ctor_set(v___x_416_, 3, v_localInstances_407_);
lean_ctor_set(v___x_416_, 4, v_defEqCtx_x3f_408_);
lean_ctor_set(v___x_416_, 5, v_synthPendingDepth_409_);
lean_ctor_set(v___x_416_, 6, v_customCanUnfoldPredicate_x3f_410_);
lean_ctor_set_uint8(v___x_416_, sizeof(void*)*7, v_trackZetaDelta_404_);
lean_ctor_set_uint8(v___x_416_, sizeof(void*)*7 + 1, v_univApprox_411_);
lean_ctor_set_uint8(v___x_416_, sizeof(void*)*7 + 2, v_inTypeClassResolution_412_);
lean_ctor_set_uint8(v___x_416_, sizeof(void*)*7 + 3, v_cacheInferType_413_);
v___x_417_ = l_Lean_Meta_Context_config(v___x_416_);
lean_dec_ref_known(v___x_416_, 7);
v_config_373_ = v___x_417_;
v___y_374_ = v_a_322_;
v___y_375_ = v_a_323_;
v___y_376_ = v_a_324_;
v___y_377_ = v_a_325_;
goto v___jp_372_;
}
}
}
v___jp_327_:
{
lean_object* v___f_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
lean_inc_ref(v_targetType_319_);
v___f_336_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_336_, 0, v___y_328_);
lean_closure_set(v___f_336_, 1, v___y_329_);
lean_closure_set(v___f_336_, 2, v_targetType_319_);
lean_closure_set(v___f_336_, 3, v___y_335_);
lean_closure_set(v___f_336_, 4, v_term_x3f_320_);
lean_closure_set(v___f_336_, 5, v_conclusionType_x3f_318_);
v___x_337_ = lean_unsigned_to_nat(2u);
v___x_338_ = lean_mk_empty_array_with_capacity(v___x_337_);
v___x_339_ = lean_array_push(v___x_338_, v_eType_317_);
v___x_340_ = lean_array_push(v___x_339_, v_targetType_319_);
v___x_341_ = l_Lean_MessageData_ofLazyM(v___f_336_, v___x_340_);
v___x_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_inc(v___y_330_);
v___x_343_ = l_Lean_Meta_throwTacticEx___redArg(v___y_330_, v_mvarId_316_, v___x_342_, v___y_334_, v___y_333_, v___y_332_, v___y_331_);
return v___x_343_;
}
v___jp_344_:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
lean_inc_ref(v___y_348_);
v___x_354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_354_, 0, v___y_348_);
lean_ctor_set(v___x_354_, 1, v___y_353_);
v___x_355_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1);
v___x_356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_354_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
lean_inc_ref(v_eType_317_);
v___x_357_ = l_Lean_indentExpr(v_eType_317_);
v___x_358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_356_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
v___x_359_ = l_Lean_MessageData_note(v___x_358_);
v___y_328_ = v___y_345_;
v___y_329_ = v___y_346_;
v___y_330_ = v___y_347_;
v___y_331_ = v___y_349_;
v___y_332_ = v___y_350_;
v___y_333_ = v___y_351_;
v___y_334_ = v___y_352_;
v___y_335_ = v___x_359_;
goto v___jp_327_;
}
v___jp_360_:
{
if (lean_obj_tag(v_conclusionType_x3f_318_) == 0)
{
lean_object* v___x_368_; 
v___x_368_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3);
v___y_328_ = v___y_361_;
v___y_329_ = v___y_367_;
v___y_330_ = v___y_366_;
v___y_331_ = v___y_362_;
v___y_332_ = v___y_363_;
v___y_333_ = v___y_364_;
v___y_334_ = v___y_365_;
v___y_335_ = v___x_368_;
goto v___jp_327_;
}
else
{
lean_object* v___x_369_; 
v___x_369_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5);
if (lean_obj_tag(v_term_x3f_320_) == 0)
{
lean_object* v___x_370_; 
v___x_370_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8);
v___y_345_ = v___y_361_;
v___y_346_ = v___y_367_;
v___y_347_ = v___y_366_;
v___y_348_ = v___x_369_;
v___y_349_ = v___y_362_;
v___y_350_ = v___y_363_;
v___y_351_ = v___y_364_;
v___y_352_ = v___y_365_;
v___y_353_ = v___x_370_;
goto v___jp_344_;
}
else
{
lean_object* v_val_371_; 
v_val_371_ = lean_ctor_get(v_term_x3f_320_, 0);
lean_inc(v_val_371_);
v___y_345_ = v___y_361_;
v___y_346_ = v___y_367_;
v___y_347_ = v___y_366_;
v___y_348_ = v___x_369_;
v___y_349_ = v___y_362_;
v___y_350_ = v___y_363_;
v___y_351_ = v___y_364_;
v___y_352_ = v___y_365_;
v___y_353_ = v_val_371_;
goto v___jp_344_;
}
}
}
v___jp_372_:
{
lean_object* v___x_378_; 
v___x_378_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7));
if (lean_obj_tag(v_conclusionType_x3f_318_) == 0)
{
lean_inc_ref(v_eType_317_);
v___y_361_ = v_config_373_;
v___y_362_ = v___y_377_;
v___y_363_ = v___y_376_;
v___y_364_ = v___y_375_;
v___y_365_ = v___y_374_;
v___y_366_ = v___x_378_;
v___y_367_ = v_eType_317_;
goto v___jp_360_;
}
else
{
lean_object* v_val_379_; 
v_val_379_ = lean_ctor_get(v_conclusionType_x3f_318_, 0);
lean_inc(v_val_379_);
v___y_361_ = v_config_373_;
v___y_362_ = v___y_377_;
v___y_363_ = v___y_376_;
v___y_364_ = v___y_375_;
v___y_365_ = v___y_374_;
v___y_366_ = v___x_378_;
v___y_367_ = v_val_379_;
goto v___jp_360_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_316_ = stack[0].m_obj;
lean_object* v_eType_317_ = stack[1].m_obj;
lean_object* v_conclusionType_x3f_318_ = stack[2].m_obj;
lean_object* v_targetType_319_ = stack[3].m_obj;
lean_object* v_term_x3f_320_ = stack[4].m_obj;
uint8_t v_approx_321_ = stack[5].m_num;
lean_object* v_a_322_ = stack[6].m_obj;
lean_object* v_a_323_ = stack[7].m_obj;
lean_object* v_a_324_ = stack[8].m_obj;
lean_object* v_a_325_ = stack[9].m_obj;
lean_object* v_res_420_;
v_res_420_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_316_, v_eType_317_, v_conclusionType_x3f_318_, v_targetType_319_, v_term_x3f_320_, v_approx_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
stack->m_obj
 = v_res_420_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___boxed(lean_object* v_mvarId_421_, lean_object* v_eType_422_, lean_object* v_conclusionType_x3f_423_, lean_object* v_targetType_424_, lean_object* v_term_x3f_425_, lean_object* v_approx_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_){
_start:
{
uint8_t v_approx_boxed_432_; lean_object* v_res_433_; 
v_approx_boxed_432_ = lean_unbox(v_approx_426_);
v_res_433_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_421_, v_eType_422_, v_conclusionType_x3f_423_, v_targetType_424_, v_term_x3f_425_, v_approx_boxed_432_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
lean_dec(v_a_430_);
lean_dec_ref(v_a_429_);
lean_dec(v_a_428_);
lean_dec_ref(v_a_427_);
return v_res_433_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError(lean_object* v_00_u03b1_434_, lean_object* v_mvarId_435_, lean_object* v_eType_436_, lean_object* v_conclusionType_x3f_437_, lean_object* v_targetType_438_, lean_object* v_term_x3f_439_, uint8_t v_approx_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_435_, v_eType_436_, v_conclusionType_x3f_437_, v_targetType_438_, v_term_x3f_439_, v_approx_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_);
return v___x_446_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_435_ = stack[1].m_obj;
lean_object* v_eType_436_ = stack[2].m_obj;
lean_object* v_conclusionType_x3f_437_ = stack[3].m_obj;
lean_object* v_targetType_438_ = stack[4].m_obj;
lean_object* v_term_x3f_439_ = stack[5].m_obj;
uint8_t v_approx_440_ = stack[6].m_num;
lean_object* v_a_441_ = stack[7].m_obj;
lean_object* v_a_442_ = stack[8].m_obj;
lean_object* v_a_443_ = stack[9].m_obj;
lean_object* v_a_444_ = stack[10].m_obj;
lean_object* v_res_447_;
v_res_447_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError(lean_box(0), v_mvarId_435_, v_eType_436_, v_conclusionType_x3f_437_, v_targetType_438_, v_term_x3f_439_, v_approx_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_);
stack->m_obj
 = v_res_447_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___boxed(lean_object* v_00_u03b1_448_, lean_object* v_mvarId_449_, lean_object* v_eType_450_, lean_object* v_conclusionType_x3f_451_, lean_object* v_targetType_452_, lean_object* v_term_x3f_453_, lean_object* v_approx_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_){
_start:
{
uint8_t v_approx_boxed_460_; lean_object* v_res_461_; 
v_approx_boxed_460_ = lean_unbox(v_approx_454_);
v_res_461_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError(v_00_u03b1_448_, v_mvarId_449_, v_eType_450_, v_conclusionType_x3f_451_, v_targetType_452_, v_term_x3f_453_, v_approx_boxed_460_, v_a_455_, v_a_456_, v_a_457_, v_a_458_);
lean_dec(v_a_458_);
lean_dec_ref(v_a_457_);
lean_dec(v_a_456_);
lean_dec_ref(v_a_455_);
return v_res_461_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(lean_object* v_a_462_, lean_object* v_snd_463_, lean_object* v_fst_464_, lean_object* v_____r_465_, uint8_t v_progressAfterEx_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_472_, 0, v_a_462_);
v___x_473_ = lean_box(v_progressAfterEx_466_);
v___x_474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
lean_ctor_set(v___x_474_, 1, v_snd_463_);
v___x_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_475_, 0, v_fst_464_);
lean_ctor_set(v___x_475_, 1, v___x_474_);
v___x_476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_476_, 0, v___x_472_);
lean_ctor_set(v___x_476_, 1, v___x_475_);
v___x_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
return v___x_477_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_462_ = stack[0].m_obj;
lean_object* v_snd_463_ = stack[1].m_obj;
lean_object* v_fst_464_ = stack[2].m_obj;
lean_object* v_____r_465_ = stack[3].m_obj;
uint8_t v_progressAfterEx_466_ = stack[4].m_num;
lean_object* v___y_467_ = stack[5].m_obj;
lean_object* v___y_468_ = stack[6].m_obj;
lean_object* v___y_469_ = stack[7].m_obj;
lean_object* v___y_470_ = stack[8].m_obj;
lean_object* v_res_478_;
v_res_478_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(v_a_462_, v_snd_463_, v_fst_464_, v_____r_465_, v_progressAfterEx_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
stack->m_obj
 = v_res_478_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0___boxed(lean_object* v_a_479_, lean_object* v_snd_480_, lean_object* v_fst_481_, lean_object* v_____r_482_, lean_object* v_progressAfterEx_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
uint8_t v_progressAfterEx_boxed_489_; lean_object* v_res_490_; 
v_progressAfterEx_boxed_489_ = lean_unbox(v_progressAfterEx_483_);
v_res_490_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(v_a_479_, v_snd_480_, v_fst_481_, v_____r_482_, v_progressAfterEx_boxed_489_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
return v_res_490_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__1));
v___x_495_ = l_Lean_MessageData_ofFormat(v___x_494_);
return v___x_495_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2);
v___x_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
return v___x_497_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0(uint8_t v_allowSynthFailures_498_, lean_object* v_tacticName_499_, lean_object* v_mvarId_500_, lean_object* v_as_501_, size_t v_sz_502_, size_t v_i_503_, lean_object* v_b_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v_a_511_; lean_object* v_fst_516_; lean_object* v_fst_517_; lean_object* v_snd_518_; uint8_t v___x_521_; 
v___x_521_ = lean_usize_dec_lt(v_i_503_, v_sz_502_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; 
lean_dec(v_mvarId_500_);
lean_dec(v_tacticName_499_);
v___x_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_522_, 0, v_b_504_);
return v___x_522_;
}
else
{
lean_object* v_snd_523_; lean_object* v_fst_524_; lean_object* v_fst_525_; lean_object* v_snd_526_; lean_object* v_a_527_; lean_object* v___y_529_; uint8_t v___y_530_; lean_object* v_a_535_; lean_object* v___y_539_; lean_object* v___x_600_; 
v_snd_523_ = lean_ctor_get(v_b_504_, 1);
lean_inc(v_snd_523_);
v_fst_524_ = lean_ctor_get(v_b_504_, 0);
lean_inc(v_fst_524_);
lean_dec_ref(v_b_504_);
v_fst_525_ = lean_ctor_get(v_snd_523_, 0);
lean_inc(v_fst_525_);
v_snd_526_ = lean_ctor_get(v_snd_523_, 1);
lean_inc(v_snd_526_);
lean_dec(v_snd_523_);
v_a_527_ = lean_array_uget_borrowed(v_as_501_, v_i_503_);
lean_inc(v___y_508_);
lean_inc_ref(v___y_507_);
lean_inc(v___y_506_);
lean_inc_ref(v___y_505_);
lean_inc(v_a_527_);
v___x_600_ = lean_infer_type(v_a_527_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_a_601_);
lean_dec_ref_known(v___x_600_, 1);
v___x_602_ = lean_box(0);
v___x_603_ = l_Lean_Meta_synthInstance(v_a_601_, v___x_602_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
if (lean_obj_tag(v___x_603_) == 0)
{
lean_object* v_a_604_; lean_object* v___x_605_; lean_object* v___x_606_; uint8_t v___x_607_; 
v_a_604_ = lean_ctor_get(v___x_603_, 0);
lean_inc(v_a_604_);
lean_dec_ref_known(v___x_603_, 1);
v___x_605_ = lean_array_get_size(v_snd_526_);
v___x_606_ = lean_unsigned_to_nat(0u);
v___x_607_ = lean_nat_dec_eq(v___x_605_, v___x_606_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_box(0);
lean_inc(v_snd_526_);
v___x_609_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(v_a_604_, v_snd_526_, v_fst_524_, v___x_608_, v___x_521_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
v___y_539_ = v___x_609_;
goto v___jp_538_;
}
else
{
lean_object* v___x_610_; uint8_t v___x_611_; lean_object* v___x_612_; 
v___x_610_ = lean_box(0);
v___x_611_ = lean_unbox(v_fst_525_);
lean_inc(v_snd_526_);
v___x_612_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(v_a_604_, v_snd_526_, v_fst_524_, v___x_610_, v___x_611_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
v___y_539_ = v___x_612_;
goto v___jp_538_;
}
}
else
{
lean_object* v_a_613_; 
lean_dec(v_fst_524_);
v_a_613_ = lean_ctor_get(v___x_603_, 0);
lean_inc(v_a_613_);
lean_dec_ref_known(v___x_603_, 1);
v_a_535_ = v_a_613_;
goto v___jp_534_;
}
}
else
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_621_; 
lean_dec(v_snd_526_);
lean_dec(v_fst_525_);
lean_dec(v_fst_524_);
lean_dec(v_mvarId_500_);
lean_dec(v_tacticName_499_);
v_a_614_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_621_ == 0)
{
v___x_616_ = v___x_600_;
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_600_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
if (v_isShared_617_ == 0)
{
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_a_614_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
v___jp_528_:
{
if (v___y_530_ == 0)
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_531_, 0, v___y_529_);
lean_inc(v_a_527_);
v___x_532_ = lean_array_push(v_snd_526_, v_a_527_);
v_fst_516_ = v___x_531_;
v_fst_517_ = v_fst_525_;
v_snd_518_ = v___x_532_;
goto v___jp_515_;
}
else
{
lean_object* v___x_533_; 
lean_dec(v_snd_526_);
lean_dec(v_fst_525_);
lean_dec(v_mvarId_500_);
lean_dec(v_tacticName_499_);
v___x_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_533_, 0, v___y_529_);
return v___x_533_;
}
}
v___jp_534_:
{
uint8_t v___x_536_; 
v___x_536_ = l_Lean_Exception_isInterrupt(v_a_535_);
if (v___x_536_ == 0)
{
uint8_t v___x_537_; 
lean_inc_ref(v_a_535_);
v___x_537_ = l_Lean_Exception_isRuntime(v_a_535_);
v___y_529_ = v_a_535_;
v___y_530_ = v___x_537_;
goto v___jp_528_;
}
else
{
v___y_529_ = v_a_535_;
v___y_530_ = v___x_536_;
goto v___jp_528_;
}
}
v___jp_538_:
{
if (lean_obj_tag(v___y_539_) == 0)
{
lean_object* v_a_540_; lean_object* v_snd_541_; lean_object* v_snd_542_; lean_object* v_fst_543_; 
lean_dec(v_snd_526_);
lean_dec(v_fst_525_);
v_a_540_ = lean_ctor_get(v___y_539_, 0);
lean_inc(v_a_540_);
lean_dec_ref_known(v___y_539_, 1);
v_snd_541_ = lean_ctor_get(v_a_540_, 1);
lean_inc(v_snd_541_);
v_snd_542_ = lean_ctor_get(v_snd_541_, 1);
lean_inc(v_snd_542_);
v_fst_543_ = lean_ctor_get(v_a_540_, 0);
lean_inc(v_fst_543_);
lean_dec(v_a_540_);
if (lean_obj_tag(v_fst_543_) == 1)
{
lean_object* v_fst_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_594_; 
v_fst_544_ = lean_ctor_get(v_snd_541_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v_snd_541_);
if (v_isSharedCheck_594_ == 0)
{
lean_object* v_unused_595_; 
v_unused_595_ = lean_ctor_get(v_snd_541_, 1);
lean_dec(v_unused_595_);
v___x_546_ = v_snd_541_;
v_isShared_547_ = v_isSharedCheck_594_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_fst_544_);
lean_dec(v_snd_541_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_594_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v_fst_548_; lean_object* v_snd_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_593_; 
v_fst_548_ = lean_ctor_get(v_snd_542_, 0);
v_snd_549_ = lean_ctor_get(v_snd_542_, 1);
v_isSharedCheck_593_ = !lean_is_exclusive(v_snd_542_);
if (v_isSharedCheck_593_ == 0)
{
v___x_551_ = v_snd_542_;
v_isShared_552_ = v_isSharedCheck_593_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_snd_549_);
lean_inc(v_fst_548_);
lean_dec(v_snd_542_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_593_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v_val_553_; lean_object* v___x_554_; 
v_val_553_ = lean_ctor_get(v_fst_543_, 0);
lean_inc(v_val_553_);
lean_dec_ref_known(v_fst_543_, 1);
lean_inc(v_a_527_);
v___x_554_ = l_Lean_Meta_isExprDefEq(v_a_527_, v_val_553_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; uint8_t v___x_556_; 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
lean_inc(v_a_555_);
lean_dec_ref_known(v___x_554_, 1);
v___x_556_ = lean_unbox(v_a_555_);
lean_dec(v_a_555_);
if (v___x_556_ == 0)
{
if (v_allowSynthFailures_498_ == 0)
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3);
lean_inc(v_mvarId_500_);
lean_inc(v_tacticName_499_);
v___x_558_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_499_, v_mvarId_500_, v___x_557_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v___x_560_; 
lean_dec_ref_known(v___x_558_, 1);
if (v_isShared_552_ == 0)
{
v___x_560_ = v___x_551_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_fst_548_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_snd_549_);
v___x_560_ = v_reuseFailAlloc_564_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
lean_object* v___x_562_; 
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 1, v___x_560_);
v___x_562_ = v___x_546_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_fst_544_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v___x_560_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
v_a_511_ = v___x_562_;
goto v___jp_510_;
}
}
}
else
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
lean_del_object(v___x_551_);
lean_dec(v_snd_549_);
lean_dec(v_fst_548_);
lean_del_object(v___x_546_);
lean_dec(v_fst_544_);
lean_dec(v_mvarId_500_);
lean_dec(v_tacticName_499_);
v_a_565_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v___x_558_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_558_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_a_565_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
else
{
lean_object* v___x_574_; 
if (v_isShared_552_ == 0)
{
v___x_574_ = v___x_551_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_fst_548_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v_snd_549_);
v___x_574_ = v_reuseFailAlloc_578_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_576_; 
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 1, v___x_574_);
v___x_576_ = v___x_546_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_fst_544_);
lean_ctor_set(v_reuseFailAlloc_577_, 1, v___x_574_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
v_a_511_ = v___x_576_;
goto v___jp_510_;
}
}
}
}
else
{
lean_object* v___x_580_; 
if (v_isShared_552_ == 0)
{
v___x_580_ = v___x_551_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_fst_548_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v_snd_549_);
v___x_580_ = v_reuseFailAlloc_584_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
lean_object* v___x_582_; 
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 1, v___x_580_);
v___x_582_ = v___x_546_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_fst_544_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v___x_580_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
v_a_511_ = v___x_582_;
goto v___jp_510_;
}
}
}
}
else
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_592_; 
lean_del_object(v___x_551_);
lean_dec(v_snd_549_);
lean_dec(v_fst_548_);
lean_del_object(v___x_546_);
lean_dec(v_fst_544_);
lean_dec(v_mvarId_500_);
lean_dec(v_tacticName_499_);
v_a_585_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_592_ == 0)
{
v___x_587_ = v___x_554_;
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_554_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_588_ == 0)
{
v___x_590_ = v___x_587_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_585_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
}
}
else
{
lean_object* v_fst_596_; lean_object* v_fst_597_; lean_object* v_snd_598_; 
lean_dec(v_fst_543_);
v_fst_596_ = lean_ctor_get(v_snd_541_, 0);
lean_inc(v_fst_596_);
lean_dec(v_snd_541_);
v_fst_597_ = lean_ctor_get(v_snd_542_, 0);
lean_inc(v_fst_597_);
v_snd_598_ = lean_ctor_get(v_snd_542_, 1);
lean_inc(v_snd_598_);
lean_dec(v_snd_542_);
v_fst_516_ = v_fst_596_;
v_fst_517_ = v_fst_597_;
v_snd_518_ = v_snd_598_;
goto v___jp_515_;
}
}
else
{
lean_object* v_a_599_; 
v_a_599_ = lean_ctor_get(v___y_539_, 0);
lean_inc(v_a_599_);
lean_dec_ref_known(v___y_539_, 1);
v_a_535_ = v_a_599_;
goto v___jp_534_;
}
}
}
v___jp_510_:
{
size_t v___x_512_; size_t v___x_513_; 
v___x_512_ = ((size_t)1ULL);
v___x_513_ = lean_usize_add(v_i_503_, v___x_512_);
v_i_503_ = v___x_513_;
v_b_504_ = v_a_511_;
goto _start;
}
v___jp_515_:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_519_, 0, v_fst_517_);
lean_ctor_set(v___x_519_, 1, v_snd_518_);
v___x_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_520_, 0, v_fst_516_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v_a_511_ = v___x_520_;
goto v___jp_510_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_allowSynthFailures_498_ = stack[0].m_num;
lean_object* v_tacticName_499_ = stack[1].m_obj;
lean_object* v_mvarId_500_ = stack[2].m_obj;
lean_object* v_as_501_ = stack[3].m_obj;
size_t v_sz_502_ = stack[4].m_num;
size_t v_i_503_ = stack[5].m_num;
lean_object* v_b_504_ = stack[6].m_obj;
lean_object* v___y_505_ = stack[7].m_obj;
lean_object* v___y_506_ = stack[8].m_obj;
lean_object* v___y_507_ = stack[9].m_obj;
lean_object* v___y_508_ = stack[10].m_obj;
lean_object* v_res_622_;
v_res_622_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0(v_allowSynthFailures_498_, v_tacticName_499_, v_mvarId_500_, v_as_501_, v_sz_502_, v_i_503_, v_b_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
stack->m_obj
 = v_res_622_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___boxed(lean_object* v_allowSynthFailures_623_, lean_object* v_tacticName_624_, lean_object* v_mvarId_625_, lean_object* v_as_626_, lean_object* v_sz_627_, lean_object* v_i_628_, lean_object* v_b_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
uint8_t v_allowSynthFailures_boxed_635_; size_t v_sz_boxed_636_; size_t v_i_boxed_637_; lean_object* v_res_638_; 
v_allowSynthFailures_boxed_635_ = lean_unbox(v_allowSynthFailures_623_);
v_sz_boxed_636_ = lean_unbox_usize(v_sz_627_);
lean_dec(v_sz_627_);
v_i_boxed_637_ = lean_unbox_usize(v_i_628_);
lean_dec(v_i_628_);
v_res_638_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0(v_allowSynthFailures_boxed_635_, v_tacticName_624_, v_mvarId_625_, v_as_626_, v_sz_boxed_636_, v_i_boxed_637_, v_b_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec_ref(v_as_626_);
return v_res_638_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(lean_object* v_tacticName_648_, lean_object* v_mvarId_649_, uint8_t v_allowSynthFailures_650_, lean_object* v_mvars_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_){
_start:
{
lean_object* v_postponed_657_; lean_object* v___x_658_; size_t v_sz_659_; size_t v___x_660_; lean_object* v___x_661_; 
v_postponed_657_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0));
v___x_658_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__2));
v_sz_659_ = lean_array_size(v_mvars_651_);
v___x_660_ = ((size_t)0ULL);
v___x_661_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0(v_allowSynthFailures_650_, v_tacticName_648_, v_mvarId_649_, v_mvars_651_, v_sz_659_, v___x_660_, v___x_658_, v_a_652_, v_a_653_, v_a_654_, v_a_655_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_684_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_684_ == 0)
{
v___x_664_ = v___x_661_;
v_isShared_665_ = v_isSharedCheck_684_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_661_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_684_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v_fst_666_; 
v_fst_666_ = lean_ctor_get(v_a_662_, 0);
lean_inc(v_fst_666_);
if (lean_obj_tag(v_fst_666_) == 1)
{
lean_object* v_snd_667_; lean_object* v_fst_668_; uint8_t v___x_669_; 
v_snd_667_ = lean_ctor_get(v_a_662_, 1);
lean_inc(v_snd_667_);
lean_dec(v_a_662_);
v_fst_668_ = lean_ctor_get(v_snd_667_, 0);
v___x_669_ = lean_unbox(v_fst_668_);
if (v___x_669_ == 0)
{
lean_dec(v_snd_667_);
if (v_allowSynthFailures_650_ == 0)
{
lean_object* v_val_670_; lean_object* v___x_672_; 
v_val_670_ = lean_ctor_get(v_fst_666_, 0);
lean_inc(v_val_670_);
lean_dec_ref_known(v_fst_666_, 1);
if (v_isShared_665_ == 0)
{
lean_ctor_set_tag(v___x_664_, 1);
lean_ctor_set(v___x_664_, 0, v_val_670_);
v___x_672_ = v___x_664_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_val_670_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
else
{
lean_object* v___x_675_; 
lean_dec_ref_known(v_fst_666_, 1);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v_postponed_657_);
v___x_675_ = v___x_664_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_postponed_657_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
else
{
lean_object* v_snd_677_; lean_object* v___x_679_; 
lean_dec_ref_known(v_fst_666_, 1);
v_snd_677_ = lean_ctor_get(v_snd_667_, 1);
lean_inc(v_snd_677_);
lean_dec(v_snd_667_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v_snd_677_);
v___x_679_ = v___x_664_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_snd_677_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
else
{
lean_object* v___x_682_; 
lean_dec(v_fst_666_);
lean_dec(v_a_662_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v_postponed_657_);
v___x_682_ = v___x_664_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_postponed_657_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
else
{
lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_692_; 
v_a_685_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_692_ == 0)
{
v___x_687_ = v___x_661_;
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_dec(v___x_661_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_690_; 
if (v_isShared_688_ == 0)
{
v___x_690_ = v___x_687_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_a_685_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_0interp(lean_interpreter_value* stack)
{
lean_object* v_tacticName_648_ = stack[0].m_obj;
lean_object* v_mvarId_649_ = stack[1].m_obj;
uint8_t v_allowSynthFailures_650_ = stack[2].m_num;
lean_object* v_mvars_651_ = stack[3].m_obj;
lean_object* v_a_652_ = stack[4].m_obj;
lean_object* v_a_653_ = stack[5].m_obj;
lean_object* v_a_654_ = stack[6].m_obj;
lean_object* v_a_655_ = stack[7].m_obj;
lean_object* v_res_693_;
v_res_693_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(v_tacticName_648_, v_mvarId_649_, v_allowSynthFailures_650_, v_mvars_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_);
stack->m_obj
 = v_res_693_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___boxed(lean_object* v_tacticName_694_, lean_object* v_mvarId_695_, lean_object* v_allowSynthFailures_696_, lean_object* v_mvars_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_){
_start:
{
uint8_t v_allowSynthFailures_boxed_703_; lean_object* v_res_704_; 
v_allowSynthFailures_boxed_703_ = lean_unbox(v_allowSynthFailures_696_);
v_res_704_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(v_tacticName_694_, v_mvarId_695_, v_allowSynthFailures_boxed_703_, v_mvars_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_);
lean_dec(v_a_701_);
lean_dec_ref(v_a_700_);
lean_dec(v_a_699_);
lean_dec_ref(v_a_698_);
lean_dec_ref(v_mvars_697_);
return v_res_704_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_keys_705_, lean_object* v_i_706_, lean_object* v_k_707_){
_start:
{
lean_object* v___x_708_; uint8_t v___x_709_; 
v___x_708_ = lean_array_get_size(v_keys_705_);
v___x_709_ = lean_nat_dec_lt(v_i_706_, v___x_708_);
if (v___x_709_ == 0)
{
lean_dec(v_i_706_);
return v___x_709_;
}
else
{
lean_object* v_k_x27_710_; uint8_t v___x_711_; 
v_k_x27_710_ = lean_array_fget_borrowed(v_keys_705_, v_i_706_);
v___x_711_ = l_Lean_instBEqMVarId_beq(v_k_707_, v_k_x27_710_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = lean_unsigned_to_nat(1u);
v___x_713_ = lean_nat_add(v_i_706_, v___x_712_);
lean_dec(v_i_706_);
v_i_706_ = v___x_713_;
goto _start;
}
else
{
lean_dec(v_i_706_);
return v___x_709_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_705_ = stack[0].m_obj;
lean_object* v_i_706_ = stack[1].m_obj;
lean_object* v_k_707_ = stack[2].m_obj;
uint8_t v_res_715_;
v_res_715_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_705_, v_i_706_, v_k_707_);
stack->m_num = v_res_715_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_keys_716_, lean_object* v_i_717_, lean_object* v_k_718_){
_start:
{
uint8_t v_res_719_; lean_object* v_r_720_; 
v_res_719_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_716_, v_i_717_, v_k_718_);
lean_dec(v_k_718_);
lean_dec_ref(v_keys_716_);
v_r_720_ = lean_box(v_res_719_);
return v_r_720_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(lean_object* v_x_721_, size_t v_x_722_, lean_object* v_x_723_){
_start:
{
if (lean_obj_tag(v_x_721_) == 0)
{
lean_object* v_es_724_; lean_object* v___x_725_; size_t v___x_726_; size_t v___x_727_; lean_object* v_j_728_; lean_object* v___x_729_; 
v_es_724_ = lean_ctor_get(v_x_721_, 0);
v___x_725_ = lean_box(2);
v___x_726_ = ((size_t)31ULL);
v___x_727_ = lean_usize_land(v_x_722_, v___x_726_);
v_j_728_ = lean_usize_to_nat(v___x_727_);
v___x_729_ = lean_array_get_borrowed(v___x_725_, v_es_724_, v_j_728_);
lean_dec(v_j_728_);
switch(lean_obj_tag(v___x_729_))
{
case 0:
{
lean_object* v_key_730_; uint8_t v___x_731_; 
v_key_730_ = lean_ctor_get(v___x_729_, 0);
v___x_731_ = l_Lean_instBEqMVarId_beq(v_x_723_, v_key_730_);
return v___x_731_;
}
case 1:
{
lean_object* v_node_732_; size_t v___x_733_; size_t v___x_734_; 
v_node_732_ = lean_ctor_get(v___x_729_, 0);
v___x_733_ = ((size_t)5ULL);
v___x_734_ = lean_usize_shift_right(v_x_722_, v___x_733_);
v_x_721_ = v_node_732_;
v_x_722_ = v___x_734_;
goto _start;
}
default: 
{
uint8_t v___x_736_; 
v___x_736_ = 0;
return v___x_736_;
}
}
}
else
{
lean_object* v_ks_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v_ks_737_ = lean_ctor_get(v_x_721_, 0);
v___x_738_ = lean_unsigned_to_nat(0u);
v___x_739_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_ks_737_, v___x_738_, v_x_723_);
return v___x_739_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_721_ = stack[0].m_obj;
size_t v_x_722_ = stack[1].m_num;
lean_object* v_x_723_ = stack[2].m_obj;
uint8_t v_res_740_;
v_res_740_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_721_, v_x_722_, v_x_723_);
stack->m_num = v_res_740_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_741_, lean_object* v_x_742_, lean_object* v_x_743_){
_start:
{
size_t v_x_2819__boxed_744_; uint8_t v_res_745_; lean_object* v_r_746_; 
v_x_2819__boxed_744_ = lean_unbox_usize(v_x_742_);
lean_dec(v_x_742_);
v_res_745_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_741_, v_x_2819__boxed_744_, v_x_743_);
lean_dec(v_x_743_);
lean_dec_ref(v_x_741_);
v_r_746_ = lean_box(v_res_745_);
return v_r_746_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(lean_object* v_x_747_, lean_object* v_x_748_){
_start:
{
uint64_t v___x_749_; size_t v___x_750_; uint8_t v___x_751_; 
v___x_749_ = l_Lean_instHashableMVarId_hash(v_x_748_);
v___x_750_ = lean_uint64_to_usize(v___x_749_);
v___x_751_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_747_, v___x_750_, v_x_748_);
return v___x_751_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_747_ = stack[0].m_obj;
lean_object* v_x_748_ = stack[1].m_obj;
uint8_t v_res_752_;
v_res_752_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_x_747_, v_x_748_);
stack->m_num = v_res_752_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg___boxed(lean_object* v_x_753_, lean_object* v_x_754_){
_start:
{
uint8_t v_res_755_; lean_object* v_r_756_; 
v_res_755_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_x_753_, v_x_754_);
lean_dec(v_x_754_);
lean_dec_ref(v_x_753_);
v_r_756_ = lean_box(v_res_755_);
return v_r_756_;
}
}
lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(lean_object* v_mvarId_757_, lean_object* v___y_758_){
_start:
{
lean_object* v___x_760_; lean_object* v_mctx_761_; lean_object* v_eAssignment_762_; uint8_t v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_760_ = lean_st_ref_get(v___y_758_);
v_mctx_761_ = lean_ctor_get(v___x_760_, 0);
lean_inc_ref(v_mctx_761_);
lean_dec(v___x_760_);
v_eAssignment_762_ = lean_ctor_get(v_mctx_761_, 8);
lean_inc_ref(v_eAssignment_762_);
lean_dec_ref(v_mctx_761_);
v___x_763_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_eAssignment_762_, v_mvarId_757_);
lean_dec_ref(v_eAssignment_762_);
v___x_764_ = lean_box(v___x_763_);
v___x_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
return v___x_765_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_757_ = stack[0].m_obj;
lean_object* v___y_758_ = stack[1].m_obj;
lean_object* v_res_766_;
v_res_766_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v_mvarId_757_, v___y_758_);
stack->m_obj
 = v_res_766_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg___boxed(lean_object* v_mvarId_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v_mvarId_767_, v___y_768_);
lean_dec(v___y_768_);
lean_dec(v_mvarId_767_);
return v_res_770_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(uint8_t v_synthAssignedInstances_771_, lean_object* v_as_772_, size_t v_sz_773_, size_t v_i_774_, lean_object* v_b_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v_a_782_; uint8_t v___x_786_; 
v___x_786_ = lean_usize_dec_lt(v_i_774_, v_sz_773_);
if (v___x_786_ == 0)
{
lean_object* v___x_787_; 
v___x_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_787_, 0, v_b_775_);
return v___x_787_;
}
else
{
lean_object* v_snd_788_; lean_object* v_fst_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_839_; 
v_snd_788_ = lean_ctor_get(v_b_775_, 1);
v_fst_789_ = lean_ctor_get(v_b_775_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v_b_775_);
if (v_isSharedCheck_839_ == 0)
{
v___x_791_ = v_b_775_;
v_isShared_792_ = v_isSharedCheck_839_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_snd_788_);
lean_inc(v_fst_789_);
lean_dec(v_b_775_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_839_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v_array_793_; lean_object* v_start_794_; lean_object* v_stop_795_; uint8_t v___x_796_; 
v_array_793_ = lean_ctor_get(v_snd_788_, 0);
v_start_794_ = lean_ctor_get(v_snd_788_, 1);
v_stop_795_ = lean_ctor_get(v_snd_788_, 2);
v___x_796_ = lean_nat_dec_lt(v_start_794_, v_stop_795_);
if (v___x_796_ == 0)
{
lean_object* v___x_798_; 
if (v_isShared_792_ == 0)
{
v___x_798_ = v___x_791_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_fst_789_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v_snd_788_);
v___x_798_ = v_reuseFailAlloc_800_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
lean_object* v___x_799_; 
v___x_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
return v___x_799_;
}
}
else
{
lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_835_; 
lean_inc(v_stop_795_);
lean_inc(v_start_794_);
lean_inc_ref(v_array_793_);
v_isSharedCheck_835_ = !lean_is_exclusive(v_snd_788_);
if (v_isSharedCheck_835_ == 0)
{
lean_object* v_unused_836_; lean_object* v_unused_837_; lean_object* v_unused_838_; 
v_unused_836_ = lean_ctor_get(v_snd_788_, 2);
lean_dec(v_unused_836_);
v_unused_837_ = lean_ctor_get(v_snd_788_, 1);
lean_dec(v_unused_837_);
v_unused_838_ = lean_ctor_get(v_snd_788_, 0);
lean_dec(v_unused_838_);
v___x_802_ = v_snd_788_;
v_isShared_803_ = v_isSharedCheck_835_;
goto v_resetjp_801_;
}
else
{
lean_dec(v_snd_788_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_835_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_808_; 
v___x_804_ = lean_array_fget(v_array_793_, v_start_794_);
v___x_805_ = lean_unsigned_to_nat(1u);
v___x_806_ = lean_nat_add(v_start_794_, v___x_805_);
lean_dec(v_start_794_);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 1, v___x_806_);
v___x_808_ = v___x_802_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_array_793_);
lean_ctor_set(v_reuseFailAlloc_834_, 1, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_834_, 2, v_stop_795_);
v___x_808_ = v_reuseFailAlloc_834_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
uint8_t v___x_809_; uint8_t v___x_810_; 
v___x_809_ = lean_unbox(v___x_804_);
lean_dec(v___x_804_);
v___x_810_ = l_Lean_BinderInfo_isInstImplicit(v___x_809_);
if (v___x_810_ == 0)
{
lean_object* v___x_812_; 
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 1, v___x_808_);
v___x_812_ = v___x_791_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_fst_789_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v___x_808_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
v_a_782_ = v___x_812_;
goto v___jp_781_;
}
}
else
{
lean_object* v_a_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v_a_814_ = lean_array_uget_borrowed(v_as_772_, v_i_774_);
v___x_815_ = l_Lean_Expr_mvarId_x21(v_a_814_);
v___x_816_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_815_, v___y_777_);
lean_dec(v___x_815_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_a_817_);
lean_dec_ref_known(v___x_816_, 1);
if (v_synthAssignedInstances_771_ == 0)
{
uint8_t v___x_825_; 
v___x_825_ = lean_unbox(v_a_817_);
lean_dec(v_a_817_);
if (v___x_825_ == 0)
{
if (v___x_810_ == 0)
{
goto v___jp_818_;
}
else
{
lean_del_object(v___x_791_);
goto v___jp_822_;
}
}
else
{
goto v___jp_818_;
}
}
else
{
lean_dec(v_a_817_);
lean_del_object(v___x_791_);
goto v___jp_822_;
}
v___jp_818_:
{
lean_object* v___x_820_; 
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 1, v___x_808_);
v___x_820_ = v___x_791_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_fst_789_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v___x_808_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
v_a_782_ = v___x_820_;
goto v___jp_781_;
}
}
v___jp_822_:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
lean_inc(v_a_814_);
v___x_823_ = lean_array_push(v_fst_789_, v_a_814_);
v___x_824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_824_, 0, v___x_823_);
lean_ctor_set(v___x_824_, 1, v___x_808_);
v_a_782_ = v___x_824_;
goto v___jp_781_;
}
}
else
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
lean_dec_ref(v___x_808_);
lean_del_object(v___x_791_);
lean_dec(v_fst_789_);
v_a_826_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___x_816_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_816_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_826_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
}
}
}
}
}
v___jp_781_:
{
size_t v___x_783_; size_t v___x_784_; 
v___x_783_ = ((size_t)1ULL);
v___x_784_ = lean_usize_add(v_i_774_, v___x_783_);
v_i_774_ = v___x_784_;
v_b_775_ = v_a_782_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_synthAssignedInstances_771_ = stack[0].m_num;
lean_object* v_as_772_ = stack[1].m_obj;
size_t v_sz_773_ = stack[2].m_num;
size_t v_i_774_ = stack[3].m_num;
lean_object* v_b_775_ = stack[4].m_obj;
lean_object* v___y_776_ = stack[5].m_obj;
lean_object* v___y_777_ = stack[6].m_obj;
lean_object* v___y_778_ = stack[7].m_obj;
lean_object* v___y_779_ = stack[8].m_obj;
lean_object* v_res_840_;
v_res_840_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(v_synthAssignedInstances_771_, v_as_772_, v_sz_773_, v_i_774_, v_b_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
stack->m_obj
 = v_res_840_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1___boxed(lean_object* v_synthAssignedInstances_841_, lean_object* v_as_842_, lean_object* v_sz_843_, lean_object* v_i_844_, lean_object* v_b_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
uint8_t v_synthAssignedInstances_boxed_851_; size_t v_sz_boxed_852_; size_t v_i_boxed_853_; lean_object* v_res_854_; 
v_synthAssignedInstances_boxed_851_ = lean_unbox(v_synthAssignedInstances_841_);
v_sz_boxed_852_ = lean_unbox_usize(v_sz_843_);
lean_dec(v_sz_843_);
v_i_boxed_853_ = lean_unbox_usize(v_i_844_);
lean_dec(v_i_844_);
v_res_854_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(v_synthAssignedInstances_boxed_851_, v_as_842_, v_sz_boxed_852_, v_i_boxed_853_, v_b_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec_ref(v_as_842_);
return v_res_854_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(lean_object* v_tacticName_855_, lean_object* v_mvarId_856_, uint8_t v_allowSynthFailures_857_, lean_object* v_a_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; uint8_t v___x_866_; 
v___x_864_ = lean_array_get_size(v_a_858_);
v___x_865_ = lean_unsigned_to_nat(0u);
v___x_866_ = lean_nat_dec_eq(v___x_864_, v___x_865_);
if (v___x_866_ == 0)
{
lean_object* v___x_867_; 
lean_inc(v_mvarId_856_);
lean_inc(v_tacticName_855_);
v___x_867_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(v_tacticName_855_, v_mvarId_856_, v_allowSynthFailures_857_, v_a_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
lean_dec_ref(v_a_858_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_868_);
lean_dec_ref_known(v___x_867_, 1);
v_a_858_ = v_a_868_;
goto _start;
}
else
{
lean_dec(v_mvarId_856_);
lean_dec(v_tacticName_855_);
return v___x_867_;
}
}
else
{
lean_object* v___x_870_; 
lean_dec(v_mvarId_856_);
lean_dec(v_tacticName_855_);
v___x_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_870_, 0, v_a_858_);
return v___x_870_;
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_tacticName_855_ = stack[0].m_obj;
lean_object* v_mvarId_856_ = stack[1].m_obj;
uint8_t v_allowSynthFailures_857_ = stack[2].m_num;
lean_object* v_a_858_ = stack[3].m_obj;
lean_object* v___y_859_ = stack[4].m_obj;
lean_object* v___y_860_ = stack[5].m_obj;
lean_object* v___y_861_ = stack[6].m_obj;
lean_object* v___y_862_ = stack[7].m_obj;
lean_object* v_res_871_;
v_res_871_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(v_tacticName_855_, v_mvarId_856_, v_allowSynthFailures_857_, v_a_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
stack->m_obj
 = v_res_871_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg___boxed(lean_object* v_tacticName_872_, lean_object* v_mvarId_873_, lean_object* v_allowSynthFailures_874_, lean_object* v_a_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
uint8_t v_allowSynthFailures_boxed_881_; lean_object* v_res_882_; 
v_allowSynthFailures_boxed_881_ = lean_unbox(v_allowSynthFailures_874_);
v_res_882_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(v_tacticName_872_, v_mvarId_873_, v_allowSynthFailures_boxed_881_, v_a_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
return v_res_882_;
}
}
lean_object* l_Lean_Meta_synthAppInstances(lean_object* v_tacticName_883_, lean_object* v_mvarId_884_, lean_object* v_mvarsNew_885_, lean_object* v_binderInfos_886_, uint8_t v_synthAssignedInstances_887_, uint8_t v_allowSynthFailures_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_){
_start:
{
lean_object* v___x_894_; lean_object* v_todo_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; size_t v_sz_899_; size_t v___x_900_; lean_object* v___x_901_; 
v___x_894_ = lean_unsigned_to_nat(0u);
v_todo_895_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0));
v___x_896_ = lean_array_get_size(v_binderInfos_886_);
v___x_897_ = l_Array_toSubarray___redArg(v_binderInfos_886_, v___x_894_, v___x_896_);
v___x_898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_898_, 0, v_todo_895_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v_sz_899_ = lean_array_size(v_mvarsNew_885_);
v___x_900_ = ((size_t)0ULL);
v___x_901_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(v_synthAssignedInstances_887_, v_mvarsNew_885_, v_sz_899_, v___x_900_, v___x_898_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v_a_902_; lean_object* v_fst_903_; lean_object* v___x_904_; 
v_a_902_ = lean_ctor_get(v___x_901_, 0);
lean_inc(v_a_902_);
lean_dec_ref_known(v___x_901_, 1);
v_fst_903_ = lean_ctor_get(v_a_902_, 0);
lean_inc(v_fst_903_);
lean_dec(v_a_902_);
v___x_904_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(v_tacticName_883_, v_mvarId_884_, v_allowSynthFailures_888_, v_fst_903_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_912_; 
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_912_ == 0)
{
lean_object* v_unused_913_; 
v_unused_913_ = lean_ctor_get(v___x_904_, 0);
lean_dec(v_unused_913_);
v___x_906_ = v___x_904_;
v_isShared_907_ = v_isSharedCheck_912_;
goto v_resetjp_905_;
}
else
{
lean_dec(v___x_904_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_912_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_908_; lean_object* v___x_910_; 
v___x_908_ = lean_box(0);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 0, v___x_908_);
v___x_910_ = v___x_906_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_908_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
else
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_921_; 
v_a_914_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_921_ == 0)
{
v___x_916_ = v___x_904_;
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_904_);
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
lean_dec(v_mvarId_884_);
lean_dec(v_tacticName_883_);
v_a_922_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_901_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_901_);
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
LEAN_EXPORT void l_Lean_Meta_synthAppInstances_0interp(lean_interpreter_value* stack)
{
lean_object* v_tacticName_883_ = stack[0].m_obj;
lean_object* v_mvarId_884_ = stack[1].m_obj;
lean_object* v_mvarsNew_885_ = stack[2].m_obj;
lean_object* v_binderInfos_886_ = stack[3].m_obj;
uint8_t v_synthAssignedInstances_887_ = stack[4].m_num;
uint8_t v_allowSynthFailures_888_ = stack[5].m_num;
lean_object* v_a_889_ = stack[6].m_obj;
lean_object* v_a_890_ = stack[7].m_obj;
lean_object* v_a_891_ = stack[8].m_obj;
lean_object* v_a_892_ = stack[9].m_obj;
lean_object* v_res_930_;
v_res_930_ = l_Lean_Meta_synthAppInstances(v_tacticName_883_, v_mvarId_884_, v_mvarsNew_885_, v_binderInfos_886_, v_synthAssignedInstances_887_, v_allowSynthFailures_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
stack->m_obj
 = v_res_930_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances___boxed(lean_object* v_tacticName_931_, lean_object* v_mvarId_932_, lean_object* v_mvarsNew_933_, lean_object* v_binderInfos_934_, lean_object* v_synthAssignedInstances_935_, lean_object* v_allowSynthFailures_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_){
_start:
{
uint8_t v_synthAssignedInstances_boxed_942_; uint8_t v_allowSynthFailures_boxed_943_; lean_object* v_res_944_; 
v_synthAssignedInstances_boxed_942_ = lean_unbox(v_synthAssignedInstances_935_);
v_allowSynthFailures_boxed_943_ = lean_unbox(v_allowSynthFailures_936_);
v_res_944_ = l_Lean_Meta_synthAppInstances(v_tacticName_931_, v_mvarId_932_, v_mvarsNew_933_, v_binderInfos_934_, v_synthAssignedInstances_boxed_942_, v_allowSynthFailures_boxed_943_, v_a_937_, v_a_938_, v_a_939_, v_a_940_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
lean_dec_ref(v_mvarsNew_933_);
return v_res_944_;
}
}
lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0(lean_object* v_mvarId_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v_mvarId_945_, v___y_947_);
return v___x_951_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_945_ = stack[0].m_obj;
lean_object* v___y_946_ = stack[1].m_obj;
lean_object* v___y_947_ = stack[2].m_obj;
lean_object* v___y_948_ = stack[3].m_obj;
lean_object* v___y_949_ = stack[4].m_obj;
lean_object* v_res_952_;
v_res_952_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0(v_mvarId_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
stack->m_obj
 = v_res_952_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___boxed(lean_object* v_mvarId_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0(v_mvarId_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v_mvarId_953_);
return v_res_959_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2(lean_object* v_tacticName_960_, lean_object* v_mvarId_961_, uint8_t v_allowSynthFailures_962_, lean_object* v_inst_963_, lean_object* v_a_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v___x_970_; 
v___x_970_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(v_tacticName_960_, v_mvarId_961_, v_allowSynthFailures_962_, v_a_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
return v___x_970_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_tacticName_960_ = stack[0].m_obj;
lean_object* v_mvarId_961_ = stack[1].m_obj;
uint8_t v_allowSynthFailures_962_ = stack[2].m_num;
lean_object* v_a_964_ = stack[4].m_obj;
lean_object* v___y_965_ = stack[5].m_obj;
lean_object* v___y_966_ = stack[6].m_obj;
lean_object* v___y_967_ = stack[7].m_obj;
lean_object* v___y_968_ = stack[8].m_obj;
lean_object* v_res_971_;
v_res_971_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2(v_tacticName_960_, v_mvarId_961_, v_allowSynthFailures_962_, lean_box(0), v_a_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
stack->m_obj
 = v_res_971_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___boxed(lean_object* v_tacticName_972_, lean_object* v_mvarId_973_, lean_object* v_allowSynthFailures_974_, lean_object* v_inst_975_, lean_object* v_a_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
uint8_t v_allowSynthFailures_boxed_982_; lean_object* v_res_983_; 
v_allowSynthFailures_boxed_982_ = lean_unbox(v_allowSynthFailures_974_);
v_res_983_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2(v_tacticName_972_, v_mvarId_973_, v_allowSynthFailures_boxed_982_, v_inst_975_, v_a_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
return v_res_983_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0(lean_object* v_00_u03b2_984_, lean_object* v_x_985_, lean_object* v_x_986_){
_start:
{
uint8_t v___x_987_; 
v___x_987_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_x_985_, v_x_986_);
return v___x_987_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_985_ = stack[1].m_obj;
lean_object* v_x_986_ = stack[2].m_obj;
uint8_t v_res_988_;
v_res_988_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0(lean_box(0), v_x_985_, v_x_986_);
stack->m_num = v_res_988_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___boxed(lean_object* v_00_u03b2_989_, lean_object* v_x_990_, lean_object* v_x_991_){
_start:
{
uint8_t v_res_992_; lean_object* v_r_993_; 
v_res_992_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0(v_00_u03b2_989_, v_x_990_, v_x_991_);
lean_dec(v_x_991_);
lean_dec_ref(v_x_990_);
v_r_993_ = lean_box(v_res_992_);
return v_r_993_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_994_, lean_object* v_x_995_, size_t v_x_996_, lean_object* v_x_997_){
_start:
{
uint8_t v___x_998_; 
v___x_998_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_995_, v_x_996_, v_x_997_);
return v___x_998_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_995_ = stack[1].m_obj;
size_t v_x_996_ = stack[2].m_num;
lean_object* v_x_997_ = stack[3].m_obj;
uint8_t v_res_999_;
v_res_999_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1(lean_box(0), v_x_995_, v_x_996_, v_x_997_);
stack->m_num = v_res_999_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1000_, lean_object* v_x_1001_, lean_object* v_x_1002_, lean_object* v_x_1003_){
_start:
{
size_t v_x_3333__boxed_1004_; uint8_t v_res_1005_; lean_object* v_r_1006_; 
v_x_3333__boxed_1004_ = lean_unbox_usize(v_x_1002_);
lean_dec(v_x_1002_);
v_res_1005_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1(v_00_u03b2_1000_, v_x_1001_, v_x_3333__boxed_1004_, v_x_1003_);
lean_dec(v_x_1003_);
lean_dec_ref(v_x_1001_);
v_r_1006_ = lean_box(v_res_1005_);
return v_r_1006_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_1007_, lean_object* v_keys_1008_, lean_object* v_vals_1009_, lean_object* v_heq_1010_, lean_object* v_i_1011_, lean_object* v_k_1012_){
_start:
{
uint8_t v___x_1013_; 
v___x_1013_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_1008_, v_i_1011_, v_k_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_1008_ = stack[1].m_obj;
lean_object* v_vals_1009_ = stack[2].m_obj;
lean_object* v_i_1011_ = stack[4].m_obj;
lean_object* v_k_1012_ = stack[5].m_obj;
uint8_t v_res_1014_;
v_res_1014_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4(lean_box(0), v_keys_1008_, v_vals_1009_, lean_box(0), v_i_1011_, v_k_1012_);
stack->m_num = v_res_1014_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_1015_, lean_object* v_keys_1016_, lean_object* v_vals_1017_, lean_object* v_heq_1018_, lean_object* v_i_1019_, lean_object* v_k_1020_){
_start:
{
uint8_t v_res_1021_; lean_object* v_r_1022_; 
v_res_1021_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_1015_, v_keys_1016_, v_vals_1017_, v_heq_1018_, v_i_1019_, v_k_1020_);
lean_dec(v_k_1020_);
lean_dec_ref(v_vals_1017_);
lean_dec_ref(v_keys_1016_);
v_r_1022_ = lean_box(v_res_1021_);
return v_r_1022_;
}
}
lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(lean_object* v_newMVars_1023_, lean_object* v_binderInfos_1024_, lean_object* v_a_1025_, lean_object* v_n_1026_, lean_object* v_i_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v_zero_1033_; uint8_t v_isZero_1034_; 
v_zero_1033_ = lean_unsigned_to_nat(0u);
v_isZero_1034_ = lean_nat_dec_eq(v_i_1027_, v_zero_1033_);
if (v_isZero_1034_ == 1)
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
lean_dec(v_i_1027_);
lean_dec(v_a_1025_);
v___x_1035_ = lean_box(0);
v___x_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
return v___x_1036_;
}
else
{
uint8_t v___x_1037_; lean_object* v_one_1038_; lean_object* v_n_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v_a_1045_; uint8_t v___x_1046_; 
v___x_1037_ = 0;
v_one_1038_ = lean_unsigned_to_nat(1u);
v_n_1039_ = lean_nat_sub(v_i_1027_, v_one_1038_);
lean_dec(v_i_1027_);
v___x_1040_ = lean_nat_sub(v_n_1026_, v_n_1039_);
v___x_1041_ = lean_nat_sub(v___x_1040_, v_one_1038_);
lean_dec(v___x_1040_);
v___x_1042_ = lean_array_fget_borrowed(v_newMVars_1023_, v___x_1041_);
v___x_1043_ = l_Lean_Expr_mvarId_x21(v___x_1042_);
v___x_1044_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_1043_, v___y_1029_);
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_a_1045_);
lean_dec_ref(v___x_1044_);
v___x_1046_ = lean_unbox(v_a_1045_);
lean_dec(v_a_1045_);
if (v___x_1046_ == 0)
{
lean_object* v___x_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; uint8_t v___x_1050_; 
v___x_1047_ = lean_box(v___x_1037_);
v___x_1048_ = lean_array_get(v___x_1047_, v_binderInfos_1024_, v___x_1041_);
lean_dec(v___x_1041_);
lean_dec(v___x_1047_);
v___x_1049_ = lean_unbox(v___x_1048_);
lean_dec(v___x_1048_);
v___x_1050_ = l_Lean_BinderInfo_isInstImplicit(v___x_1049_);
if (v___x_1050_ == 0)
{
lean_object* v___x_1051_; 
lean_inc(v___x_1043_);
v___x_1051_ = l_Lean_MVarId_getTag(v___x_1043_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v_a_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
lean_inc(v_a_1052_);
lean_dec_ref_known(v___x_1051_, 1);
lean_inc(v_a_1025_);
v___x_1053_ = l_Lean_Meta_appendTag(v_a_1025_, v_a_1052_);
lean_dec(v_a_1052_);
v___x_1054_ = l_Lean_MVarId_setTag___redArg(v___x_1043_, v___x_1053_, v___y_1029_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_dec_ref_known(v___x_1054_, 1);
v_i_1027_ = v_n_1039_;
goto _start;
}
else
{
lean_dec(v_n_1039_);
lean_dec(v_a_1025_);
return v___x_1054_;
}
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
lean_dec(v___x_1043_);
lean_dec(v_n_1039_);
lean_dec(v_a_1025_);
v_a_1056_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1051_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1051_);
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
lean_dec(v___x_1043_);
v_i_1027_ = v_n_1039_;
goto _start;
}
}
else
{
lean_dec(v___x_1043_);
lean_dec(v___x_1041_);
v_i_1027_ = v_n_1039_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_newMVars_1023_ = stack[0].m_obj;
lean_object* v_binderInfos_1024_ = stack[1].m_obj;
lean_object* v_a_1025_ = stack[2].m_obj;
lean_object* v_n_1026_ = stack[3].m_obj;
lean_object* v_i_1027_ = stack[4].m_obj;
lean_object* v___y_1028_ = stack[5].m_obj;
lean_object* v___y_1029_ = stack[6].m_obj;
lean_object* v___y_1030_ = stack[7].m_obj;
lean_object* v___y_1031_ = stack[8].m_obj;
lean_object* v_res_1066_;
v_res_1066_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_1023_, v_binderInfos_1024_, v_a_1025_, v_n_1026_, v_i_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
stack->m_obj
 = v_res_1066_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg___boxed(lean_object* v_newMVars_1067_, lean_object* v_binderInfos_1068_, lean_object* v_a_1069_, lean_object* v_n_1070_, lean_object* v_i_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_1067_, v_binderInfos_1068_, v_a_1069_, v_n_1070_, v_i_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v_n_1070_);
lean_dec_ref(v_binderInfos_1068_);
lean_dec_ref(v_newMVars_1067_);
return v_res_1077_;
}
}
lean_object* l_Lean_Meta_appendParentTag(lean_object* v_mvarId_1078_, lean_object* v_newMVars_1079_, lean_object* v_binderInfos_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = l_Lean_instInhabitedExpr;
v___x_1087_ = l_Lean_MVarId_getTag(v_mvarId_1078_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1105_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1090_ = v___x_1087_;
v_isShared_1091_ = v_isSharedCheck_1105_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1087_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1105_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; uint8_t v___x_1094_; 
v___x_1092_ = lean_array_get_size(v_newMVars_1079_);
v___x_1093_ = lean_unsigned_to_nat(1u);
v___x_1094_ = lean_nat_dec_eq(v___x_1092_, v___x_1093_);
if (v___x_1094_ == 0)
{
uint8_t v___x_1095_; 
v___x_1095_ = l_Lean_Name_isAnonymous(v_a_1088_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1096_; 
lean_del_object(v___x_1090_);
v___x_1096_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_1079_, v_binderInfos_1080_, v_a_1088_, v___x_1092_, v___x_1092_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_);
return v___x_1096_;
}
else
{
lean_object* v___x_1097_; lean_object* v___x_1099_; 
lean_dec(v_a_1088_);
v___x_1097_ = lean_box(0);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 0, v___x_1097_);
v___x_1099_ = v___x_1090_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1097_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
else
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
lean_del_object(v___x_1090_);
v___x_1101_ = lean_unsigned_to_nat(0u);
v___x_1102_ = lean_array_get_borrowed(v___x_1086_, v_newMVars_1079_, v___x_1101_);
v___x_1103_ = l_Lean_Expr_mvarId_x21(v___x_1102_);
v___x_1104_ = l_Lean_MVarId_setTag___redArg(v___x_1103_, v_a_1088_, v_a_1082_);
return v___x_1104_;
}
}
}
else
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
v_a_1106_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1087_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1087_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1106_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_appendParentTag_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1078_ = stack[0].m_obj;
lean_object* v_newMVars_1079_ = stack[1].m_obj;
lean_object* v_binderInfos_1080_ = stack[2].m_obj;
lean_object* v_a_1081_ = stack[3].m_obj;
lean_object* v_a_1082_ = stack[4].m_obj;
lean_object* v_a_1083_ = stack[5].m_obj;
lean_object* v_a_1084_ = stack[6].m_obj;
lean_object* v_res_1114_;
v_res_1114_ = l_Lean_Meta_appendParentTag(v_mvarId_1078_, v_newMVars_1079_, v_binderInfos_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_);
stack->m_obj
 = v_res_1114_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendParentTag___boxed(lean_object* v_mvarId_1115_, lean_object* v_newMVars_1116_, lean_object* v_binderInfos_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Lean_Meta_appendParentTag(v_mvarId_1115_, v_newMVars_1116_, v_binderInfos_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_);
lean_dec(v_a_1121_);
lean_dec_ref(v_a_1120_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec_ref(v_binderInfos_1117_);
lean_dec_ref(v_newMVars_1116_);
return v_res_1123_;
}
}
lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0(lean_object* v_newMVars_1124_, lean_object* v_binderInfos_1125_, lean_object* v_a_1126_, lean_object* v_n_1127_, lean_object* v_i_1128_, lean_object* v_a_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_1124_, v_binderInfos_1125_, v_a_1126_, v_n_1127_, v_i_1128_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
return v___x_1135_;
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_newMVars_1124_ = stack[0].m_obj;
lean_object* v_binderInfos_1125_ = stack[1].m_obj;
lean_object* v_a_1126_ = stack[2].m_obj;
lean_object* v_n_1127_ = stack[3].m_obj;
lean_object* v_i_1128_ = stack[4].m_obj;
lean_object* v___y_1130_ = stack[6].m_obj;
lean_object* v___y_1131_ = stack[7].m_obj;
lean_object* v___y_1132_ = stack[8].m_obj;
lean_object* v___y_1133_ = stack[9].m_obj;
lean_object* v_res_1136_;
v_res_1136_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0(v_newMVars_1124_, v_binderInfos_1125_, v_a_1126_, v_n_1127_, v_i_1128_, lean_box(0), v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
stack->m_obj
 = v_res_1136_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___boxed(lean_object* v_newMVars_1137_, lean_object* v_binderInfos_1138_, lean_object* v_a_1139_, lean_object* v_n_1140_, lean_object* v_i_1141_, lean_object* v_a_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0(v_newMVars_1137_, v_binderInfos_1138_, v_a_1139_, v_n_1140_, v_i_1141_, v_a_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v_n_1140_);
lean_dec_ref(v_binderInfos_1138_);
lean_dec_ref(v_newMVars_1137_);
return v_res_1148_;
}
}
lean_object* l_Lean_Meta_postprocessAppMVars(lean_object* v_tacticName_1149_, lean_object* v_mvarId_1150_, lean_object* v_newMVars_1151_, lean_object* v_binderInfos_1152_, uint8_t v_synthAssignedInstances_1153_, uint8_t v_allowSynthFailures_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_){
_start:
{
lean_object* v___x_1160_; 
v___x_1160_ = l_Lean_Meta_synthAppInstances(v_tacticName_1149_, v_mvarId_1150_, v_newMVars_1151_, v_binderInfos_1152_, v_synthAssignedInstances_1153_, v_allowSynthFailures_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_);
return v___x_1160_;
}
}
LEAN_EXPORT void l_Lean_Meta_postprocessAppMVars_0interp(lean_interpreter_value* stack)
{
lean_object* v_tacticName_1149_ = stack[0].m_obj;
lean_object* v_mvarId_1150_ = stack[1].m_obj;
lean_object* v_newMVars_1151_ = stack[2].m_obj;
lean_object* v_binderInfos_1152_ = stack[3].m_obj;
uint8_t v_synthAssignedInstances_1153_ = stack[4].m_num;
uint8_t v_allowSynthFailures_1154_ = stack[5].m_num;
lean_object* v_a_1155_ = stack[6].m_obj;
lean_object* v_a_1156_ = stack[7].m_obj;
lean_object* v_a_1157_ = stack[8].m_obj;
lean_object* v_a_1158_ = stack[9].m_obj;
lean_object* v_res_1161_;
v_res_1161_ = l_Lean_Meta_postprocessAppMVars(v_tacticName_1149_, v_mvarId_1150_, v_newMVars_1151_, v_binderInfos_1152_, v_synthAssignedInstances_1153_, v_allowSynthFailures_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_);
stack->m_obj
 = v_res_1161_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_postprocessAppMVars___boxed(lean_object* v_tacticName_1162_, lean_object* v_mvarId_1163_, lean_object* v_newMVars_1164_, lean_object* v_binderInfos_1165_, lean_object* v_synthAssignedInstances_1166_, lean_object* v_allowSynthFailures_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_){
_start:
{
uint8_t v_synthAssignedInstances_boxed_1173_; uint8_t v_allowSynthFailures_boxed_1174_; lean_object* v_res_1175_; 
v_synthAssignedInstances_boxed_1173_ = lean_unbox(v_synthAssignedInstances_1166_);
v_allowSynthFailures_boxed_1174_ = lean_unbox(v_allowSynthFailures_1167_);
v_res_1175_ = l_Lean_Meta_postprocessAppMVars(v_tacticName_1162_, v_mvarId_1163_, v_newMVars_1164_, v_binderInfos_1165_, v_synthAssignedInstances_boxed_1173_, v_allowSynthFailures_boxed_1174_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_);
lean_dec(v_a_1171_);
lean_dec_ref(v_a_1170_);
lean_dec(v_a_1169_);
lean_dec_ref(v_a_1168_);
lean_dec_ref(v_newMVars_1164_);
return v_res_1175_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0(lean_object* v_mvar_1176_, lean_object* v_mvarId_1177_){
_start:
{
lean_object* v___x_1178_; uint8_t v___x_1179_; 
v___x_1178_ = l_Lean_Expr_mvarId_x21(v_mvar_1176_);
v___x_1179_ = l_Lean_instBEqMVarId_beq(v_mvarId_1177_, v___x_1178_);
lean_dec(v___x_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvar_1176_ = stack[0].m_obj;
lean_object* v_mvarId_1177_ = stack[1].m_obj;
uint8_t v_res_1180_;
v_res_1180_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0(v_mvar_1176_, v_mvarId_1177_);
stack->m_num = v_res_1180_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0___boxed(lean_object* v_mvar_1181_, lean_object* v_mvarId_1182_){
_start:
{
uint8_t v_res_1183_; lean_object* v_r_1184_; 
v_res_1183_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0(v_mvar_1181_, v_mvarId_1182_);
lean_dec(v_mvarId_1182_);
lean_dec_ref(v_mvar_1181_);
v_r_1184_ = lean_box(v_res_1183_);
return v_r_1184_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(lean_object* v_mvar_1185_, lean_object* v_as_1186_, size_t v_i_1187_, size_t v_stop_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
uint8_t v___x_1198_; 
v___x_1198_ = lean_usize_dec_eq(v_i_1187_, v_stop_1188_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; uint8_t v___x_1200_; 
v___x_1199_ = lean_array_uget_borrowed(v_as_1186_, v_i_1187_);
v___x_1200_ = lean_expr_eqv(v_mvar_1185_, v___x_1199_);
if (v___x_1200_ == 0)
{
lean_object* v___f_1201_; uint8_t v___x_1202_; lean_object* v___x_1203_; 
lean_inc_ref(v_mvar_1185_);
v___f_1201_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1201_, 0, v_mvar_1185_);
v___x_1202_ = 1;
lean_inc(v___y_1192_);
lean_inc_ref(v___y_1191_);
lean_inc(v___y_1190_);
lean_inc_ref(v___y_1189_);
lean_inc(v___x_1199_);
v___x_1203_ = lean_infer_type(v___x_1199_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1218_; 
v_a_1204_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1206_ = v___x_1203_;
v_isShared_1207_ = v_isSharedCheck_1218_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1203_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1218_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = lean_box(0);
v___x_1209_ = l_Lean_FindMVar_main(v___f_1201_, v_a_1204_, v___x_1208_);
if (lean_obj_tag(v___x_1209_) == 0)
{
if (v___x_1200_ == 0)
{
lean_del_object(v___x_1206_);
goto v___jp_1194_;
}
else
{
lean_object* v___x_1210_; lean_object* v___x_1212_; 
lean_dec_ref(v_mvar_1185_);
v___x_1210_ = lean_box(v___x_1202_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 0, v___x_1210_);
v___x_1212_ = v___x_1206_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1210_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
else
{
lean_object* v___x_1214_; lean_object* v___x_1216_; 
lean_dec_ref_known(v___x_1209_, 1);
lean_dec_ref(v_mvar_1185_);
v___x_1214_ = lean_box(v___x_1202_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 0, v___x_1214_);
v___x_1216_ = v___x_1206_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___x_1214_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
else
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1226_; 
lean_dec_ref(v___f_1201_);
lean_dec_ref(v_mvar_1185_);
v_a_1219_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1221_ = v___x_1203_;
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1203_);
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
goto v___jp_1194_;
}
}
else
{
uint8_t v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
lean_dec_ref(v_mvar_1185_);
v___x_1227_ = 0;
v___x_1228_ = lean_box(v___x_1227_);
v___x_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1228_);
return v___x_1229_;
}
v___jp_1194_:
{
size_t v___x_1195_; size_t v___x_1196_; 
v___x_1195_ = ((size_t)1ULL);
v___x_1196_ = lean_usize_add(v_i_1187_, v___x_1195_);
v_i_1187_ = v___x_1196_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvar_1185_ = stack[0].m_obj;
lean_object* v_as_1186_ = stack[1].m_obj;
size_t v_i_1187_ = stack[2].m_num;
size_t v_stop_1188_ = stack[3].m_num;
lean_object* v___y_1189_ = stack[4].m_obj;
lean_object* v___y_1190_ = stack[5].m_obj;
lean_object* v___y_1191_ = stack[6].m_obj;
lean_object* v___y_1192_ = stack[7].m_obj;
lean_object* v_res_1230_;
v_res_1230_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(v_mvar_1185_, v_as_1186_, v_i_1187_, v_stop_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
stack->m_obj
 = v_res_1230_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___boxed(lean_object* v_mvar_1231_, lean_object* v_as_1232_, lean_object* v_i_1233_, lean_object* v_stop_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
size_t v_i_boxed_1240_; size_t v_stop_boxed_1241_; lean_object* v_res_1242_; 
v_i_boxed_1240_ = lean_unbox_usize(v_i_1233_);
lean_dec(v_i_1233_);
v_stop_boxed_1241_ = lean_unbox_usize(v_stop_1234_);
lean_dec(v_stop_1234_);
v_res_1242_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(v_mvar_1231_, v_as_1232_, v_i_boxed_1240_, v_stop_boxed_1241_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec_ref(v_as_1232_);
return v_res_1242_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(lean_object* v_mvar_1243_, lean_object* v_otherMVars_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_){
_start:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; 
v___x_1250_ = lean_unsigned_to_nat(0u);
v___x_1251_ = lean_array_get_size(v_otherMVars_1244_);
v___x_1252_ = lean_nat_dec_lt(v___x_1250_, v___x_1251_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
lean_dec_ref(v_mvar_1243_);
v___x_1253_ = lean_box(v___x_1252_);
v___x_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
return v___x_1254_;
}
else
{
if (v___x_1252_ == 0)
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
lean_dec_ref(v_mvar_1243_);
v___x_1255_ = lean_box(v___x_1252_);
v___x_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1255_);
return v___x_1256_;
}
else
{
size_t v___x_1257_; size_t v___x_1258_; lean_object* v___x_1259_; 
v___x_1257_ = ((size_t)0ULL);
v___x_1258_ = lean_usize_of_nat(v___x_1251_);
v___x_1259_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(v_mvar_1243_, v_otherMVars_1244_, v___x_1257_, v___x_1258_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_);
return v___x_1259_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvar_1243_ = stack[0].m_obj;
lean_object* v_otherMVars_1244_ = stack[1].m_obj;
lean_object* v_a_1245_ = stack[2].m_obj;
lean_object* v_a_1246_ = stack[3].m_obj;
lean_object* v_a_1247_ = stack[4].m_obj;
lean_object* v_a_1248_ = stack[5].m_obj;
lean_object* v_res_1260_;
v_res_1260_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(v_mvar_1243_, v_otherMVars_1244_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_);
stack->m_obj
 = v_res_1260_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___boxed(lean_object* v_mvar_1261_, lean_object* v_otherMVars_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(v_mvar_1261_, v_otherMVars_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_);
lean_dec(v_a_1266_);
lean_dec_ref(v_a_1265_);
lean_dec(v_a_1264_);
lean_dec_ref(v_a_1263_);
lean_dec_ref(v_otherMVars_1262_);
return v_res_1268_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(lean_object* v_mvars_1269_, lean_object* v_as_1270_, size_t v_i_1271_, size_t v_stop_1272_, lean_object* v_b_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
lean_object* v_a_1280_; uint8_t v___x_1284_; 
v___x_1284_ = lean_usize_dec_eq(v_i_1271_, v_stop_1272_);
if (v___x_1284_ == 0)
{
lean_object* v_fst_1285_; lean_object* v_snd_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1311_; 
v_fst_1285_ = lean_ctor_get(v_b_1273_, 0);
v_snd_1286_ = lean_ctor_get(v_b_1273_, 1);
v_isSharedCheck_1311_ = !lean_is_exclusive(v_b_1273_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1288_ = v_b_1273_;
v_isShared_1289_ = v_isSharedCheck_1311_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_snd_1286_);
lean_inc(v_fst_1285_);
lean_dec(v_b_1273_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1311_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1290_; lean_object* v_currMVarId_1291_; lean_object* v___x_1292_; 
v___x_1290_ = lean_array_uget_borrowed(v_as_1270_, v_i_1271_);
v_currMVarId_1291_ = l_Lean_Expr_mvarId_x21(v___x_1290_);
lean_inc(v___x_1290_);
v___x_1292_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(v___x_1290_, v_mvars_1269_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v_a_1293_; uint8_t v___x_1294_; 
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
lean_inc(v_a_1293_);
lean_dec_ref_known(v___x_1292_, 1);
v___x_1294_ = lean_unbox(v_a_1293_);
lean_dec(v_a_1293_);
if (v___x_1294_ == 0)
{
lean_object* v___x_1295_; lean_object* v___x_1297_; 
v___x_1295_ = lean_array_push(v_fst_1285_, v_currMVarId_1291_);
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 0, v___x_1295_);
v___x_1297_ = v___x_1288_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v___x_1295_);
lean_ctor_set(v_reuseFailAlloc_1298_, 1, v_snd_1286_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
v_a_1280_ = v___x_1297_;
goto v___jp_1279_;
}
}
else
{
lean_object* v___x_1299_; lean_object* v___x_1301_; 
v___x_1299_ = lean_array_push(v_snd_1286_, v_currMVarId_1291_);
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 1, v___x_1299_);
v___x_1301_ = v___x_1288_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_fst_1285_);
lean_ctor_set(v_reuseFailAlloc_1302_, 1, v___x_1299_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
v_a_1280_ = v___x_1301_;
goto v___jp_1279_;
}
}
}
else
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
lean_dec(v_currMVarId_1291_);
lean_del_object(v___x_1288_);
lean_dec(v_snd_1286_);
lean_dec(v_fst_1285_);
v_a_1303_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v___x_1292_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1292_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
if (v_isShared_1306_ == 0)
{
v___x_1308_ = v___x_1305_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_a_1303_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
}
else
{
lean_object* v___x_1312_; 
v___x_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1312_, 0, v_b_1273_);
return v___x_1312_;
}
v___jp_1279_:
{
size_t v___x_1281_; size_t v___x_1282_; 
v___x_1281_ = ((size_t)1ULL);
v___x_1282_ = lean_usize_add(v_i_1271_, v___x_1281_);
v_i_1271_ = v___x_1282_;
v_b_1273_ = v_a_1280_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvars_1269_ = stack[0].m_obj;
lean_object* v_as_1270_ = stack[1].m_obj;
size_t v_i_1271_ = stack[2].m_num;
size_t v_stop_1272_ = stack[3].m_num;
lean_object* v_b_1273_ = stack[4].m_obj;
lean_object* v___y_1274_ = stack[5].m_obj;
lean_object* v___y_1275_ = stack[6].m_obj;
lean_object* v___y_1276_ = stack[7].m_obj;
lean_object* v___y_1277_ = stack[8].m_obj;
lean_object* v_res_1313_;
v_res_1313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_1269_, v_as_1270_, v_i_1271_, v_stop_1272_, v_b_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
stack->m_obj
 = v_res_1313_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0___boxed(lean_object* v_mvars_1314_, lean_object* v_as_1315_, lean_object* v_i_1316_, lean_object* v_stop_1317_, lean_object* v_b_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
size_t v_i_boxed_1324_; size_t v_stop_boxed_1325_; lean_object* v_res_1326_; 
v_i_boxed_1324_ = lean_unbox_usize(v_i_1316_);
lean_dec(v_i_1316_);
v_stop_boxed_1325_ = lean_unbox_usize(v_stop_1317_);
lean_dec(v_stop_1317_);
v_res_1326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_1314_, v_as_1315_, v_i_boxed_1324_, v_stop_boxed_1325_, v_b_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_dec_ref(v_as_1315_);
lean_dec_ref(v_mvars_1314_);
return v_res_1326_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(lean_object* v_mvars_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_){
_start:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; uint8_t v___x_1340_; 
v___x_1337_ = lean_unsigned_to_nat(0u);
v___x_1338_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1));
v___x_1339_ = lean_array_get_size(v_mvars_1331_);
v___x_1340_ = lean_nat_dec_lt(v___x_1337_, v___x_1339_);
if (v___x_1340_ == 0)
{
lean_object* v___x_1341_; 
v___x_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1338_);
return v___x_1341_;
}
else
{
uint8_t v___x_1342_; 
v___x_1342_ = lean_nat_dec_le(v___x_1339_, v___x_1339_);
if (v___x_1342_ == 0)
{
if (v___x_1340_ == 0)
{
lean_object* v___x_1343_; 
v___x_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1338_);
return v___x_1343_;
}
else
{
size_t v___x_1344_; size_t v___x_1345_; lean_object* v___x_1346_; 
v___x_1344_ = ((size_t)0ULL);
v___x_1345_ = lean_usize_of_nat(v___x_1339_);
v___x_1346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_1331_, v_mvars_1331_, v___x_1344_, v___x_1345_, v___x_1338_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_);
return v___x_1346_;
}
}
else
{
size_t v___x_1347_; size_t v___x_1348_; lean_object* v___x_1349_; 
v___x_1347_ = ((size_t)0ULL);
v___x_1348_ = lean_usize_of_nat(v___x_1339_);
v___x_1349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_1331_, v_mvars_1331_, v___x_1347_, v___x_1348_, v___x_1338_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_);
return v___x_1349_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvars_1331_ = stack[0].m_obj;
lean_object* v_a_1332_ = stack[1].m_obj;
lean_object* v_a_1333_ = stack[2].m_obj;
lean_object* v_a_1334_ = stack[3].m_obj;
lean_object* v_a_1335_ = stack[4].m_obj;
lean_object* v_res_1350_;
v_res_1350_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_);
stack->m_obj
 = v_res_1350_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___boxed(lean_object* v_mvars_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
lean_dec(v_a_1355_);
lean_dec_ref(v_a_1354_);
lean_dec(v_a_1353_);
lean_dec_ref(v_a_1352_);
lean_dec_ref(v_mvars_1351_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals_spec__0(lean_object* v_a_1358_, lean_object* v_a_1359_){
_start:
{
if (lean_obj_tag(v_a_1358_) == 0)
{
lean_object* v___x_1360_; 
v___x_1360_ = l_List_reverse___redArg(v_a_1359_);
return v___x_1360_;
}
else
{
lean_object* v_head_1361_; lean_object* v_tail_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1371_; 
v_head_1361_ = lean_ctor_get(v_a_1358_, 0);
v_tail_1362_ = lean_ctor_get(v_a_1358_, 1);
v_isSharedCheck_1371_ = !lean_is_exclusive(v_a_1358_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1364_ = v_a_1358_;
v_isShared_1365_ = v_isSharedCheck_1371_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_tail_1362_);
lean_inc(v_head_1361_);
lean_dec(v_a_1358_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1371_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1366_; lean_object* v___x_1368_; 
v___x_1366_ = l_Lean_Expr_mvarId_x21(v_head_1361_);
lean_dec(v_head_1361_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 1, v_a_1359_);
lean_ctor_set(v___x_1364_, 0, v___x_1366_);
v___x_1368_ = v___x_1364_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v___x_1366_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v_a_1359_);
v___x_1368_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
v_a_1358_ = v_tail_1362_;
v_a_1359_ = v___x_1368_;
goto _start;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(lean_object* v_mvars_1372_, uint8_t v_x_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_){
_start:
{
switch(v_x_1373_)
{
case 0:
{
lean_object* v___x_1379_; 
v___x_1379_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1372_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
lean_dec_ref(v_mvars_1372_);
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
lean_object* v_fst_1384_; lean_object* v_snd_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1390_; 
v_fst_1384_ = lean_ctor_get(v_a_1380_, 0);
lean_inc(v_fst_1384_);
v_snd_1385_ = lean_ctor_get(v_a_1380_, 1);
lean_inc(v_snd_1385_);
lean_dec(v_a_1380_);
v___x_1386_ = lean_array_to_list(v_fst_1384_);
v___x_1387_ = lean_array_to_list(v_snd_1385_);
v___x_1388_ = l_List_appendTR___redArg(v___x_1386_, v___x_1387_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 0, v___x_1388_);
v___x_1390_ = v___x_1382_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1388_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
else
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
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
case 1:
{
lean_object* v___x_1401_; 
v___x_1401_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1372_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
lean_dec_ref(v_mvars_1372_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1411_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1404_ = v___x_1401_;
v_isShared_1405_ = v_isSharedCheck_1411_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1401_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1411_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v_fst_1406_; lean_object* v___x_1407_; lean_object* v___x_1409_; 
v_fst_1406_ = lean_ctor_get(v_a_1402_, 0);
lean_inc(v_fst_1406_);
lean_dec(v_a_1402_);
v___x_1407_ = lean_array_to_list(v_fst_1406_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v___x_1407_);
v___x_1409_ = v___x_1404_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1407_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
else
{
lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1419_; 
v_a_1412_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1414_ = v___x_1401_;
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1401_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1412_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
default: 
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1420_ = lean_array_to_list(v_mvars_1372_);
v___x_1421_ = lean_box(0);
v___x_1422_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals_spec__0(v___x_1420_, v___x_1421_);
v___x_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1422_);
return v___x_1423_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvars_1372_ = stack[0].m_obj;
uint8_t v_x_1373_ = stack[1].m_num;
lean_object* v_a_1374_ = stack[2].m_obj;
lean_object* v_a_1375_ = stack[3].m_obj;
lean_object* v_a_1376_ = stack[4].m_obj;
lean_object* v_a_1377_ = stack[5].m_obj;
lean_object* v_res_1424_;
v_res_1424_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(v_mvars_1372_, v_x_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
stack->m_obj
 = v_res_1424_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals___boxed(lean_object* v_mvars_1425_, lean_object* v_x_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_){
_start:
{
uint8_t v_x_745__boxed_1432_; lean_object* v_res_1433_; 
v_x_745__boxed_1432_ = lean_unbox(v_x_1426_);
v_res_1433_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(v_mvars_1425_, v_x_745__boxed_1432_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_);
lean_dec(v_a_1430_);
lean_dec_ref(v_a_1429_);
lean_dec(v_a_1428_);
lean_dec_ref(v_a_1427_);
return v_res_1433_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(uint8_t v_approx_1434_, lean_object* v_a_1435_, lean_object* v_b_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_){
_start:
{
if (v_approx_1434_ == 0)
{
lean_object* v___x_1442_; 
v___x_1442_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1435_, v_b_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_);
return v___x_1442_;
}
else
{
lean_object* v___x_1443_; uint8_t v_constApprox_1444_; uint8_t v_isDefEqStuckEx_1445_; uint8_t v_unificationHints_1446_; uint8_t v_proofIrrelevance_1447_; uint8_t v_assignSyntheticOpaque_1448_; uint8_t v_offsetCnstrs_1449_; uint8_t v_transparency_1450_; uint8_t v_etaStruct_1451_; uint8_t v_univApprox_1452_; uint8_t v_iota_1453_; uint8_t v_beta_1454_; uint8_t v_proj_1455_; uint8_t v_zeta_1456_; uint8_t v_zetaDelta_1457_; uint8_t v_zetaUnused_1458_; uint8_t v_zetaHave_1459_; uint8_t v_canUnfoldPredicateConfig_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1481_; 
v___x_1443_ = l_Lean_Meta_Context_config(v_a_1437_);
v_constApprox_1444_ = lean_ctor_get_uint8(v___x_1443_, 3);
v_isDefEqStuckEx_1445_ = lean_ctor_get_uint8(v___x_1443_, 4);
v_unificationHints_1446_ = lean_ctor_get_uint8(v___x_1443_, 5);
v_proofIrrelevance_1447_ = lean_ctor_get_uint8(v___x_1443_, 6);
v_assignSyntheticOpaque_1448_ = lean_ctor_get_uint8(v___x_1443_, 7);
v_offsetCnstrs_1449_ = lean_ctor_get_uint8(v___x_1443_, 8);
v_transparency_1450_ = lean_ctor_get_uint8(v___x_1443_, 9);
v_etaStruct_1451_ = lean_ctor_get_uint8(v___x_1443_, 10);
v_univApprox_1452_ = lean_ctor_get_uint8(v___x_1443_, 11);
v_iota_1453_ = lean_ctor_get_uint8(v___x_1443_, 12);
v_beta_1454_ = lean_ctor_get_uint8(v___x_1443_, 13);
v_proj_1455_ = lean_ctor_get_uint8(v___x_1443_, 14);
v_zeta_1456_ = lean_ctor_get_uint8(v___x_1443_, 15);
v_zetaDelta_1457_ = lean_ctor_get_uint8(v___x_1443_, 16);
v_zetaUnused_1458_ = lean_ctor_get_uint8(v___x_1443_, 17);
v_zetaHave_1459_ = lean_ctor_get_uint8(v___x_1443_, 18);
v_canUnfoldPredicateConfig_1460_ = lean_ctor_get_uint8(v___x_1443_, 19);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1462_ = v___x_1443_;
v_isShared_1463_ = v_isSharedCheck_1481_;
goto v_resetjp_1461_;
}
else
{
lean_dec(v___x_1443_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1481_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_1480_, 3, v_constApprox_1444_);
lean_ctor_set_uint8(v_reuseFailAlloc_1480_, 4, v_isDefEqStuckEx_1445_);
lean_ctor_set_uint8(v_reuseFailAlloc_1480_, 5, v_unificationHints_1446_);
lean_ctor_set_uint8(v_reuseFailAlloc_1480_, 6, v_proofIrrelevance_1447_);
lean_ctor_set_uint8(v_reuseFailAlloc_1480_, 7, v_assignSyntheticOpaque_1448_);
lean_ctor_set_uint8(v_reuseFailAlloc_1480_, 8, v_offsetCnstrs_1449_);
lean_ctor_set_uint8(v_reuseFailAlloc_1480_, 9, v_transparency_1450_);
lean_ctor_set_uint8(v_reuseFailAlloc_1480_, 10, v_etaStruct_1451_);
lean_ctor_set_uint8(v_reuseFailAlloc_1480_, 11, v_univApprox_1452_);
lean_ctor_set_uint8(v_reuseFailAlloc_1480_, 12, v_iota_1453_);
lean_ctor_set_uint8(v_reuseFailAlloc_1480_, 13, v_beta_1454_);
lean_ctor_set_uint8(v_reuseFailAlloc_1480_, 14, v_proj_1455_);
lean_ctor_set_uint8(v_reuseFailAlloc_1480_, 15, v_zeta_1456_);
lean_ctor_set_uint8(v_reuseFailAlloc_1480_, 16, v_zetaDelta_1457_);
lean_ctor_set_uint8(v_reuseFailAlloc_1480_, 17, v_zetaUnused_1458_);
lean_ctor_set_uint8(v_reuseFailAlloc_1480_, 18, v_zetaHave_1459_);
lean_ctor_set_uint8(v_reuseFailAlloc_1480_, 19, v_canUnfoldPredicateConfig_1460_);
v___x_1465_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
uint8_t v_trackZetaDelta_1466_; lean_object* v_zetaDeltaSet_1467_; lean_object* v_lctx_1468_; lean_object* v_localInstances_1469_; lean_object* v_defEqCtx_x3f_1470_; lean_object* v_synthPendingDepth_1471_; lean_object* v_customCanUnfoldPredicate_x3f_1472_; uint8_t v_univApprox_1473_; uint8_t v_inTypeClassResolution_1474_; uint8_t v_cacheInferType_1475_; uint64_t v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
lean_ctor_set_uint8(v___x_1465_, 0, v_approx_1434_);
lean_ctor_set_uint8(v___x_1465_, 1, v_approx_1434_);
lean_ctor_set_uint8(v___x_1465_, 2, v_approx_1434_);
v_trackZetaDelta_1466_ = lean_ctor_get_uint8(v_a_1437_, sizeof(void*)*7);
v_zetaDeltaSet_1467_ = lean_ctor_get(v_a_1437_, 1);
v_lctx_1468_ = lean_ctor_get(v_a_1437_, 2);
v_localInstances_1469_ = lean_ctor_get(v_a_1437_, 3);
v_defEqCtx_x3f_1470_ = lean_ctor_get(v_a_1437_, 4);
v_synthPendingDepth_1471_ = lean_ctor_get(v_a_1437_, 5);
v_customCanUnfoldPredicate_x3f_1472_ = lean_ctor_get(v_a_1437_, 6);
v_univApprox_1473_ = lean_ctor_get_uint8(v_a_1437_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1474_ = lean_ctor_get_uint8(v_a_1437_, sizeof(void*)*7 + 2);
v_cacheInferType_1475_ = lean_ctor_get_uint8(v_a_1437_, sizeof(void*)*7 + 3);
v___x_1476_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1465_);
v___x_1477_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1477_, 0, v___x_1465_);
lean_ctor_set_uint64(v___x_1477_, sizeof(void*)*1, v___x_1476_);
lean_inc(v_customCanUnfoldPredicate_x3f_1472_);
lean_inc(v_synthPendingDepth_1471_);
lean_inc(v_defEqCtx_x3f_1470_);
lean_inc_ref(v_localInstances_1469_);
lean_inc_ref(v_lctx_1468_);
lean_inc(v_zetaDeltaSet_1467_);
v___x_1478_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1478_, 0, v___x_1477_);
lean_ctor_set(v___x_1478_, 1, v_zetaDeltaSet_1467_);
lean_ctor_set(v___x_1478_, 2, v_lctx_1468_);
lean_ctor_set(v___x_1478_, 3, v_localInstances_1469_);
lean_ctor_set(v___x_1478_, 4, v_defEqCtx_x3f_1470_);
lean_ctor_set(v___x_1478_, 5, v_synthPendingDepth_1471_);
lean_ctor_set(v___x_1478_, 6, v_customCanUnfoldPredicate_x3f_1472_);
lean_ctor_set_uint8(v___x_1478_, sizeof(void*)*7, v_trackZetaDelta_1466_);
lean_ctor_set_uint8(v___x_1478_, sizeof(void*)*7 + 1, v_univApprox_1473_);
lean_ctor_set_uint8(v___x_1478_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1474_);
lean_ctor_set_uint8(v___x_1478_, sizeof(void*)*7 + 3, v_cacheInferType_1475_);
v___x_1479_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1435_, v_b_1436_, v___x_1478_, v_a_1438_, v_a_1439_, v_a_1440_);
lean_dec_ref_known(v___x_1478_, 7);
return v___x_1479_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply_0interp(lean_interpreter_value* stack)
{
uint8_t v_approx_1434_ = stack[0].m_num;
lean_object* v_a_1435_ = stack[1].m_obj;
lean_object* v_b_1436_ = stack[2].m_obj;
lean_object* v_a_1437_ = stack[3].m_obj;
lean_object* v_a_1438_ = stack[4].m_obj;
lean_object* v_a_1439_ = stack[5].m_obj;
lean_object* v_a_1440_ = stack[6].m_obj;
lean_object* v_res_1482_;
v_res_1482_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_approx_1434_, v_a_1435_, v_b_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_);
stack->m_obj
 = v_res_1482_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply___boxed(lean_object* v_approx_1483_, lean_object* v_a_1484_, lean_object* v_b_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_){
_start:
{
uint8_t v_approx_boxed_1491_; lean_object* v_res_1492_; 
v_approx_boxed_1491_ = lean_unbox(v_approx_1483_);
v_res_1492_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_approx_boxed_1491_, v_a_1484_, v_b_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_);
lean_dec(v_a_1489_);
lean_dec_ref(v_a_1488_);
lean_dec(v_a_1487_);
lean_dec_ref(v_a_1486_);
return v_res_1492_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(lean_object* v_mvarId_1493_, lean_object* v_cfg_1494_, lean_object* v_term_x3f_1495_, lean_object* v_targetType_1496_, lean_object* v_eType_1497_, lean_object* v_rangeNumArgs_1498_, lean_object* v_i_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_){
_start:
{
lean_object* v_conclusionType_x3f_1506_; lean_object* v___y_1507_; lean_object* v___y_1508_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v_lower_1513_; lean_object* v_upper_1514_; uint8_t v___x_1515_; 
v_lower_1513_ = lean_ctor_get(v_rangeNumArgs_1498_, 0);
v_upper_1514_ = lean_ctor_get(v_rangeNumArgs_1498_, 1);
v___x_1515_ = lean_nat_dec_lt(v_i_1499_, v_upper_1514_);
if (v___x_1515_ == 0)
{
lean_object* v___x_1516_; uint8_t v___x_1517_; 
lean_dec(v_i_1499_);
v___x_1516_ = lean_unsigned_to_nat(0u);
v___x_1517_ = lean_nat_dec_eq(v_lower_1513_, v___x_1516_);
if (v___x_1517_ == 0)
{
lean_object* v___x_1518_; uint8_t v___x_1519_; lean_object* v___x_1520_; 
lean_inc(v_lower_1513_);
v___x_1518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1518_, 0, v_lower_1513_);
v___x_1519_ = 0;
lean_inc_ref(v_eType_1497_);
v___x_1520_ = l_Lean_Meta_forallMetaTelescopeReducing(v_eType_1497_, v___x_1518_, v___x_1519_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v_a_1521_; lean_object* v_snd_1522_; lean_object* v_snd_1523_; lean_object* v___x_1524_; 
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_a_1521_);
lean_dec_ref_known(v___x_1520_, 1);
v_snd_1522_ = lean_ctor_get(v_a_1521_, 1);
lean_inc(v_snd_1522_);
lean_dec(v_a_1521_);
v_snd_1523_ = lean_ctor_get(v_snd_1522_, 1);
lean_inc(v_snd_1523_);
lean_dec(v_snd_1522_);
v___x_1524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1524_, 0, v_snd_1523_);
v_conclusionType_x3f_1506_ = v___x_1524_;
v___y_1507_ = v_a_1500_;
v___y_1508_ = v_a_1501_;
v___y_1509_ = v_a_1502_;
v___y_1510_ = v_a_1503_;
goto v___jp_1505_;
}
else
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1532_; 
lean_dec_ref(v_eType_1497_);
lean_dec_ref(v_targetType_1496_);
lean_dec(v_term_x3f_1495_);
lean_dec(v_mvarId_1493_);
v_a_1525_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1527_ = v___x_1520_;
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1520_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1530_; 
if (v_isShared_1528_ == 0)
{
v___x_1530_ = v___x_1527_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_a_1525_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
}
else
{
lean_object* v___x_1533_; 
v___x_1533_ = lean_box(0);
v_conclusionType_x3f_1506_ = v___x_1533_;
v___y_1507_ = v_a_1500_;
v___y_1508_ = v_a_1501_;
v___y_1509_ = v_a_1502_;
v___y_1510_ = v_a_1503_;
goto v___jp_1505_;
}
}
else
{
lean_object* v___x_1534_; 
v___x_1534_ = l_Lean_Meta_saveState___redArg(v_a_1501_, v_a_1503_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v_a_1535_; lean_object* v___x_1536_; uint8_t v___x_1537_; lean_object* v___x_1538_; 
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_a_1535_);
lean_dec_ref_known(v___x_1534_, 1);
lean_inc(v_i_1499_);
v___x_1536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1536_, 0, v_i_1499_);
v___x_1537_ = 0;
lean_inc_ref(v_eType_1497_);
v___x_1538_ = l_Lean_Meta_forallMetaTelescopeReducing(v_eType_1497_, v___x_1536_, v___x_1537_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v_a_1539_; lean_object* v_snd_1540_; lean_object* v_fst_1541_; lean_object* v_fst_1542_; lean_object* v_snd_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1581_; 
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
lean_inc(v_a_1539_);
lean_dec_ref_known(v___x_1538_, 1);
v_snd_1540_ = lean_ctor_get(v_a_1539_, 1);
lean_inc(v_snd_1540_);
v_fst_1541_ = lean_ctor_get(v_a_1539_, 0);
lean_inc(v_fst_1541_);
lean_dec(v_a_1539_);
v_fst_1542_ = lean_ctor_get(v_snd_1540_, 0);
v_snd_1543_ = lean_ctor_get(v_snd_1540_, 1);
v_isSharedCheck_1581_ = !lean_is_exclusive(v_snd_1540_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1545_ = v_snd_1540_;
v_isShared_1546_ = v_isSharedCheck_1581_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_snd_1543_);
lean_inc(v_fst_1542_);
lean_dec(v_snd_1540_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1581_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
uint8_t v_approx_1547_; lean_object* v___x_1548_; 
v_approx_1547_ = lean_ctor_get_uint8(v_cfg_1494_, 3);
lean_inc_ref(v_targetType_1496_);
v___x_1548_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_approx_1547_, v_snd_1543_, v_targetType_1496_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1572_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1551_ = v___x_1548_;
v_isShared_1552_ = v_isSharedCheck_1572_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1548_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1572_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
uint8_t v___x_1553_; 
v___x_1553_ = lean_unbox(v_a_1549_);
lean_dec(v_a_1549_);
if (v___x_1553_ == 0)
{
lean_object* v___x_1554_; 
lean_del_object(v___x_1551_);
lean_del_object(v___x_1545_);
lean_dec(v_fst_1542_);
lean_dec(v_fst_1541_);
v___x_1554_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1535_, v_a_1501_, v_a_1503_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
lean_dec_ref_known(v___x_1554_, 1);
v___x_1555_ = lean_unsigned_to_nat(1u);
v___x_1556_ = lean_nat_add(v_i_1499_, v___x_1555_);
lean_dec(v_i_1499_);
v_i_1499_ = v___x_1556_;
goto _start;
}
else
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
lean_dec(v_i_1499_);
lean_dec_ref(v_eType_1497_);
lean_dec_ref(v_targetType_1496_);
lean_dec(v_term_x3f_1495_);
lean_dec(v_mvarId_1493_);
v_a_1558_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1560_ = v___x_1554_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1554_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
v___x_1563_ = v___x_1560_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1558_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
else
{
lean_object* v___x_1567_; 
lean_dec(v_a_1535_);
lean_dec(v_i_1499_);
lean_dec_ref(v_eType_1497_);
lean_dec_ref(v_targetType_1496_);
lean_dec(v_term_x3f_1495_);
lean_dec(v_mvarId_1493_);
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 1, v_fst_1542_);
lean_ctor_set(v___x_1545_, 0, v_fst_1541_);
v___x_1567_ = v___x_1545_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_fst_1541_);
lean_ctor_set(v_reuseFailAlloc_1571_, 1, v_fst_1542_);
v___x_1567_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
lean_object* v___x_1569_; 
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 0, v___x_1567_);
v___x_1569_ = v___x_1551_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1567_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
}
else
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
lean_del_object(v___x_1545_);
lean_dec(v_fst_1542_);
lean_dec(v_fst_1541_);
lean_dec(v_a_1535_);
lean_dec(v_i_1499_);
lean_dec_ref(v_eType_1497_);
lean_dec_ref(v_targetType_1496_);
lean_dec(v_term_x3f_1495_);
lean_dec(v_mvarId_1493_);
v_a_1573_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1548_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1548_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1576_ == 0)
{
v___x_1578_ = v___x_1575_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_a_1573_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
}
else
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
lean_dec(v_a_1535_);
lean_dec(v_i_1499_);
lean_dec_ref(v_eType_1497_);
lean_dec_ref(v_targetType_1496_);
lean_dec(v_term_x3f_1495_);
lean_dec(v_mvarId_1493_);
v_a_1582_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1538_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1538_);
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
lean_dec(v_i_1499_);
lean_dec_ref(v_eType_1497_);
lean_dec_ref(v_targetType_1496_);
lean_dec(v_term_x3f_1495_);
lean_dec(v_mvarId_1493_);
v_a_1590_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1592_ = v___x_1534_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1534_);
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
v___jp_1505_:
{
uint8_t v_approx_1511_; lean_object* v___x_1512_; 
v_approx_1511_ = lean_ctor_get_uint8(v_cfg_1494_, 3);
v___x_1512_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_1493_, v_eType_1497_, v_conclusionType_x3f_1506_, v_targetType_1496_, v_term_x3f_1495_, v_approx_1511_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
return v___x_1512_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1493_ = stack[0].m_obj;
lean_object* v_cfg_1494_ = stack[1].m_obj;
lean_object* v_term_x3f_1495_ = stack[2].m_obj;
lean_object* v_targetType_1496_ = stack[3].m_obj;
lean_object* v_eType_1497_ = stack[4].m_obj;
lean_object* v_rangeNumArgs_1498_ = stack[5].m_obj;
lean_object* v_i_1499_ = stack[6].m_obj;
lean_object* v_a_1500_ = stack[7].m_obj;
lean_object* v_a_1501_ = stack[8].m_obj;
lean_object* v_a_1502_ = stack[9].m_obj;
lean_object* v_a_1503_ = stack[10].m_obj;
lean_object* v_res_1598_;
v_res_1598_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(v_mvarId_1493_, v_cfg_1494_, v_term_x3f_1495_, v_targetType_1496_, v_eType_1497_, v_rangeNumArgs_1498_, v_i_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_);
stack->m_obj
 = v_res_1598_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go___boxed(lean_object* v_mvarId_1599_, lean_object* v_cfg_1600_, lean_object* v_term_x3f_1601_, lean_object* v_targetType_1602_, lean_object* v_eType_1603_, lean_object* v_rangeNumArgs_1604_, lean_object* v_i_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(v_mvarId_1599_, v_cfg_1600_, v_term_x3f_1601_, v_targetType_1602_, v_eType_1603_, v_rangeNumArgs_1604_, v_i_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_);
lean_dec(v_a_1609_);
lean_dec_ref(v_a_1608_);
lean_dec(v_a_1607_);
lean_dec_ref(v_a_1606_);
lean_dec_ref(v_rangeNumArgs_1604_);
lean_dec_ref(v_cfg_1600_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go_match__1_splitter___redArg(lean_object* v_x_1612_, lean_object* v_h__1_1613_){
_start:
{
lean_object* v_snd_1614_; lean_object* v_fst_1615_; lean_object* v_fst_1616_; lean_object* v_snd_1617_; lean_object* v___x_1618_; 
v_snd_1614_ = lean_ctor_get(v_x_1612_, 1);
lean_inc(v_snd_1614_);
v_fst_1615_ = lean_ctor_get(v_x_1612_, 0);
lean_inc(v_fst_1615_);
lean_dec_ref(v_x_1612_);
v_fst_1616_ = lean_ctor_get(v_snd_1614_, 0);
lean_inc(v_fst_1616_);
v_snd_1617_ = lean_ctor_get(v_snd_1614_, 1);
lean_inc(v_snd_1617_);
lean_dec(v_snd_1614_);
v___x_1618_ = lean_apply_3(v_h__1_1613_, v_fst_1615_, v_fst_1616_, v_snd_1617_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go_match__1_splitter(lean_object* v_motive_1619_, lean_object* v_x_1620_, lean_object* v_h__1_1621_){
_start:
{
lean_object* v_snd_1622_; lean_object* v_fst_1623_; lean_object* v_fst_1624_; lean_object* v_snd_1625_; lean_object* v___x_1626_; 
v_snd_1622_ = lean_ctor_get(v_x_1620_, 1);
lean_inc(v_snd_1622_);
v_fst_1623_ = lean_ctor_get(v_x_1620_, 0);
lean_inc(v_fst_1623_);
lean_dec_ref(v_x_1620_);
v_fst_1624_ = lean_ctor_get(v_snd_1622_, 0);
lean_inc(v_fst_1624_);
v_snd_1625_ = lean_ctor_get(v_snd_1622_, 1);
lean_inc(v_snd_1625_);
lean_dec(v_snd_1622_);
v___x_1626_ = lean_apply_3(v_h__1_1621_, v_fst_1623_, v_fst_1624_, v_snd_1625_);
return v___x_1626_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(lean_object* v_e_1627_, lean_object* v___y_1628_){
_start:
{
uint8_t v___x_1630_; 
v___x_1630_ = l_Lean_Expr_hasMVar(v_e_1627_);
if (v___x_1630_ == 0)
{
lean_object* v___x_1631_; 
v___x_1631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1631_, 0, v_e_1627_);
return v___x_1631_;
}
else
{
lean_object* v___x_1632_; lean_object* v_mctx_1633_; lean_object* v___x_1634_; lean_object* v_fst_1635_; lean_object* v_snd_1636_; lean_object* v___x_1637_; lean_object* v_cache_1638_; lean_object* v_zetaDeltaFVarIds_1639_; lean_object* v_postponed_1640_; lean_object* v_diag_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1650_; 
v___x_1632_ = lean_st_ref_get(v___y_1628_);
v_mctx_1633_ = lean_ctor_get(v___x_1632_, 0);
lean_inc_ref(v_mctx_1633_);
lean_dec(v___x_1632_);
v___x_1634_ = l_Lean_instantiateMVarsCore(v_mctx_1633_, v_e_1627_);
v_fst_1635_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_fst_1635_);
v_snd_1636_ = lean_ctor_get(v___x_1634_, 1);
lean_inc(v_snd_1636_);
lean_dec_ref(v___x_1634_);
v___x_1637_ = lean_st_ref_take(v___y_1628_);
v_cache_1638_ = lean_ctor_get(v___x_1637_, 1);
v_zetaDeltaFVarIds_1639_ = lean_ctor_get(v___x_1637_, 2);
v_postponed_1640_ = lean_ctor_get(v___x_1637_, 3);
v_diag_1641_ = lean_ctor_get(v___x_1637_, 4);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1650_ == 0)
{
lean_object* v_unused_1651_; 
v_unused_1651_ = lean_ctor_get(v___x_1637_, 0);
lean_dec(v_unused_1651_);
v___x_1643_ = v___x_1637_;
v_isShared_1644_ = v_isSharedCheck_1650_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_diag_1641_);
lean_inc(v_postponed_1640_);
lean_inc(v_zetaDeltaFVarIds_1639_);
lean_inc(v_cache_1638_);
lean_dec(v___x_1637_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1650_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1646_; 
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 0, v_snd_1636_);
v___x_1646_ = v___x_1643_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_snd_1636_);
lean_ctor_set(v_reuseFailAlloc_1649_, 1, v_cache_1638_);
lean_ctor_set(v_reuseFailAlloc_1649_, 2, v_zetaDeltaFVarIds_1639_);
lean_ctor_set(v_reuseFailAlloc_1649_, 3, v_postponed_1640_);
lean_ctor_set(v_reuseFailAlloc_1649_, 4, v_diag_1641_);
v___x_1646_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1647_ = lean_st_ref_put(v___y_1628_, v___x_1646_);
v___x_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1648_, 0, v_fst_1635_);
return v___x_1648_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1627_ = stack[0].m_obj;
lean_object* v___y_1628_ = stack[1].m_obj;
lean_object* v_res_1652_;
v_res_1652_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_1627_, v___y_1628_);
stack->m_obj
 = v_res_1652_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg___boxed(lean_object* v_e_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_1653_, v___y_1654_);
lean_dec(v___y_1654_);
return v_res_1656_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0(lean_object* v_e_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_1657_, v___y_1659_);
return v___x_1663_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1657_ = stack[0].m_obj;
lean_object* v___y_1658_ = stack[1].m_obj;
lean_object* v___y_1659_ = stack[2].m_obj;
lean_object* v___y_1660_ = stack[3].m_obj;
lean_object* v___y_1661_ = stack[4].m_obj;
lean_object* v_res_1664_;
v_res_1664_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0(v_e_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
stack->m_obj
 = v_res_1664_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___boxed(lean_object* v_e_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0(v_e_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
return v_res_1671_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(lean_object* v_mvarId_1672_, lean_object* v_x_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1672_, v_x_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1687_; 
v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1682_ = v___x_1679_;
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1679_);
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
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1695_; 
v_a_1688_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1690_ = v___x_1679_;
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1679_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1691_ == 0)
{
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1688_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1672_ = stack[0].m_obj;
lean_object* v_x_1673_ = stack[1].m_obj;
lean_object* v___y_1674_ = stack[2].m_obj;
lean_object* v___y_1675_ = stack[3].m_obj;
lean_object* v___y_1676_ = stack[4].m_obj;
lean_object* v___y_1677_ = stack[5].m_obj;
lean_object* v_res_1696_;
v_res_1696_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_1672_, v_x_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
stack->m_obj
 = v_res_1696_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg___boxed(lean_object* v_mvarId_1697_, lean_object* v_x_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_1697_, v_x_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
return v_res_1704_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6(lean_object* v_00_u03b1_1705_, lean_object* v_mvarId_1706_, lean_object* v_x_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_1706_, v_x_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
return v___x_1713_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1706_ = stack[1].m_obj;
lean_object* v_x_1707_ = stack[2].m_obj;
lean_object* v___y_1708_ = stack[3].m_obj;
lean_object* v___y_1709_ = stack[4].m_obj;
lean_object* v___y_1710_ = stack[5].m_obj;
lean_object* v___y_1711_ = stack[6].m_obj;
lean_object* v_res_1714_;
v_res_1714_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6(lean_box(0), v_mvarId_1706_, v_x_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
stack->m_obj
 = v_res_1714_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___boxed(lean_object* v_00_u03b1_1715_, lean_object* v_mvarId_1716_, lean_object* v_x_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6(v_00_u03b1_1715_, v_mvarId_1716_, v_x_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
return v_res_1723_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(lean_object* v_as_1724_, size_t v_i_1725_, size_t v_stop_1726_, lean_object* v_b_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v_a_1731_; uint8_t v___x_1735_; 
v___x_1735_ = lean_usize_dec_eq(v_i_1725_, v_stop_1726_);
if (v___x_1735_ == 0)
{
lean_object* v___x_1736_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1736_ = lean_array_uget_borrowed(v_as_1724_, v_i_1725_);
v___x_1739_ = l_Lean_Expr_mvarId_x21(v___x_1736_);
v___x_1740_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_1739_, v___y_1728_);
lean_dec(v___x_1739_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1741_; uint8_t v___x_1742_; 
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_a_1741_);
lean_dec_ref_known(v___x_1740_, 1);
v___x_1742_ = lean_unbox(v_a_1741_);
lean_dec(v_a_1741_);
if (v___x_1742_ == 0)
{
goto v___jp_1737_;
}
else
{
v_a_1731_ = v_b_1727_;
goto v___jp_1730_;
}
}
else
{
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1743_; uint8_t v___x_1744_; 
v_a_1743_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_a_1743_);
lean_dec_ref_known(v___x_1740_, 1);
v___x_1744_ = lean_unbox(v_a_1743_);
lean_dec(v_a_1743_);
if (v___x_1744_ == 0)
{
v_a_1731_ = v_b_1727_;
goto v___jp_1730_;
}
else
{
goto v___jp_1737_;
}
}
else
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1752_; 
lean_dec_ref(v_b_1727_);
v_a_1745_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1747_ = v___x_1740_;
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1740_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1750_; 
if (v_isShared_1748_ == 0)
{
v___x_1750_ = v___x_1747_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_a_1745_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
}
v___jp_1737_:
{
lean_object* v___x_1738_; 
lean_inc(v___x_1736_);
v___x_1738_ = lean_array_push(v_b_1727_, v___x_1736_);
v_a_1731_ = v___x_1738_;
goto v___jp_1730_;
}
}
else
{
lean_object* v___x_1753_; 
v___x_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1753_, 0, v_b_1727_);
return v___x_1753_;
}
v___jp_1730_:
{
size_t v___x_1732_; size_t v___x_1733_; 
v___x_1732_ = ((size_t)1ULL);
v___x_1733_ = lean_usize_add(v_i_1725_, v___x_1732_);
v_i_1725_ = v___x_1733_;
v_b_1727_ = v_a_1731_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1724_ = stack[0].m_obj;
size_t v_i_1725_ = stack[1].m_num;
size_t v_stop_1726_ = stack[2].m_num;
lean_object* v_b_1727_ = stack[3].m_obj;
lean_object* v___y_1728_ = stack[4].m_obj;
lean_object* v_res_1754_;
v_res_1754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_as_1724_, v_i_1725_, v_stop_1726_, v_b_1727_, v___y_1728_);
stack->m_obj
 = v_res_1754_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg___boxed(lean_object* v_as_1755_, lean_object* v_i_1756_, lean_object* v_stop_1757_, lean_object* v_b_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
size_t v_i_boxed_1761_; size_t v_stop_boxed_1762_; lean_object* v_res_1763_; 
v_i_boxed_1761_ = lean_unbox_usize(v_i_1756_);
lean_dec(v_i_1756_);
v_stop_boxed_1762_ = lean_unbox_usize(v_stop_1757_);
lean_dec(v_stop_1757_);
v_res_1763_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_as_1755_, v_i_boxed_1761_, v_stop_boxed_1762_, v_b_1758_, v___y_1759_);
lean_dec(v___y_1759_);
lean_dec_ref(v_as_1755_);
return v_res_1763_;
}
}
lean_object* l_List_forM___at___00Lean_MVarId_apply_spec__3(lean_object* v_as_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
if (lean_obj_tag(v_as_1764_) == 0)
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = lean_box(0);
v___x_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1770_);
return v___x_1771_;
}
else
{
lean_object* v_head_1772_; lean_object* v_tail_1773_; lean_object* v___x_1774_; 
v_head_1772_ = lean_ctor_get(v_as_1764_, 0);
lean_inc(v_head_1772_);
v_tail_1773_ = lean_ctor_get(v_as_1764_, 1);
lean_inc(v_tail_1773_);
lean_dec_ref_known(v_as_1764_, 2);
v___x_1774_ = l_Lean_MVarId_headBetaType(v_head_1772_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_dec_ref_known(v___x_1774_, 1);
v_as_1764_ = v_tail_1773_;
goto _start;
}
else
{
lean_dec(v_tail_1773_);
return v___x_1774_;
}
}
}
}
LEAN_EXPORT void l_List_forM___at___00Lean_MVarId_apply_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1764_ = stack[0].m_obj;
lean_object* v___y_1765_ = stack[1].m_obj;
lean_object* v___y_1766_ = stack[2].m_obj;
lean_object* v___y_1767_ = stack[3].m_obj;
lean_object* v___y_1768_ = stack[4].m_obj;
lean_object* v_res_1776_;
v_res_1776_ = l_List_forM___at___00Lean_MVarId_apply_spec__3(v_as_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
stack->m_obj
 = v_res_1776_;
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_apply_spec__3___boxed(lean_object* v_as_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l_List_forM___at___00Lean_MVarId_apply_spec__3(v_as_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(lean_object* v_x_1784_, lean_object* v_x_1785_, lean_object* v_x_1786_, lean_object* v_x_1787_){
_start:
{
lean_object* v_ks_1788_; lean_object* v_vs_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1813_; 
v_ks_1788_ = lean_ctor_get(v_x_1784_, 0);
v_vs_1789_ = lean_ctor_get(v_x_1784_, 1);
v_isSharedCheck_1813_ = !lean_is_exclusive(v_x_1784_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1791_ = v_x_1784_;
v_isShared_1792_ = v_isSharedCheck_1813_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_vs_1789_);
lean_inc(v_ks_1788_);
lean_dec(v_x_1784_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1813_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1793_; uint8_t v___x_1794_; 
v___x_1793_ = lean_array_get_size(v_ks_1788_);
v___x_1794_ = lean_nat_dec_lt(v_x_1785_, v___x_1793_);
if (v___x_1794_ == 0)
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1798_; 
lean_dec(v_x_1785_);
v___x_1795_ = lean_array_push(v_ks_1788_, v_x_1786_);
v___x_1796_ = lean_array_push(v_vs_1789_, v_x_1787_);
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 1, v___x_1796_);
lean_ctor_set(v___x_1791_, 0, v___x_1795_);
v___x_1798_ = v___x_1791_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v___x_1795_);
lean_ctor_set(v_reuseFailAlloc_1799_, 1, v___x_1796_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
else
{
lean_object* v_k_x27_1800_; uint8_t v___x_1801_; 
v_k_x27_1800_ = lean_array_fget_borrowed(v_ks_1788_, v_x_1785_);
v___x_1801_ = l_Lean_instBEqMVarId_beq(v_x_1786_, v_k_x27_1800_);
if (v___x_1801_ == 0)
{
lean_object* v___x_1803_; 
if (v_isShared_1792_ == 0)
{
v___x_1803_ = v___x_1791_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_ks_1788_);
lean_ctor_set(v_reuseFailAlloc_1807_, 1, v_vs_1789_);
v___x_1803_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1804_ = lean_unsigned_to_nat(1u);
v___x_1805_ = lean_nat_add(v_x_1785_, v___x_1804_);
lean_dec(v_x_1785_);
v_x_1784_ = v___x_1803_;
v_x_1785_ = v___x_1805_;
goto _start;
}
}
else
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1811_; 
v___x_1808_ = lean_array_fset(v_ks_1788_, v_x_1785_, v_x_1786_);
v___x_1809_ = lean_array_fset(v_vs_1789_, v_x_1785_, v_x_1787_);
lean_dec(v_x_1785_);
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 1, v___x_1809_);
lean_ctor_set(v___x_1791_, 0, v___x_1808_);
v___x_1811_ = v___x_1791_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v___x_1808_);
lean_ctor_set(v_reuseFailAlloc_1812_, 1, v___x_1809_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(lean_object* v_n_1814_, lean_object* v_k_1815_, lean_object* v_v_1816_){
_start:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1817_ = lean_unsigned_to_nat(0u);
v___x_1818_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(v_n_1814_, v___x_1817_, v_k_1815_, v_v_1816_);
return v___x_1818_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1819_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(lean_object* v_x_1820_, size_t v_x_1821_, size_t v_x_1822_, lean_object* v_x_1823_, lean_object* v_x_1824_){
_start:
{
if (lean_obj_tag(v_x_1820_) == 0)
{
lean_object* v_es_1825_; size_t v___x_1826_; size_t v___x_1827_; lean_object* v_j_1828_; lean_object* v___x_1829_; uint8_t v___x_1830_; 
v_es_1825_ = lean_ctor_get(v_x_1820_, 0);
v___x_1826_ = ((size_t)31ULL);
v___x_1827_ = lean_usize_land(v_x_1821_, v___x_1826_);
v_j_1828_ = lean_usize_to_nat(v___x_1827_);
v___x_1829_ = lean_array_get_size(v_es_1825_);
v___x_1830_ = lean_nat_dec_lt(v_j_1828_, v___x_1829_);
if (v___x_1830_ == 0)
{
lean_dec(v_j_1828_);
lean_dec(v_x_1824_);
lean_dec(v_x_1823_);
return v_x_1820_;
}
else
{
lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1869_; 
lean_inc_ref(v_es_1825_);
v_isSharedCheck_1869_ = !lean_is_exclusive(v_x_1820_);
if (v_isSharedCheck_1869_ == 0)
{
lean_object* v_unused_1870_; 
v_unused_1870_ = lean_ctor_get(v_x_1820_, 0);
lean_dec(v_unused_1870_);
v___x_1832_ = v_x_1820_;
v_isShared_1833_ = v_isSharedCheck_1869_;
goto v_resetjp_1831_;
}
else
{
lean_dec(v_x_1820_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1869_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v_v_1834_; lean_object* v___x_1835_; lean_object* v_xs_x27_1836_; lean_object* v___y_1838_; 
v_v_1834_ = lean_array_fget(v_es_1825_, v_j_1828_);
v___x_1835_ = lean_box(0);
v_xs_x27_1836_ = lean_array_fset(v_es_1825_, v_j_1828_, v___x_1835_);
switch(lean_obj_tag(v_v_1834_))
{
case 0:
{
lean_object* v_key_1843_; lean_object* v_val_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1854_; 
v_key_1843_ = lean_ctor_get(v_v_1834_, 0);
v_val_1844_ = lean_ctor_get(v_v_1834_, 1);
v_isSharedCheck_1854_ = !lean_is_exclusive(v_v_1834_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1846_ = v_v_1834_;
v_isShared_1847_ = v_isSharedCheck_1854_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_val_1844_);
lean_inc(v_key_1843_);
lean_dec(v_v_1834_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1854_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
uint8_t v___x_1848_; 
v___x_1848_ = l_Lean_instBEqMVarId_beq(v_x_1823_, v_key_1843_);
if (v___x_1848_ == 0)
{
lean_object* v___x_1849_; lean_object* v___x_1850_; 
lean_del_object(v___x_1846_);
v___x_1849_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1843_, v_val_1844_, v_x_1823_, v_x_1824_);
v___x_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1849_);
v___y_1838_ = v___x_1850_;
goto v___jp_1837_;
}
else
{
lean_object* v___x_1852_; 
lean_dec(v_val_1844_);
lean_dec(v_key_1843_);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 1, v_x_1824_);
lean_ctor_set(v___x_1846_, 0, v_x_1823_);
v___x_1852_ = v___x_1846_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_x_1823_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v_x_1824_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
v___y_1838_ = v___x_1852_;
goto v___jp_1837_;
}
}
}
}
case 1:
{
lean_object* v_node_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1867_; 
v_node_1855_ = lean_ctor_get(v_v_1834_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v_v_1834_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1857_ = v_v_1834_;
v_isShared_1858_ = v_isSharedCheck_1867_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_node_1855_);
lean_dec(v_v_1834_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1867_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
size_t v___x_1859_; size_t v___x_1860_; size_t v___x_1861_; size_t v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1865_; 
v___x_1859_ = ((size_t)5ULL);
v___x_1860_ = lean_usize_shift_right(v_x_1821_, v___x_1859_);
v___x_1861_ = ((size_t)1ULL);
v___x_1862_ = lean_usize_add(v_x_1822_, v___x_1861_);
v___x_1863_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_node_1855_, v___x_1860_, v___x_1862_, v_x_1823_, v_x_1824_);
if (v_isShared_1858_ == 0)
{
lean_ctor_set(v___x_1857_, 0, v___x_1863_);
v___x_1865_ = v___x_1857_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v___x_1863_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
v___y_1838_ = v___x_1865_;
goto v___jp_1837_;
}
}
}
default: 
{
lean_object* v___x_1868_; 
v___x_1868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1868_, 0, v_x_1823_);
lean_ctor_set(v___x_1868_, 1, v_x_1824_);
v___y_1838_ = v___x_1868_;
goto v___jp_1837_;
}
}
v___jp_1837_:
{
lean_object* v___x_1839_; lean_object* v___x_1841_; 
v___x_1839_ = lean_array_fset(v_xs_x27_1836_, v_j_1828_, v___y_1838_);
lean_dec(v_j_1828_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 0, v___x_1839_);
v___x_1841_ = v___x_1832_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1839_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
}
}
else
{
lean_object* v_ks_1871_; lean_object* v_vs_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1890_; 
v_ks_1871_ = lean_ctor_get(v_x_1820_, 0);
v_vs_1872_ = lean_ctor_get(v_x_1820_, 1);
v_isSharedCheck_1890_ = !lean_is_exclusive(v_x_1820_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1874_ = v_x_1820_;
v_isShared_1875_ = v_isSharedCheck_1890_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_vs_1872_);
lean_inc(v_ks_1871_);
lean_dec(v_x_1820_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1890_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1877_; 
if (v_isShared_1875_ == 0)
{
v___x_1877_ = v___x_1874_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_ks_1871_);
lean_ctor_set(v_reuseFailAlloc_1889_, 1, v_vs_1872_);
v___x_1877_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
lean_object* v_newNode_1878_; size_t v___x_1879_; uint8_t v___x_1880_; 
v_newNode_1878_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(v___x_1877_, v_x_1823_, v_x_1824_);
v___x_1879_ = ((size_t)7ULL);
v___x_1880_ = lean_usize_dec_le(v___x_1879_, v_x_1822_);
if (v___x_1880_ == 0)
{
lean_object* v___x_1881_; lean_object* v___x_1882_; uint8_t v___x_1883_; 
v___x_1881_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1878_);
v___x_1882_ = lean_unsigned_to_nat(4u);
v___x_1883_ = lean_nat_dec_lt(v___x_1881_, v___x_1882_);
lean_dec(v___x_1881_);
if (v___x_1883_ == 0)
{
lean_object* v_ks_1884_; lean_object* v_vs_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v_ks_1884_ = lean_ctor_get(v_newNode_1878_, 0);
lean_inc_ref(v_ks_1884_);
v_vs_1885_ = lean_ctor_get(v_newNode_1878_, 1);
lean_inc_ref(v_vs_1885_);
lean_dec_ref(v_newNode_1878_);
v___x_1886_ = lean_unsigned_to_nat(0u);
v___x_1887_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_1888_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_x_1822_, v_ks_1884_, v_vs_1885_, v___x_1886_, v___x_1887_);
lean_dec_ref(v_vs_1885_);
lean_dec_ref(v_ks_1884_);
return v___x_1888_;
}
else
{
return v_newNode_1878_;
}
}
else
{
return v_newNode_1878_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1820_ = stack[0].m_obj;
size_t v_x_1821_ = stack[1].m_num;
size_t v_x_1822_ = stack[2].m_num;
lean_object* v_x_1823_ = stack[3].m_obj;
lean_object* v_x_1824_ = stack[4].m_obj;
lean_object* v_res_1891_;
v_res_1891_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_1820_, v_x_1821_, v_x_1822_, v_x_1823_, v_x_1824_);
stack->m_obj
 = v_res_1891_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(size_t v_depth_1892_, lean_object* v_keys_1893_, lean_object* v_vals_1894_, lean_object* v_i_1895_, lean_object* v_entries_1896_){
_start:
{
lean_object* v___x_1897_; uint8_t v___x_1898_; 
v___x_1897_ = lean_array_get_size(v_keys_1893_);
v___x_1898_ = lean_nat_dec_lt(v_i_1895_, v___x_1897_);
if (v___x_1898_ == 0)
{
lean_dec(v_i_1895_);
return v_entries_1896_;
}
else
{
lean_object* v_k_1899_; lean_object* v_v_1900_; uint64_t v___x_1901_; size_t v_h_1902_; size_t v___x_1903_; lean_object* v___x_1904_; size_t v___x_1905_; size_t v___x_1906_; size_t v___x_1907_; size_t v_h_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v_k_1899_ = lean_array_fget_borrowed(v_keys_1893_, v_i_1895_);
v_v_1900_ = lean_array_fget_borrowed(v_vals_1894_, v_i_1895_);
v___x_1901_ = l_Lean_instHashableMVarId_hash(v_k_1899_);
v_h_1902_ = lean_uint64_to_usize(v___x_1901_);
v___x_1903_ = ((size_t)5ULL);
v___x_1904_ = lean_unsigned_to_nat(1u);
v___x_1905_ = ((size_t)1ULL);
v___x_1906_ = lean_usize_sub(v_depth_1892_, v___x_1905_);
v___x_1907_ = lean_usize_mul(v___x_1903_, v___x_1906_);
v_h_1908_ = lean_usize_shift_right(v_h_1902_, v___x_1907_);
v___x_1909_ = lean_nat_add(v_i_1895_, v___x_1904_);
lean_dec(v_i_1895_);
lean_inc(v_v_1900_);
lean_inc(v_k_1899_);
v___x_1910_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_entries_1896_, v_h_1908_, v_depth_1892_, v_k_1899_, v_v_1900_);
v_i_1895_ = v___x_1909_;
v_entries_1896_ = v___x_1910_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1892_ = stack[0].m_num;
lean_object* v_keys_1893_ = stack[1].m_obj;
lean_object* v_vals_1894_ = stack[2].m_obj;
lean_object* v_i_1895_ = stack[3].m_obj;
lean_object* v_entries_1896_ = stack[4].m_obj;
lean_object* v_res_1912_;
v_res_1912_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_depth_1892_, v_keys_1893_, v_vals_1894_, v_i_1895_, v_entries_1896_);
stack->m_obj
 = v_res_1912_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg___boxed(lean_object* v_depth_1913_, lean_object* v_keys_1914_, lean_object* v_vals_1915_, lean_object* v_i_1916_, lean_object* v_entries_1917_){
_start:
{
size_t v_depth_boxed_1918_; lean_object* v_res_1919_; 
v_depth_boxed_1918_ = lean_unbox_usize(v_depth_1913_);
lean_dec(v_depth_1913_);
v_res_1919_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_depth_boxed_1918_, v_keys_1914_, v_vals_1915_, v_i_1916_, v_entries_1917_);
lean_dec_ref(v_vals_1915_);
lean_dec_ref(v_keys_1914_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_1920_, lean_object* v_x_1921_, lean_object* v_x_1922_, lean_object* v_x_1923_, lean_object* v_x_1924_){
_start:
{
size_t v_x_7235__boxed_1925_; size_t v_x_7236__boxed_1926_; lean_object* v_res_1927_; 
v_x_7235__boxed_1925_ = lean_unbox_usize(v_x_1921_);
lean_dec(v_x_1921_);
v_x_7236__boxed_1926_ = lean_unbox_usize(v_x_1922_);
lean_dec(v_x_1922_);
v_res_1927_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_1920_, v_x_7235__boxed_1925_, v_x_7236__boxed_1926_, v_x_1923_, v_x_1924_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(lean_object* v_x_1928_, lean_object* v_x_1929_, lean_object* v_x_1930_){
_start:
{
uint64_t v___x_1931_; size_t v___x_1932_; size_t v___x_1933_; lean_object* v___x_1934_; 
v___x_1931_ = l_Lean_instHashableMVarId_hash(v_x_1929_);
v___x_1932_ = lean_uint64_to_usize(v___x_1931_);
v___x_1933_ = ((size_t)1ULL);
v___x_1934_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_1928_, v___x_1932_, v___x_1933_, v_x_1929_, v_x_1930_);
return v___x_1934_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(lean_object* v_mvarId_1935_, lean_object* v_val_1936_, lean_object* v___y_1937_){
_start:
{
lean_object* v___x_1939_; lean_object* v_mctx_1940_; lean_object* v_cache_1941_; lean_object* v_zetaDeltaFVarIds_1942_; lean_object* v_postponed_1943_; lean_object* v_diag_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1974_; 
v___x_1939_ = lean_st_ref_take(v___y_1937_);
v_mctx_1940_ = lean_ctor_get(v___x_1939_, 0);
v_cache_1941_ = lean_ctor_get(v___x_1939_, 1);
v_zetaDeltaFVarIds_1942_ = lean_ctor_get(v___x_1939_, 2);
v_postponed_1943_ = lean_ctor_get(v___x_1939_, 3);
v_diag_1944_ = lean_ctor_get(v___x_1939_, 4);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1946_ = v___x_1939_;
v_isShared_1947_ = v_isSharedCheck_1974_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_diag_1944_);
lean_inc(v_postponed_1943_);
lean_inc(v_zetaDeltaFVarIds_1942_);
lean_inc(v_cache_1941_);
lean_inc(v_mctx_1940_);
lean_dec(v___x_1939_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1974_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v_depth_1948_; lean_object* v_levelAssignDepth_1949_; lean_object* v_lmvarCounter_1950_; lean_object* v_mvarCounter_1951_; lean_object* v_lDecls_1952_; lean_object* v_decls_1953_; lean_object* v_userNames_1954_; lean_object* v_lAssignment_1955_; lean_object* v_eAssignment_1956_; lean_object* v_dAssignment_1957_; lean_object* v_instanceTypedMVars_1958_; lean_object* v_synthNormMemo_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1973_; 
v_depth_1948_ = lean_ctor_get(v_mctx_1940_, 0);
v_levelAssignDepth_1949_ = lean_ctor_get(v_mctx_1940_, 1);
v_lmvarCounter_1950_ = lean_ctor_get(v_mctx_1940_, 2);
v_mvarCounter_1951_ = lean_ctor_get(v_mctx_1940_, 3);
v_lDecls_1952_ = lean_ctor_get(v_mctx_1940_, 4);
v_decls_1953_ = lean_ctor_get(v_mctx_1940_, 5);
v_userNames_1954_ = lean_ctor_get(v_mctx_1940_, 6);
v_lAssignment_1955_ = lean_ctor_get(v_mctx_1940_, 7);
v_eAssignment_1956_ = lean_ctor_get(v_mctx_1940_, 8);
v_dAssignment_1957_ = lean_ctor_get(v_mctx_1940_, 9);
v_instanceTypedMVars_1958_ = lean_ctor_get(v_mctx_1940_, 10);
v_synthNormMemo_1959_ = lean_ctor_get(v_mctx_1940_, 11);
v_isSharedCheck_1973_ = !lean_is_exclusive(v_mctx_1940_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1961_ = v_mctx_1940_;
v_isShared_1962_ = v_isSharedCheck_1973_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_synthNormMemo_1959_);
lean_inc(v_instanceTypedMVars_1958_);
lean_inc(v_dAssignment_1957_);
lean_inc(v_eAssignment_1956_);
lean_inc(v_lAssignment_1955_);
lean_inc(v_userNames_1954_);
lean_inc(v_decls_1953_);
lean_inc(v_lDecls_1952_);
lean_inc(v_mvarCounter_1951_);
lean_inc(v_lmvarCounter_1950_);
lean_inc(v_levelAssignDepth_1949_);
lean_inc(v_depth_1948_);
lean_dec(v_mctx_1940_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1973_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1966_; 
v___x_1963_ = lean_box(0);
v___x_1964_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(v_eAssignment_1956_, v_mvarId_1935_, v_val_1936_);
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 8, v___x_1964_);
v___x_1966_ = v___x_1961_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_depth_1948_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v_levelAssignDepth_1949_);
lean_ctor_set(v_reuseFailAlloc_1972_, 2, v_lmvarCounter_1950_);
lean_ctor_set(v_reuseFailAlloc_1972_, 3, v_mvarCounter_1951_);
lean_ctor_set(v_reuseFailAlloc_1972_, 4, v_lDecls_1952_);
lean_ctor_set(v_reuseFailAlloc_1972_, 5, v_decls_1953_);
lean_ctor_set(v_reuseFailAlloc_1972_, 6, v_userNames_1954_);
lean_ctor_set(v_reuseFailAlloc_1972_, 7, v_lAssignment_1955_);
lean_ctor_set(v_reuseFailAlloc_1972_, 8, v___x_1964_);
lean_ctor_set(v_reuseFailAlloc_1972_, 9, v_dAssignment_1957_);
lean_ctor_set(v_reuseFailAlloc_1972_, 10, v_instanceTypedMVars_1958_);
lean_ctor_set(v_reuseFailAlloc_1972_, 11, v_synthNormMemo_1959_);
v___x_1966_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
lean_object* v___x_1968_; 
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 0, v___x_1966_);
v___x_1968_ = v___x_1946_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1966_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v_cache_1941_);
lean_ctor_set(v_reuseFailAlloc_1971_, 2, v_zetaDeltaFVarIds_1942_);
lean_ctor_set(v_reuseFailAlloc_1971_, 3, v_postponed_1943_);
lean_ctor_set(v_reuseFailAlloc_1971_, 4, v_diag_1944_);
v___x_1968_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1969_ = lean_st_ref_put(v___y_1937_, v___x_1968_);
v___x_1970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1963_);
return v___x_1970_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1935_ = stack[0].m_obj;
lean_object* v_val_1936_ = stack[1].m_obj;
lean_object* v___y_1937_ = stack[2].m_obj;
lean_object* v_res_1975_;
v_res_1975_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_1935_, v_val_1936_, v___y_1937_);
stack->m_obj
 = v_res_1975_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg___boxed(lean_object* v_mvarId_1976_, lean_object* v_val_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_1976_, v_val_1977_, v___y_1978_);
lean_dec(v___y_1978_);
return v_res_1980_;
}
}
uint8_t l_List_elem___at___00Lean_MVarId_apply_spec__2(lean_object* v_a_1981_, lean_object* v_x_1982_){
_start:
{
if (lean_obj_tag(v_x_1982_) == 0)
{
uint8_t v___x_1983_; 
v___x_1983_ = 0;
return v___x_1983_;
}
else
{
lean_object* v_head_1984_; lean_object* v_tail_1985_; uint8_t v___x_1986_; 
v_head_1984_ = lean_ctor_get(v_x_1982_, 0);
v_tail_1985_ = lean_ctor_get(v_x_1982_, 1);
v___x_1986_ = l_Lean_instBEqMVarId_beq(v_a_1981_, v_head_1984_);
if (v___x_1986_ == 0)
{
v_x_1982_ = v_tail_1985_;
goto _start;
}
else
{
return v___x_1986_;
}
}
}
}
LEAN_EXPORT void l_List_elem___at___00Lean_MVarId_apply_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1981_ = stack[0].m_obj;
lean_object* v_x_1982_ = stack[1].m_obj;
uint8_t v_res_1988_;
v_res_1988_ = l_List_elem___at___00Lean_MVarId_apply_spec__2(v_a_1981_, v_x_1982_);
stack->m_num = v_res_1988_;
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_MVarId_apply_spec__2___boxed(lean_object* v_a_1989_, lean_object* v_x_1990_){
_start:
{
uint8_t v_res_1991_; lean_object* v_r_1992_; 
v_res_1991_ = l_List_elem___at___00Lean_MVarId_apply_spec__2(v_a_1989_, v_x_1990_);
lean_dec(v_x_1990_);
lean_dec(v_a_1989_);
v_r_1992_ = lean_box(v_res_1991_);
return v_r_1992_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(lean_object* v_a_1993_, lean_object* v_as_1994_, size_t v_i_1995_, size_t v_stop_1996_, lean_object* v_b_1997_){
_start:
{
lean_object* v___y_1999_; uint8_t v___x_2003_; 
v___x_2003_ = lean_usize_dec_eq(v_i_1995_, v_stop_1996_);
if (v___x_2003_ == 0)
{
lean_object* v___x_2004_; uint8_t v___x_2005_; 
v___x_2004_ = lean_array_uget_borrowed(v_as_1994_, v_i_1995_);
v___x_2005_ = l_List_elem___at___00Lean_MVarId_apply_spec__2(v___x_2004_, v_a_1993_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2006_; 
lean_inc(v___x_2004_);
v___x_2006_ = lean_array_push(v_b_1997_, v___x_2004_);
v___y_1999_ = v___x_2006_;
goto v___jp_1998_;
}
else
{
v___y_1999_ = v_b_1997_;
goto v___jp_1998_;
}
}
else
{
return v_b_1997_;
}
v___jp_1998_:
{
size_t v___x_2000_; size_t v___x_2001_; 
v___x_2000_ = ((size_t)1ULL);
v___x_2001_ = lean_usize_add(v_i_1995_, v___x_2000_);
v_i_1995_ = v___x_2001_;
v_b_1997_ = v___y_1999_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1993_ = stack[0].m_obj;
lean_object* v_as_1994_ = stack[1].m_obj;
size_t v_i_1995_ = stack[2].m_num;
size_t v_stop_1996_ = stack[3].m_num;
lean_object* v_b_1997_ = stack[4].m_obj;
lean_object* v_res_2007_;
v_res_2007_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_1993_, v_as_1994_, v_i_1995_, v_stop_1996_, v_b_1997_);
stack->m_obj
 = v_res_2007_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4___boxed(lean_object* v_a_2008_, lean_object* v_as_2009_, lean_object* v_i_2010_, lean_object* v_stop_2011_, lean_object* v_b_2012_){
_start:
{
size_t v_i_boxed_2013_; size_t v_stop_boxed_2014_; lean_object* v_res_2015_; 
v_i_boxed_2013_ = lean_unbox_usize(v_i_2010_);
lean_dec(v_i_2010_);
v_stop_boxed_2014_ = lean_unbox_usize(v_stop_2011_);
lean_dec(v_stop_2011_);
v_res_2015_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_2008_, v_as_2009_, v_i_boxed_2013_, v_stop_boxed_2014_, v_b_2012_);
lean_dec_ref(v_as_2009_);
lean_dec(v_a_2008_);
return v_res_2015_;
}
}
lean_object* l_Lean_MVarId_apply___lam__0(lean_object* v_mvarId_2016_, lean_object* v___x_2017_, lean_object* v_e_2018_, lean_object* v_cfg_2019_, lean_object* v_term_x3f_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v___y_2027_; lean_object* v___y_2028_; lean_object* v___y_2029_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v___y_2032_; uint8_t v___y_2053_; lean_object* v___y_2054_; lean_object* v___y_2055_; lean_object* v___y_2056_; lean_object* v___y_2057_; lean_object* v___y_2058_; lean_object* v___y_2059_; lean_object* v___y_2060_; lean_object* v_a_2061_; uint8_t v___y_2094_; lean_object* v___y_2095_; lean_object* v___y_2096_; lean_object* v___y_2097_; lean_object* v___y_2098_; lean_object* v___y_2099_; lean_object* v___y_2100_; lean_object* v___y_2101_; lean_object* v___y_2102_; lean_object* v___x_2112_; 
lean_inc(v___x_2017_);
lean_inc(v_mvarId_2016_);
v___x_2112_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2016_, v___x_2017_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v___x_2113_; 
lean_dec_ref_known(v___x_2112_, 1);
lean_inc(v_mvarId_2016_);
v___x_2113_ = l_Lean_MVarId_getType(v_mvarId_2016_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v_a_2114_; lean_object* v___x_2115_; 
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
lean_inc(v_a_2114_);
lean_dec_ref_known(v___x_2113_, 1);
lean_inc(v___y_2024_);
lean_inc_ref(v___y_2023_);
lean_inc(v___y_2022_);
lean_inc_ref(v___y_2021_);
lean_inc_ref(v_e_2018_);
v___x_2115_ = lean_infer_type(v_e_2018_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; lean_object* v_rangeNumArgs_2118_; lean_object* v_lower_2119_; lean_object* v___y_2120_; lean_object* v___y_2121_; lean_object* v___y_2122_; lean_object* v___y_2123_; lean_object* v___x_2163_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
lean_inc_n(v_a_2116_, 2);
lean_dec_ref_known(v___x_2115_, 1);
v___x_2163_ = l_Lean_Meta_getExpectedNumArgsAux(v_a_2116_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; lean_object* v_snd_2165_; uint8_t v___x_2166_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
lean_inc(v_a_2164_);
lean_dec_ref_known(v___x_2163_, 1);
v_snd_2165_ = lean_ctor_get(v_a_2164_, 1);
v___x_2166_ = lean_unbox(v_snd_2165_);
if (v___x_2166_ == 0)
{
lean_object* v_fst_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2187_; 
v_fst_2167_ = lean_ctor_get(v_a_2164_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v_a_2164_);
if (v_isSharedCheck_2187_ == 0)
{
lean_object* v_unused_2188_; 
v_unused_2188_ = lean_ctor_get(v_a_2164_, 1);
lean_dec(v_unused_2188_);
v___x_2169_ = v_a_2164_;
v_isShared_2170_ = v_isSharedCheck_2187_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_fst_2167_);
lean_dec(v_a_2164_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2187_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2171_; 
lean_inc(v_a_2114_);
v___x_2171_ = l_Lean_Meta_getExpectedNumArgs(v_a_2114_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v_a_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2177_; 
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
lean_inc(v_a_2172_);
lean_dec_ref_known(v___x_2171_, 1);
v___x_2173_ = lean_nat_sub(v_fst_2167_, v_a_2172_);
lean_dec(v_a_2172_);
v___x_2174_ = lean_unsigned_to_nat(1u);
v___x_2175_ = lean_nat_add(v_fst_2167_, v___x_2174_);
lean_dec(v_fst_2167_);
lean_inc(v___x_2173_);
if (v_isShared_2170_ == 0)
{
lean_ctor_set(v___x_2169_, 1, v___x_2175_);
lean_ctor_set(v___x_2169_, 0, v___x_2173_);
v___x_2177_ = v___x_2169_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2173_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v___x_2175_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
v_rangeNumArgs_2118_ = v___x_2177_;
v_lower_2119_ = v___x_2173_;
v___y_2120_ = v___y_2021_;
v___y_2121_ = v___y_2022_;
v___y_2122_ = v___y_2023_;
v___y_2123_ = v___y_2024_;
goto v___jp_2117_;
}
}
else
{
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2186_; 
lean_del_object(v___x_2169_);
lean_dec(v_fst_2167_);
lean_dec(v_a_2116_);
lean_dec(v_a_2114_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v_term_x3f_2020_);
lean_dec_ref(v_e_2018_);
lean_dec(v___x_2017_);
lean_dec(v_mvarId_2016_);
v_a_2179_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2181_ = v___x_2171_;
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2171_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2184_; 
if (v_isShared_2182_ == 0)
{
v___x_2184_ = v___x_2181_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_a_2179_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
}
else
{
lean_object* v_fst_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2198_; 
v_fst_2189_ = lean_ctor_get(v_a_2164_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v_a_2164_);
if (v_isSharedCheck_2198_ == 0)
{
lean_object* v_unused_2199_; 
v_unused_2199_ = lean_ctor_get(v_a_2164_, 1);
lean_dec(v_unused_2199_);
v___x_2191_ = v_a_2164_;
v_isShared_2192_ = v_isSharedCheck_2198_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_fst_2189_);
lean_dec(v_a_2164_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2198_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2196_; 
v___x_2193_ = lean_unsigned_to_nat(1u);
v___x_2194_ = lean_nat_add(v_fst_2189_, v___x_2193_);
lean_inc(v_fst_2189_);
if (v_isShared_2192_ == 0)
{
lean_ctor_set(v___x_2191_, 1, v___x_2194_);
v___x_2196_ = v___x_2191_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_fst_2189_);
lean_ctor_set(v_reuseFailAlloc_2197_, 1, v___x_2194_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
v_rangeNumArgs_2118_ = v___x_2196_;
v_lower_2119_ = v_fst_2189_;
v___y_2120_ = v___y_2021_;
v___y_2121_ = v___y_2022_;
v___y_2122_ = v___y_2023_;
v___y_2123_ = v___y_2024_;
goto v___jp_2117_;
}
}
}
}
else
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
lean_dec(v_a_2116_);
lean_dec(v_a_2114_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v_term_x3f_2020_);
lean_dec_ref(v_e_2018_);
lean_dec(v___x_2017_);
lean_dec(v_mvarId_2016_);
v_a_2200_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2202_ = v___x_2163_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2163_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_a_2200_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
v___jp_2117_:
{
lean_object* v___x_2124_; 
lean_inc(v_mvarId_2016_);
v___x_2124_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(v_mvarId_2016_, v_cfg_2019_, v_term_x3f_2020_, v_a_2114_, v_a_2116_, v_rangeNumArgs_2118_, v_lower_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
lean_dec_ref(v_rangeNumArgs_2118_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; lean_object* v_fst_2126_; lean_object* v_snd_2127_; uint8_t v_newGoals_2128_; uint8_t v_synthAssignedInstances_2129_; uint8_t v_allowSynthFailures_2130_; lean_object* v___x_2131_; 
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
lean_inc(v_a_2125_);
lean_dec_ref_known(v___x_2124_, 1);
v_fst_2126_ = lean_ctor_get(v_a_2125_, 0);
lean_inc(v_fst_2126_);
v_snd_2127_ = lean_ctor_get(v_a_2125_, 1);
lean_inc_n(v_snd_2127_, 2);
lean_dec(v_a_2125_);
v_newGoals_2128_ = lean_ctor_get_uint8(v_cfg_2019_, 0);
v_synthAssignedInstances_2129_ = lean_ctor_get_uint8(v_cfg_2019_, 1);
v_allowSynthFailures_2130_ = lean_ctor_get_uint8(v_cfg_2019_, 2);
lean_inc(v_mvarId_2016_);
v___x_2131_ = l_Lean_Meta_synthAppInstances(v___x_2017_, v_mvarId_2016_, v_fst_2126_, v_snd_2127_, v_synthAssignedInstances_2129_, v_allowSynthFailures_2130_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v___x_2132_; lean_object* v_a_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; uint8_t v___x_2139_; 
lean_dec_ref_known(v___x_2131_, 1);
v___x_2132_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_2018_, v___y_2121_);
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc_n(v_a_2133_, 2);
lean_dec_ref(v___x_2132_);
v___x_2134_ = l_Lean_mkAppN(v_a_2133_, v_fst_2126_);
lean_inc(v_mvarId_2016_);
v___x_2135_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2016_, v___x_2134_, v___y_2121_);
lean_dec_ref(v___x_2135_);
v___x_2136_ = lean_unsigned_to_nat(0u);
v___x_2137_ = lean_array_get_size(v_fst_2126_);
v___x_2138_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0));
v___x_2139_ = lean_nat_dec_lt(v___x_2136_, v___x_2137_);
if (v___x_2139_ == 0)
{
lean_dec(v_fst_2126_);
v___y_2053_ = v_newGoals_2128_;
v___y_2054_ = v___y_2121_;
v___y_2055_ = v___y_2120_;
v___y_2056_ = v___x_2136_;
v___y_2057_ = v___y_2122_;
v___y_2058_ = v___y_2123_;
v___y_2059_ = v_a_2133_;
v___y_2060_ = v_snd_2127_;
v_a_2061_ = v___x_2138_;
goto v___jp_2052_;
}
else
{
uint8_t v___x_2140_; 
v___x_2140_ = lean_nat_dec_le(v___x_2137_, v___x_2137_);
if (v___x_2140_ == 0)
{
if (v___x_2139_ == 0)
{
lean_dec(v_fst_2126_);
v___y_2053_ = v_newGoals_2128_;
v___y_2054_ = v___y_2121_;
v___y_2055_ = v___y_2120_;
v___y_2056_ = v___x_2136_;
v___y_2057_ = v___y_2122_;
v___y_2058_ = v___y_2123_;
v___y_2059_ = v_a_2133_;
v___y_2060_ = v_snd_2127_;
v_a_2061_ = v___x_2138_;
goto v___jp_2052_;
}
else
{
size_t v___x_2141_; size_t v___x_2142_; lean_object* v___x_2143_; 
v___x_2141_ = ((size_t)0ULL);
v___x_2142_ = lean_usize_of_nat(v___x_2137_);
v___x_2143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_fst_2126_, v___x_2141_, v___x_2142_, v___x_2138_, v___y_2121_);
lean_dec(v_fst_2126_);
v___y_2094_ = v_newGoals_2128_;
v___y_2095_ = v___y_2120_;
v___y_2096_ = v___y_2121_;
v___y_2097_ = v___x_2136_;
v___y_2098_ = v___y_2122_;
v___y_2099_ = v___y_2123_;
v___y_2100_ = v_snd_2127_;
v___y_2101_ = v_a_2133_;
v___y_2102_ = v___x_2143_;
goto v___jp_2093_;
}
}
else
{
size_t v___x_2144_; size_t v___x_2145_; lean_object* v___x_2146_; 
v___x_2144_ = ((size_t)0ULL);
v___x_2145_ = lean_usize_of_nat(v___x_2137_);
v___x_2146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_fst_2126_, v___x_2144_, v___x_2145_, v___x_2138_, v___y_2121_);
lean_dec(v_fst_2126_);
v___y_2094_ = v_newGoals_2128_;
v___y_2095_ = v___y_2120_;
v___y_2096_ = v___y_2121_;
v___y_2097_ = v___x_2136_;
v___y_2098_ = v___y_2122_;
v___y_2099_ = v___y_2123_;
v___y_2100_ = v_snd_2127_;
v___y_2101_ = v_a_2133_;
v___y_2102_ = v___x_2146_;
goto v___jp_2093_;
}
}
}
else
{
lean_object* v_a_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2154_; 
lean_dec(v_snd_2127_);
lean_dec(v_fst_2126_);
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2122_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
lean_dec_ref(v_e_2018_);
lean_dec(v_mvarId_2016_);
v_a_2147_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2149_ = v___x_2131_;
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_a_2147_);
lean_dec(v___x_2131_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2152_; 
if (v_isShared_2150_ == 0)
{
v___x_2152_ = v___x_2149_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_a_2147_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
}
else
{
lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2162_; 
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2122_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
lean_dec_ref(v_e_2018_);
lean_dec(v___x_2017_);
lean_dec(v_mvarId_2016_);
v_a_2155_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2157_ = v___x_2124_;
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_dec(v___x_2124_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2160_; 
if (v_isShared_2158_ == 0)
{
v___x_2160_ = v___x_2157_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_a_2155_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
}
}
else
{
lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2215_; 
lean_dec(v_a_2114_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v_term_x3f_2020_);
lean_dec_ref(v_e_2018_);
lean_dec(v___x_2017_);
lean_dec(v_mvarId_2016_);
v_a_2208_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2210_ = v___x_2115_;
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___x_2115_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2213_; 
if (v_isShared_2211_ == 0)
{
v___x_2213_ = v___x_2210_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_a_2208_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
else
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2223_; 
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v_term_x3f_2020_);
lean_dec_ref(v_e_2018_);
lean_dec(v___x_2017_);
lean_dec(v_mvarId_2016_);
v_a_2216_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2218_ = v___x_2113_;
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2113_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2221_; 
if (v_isShared_2219_ == 0)
{
v___x_2221_ = v___x_2218_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2216_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
else
{
lean_object* v_a_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2231_; 
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v_term_x3f_2020_);
lean_dec_ref(v_e_2018_);
lean_dec(v___x_2017_);
lean_dec(v_mvarId_2016_);
v_a_2224_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2226_ = v___x_2112_;
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_a_2224_);
lean_dec(v___x_2112_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2229_; 
if (v_isShared_2227_ == 0)
{
v___x_2229_ = v___x_2226_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_a_2224_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
v___jp_2026_:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2033_ = lean_array_to_list(v___y_2032_);
v___x_2034_ = l_List_appendTR___redArg(v___y_2027_, v___x_2033_);
lean_inc(v___x_2034_);
v___x_2035_ = l_List_forM___at___00Lean_MVarId_apply_spec__3(v___x_2034_, v___y_2029_, v___y_2028_, v___y_2030_, v___y_2031_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2029_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2042_ == 0)
{
lean_object* v_unused_2043_; 
v_unused_2043_ = lean_ctor_get(v___x_2035_, 0);
lean_dec(v_unused_2043_);
v___x_2037_ = v___x_2035_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_dec(v___x_2035_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 0, v___x_2034_);
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2034_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
else
{
lean_object* v_a_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2051_; 
lean_dec(v___x_2034_);
v_a_2044_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2046_ = v___x_2035_;
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_a_2044_);
lean_dec(v___x_2035_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2049_; 
if (v_isShared_2047_ == 0)
{
v___x_2049_ = v___x_2046_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_a_2044_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
}
v___jp_2052_:
{
lean_object* v___x_2062_; 
v___x_2062_ = l_Lean_Meta_appendParentTag(v_mvarId_2016_, v_a_2061_, v___y_2060_, v___y_2055_, v___y_2054_, v___y_2057_, v___y_2058_);
lean_dec_ref(v___y_2060_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v___x_2063_; 
lean_dec_ref_known(v___x_2062_, 1);
v___x_2063_ = l_Lean_Meta_getMVarsNoDelayed(v___y_2059_, v___y_2055_, v___y_2054_, v___y_2057_, v___y_2058_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v_a_2064_; lean_object* v___x_2065_; 
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_a_2064_);
lean_dec_ref_known(v___x_2063_, 1);
v___x_2065_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(v_a_2061_, v___y_2053_, v___y_2055_, v___y_2054_, v___y_2057_, v___y_2058_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v_a_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; uint8_t v___x_2069_; 
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc(v_a_2066_);
lean_dec_ref_known(v___x_2065_, 1);
v___x_2067_ = lean_array_get_size(v_a_2064_);
v___x_2068_ = lean_mk_empty_array_with_capacity(v___y_2056_);
v___x_2069_ = lean_nat_dec_lt(v___y_2056_, v___x_2067_);
if (v___x_2069_ == 0)
{
lean_dec(v_a_2064_);
v___y_2027_ = v_a_2066_;
v___y_2028_ = v___y_2054_;
v___y_2029_ = v___y_2055_;
v___y_2030_ = v___y_2057_;
v___y_2031_ = v___y_2058_;
v___y_2032_ = v___x_2068_;
goto v___jp_2026_;
}
else
{
uint8_t v___x_2070_; 
v___x_2070_ = lean_nat_dec_le(v___x_2067_, v___x_2067_);
if (v___x_2070_ == 0)
{
if (v___x_2069_ == 0)
{
lean_dec(v_a_2064_);
v___y_2027_ = v_a_2066_;
v___y_2028_ = v___y_2054_;
v___y_2029_ = v___y_2055_;
v___y_2030_ = v___y_2057_;
v___y_2031_ = v___y_2058_;
v___y_2032_ = v___x_2068_;
goto v___jp_2026_;
}
else
{
size_t v___x_2071_; size_t v___x_2072_; lean_object* v___x_2073_; 
v___x_2071_ = ((size_t)0ULL);
v___x_2072_ = lean_usize_of_nat(v___x_2067_);
v___x_2073_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_2066_, v_a_2064_, v___x_2071_, v___x_2072_, v___x_2068_);
lean_dec(v_a_2064_);
v___y_2027_ = v_a_2066_;
v___y_2028_ = v___y_2054_;
v___y_2029_ = v___y_2055_;
v___y_2030_ = v___y_2057_;
v___y_2031_ = v___y_2058_;
v___y_2032_ = v___x_2073_;
goto v___jp_2026_;
}
}
else
{
size_t v___x_2074_; size_t v___x_2075_; lean_object* v___x_2076_; 
v___x_2074_ = ((size_t)0ULL);
v___x_2075_ = lean_usize_of_nat(v___x_2067_);
v___x_2076_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_2066_, v_a_2064_, v___x_2074_, v___x_2075_, v___x_2068_);
lean_dec(v_a_2064_);
v___y_2027_ = v_a_2066_;
v___y_2028_ = v___y_2054_;
v___y_2029_ = v___y_2055_;
v___y_2030_ = v___y_2057_;
v___y_2031_ = v___y_2058_;
v___y_2032_ = v___x_2076_;
goto v___jp_2026_;
}
}
}
else
{
lean_dec(v_a_2064_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec_ref(v___y_2055_);
lean_dec(v___y_2054_);
return v___x_2065_;
}
}
else
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2084_; 
lean_dec_ref(v_a_2061_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec_ref(v___y_2055_);
lean_dec(v___y_2054_);
v_a_2077_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2079_ = v___x_2063_;
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_2063_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2082_; 
if (v_isShared_2080_ == 0)
{
v___x_2082_ = v___x_2079_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_a_2077_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
}
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
lean_dec_ref(v_a_2061_);
lean_dec_ref(v___y_2059_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec_ref(v___y_2055_);
lean_dec(v___y_2054_);
v_a_2085_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___x_2062_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2062_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2090_; 
if (v_isShared_2088_ == 0)
{
v___x_2090_ = v___x_2087_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2085_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
v___jp_2093_:
{
if (lean_obj_tag(v___y_2102_) == 0)
{
lean_object* v_a_2103_; 
v_a_2103_ = lean_ctor_get(v___y_2102_, 0);
lean_inc(v_a_2103_);
lean_dec_ref_known(v___y_2102_, 1);
v___y_2053_ = v___y_2094_;
v___y_2054_ = v___y_2096_;
v___y_2055_ = v___y_2095_;
v___y_2056_ = v___y_2097_;
v___y_2057_ = v___y_2098_;
v___y_2058_ = v___y_2099_;
v___y_2059_ = v___y_2101_;
v___y_2060_ = v___y_2100_;
v_a_2061_ = v_a_2103_;
goto v___jp_2052_;
}
else
{
lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2111_; 
lean_dec_ref(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v_mvarId_2016_);
v_a_2104_ = lean_ctor_get(v___y_2102_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___y_2102_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2106_ = v___y_2102_;
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___y_2102_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2109_; 
if (v_isShared_2107_ == 0)
{
v___x_2109_ = v___x_2106_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_a_2104_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_apply___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2016_ = stack[0].m_obj;
lean_object* v___x_2017_ = stack[1].m_obj;
lean_object* v_e_2018_ = stack[2].m_obj;
lean_object* v_cfg_2019_ = stack[3].m_obj;
lean_object* v_term_x3f_2020_ = stack[4].m_obj;
lean_object* v___y_2021_ = stack[5].m_obj;
lean_object* v___y_2022_ = stack[6].m_obj;
lean_object* v___y_2023_ = stack[7].m_obj;
lean_object* v___y_2024_ = stack[8].m_obj;
lean_object* v_res_2232_;
v_res_2232_ = l_Lean_MVarId_apply___lam__0(v_mvarId_2016_, v___x_2017_, v_e_2018_, v_cfg_2019_, v_term_x3f_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
stack->m_obj
 = v_res_2232_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lam__0___boxed(lean_object* v_mvarId_2233_, lean_object* v___x_2234_, lean_object* v_e_2235_, lean_object* v_cfg_2236_, lean_object* v_term_x3f_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l_Lean_MVarId_apply___lam__0(v_mvarId_2233_, v___x_2234_, v_e_2235_, v_cfg_2236_, v_term_x3f_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
lean_dec_ref(v_cfg_2236_);
return v_res_2243_;
}
}
lean_object* l_Lean_MVarId_apply(lean_object* v_mvarId_2244_, lean_object* v_e_2245_, lean_object* v_cfg_2246_, lean_object* v_term_x3f_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_){
_start:
{
lean_object* v___x_2253_; lean_object* v___f_2254_; lean_object* v___x_2255_; 
v___x_2253_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7));
lean_inc(v_mvarId_2244_);
v___f_2254_ = lean_alloc_closure((void*)(l_Lean_MVarId_apply___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2254_, 0, v_mvarId_2244_);
lean_closure_set(v___f_2254_, 1, v___x_2253_);
lean_closure_set(v___f_2254_, 2, v_e_2245_);
lean_closure_set(v___f_2254_, 3, v_cfg_2246_);
lean_closure_set(v___f_2254_, 4, v_term_x3f_2247_);
v___x_2255_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2244_, v___f_2254_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_);
return v___x_2255_;
}
}
LEAN_EXPORT void l_Lean_MVarId_apply_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2244_ = stack[0].m_obj;
lean_object* v_e_2245_ = stack[1].m_obj;
lean_object* v_cfg_2246_ = stack[2].m_obj;
lean_object* v_term_x3f_2247_ = stack[3].m_obj;
lean_object* v_a_2248_ = stack[4].m_obj;
lean_object* v_a_2249_ = stack[5].m_obj;
lean_object* v_a_2250_ = stack[6].m_obj;
lean_object* v_a_2251_ = stack[7].m_obj;
lean_object* v_res_2256_;
v_res_2256_ = l_Lean_MVarId_apply(v_mvarId_2244_, v_e_2245_, v_cfg_2246_, v_term_x3f_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_);
stack->m_obj
 = v_res_2256_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___boxed(lean_object* v_mvarId_2257_, lean_object* v_e_2258_, lean_object* v_cfg_2259_, lean_object* v_term_x3f_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_){
_start:
{
lean_object* v_res_2266_; 
v_res_2266_ = l_Lean_MVarId_apply(v_mvarId_2257_, v_e_2258_, v_cfg_2259_, v_term_x3f_2260_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_);
lean_dec(v_a_2264_);
lean_dec_ref(v_a_2263_);
lean_dec(v_a_2262_);
lean_dec_ref(v_a_2261_);
return v_res_2266_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1(lean_object* v_mvarId_2267_, lean_object* v_val_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
lean_object* v___x_2274_; 
v___x_2274_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2267_, v_val_2268_, v___y_2270_);
return v___x_2274_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2267_ = stack[0].m_obj;
lean_object* v_val_2268_ = stack[1].m_obj;
lean_object* v___y_2269_ = stack[2].m_obj;
lean_object* v___y_2270_ = stack[3].m_obj;
lean_object* v___y_2271_ = stack[4].m_obj;
lean_object* v___y_2272_ = stack[5].m_obj;
lean_object* v_res_2275_;
v_res_2275_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1(v_mvarId_2267_, v_val_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
stack->m_obj
 = v_res_2275_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___boxed(lean_object* v_mvarId_2276_, lean_object* v_val_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v_res_2283_; 
v_res_2283_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1(v_mvarId_2276_, v_val_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
return v_res_2283_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5(lean_object* v_as_2284_, size_t v_i_2285_, size_t v_stop_2286_, lean_object* v_b_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v___x_2293_; 
v___x_2293_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_as_2284_, v_i_2285_, v_stop_2286_, v_b_2287_, v___y_2289_);
return v___x_2293_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2284_ = stack[0].m_obj;
size_t v_i_2285_ = stack[1].m_num;
size_t v_stop_2286_ = stack[2].m_num;
lean_object* v_b_2287_ = stack[3].m_obj;
lean_object* v___y_2288_ = stack[4].m_obj;
lean_object* v___y_2289_ = stack[5].m_obj;
lean_object* v___y_2290_ = stack[6].m_obj;
lean_object* v___y_2291_ = stack[7].m_obj;
lean_object* v_res_2294_;
v_res_2294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5(v_as_2284_, v_i_2285_, v_stop_2286_, v_b_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
stack->m_obj
 = v_res_2294_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___boxed(lean_object* v_as_2295_, lean_object* v_i_2296_, lean_object* v_stop_2297_, lean_object* v_b_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_){
_start:
{
size_t v_i_boxed_2304_; size_t v_stop_boxed_2305_; lean_object* v_res_2306_; 
v_i_boxed_2304_ = lean_unbox_usize(v_i_2296_);
lean_dec(v_i_2296_);
v_stop_boxed_2305_ = lean_unbox_usize(v_stop_2297_);
lean_dec(v_stop_2297_);
v_res_2306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5(v_as_2295_, v_i_boxed_2304_, v_stop_boxed_2305_, v_b_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec_ref(v_as_2295_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1(lean_object* v_00_u03b2_2307_, lean_object* v_x_2308_, lean_object* v_x_2309_, lean_object* v_x_2310_){
_start:
{
lean_object* v___x_2311_; 
v___x_2311_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(v_x_2308_, v_x_2309_, v_x_2310_);
return v___x_2311_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_2312_, lean_object* v_x_2313_, size_t v_x_2314_, size_t v_x_2315_, lean_object* v_x_2316_, lean_object* v_x_2317_){
_start:
{
lean_object* v___x_2318_; 
v___x_2318_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_2313_, v_x_2314_, v_x_2315_, v_x_2316_, v_x_2317_);
return v___x_2318_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2313_ = stack[1].m_obj;
size_t v_x_2314_ = stack[2].m_num;
size_t v_x_2315_ = stack[3].m_num;
lean_object* v_x_2316_ = stack[4].m_obj;
lean_object* v_x_2317_ = stack[5].m_obj;
lean_object* v_res_2319_;
v_res_2319_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3(lean_box(0), v_x_2313_, v_x_2314_, v_x_2315_, v_x_2316_, v_x_2317_);
stack->m_obj
 = v_res_2319_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2320_, lean_object* v_x_2321_, lean_object* v_x_2322_, lean_object* v_x_2323_, lean_object* v_x_2324_, lean_object* v_x_2325_){
_start:
{
size_t v_x_8340__boxed_2326_; size_t v_x_8341__boxed_2327_; lean_object* v_res_2328_; 
v_x_8340__boxed_2326_ = lean_unbox_usize(v_x_2322_);
lean_dec(v_x_2322_);
v_x_8341__boxed_2327_ = lean_unbox_usize(v_x_2323_);
lean_dec(v_x_2323_);
v_res_2328_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3(v_00_u03b2_2320_, v_x_2321_, v_x_8340__boxed_2326_, v_x_8341__boxed_2327_, v_x_2324_, v_x_2325_);
return v_res_2328_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_2329_, lean_object* v_n_2330_, lean_object* v_k_2331_, lean_object* v_v_2332_){
_start:
{
lean_object* v___x_2333_; 
v___x_2333_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(v_n_2330_, v_k_2331_, v_v_2332_);
return v___x_2333_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9(lean_object* v_00_u03b2_2334_, size_t v_depth_2335_, lean_object* v_keys_2336_, lean_object* v_vals_2337_, lean_object* v_heq_2338_, lean_object* v_i_2339_, lean_object* v_entries_2340_){
_start:
{
lean_object* v___x_2341_; 
v___x_2341_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_depth_2335_, v_keys_2336_, v_vals_2337_, v_i_2339_, v_entries_2340_);
return v___x_2341_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9_0interp(lean_interpreter_value* stack)
{
size_t v_depth_2335_ = stack[1].m_num;
lean_object* v_keys_2336_ = stack[2].m_obj;
lean_object* v_vals_2337_ = stack[3].m_obj;
lean_object* v_i_2339_ = stack[5].m_obj;
lean_object* v_entries_2340_ = stack[6].m_obj;
lean_object* v_res_2342_;
v_res_2342_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9(lean_box(0), v_depth_2335_, v_keys_2336_, v_vals_2337_, lean_box(0), v_i_2339_, v_entries_2340_);
stack->m_obj
 = v_res_2342_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___boxed(lean_object* v_00_u03b2_2343_, lean_object* v_depth_2344_, lean_object* v_keys_2345_, lean_object* v_vals_2346_, lean_object* v_heq_2347_, lean_object* v_i_2348_, lean_object* v_entries_2349_){
_start:
{
size_t v_depth_boxed_2350_; lean_object* v_res_2351_; 
v_depth_boxed_2350_ = lean_unbox_usize(v_depth_2344_);
lean_dec(v_depth_2344_);
v_res_2351_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9(v_00_u03b2_2343_, v_depth_boxed_2350_, v_keys_2345_, v_vals_2346_, v_heq_2347_, v_i_2348_, v_entries_2349_);
lean_dec_ref(v_vals_2346_);
lean_dec_ref(v_keys_2345_);
return v_res_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9(lean_object* v_00_u03b2_2352_, lean_object* v_x_2353_, lean_object* v_x_2354_, lean_object* v_x_2355_, lean_object* v_x_2356_){
_start:
{
lean_object* v___x_2357_; 
v___x_2357_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(v_x_2353_, v_x_2354_, v_x_2355_, v_x_2356_);
return v___x_2357_;
}
}
static lean_object* _init_l_Lean_MVarId_applyConst___closed__1(void){
_start:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2359_ = ((lean_object*)(l_Lean_MVarId_applyConst___closed__0));
v___x_2360_ = l_Lean_stringToMessageData(v___x_2359_);
return v___x_2360_;
}
}
lean_object* l_Lean_MVarId_applyConst(lean_object* v_mvar_2361_, lean_object* v_c_2362_, lean_object* v_cfg_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_){
_start:
{
lean_object* v___x_2369_; 
lean_inc(v_c_2362_);
v___x_2369_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_c_2362_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_);
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_object* v_a_2370_; lean_object* v___x_2371_; uint8_t v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
lean_inc(v_a_2370_);
lean_dec_ref_known(v___x_2369_, 1);
v___x_2371_ = lean_obj_once(&l_Lean_MVarId_applyConst___closed__1, &l_Lean_MVarId_applyConst___closed__1_once, _init_l_Lean_MVarId_applyConst___closed__1);
v___x_2372_ = 0;
v___x_2373_ = l_Lean_MessageData_ofConstName(v_c_2362_, v___x_2372_);
v___x_2374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2371_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
v___x_2375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2374_);
lean_ctor_set(v___x_2375_, 1, v___x_2371_);
v___x_2376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2375_);
v___x_2377_ = l_Lean_MVarId_apply(v_mvar_2361_, v_a_2370_, v_cfg_2363_, v___x_2376_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_);
return v___x_2377_;
}
else
{
lean_object* v_a_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2385_; 
lean_dec_ref(v_cfg_2363_);
lean_dec(v_c_2362_);
lean_dec(v_mvar_2361_);
v_a_2378_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2380_ = v___x_2369_;
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_a_2378_);
lean_dec(v___x_2369_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2383_; 
if (v_isShared_2381_ == 0)
{
v___x_2383_ = v___x_2380_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v_a_2378_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_applyConst_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvar_2361_ = stack[0].m_obj;
lean_object* v_c_2362_ = stack[1].m_obj;
lean_object* v_cfg_2363_ = stack[2].m_obj;
lean_object* v_a_2364_ = stack[3].m_obj;
lean_object* v_a_2365_ = stack[4].m_obj;
lean_object* v_a_2366_ = stack[5].m_obj;
lean_object* v_a_2367_ = stack[6].m_obj;
lean_object* v_res_2386_;
v_res_2386_ = l_Lean_MVarId_applyConst(v_mvar_2361_, v_c_2362_, v_cfg_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_);
stack->m_obj
 = v_res_2386_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyConst___boxed(lean_object* v_mvar_2387_, lean_object* v_c_2388_, lean_object* v_cfg_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_){
_start:
{
lean_object* v_res_2395_; 
v_res_2395_ = l_Lean_MVarId_applyConst(v_mvar_2387_, v_c_2388_, v_cfg_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_);
lean_dec(v_a_2393_);
lean_dec_ref(v_a_2392_);
lean_dec(v_a_2391_);
lean_dec_ref(v_a_2390_);
return v_res_2395_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(lean_object* v_msgData_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
lean_object* v___x_2402_; lean_object* v_env_2403_; uint8_t v___x_2404_; lean_object* v_env_2405_; lean_object* v___x_2406_; lean_object* v_toCold_2407_; lean_object* v_mctx_2408_; lean_object* v_lctx_2409_; lean_object* v_options_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2402_ = lean_st_ref_get(v___y_2400_);
v_env_2403_ = lean_ctor_get(v___x_2402_, 0);
lean_inc_ref(v_env_2403_);
lean_dec(v___x_2402_);
v___x_2404_ = 0;
v_env_2405_ = l_Lean_Environment_setRecordingDeps(v_env_2403_, v___x_2404_);
v___x_2406_ = lean_st_ref_get(v___y_2398_);
v_toCold_2407_ = lean_ctor_get(v___y_2399_, 0);
v_mctx_2408_ = lean_ctor_get(v___x_2406_, 0);
lean_inc_ref(v_mctx_2408_);
lean_dec(v___x_2406_);
v_lctx_2409_ = lean_ctor_get(v___y_2397_, 2);
v_options_2410_ = lean_ctor_get(v_toCold_2407_, 2);
lean_inc_ref(v_options_2410_);
lean_inc_ref(v_lctx_2409_);
v___x_2411_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2411_, 0, v_env_2405_);
lean_ctor_set(v___x_2411_, 1, v_mctx_2408_);
lean_ctor_set(v___x_2411_, 2, v_lctx_2409_);
lean_ctor_set(v___x_2411_, 3, v_options_2410_);
v___x_2412_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2411_);
lean_ctor_set(v___x_2412_, 1, v_msgData_2396_);
v___x_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2412_);
return v___x_2413_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2396_ = stack[0].m_obj;
lean_object* v___y_2397_ = stack[1].m_obj;
lean_object* v___y_2398_ = stack[2].m_obj;
lean_object* v___y_2399_ = stack[3].m_obj;
lean_object* v___y_2400_ = stack[4].m_obj;
lean_object* v_res_2414_;
v_res_2414_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(v_msgData_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
stack->m_obj
 = v_res_2414_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1___boxed(lean_object* v_msgData_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(v_msgData_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
return v_res_2421_;
}
}
lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(lean_object* v_msg_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
lean_object* v_ref_2428_; lean_object* v___x_2429_; lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2438_; 
v_ref_2428_ = lean_ctor_get(v___y_2425_, 2);
v___x_2429_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(v_msg_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2432_ = v___x_2429_;
v_isShared_2433_ = v_isSharedCheck_2438_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2429_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2438_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2434_; lean_object* v___x_2436_; 
lean_inc(v_ref_2428_);
v___x_2434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2434_, 0, v_ref_2428_);
lean_ctor_set(v___x_2434_, 1, v_a_2430_);
if (v_isShared_2433_ == 0)
{
lean_ctor_set_tag(v___x_2432_, 1);
lean_ctor_set(v___x_2432_, 0, v___x_2434_);
v___x_2436_ = v___x_2432_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v___x_2434_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2422_ = stack[0].m_obj;
lean_object* v___y_2423_ = stack[1].m_obj;
lean_object* v___y_2424_ = stack[2].m_obj;
lean_object* v___y_2425_ = stack[3].m_obj;
lean_object* v___y_2426_ = stack[4].m_obj;
lean_object* v_res_2439_;
v_res_2439_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v_msg_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
stack->m_obj
 = v_res_2439_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg___boxed(lean_object* v_msg_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v_msg_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
return v_res_2446_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(size_t v_sz_2447_, size_t v_i_2448_, lean_object* v_bs_2449_){
_start:
{
uint8_t v___x_2450_; 
v___x_2450_ = lean_usize_dec_lt(v_i_2448_, v_sz_2447_);
if (v___x_2450_ == 0)
{
return v_bs_2449_;
}
else
{
lean_object* v_v_2451_; lean_object* v___x_2452_; lean_object* v_bs_x27_2453_; lean_object* v___x_2454_; size_t v___x_2455_; size_t v___x_2456_; lean_object* v___x_2457_; 
v_v_2451_ = lean_array_uget(v_bs_2449_, v_i_2448_);
v___x_2452_ = lean_unsigned_to_nat(0u);
v_bs_x27_2453_ = lean_array_uset(v_bs_2449_, v_i_2448_, v___x_2452_);
v___x_2454_ = l_Lean_Expr_mvarId_x21(v_v_2451_);
lean_dec(v_v_2451_);
v___x_2455_ = ((size_t)1ULL);
v___x_2456_ = lean_usize_add(v_i_2448_, v___x_2455_);
v___x_2457_ = lean_array_uset(v_bs_x27_2453_, v_i_2448_, v___x_2454_);
v_i_2448_ = v___x_2456_;
v_bs_2449_ = v___x_2457_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2447_ = stack[0].m_num;
size_t v_i_2448_ = stack[1].m_num;
lean_object* v_bs_2449_ = stack[2].m_obj;
lean_object* v_res_2459_;
v_res_2459_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(v_sz_2447_, v_i_2448_, v_bs_2449_);
stack->m_obj
 = v_res_2459_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0___boxed(lean_object* v_sz_2460_, lean_object* v_i_2461_, lean_object* v_bs_2462_){
_start:
{
size_t v_sz_boxed_2463_; size_t v_i_boxed_2464_; lean_object* v_res_2465_; 
v_sz_boxed_2463_ = lean_unbox_usize(v_sz_2460_);
lean_dec(v_sz_2460_);
v_i_boxed_2464_ = lean_unbox_usize(v_i_2461_);
lean_dec(v_i_2461_);
v_res_2465_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(v_sz_boxed_2463_, v_i_boxed_2464_, v_bs_2462_);
return v_res_2465_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2467_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__0));
v___x_2468_ = l_Lean_stringToMessageData(v___x_2467_);
return v___x_2468_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2470_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__2));
v___x_2471_ = l_Lean_stringToMessageData(v___x_2470_);
return v___x_2471_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2473_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__4));
v___x_2474_ = l_Lean_stringToMessageData(v___x_2473_);
return v___x_2474_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2476_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__6));
v___x_2477_ = l_Lean_stringToMessageData(v___x_2476_);
return v___x_2477_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__9(void){
_start:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2479_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__8));
v___x_2480_ = l_Lean_stringToMessageData(v___x_2479_);
return v___x_2480_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__11(void){
_start:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2482_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__10));
v___x_2483_ = l_Lean_stringToMessageData(v___x_2482_);
return v___x_2483_;
}
}
lean_object* l_Lean_MVarId_applyN___lam__0(lean_object* v_mvarId_2484_, lean_object* v___x_2485_, lean_object* v_e_2486_, lean_object* v_n_2487_, uint8_t v_useApproxDefEq_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
lean_object* v___x_2494_; 
lean_inc(v_mvarId_2484_);
v___x_2494_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2484_, v___x_2485_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_object* v___x_2495_; 
lean_dec_ref_known(v___x_2494_, 1);
lean_inc(v_mvarId_2484_);
v___x_2495_ = l_Lean_MVarId_getType(v_mvarId_2484_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
if (lean_obj_tag(v___x_2495_) == 0)
{
lean_object* v_a_2496_; lean_object* v___x_2497_; 
v_a_2496_ = lean_ctor_get(v___x_2495_, 0);
lean_inc(v_a_2496_);
lean_dec_ref_known(v___x_2495_, 1);
lean_inc(v___y_2492_);
lean_inc_ref(v___y_2491_);
lean_inc(v___y_2490_);
lean_inc_ref(v___y_2489_);
lean_inc_ref(v_e_2486_);
v___x_2497_ = lean_infer_type(v_e_2486_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v_a_2498_; uint8_t v___x_2499_; lean_object* v___x_2500_; 
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
lean_inc(v_a_2498_);
lean_dec_ref_known(v___x_2497_, 1);
v___x_2499_ = 0;
lean_inc(v_n_2487_);
v___x_2500_ = l_Lean_Meta_forallMetaBoundedTelescope(v_a_2498_, v_n_2487_, v___x_2499_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
if (lean_obj_tag(v___x_2500_) == 0)
{
lean_object* v_a_2501_; lean_object* v_fst_2502_; lean_object* v_snd_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2593_; 
v_a_2501_ = lean_ctor_get(v___x_2500_, 0);
lean_inc(v_a_2501_);
lean_dec_ref_known(v___x_2500_, 1);
v_fst_2502_ = lean_ctor_get(v_a_2501_, 0);
v_snd_2503_ = lean_ctor_get(v_a_2501_, 1);
v_isSharedCheck_2593_ = !lean_is_exclusive(v_a_2501_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2505_ = v_a_2501_;
v_isShared_2506_ = v_isSharedCheck_2593_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_snd_2503_);
lean_inc(v_fst_2502_);
lean_dec(v_a_2501_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2593_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___y_2508_; lean_object* v_snd_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2591_; 
v_snd_2523_ = lean_ctor_get(v_snd_2503_, 1);
v_isSharedCheck_2591_ = !lean_is_exclusive(v_snd_2503_);
if (v_isSharedCheck_2591_ == 0)
{
lean_object* v_unused_2592_; 
v_unused_2592_ = lean_ctor_get(v_snd_2503_, 0);
lean_dec(v_unused_2592_);
v___x_2525_ = v_snd_2503_;
v_isShared_2526_ = v_isSharedCheck_2591_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_snd_2523_);
lean_dec(v_snd_2503_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2591_;
goto v_resetjp_2524_;
}
v___jp_2507_:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2521_; 
lean_inc(v_fst_2502_);
v___x_2509_ = l_Lean_Expr_beta(v_e_2486_, v_fst_2502_);
v___x_2510_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2484_, v___x_2509_, v___y_2508_);
lean_dec(v___y_2508_);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2510_);
if (v_isSharedCheck_2521_ == 0)
{
lean_object* v_unused_2522_; 
v_unused_2522_ = lean_ctor_get(v___x_2510_, 0);
lean_dec(v_unused_2522_);
v___x_2512_ = v___x_2510_;
v_isShared_2513_ = v_isSharedCheck_2521_;
goto v_resetjp_2511_;
}
else
{
lean_dec(v___x_2510_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2521_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
size_t v_sz_2514_; size_t v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2519_; 
v_sz_2514_ = lean_array_size(v_fst_2502_);
v___x_2515_ = ((size_t)0ULL);
v___x_2516_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(v_sz_2514_, v___x_2515_, v_fst_2502_);
v___x_2517_ = lean_array_to_list(v___x_2516_);
if (v_isShared_2513_ == 0)
{
lean_ctor_set(v___x_2512_, 0, v___x_2517_);
v___x_2519_ = v___x_2512_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v___x_2517_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
v_resetjp_2524_:
{
lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___x_2571_; uint8_t v___x_2572_; 
v___x_2571_ = lean_array_get_size(v_fst_2502_);
v___x_2572_ = lean_nat_dec_eq(v___x_2571_, v_n_2487_);
if (v___x_2572_ == 0)
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v_a_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2590_; 
lean_del_object(v___x_2525_);
lean_del_object(v___x_2505_);
lean_dec(v_fst_2502_);
lean_dec(v_a_2496_);
lean_dec_ref(v_e_2486_);
lean_dec(v_mvarId_2484_);
v___x_2573_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__9, &l_Lean_MVarId_applyN___lam__0___closed__9_once, _init_l_Lean_MVarId_applyN___lam__0___closed__9);
v___x_2574_ = l_Nat_reprFast(v_n_2487_);
v___x_2575_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
v___x_2576_ = l_Lean_MessageData_ofFormat(v___x_2575_);
v___x_2577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2573_);
lean_ctor_set(v___x_2577_, 1, v___x_2576_);
v___x_2578_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__11, &l_Lean_MVarId_applyN___lam__0___closed__11_once, _init_l_Lean_MVarId_applyN___lam__0___closed__11);
v___x_2579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2577_);
lean_ctor_set(v___x_2579_, 1, v___x_2578_);
v___x_2580_ = l_Lean_indentExpr(v_snd_2523_);
v___x_2581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2579_);
lean_ctor_set(v___x_2581_, 1, v___x_2580_);
v___x_2582_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_2581_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
v_a_2583_ = lean_ctor_get(v___x_2582_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2585_ = v___x_2582_;
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_a_2583_);
lean_dec(v___x_2582_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2588_; 
if (v_isShared_2586_ == 0)
{
v___x_2588_ = v___x_2585_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_a_2583_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
else
{
v___y_2528_ = v___y_2489_;
v___y_2529_ = v___y_2490_;
v___y_2530_ = v___y_2491_;
v___y_2531_ = v___y_2492_;
goto v___jp_2527_;
}
v___jp_2527_:
{
lean_object* v___x_2532_; 
lean_inc(v_a_2496_);
lean_inc(v_snd_2523_);
v___x_2532_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_useApproxDefEq_2488_, v_snd_2523_, v_a_2496_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; uint8_t v___x_2534_; 
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_a_2533_);
lean_dec_ref_known(v___x_2532_, 1);
v___x_2534_ = lean_unbox(v_a_2533_);
lean_dec(v_a_2533_);
if (v___x_2534_ == 0)
{
lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2538_; 
lean_dec(v_fst_2502_);
lean_dec_ref(v_e_2486_);
lean_dec(v_mvarId_2484_);
v___x_2535_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__1, &l_Lean_MVarId_applyN___lam__0___closed__1_once, _init_l_Lean_MVarId_applyN___lam__0___closed__1);
v___x_2536_ = l_Lean_indentExpr(v_a_2496_);
if (v_isShared_2526_ == 0)
{
lean_ctor_set_tag(v___x_2525_, 7);
lean_ctor_set(v___x_2525_, 1, v___x_2536_);
lean_ctor_set(v___x_2525_, 0, v___x_2535_);
v___x_2538_ = v___x_2525_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v___x_2535_);
lean_ctor_set(v_reuseFailAlloc_2562_, 1, v___x_2536_);
v___x_2538_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
lean_object* v___x_2539_; lean_object* v___x_2541_; 
v___x_2539_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__3, &l_Lean_MVarId_applyN___lam__0___closed__3_once, _init_l_Lean_MVarId_applyN___lam__0___closed__3);
if (v_isShared_2506_ == 0)
{
lean_ctor_set_tag(v___x_2505_, 7);
lean_ctor_set(v___x_2505_, 1, v___x_2539_);
lean_ctor_set(v___x_2505_, 0, v___x_2538_);
v___x_2541_ = v___x_2505_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v___x_2538_);
lean_ctor_set(v_reuseFailAlloc_2561_, 1, v___x_2539_);
v___x_2541_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2560_; 
v___x_2542_ = l_Lean_indentExpr(v_snd_2523_);
v___x_2543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2541_);
lean_ctor_set(v___x_2543_, 1, v___x_2542_);
v___x_2544_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__5, &l_Lean_MVarId_applyN___lam__0___closed__5_once, _init_l_Lean_MVarId_applyN___lam__0___closed__5);
v___x_2545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2543_);
lean_ctor_set(v___x_2545_, 1, v___x_2544_);
v___x_2546_ = l_Nat_reprFast(v_n_2487_);
v___x_2547_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2546_);
v___x_2548_ = l_Lean_MessageData_ofFormat(v___x_2547_);
v___x_2549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2545_);
lean_ctor_set(v___x_2549_, 1, v___x_2548_);
v___x_2550_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__7, &l_Lean_MVarId_applyN___lam__0___closed__7_once, _init_l_Lean_MVarId_applyN___lam__0___closed__7);
v___x_2551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2549_);
lean_ctor_set(v___x_2551_, 1, v___x_2550_);
v___x_2552_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_2551_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2555_ = v___x_2552_;
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2552_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2558_; 
if (v_isShared_2556_ == 0)
{
v___x_2558_ = v___x_2555_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_a_2553_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
}
}
}
else
{
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec_ref(v___y_2528_);
lean_del_object(v___x_2525_);
lean_dec(v_snd_2523_);
lean_del_object(v___x_2505_);
lean_dec(v_a_2496_);
lean_dec(v_n_2487_);
v___y_2508_ = v___y_2529_;
goto v___jp_2507_;
}
}
else
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
lean_del_object(v___x_2525_);
lean_dec(v_snd_2523_);
lean_del_object(v___x_2505_);
lean_dec(v_fst_2502_);
lean_dec(v_a_2496_);
lean_dec(v_n_2487_);
lean_dec_ref(v_e_2486_);
lean_dec(v_mvarId_2484_);
v_a_2563_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2565_ = v___x_2532_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2532_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2568_; 
if (v_isShared_2566_ == 0)
{
v___x_2568_ = v___x_2565_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_a_2563_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2601_; 
lean_dec(v_a_2496_);
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec(v_n_2487_);
lean_dec_ref(v_e_2486_);
lean_dec(v_mvarId_2484_);
v_a_2594_ = lean_ctor_get(v___x_2500_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2596_ = v___x_2500_;
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2500_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2599_; 
if (v_isShared_2597_ == 0)
{
v___x_2599_ = v___x_2596_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_a_2594_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
}
else
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2609_; 
lean_dec(v_a_2496_);
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec(v_n_2487_);
lean_dec_ref(v_e_2486_);
lean_dec(v_mvarId_2484_);
v_a_2602_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2604_ = v___x_2497_;
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2497_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2607_; 
if (v_isShared_2605_ == 0)
{
v___x_2607_ = v___x_2604_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_a_2602_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
}
}
else
{
lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2617_; 
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec(v_n_2487_);
lean_dec_ref(v_e_2486_);
lean_dec(v_mvarId_2484_);
v_a_2610_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2612_ = v___x_2495_;
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2495_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2615_; 
if (v_isShared_2613_ == 0)
{
v___x_2615_ = v___x_2612_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_a_2610_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
}
else
{
lean_object* v_a_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2625_; 
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec(v_n_2487_);
lean_dec_ref(v_e_2486_);
lean_dec(v_mvarId_2484_);
v_a_2618_ = lean_ctor_get(v___x_2494_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2620_ = v___x_2494_;
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_a_2618_);
lean_dec(v___x_2494_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2623_; 
if (v_isShared_2621_ == 0)
{
v___x_2623_ = v___x_2620_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_a_2618_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_applyN___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2484_ = stack[0].m_obj;
lean_object* v___x_2485_ = stack[1].m_obj;
lean_object* v_e_2486_ = stack[2].m_obj;
lean_object* v_n_2487_ = stack[3].m_obj;
uint8_t v_useApproxDefEq_2488_ = stack[4].m_num;
lean_object* v___y_2489_ = stack[5].m_obj;
lean_object* v___y_2490_ = stack[6].m_obj;
lean_object* v___y_2491_ = stack[7].m_obj;
lean_object* v___y_2492_ = stack[8].m_obj;
lean_object* v_res_2626_;
v_res_2626_ = l_Lean_MVarId_applyN___lam__0(v_mvarId_2484_, v___x_2485_, v_e_2486_, v_n_2487_, v_useApproxDefEq_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
stack->m_obj
 = v_res_2626_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___lam__0___boxed(lean_object* v_mvarId_2627_, lean_object* v___x_2628_, lean_object* v_e_2629_, lean_object* v_n_2630_, lean_object* v_useApproxDefEq_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
uint8_t v_useApproxDefEq_boxed_2637_; lean_object* v_res_2638_; 
v_useApproxDefEq_boxed_2637_ = lean_unbox(v_useApproxDefEq_2631_);
v_res_2638_ = l_Lean_MVarId_applyN___lam__0(v_mvarId_2627_, v___x_2628_, v_e_2629_, v_n_2630_, v_useApproxDefEq_boxed_2637_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
return v_res_2638_;
}
}
lean_object* l_Lean_MVarId_applyN(lean_object* v_mvarId_2639_, lean_object* v_e_2640_, lean_object* v_n_2641_, uint8_t v_useApproxDefEq_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_){
_start:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___f_2650_; lean_object* v___x_2651_; 
v___x_2648_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7));
v___x_2649_ = lean_box(v_useApproxDefEq_2642_);
lean_inc(v_mvarId_2639_);
v___f_2650_ = lean_alloc_closure((void*)(l_Lean_MVarId_applyN___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2650_, 0, v_mvarId_2639_);
lean_closure_set(v___f_2650_, 1, v___x_2648_);
lean_closure_set(v___f_2650_, 2, v_e_2640_);
lean_closure_set(v___f_2650_, 3, v_n_2641_);
lean_closure_set(v___f_2650_, 4, v___x_2649_);
v___x_2651_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2639_, v___f_2650_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_);
return v___x_2651_;
}
}
LEAN_EXPORT void l_Lean_MVarId_applyN_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2639_ = stack[0].m_obj;
lean_object* v_e_2640_ = stack[1].m_obj;
lean_object* v_n_2641_ = stack[2].m_obj;
uint8_t v_useApproxDefEq_2642_ = stack[3].m_num;
lean_object* v_a_2643_ = stack[4].m_obj;
lean_object* v_a_2644_ = stack[5].m_obj;
lean_object* v_a_2645_ = stack[6].m_obj;
lean_object* v_a_2646_ = stack[7].m_obj;
lean_object* v_res_2652_;
v_res_2652_ = l_Lean_MVarId_applyN(v_mvarId_2639_, v_e_2640_, v_n_2641_, v_useApproxDefEq_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_);
stack->m_obj
 = v_res_2652_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___boxed(lean_object* v_mvarId_2653_, lean_object* v_e_2654_, lean_object* v_n_2655_, lean_object* v_useApproxDefEq_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_){
_start:
{
uint8_t v_useApproxDefEq_boxed_2662_; lean_object* v_res_2663_; 
v_useApproxDefEq_boxed_2662_ = lean_unbox(v_useApproxDefEq_2656_);
v_res_2663_ = l_Lean_MVarId_applyN(v_mvarId_2653_, v_e_2654_, v_n_2655_, v_useApproxDefEq_boxed_2662_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_);
lean_dec(v_a_2660_);
lean_dec_ref(v_a_2659_);
lean_dec(v_a_2658_);
lean_dec_ref(v_a_2657_);
return v_res_2663_;
}
}
lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1(lean_object* v_00_u03b1_2664_, lean_object* v_msg_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
lean_object* v___x_2671_; 
v___x_2671_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v_msg_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_);
return v___x_2671_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2665_ = stack[1].m_obj;
lean_object* v___y_2666_ = stack[2].m_obj;
lean_object* v___y_2667_ = stack[3].m_obj;
lean_object* v___y_2668_ = stack[4].m_obj;
lean_object* v___y_2669_ = stack[5].m_obj;
lean_object* v_res_2672_;
v_res_2672_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1(lean_box(0), v_msg_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_);
stack->m_obj
 = v_res_2672_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___boxed(lean_object* v_00_u03b1_2673_, lean_object* v_msg_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
lean_object* v_res_2680_; 
v_res_2680_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1(v_00_u03b1_2673_, v_msg_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
return v_res_2680_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6(void){
_start:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; 
v___x_2691_ = lean_box(0);
v___x_2692_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__5));
v___x_2693_ = l_Lean_mkConst(v___x_2692_, v___x_2691_);
return v___x_2693_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(lean_object* v_tag_2694_, lean_object* v_type_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_){
_start:
{
lean_object* v___x_2702_; 
lean_inc(v_a_2700_);
lean_inc_ref(v_a_2699_);
lean_inc(v_a_2698_);
lean_inc_ref(v_a_2697_);
v___x_2702_ = lean_whnf(v_type_2695_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_);
if (lean_obj_tag(v___x_2702_) == 0)
{
lean_object* v_a_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; uint8_t v___x_2706_; 
v_a_2703_ = lean_ctor_get(v___x_2702_, 0);
lean_inc(v_a_2703_);
lean_dec_ref_known(v___x_2702_, 1);
v___x_2704_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1));
v___x_2705_ = lean_unsigned_to_nat(2u);
v___x_2706_ = l_Lean_Expr_isAppOfArity(v_a_2703_, v___x_2704_, v___x_2705_);
if (v___x_2706_ == 0)
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2707_ = lean_st_ref_get(v_a_2696_);
v___x_2708_ = lean_array_get_size(v___x_2707_);
lean_dec(v___x_2707_);
v___x_2709_ = lean_unsigned_to_nat(1u);
v___x_2710_ = lean_nat_add(v___x_2708_, v___x_2709_);
v___x_2711_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__3));
v___x_2712_ = lean_name_append_index_after(v___x_2711_, v___x_2710_);
v___x_2713_ = l_Lean_Name_append(v_tag_2694_, v___x_2712_);
v___x_2714_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2703_, v___x_2713_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_);
if (lean_obj_tag(v___x_2714_) == 0)
{
lean_object* v_a_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2726_; 
v_a_2715_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2717_ = v___x_2714_;
v_isShared_2718_ = v_isSharedCheck_2726_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_a_2715_);
lean_dec(v___x_2714_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2726_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2724_; 
v___x_2719_ = lean_st_ref_take(v_a_2696_);
v___x_2720_ = l_Lean_Expr_mvarId_x21(v_a_2715_);
v___x_2721_ = lean_array_push(v___x_2719_, v___x_2720_);
v___x_2722_ = lean_st_ref_put(v_a_2696_, v___x_2721_);
if (v_isShared_2718_ == 0)
{
v___x_2724_ = v___x_2717_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_a_2715_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
else
{
return v___x_2714_;
}
}
else
{
lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v___x_2727_ = l_Lean_Expr_appFn_x21(v_a_2703_);
v___x_2728_ = l_Lean_Expr_appArg_x21(v___x_2727_);
lean_dec_ref(v___x_2727_);
v___x_2729_ = l_Lean_Expr_appArg_x21(v_a_2703_);
lean_dec(v_a_2703_);
lean_inc_ref(v___x_2728_);
lean_inc(v_tag_2694_);
v___x_2730_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2694_, v___x_2728_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v_a_2731_; lean_object* v___x_2732_; 
v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
lean_inc(v_a_2731_);
lean_dec_ref_known(v___x_2730_, 1);
lean_inc_ref(v___x_2729_);
v___x_2732_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2694_, v___x_2729_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_);
if (lean_obj_tag(v___x_2732_) == 0)
{
lean_object* v_a_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2742_; 
v_a_2733_ = lean_ctor_get(v___x_2732_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2735_ = v___x_2732_;
v_isShared_2736_ = v_isSharedCheck_2742_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_a_2733_);
lean_dec(v___x_2732_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2742_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2740_; 
v___x_2737_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6, &l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6);
v___x_2738_ = l_Lean_mkApp4(v___x_2737_, v___x_2728_, v___x_2729_, v_a_2731_, v_a_2733_);
if (v_isShared_2736_ == 0)
{
lean_ctor_set(v___x_2735_, 0, v___x_2738_);
v___x_2740_ = v___x_2735_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v___x_2738_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
else
{
lean_dec(v_a_2731_);
lean_dec_ref(v___x_2729_);
lean_dec_ref(v___x_2728_);
return v___x_2732_;
}
}
else
{
lean_dec_ref(v___x_2729_);
lean_dec_ref(v___x_2728_);
lean_dec(v_tag_2694_);
return v___x_2730_;
}
}
}
else
{
lean_dec(v_tag_2694_);
return v___x_2702_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_tag_2694_ = stack[0].m_obj;
lean_object* v_type_2695_ = stack[1].m_obj;
lean_object* v_a_2696_ = stack[2].m_obj;
lean_object* v_a_2697_ = stack[3].m_obj;
lean_object* v_a_2698_ = stack[4].m_obj;
lean_object* v_a_2699_ = stack[5].m_obj;
lean_object* v_a_2700_ = stack[6].m_obj;
lean_object* v_res_2743_;
v_res_2743_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2694_, v_type_2695_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_);
stack->m_obj
 = v_res_2743_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___boxed(lean_object* v_tag_2744_, lean_object* v_type_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2744_, v_type_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_);
lean_dec(v_a_2750_);
lean_dec_ref(v_a_2749_);
lean_dec(v_a_2748_);
lean_dec_ref(v_a_2747_);
lean_dec(v_a_2746_);
return v_res_2752_;
}
}
lean_object* l_Lean_MVarId_splitAndCore___lam__0(lean_object* v_mvarId_2753_, lean_object* v___x_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v___x_2760_; 
lean_inc(v_mvarId_2753_);
v___x_2760_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2753_, v___x_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_);
if (lean_obj_tag(v___x_2760_) == 0)
{
lean_object* v___x_2761_; 
lean_dec_ref_known(v___x_2760_, 1);
lean_inc(v_mvarId_2753_);
v___x_2761_ = l_Lean_MVarId_getType_x27(v_mvarId_2753_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2807_; 
v_a_2762_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2764_ = v___x_2761_;
v_isShared_2765_ = v_isSharedCheck_2807_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2761_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2807_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; uint8_t v___x_2768_; 
v___x_2766_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1));
v___x_2767_ = lean_unsigned_to_nat(2u);
v___x_2768_ = l_Lean_Expr_isAppOfArity(v_a_2762_, v___x_2766_, v___x_2767_);
if (v___x_2768_ == 0)
{
lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2772_; 
lean_dec(v_a_2762_);
v___x_2769_ = lean_box(0);
v___x_2770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2770_, 0, v_mvarId_2753_);
lean_ctor_set(v___x_2770_, 1, v___x_2769_);
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 0, v___x_2770_);
v___x_2772_ = v___x_2764_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v___x_2770_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
else
{
lean_object* v___x_2774_; 
lean_del_object(v___x_2764_);
lean_inc(v_mvarId_2753_);
v___x_2774_ = l_Lean_MVarId_getTag(v_mvarId_2753_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_);
if (lean_obj_tag(v___x_2774_) == 0)
{
lean_object* v_a_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v_a_2775_ = lean_ctor_get(v___x_2774_, 0);
lean_inc(v_a_2775_);
lean_dec_ref_known(v___x_2774_, 1);
v___x_2776_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__0));
v___x_2777_ = lean_st_mk_ref(v___x_2776_);
v___x_2778_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_a_2775_, v_a_2762_, v___x_2777_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2789_; 
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
lean_inc(v_a_2779_);
lean_dec_ref_known(v___x_2778_, 1);
v___x_2780_ = lean_st_ref_get(v___x_2777_);
lean_dec(v___x_2777_);
v___x_2781_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2753_, v_a_2779_, v___y_2756_);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2789_ == 0)
{
lean_object* v_unused_2790_; 
v_unused_2790_ = lean_ctor_get(v___x_2781_, 0);
lean_dec(v_unused_2790_);
v___x_2783_ = v___x_2781_;
v_isShared_2784_ = v_isSharedCheck_2789_;
goto v_resetjp_2782_;
}
else
{
lean_dec(v___x_2781_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2789_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2785_; lean_object* v___x_2787_; 
v___x_2785_ = lean_array_to_list(v___x_2780_);
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 0, v___x_2785_);
v___x_2787_ = v___x_2783_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v___x_2785_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
else
{
lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2798_; 
lean_dec(v___x_2777_);
lean_dec(v_mvarId_2753_);
v_a_2791_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2793_ = v___x_2778_;
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v___x_2778_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2796_; 
if (v_isShared_2794_ == 0)
{
v___x_2796_ = v___x_2793_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2791_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
}
else
{
lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2806_; 
lean_dec(v_a_2762_);
lean_dec(v_mvarId_2753_);
v_a_2799_ = lean_ctor_get(v___x_2774_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2801_ = v___x_2774_;
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_dec(v___x_2774_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2804_; 
if (v_isShared_2802_ == 0)
{
v___x_2804_ = v___x_2801_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2799_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
}
}
}
else
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2815_; 
lean_dec(v_mvarId_2753_);
v_a_2808_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2810_ = v___x_2761_;
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2761_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2813_; 
if (v_isShared_2811_ == 0)
{
v___x_2813_ = v___x_2810_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_a_2808_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
}
}
else
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2823_; 
lean_dec(v_mvarId_2753_);
v_a_2816_ = lean_ctor_get(v___x_2760_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2760_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2818_ = v___x_2760_;
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2760_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2821_; 
if (v_isShared_2819_ == 0)
{
v___x_2821_ = v___x_2818_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_a_2816_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_splitAndCore___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2753_ = stack[0].m_obj;
lean_object* v___x_2754_ = stack[1].m_obj;
lean_object* v___y_2755_ = stack[2].m_obj;
lean_object* v___y_2756_ = stack[3].m_obj;
lean_object* v___y_2757_ = stack[4].m_obj;
lean_object* v___y_2758_ = stack[5].m_obj;
lean_object* v_res_2824_;
v_res_2824_ = l_Lean_MVarId_splitAndCore___lam__0(v_mvarId_2753_, v___x_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_);
stack->m_obj
 = v_res_2824_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___lam__0___boxed(lean_object* v_mvarId_2825_, lean_object* v___x_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l_Lean_MVarId_splitAndCore___lam__0(v_mvarId_2825_, v___x_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_);
lean_dec(v___y_2830_);
lean_dec_ref(v___y_2829_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
return v_res_2832_;
}
}
lean_object* l_Lean_MVarId_splitAndCore(lean_object* v_mvarId_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_){
_start:
{
lean_object* v___x_2842_; lean_object* v___f_2843_; lean_object* v___x_2844_; 
v___x_2842_ = ((lean_object*)(l_Lean_MVarId_splitAndCore___closed__1));
lean_inc(v_mvarId_2836_);
v___f_2843_ = lean_alloc_closure((void*)(l_Lean_MVarId_splitAndCore___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2843_, 0, v_mvarId_2836_);
lean_closure_set(v___f_2843_, 1, v___x_2842_);
v___x_2844_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2836_, v___f_2843_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_);
return v___x_2844_;
}
}
LEAN_EXPORT void l_Lean_MVarId_splitAndCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2836_ = stack[0].m_obj;
lean_object* v_a_2837_ = stack[1].m_obj;
lean_object* v_a_2838_ = stack[2].m_obj;
lean_object* v_a_2839_ = stack[3].m_obj;
lean_object* v_a_2840_ = stack[4].m_obj;
lean_object* v_res_2845_;
v_res_2845_ = l_Lean_MVarId_splitAndCore(v_mvarId_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_);
stack->m_obj
 = v_res_2845_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___boxed(lean_object* v_mvarId_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_){
_start:
{
lean_object* v_res_2852_; 
v_res_2852_ = l_Lean_MVarId_splitAndCore(v_mvarId_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_);
lean_dec(v_a_2850_);
lean_dec_ref(v_a_2849_);
lean_dec(v_a_2848_);
lean_dec_ref(v_a_2847_);
return v_res_2852_;
}
}
lean_object* l_Lean_MVarId_splitAnd(lean_object* v_mvarId_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_){
_start:
{
lean_object* v___x_2859_; 
v___x_2859_ = l_Lean_MVarId_splitAndCore(v_mvarId_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_);
return v___x_2859_;
}
}
LEAN_EXPORT void l_Lean_MVarId_splitAnd_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2853_ = stack[0].m_obj;
lean_object* v_a_2854_ = stack[1].m_obj;
lean_object* v_a_2855_ = stack[2].m_obj;
lean_object* v_a_2856_ = stack[3].m_obj;
lean_object* v_a_2857_ = stack[4].m_obj;
lean_object* v_res_2860_;
v_res_2860_ = l_Lean_MVarId_splitAnd(v_mvarId_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_);
stack->m_obj
 = v_res_2860_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAnd___boxed(lean_object* v_mvarId_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_){
_start:
{
lean_object* v_res_2867_; 
v_res_2867_ = l_Lean_MVarId_splitAnd(v_mvarId_2861_, v_a_2862_, v_a_2863_, v_a_2864_, v_a_2865_);
lean_dec(v_a_2865_);
lean_dec_ref(v_a_2864_);
lean_dec(v_a_2863_);
lean_dec_ref(v_a_2862_);
return v_res_2867_;
}
}
static lean_object* _init_l_Lean_MVarId_exfalso___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2871_ = lean_box(0);
v___x_2872_ = ((lean_object*)(l_Lean_MVarId_exfalso___lam__0___closed__1));
v___x_2873_ = l_Lean_mkConst(v___x_2872_, v___x_2871_);
return v___x_2873_;
}
}
lean_object* l_Lean_MVarId_exfalso___lam__0(lean_object* v_mvarId_2878_, lean_object* v___x_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_){
_start:
{
lean_object* v___x_2885_; 
lean_inc(v_mvarId_2878_);
v___x_2885_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2878_, v___x_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_object* v___x_2886_; 
lean_dec_ref_known(v___x_2885_, 1);
lean_inc(v_mvarId_2878_);
v___x_2886_ = l_Lean_MVarId_getType(v_mvarId_2878_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
if (lean_obj_tag(v___x_2886_) == 0)
{
lean_object* v_a_2887_; lean_object* v___x_2888_; lean_object* v_a_2889_; lean_object* v___x_2890_; 
v_a_2887_ = lean_ctor_get(v___x_2886_, 0);
lean_inc(v_a_2887_);
lean_dec_ref_known(v___x_2886_, 1);
v___x_2888_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_a_2887_, v___y_2881_);
v_a_2889_ = lean_ctor_get(v___x_2888_, 0);
lean_inc_n(v_a_2889_, 2);
lean_dec_ref(v___x_2888_);
v___x_2890_ = l_Lean_Meta_getLevel(v_a_2889_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v_a_2891_; lean_object* v___x_2892_; 
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
lean_inc(v_a_2891_);
lean_dec_ref_known(v___x_2890_, 1);
lean_inc(v_mvarId_2878_);
v___x_2892_ = l_Lean_MVarId_getTag(v_mvarId_2878_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v_a_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
lean_inc(v_a_2893_);
lean_dec_ref_known(v___x_2892_, 1);
v___x_2894_ = lean_box(0);
v___x_2895_ = lean_obj_once(&l_Lean_MVarId_exfalso___lam__0___closed__2, &l_Lean_MVarId_exfalso___lam__0___closed__2_once, _init_l_Lean_MVarId_exfalso___lam__0___closed__2);
v___x_2896_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2895_, v_a_2893_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_object* v_a_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2910_; 
v_a_2897_ = lean_ctor_get(v___x_2896_, 0);
lean_inc_n(v_a_2897_, 2);
lean_dec_ref_known(v___x_2896_, 1);
v___x_2898_ = ((lean_object*)(l_Lean_MVarId_exfalso___lam__0___closed__4));
v___x_2899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2899_, 0, v_a_2891_);
lean_ctor_set(v___x_2899_, 1, v___x_2894_);
v___x_2900_ = l_Lean_mkConst(v___x_2898_, v___x_2899_);
v___x_2901_ = l_Lean_mkAppB(v___x_2900_, v_a_2889_, v_a_2897_);
v___x_2902_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2878_, v___x_2901_, v___y_2881_);
v_isSharedCheck_2910_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2910_ == 0)
{
lean_object* v_unused_2911_; 
v_unused_2911_ = lean_ctor_get(v___x_2902_, 0);
lean_dec(v_unused_2911_);
v___x_2904_ = v___x_2902_;
v_isShared_2905_ = v_isSharedCheck_2910_;
goto v_resetjp_2903_;
}
else
{
lean_dec(v___x_2902_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2910_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___x_2906_; lean_object* v___x_2908_; 
v___x_2906_ = l_Lean_Expr_mvarId_x21(v_a_2897_);
lean_dec(v_a_2897_);
if (v_isShared_2905_ == 0)
{
lean_ctor_set(v___x_2904_, 0, v___x_2906_);
v___x_2908_ = v___x_2904_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v___x_2906_);
v___x_2908_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
return v___x_2908_;
}
}
}
else
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2919_; 
lean_dec(v_a_2891_);
lean_dec(v_a_2889_);
lean_dec(v_mvarId_2878_);
v_a_2912_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2914_ = v___x_2896_;
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2896_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2917_; 
if (v_isShared_2915_ == 0)
{
v___x_2917_ = v___x_2914_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_a_2912_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
}
else
{
lean_object* v_a_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2927_; 
lean_dec(v_a_2891_);
lean_dec(v_a_2889_);
lean_dec(v_mvarId_2878_);
v_a_2920_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2922_ = v___x_2892_;
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_a_2920_);
lean_dec(v___x_2892_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2925_; 
if (v_isShared_2923_ == 0)
{
v___x_2925_ = v___x_2922_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_a_2920_);
v___x_2925_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
return v___x_2925_;
}
}
}
}
else
{
lean_object* v_a_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2935_; 
lean_dec(v_a_2889_);
lean_dec(v_mvarId_2878_);
v_a_2928_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2930_ = v___x_2890_;
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_a_2928_);
lean_dec(v___x_2890_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2933_; 
if (v_isShared_2931_ == 0)
{
v___x_2933_ = v___x_2930_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_a_2928_);
v___x_2933_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
return v___x_2933_;
}
}
}
}
else
{
lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2943_; 
lean_dec(v_mvarId_2878_);
v_a_2936_ = lean_ctor_get(v___x_2886_, 0);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2886_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2938_ = v___x_2886_;
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_dec(v___x_2886_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2941_; 
if (v_isShared_2939_ == 0)
{
v___x_2941_ = v___x_2938_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_a_2936_);
v___x_2941_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
return v___x_2941_;
}
}
}
}
else
{
lean_object* v_a_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2951_; 
lean_dec(v_mvarId_2878_);
v_a_2944_ = lean_ctor_get(v___x_2885_, 0);
v_isSharedCheck_2951_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2946_ = v___x_2885_;
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_a_2944_);
lean_dec(v___x_2885_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2949_; 
if (v_isShared_2947_ == 0)
{
v___x_2949_ = v___x_2946_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_a_2944_);
v___x_2949_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
return v___x_2949_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_exfalso___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2878_ = stack[0].m_obj;
lean_object* v___x_2879_ = stack[1].m_obj;
lean_object* v___y_2880_ = stack[2].m_obj;
lean_object* v___y_2881_ = stack[3].m_obj;
lean_object* v___y_2882_ = stack[4].m_obj;
lean_object* v___y_2883_ = stack[5].m_obj;
lean_object* v_res_2952_;
v_res_2952_ = l_Lean_MVarId_exfalso___lam__0(v_mvarId_2878_, v___x_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
stack->m_obj
 = v_res_2952_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___lam__0___boxed(lean_object* v_mvarId_2953_, lean_object* v___x_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_){
_start:
{
lean_object* v_res_2960_; 
v_res_2960_ = l_Lean_MVarId_exfalso___lam__0(v_mvarId_2953_, v___x_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_);
lean_dec(v___y_2958_);
lean_dec_ref(v___y_2957_);
lean_dec(v___y_2956_);
lean_dec_ref(v___y_2955_);
return v_res_2960_;
}
}
lean_object* l_Lean_MVarId_exfalso(lean_object* v_mvarId_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_){
_start:
{
lean_object* v___x_2970_; lean_object* v___f_2971_; lean_object* v___x_2972_; 
v___x_2970_ = ((lean_object*)(l_Lean_MVarId_exfalso___closed__1));
lean_inc(v_mvarId_2964_);
v___f_2971_ = lean_alloc_closure((void*)(l_Lean_MVarId_exfalso___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2971_, 0, v_mvarId_2964_);
lean_closure_set(v___f_2971_, 1, v___x_2970_);
v___x_2972_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2964_, v___f_2971_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
return v___x_2972_;
}
}
LEAN_EXPORT void l_Lean_MVarId_exfalso_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2964_ = stack[0].m_obj;
lean_object* v_a_2965_ = stack[1].m_obj;
lean_object* v_a_2966_ = stack[2].m_obj;
lean_object* v_a_2967_ = stack[3].m_obj;
lean_object* v_a_2968_ = stack[4].m_obj;
lean_object* v_res_2973_;
v_res_2973_ = l_Lean_MVarId_exfalso(v_mvarId_2964_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
stack->m_obj
 = v_res_2973_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___boxed(lean_object* v_mvarId_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_){
_start:
{
lean_object* v_res_2980_; 
v_res_2980_ = l_Lean_MVarId_exfalso(v_mvarId_2974_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_);
lean_dec(v_a_2978_);
lean_dec_ref(v_a_2977_);
lean_dec(v_a_2976_);
lean_dec_ref(v_a_2975_);
return v_res_2980_;
}
}
static lean_object* _init_l_Lean_MVarId_nthConstructor___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2984_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__1));
v___x_2985_ = l_Lean_MessageData_ofFormat(v___x_2984_);
return v___x_2985_;
}
}
static lean_object* _init_l_Lean_MVarId_nthConstructor___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2986_ = lean_obj_once(&l_Lean_MVarId_nthConstructor___lam__0___closed__2, &l_Lean_MVarId_nthConstructor___lam__0___closed__2_once, _init_l_Lean_MVarId_nthConstructor___lam__0___closed__2);
v___x_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2986_);
return v___x_2987_;
}
}
lean_object* l_Lean_MVarId_nthConstructor___lam__0(lean_object* v_name_2992_, lean_object* v_goal_2993_, lean_object* v_idx_2994_, lean_object* v_expected_x3f_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_){
_start:
{
lean_object* v___x_3004_; 
lean_inc(v_name_2992_);
lean_inc(v_goal_2993_);
v___x_3004_ = l_Lean_MVarId_checkNotAssigned(v_goal_2993_, v_name_2992_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v___x_3005_; 
lean_dec_ref_known(v___x_3004_, 1);
lean_inc(v_goal_2993_);
v___x_3005_ = l_Lean_MVarId_getType_x27(v_goal_2993_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v_a_3006_; lean_object* v___x_3007_; 
v_a_3006_ = lean_ctor_get(v___x_3005_, 0);
lean_inc(v_a_3006_);
lean_dec_ref_known(v___x_3005_, 1);
v___x_3007_ = l_Lean_Expr_getAppFn(v_a_3006_);
lean_dec(v_a_3006_);
if (lean_obj_tag(v___x_3007_) == 4)
{
lean_object* v_declName_3008_; lean_object* v_us_3009_; lean_object* v___x_3010_; lean_object* v_env_3011_; uint8_t v___x_3012_; lean_object* v___x_3013_; 
v_declName_3008_ = lean_ctor_get(v___x_3007_, 0);
lean_inc(v_declName_3008_);
v_us_3009_ = lean_ctor_get(v___x_3007_, 1);
lean_inc(v_us_3009_);
lean_dec_ref_known(v___x_3007_, 2);
v___x_3010_ = lean_st_ref_get(v___y_2999_);
v_env_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc_ref(v_env_3011_);
lean_dec(v___x_3010_);
v___x_3012_ = 0;
v___x_3013_ = l_Lean_Environment_find_x3f(v_env_3011_, v_declName_3008_, v___x_3012_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_dec(v_us_3009_);
lean_dec(v_expected_x3f_2995_);
lean_dec(v_idx_2994_);
goto v___jp_3001_;
}
else
{
lean_object* v_val_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3084_; 
v_val_3014_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3016_ = v___x_3013_;
v_isShared_3017_ = v_isSharedCheck_3084_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_val_3014_);
lean_dec(v___x_3013_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3084_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
if (lean_obj_tag(v_val_3014_) == 5)
{
lean_object* v_val_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3083_; 
v_val_3018_ = lean_ctor_get(v_val_3014_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v_val_3014_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3020_ = v_val_3014_;
v_isShared_3021_ = v_isSharedCheck_3083_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_val_3018_);
lean_dec(v_val_3014_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3083_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; 
if (lean_obj_tag(v_expected_x3f_2995_) == 1)
{
lean_object* v_val_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3082_; 
v_val_3053_ = lean_ctor_get(v_expected_x3f_2995_, 0);
v_isSharedCheck_3082_ = !lean_is_exclusive(v_expected_x3f_2995_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3055_ = v_expected_x3f_2995_;
v_isShared_3056_ = v_isSharedCheck_3082_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_val_3053_);
lean_dec(v_expected_x3f_2995_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3082_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v_ctors_3057_; lean_object* v___x_3058_; uint8_t v___x_3059_; 
v_ctors_3057_ = lean_ctor_get(v_val_3018_, 4);
v___x_3058_ = l_List_lengthTR___redArg(v_ctors_3057_);
v___x_3059_ = lean_nat_dec_eq(v___x_3058_, v_val_3053_);
lean_dec(v___x_3058_);
if (v___x_3059_ == 0)
{
uint8_t v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3071_; 
v___x_3060_ = 1;
lean_inc(v_name_2992_);
v___x_3061_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2992_, v___x_3060_);
v___x_3062_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__7));
v___x_3063_ = lean_string_append(v___x_3061_, v___x_3062_);
v___x_3064_ = l_Nat_reprFast(v_val_3053_);
v___x_3065_ = lean_string_append(v___x_3063_, v___x_3064_);
lean_dec_ref(v___x_3064_);
v___x_3066_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__6));
v___x_3067_ = lean_string_append(v___x_3065_, v___x_3066_);
v___x_3068_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3067_);
v___x_3069_ = l_Lean_MessageData_ofFormat(v___x_3068_);
if (v_isShared_3056_ == 0)
{
lean_ctor_set(v___x_3055_, 0, v___x_3069_);
v___x_3071_ = v___x_3055_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v___x_3069_);
v___x_3071_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
lean_object* v___x_3072_; 
lean_inc(v_goal_2993_);
lean_inc(v_name_2992_);
v___x_3072_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2992_, v_goal_2993_, v___x_3071_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
if (lean_obj_tag(v___x_3072_) == 0)
{
lean_dec_ref_known(v___x_3072_, 1);
v___y_3023_ = v___y_2996_;
v___y_3024_ = v___y_2997_;
v___y_3025_ = v___y_2998_;
v___y_3026_ = v___y_2999_;
goto v___jp_3022_;
}
else
{
lean_object* v_a_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3080_; 
lean_del_object(v___x_3020_);
lean_dec_ref(v_val_3018_);
lean_del_object(v___x_3016_);
lean_dec(v_us_3009_);
lean_dec(v_idx_2994_);
lean_dec(v_goal_2993_);
lean_dec(v_name_2992_);
v_a_3073_ = lean_ctor_get(v___x_3072_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3072_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3075_ = v___x_3072_;
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_a_3073_);
lean_dec(v___x_3072_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
lean_object* v___x_3078_; 
if (v_isShared_3076_ == 0)
{
v___x_3078_ = v___x_3075_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_a_3073_);
v___x_3078_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
return v___x_3078_;
}
}
}
}
}
else
{
lean_del_object(v___x_3055_);
lean_dec(v_val_3053_);
v___y_3023_ = v___y_2996_;
v___y_3024_ = v___y_2997_;
v___y_3025_ = v___y_2998_;
v___y_3026_ = v___y_2999_;
goto v___jp_3022_;
}
}
}
else
{
lean_dec(v_expected_x3f_2995_);
v___y_3023_ = v___y_2996_;
v___y_3024_ = v___y_2997_;
v___y_3025_ = v___y_2998_;
v___y_3026_ = v___y_2999_;
goto v___jp_3022_;
}
v___jp_3022_:
{
lean_object* v_ctors_3027_; lean_object* v___x_3028_; uint8_t v___x_3029_; 
v_ctors_3027_ = lean_ctor_get(v_val_3018_, 4);
lean_inc(v_ctors_3027_);
lean_dec_ref(v_val_3018_);
v___x_3028_ = l_List_lengthTR___redArg(v_ctors_3027_);
v___x_3029_ = lean_nat_dec_lt(v_idx_2994_, v___x_3028_);
if (v___x_3029_ == 0)
{
lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3040_; 
lean_dec(v_ctors_3027_);
lean_dec(v_us_3009_);
v___x_3030_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__4));
v___x_3031_ = l_Nat_reprFast(v_idx_2994_);
v___x_3032_ = lean_string_append(v___x_3030_, v___x_3031_);
lean_dec_ref(v___x_3031_);
v___x_3033_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__5));
v___x_3034_ = lean_string_append(v___x_3032_, v___x_3033_);
v___x_3035_ = l_Nat_reprFast(v___x_3028_);
v___x_3036_ = lean_string_append(v___x_3034_, v___x_3035_);
lean_dec_ref(v___x_3035_);
v___x_3037_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__6));
v___x_3038_ = lean_string_append(v___x_3036_, v___x_3037_);
if (v_isShared_3021_ == 0)
{
lean_ctor_set_tag(v___x_3020_, 3);
lean_ctor_set(v___x_3020_, 0, v___x_3038_);
v___x_3040_ = v___x_3020_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v___x_3038_);
v___x_3040_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
lean_object* v___x_3041_; lean_object* v___x_3043_; 
v___x_3041_ = l_Lean_MessageData_ofFormat(v___x_3040_);
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 0, v___x_3041_);
v___x_3043_ = v___x_3016_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v___x_3041_);
v___x_3043_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
lean_object* v___x_3044_; 
v___x_3044_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2992_, v_goal_2993_, v___x_3043_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_);
return v___x_3044_;
}
}
}
else
{
lean_object* v___x_3047_; lean_object* v___x_3048_; uint8_t v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; 
lean_dec(v___x_3028_);
lean_del_object(v___x_3020_);
lean_del_object(v___x_3016_);
lean_dec(v_name_2992_);
v___x_3047_ = l_List_get___redArg(v_ctors_3027_, v_idx_2994_);
lean_dec(v_ctors_3027_);
v___x_3048_ = l_Lean_mkConst(v___x_3047_, v_us_3009_);
v___x_3049_ = 0;
v___x_3050_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3050_, 0, v___x_3049_);
lean_ctor_set_uint8(v___x_3050_, 1, v___x_3029_);
lean_ctor_set_uint8(v___x_3050_, 2, v___x_3012_);
lean_ctor_set_uint8(v___x_3050_, 3, v___x_3029_);
v___x_3051_ = lean_box(0);
v___x_3052_ = l_Lean_MVarId_apply(v_goal_2993_, v___x_3048_, v___x_3050_, v___x_3051_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_);
return v___x_3052_;
}
}
}
}
else
{
lean_del_object(v___x_3016_);
lean_dec(v_val_3014_);
lean_dec(v_us_3009_);
lean_dec(v_expected_x3f_2995_);
lean_dec(v_idx_2994_);
goto v___jp_3001_;
}
}
}
}
else
{
lean_dec_ref(v___x_3007_);
lean_dec(v_expected_x3f_2995_);
lean_dec(v_idx_2994_);
goto v___jp_3001_;
}
}
else
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3092_; 
lean_dec(v_expected_x3f_2995_);
lean_dec(v_idx_2994_);
lean_dec(v_goal_2993_);
lean_dec(v_name_2992_);
v_a_3085_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3087_ = v___x_3005_;
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3005_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3090_; 
if (v_isShared_3088_ == 0)
{
v___x_3090_ = v___x_3087_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_a_3085_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
}
}
else
{
lean_object* v_a_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3100_; 
lean_dec(v_expected_x3f_2995_);
lean_dec(v_idx_2994_);
lean_dec(v_goal_2993_);
lean_dec(v_name_2992_);
v_a_3093_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3095_ = v___x_3004_;
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_a_3093_);
lean_dec(v___x_3004_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3098_; 
if (v_isShared_3096_ == 0)
{
v___x_3098_ = v___x_3095_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_a_3093_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
return v___x_3098_;
}
}
}
v___jp_3001_:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; 
v___x_3002_ = lean_obj_once(&l_Lean_MVarId_nthConstructor___lam__0___closed__3, &l_Lean_MVarId_nthConstructor___lam__0___closed__3_once, _init_l_Lean_MVarId_nthConstructor___lam__0___closed__3);
v___x_3003_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2992_, v_goal_2993_, v___x_3002_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
return v___x_3003_;
}
}
}
LEAN_EXPORT void l_Lean_MVarId_nthConstructor___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2992_ = stack[0].m_obj;
lean_object* v_goal_2993_ = stack[1].m_obj;
lean_object* v_idx_2994_ = stack[2].m_obj;
lean_object* v_expected_x3f_2995_ = stack[3].m_obj;
lean_object* v___y_2996_ = stack[4].m_obj;
lean_object* v___y_2997_ = stack[5].m_obj;
lean_object* v___y_2998_ = stack[6].m_obj;
lean_object* v___y_2999_ = stack[7].m_obj;
lean_object* v_res_3101_;
v_res_3101_ = l_Lean_MVarId_nthConstructor___lam__0(v_name_2992_, v_goal_2993_, v_idx_2994_, v_expected_x3f_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
stack->m_obj
 = v_res_3101_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___lam__0___boxed(lean_object* v_name_3102_, lean_object* v_goal_3103_, lean_object* v_idx_3104_, lean_object* v_expected_x3f_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_){
_start:
{
lean_object* v_res_3111_; 
v_res_3111_ = l_Lean_MVarId_nthConstructor___lam__0(v_name_3102_, v_goal_3103_, v_idx_3104_, v_expected_x3f_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec(v___y_3107_);
lean_dec_ref(v___y_3106_);
return v_res_3111_;
}
}
lean_object* l_Lean_MVarId_nthConstructor(lean_object* v_name_3112_, lean_object* v_idx_3113_, lean_object* v_expected_x3f_3114_, lean_object* v_goal_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_){
_start:
{
lean_object* v___f_3121_; lean_object* v___x_3122_; 
lean_inc(v_goal_3115_);
v___f_3121_ = lean_alloc_closure((void*)(l_Lean_MVarId_nthConstructor___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3121_, 0, v_name_3112_);
lean_closure_set(v___f_3121_, 1, v_goal_3115_);
lean_closure_set(v___f_3121_, 2, v_idx_3113_);
lean_closure_set(v___f_3121_, 3, v_expected_x3f_3114_);
v___x_3122_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_goal_3115_, v___f_3121_, v_a_3116_, v_a_3117_, v_a_3118_, v_a_3119_);
return v___x_3122_;
}
}
LEAN_EXPORT void l_Lean_MVarId_nthConstructor_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_3112_ = stack[0].m_obj;
lean_object* v_idx_3113_ = stack[1].m_obj;
lean_object* v_expected_x3f_3114_ = stack[2].m_obj;
lean_object* v_goal_3115_ = stack[3].m_obj;
lean_object* v_a_3116_ = stack[4].m_obj;
lean_object* v_a_3117_ = stack[5].m_obj;
lean_object* v_a_3118_ = stack[6].m_obj;
lean_object* v_a_3119_ = stack[7].m_obj;
lean_object* v_res_3123_;
v_res_3123_ = l_Lean_MVarId_nthConstructor(v_name_3112_, v_idx_3113_, v_expected_x3f_3114_, v_goal_3115_, v_a_3116_, v_a_3117_, v_a_3118_, v_a_3119_);
stack->m_obj
 = v_res_3123_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___boxed(lean_object* v_name_3124_, lean_object* v_idx_3125_, lean_object* v_expected_x3f_3126_, lean_object* v_goal_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_){
_start:
{
lean_object* v_res_3133_; 
v_res_3133_ = l_Lean_MVarId_nthConstructor(v_name_3124_, v_idx_3125_, v_expected_x3f_3126_, v_goal_3127_, v_a_3128_, v_a_3129_, v_a_3130_, v_a_3131_);
lean_dec(v_a_3131_);
lean_dec_ref(v_a_3130_);
lean_dec(v_a_3129_);
lean_dec_ref(v_a_3128_);
return v_res_3133_;
}
}
lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(lean_object* v_x_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_){
_start:
{
lean_object* v___x_3140_; 
v___x_3140_ = l_Lean_Meta_saveState___redArg(v___y_3136_, v___y_3138_);
if (lean_obj_tag(v___x_3140_) == 0)
{
lean_object* v_a_3141_; lean_object* v___x_3142_; 
v_a_3141_ = lean_ctor_get(v___x_3140_, 0);
lean_inc(v_a_3141_);
lean_dec_ref_known(v___x_3140_, 1);
lean_inc(v___y_3138_);
lean_inc_ref(v___y_3137_);
lean_inc(v___y_3136_);
lean_inc_ref(v___y_3135_);
v___x_3142_ = lean_apply_5(v_x_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, lean_box(0));
if (lean_obj_tag(v___x_3142_) == 0)
{
lean_object* v_a_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3151_; 
lean_dec(v_a_3141_);
v_a_3143_ = lean_ctor_get(v___x_3142_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3145_ = v___x_3142_;
v_isShared_3146_ = v_isSharedCheck_3151_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_a_3143_);
lean_dec(v___x_3142_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3151_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v___x_3147_; lean_object* v___x_3149_; 
v___x_3147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3147_, 0, v_a_3143_);
if (v_isShared_3146_ == 0)
{
lean_ctor_set(v___x_3145_, 0, v___x_3147_);
v___x_3149_ = v___x_3145_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3147_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
else
{
lean_object* v_a_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3181_; 
v_a_3152_ = lean_ctor_get(v___x_3142_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3154_ = v___x_3142_;
v_isShared_3155_ = v_isSharedCheck_3181_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_a_3152_);
lean_dec(v___x_3142_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3181_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
uint8_t v___y_3157_; uint8_t v___x_3179_; 
v___x_3179_ = l_Lean_Exception_isInterrupt(v_a_3152_);
if (v___x_3179_ == 0)
{
uint8_t v___x_3180_; 
lean_inc(v_a_3152_);
v___x_3180_ = l_Lean_Exception_isRuntime(v_a_3152_);
v___y_3157_ = v___x_3180_;
goto v___jp_3156_;
}
else
{
v___y_3157_ = v___x_3179_;
goto v___jp_3156_;
}
v___jp_3156_:
{
if (v___y_3157_ == 0)
{
lean_object* v___x_3158_; 
lean_del_object(v___x_3154_);
lean_dec(v_a_3152_);
v___x_3158_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3141_, v___y_3136_, v___y_3138_);
if (lean_obj_tag(v___x_3158_) == 0)
{
lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3166_; 
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_3158_);
if (v_isSharedCheck_3166_ == 0)
{
lean_object* v_unused_3167_; 
v_unused_3167_ = lean_ctor_get(v___x_3158_, 0);
lean_dec(v_unused_3167_);
v___x_3160_ = v___x_3158_;
v_isShared_3161_ = v_isSharedCheck_3166_;
goto v_resetjp_3159_;
}
else
{
lean_dec(v___x_3158_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3166_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v___x_3162_; lean_object* v___x_3164_; 
v___x_3162_ = lean_box(0);
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 0, v___x_3162_);
v___x_3164_ = v___x_3160_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v___x_3162_);
v___x_3164_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
return v___x_3164_;
}
}
}
else
{
lean_object* v_a_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3175_; 
v_a_3168_ = lean_ctor_get(v___x_3158_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3158_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3170_ = v___x_3158_;
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_dec(v___x_3158_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3173_; 
if (v_isShared_3171_ == 0)
{
v___x_3173_ = v___x_3170_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_a_3168_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
}
}
else
{
lean_object* v___x_3177_; 
lean_dec(v_a_3141_);
if (v_isShared_3155_ == 0)
{
v___x_3177_ = v___x_3154_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_a_3152_);
v___x_3177_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
return v___x_3177_;
}
}
}
}
}
}
else
{
lean_object* v_a_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3189_; 
lean_dec_ref(v_x_3134_);
v_a_3182_ = lean_ctor_get(v___x_3140_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3184_ = v___x_3140_;
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_a_3182_);
lean_dec(v___x_3140_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3187_; 
if (v_isShared_3185_ == 0)
{
v___x_3187_ = v___x_3184_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_a_3182_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3134_ = stack[0].m_obj;
lean_object* v___y_3135_ = stack[1].m_obj;
lean_object* v___y_3136_ = stack[2].m_obj;
lean_object* v___y_3137_ = stack[3].m_obj;
lean_object* v___y_3138_ = stack[4].m_obj;
lean_object* v_res_3190_;
v_res_3190_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v_x_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_);
stack->m_obj
 = v_res_3190_;
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg___boxed(lean_object* v_x_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_){
_start:
{
lean_object* v_res_3197_; 
v_res_3197_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v_x_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3194_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
return v_res_3197_;
}
}
lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0(lean_object* v_00_u03b1_3198_, lean_object* v_x_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_){
_start:
{
lean_object* v___x_3205_; 
v___x_3205_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v_x_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_);
return v___x_3205_;
}
}
LEAN_EXPORT void l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3199_ = stack[1].m_obj;
lean_object* v___y_3200_ = stack[2].m_obj;
lean_object* v___y_3201_ = stack[3].m_obj;
lean_object* v___y_3202_ = stack[4].m_obj;
lean_object* v___y_3203_ = stack[5].m_obj;
lean_object* v_res_3206_;
v_res_3206_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0(lean_box(0), v_x_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_);
stack->m_obj
 = v_res_3206_;
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___boxed(lean_object* v_00_u03b1_3207_, lean_object* v_x_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_){
_start:
{
lean_object* v_res_3214_; 
v_res_3214_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0(v_00_u03b1_3207_, v_x_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_);
lean_dec(v___y_3212_);
lean_dec_ref(v___y_3211_);
lean_dec(v___y_3210_);
lean_dec_ref(v___y_3209_);
return v_res_3214_;
}
}
static lean_object* _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; 
v___x_3216_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___lam__0___closed__0));
v___x_3217_ = l_Lean_stringToMessageData(v___x_3216_);
return v___x_3217_;
}
}
lean_object* l_Lean_MVarId_iffOfEq___lam__0(lean_object* v_mvarId_3218_, lean_object* v___x_3219_, lean_object* v___x_3220_, lean_object* v___x_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_){
_start:
{
lean_object* v___x_3230_; 
v___x_3230_ = l_Lean_MVarId_apply(v_mvarId_3218_, v___x_3219_, v___x_3220_, v___x_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v_a_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3240_; 
v_a_3231_ = lean_ctor_get(v___x_3230_, 0);
v_isSharedCheck_3240_ = !lean_is_exclusive(v___x_3230_);
if (v_isSharedCheck_3240_ == 0)
{
v___x_3233_ = v___x_3230_;
v_isShared_3234_ = v_isSharedCheck_3240_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_a_3231_);
lean_dec(v___x_3230_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3240_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
if (lean_obj_tag(v_a_3231_) == 1)
{
lean_object* v_tail_3235_; 
v_tail_3235_ = lean_ctor_get(v_a_3231_, 1);
if (lean_obj_tag(v_tail_3235_) == 0)
{
lean_object* v_head_3236_; lean_object* v___x_3238_; 
v_head_3236_ = lean_ctor_get(v_a_3231_, 0);
lean_inc(v_head_3236_);
lean_dec_ref_known(v_a_3231_, 2);
if (v_isShared_3234_ == 0)
{
lean_ctor_set(v___x_3233_, 0, v_head_3236_);
v___x_3238_ = v___x_3233_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v_head_3236_);
v___x_3238_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
return v___x_3238_;
}
}
else
{
lean_dec_ref_known(v_a_3231_, 2);
lean_del_object(v___x_3233_);
goto v___jp_3227_;
}
}
else
{
lean_del_object(v___x_3233_);
lean_dec(v_a_3231_);
goto v___jp_3227_;
}
}
}
else
{
lean_object* v_a_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3248_; 
v_a_3241_ = lean_ctor_get(v___x_3230_, 0);
v_isSharedCheck_3248_ = !lean_is_exclusive(v___x_3230_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3243_ = v___x_3230_;
v_isShared_3244_ = v_isSharedCheck_3248_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_a_3241_);
lean_dec(v___x_3230_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3248_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
lean_object* v___x_3246_; 
if (v_isShared_3244_ == 0)
{
v___x_3246_ = v___x_3243_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v_a_3241_);
v___x_3246_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
return v___x_3246_;
}
}
}
v___jp_3227_:
{
lean_object* v___x_3228_; lean_object* v___x_3229_; 
v___x_3228_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3229_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3228_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
return v___x_3229_;
}
}
}
LEAN_EXPORT void l_Lean_MVarId_iffOfEq___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3218_ = stack[0].m_obj;
lean_object* v___x_3219_ = stack[1].m_obj;
lean_object* v___x_3220_ = stack[2].m_obj;
lean_object* v___x_3221_ = stack[3].m_obj;
lean_object* v___y_3222_ = stack[4].m_obj;
lean_object* v___y_3223_ = stack[5].m_obj;
lean_object* v___y_3224_ = stack[6].m_obj;
lean_object* v___y_3225_ = stack[7].m_obj;
lean_object* v_res_3249_;
v_res_3249_ = l_Lean_MVarId_iffOfEq___lam__0(v_mvarId_3218_, v___x_3219_, v___x_3220_, v___x_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
stack->m_obj
 = v_res_3249_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___lam__0___boxed(lean_object* v_mvarId_3250_, lean_object* v___x_3251_, lean_object* v___x_3252_, lean_object* v___x_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_){
_start:
{
lean_object* v_res_3259_; 
v_res_3259_ = l_Lean_MVarId_iffOfEq___lam__0(v_mvarId_3250_, v___x_3251_, v___x_3252_, v___x_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_);
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3256_);
lean_dec(v___y_3255_);
lean_dec_ref(v___y_3254_);
return v_res_3259_;
}
}
static lean_object* _init_l_Lean_MVarId_iffOfEq___closed__2(void){
_start:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; 
v___x_3263_ = lean_box(0);
v___x_3264_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___closed__1));
v___x_3265_ = l_Lean_mkConst(v___x_3264_, v___x_3263_);
return v___x_3265_;
}
}
lean_object* l_Lean_MVarId_iffOfEq(lean_object* v_mvarId_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_){
_start:
{
lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___f_3279_; lean_object* v___x_3280_; 
v___x_3276_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___closed__2, &l_Lean_MVarId_iffOfEq___closed__2_once, _init_l_Lean_MVarId_iffOfEq___closed__2);
v___x_3277_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___closed__3));
v___x_3278_ = lean_box(0);
lean_inc(v_mvarId_3270_);
v___f_3279_ = lean_alloc_closure((void*)(l_Lean_MVarId_iffOfEq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3279_, 0, v_mvarId_3270_);
lean_closure_set(v___f_3279_, 1, v___x_3276_);
lean_closure_set(v___f_3279_, 2, v___x_3277_);
lean_closure_set(v___f_3279_, 3, v___x_3278_);
v___x_3280_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3279_, v_a_3271_, v_a_3272_, v_a_3273_, v_a_3274_);
if (lean_obj_tag(v___x_3280_) == 0)
{
lean_object* v_a_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3292_; 
v_a_3281_ = lean_ctor_get(v___x_3280_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3283_ = v___x_3280_;
v_isShared_3284_ = v_isSharedCheck_3292_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_a_3281_);
lean_dec(v___x_3280_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3292_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
if (lean_obj_tag(v_a_3281_) == 0)
{
lean_object* v___x_3286_; 
if (v_isShared_3284_ == 0)
{
lean_ctor_set(v___x_3283_, 0, v_mvarId_3270_);
v___x_3286_ = v___x_3283_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_mvarId_3270_);
v___x_3286_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
return v___x_3286_;
}
}
else
{
lean_object* v_val_3288_; lean_object* v___x_3290_; 
lean_dec(v_mvarId_3270_);
v_val_3288_ = lean_ctor_get(v_a_3281_, 0);
lean_inc(v_val_3288_);
lean_dec_ref_known(v_a_3281_, 1);
if (v_isShared_3284_ == 0)
{
lean_ctor_set(v___x_3283_, 0, v_val_3288_);
v___x_3290_ = v___x_3283_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_val_3288_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
return v___x_3290_;
}
}
}
}
else
{
lean_object* v_a_3293_; lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3300_; 
lean_dec(v_mvarId_3270_);
v_a_3293_ = lean_ctor_get(v___x_3280_, 0);
v_isSharedCheck_3300_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3300_ == 0)
{
v___x_3295_ = v___x_3280_;
v_isShared_3296_ = v_isSharedCheck_3300_;
goto v_resetjp_3294_;
}
else
{
lean_inc(v_a_3293_);
lean_dec(v___x_3280_);
v___x_3295_ = lean_box(0);
v_isShared_3296_ = v_isSharedCheck_3300_;
goto v_resetjp_3294_;
}
v_resetjp_3294_:
{
lean_object* v___x_3298_; 
if (v_isShared_3296_ == 0)
{
v___x_3298_ = v___x_3295_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v_a_3293_);
v___x_3298_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
return v___x_3298_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_iffOfEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3270_ = stack[0].m_obj;
lean_object* v_a_3271_ = stack[1].m_obj;
lean_object* v_a_3272_ = stack[2].m_obj;
lean_object* v_a_3273_ = stack[3].m_obj;
lean_object* v_a_3274_ = stack[4].m_obj;
lean_object* v_res_3301_;
v_res_3301_ = l_Lean_MVarId_iffOfEq(v_mvarId_3270_, v_a_3271_, v_a_3272_, v_a_3273_, v_a_3274_);
stack->m_obj
 = v_res_3301_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___boxed(lean_object* v_mvarId_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_){
_start:
{
lean_object* v_res_3308_; 
v_res_3308_ = l_Lean_MVarId_iffOfEq(v_mvarId_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_);
lean_dec(v_a_3306_);
lean_dec_ref(v_a_3305_);
lean_dec(v_a_3304_);
lean_dec_ref(v_a_3303_);
return v_res_3308_;
}
}
static lean_object* _init_l_Lean_MVarId_propext___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; 
v___x_3312_ = lean_box(0);
v___x_3313_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__1));
v___x_3314_ = l_Lean_mkConst(v___x_3313_, v___x_3312_);
return v___x_3314_;
}
}
lean_object* l_Lean_MVarId_propext___lam__0(lean_object* v_mvarId_3318_, uint8_t v___x_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_){
_start:
{
lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; uint8_t v___y_3333_; lean_object* v___y_3359_; lean_object* v___x_3397_; uint8_t v_transparency_3398_; uint8_t v___x_3399_; 
v___x_3397_ = l_Lean_Meta_Context_config(v___y_3320_);
v_transparency_3398_ = lean_ctor_get_uint8(v___x_3397_, 9);
lean_dec_ref(v___x_3397_);
v___x_3399_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3398_, v___x_3319_);
if (v___x_3399_ == 0)
{
lean_object* v_keyedConfig_3400_; uint8_t v_trackZetaDelta_3401_; lean_object* v_zetaDeltaSet_3402_; lean_object* v_lctx_3403_; lean_object* v_localInstances_3404_; lean_object* v_defEqCtx_x3f_3405_; lean_object* v_synthPendingDepth_3406_; lean_object* v_customCanUnfoldPredicate_x3f_3407_; uint8_t v_univApprox_3408_; uint8_t v_inTypeClassResolution_3409_; uint8_t v_cacheInferType_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; 
v_keyedConfig_3400_ = lean_ctor_get(v___y_3320_, 0);
v_trackZetaDelta_3401_ = lean_ctor_get_uint8(v___y_3320_, sizeof(void*)*7);
v_zetaDeltaSet_3402_ = lean_ctor_get(v___y_3320_, 1);
v_lctx_3403_ = lean_ctor_get(v___y_3320_, 2);
v_localInstances_3404_ = lean_ctor_get(v___y_3320_, 3);
v_defEqCtx_x3f_3405_ = lean_ctor_get(v___y_3320_, 4);
v_synthPendingDepth_3406_ = lean_ctor_get(v___y_3320_, 5);
v_customCanUnfoldPredicate_x3f_3407_ = lean_ctor_get(v___y_3320_, 6);
v_univApprox_3408_ = lean_ctor_get_uint8(v___y_3320_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3409_ = lean_ctor_get_uint8(v___y_3320_, sizeof(void*)*7 + 2);
v_cacheInferType_3410_ = lean_ctor_get_uint8(v___y_3320_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3400_);
v___x_3411_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3319_, v_keyedConfig_3400_);
lean_inc(v_customCanUnfoldPredicate_x3f_3407_);
lean_inc(v_synthPendingDepth_3406_);
lean_inc(v_defEqCtx_x3f_3405_);
lean_inc_ref(v_localInstances_3404_);
lean_inc_ref(v_lctx_3403_);
lean_inc(v_zetaDeltaSet_3402_);
v___x_3412_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3412_, 0, v___x_3411_);
lean_ctor_set(v___x_3412_, 1, v_zetaDeltaSet_3402_);
lean_ctor_set(v___x_3412_, 2, v_lctx_3403_);
lean_ctor_set(v___x_3412_, 3, v_localInstances_3404_);
lean_ctor_set(v___x_3412_, 4, v_defEqCtx_x3f_3405_);
lean_ctor_set(v___x_3412_, 5, v_synthPendingDepth_3406_);
lean_ctor_set(v___x_3412_, 6, v_customCanUnfoldPredicate_x3f_3407_);
lean_ctor_set_uint8(v___x_3412_, sizeof(void*)*7, v_trackZetaDelta_3401_);
lean_ctor_set_uint8(v___x_3412_, sizeof(void*)*7 + 1, v_univApprox_3408_);
lean_ctor_set_uint8(v___x_3412_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3409_);
lean_ctor_set_uint8(v___x_3412_, sizeof(void*)*7 + 3, v_cacheInferType_3410_);
lean_inc(v_mvarId_3318_);
v___x_3413_ = l_Lean_MVarId_getType_x27(v_mvarId_3318_, v___x_3412_, v___y_3321_, v___y_3322_, v___y_3323_);
lean_dec_ref_known(v___x_3412_, 7);
v___y_3359_ = v___x_3413_;
goto v___jp_3358_;
}
else
{
lean_object* v___x_3414_; 
lean_inc(v_mvarId_3318_);
v___x_3414_ = l_Lean_MVarId_getType_x27(v_mvarId_3318_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_);
v___y_3359_ = v___x_3414_;
goto v___jp_3358_;
}
v___jp_3325_:
{
lean_object* v___x_3330_; lean_object* v___x_3331_; 
v___x_3330_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3331_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3330_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
lean_dec_ref(v___y_3326_);
return v___x_3331_;
}
v___jp_3332_:
{
lean_object* v___x_3334_; uint8_t v___x_3335_; uint8_t v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; 
v___x_3334_ = lean_obj_once(&l_Lean_MVarId_propext___lam__0___closed__2, &l_Lean_MVarId_propext___lam__0___closed__2_once, _init_l_Lean_MVarId_propext___lam__0___closed__2);
v___x_3335_ = 0;
v___x_3336_ = 0;
v___x_3337_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3337_, 0, v___x_3335_);
lean_ctor_set_uint8(v___x_3337_, 1, v___y_3333_);
lean_ctor_set_uint8(v___x_3337_, 2, v___x_3336_);
lean_ctor_set_uint8(v___x_3337_, 3, v___y_3333_);
v___x_3338_ = lean_box(0);
v___x_3339_ = l_Lean_MVarId_apply(v_mvarId_3318_, v___x_3334_, v___x_3337_, v___x_3338_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_);
if (lean_obj_tag(v___x_3339_) == 0)
{
lean_object* v_a_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3349_; 
v_a_3340_ = lean_ctor_get(v___x_3339_, 0);
v_isSharedCheck_3349_ = !lean_is_exclusive(v___x_3339_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3342_ = v___x_3339_;
v_isShared_3343_ = v_isSharedCheck_3349_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_a_3340_);
lean_dec(v___x_3339_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3349_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
if (lean_obj_tag(v_a_3340_) == 1)
{
lean_object* v_tail_3344_; 
v_tail_3344_ = lean_ctor_get(v_a_3340_, 1);
if (lean_obj_tag(v_tail_3344_) == 0)
{
lean_object* v_head_3345_; lean_object* v___x_3347_; 
lean_dec_ref(v___y_3320_);
v_head_3345_ = lean_ctor_get(v_a_3340_, 0);
lean_inc(v_head_3345_);
lean_dec_ref_known(v_a_3340_, 2);
if (v_isShared_3343_ == 0)
{
lean_ctor_set(v___x_3342_, 0, v_head_3345_);
v___x_3347_ = v___x_3342_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v_head_3345_);
v___x_3347_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
return v___x_3347_;
}
}
else
{
lean_dec_ref_known(v_a_3340_, 2);
lean_del_object(v___x_3342_);
v___y_3326_ = v___y_3320_;
v___y_3327_ = v___y_3321_;
v___y_3328_ = v___y_3322_;
v___y_3329_ = v___y_3323_;
goto v___jp_3325_;
}
}
else
{
lean_del_object(v___x_3342_);
lean_dec(v_a_3340_);
v___y_3326_ = v___y_3320_;
v___y_3327_ = v___y_3321_;
v___y_3328_ = v___y_3322_;
v___y_3329_ = v___y_3323_;
goto v___jp_3325_;
}
}
}
else
{
lean_object* v_a_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3357_; 
lean_dec_ref(v___y_3320_);
v_a_3350_ = lean_ctor_get(v___x_3339_, 0);
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3339_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3352_ = v___x_3339_;
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_a_3350_);
lean_dec(v___x_3339_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v___x_3355_; 
if (v_isShared_3353_ == 0)
{
v___x_3355_ = v___x_3352_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_a_3350_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
return v___x_3355_;
}
}
}
}
v___jp_3358_:
{
if (lean_obj_tag(v___y_3359_) == 0)
{
lean_object* v_a_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; uint8_t v___x_3363_; 
v_a_3360_ = lean_ctor_get(v___y_3359_, 0);
lean_inc(v_a_3360_);
lean_dec_ref_known(v___y_3359_, 1);
v___x_3361_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__4));
v___x_3362_ = lean_unsigned_to_nat(3u);
v___x_3363_ = l_Lean_Expr_isAppOfArity(v_a_3360_, v___x_3361_, v___x_3362_);
if (v___x_3363_ == 0)
{
lean_object* v___x_3364_; lean_object* v___x_3365_; 
lean_dec(v_a_3360_);
lean_dec(v_mvarId_3318_);
v___x_3364_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3365_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3364_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_);
lean_dec_ref(v___y_3320_);
return v___x_3365_;
}
else
{
lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; 
v___x_3366_ = l_Lean_Expr_appFn_x21(v_a_3360_);
lean_dec(v_a_3360_);
v___x_3367_ = l_Lean_Expr_appArg_x21(v___x_3366_);
lean_dec_ref(v___x_3366_);
v___x_3368_ = l_Lean_Meta_isProp(v___x_3367_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_);
if (lean_obj_tag(v___x_3368_) == 0)
{
lean_object* v_a_3369_; uint8_t v___x_3370_; 
v_a_3369_ = lean_ctor_get(v___x_3368_, 0);
lean_inc(v_a_3369_);
lean_dec_ref_known(v___x_3368_, 1);
v___x_3370_ = lean_unbox(v_a_3369_);
lean_dec(v_a_3369_);
if (v___x_3370_ == 0)
{
lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v_a_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3380_; 
lean_dec(v_mvarId_3318_);
v___x_3371_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3372_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3371_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_);
lean_dec_ref(v___y_3320_);
v_a_3373_ = lean_ctor_get(v___x_3372_, 0);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3375_ = v___x_3372_;
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_a_3373_);
lean_dec(v___x_3372_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3378_; 
if (v_isShared_3376_ == 0)
{
v___x_3378_ = v___x_3375_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_a_3373_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
return v___x_3378_;
}
}
}
else
{
v___y_3333_ = v___x_3363_;
goto v___jp_3332_;
}
}
else
{
lean_object* v_a_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3388_; 
lean_dec_ref(v___y_3320_);
lean_dec(v_mvarId_3318_);
v_a_3381_ = lean_ctor_get(v___x_3368_, 0);
v_isSharedCheck_3388_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3383_ = v___x_3368_;
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_a_3381_);
lean_dec(v___x_3368_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v___x_3386_; 
if (v_isShared_3384_ == 0)
{
v___x_3386_ = v___x_3383_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v_a_3381_);
v___x_3386_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
return v___x_3386_;
}
}
}
}
}
else
{
lean_object* v_a_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3396_; 
lean_dec_ref(v___y_3320_);
lean_dec(v_mvarId_3318_);
v_a_3389_ = lean_ctor_get(v___y_3359_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___y_3359_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3391_ = v___y_3359_;
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_a_3389_);
lean_dec(v___y_3359_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v___x_3394_; 
if (v_isShared_3392_ == 0)
{
v___x_3394_ = v___x_3391_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_a_3389_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_propext___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3318_ = stack[0].m_obj;
uint8_t v___x_3319_ = stack[1].m_num;
lean_object* v___y_3320_ = stack[2].m_obj;
lean_object* v___y_3321_ = stack[3].m_obj;
lean_object* v___y_3322_ = stack[4].m_obj;
lean_object* v___y_3323_ = stack[5].m_obj;
lean_object* v_res_3415_;
v_res_3415_ = l_Lean_MVarId_propext___lam__0(v_mvarId_3318_, v___x_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_);
stack->m_obj
 = v_res_3415_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___lam__0___boxed(lean_object* v_mvarId_3416_, lean_object* v___x_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_){
_start:
{
uint8_t v___x_2525__boxed_3423_; lean_object* v_res_3424_; 
v___x_2525__boxed_3423_ = lean_unbox(v___x_3417_);
v_res_3424_ = l_Lean_MVarId_propext___lam__0(v_mvarId_3416_, v___x_2525__boxed_3423_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_);
lean_dec(v___y_3421_);
lean_dec_ref(v___y_3420_);
lean_dec(v___y_3419_);
return v_res_3424_;
}
}
lean_object* l_Lean_MVarId_propext(lean_object* v_mvarId_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_){
_start:
{
uint8_t v___x_3431_; lean_object* v___x_3432_; lean_object* v___f_3433_; lean_object* v___x_3434_; 
v___x_3431_ = 2;
v___x_3432_ = lean_box(v___x_3431_);
lean_inc(v_mvarId_3425_);
v___f_3433_ = lean_alloc_closure((void*)(l_Lean_MVarId_propext___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3433_, 0, v_mvarId_3425_);
lean_closure_set(v___f_3433_, 1, v___x_3432_);
v___x_3434_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3433_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_);
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v_a_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3446_; 
v_a_3435_ = lean_ctor_get(v___x_3434_, 0);
v_isSharedCheck_3446_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3437_ = v___x_3434_;
v_isShared_3438_ = v_isSharedCheck_3446_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_a_3435_);
lean_dec(v___x_3434_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3446_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
if (lean_obj_tag(v_a_3435_) == 0)
{
lean_object* v___x_3440_; 
if (v_isShared_3438_ == 0)
{
lean_ctor_set(v___x_3437_, 0, v_mvarId_3425_);
v___x_3440_ = v___x_3437_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_mvarId_3425_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
else
{
lean_object* v_val_3442_; lean_object* v___x_3444_; 
lean_dec(v_mvarId_3425_);
v_val_3442_ = lean_ctor_get(v_a_3435_, 0);
lean_inc(v_val_3442_);
lean_dec_ref_known(v_a_3435_, 1);
if (v_isShared_3438_ == 0)
{
lean_ctor_set(v___x_3437_, 0, v_val_3442_);
v___x_3444_ = v___x_3437_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_val_3442_);
v___x_3444_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
return v___x_3444_;
}
}
}
}
else
{
lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3454_; 
lean_dec(v_mvarId_3425_);
v_a_3447_ = lean_ctor_get(v___x_3434_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3449_ = v___x_3434_;
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_a_3447_);
lean_dec(v___x_3434_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3452_; 
if (v_isShared_3450_ == 0)
{
v___x_3452_ = v___x_3449_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_a_3447_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_propext_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3425_ = stack[0].m_obj;
lean_object* v_a_3426_ = stack[1].m_obj;
lean_object* v_a_3427_ = stack[2].m_obj;
lean_object* v_a_3428_ = stack[3].m_obj;
lean_object* v_a_3429_ = stack[4].m_obj;
lean_object* v_res_3455_;
v_res_3455_ = l_Lean_MVarId_propext(v_mvarId_3425_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_);
stack->m_obj
 = v_res_3455_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___boxed(lean_object* v_mvarId_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_){
_start:
{
lean_object* v_res_3462_; 
v_res_3462_ = l_Lean_MVarId_propext(v_mvarId_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_);
lean_dec(v_a_3460_);
lean_dec_ref(v_a_3459_);
lean_dec(v_a_3458_);
lean_dec_ref(v_a_3457_);
return v_res_3462_;
}
}
lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0(lean_object* v_mvarId_3469_, lean_object* v___x_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_){
_start:
{
lean_object* v___y_3477_; lean_object* v___x_3521_; 
lean_inc(v_mvarId_3469_);
v___x_3521_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3469_, v___x_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v___x_3522_; uint8_t v_transparency_3523_; uint8_t v___x_3524_; uint8_t v___x_3525_; 
lean_dec_ref_known(v___x_3521_, 1);
v___x_3522_ = l_Lean_Meta_Context_config(v___y_3471_);
v_transparency_3523_ = lean_ctor_get_uint8(v___x_3522_, 9);
lean_dec_ref(v___x_3522_);
v___x_3524_ = 2;
v___x_3525_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3523_, v___x_3524_);
if (v___x_3525_ == 0)
{
lean_object* v_keyedConfig_3526_; uint8_t v_trackZetaDelta_3527_; lean_object* v_zetaDeltaSet_3528_; lean_object* v_lctx_3529_; lean_object* v_localInstances_3530_; lean_object* v_defEqCtx_x3f_3531_; lean_object* v_synthPendingDepth_3532_; lean_object* v_customCanUnfoldPredicate_x3f_3533_; uint8_t v_univApprox_3534_; uint8_t v_inTypeClassResolution_3535_; uint8_t v_cacheInferType_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; 
v_keyedConfig_3526_ = lean_ctor_get(v___y_3471_, 0);
v_trackZetaDelta_3527_ = lean_ctor_get_uint8(v___y_3471_, sizeof(void*)*7);
v_zetaDeltaSet_3528_ = lean_ctor_get(v___y_3471_, 1);
v_lctx_3529_ = lean_ctor_get(v___y_3471_, 2);
v_localInstances_3530_ = lean_ctor_get(v___y_3471_, 3);
v_defEqCtx_x3f_3531_ = lean_ctor_get(v___y_3471_, 4);
v_synthPendingDepth_3532_ = lean_ctor_get(v___y_3471_, 5);
v_customCanUnfoldPredicate_x3f_3533_ = lean_ctor_get(v___y_3471_, 6);
v_univApprox_3534_ = lean_ctor_get_uint8(v___y_3471_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3535_ = lean_ctor_get_uint8(v___y_3471_, sizeof(void*)*7 + 2);
v_cacheInferType_3536_ = lean_ctor_get_uint8(v___y_3471_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3526_);
v___x_3537_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3524_, v_keyedConfig_3526_);
lean_inc(v_customCanUnfoldPredicate_x3f_3533_);
lean_inc(v_synthPendingDepth_3532_);
lean_inc(v_defEqCtx_x3f_3531_);
lean_inc_ref(v_localInstances_3530_);
lean_inc_ref(v_lctx_3529_);
lean_inc(v_zetaDeltaSet_3528_);
v___x_3538_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3538_, 0, v___x_3537_);
lean_ctor_set(v___x_3538_, 1, v_zetaDeltaSet_3528_);
lean_ctor_set(v___x_3538_, 2, v_lctx_3529_);
lean_ctor_set(v___x_3538_, 3, v_localInstances_3530_);
lean_ctor_set(v___x_3538_, 4, v_defEqCtx_x3f_3531_);
lean_ctor_set(v___x_3538_, 5, v_synthPendingDepth_3532_);
lean_ctor_set(v___x_3538_, 6, v_customCanUnfoldPredicate_x3f_3533_);
lean_ctor_set_uint8(v___x_3538_, sizeof(void*)*7, v_trackZetaDelta_3527_);
lean_ctor_set_uint8(v___x_3538_, sizeof(void*)*7 + 1, v_univApprox_3534_);
lean_ctor_set_uint8(v___x_3538_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3535_);
lean_ctor_set_uint8(v___x_3538_, sizeof(void*)*7 + 3, v_cacheInferType_3536_);
lean_inc(v_mvarId_3469_);
v___x_3539_ = l_Lean_MVarId_getType_x27(v_mvarId_3469_, v___x_3538_, v___y_3472_, v___y_3473_, v___y_3474_);
lean_dec_ref_known(v___x_3538_, 7);
v___y_3477_ = v___x_3539_;
goto v___jp_3476_;
}
else
{
lean_object* v___x_3540_; 
lean_inc(v_mvarId_3469_);
v___x_3540_ = l_Lean_MVarId_getType_x27(v_mvarId_3469_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_);
v___y_3477_ = v___x_3540_;
goto v___jp_3476_;
}
}
else
{
lean_object* v_a_3541_; lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3548_; 
lean_dec_ref(v___y_3471_);
lean_dec(v_mvarId_3469_);
v_a_3541_ = lean_ctor_get(v___x_3521_, 0);
v_isSharedCheck_3548_ = !lean_is_exclusive(v___x_3521_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3543_ = v___x_3521_;
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
else
{
lean_inc(v_a_3541_);
lean_dec(v___x_3521_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v___x_3546_; 
if (v_isShared_3544_ == 0)
{
v___x_3546_ = v___x_3543_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_a_3541_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
return v___x_3546_;
}
}
}
v___jp_3476_:
{
if (lean_obj_tag(v___y_3477_) == 0)
{
lean_object* v_a_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; uint8_t v___x_3481_; 
v_a_3478_ = lean_ctor_get(v___y_3477_, 0);
lean_inc(v_a_3478_);
lean_dec_ref_known(v___y_3477_, 1);
v___x_3479_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__1));
v___x_3480_ = lean_unsigned_to_nat(4u);
v___x_3481_ = l_Lean_Expr_isAppOfArity(v_a_3478_, v___x_3479_, v___x_3480_);
if (v___x_3481_ == 0)
{
lean_object* v___x_3482_; lean_object* v___x_3483_; 
lean_dec(v_a_3478_);
lean_dec(v_mvarId_3469_);
v___x_3482_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3483_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3482_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_);
lean_dec_ref(v___y_3471_);
return v___x_3483_;
}
else
{
lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; 
v___x_3484_ = l_Lean_Expr_appFn_x21(v_a_3478_);
v___x_3485_ = l_Lean_Expr_appFn_x21(v___x_3484_);
lean_dec_ref(v___x_3484_);
v___x_3486_ = l_Lean_Expr_appArg_x21(v___x_3485_);
lean_dec_ref(v___x_3485_);
v___x_3487_ = l_Lean_Expr_appArg_x21(v_a_3478_);
lean_dec(v_a_3478_);
v___x_3488_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__3));
v___x_3489_ = lean_unsigned_to_nat(2u);
v___x_3490_ = lean_mk_empty_array_with_capacity(v___x_3489_);
v___x_3491_ = lean_array_push(v___x_3490_, v___x_3486_);
v___x_3492_ = lean_array_push(v___x_3491_, v___x_3487_);
v___x_3493_ = l_Lean_Meta_mkAppM(v___x_3488_, v___x_3492_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_);
lean_dec_ref(v___y_3471_);
if (lean_obj_tag(v___x_3493_) == 0)
{
lean_object* v_a_3494_; lean_object* v___x_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3503_; 
v_a_3494_ = lean_ctor_get(v___x_3493_, 0);
lean_inc(v_a_3494_);
lean_dec_ref_known(v___x_3493_, 1);
v___x_3495_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_3469_, v_a_3494_, v___y_3472_);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3503_ == 0)
{
lean_object* v_unused_3504_; 
v_unused_3504_ = lean_ctor_get(v___x_3495_, 0);
lean_dec(v_unused_3504_);
v___x_3497_ = v___x_3495_;
v_isShared_3498_ = v_isSharedCheck_3503_;
goto v_resetjp_3496_;
}
else
{
lean_dec(v___x_3495_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3503_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
lean_object* v___x_3499_; lean_object* v___x_3501_; 
v___x_3499_ = lean_box(v___x_3481_);
if (v_isShared_3498_ == 0)
{
lean_ctor_set(v___x_3497_, 0, v___x_3499_);
v___x_3501_ = v___x_3497_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v___x_3499_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
else
{
lean_object* v_a_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3512_; 
lean_dec(v_mvarId_3469_);
v_a_3505_ = lean_ctor_get(v___x_3493_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3507_ = v___x_3493_;
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_a_3505_);
lean_dec(v___x_3493_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3510_; 
if (v_isShared_3508_ == 0)
{
v___x_3510_ = v___x_3507_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3505_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
}
}
}
else
{
lean_object* v_a_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3520_; 
lean_dec_ref(v___y_3471_);
lean_dec(v_mvarId_3469_);
v_a_3513_ = lean_ctor_get(v___y_3477_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v___y_3477_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3515_ = v___y_3477_;
v_isShared_3516_ = v_isSharedCheck_3520_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_a_3513_);
lean_dec(v___y_3477_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3520_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3518_; 
if (v_isShared_3516_ == 0)
{
v___x_3518_ = v___x_3515_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v_a_3513_);
v___x_3518_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
return v___x_3518_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_proofIrrelHeq___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3469_ = stack[0].m_obj;
lean_object* v___x_3470_ = stack[1].m_obj;
lean_object* v___y_3471_ = stack[2].m_obj;
lean_object* v___y_3472_ = stack[3].m_obj;
lean_object* v___y_3473_ = stack[4].m_obj;
lean_object* v___y_3474_ = stack[5].m_obj;
lean_object* v_res_3549_;
v_res_3549_ = l_Lean_MVarId_proofIrrelHeq___lam__0(v_mvarId_3469_, v___x_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_);
stack->m_obj
 = v_res_3549_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0___boxed(lean_object* v_mvarId_3550_, lean_object* v___x_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_){
_start:
{
lean_object* v_res_3557_; 
v_res_3557_ = l_Lean_MVarId_proofIrrelHeq___lam__0(v_mvarId_3550_, v___x_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_);
lean_dec(v___y_3555_);
lean_dec_ref(v___y_3554_);
lean_dec(v___y_3553_);
return v_res_3557_;
}
}
lean_object* l_Lean_MVarId_proofIrrelHeq___lam__1(lean_object* v___f_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_){
_start:
{
lean_object* v___x_3564_; 
v___x_3564_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_);
if (lean_obj_tag(v___x_3564_) == 0)
{
lean_object* v_a_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3578_; 
v_a_3565_ = lean_ctor_get(v___x_3564_, 0);
v_isSharedCheck_3578_ = !lean_is_exclusive(v___x_3564_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3567_ = v___x_3564_;
v_isShared_3568_ = v_isSharedCheck_3578_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_a_3565_);
lean_dec(v___x_3564_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3578_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
if (lean_obj_tag(v_a_3565_) == 0)
{
uint8_t v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3572_; 
v___x_3569_ = 0;
v___x_3570_ = lean_box(v___x_3569_);
if (v_isShared_3568_ == 0)
{
lean_ctor_set(v___x_3567_, 0, v___x_3570_);
v___x_3572_ = v___x_3567_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v___x_3570_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
else
{
lean_object* v_val_3574_; lean_object* v___x_3576_; 
v_val_3574_ = lean_ctor_get(v_a_3565_, 0);
lean_inc(v_val_3574_);
lean_dec_ref_known(v_a_3565_, 1);
if (v_isShared_3568_ == 0)
{
lean_ctor_set(v___x_3567_, 0, v_val_3574_);
v___x_3576_ = v___x_3567_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v_val_3574_);
v___x_3576_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
return v___x_3576_;
}
}
}
}
else
{
lean_object* v_a_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3586_; 
v_a_3579_ = lean_ctor_get(v___x_3564_, 0);
v_isSharedCheck_3586_ = !lean_is_exclusive(v___x_3564_);
if (v_isSharedCheck_3586_ == 0)
{
v___x_3581_ = v___x_3564_;
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_a_3579_);
lean_dec(v___x_3564_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3584_; 
if (v_isShared_3582_ == 0)
{
v___x_3584_ = v___x_3581_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v_a_3579_);
v___x_3584_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
return v___x_3584_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_proofIrrelHeq___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_3558_ = stack[0].m_obj;
lean_object* v___y_3559_ = stack[1].m_obj;
lean_object* v___y_3560_ = stack[2].m_obj;
lean_object* v___y_3561_ = stack[3].m_obj;
lean_object* v___y_3562_ = stack[4].m_obj;
lean_object* v_res_3587_;
v_res_3587_ = l_Lean_MVarId_proofIrrelHeq___lam__1(v___f_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_);
stack->m_obj
 = v_res_3587_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__1___boxed(lean_object* v___f_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_){
_start:
{
lean_object* v_res_3594_; 
v_res_3594_ = l_Lean_MVarId_proofIrrelHeq___lam__1(v___f_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_);
lean_dec(v___y_3592_);
lean_dec_ref(v___y_3591_);
lean_dec(v___y_3590_);
lean_dec_ref(v___y_3589_);
return v_res_3594_;
}
}
lean_object* l_Lean_MVarId_proofIrrelHeq(lean_object* v_mvarId_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_){
_start:
{
lean_object* v___x_3604_; lean_object* v___f_3605_; lean_object* v___f_3606_; lean_object* v___x_3607_; 
v___x_3604_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___closed__1));
lean_inc(v_mvarId_3598_);
v___f_3605_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3605_, 0, v_mvarId_3598_);
lean_closure_set(v___f_3605_, 1, v___x_3604_);
v___f_3606_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__1___boxed), 6, 1);
lean_closure_set(v___f_3606_, 0, v___f_3605_);
v___x_3607_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_3598_, v___f_3606_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_);
return v___x_3607_;
}
}
LEAN_EXPORT void l_Lean_MVarId_proofIrrelHeq_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3598_ = stack[0].m_obj;
lean_object* v_a_3599_ = stack[1].m_obj;
lean_object* v_a_3600_ = stack[2].m_obj;
lean_object* v_a_3601_ = stack[3].m_obj;
lean_object* v_a_3602_ = stack[4].m_obj;
lean_object* v_res_3608_;
v_res_3608_ = l_Lean_MVarId_proofIrrelHeq(v_mvarId_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_);
stack->m_obj
 = v_res_3608_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___boxed(lean_object* v_mvarId_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_){
_start:
{
lean_object* v_res_3615_; 
v_res_3615_ = l_Lean_MVarId_proofIrrelHeq(v_mvarId_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_);
lean_dec(v_a_3613_);
lean_dec_ref(v_a_3612_);
lean_dec(v_a_3611_);
lean_dec_ref(v_a_3610_);
return v_res_3615_;
}
}
lean_object* l_Lean_MVarId_subsingletonElim___lam__0(lean_object* v_mvarId_3620_, lean_object* v___x_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_){
_start:
{
lean_object* v___y_3628_; lean_object* v___x_3671_; 
lean_inc(v_mvarId_3620_);
v___x_3671_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3620_, v___x_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_);
if (lean_obj_tag(v___x_3671_) == 0)
{
lean_object* v___x_3672_; uint8_t v_transparency_3673_; uint8_t v___x_3674_; uint8_t v___x_3675_; 
lean_dec_ref_known(v___x_3671_, 1);
v___x_3672_ = l_Lean_Meta_Context_config(v___y_3622_);
v_transparency_3673_ = lean_ctor_get_uint8(v___x_3672_, 9);
lean_dec_ref(v___x_3672_);
v___x_3674_ = 2;
v___x_3675_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3673_, v___x_3674_);
if (v___x_3675_ == 0)
{
lean_object* v_keyedConfig_3676_; uint8_t v_trackZetaDelta_3677_; lean_object* v_zetaDeltaSet_3678_; lean_object* v_lctx_3679_; lean_object* v_localInstances_3680_; lean_object* v_defEqCtx_x3f_3681_; lean_object* v_synthPendingDepth_3682_; lean_object* v_customCanUnfoldPredicate_x3f_3683_; uint8_t v_univApprox_3684_; uint8_t v_inTypeClassResolution_3685_; uint8_t v_cacheInferType_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; 
v_keyedConfig_3676_ = lean_ctor_get(v___y_3622_, 0);
v_trackZetaDelta_3677_ = lean_ctor_get_uint8(v___y_3622_, sizeof(void*)*7);
v_zetaDeltaSet_3678_ = lean_ctor_get(v___y_3622_, 1);
v_lctx_3679_ = lean_ctor_get(v___y_3622_, 2);
v_localInstances_3680_ = lean_ctor_get(v___y_3622_, 3);
v_defEqCtx_x3f_3681_ = lean_ctor_get(v___y_3622_, 4);
v_synthPendingDepth_3682_ = lean_ctor_get(v___y_3622_, 5);
v_customCanUnfoldPredicate_x3f_3683_ = lean_ctor_get(v___y_3622_, 6);
v_univApprox_3684_ = lean_ctor_get_uint8(v___y_3622_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3685_ = lean_ctor_get_uint8(v___y_3622_, sizeof(void*)*7 + 2);
v_cacheInferType_3686_ = lean_ctor_get_uint8(v___y_3622_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3676_);
v___x_3687_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3674_, v_keyedConfig_3676_);
lean_inc(v_customCanUnfoldPredicate_x3f_3683_);
lean_inc(v_synthPendingDepth_3682_);
lean_inc(v_defEqCtx_x3f_3681_);
lean_inc_ref(v_localInstances_3680_);
lean_inc_ref(v_lctx_3679_);
lean_inc(v_zetaDeltaSet_3678_);
v___x_3688_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3688_, 0, v___x_3687_);
lean_ctor_set(v___x_3688_, 1, v_zetaDeltaSet_3678_);
lean_ctor_set(v___x_3688_, 2, v_lctx_3679_);
lean_ctor_set(v___x_3688_, 3, v_localInstances_3680_);
lean_ctor_set(v___x_3688_, 4, v_defEqCtx_x3f_3681_);
lean_ctor_set(v___x_3688_, 5, v_synthPendingDepth_3682_);
lean_ctor_set(v___x_3688_, 6, v_customCanUnfoldPredicate_x3f_3683_);
lean_ctor_set_uint8(v___x_3688_, sizeof(void*)*7, v_trackZetaDelta_3677_);
lean_ctor_set_uint8(v___x_3688_, sizeof(void*)*7 + 1, v_univApprox_3684_);
lean_ctor_set_uint8(v___x_3688_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3685_);
lean_ctor_set_uint8(v___x_3688_, sizeof(void*)*7 + 3, v_cacheInferType_3686_);
lean_inc(v_mvarId_3620_);
v___x_3689_ = l_Lean_MVarId_getType_x27(v_mvarId_3620_, v___x_3688_, v___y_3623_, v___y_3624_, v___y_3625_);
lean_dec_ref_known(v___x_3688_, 7);
v___y_3628_ = v___x_3689_;
goto v___jp_3627_;
}
else
{
lean_object* v___x_3690_; 
lean_inc(v_mvarId_3620_);
v___x_3690_ = l_Lean_MVarId_getType_x27(v_mvarId_3620_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_);
v___y_3628_ = v___x_3690_;
goto v___jp_3627_;
}
}
else
{
lean_object* v_a_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3698_; 
lean_dec_ref(v___y_3622_);
lean_dec(v_mvarId_3620_);
v_a_3691_ = lean_ctor_get(v___x_3671_, 0);
v_isSharedCheck_3698_ = !lean_is_exclusive(v___x_3671_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3693_ = v___x_3671_;
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_a_3691_);
lean_dec(v___x_3671_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v___x_3696_; 
if (v_isShared_3694_ == 0)
{
v___x_3696_ = v___x_3693_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_a_3691_);
v___x_3696_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
return v___x_3696_;
}
}
}
v___jp_3627_:
{
if (lean_obj_tag(v___y_3628_) == 0)
{
lean_object* v_a_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; uint8_t v___x_3632_; 
v_a_3629_ = lean_ctor_get(v___y_3628_, 0);
lean_inc(v_a_3629_);
lean_dec_ref_known(v___y_3628_, 1);
v___x_3630_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__4));
v___x_3631_ = lean_unsigned_to_nat(3u);
v___x_3632_ = l_Lean_Expr_isAppOfArity(v_a_3629_, v___x_3630_, v___x_3631_);
if (v___x_3632_ == 0)
{
lean_object* v___x_3633_; lean_object* v___x_3634_; 
lean_dec(v_a_3629_);
lean_dec(v_mvarId_3620_);
v___x_3633_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3634_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3633_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_);
lean_dec_ref(v___y_3622_);
return v___x_3634_;
}
else
{
lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; 
v___x_3635_ = l_Lean_Expr_appFn_x21(v_a_3629_);
v___x_3636_ = l_Lean_Expr_appArg_x21(v___x_3635_);
lean_dec_ref(v___x_3635_);
v___x_3637_ = l_Lean_Expr_appArg_x21(v_a_3629_);
lean_dec(v_a_3629_);
v___x_3638_ = ((lean_object*)(l_Lean_MVarId_subsingletonElim___lam__0___closed__1));
v___x_3639_ = lean_unsigned_to_nat(2u);
v___x_3640_ = lean_mk_empty_array_with_capacity(v___x_3639_);
v___x_3641_ = lean_array_push(v___x_3640_, v___x_3636_);
v___x_3642_ = lean_array_push(v___x_3641_, v___x_3637_);
v___x_3643_ = l_Lean_Meta_mkAppM(v___x_3638_, v___x_3642_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_);
lean_dec_ref(v___y_3622_);
if (lean_obj_tag(v___x_3643_) == 0)
{
lean_object* v_a_3644_; lean_object* v___x_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3653_; 
v_a_3644_ = lean_ctor_get(v___x_3643_, 0);
lean_inc(v_a_3644_);
lean_dec_ref_known(v___x_3643_, 1);
v___x_3645_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_3620_, v_a_3644_, v___y_3623_);
v_isSharedCheck_3653_ = !lean_is_exclusive(v___x_3645_);
if (v_isSharedCheck_3653_ == 0)
{
lean_object* v_unused_3654_; 
v_unused_3654_ = lean_ctor_get(v___x_3645_, 0);
lean_dec(v_unused_3654_);
v___x_3647_ = v___x_3645_;
v_isShared_3648_ = v_isSharedCheck_3653_;
goto v_resetjp_3646_;
}
else
{
lean_dec(v___x_3645_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3653_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v___x_3649_; lean_object* v___x_3651_; 
v___x_3649_ = lean_box(v___x_3632_);
if (v_isShared_3648_ == 0)
{
lean_ctor_set(v___x_3647_, 0, v___x_3649_);
v___x_3651_ = v___x_3647_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v___x_3649_);
v___x_3651_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
return v___x_3651_;
}
}
}
else
{
lean_object* v_a_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3662_; 
lean_dec(v_mvarId_3620_);
v_a_3655_ = lean_ctor_get(v___x_3643_, 0);
v_isSharedCheck_3662_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3657_ = v___x_3643_;
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_a_3655_);
lean_dec(v___x_3643_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v___x_3660_; 
if (v_isShared_3658_ == 0)
{
v___x_3660_ = v___x_3657_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_a_3655_);
v___x_3660_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
return v___x_3660_;
}
}
}
}
}
else
{
lean_object* v_a_3663_; lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3670_; 
lean_dec_ref(v___y_3622_);
lean_dec(v_mvarId_3620_);
v_a_3663_ = lean_ctor_get(v___y_3628_, 0);
v_isSharedCheck_3670_ = !lean_is_exclusive(v___y_3628_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3665_ = v___y_3628_;
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
else
{
lean_inc(v_a_3663_);
lean_dec(v___y_3628_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
lean_object* v___x_3668_; 
if (v_isShared_3666_ == 0)
{
v___x_3668_ = v___x_3665_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_a_3663_);
v___x_3668_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
return v___x_3668_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_subsingletonElim___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3620_ = stack[0].m_obj;
lean_object* v___x_3621_ = stack[1].m_obj;
lean_object* v___y_3622_ = stack[2].m_obj;
lean_object* v___y_3623_ = stack[3].m_obj;
lean_object* v___y_3624_ = stack[4].m_obj;
lean_object* v___y_3625_ = stack[5].m_obj;
lean_object* v_res_3699_;
v_res_3699_ = l_Lean_MVarId_subsingletonElim___lam__0(v_mvarId_3620_, v___x_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_);
stack->m_obj
 = v_res_3699_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___lam__0___boxed(lean_object* v_mvarId_3700_, lean_object* v___x_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_){
_start:
{
lean_object* v_res_3707_; 
v_res_3707_ = l_Lean_MVarId_subsingletonElim___lam__0(v_mvarId_3700_, v___x_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec(v___y_3703_);
return v_res_3707_;
}
}
lean_object* l_Lean_MVarId_subsingletonElim(lean_object* v_mvarId_3711_, lean_object* v_a_3712_, lean_object* v_a_3713_, lean_object* v_a_3714_, lean_object* v_a_3715_){
_start:
{
lean_object* v___x_3717_; lean_object* v___f_3718_; lean_object* v___f_3719_; lean_object* v___x_3720_; 
v___x_3717_ = ((lean_object*)(l_Lean_MVarId_subsingletonElim___closed__1));
lean_inc(v_mvarId_3711_);
v___f_3718_ = lean_alloc_closure((void*)(l_Lean_MVarId_subsingletonElim___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3718_, 0, v_mvarId_3711_);
lean_closure_set(v___f_3718_, 1, v___x_3717_);
v___f_3719_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__1___boxed), 6, 1);
lean_closure_set(v___f_3719_, 0, v___f_3718_);
v___x_3720_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_3711_, v___f_3719_, v_a_3712_, v_a_3713_, v_a_3714_, v_a_3715_);
return v___x_3720_;
}
}
LEAN_EXPORT void l_Lean_MVarId_subsingletonElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3711_ = stack[0].m_obj;
lean_object* v_a_3712_ = stack[1].m_obj;
lean_object* v_a_3713_ = stack[2].m_obj;
lean_object* v_a_3714_ = stack[3].m_obj;
lean_object* v_a_3715_ = stack[4].m_obj;
lean_object* v_res_3721_;
v_res_3721_ = l_Lean_MVarId_subsingletonElim(v_mvarId_3711_, v_a_3712_, v_a_3713_, v_a_3714_, v_a_3715_);
stack->m_obj
 = v_res_3721_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___boxed(lean_object* v_mvarId_3722_, lean_object* v_a_3723_, lean_object* v_a_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_){
_start:
{
lean_object* v_res_3728_; 
v_res_3728_ = l_Lean_MVarId_subsingletonElim(v_mvarId_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
lean_dec(v_a_3726_);
lean_dec_ref(v_a_3725_);
lean_dec(v_a_3724_);
lean_dec_ref(v_a_3723_);
return v_res_3728_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_PrettyPrinter(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Apply(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_PrettyPrinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Apply(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin);
lean_object* initialize_Lean_PrettyPrinter(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Apply(builtin);
}
#ifdef __cplusplus
}
#endif
