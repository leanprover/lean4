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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg___lam__0(lean_object* v_k_1_, lean_object* v_b_2_, lean_object* v_c_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg___lam__0___boxed(lean_object* v_k_10_, lean_object* v_b_11_, lean_object* v_c_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg___lam__0(v_k_10_, v_b_11_, v_c_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
lean_dec(v___y_14_);
lean_dec_ref(v___y_13_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg(lean_object* v_type_19_, lean_object* v_k_20_, uint8_t v_cleanupAnnotations_21_, uint8_t v_whnfType_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_){
_start:
{
lean_object* v___f_28_; lean_object* v___x_29_; 
v___f_28_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg___lam__0___boxed), 8, 1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg___boxed(lean_object* v_type_46_, lean_object* v_k_47_, lean_object* v_cleanupAnnotations_48_, lean_object* v_whnfType_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_55_; uint8_t v_whnfType_boxed_56_; lean_object* v_res_57_; 
v_cleanupAnnotations_boxed_55_ = lean_unbox(v_cleanupAnnotations_48_);
v_whnfType_boxed_56_ = lean_unbox(v_whnfType_49_);
v_res_57_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg(v_type_46_, v_k_47_, v_cleanupAnnotations_boxed_55_, v_whnfType_boxed_56_, v___y_50_, v___y_51_, v___y_52_, v___y_53_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0(lean_object* v_00_u03b1_58_, lean_object* v_type_59_, lean_object* v_k_60_, uint8_t v_cleanupAnnotations_61_, uint8_t v_whnfType_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg(v_type_59_, v_k_60_, v_cleanupAnnotations_61_, v_whnfType_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___boxed(lean_object* v_00_u03b1_69_, lean_object* v_type_70_, lean_object* v_k_71_, lean_object* v_cleanupAnnotations_72_, lean_object* v_whnfType_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_79_; uint8_t v_whnfType_boxed_80_; lean_object* v_res_81_; 
v_cleanupAnnotations_boxed_79_ = lean_unbox(v_cleanupAnnotations_72_);
v_whnfType_boxed_80_ = lean_unbox(v_whnfType_73_);
v_res_81_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0(v_00_u03b1_69_, v_type_70_, v_k_71_, v_cleanupAnnotations_boxed_79_, v_whnfType_boxed_80_, v___y_74_, v___y_75_, v___y_76_, v___y_77_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgsAux___lam__0(lean_object* v_xs_82_, lean_object* v_body_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_89_ = lean_array_get_size(v_xs_82_);
v___x_90_ = l_Lean_Expr_getAppFn(v_body_83_);
v___x_91_ = l_Lean_Expr_isMVar(v___x_90_);
lean_dec_ref(v___x_90_);
v___x_92_ = lean_box(v___x_91_);
v___x_93_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_89_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
v___x_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgsAux___lam__0___boxed(lean_object* v_xs_95_, lean_object* v_body_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Lean_Meta_getExpectedNumArgsAux___lam__0(v_xs_95_, v_body_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
lean_dec_ref(v_body_96_);
lean_dec_ref(v_xs_95_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgsAux(lean_object* v_e_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_){
_start:
{
lean_object* v___y_111_; lean_object* v___x_128_; uint8_t v_transparency_129_; lean_object* v___f_130_; uint8_t v___x_131_; uint8_t v___x_132_; uint8_t v___x_133_; 
v___x_128_ = l_Lean_Meta_Context_config(v_a_105_);
v_transparency_129_ = lean_ctor_get_uint8(v___x_128_, 9);
lean_dec_ref(v___x_128_);
v___f_130_ = ((lean_object*)(l_Lean_Meta_getExpectedNumArgsAux___closed__0));
v___x_131_ = 0;
v___x_132_ = 1;
v___x_133_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_129_, v___x_132_);
if (v___x_133_ == 0)
{
lean_object* v_keyedConfig_134_; uint8_t v_trackZetaDelta_135_; lean_object* v_zetaDeltaSet_136_; lean_object* v_lctx_137_; lean_object* v_localInstances_138_; lean_object* v_defEqCtx_x3f_139_; lean_object* v_synthPendingDepth_140_; lean_object* v_customCanUnfoldPredicate_x3f_141_; uint8_t v_univApprox_142_; uint8_t v_inTypeClassResolution_143_; uint8_t v_cacheInferType_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v_keyedConfig_134_ = lean_ctor_get(v_a_105_, 0);
v_trackZetaDelta_135_ = lean_ctor_get_uint8(v_a_105_, sizeof(void*)*7);
v_zetaDeltaSet_136_ = lean_ctor_get(v_a_105_, 1);
v_lctx_137_ = lean_ctor_get(v_a_105_, 2);
v_localInstances_138_ = lean_ctor_get(v_a_105_, 3);
v_defEqCtx_x3f_139_ = lean_ctor_get(v_a_105_, 4);
v_synthPendingDepth_140_ = lean_ctor_get(v_a_105_, 5);
v_customCanUnfoldPredicate_x3f_141_ = lean_ctor_get(v_a_105_, 6);
v_univApprox_142_ = lean_ctor_get_uint8(v_a_105_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_143_ = lean_ctor_get_uint8(v_a_105_, sizeof(void*)*7 + 2);
v_cacheInferType_144_ = lean_ctor_get_uint8(v_a_105_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_134_);
v___x_145_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_132_, v_keyedConfig_134_);
lean_inc(v_customCanUnfoldPredicate_x3f_141_);
lean_inc(v_synthPendingDepth_140_);
lean_inc(v_defEqCtx_x3f_139_);
lean_inc_ref(v_localInstances_138_);
lean_inc_ref(v_lctx_137_);
lean_inc(v_zetaDeltaSet_136_);
v___x_146_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_146_, 0, v___x_145_);
lean_ctor_set(v___x_146_, 1, v_zetaDeltaSet_136_);
lean_ctor_set(v___x_146_, 2, v_lctx_137_);
lean_ctor_set(v___x_146_, 3, v_localInstances_138_);
lean_ctor_set(v___x_146_, 4, v_defEqCtx_x3f_139_);
lean_ctor_set(v___x_146_, 5, v_synthPendingDepth_140_);
lean_ctor_set(v___x_146_, 6, v_customCanUnfoldPredicate_x3f_141_);
lean_ctor_set_uint8(v___x_146_, sizeof(void*)*7, v_trackZetaDelta_135_);
lean_ctor_set_uint8(v___x_146_, sizeof(void*)*7 + 1, v_univApprox_142_);
lean_ctor_set_uint8(v___x_146_, sizeof(void*)*7 + 2, v_inTypeClassResolution_143_);
lean_ctor_set_uint8(v___x_146_, sizeof(void*)*7 + 3, v_cacheInferType_144_);
v___x_147_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg(v_e_104_, v___f_130_, v___x_131_, v___x_131_, v___x_146_, v_a_106_, v_a_107_, v_a_108_);
lean_dec_ref_known(v___x_146_, 7);
v___y_111_ = v___x_147_;
goto v___jp_110_;
}
else
{
lean_object* v___x_148_; 
v___x_148_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg(v_e_104_, v___f_130_, v___x_131_, v___x_131_, v_a_105_, v_a_106_, v_a_107_, v_a_108_);
v___y_111_ = v___x_148_;
goto v___jp_110_;
}
v___jp_110_:
{
if (lean_obj_tag(v___y_111_) == 0)
{
lean_object* v_a_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_119_; 
v_a_112_ = lean_ctor_get(v___y_111_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v___y_111_);
if (v_isSharedCheck_119_ == 0)
{
v___x_114_ = v___y_111_;
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_a_112_);
lean_dec(v___y_111_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_117_; 
if (v_isShared_115_ == 0)
{
v___x_117_ = v___x_114_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_a_112_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
else
{
lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_127_; 
v_a_120_ = lean_ctor_get(v___y_111_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v___y_111_);
if (v_isSharedCheck_127_ == 0)
{
v___x_122_ = v___y_111_;
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v___y_111_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_125_; 
if (v_isShared_123_ == 0)
{
v___x_125_ = v___x_122_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_a_120_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgsAux___boxed(lean_object* v_e_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lean_Meta_getExpectedNumArgsAux(v_e_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_);
lean_dec(v_a_153_);
lean_dec_ref(v_a_152_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgs(lean_object* v_e_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l_Lean_Meta_getExpectedNumArgsAux(v_e_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_);
if (lean_obj_tag(v___x_162_) == 0)
{
lean_object* v_a_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_171_; 
v_a_163_ = lean_ctor_get(v___x_162_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_171_ == 0)
{
v___x_165_ = v___x_162_;
v_isShared_166_ = v_isSharedCheck_171_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_a_163_);
lean_dec(v___x_162_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_171_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v_fst_167_; lean_object* v___x_169_; 
v_fst_167_ = lean_ctor_get(v_a_163_, 0);
lean_inc(v_fst_167_);
lean_dec(v_a_163_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 0, v_fst_167_);
v___x_169_ = v___x_165_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_fst_167_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
else
{
lean_object* v_a_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_179_; 
v_a_172_ = lean_ctor_get(v___x_162_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_179_ == 0)
{
v___x_174_ = v___x_162_;
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_a_172_);
lean_dec(v___x_162_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_177_; 
if (v_isShared_175_ == 0)
{
v___x_177_ = v___x_174_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_a_172_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgs___boxed(lean_object* v_e_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_Meta_getExpectedNumArgs(v_e_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
lean_dec(v_a_184_);
lean_dec_ref(v_a_183_);
lean_dec(v_a_182_);
lean_dec_ref(v_a_181_);
return v_res_186_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__0));
v___x_189_ = l_Lean_stringToMessageData(v___x_188_);
return v___x_189_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__2));
v___x_192_ = l_Lean_stringToMessageData(v___x_191_);
return v___x_192_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__4));
v___x_195_ = l_Lean_stringToMessageData(v___x_194_);
return v___x_195_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__7));
v___x_200_ = l_Lean_MessageData_ofFormat(v___x_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0(lean_object* v_config_203_, lean_object* v___y_204_, lean_object* v_targetType_205_, lean_object* v___y_206_, lean_object* v_term_x3f_207_, lean_object* v_conclusionType_x3f_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
uint8_t v_trackZetaDelta_214_; lean_object* v_zetaDeltaSet_215_; lean_object* v_lctx_216_; lean_object* v_localInstances_217_; lean_object* v_defEqCtx_x3f_218_; lean_object* v_synthPendingDepth_219_; lean_object* v_customCanUnfoldPredicate_x3f_220_; uint8_t v_univApprox_221_; uint8_t v_inTypeClassResolution_222_; uint8_t v_cacheInferType_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_283_; 
v_trackZetaDelta_214_ = lean_ctor_get_uint8(v___y_209_, sizeof(void*)*7);
v_zetaDeltaSet_215_ = lean_ctor_get(v___y_209_, 1);
v_lctx_216_ = lean_ctor_get(v___y_209_, 2);
v_localInstances_217_ = lean_ctor_get(v___y_209_, 3);
v_defEqCtx_x3f_218_ = lean_ctor_get(v___y_209_, 4);
v_synthPendingDepth_219_ = lean_ctor_get(v___y_209_, 5);
v_customCanUnfoldPredicate_x3f_220_ = lean_ctor_get(v___y_209_, 6);
v_univApprox_221_ = lean_ctor_get_uint8(v___y_209_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_222_ = lean_ctor_get_uint8(v___y_209_, sizeof(void*)*7 + 2);
v_cacheInferType_223_ = lean_ctor_get_uint8(v___y_209_, sizeof(void*)*7 + 3);
v_isSharedCheck_283_ = !lean_is_exclusive(v___y_209_);
if (v_isSharedCheck_283_ == 0)
{
lean_object* v_unused_284_; 
v_unused_284_ = lean_ctor_get(v___y_209_, 0);
lean_dec(v_unused_284_);
v___x_225_ = v___y_209_;
v_isShared_226_ = v_isSharedCheck_283_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_220_);
lean_inc(v_synthPendingDepth_219_);
lean_inc(v_defEqCtx_x3f_218_);
lean_inc(v_localInstances_217_);
lean_inc(v_lctx_216_);
lean_inc(v_zetaDeltaSet_215_);
lean_dec(v___y_209_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_283_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
uint64_t v___x_227_; lean_object* v___x_228_; lean_object* v___x_230_; 
v___x_227_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_203_);
v___x_228_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_228_, 0, v_config_203_);
lean_ctor_set_uint64(v___x_228_, sizeof(void*)*1, v___x_227_);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 0, v___x_228_);
v___x_230_ = v___x_225_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_228_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v_zetaDeltaSet_215_);
lean_ctor_set(v_reuseFailAlloc_282_, 2, v_lctx_216_);
lean_ctor_set(v_reuseFailAlloc_282_, 3, v_localInstances_217_);
lean_ctor_set(v_reuseFailAlloc_282_, 4, v_defEqCtx_x3f_218_);
lean_ctor_set(v_reuseFailAlloc_282_, 5, v_synthPendingDepth_219_);
lean_ctor_set(v_reuseFailAlloc_282_, 6, v_customCanUnfoldPredicate_x3f_220_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, sizeof(void*)*7, v_trackZetaDelta_214_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, sizeof(void*)*7 + 1, v_univApprox_221_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, sizeof(void*)*7 + 2, v_inTypeClassResolution_222_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, sizeof(void*)*7 + 3, v_cacheInferType_223_);
v___x_230_ = v_reuseFailAlloc_282_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
lean_object* v___x_231_; 
v___x_231_ = l_Lean_Meta_addPPExplicitToExposeDiff(v___y_204_, v_targetType_205_, v___x_230_, v___y_210_, v___y_211_, v___y_212_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v_a_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_273_; 
v_a_232_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_273_ == 0)
{
v___x_234_ = v___x_231_;
v_isShared_235_ = v_isSharedCheck_273_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_a_232_);
lean_dec(v___x_231_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_273_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v_fst_236_; lean_object* v_snd_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_272_; 
v_fst_236_ = lean_ctor_get(v_a_232_, 0);
v_snd_237_ = lean_ctor_get(v_a_232_, 1);
v_isSharedCheck_272_ = !lean_is_exclusive(v_a_232_);
if (v_isSharedCheck_272_ == 0)
{
v___x_239_ = v_a_232_;
v_isShared_240_ = v_isSharedCheck_272_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_snd_237_);
lean_inc(v_fst_236_);
lean_dec(v_a_232_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_272_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___y_242_; lean_object* v___y_243_; lean_object* v___y_244_; lean_object* v___y_260_; 
if (lean_obj_tag(v_conclusionType_x3f_208_) == 0)
{
lean_object* v___x_270_; 
v___x_270_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__9));
v___y_260_ = v___x_270_;
goto v___jp_259_;
}
else
{
lean_object* v___x_271_; 
v___x_271_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__10));
v___y_260_ = v___x_271_;
goto v___jp_259_;
}
v___jp_241_:
{
lean_object* v___x_246_; 
if (v_isShared_240_ == 0)
{
lean_ctor_set_tag(v___x_239_, 7);
lean_ctor_set(v___x_239_, 1, v___y_244_);
lean_ctor_set(v___x_239_, 0, v___y_243_);
v___x_246_ = v___x_239_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___y_243_);
lean_ctor_set(v_reuseFailAlloc_258_, 1, v___y_244_);
v___x_246_ = v_reuseFailAlloc_258_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_256_; 
v___x_247_ = l_Lean_indentExpr(v_fst_236_);
v___x_248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_246_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
v___x_249_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1);
v___x_250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_248_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
v___x_251_ = l_Lean_indentExpr(v_snd_237_);
v___x_252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_250_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
v___x_253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
lean_ctor_set(v___x_253_, 1, v___y_206_);
v___x_254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
lean_ctor_set(v___x_254_, 1, v___y_242_);
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 0, v___x_254_);
v___x_256_ = v___x_234_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_254_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
v___jp_259_:
{
lean_object* v___x_261_; 
lean_inc(v_snd_237_);
lean_inc(v_fst_236_);
v___x_261_ = l_Lean_Meta_mkUnfoldAxiomsNote(v_fst_236_, v_snd_237_, v___x_230_, v___y_210_, v___y_211_, v___y_212_);
lean_dec_ref(v___x_230_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_a_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v_a_262_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_a_262_);
lean_dec_ref_known(v___x_261_, 1);
v___x_263_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3);
lean_inc_ref(v___y_260_);
v___x_264_ = l_Lean_stringToMessageData(v___y_260_);
v___x_265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_263_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
v___x_266_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5);
v___x_267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_265_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
if (lean_obj_tag(v_term_x3f_207_) == 0)
{
lean_object* v___x_268_; 
v___x_268_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8);
v___y_242_ = v_a_262_;
v___y_243_ = v___x_267_;
v___y_244_ = v___x_268_;
goto v___jp_241_;
}
else
{
lean_object* v_val_269_; 
v_val_269_ = lean_ctor_get(v_term_x3f_207_, 0);
lean_inc(v_val_269_);
lean_dec_ref_known(v_term_x3f_207_, 1);
v___y_242_ = v_a_262_;
v___y_243_ = v___x_267_;
v___y_244_ = v_val_269_;
goto v___jp_241_;
}
}
else
{
lean_del_object(v___x_239_);
lean_dec(v_snd_237_);
lean_dec(v_fst_236_);
lean_del_object(v___x_234_);
lean_dec(v_term_x3f_207_);
lean_dec_ref(v___y_206_);
return v___x_261_;
}
}
}
}
}
else
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_281_; 
lean_dec_ref(v___x_230_);
lean_dec(v_term_x3f_207_);
lean_dec_ref(v___y_206_);
v_a_274_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_281_ == 0)
{
v___x_276_ = v___x_231_;
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_231_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
if (v_isShared_277_ == 0)
{
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_274_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___boxed(lean_object* v_config_285_, lean_object* v___y_286_, lean_object* v_targetType_287_, lean_object* v___y_288_, lean_object* v_term_x3f_289_, lean_object* v_conclusionType_x3f_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0(v_config_285_, v___y_286_, v_targetType_287_, v___y_288_, v_term_x3f_289_, v_conclusionType_x3f_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
lean_dec(v_conclusionType_x3f_290_);
return v_res_296_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__0));
v___x_299_ = l_Lean_stringToMessageData(v___x_298_);
return v___x_299_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__2));
v___x_302_ = l_Lean_stringToMessageData(v___x_301_);
return v___x_302_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__4));
v___x_305_ = l_Lean_stringToMessageData(v___x_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(lean_object* v_mvarId_309_, lean_object* v_eType_310_, lean_object* v_conclusionType_x3f_311_, lean_object* v_targetType_312_, lean_object* v_term_x3f_313_, uint8_t v_approx_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_){
_start:
{
lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_324_; lean_object* v___y_325_; lean_object* v___y_326_; lean_object* v___y_327_; lean_object* v___y_328_; lean_object* v___y_338_; lean_object* v___y_339_; lean_object* v___y_340_; lean_object* v___y_341_; lean_object* v___y_342_; lean_object* v___y_343_; lean_object* v___y_344_; lean_object* v___y_345_; lean_object* v___y_346_; lean_object* v___y_354_; lean_object* v___y_355_; lean_object* v___y_356_; lean_object* v___y_357_; lean_object* v___y_358_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v_config_366_; lean_object* v___y_367_; lean_object* v___y_368_; lean_object* v___y_369_; lean_object* v___y_370_; 
if (v_approx_314_ == 0)
{
lean_object* v___x_373_; 
v___x_373_ = l_Lean_Meta_Context_config(v_a_315_);
v_config_366_ = v___x_373_;
v___y_367_ = v_a_315_;
v___y_368_ = v_a_316_;
v___y_369_ = v_a_317_;
v___y_370_ = v_a_318_;
goto v___jp_365_;
}
else
{
lean_object* v___x_374_; uint8_t v_constApprox_375_; uint8_t v_isDefEqStuckEx_376_; uint8_t v_unificationHints_377_; uint8_t v_proofIrrelevance_378_; uint8_t v_assignSyntheticOpaque_379_; uint8_t v_offsetCnstrs_380_; uint8_t v_transparency_381_; uint8_t v_etaStruct_382_; uint8_t v_univApprox_383_; uint8_t v_iota_384_; uint8_t v_beta_385_; uint8_t v_proj_386_; uint8_t v_zeta_387_; uint8_t v_zetaDelta_388_; uint8_t v_zetaUnused_389_; uint8_t v_zetaHave_390_; uint8_t v_canUnfoldPredicateConfig_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_412_; 
v___x_374_ = l_Lean_Meta_Context_config(v_a_315_);
v_constApprox_375_ = lean_ctor_get_uint8(v___x_374_, 3);
v_isDefEqStuckEx_376_ = lean_ctor_get_uint8(v___x_374_, 4);
v_unificationHints_377_ = lean_ctor_get_uint8(v___x_374_, 5);
v_proofIrrelevance_378_ = lean_ctor_get_uint8(v___x_374_, 6);
v_assignSyntheticOpaque_379_ = lean_ctor_get_uint8(v___x_374_, 7);
v_offsetCnstrs_380_ = lean_ctor_get_uint8(v___x_374_, 8);
v_transparency_381_ = lean_ctor_get_uint8(v___x_374_, 9);
v_etaStruct_382_ = lean_ctor_get_uint8(v___x_374_, 10);
v_univApprox_383_ = lean_ctor_get_uint8(v___x_374_, 11);
v_iota_384_ = lean_ctor_get_uint8(v___x_374_, 12);
v_beta_385_ = lean_ctor_get_uint8(v___x_374_, 13);
v_proj_386_ = lean_ctor_get_uint8(v___x_374_, 14);
v_zeta_387_ = lean_ctor_get_uint8(v___x_374_, 15);
v_zetaDelta_388_ = lean_ctor_get_uint8(v___x_374_, 16);
v_zetaUnused_389_ = lean_ctor_get_uint8(v___x_374_, 17);
v_zetaHave_390_ = lean_ctor_get_uint8(v___x_374_, 18);
v_canUnfoldPredicateConfig_391_ = lean_ctor_get_uint8(v___x_374_, 19);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_412_ == 0)
{
v___x_393_ = v___x_374_;
v_isShared_394_ = v_isSharedCheck_412_;
goto v_resetjp_392_;
}
else
{
lean_dec(v___x_374_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_412_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_411_, 3, v_constApprox_375_);
lean_ctor_set_uint8(v_reuseFailAlloc_411_, 4, v_isDefEqStuckEx_376_);
lean_ctor_set_uint8(v_reuseFailAlloc_411_, 5, v_unificationHints_377_);
lean_ctor_set_uint8(v_reuseFailAlloc_411_, 6, v_proofIrrelevance_378_);
lean_ctor_set_uint8(v_reuseFailAlloc_411_, 7, v_assignSyntheticOpaque_379_);
lean_ctor_set_uint8(v_reuseFailAlloc_411_, 8, v_offsetCnstrs_380_);
lean_ctor_set_uint8(v_reuseFailAlloc_411_, 9, v_transparency_381_);
lean_ctor_set_uint8(v_reuseFailAlloc_411_, 10, v_etaStruct_382_);
lean_ctor_set_uint8(v_reuseFailAlloc_411_, 11, v_univApprox_383_);
lean_ctor_set_uint8(v_reuseFailAlloc_411_, 12, v_iota_384_);
lean_ctor_set_uint8(v_reuseFailAlloc_411_, 13, v_beta_385_);
lean_ctor_set_uint8(v_reuseFailAlloc_411_, 14, v_proj_386_);
lean_ctor_set_uint8(v_reuseFailAlloc_411_, 15, v_zeta_387_);
lean_ctor_set_uint8(v_reuseFailAlloc_411_, 16, v_zetaDelta_388_);
lean_ctor_set_uint8(v_reuseFailAlloc_411_, 17, v_zetaUnused_389_);
lean_ctor_set_uint8(v_reuseFailAlloc_411_, 18, v_zetaHave_390_);
lean_ctor_set_uint8(v_reuseFailAlloc_411_, 19, v_canUnfoldPredicateConfig_391_);
v___x_396_ = v_reuseFailAlloc_411_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
uint8_t v_trackZetaDelta_397_; lean_object* v_zetaDeltaSet_398_; lean_object* v_lctx_399_; lean_object* v_localInstances_400_; lean_object* v_defEqCtx_x3f_401_; lean_object* v_synthPendingDepth_402_; lean_object* v_customCanUnfoldPredicate_x3f_403_; uint8_t v_univApprox_404_; uint8_t v_inTypeClassResolution_405_; uint8_t v_cacheInferType_406_; uint64_t v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
lean_ctor_set_uint8(v___x_396_, 0, v_approx_314_);
lean_ctor_set_uint8(v___x_396_, 1, v_approx_314_);
lean_ctor_set_uint8(v___x_396_, 2, v_approx_314_);
v_trackZetaDelta_397_ = lean_ctor_get_uint8(v_a_315_, sizeof(void*)*7);
v_zetaDeltaSet_398_ = lean_ctor_get(v_a_315_, 1);
v_lctx_399_ = lean_ctor_get(v_a_315_, 2);
v_localInstances_400_ = lean_ctor_get(v_a_315_, 3);
v_defEqCtx_x3f_401_ = lean_ctor_get(v_a_315_, 4);
v_synthPendingDepth_402_ = lean_ctor_get(v_a_315_, 5);
v_customCanUnfoldPredicate_x3f_403_ = lean_ctor_get(v_a_315_, 6);
v_univApprox_404_ = lean_ctor_get_uint8(v_a_315_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_405_ = lean_ctor_get_uint8(v_a_315_, sizeof(void*)*7 + 2);
v_cacheInferType_406_ = lean_ctor_get_uint8(v_a_315_, sizeof(void*)*7 + 3);
v___x_407_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_396_);
v___x_408_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_408_, 0, v___x_396_);
lean_ctor_set_uint64(v___x_408_, sizeof(void*)*1, v___x_407_);
lean_inc(v_customCanUnfoldPredicate_x3f_403_);
lean_inc(v_synthPendingDepth_402_);
lean_inc(v_defEqCtx_x3f_401_);
lean_inc_ref(v_localInstances_400_);
lean_inc_ref(v_lctx_399_);
lean_inc(v_zetaDeltaSet_398_);
v___x_409_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_409_, 0, v___x_408_);
lean_ctor_set(v___x_409_, 1, v_zetaDeltaSet_398_);
lean_ctor_set(v___x_409_, 2, v_lctx_399_);
lean_ctor_set(v___x_409_, 3, v_localInstances_400_);
lean_ctor_set(v___x_409_, 4, v_defEqCtx_x3f_401_);
lean_ctor_set(v___x_409_, 5, v_synthPendingDepth_402_);
lean_ctor_set(v___x_409_, 6, v_customCanUnfoldPredicate_x3f_403_);
lean_ctor_set_uint8(v___x_409_, sizeof(void*)*7, v_trackZetaDelta_397_);
lean_ctor_set_uint8(v___x_409_, sizeof(void*)*7 + 1, v_univApprox_404_);
lean_ctor_set_uint8(v___x_409_, sizeof(void*)*7 + 2, v_inTypeClassResolution_405_);
lean_ctor_set_uint8(v___x_409_, sizeof(void*)*7 + 3, v_cacheInferType_406_);
v___x_410_ = l_Lean_Meta_Context_config(v___x_409_);
lean_dec_ref_known(v___x_409_, 7);
v_config_366_ = v___x_410_;
v___y_367_ = v_a_315_;
v___y_368_ = v_a_316_;
v___y_369_ = v_a_317_;
v___y_370_ = v_a_318_;
goto v___jp_365_;
}
}
}
v___jp_320_:
{
lean_object* v___f_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
lean_inc_ref(v_targetType_312_);
v___f_329_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_329_, 0, v___y_321_);
lean_closure_set(v___f_329_, 1, v___y_322_);
lean_closure_set(v___f_329_, 2, v_targetType_312_);
lean_closure_set(v___f_329_, 3, v___y_328_);
lean_closure_set(v___f_329_, 4, v_term_x3f_313_);
lean_closure_set(v___f_329_, 5, v_conclusionType_x3f_311_);
v___x_330_ = lean_unsigned_to_nat(2u);
v___x_331_ = lean_mk_empty_array_with_capacity(v___x_330_);
v___x_332_ = lean_array_push(v___x_331_, v_eType_310_);
v___x_333_ = lean_array_push(v___x_332_, v_targetType_312_);
v___x_334_ = l_Lean_MessageData_ofLazyM(v___f_329_, v___x_333_);
v___x_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_inc(v___y_323_);
v___x_336_ = l_Lean_Meta_throwTacticEx___redArg(v___y_323_, v_mvarId_309_, v___x_335_, v___y_327_, v___y_326_, v___y_325_, v___y_324_);
return v___x_336_;
}
v___jp_337_:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
lean_inc_ref(v___y_341_);
v___x_347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_347_, 0, v___y_341_);
lean_ctor_set(v___x_347_, 1, v___y_346_);
v___x_348_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1);
v___x_349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_347_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
lean_inc_ref(v_eType_310_);
v___x_350_ = l_Lean_indentExpr(v_eType_310_);
v___x_351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_351_, 0, v___x_349_);
lean_ctor_set(v___x_351_, 1, v___x_350_);
v___x_352_ = l_Lean_MessageData_note(v___x_351_);
v___y_321_ = v___y_338_;
v___y_322_ = v___y_339_;
v___y_323_ = v___y_340_;
v___y_324_ = v___y_342_;
v___y_325_ = v___y_343_;
v___y_326_ = v___y_344_;
v___y_327_ = v___y_345_;
v___y_328_ = v___x_352_;
goto v___jp_320_;
}
v___jp_353_:
{
if (lean_obj_tag(v_conclusionType_x3f_311_) == 0)
{
lean_object* v___x_361_; 
v___x_361_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3);
v___y_321_ = v___y_354_;
v___y_322_ = v___y_360_;
v___y_323_ = v___y_359_;
v___y_324_ = v___y_355_;
v___y_325_ = v___y_356_;
v___y_326_ = v___y_357_;
v___y_327_ = v___y_358_;
v___y_328_ = v___x_361_;
goto v___jp_320_;
}
else
{
lean_object* v___x_362_; 
v___x_362_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5);
if (lean_obj_tag(v_term_x3f_313_) == 0)
{
lean_object* v___x_363_; 
v___x_363_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8);
v___y_338_ = v___y_354_;
v___y_339_ = v___y_360_;
v___y_340_ = v___y_359_;
v___y_341_ = v___x_362_;
v___y_342_ = v___y_355_;
v___y_343_ = v___y_356_;
v___y_344_ = v___y_357_;
v___y_345_ = v___y_358_;
v___y_346_ = v___x_363_;
goto v___jp_337_;
}
else
{
lean_object* v_val_364_; 
v_val_364_ = lean_ctor_get(v_term_x3f_313_, 0);
lean_inc(v_val_364_);
v___y_338_ = v___y_354_;
v___y_339_ = v___y_360_;
v___y_340_ = v___y_359_;
v___y_341_ = v___x_362_;
v___y_342_ = v___y_355_;
v___y_343_ = v___y_356_;
v___y_344_ = v___y_357_;
v___y_345_ = v___y_358_;
v___y_346_ = v_val_364_;
goto v___jp_337_;
}
}
}
v___jp_365_:
{
lean_object* v___x_371_; 
v___x_371_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7));
if (lean_obj_tag(v_conclusionType_x3f_311_) == 0)
{
lean_inc_ref(v_eType_310_);
v___y_354_ = v_config_366_;
v___y_355_ = v___y_370_;
v___y_356_ = v___y_369_;
v___y_357_ = v___y_368_;
v___y_358_ = v___y_367_;
v___y_359_ = v___x_371_;
v___y_360_ = v_eType_310_;
goto v___jp_353_;
}
else
{
lean_object* v_val_372_; 
v_val_372_ = lean_ctor_get(v_conclusionType_x3f_311_, 0);
lean_inc(v_val_372_);
v___y_354_ = v_config_366_;
v___y_355_ = v___y_370_;
v___y_356_ = v___y_369_;
v___y_357_ = v___y_368_;
v___y_358_ = v___y_367_;
v___y_359_ = v___x_371_;
v___y_360_ = v_val_372_;
goto v___jp_353_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___boxed(lean_object* v_mvarId_413_, lean_object* v_eType_414_, lean_object* v_conclusionType_x3f_415_, lean_object* v_targetType_416_, lean_object* v_term_x3f_417_, lean_object* v_approx_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_){
_start:
{
uint8_t v_approx_boxed_424_; lean_object* v_res_425_; 
v_approx_boxed_424_ = lean_unbox(v_approx_418_);
v_res_425_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_413_, v_eType_414_, v_conclusionType_x3f_415_, v_targetType_416_, v_term_x3f_417_, v_approx_boxed_424_, v_a_419_, v_a_420_, v_a_421_, v_a_422_);
lean_dec(v_a_422_);
lean_dec_ref(v_a_421_);
lean_dec(v_a_420_);
lean_dec_ref(v_a_419_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError(lean_object* v_00_u03b1_426_, lean_object* v_mvarId_427_, lean_object* v_eType_428_, lean_object* v_conclusionType_x3f_429_, lean_object* v_targetType_430_, lean_object* v_term_x3f_431_, uint8_t v_approx_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_427_, v_eType_428_, v_conclusionType_x3f_429_, v_targetType_430_, v_term_x3f_431_, v_approx_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___boxed(lean_object* v_00_u03b1_439_, lean_object* v_mvarId_440_, lean_object* v_eType_441_, lean_object* v_conclusionType_x3f_442_, lean_object* v_targetType_443_, lean_object* v_term_x3f_444_, lean_object* v_approx_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_){
_start:
{
uint8_t v_approx_boxed_451_; lean_object* v_res_452_; 
v_approx_boxed_451_ = lean_unbox(v_approx_445_);
v_res_452_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError(v_00_u03b1_439_, v_mvarId_440_, v_eType_441_, v_conclusionType_x3f_442_, v_targetType_443_, v_term_x3f_444_, v_approx_boxed_451_, v_a_446_, v_a_447_, v_a_448_, v_a_449_);
lean_dec(v_a_449_);
lean_dec_ref(v_a_448_);
lean_dec(v_a_447_);
lean_dec_ref(v_a_446_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(lean_object* v_a_453_, lean_object* v_snd_454_, lean_object* v_fst_455_, lean_object* v_____r_456_, uint8_t v_progressAfterEx_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_463_, 0, v_a_453_);
v___x_464_ = lean_box(v_progressAfterEx_457_);
v___x_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
lean_ctor_set(v___x_465_, 1, v_snd_454_);
v___x_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_466_, 0, v_fst_455_);
lean_ctor_set(v___x_466_, 1, v___x_465_);
v___x_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_467_, 0, v___x_463_);
lean_ctor_set(v___x_467_, 1, v___x_466_);
v___x_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0___boxed(lean_object* v_a_469_, lean_object* v_snd_470_, lean_object* v_fst_471_, lean_object* v_____r_472_, lean_object* v_progressAfterEx_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
uint8_t v_progressAfterEx_boxed_479_; lean_object* v_res_480_; 
v_progressAfterEx_boxed_479_ = lean_unbox(v_progressAfterEx_473_);
v_res_480_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(v_a_469_, v_snd_470_, v_fst_471_, v_____r_472_, v_progressAfterEx_boxed_479_, v___y_474_, v___y_475_, v___y_476_, v___y_477_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
return v_res_480_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2(void){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__1));
v___x_485_ = l_Lean_MessageData_ofFormat(v___x_484_);
return v___x_485_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3(void){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2);
v___x_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0(uint8_t v_allowSynthFailures_488_, lean_object* v_tacticName_489_, lean_object* v_mvarId_490_, lean_object* v_as_491_, size_t v_sz_492_, size_t v_i_493_, lean_object* v_b_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v_a_501_; lean_object* v_fst_506_; lean_object* v_fst_507_; lean_object* v_snd_508_; uint8_t v___x_511_; 
v___x_511_ = lean_usize_dec_lt(v_i_493_, v_sz_492_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; 
lean_dec(v_mvarId_490_);
lean_dec(v_tacticName_489_);
v___x_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_512_, 0, v_b_494_);
return v___x_512_;
}
else
{
lean_object* v_snd_513_; lean_object* v_fst_514_; lean_object* v_fst_515_; lean_object* v_snd_516_; lean_object* v_a_517_; lean_object* v___y_519_; uint8_t v___y_520_; lean_object* v_a_525_; lean_object* v___y_529_; lean_object* v___x_590_; 
v_snd_513_ = lean_ctor_get(v_b_494_, 1);
lean_inc(v_snd_513_);
v_fst_514_ = lean_ctor_get(v_b_494_, 0);
lean_inc(v_fst_514_);
lean_dec_ref(v_b_494_);
v_fst_515_ = lean_ctor_get(v_snd_513_, 0);
lean_inc(v_fst_515_);
v_snd_516_ = lean_ctor_get(v_snd_513_, 1);
lean_inc(v_snd_516_);
lean_dec(v_snd_513_);
v_a_517_ = lean_array_uget_borrowed(v_as_491_, v_i_493_);
lean_inc(v___y_498_);
lean_inc_ref(v___y_497_);
lean_inc(v___y_496_);
lean_inc_ref(v___y_495_);
lean_inc(v_a_517_);
v___x_590_ = lean_infer_type(v_a_517_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_a_591_);
lean_dec_ref_known(v___x_590_, 1);
v___x_592_ = lean_box(0);
v___x_593_ = l_Lean_Meta_synthInstance(v_a_591_, v___x_592_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v_a_594_; lean_object* v___x_595_; lean_object* v___x_596_; uint8_t v___x_597_; 
v_a_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_a_594_);
lean_dec_ref_known(v___x_593_, 1);
v___x_595_ = lean_array_get_size(v_snd_516_);
v___x_596_ = lean_unsigned_to_nat(0u);
v___x_597_ = lean_nat_dec_eq(v___x_595_, v___x_596_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = lean_box(0);
lean_inc(v_snd_516_);
v___x_599_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(v_a_594_, v_snd_516_, v_fst_514_, v___x_598_, v___x_511_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
v___y_529_ = v___x_599_;
goto v___jp_528_;
}
else
{
lean_object* v___x_600_; uint8_t v___x_601_; lean_object* v___x_602_; 
v___x_600_ = lean_box(0);
v___x_601_ = lean_unbox(v_fst_515_);
lean_inc(v_snd_516_);
v___x_602_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(v_a_594_, v_snd_516_, v_fst_514_, v___x_600_, v___x_601_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
v___y_529_ = v___x_602_;
goto v___jp_528_;
}
}
else
{
lean_object* v_a_603_; 
lean_dec(v_fst_514_);
v_a_603_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_a_603_);
lean_dec_ref_known(v___x_593_, 1);
v_a_525_ = v_a_603_;
goto v___jp_524_;
}
}
else
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
lean_dec(v_snd_516_);
lean_dec(v_fst_515_);
lean_dec(v_fst_514_);
lean_dec(v_mvarId_490_);
lean_dec(v_tacticName_489_);
v_a_604_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___x_590_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_590_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
v___jp_518_:
{
if (v___y_520_ == 0)
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_521_, 0, v___y_519_);
lean_inc(v_a_517_);
v___x_522_ = lean_array_push(v_snd_516_, v_a_517_);
v_fst_506_ = v___x_521_;
v_fst_507_ = v_fst_515_;
v_snd_508_ = v___x_522_;
goto v___jp_505_;
}
else
{
lean_object* v___x_523_; 
lean_dec(v_snd_516_);
lean_dec(v_fst_515_);
lean_dec(v_mvarId_490_);
lean_dec(v_tacticName_489_);
v___x_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_523_, 0, v___y_519_);
return v___x_523_;
}
}
v___jp_524_:
{
uint8_t v___x_526_; 
v___x_526_ = l_Lean_Exception_isInterrupt(v_a_525_);
if (v___x_526_ == 0)
{
uint8_t v___x_527_; 
lean_inc_ref(v_a_525_);
v___x_527_ = l_Lean_Exception_isRuntime(v_a_525_);
v___y_519_ = v_a_525_;
v___y_520_ = v___x_527_;
goto v___jp_518_;
}
else
{
v___y_519_ = v_a_525_;
v___y_520_ = v___x_526_;
goto v___jp_518_;
}
}
v___jp_528_:
{
if (lean_obj_tag(v___y_529_) == 0)
{
lean_object* v_a_530_; lean_object* v_snd_531_; lean_object* v_snd_532_; lean_object* v_fst_533_; 
lean_dec(v_snd_516_);
lean_dec(v_fst_515_);
v_a_530_ = lean_ctor_get(v___y_529_, 0);
lean_inc(v_a_530_);
lean_dec_ref_known(v___y_529_, 1);
v_snd_531_ = lean_ctor_get(v_a_530_, 1);
lean_inc(v_snd_531_);
v_snd_532_ = lean_ctor_get(v_snd_531_, 1);
lean_inc(v_snd_532_);
v_fst_533_ = lean_ctor_get(v_a_530_, 0);
lean_inc(v_fst_533_);
lean_dec(v_a_530_);
if (lean_obj_tag(v_fst_533_) == 1)
{
lean_object* v_fst_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_584_; 
v_fst_534_ = lean_ctor_get(v_snd_531_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v_snd_531_);
if (v_isSharedCheck_584_ == 0)
{
lean_object* v_unused_585_; 
v_unused_585_ = lean_ctor_get(v_snd_531_, 1);
lean_dec(v_unused_585_);
v___x_536_ = v_snd_531_;
v_isShared_537_ = v_isSharedCheck_584_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_fst_534_);
lean_dec(v_snd_531_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_584_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v_fst_538_; lean_object* v_snd_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_583_; 
v_fst_538_ = lean_ctor_get(v_snd_532_, 0);
v_snd_539_ = lean_ctor_get(v_snd_532_, 1);
v_isSharedCheck_583_ = !lean_is_exclusive(v_snd_532_);
if (v_isSharedCheck_583_ == 0)
{
v___x_541_ = v_snd_532_;
v_isShared_542_ = v_isSharedCheck_583_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_snd_539_);
lean_inc(v_fst_538_);
lean_dec(v_snd_532_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_583_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v_val_543_; lean_object* v___x_544_; 
v_val_543_ = lean_ctor_get(v_fst_533_, 0);
lean_inc(v_val_543_);
lean_dec_ref_known(v_fst_533_, 1);
lean_inc(v_a_517_);
v___x_544_ = l_Lean_Meta_isExprDefEq(v_a_517_, v_val_543_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_545_; uint8_t v___x_546_; 
v_a_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_a_545_);
lean_dec_ref_known(v___x_544_, 1);
v___x_546_ = lean_unbox(v_a_545_);
lean_dec(v_a_545_);
if (v___x_546_ == 0)
{
if (v_allowSynthFailures_488_ == 0)
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3);
lean_inc(v_mvarId_490_);
lean_inc(v_tacticName_489_);
v___x_548_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_489_, v_mvarId_490_, v___x_547_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v___x_550_; 
lean_dec_ref_known(v___x_548_, 1);
if (v_isShared_542_ == 0)
{
v___x_550_ = v___x_541_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_fst_538_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_snd_539_);
v___x_550_ = v_reuseFailAlloc_554_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_object* v___x_552_; 
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 1, v___x_550_);
v___x_552_ = v___x_536_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_fst_534_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v___x_550_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
v_a_501_ = v___x_552_;
goto v___jp_500_;
}
}
}
else
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
lean_del_object(v___x_541_);
lean_dec(v_snd_539_);
lean_dec(v_fst_538_);
lean_del_object(v___x_536_);
lean_dec(v_fst_534_);
lean_dec(v_mvarId_490_);
lean_dec(v_tacticName_489_);
v_a_555_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___x_548_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_548_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
else
{
lean_object* v___x_564_; 
if (v_isShared_542_ == 0)
{
v___x_564_ = v___x_541_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_fst_538_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v_snd_539_);
v___x_564_ = v_reuseFailAlloc_568_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
lean_object* v___x_566_; 
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 1, v___x_564_);
v___x_566_ = v___x_536_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_fst_534_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v___x_564_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
v_a_501_ = v___x_566_;
goto v___jp_500_;
}
}
}
}
else
{
lean_object* v___x_570_; 
if (v_isShared_542_ == 0)
{
v___x_570_ = v___x_541_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_fst_538_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v_snd_539_);
v___x_570_ = v_reuseFailAlloc_574_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
lean_object* v___x_572_; 
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 1, v___x_570_);
v___x_572_ = v___x_536_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_fst_534_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v___x_570_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
v_a_501_ = v___x_572_;
goto v___jp_500_;
}
}
}
}
else
{
lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_582_; 
lean_del_object(v___x_541_);
lean_dec(v_snd_539_);
lean_dec(v_fst_538_);
lean_del_object(v___x_536_);
lean_dec(v_fst_534_);
lean_dec(v_mvarId_490_);
lean_dec(v_tacticName_489_);
v_a_575_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_582_ == 0)
{
v___x_577_ = v___x_544_;
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v___x_544_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_580_; 
if (v_isShared_578_ == 0)
{
v___x_580_ = v___x_577_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_a_575_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
}
}
}
else
{
lean_object* v_fst_586_; lean_object* v_fst_587_; lean_object* v_snd_588_; 
lean_dec(v_fst_533_);
v_fst_586_ = lean_ctor_get(v_snd_531_, 0);
lean_inc(v_fst_586_);
lean_dec(v_snd_531_);
v_fst_587_ = lean_ctor_get(v_snd_532_, 0);
lean_inc(v_fst_587_);
v_snd_588_ = lean_ctor_get(v_snd_532_, 1);
lean_inc(v_snd_588_);
lean_dec(v_snd_532_);
v_fst_506_ = v_fst_586_;
v_fst_507_ = v_fst_587_;
v_snd_508_ = v_snd_588_;
goto v___jp_505_;
}
}
else
{
lean_object* v_a_589_; 
v_a_589_ = lean_ctor_get(v___y_529_, 0);
lean_inc(v_a_589_);
lean_dec_ref_known(v___y_529_, 1);
v_a_525_ = v_a_589_;
goto v___jp_524_;
}
}
}
v___jp_500_:
{
size_t v___x_502_; size_t v___x_503_; 
v___x_502_ = ((size_t)1ULL);
v___x_503_ = lean_usize_add(v_i_493_, v___x_502_);
v_i_493_ = v___x_503_;
v_b_494_ = v_a_501_;
goto _start;
}
v___jp_505_:
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_509_, 0, v_fst_507_);
lean_ctor_set(v___x_509_, 1, v_snd_508_);
v___x_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_510_, 0, v_fst_506_);
lean_ctor_set(v___x_510_, 1, v___x_509_);
v_a_501_ = v___x_510_;
goto v___jp_500_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___boxed(lean_object* v_allowSynthFailures_612_, lean_object* v_tacticName_613_, lean_object* v_mvarId_614_, lean_object* v_as_615_, lean_object* v_sz_616_, lean_object* v_i_617_, lean_object* v_b_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
uint8_t v_allowSynthFailures_boxed_624_; size_t v_sz_boxed_625_; size_t v_i_boxed_626_; lean_object* v_res_627_; 
v_allowSynthFailures_boxed_624_ = lean_unbox(v_allowSynthFailures_612_);
v_sz_boxed_625_ = lean_unbox_usize(v_sz_616_);
lean_dec(v_sz_616_);
v_i_boxed_626_ = lean_unbox_usize(v_i_617_);
lean_dec(v_i_617_);
v_res_627_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0(v_allowSynthFailures_boxed_624_, v_tacticName_613_, v_mvarId_614_, v_as_615_, v_sz_boxed_625_, v_i_boxed_626_, v_b_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec_ref(v_as_615_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(lean_object* v_tacticName_637_, lean_object* v_mvarId_638_, uint8_t v_allowSynthFailures_639_, lean_object* v_mvars_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_){
_start:
{
lean_object* v_postponed_646_; lean_object* v___x_647_; size_t v_sz_648_; size_t v___x_649_; lean_object* v___x_650_; 
v_postponed_646_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0));
v___x_647_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__2));
v_sz_648_ = lean_array_size(v_mvars_640_);
v___x_649_ = ((size_t)0ULL);
v___x_650_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0(v_allowSynthFailures_639_, v_tacticName_637_, v_mvarId_638_, v_mvars_640_, v_sz_648_, v___x_649_, v___x_647_, v_a_641_, v_a_642_, v_a_643_, v_a_644_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_673_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_673_ == 0)
{
v___x_653_ = v___x_650_;
v_isShared_654_ = v_isSharedCheck_673_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_650_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_673_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v_fst_655_; 
v_fst_655_ = lean_ctor_get(v_a_651_, 0);
lean_inc(v_fst_655_);
if (lean_obj_tag(v_fst_655_) == 1)
{
lean_object* v_snd_656_; lean_object* v_fst_657_; uint8_t v___x_658_; 
v_snd_656_ = lean_ctor_get(v_a_651_, 1);
lean_inc(v_snd_656_);
lean_dec(v_a_651_);
v_fst_657_ = lean_ctor_get(v_snd_656_, 0);
v___x_658_ = lean_unbox(v_fst_657_);
if (v___x_658_ == 0)
{
lean_dec(v_snd_656_);
if (v_allowSynthFailures_639_ == 0)
{
lean_object* v_val_659_; lean_object* v___x_661_; 
v_val_659_ = lean_ctor_get(v_fst_655_, 0);
lean_inc(v_val_659_);
lean_dec_ref_known(v_fst_655_, 1);
if (v_isShared_654_ == 0)
{
lean_ctor_set_tag(v___x_653_, 1);
lean_ctor_set(v___x_653_, 0, v_val_659_);
v___x_661_ = v___x_653_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_val_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
else
{
lean_object* v___x_664_; 
lean_dec_ref_known(v_fst_655_, 1);
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 0, v_postponed_646_);
v___x_664_ = v___x_653_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_postponed_646_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
else
{
lean_object* v_snd_666_; lean_object* v___x_668_; 
lean_dec_ref_known(v_fst_655_, 1);
v_snd_666_ = lean_ctor_get(v_snd_656_, 1);
lean_inc(v_snd_666_);
lean_dec(v_snd_656_);
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 0, v_snd_666_);
v___x_668_ = v___x_653_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_snd_666_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
else
{
lean_object* v___x_671_; 
lean_dec(v_fst_655_);
lean_dec(v_a_651_);
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 0, v_postponed_646_);
v___x_671_ = v___x_653_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_postponed_646_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
else
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
v_a_674_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v___x_650_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_650_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_a_674_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___boxed(lean_object* v_tacticName_682_, lean_object* v_mvarId_683_, lean_object* v_allowSynthFailures_684_, lean_object* v_mvars_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_){
_start:
{
uint8_t v_allowSynthFailures_boxed_691_; lean_object* v_res_692_; 
v_allowSynthFailures_boxed_691_ = lean_unbox(v_allowSynthFailures_684_);
v_res_692_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(v_tacticName_682_, v_mvarId_683_, v_allowSynthFailures_boxed_691_, v_mvars_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
lean_dec(v_a_689_);
lean_dec_ref(v_a_688_);
lean_dec(v_a_687_);
lean_dec_ref(v_a_686_);
lean_dec_ref(v_mvars_685_);
return v_res_692_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_keys_693_, lean_object* v_i_694_, lean_object* v_k_695_){
_start:
{
lean_object* v___x_696_; uint8_t v___x_697_; 
v___x_696_ = lean_array_get_size(v_keys_693_);
v___x_697_ = lean_nat_dec_lt(v_i_694_, v___x_696_);
if (v___x_697_ == 0)
{
lean_dec(v_i_694_);
return v___x_697_;
}
else
{
lean_object* v_k_x27_698_; uint8_t v___x_699_; 
v_k_x27_698_ = lean_array_fget_borrowed(v_keys_693_, v_i_694_);
v___x_699_ = l_Lean_instBEqMVarId_beq(v_k_695_, v_k_x27_698_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = lean_unsigned_to_nat(1u);
v___x_701_ = lean_nat_add(v_i_694_, v___x_700_);
lean_dec(v_i_694_);
v_i_694_ = v___x_701_;
goto _start;
}
else
{
lean_dec(v_i_694_);
return v___x_697_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_keys_703_, lean_object* v_i_704_, lean_object* v_k_705_){
_start:
{
uint8_t v_res_706_; lean_object* v_r_707_; 
v_res_706_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_703_, v_i_704_, v_k_705_);
lean_dec(v_k_705_);
lean_dec_ref(v_keys_703_);
v_r_707_ = lean_box(v_res_706_);
return v_r_707_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(lean_object* v_x_708_, size_t v_x_709_, lean_object* v_x_710_){
_start:
{
if (lean_obj_tag(v_x_708_) == 0)
{
lean_object* v_es_711_; lean_object* v___x_712_; size_t v___x_713_; size_t v___x_714_; lean_object* v_j_715_; lean_object* v___x_716_; 
v_es_711_ = lean_ctor_get(v_x_708_, 0);
v___x_712_ = lean_box(2);
v___x_713_ = ((size_t)31ULL);
v___x_714_ = lean_usize_land(v_x_709_, v___x_713_);
v_j_715_ = lean_usize_to_nat(v___x_714_);
v___x_716_ = lean_array_get_borrowed(v___x_712_, v_es_711_, v_j_715_);
lean_dec(v_j_715_);
switch(lean_obj_tag(v___x_716_))
{
case 0:
{
lean_object* v_key_717_; uint8_t v___x_718_; 
v_key_717_ = lean_ctor_get(v___x_716_, 0);
v___x_718_ = l_Lean_instBEqMVarId_beq(v_x_710_, v_key_717_);
return v___x_718_;
}
case 1:
{
lean_object* v_node_719_; size_t v___x_720_; size_t v___x_721_; 
v_node_719_ = lean_ctor_get(v___x_716_, 0);
v___x_720_ = ((size_t)5ULL);
v___x_721_ = lean_usize_shift_right(v_x_709_, v___x_720_);
v_x_708_ = v_node_719_;
v_x_709_ = v___x_721_;
goto _start;
}
default: 
{
uint8_t v___x_723_; 
v___x_723_ = 0;
return v___x_723_;
}
}
}
else
{
lean_object* v_ks_724_; lean_object* v___x_725_; uint8_t v___x_726_; 
v_ks_724_ = lean_ctor_get(v_x_708_, 0);
v___x_725_ = lean_unsigned_to_nat(0u);
v___x_726_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_ks_724_, v___x_725_, v_x_710_);
return v___x_726_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_727_, lean_object* v_x_728_, lean_object* v_x_729_){
_start:
{
size_t v_x_2813__boxed_730_; uint8_t v_res_731_; lean_object* v_r_732_; 
v_x_2813__boxed_730_ = lean_unbox_usize(v_x_728_);
lean_dec(v_x_728_);
v_res_731_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_727_, v_x_2813__boxed_730_, v_x_729_);
lean_dec(v_x_729_);
lean_dec_ref(v_x_727_);
v_r_732_ = lean_box(v_res_731_);
return v_r_732_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(lean_object* v_x_733_, lean_object* v_x_734_){
_start:
{
uint64_t v___x_735_; size_t v___x_736_; uint8_t v___x_737_; 
v___x_735_ = l_Lean_instHashableMVarId_hash(v_x_734_);
v___x_736_ = lean_uint64_to_usize(v___x_735_);
v___x_737_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_733_, v___x_736_, v_x_734_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg___boxed(lean_object* v_x_738_, lean_object* v_x_739_){
_start:
{
uint8_t v_res_740_; lean_object* v_r_741_; 
v_res_740_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_x_738_, v_x_739_);
lean_dec(v_x_739_);
lean_dec_ref(v_x_738_);
v_r_741_ = lean_box(v_res_740_);
return v_r_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(lean_object* v_mvarId_742_, lean_object* v___y_743_){
_start:
{
lean_object* v___x_745_; lean_object* v_mctx_746_; lean_object* v_eAssignment_747_; uint8_t v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_745_ = lean_st_ref_get(v___y_743_);
v_mctx_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc_ref(v_mctx_746_);
lean_dec(v___x_745_);
v_eAssignment_747_ = lean_ctor_get(v_mctx_746_, 8);
lean_inc_ref(v_eAssignment_747_);
lean_dec_ref(v_mctx_746_);
v___x_748_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_eAssignment_747_, v_mvarId_742_);
lean_dec_ref(v_eAssignment_747_);
v___x_749_ = lean_box(v___x_748_);
v___x_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg___boxed(lean_object* v_mvarId_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v_mvarId_751_, v___y_752_);
lean_dec(v___y_752_);
lean_dec(v_mvarId_751_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(uint8_t v_synthAssignedInstances_755_, lean_object* v_as_756_, size_t v_sz_757_, size_t v_i_758_, lean_object* v_b_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v_a_766_; uint8_t v___x_770_; 
v___x_770_ = lean_usize_dec_lt(v_i_758_, v_sz_757_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; 
v___x_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_771_, 0, v_b_759_);
return v___x_771_;
}
else
{
lean_object* v_snd_772_; lean_object* v_fst_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_823_; 
v_snd_772_ = lean_ctor_get(v_b_759_, 1);
v_fst_773_ = lean_ctor_get(v_b_759_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v_b_759_);
if (v_isSharedCheck_823_ == 0)
{
v___x_775_ = v_b_759_;
v_isShared_776_ = v_isSharedCheck_823_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_snd_772_);
lean_inc(v_fst_773_);
lean_dec(v_b_759_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_823_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v_array_777_; lean_object* v_start_778_; lean_object* v_stop_779_; uint8_t v___x_780_; 
v_array_777_ = lean_ctor_get(v_snd_772_, 0);
v_start_778_ = lean_ctor_get(v_snd_772_, 1);
v_stop_779_ = lean_ctor_get(v_snd_772_, 2);
v___x_780_ = lean_nat_dec_lt(v_start_778_, v_stop_779_);
if (v___x_780_ == 0)
{
lean_object* v___x_782_; 
if (v_isShared_776_ == 0)
{
v___x_782_ = v___x_775_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_fst_773_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_snd_772_);
v___x_782_ = v_reuseFailAlloc_784_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
lean_object* v___x_783_; 
v___x_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
return v___x_783_;
}
}
else
{
lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_819_; 
lean_inc(v_stop_779_);
lean_inc(v_start_778_);
lean_inc_ref(v_array_777_);
v_isSharedCheck_819_ = !lean_is_exclusive(v_snd_772_);
if (v_isSharedCheck_819_ == 0)
{
lean_object* v_unused_820_; lean_object* v_unused_821_; lean_object* v_unused_822_; 
v_unused_820_ = lean_ctor_get(v_snd_772_, 2);
lean_dec(v_unused_820_);
v_unused_821_ = lean_ctor_get(v_snd_772_, 1);
lean_dec(v_unused_821_);
v_unused_822_ = lean_ctor_get(v_snd_772_, 0);
lean_dec(v_unused_822_);
v___x_786_ = v_snd_772_;
v_isShared_787_ = v_isSharedCheck_819_;
goto v_resetjp_785_;
}
else
{
lean_dec(v_snd_772_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_819_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_792_; 
v___x_788_ = lean_array_fget(v_array_777_, v_start_778_);
v___x_789_ = lean_unsigned_to_nat(1u);
v___x_790_ = lean_nat_add(v_start_778_, v___x_789_);
lean_dec(v_start_778_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 1, v___x_790_);
v___x_792_ = v___x_786_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_array_777_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_818_, 2, v_stop_779_);
v___x_792_ = v_reuseFailAlloc_818_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
uint8_t v___x_793_; uint8_t v___x_794_; 
v___x_793_ = lean_unbox(v___x_788_);
lean_dec(v___x_788_);
v___x_794_ = l_Lean_BinderInfo_isInstImplicit(v___x_793_);
if (v___x_794_ == 0)
{
lean_object* v___x_796_; 
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 1, v___x_792_);
v___x_796_ = v___x_775_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_fst_773_);
lean_ctor_set(v_reuseFailAlloc_797_, 1, v___x_792_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
v_a_766_ = v___x_796_;
goto v___jp_765_;
}
}
else
{
lean_object* v_a_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v_a_798_ = lean_array_uget_borrowed(v_as_756_, v_i_758_);
v___x_799_ = l_Lean_Expr_mvarId_x21(v_a_798_);
v___x_800_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_799_, v___y_761_);
lean_dec(v___x_799_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v_a_801_; 
v_a_801_ = lean_ctor_get(v___x_800_, 0);
lean_inc(v_a_801_);
lean_dec_ref_known(v___x_800_, 1);
if (v_synthAssignedInstances_755_ == 0)
{
uint8_t v___x_809_; 
v___x_809_ = lean_unbox(v_a_801_);
lean_dec(v_a_801_);
if (v___x_809_ == 0)
{
if (v___x_794_ == 0)
{
goto v___jp_802_;
}
else
{
lean_del_object(v___x_775_);
goto v___jp_806_;
}
}
else
{
goto v___jp_802_;
}
}
else
{
lean_dec(v_a_801_);
lean_del_object(v___x_775_);
goto v___jp_806_;
}
v___jp_802_:
{
lean_object* v___x_804_; 
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 1, v___x_792_);
v___x_804_ = v___x_775_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_fst_773_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v___x_792_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
v_a_766_ = v___x_804_;
goto v___jp_765_;
}
}
v___jp_806_:
{
lean_object* v___x_807_; lean_object* v___x_808_; 
lean_inc(v_a_798_);
v___x_807_ = lean_array_push(v_fst_773_, v_a_798_);
v___x_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
lean_ctor_set(v___x_808_, 1, v___x_792_);
v_a_766_ = v___x_808_;
goto v___jp_765_;
}
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_dec_ref(v___x_792_);
lean_del_object(v___x_775_);
lean_dec(v_fst_773_);
v_a_810_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_800_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_800_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
}
}
}
}
}
v___jp_765_:
{
size_t v___x_767_; size_t v___x_768_; 
v___x_767_ = ((size_t)1ULL);
v___x_768_ = lean_usize_add(v_i_758_, v___x_767_);
v_i_758_ = v___x_768_;
v_b_759_ = v_a_766_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1___boxed(lean_object* v_synthAssignedInstances_824_, lean_object* v_as_825_, lean_object* v_sz_826_, lean_object* v_i_827_, lean_object* v_b_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
uint8_t v_synthAssignedInstances_boxed_834_; size_t v_sz_boxed_835_; size_t v_i_boxed_836_; lean_object* v_res_837_; 
v_synthAssignedInstances_boxed_834_ = lean_unbox(v_synthAssignedInstances_824_);
v_sz_boxed_835_ = lean_unbox_usize(v_sz_826_);
lean_dec(v_sz_826_);
v_i_boxed_836_ = lean_unbox_usize(v_i_827_);
lean_dec(v_i_827_);
v_res_837_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(v_synthAssignedInstances_boxed_834_, v_as_825_, v_sz_boxed_835_, v_i_boxed_836_, v_b_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec_ref(v_as_825_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(lean_object* v_tacticName_838_, lean_object* v_mvarId_839_, uint8_t v_allowSynthFailures_840_, lean_object* v_a_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; uint8_t v___x_849_; 
v___x_847_ = lean_array_get_size(v_a_841_);
v___x_848_ = lean_unsigned_to_nat(0u);
v___x_849_ = lean_nat_dec_eq(v___x_847_, v___x_848_);
if (v___x_849_ == 0)
{
lean_object* v___x_850_; 
lean_inc(v_mvarId_839_);
lean_inc(v_tacticName_838_);
v___x_850_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(v_tacticName_838_, v_mvarId_839_, v_allowSynthFailures_840_, v_a_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
lean_dec_ref(v_a_841_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v_a_851_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_a_851_);
lean_dec_ref_known(v___x_850_, 1);
v_a_841_ = v_a_851_;
goto _start;
}
else
{
lean_dec(v_mvarId_839_);
lean_dec(v_tacticName_838_);
return v___x_850_;
}
}
else
{
lean_object* v___x_853_; 
lean_dec(v_mvarId_839_);
lean_dec(v_tacticName_838_);
v___x_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_853_, 0, v_a_841_);
return v___x_853_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg___boxed(lean_object* v_tacticName_854_, lean_object* v_mvarId_855_, lean_object* v_allowSynthFailures_856_, lean_object* v_a_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
uint8_t v_allowSynthFailures_boxed_863_; lean_object* v_res_864_; 
v_allowSynthFailures_boxed_863_ = lean_unbox(v_allowSynthFailures_856_);
v_res_864_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(v_tacticName_854_, v_mvarId_855_, v_allowSynthFailures_boxed_863_, v_a_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances(lean_object* v_tacticName_865_, lean_object* v_mvarId_866_, lean_object* v_mvarsNew_867_, lean_object* v_binderInfos_868_, uint8_t v_synthAssignedInstances_869_, uint8_t v_allowSynthFailures_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
lean_object* v___x_876_; lean_object* v_todo_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; size_t v_sz_881_; size_t v___x_882_; lean_object* v___x_883_; 
v___x_876_ = lean_unsigned_to_nat(0u);
v_todo_877_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0));
v___x_878_ = lean_array_get_size(v_binderInfos_868_);
v___x_879_ = l_Array_toSubarray___redArg(v_binderInfos_868_, v___x_876_, v___x_878_);
v___x_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_880_, 0, v_todo_877_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v_sz_881_ = lean_array_size(v_mvarsNew_867_);
v___x_882_ = ((size_t)0ULL);
v___x_883_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(v_synthAssignedInstances_869_, v_mvarsNew_867_, v_sz_881_, v___x_882_, v___x_880_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v_fst_885_; lean_object* v___x_886_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_884_);
lean_dec_ref_known(v___x_883_, 1);
v_fst_885_ = lean_ctor_get(v_a_884_, 0);
lean_inc(v_fst_885_);
lean_dec(v_a_884_);
v___x_886_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(v_tacticName_865_, v_mvarId_866_, v_allowSynthFailures_870_, v_fst_885_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_894_; 
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_894_ == 0)
{
lean_object* v_unused_895_; 
v_unused_895_ = lean_ctor_get(v___x_886_, 0);
lean_dec(v_unused_895_);
v___x_888_ = v___x_886_;
v_isShared_889_ = v_isSharedCheck_894_;
goto v_resetjp_887_;
}
else
{
lean_dec(v___x_886_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_894_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_890_; lean_object* v___x_892_; 
v___x_890_ = lean_box(0);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v___x_890_);
v___x_892_ = v___x_888_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_890_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
else
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_903_; 
v_a_896_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_903_ == 0)
{
v___x_898_ = v___x_886_;
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_886_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_901_; 
if (v_isShared_899_ == 0)
{
v___x_901_ = v___x_898_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_896_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
else
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
lean_dec(v_mvarId_866_);
lean_dec(v_tacticName_865_);
v_a_904_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_911_ == 0)
{
v___x_906_ = v___x_883_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_883_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_904_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances___boxed(lean_object* v_tacticName_912_, lean_object* v_mvarId_913_, lean_object* v_mvarsNew_914_, lean_object* v_binderInfos_915_, lean_object* v_synthAssignedInstances_916_, lean_object* v_allowSynthFailures_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_){
_start:
{
uint8_t v_synthAssignedInstances_boxed_923_; uint8_t v_allowSynthFailures_boxed_924_; lean_object* v_res_925_; 
v_synthAssignedInstances_boxed_923_ = lean_unbox(v_synthAssignedInstances_916_);
v_allowSynthFailures_boxed_924_ = lean_unbox(v_allowSynthFailures_917_);
v_res_925_ = l_Lean_Meta_synthAppInstances(v_tacticName_912_, v_mvarId_913_, v_mvarsNew_914_, v_binderInfos_915_, v_synthAssignedInstances_boxed_923_, v_allowSynthFailures_boxed_924_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
lean_dec(v_a_921_);
lean_dec_ref(v_a_920_);
lean_dec(v_a_919_);
lean_dec_ref(v_a_918_);
lean_dec_ref(v_mvarsNew_914_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0(lean_object* v_mvarId_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v_mvarId_926_, v___y_928_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___boxed(lean_object* v_mvarId_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0(v_mvarId_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v_mvarId_933_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2(lean_object* v_tacticName_940_, lean_object* v_mvarId_941_, uint8_t v_allowSynthFailures_942_, lean_object* v_inst_943_, lean_object* v_a_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(v_tacticName_940_, v_mvarId_941_, v_allowSynthFailures_942_, v_a_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___boxed(lean_object* v_tacticName_951_, lean_object* v_mvarId_952_, lean_object* v_allowSynthFailures_953_, lean_object* v_inst_954_, lean_object* v_a_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
uint8_t v_allowSynthFailures_boxed_961_; lean_object* v_res_962_; 
v_allowSynthFailures_boxed_961_ = lean_unbox(v_allowSynthFailures_953_);
v_res_962_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2(v_tacticName_951_, v_mvarId_952_, v_allowSynthFailures_boxed_961_, v_inst_954_, v_a_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
return v_res_962_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0(lean_object* v_00_u03b2_963_, lean_object* v_x_964_, lean_object* v_x_965_){
_start:
{
uint8_t v___x_966_; 
v___x_966_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_x_964_, v_x_965_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___boxed(lean_object* v_00_u03b2_967_, lean_object* v_x_968_, lean_object* v_x_969_){
_start:
{
uint8_t v_res_970_; lean_object* v_r_971_; 
v_res_970_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0(v_00_u03b2_967_, v_x_968_, v_x_969_);
lean_dec(v_x_969_);
lean_dec_ref(v_x_968_);
v_r_971_ = lean_box(v_res_970_);
return v_r_971_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_972_, lean_object* v_x_973_, size_t v_x_974_, lean_object* v_x_975_){
_start:
{
uint8_t v___x_976_; 
v___x_976_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_973_, v_x_974_, v_x_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_977_, lean_object* v_x_978_, lean_object* v_x_979_, lean_object* v_x_980_){
_start:
{
size_t v_x_3147__boxed_981_; uint8_t v_res_982_; lean_object* v_r_983_; 
v_x_3147__boxed_981_ = lean_unbox_usize(v_x_979_);
lean_dec(v_x_979_);
v_res_982_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1(v_00_u03b2_977_, v_x_978_, v_x_3147__boxed_981_, v_x_980_);
lean_dec(v_x_980_);
lean_dec_ref(v_x_978_);
v_r_983_ = lean_box(v_res_982_);
return v_r_983_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_984_, lean_object* v_keys_985_, lean_object* v_vals_986_, lean_object* v_heq_987_, lean_object* v_i_988_, lean_object* v_k_989_){
_start:
{
uint8_t v___x_990_; 
v___x_990_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_985_, v_i_988_, v_k_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_991_, lean_object* v_keys_992_, lean_object* v_vals_993_, lean_object* v_heq_994_, lean_object* v_i_995_, lean_object* v_k_996_){
_start:
{
uint8_t v_res_997_; lean_object* v_r_998_; 
v_res_997_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_991_, v_keys_992_, v_vals_993_, v_heq_994_, v_i_995_, v_k_996_);
lean_dec(v_k_996_);
lean_dec_ref(v_vals_993_);
lean_dec_ref(v_keys_992_);
v_r_998_ = lean_box(v_res_997_);
return v_r_998_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(lean_object* v_newMVars_999_, lean_object* v_binderInfos_1000_, lean_object* v_a_1001_, lean_object* v_n_1002_, lean_object* v_i_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v_zero_1009_; uint8_t v_isZero_1010_; 
v_zero_1009_ = lean_unsigned_to_nat(0u);
v_isZero_1010_ = lean_nat_dec_eq(v_i_1003_, v_zero_1009_);
if (v_isZero_1010_ == 1)
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
lean_dec(v_i_1003_);
lean_dec(v_a_1001_);
v___x_1011_ = lean_box(0);
v___x_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
return v___x_1012_;
}
else
{
uint8_t v___x_1013_; lean_object* v_one_1014_; lean_object* v_n_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v_a_1021_; uint8_t v___x_1022_; 
v___x_1013_ = 0;
v_one_1014_ = lean_unsigned_to_nat(1u);
v_n_1015_ = lean_nat_sub(v_i_1003_, v_one_1014_);
lean_dec(v_i_1003_);
v___x_1016_ = lean_nat_sub(v_n_1002_, v_n_1015_);
v___x_1017_ = lean_nat_sub(v___x_1016_, v_one_1014_);
lean_dec(v___x_1016_);
v___x_1018_ = lean_array_fget_borrowed(v_newMVars_999_, v___x_1017_);
v___x_1019_ = l_Lean_Expr_mvarId_x21(v___x_1018_);
v___x_1020_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_1019_, v___y_1005_);
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_a_1021_);
lean_dec_ref(v___x_1020_);
v___x_1022_ = lean_unbox(v_a_1021_);
lean_dec(v_a_1021_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1023_; lean_object* v___x_1024_; uint8_t v___x_1025_; uint8_t v___x_1026_; 
v___x_1023_ = lean_box(v___x_1013_);
v___x_1024_ = lean_array_get(v___x_1023_, v_binderInfos_1000_, v___x_1017_);
lean_dec(v___x_1017_);
lean_dec(v___x_1023_);
v___x_1025_ = lean_unbox(v___x_1024_);
lean_dec(v___x_1024_);
v___x_1026_ = l_Lean_BinderInfo_isInstImplicit(v___x_1025_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1027_; 
lean_inc(v___x_1019_);
v___x_1027_ = l_Lean_MVarId_getTag(v___x_1019_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
lean_inc(v_a_1028_);
lean_dec_ref_known(v___x_1027_, 1);
lean_inc(v_a_1001_);
v___x_1029_ = l_Lean_Meta_appendTag(v_a_1001_, v_a_1028_);
lean_dec(v_a_1028_);
v___x_1030_ = l_Lean_MVarId_setTag___redArg(v___x_1019_, v___x_1029_, v___y_1005_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_dec_ref_known(v___x_1030_, 1);
v_i_1003_ = v_n_1015_;
goto _start;
}
else
{
lean_dec(v_n_1015_);
lean_dec(v_a_1001_);
return v___x_1030_;
}
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
lean_dec(v___x_1019_);
lean_dec(v_n_1015_);
lean_dec(v_a_1001_);
v_a_1032_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_1027_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1027_);
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
else
{
lean_dec(v___x_1019_);
v_i_1003_ = v_n_1015_;
goto _start;
}
}
else
{
lean_dec(v___x_1019_);
lean_dec(v___x_1017_);
v_i_1003_ = v_n_1015_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg___boxed(lean_object* v_newMVars_1042_, lean_object* v_binderInfos_1043_, lean_object* v_a_1044_, lean_object* v_n_1045_, lean_object* v_i_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_1042_, v_binderInfos_1043_, v_a_1044_, v_n_1045_, v_i_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v_n_1045_);
lean_dec_ref(v_binderInfos_1043_);
lean_dec_ref(v_newMVars_1042_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendParentTag(lean_object* v_mvarId_1053_, lean_object* v_newMVars_1054_, lean_object* v_binderInfos_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = l_Lean_instInhabitedExpr;
v___x_1062_ = l_Lean_MVarId_getTag(v_mvarId_1053_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1080_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1065_ = v___x_1062_;
v_isShared_1066_ = v_isSharedCheck_1080_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1062_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1080_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; uint8_t v___x_1069_; 
v___x_1067_ = lean_array_get_size(v_newMVars_1054_);
v___x_1068_ = lean_unsigned_to_nat(1u);
v___x_1069_ = lean_nat_dec_eq(v___x_1067_, v___x_1068_);
if (v___x_1069_ == 0)
{
uint8_t v___x_1070_; 
v___x_1070_ = l_Lean_Name_isAnonymous(v_a_1063_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1071_; 
lean_del_object(v___x_1065_);
v___x_1071_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_1054_, v_binderInfos_1055_, v_a_1063_, v___x_1067_, v___x_1067_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_);
return v___x_1071_;
}
else
{
lean_object* v___x_1072_; lean_object* v___x_1074_; 
lean_dec(v_a_1063_);
v___x_1072_ = lean_box(0);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 0, v___x_1072_);
v___x_1074_ = v___x_1065_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1072_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
else
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
lean_del_object(v___x_1065_);
v___x_1076_ = lean_unsigned_to_nat(0u);
v___x_1077_ = lean_array_get_borrowed(v___x_1061_, v_newMVars_1054_, v___x_1076_);
v___x_1078_ = l_Lean_Expr_mvarId_x21(v___x_1077_);
v___x_1079_ = l_Lean_MVarId_setTag___redArg(v___x_1078_, v_a_1063_, v_a_1057_);
return v___x_1079_;
}
}
}
else
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1088_; 
v_a_1081_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1083_ = v___x_1062_;
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1062_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1081_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendParentTag___boxed(lean_object* v_mvarId_1089_, lean_object* v_newMVars_1090_, lean_object* v_binderInfos_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_Meta_appendParentTag(v_mvarId_1089_, v_newMVars_1090_, v_binderInfos_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
lean_dec(v_a_1095_);
lean_dec_ref(v_a_1094_);
lean_dec(v_a_1093_);
lean_dec_ref(v_a_1092_);
lean_dec_ref(v_binderInfos_1091_);
lean_dec_ref(v_newMVars_1090_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0(lean_object* v_newMVars_1098_, lean_object* v_binderInfos_1099_, lean_object* v_a_1100_, lean_object* v_n_1101_, lean_object* v_i_1102_, lean_object* v_a_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_1098_, v_binderInfos_1099_, v_a_1100_, v_n_1101_, v_i_1102_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___boxed(lean_object* v_newMVars_1110_, lean_object* v_binderInfos_1111_, lean_object* v_a_1112_, lean_object* v_n_1113_, lean_object* v_i_1114_, lean_object* v_a_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0(v_newMVars_1110_, v_binderInfos_1111_, v_a_1112_, v_n_1113_, v_i_1114_, v_a_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v_n_1113_);
lean_dec_ref(v_binderInfos_1111_);
lean_dec_ref(v_newMVars_1110_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_postprocessAppMVars(lean_object* v_tacticName_1122_, lean_object* v_mvarId_1123_, lean_object* v_newMVars_1124_, lean_object* v_binderInfos_1125_, uint8_t v_synthAssignedInstances_1126_, uint8_t v_allowSynthFailures_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Lean_Meta_synthAppInstances(v_tacticName_1122_, v_mvarId_1123_, v_newMVars_1124_, v_binderInfos_1125_, v_synthAssignedInstances_1126_, v_allowSynthFailures_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_postprocessAppMVars___boxed(lean_object* v_tacticName_1134_, lean_object* v_mvarId_1135_, lean_object* v_newMVars_1136_, lean_object* v_binderInfos_1137_, lean_object* v_synthAssignedInstances_1138_, lean_object* v_allowSynthFailures_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_){
_start:
{
uint8_t v_synthAssignedInstances_boxed_1145_; uint8_t v_allowSynthFailures_boxed_1146_; lean_object* v_res_1147_; 
v_synthAssignedInstances_boxed_1145_ = lean_unbox(v_synthAssignedInstances_1138_);
v_allowSynthFailures_boxed_1146_ = lean_unbox(v_allowSynthFailures_1139_);
v_res_1147_ = l_Lean_Meta_postprocessAppMVars(v_tacticName_1134_, v_mvarId_1135_, v_newMVars_1136_, v_binderInfos_1137_, v_synthAssignedInstances_boxed_1145_, v_allowSynthFailures_boxed_1146_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_);
lean_dec(v_a_1143_);
lean_dec_ref(v_a_1142_);
lean_dec(v_a_1141_);
lean_dec_ref(v_a_1140_);
lean_dec_ref(v_newMVars_1136_);
return v_res_1147_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0(lean_object* v_mvar_1148_, lean_object* v_mvarId_1149_){
_start:
{
lean_object* v___x_1150_; uint8_t v___x_1151_; 
v___x_1150_ = l_Lean_Expr_mvarId_x21(v_mvar_1148_);
v___x_1151_ = l_Lean_instBEqMVarId_beq(v_mvarId_1149_, v___x_1150_);
lean_dec(v___x_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0___boxed(lean_object* v_mvar_1152_, lean_object* v_mvarId_1153_){
_start:
{
uint8_t v_res_1154_; lean_object* v_r_1155_; 
v_res_1154_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0(v_mvar_1152_, v_mvarId_1153_);
lean_dec(v_mvarId_1153_);
lean_dec_ref(v_mvar_1152_);
v_r_1155_ = lean_box(v_res_1154_);
return v_r_1155_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(lean_object* v_mvar_1156_, lean_object* v_as_1157_, size_t v_i_1158_, size_t v_stop_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
uint8_t v___x_1169_; 
v___x_1169_ = lean_usize_dec_eq(v_i_1158_, v_stop_1159_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1170_; uint8_t v___x_1171_; 
v___x_1170_ = lean_array_uget_borrowed(v_as_1157_, v_i_1158_);
v___x_1171_ = lean_expr_eqv(v_mvar_1156_, v___x_1170_);
if (v___x_1171_ == 0)
{
lean_object* v___f_1172_; uint8_t v___x_1173_; lean_object* v___x_1174_; 
lean_inc_ref(v_mvar_1156_);
v___f_1172_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1172_, 0, v_mvar_1156_);
v___x_1173_ = 1;
lean_inc(v___y_1163_);
lean_inc_ref(v___y_1162_);
lean_inc(v___y_1161_);
lean_inc_ref(v___y_1160_);
lean_inc(v___x_1170_);
v___x_1174_ = lean_infer_type(v___x_1170_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1189_; 
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1177_ = v___x_1174_;
v_isShared_1178_ = v_isSharedCheck_1189_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1174_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1189_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1179_ = lean_box(0);
v___x_1180_ = l_Lean_FindMVar_main(v___f_1172_, v_a_1175_, v___x_1179_);
if (lean_obj_tag(v___x_1180_) == 0)
{
if (v___x_1171_ == 0)
{
lean_del_object(v___x_1177_);
goto v___jp_1165_;
}
else
{
lean_object* v___x_1181_; lean_object* v___x_1183_; 
lean_dec_ref(v_mvar_1156_);
v___x_1181_ = lean_box(v___x_1173_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v___x_1181_);
v___x_1183_ = v___x_1177_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1181_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
else
{
lean_object* v___x_1185_; lean_object* v___x_1187_; 
lean_dec_ref_known(v___x_1180_, 1);
lean_dec_ref(v_mvar_1156_);
v___x_1185_ = lean_box(v___x_1173_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v___x_1185_);
v___x_1187_ = v___x_1177_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1185_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
else
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1197_; 
lean_dec_ref(v___f_1172_);
lean_dec_ref(v_mvar_1156_);
v_a_1190_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1192_ = v___x_1174_;
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v___x_1174_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1195_; 
if (v_isShared_1193_ == 0)
{
v___x_1195_ = v___x_1192_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_a_1190_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
}
else
{
goto v___jp_1165_;
}
}
else
{
uint8_t v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
lean_dec_ref(v_mvar_1156_);
v___x_1198_ = 0;
v___x_1199_ = lean_box(v___x_1198_);
v___x_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
return v___x_1200_;
}
v___jp_1165_:
{
size_t v___x_1166_; size_t v___x_1167_; 
v___x_1166_ = ((size_t)1ULL);
v___x_1167_ = lean_usize_add(v_i_1158_, v___x_1166_);
v_i_1158_ = v___x_1167_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___boxed(lean_object* v_mvar_1201_, lean_object* v_as_1202_, lean_object* v_i_1203_, lean_object* v_stop_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
size_t v_i_boxed_1210_; size_t v_stop_boxed_1211_; lean_object* v_res_1212_; 
v_i_boxed_1210_ = lean_unbox_usize(v_i_1203_);
lean_dec(v_i_1203_);
v_stop_boxed_1211_ = lean_unbox_usize(v_stop_1204_);
lean_dec(v_stop_1204_);
v_res_1212_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(v_mvar_1201_, v_as_1202_, v_i_boxed_1210_, v_stop_boxed_1211_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec_ref(v_as_1202_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(lean_object* v_mvar_1213_, lean_object* v_otherMVars_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; uint8_t v___x_1222_; 
v___x_1220_ = lean_unsigned_to_nat(0u);
v___x_1221_ = lean_array_get_size(v_otherMVars_1214_);
v___x_1222_ = lean_nat_dec_lt(v___x_1220_, v___x_1221_);
if (v___x_1222_ == 0)
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
lean_dec_ref(v_mvar_1213_);
v___x_1223_ = lean_box(v___x_1222_);
v___x_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
return v___x_1224_;
}
else
{
if (v___x_1222_ == 0)
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
lean_dec_ref(v_mvar_1213_);
v___x_1225_ = lean_box(v___x_1222_);
v___x_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
return v___x_1226_;
}
else
{
size_t v___x_1227_; size_t v___x_1228_; lean_object* v___x_1229_; 
v___x_1227_ = ((size_t)0ULL);
v___x_1228_ = lean_usize_of_nat(v___x_1221_);
v___x_1229_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(v_mvar_1213_, v_otherMVars_1214_, v___x_1227_, v___x_1228_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_);
return v___x_1229_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___boxed(lean_object* v_mvar_1230_, lean_object* v_otherMVars_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(v_mvar_1230_, v_otherMVars_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_);
lean_dec(v_a_1235_);
lean_dec_ref(v_a_1234_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec_ref(v_otherMVars_1231_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(lean_object* v_mvars_1238_, lean_object* v_as_1239_, size_t v_i_1240_, size_t v_stop_1241_, lean_object* v_b_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
lean_object* v_a_1249_; uint8_t v___x_1253_; 
v___x_1253_ = lean_usize_dec_eq(v_i_1240_, v_stop_1241_);
if (v___x_1253_ == 0)
{
lean_object* v_fst_1254_; lean_object* v_snd_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1280_; 
v_fst_1254_ = lean_ctor_get(v_b_1242_, 0);
v_snd_1255_ = lean_ctor_get(v_b_1242_, 1);
v_isSharedCheck_1280_ = !lean_is_exclusive(v_b_1242_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1257_ = v_b_1242_;
v_isShared_1258_ = v_isSharedCheck_1280_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_snd_1255_);
lean_inc(v_fst_1254_);
lean_dec(v_b_1242_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1280_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1259_; lean_object* v_currMVarId_1260_; lean_object* v___x_1261_; 
v___x_1259_ = lean_array_uget_borrowed(v_as_1239_, v_i_1240_);
v_currMVarId_1260_ = l_Lean_Expr_mvarId_x21(v___x_1259_);
lean_inc(v___x_1259_);
v___x_1261_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(v___x_1259_, v_mvars_1238_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; uint8_t v___x_1263_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_a_1262_);
lean_dec_ref_known(v___x_1261_, 1);
v___x_1263_ = lean_unbox(v_a_1262_);
lean_dec(v_a_1262_);
if (v___x_1263_ == 0)
{
lean_object* v___x_1264_; lean_object* v___x_1266_; 
v___x_1264_ = lean_array_push(v_fst_1254_, v_currMVarId_1260_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 0, v___x_1264_);
v___x_1266_ = v___x_1257_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1264_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v_snd_1255_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
v_a_1249_ = v___x_1266_;
goto v___jp_1248_;
}
}
else
{
lean_object* v___x_1268_; lean_object* v___x_1270_; 
v___x_1268_ = lean_array_push(v_snd_1255_, v_currMVarId_1260_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 1, v___x_1268_);
v___x_1270_ = v___x_1257_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_fst_1254_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v___x_1268_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
v_a_1249_ = v___x_1270_;
goto v___jp_1248_;
}
}
}
else
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1279_; 
lean_dec(v_currMVarId_1260_);
lean_del_object(v___x_1257_);
lean_dec(v_snd_1255_);
lean_dec(v_fst_1254_);
v_a_1272_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1274_ = v___x_1261_;
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1261_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1272_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
}
else
{
lean_object* v___x_1281_; 
v___x_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1281_, 0, v_b_1242_);
return v___x_1281_;
}
v___jp_1248_:
{
size_t v___x_1250_; size_t v___x_1251_; 
v___x_1250_ = ((size_t)1ULL);
v___x_1251_ = lean_usize_add(v_i_1240_, v___x_1250_);
v_i_1240_ = v___x_1251_;
v_b_1242_ = v_a_1249_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0___boxed(lean_object* v_mvars_1282_, lean_object* v_as_1283_, lean_object* v_i_1284_, lean_object* v_stop_1285_, lean_object* v_b_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
size_t v_i_boxed_1292_; size_t v_stop_boxed_1293_; lean_object* v_res_1294_; 
v_i_boxed_1292_ = lean_unbox_usize(v_i_1284_);
lean_dec(v_i_1284_);
v_stop_boxed_1293_ = lean_unbox_usize(v_stop_1285_);
lean_dec(v_stop_1285_);
v_res_1294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_1282_, v_as_1283_, v_i_boxed_1292_, v_stop_boxed_1293_, v_b_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec_ref(v_as_1283_);
lean_dec_ref(v_mvars_1282_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(lean_object* v_mvars_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; uint8_t v___x_1308_; 
v___x_1305_ = lean_unsigned_to_nat(0u);
v___x_1306_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1));
v___x_1307_ = lean_array_get_size(v_mvars_1299_);
v___x_1308_ = lean_nat_dec_lt(v___x_1305_, v___x_1307_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; 
v___x_1309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1306_);
return v___x_1309_;
}
else
{
uint8_t v___x_1310_; 
v___x_1310_ = lean_nat_dec_le(v___x_1307_, v___x_1307_);
if (v___x_1310_ == 0)
{
if (v___x_1308_ == 0)
{
lean_object* v___x_1311_; 
v___x_1311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1306_);
return v___x_1311_;
}
else
{
size_t v___x_1312_; size_t v___x_1313_; lean_object* v___x_1314_; 
v___x_1312_ = ((size_t)0ULL);
v___x_1313_ = lean_usize_of_nat(v___x_1307_);
v___x_1314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_1299_, v_mvars_1299_, v___x_1312_, v___x_1313_, v___x_1306_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_);
return v___x_1314_;
}
}
else
{
size_t v___x_1315_; size_t v___x_1316_; lean_object* v___x_1317_; 
v___x_1315_ = ((size_t)0ULL);
v___x_1316_ = lean_usize_of_nat(v___x_1307_);
v___x_1317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_1299_, v_mvars_1299_, v___x_1315_, v___x_1316_, v___x_1306_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_);
return v___x_1317_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___boxed(lean_object* v_mvars_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_);
lean_dec(v_a_1322_);
lean_dec_ref(v_a_1321_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
lean_dec_ref(v_mvars_1318_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals_spec__0(lean_object* v_a_1325_, lean_object* v_a_1326_){
_start:
{
if (lean_obj_tag(v_a_1325_) == 0)
{
lean_object* v___x_1327_; 
v___x_1327_ = l_List_reverse___redArg(v_a_1326_);
return v___x_1327_;
}
else
{
lean_object* v_head_1328_; lean_object* v_tail_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1338_; 
v_head_1328_ = lean_ctor_get(v_a_1325_, 0);
v_tail_1329_ = lean_ctor_get(v_a_1325_, 1);
v_isSharedCheck_1338_ = !lean_is_exclusive(v_a_1325_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1331_ = v_a_1325_;
v_isShared_1332_ = v_isSharedCheck_1338_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_tail_1329_);
lean_inc(v_head_1328_);
lean_dec(v_a_1325_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1338_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1333_; lean_object* v___x_1335_; 
v___x_1333_ = l_Lean_Expr_mvarId_x21(v_head_1328_);
lean_dec(v_head_1328_);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 1, v_a_1326_);
lean_ctor_set(v___x_1331_, 0, v___x_1333_);
v___x_1335_ = v___x_1331_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v___x_1333_);
lean_ctor_set(v_reuseFailAlloc_1337_, 1, v_a_1326_);
v___x_1335_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
v_a_1325_ = v_tail_1329_;
v_a_1326_ = v___x_1335_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(lean_object* v_mvars_1339_, uint8_t v_x_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_){
_start:
{
switch(v_x_1340_)
{
case 0:
{
lean_object* v___x_1346_; 
v___x_1346_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1339_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_);
lean_dec_ref(v_mvars_1339_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1359_; 
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1349_ = v___x_1346_;
v_isShared_1350_ = v_isSharedCheck_1359_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1346_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1359_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v_fst_1351_; lean_object* v_snd_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1357_; 
v_fst_1351_ = lean_ctor_get(v_a_1347_, 0);
lean_inc(v_fst_1351_);
v_snd_1352_ = lean_ctor_get(v_a_1347_, 1);
lean_inc(v_snd_1352_);
lean_dec(v_a_1347_);
v___x_1353_ = lean_array_to_list(v_fst_1351_);
v___x_1354_ = lean_array_to_list(v_snd_1352_);
v___x_1355_ = l_List_appendTR___redArg(v___x_1353_, v___x_1354_);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 0, v___x_1355_);
v___x_1357_ = v___x_1349_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v___x_1355_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
v_a_1360_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1346_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1346_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
case 1:
{
lean_object* v___x_1368_; 
v___x_1368_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1339_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_);
lean_dec_ref(v_mvars_1339_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1378_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1371_ = v___x_1368_;
v_isShared_1372_ = v_isSharedCheck_1378_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1368_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1378_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v_fst_1373_; lean_object* v___x_1374_; lean_object* v___x_1376_; 
v_fst_1373_ = lean_ctor_get(v_a_1369_, 0);
lean_inc(v_fst_1373_);
lean_dec(v_a_1369_);
v___x_1374_ = lean_array_to_list(v_fst_1373_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v___x_1374_);
v___x_1376_ = v___x_1371_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1374_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
v_a_1379_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v___x_1368_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1368_);
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
default: 
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1387_ = lean_array_to_list(v_mvars_1339_);
v___x_1388_ = lean_box(0);
v___x_1389_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals_spec__0(v___x_1387_, v___x_1388_);
v___x_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
return v___x_1390_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals___boxed(lean_object* v_mvars_1391_, lean_object* v_x_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_){
_start:
{
uint8_t v_x_731__boxed_1398_; lean_object* v_res_1399_; 
v_x_731__boxed_1398_ = lean_unbox(v_x_1392_);
v_res_1399_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(v_mvars_1391_, v_x_731__boxed_1398_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_);
lean_dec(v_a_1396_);
lean_dec_ref(v_a_1395_);
lean_dec(v_a_1394_);
lean_dec_ref(v_a_1393_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(uint8_t v_approx_1400_, lean_object* v_a_1401_, lean_object* v_b_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_){
_start:
{
if (v_approx_1400_ == 0)
{
lean_object* v___x_1408_; 
v___x_1408_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1401_, v_b_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_);
return v___x_1408_;
}
else
{
lean_object* v___x_1409_; uint8_t v_constApprox_1410_; uint8_t v_isDefEqStuckEx_1411_; uint8_t v_unificationHints_1412_; uint8_t v_proofIrrelevance_1413_; uint8_t v_assignSyntheticOpaque_1414_; uint8_t v_offsetCnstrs_1415_; uint8_t v_transparency_1416_; uint8_t v_etaStruct_1417_; uint8_t v_univApprox_1418_; uint8_t v_iota_1419_; uint8_t v_beta_1420_; uint8_t v_proj_1421_; uint8_t v_zeta_1422_; uint8_t v_zetaDelta_1423_; uint8_t v_zetaUnused_1424_; uint8_t v_zetaHave_1425_; uint8_t v_canUnfoldPredicateConfig_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1447_; 
v___x_1409_ = l_Lean_Meta_Context_config(v_a_1403_);
v_constApprox_1410_ = lean_ctor_get_uint8(v___x_1409_, 3);
v_isDefEqStuckEx_1411_ = lean_ctor_get_uint8(v___x_1409_, 4);
v_unificationHints_1412_ = lean_ctor_get_uint8(v___x_1409_, 5);
v_proofIrrelevance_1413_ = lean_ctor_get_uint8(v___x_1409_, 6);
v_assignSyntheticOpaque_1414_ = lean_ctor_get_uint8(v___x_1409_, 7);
v_offsetCnstrs_1415_ = lean_ctor_get_uint8(v___x_1409_, 8);
v_transparency_1416_ = lean_ctor_get_uint8(v___x_1409_, 9);
v_etaStruct_1417_ = lean_ctor_get_uint8(v___x_1409_, 10);
v_univApprox_1418_ = lean_ctor_get_uint8(v___x_1409_, 11);
v_iota_1419_ = lean_ctor_get_uint8(v___x_1409_, 12);
v_beta_1420_ = lean_ctor_get_uint8(v___x_1409_, 13);
v_proj_1421_ = lean_ctor_get_uint8(v___x_1409_, 14);
v_zeta_1422_ = lean_ctor_get_uint8(v___x_1409_, 15);
v_zetaDelta_1423_ = lean_ctor_get_uint8(v___x_1409_, 16);
v_zetaUnused_1424_ = lean_ctor_get_uint8(v___x_1409_, 17);
v_zetaHave_1425_ = lean_ctor_get_uint8(v___x_1409_, 18);
v_canUnfoldPredicateConfig_1426_ = lean_ctor_get_uint8(v___x_1409_, 19);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1428_ = v___x_1409_;
v_isShared_1429_ = v_isSharedCheck_1447_;
goto v_resetjp_1427_;
}
else
{
lean_dec(v___x_1409_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1447_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1431_; 
if (v_isShared_1429_ == 0)
{
v___x_1431_ = v___x_1428_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_1446_, 3, v_constApprox_1410_);
lean_ctor_set_uint8(v_reuseFailAlloc_1446_, 4, v_isDefEqStuckEx_1411_);
lean_ctor_set_uint8(v_reuseFailAlloc_1446_, 5, v_unificationHints_1412_);
lean_ctor_set_uint8(v_reuseFailAlloc_1446_, 6, v_proofIrrelevance_1413_);
lean_ctor_set_uint8(v_reuseFailAlloc_1446_, 7, v_assignSyntheticOpaque_1414_);
lean_ctor_set_uint8(v_reuseFailAlloc_1446_, 8, v_offsetCnstrs_1415_);
lean_ctor_set_uint8(v_reuseFailAlloc_1446_, 9, v_transparency_1416_);
lean_ctor_set_uint8(v_reuseFailAlloc_1446_, 10, v_etaStruct_1417_);
lean_ctor_set_uint8(v_reuseFailAlloc_1446_, 11, v_univApprox_1418_);
lean_ctor_set_uint8(v_reuseFailAlloc_1446_, 12, v_iota_1419_);
lean_ctor_set_uint8(v_reuseFailAlloc_1446_, 13, v_beta_1420_);
lean_ctor_set_uint8(v_reuseFailAlloc_1446_, 14, v_proj_1421_);
lean_ctor_set_uint8(v_reuseFailAlloc_1446_, 15, v_zeta_1422_);
lean_ctor_set_uint8(v_reuseFailAlloc_1446_, 16, v_zetaDelta_1423_);
lean_ctor_set_uint8(v_reuseFailAlloc_1446_, 17, v_zetaUnused_1424_);
lean_ctor_set_uint8(v_reuseFailAlloc_1446_, 18, v_zetaHave_1425_);
lean_ctor_set_uint8(v_reuseFailAlloc_1446_, 19, v_canUnfoldPredicateConfig_1426_);
v___x_1431_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
uint8_t v_trackZetaDelta_1432_; lean_object* v_zetaDeltaSet_1433_; lean_object* v_lctx_1434_; lean_object* v_localInstances_1435_; lean_object* v_defEqCtx_x3f_1436_; lean_object* v_synthPendingDepth_1437_; lean_object* v_customCanUnfoldPredicate_x3f_1438_; uint8_t v_univApprox_1439_; uint8_t v_inTypeClassResolution_1440_; uint8_t v_cacheInferType_1441_; uint64_t v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
lean_ctor_set_uint8(v___x_1431_, 0, v_approx_1400_);
lean_ctor_set_uint8(v___x_1431_, 1, v_approx_1400_);
lean_ctor_set_uint8(v___x_1431_, 2, v_approx_1400_);
v_trackZetaDelta_1432_ = lean_ctor_get_uint8(v_a_1403_, sizeof(void*)*7);
v_zetaDeltaSet_1433_ = lean_ctor_get(v_a_1403_, 1);
v_lctx_1434_ = lean_ctor_get(v_a_1403_, 2);
v_localInstances_1435_ = lean_ctor_get(v_a_1403_, 3);
v_defEqCtx_x3f_1436_ = lean_ctor_get(v_a_1403_, 4);
v_synthPendingDepth_1437_ = lean_ctor_get(v_a_1403_, 5);
v_customCanUnfoldPredicate_x3f_1438_ = lean_ctor_get(v_a_1403_, 6);
v_univApprox_1439_ = lean_ctor_get_uint8(v_a_1403_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1440_ = lean_ctor_get_uint8(v_a_1403_, sizeof(void*)*7 + 2);
v_cacheInferType_1441_ = lean_ctor_get_uint8(v_a_1403_, sizeof(void*)*7 + 3);
v___x_1442_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1431_);
v___x_1443_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1443_, 0, v___x_1431_);
lean_ctor_set_uint64(v___x_1443_, sizeof(void*)*1, v___x_1442_);
lean_inc(v_customCanUnfoldPredicate_x3f_1438_);
lean_inc(v_synthPendingDepth_1437_);
lean_inc(v_defEqCtx_x3f_1436_);
lean_inc_ref(v_localInstances_1435_);
lean_inc_ref(v_lctx_1434_);
lean_inc(v_zetaDeltaSet_1433_);
v___x_1444_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1444_, 0, v___x_1443_);
lean_ctor_set(v___x_1444_, 1, v_zetaDeltaSet_1433_);
lean_ctor_set(v___x_1444_, 2, v_lctx_1434_);
lean_ctor_set(v___x_1444_, 3, v_localInstances_1435_);
lean_ctor_set(v___x_1444_, 4, v_defEqCtx_x3f_1436_);
lean_ctor_set(v___x_1444_, 5, v_synthPendingDepth_1437_);
lean_ctor_set(v___x_1444_, 6, v_customCanUnfoldPredicate_x3f_1438_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*7, v_trackZetaDelta_1432_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*7 + 1, v_univApprox_1439_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1440_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*7 + 3, v_cacheInferType_1441_);
v___x_1445_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1401_, v_b_1402_, v___x_1444_, v_a_1404_, v_a_1405_, v_a_1406_);
lean_dec_ref_known(v___x_1444_, 7);
return v___x_1445_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply___boxed(lean_object* v_approx_1448_, lean_object* v_a_1449_, lean_object* v_b_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_){
_start:
{
uint8_t v_approx_boxed_1456_; lean_object* v_res_1457_; 
v_approx_boxed_1456_ = lean_unbox(v_approx_1448_);
v_res_1457_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_approx_boxed_1456_, v_a_1449_, v_b_1450_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_);
lean_dec(v_a_1454_);
lean_dec_ref(v_a_1453_);
lean_dec(v_a_1452_);
lean_dec_ref(v_a_1451_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(lean_object* v_mvarId_1458_, lean_object* v_cfg_1459_, lean_object* v_term_x3f_1460_, lean_object* v_targetType_1461_, lean_object* v_eType_1462_, lean_object* v_rangeNumArgs_1463_, lean_object* v_i_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_){
_start:
{
lean_object* v_conclusionType_x3f_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1475_; lean_object* v_lower_1478_; lean_object* v_upper_1479_; uint8_t v___x_1480_; 
v_lower_1478_ = lean_ctor_get(v_rangeNumArgs_1463_, 0);
v_upper_1479_ = lean_ctor_get(v_rangeNumArgs_1463_, 1);
v___x_1480_ = lean_nat_dec_lt(v_i_1464_, v_upper_1479_);
if (v___x_1480_ == 0)
{
lean_object* v___x_1481_; uint8_t v___x_1482_; 
lean_dec(v_i_1464_);
v___x_1481_ = lean_unsigned_to_nat(0u);
v___x_1482_ = lean_nat_dec_eq(v_lower_1478_, v___x_1481_);
if (v___x_1482_ == 0)
{
lean_object* v___x_1483_; uint8_t v___x_1484_; lean_object* v___x_1485_; 
lean_inc(v_lower_1478_);
v___x_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1483_, 0, v_lower_1478_);
v___x_1484_ = 0;
lean_inc_ref(v_eType_1462_);
v___x_1485_ = l_Lean_Meta_forallMetaTelescopeReducing(v_eType_1462_, v___x_1483_, v___x_1484_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; lean_object* v_snd_1487_; lean_object* v_snd_1488_; lean_object* v___x_1489_; 
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_a_1486_);
lean_dec_ref_known(v___x_1485_, 1);
v_snd_1487_ = lean_ctor_get(v_a_1486_, 1);
lean_inc(v_snd_1487_);
lean_dec(v_a_1486_);
v_snd_1488_ = lean_ctor_get(v_snd_1487_, 1);
lean_inc(v_snd_1488_);
lean_dec(v_snd_1487_);
v___x_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1489_, 0, v_snd_1488_);
v_conclusionType_x3f_1471_ = v___x_1489_;
v___y_1472_ = v_a_1465_;
v___y_1473_ = v_a_1466_;
v___y_1474_ = v_a_1467_;
v___y_1475_ = v_a_1468_;
goto v___jp_1470_;
}
else
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
lean_dec_ref(v_eType_1462_);
lean_dec_ref(v_targetType_1461_);
lean_dec(v_term_x3f_1460_);
lean_dec(v_mvarId_1458_);
v_a_1490_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1492_ = v___x_1485_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1485_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1490_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
else
{
lean_object* v___x_1498_; 
v___x_1498_ = lean_box(0);
v_conclusionType_x3f_1471_ = v___x_1498_;
v___y_1472_ = v_a_1465_;
v___y_1473_ = v_a_1466_;
v___y_1474_ = v_a_1467_;
v___y_1475_ = v_a_1468_;
goto v___jp_1470_;
}
}
else
{
lean_object* v___x_1499_; 
v___x_1499_ = l_Lean_Meta_saveState___redArg(v_a_1466_, v_a_1468_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_a_1500_; lean_object* v___x_1501_; uint8_t v___x_1502_; lean_object* v___x_1503_; 
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_a_1500_);
lean_dec_ref_known(v___x_1499_, 1);
lean_inc(v_i_1464_);
v___x_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1501_, 0, v_i_1464_);
v___x_1502_ = 0;
lean_inc_ref(v_eType_1462_);
v___x_1503_ = l_Lean_Meta_forallMetaTelescopeReducing(v_eType_1462_, v___x_1501_, v___x_1502_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; lean_object* v_snd_1505_; lean_object* v_fst_1506_; lean_object* v_fst_1507_; lean_object* v_snd_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1546_; 
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
lean_inc(v_a_1504_);
lean_dec_ref_known(v___x_1503_, 1);
v_snd_1505_ = lean_ctor_get(v_a_1504_, 1);
lean_inc(v_snd_1505_);
v_fst_1506_ = lean_ctor_get(v_a_1504_, 0);
lean_inc(v_fst_1506_);
lean_dec(v_a_1504_);
v_fst_1507_ = lean_ctor_get(v_snd_1505_, 0);
v_snd_1508_ = lean_ctor_get(v_snd_1505_, 1);
v_isSharedCheck_1546_ = !lean_is_exclusive(v_snd_1505_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1510_ = v_snd_1505_;
v_isShared_1511_ = v_isSharedCheck_1546_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_snd_1508_);
lean_inc(v_fst_1507_);
lean_dec(v_snd_1505_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1546_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
uint8_t v_approx_1512_; lean_object* v___x_1513_; 
v_approx_1512_ = lean_ctor_get_uint8(v_cfg_1459_, 3);
lean_inc_ref(v_targetType_1461_);
v___x_1513_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_approx_1512_, v_snd_1508_, v_targetType_1461_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1537_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1516_ = v___x_1513_;
v_isShared_1517_ = v_isSharedCheck_1537_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1513_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1537_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
uint8_t v___x_1518_; 
v___x_1518_ = lean_unbox(v_a_1514_);
lean_dec(v_a_1514_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; 
lean_del_object(v___x_1516_);
lean_del_object(v___x_1510_);
lean_dec(v_fst_1507_);
lean_dec(v_fst_1506_);
v___x_1519_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1500_, v_a_1466_, v_a_1468_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
lean_dec_ref_known(v___x_1519_, 1);
v___x_1520_ = lean_unsigned_to_nat(1u);
v___x_1521_ = lean_nat_add(v_i_1464_, v___x_1520_);
lean_dec(v_i_1464_);
v_i_1464_ = v___x_1521_;
goto _start;
}
else
{
lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1530_; 
lean_dec(v_i_1464_);
lean_dec_ref(v_eType_1462_);
lean_dec_ref(v_targetType_1461_);
lean_dec(v_term_x3f_1460_);
lean_dec(v_mvarId_1458_);
v_a_1523_ = lean_ctor_get(v___x_1519_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1525_ = v___x_1519_;
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v___x_1519_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1528_; 
if (v_isShared_1526_ == 0)
{
v___x_1528_ = v___x_1525_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_a_1523_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
}
else
{
lean_object* v___x_1532_; 
lean_dec(v_a_1500_);
lean_dec(v_i_1464_);
lean_dec_ref(v_eType_1462_);
lean_dec_ref(v_targetType_1461_);
lean_dec(v_term_x3f_1460_);
lean_dec(v_mvarId_1458_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 1, v_fst_1507_);
lean_ctor_set(v___x_1510_, 0, v_fst_1506_);
v___x_1532_ = v___x_1510_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_fst_1506_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v_fst_1507_);
v___x_1532_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
lean_object* v___x_1534_; 
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 0, v___x_1532_);
v___x_1534_ = v___x_1516_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1532_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
}
}
else
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
lean_del_object(v___x_1510_);
lean_dec(v_fst_1507_);
lean_dec(v_fst_1506_);
lean_dec(v_a_1500_);
lean_dec(v_i_1464_);
lean_dec_ref(v_eType_1462_);
lean_dec_ref(v_targetType_1461_);
lean_dec(v_term_x3f_1460_);
lean_dec(v_mvarId_1458_);
v_a_1538_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1540_ = v___x_1513_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1513_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1538_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
}
else
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1554_; 
lean_dec(v_a_1500_);
lean_dec(v_i_1464_);
lean_dec_ref(v_eType_1462_);
lean_dec_ref(v_targetType_1461_);
lean_dec(v_term_x3f_1460_);
lean_dec(v_mvarId_1458_);
v_a_1547_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1549_ = v___x_1503_;
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1503_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1552_; 
if (v_isShared_1550_ == 0)
{
v___x_1552_ = v___x_1549_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_a_1547_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
else
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1562_; 
lean_dec(v_i_1464_);
lean_dec_ref(v_eType_1462_);
lean_dec_ref(v_targetType_1461_);
lean_dec(v_term_x3f_1460_);
lean_dec(v_mvarId_1458_);
v_a_1555_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1557_ = v___x_1499_;
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v___x_1499_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1560_; 
if (v_isShared_1558_ == 0)
{
v___x_1560_ = v___x_1557_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1555_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
v___jp_1470_:
{
uint8_t v_approx_1476_; lean_object* v___x_1477_; 
v_approx_1476_ = lean_ctor_get_uint8(v_cfg_1459_, 3);
v___x_1477_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_1458_, v_eType_1462_, v_conclusionType_x3f_1471_, v_targetType_1461_, v_term_x3f_1460_, v_approx_1476_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
return v___x_1477_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go___boxed(lean_object* v_mvarId_1563_, lean_object* v_cfg_1564_, lean_object* v_term_x3f_1565_, lean_object* v_targetType_1566_, lean_object* v_eType_1567_, lean_object* v_rangeNumArgs_1568_, lean_object* v_i_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(v_mvarId_1563_, v_cfg_1564_, v_term_x3f_1565_, v_targetType_1566_, v_eType_1567_, v_rangeNumArgs_1568_, v_i_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_);
lean_dec(v_a_1573_);
lean_dec_ref(v_a_1572_);
lean_dec(v_a_1571_);
lean_dec_ref(v_a_1570_);
lean_dec_ref(v_rangeNumArgs_1568_);
lean_dec_ref(v_cfg_1564_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go_match__1_splitter___redArg(lean_object* v_x_1576_, lean_object* v_h__1_1577_){
_start:
{
lean_object* v_snd_1578_; lean_object* v_fst_1579_; lean_object* v_fst_1580_; lean_object* v_snd_1581_; lean_object* v___x_1582_; 
v_snd_1578_ = lean_ctor_get(v_x_1576_, 1);
lean_inc(v_snd_1578_);
v_fst_1579_ = lean_ctor_get(v_x_1576_, 0);
lean_inc(v_fst_1579_);
lean_dec_ref(v_x_1576_);
v_fst_1580_ = lean_ctor_get(v_snd_1578_, 0);
lean_inc(v_fst_1580_);
v_snd_1581_ = lean_ctor_get(v_snd_1578_, 1);
lean_inc(v_snd_1581_);
lean_dec(v_snd_1578_);
v___x_1582_ = lean_apply_3(v_h__1_1577_, v_fst_1579_, v_fst_1580_, v_snd_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go_match__1_splitter(lean_object* v_motive_1583_, lean_object* v_x_1584_, lean_object* v_h__1_1585_){
_start:
{
lean_object* v_snd_1586_; lean_object* v_fst_1587_; lean_object* v_fst_1588_; lean_object* v_snd_1589_; lean_object* v___x_1590_; 
v_snd_1586_ = lean_ctor_get(v_x_1584_, 1);
lean_inc(v_snd_1586_);
v_fst_1587_ = lean_ctor_get(v_x_1584_, 0);
lean_inc(v_fst_1587_);
lean_dec_ref(v_x_1584_);
v_fst_1588_ = lean_ctor_get(v_snd_1586_, 0);
lean_inc(v_fst_1588_);
v_snd_1589_ = lean_ctor_get(v_snd_1586_, 1);
lean_inc(v_snd_1589_);
lean_dec(v_snd_1586_);
v___x_1590_ = lean_apply_3(v_h__1_1585_, v_fst_1587_, v_fst_1588_, v_snd_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(lean_object* v_e_1591_, lean_object* v___y_1592_){
_start:
{
uint8_t v___x_1594_; 
v___x_1594_ = l_Lean_Expr_hasMVar(v_e_1591_);
if (v___x_1594_ == 0)
{
lean_object* v___x_1595_; 
v___x_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1595_, 0, v_e_1591_);
return v___x_1595_;
}
else
{
lean_object* v___x_1596_; lean_object* v_mctx_1597_; lean_object* v___x_1598_; lean_object* v_fst_1599_; lean_object* v_snd_1600_; lean_object* v___x_1601_; lean_object* v_cache_1602_; lean_object* v_zetaDeltaFVarIds_1603_; lean_object* v_postponed_1604_; lean_object* v_diag_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1614_; 
v___x_1596_ = lean_st_ref_get(v___y_1592_);
v_mctx_1597_ = lean_ctor_get(v___x_1596_, 0);
lean_inc_ref(v_mctx_1597_);
lean_dec(v___x_1596_);
v___x_1598_ = l_Lean_instantiateMVarsCore(v_mctx_1597_, v_e_1591_);
v_fst_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_fst_1599_);
v_snd_1600_ = lean_ctor_get(v___x_1598_, 1);
lean_inc(v_snd_1600_);
lean_dec_ref(v___x_1598_);
v___x_1601_ = lean_st_ref_take(v___y_1592_);
v_cache_1602_ = lean_ctor_get(v___x_1601_, 1);
v_zetaDeltaFVarIds_1603_ = lean_ctor_get(v___x_1601_, 2);
v_postponed_1604_ = lean_ctor_get(v___x_1601_, 3);
v_diag_1605_ = lean_ctor_get(v___x_1601_, 4);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1614_ == 0)
{
lean_object* v_unused_1615_; 
v_unused_1615_ = lean_ctor_get(v___x_1601_, 0);
lean_dec(v_unused_1615_);
v___x_1607_ = v___x_1601_;
v_isShared_1608_ = v_isSharedCheck_1614_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_diag_1605_);
lean_inc(v_postponed_1604_);
lean_inc(v_zetaDeltaFVarIds_1603_);
lean_inc(v_cache_1602_);
lean_dec(v___x_1601_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1614_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
lean_ctor_set(v___x_1607_, 0, v_snd_1600_);
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_snd_1600_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v_cache_1602_);
lean_ctor_set(v_reuseFailAlloc_1613_, 2, v_zetaDeltaFVarIds_1603_);
lean_ctor_set(v_reuseFailAlloc_1613_, 3, v_postponed_1604_);
lean_ctor_set(v_reuseFailAlloc_1613_, 4, v_diag_1605_);
v___x_1610_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1611_ = lean_st_ref_put(v___y_1592_, v___x_1610_);
v___x_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1612_, 0, v_fst_1599_);
return v___x_1612_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg___boxed(lean_object* v_e_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_1616_, v___y_1617_);
lean_dec(v___y_1617_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0(lean_object* v_e_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_1620_, v___y_1622_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___boxed(lean_object* v_e_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0(v_e_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(lean_object* v_mvarId_1634_, lean_object* v_x_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1634_, v_x_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1649_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1644_ = v___x_1641_;
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1641_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1647_; 
if (v_isShared_1645_ == 0)
{
v___x_1647_ = v___x_1644_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_a_1642_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
else
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1657_; 
v_a_1650_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1652_ = v___x_1641_;
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1641_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1650_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg___boxed(lean_object* v_mvarId_1658_, lean_object* v_x_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_1658_, v_x_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6(lean_object* v_00_u03b1_1666_, lean_object* v_mvarId_1667_, lean_object* v_x_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_1667_, v_x_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___boxed(lean_object* v_00_u03b1_1675_, lean_object* v_mvarId_1676_, lean_object* v_x_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6(v_00_u03b1_1675_, v_mvarId_1676_, v_x_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(lean_object* v_as_1684_, size_t v_i_1685_, size_t v_stop_1686_, lean_object* v_b_1687_, lean_object* v___y_1688_){
_start:
{
lean_object* v_a_1691_; uint8_t v___x_1695_; 
v___x_1695_ = lean_usize_dec_eq(v_i_1685_, v_stop_1686_);
if (v___x_1695_ == 0)
{
lean_object* v___x_1696_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1696_ = lean_array_uget_borrowed(v_as_1684_, v_i_1685_);
v___x_1699_ = l_Lean_Expr_mvarId_x21(v___x_1696_);
v___x_1700_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_1699_, v___y_1688_);
lean_dec(v___x_1699_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_object* v_a_1701_; uint8_t v___x_1702_; 
v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
lean_inc(v_a_1701_);
lean_dec_ref_known(v___x_1700_, 1);
v___x_1702_ = lean_unbox(v_a_1701_);
lean_dec(v_a_1701_);
if (v___x_1702_ == 0)
{
goto v___jp_1697_;
}
else
{
v_a_1691_ = v_b_1687_;
goto v___jp_1690_;
}
}
else
{
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_object* v_a_1703_; uint8_t v___x_1704_; 
v_a_1703_ = lean_ctor_get(v___x_1700_, 0);
lean_inc(v_a_1703_);
lean_dec_ref_known(v___x_1700_, 1);
v___x_1704_ = lean_unbox(v_a_1703_);
lean_dec(v_a_1703_);
if (v___x_1704_ == 0)
{
v_a_1691_ = v_b_1687_;
goto v___jp_1690_;
}
else
{
goto v___jp_1697_;
}
}
else
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1712_; 
lean_dec_ref(v_b_1687_);
v_a_1705_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1707_ = v___x_1700_;
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1700_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1710_; 
if (v_isShared_1708_ == 0)
{
v___x_1710_ = v___x_1707_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1705_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
}
v___jp_1697_:
{
lean_object* v___x_1698_; 
lean_inc(v___x_1696_);
v___x_1698_ = lean_array_push(v_b_1687_, v___x_1696_);
v_a_1691_ = v___x_1698_;
goto v___jp_1690_;
}
}
else
{
lean_object* v___x_1713_; 
v___x_1713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1713_, 0, v_b_1687_);
return v___x_1713_;
}
v___jp_1690_:
{
size_t v___x_1692_; size_t v___x_1693_; 
v___x_1692_ = ((size_t)1ULL);
v___x_1693_ = lean_usize_add(v_i_1685_, v___x_1692_);
v_i_1685_ = v___x_1693_;
v_b_1687_ = v_a_1691_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg___boxed(lean_object* v_as_1714_, lean_object* v_i_1715_, lean_object* v_stop_1716_, lean_object* v_b_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
size_t v_i_boxed_1720_; size_t v_stop_boxed_1721_; lean_object* v_res_1722_; 
v_i_boxed_1720_ = lean_unbox_usize(v_i_1715_);
lean_dec(v_i_1715_);
v_stop_boxed_1721_ = lean_unbox_usize(v_stop_1716_);
lean_dec(v_stop_1716_);
v_res_1722_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_as_1714_, v_i_boxed_1720_, v_stop_boxed_1721_, v_b_1717_, v___y_1718_);
lean_dec(v___y_1718_);
lean_dec_ref(v_as_1714_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_apply_spec__3(lean_object* v_as_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
if (lean_obj_tag(v_as_1723_) == 0)
{
lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1729_ = lean_box(0);
v___x_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1729_);
return v___x_1730_;
}
else
{
lean_object* v_head_1731_; lean_object* v_tail_1732_; lean_object* v___x_1733_; 
v_head_1731_ = lean_ctor_get(v_as_1723_, 0);
lean_inc(v_head_1731_);
v_tail_1732_ = lean_ctor_get(v_as_1723_, 1);
lean_inc(v_tail_1732_);
lean_dec_ref_known(v_as_1723_, 2);
v___x_1733_ = l_Lean_MVarId_headBetaType(v_head_1731_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_dec_ref_known(v___x_1733_, 1);
v_as_1723_ = v_tail_1732_;
goto _start;
}
else
{
lean_dec(v_tail_1732_);
return v___x_1733_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_apply_spec__3___boxed(lean_object* v_as_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_List_forM___at___00Lean_MVarId_apply_spec__3(v_as_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(lean_object* v_x_1742_, lean_object* v_x_1743_, lean_object* v_x_1744_, lean_object* v_x_1745_){
_start:
{
lean_object* v_ks_1746_; lean_object* v_vs_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1771_; 
v_ks_1746_ = lean_ctor_get(v_x_1742_, 0);
v_vs_1747_ = lean_ctor_get(v_x_1742_, 1);
v_isSharedCheck_1771_ = !lean_is_exclusive(v_x_1742_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1749_ = v_x_1742_;
v_isShared_1750_ = v_isSharedCheck_1771_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_vs_1747_);
lean_inc(v_ks_1746_);
lean_dec(v_x_1742_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1771_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1751_; uint8_t v___x_1752_; 
v___x_1751_ = lean_array_get_size(v_ks_1746_);
v___x_1752_ = lean_nat_dec_lt(v_x_1743_, v___x_1751_);
if (v___x_1752_ == 0)
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1756_; 
lean_dec(v_x_1743_);
v___x_1753_ = lean_array_push(v_ks_1746_, v_x_1744_);
v___x_1754_ = lean_array_push(v_vs_1747_, v_x_1745_);
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 1, v___x_1754_);
lean_ctor_set(v___x_1749_, 0, v___x_1753_);
v___x_1756_ = v___x_1749_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1753_);
lean_ctor_set(v_reuseFailAlloc_1757_, 1, v___x_1754_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
else
{
lean_object* v_k_x27_1758_; uint8_t v___x_1759_; 
v_k_x27_1758_ = lean_array_fget_borrowed(v_ks_1746_, v_x_1743_);
v___x_1759_ = l_Lean_instBEqMVarId_beq(v_x_1744_, v_k_x27_1758_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1761_; 
if (v_isShared_1750_ == 0)
{
v___x_1761_ = v___x_1749_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_ks_1746_);
lean_ctor_set(v_reuseFailAlloc_1765_, 1, v_vs_1747_);
v___x_1761_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1762_ = lean_unsigned_to_nat(1u);
v___x_1763_ = lean_nat_add(v_x_1743_, v___x_1762_);
lean_dec(v_x_1743_);
v_x_1742_ = v___x_1761_;
v_x_1743_ = v___x_1763_;
goto _start;
}
}
else
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1769_; 
v___x_1766_ = lean_array_fset(v_ks_1746_, v_x_1743_, v_x_1744_);
v___x_1767_ = lean_array_fset(v_vs_1747_, v_x_1743_, v_x_1745_);
lean_dec(v_x_1743_);
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 1, v___x_1767_);
lean_ctor_set(v___x_1749_, 0, v___x_1766_);
v___x_1769_ = v___x_1749_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___x_1766_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v___x_1767_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(lean_object* v_n_1772_, lean_object* v_k_1773_, lean_object* v_v_1774_){
_start:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1775_ = lean_unsigned_to_nat(0u);
v___x_1776_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(v_n_1772_, v___x_1775_, v_k_1773_, v_v_1774_);
return v___x_1776_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(lean_object* v_x_1778_, size_t v_x_1779_, size_t v_x_1780_, lean_object* v_x_1781_, lean_object* v_x_1782_){
_start:
{
if (lean_obj_tag(v_x_1778_) == 0)
{
lean_object* v_es_1783_; size_t v___x_1784_; size_t v___x_1785_; lean_object* v_j_1786_; lean_object* v___x_1787_; uint8_t v___x_1788_; 
v_es_1783_ = lean_ctor_get(v_x_1778_, 0);
v___x_1784_ = ((size_t)31ULL);
v___x_1785_ = lean_usize_land(v_x_1779_, v___x_1784_);
v_j_1786_ = lean_usize_to_nat(v___x_1785_);
v___x_1787_ = lean_array_get_size(v_es_1783_);
v___x_1788_ = lean_nat_dec_lt(v_j_1786_, v___x_1787_);
if (v___x_1788_ == 0)
{
lean_dec(v_j_1786_);
lean_dec(v_x_1782_);
lean_dec(v_x_1781_);
return v_x_1778_;
}
else
{
lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1827_; 
lean_inc_ref(v_es_1783_);
v_isSharedCheck_1827_ = !lean_is_exclusive(v_x_1778_);
if (v_isSharedCheck_1827_ == 0)
{
lean_object* v_unused_1828_; 
v_unused_1828_ = lean_ctor_get(v_x_1778_, 0);
lean_dec(v_unused_1828_);
v___x_1790_ = v_x_1778_;
v_isShared_1791_ = v_isSharedCheck_1827_;
goto v_resetjp_1789_;
}
else
{
lean_dec(v_x_1778_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1827_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v_v_1792_; lean_object* v___x_1793_; lean_object* v_xs_x27_1794_; lean_object* v___y_1796_; 
v_v_1792_ = lean_array_fget(v_es_1783_, v_j_1786_);
v___x_1793_ = lean_box(0);
v_xs_x27_1794_ = lean_array_fset(v_es_1783_, v_j_1786_, v___x_1793_);
switch(lean_obj_tag(v_v_1792_))
{
case 0:
{
lean_object* v_key_1801_; lean_object* v_val_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1812_; 
v_key_1801_ = lean_ctor_get(v_v_1792_, 0);
v_val_1802_ = lean_ctor_get(v_v_1792_, 1);
v_isSharedCheck_1812_ = !lean_is_exclusive(v_v_1792_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1804_ = v_v_1792_;
v_isShared_1805_ = v_isSharedCheck_1812_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_val_1802_);
lean_inc(v_key_1801_);
lean_dec(v_v_1792_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1812_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
uint8_t v___x_1806_; 
v___x_1806_ = l_Lean_instBEqMVarId_beq(v_x_1781_, v_key_1801_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
lean_del_object(v___x_1804_);
v___x_1807_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1801_, v_val_1802_, v_x_1781_, v_x_1782_);
v___x_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1807_);
v___y_1796_ = v___x_1808_;
goto v___jp_1795_;
}
else
{
lean_object* v___x_1810_; 
lean_dec(v_val_1802_);
lean_dec(v_key_1801_);
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 1, v_x_1782_);
lean_ctor_set(v___x_1804_, 0, v_x_1781_);
v___x_1810_ = v___x_1804_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_x_1781_);
lean_ctor_set(v_reuseFailAlloc_1811_, 1, v_x_1782_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
v___y_1796_ = v___x_1810_;
goto v___jp_1795_;
}
}
}
}
case 1:
{
lean_object* v_node_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1825_; 
v_node_1813_ = lean_ctor_get(v_v_1792_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v_v_1792_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1815_ = v_v_1792_;
v_isShared_1816_ = v_isSharedCheck_1825_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_node_1813_);
lean_dec(v_v_1792_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1825_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
size_t v___x_1817_; size_t v___x_1818_; size_t v___x_1819_; size_t v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1823_; 
v___x_1817_ = ((size_t)5ULL);
v___x_1818_ = lean_usize_shift_right(v_x_1779_, v___x_1817_);
v___x_1819_ = ((size_t)1ULL);
v___x_1820_ = lean_usize_add(v_x_1780_, v___x_1819_);
v___x_1821_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_node_1813_, v___x_1818_, v___x_1820_, v_x_1781_, v_x_1782_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 0, v___x_1821_);
v___x_1823_ = v___x_1815_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v___x_1821_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
v___y_1796_ = v___x_1823_;
goto v___jp_1795_;
}
}
}
default: 
{
lean_object* v___x_1826_; 
v___x_1826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1826_, 0, v_x_1781_);
lean_ctor_set(v___x_1826_, 1, v_x_1782_);
v___y_1796_ = v___x_1826_;
goto v___jp_1795_;
}
}
v___jp_1795_:
{
lean_object* v___x_1797_; lean_object* v___x_1799_; 
v___x_1797_ = lean_array_fset(v_xs_x27_1794_, v_j_1786_, v___y_1796_);
lean_dec(v_j_1786_);
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 0, v___x_1797_);
v___x_1799_ = v___x_1790_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v___x_1797_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
}
}
else
{
lean_object* v_ks_1829_; lean_object* v_vs_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1848_; 
v_ks_1829_ = lean_ctor_get(v_x_1778_, 0);
v_vs_1830_ = lean_ctor_get(v_x_1778_, 1);
v_isSharedCheck_1848_ = !lean_is_exclusive(v_x_1778_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1832_ = v_x_1778_;
v_isShared_1833_ = v_isSharedCheck_1848_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_vs_1830_);
lean_inc(v_ks_1829_);
lean_dec(v_x_1778_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1848_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1835_; 
if (v_isShared_1833_ == 0)
{
v___x_1835_ = v___x_1832_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_ks_1829_);
lean_ctor_set(v_reuseFailAlloc_1847_, 1, v_vs_1830_);
v___x_1835_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
lean_object* v_newNode_1836_; size_t v___x_1837_; uint8_t v___x_1838_; 
v_newNode_1836_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(v___x_1835_, v_x_1781_, v_x_1782_);
v___x_1837_ = ((size_t)7ULL);
v___x_1838_ = lean_usize_dec_le(v___x_1837_, v_x_1780_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; lean_object* v___x_1840_; uint8_t v___x_1841_; 
v___x_1839_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1836_);
v___x_1840_ = lean_unsigned_to_nat(4u);
v___x_1841_ = lean_nat_dec_lt(v___x_1839_, v___x_1840_);
lean_dec(v___x_1839_);
if (v___x_1841_ == 0)
{
lean_object* v_ks_1842_; lean_object* v_vs_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v_ks_1842_ = lean_ctor_get(v_newNode_1836_, 0);
lean_inc_ref(v_ks_1842_);
v_vs_1843_ = lean_ctor_get(v_newNode_1836_, 1);
lean_inc_ref(v_vs_1843_);
lean_dec_ref(v_newNode_1836_);
v___x_1844_ = lean_unsigned_to_nat(0u);
v___x_1845_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_1846_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_x_1780_, v_ks_1842_, v_vs_1843_, v___x_1844_, v___x_1845_);
lean_dec_ref(v_vs_1843_);
lean_dec_ref(v_ks_1842_);
return v___x_1846_;
}
else
{
return v_newNode_1836_;
}
}
else
{
return v_newNode_1836_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(size_t v_depth_1849_, lean_object* v_keys_1850_, lean_object* v_vals_1851_, lean_object* v_i_1852_, lean_object* v_entries_1853_){
_start:
{
lean_object* v___x_1854_; uint8_t v___x_1855_; 
v___x_1854_ = lean_array_get_size(v_keys_1850_);
v___x_1855_ = lean_nat_dec_lt(v_i_1852_, v___x_1854_);
if (v___x_1855_ == 0)
{
lean_dec(v_i_1852_);
return v_entries_1853_;
}
else
{
lean_object* v_k_1856_; lean_object* v_v_1857_; uint64_t v___x_1858_; size_t v_h_1859_; size_t v___x_1860_; lean_object* v___x_1861_; size_t v___x_1862_; size_t v___x_1863_; size_t v___x_1864_; size_t v_h_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
v_k_1856_ = lean_array_fget_borrowed(v_keys_1850_, v_i_1852_);
v_v_1857_ = lean_array_fget_borrowed(v_vals_1851_, v_i_1852_);
v___x_1858_ = l_Lean_instHashableMVarId_hash(v_k_1856_);
v_h_1859_ = lean_uint64_to_usize(v___x_1858_);
v___x_1860_ = ((size_t)5ULL);
v___x_1861_ = lean_unsigned_to_nat(1u);
v___x_1862_ = ((size_t)1ULL);
v___x_1863_ = lean_usize_sub(v_depth_1849_, v___x_1862_);
v___x_1864_ = lean_usize_mul(v___x_1860_, v___x_1863_);
v_h_1865_ = lean_usize_shift_right(v_h_1859_, v___x_1864_);
v___x_1866_ = lean_nat_add(v_i_1852_, v___x_1861_);
lean_dec(v_i_1852_);
lean_inc(v_v_1857_);
lean_inc(v_k_1856_);
v___x_1867_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_entries_1853_, v_h_1865_, v_depth_1849_, v_k_1856_, v_v_1857_);
v_i_1852_ = v___x_1866_;
v_entries_1853_ = v___x_1867_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg___boxed(lean_object* v_depth_1869_, lean_object* v_keys_1870_, lean_object* v_vals_1871_, lean_object* v_i_1872_, lean_object* v_entries_1873_){
_start:
{
size_t v_depth_boxed_1874_; lean_object* v_res_1875_; 
v_depth_boxed_1874_ = lean_unbox_usize(v_depth_1869_);
lean_dec(v_depth_1869_);
v_res_1875_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_depth_boxed_1874_, v_keys_1870_, v_vals_1871_, v_i_1872_, v_entries_1873_);
lean_dec_ref(v_vals_1871_);
lean_dec_ref(v_keys_1870_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_1876_, lean_object* v_x_1877_, lean_object* v_x_1878_, lean_object* v_x_1879_, lean_object* v_x_1880_){
_start:
{
size_t v_x_7090__boxed_1881_; size_t v_x_7091__boxed_1882_; lean_object* v_res_1883_; 
v_x_7090__boxed_1881_ = lean_unbox_usize(v_x_1877_);
lean_dec(v_x_1877_);
v_x_7091__boxed_1882_ = lean_unbox_usize(v_x_1878_);
lean_dec(v_x_1878_);
v_res_1883_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_1876_, v_x_7090__boxed_1881_, v_x_7091__boxed_1882_, v_x_1879_, v_x_1880_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(lean_object* v_x_1884_, lean_object* v_x_1885_, lean_object* v_x_1886_){
_start:
{
uint64_t v___x_1887_; size_t v___x_1888_; size_t v___x_1889_; lean_object* v___x_1890_; 
v___x_1887_ = l_Lean_instHashableMVarId_hash(v_x_1885_);
v___x_1888_ = lean_uint64_to_usize(v___x_1887_);
v___x_1889_ = ((size_t)1ULL);
v___x_1890_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_1884_, v___x_1888_, v___x_1889_, v_x_1885_, v_x_1886_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(lean_object* v_mvarId_1891_, lean_object* v_val_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v___x_1895_; lean_object* v_mctx_1896_; lean_object* v_cache_1897_; lean_object* v_zetaDeltaFVarIds_1898_; lean_object* v_postponed_1899_; lean_object* v_diag_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1930_; 
v___x_1895_ = lean_st_ref_take(v___y_1893_);
v_mctx_1896_ = lean_ctor_get(v___x_1895_, 0);
v_cache_1897_ = lean_ctor_get(v___x_1895_, 1);
v_zetaDeltaFVarIds_1898_ = lean_ctor_get(v___x_1895_, 2);
v_postponed_1899_ = lean_ctor_get(v___x_1895_, 3);
v_diag_1900_ = lean_ctor_get(v___x_1895_, 4);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1902_ = v___x_1895_;
v_isShared_1903_ = v_isSharedCheck_1930_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_diag_1900_);
lean_inc(v_postponed_1899_);
lean_inc(v_zetaDeltaFVarIds_1898_);
lean_inc(v_cache_1897_);
lean_inc(v_mctx_1896_);
lean_dec(v___x_1895_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1930_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v_depth_1904_; lean_object* v_levelAssignDepth_1905_; lean_object* v_lmvarCounter_1906_; lean_object* v_mvarCounter_1907_; lean_object* v_lDecls_1908_; lean_object* v_decls_1909_; lean_object* v_userNames_1910_; lean_object* v_lAssignment_1911_; lean_object* v_eAssignment_1912_; lean_object* v_dAssignment_1913_; lean_object* v_instanceTypedMVars_1914_; lean_object* v_synthNormMemo_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1929_; 
v_depth_1904_ = lean_ctor_get(v_mctx_1896_, 0);
v_levelAssignDepth_1905_ = lean_ctor_get(v_mctx_1896_, 1);
v_lmvarCounter_1906_ = lean_ctor_get(v_mctx_1896_, 2);
v_mvarCounter_1907_ = lean_ctor_get(v_mctx_1896_, 3);
v_lDecls_1908_ = lean_ctor_get(v_mctx_1896_, 4);
v_decls_1909_ = lean_ctor_get(v_mctx_1896_, 5);
v_userNames_1910_ = lean_ctor_get(v_mctx_1896_, 6);
v_lAssignment_1911_ = lean_ctor_get(v_mctx_1896_, 7);
v_eAssignment_1912_ = lean_ctor_get(v_mctx_1896_, 8);
v_dAssignment_1913_ = lean_ctor_get(v_mctx_1896_, 9);
v_instanceTypedMVars_1914_ = lean_ctor_get(v_mctx_1896_, 10);
v_synthNormMemo_1915_ = lean_ctor_get(v_mctx_1896_, 11);
v_isSharedCheck_1929_ = !lean_is_exclusive(v_mctx_1896_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1917_ = v_mctx_1896_;
v_isShared_1918_ = v_isSharedCheck_1929_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_synthNormMemo_1915_);
lean_inc(v_instanceTypedMVars_1914_);
lean_inc(v_dAssignment_1913_);
lean_inc(v_eAssignment_1912_);
lean_inc(v_lAssignment_1911_);
lean_inc(v_userNames_1910_);
lean_inc(v_decls_1909_);
lean_inc(v_lDecls_1908_);
lean_inc(v_mvarCounter_1907_);
lean_inc(v_lmvarCounter_1906_);
lean_inc(v_levelAssignDepth_1905_);
lean_inc(v_depth_1904_);
lean_dec(v_mctx_1896_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1929_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1922_; 
v___x_1919_ = lean_box(0);
v___x_1920_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(v_eAssignment_1912_, v_mvarId_1891_, v_val_1892_);
if (v_isShared_1918_ == 0)
{
lean_ctor_set(v___x_1917_, 8, v___x_1920_);
v___x_1922_ = v___x_1917_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_depth_1904_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v_levelAssignDepth_1905_);
lean_ctor_set(v_reuseFailAlloc_1928_, 2, v_lmvarCounter_1906_);
lean_ctor_set(v_reuseFailAlloc_1928_, 3, v_mvarCounter_1907_);
lean_ctor_set(v_reuseFailAlloc_1928_, 4, v_lDecls_1908_);
lean_ctor_set(v_reuseFailAlloc_1928_, 5, v_decls_1909_);
lean_ctor_set(v_reuseFailAlloc_1928_, 6, v_userNames_1910_);
lean_ctor_set(v_reuseFailAlloc_1928_, 7, v_lAssignment_1911_);
lean_ctor_set(v_reuseFailAlloc_1928_, 8, v___x_1920_);
lean_ctor_set(v_reuseFailAlloc_1928_, 9, v_dAssignment_1913_);
lean_ctor_set(v_reuseFailAlloc_1928_, 10, v_instanceTypedMVars_1914_);
lean_ctor_set(v_reuseFailAlloc_1928_, 11, v_synthNormMemo_1915_);
v___x_1922_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
lean_object* v___x_1924_; 
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v___x_1922_);
v___x_1924_ = v___x_1902_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1922_);
lean_ctor_set(v_reuseFailAlloc_1927_, 1, v_cache_1897_);
lean_ctor_set(v_reuseFailAlloc_1927_, 2, v_zetaDeltaFVarIds_1898_);
lean_ctor_set(v_reuseFailAlloc_1927_, 3, v_postponed_1899_);
lean_ctor_set(v_reuseFailAlloc_1927_, 4, v_diag_1900_);
v___x_1924_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1925_ = lean_st_ref_put(v___y_1893_, v___x_1924_);
v___x_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1919_);
return v___x_1926_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg___boxed(lean_object* v_mvarId_1931_, lean_object* v_val_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_1931_, v_val_1932_, v___y_1933_);
lean_dec(v___y_1933_);
return v_res_1935_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_MVarId_apply_spec__2(lean_object* v_a_1936_, lean_object* v_x_1937_){
_start:
{
if (lean_obj_tag(v_x_1937_) == 0)
{
uint8_t v___x_1938_; 
v___x_1938_ = 0;
return v___x_1938_;
}
else
{
lean_object* v_head_1939_; lean_object* v_tail_1940_; uint8_t v___x_1941_; 
v_head_1939_ = lean_ctor_get(v_x_1937_, 0);
v_tail_1940_ = lean_ctor_get(v_x_1937_, 1);
v___x_1941_ = l_Lean_instBEqMVarId_beq(v_a_1936_, v_head_1939_);
if (v___x_1941_ == 0)
{
v_x_1937_ = v_tail_1940_;
goto _start;
}
else
{
return v___x_1941_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_MVarId_apply_spec__2___boxed(lean_object* v_a_1943_, lean_object* v_x_1944_){
_start:
{
uint8_t v_res_1945_; lean_object* v_r_1946_; 
v_res_1945_ = l_List_elem___at___00Lean_MVarId_apply_spec__2(v_a_1943_, v_x_1944_);
lean_dec(v_x_1944_);
lean_dec(v_a_1943_);
v_r_1946_ = lean_box(v_res_1945_);
return v_r_1946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(lean_object* v_a_1947_, lean_object* v_as_1948_, size_t v_i_1949_, size_t v_stop_1950_, lean_object* v_b_1951_){
_start:
{
lean_object* v___y_1953_; uint8_t v___x_1957_; 
v___x_1957_ = lean_usize_dec_eq(v_i_1949_, v_stop_1950_);
if (v___x_1957_ == 0)
{
lean_object* v___x_1958_; uint8_t v___x_1959_; 
v___x_1958_ = lean_array_uget_borrowed(v_as_1948_, v_i_1949_);
v___x_1959_ = l_List_elem___at___00Lean_MVarId_apply_spec__2(v___x_1958_, v_a_1947_);
if (v___x_1959_ == 0)
{
lean_object* v___x_1960_; 
lean_inc(v___x_1958_);
v___x_1960_ = lean_array_push(v_b_1951_, v___x_1958_);
v___y_1953_ = v___x_1960_;
goto v___jp_1952_;
}
else
{
v___y_1953_ = v_b_1951_;
goto v___jp_1952_;
}
}
else
{
return v_b_1951_;
}
v___jp_1952_:
{
size_t v___x_1954_; size_t v___x_1955_; 
v___x_1954_ = ((size_t)1ULL);
v___x_1955_ = lean_usize_add(v_i_1949_, v___x_1954_);
v_i_1949_ = v___x_1955_;
v_b_1951_ = v___y_1953_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4___boxed(lean_object* v_a_1961_, lean_object* v_as_1962_, lean_object* v_i_1963_, lean_object* v_stop_1964_, lean_object* v_b_1965_){
_start:
{
size_t v_i_boxed_1966_; size_t v_stop_boxed_1967_; lean_object* v_res_1968_; 
v_i_boxed_1966_ = lean_unbox_usize(v_i_1963_);
lean_dec(v_i_1963_);
v_stop_boxed_1967_ = lean_unbox_usize(v_stop_1964_);
lean_dec(v_stop_1964_);
v_res_1968_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_1961_, v_as_1962_, v_i_boxed_1966_, v_stop_boxed_1967_, v_b_1965_);
lean_dec_ref(v_as_1962_);
lean_dec(v_a_1961_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lam__0(lean_object* v_mvarId_1969_, lean_object* v___x_1970_, lean_object* v_e_1971_, lean_object* v_cfg_1972_, lean_object* v_term_x3f_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; uint8_t v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v_a_2014_; uint8_t v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v___y_2050_; lean_object* v___y_2051_; lean_object* v___y_2052_; lean_object* v___y_2053_; lean_object* v___y_2054_; lean_object* v___y_2055_; lean_object* v___x_2065_; 
lean_inc(v___x_1970_);
lean_inc(v_mvarId_1969_);
v___x_2065_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1969_, v___x_1970_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v___x_2066_; 
lean_dec_ref_known(v___x_2065_, 1);
lean_inc(v_mvarId_1969_);
v___x_2066_ = l_Lean_MVarId_getType(v_mvarId_1969_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2067_; lean_object* v___x_2068_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
lean_inc(v_a_2067_);
lean_dec_ref_known(v___x_2066_, 1);
lean_inc(v___y_1977_);
lean_inc_ref(v___y_1976_);
lean_inc(v___y_1975_);
lean_inc_ref(v___y_1974_);
lean_inc_ref(v_e_1971_);
v___x_2068_ = lean_infer_type(v_e_1971_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_object* v_a_2069_; lean_object* v_rangeNumArgs_2071_; lean_object* v_lower_2072_; lean_object* v___y_2073_; lean_object* v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v___x_2116_; 
v_a_2069_ = lean_ctor_get(v___x_2068_, 0);
lean_inc_n(v_a_2069_, 2);
lean_dec_ref_known(v___x_2068_, 1);
v___x_2116_ = l_Lean_Meta_getExpectedNumArgsAux(v_a_2069_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v_snd_2118_; uint8_t v___x_2119_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_a_2117_);
lean_dec_ref_known(v___x_2116_, 1);
v_snd_2118_ = lean_ctor_get(v_a_2117_, 1);
v___x_2119_ = lean_unbox(v_snd_2118_);
if (v___x_2119_ == 0)
{
lean_object* v_fst_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2140_; 
v_fst_2120_ = lean_ctor_get(v_a_2117_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v_a_2117_);
if (v_isSharedCheck_2140_ == 0)
{
lean_object* v_unused_2141_; 
v_unused_2141_ = lean_ctor_get(v_a_2117_, 1);
lean_dec(v_unused_2141_);
v___x_2122_ = v_a_2117_;
v_isShared_2123_ = v_isSharedCheck_2140_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_fst_2120_);
lean_dec(v_a_2117_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2140_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2124_; 
lean_inc(v_a_2067_);
v___x_2124_ = l_Lean_Meta_getExpectedNumArgs(v_a_2067_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2130_; 
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
lean_inc(v_a_2125_);
lean_dec_ref_known(v___x_2124_, 1);
v___x_2126_ = lean_nat_sub(v_fst_2120_, v_a_2125_);
lean_dec(v_a_2125_);
v___x_2127_ = lean_unsigned_to_nat(1u);
v___x_2128_ = lean_nat_add(v_fst_2120_, v___x_2127_);
lean_dec(v_fst_2120_);
lean_inc(v___x_2126_);
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 1, v___x_2128_);
lean_ctor_set(v___x_2122_, 0, v___x_2126_);
v___x_2130_ = v___x_2122_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v___x_2126_);
lean_ctor_set(v_reuseFailAlloc_2131_, 1, v___x_2128_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
v_rangeNumArgs_2071_ = v___x_2130_;
v_lower_2072_ = v___x_2126_;
v___y_2073_ = v___y_1974_;
v___y_2074_ = v___y_1975_;
v___y_2075_ = v___y_1976_;
v___y_2076_ = v___y_1977_;
goto v___jp_2070_;
}
}
else
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2139_; 
lean_del_object(v___x_2122_);
lean_dec(v_fst_2120_);
lean_dec(v_a_2069_);
lean_dec(v_a_2067_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v_term_x3f_1973_);
lean_dec_ref(v_e_1971_);
lean_dec(v___x_1970_);
lean_dec(v_mvarId_1969_);
v_a_2132_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2134_ = v___x_2124_;
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2124_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2137_; 
if (v_isShared_2135_ == 0)
{
v___x_2137_ = v___x_2134_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_a_2132_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
}
}
}
else
{
lean_object* v_fst_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2151_; 
v_fst_2142_ = lean_ctor_get(v_a_2117_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v_a_2117_);
if (v_isSharedCheck_2151_ == 0)
{
lean_object* v_unused_2152_; 
v_unused_2152_ = lean_ctor_get(v_a_2117_, 1);
lean_dec(v_unused_2152_);
v___x_2144_ = v_a_2117_;
v_isShared_2145_ = v_isSharedCheck_2151_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_fst_2142_);
lean_dec(v_a_2117_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2151_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2149_; 
v___x_2146_ = lean_unsigned_to_nat(1u);
v___x_2147_ = lean_nat_add(v_fst_2142_, v___x_2146_);
lean_inc(v_fst_2142_);
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 1, v___x_2147_);
v___x_2149_ = v___x_2144_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_fst_2142_);
lean_ctor_set(v_reuseFailAlloc_2150_, 1, v___x_2147_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
v_rangeNumArgs_2071_ = v___x_2149_;
v_lower_2072_ = v_fst_2142_;
v___y_2073_ = v___y_1974_;
v___y_2074_ = v___y_1975_;
v___y_2075_ = v___y_1976_;
v___y_2076_ = v___y_1977_;
goto v___jp_2070_;
}
}
}
}
else
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2160_; 
lean_dec(v_a_2069_);
lean_dec(v_a_2067_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v_term_x3f_1973_);
lean_dec_ref(v_e_1971_);
lean_dec(v___x_1970_);
lean_dec(v_mvarId_1969_);
v_a_2153_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2155_ = v___x_2116_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2116_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2153_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
v___jp_2070_:
{
lean_object* v___x_2077_; 
lean_inc(v_mvarId_1969_);
v___x_2077_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(v_mvarId_1969_, v_cfg_1972_, v_term_x3f_1973_, v_a_2067_, v_a_2069_, v_rangeNumArgs_2071_, v_lower_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
lean_dec_ref(v_rangeNumArgs_2071_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; lean_object* v_fst_2079_; lean_object* v_snd_2080_; uint8_t v_newGoals_2081_; uint8_t v_synthAssignedInstances_2082_; uint8_t v_allowSynthFailures_2083_; lean_object* v___x_2084_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_a_2078_);
lean_dec_ref_known(v___x_2077_, 1);
v_fst_2079_ = lean_ctor_get(v_a_2078_, 0);
lean_inc(v_fst_2079_);
v_snd_2080_ = lean_ctor_get(v_a_2078_, 1);
lean_inc_n(v_snd_2080_, 2);
lean_dec(v_a_2078_);
v_newGoals_2081_ = lean_ctor_get_uint8(v_cfg_1972_, 0);
v_synthAssignedInstances_2082_ = lean_ctor_get_uint8(v_cfg_1972_, 1);
v_allowSynthFailures_2083_ = lean_ctor_get_uint8(v_cfg_1972_, 2);
lean_inc(v_mvarId_1969_);
v___x_2084_ = l_Lean_Meta_synthAppInstances(v___x_1970_, v_mvarId_1969_, v_fst_2079_, v_snd_2080_, v_synthAssignedInstances_2082_, v_allowSynthFailures_2083_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v___x_2085_; lean_object* v_a_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; uint8_t v___x_2092_; 
lean_dec_ref_known(v___x_2084_, 1);
v___x_2085_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_1971_, v___y_2074_);
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
lean_inc_n(v_a_2086_, 2);
lean_dec_ref(v___x_2085_);
v___x_2087_ = l_Lean_mkAppN(v_a_2086_, v_fst_2079_);
lean_inc(v_mvarId_1969_);
v___x_2088_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_1969_, v___x_2087_, v___y_2074_);
lean_dec_ref(v___x_2088_);
v___x_2089_ = lean_unsigned_to_nat(0u);
v___x_2090_ = lean_array_get_size(v_fst_2079_);
v___x_2091_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0));
v___x_2092_ = lean_nat_dec_lt(v___x_2089_, v___x_2090_);
if (v___x_2092_ == 0)
{
lean_dec(v_fst_2079_);
v___y_2006_ = v_newGoals_2081_;
v___y_2007_ = v___y_2074_;
v___y_2008_ = v___y_2073_;
v___y_2009_ = v___x_2089_;
v___y_2010_ = v___y_2075_;
v___y_2011_ = v___y_2076_;
v___y_2012_ = v_a_2086_;
v___y_2013_ = v_snd_2080_;
v_a_2014_ = v___x_2091_;
goto v___jp_2005_;
}
else
{
uint8_t v___x_2093_; 
v___x_2093_ = lean_nat_dec_le(v___x_2090_, v___x_2090_);
if (v___x_2093_ == 0)
{
if (v___x_2092_ == 0)
{
lean_dec(v_fst_2079_);
v___y_2006_ = v_newGoals_2081_;
v___y_2007_ = v___y_2074_;
v___y_2008_ = v___y_2073_;
v___y_2009_ = v___x_2089_;
v___y_2010_ = v___y_2075_;
v___y_2011_ = v___y_2076_;
v___y_2012_ = v_a_2086_;
v___y_2013_ = v_snd_2080_;
v_a_2014_ = v___x_2091_;
goto v___jp_2005_;
}
else
{
size_t v___x_2094_; size_t v___x_2095_; lean_object* v___x_2096_; 
v___x_2094_ = ((size_t)0ULL);
v___x_2095_ = lean_usize_of_nat(v___x_2090_);
v___x_2096_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_fst_2079_, v___x_2094_, v___x_2095_, v___x_2091_, v___y_2074_);
lean_dec(v_fst_2079_);
v___y_2047_ = v_newGoals_2081_;
v___y_2048_ = v___y_2073_;
v___y_2049_ = v___y_2074_;
v___y_2050_ = v___x_2089_;
v___y_2051_ = v___y_2075_;
v___y_2052_ = v___y_2076_;
v___y_2053_ = v_snd_2080_;
v___y_2054_ = v_a_2086_;
v___y_2055_ = v___x_2096_;
goto v___jp_2046_;
}
}
else
{
size_t v___x_2097_; size_t v___x_2098_; lean_object* v___x_2099_; 
v___x_2097_ = ((size_t)0ULL);
v___x_2098_ = lean_usize_of_nat(v___x_2090_);
v___x_2099_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_fst_2079_, v___x_2097_, v___x_2098_, v___x_2091_, v___y_2074_);
lean_dec(v_fst_2079_);
v___y_2047_ = v_newGoals_2081_;
v___y_2048_ = v___y_2073_;
v___y_2049_ = v___y_2074_;
v___y_2050_ = v___x_2089_;
v___y_2051_ = v___y_2075_;
v___y_2052_ = v___y_2076_;
v___y_2053_ = v_snd_2080_;
v___y_2054_ = v_a_2086_;
v___y_2055_ = v___x_2099_;
goto v___jp_2046_;
}
}
}
else
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2107_; 
lean_dec(v_snd_2080_);
lean_dec(v_fst_2079_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
lean_dec_ref(v_e_1971_);
lean_dec(v_mvarId_1969_);
v_a_2100_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2102_ = v___x_2084_;
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2084_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2105_; 
if (v_isShared_2103_ == 0)
{
v___x_2105_ = v___x_2102_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_a_2100_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
}
else
{
lean_object* v_a_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2115_; 
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
lean_dec_ref(v_e_1971_);
lean_dec(v___x_1970_);
lean_dec(v_mvarId_1969_);
v_a_2108_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2110_ = v___x_2077_;
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_a_2108_);
lean_dec(v___x_2077_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2113_; 
if (v_isShared_2111_ == 0)
{
v___x_2113_ = v___x_2110_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_a_2108_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
}
}
else
{
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2168_; 
lean_dec(v_a_2067_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v_term_x3f_1973_);
lean_dec_ref(v_e_1971_);
lean_dec(v___x_1970_);
lean_dec(v_mvarId_1969_);
v_a_2161_ = lean_ctor_get(v___x_2068_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2163_ = v___x_2068_;
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v___x_2068_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2166_; 
if (v_isShared_2164_ == 0)
{
v___x_2166_ = v___x_2163_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_a_2161_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
}
else
{
lean_object* v_a_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2176_; 
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v_term_x3f_1973_);
lean_dec_ref(v_e_1971_);
lean_dec(v___x_1970_);
lean_dec(v_mvarId_1969_);
v_a_2169_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2171_ = v___x_2066_;
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_a_2169_);
lean_dec(v___x_2066_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2174_; 
if (v_isShared_2172_ == 0)
{
v___x_2174_ = v___x_2171_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_a_2169_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
}
else
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2184_; 
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v_term_x3f_1973_);
lean_dec_ref(v_e_1971_);
lean_dec(v___x_1970_);
lean_dec(v_mvarId_1969_);
v_a_2177_ = lean_ctor_get(v___x_2065_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2179_ = v___x_2065_;
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2065_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2182_; 
if (v_isShared_2180_ == 0)
{
v___x_2182_ = v___x_2179_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_a_2177_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
v___jp_1979_:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1986_ = lean_array_to_list(v___y_1985_);
v___x_1987_ = l_List_appendTR___redArg(v___y_1980_, v___x_1986_);
lean_inc(v___x_1987_);
v___x_1988_ = l_List_forM___at___00Lean_MVarId_apply_spec__3(v___x_1987_, v___y_1982_, v___y_1981_, v___y_1983_, v___y_1984_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1982_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_1995_ == 0)
{
lean_object* v_unused_1996_; 
v_unused_1996_ = lean_ctor_get(v___x_1988_, 0);
lean_dec(v_unused_1996_);
v___x_1990_ = v___x_1988_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_dec(v___x_1988_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 0, v___x_1987_);
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1987_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
else
{
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2004_; 
lean_dec(v___x_1987_);
v_a_1997_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1999_ = v___x_1988_;
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v___x_1988_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2002_; 
if (v_isShared_2000_ == 0)
{
v___x_2002_ = v___x_1999_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_a_1997_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
v___jp_2005_:
{
lean_object* v___x_2015_; 
v___x_2015_ = l_Lean_Meta_appendParentTag(v_mvarId_1969_, v_a_2014_, v___y_2013_, v___y_2008_, v___y_2007_, v___y_2010_, v___y_2011_);
lean_dec_ref(v___y_2013_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v___x_2016_; 
lean_dec_ref_known(v___x_2015_, 1);
v___x_2016_ = l_Lean_Meta_getMVarsNoDelayed(v___y_2012_, v___y_2008_, v___y_2007_, v___y_2010_, v___y_2011_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; lean_object* v___x_2018_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
lean_inc(v_a_2017_);
lean_dec_ref_known(v___x_2016_, 1);
v___x_2018_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(v_a_2014_, v___y_2006_, v___y_2008_, v___y_2007_, v___y_2010_, v___y_2011_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_a_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; uint8_t v___x_2022_; 
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_a_2019_);
lean_dec_ref_known(v___x_2018_, 1);
v___x_2020_ = lean_array_get_size(v_a_2017_);
v___x_2021_ = lean_mk_empty_array_with_capacity(v___y_2009_);
v___x_2022_ = lean_nat_dec_lt(v___y_2009_, v___x_2020_);
if (v___x_2022_ == 0)
{
lean_dec(v_a_2017_);
v___y_1980_ = v_a_2019_;
v___y_1981_ = v___y_2007_;
v___y_1982_ = v___y_2008_;
v___y_1983_ = v___y_2010_;
v___y_1984_ = v___y_2011_;
v___y_1985_ = v___x_2021_;
goto v___jp_1979_;
}
else
{
uint8_t v___x_2023_; 
v___x_2023_ = lean_nat_dec_le(v___x_2020_, v___x_2020_);
if (v___x_2023_ == 0)
{
if (v___x_2022_ == 0)
{
lean_dec(v_a_2017_);
v___y_1980_ = v_a_2019_;
v___y_1981_ = v___y_2007_;
v___y_1982_ = v___y_2008_;
v___y_1983_ = v___y_2010_;
v___y_1984_ = v___y_2011_;
v___y_1985_ = v___x_2021_;
goto v___jp_1979_;
}
else
{
size_t v___x_2024_; size_t v___x_2025_; lean_object* v___x_2026_; 
v___x_2024_ = ((size_t)0ULL);
v___x_2025_ = lean_usize_of_nat(v___x_2020_);
v___x_2026_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_2019_, v_a_2017_, v___x_2024_, v___x_2025_, v___x_2021_);
lean_dec(v_a_2017_);
v___y_1980_ = v_a_2019_;
v___y_1981_ = v___y_2007_;
v___y_1982_ = v___y_2008_;
v___y_1983_ = v___y_2010_;
v___y_1984_ = v___y_2011_;
v___y_1985_ = v___x_2026_;
goto v___jp_1979_;
}
}
else
{
size_t v___x_2027_; size_t v___x_2028_; lean_object* v___x_2029_; 
v___x_2027_ = ((size_t)0ULL);
v___x_2028_ = lean_usize_of_nat(v___x_2020_);
v___x_2029_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_2019_, v_a_2017_, v___x_2027_, v___x_2028_, v___x_2021_);
lean_dec(v_a_2017_);
v___y_1980_ = v_a_2019_;
v___y_1981_ = v___y_2007_;
v___y_1982_ = v___y_2008_;
v___y_1983_ = v___y_2010_;
v___y_1984_ = v___y_2011_;
v___y_1985_ = v___x_2029_;
goto v___jp_1979_;
}
}
}
else
{
lean_dec(v_a_2017_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec_ref(v___y_2008_);
lean_dec(v___y_2007_);
return v___x_2018_;
}
}
else
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2037_; 
lean_dec_ref(v_a_2014_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec_ref(v___y_2008_);
lean_dec(v___y_2007_);
v_a_2030_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2032_ = v___x_2016_;
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_2016_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2033_ == 0)
{
v___x_2035_ = v___x_2032_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_a_2030_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
}
else
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
lean_dec_ref(v_a_2014_);
lean_dec_ref(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec_ref(v___y_2008_);
lean_dec(v___y_2007_);
v_a_2038_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_2015_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2015_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
v___jp_2046_:
{
if (lean_obj_tag(v___y_2055_) == 0)
{
lean_object* v_a_2056_; 
v_a_2056_ = lean_ctor_get(v___y_2055_, 0);
lean_inc(v_a_2056_);
lean_dec_ref_known(v___y_2055_, 1);
v___y_2006_ = v___y_2047_;
v___y_2007_ = v___y_2049_;
v___y_2008_ = v___y_2048_;
v___y_2009_ = v___y_2050_;
v___y_2010_ = v___y_2051_;
v___y_2011_ = v___y_2052_;
v___y_2012_ = v___y_2054_;
v___y_2013_ = v___y_2053_;
v_a_2014_ = v_a_2056_;
goto v___jp_2005_;
}
else
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
lean_dec_ref(v___y_2054_);
lean_dec_ref(v___y_2053_);
lean_dec(v___y_2052_);
lean_dec_ref(v___y_2051_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec(v_mvarId_1969_);
v_a_2057_ = lean_ctor_get(v___y_2055_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___y_2055_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___y_2055_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___y_2055_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_a_2057_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lam__0___boxed(lean_object* v_mvarId_2185_, lean_object* v___x_2186_, lean_object* v_e_2187_, lean_object* v_cfg_2188_, lean_object* v_term_x3f_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
lean_object* v_res_2195_; 
v_res_2195_ = l_Lean_MVarId_apply___lam__0(v_mvarId_2185_, v___x_2186_, v_e_2187_, v_cfg_2188_, v_term_x3f_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
lean_dec_ref(v_cfg_2188_);
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply(lean_object* v_mvarId_2196_, lean_object* v_e_2197_, lean_object* v_cfg_2198_, lean_object* v_term_x3f_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_){
_start:
{
lean_object* v___x_2205_; lean_object* v___f_2206_; lean_object* v___x_2207_; 
v___x_2205_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7));
lean_inc(v_mvarId_2196_);
v___f_2206_ = lean_alloc_closure((void*)(l_Lean_MVarId_apply___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2206_, 0, v_mvarId_2196_);
lean_closure_set(v___f_2206_, 1, v___x_2205_);
lean_closure_set(v___f_2206_, 2, v_e_2197_);
lean_closure_set(v___f_2206_, 3, v_cfg_2198_);
lean_closure_set(v___f_2206_, 4, v_term_x3f_2199_);
v___x_2207_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2196_, v___f_2206_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___boxed(lean_object* v_mvarId_2208_, lean_object* v_e_2209_, lean_object* v_cfg_2210_, lean_object* v_term_x3f_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l_Lean_MVarId_apply(v_mvarId_2208_, v_e_2209_, v_cfg_2210_, v_term_x3f_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_);
lean_dec(v_a_2215_);
lean_dec_ref(v_a_2214_);
lean_dec(v_a_2213_);
lean_dec_ref(v_a_2212_);
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1(lean_object* v_mvarId_2218_, lean_object* v_val_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_){
_start:
{
lean_object* v___x_2225_; 
v___x_2225_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2218_, v_val_2219_, v___y_2221_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___boxed(lean_object* v_mvarId_2226_, lean_object* v_val_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1(v_mvarId_2226_, v_val_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5(lean_object* v_as_2234_, size_t v_i_2235_, size_t v_stop_2236_, lean_object* v_b_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
lean_object* v___x_2243_; 
v___x_2243_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_as_2234_, v_i_2235_, v_stop_2236_, v_b_2237_, v___y_2239_);
return v___x_2243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___boxed(lean_object* v_as_2244_, lean_object* v_i_2245_, lean_object* v_stop_2246_, lean_object* v_b_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
size_t v_i_boxed_2253_; size_t v_stop_boxed_2254_; lean_object* v_res_2255_; 
v_i_boxed_2253_ = lean_unbox_usize(v_i_2245_);
lean_dec(v_i_2245_);
v_stop_boxed_2254_ = lean_unbox_usize(v_stop_2246_);
lean_dec(v_stop_2246_);
v_res_2255_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5(v_as_2244_, v_i_boxed_2253_, v_stop_boxed_2254_, v_b_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec_ref(v_as_2244_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1(lean_object* v_00_u03b2_2256_, lean_object* v_x_2257_, lean_object* v_x_2258_, lean_object* v_x_2259_){
_start:
{
lean_object* v___x_2260_; 
v___x_2260_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(v_x_2257_, v_x_2258_, v_x_2259_);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_2261_, lean_object* v_x_2262_, size_t v_x_2263_, size_t v_x_2264_, lean_object* v_x_2265_, lean_object* v_x_2266_){
_start:
{
lean_object* v___x_2267_; 
v___x_2267_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_2262_, v_x_2263_, v_x_2264_, v_x_2265_, v_x_2266_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2268_, lean_object* v_x_2269_, lean_object* v_x_2270_, lean_object* v_x_2271_, lean_object* v_x_2272_, lean_object* v_x_2273_){
_start:
{
size_t v_x_7819__boxed_2274_; size_t v_x_7820__boxed_2275_; lean_object* v_res_2276_; 
v_x_7819__boxed_2274_ = lean_unbox_usize(v_x_2270_);
lean_dec(v_x_2270_);
v_x_7820__boxed_2275_ = lean_unbox_usize(v_x_2271_);
lean_dec(v_x_2271_);
v_res_2276_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3(v_00_u03b2_2268_, v_x_2269_, v_x_7819__boxed_2274_, v_x_7820__boxed_2275_, v_x_2272_, v_x_2273_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_2277_, lean_object* v_n_2278_, lean_object* v_k_2279_, lean_object* v_v_2280_){
_start:
{
lean_object* v___x_2281_; 
v___x_2281_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(v_n_2278_, v_k_2279_, v_v_2280_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9(lean_object* v_00_u03b2_2282_, size_t v_depth_2283_, lean_object* v_keys_2284_, lean_object* v_vals_2285_, lean_object* v_heq_2286_, lean_object* v_i_2287_, lean_object* v_entries_2288_){
_start:
{
lean_object* v___x_2289_; 
v___x_2289_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_depth_2283_, v_keys_2284_, v_vals_2285_, v_i_2287_, v_entries_2288_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___boxed(lean_object* v_00_u03b2_2290_, lean_object* v_depth_2291_, lean_object* v_keys_2292_, lean_object* v_vals_2293_, lean_object* v_heq_2294_, lean_object* v_i_2295_, lean_object* v_entries_2296_){
_start:
{
size_t v_depth_boxed_2297_; lean_object* v_res_2298_; 
v_depth_boxed_2297_ = lean_unbox_usize(v_depth_2291_);
lean_dec(v_depth_2291_);
v_res_2298_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9(v_00_u03b2_2290_, v_depth_boxed_2297_, v_keys_2292_, v_vals_2293_, v_heq_2294_, v_i_2295_, v_entries_2296_);
lean_dec_ref(v_vals_2293_);
lean_dec_ref(v_keys_2292_);
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9(lean_object* v_00_u03b2_2299_, lean_object* v_x_2300_, lean_object* v_x_2301_, lean_object* v_x_2302_, lean_object* v_x_2303_){
_start:
{
lean_object* v___x_2304_; 
v___x_2304_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(v_x_2300_, v_x_2301_, v_x_2302_, v_x_2303_);
return v___x_2304_;
}
}
static lean_object* _init_l_Lean_MVarId_applyConst___closed__1(void){
_start:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2306_ = ((lean_object*)(l_Lean_MVarId_applyConst___closed__0));
v___x_2307_ = l_Lean_stringToMessageData(v___x_2306_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyConst(lean_object* v_mvar_2308_, lean_object* v_c_2309_, lean_object* v_cfg_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_){
_start:
{
lean_object* v___x_2316_; 
lean_inc(v_c_2309_);
v___x_2316_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_c_2309_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v_a_2317_; lean_object* v___x_2318_; uint8_t v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
lean_inc(v_a_2317_);
lean_dec_ref_known(v___x_2316_, 1);
v___x_2318_ = lean_obj_once(&l_Lean_MVarId_applyConst___closed__1, &l_Lean_MVarId_applyConst___closed__1_once, _init_l_Lean_MVarId_applyConst___closed__1);
v___x_2319_ = 0;
v___x_2320_ = l_Lean_MessageData_ofConstName(v_c_2309_, v___x_2319_);
v___x_2321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2318_);
lean_ctor_set(v___x_2321_, 1, v___x_2320_);
v___x_2322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2321_);
lean_ctor_set(v___x_2322_, 1, v___x_2318_);
v___x_2323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2322_);
v___x_2324_ = l_Lean_MVarId_apply(v_mvar_2308_, v_a_2317_, v_cfg_2310_, v___x_2323_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_);
return v___x_2324_;
}
else
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2332_; 
lean_dec_ref(v_cfg_2310_);
lean_dec(v_c_2309_);
lean_dec(v_mvar_2308_);
v_a_2325_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2327_ = v___x_2316_;
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2316_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2330_; 
if (v_isShared_2328_ == 0)
{
v___x_2330_ = v___x_2327_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_a_2325_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyConst___boxed(lean_object* v_mvar_2333_, lean_object* v_c_2334_, lean_object* v_cfg_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_){
_start:
{
lean_object* v_res_2341_; 
v_res_2341_ = l_Lean_MVarId_applyConst(v_mvar_2333_, v_c_2334_, v_cfg_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_);
lean_dec(v_a_2339_);
lean_dec_ref(v_a_2338_);
lean_dec(v_a_2337_);
lean_dec_ref(v_a_2336_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(lean_object* v_msgData_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
lean_object* v___x_2348_; lean_object* v_env_2349_; uint8_t v___x_2350_; lean_object* v_env_2351_; lean_object* v___x_2352_; lean_object* v_toCold_2353_; lean_object* v_mctx_2354_; lean_object* v_lctx_2355_; lean_object* v_options_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2348_ = lean_st_ref_get(v___y_2346_);
v_env_2349_ = lean_ctor_get(v___x_2348_, 0);
lean_inc_ref(v_env_2349_);
lean_dec(v___x_2348_);
v___x_2350_ = 0;
v_env_2351_ = l_Lean_Environment_setRecordingDeps(v_env_2349_, v___x_2350_);
v___x_2352_ = lean_st_ref_get(v___y_2344_);
v_toCold_2353_ = lean_ctor_get(v___y_2345_, 0);
v_mctx_2354_ = lean_ctor_get(v___x_2352_, 0);
lean_inc_ref(v_mctx_2354_);
lean_dec(v___x_2352_);
v_lctx_2355_ = lean_ctor_get(v___y_2343_, 2);
v_options_2356_ = lean_ctor_get(v_toCold_2353_, 2);
lean_inc_ref(v_options_2356_);
lean_inc_ref(v_lctx_2355_);
v___x_2357_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2357_, 0, v_env_2351_);
lean_ctor_set(v___x_2357_, 1, v_mctx_2354_);
lean_ctor_set(v___x_2357_, 2, v_lctx_2355_);
lean_ctor_set(v___x_2357_, 3, v_options_2356_);
v___x_2358_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2357_);
lean_ctor_set(v___x_2358_, 1, v_msgData_2342_);
v___x_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1___boxed(lean_object* v_msgData_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(v_msgData_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(lean_object* v_msg_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_){
_start:
{
lean_object* v_ref_2373_; lean_object* v___x_2374_; lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2383_; 
v_ref_2373_ = lean_ctor_get(v___y_2370_, 2);
v___x_2374_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(v_msg_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_);
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2377_ = v___x_2374_;
v_isShared_2378_ = v_isSharedCheck_2383_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___x_2374_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2383_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2379_; lean_object* v___x_2381_; 
lean_inc(v_ref_2373_);
v___x_2379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2379_, 0, v_ref_2373_);
lean_ctor_set(v___x_2379_, 1, v_a_2375_);
if (v_isShared_2378_ == 0)
{
lean_ctor_set_tag(v___x_2377_, 1);
lean_ctor_set(v___x_2377_, 0, v___x_2379_);
v___x_2381_ = v___x_2377_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v___x_2379_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg___boxed(lean_object* v_msg_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v_msg_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(size_t v_sz_2391_, size_t v_i_2392_, lean_object* v_bs_2393_){
_start:
{
uint8_t v___x_2394_; 
v___x_2394_ = lean_usize_dec_lt(v_i_2392_, v_sz_2391_);
if (v___x_2394_ == 0)
{
return v_bs_2393_;
}
else
{
lean_object* v_v_2395_; lean_object* v___x_2396_; lean_object* v_bs_x27_2397_; lean_object* v___x_2398_; size_t v___x_2399_; size_t v___x_2400_; lean_object* v___x_2401_; 
v_v_2395_ = lean_array_uget(v_bs_2393_, v_i_2392_);
v___x_2396_ = lean_unsigned_to_nat(0u);
v_bs_x27_2397_ = lean_array_uset(v_bs_2393_, v_i_2392_, v___x_2396_);
v___x_2398_ = l_Lean_Expr_mvarId_x21(v_v_2395_);
lean_dec(v_v_2395_);
v___x_2399_ = ((size_t)1ULL);
v___x_2400_ = lean_usize_add(v_i_2392_, v___x_2399_);
v___x_2401_ = lean_array_uset(v_bs_x27_2397_, v_i_2392_, v___x_2398_);
v_i_2392_ = v___x_2400_;
v_bs_2393_ = v___x_2401_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0___boxed(lean_object* v_sz_2403_, lean_object* v_i_2404_, lean_object* v_bs_2405_){
_start:
{
size_t v_sz_boxed_2406_; size_t v_i_boxed_2407_; lean_object* v_res_2408_; 
v_sz_boxed_2406_ = lean_unbox_usize(v_sz_2403_);
lean_dec(v_sz_2403_);
v_i_boxed_2407_ = lean_unbox_usize(v_i_2404_);
lean_dec(v_i_2404_);
v_res_2408_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(v_sz_boxed_2406_, v_i_boxed_2407_, v_bs_2405_);
return v_res_2408_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2410_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__0));
v___x_2411_ = l_Lean_stringToMessageData(v___x_2410_);
return v___x_2411_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2413_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__2));
v___x_2414_ = l_Lean_stringToMessageData(v___x_2413_);
return v___x_2414_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2416_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__4));
v___x_2417_ = l_Lean_stringToMessageData(v___x_2416_);
return v___x_2417_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2419_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__6));
v___x_2420_ = l_Lean_stringToMessageData(v___x_2419_);
return v___x_2420_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__9(void){
_start:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2422_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__8));
v___x_2423_ = l_Lean_stringToMessageData(v___x_2422_);
return v___x_2423_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__11(void){
_start:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2425_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__10));
v___x_2426_ = l_Lean_stringToMessageData(v___x_2425_);
return v___x_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___lam__0(lean_object* v_mvarId_2427_, lean_object* v___x_2428_, lean_object* v_e_2429_, lean_object* v_n_2430_, uint8_t v_useApproxDefEq_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
lean_object* v___x_2437_; 
lean_inc(v_mvarId_2427_);
v___x_2437_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2427_, v___x_2428_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v___x_2438_; 
lean_dec_ref_known(v___x_2437_, 1);
lean_inc(v_mvarId_2427_);
v___x_2438_ = l_Lean_MVarId_getType(v_mvarId_2427_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_);
if (lean_obj_tag(v___x_2438_) == 0)
{
lean_object* v_a_2439_; lean_object* v___x_2440_; 
v_a_2439_ = lean_ctor_get(v___x_2438_, 0);
lean_inc(v_a_2439_);
lean_dec_ref_known(v___x_2438_, 1);
lean_inc(v___y_2435_);
lean_inc_ref(v___y_2434_);
lean_inc(v___y_2433_);
lean_inc_ref(v___y_2432_);
lean_inc_ref(v_e_2429_);
v___x_2440_ = lean_infer_type(v_e_2429_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_);
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_object* v_a_2441_; uint8_t v___x_2442_; lean_object* v___x_2443_; 
v_a_2441_ = lean_ctor_get(v___x_2440_, 0);
lean_inc(v_a_2441_);
lean_dec_ref_known(v___x_2440_, 1);
v___x_2442_ = 0;
lean_inc(v_n_2430_);
v___x_2443_ = l_Lean_Meta_forallMetaBoundedTelescope(v_a_2441_, v_n_2430_, v___x_2442_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; lean_object* v_fst_2445_; lean_object* v_snd_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2536_; 
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
lean_inc(v_a_2444_);
lean_dec_ref_known(v___x_2443_, 1);
v_fst_2445_ = lean_ctor_get(v_a_2444_, 0);
v_snd_2446_ = lean_ctor_get(v_a_2444_, 1);
v_isSharedCheck_2536_ = !lean_is_exclusive(v_a_2444_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2448_ = v_a_2444_;
v_isShared_2449_ = v_isSharedCheck_2536_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_snd_2446_);
lean_inc(v_fst_2445_);
lean_dec(v_a_2444_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2536_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___y_2451_; lean_object* v_snd_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2534_; 
v_snd_2466_ = lean_ctor_get(v_snd_2446_, 1);
v_isSharedCheck_2534_ = !lean_is_exclusive(v_snd_2446_);
if (v_isSharedCheck_2534_ == 0)
{
lean_object* v_unused_2535_; 
v_unused_2535_ = lean_ctor_get(v_snd_2446_, 0);
lean_dec(v_unused_2535_);
v___x_2468_ = v_snd_2446_;
v_isShared_2469_ = v_isSharedCheck_2534_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_snd_2466_);
lean_dec(v_snd_2446_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2534_;
goto v_resetjp_2467_;
}
v___jp_2450_:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2464_; 
lean_inc(v_fst_2445_);
v___x_2452_ = l_Lean_Expr_beta(v_e_2429_, v_fst_2445_);
v___x_2453_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2427_, v___x_2452_, v___y_2451_);
lean_dec(v___y_2451_);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2464_ == 0)
{
lean_object* v_unused_2465_; 
v_unused_2465_ = lean_ctor_get(v___x_2453_, 0);
lean_dec(v_unused_2465_);
v___x_2455_ = v___x_2453_;
v_isShared_2456_ = v_isSharedCheck_2464_;
goto v_resetjp_2454_;
}
else
{
lean_dec(v___x_2453_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2464_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
size_t v_sz_2457_; size_t v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2462_; 
v_sz_2457_ = lean_array_size(v_fst_2445_);
v___x_2458_ = ((size_t)0ULL);
v___x_2459_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(v_sz_2457_, v___x_2458_, v_fst_2445_);
v___x_2460_ = lean_array_to_list(v___x_2459_);
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 0, v___x_2460_);
v___x_2462_ = v___x_2455_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v___x_2460_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
}
v_resetjp_2467_:
{
lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v___x_2514_; uint8_t v___x_2515_; 
v___x_2514_ = lean_array_get_size(v_fst_2445_);
v___x_2515_ = lean_nat_dec_eq(v___x_2514_, v_n_2430_);
if (v___x_2515_ == 0)
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
lean_del_object(v___x_2468_);
lean_del_object(v___x_2448_);
lean_dec(v_fst_2445_);
lean_dec(v_a_2439_);
lean_dec_ref(v_e_2429_);
lean_dec(v_mvarId_2427_);
v___x_2516_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__9, &l_Lean_MVarId_applyN___lam__0___closed__9_once, _init_l_Lean_MVarId_applyN___lam__0___closed__9);
v___x_2517_ = l_Nat_reprFast(v_n_2430_);
v___x_2518_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2517_);
v___x_2519_ = l_Lean_MessageData_ofFormat(v___x_2518_);
v___x_2520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2516_);
lean_ctor_set(v___x_2520_, 1, v___x_2519_);
v___x_2521_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__11, &l_Lean_MVarId_applyN___lam__0___closed__11_once, _init_l_Lean_MVarId_applyN___lam__0___closed__11);
v___x_2522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2520_);
lean_ctor_set(v___x_2522_, 1, v___x_2521_);
v___x_2523_ = l_Lean_indentExpr(v_snd_2466_);
v___x_2524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2524_, 0, v___x_2522_);
lean_ctor_set(v___x_2524_, 1, v___x_2523_);
v___x_2525_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_2524_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_);
lean_dec(v___y_2435_);
lean_dec_ref(v___y_2434_);
lean_dec(v___y_2433_);
lean_dec_ref(v___y_2432_);
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2528_ = v___x_2525_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2525_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2529_ == 0)
{
v___x_2531_ = v___x_2528_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_a_2526_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
else
{
v___y_2471_ = v___y_2432_;
v___y_2472_ = v___y_2433_;
v___y_2473_ = v___y_2434_;
v___y_2474_ = v___y_2435_;
goto v___jp_2470_;
}
v___jp_2470_:
{
lean_object* v___x_2475_; 
lean_inc(v_a_2439_);
lean_inc(v_snd_2466_);
v___x_2475_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_useApproxDefEq_2431_, v_snd_2466_, v_a_2439_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_);
if (lean_obj_tag(v___x_2475_) == 0)
{
lean_object* v_a_2476_; uint8_t v___x_2477_; 
v_a_2476_ = lean_ctor_get(v___x_2475_, 0);
lean_inc(v_a_2476_);
lean_dec_ref_known(v___x_2475_, 1);
v___x_2477_ = lean_unbox(v_a_2476_);
lean_dec(v_a_2476_);
if (v___x_2477_ == 0)
{
lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2481_; 
lean_dec(v_fst_2445_);
lean_dec_ref(v_e_2429_);
lean_dec(v_mvarId_2427_);
v___x_2478_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__1, &l_Lean_MVarId_applyN___lam__0___closed__1_once, _init_l_Lean_MVarId_applyN___lam__0___closed__1);
v___x_2479_ = l_Lean_indentExpr(v_a_2439_);
if (v_isShared_2469_ == 0)
{
lean_ctor_set_tag(v___x_2468_, 7);
lean_ctor_set(v___x_2468_, 1, v___x_2479_);
lean_ctor_set(v___x_2468_, 0, v___x_2478_);
v___x_2481_ = v___x_2468_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v___x_2478_);
lean_ctor_set(v_reuseFailAlloc_2505_, 1, v___x_2479_);
v___x_2481_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
lean_object* v___x_2482_; lean_object* v___x_2484_; 
v___x_2482_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__3, &l_Lean_MVarId_applyN___lam__0___closed__3_once, _init_l_Lean_MVarId_applyN___lam__0___closed__3);
if (v_isShared_2449_ == 0)
{
lean_ctor_set_tag(v___x_2448_, 7);
lean_ctor_set(v___x_2448_, 1, v___x_2482_);
lean_ctor_set(v___x_2448_, 0, v___x_2481_);
v___x_2484_ = v___x_2448_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v___x_2481_);
lean_ctor_set(v_reuseFailAlloc_2504_, 1, v___x_2482_);
v___x_2484_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2503_; 
v___x_2485_ = l_Lean_indentExpr(v_snd_2466_);
v___x_2486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2484_);
lean_ctor_set(v___x_2486_, 1, v___x_2485_);
v___x_2487_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__5, &l_Lean_MVarId_applyN___lam__0___closed__5_once, _init_l_Lean_MVarId_applyN___lam__0___closed__5);
v___x_2488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2486_);
lean_ctor_set(v___x_2488_, 1, v___x_2487_);
v___x_2489_ = l_Nat_reprFast(v_n_2430_);
v___x_2490_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2490_, 0, v___x_2489_);
v___x_2491_ = l_Lean_MessageData_ofFormat(v___x_2490_);
v___x_2492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2488_);
lean_ctor_set(v___x_2492_, 1, v___x_2491_);
v___x_2493_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__7, &l_Lean_MVarId_applyN___lam__0___closed__7_once, _init_l_Lean_MVarId_applyN___lam__0___closed__7);
v___x_2494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2492_);
lean_ctor_set(v___x_2494_, 1, v___x_2493_);
v___x_2495_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_2494_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
v_a_2496_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2498_ = v___x_2495_;
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2495_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2501_; 
if (v_isShared_2499_ == 0)
{
v___x_2501_ = v___x_2498_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_a_2496_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
}
}
else
{
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec_ref(v___y_2471_);
lean_del_object(v___x_2468_);
lean_dec(v_snd_2466_);
lean_del_object(v___x_2448_);
lean_dec(v_a_2439_);
lean_dec(v_n_2430_);
v___y_2451_ = v___y_2472_;
goto v___jp_2450_;
}
}
else
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2513_; 
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_del_object(v___x_2468_);
lean_dec(v_snd_2466_);
lean_del_object(v___x_2448_);
lean_dec(v_fst_2445_);
lean_dec(v_a_2439_);
lean_dec(v_n_2430_);
lean_dec_ref(v_e_2429_);
lean_dec(v_mvarId_2427_);
v_a_2506_ = lean_ctor_get(v___x_2475_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2508_ = v___x_2475_;
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___x_2475_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2511_; 
if (v_isShared_2509_ == 0)
{
v___x_2511_ = v___x_2508_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_a_2506_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2544_; 
lean_dec(v_a_2439_);
lean_dec(v___y_2435_);
lean_dec_ref(v___y_2434_);
lean_dec(v___y_2433_);
lean_dec_ref(v___y_2432_);
lean_dec(v_n_2430_);
lean_dec_ref(v_e_2429_);
lean_dec(v_mvarId_2427_);
v_a_2537_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2539_ = v___x_2443_;
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2443_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2542_; 
if (v_isShared_2540_ == 0)
{
v___x_2542_ = v___x_2539_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_a_2537_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
}
else
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2552_; 
lean_dec(v_a_2439_);
lean_dec(v___y_2435_);
lean_dec_ref(v___y_2434_);
lean_dec(v___y_2433_);
lean_dec_ref(v___y_2432_);
lean_dec(v_n_2430_);
lean_dec_ref(v_e_2429_);
lean_dec(v_mvarId_2427_);
v_a_2545_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2547_ = v___x_2440_;
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2440_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2550_; 
if (v_isShared_2548_ == 0)
{
v___x_2550_ = v___x_2547_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_a_2545_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
}
else
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2560_; 
lean_dec(v___y_2435_);
lean_dec_ref(v___y_2434_);
lean_dec(v___y_2433_);
lean_dec_ref(v___y_2432_);
lean_dec(v_n_2430_);
lean_dec_ref(v_e_2429_);
lean_dec(v_mvarId_2427_);
v_a_2553_ = lean_ctor_get(v___x_2438_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2438_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2555_ = v___x_2438_;
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2438_);
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
else
{
lean_object* v_a_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2568_; 
lean_dec(v___y_2435_);
lean_dec_ref(v___y_2434_);
lean_dec(v___y_2433_);
lean_dec_ref(v___y_2432_);
lean_dec(v_n_2430_);
lean_dec_ref(v_e_2429_);
lean_dec(v_mvarId_2427_);
v_a_2561_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2563_ = v___x_2437_;
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_a_2561_);
lean_dec(v___x_2437_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2566_; 
if (v_isShared_2564_ == 0)
{
v___x_2566_ = v___x_2563_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_a_2561_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___lam__0___boxed(lean_object* v_mvarId_2569_, lean_object* v___x_2570_, lean_object* v_e_2571_, lean_object* v_n_2572_, lean_object* v_useApproxDefEq_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_){
_start:
{
uint8_t v_useApproxDefEq_boxed_2579_; lean_object* v_res_2580_; 
v_useApproxDefEq_boxed_2579_ = lean_unbox(v_useApproxDefEq_2573_);
v_res_2580_ = l_Lean_MVarId_applyN___lam__0(v_mvarId_2569_, v___x_2570_, v_e_2571_, v_n_2572_, v_useApproxDefEq_boxed_2579_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN(lean_object* v_mvarId_2581_, lean_object* v_e_2582_, lean_object* v_n_2583_, uint8_t v_useApproxDefEq_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_){
_start:
{
lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___f_2592_; lean_object* v___x_2593_; 
v___x_2590_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7));
v___x_2591_ = lean_box(v_useApproxDefEq_2584_);
lean_inc(v_mvarId_2581_);
v___f_2592_ = lean_alloc_closure((void*)(l_Lean_MVarId_applyN___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2592_, 0, v_mvarId_2581_);
lean_closure_set(v___f_2592_, 1, v___x_2590_);
lean_closure_set(v___f_2592_, 2, v_e_2582_);
lean_closure_set(v___f_2592_, 3, v_n_2583_);
lean_closure_set(v___f_2592_, 4, v___x_2591_);
v___x_2593_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2581_, v___f_2592_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_);
return v___x_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___boxed(lean_object* v_mvarId_2594_, lean_object* v_e_2595_, lean_object* v_n_2596_, lean_object* v_useApproxDefEq_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_){
_start:
{
uint8_t v_useApproxDefEq_boxed_2603_; lean_object* v_res_2604_; 
v_useApproxDefEq_boxed_2603_ = lean_unbox(v_useApproxDefEq_2597_);
v_res_2604_ = l_Lean_MVarId_applyN(v_mvarId_2594_, v_e_2595_, v_n_2596_, v_useApproxDefEq_boxed_2603_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_);
lean_dec(v_a_2601_);
lean_dec_ref(v_a_2600_);
lean_dec(v_a_2599_);
lean_dec_ref(v_a_2598_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1(lean_object* v_00_u03b1_2605_, lean_object* v_msg_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
lean_object* v___x_2612_; 
v___x_2612_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v_msg_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
return v___x_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___boxed(lean_object* v_00_u03b1_2613_, lean_object* v_msg_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
lean_object* v_res_2620_; 
v_res_2620_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1(v_00_u03b1_2613_, v_msg_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
return v_res_2620_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6(void){
_start:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2631_ = lean_box(0);
v___x_2632_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__5));
v___x_2633_ = l_Lean_mkConst(v___x_2632_, v___x_2631_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(lean_object* v_tag_2634_, lean_object* v_type_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_){
_start:
{
lean_object* v___x_2642_; 
lean_inc(v_a_2640_);
lean_inc_ref(v_a_2639_);
lean_inc(v_a_2638_);
lean_inc_ref(v_a_2637_);
v___x_2642_ = lean_whnf(v_type_2635_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_);
if (lean_obj_tag(v___x_2642_) == 0)
{
lean_object* v_a_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; uint8_t v___x_2646_; 
v_a_2643_ = lean_ctor_get(v___x_2642_, 0);
lean_inc(v_a_2643_);
lean_dec_ref_known(v___x_2642_, 1);
v___x_2644_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1));
v___x_2645_ = lean_unsigned_to_nat(2u);
v___x_2646_ = l_Lean_Expr_isAppOfArity(v_a_2643_, v___x_2644_, v___x_2645_);
if (v___x_2646_ == 0)
{
lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2647_ = lean_st_ref_get(v_a_2636_);
v___x_2648_ = lean_array_get_size(v___x_2647_);
lean_dec(v___x_2647_);
v___x_2649_ = lean_unsigned_to_nat(1u);
v___x_2650_ = lean_nat_add(v___x_2648_, v___x_2649_);
v___x_2651_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__3));
v___x_2652_ = lean_name_append_index_after(v___x_2651_, v___x_2650_);
v___x_2653_ = l_Lean_Name_append(v_tag_2634_, v___x_2652_);
v___x_2654_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2643_, v___x_2653_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_object* v_a_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2666_; 
v_a_2655_ = lean_ctor_get(v___x_2654_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2657_ = v___x_2654_;
v_isShared_2658_ = v_isSharedCheck_2666_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_a_2655_);
lean_dec(v___x_2654_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2666_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2664_; 
v___x_2659_ = lean_st_ref_take(v_a_2636_);
v___x_2660_ = l_Lean_Expr_mvarId_x21(v_a_2655_);
v___x_2661_ = lean_array_push(v___x_2659_, v___x_2660_);
v___x_2662_ = lean_st_ref_put(v_a_2636_, v___x_2661_);
if (v_isShared_2658_ == 0)
{
v___x_2664_ = v___x_2657_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v_a_2655_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
else
{
return v___x_2654_;
}
}
else
{
lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; 
v___x_2667_ = l_Lean_Expr_appFn_x21(v_a_2643_);
v___x_2668_ = l_Lean_Expr_appArg_x21(v___x_2667_);
lean_dec_ref(v___x_2667_);
v___x_2669_ = l_Lean_Expr_appArg_x21(v_a_2643_);
lean_dec(v_a_2643_);
lean_inc_ref(v___x_2668_);
lean_inc(v_tag_2634_);
v___x_2670_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2634_, v___x_2668_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_);
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_object* v_a_2671_; lean_object* v___x_2672_; 
v_a_2671_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_a_2671_);
lean_dec_ref_known(v___x_2670_, 1);
lean_inc_ref(v___x_2669_);
v___x_2672_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2634_, v___x_2669_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v_a_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2682_; 
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2675_ = v___x_2672_;
v_isShared_2676_ = v_isSharedCheck_2682_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_a_2673_);
lean_dec(v___x_2672_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2682_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2680_; 
v___x_2677_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6, &l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6);
v___x_2678_ = l_Lean_mkApp4(v___x_2677_, v___x_2668_, v___x_2669_, v_a_2671_, v_a_2673_);
if (v_isShared_2676_ == 0)
{
lean_ctor_set(v___x_2675_, 0, v___x_2678_);
v___x_2680_ = v___x_2675_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v___x_2678_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
else
{
lean_dec(v_a_2671_);
lean_dec_ref(v___x_2669_);
lean_dec_ref(v___x_2668_);
return v___x_2672_;
}
}
else
{
lean_dec_ref(v___x_2669_);
lean_dec_ref(v___x_2668_);
lean_dec(v_tag_2634_);
return v___x_2670_;
}
}
}
else
{
lean_dec(v_tag_2634_);
return v___x_2642_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___boxed(lean_object* v_tag_2683_, lean_object* v_type_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_){
_start:
{
lean_object* v_res_2691_; 
v_res_2691_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2683_, v_type_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_);
lean_dec(v_a_2689_);
lean_dec_ref(v_a_2688_);
lean_dec(v_a_2687_);
lean_dec_ref(v_a_2686_);
lean_dec(v_a_2685_);
return v_res_2691_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___lam__0(lean_object* v_mvarId_2692_, lean_object* v___x_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
lean_object* v___x_2699_; 
lean_inc(v_mvarId_2692_);
v___x_2699_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2692_, v___x_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
if (lean_obj_tag(v___x_2699_) == 0)
{
lean_object* v___x_2700_; 
lean_dec_ref_known(v___x_2699_, 1);
lean_inc(v_mvarId_2692_);
v___x_2700_ = l_Lean_MVarId_getType_x27(v_mvarId_2692_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
if (lean_obj_tag(v___x_2700_) == 0)
{
lean_object* v_a_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2746_; 
v_a_2701_ = lean_ctor_get(v___x_2700_, 0);
v_isSharedCheck_2746_ = !lean_is_exclusive(v___x_2700_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2703_ = v___x_2700_;
v_isShared_2704_ = v_isSharedCheck_2746_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_a_2701_);
lean_dec(v___x_2700_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2746_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; uint8_t v___x_2707_; 
v___x_2705_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1));
v___x_2706_ = lean_unsigned_to_nat(2u);
v___x_2707_ = l_Lean_Expr_isAppOfArity(v_a_2701_, v___x_2705_, v___x_2706_);
if (v___x_2707_ == 0)
{
lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2711_; 
lean_dec(v_a_2701_);
v___x_2708_ = lean_box(0);
v___x_2709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2709_, 0, v_mvarId_2692_);
lean_ctor_set(v___x_2709_, 1, v___x_2708_);
if (v_isShared_2704_ == 0)
{
lean_ctor_set(v___x_2703_, 0, v___x_2709_);
v___x_2711_ = v___x_2703_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v___x_2709_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
return v___x_2711_;
}
}
else
{
lean_object* v___x_2713_; 
lean_del_object(v___x_2703_);
lean_inc(v_mvarId_2692_);
v___x_2713_ = l_Lean_MVarId_getTag(v_mvarId_2692_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
if (lean_obj_tag(v___x_2713_) == 0)
{
lean_object* v_a_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v_a_2714_ = lean_ctor_get(v___x_2713_, 0);
lean_inc(v_a_2714_);
lean_dec_ref_known(v___x_2713_, 1);
v___x_2715_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__0));
v___x_2716_ = lean_st_mk_ref(v___x_2715_);
v___x_2717_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_a_2714_, v_a_2701_, v___x_2716_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
if (lean_obj_tag(v___x_2717_) == 0)
{
lean_object* v_a_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2728_; 
v_a_2718_ = lean_ctor_get(v___x_2717_, 0);
lean_inc(v_a_2718_);
lean_dec_ref_known(v___x_2717_, 1);
v___x_2719_ = lean_st_ref_get(v___x_2716_);
lean_dec(v___x_2716_);
v___x_2720_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2692_, v_a_2718_, v___y_2695_);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2720_);
if (v_isSharedCheck_2728_ == 0)
{
lean_object* v_unused_2729_; 
v_unused_2729_ = lean_ctor_get(v___x_2720_, 0);
lean_dec(v_unused_2729_);
v___x_2722_ = v___x_2720_;
v_isShared_2723_ = v_isSharedCheck_2728_;
goto v_resetjp_2721_;
}
else
{
lean_dec(v___x_2720_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2728_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2724_; lean_object* v___x_2726_; 
v___x_2724_ = lean_array_to_list(v___x_2719_);
if (v_isShared_2723_ == 0)
{
lean_ctor_set(v___x_2722_, 0, v___x_2724_);
v___x_2726_ = v___x_2722_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v___x_2724_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
return v___x_2726_;
}
}
}
else
{
lean_object* v_a_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2737_; 
lean_dec(v___x_2716_);
lean_dec(v_mvarId_2692_);
v_a_2730_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2732_ = v___x_2717_;
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_a_2730_);
lean_dec(v___x_2717_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2735_; 
if (v_isShared_2733_ == 0)
{
v___x_2735_ = v___x_2732_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_a_2730_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
}
else
{
lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2745_; 
lean_dec(v_a_2701_);
lean_dec(v_mvarId_2692_);
v_a_2738_ = lean_ctor_get(v___x_2713_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2740_ = v___x_2713_;
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_dec(v___x_2713_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2743_; 
if (v_isShared_2741_ == 0)
{
v___x_2743_ = v___x_2740_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_a_2738_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
}
}
}
else
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2754_; 
lean_dec(v_mvarId_2692_);
v_a_2747_ = lean_ctor_get(v___x_2700_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2700_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2749_ = v___x_2700_;
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2700_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2752_; 
if (v_isShared_2750_ == 0)
{
v___x_2752_ = v___x_2749_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_a_2747_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
}
else
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
lean_dec(v_mvarId_2692_);
v_a_2755_ = lean_ctor_get(v___x_2699_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2699_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v___x_2699_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2699_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2758_ == 0)
{
v___x_2760_ = v___x_2757_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2755_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___lam__0___boxed(lean_object* v_mvarId_2763_, lean_object* v___x_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_){
_start:
{
lean_object* v_res_2770_; 
v_res_2770_ = l_Lean_MVarId_splitAndCore___lam__0(v_mvarId_2763_, v___x_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_);
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
lean_dec(v___y_2766_);
lean_dec_ref(v___y_2765_);
return v_res_2770_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore(lean_object* v_mvarId_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_){
_start:
{
lean_object* v___x_2780_; lean_object* v___f_2781_; lean_object* v___x_2782_; 
v___x_2780_ = ((lean_object*)(l_Lean_MVarId_splitAndCore___closed__1));
lean_inc(v_mvarId_2774_);
v___f_2781_ = lean_alloc_closure((void*)(l_Lean_MVarId_splitAndCore___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2781_, 0, v_mvarId_2774_);
lean_closure_set(v___f_2781_, 1, v___x_2780_);
v___x_2782_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2774_, v___f_2781_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___boxed(lean_object* v_mvarId_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_){
_start:
{
lean_object* v_res_2789_; 
v_res_2789_ = l_Lean_MVarId_splitAndCore(v_mvarId_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_);
lean_dec(v_a_2787_);
lean_dec_ref(v_a_2786_);
lean_dec(v_a_2785_);
lean_dec_ref(v_a_2784_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAnd(lean_object* v_mvarId_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_){
_start:
{
lean_object* v___x_2796_; 
v___x_2796_ = l_Lean_MVarId_splitAndCore(v_mvarId_2790_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_);
return v___x_2796_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAnd___boxed(lean_object* v_mvarId_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_){
_start:
{
lean_object* v_res_2803_; 
v_res_2803_ = l_Lean_MVarId_splitAnd(v_mvarId_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_);
lean_dec(v_a_2801_);
lean_dec_ref(v_a_2800_);
lean_dec(v_a_2799_);
lean_dec_ref(v_a_2798_);
return v_res_2803_;
}
}
static lean_object* _init_l_Lean_MVarId_exfalso___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2807_ = lean_box(0);
v___x_2808_ = ((lean_object*)(l_Lean_MVarId_exfalso___lam__0___closed__1));
v___x_2809_ = l_Lean_mkConst(v___x_2808_, v___x_2807_);
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___lam__0(lean_object* v_mvarId_2814_, lean_object* v___x_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_){
_start:
{
lean_object* v___x_2821_; 
lean_inc(v_mvarId_2814_);
v___x_2821_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2814_, v___x_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
if (lean_obj_tag(v___x_2821_) == 0)
{
lean_object* v___x_2822_; 
lean_dec_ref_known(v___x_2821_, 1);
lean_inc(v_mvarId_2814_);
v___x_2822_ = l_Lean_MVarId_getType(v_mvarId_2814_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_object* v_a_2823_; lean_object* v___x_2824_; lean_object* v_a_2825_; lean_object* v___x_2826_; 
v_a_2823_ = lean_ctor_get(v___x_2822_, 0);
lean_inc(v_a_2823_);
lean_dec_ref_known(v___x_2822_, 1);
v___x_2824_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_a_2823_, v___y_2817_);
v_a_2825_ = lean_ctor_get(v___x_2824_, 0);
lean_inc_n(v_a_2825_, 2);
lean_dec_ref(v___x_2824_);
v___x_2826_ = l_Lean_Meta_getLevel(v_a_2825_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v_a_2827_; lean_object* v___x_2828_; 
v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
lean_inc(v_a_2827_);
lean_dec_ref_known(v___x_2826_, 1);
lean_inc(v_mvarId_2814_);
v___x_2828_ = l_Lean_MVarId_getTag(v_mvarId_2814_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
if (lean_obj_tag(v___x_2828_) == 0)
{
lean_object* v_a_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; 
v_a_2829_ = lean_ctor_get(v___x_2828_, 0);
lean_inc(v_a_2829_);
lean_dec_ref_known(v___x_2828_, 1);
v___x_2830_ = lean_box(0);
v___x_2831_ = lean_obj_once(&l_Lean_MVarId_exfalso___lam__0___closed__2, &l_Lean_MVarId_exfalso___lam__0___closed__2_once, _init_l_Lean_MVarId_exfalso___lam__0___closed__2);
v___x_2832_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2831_, v_a_2829_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
if (lean_obj_tag(v___x_2832_) == 0)
{
lean_object* v_a_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2846_; 
v_a_2833_ = lean_ctor_get(v___x_2832_, 0);
lean_inc_n(v_a_2833_, 2);
lean_dec_ref_known(v___x_2832_, 1);
v___x_2834_ = ((lean_object*)(l_Lean_MVarId_exfalso___lam__0___closed__4));
v___x_2835_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2835_, 0, v_a_2827_);
lean_ctor_set(v___x_2835_, 1, v___x_2830_);
v___x_2836_ = l_Lean_mkConst(v___x_2834_, v___x_2835_);
v___x_2837_ = l_Lean_mkAppB(v___x_2836_, v_a_2825_, v_a_2833_);
v___x_2838_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2814_, v___x_2837_, v___y_2817_);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2846_ == 0)
{
lean_object* v_unused_2847_; 
v_unused_2847_ = lean_ctor_get(v___x_2838_, 0);
lean_dec(v_unused_2847_);
v___x_2840_ = v___x_2838_;
v_isShared_2841_ = v_isSharedCheck_2846_;
goto v_resetjp_2839_;
}
else
{
lean_dec(v___x_2838_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2846_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2842_; lean_object* v___x_2844_; 
v___x_2842_ = l_Lean_Expr_mvarId_x21(v_a_2833_);
lean_dec(v_a_2833_);
if (v_isShared_2841_ == 0)
{
lean_ctor_set(v___x_2840_, 0, v___x_2842_);
v___x_2844_ = v___x_2840_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v___x_2842_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
}
else
{
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2855_; 
lean_dec(v_a_2827_);
lean_dec(v_a_2825_);
lean_dec(v_mvarId_2814_);
v_a_2848_ = lean_ctor_get(v___x_2832_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2832_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2850_ = v___x_2832_;
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2832_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2853_; 
if (v_isShared_2851_ == 0)
{
v___x_2853_ = v___x_2850_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_a_2848_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
}
}
else
{
lean_object* v_a_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2863_; 
lean_dec(v_a_2827_);
lean_dec(v_a_2825_);
lean_dec(v_mvarId_2814_);
v_a_2856_ = lean_ctor_get(v___x_2828_, 0);
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2828_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2858_ = v___x_2828_;
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_a_2856_);
lean_dec(v___x_2828_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2861_; 
if (v_isShared_2859_ == 0)
{
v___x_2861_ = v___x_2858_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_a_2856_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
}
else
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2871_; 
lean_dec(v_a_2825_);
lean_dec(v_mvarId_2814_);
v_a_2864_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2866_ = v___x_2826_;
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2826_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2869_; 
if (v_isShared_2867_ == 0)
{
v___x_2869_ = v___x_2866_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_a_2864_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
}
else
{
lean_object* v_a_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2879_; 
lean_dec(v_mvarId_2814_);
v_a_2872_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2874_ = v___x_2822_;
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_a_2872_);
lean_dec(v___x_2822_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2877_; 
if (v_isShared_2875_ == 0)
{
v___x_2877_ = v___x_2874_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_a_2872_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
}
}
else
{
lean_object* v_a_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2887_; 
lean_dec(v_mvarId_2814_);
v_a_2880_ = lean_ctor_get(v___x_2821_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2882_ = v___x_2821_;
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_a_2880_);
lean_dec(v___x_2821_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2885_; 
if (v_isShared_2883_ == 0)
{
v___x_2885_ = v___x_2882_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_a_2880_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___lam__0___boxed(lean_object* v_mvarId_2888_, lean_object* v___x_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_){
_start:
{
lean_object* v_res_2895_; 
v_res_2895_ = l_Lean_MVarId_exfalso___lam__0(v_mvarId_2888_, v___x_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso(lean_object* v_mvarId_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_){
_start:
{
lean_object* v___x_2905_; lean_object* v___f_2906_; lean_object* v___x_2907_; 
v___x_2905_ = ((lean_object*)(l_Lean_MVarId_exfalso___closed__1));
lean_inc(v_mvarId_2899_);
v___f_2906_ = lean_alloc_closure((void*)(l_Lean_MVarId_exfalso___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2906_, 0, v_mvarId_2899_);
lean_closure_set(v___f_2906_, 1, v___x_2905_);
v___x_2907_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2899_, v___f_2906_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_);
return v___x_2907_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___boxed(lean_object* v_mvarId_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_){
_start:
{
lean_object* v_res_2914_; 
v_res_2914_ = l_Lean_MVarId_exfalso(v_mvarId_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
lean_dec(v_a_2912_);
lean_dec_ref(v_a_2911_);
lean_dec(v_a_2910_);
lean_dec_ref(v_a_2909_);
return v_res_2914_;
}
}
static lean_object* _init_l_Lean_MVarId_nthConstructor___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2918_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__1));
v___x_2919_ = l_Lean_MessageData_ofFormat(v___x_2918_);
return v___x_2919_;
}
}
static lean_object* _init_l_Lean_MVarId_nthConstructor___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2920_ = lean_obj_once(&l_Lean_MVarId_nthConstructor___lam__0___closed__2, &l_Lean_MVarId_nthConstructor___lam__0___closed__2_once, _init_l_Lean_MVarId_nthConstructor___lam__0___closed__2);
v___x_2921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2920_);
return v___x_2921_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___lam__0(lean_object* v_name_2926_, lean_object* v_goal_2927_, lean_object* v_idx_2928_, lean_object* v_expected_x3f_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_){
_start:
{
lean_object* v___x_2938_; 
lean_inc(v_name_2926_);
lean_inc(v_goal_2927_);
v___x_2938_ = l_Lean_MVarId_checkNotAssigned(v_goal_2927_, v_name_2926_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
if (lean_obj_tag(v___x_2938_) == 0)
{
lean_object* v___x_2939_; 
lean_dec_ref_known(v___x_2938_, 1);
lean_inc(v_goal_2927_);
v___x_2939_ = l_Lean_MVarId_getType_x27(v_goal_2927_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v_a_2940_; lean_object* v___x_2941_; 
v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
lean_inc(v_a_2940_);
lean_dec_ref_known(v___x_2939_, 1);
v___x_2941_ = l_Lean_Expr_getAppFn(v_a_2940_);
lean_dec(v_a_2940_);
if (lean_obj_tag(v___x_2941_) == 4)
{
lean_object* v_declName_2942_; lean_object* v_us_2943_; lean_object* v___x_2944_; lean_object* v_env_2945_; uint8_t v___x_2946_; lean_object* v___x_2947_; 
v_declName_2942_ = lean_ctor_get(v___x_2941_, 0);
lean_inc(v_declName_2942_);
v_us_2943_ = lean_ctor_get(v___x_2941_, 1);
lean_inc(v_us_2943_);
lean_dec_ref_known(v___x_2941_, 2);
v___x_2944_ = lean_st_ref_get(v___y_2933_);
v_env_2945_ = lean_ctor_get(v___x_2944_, 0);
lean_inc_ref(v_env_2945_);
lean_dec(v___x_2944_);
v___x_2946_ = 0;
v___x_2947_ = l_Lean_Environment_find_x3f(v_env_2945_, v_declName_2942_, v___x_2946_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_dec(v_us_2943_);
lean_dec(v_expected_x3f_2929_);
lean_dec(v_idx_2928_);
goto v___jp_2935_;
}
else
{
lean_object* v_val_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_3018_; 
v_val_2948_ = lean_ctor_get(v___x_2947_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_2950_ = v___x_2947_;
v_isShared_2951_ = v_isSharedCheck_3018_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_val_2948_);
lean_dec(v___x_2947_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_3018_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
if (lean_obj_tag(v_val_2948_) == 5)
{
lean_object* v_val_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_3017_; 
v_val_2952_ = lean_ctor_get(v_val_2948_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v_val_2948_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_2954_ = v_val_2948_;
v_isShared_2955_ = v_isSharedCheck_3017_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_val_2952_);
lean_dec(v_val_2948_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_3017_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; 
if (lean_obj_tag(v_expected_x3f_2929_) == 1)
{
lean_object* v_val_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_3016_; 
v_val_2987_ = lean_ctor_get(v_expected_x3f_2929_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v_expected_x3f_2929_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_2989_ = v_expected_x3f_2929_;
v_isShared_2990_ = v_isSharedCheck_3016_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_val_2987_);
lean_dec(v_expected_x3f_2929_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_3016_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v_ctors_2991_; lean_object* v___x_2992_; uint8_t v___x_2993_; 
v_ctors_2991_ = lean_ctor_get(v_val_2952_, 4);
v___x_2992_ = l_List_lengthTR___redArg(v_ctors_2991_);
v___x_2993_ = lean_nat_dec_eq(v___x_2992_, v_val_2987_);
lean_dec(v___x_2992_);
if (v___x_2993_ == 0)
{
uint8_t v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3005_; 
v___x_2994_ = 1;
lean_inc(v_name_2926_);
v___x_2995_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2926_, v___x_2994_);
v___x_2996_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__7));
v___x_2997_ = lean_string_append(v___x_2995_, v___x_2996_);
v___x_2998_ = l_Nat_reprFast(v_val_2987_);
v___x_2999_ = lean_string_append(v___x_2997_, v___x_2998_);
lean_dec_ref(v___x_2998_);
v___x_3000_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__6));
v___x_3001_ = lean_string_append(v___x_2999_, v___x_3000_);
v___x_3002_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3002_, 0, v___x_3001_);
v___x_3003_ = l_Lean_MessageData_ofFormat(v___x_3002_);
if (v_isShared_2990_ == 0)
{
lean_ctor_set(v___x_2989_, 0, v___x_3003_);
v___x_3005_ = v___x_2989_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v___x_3003_);
v___x_3005_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
lean_object* v___x_3006_; 
lean_inc(v_goal_2927_);
lean_inc(v_name_2926_);
v___x_3006_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2926_, v_goal_2927_, v___x_3005_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_dec_ref_known(v___x_3006_, 1);
v___y_2957_ = v___y_2930_;
v___y_2958_ = v___y_2931_;
v___y_2959_ = v___y_2932_;
v___y_2960_ = v___y_2933_;
goto v___jp_2956_;
}
else
{
lean_object* v_a_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3014_; 
lean_del_object(v___x_2954_);
lean_dec_ref(v_val_2952_);
lean_del_object(v___x_2950_);
lean_dec(v_us_2943_);
lean_dec(v_idx_2928_);
lean_dec(v_goal_2927_);
lean_dec(v_name_2926_);
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_3009_ = v___x_3006_;
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_a_3007_);
lean_dec(v___x_3006_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3012_; 
if (v_isShared_3010_ == 0)
{
v___x_3012_ = v___x_3009_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_a_3007_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
}
}
}
else
{
lean_del_object(v___x_2989_);
lean_dec(v_val_2987_);
v___y_2957_ = v___y_2930_;
v___y_2958_ = v___y_2931_;
v___y_2959_ = v___y_2932_;
v___y_2960_ = v___y_2933_;
goto v___jp_2956_;
}
}
}
else
{
lean_dec(v_expected_x3f_2929_);
v___y_2957_ = v___y_2930_;
v___y_2958_ = v___y_2931_;
v___y_2959_ = v___y_2932_;
v___y_2960_ = v___y_2933_;
goto v___jp_2956_;
}
v___jp_2956_:
{
lean_object* v_ctors_2961_; lean_object* v___x_2962_; uint8_t v___x_2963_; 
v_ctors_2961_ = lean_ctor_get(v_val_2952_, 4);
lean_inc(v_ctors_2961_);
lean_dec_ref(v_val_2952_);
v___x_2962_ = l_List_lengthTR___redArg(v_ctors_2961_);
v___x_2963_ = lean_nat_dec_lt(v_idx_2928_, v___x_2962_);
if (v___x_2963_ == 0)
{
lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2974_; 
lean_dec(v_ctors_2961_);
lean_dec(v_us_2943_);
v___x_2964_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__4));
v___x_2965_ = l_Nat_reprFast(v_idx_2928_);
v___x_2966_ = lean_string_append(v___x_2964_, v___x_2965_);
lean_dec_ref(v___x_2965_);
v___x_2967_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__5));
v___x_2968_ = lean_string_append(v___x_2966_, v___x_2967_);
v___x_2969_ = l_Nat_reprFast(v___x_2962_);
v___x_2970_ = lean_string_append(v___x_2968_, v___x_2969_);
lean_dec_ref(v___x_2969_);
v___x_2971_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__6));
v___x_2972_ = lean_string_append(v___x_2970_, v___x_2971_);
if (v_isShared_2955_ == 0)
{
lean_ctor_set_tag(v___x_2954_, 3);
lean_ctor_set(v___x_2954_, 0, v___x_2972_);
v___x_2974_ = v___x_2954_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v___x_2972_);
v___x_2974_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
lean_object* v___x_2975_; lean_object* v___x_2977_; 
v___x_2975_ = l_Lean_MessageData_ofFormat(v___x_2974_);
if (v_isShared_2951_ == 0)
{
lean_ctor_set(v___x_2950_, 0, v___x_2975_);
v___x_2977_ = v___x_2950_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v___x_2975_);
v___x_2977_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
lean_object* v___x_2978_; 
v___x_2978_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2926_, v_goal_2927_, v___x_2977_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
return v___x_2978_;
}
}
}
else
{
lean_object* v___x_2981_; lean_object* v___x_2982_; uint8_t v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
lean_dec(v___x_2962_);
lean_del_object(v___x_2954_);
lean_del_object(v___x_2950_);
lean_dec(v_name_2926_);
v___x_2981_ = l_List_get___redArg(v_ctors_2961_, v_idx_2928_);
lean_dec(v_ctors_2961_);
v___x_2982_ = l_Lean_mkConst(v___x_2981_, v_us_2943_);
v___x_2983_ = 0;
v___x_2984_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_2984_, 0, v___x_2983_);
lean_ctor_set_uint8(v___x_2984_, 1, v___x_2963_);
lean_ctor_set_uint8(v___x_2984_, 2, v___x_2946_);
lean_ctor_set_uint8(v___x_2984_, 3, v___x_2963_);
v___x_2985_ = lean_box(0);
v___x_2986_ = l_Lean_MVarId_apply(v_goal_2927_, v___x_2982_, v___x_2984_, v___x_2985_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
return v___x_2986_;
}
}
}
}
else
{
lean_del_object(v___x_2950_);
lean_dec(v_val_2948_);
lean_dec(v_us_2943_);
lean_dec(v_expected_x3f_2929_);
lean_dec(v_idx_2928_);
goto v___jp_2935_;
}
}
}
}
else
{
lean_dec_ref(v___x_2941_);
lean_dec(v_expected_x3f_2929_);
lean_dec(v_idx_2928_);
goto v___jp_2935_;
}
}
else
{
lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3026_; 
lean_dec(v_expected_x3f_2929_);
lean_dec(v_idx_2928_);
lean_dec(v_goal_2927_);
lean_dec(v_name_2926_);
v_a_3019_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3021_ = v___x_2939_;
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_dec(v___x_2939_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3024_; 
if (v_isShared_3022_ == 0)
{
v___x_3024_ = v___x_3021_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_a_3019_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
}
}
else
{
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3034_; 
lean_dec(v_expected_x3f_2929_);
lean_dec(v_idx_2928_);
lean_dec(v_goal_2927_);
lean_dec(v_name_2926_);
v_a_3027_ = lean_ctor_get(v___x_2938_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_2938_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_2938_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_2938_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3032_; 
if (v_isShared_3030_ == 0)
{
v___x_3032_ = v___x_3029_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_a_3027_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
return v___x_3032_;
}
}
}
v___jp_2935_:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; 
v___x_2936_ = lean_obj_once(&l_Lean_MVarId_nthConstructor___lam__0___closed__3, &l_Lean_MVarId_nthConstructor___lam__0___closed__3_once, _init_l_Lean_MVarId_nthConstructor___lam__0___closed__3);
v___x_2937_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2926_, v_goal_2927_, v___x_2936_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
return v___x_2937_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___lam__0___boxed(lean_object* v_name_3035_, lean_object* v_goal_3036_, lean_object* v_idx_3037_, lean_object* v_expected_x3f_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l_Lean_MVarId_nthConstructor___lam__0(v_name_3035_, v_goal_3036_, v_idx_3037_, v_expected_x3f_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_);
lean_dec(v___y_3042_);
lean_dec_ref(v___y_3041_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor(lean_object* v_name_3045_, lean_object* v_idx_3046_, lean_object* v_expected_x3f_3047_, lean_object* v_goal_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_){
_start:
{
lean_object* v___f_3054_; lean_object* v___x_3055_; 
lean_inc(v_goal_3048_);
v___f_3054_ = lean_alloc_closure((void*)(l_Lean_MVarId_nthConstructor___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3054_, 0, v_name_3045_);
lean_closure_set(v___f_3054_, 1, v_goal_3048_);
lean_closure_set(v___f_3054_, 2, v_idx_3046_);
lean_closure_set(v___f_3054_, 3, v_expected_x3f_3047_);
v___x_3055_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_goal_3048_, v___f_3054_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___boxed(lean_object* v_name_3056_, lean_object* v_idx_3057_, lean_object* v_expected_x3f_3058_, lean_object* v_goal_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_){
_start:
{
lean_object* v_res_3065_; 
v_res_3065_ = l_Lean_MVarId_nthConstructor(v_name_3056_, v_idx_3057_, v_expected_x3f_3058_, v_goal_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_);
lean_dec(v_a_3063_);
lean_dec_ref(v_a_3062_);
lean_dec(v_a_3061_);
lean_dec_ref(v_a_3060_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(lean_object* v_x_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_){
_start:
{
lean_object* v___x_3072_; 
v___x_3072_ = l_Lean_Meta_saveState___redArg(v___y_3068_, v___y_3070_);
if (lean_obj_tag(v___x_3072_) == 0)
{
lean_object* v_a_3073_; lean_object* v___x_3074_; 
v_a_3073_ = lean_ctor_get(v___x_3072_, 0);
lean_inc(v_a_3073_);
lean_dec_ref_known(v___x_3072_, 1);
lean_inc(v___y_3070_);
lean_inc_ref(v___y_3069_);
lean_inc(v___y_3068_);
lean_inc_ref(v___y_3067_);
v___x_3074_ = lean_apply_5(v_x_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, lean_box(0));
if (lean_obj_tag(v___x_3074_) == 0)
{
lean_object* v_a_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3083_; 
lean_dec(v_a_3073_);
v_a_3075_ = lean_ctor_get(v___x_3074_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_3074_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3077_ = v___x_3074_;
v_isShared_3078_ = v_isSharedCheck_3083_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_a_3075_);
lean_dec(v___x_3074_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3083_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3079_; lean_object* v___x_3081_; 
v___x_3079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3079_, 0, v_a_3075_);
if (v_isShared_3078_ == 0)
{
lean_ctor_set(v___x_3077_, 0, v___x_3079_);
v___x_3081_ = v___x_3077_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v___x_3079_);
v___x_3081_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
return v___x_3081_;
}
}
}
else
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3113_; 
v_a_3084_ = lean_ctor_get(v___x_3074_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v___x_3074_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3086_ = v___x_3074_;
v_isShared_3087_ = v_isSharedCheck_3113_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3074_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3113_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
uint8_t v___y_3089_; uint8_t v___x_3111_; 
v___x_3111_ = l_Lean_Exception_isInterrupt(v_a_3084_);
if (v___x_3111_ == 0)
{
uint8_t v___x_3112_; 
lean_inc(v_a_3084_);
v___x_3112_ = l_Lean_Exception_isRuntime(v_a_3084_);
v___y_3089_ = v___x_3112_;
goto v___jp_3088_;
}
else
{
v___y_3089_ = v___x_3111_;
goto v___jp_3088_;
}
v___jp_3088_:
{
if (v___y_3089_ == 0)
{
lean_object* v___x_3090_; 
lean_del_object(v___x_3086_);
lean_dec(v_a_3084_);
v___x_3090_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3073_, v___y_3068_, v___y_3070_);
if (lean_obj_tag(v___x_3090_) == 0)
{
lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3098_; 
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3098_ == 0)
{
lean_object* v_unused_3099_; 
v_unused_3099_ = lean_ctor_get(v___x_3090_, 0);
lean_dec(v_unused_3099_);
v___x_3092_ = v___x_3090_;
v_isShared_3093_ = v_isSharedCheck_3098_;
goto v_resetjp_3091_;
}
else
{
lean_dec(v___x_3090_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3098_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3094_; lean_object* v___x_3096_; 
v___x_3094_ = lean_box(0);
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 0, v___x_3094_);
v___x_3096_ = v___x_3092_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v___x_3094_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
else
{
lean_object* v_a_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3107_; 
v_a_3100_ = lean_ctor_get(v___x_3090_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3102_ = v___x_3090_;
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_a_3100_);
lean_dec(v___x_3090_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3105_; 
if (v_isShared_3103_ == 0)
{
v___x_3105_ = v___x_3102_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v_a_3100_);
v___x_3105_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
return v___x_3105_;
}
}
}
}
else
{
lean_object* v___x_3109_; 
lean_dec(v_a_3073_);
if (v_isShared_3087_ == 0)
{
v___x_3109_ = v___x_3086_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_a_3084_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
}
}
}
}
else
{
lean_object* v_a_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3121_; 
lean_dec_ref(v_x_3066_);
v_a_3114_ = lean_ctor_get(v___x_3072_, 0);
v_isSharedCheck_3121_ = !lean_is_exclusive(v___x_3072_);
if (v_isSharedCheck_3121_ == 0)
{
v___x_3116_ = v___x_3072_;
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_a_3114_);
lean_dec(v___x_3072_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3119_; 
if (v_isShared_3117_ == 0)
{
v___x_3119_ = v___x_3116_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_a_3114_);
v___x_3119_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
return v___x_3119_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg___boxed(lean_object* v_x_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_){
_start:
{
lean_object* v_res_3128_; 
v_res_3128_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v_x_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_);
lean_dec(v___y_3126_);
lean_dec_ref(v___y_3125_);
lean_dec(v___y_3124_);
lean_dec_ref(v___y_3123_);
return v_res_3128_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0(lean_object* v_00_u03b1_3129_, lean_object* v_x_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_){
_start:
{
lean_object* v___x_3136_; 
v___x_3136_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v_x_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
return v___x_3136_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___boxed(lean_object* v_00_u03b1_3137_, lean_object* v_x_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_){
_start:
{
lean_object* v_res_3144_; 
v_res_3144_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0(v_00_u03b1_3137_, v_x_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_);
lean_dec(v___y_3142_);
lean_dec_ref(v___y_3141_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
return v_res_3144_;
}
}
static lean_object* _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3146_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___lam__0___closed__0));
v___x_3147_ = l_Lean_stringToMessageData(v___x_3146_);
return v___x_3147_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___lam__0(lean_object* v_mvarId_3148_, lean_object* v___x_3149_, lean_object* v___x_3150_, lean_object* v___x_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_){
_start:
{
lean_object* v___x_3160_; 
v___x_3160_ = l_Lean_MVarId_apply(v_mvarId_3148_, v___x_3149_, v___x_3150_, v___x_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_);
if (lean_obj_tag(v___x_3160_) == 0)
{
lean_object* v_a_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3170_; 
v_a_3161_ = lean_ctor_get(v___x_3160_, 0);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3163_ = v___x_3160_;
v_isShared_3164_ = v_isSharedCheck_3170_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_a_3161_);
lean_dec(v___x_3160_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3170_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
if (lean_obj_tag(v_a_3161_) == 1)
{
lean_object* v_tail_3165_; 
v_tail_3165_ = lean_ctor_get(v_a_3161_, 1);
if (lean_obj_tag(v_tail_3165_) == 0)
{
lean_object* v_head_3166_; lean_object* v___x_3168_; 
v_head_3166_ = lean_ctor_get(v_a_3161_, 0);
lean_inc(v_head_3166_);
lean_dec_ref_known(v_a_3161_, 2);
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 0, v_head_3166_);
v___x_3168_ = v___x_3163_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_head_3166_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
else
{
lean_dec_ref_known(v_a_3161_, 2);
lean_del_object(v___x_3163_);
goto v___jp_3157_;
}
}
else
{
lean_del_object(v___x_3163_);
lean_dec(v_a_3161_);
goto v___jp_3157_;
}
}
}
else
{
lean_object* v_a_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3178_; 
v_a_3171_ = lean_ctor_get(v___x_3160_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3173_ = v___x_3160_;
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_a_3171_);
lean_dec(v___x_3160_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3176_; 
if (v_isShared_3174_ == 0)
{
v___x_3176_ = v___x_3173_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_a_3171_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
}
v___jp_3157_:
{
lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3158_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3159_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3158_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_);
return v___x_3159_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___lam__0___boxed(lean_object* v_mvarId_3179_, lean_object* v___x_3180_, lean_object* v___x_3181_, lean_object* v___x_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
lean_object* v_res_3188_; 
v_res_3188_ = l_Lean_MVarId_iffOfEq___lam__0(v_mvarId_3179_, v___x_3180_, v___x_3181_, v___x_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
return v_res_3188_;
}
}
static lean_object* _init_l_Lean_MVarId_iffOfEq___closed__2(void){
_start:
{
lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3192_ = lean_box(0);
v___x_3193_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___closed__1));
v___x_3194_ = l_Lean_mkConst(v___x_3193_, v___x_3192_);
return v___x_3194_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq(lean_object* v_mvarId_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_){
_start:
{
lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___f_3208_; lean_object* v___x_3209_; 
v___x_3205_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___closed__2, &l_Lean_MVarId_iffOfEq___closed__2_once, _init_l_Lean_MVarId_iffOfEq___closed__2);
v___x_3206_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___closed__3));
v___x_3207_ = lean_box(0);
lean_inc(v_mvarId_3199_);
v___f_3208_ = lean_alloc_closure((void*)(l_Lean_MVarId_iffOfEq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3208_, 0, v_mvarId_3199_);
lean_closure_set(v___f_3208_, 1, v___x_3205_);
lean_closure_set(v___f_3208_, 2, v___x_3206_);
lean_closure_set(v___f_3208_, 3, v___x_3207_);
v___x_3209_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3208_, v_a_3200_, v_a_3201_, v_a_3202_, v_a_3203_);
if (lean_obj_tag(v___x_3209_) == 0)
{
lean_object* v_a_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3221_; 
v_a_3210_ = lean_ctor_get(v___x_3209_, 0);
v_isSharedCheck_3221_ = !lean_is_exclusive(v___x_3209_);
if (v_isSharedCheck_3221_ == 0)
{
v___x_3212_ = v___x_3209_;
v_isShared_3213_ = v_isSharedCheck_3221_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_a_3210_);
lean_dec(v___x_3209_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3221_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
if (lean_obj_tag(v_a_3210_) == 0)
{
lean_object* v___x_3215_; 
if (v_isShared_3213_ == 0)
{
lean_ctor_set(v___x_3212_, 0, v_mvarId_3199_);
v___x_3215_ = v___x_3212_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_mvarId_3199_);
v___x_3215_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
return v___x_3215_;
}
}
else
{
lean_object* v_val_3217_; lean_object* v___x_3219_; 
lean_dec(v_mvarId_3199_);
v_val_3217_ = lean_ctor_get(v_a_3210_, 0);
lean_inc(v_val_3217_);
lean_dec_ref_known(v_a_3210_, 1);
if (v_isShared_3213_ == 0)
{
lean_ctor_set(v___x_3212_, 0, v_val_3217_);
v___x_3219_ = v___x_3212_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_val_3217_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
}
}
else
{
lean_object* v_a_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3229_; 
lean_dec(v_mvarId_3199_);
v_a_3222_ = lean_ctor_get(v___x_3209_, 0);
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_3209_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3224_ = v___x_3209_;
v_isShared_3225_ = v_isSharedCheck_3229_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_a_3222_);
lean_dec(v___x_3209_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3229_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v___x_3227_; 
if (v_isShared_3225_ == 0)
{
v___x_3227_ = v___x_3224_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v_a_3222_);
v___x_3227_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
return v___x_3227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___boxed(lean_object* v_mvarId_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_){
_start:
{
lean_object* v_res_3236_; 
v_res_3236_ = l_Lean_MVarId_iffOfEq(v_mvarId_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_);
lean_dec(v_a_3234_);
lean_dec_ref(v_a_3233_);
lean_dec(v_a_3232_);
lean_dec_ref(v_a_3231_);
return v_res_3236_;
}
}
static lean_object* _init_l_Lean_MVarId_propext___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; 
v___x_3240_ = lean_box(0);
v___x_3241_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__1));
v___x_3242_ = l_Lean_mkConst(v___x_3241_, v___x_3240_);
return v___x_3242_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___lam__0(lean_object* v_mvarId_3246_, uint8_t v___x_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_){
_start:
{
lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; uint8_t v___y_3261_; lean_object* v___y_3287_; lean_object* v___x_3325_; uint8_t v_transparency_3326_; uint8_t v___x_3327_; 
v___x_3325_ = l_Lean_Meta_Context_config(v___y_3248_);
v_transparency_3326_ = lean_ctor_get_uint8(v___x_3325_, 9);
lean_dec_ref(v___x_3325_);
v___x_3327_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3326_, v___x_3247_);
if (v___x_3327_ == 0)
{
lean_object* v_keyedConfig_3328_; uint8_t v_trackZetaDelta_3329_; lean_object* v_zetaDeltaSet_3330_; lean_object* v_lctx_3331_; lean_object* v_localInstances_3332_; lean_object* v_defEqCtx_x3f_3333_; lean_object* v_synthPendingDepth_3334_; lean_object* v_customCanUnfoldPredicate_x3f_3335_; uint8_t v_univApprox_3336_; uint8_t v_inTypeClassResolution_3337_; uint8_t v_cacheInferType_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; 
v_keyedConfig_3328_ = lean_ctor_get(v___y_3248_, 0);
v_trackZetaDelta_3329_ = lean_ctor_get_uint8(v___y_3248_, sizeof(void*)*7);
v_zetaDeltaSet_3330_ = lean_ctor_get(v___y_3248_, 1);
v_lctx_3331_ = lean_ctor_get(v___y_3248_, 2);
v_localInstances_3332_ = lean_ctor_get(v___y_3248_, 3);
v_defEqCtx_x3f_3333_ = lean_ctor_get(v___y_3248_, 4);
v_synthPendingDepth_3334_ = lean_ctor_get(v___y_3248_, 5);
v_customCanUnfoldPredicate_x3f_3335_ = lean_ctor_get(v___y_3248_, 6);
v_univApprox_3336_ = lean_ctor_get_uint8(v___y_3248_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3337_ = lean_ctor_get_uint8(v___y_3248_, sizeof(void*)*7 + 2);
v_cacheInferType_3338_ = lean_ctor_get_uint8(v___y_3248_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3328_);
v___x_3339_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3247_, v_keyedConfig_3328_);
lean_inc(v_customCanUnfoldPredicate_x3f_3335_);
lean_inc(v_synthPendingDepth_3334_);
lean_inc(v_defEqCtx_x3f_3333_);
lean_inc_ref(v_localInstances_3332_);
lean_inc_ref(v_lctx_3331_);
lean_inc(v_zetaDeltaSet_3330_);
v___x_3340_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3340_, 0, v___x_3339_);
lean_ctor_set(v___x_3340_, 1, v_zetaDeltaSet_3330_);
lean_ctor_set(v___x_3340_, 2, v_lctx_3331_);
lean_ctor_set(v___x_3340_, 3, v_localInstances_3332_);
lean_ctor_set(v___x_3340_, 4, v_defEqCtx_x3f_3333_);
lean_ctor_set(v___x_3340_, 5, v_synthPendingDepth_3334_);
lean_ctor_set(v___x_3340_, 6, v_customCanUnfoldPredicate_x3f_3335_);
lean_ctor_set_uint8(v___x_3340_, sizeof(void*)*7, v_trackZetaDelta_3329_);
lean_ctor_set_uint8(v___x_3340_, sizeof(void*)*7 + 1, v_univApprox_3336_);
lean_ctor_set_uint8(v___x_3340_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3337_);
lean_ctor_set_uint8(v___x_3340_, sizeof(void*)*7 + 3, v_cacheInferType_3338_);
lean_inc(v_mvarId_3246_);
v___x_3341_ = l_Lean_MVarId_getType_x27(v_mvarId_3246_, v___x_3340_, v___y_3249_, v___y_3250_, v___y_3251_);
lean_dec_ref_known(v___x_3340_, 7);
v___y_3287_ = v___x_3341_;
goto v___jp_3286_;
}
else
{
lean_object* v___x_3342_; 
lean_inc(v_mvarId_3246_);
v___x_3342_ = l_Lean_MVarId_getType_x27(v_mvarId_3246_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
v___y_3287_ = v___x_3342_;
goto v___jp_3286_;
}
v___jp_3253_:
{
lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3258_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3259_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3258_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_);
lean_dec_ref(v___y_3254_);
return v___x_3259_;
}
v___jp_3260_:
{
lean_object* v___x_3262_; uint8_t v___x_3263_; uint8_t v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; 
v___x_3262_ = lean_obj_once(&l_Lean_MVarId_propext___lam__0___closed__2, &l_Lean_MVarId_propext___lam__0___closed__2_once, _init_l_Lean_MVarId_propext___lam__0___closed__2);
v___x_3263_ = 0;
v___x_3264_ = 0;
v___x_3265_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3265_, 0, v___x_3263_);
lean_ctor_set_uint8(v___x_3265_, 1, v___y_3261_);
lean_ctor_set_uint8(v___x_3265_, 2, v___x_3264_);
lean_ctor_set_uint8(v___x_3265_, 3, v___y_3261_);
v___x_3266_ = lean_box(0);
v___x_3267_ = l_Lean_MVarId_apply(v_mvarId_3246_, v___x_3262_, v___x_3265_, v___x_3266_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
if (lean_obj_tag(v___x_3267_) == 0)
{
lean_object* v_a_3268_; lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3277_; 
v_a_3268_ = lean_ctor_get(v___x_3267_, 0);
v_isSharedCheck_3277_ = !lean_is_exclusive(v___x_3267_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3270_ = v___x_3267_;
v_isShared_3271_ = v_isSharedCheck_3277_;
goto v_resetjp_3269_;
}
else
{
lean_inc(v_a_3268_);
lean_dec(v___x_3267_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3277_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
if (lean_obj_tag(v_a_3268_) == 1)
{
lean_object* v_tail_3272_; 
v_tail_3272_ = lean_ctor_get(v_a_3268_, 1);
if (lean_obj_tag(v_tail_3272_) == 0)
{
lean_object* v_head_3273_; lean_object* v___x_3275_; 
lean_dec_ref(v___y_3248_);
v_head_3273_ = lean_ctor_get(v_a_3268_, 0);
lean_inc(v_head_3273_);
lean_dec_ref_known(v_a_3268_, 2);
if (v_isShared_3271_ == 0)
{
lean_ctor_set(v___x_3270_, 0, v_head_3273_);
v___x_3275_ = v___x_3270_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_head_3273_);
v___x_3275_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
return v___x_3275_;
}
}
else
{
lean_dec_ref_known(v_a_3268_, 2);
lean_del_object(v___x_3270_);
v___y_3254_ = v___y_3248_;
v___y_3255_ = v___y_3249_;
v___y_3256_ = v___y_3250_;
v___y_3257_ = v___y_3251_;
goto v___jp_3253_;
}
}
else
{
lean_del_object(v___x_3270_);
lean_dec(v_a_3268_);
v___y_3254_ = v___y_3248_;
v___y_3255_ = v___y_3249_;
v___y_3256_ = v___y_3250_;
v___y_3257_ = v___y_3251_;
goto v___jp_3253_;
}
}
}
else
{
lean_object* v_a_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3285_; 
lean_dec_ref(v___y_3248_);
v_a_3278_ = lean_ctor_get(v___x_3267_, 0);
v_isSharedCheck_3285_ = !lean_is_exclusive(v___x_3267_);
if (v_isSharedCheck_3285_ == 0)
{
v___x_3280_ = v___x_3267_;
v_isShared_3281_ = v_isSharedCheck_3285_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_a_3278_);
lean_dec(v___x_3267_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3285_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v___x_3283_; 
if (v_isShared_3281_ == 0)
{
v___x_3283_ = v___x_3280_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v_a_3278_);
v___x_3283_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
return v___x_3283_;
}
}
}
}
v___jp_3286_:
{
if (lean_obj_tag(v___y_3287_) == 0)
{
lean_object* v_a_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; uint8_t v___x_3291_; 
v_a_3288_ = lean_ctor_get(v___y_3287_, 0);
lean_inc(v_a_3288_);
lean_dec_ref_known(v___y_3287_, 1);
v___x_3289_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__4));
v___x_3290_ = lean_unsigned_to_nat(3u);
v___x_3291_ = l_Lean_Expr_isAppOfArity(v_a_3288_, v___x_3289_, v___x_3290_);
if (v___x_3291_ == 0)
{
lean_object* v___x_3292_; lean_object* v___x_3293_; 
lean_dec(v_a_3288_);
lean_dec(v_mvarId_3246_);
v___x_3292_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3293_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3292_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
lean_dec_ref(v___y_3248_);
return v___x_3293_;
}
else
{
lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3294_ = l_Lean_Expr_appFn_x21(v_a_3288_);
lean_dec(v_a_3288_);
v___x_3295_ = l_Lean_Expr_appArg_x21(v___x_3294_);
lean_dec_ref(v___x_3294_);
v___x_3296_ = l_Lean_Meta_isProp(v___x_3295_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_object* v_a_3297_; uint8_t v___x_3298_; 
v_a_3297_ = lean_ctor_get(v___x_3296_, 0);
lean_inc(v_a_3297_);
lean_dec_ref_known(v___x_3296_, 1);
v___x_3298_ = lean_unbox(v_a_3297_);
lean_dec(v_a_3297_);
if (v___x_3298_ == 0)
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v_a_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3308_; 
lean_dec(v_mvarId_3246_);
v___x_3299_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3300_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3299_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
lean_dec_ref(v___y_3248_);
v_a_3301_ = lean_ctor_get(v___x_3300_, 0);
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_3300_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3303_ = v___x_3300_;
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_a_3301_);
lean_dec(v___x_3300_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v___x_3306_; 
if (v_isShared_3304_ == 0)
{
v___x_3306_ = v___x_3303_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v_a_3301_);
v___x_3306_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
return v___x_3306_;
}
}
}
else
{
v___y_3261_ = v___x_3291_;
goto v___jp_3260_;
}
}
else
{
lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3316_; 
lean_dec_ref(v___y_3248_);
lean_dec(v_mvarId_3246_);
v_a_3309_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3311_ = v___x_3296_;
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_a_3309_);
lean_dec(v___x_3296_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3314_; 
if (v_isShared_3312_ == 0)
{
v___x_3314_ = v___x_3311_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_a_3309_);
v___x_3314_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
return v___x_3314_;
}
}
}
}
}
else
{
lean_object* v_a_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3324_; 
lean_dec_ref(v___y_3248_);
lean_dec(v_mvarId_3246_);
v_a_3317_ = lean_ctor_get(v___y_3287_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___y_3287_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3319_ = v___y_3287_;
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_a_3317_);
lean_dec(v___y_3287_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3322_; 
if (v_isShared_3320_ == 0)
{
v___x_3322_ = v___x_3319_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_a_3317_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___lam__0___boxed(lean_object* v_mvarId_3343_, lean_object* v___x_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_){
_start:
{
uint8_t v___x_2525__boxed_3350_; lean_object* v_res_3351_; 
v___x_2525__boxed_3350_ = lean_unbox(v___x_3344_);
v_res_3351_ = l_Lean_MVarId_propext___lam__0(v_mvarId_3343_, v___x_2525__boxed_3350_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3347_);
lean_dec(v___y_3346_);
return v_res_3351_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext(lean_object* v_mvarId_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_){
_start:
{
uint8_t v___x_3358_; lean_object* v___x_3359_; lean_object* v___f_3360_; lean_object* v___x_3361_; 
v___x_3358_ = 2;
v___x_3359_ = lean_box(v___x_3358_);
lean_inc(v_mvarId_3352_);
v___f_3360_ = lean_alloc_closure((void*)(l_Lean_MVarId_propext___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3360_, 0, v_mvarId_3352_);
lean_closure_set(v___f_3360_, 1, v___x_3359_);
v___x_3361_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3360_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v_a_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3373_; 
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3373_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3373_ == 0)
{
v___x_3364_ = v___x_3361_;
v_isShared_3365_ = v_isSharedCheck_3373_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_a_3362_);
lean_dec(v___x_3361_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3373_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
if (lean_obj_tag(v_a_3362_) == 0)
{
lean_object* v___x_3367_; 
if (v_isShared_3365_ == 0)
{
lean_ctor_set(v___x_3364_, 0, v_mvarId_3352_);
v___x_3367_ = v___x_3364_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_mvarId_3352_);
v___x_3367_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
return v___x_3367_;
}
}
else
{
lean_object* v_val_3369_; lean_object* v___x_3371_; 
lean_dec(v_mvarId_3352_);
v_val_3369_ = lean_ctor_get(v_a_3362_, 0);
lean_inc(v_val_3369_);
lean_dec_ref_known(v_a_3362_, 1);
if (v_isShared_3365_ == 0)
{
lean_ctor_set(v___x_3364_, 0, v_val_3369_);
v___x_3371_ = v___x_3364_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v_val_3369_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
return v___x_3371_;
}
}
}
}
else
{
lean_object* v_a_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3381_; 
lean_dec(v_mvarId_3352_);
v_a_3374_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3376_ = v___x_3361_;
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_a_3374_);
lean_dec(v___x_3361_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v___x_3379_; 
if (v_isShared_3377_ == 0)
{
v___x_3379_ = v___x_3376_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_a_3374_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___boxed(lean_object* v_mvarId_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_){
_start:
{
lean_object* v_res_3388_; 
v_res_3388_ = l_Lean_MVarId_propext(v_mvarId_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_);
lean_dec(v_a_3386_);
lean_dec_ref(v_a_3385_);
lean_dec(v_a_3384_);
lean_dec_ref(v_a_3383_);
return v_res_3388_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0(lean_object* v_mvarId_3395_, lean_object* v___x_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_){
_start:
{
lean_object* v___y_3403_; lean_object* v___x_3447_; 
lean_inc(v_mvarId_3395_);
v___x_3447_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3395_, v___x_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
if (lean_obj_tag(v___x_3447_) == 0)
{
lean_object* v___x_3448_; uint8_t v_transparency_3449_; uint8_t v___x_3450_; uint8_t v___x_3451_; 
lean_dec_ref_known(v___x_3447_, 1);
v___x_3448_ = l_Lean_Meta_Context_config(v___y_3397_);
v_transparency_3449_ = lean_ctor_get_uint8(v___x_3448_, 9);
lean_dec_ref(v___x_3448_);
v___x_3450_ = 2;
v___x_3451_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3449_, v___x_3450_);
if (v___x_3451_ == 0)
{
lean_object* v_keyedConfig_3452_; uint8_t v_trackZetaDelta_3453_; lean_object* v_zetaDeltaSet_3454_; lean_object* v_lctx_3455_; lean_object* v_localInstances_3456_; lean_object* v_defEqCtx_x3f_3457_; lean_object* v_synthPendingDepth_3458_; lean_object* v_customCanUnfoldPredicate_x3f_3459_; uint8_t v_univApprox_3460_; uint8_t v_inTypeClassResolution_3461_; uint8_t v_cacheInferType_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; 
v_keyedConfig_3452_ = lean_ctor_get(v___y_3397_, 0);
v_trackZetaDelta_3453_ = lean_ctor_get_uint8(v___y_3397_, sizeof(void*)*7);
v_zetaDeltaSet_3454_ = lean_ctor_get(v___y_3397_, 1);
v_lctx_3455_ = lean_ctor_get(v___y_3397_, 2);
v_localInstances_3456_ = lean_ctor_get(v___y_3397_, 3);
v_defEqCtx_x3f_3457_ = lean_ctor_get(v___y_3397_, 4);
v_synthPendingDepth_3458_ = lean_ctor_get(v___y_3397_, 5);
v_customCanUnfoldPredicate_x3f_3459_ = lean_ctor_get(v___y_3397_, 6);
v_univApprox_3460_ = lean_ctor_get_uint8(v___y_3397_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3461_ = lean_ctor_get_uint8(v___y_3397_, sizeof(void*)*7 + 2);
v_cacheInferType_3462_ = lean_ctor_get_uint8(v___y_3397_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3452_);
v___x_3463_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3450_, v_keyedConfig_3452_);
lean_inc(v_customCanUnfoldPredicate_x3f_3459_);
lean_inc(v_synthPendingDepth_3458_);
lean_inc(v_defEqCtx_x3f_3457_);
lean_inc_ref(v_localInstances_3456_);
lean_inc_ref(v_lctx_3455_);
lean_inc(v_zetaDeltaSet_3454_);
v___x_3464_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3464_, 0, v___x_3463_);
lean_ctor_set(v___x_3464_, 1, v_zetaDeltaSet_3454_);
lean_ctor_set(v___x_3464_, 2, v_lctx_3455_);
lean_ctor_set(v___x_3464_, 3, v_localInstances_3456_);
lean_ctor_set(v___x_3464_, 4, v_defEqCtx_x3f_3457_);
lean_ctor_set(v___x_3464_, 5, v_synthPendingDepth_3458_);
lean_ctor_set(v___x_3464_, 6, v_customCanUnfoldPredicate_x3f_3459_);
lean_ctor_set_uint8(v___x_3464_, sizeof(void*)*7, v_trackZetaDelta_3453_);
lean_ctor_set_uint8(v___x_3464_, sizeof(void*)*7 + 1, v_univApprox_3460_);
lean_ctor_set_uint8(v___x_3464_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3461_);
lean_ctor_set_uint8(v___x_3464_, sizeof(void*)*7 + 3, v_cacheInferType_3462_);
lean_inc(v_mvarId_3395_);
v___x_3465_ = l_Lean_MVarId_getType_x27(v_mvarId_3395_, v___x_3464_, v___y_3398_, v___y_3399_, v___y_3400_);
lean_dec_ref_known(v___x_3464_, 7);
v___y_3403_ = v___x_3465_;
goto v___jp_3402_;
}
else
{
lean_object* v___x_3466_; 
lean_inc(v_mvarId_3395_);
v___x_3466_ = l_Lean_MVarId_getType_x27(v_mvarId_3395_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
v___y_3403_ = v___x_3466_;
goto v___jp_3402_;
}
}
else
{
lean_object* v_a_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3474_; 
lean_dec_ref(v___y_3397_);
lean_dec(v_mvarId_3395_);
v_a_3467_ = lean_ctor_get(v___x_3447_, 0);
v_isSharedCheck_3474_ = !lean_is_exclusive(v___x_3447_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3469_ = v___x_3447_;
v_isShared_3470_ = v_isSharedCheck_3474_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_a_3467_);
lean_dec(v___x_3447_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3474_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___x_3472_; 
if (v_isShared_3470_ == 0)
{
v___x_3472_ = v___x_3469_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v_a_3467_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
return v___x_3472_;
}
}
}
v___jp_3402_:
{
if (lean_obj_tag(v___y_3403_) == 0)
{
lean_object* v_a_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; uint8_t v___x_3407_; 
v_a_3404_ = lean_ctor_get(v___y_3403_, 0);
lean_inc(v_a_3404_);
lean_dec_ref_known(v___y_3403_, 1);
v___x_3405_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__1));
v___x_3406_ = lean_unsigned_to_nat(4u);
v___x_3407_ = l_Lean_Expr_isAppOfArity(v_a_3404_, v___x_3405_, v___x_3406_);
if (v___x_3407_ == 0)
{
lean_object* v___x_3408_; lean_object* v___x_3409_; 
lean_dec(v_a_3404_);
lean_dec(v_mvarId_3395_);
v___x_3408_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3409_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3408_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
lean_dec_ref(v___y_3397_);
return v___x_3409_;
}
else
{
lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; 
v___x_3410_ = l_Lean_Expr_appFn_x21(v_a_3404_);
v___x_3411_ = l_Lean_Expr_appFn_x21(v___x_3410_);
lean_dec_ref(v___x_3410_);
v___x_3412_ = l_Lean_Expr_appArg_x21(v___x_3411_);
lean_dec_ref(v___x_3411_);
v___x_3413_ = l_Lean_Expr_appArg_x21(v_a_3404_);
lean_dec(v_a_3404_);
v___x_3414_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__3));
v___x_3415_ = lean_unsigned_to_nat(2u);
v___x_3416_ = lean_mk_empty_array_with_capacity(v___x_3415_);
v___x_3417_ = lean_array_push(v___x_3416_, v___x_3412_);
v___x_3418_ = lean_array_push(v___x_3417_, v___x_3413_);
v___x_3419_ = l_Lean_Meta_mkAppM(v___x_3414_, v___x_3418_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
lean_dec_ref(v___y_3397_);
if (lean_obj_tag(v___x_3419_) == 0)
{
lean_object* v_a_3420_; lean_object* v___x_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3429_; 
v_a_3420_ = lean_ctor_get(v___x_3419_, 0);
lean_inc(v_a_3420_);
lean_dec_ref_known(v___x_3419_, 1);
v___x_3421_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_3395_, v_a_3420_, v___y_3398_);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3421_);
if (v_isSharedCheck_3429_ == 0)
{
lean_object* v_unused_3430_; 
v_unused_3430_ = lean_ctor_get(v___x_3421_, 0);
lean_dec(v_unused_3430_);
v___x_3423_ = v___x_3421_;
v_isShared_3424_ = v_isSharedCheck_3429_;
goto v_resetjp_3422_;
}
else
{
lean_dec(v___x_3421_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3429_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___x_3425_; lean_object* v___x_3427_; 
v___x_3425_ = lean_box(v___x_3407_);
if (v_isShared_3424_ == 0)
{
lean_ctor_set(v___x_3423_, 0, v___x_3425_);
v___x_3427_ = v___x_3423_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v___x_3425_);
v___x_3427_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
return v___x_3427_;
}
}
}
else
{
lean_object* v_a_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3438_; 
lean_dec(v_mvarId_3395_);
v_a_3431_ = lean_ctor_get(v___x_3419_, 0);
v_isSharedCheck_3438_ = !lean_is_exclusive(v___x_3419_);
if (v_isSharedCheck_3438_ == 0)
{
v___x_3433_ = v___x_3419_;
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_a_3431_);
lean_dec(v___x_3419_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3436_; 
if (v_isShared_3434_ == 0)
{
v___x_3436_ = v___x_3433_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v_a_3431_);
v___x_3436_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
return v___x_3436_;
}
}
}
}
}
else
{
lean_object* v_a_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3446_; 
lean_dec_ref(v___y_3397_);
lean_dec(v_mvarId_3395_);
v_a_3439_ = lean_ctor_get(v___y_3403_, 0);
v_isSharedCheck_3446_ = !lean_is_exclusive(v___y_3403_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3441_ = v___y_3403_;
v_isShared_3442_ = v_isSharedCheck_3446_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_a_3439_);
lean_dec(v___y_3403_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3446_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v___x_3444_; 
if (v_isShared_3442_ == 0)
{
v___x_3444_ = v___x_3441_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_a_3439_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0___boxed(lean_object* v_mvarId_3475_, lean_object* v___x_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_){
_start:
{
lean_object* v_res_3482_; 
v_res_3482_ = l_Lean_MVarId_proofIrrelHeq___lam__0(v_mvarId_3475_, v___x_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_);
lean_dec(v___y_3480_);
lean_dec_ref(v___y_3479_);
lean_dec(v___y_3478_);
return v_res_3482_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__1(lean_object* v___f_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_){
_start:
{
lean_object* v___x_3489_; 
v___x_3489_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_);
if (lean_obj_tag(v___x_3489_) == 0)
{
lean_object* v_a_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3503_; 
v_a_3490_ = lean_ctor_get(v___x_3489_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3492_ = v___x_3489_;
v_isShared_3493_ = v_isSharedCheck_3503_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_a_3490_);
lean_dec(v___x_3489_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3503_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
if (lean_obj_tag(v_a_3490_) == 0)
{
uint8_t v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3497_; 
v___x_3494_ = 0;
v___x_3495_ = lean_box(v___x_3494_);
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 0, v___x_3495_);
v___x_3497_ = v___x_3492_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v___x_3495_);
v___x_3497_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
return v___x_3497_;
}
}
else
{
lean_object* v_val_3499_; lean_object* v___x_3501_; 
v_val_3499_ = lean_ctor_get(v_a_3490_, 0);
lean_inc(v_val_3499_);
lean_dec_ref_known(v_a_3490_, 1);
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 0, v_val_3499_);
v___x_3501_ = v___x_3492_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_val_3499_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
}
else
{
lean_object* v_a_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3511_; 
v_a_3504_ = lean_ctor_get(v___x_3489_, 0);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3506_ = v___x_3489_;
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_a_3504_);
lean_dec(v___x_3489_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v___x_3509_; 
if (v_isShared_3507_ == 0)
{
v___x_3509_ = v___x_3506_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_a_3504_);
v___x_3509_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
return v___x_3509_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__1___boxed(lean_object* v___f_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_){
_start:
{
lean_object* v_res_3518_; 
v_res_3518_ = l_Lean_MVarId_proofIrrelHeq___lam__1(v___f_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_);
lean_dec(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3513_);
return v_res_3518_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq(lean_object* v_mvarId_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_){
_start:
{
lean_object* v___x_3528_; lean_object* v___f_3529_; lean_object* v___f_3530_; lean_object* v___x_3531_; 
v___x_3528_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___closed__1));
lean_inc(v_mvarId_3522_);
v___f_3529_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3529_, 0, v_mvarId_3522_);
lean_closure_set(v___f_3529_, 1, v___x_3528_);
v___f_3530_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__1___boxed), 6, 1);
lean_closure_set(v___f_3530_, 0, v___f_3529_);
v___x_3531_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_3522_, v___f_3530_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_);
return v___x_3531_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___boxed(lean_object* v_mvarId_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_){
_start:
{
lean_object* v_res_3538_; 
v_res_3538_ = l_Lean_MVarId_proofIrrelHeq(v_mvarId_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_);
lean_dec(v_a_3536_);
lean_dec_ref(v_a_3535_);
lean_dec(v_a_3534_);
lean_dec_ref(v_a_3533_);
return v_res_3538_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___lam__0(lean_object* v_mvarId_3543_, lean_object* v___x_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_){
_start:
{
lean_object* v___y_3551_; lean_object* v___x_3594_; 
lean_inc(v_mvarId_3543_);
v___x_3594_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3543_, v___x_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
if (lean_obj_tag(v___x_3594_) == 0)
{
lean_object* v___x_3595_; uint8_t v_transparency_3596_; uint8_t v___x_3597_; uint8_t v___x_3598_; 
lean_dec_ref_known(v___x_3594_, 1);
v___x_3595_ = l_Lean_Meta_Context_config(v___y_3545_);
v_transparency_3596_ = lean_ctor_get_uint8(v___x_3595_, 9);
lean_dec_ref(v___x_3595_);
v___x_3597_ = 2;
v___x_3598_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3596_, v___x_3597_);
if (v___x_3598_ == 0)
{
lean_object* v_keyedConfig_3599_; uint8_t v_trackZetaDelta_3600_; lean_object* v_zetaDeltaSet_3601_; lean_object* v_lctx_3602_; lean_object* v_localInstances_3603_; lean_object* v_defEqCtx_x3f_3604_; lean_object* v_synthPendingDepth_3605_; lean_object* v_customCanUnfoldPredicate_x3f_3606_; uint8_t v_univApprox_3607_; uint8_t v_inTypeClassResolution_3608_; uint8_t v_cacheInferType_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; 
v_keyedConfig_3599_ = lean_ctor_get(v___y_3545_, 0);
v_trackZetaDelta_3600_ = lean_ctor_get_uint8(v___y_3545_, sizeof(void*)*7);
v_zetaDeltaSet_3601_ = lean_ctor_get(v___y_3545_, 1);
v_lctx_3602_ = lean_ctor_get(v___y_3545_, 2);
v_localInstances_3603_ = lean_ctor_get(v___y_3545_, 3);
v_defEqCtx_x3f_3604_ = lean_ctor_get(v___y_3545_, 4);
v_synthPendingDepth_3605_ = lean_ctor_get(v___y_3545_, 5);
v_customCanUnfoldPredicate_x3f_3606_ = lean_ctor_get(v___y_3545_, 6);
v_univApprox_3607_ = lean_ctor_get_uint8(v___y_3545_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3608_ = lean_ctor_get_uint8(v___y_3545_, sizeof(void*)*7 + 2);
v_cacheInferType_3609_ = lean_ctor_get_uint8(v___y_3545_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3599_);
v___x_3610_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3597_, v_keyedConfig_3599_);
lean_inc(v_customCanUnfoldPredicate_x3f_3606_);
lean_inc(v_synthPendingDepth_3605_);
lean_inc(v_defEqCtx_x3f_3604_);
lean_inc_ref(v_localInstances_3603_);
lean_inc_ref(v_lctx_3602_);
lean_inc(v_zetaDeltaSet_3601_);
v___x_3611_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3611_, 0, v___x_3610_);
lean_ctor_set(v___x_3611_, 1, v_zetaDeltaSet_3601_);
lean_ctor_set(v___x_3611_, 2, v_lctx_3602_);
lean_ctor_set(v___x_3611_, 3, v_localInstances_3603_);
lean_ctor_set(v___x_3611_, 4, v_defEqCtx_x3f_3604_);
lean_ctor_set(v___x_3611_, 5, v_synthPendingDepth_3605_);
lean_ctor_set(v___x_3611_, 6, v_customCanUnfoldPredicate_x3f_3606_);
lean_ctor_set_uint8(v___x_3611_, sizeof(void*)*7, v_trackZetaDelta_3600_);
lean_ctor_set_uint8(v___x_3611_, sizeof(void*)*7 + 1, v_univApprox_3607_);
lean_ctor_set_uint8(v___x_3611_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3608_);
lean_ctor_set_uint8(v___x_3611_, sizeof(void*)*7 + 3, v_cacheInferType_3609_);
lean_inc(v_mvarId_3543_);
v___x_3612_ = l_Lean_MVarId_getType_x27(v_mvarId_3543_, v___x_3611_, v___y_3546_, v___y_3547_, v___y_3548_);
lean_dec_ref_known(v___x_3611_, 7);
v___y_3551_ = v___x_3612_;
goto v___jp_3550_;
}
else
{
lean_object* v___x_3613_; 
lean_inc(v_mvarId_3543_);
v___x_3613_ = l_Lean_MVarId_getType_x27(v_mvarId_3543_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
v___y_3551_ = v___x_3613_;
goto v___jp_3550_;
}
}
else
{
lean_object* v_a_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3621_; 
lean_dec_ref(v___y_3545_);
lean_dec(v_mvarId_3543_);
v_a_3614_ = lean_ctor_get(v___x_3594_, 0);
v_isSharedCheck_3621_ = !lean_is_exclusive(v___x_3594_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3616_ = v___x_3594_;
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_a_3614_);
lean_dec(v___x_3594_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___x_3619_; 
if (v_isShared_3617_ == 0)
{
v___x_3619_ = v___x_3616_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_a_3614_);
v___x_3619_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
return v___x_3619_;
}
}
}
v___jp_3550_:
{
if (lean_obj_tag(v___y_3551_) == 0)
{
lean_object* v_a_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; uint8_t v___x_3555_; 
v_a_3552_ = lean_ctor_get(v___y_3551_, 0);
lean_inc(v_a_3552_);
lean_dec_ref_known(v___y_3551_, 1);
v___x_3553_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__4));
v___x_3554_ = lean_unsigned_to_nat(3u);
v___x_3555_ = l_Lean_Expr_isAppOfArity(v_a_3552_, v___x_3553_, v___x_3554_);
if (v___x_3555_ == 0)
{
lean_object* v___x_3556_; lean_object* v___x_3557_; 
lean_dec(v_a_3552_);
lean_dec(v_mvarId_3543_);
v___x_3556_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3557_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3556_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
lean_dec_ref(v___y_3545_);
return v___x_3557_;
}
else
{
lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3558_ = l_Lean_Expr_appFn_x21(v_a_3552_);
v___x_3559_ = l_Lean_Expr_appArg_x21(v___x_3558_);
lean_dec_ref(v___x_3558_);
v___x_3560_ = l_Lean_Expr_appArg_x21(v_a_3552_);
lean_dec(v_a_3552_);
v___x_3561_ = ((lean_object*)(l_Lean_MVarId_subsingletonElim___lam__0___closed__1));
v___x_3562_ = lean_unsigned_to_nat(2u);
v___x_3563_ = lean_mk_empty_array_with_capacity(v___x_3562_);
v___x_3564_ = lean_array_push(v___x_3563_, v___x_3559_);
v___x_3565_ = lean_array_push(v___x_3564_, v___x_3560_);
v___x_3566_ = l_Lean_Meta_mkAppM(v___x_3561_, v___x_3565_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
lean_dec_ref(v___y_3545_);
if (lean_obj_tag(v___x_3566_) == 0)
{
lean_object* v_a_3567_; lean_object* v___x_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3576_; 
v_a_3567_ = lean_ctor_get(v___x_3566_, 0);
lean_inc(v_a_3567_);
lean_dec_ref_known(v___x_3566_, 1);
v___x_3568_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_3543_, v_a_3567_, v___y_3546_);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3568_);
if (v_isSharedCheck_3576_ == 0)
{
lean_object* v_unused_3577_; 
v_unused_3577_ = lean_ctor_get(v___x_3568_, 0);
lean_dec(v_unused_3577_);
v___x_3570_ = v___x_3568_;
v_isShared_3571_ = v_isSharedCheck_3576_;
goto v_resetjp_3569_;
}
else
{
lean_dec(v___x_3568_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3576_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___x_3572_; lean_object* v___x_3574_; 
v___x_3572_ = lean_box(v___x_3555_);
if (v_isShared_3571_ == 0)
{
lean_ctor_set(v___x_3570_, 0, v___x_3572_);
v___x_3574_ = v___x_3570_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v___x_3572_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
else
{
lean_object* v_a_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3585_; 
lean_dec(v_mvarId_3543_);
v_a_3578_ = lean_ctor_get(v___x_3566_, 0);
v_isSharedCheck_3585_ = !lean_is_exclusive(v___x_3566_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3580_ = v___x_3566_;
v_isShared_3581_ = v_isSharedCheck_3585_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_a_3578_);
lean_dec(v___x_3566_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3585_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v___x_3583_; 
if (v_isShared_3581_ == 0)
{
v___x_3583_ = v___x_3580_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v_a_3578_);
v___x_3583_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
return v___x_3583_;
}
}
}
}
}
else
{
lean_object* v_a_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3593_; 
lean_dec_ref(v___y_3545_);
lean_dec(v_mvarId_3543_);
v_a_3586_ = lean_ctor_get(v___y_3551_, 0);
v_isSharedCheck_3593_ = !lean_is_exclusive(v___y_3551_);
if (v_isSharedCheck_3593_ == 0)
{
v___x_3588_ = v___y_3551_;
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_a_3586_);
lean_dec(v___y_3551_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
lean_object* v___x_3591_; 
if (v_isShared_3589_ == 0)
{
v___x_3591_ = v___x_3588_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v_a_3586_);
v___x_3591_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
return v___x_3591_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___lam__0___boxed(lean_object* v_mvarId_3622_, lean_object* v___x_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_){
_start:
{
lean_object* v_res_3629_; 
v_res_3629_ = l_Lean_MVarId_subsingletonElim___lam__0(v_mvarId_3622_, v___x_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_);
lean_dec(v___y_3627_);
lean_dec_ref(v___y_3626_);
lean_dec(v___y_3625_);
return v_res_3629_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim(lean_object* v_mvarId_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_){
_start:
{
lean_object* v___x_3639_; lean_object* v___f_3640_; lean_object* v___f_3641_; lean_object* v___x_3642_; 
v___x_3639_ = ((lean_object*)(l_Lean_MVarId_subsingletonElim___closed__1));
lean_inc(v_mvarId_3633_);
v___f_3640_ = lean_alloc_closure((void*)(l_Lean_MVarId_subsingletonElim___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3640_, 0, v_mvarId_3633_);
lean_closure_set(v___f_3640_, 1, v___x_3639_);
v___f_3641_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__1___boxed), 6, 1);
lean_closure_set(v___f_3641_, 0, v___f_3640_);
v___x_3642_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_3633_, v___f_3641_, v_a_3634_, v_a_3635_, v_a_3636_, v_a_3637_);
return v___x_3642_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___boxed(lean_object* v_mvarId_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_){
_start:
{
lean_object* v_res_3649_; 
v_res_3649_ = l_Lean_MVarId_subsingletonElim(v_mvarId_3643_, v_a_3644_, v_a_3645_, v_a_3646_, v_a_3647_);
lean_dec(v_a_3647_);
lean_dec_ref(v_a_3646_);
lean_dec(v_a_3645_);
lean_dec_ref(v_a_3644_);
return v_res_3649_;
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
