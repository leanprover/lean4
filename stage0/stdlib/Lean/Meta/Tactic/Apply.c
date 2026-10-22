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
lean_object* v_snd_513_; lean_object* v_fst_514_; lean_object* v_fst_515_; lean_object* v_snd_516_; lean_object* v_a_517_; lean_object* v_a_519_; lean_object* v___y_527_; lean_object* v___x_588_; 
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
v___x_588_ = lean_infer_type(v_a_517_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v_a_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v_a_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_a_589_);
lean_dec_ref_known(v___x_588_, 1);
v___x_590_ = lean_box(0);
v___x_591_ = l_Lean_Meta_synthInstance(v_a_589_, v___x_590_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; lean_object* v___x_593_; lean_object* v___x_594_; uint8_t v___x_595_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
lean_inc(v_a_592_);
lean_dec_ref_known(v___x_591_, 1);
v___x_593_ = lean_array_get_size(v_snd_516_);
v___x_594_ = lean_unsigned_to_nat(0u);
v___x_595_ = lean_nat_dec_eq(v___x_593_, v___x_594_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = lean_box(0);
lean_inc(v_snd_516_);
v___x_597_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(v_a_592_, v_snd_516_, v_fst_514_, v___x_596_, v___x_511_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
v___y_527_ = v___x_597_;
goto v___jp_526_;
}
else
{
lean_object* v___x_598_; uint8_t v___x_599_; lean_object* v___x_600_; 
v___x_598_ = lean_box(0);
v___x_599_ = lean_unbox(v_fst_515_);
lean_inc(v_snd_516_);
v___x_600_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(v_a_592_, v_snd_516_, v_fst_514_, v___x_598_, v___x_599_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
v___y_527_ = v___x_600_;
goto v___jp_526_;
}
}
else
{
lean_object* v_a_601_; 
lean_dec(v_fst_514_);
v_a_601_ = lean_ctor_get(v___x_591_, 0);
lean_inc(v_a_601_);
lean_dec_ref_known(v___x_591_, 1);
v_a_519_ = v_a_601_;
goto v___jp_518_;
}
}
else
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_609_; 
lean_dec(v_snd_516_);
lean_dec(v_fst_515_);
lean_dec(v_fst_514_);
lean_dec(v_mvarId_490_);
lean_dec(v_tacticName_489_);
v_a_602_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_609_ == 0)
{
v___x_604_ = v___x_588_;
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_588_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_a_602_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
v___jp_518_:
{
uint8_t v___x_520_; 
v___x_520_ = l_Lean_Exception_isInterrupt(v_a_519_);
if (v___x_520_ == 0)
{
uint8_t v___x_521_; 
lean_inc_ref(v_a_519_);
v___x_521_ = l_Lean_Exception_isRuntime(v_a_519_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_522_, 0, v_a_519_);
lean_inc(v_a_517_);
v___x_523_ = lean_array_push(v_snd_516_, v_a_517_);
v_fst_506_ = v___x_522_;
v_fst_507_ = v_fst_515_;
v_snd_508_ = v___x_523_;
goto v___jp_505_;
}
else
{
lean_object* v___x_524_; 
lean_dec(v_snd_516_);
lean_dec(v_fst_515_);
lean_dec(v_mvarId_490_);
lean_dec(v_tacticName_489_);
v___x_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_524_, 0, v_a_519_);
return v___x_524_;
}
}
else
{
lean_object* v___x_525_; 
lean_dec(v_snd_516_);
lean_dec(v_fst_515_);
lean_dec(v_mvarId_490_);
lean_dec(v_tacticName_489_);
v___x_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_525_, 0, v_a_519_);
return v___x_525_;
}
}
v___jp_526_:
{
if (lean_obj_tag(v___y_527_) == 0)
{
lean_object* v_a_528_; lean_object* v_snd_529_; lean_object* v_snd_530_; lean_object* v_fst_531_; 
lean_dec(v_snd_516_);
lean_dec(v_fst_515_);
v_a_528_ = lean_ctor_get(v___y_527_, 0);
lean_inc(v_a_528_);
lean_dec_ref_known(v___y_527_, 1);
v_snd_529_ = lean_ctor_get(v_a_528_, 1);
lean_inc(v_snd_529_);
v_snd_530_ = lean_ctor_get(v_snd_529_, 1);
lean_inc(v_snd_530_);
v_fst_531_ = lean_ctor_get(v_a_528_, 0);
lean_inc(v_fst_531_);
lean_dec(v_a_528_);
if (lean_obj_tag(v_fst_531_) == 1)
{
lean_object* v_fst_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_582_; 
v_fst_532_ = lean_ctor_get(v_snd_529_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v_snd_529_);
if (v_isSharedCheck_582_ == 0)
{
lean_object* v_unused_583_; 
v_unused_583_ = lean_ctor_get(v_snd_529_, 1);
lean_dec(v_unused_583_);
v___x_534_ = v_snd_529_;
v_isShared_535_ = v_isSharedCheck_582_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_fst_532_);
lean_dec(v_snd_529_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_582_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v_fst_536_; lean_object* v_snd_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_581_; 
v_fst_536_ = lean_ctor_get(v_snd_530_, 0);
v_snd_537_ = lean_ctor_get(v_snd_530_, 1);
v_isSharedCheck_581_ = !lean_is_exclusive(v_snd_530_);
if (v_isSharedCheck_581_ == 0)
{
v___x_539_ = v_snd_530_;
v_isShared_540_ = v_isSharedCheck_581_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_snd_537_);
lean_inc(v_fst_536_);
lean_dec(v_snd_530_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_581_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v_val_541_; lean_object* v___x_542_; 
v_val_541_ = lean_ctor_get(v_fst_531_, 0);
lean_inc(v_val_541_);
lean_dec_ref_known(v_fst_531_, 1);
lean_inc(v_a_517_);
v___x_542_ = l_Lean_Meta_isExprDefEq(v_a_517_, v_val_541_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v_a_543_; uint8_t v___x_544_; 
v_a_543_ = lean_ctor_get(v___x_542_, 0);
lean_inc(v_a_543_);
lean_dec_ref_known(v___x_542_, 1);
v___x_544_ = lean_unbox(v_a_543_);
lean_dec(v_a_543_);
if (v___x_544_ == 0)
{
if (v_allowSynthFailures_488_ == 0)
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3);
lean_inc(v_mvarId_490_);
lean_inc(v_tacticName_489_);
v___x_546_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_489_, v_mvarId_490_, v___x_545_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v___x_548_; 
lean_dec_ref_known(v___x_546_, 1);
if (v_isShared_540_ == 0)
{
v___x_548_ = v___x_539_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_fst_536_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v_snd_537_);
v___x_548_ = v_reuseFailAlloc_552_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
lean_object* v___x_550_; 
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 1, v___x_548_);
v___x_550_ = v___x_534_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_fst_532_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v___x_548_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
v_a_501_ = v___x_550_;
goto v___jp_500_;
}
}
}
else
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_560_; 
lean_del_object(v___x_539_);
lean_dec(v_snd_537_);
lean_dec(v_fst_536_);
lean_del_object(v___x_534_);
lean_dec(v_fst_532_);
lean_dec(v_mvarId_490_);
lean_dec(v_tacticName_489_);
v_a_553_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_560_ == 0)
{
v___x_555_ = v___x_546_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_546_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_558_; 
if (v_isShared_556_ == 0)
{
v___x_558_ = v___x_555_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_553_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
else
{
lean_object* v___x_562_; 
if (v_isShared_540_ == 0)
{
v___x_562_ = v___x_539_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_fst_536_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_snd_537_);
v___x_562_ = v_reuseFailAlloc_566_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
lean_object* v___x_564_; 
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 1, v___x_562_);
v___x_564_ = v___x_534_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_fst_532_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v___x_562_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
v_a_501_ = v___x_564_;
goto v___jp_500_;
}
}
}
}
else
{
lean_object* v___x_568_; 
if (v_isShared_540_ == 0)
{
v___x_568_ = v___x_539_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_fst_536_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_snd_537_);
v___x_568_ = v_reuseFailAlloc_572_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
lean_object* v___x_570_; 
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 1, v___x_568_);
v___x_570_ = v___x_534_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_fst_532_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v___x_568_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
v_a_501_ = v___x_570_;
goto v___jp_500_;
}
}
}
}
else
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
lean_del_object(v___x_539_);
lean_dec(v_snd_537_);
lean_dec(v_fst_536_);
lean_del_object(v___x_534_);
lean_dec(v_fst_532_);
lean_dec(v_mvarId_490_);
lean_dec(v_tacticName_489_);
v_a_573_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_580_ == 0)
{
v___x_575_ = v___x_542_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_542_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_a_573_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
}
}
else
{
lean_object* v_fst_584_; lean_object* v_fst_585_; lean_object* v_snd_586_; 
lean_dec(v_fst_531_);
v_fst_584_ = lean_ctor_get(v_snd_529_, 0);
lean_inc(v_fst_584_);
lean_dec(v_snd_529_);
v_fst_585_ = lean_ctor_get(v_snd_530_, 0);
lean_inc(v_fst_585_);
v_snd_586_ = lean_ctor_get(v_snd_530_, 1);
lean_inc(v_snd_586_);
lean_dec(v_snd_530_);
v_fst_506_ = v_fst_584_;
v_fst_507_ = v_fst_585_;
v_snd_508_ = v_snd_586_;
goto v___jp_505_;
}
}
else
{
lean_object* v_a_587_; 
v_a_587_ = lean_ctor_get(v___y_527_, 0);
lean_inc(v_a_587_);
lean_dec_ref_known(v___y_527_, 1);
v_a_519_ = v_a_587_;
goto v___jp_518_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___boxed(lean_object* v_allowSynthFailures_610_, lean_object* v_tacticName_611_, lean_object* v_mvarId_612_, lean_object* v_as_613_, lean_object* v_sz_614_, lean_object* v_i_615_, lean_object* v_b_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
uint8_t v_allowSynthFailures_boxed_622_; size_t v_sz_boxed_623_; size_t v_i_boxed_624_; lean_object* v_res_625_; 
v_allowSynthFailures_boxed_622_ = lean_unbox(v_allowSynthFailures_610_);
v_sz_boxed_623_ = lean_unbox_usize(v_sz_614_);
lean_dec(v_sz_614_);
v_i_boxed_624_ = lean_unbox_usize(v_i_615_);
lean_dec(v_i_615_);
v_res_625_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0(v_allowSynthFailures_boxed_622_, v_tacticName_611_, v_mvarId_612_, v_as_613_, v_sz_boxed_623_, v_i_boxed_624_, v_b_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec_ref(v_as_613_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(lean_object* v_tacticName_635_, lean_object* v_mvarId_636_, uint8_t v_allowSynthFailures_637_, lean_object* v_mvars_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_){
_start:
{
lean_object* v_postponed_644_; lean_object* v___x_645_; size_t v_sz_646_; size_t v___x_647_; lean_object* v___x_648_; 
v_postponed_644_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0));
v___x_645_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__2));
v_sz_646_ = lean_array_size(v_mvars_638_);
v___x_647_ = ((size_t)0ULL);
v___x_648_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0(v_allowSynthFailures_637_, v_tacticName_635_, v_mvarId_636_, v_mvars_638_, v_sz_646_, v___x_647_, v___x_645_, v_a_639_, v_a_640_, v_a_641_, v_a_642_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_671_; 
v_a_649_ = lean_ctor_get(v___x_648_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_671_ == 0)
{
v___x_651_ = v___x_648_;
v_isShared_652_ = v_isSharedCheck_671_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_648_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_671_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v_fst_653_; 
v_fst_653_ = lean_ctor_get(v_a_649_, 0);
lean_inc(v_fst_653_);
if (lean_obj_tag(v_fst_653_) == 1)
{
lean_object* v_snd_654_; lean_object* v_fst_655_; uint8_t v___x_656_; 
v_snd_654_ = lean_ctor_get(v_a_649_, 1);
lean_inc(v_snd_654_);
lean_dec(v_a_649_);
v_fst_655_ = lean_ctor_get(v_snd_654_, 0);
v___x_656_ = lean_unbox(v_fst_655_);
if (v___x_656_ == 0)
{
lean_dec(v_snd_654_);
if (v_allowSynthFailures_637_ == 0)
{
lean_object* v_val_657_; lean_object* v___x_659_; 
v_val_657_ = lean_ctor_get(v_fst_653_, 0);
lean_inc(v_val_657_);
lean_dec_ref_known(v_fst_653_, 1);
if (v_isShared_652_ == 0)
{
lean_ctor_set_tag(v___x_651_, 1);
lean_ctor_set(v___x_651_, 0, v_val_657_);
v___x_659_ = v___x_651_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_val_657_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
else
{
lean_object* v___x_662_; 
lean_dec_ref_known(v_fst_653_, 1);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 0, v_postponed_644_);
v___x_662_ = v___x_651_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_postponed_644_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
else
{
lean_object* v_snd_664_; lean_object* v___x_666_; 
lean_dec_ref_known(v_fst_653_, 1);
v_snd_664_ = lean_ctor_get(v_snd_654_, 1);
lean_inc(v_snd_664_);
lean_dec(v_snd_654_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 0, v_snd_664_);
v___x_666_ = v___x_651_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_snd_664_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
else
{
lean_object* v___x_669_; 
lean_dec(v_fst_653_);
lean_dec(v_a_649_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 0, v_postponed_644_);
v___x_669_ = v___x_651_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_postponed_644_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
else
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_679_; 
v_a_672_ = lean_ctor_get(v___x_648_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_679_ == 0)
{
v___x_674_ = v___x_648_;
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_648_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_677_; 
if (v_isShared_675_ == 0)
{
v___x_677_ = v___x_674_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_a_672_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___boxed(lean_object* v_tacticName_680_, lean_object* v_mvarId_681_, lean_object* v_allowSynthFailures_682_, lean_object* v_mvars_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
uint8_t v_allowSynthFailures_boxed_689_; lean_object* v_res_690_; 
v_allowSynthFailures_boxed_689_ = lean_unbox(v_allowSynthFailures_682_);
v_res_690_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(v_tacticName_680_, v_mvarId_681_, v_allowSynthFailures_boxed_689_, v_mvars_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_);
lean_dec(v_a_687_);
lean_dec_ref(v_a_686_);
lean_dec(v_a_685_);
lean_dec_ref(v_a_684_);
lean_dec_ref(v_mvars_683_);
return v_res_690_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_keys_691_, lean_object* v_i_692_, lean_object* v_k_693_){
_start:
{
lean_object* v___x_694_; uint8_t v___x_695_; 
v___x_694_ = lean_array_get_size(v_keys_691_);
v___x_695_ = lean_nat_dec_lt(v_i_692_, v___x_694_);
if (v___x_695_ == 0)
{
lean_dec(v_i_692_);
return v___x_695_;
}
else
{
lean_object* v_k_x27_696_; uint8_t v___x_697_; 
v_k_x27_696_ = lean_array_fget_borrowed(v_keys_691_, v_i_692_);
v___x_697_ = l_Lean_instBEqMVarId_beq(v_k_693_, v_k_x27_696_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = lean_unsigned_to_nat(1u);
v___x_699_ = lean_nat_add(v_i_692_, v___x_698_);
lean_dec(v_i_692_);
v_i_692_ = v___x_699_;
goto _start;
}
else
{
lean_dec(v_i_692_);
return v___x_695_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_keys_701_, lean_object* v_i_702_, lean_object* v_k_703_){
_start:
{
uint8_t v_res_704_; lean_object* v_r_705_; 
v_res_704_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_701_, v_i_702_, v_k_703_);
lean_dec(v_k_703_);
lean_dec_ref(v_keys_701_);
v_r_705_ = lean_box(v_res_704_);
return v_r_705_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(lean_object* v_x_706_, size_t v_x_707_, lean_object* v_x_708_){
_start:
{
if (lean_obj_tag(v_x_706_) == 0)
{
lean_object* v_es_709_; lean_object* v___x_710_; size_t v___x_711_; size_t v___x_712_; lean_object* v_j_713_; lean_object* v___x_714_; 
v_es_709_ = lean_ctor_get(v_x_706_, 0);
v___x_710_ = lean_box(2);
v___x_711_ = ((size_t)31ULL);
v___x_712_ = lean_usize_land(v_x_707_, v___x_711_);
v_j_713_ = lean_usize_to_nat(v___x_712_);
v___x_714_ = lean_array_get_borrowed(v___x_710_, v_es_709_, v_j_713_);
lean_dec(v_j_713_);
switch(lean_obj_tag(v___x_714_))
{
case 0:
{
lean_object* v_key_715_; uint8_t v___x_716_; 
v_key_715_ = lean_ctor_get(v___x_714_, 0);
v___x_716_ = l_Lean_instBEqMVarId_beq(v_x_708_, v_key_715_);
return v___x_716_;
}
case 1:
{
lean_object* v_node_717_; size_t v___x_718_; size_t v___x_719_; 
v_node_717_ = lean_ctor_get(v___x_714_, 0);
v___x_718_ = ((size_t)5ULL);
v___x_719_ = lean_usize_shift_right(v_x_707_, v___x_718_);
v_x_706_ = v_node_717_;
v_x_707_ = v___x_719_;
goto _start;
}
default: 
{
uint8_t v___x_721_; 
v___x_721_ = 0;
return v___x_721_;
}
}
}
else
{
lean_object* v_ks_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v_ks_722_ = lean_ctor_get(v_x_706_, 0);
v___x_723_ = lean_unsigned_to_nat(0u);
v___x_724_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_ks_722_, v___x_723_, v_x_708_);
return v___x_724_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_725_, lean_object* v_x_726_, lean_object* v_x_727_){
_start:
{
size_t v_x_2813__boxed_728_; uint8_t v_res_729_; lean_object* v_r_730_; 
v_x_2813__boxed_728_ = lean_unbox_usize(v_x_726_);
lean_dec(v_x_726_);
v_res_729_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_725_, v_x_2813__boxed_728_, v_x_727_);
lean_dec(v_x_727_);
lean_dec_ref(v_x_725_);
v_r_730_ = lean_box(v_res_729_);
return v_r_730_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(lean_object* v_x_731_, lean_object* v_x_732_){
_start:
{
uint64_t v___x_733_; size_t v___x_734_; uint8_t v___x_735_; 
v___x_733_ = l_Lean_instHashableMVarId_hash(v_x_732_);
v___x_734_ = lean_uint64_to_usize(v___x_733_);
v___x_735_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_731_, v___x_734_, v_x_732_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg___boxed(lean_object* v_x_736_, lean_object* v_x_737_){
_start:
{
uint8_t v_res_738_; lean_object* v_r_739_; 
v_res_738_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_x_736_, v_x_737_);
lean_dec(v_x_737_);
lean_dec_ref(v_x_736_);
v_r_739_ = lean_box(v_res_738_);
return v_r_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(lean_object* v_mvarId_740_, lean_object* v___y_741_){
_start:
{
lean_object* v___x_743_; lean_object* v_mctx_744_; lean_object* v_eAssignment_745_; uint8_t v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_743_ = lean_st_ref_get(v___y_741_);
v_mctx_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc_ref(v_mctx_744_);
lean_dec(v___x_743_);
v_eAssignment_745_ = lean_ctor_get(v_mctx_744_, 8);
lean_inc_ref(v_eAssignment_745_);
lean_dec_ref(v_mctx_744_);
v___x_746_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_eAssignment_745_, v_mvarId_740_);
lean_dec_ref(v_eAssignment_745_);
v___x_747_ = lean_box(v___x_746_);
v___x_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg___boxed(lean_object* v_mvarId_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v_mvarId_749_, v___y_750_);
lean_dec(v___y_750_);
lean_dec(v_mvarId_749_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(uint8_t v_synthAssignedInstances_753_, lean_object* v_as_754_, size_t v_sz_755_, size_t v_i_756_, lean_object* v_b_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
lean_object* v_a_764_; uint8_t v___x_768_; 
v___x_768_ = lean_usize_dec_lt(v_i_756_, v_sz_755_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; 
v___x_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_769_, 0, v_b_757_);
return v___x_769_;
}
else
{
lean_object* v_snd_770_; lean_object* v_fst_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_820_; 
v_snd_770_ = lean_ctor_get(v_b_757_, 1);
v_fst_771_ = lean_ctor_get(v_b_757_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v_b_757_);
if (v_isSharedCheck_820_ == 0)
{
v___x_773_ = v_b_757_;
v_isShared_774_ = v_isSharedCheck_820_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_snd_770_);
lean_inc(v_fst_771_);
lean_dec(v_b_757_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_820_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v_array_775_; lean_object* v_start_776_; lean_object* v_stop_777_; uint8_t v___x_778_; 
v_array_775_ = lean_ctor_get(v_snd_770_, 0);
v_start_776_ = lean_ctor_get(v_snd_770_, 1);
v_stop_777_ = lean_ctor_get(v_snd_770_, 2);
v___x_778_ = lean_nat_dec_lt(v_start_776_, v_stop_777_);
if (v___x_778_ == 0)
{
lean_object* v___x_780_; 
if (v_isShared_774_ == 0)
{
v___x_780_ = v___x_773_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_fst_771_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_snd_770_);
v___x_780_ = v_reuseFailAlloc_782_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_781_; 
v___x_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
return v___x_781_;
}
}
else
{
lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_816_; 
lean_inc(v_stop_777_);
lean_inc(v_start_776_);
lean_inc_ref(v_array_775_);
v_isSharedCheck_816_ = !lean_is_exclusive(v_snd_770_);
if (v_isSharedCheck_816_ == 0)
{
lean_object* v_unused_817_; lean_object* v_unused_818_; lean_object* v_unused_819_; 
v_unused_817_ = lean_ctor_get(v_snd_770_, 2);
lean_dec(v_unused_817_);
v_unused_818_ = lean_ctor_get(v_snd_770_, 1);
lean_dec(v_unused_818_);
v_unused_819_ = lean_ctor_get(v_snd_770_, 0);
lean_dec(v_unused_819_);
v___x_784_ = v_snd_770_;
v_isShared_785_ = v_isSharedCheck_816_;
goto v_resetjp_783_;
}
else
{
lean_dec(v_snd_770_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_816_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_790_; 
v___x_786_ = lean_array_fget(v_array_775_, v_start_776_);
v___x_787_ = lean_unsigned_to_nat(1u);
v___x_788_ = lean_nat_add(v_start_776_, v___x_787_);
lean_dec(v_start_776_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 1, v___x_788_);
v___x_790_ = v___x_784_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_array_775_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_815_, 2, v_stop_777_);
v___x_790_ = v_reuseFailAlloc_815_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
uint8_t v___x_791_; uint8_t v___x_792_; 
v___x_791_ = lean_unbox(v___x_786_);
lean_dec(v___x_786_);
v___x_792_ = l_Lean_BinderInfo_isInstImplicit(v___x_791_);
if (v___x_792_ == 0)
{
lean_object* v___x_794_; 
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 1, v___x_790_);
v___x_794_ = v___x_773_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_fst_771_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v___x_790_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
v_a_764_ = v___x_794_;
goto v___jp_763_;
}
}
else
{
lean_object* v_a_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v_a_796_ = lean_array_uget_borrowed(v_as_754_, v_i_756_);
v___x_797_ = l_Lean_Expr_mvarId_x21(v_a_796_);
v___x_798_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_797_, v___y_759_);
lean_dec(v___x_797_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_a_799_);
lean_dec_ref_known(v___x_798_, 1);
if (v_synthAssignedInstances_753_ == 0)
{
uint8_t v___x_805_; 
v___x_805_ = lean_unbox(v_a_799_);
lean_dec(v_a_799_);
if (v___x_805_ == 0)
{
goto v___jp_800_;
}
else
{
lean_object* v___x_806_; 
lean_del_object(v___x_773_);
v___x_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_806_, 0, v_fst_771_);
lean_ctor_set(v___x_806_, 1, v___x_790_);
v_a_764_ = v___x_806_;
goto v___jp_763_;
}
}
else
{
lean_dec(v_a_799_);
goto v___jp_800_;
}
v___jp_800_:
{
lean_object* v___x_801_; lean_object* v___x_803_; 
lean_inc(v_a_796_);
v___x_801_ = lean_array_push(v_fst_771_, v_a_796_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 1, v___x_790_);
lean_ctor_set(v___x_773_, 0, v___x_801_);
v___x_803_ = v___x_773_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_801_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v___x_790_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
v_a_764_ = v___x_803_;
goto v___jp_763_;
}
}
}
else
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_814_; 
lean_dec_ref(v___x_790_);
lean_del_object(v___x_773_);
lean_dec(v_fst_771_);
v_a_807_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_814_ == 0)
{
v___x_809_ = v___x_798_;
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_798_);
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
}
}
}
}
v___jp_763_:
{
size_t v___x_765_; size_t v___x_766_; 
v___x_765_ = ((size_t)1ULL);
v___x_766_ = lean_usize_add(v_i_756_, v___x_765_);
v_i_756_ = v___x_766_;
v_b_757_ = v_a_764_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1___boxed(lean_object* v_synthAssignedInstances_821_, lean_object* v_as_822_, lean_object* v_sz_823_, lean_object* v_i_824_, lean_object* v_b_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
uint8_t v_synthAssignedInstances_boxed_831_; size_t v_sz_boxed_832_; size_t v_i_boxed_833_; lean_object* v_res_834_; 
v_synthAssignedInstances_boxed_831_ = lean_unbox(v_synthAssignedInstances_821_);
v_sz_boxed_832_ = lean_unbox_usize(v_sz_823_);
lean_dec(v_sz_823_);
v_i_boxed_833_ = lean_unbox_usize(v_i_824_);
lean_dec(v_i_824_);
v_res_834_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(v_synthAssignedInstances_boxed_831_, v_as_822_, v_sz_boxed_832_, v_i_boxed_833_, v_b_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec_ref(v_as_822_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(lean_object* v_tacticName_835_, lean_object* v_mvarId_836_, uint8_t v_allowSynthFailures_837_, lean_object* v_a_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; uint8_t v___x_846_; 
v___x_844_ = lean_array_get_size(v_a_838_);
v___x_845_ = lean_unsigned_to_nat(0u);
v___x_846_ = lean_nat_dec_eq(v___x_844_, v___x_845_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; 
lean_inc(v_mvarId_836_);
lean_inc(v_tacticName_835_);
v___x_847_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(v_tacticName_835_, v_mvarId_836_, v_allowSynthFailures_837_, v_a_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
lean_dec_ref(v_a_838_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_848_; 
v_a_848_ = lean_ctor_get(v___x_847_, 0);
lean_inc(v_a_848_);
lean_dec_ref_known(v___x_847_, 1);
v_a_838_ = v_a_848_;
goto _start;
}
else
{
lean_dec(v_mvarId_836_);
lean_dec(v_tacticName_835_);
return v___x_847_;
}
}
else
{
lean_object* v___x_850_; 
lean_dec(v_mvarId_836_);
lean_dec(v_tacticName_835_);
v___x_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_850_, 0, v_a_838_);
return v___x_850_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg___boxed(lean_object* v_tacticName_851_, lean_object* v_mvarId_852_, lean_object* v_allowSynthFailures_853_, lean_object* v_a_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
uint8_t v_allowSynthFailures_boxed_860_; lean_object* v_res_861_; 
v_allowSynthFailures_boxed_860_ = lean_unbox(v_allowSynthFailures_853_);
v_res_861_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(v_tacticName_851_, v_mvarId_852_, v_allowSynthFailures_boxed_860_, v_a_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances(lean_object* v_tacticName_862_, lean_object* v_mvarId_863_, lean_object* v_mvarsNew_864_, lean_object* v_binderInfos_865_, uint8_t v_synthAssignedInstances_866_, uint8_t v_allowSynthFailures_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_){
_start:
{
lean_object* v___x_873_; lean_object* v_todo_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; size_t v_sz_878_; size_t v___x_879_; lean_object* v___x_880_; 
v___x_873_ = lean_unsigned_to_nat(0u);
v_todo_874_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0));
v___x_875_ = lean_array_get_size(v_binderInfos_865_);
v___x_876_ = l_Array_toSubarray___redArg(v_binderInfos_865_, v___x_873_, v___x_875_);
v___x_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_877_, 0, v_todo_874_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
v_sz_878_ = lean_array_size(v_mvarsNew_864_);
v___x_879_ = ((size_t)0ULL);
v___x_880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(v_synthAssignedInstances_866_, v_mvarsNew_864_, v_sz_878_, v___x_879_, v___x_877_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; lean_object* v_fst_882_; lean_object* v___x_883_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_a_881_);
lean_dec_ref_known(v___x_880_, 1);
v_fst_882_ = lean_ctor_get(v_a_881_, 0);
lean_inc(v_fst_882_);
lean_dec(v_a_881_);
v___x_883_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(v_tacticName_862_, v_mvarId_863_, v_allowSynthFailures_867_, v_fst_882_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_891_; 
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_891_ == 0)
{
lean_object* v_unused_892_; 
v_unused_892_ = lean_ctor_get(v___x_883_, 0);
lean_dec(v_unused_892_);
v___x_885_ = v___x_883_;
v_isShared_886_ = v_isSharedCheck_891_;
goto v_resetjp_884_;
}
else
{
lean_dec(v___x_883_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_891_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_887_; lean_object* v___x_889_; 
v___x_887_ = lean_box(0);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v___x_887_);
v___x_889_ = v___x_885_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_887_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
else
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_900_; 
v_a_893_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_900_ == 0)
{
v___x_895_ = v___x_883_;
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_883_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_896_ == 0)
{
v___x_898_ = v___x_895_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_893_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
else
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
lean_dec(v_mvarId_863_);
lean_dec(v_tacticName_862_);
v_a_901_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_908_ == 0)
{
v___x_903_ = v___x_880_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_880_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_901_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances___boxed(lean_object* v_tacticName_909_, lean_object* v_mvarId_910_, lean_object* v_mvarsNew_911_, lean_object* v_binderInfos_912_, lean_object* v_synthAssignedInstances_913_, lean_object* v_allowSynthFailures_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_){
_start:
{
uint8_t v_synthAssignedInstances_boxed_920_; uint8_t v_allowSynthFailures_boxed_921_; lean_object* v_res_922_; 
v_synthAssignedInstances_boxed_920_ = lean_unbox(v_synthAssignedInstances_913_);
v_allowSynthFailures_boxed_921_ = lean_unbox(v_allowSynthFailures_914_);
v_res_922_ = l_Lean_Meta_synthAppInstances(v_tacticName_909_, v_mvarId_910_, v_mvarsNew_911_, v_binderInfos_912_, v_synthAssignedInstances_boxed_920_, v_allowSynthFailures_boxed_921_, v_a_915_, v_a_916_, v_a_917_, v_a_918_);
lean_dec(v_a_918_);
lean_dec_ref(v_a_917_);
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
lean_dec_ref(v_mvarsNew_911_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0(lean_object* v_mvarId_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v_mvarId_923_, v___y_925_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___boxed(lean_object* v_mvarId_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0(v_mvarId_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v_mvarId_930_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2(lean_object* v_tacticName_937_, lean_object* v_mvarId_938_, uint8_t v_allowSynthFailures_939_, lean_object* v_inst_940_, lean_object* v_a_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(v_tacticName_937_, v_mvarId_938_, v_allowSynthFailures_939_, v_a_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___boxed(lean_object* v_tacticName_948_, lean_object* v_mvarId_949_, lean_object* v_allowSynthFailures_950_, lean_object* v_inst_951_, lean_object* v_a_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
uint8_t v_allowSynthFailures_boxed_958_; lean_object* v_res_959_; 
v_allowSynthFailures_boxed_958_ = lean_unbox(v_allowSynthFailures_950_);
v_res_959_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2(v_tacticName_948_, v_mvarId_949_, v_allowSynthFailures_boxed_958_, v_inst_951_, v_a_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
return v_res_959_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0(lean_object* v_00_u03b2_960_, lean_object* v_x_961_, lean_object* v_x_962_){
_start:
{
uint8_t v___x_963_; 
v___x_963_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_x_961_, v_x_962_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___boxed(lean_object* v_00_u03b2_964_, lean_object* v_x_965_, lean_object* v_x_966_){
_start:
{
uint8_t v_res_967_; lean_object* v_r_968_; 
v_res_967_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0(v_00_u03b2_964_, v_x_965_, v_x_966_);
lean_dec(v_x_966_);
lean_dec_ref(v_x_965_);
v_r_968_ = lean_box(v_res_967_);
return v_r_968_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_969_, lean_object* v_x_970_, size_t v_x_971_, lean_object* v_x_972_){
_start:
{
uint8_t v___x_973_; 
v___x_973_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_970_, v_x_971_, v_x_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_974_, lean_object* v_x_975_, lean_object* v_x_976_, lean_object* v_x_977_){
_start:
{
size_t v_x_3145__boxed_978_; uint8_t v_res_979_; lean_object* v_r_980_; 
v_x_3145__boxed_978_ = lean_unbox_usize(v_x_976_);
lean_dec(v_x_976_);
v_res_979_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1(v_00_u03b2_974_, v_x_975_, v_x_3145__boxed_978_, v_x_977_);
lean_dec(v_x_977_);
lean_dec_ref(v_x_975_);
v_r_980_ = lean_box(v_res_979_);
return v_r_980_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_981_, lean_object* v_keys_982_, lean_object* v_vals_983_, lean_object* v_heq_984_, lean_object* v_i_985_, lean_object* v_k_986_){
_start:
{
uint8_t v___x_987_; 
v___x_987_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_982_, v_i_985_, v_k_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_988_, lean_object* v_keys_989_, lean_object* v_vals_990_, lean_object* v_heq_991_, lean_object* v_i_992_, lean_object* v_k_993_){
_start:
{
uint8_t v_res_994_; lean_object* v_r_995_; 
v_res_994_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_988_, v_keys_989_, v_vals_990_, v_heq_991_, v_i_992_, v_k_993_);
lean_dec(v_k_993_);
lean_dec_ref(v_vals_990_);
lean_dec_ref(v_keys_989_);
v_r_995_ = lean_box(v_res_994_);
return v_r_995_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(lean_object* v_newMVars_996_, lean_object* v_binderInfos_997_, lean_object* v_a_998_, lean_object* v_n_999_, lean_object* v_i_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v_zero_1006_; uint8_t v_isZero_1007_; 
v_zero_1006_ = lean_unsigned_to_nat(0u);
v_isZero_1007_ = lean_nat_dec_eq(v_i_1000_, v_zero_1006_);
if (v_isZero_1007_ == 1)
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
lean_dec(v_i_1000_);
lean_dec(v_a_998_);
v___x_1008_ = lean_box(0);
v___x_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
return v___x_1009_;
}
else
{
uint8_t v___x_1010_; lean_object* v_one_1011_; lean_object* v_n_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v_a_1018_; uint8_t v___x_1019_; 
v___x_1010_ = 0;
v_one_1011_ = lean_unsigned_to_nat(1u);
v_n_1012_ = lean_nat_sub(v_i_1000_, v_one_1011_);
lean_dec(v_i_1000_);
v___x_1013_ = lean_nat_sub(v_n_999_, v_n_1012_);
v___x_1014_ = lean_nat_sub(v___x_1013_, v_one_1011_);
lean_dec(v___x_1013_);
v___x_1015_ = lean_array_fget_borrowed(v_newMVars_996_, v___x_1014_);
v___x_1016_ = l_Lean_Expr_mvarId_x21(v___x_1015_);
v___x_1017_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_1016_, v___y_1002_);
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc(v_a_1018_);
lean_dec_ref(v___x_1017_);
v___x_1019_ = lean_unbox(v_a_1018_);
lean_dec(v_a_1018_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; lean_object* v___x_1021_; uint8_t v___x_1022_; uint8_t v___x_1023_; 
v___x_1020_ = lean_box(v___x_1010_);
v___x_1021_ = lean_array_get(v___x_1020_, v_binderInfos_997_, v___x_1014_);
lean_dec(v___x_1014_);
lean_dec(v___x_1020_);
v___x_1022_ = lean_unbox(v___x_1021_);
lean_dec(v___x_1021_);
v___x_1023_ = l_Lean_BinderInfo_isInstImplicit(v___x_1022_);
if (v___x_1023_ == 0)
{
lean_object* v___x_1024_; 
lean_inc(v___x_1016_);
v___x_1024_ = l_Lean_MVarId_getTag(v___x_1016_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc(v_a_1025_);
lean_dec_ref_known(v___x_1024_, 1);
lean_inc(v_a_998_);
v___x_1026_ = l_Lean_Meta_appendTag(v_a_998_, v_a_1025_);
lean_dec(v_a_1025_);
v___x_1027_ = l_Lean_MVarId_setTag___redArg(v___x_1016_, v___x_1026_, v___y_1002_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_dec_ref_known(v___x_1027_, 1);
v_i_1000_ = v_n_1012_;
goto _start;
}
else
{
lean_dec(v_n_1012_);
lean_dec(v_a_998_);
return v___x_1027_;
}
}
else
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1036_; 
lean_dec(v___x_1016_);
lean_dec(v_n_1012_);
lean_dec(v_a_998_);
v_a_1029_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1031_ = v___x_1024_;
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_1024_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_a_1029_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
else
{
lean_dec(v___x_1016_);
v_i_1000_ = v_n_1012_;
goto _start;
}
}
else
{
lean_dec(v___x_1016_);
lean_dec(v___x_1014_);
v_i_1000_ = v_n_1012_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg___boxed(lean_object* v_newMVars_1039_, lean_object* v_binderInfos_1040_, lean_object* v_a_1041_, lean_object* v_n_1042_, lean_object* v_i_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_1039_, v_binderInfos_1040_, v_a_1041_, v_n_1042_, v_i_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v_n_1042_);
lean_dec_ref(v_binderInfos_1040_);
lean_dec_ref(v_newMVars_1039_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendParentTag(lean_object* v_mvarId_1050_, lean_object* v_newMVars_1051_, lean_object* v_binderInfos_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = l_Lean_instInhabitedExpr;
v___x_1059_ = l_Lean_MVarId_getTag(v_mvarId_1050_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1077_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1062_ = v___x_1059_;
v_isShared_1063_ = v_isSharedCheck_1077_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1059_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1077_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; uint8_t v___x_1066_; 
v___x_1064_ = lean_array_get_size(v_newMVars_1051_);
v___x_1065_ = lean_unsigned_to_nat(1u);
v___x_1066_ = lean_nat_dec_eq(v___x_1064_, v___x_1065_);
if (v___x_1066_ == 0)
{
uint8_t v___x_1067_; 
v___x_1067_ = l_Lean_Name_isAnonymous(v_a_1060_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1068_; 
lean_del_object(v___x_1062_);
v___x_1068_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_1051_, v_binderInfos_1052_, v_a_1060_, v___x_1064_, v___x_1064_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_);
return v___x_1068_;
}
else
{
lean_object* v___x_1069_; lean_object* v___x_1071_; 
lean_dec(v_a_1060_);
v___x_1069_ = lean_box(0);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 0, v___x_1069_);
v___x_1071_ = v___x_1062_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1069_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
else
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
lean_del_object(v___x_1062_);
v___x_1073_ = lean_unsigned_to_nat(0u);
v___x_1074_ = lean_array_get_borrowed(v___x_1058_, v_newMVars_1051_, v___x_1073_);
v___x_1075_ = l_Lean_Expr_mvarId_x21(v___x_1074_);
v___x_1076_ = l_Lean_MVarId_setTag___redArg(v___x_1075_, v_a_1060_, v_a_1054_);
return v___x_1076_;
}
}
}
else
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
v_a_1078_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___x_1059_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1059_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendParentTag___boxed(lean_object* v_mvarId_1086_, lean_object* v_newMVars_1087_, lean_object* v_binderInfos_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Lean_Meta_appendParentTag(v_mvarId_1086_, v_newMVars_1087_, v_binderInfos_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_);
lean_dec(v_a_1092_);
lean_dec_ref(v_a_1091_);
lean_dec(v_a_1090_);
lean_dec_ref(v_a_1089_);
lean_dec_ref(v_binderInfos_1088_);
lean_dec_ref(v_newMVars_1087_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0(lean_object* v_newMVars_1095_, lean_object* v_binderInfos_1096_, lean_object* v_a_1097_, lean_object* v_n_1098_, lean_object* v_i_1099_, lean_object* v_a_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_1095_, v_binderInfos_1096_, v_a_1097_, v_n_1098_, v_i_1099_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___boxed(lean_object* v_newMVars_1107_, lean_object* v_binderInfos_1108_, lean_object* v_a_1109_, lean_object* v_n_1110_, lean_object* v_i_1111_, lean_object* v_a_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0(v_newMVars_1107_, v_binderInfos_1108_, v_a_1109_, v_n_1110_, v_i_1111_, v_a_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec(v_n_1110_);
lean_dec_ref(v_binderInfos_1108_);
lean_dec_ref(v_newMVars_1107_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_postprocessAppMVars(lean_object* v_tacticName_1119_, lean_object* v_mvarId_1120_, lean_object* v_newMVars_1121_, lean_object* v_binderInfos_1122_, uint8_t v_synthAssignedInstances_1123_, uint8_t v_allowSynthFailures_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = l_Lean_Meta_synthAppInstances(v_tacticName_1119_, v_mvarId_1120_, v_newMVars_1121_, v_binderInfos_1122_, v_synthAssignedInstances_1123_, v_allowSynthFailures_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_postprocessAppMVars___boxed(lean_object* v_tacticName_1131_, lean_object* v_mvarId_1132_, lean_object* v_newMVars_1133_, lean_object* v_binderInfos_1134_, lean_object* v_synthAssignedInstances_1135_, lean_object* v_allowSynthFailures_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_){
_start:
{
uint8_t v_synthAssignedInstances_boxed_1142_; uint8_t v_allowSynthFailures_boxed_1143_; lean_object* v_res_1144_; 
v_synthAssignedInstances_boxed_1142_ = lean_unbox(v_synthAssignedInstances_1135_);
v_allowSynthFailures_boxed_1143_ = lean_unbox(v_allowSynthFailures_1136_);
v_res_1144_ = l_Lean_Meta_postprocessAppMVars(v_tacticName_1131_, v_mvarId_1132_, v_newMVars_1133_, v_binderInfos_1134_, v_synthAssignedInstances_boxed_1142_, v_allowSynthFailures_boxed_1143_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_);
lean_dec(v_a_1140_);
lean_dec_ref(v_a_1139_);
lean_dec(v_a_1138_);
lean_dec_ref(v_a_1137_);
lean_dec_ref(v_newMVars_1133_);
return v_res_1144_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0(lean_object* v_mvar_1145_, lean_object* v_mvarId_1146_){
_start:
{
lean_object* v___x_1147_; uint8_t v___x_1148_; 
v___x_1147_ = l_Lean_Expr_mvarId_x21(v_mvar_1145_);
v___x_1148_ = l_Lean_instBEqMVarId_beq(v_mvarId_1146_, v___x_1147_);
lean_dec(v___x_1147_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0___boxed(lean_object* v_mvar_1149_, lean_object* v_mvarId_1150_){
_start:
{
uint8_t v_res_1151_; lean_object* v_r_1152_; 
v_res_1151_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0(v_mvar_1149_, v_mvarId_1150_);
lean_dec(v_mvarId_1150_);
lean_dec_ref(v_mvar_1149_);
v_r_1152_ = lean_box(v_res_1151_);
return v_r_1152_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(lean_object* v_mvar_1153_, lean_object* v_as_1154_, size_t v_i_1155_, size_t v_stop_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
uint8_t v___x_1166_; 
v___x_1166_ = lean_usize_dec_eq(v_i_1155_, v_stop_1156_);
if (v___x_1166_ == 0)
{
lean_object* v___x_1167_; uint8_t v___x_1168_; 
v___x_1167_ = lean_array_uget_borrowed(v_as_1154_, v_i_1155_);
v___x_1168_ = lean_expr_eqv(v_mvar_1153_, v___x_1167_);
if (v___x_1168_ == 0)
{
lean_object* v___f_1169_; uint8_t v___x_1170_; lean_object* v___x_1171_; 
lean_inc_ref(v_mvar_1153_);
v___f_1169_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1169_, 0, v_mvar_1153_);
v___x_1170_ = 1;
lean_inc(v___y_1160_);
lean_inc_ref(v___y_1159_);
lean_inc(v___y_1158_);
lean_inc_ref(v___y_1157_);
lean_inc(v___x_1167_);
v___x_1171_ = lean_infer_type(v___x_1167_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1182_; 
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1174_ = v___x_1171_;
v_isShared_1175_ = v_isSharedCheck_1182_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1171_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1182_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1176_ = lean_box(0);
v___x_1177_ = l_Lean_FindMVar_main(v___f_1169_, v_a_1172_, v___x_1176_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_del_object(v___x_1174_);
goto v___jp_1162_;
}
else
{
lean_object* v___x_1178_; lean_object* v___x_1180_; 
lean_dec_ref_known(v___x_1177_, 1);
lean_dec_ref(v_mvar_1153_);
v___x_1178_ = lean_box(v___x_1170_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 0, v___x_1178_);
v___x_1180_ = v___x_1174_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1178_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
else
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1190_; 
lean_dec_ref(v___f_1169_);
lean_dec_ref(v_mvar_1153_);
v_a_1183_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1185_ = v___x_1171_;
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1171_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1183_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
else
{
goto v___jp_1162_;
}
}
else
{
uint8_t v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
lean_dec_ref(v_mvar_1153_);
v___x_1191_ = 0;
v___x_1192_ = lean_box(v___x_1191_);
v___x_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
return v___x_1193_;
}
v___jp_1162_:
{
size_t v___x_1163_; size_t v___x_1164_; 
v___x_1163_ = ((size_t)1ULL);
v___x_1164_ = lean_usize_add(v_i_1155_, v___x_1163_);
v_i_1155_ = v___x_1164_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___boxed(lean_object* v_mvar_1194_, lean_object* v_as_1195_, lean_object* v_i_1196_, lean_object* v_stop_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
size_t v_i_boxed_1203_; size_t v_stop_boxed_1204_; lean_object* v_res_1205_; 
v_i_boxed_1203_ = lean_unbox_usize(v_i_1196_);
lean_dec(v_i_1196_);
v_stop_boxed_1204_ = lean_unbox_usize(v_stop_1197_);
lean_dec(v_stop_1197_);
v_res_1205_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(v_mvar_1194_, v_as_1195_, v_i_boxed_1203_, v_stop_boxed_1204_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec_ref(v_as_1195_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(lean_object* v_mvar_1206_, lean_object* v_otherMVars_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; uint8_t v___x_1215_; 
v___x_1213_ = lean_unsigned_to_nat(0u);
v___x_1214_ = lean_array_get_size(v_otherMVars_1207_);
v___x_1215_ = lean_nat_dec_lt(v___x_1213_, v___x_1214_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1216_; lean_object* v___x_1217_; 
lean_dec_ref(v_mvar_1206_);
v___x_1216_ = lean_box(v___x_1215_);
v___x_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
return v___x_1217_;
}
else
{
if (v___x_1215_ == 0)
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
lean_dec_ref(v_mvar_1206_);
v___x_1218_ = lean_box(v___x_1215_);
v___x_1219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1218_);
return v___x_1219_;
}
else
{
size_t v___x_1220_; size_t v___x_1221_; lean_object* v___x_1222_; 
v___x_1220_ = ((size_t)0ULL);
v___x_1221_ = lean_usize_of_nat(v___x_1214_);
v___x_1222_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(v_mvar_1206_, v_otherMVars_1207_, v___x_1220_, v___x_1221_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
return v___x_1222_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___boxed(lean_object* v_mvar_1223_, lean_object* v_otherMVars_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(v_mvar_1223_, v_otherMVars_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_);
lean_dec(v_a_1228_);
lean_dec_ref(v_a_1227_);
lean_dec(v_a_1226_);
lean_dec_ref(v_a_1225_);
lean_dec_ref(v_otherMVars_1224_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(lean_object* v_mvars_1231_, lean_object* v_as_1232_, size_t v_i_1233_, size_t v_stop_1234_, lean_object* v_b_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v_a_1242_; uint8_t v___x_1246_; 
v___x_1246_ = lean_usize_dec_eq(v_i_1233_, v_stop_1234_);
if (v___x_1246_ == 0)
{
lean_object* v_fst_1247_; lean_object* v_snd_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1273_; 
v_fst_1247_ = lean_ctor_get(v_b_1235_, 0);
v_snd_1248_ = lean_ctor_get(v_b_1235_, 1);
v_isSharedCheck_1273_ = !lean_is_exclusive(v_b_1235_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1250_ = v_b_1235_;
v_isShared_1251_ = v_isSharedCheck_1273_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_snd_1248_);
lean_inc(v_fst_1247_);
lean_dec(v_b_1235_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1273_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1252_; lean_object* v_currMVarId_1253_; lean_object* v___x_1254_; 
v___x_1252_ = lean_array_uget_borrowed(v_as_1232_, v_i_1233_);
v_currMVarId_1253_ = l_Lean_Expr_mvarId_x21(v___x_1252_);
lean_inc(v___x_1252_);
v___x_1254_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(v___x_1252_, v_mvars_1231_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; uint8_t v___x_1256_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_a_1255_);
lean_dec_ref_known(v___x_1254_, 1);
v___x_1256_ = lean_unbox(v_a_1255_);
lean_dec(v_a_1255_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; lean_object* v___x_1259_; 
v___x_1257_ = lean_array_push(v_fst_1247_, v_currMVarId_1253_);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 0, v___x_1257_);
v___x_1259_ = v___x_1250_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1257_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v_snd_1248_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
v_a_1242_ = v___x_1259_;
goto v___jp_1241_;
}
}
else
{
lean_object* v___x_1261_; lean_object* v___x_1263_; 
v___x_1261_ = lean_array_push(v_snd_1248_, v_currMVarId_1253_);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 1, v___x_1261_);
v___x_1263_ = v___x_1250_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_fst_1247_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v___x_1261_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
v_a_1242_ = v___x_1263_;
goto v___jp_1241_;
}
}
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
lean_dec(v_currMVarId_1253_);
lean_del_object(v___x_1250_);
lean_dec(v_snd_1248_);
lean_dec(v_fst_1247_);
v_a_1265_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1267_ = v___x_1254_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1254_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_a_1265_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
}
}
else
{
lean_object* v___x_1274_; 
v___x_1274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1274_, 0, v_b_1235_);
return v___x_1274_;
}
v___jp_1241_:
{
size_t v___x_1243_; size_t v___x_1244_; 
v___x_1243_ = ((size_t)1ULL);
v___x_1244_ = lean_usize_add(v_i_1233_, v___x_1243_);
v_i_1233_ = v___x_1244_;
v_b_1235_ = v_a_1242_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0___boxed(lean_object* v_mvars_1275_, lean_object* v_as_1276_, lean_object* v_i_1277_, lean_object* v_stop_1278_, lean_object* v_b_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
size_t v_i_boxed_1285_; size_t v_stop_boxed_1286_; lean_object* v_res_1287_; 
v_i_boxed_1285_ = lean_unbox_usize(v_i_1277_);
lean_dec(v_i_1277_);
v_stop_boxed_1286_ = lean_unbox_usize(v_stop_1278_);
lean_dec(v_stop_1278_);
v_res_1287_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_1275_, v_as_1276_, v_i_boxed_1285_, v_stop_boxed_1286_, v_b_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec_ref(v_as_1276_);
lean_dec_ref(v_mvars_1275_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(lean_object* v_mvars_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; uint8_t v___x_1301_; 
v___x_1298_ = lean_unsigned_to_nat(0u);
v___x_1299_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1));
v___x_1300_ = lean_array_get_size(v_mvars_1292_);
v___x_1301_ = lean_nat_dec_lt(v___x_1298_, v___x_1300_);
if (v___x_1301_ == 0)
{
lean_object* v___x_1302_; 
v___x_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1299_);
return v___x_1302_;
}
else
{
size_t v___x_1303_; size_t v___x_1304_; lean_object* v___x_1305_; 
v___x_1303_ = ((size_t)0ULL);
v___x_1304_ = lean_usize_of_nat(v___x_1300_);
v___x_1305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_1292_, v_mvars_1292_, v___x_1303_, v___x_1304_, v___x_1299_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_);
return v___x_1305_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___boxed(lean_object* v_mvars_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_);
lean_dec(v_a_1310_);
lean_dec_ref(v_a_1309_);
lean_dec(v_a_1308_);
lean_dec_ref(v_a_1307_);
lean_dec_ref(v_mvars_1306_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals_spec__0(lean_object* v_a_1313_, lean_object* v_a_1314_){
_start:
{
if (lean_obj_tag(v_a_1313_) == 0)
{
lean_object* v___x_1315_; 
v___x_1315_ = l_List_reverse___redArg(v_a_1314_);
return v___x_1315_;
}
else
{
lean_object* v_head_1316_; lean_object* v_tail_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1326_; 
v_head_1316_ = lean_ctor_get(v_a_1313_, 0);
v_tail_1317_ = lean_ctor_get(v_a_1313_, 1);
v_isSharedCheck_1326_ = !lean_is_exclusive(v_a_1313_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1319_ = v_a_1313_;
v_isShared_1320_ = v_isSharedCheck_1326_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_tail_1317_);
lean_inc(v_head_1316_);
lean_dec(v_a_1313_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1326_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1321_; lean_object* v___x_1323_; 
v___x_1321_ = l_Lean_Expr_mvarId_x21(v_head_1316_);
lean_dec(v_head_1316_);
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 1, v_a_1314_);
lean_ctor_set(v___x_1319_, 0, v___x_1321_);
v___x_1323_ = v___x_1319_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___x_1321_);
lean_ctor_set(v_reuseFailAlloc_1325_, 1, v_a_1314_);
v___x_1323_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
v_a_1313_ = v_tail_1317_;
v_a_1314_ = v___x_1323_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(lean_object* v_mvars_1327_, uint8_t v_x_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_){
_start:
{
switch(v_x_1328_)
{
case 0:
{
lean_object* v___x_1334_; 
v___x_1334_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1327_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_);
lean_dec_ref(v_mvars_1327_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1347_; 
v_a_1335_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1337_ = v___x_1334_;
v_isShared_1338_ = v_isSharedCheck_1347_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1334_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1347_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v_fst_1339_; lean_object* v_snd_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1345_; 
v_fst_1339_ = lean_ctor_get(v_a_1335_, 0);
lean_inc(v_fst_1339_);
v_snd_1340_ = lean_ctor_get(v_a_1335_, 1);
lean_inc(v_snd_1340_);
lean_dec(v_a_1335_);
v___x_1341_ = lean_array_to_list(v_fst_1339_);
v___x_1342_ = lean_array_to_list(v_snd_1340_);
v___x_1343_ = l_List_appendTR___redArg(v___x_1341_, v___x_1342_);
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 0, v___x_1343_);
v___x_1345_ = v___x_1337_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v___x_1343_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
else
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1355_; 
v_a_1348_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1350_ = v___x_1334_;
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___x_1334_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1353_; 
if (v_isShared_1351_ == 0)
{
v___x_1353_ = v___x_1350_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_a_1348_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
}
case 1:
{
lean_object* v___x_1356_; 
v___x_1356_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1327_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_);
lean_dec_ref(v_mvars_1327_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1366_; 
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1359_ = v___x_1356_;
v_isShared_1360_ = v_isSharedCheck_1366_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1356_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1366_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v_fst_1361_; lean_object* v___x_1362_; lean_object* v___x_1364_; 
v_fst_1361_ = lean_ctor_get(v_a_1357_, 0);
lean_inc(v_fst_1361_);
lean_dec(v_a_1357_);
v___x_1362_ = lean_array_to_list(v_fst_1361_);
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 0, v___x_1362_);
v___x_1364_ = v___x_1359_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1362_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
else
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
v_a_1367_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1369_ = v___x_1356_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1356_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1367_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
default: 
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1375_ = lean_array_to_list(v_mvars_1327_);
v___x_1376_ = lean_box(0);
v___x_1377_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals_spec__0(v___x_1375_, v___x_1376_);
v___x_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1377_);
return v___x_1378_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals___boxed(lean_object* v_mvars_1379_, lean_object* v_x_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_){
_start:
{
uint8_t v_x_731__boxed_1386_; lean_object* v_res_1387_; 
v_x_731__boxed_1386_ = lean_unbox(v_x_1380_);
v_res_1387_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(v_mvars_1379_, v_x_731__boxed_1386_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_);
lean_dec(v_a_1384_);
lean_dec_ref(v_a_1383_);
lean_dec(v_a_1382_);
lean_dec_ref(v_a_1381_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(uint8_t v_approx_1388_, lean_object* v_a_1389_, lean_object* v_b_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_){
_start:
{
if (v_approx_1388_ == 0)
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1389_, v_b_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_);
return v___x_1396_;
}
else
{
lean_object* v___x_1397_; uint8_t v_constApprox_1398_; uint8_t v_isDefEqStuckEx_1399_; uint8_t v_unificationHints_1400_; uint8_t v_proofIrrelevance_1401_; uint8_t v_assignSyntheticOpaque_1402_; uint8_t v_offsetCnstrs_1403_; uint8_t v_transparency_1404_; uint8_t v_etaStruct_1405_; uint8_t v_univApprox_1406_; uint8_t v_iota_1407_; uint8_t v_beta_1408_; uint8_t v_proj_1409_; uint8_t v_zeta_1410_; uint8_t v_zetaDelta_1411_; uint8_t v_zetaUnused_1412_; uint8_t v_zetaHave_1413_; uint8_t v_canUnfoldPredicateConfig_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1435_; 
v___x_1397_ = l_Lean_Meta_Context_config(v_a_1391_);
v_constApprox_1398_ = lean_ctor_get_uint8(v___x_1397_, 3);
v_isDefEqStuckEx_1399_ = lean_ctor_get_uint8(v___x_1397_, 4);
v_unificationHints_1400_ = lean_ctor_get_uint8(v___x_1397_, 5);
v_proofIrrelevance_1401_ = lean_ctor_get_uint8(v___x_1397_, 6);
v_assignSyntheticOpaque_1402_ = lean_ctor_get_uint8(v___x_1397_, 7);
v_offsetCnstrs_1403_ = lean_ctor_get_uint8(v___x_1397_, 8);
v_transparency_1404_ = lean_ctor_get_uint8(v___x_1397_, 9);
v_etaStruct_1405_ = lean_ctor_get_uint8(v___x_1397_, 10);
v_univApprox_1406_ = lean_ctor_get_uint8(v___x_1397_, 11);
v_iota_1407_ = lean_ctor_get_uint8(v___x_1397_, 12);
v_beta_1408_ = lean_ctor_get_uint8(v___x_1397_, 13);
v_proj_1409_ = lean_ctor_get_uint8(v___x_1397_, 14);
v_zeta_1410_ = lean_ctor_get_uint8(v___x_1397_, 15);
v_zetaDelta_1411_ = lean_ctor_get_uint8(v___x_1397_, 16);
v_zetaUnused_1412_ = lean_ctor_get_uint8(v___x_1397_, 17);
v_zetaHave_1413_ = lean_ctor_get_uint8(v___x_1397_, 18);
v_canUnfoldPredicateConfig_1414_ = lean_ctor_get_uint8(v___x_1397_, 19);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1416_ = v___x_1397_;
v_isShared_1417_ = v_isSharedCheck_1435_;
goto v_resetjp_1415_;
}
else
{
lean_dec(v___x_1397_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1435_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_1434_, 3, v_constApprox_1398_);
lean_ctor_set_uint8(v_reuseFailAlloc_1434_, 4, v_isDefEqStuckEx_1399_);
lean_ctor_set_uint8(v_reuseFailAlloc_1434_, 5, v_unificationHints_1400_);
lean_ctor_set_uint8(v_reuseFailAlloc_1434_, 6, v_proofIrrelevance_1401_);
lean_ctor_set_uint8(v_reuseFailAlloc_1434_, 7, v_assignSyntheticOpaque_1402_);
lean_ctor_set_uint8(v_reuseFailAlloc_1434_, 8, v_offsetCnstrs_1403_);
lean_ctor_set_uint8(v_reuseFailAlloc_1434_, 9, v_transparency_1404_);
lean_ctor_set_uint8(v_reuseFailAlloc_1434_, 10, v_etaStruct_1405_);
lean_ctor_set_uint8(v_reuseFailAlloc_1434_, 11, v_univApprox_1406_);
lean_ctor_set_uint8(v_reuseFailAlloc_1434_, 12, v_iota_1407_);
lean_ctor_set_uint8(v_reuseFailAlloc_1434_, 13, v_beta_1408_);
lean_ctor_set_uint8(v_reuseFailAlloc_1434_, 14, v_proj_1409_);
lean_ctor_set_uint8(v_reuseFailAlloc_1434_, 15, v_zeta_1410_);
lean_ctor_set_uint8(v_reuseFailAlloc_1434_, 16, v_zetaDelta_1411_);
lean_ctor_set_uint8(v_reuseFailAlloc_1434_, 17, v_zetaUnused_1412_);
lean_ctor_set_uint8(v_reuseFailAlloc_1434_, 18, v_zetaHave_1413_);
lean_ctor_set_uint8(v_reuseFailAlloc_1434_, 19, v_canUnfoldPredicateConfig_1414_);
v___x_1419_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
uint8_t v_trackZetaDelta_1420_; lean_object* v_zetaDeltaSet_1421_; lean_object* v_lctx_1422_; lean_object* v_localInstances_1423_; lean_object* v_defEqCtx_x3f_1424_; lean_object* v_synthPendingDepth_1425_; lean_object* v_customCanUnfoldPredicate_x3f_1426_; uint8_t v_univApprox_1427_; uint8_t v_inTypeClassResolution_1428_; uint8_t v_cacheInferType_1429_; uint64_t v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
lean_ctor_set_uint8(v___x_1419_, 0, v_approx_1388_);
lean_ctor_set_uint8(v___x_1419_, 1, v_approx_1388_);
lean_ctor_set_uint8(v___x_1419_, 2, v_approx_1388_);
v_trackZetaDelta_1420_ = lean_ctor_get_uint8(v_a_1391_, sizeof(void*)*7);
v_zetaDeltaSet_1421_ = lean_ctor_get(v_a_1391_, 1);
v_lctx_1422_ = lean_ctor_get(v_a_1391_, 2);
v_localInstances_1423_ = lean_ctor_get(v_a_1391_, 3);
v_defEqCtx_x3f_1424_ = lean_ctor_get(v_a_1391_, 4);
v_synthPendingDepth_1425_ = lean_ctor_get(v_a_1391_, 5);
v_customCanUnfoldPredicate_x3f_1426_ = lean_ctor_get(v_a_1391_, 6);
v_univApprox_1427_ = lean_ctor_get_uint8(v_a_1391_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1428_ = lean_ctor_get_uint8(v_a_1391_, sizeof(void*)*7 + 2);
v_cacheInferType_1429_ = lean_ctor_get_uint8(v_a_1391_, sizeof(void*)*7 + 3);
v___x_1430_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1419_);
v___x_1431_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1431_, 0, v___x_1419_);
lean_ctor_set_uint64(v___x_1431_, sizeof(void*)*1, v___x_1430_);
lean_inc(v_customCanUnfoldPredicate_x3f_1426_);
lean_inc(v_synthPendingDepth_1425_);
lean_inc(v_defEqCtx_x3f_1424_);
lean_inc_ref(v_localInstances_1423_);
lean_inc_ref(v_lctx_1422_);
lean_inc(v_zetaDeltaSet_1421_);
v___x_1432_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
lean_ctor_set(v___x_1432_, 1, v_zetaDeltaSet_1421_);
lean_ctor_set(v___x_1432_, 2, v_lctx_1422_);
lean_ctor_set(v___x_1432_, 3, v_localInstances_1423_);
lean_ctor_set(v___x_1432_, 4, v_defEqCtx_x3f_1424_);
lean_ctor_set(v___x_1432_, 5, v_synthPendingDepth_1425_);
lean_ctor_set(v___x_1432_, 6, v_customCanUnfoldPredicate_x3f_1426_);
lean_ctor_set_uint8(v___x_1432_, sizeof(void*)*7, v_trackZetaDelta_1420_);
lean_ctor_set_uint8(v___x_1432_, sizeof(void*)*7 + 1, v_univApprox_1427_);
lean_ctor_set_uint8(v___x_1432_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1428_);
lean_ctor_set_uint8(v___x_1432_, sizeof(void*)*7 + 3, v_cacheInferType_1429_);
v___x_1433_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1389_, v_b_1390_, v___x_1432_, v_a_1392_, v_a_1393_, v_a_1394_);
lean_dec_ref_known(v___x_1432_, 7);
return v___x_1433_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply___boxed(lean_object* v_approx_1436_, lean_object* v_a_1437_, lean_object* v_b_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_){
_start:
{
uint8_t v_approx_boxed_1444_; lean_object* v_res_1445_; 
v_approx_boxed_1444_ = lean_unbox(v_approx_1436_);
v_res_1445_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_approx_boxed_1444_, v_a_1437_, v_b_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_);
lean_dec(v_a_1442_);
lean_dec_ref(v_a_1441_);
lean_dec(v_a_1440_);
lean_dec_ref(v_a_1439_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(lean_object* v_mvarId_1446_, lean_object* v_cfg_1447_, lean_object* v_term_x3f_1448_, lean_object* v_targetType_1449_, lean_object* v_eType_1450_, lean_object* v_rangeNumArgs_1451_, lean_object* v_i_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_){
_start:
{
lean_object* v_conclusionType_x3f_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v_lower_1466_; lean_object* v_upper_1467_; uint8_t v___x_1468_; 
v_lower_1466_ = lean_ctor_get(v_rangeNumArgs_1451_, 0);
v_upper_1467_ = lean_ctor_get(v_rangeNumArgs_1451_, 1);
v___x_1468_ = lean_nat_dec_lt(v_i_1452_, v_upper_1467_);
if (v___x_1468_ == 0)
{
lean_object* v___x_1469_; uint8_t v___x_1470_; 
lean_dec(v_i_1452_);
v___x_1469_ = lean_unsigned_to_nat(0u);
v___x_1470_ = lean_nat_dec_eq(v_lower_1466_, v___x_1469_);
if (v___x_1470_ == 0)
{
lean_object* v___x_1471_; uint8_t v___x_1472_; lean_object* v___x_1473_; 
lean_inc(v_lower_1466_);
v___x_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1471_, 0, v_lower_1466_);
v___x_1472_ = 0;
lean_inc_ref(v_eType_1450_);
v___x_1473_ = l_Lean_Meta_forallMetaTelescopeReducing(v_eType_1450_, v___x_1471_, v___x_1472_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; lean_object* v_snd_1475_; lean_object* v_snd_1476_; lean_object* v___x_1477_; 
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
lean_inc(v_a_1474_);
lean_dec_ref_known(v___x_1473_, 1);
v_snd_1475_ = lean_ctor_get(v_a_1474_, 1);
lean_inc(v_snd_1475_);
lean_dec(v_a_1474_);
v_snd_1476_ = lean_ctor_get(v_snd_1475_, 1);
lean_inc(v_snd_1476_);
lean_dec(v_snd_1475_);
v___x_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1477_, 0, v_snd_1476_);
v_conclusionType_x3f_1459_ = v___x_1477_;
v___y_1460_ = v_a_1453_;
v___y_1461_ = v_a_1454_;
v___y_1462_ = v_a_1455_;
v___y_1463_ = v_a_1456_;
goto v___jp_1458_;
}
else
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1485_; 
lean_dec_ref(v_eType_1450_);
lean_dec_ref(v_targetType_1449_);
lean_dec(v_term_x3f_1448_);
lean_dec(v_mvarId_1446_);
v_a_1478_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1480_ = v___x_1473_;
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1473_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1481_ == 0)
{
v___x_1483_ = v___x_1480_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1478_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
else
{
lean_object* v___x_1486_; 
v___x_1486_ = lean_box(0);
v_conclusionType_x3f_1459_ = v___x_1486_;
v___y_1460_ = v_a_1453_;
v___y_1461_ = v_a_1454_;
v___y_1462_ = v_a_1455_;
v___y_1463_ = v_a_1456_;
goto v___jp_1458_;
}
}
else
{
lean_object* v___x_1487_; 
v___x_1487_ = l_Lean_Meta_saveState___redArg(v_a_1454_, v_a_1456_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v_a_1488_; lean_object* v___x_1489_; uint8_t v___x_1490_; lean_object* v___x_1491_; 
v_a_1488_ = lean_ctor_get(v___x_1487_, 0);
lean_inc(v_a_1488_);
lean_dec_ref_known(v___x_1487_, 1);
lean_inc(v_i_1452_);
v___x_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1489_, 0, v_i_1452_);
v___x_1490_ = 0;
lean_inc_ref(v_eType_1450_);
v___x_1491_ = l_Lean_Meta_forallMetaTelescopeReducing(v_eType_1450_, v___x_1489_, v___x_1490_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v_a_1492_; lean_object* v_snd_1493_; lean_object* v_fst_1494_; lean_object* v_fst_1495_; lean_object* v_snd_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1534_; 
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_a_1492_);
lean_dec_ref_known(v___x_1491_, 1);
v_snd_1493_ = lean_ctor_get(v_a_1492_, 1);
lean_inc(v_snd_1493_);
v_fst_1494_ = lean_ctor_get(v_a_1492_, 0);
lean_inc(v_fst_1494_);
lean_dec(v_a_1492_);
v_fst_1495_ = lean_ctor_get(v_snd_1493_, 0);
v_snd_1496_ = lean_ctor_get(v_snd_1493_, 1);
v_isSharedCheck_1534_ = !lean_is_exclusive(v_snd_1493_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1498_ = v_snd_1493_;
v_isShared_1499_ = v_isSharedCheck_1534_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_snd_1496_);
lean_inc(v_fst_1495_);
lean_dec(v_snd_1493_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1534_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
uint8_t v_approx_1500_; lean_object* v___x_1501_; 
v_approx_1500_ = lean_ctor_get_uint8(v_cfg_1447_, 3);
lean_inc_ref(v_targetType_1449_);
v___x_1501_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_approx_1500_, v_snd_1496_, v_targetType_1449_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1525_; 
v_a_1502_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1504_ = v___x_1501_;
v_isShared_1505_ = v_isSharedCheck_1525_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1501_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1525_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
uint8_t v___x_1506_; 
v___x_1506_ = lean_unbox(v_a_1502_);
lean_dec(v_a_1502_);
if (v___x_1506_ == 0)
{
lean_object* v___x_1507_; 
lean_del_object(v___x_1504_);
lean_del_object(v___x_1498_);
lean_dec(v_fst_1495_);
lean_dec(v_fst_1494_);
v___x_1507_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1488_, v_a_1454_, v_a_1456_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
lean_dec_ref_known(v___x_1507_, 1);
v___x_1508_ = lean_unsigned_to_nat(1u);
v___x_1509_ = lean_nat_add(v_i_1452_, v___x_1508_);
lean_dec(v_i_1452_);
v_i_1452_ = v___x_1509_;
goto _start;
}
else
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1518_; 
lean_dec(v_i_1452_);
lean_dec_ref(v_eType_1450_);
lean_dec_ref(v_targetType_1449_);
lean_dec(v_term_x3f_1448_);
lean_dec(v_mvarId_1446_);
v_a_1511_ = lean_ctor_get(v___x_1507_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1513_ = v___x_1507_;
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1507_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1514_ == 0)
{
v___x_1516_ = v___x_1513_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1511_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
}
else
{
lean_object* v___x_1520_; 
lean_dec(v_a_1488_);
lean_dec(v_i_1452_);
lean_dec_ref(v_eType_1450_);
lean_dec_ref(v_targetType_1449_);
lean_dec(v_term_x3f_1448_);
lean_dec(v_mvarId_1446_);
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 1, v_fst_1495_);
lean_ctor_set(v___x_1498_, 0, v_fst_1494_);
v___x_1520_ = v___x_1498_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_fst_1494_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_fst_1495_);
v___x_1520_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
lean_object* v___x_1522_; 
if (v_isShared_1505_ == 0)
{
lean_ctor_set(v___x_1504_, 0, v___x_1520_);
v___x_1522_ = v___x_1504_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1520_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
}
}
else
{
lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1533_; 
lean_del_object(v___x_1498_);
lean_dec(v_fst_1495_);
lean_dec(v_fst_1494_);
lean_dec(v_a_1488_);
lean_dec(v_i_1452_);
lean_dec_ref(v_eType_1450_);
lean_dec_ref(v_targetType_1449_);
lean_dec(v_term_x3f_1448_);
lean_dec(v_mvarId_1446_);
v_a_1526_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1528_ = v___x_1501_;
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_a_1526_);
lean_dec(v___x_1501_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1531_; 
if (v_isShared_1529_ == 0)
{
v___x_1531_ = v___x_1528_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_a_1526_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
}
}
else
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1542_; 
lean_dec(v_a_1488_);
lean_dec(v_i_1452_);
lean_dec_ref(v_eType_1450_);
lean_dec_ref(v_targetType_1449_);
lean_dec(v_term_x3f_1448_);
lean_dec(v_mvarId_1446_);
v_a_1535_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1537_ = v___x_1491_;
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1491_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1540_; 
if (v_isShared_1538_ == 0)
{
v___x_1540_ = v___x_1537_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_a_1535_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
else
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1550_; 
lean_dec(v_i_1452_);
lean_dec_ref(v_eType_1450_);
lean_dec_ref(v_targetType_1449_);
lean_dec(v_term_x3f_1448_);
lean_dec(v_mvarId_1446_);
v_a_1543_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1545_ = v___x_1487_;
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1487_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1548_; 
if (v_isShared_1546_ == 0)
{
v___x_1548_ = v___x_1545_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_a_1543_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
v___jp_1458_:
{
uint8_t v_approx_1464_; lean_object* v___x_1465_; 
v_approx_1464_ = lean_ctor_get_uint8(v_cfg_1447_, 3);
v___x_1465_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_1446_, v_eType_1450_, v_conclusionType_x3f_1459_, v_targetType_1449_, v_term_x3f_1448_, v_approx_1464_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
return v___x_1465_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go___boxed(lean_object* v_mvarId_1551_, lean_object* v_cfg_1552_, lean_object* v_term_x3f_1553_, lean_object* v_targetType_1554_, lean_object* v_eType_1555_, lean_object* v_rangeNumArgs_1556_, lean_object* v_i_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(v_mvarId_1551_, v_cfg_1552_, v_term_x3f_1553_, v_targetType_1554_, v_eType_1555_, v_rangeNumArgs_1556_, v_i_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_);
lean_dec(v_a_1561_);
lean_dec_ref(v_a_1560_);
lean_dec(v_a_1559_);
lean_dec_ref(v_a_1558_);
lean_dec_ref(v_rangeNumArgs_1556_);
lean_dec_ref(v_cfg_1552_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go_match__1_splitter___redArg(lean_object* v_x_1564_, lean_object* v_h__1_1565_){
_start:
{
lean_object* v_snd_1566_; lean_object* v_fst_1567_; lean_object* v_fst_1568_; lean_object* v_snd_1569_; lean_object* v___x_1570_; 
v_snd_1566_ = lean_ctor_get(v_x_1564_, 1);
lean_inc(v_snd_1566_);
v_fst_1567_ = lean_ctor_get(v_x_1564_, 0);
lean_inc(v_fst_1567_);
lean_dec_ref(v_x_1564_);
v_fst_1568_ = lean_ctor_get(v_snd_1566_, 0);
lean_inc(v_fst_1568_);
v_snd_1569_ = lean_ctor_get(v_snd_1566_, 1);
lean_inc(v_snd_1569_);
lean_dec(v_snd_1566_);
v___x_1570_ = lean_apply_3(v_h__1_1565_, v_fst_1567_, v_fst_1568_, v_snd_1569_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go_match__1_splitter(lean_object* v_motive_1571_, lean_object* v_x_1572_, lean_object* v_h__1_1573_){
_start:
{
lean_object* v_snd_1574_; lean_object* v_fst_1575_; lean_object* v_fst_1576_; lean_object* v_snd_1577_; lean_object* v___x_1578_; 
v_snd_1574_ = lean_ctor_get(v_x_1572_, 1);
lean_inc(v_snd_1574_);
v_fst_1575_ = lean_ctor_get(v_x_1572_, 0);
lean_inc(v_fst_1575_);
lean_dec_ref(v_x_1572_);
v_fst_1576_ = lean_ctor_get(v_snd_1574_, 0);
lean_inc(v_fst_1576_);
v_snd_1577_ = lean_ctor_get(v_snd_1574_, 1);
lean_inc(v_snd_1577_);
lean_dec(v_snd_1574_);
v___x_1578_ = lean_apply_3(v_h__1_1573_, v_fst_1575_, v_fst_1576_, v_snd_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(lean_object* v_e_1579_, lean_object* v___y_1580_){
_start:
{
uint8_t v___x_1582_; 
v___x_1582_ = l_Lean_Expr_hasMVar(v_e_1579_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1583_; 
v___x_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1583_, 0, v_e_1579_);
return v___x_1583_;
}
else
{
lean_object* v___x_1584_; lean_object* v_mctx_1585_; lean_object* v___x_1586_; lean_object* v_fst_1587_; lean_object* v_snd_1588_; lean_object* v___x_1589_; lean_object* v_cache_1590_; lean_object* v_zetaDeltaFVarIds_1591_; lean_object* v_postponed_1592_; lean_object* v_diag_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1602_; 
v___x_1584_ = lean_st_ref_get(v___y_1580_);
v_mctx_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc_ref(v_mctx_1585_);
lean_dec(v___x_1584_);
v___x_1586_ = l_Lean_instantiateMVarsCore(v_mctx_1585_, v_e_1579_);
v_fst_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_fst_1587_);
v_snd_1588_ = lean_ctor_get(v___x_1586_, 1);
lean_inc(v_snd_1588_);
lean_dec_ref(v___x_1586_);
v___x_1589_ = lean_st_ref_take(v___y_1580_);
v_cache_1590_ = lean_ctor_get(v___x_1589_, 1);
v_zetaDeltaFVarIds_1591_ = lean_ctor_get(v___x_1589_, 2);
v_postponed_1592_ = lean_ctor_get(v___x_1589_, 3);
v_diag_1593_ = lean_ctor_get(v___x_1589_, 4);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1602_ == 0)
{
lean_object* v_unused_1603_; 
v_unused_1603_ = lean_ctor_get(v___x_1589_, 0);
lean_dec(v_unused_1603_);
v___x_1595_ = v___x_1589_;
v_isShared_1596_ = v_isSharedCheck_1602_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_diag_1593_);
lean_inc(v_postponed_1592_);
lean_inc(v_zetaDeltaFVarIds_1591_);
lean_inc(v_cache_1590_);
lean_dec(v___x_1589_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1602_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 0, v_snd_1588_);
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_snd_1588_);
lean_ctor_set(v_reuseFailAlloc_1601_, 1, v_cache_1590_);
lean_ctor_set(v_reuseFailAlloc_1601_, 2, v_zetaDeltaFVarIds_1591_);
lean_ctor_set(v_reuseFailAlloc_1601_, 3, v_postponed_1592_);
lean_ctor_set(v_reuseFailAlloc_1601_, 4, v_diag_1593_);
v___x_1598_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1599_ = lean_st_ref_put(v___y_1580_, v___x_1598_);
v___x_1600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1600_, 0, v_fst_1587_);
return v___x_1600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg___boxed(lean_object* v_e_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_1604_, v___y_1605_);
lean_dec(v___y_1605_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0(lean_object* v_e_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_1608_, v___y_1610_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___boxed(lean_object* v_e_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0(v_e_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(lean_object* v_mvarId_1622_, lean_object* v_x_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
lean_object* v___x_1629_; 
v___x_1629_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1622_, v_x_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1629_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1629_);
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
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
v_a_1638_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1640_ = v___x_1629_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1629_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg___boxed(lean_object* v_mvarId_1646_, lean_object* v_x_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_1646_, v_x_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
lean_dec(v___y_1649_);
lean_dec_ref(v___y_1648_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6(lean_object* v_00_u03b1_1654_, lean_object* v_mvarId_1655_, lean_object* v_x_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_1655_, v_x_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___boxed(lean_object* v_00_u03b1_1663_, lean_object* v_mvarId_1664_, lean_object* v_x_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6(v_00_u03b1_1663_, v_mvarId_1664_, v_x_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(lean_object* v_as_1672_, size_t v_i_1673_, size_t v_stop_1674_, lean_object* v_b_1675_, lean_object* v___y_1676_){
_start:
{
lean_object* v_a_1679_; uint8_t v___x_1683_; 
v___x_1683_ = lean_usize_dec_eq(v_i_1673_, v_stop_1674_);
if (v___x_1683_ == 0)
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1684_ = lean_array_uget_borrowed(v_as_1672_, v_i_1673_);
v___x_1685_ = l_Lean_Expr_mvarId_x21(v___x_1684_);
v___x_1686_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_1685_, v___y_1676_);
lean_dec(v___x_1685_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v_a_1687_; uint8_t v___x_1688_; 
v_a_1687_ = lean_ctor_get(v___x_1686_, 0);
lean_inc(v_a_1687_);
lean_dec_ref_known(v___x_1686_, 1);
v___x_1688_ = lean_unbox(v_a_1687_);
lean_dec(v_a_1687_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; 
lean_inc(v___x_1684_);
v___x_1689_ = lean_array_push(v_b_1675_, v___x_1684_);
v_a_1679_ = v___x_1689_;
goto v___jp_1678_;
}
else
{
v_a_1679_ = v_b_1675_;
goto v___jp_1678_;
}
}
else
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1697_; 
lean_dec_ref(v_b_1675_);
v_a_1690_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1692_ = v___x_1686_;
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1686_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1690_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
}
else
{
lean_object* v___x_1698_; 
v___x_1698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1698_, 0, v_b_1675_);
return v___x_1698_;
}
v___jp_1678_:
{
size_t v___x_1680_; size_t v___x_1681_; 
v___x_1680_ = ((size_t)1ULL);
v___x_1681_ = lean_usize_add(v_i_1673_, v___x_1680_);
v_i_1673_ = v___x_1681_;
v_b_1675_ = v_a_1679_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg___boxed(lean_object* v_as_1699_, lean_object* v_i_1700_, lean_object* v_stop_1701_, lean_object* v_b_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
size_t v_i_boxed_1705_; size_t v_stop_boxed_1706_; lean_object* v_res_1707_; 
v_i_boxed_1705_ = lean_unbox_usize(v_i_1700_);
lean_dec(v_i_1700_);
v_stop_boxed_1706_ = lean_unbox_usize(v_stop_1701_);
lean_dec(v_stop_1701_);
v_res_1707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_as_1699_, v_i_boxed_1705_, v_stop_boxed_1706_, v_b_1702_, v___y_1703_);
lean_dec(v___y_1703_);
lean_dec_ref(v_as_1699_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_apply_spec__3(lean_object* v_as_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
if (lean_obj_tag(v_as_1708_) == 0)
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1714_ = lean_box(0);
v___x_1715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1714_);
return v___x_1715_;
}
else
{
lean_object* v_head_1716_; lean_object* v_tail_1717_; lean_object* v___x_1718_; 
v_head_1716_ = lean_ctor_get(v_as_1708_, 0);
lean_inc(v_head_1716_);
v_tail_1717_ = lean_ctor_get(v_as_1708_, 1);
lean_inc(v_tail_1717_);
lean_dec_ref_known(v_as_1708_, 2);
v___x_1718_ = l_Lean_MVarId_headBetaType(v_head_1716_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_dec_ref_known(v___x_1718_, 1);
v_as_1708_ = v_tail_1717_;
goto _start;
}
else
{
lean_dec(v_tail_1717_);
return v___x_1718_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_apply_spec__3___boxed(lean_object* v_as_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_List_forM___at___00Lean_MVarId_apply_spec__3(v_as_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(lean_object* v_x_1727_, lean_object* v_x_1728_, lean_object* v_x_1729_, lean_object* v_x_1730_){
_start:
{
lean_object* v_ks_1731_; lean_object* v_vs_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1756_; 
v_ks_1731_ = lean_ctor_get(v_x_1727_, 0);
v_vs_1732_ = lean_ctor_get(v_x_1727_, 1);
v_isSharedCheck_1756_ = !lean_is_exclusive(v_x_1727_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1734_ = v_x_1727_;
v_isShared_1735_ = v_isSharedCheck_1756_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_vs_1732_);
lean_inc(v_ks_1731_);
lean_dec(v_x_1727_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1756_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1736_; uint8_t v___x_1737_; 
v___x_1736_ = lean_array_get_size(v_ks_1731_);
v___x_1737_ = lean_nat_dec_lt(v_x_1728_, v___x_1736_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1741_; 
lean_dec(v_x_1728_);
v___x_1738_ = lean_array_push(v_ks_1731_, v_x_1729_);
v___x_1739_ = lean_array_push(v_vs_1732_, v_x_1730_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 1, v___x_1739_);
lean_ctor_set(v___x_1734_, 0, v___x_1738_);
v___x_1741_ = v___x_1734_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v___x_1738_);
lean_ctor_set(v_reuseFailAlloc_1742_, 1, v___x_1739_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
else
{
lean_object* v_k_x27_1743_; uint8_t v___x_1744_; 
v_k_x27_1743_ = lean_array_fget_borrowed(v_ks_1731_, v_x_1728_);
v___x_1744_ = l_Lean_instBEqMVarId_beq(v_x_1729_, v_k_x27_1743_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1746_; 
if (v_isShared_1735_ == 0)
{
v___x_1746_ = v___x_1734_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_ks_1731_);
lean_ctor_set(v_reuseFailAlloc_1750_, 1, v_vs_1732_);
v___x_1746_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1747_ = lean_unsigned_to_nat(1u);
v___x_1748_ = lean_nat_add(v_x_1728_, v___x_1747_);
lean_dec(v_x_1728_);
v_x_1727_ = v___x_1746_;
v_x_1728_ = v___x_1748_;
goto _start;
}
}
else
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1754_; 
v___x_1751_ = lean_array_fset(v_ks_1731_, v_x_1728_, v_x_1729_);
v___x_1752_ = lean_array_fset(v_vs_1732_, v_x_1728_, v_x_1730_);
lean_dec(v_x_1728_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 1, v___x_1752_);
lean_ctor_set(v___x_1734_, 0, v___x_1751_);
v___x_1754_ = v___x_1734_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v___x_1751_);
lean_ctor_set(v_reuseFailAlloc_1755_, 1, v___x_1752_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(lean_object* v_n_1757_, lean_object* v_k_1758_, lean_object* v_v_1759_){
_start:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1760_ = lean_unsigned_to_nat(0u);
v___x_1761_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(v_n_1757_, v___x_1760_, v_k_1758_, v_v_1759_);
return v___x_1761_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(lean_object* v_x_1763_, size_t v_x_1764_, size_t v_x_1765_, lean_object* v_x_1766_, lean_object* v_x_1767_){
_start:
{
if (lean_obj_tag(v_x_1763_) == 0)
{
lean_object* v_es_1768_; size_t v___x_1769_; size_t v___x_1770_; lean_object* v_j_1771_; lean_object* v___x_1772_; uint8_t v___x_1773_; 
v_es_1768_ = lean_ctor_get(v_x_1763_, 0);
v___x_1769_ = ((size_t)31ULL);
v___x_1770_ = lean_usize_land(v_x_1764_, v___x_1769_);
v_j_1771_ = lean_usize_to_nat(v___x_1770_);
v___x_1772_ = lean_array_get_size(v_es_1768_);
v___x_1773_ = lean_nat_dec_lt(v_j_1771_, v___x_1772_);
if (v___x_1773_ == 0)
{
lean_dec(v_j_1771_);
lean_dec(v_x_1767_);
lean_dec(v_x_1766_);
return v_x_1763_;
}
else
{
lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1812_; 
lean_inc_ref(v_es_1768_);
v_isSharedCheck_1812_ = !lean_is_exclusive(v_x_1763_);
if (v_isSharedCheck_1812_ == 0)
{
lean_object* v_unused_1813_; 
v_unused_1813_ = lean_ctor_get(v_x_1763_, 0);
lean_dec(v_unused_1813_);
v___x_1775_ = v_x_1763_;
v_isShared_1776_ = v_isSharedCheck_1812_;
goto v_resetjp_1774_;
}
else
{
lean_dec(v_x_1763_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1812_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v_v_1777_; lean_object* v___x_1778_; lean_object* v_xs_x27_1779_; lean_object* v___y_1781_; 
v_v_1777_ = lean_array_fget(v_es_1768_, v_j_1771_);
v___x_1778_ = lean_box(0);
v_xs_x27_1779_ = lean_array_fset(v_es_1768_, v_j_1771_, v___x_1778_);
switch(lean_obj_tag(v_v_1777_))
{
case 0:
{
lean_object* v_key_1786_; lean_object* v_val_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1797_; 
v_key_1786_ = lean_ctor_get(v_v_1777_, 0);
v_val_1787_ = lean_ctor_get(v_v_1777_, 1);
v_isSharedCheck_1797_ = !lean_is_exclusive(v_v_1777_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1789_ = v_v_1777_;
v_isShared_1790_ = v_isSharedCheck_1797_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_val_1787_);
lean_inc(v_key_1786_);
lean_dec(v_v_1777_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1797_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
uint8_t v___x_1791_; 
v___x_1791_ = l_Lean_instBEqMVarId_beq(v_x_1766_, v_key_1786_);
if (v___x_1791_ == 0)
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
lean_del_object(v___x_1789_);
v___x_1792_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1786_, v_val_1787_, v_x_1766_, v_x_1767_);
v___x_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1792_);
v___y_1781_ = v___x_1793_;
goto v___jp_1780_;
}
else
{
lean_object* v___x_1795_; 
lean_dec(v_val_1787_);
lean_dec(v_key_1786_);
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 1, v_x_1767_);
lean_ctor_set(v___x_1789_, 0, v_x_1766_);
v___x_1795_ = v___x_1789_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_x_1766_);
lean_ctor_set(v_reuseFailAlloc_1796_, 1, v_x_1767_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
v___y_1781_ = v___x_1795_;
goto v___jp_1780_;
}
}
}
}
case 1:
{
lean_object* v_node_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1810_; 
v_node_1798_ = lean_ctor_get(v_v_1777_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v_v_1777_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1800_ = v_v_1777_;
v_isShared_1801_ = v_isSharedCheck_1810_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_node_1798_);
lean_dec(v_v_1777_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1810_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
size_t v___x_1802_; size_t v___x_1803_; size_t v___x_1804_; size_t v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1808_; 
v___x_1802_ = ((size_t)5ULL);
v___x_1803_ = lean_usize_shift_right(v_x_1764_, v___x_1802_);
v___x_1804_ = ((size_t)1ULL);
v___x_1805_ = lean_usize_add(v_x_1765_, v___x_1804_);
v___x_1806_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_node_1798_, v___x_1803_, v___x_1805_, v_x_1766_, v_x_1767_);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 0, v___x_1806_);
v___x_1808_ = v___x_1800_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1806_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
v___y_1781_ = v___x_1808_;
goto v___jp_1780_;
}
}
}
default: 
{
lean_object* v___x_1811_; 
v___x_1811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1811_, 0, v_x_1766_);
lean_ctor_set(v___x_1811_, 1, v_x_1767_);
v___y_1781_ = v___x_1811_;
goto v___jp_1780_;
}
}
v___jp_1780_:
{
lean_object* v___x_1782_; lean_object* v___x_1784_; 
v___x_1782_ = lean_array_fset(v_xs_x27_1779_, v_j_1771_, v___y_1781_);
lean_dec(v_j_1771_);
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 0, v___x_1782_);
v___x_1784_ = v___x_1775_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1782_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
}
else
{
lean_object* v_ks_1814_; lean_object* v_vs_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1833_; 
v_ks_1814_ = lean_ctor_get(v_x_1763_, 0);
v_vs_1815_ = lean_ctor_get(v_x_1763_, 1);
v_isSharedCheck_1833_ = !lean_is_exclusive(v_x_1763_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1817_ = v_x_1763_;
v_isShared_1818_ = v_isSharedCheck_1833_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_vs_1815_);
lean_inc(v_ks_1814_);
lean_dec(v_x_1763_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1833_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1820_; 
if (v_isShared_1818_ == 0)
{
v___x_1820_ = v___x_1817_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_ks_1814_);
lean_ctor_set(v_reuseFailAlloc_1832_, 1, v_vs_1815_);
v___x_1820_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
lean_object* v_newNode_1821_; size_t v___x_1822_; uint8_t v___x_1823_; 
v_newNode_1821_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(v___x_1820_, v_x_1766_, v_x_1767_);
v___x_1822_ = ((size_t)7ULL);
v___x_1823_ = lean_usize_dec_le(v___x_1822_, v_x_1765_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; lean_object* v___x_1825_; uint8_t v___x_1826_; 
v___x_1824_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1821_);
v___x_1825_ = lean_unsigned_to_nat(4u);
v___x_1826_ = lean_nat_dec_lt(v___x_1824_, v___x_1825_);
lean_dec(v___x_1824_);
if (v___x_1826_ == 0)
{
lean_object* v_ks_1827_; lean_object* v_vs_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v_ks_1827_ = lean_ctor_get(v_newNode_1821_, 0);
lean_inc_ref(v_ks_1827_);
v_vs_1828_ = lean_ctor_get(v_newNode_1821_, 1);
lean_inc_ref(v_vs_1828_);
lean_dec_ref(v_newNode_1821_);
v___x_1829_ = lean_unsigned_to_nat(0u);
v___x_1830_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_1831_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_x_1765_, v_ks_1827_, v_vs_1828_, v___x_1829_, v___x_1830_);
lean_dec_ref(v_vs_1828_);
lean_dec_ref(v_ks_1827_);
return v___x_1831_;
}
else
{
return v_newNode_1821_;
}
}
else
{
return v_newNode_1821_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(size_t v_depth_1834_, lean_object* v_keys_1835_, lean_object* v_vals_1836_, lean_object* v_i_1837_, lean_object* v_entries_1838_){
_start:
{
lean_object* v___x_1839_; uint8_t v___x_1840_; 
v___x_1839_ = lean_array_get_size(v_keys_1835_);
v___x_1840_ = lean_nat_dec_lt(v_i_1837_, v___x_1839_);
if (v___x_1840_ == 0)
{
lean_dec(v_i_1837_);
return v_entries_1838_;
}
else
{
lean_object* v_k_1841_; lean_object* v_v_1842_; uint64_t v___x_1843_; size_t v_h_1844_; size_t v___x_1845_; lean_object* v___x_1846_; size_t v___x_1847_; size_t v___x_1848_; size_t v___x_1849_; size_t v_h_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v_k_1841_ = lean_array_fget_borrowed(v_keys_1835_, v_i_1837_);
v_v_1842_ = lean_array_fget_borrowed(v_vals_1836_, v_i_1837_);
v___x_1843_ = l_Lean_instHashableMVarId_hash(v_k_1841_);
v_h_1844_ = lean_uint64_to_usize(v___x_1843_);
v___x_1845_ = ((size_t)5ULL);
v___x_1846_ = lean_unsigned_to_nat(1u);
v___x_1847_ = ((size_t)1ULL);
v___x_1848_ = lean_usize_sub(v_depth_1834_, v___x_1847_);
v___x_1849_ = lean_usize_mul(v___x_1845_, v___x_1848_);
v_h_1850_ = lean_usize_shift_right(v_h_1844_, v___x_1849_);
v___x_1851_ = lean_nat_add(v_i_1837_, v___x_1846_);
lean_dec(v_i_1837_);
lean_inc(v_v_1842_);
lean_inc(v_k_1841_);
v___x_1852_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_entries_1838_, v_h_1850_, v_depth_1834_, v_k_1841_, v_v_1842_);
v_i_1837_ = v___x_1851_;
v_entries_1838_ = v___x_1852_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg___boxed(lean_object* v_depth_1854_, lean_object* v_keys_1855_, lean_object* v_vals_1856_, lean_object* v_i_1857_, lean_object* v_entries_1858_){
_start:
{
size_t v_depth_boxed_1859_; lean_object* v_res_1860_; 
v_depth_boxed_1859_ = lean_unbox_usize(v_depth_1854_);
lean_dec(v_depth_1854_);
v_res_1860_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_depth_boxed_1859_, v_keys_1855_, v_vals_1856_, v_i_1857_, v_entries_1858_);
lean_dec_ref(v_vals_1856_);
lean_dec_ref(v_keys_1855_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_1861_, lean_object* v_x_1862_, lean_object* v_x_1863_, lean_object* v_x_1864_, lean_object* v_x_1865_){
_start:
{
size_t v_x_7048__boxed_1866_; size_t v_x_7049__boxed_1867_; lean_object* v_res_1868_; 
v_x_7048__boxed_1866_ = lean_unbox_usize(v_x_1862_);
lean_dec(v_x_1862_);
v_x_7049__boxed_1867_ = lean_unbox_usize(v_x_1863_);
lean_dec(v_x_1863_);
v_res_1868_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_1861_, v_x_7048__boxed_1866_, v_x_7049__boxed_1867_, v_x_1864_, v_x_1865_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(lean_object* v_x_1869_, lean_object* v_x_1870_, lean_object* v_x_1871_){
_start:
{
uint64_t v___x_1872_; size_t v___x_1873_; size_t v___x_1874_; lean_object* v___x_1875_; 
v___x_1872_ = l_Lean_instHashableMVarId_hash(v_x_1870_);
v___x_1873_ = lean_uint64_to_usize(v___x_1872_);
v___x_1874_ = ((size_t)1ULL);
v___x_1875_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_1869_, v___x_1873_, v___x_1874_, v_x_1870_, v_x_1871_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(lean_object* v_mvarId_1876_, lean_object* v_val_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v___x_1880_; lean_object* v_mctx_1881_; lean_object* v_cache_1882_; lean_object* v_zetaDeltaFVarIds_1883_; lean_object* v_postponed_1884_; lean_object* v_diag_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1914_; 
v___x_1880_ = lean_st_ref_take(v___y_1878_);
v_mctx_1881_ = lean_ctor_get(v___x_1880_, 0);
v_cache_1882_ = lean_ctor_get(v___x_1880_, 1);
v_zetaDeltaFVarIds_1883_ = lean_ctor_get(v___x_1880_, 2);
v_postponed_1884_ = lean_ctor_get(v___x_1880_, 3);
v_diag_1885_ = lean_ctor_get(v___x_1880_, 4);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1887_ = v___x_1880_;
v_isShared_1888_ = v_isSharedCheck_1914_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_diag_1885_);
lean_inc(v_postponed_1884_);
lean_inc(v_zetaDeltaFVarIds_1883_);
lean_inc(v_cache_1882_);
lean_inc(v_mctx_1881_);
lean_dec(v___x_1880_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1914_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v_depth_1889_; lean_object* v_levelAssignDepth_1890_; lean_object* v_lmvarCounter_1891_; lean_object* v_mvarCounter_1892_; lean_object* v_lDecls_1893_; lean_object* v_decls_1894_; lean_object* v_userNames_1895_; lean_object* v_lAssignment_1896_; lean_object* v_eAssignment_1897_; lean_object* v_dAssignment_1898_; lean_object* v_synthNormMemo_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1913_; 
v_depth_1889_ = lean_ctor_get(v_mctx_1881_, 0);
v_levelAssignDepth_1890_ = lean_ctor_get(v_mctx_1881_, 1);
v_lmvarCounter_1891_ = lean_ctor_get(v_mctx_1881_, 2);
v_mvarCounter_1892_ = lean_ctor_get(v_mctx_1881_, 3);
v_lDecls_1893_ = lean_ctor_get(v_mctx_1881_, 4);
v_decls_1894_ = lean_ctor_get(v_mctx_1881_, 5);
v_userNames_1895_ = lean_ctor_get(v_mctx_1881_, 6);
v_lAssignment_1896_ = lean_ctor_get(v_mctx_1881_, 7);
v_eAssignment_1897_ = lean_ctor_get(v_mctx_1881_, 8);
v_dAssignment_1898_ = lean_ctor_get(v_mctx_1881_, 9);
v_synthNormMemo_1899_ = lean_ctor_get(v_mctx_1881_, 10);
v_isSharedCheck_1913_ = !lean_is_exclusive(v_mctx_1881_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1901_ = v_mctx_1881_;
v_isShared_1902_ = v_isSharedCheck_1913_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_synthNormMemo_1899_);
lean_inc(v_dAssignment_1898_);
lean_inc(v_eAssignment_1897_);
lean_inc(v_lAssignment_1896_);
lean_inc(v_userNames_1895_);
lean_inc(v_decls_1894_);
lean_inc(v_lDecls_1893_);
lean_inc(v_mvarCounter_1892_);
lean_inc(v_lmvarCounter_1891_);
lean_inc(v_levelAssignDepth_1890_);
lean_inc(v_depth_1889_);
lean_dec(v_mctx_1881_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1913_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1906_; 
v___x_1903_ = lean_box(0);
v___x_1904_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(v_eAssignment_1897_, v_mvarId_1876_, v_val_1877_);
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 8, v___x_1904_);
v___x_1906_ = v___x_1901_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_depth_1889_);
lean_ctor_set(v_reuseFailAlloc_1912_, 1, v_levelAssignDepth_1890_);
lean_ctor_set(v_reuseFailAlloc_1912_, 2, v_lmvarCounter_1891_);
lean_ctor_set(v_reuseFailAlloc_1912_, 3, v_mvarCounter_1892_);
lean_ctor_set(v_reuseFailAlloc_1912_, 4, v_lDecls_1893_);
lean_ctor_set(v_reuseFailAlloc_1912_, 5, v_decls_1894_);
lean_ctor_set(v_reuseFailAlloc_1912_, 6, v_userNames_1895_);
lean_ctor_set(v_reuseFailAlloc_1912_, 7, v_lAssignment_1896_);
lean_ctor_set(v_reuseFailAlloc_1912_, 8, v___x_1904_);
lean_ctor_set(v_reuseFailAlloc_1912_, 9, v_dAssignment_1898_);
lean_ctor_set(v_reuseFailAlloc_1912_, 10, v_synthNormMemo_1899_);
v___x_1906_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
lean_object* v___x_1908_; 
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 0, v___x_1906_);
v___x_1908_ = v___x_1887_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1906_);
lean_ctor_set(v_reuseFailAlloc_1911_, 1, v_cache_1882_);
lean_ctor_set(v_reuseFailAlloc_1911_, 2, v_zetaDeltaFVarIds_1883_);
lean_ctor_set(v_reuseFailAlloc_1911_, 3, v_postponed_1884_);
lean_ctor_set(v_reuseFailAlloc_1911_, 4, v_diag_1885_);
v___x_1908_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1909_ = lean_st_ref_put(v___y_1878_, v___x_1908_);
v___x_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1903_);
return v___x_1910_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg___boxed(lean_object* v_mvarId_1915_, lean_object* v_val_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_){
_start:
{
lean_object* v_res_1919_; 
v_res_1919_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_1915_, v_val_1916_, v___y_1917_);
lean_dec(v___y_1917_);
return v_res_1919_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_MVarId_apply_spec__2(lean_object* v_a_1920_, lean_object* v_x_1921_){
_start:
{
if (lean_obj_tag(v_x_1921_) == 0)
{
uint8_t v___x_1922_; 
v___x_1922_ = 0;
return v___x_1922_;
}
else
{
lean_object* v_head_1923_; lean_object* v_tail_1924_; uint8_t v___x_1925_; 
v_head_1923_ = lean_ctor_get(v_x_1921_, 0);
v_tail_1924_ = lean_ctor_get(v_x_1921_, 1);
v___x_1925_ = l_Lean_instBEqMVarId_beq(v_a_1920_, v_head_1923_);
if (v___x_1925_ == 0)
{
v_x_1921_ = v_tail_1924_;
goto _start;
}
else
{
return v___x_1925_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_MVarId_apply_spec__2___boxed(lean_object* v_a_1927_, lean_object* v_x_1928_){
_start:
{
uint8_t v_res_1929_; lean_object* v_r_1930_; 
v_res_1929_ = l_List_elem___at___00Lean_MVarId_apply_spec__2(v_a_1927_, v_x_1928_);
lean_dec(v_x_1928_);
lean_dec(v_a_1927_);
v_r_1930_ = lean_box(v_res_1929_);
return v_r_1930_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(lean_object* v_a_1931_, lean_object* v_as_1932_, size_t v_i_1933_, size_t v_stop_1934_, lean_object* v_b_1935_){
_start:
{
lean_object* v___y_1937_; uint8_t v___x_1941_; 
v___x_1941_ = lean_usize_dec_eq(v_i_1933_, v_stop_1934_);
if (v___x_1941_ == 0)
{
lean_object* v___x_1942_; uint8_t v___x_1943_; 
v___x_1942_ = lean_array_uget_borrowed(v_as_1932_, v_i_1933_);
v___x_1943_ = l_List_elem___at___00Lean_MVarId_apply_spec__2(v___x_1942_, v_a_1931_);
if (v___x_1943_ == 0)
{
lean_object* v___x_1944_; 
lean_inc(v___x_1942_);
v___x_1944_ = lean_array_push(v_b_1935_, v___x_1942_);
v___y_1937_ = v___x_1944_;
goto v___jp_1936_;
}
else
{
v___y_1937_ = v_b_1935_;
goto v___jp_1936_;
}
}
else
{
return v_b_1935_;
}
v___jp_1936_:
{
size_t v___x_1938_; size_t v___x_1939_; 
v___x_1938_ = ((size_t)1ULL);
v___x_1939_ = lean_usize_add(v_i_1933_, v___x_1938_);
v_i_1933_ = v___x_1939_;
v_b_1935_ = v___y_1937_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4___boxed(lean_object* v_a_1945_, lean_object* v_as_1946_, lean_object* v_i_1947_, lean_object* v_stop_1948_, lean_object* v_b_1949_){
_start:
{
size_t v_i_boxed_1950_; size_t v_stop_boxed_1951_; lean_object* v_res_1952_; 
v_i_boxed_1950_ = lean_unbox_usize(v_i_1947_);
lean_dec(v_i_1947_);
v_stop_boxed_1951_ = lean_unbox_usize(v_stop_1948_);
lean_dec(v_stop_1948_);
v_res_1952_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_1945_, v_as_1946_, v_i_boxed_1950_, v_stop_boxed_1951_, v_b_1949_);
lean_dec_ref(v_as_1946_);
lean_dec(v_a_1945_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lam__0(lean_object* v_mvarId_1953_, lean_object* v___x_1954_, lean_object* v_e_1955_, lean_object* v_cfg_1956_, lean_object* v_term_x3f_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1968_; lean_object* v___y_1969_; lean_object* v___y_1990_; uint8_t v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v_a_1998_; lean_object* v___x_2026_; 
lean_inc(v___x_1954_);
lean_inc(v_mvarId_1953_);
v___x_2026_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1953_, v___x_1954_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v___x_2027_; 
lean_dec_ref_known(v___x_2026_, 1);
lean_inc(v_mvarId_1953_);
v___x_2027_ = l_Lean_MVarId_getType(v_mvarId_1953_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2029_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_a_2028_);
lean_dec_ref_known(v___x_2027_, 1);
lean_inc(v___y_1961_);
lean_inc_ref(v___y_1960_);
lean_inc(v___y_1959_);
lean_inc_ref(v___y_1958_);
lean_inc_ref(v_e_1955_);
v___x_2029_ = lean_infer_type(v_e_1955_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v_a_2030_; lean_object* v_rangeNumArgs_2032_; lean_object* v_lower_2033_; lean_object* v___y_2034_; lean_object* v___y_2035_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___x_2082_; 
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
lean_inc_n(v_a_2030_, 2);
lean_dec_ref_known(v___x_2029_, 1);
v___x_2082_ = l_Lean_Meta_getExpectedNumArgsAux(v_a_2030_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v_a_2083_; lean_object* v_snd_2084_; uint8_t v___x_2085_; 
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
lean_inc(v_a_2083_);
lean_dec_ref_known(v___x_2082_, 1);
v_snd_2084_ = lean_ctor_get(v_a_2083_, 1);
v___x_2085_ = lean_unbox(v_snd_2084_);
if (v___x_2085_ == 0)
{
lean_object* v_fst_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2106_; 
v_fst_2086_ = lean_ctor_get(v_a_2083_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v_a_2083_);
if (v_isSharedCheck_2106_ == 0)
{
lean_object* v_unused_2107_; 
v_unused_2107_ = lean_ctor_get(v_a_2083_, 1);
lean_dec(v_unused_2107_);
v___x_2088_ = v_a_2083_;
v_isShared_2089_ = v_isSharedCheck_2106_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_fst_2086_);
lean_dec(v_a_2083_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2106_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2090_; 
lean_inc(v_a_2028_);
v___x_2090_ = l_Lean_Meta_getExpectedNumArgs(v_a_2028_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_a_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2096_; 
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_a_2091_);
lean_dec_ref_known(v___x_2090_, 1);
v___x_2092_ = lean_nat_sub(v_fst_2086_, v_a_2091_);
lean_dec(v_a_2091_);
v___x_2093_ = lean_unsigned_to_nat(1u);
v___x_2094_ = lean_nat_add(v_fst_2086_, v___x_2093_);
lean_dec(v_fst_2086_);
lean_inc(v___x_2092_);
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 1, v___x_2094_);
lean_ctor_set(v___x_2088_, 0, v___x_2092_);
v___x_2096_ = v___x_2088_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v___x_2092_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v___x_2094_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
v_rangeNumArgs_2032_ = v___x_2096_;
v_lower_2033_ = v___x_2092_;
v___y_2034_ = v___y_1958_;
v___y_2035_ = v___y_1959_;
v___y_2036_ = v___y_1960_;
v___y_2037_ = v___y_1961_;
goto v___jp_2031_;
}
}
else
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2105_; 
lean_del_object(v___x_2088_);
lean_dec(v_fst_2086_);
lean_dec(v_a_2030_);
lean_dec(v_a_2028_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v_term_x3f_1957_);
lean_dec_ref(v_e_1955_);
lean_dec(v___x_1954_);
lean_dec(v_mvarId_1953_);
v_a_2098_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2100_ = v___x_2090_;
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2090_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2103_; 
if (v_isShared_2101_ == 0)
{
v___x_2103_ = v___x_2100_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_a_2098_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
}
else
{
lean_object* v_fst_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2117_; 
v_fst_2108_ = lean_ctor_get(v_a_2083_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v_a_2083_);
if (v_isSharedCheck_2117_ == 0)
{
lean_object* v_unused_2118_; 
v_unused_2118_ = lean_ctor_get(v_a_2083_, 1);
lean_dec(v_unused_2118_);
v___x_2110_ = v_a_2083_;
v_isShared_2111_ = v_isSharedCheck_2117_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_fst_2108_);
lean_dec(v_a_2083_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2117_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2115_; 
v___x_2112_ = lean_unsigned_to_nat(1u);
v___x_2113_ = lean_nat_add(v_fst_2108_, v___x_2112_);
lean_inc(v_fst_2108_);
if (v_isShared_2111_ == 0)
{
lean_ctor_set(v___x_2110_, 1, v___x_2113_);
v___x_2115_ = v___x_2110_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_fst_2108_);
lean_ctor_set(v_reuseFailAlloc_2116_, 1, v___x_2113_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
v_rangeNumArgs_2032_ = v___x_2115_;
v_lower_2033_ = v_fst_2108_;
v___y_2034_ = v___y_1958_;
v___y_2035_ = v___y_1959_;
v___y_2036_ = v___y_1960_;
v___y_2037_ = v___y_1961_;
goto v___jp_2031_;
}
}
}
}
else
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2126_; 
lean_dec(v_a_2030_);
lean_dec(v_a_2028_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v_term_x3f_1957_);
lean_dec_ref(v_e_1955_);
lean_dec(v___x_1954_);
lean_dec(v_mvarId_1953_);
v_a_2119_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v___x_2082_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2082_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2124_; 
if (v_isShared_2122_ == 0)
{
v___x_2124_ = v___x_2121_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_a_2119_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
v___jp_2031_:
{
lean_object* v___x_2038_; 
lean_inc(v_mvarId_1953_);
v___x_2038_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(v_mvarId_1953_, v_cfg_1956_, v_term_x3f_1957_, v_a_2028_, v_a_2030_, v_rangeNumArgs_2032_, v_lower_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
lean_dec_ref(v_rangeNumArgs_2032_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v_a_2039_; lean_object* v_fst_2040_; lean_object* v_snd_2041_; uint8_t v_newGoals_2042_; uint8_t v_synthAssignedInstances_2043_; uint8_t v_allowSynthFailures_2044_; lean_object* v___x_2045_; 
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
lean_inc(v_a_2039_);
lean_dec_ref_known(v___x_2038_, 1);
v_fst_2040_ = lean_ctor_get(v_a_2039_, 0);
lean_inc(v_fst_2040_);
v_snd_2041_ = lean_ctor_get(v_a_2039_, 1);
lean_inc_n(v_snd_2041_, 2);
lean_dec(v_a_2039_);
v_newGoals_2042_ = lean_ctor_get_uint8(v_cfg_1956_, 0);
v_synthAssignedInstances_2043_ = lean_ctor_get_uint8(v_cfg_1956_, 1);
v_allowSynthFailures_2044_ = lean_ctor_get_uint8(v_cfg_1956_, 2);
lean_inc(v_mvarId_1953_);
v___x_2045_ = l_Lean_Meta_synthAppInstances(v___x_1954_, v_mvarId_1953_, v_fst_2040_, v_snd_2041_, v_synthAssignedInstances_2043_, v_allowSynthFailures_2044_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v___x_2046_; lean_object* v_a_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; uint8_t v___x_2053_; 
lean_dec_ref_known(v___x_2045_, 1);
v___x_2046_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_1955_, v___y_2035_);
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc_n(v_a_2047_, 2);
lean_dec_ref(v___x_2046_);
v___x_2048_ = l_Lean_mkAppN(v_a_2047_, v_fst_2040_);
lean_inc(v_mvarId_1953_);
v___x_2049_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_1953_, v___x_2048_, v___y_2035_);
lean_dec_ref(v___x_2049_);
v___x_2050_ = lean_unsigned_to_nat(0u);
v___x_2051_ = lean_array_get_size(v_fst_2040_);
v___x_2052_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0));
v___x_2053_ = lean_nat_dec_lt(v___x_2050_, v___x_2051_);
if (v___x_2053_ == 0)
{
lean_dec(v_fst_2040_);
v___y_1990_ = v_snd_2041_;
v___y_1991_ = v_newGoals_2042_;
v___y_1992_ = v_a_2047_;
v___y_1993_ = v___y_2034_;
v___y_1994_ = v___y_2037_;
v___y_1995_ = v___y_2036_;
v___y_1996_ = v___x_2050_;
v___y_1997_ = v___y_2035_;
v_a_1998_ = v___x_2052_;
goto v___jp_1989_;
}
else
{
size_t v___x_2054_; size_t v___x_2055_; lean_object* v___x_2056_; 
v___x_2054_ = ((size_t)0ULL);
v___x_2055_ = lean_usize_of_nat(v___x_2051_);
v___x_2056_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_fst_2040_, v___x_2054_, v___x_2055_, v___x_2052_, v___y_2035_);
lean_dec(v_fst_2040_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v_a_2057_; 
v_a_2057_ = lean_ctor_get(v___x_2056_, 0);
lean_inc(v_a_2057_);
lean_dec_ref_known(v___x_2056_, 1);
v___y_1990_ = v_snd_2041_;
v___y_1991_ = v_newGoals_2042_;
v___y_1992_ = v_a_2047_;
v___y_1993_ = v___y_2034_;
v___y_1994_ = v___y_2037_;
v___y_1995_ = v___y_2036_;
v___y_1996_ = v___x_2050_;
v___y_1997_ = v___y_2035_;
v_a_1998_ = v_a_2057_;
goto v___jp_1989_;
}
else
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
lean_dec(v_a_2047_);
lean_dec(v_snd_2041_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
lean_dec(v_mvarId_1953_);
v_a_2058_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_2056_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2056_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
if (v_isShared_2061_ == 0)
{
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
}
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_dec(v_snd_2041_);
lean_dec(v_fst_2040_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
lean_dec_ref(v_e_1955_);
lean_dec(v_mvarId_1953_);
v_a_2066_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2045_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2045_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
else
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
lean_dec_ref(v_e_1955_);
lean_dec(v___x_1954_);
lean_dec(v_mvarId_1953_);
v_a_2074_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_2038_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2038_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
}
}
else
{
lean_object* v_a_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2134_; 
lean_dec(v_a_2028_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v_term_x3f_1957_);
lean_dec_ref(v_e_1955_);
lean_dec(v___x_1954_);
lean_dec(v_mvarId_1953_);
v_a_2127_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2129_ = v___x_2029_;
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_2029_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2132_; 
if (v_isShared_2130_ == 0)
{
v___x_2132_ = v___x_2129_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_a_2127_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
}
else
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2142_; 
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v_term_x3f_1957_);
lean_dec_ref(v_e_1955_);
lean_dec(v___x_1954_);
lean_dec(v_mvarId_1953_);
v_a_2135_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2137_ = v___x_2027_;
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2027_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2140_; 
if (v_isShared_2138_ == 0)
{
v___x_2140_ = v___x_2137_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_a_2135_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
else
{
lean_object* v_a_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2150_; 
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v_term_x3f_1957_);
lean_dec_ref(v_e_1955_);
lean_dec(v___x_1954_);
lean_dec(v_mvarId_1953_);
v_a_2143_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2145_ = v___x_2026_;
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_a_2143_);
lean_dec(v___x_2026_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2148_; 
if (v_isShared_2146_ == 0)
{
v___x_2148_ = v___x_2145_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_a_2143_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
v___jp_1963_:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1970_ = lean_array_to_list(v___y_1969_);
v___x_1971_ = l_List_appendTR___redArg(v___y_1965_, v___x_1970_);
lean_inc(v___x_1971_);
v___x_1972_ = l_List_forM___at___00Lean_MVarId_apply_spec__3(v___x_1971_, v___y_1964_, v___y_1968_, v___y_1967_, v___y_1966_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1967_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1964_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1979_ == 0)
{
lean_object* v_unused_1980_; 
v_unused_1980_ = lean_ctor_get(v___x_1972_, 0);
lean_dec(v_unused_1980_);
v___x_1974_ = v___x_1972_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_dec(v___x_1972_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 0, v___x_1971_);
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1971_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
else
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1988_; 
lean_dec(v___x_1971_);
v_a_1981_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1983_ = v___x_1972_;
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1972_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1986_; 
if (v_isShared_1984_ == 0)
{
v___x_1986_ = v___x_1983_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1981_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
v___jp_1989_:
{
lean_object* v___x_1999_; 
v___x_1999_ = l_Lean_Meta_appendParentTag(v_mvarId_1953_, v_a_1998_, v___y_1990_, v___y_1993_, v___y_1997_, v___y_1995_, v___y_1994_);
lean_dec_ref(v___y_1990_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v___x_2000_; 
lean_dec_ref_known(v___x_1999_, 1);
v___x_2000_ = l_Lean_Meta_getMVarsNoDelayed(v___y_1992_, v___y_1993_, v___y_1997_, v___y_1995_, v___y_1994_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2001_; lean_object* v___x_2002_; 
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
lean_inc(v_a_2001_);
lean_dec_ref_known(v___x_2000_, 1);
v___x_2002_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(v_a_1998_, v___y_1991_, v___y_1993_, v___y_1997_, v___y_1995_, v___y_1994_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; uint8_t v___x_2006_; 
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_a_2003_);
lean_dec_ref_known(v___x_2002_, 1);
v___x_2004_ = lean_array_get_size(v_a_2001_);
v___x_2005_ = lean_mk_empty_array_with_capacity(v___y_1996_);
v___x_2006_ = lean_nat_dec_lt(v___y_1996_, v___x_2004_);
if (v___x_2006_ == 0)
{
lean_dec(v_a_2001_);
v___y_1964_ = v___y_1993_;
v___y_1965_ = v_a_2003_;
v___y_1966_ = v___y_1994_;
v___y_1967_ = v___y_1995_;
v___y_1968_ = v___y_1997_;
v___y_1969_ = v___x_2005_;
goto v___jp_1963_;
}
else
{
size_t v___x_2007_; size_t v___x_2008_; lean_object* v___x_2009_; 
v___x_2007_ = ((size_t)0ULL);
v___x_2008_ = lean_usize_of_nat(v___x_2004_);
v___x_2009_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_2003_, v_a_2001_, v___x_2007_, v___x_2008_, v___x_2005_);
lean_dec(v_a_2001_);
v___y_1964_ = v___y_1993_;
v___y_1965_ = v_a_2003_;
v___y_1966_ = v___y_1994_;
v___y_1967_ = v___y_1995_;
v___y_1968_ = v___y_1997_;
v___y_1969_ = v___x_2009_;
goto v___jp_1963_;
}
}
else
{
lean_dec(v_a_2001_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
return v___x_2002_;
}
}
else
{
lean_object* v_a_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2017_; 
lean_dec_ref(v_a_1998_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
v_a_2010_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2012_ = v___x_2000_;
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_a_2010_);
lean_dec(v___x_2000_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2015_; 
if (v_isShared_2013_ == 0)
{
v___x_2015_ = v___x_2012_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_a_2010_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
}
else
{
lean_object* v_a_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2025_; 
lean_dec_ref(v_a_1998_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec_ref(v___y_1992_);
v_a_2018_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2020_ = v___x_1999_;
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_a_2018_);
lean_dec(v___x_1999_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2023_; 
if (v_isShared_2021_ == 0)
{
v___x_2023_ = v___x_2020_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_a_2018_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lam__0___boxed(lean_object* v_mvarId_2151_, lean_object* v___x_2152_, lean_object* v_e_2153_, lean_object* v_cfg_2154_, lean_object* v_term_x3f_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
lean_object* v_res_2161_; 
v_res_2161_ = l_Lean_MVarId_apply___lam__0(v_mvarId_2151_, v___x_2152_, v_e_2153_, v_cfg_2154_, v_term_x3f_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_);
lean_dec_ref(v_cfg_2154_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply(lean_object* v_mvarId_2162_, lean_object* v_e_2163_, lean_object* v_cfg_2164_, lean_object* v_term_x3f_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_){
_start:
{
lean_object* v___x_2171_; lean_object* v___f_2172_; lean_object* v___x_2173_; 
v___x_2171_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7));
lean_inc(v_mvarId_2162_);
v___f_2172_ = lean_alloc_closure((void*)(l_Lean_MVarId_apply___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2172_, 0, v_mvarId_2162_);
lean_closure_set(v___f_2172_, 1, v___x_2171_);
lean_closure_set(v___f_2172_, 2, v_e_2163_);
lean_closure_set(v___f_2172_, 3, v_cfg_2164_);
lean_closure_set(v___f_2172_, 4, v_term_x3f_2165_);
v___x_2173_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2162_, v___f_2172_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_);
return v___x_2173_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___boxed(lean_object* v_mvarId_2174_, lean_object* v_e_2175_, lean_object* v_cfg_2176_, lean_object* v_term_x3f_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_){
_start:
{
lean_object* v_res_2183_; 
v_res_2183_ = l_Lean_MVarId_apply(v_mvarId_2174_, v_e_2175_, v_cfg_2176_, v_term_x3f_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_);
lean_dec(v_a_2181_);
lean_dec_ref(v_a_2180_);
lean_dec(v_a_2179_);
lean_dec_ref(v_a_2178_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1(lean_object* v_mvarId_2184_, lean_object* v_val_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
lean_object* v___x_2191_; 
v___x_2191_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2184_, v_val_2185_, v___y_2187_);
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___boxed(lean_object* v_mvarId_2192_, lean_object* v_val_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1(v_mvarId_2192_, v_val_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5(lean_object* v_as_2200_, size_t v_i_2201_, size_t v_stop_2202_, lean_object* v_b_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_){
_start:
{
lean_object* v___x_2209_; 
v___x_2209_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_as_2200_, v_i_2201_, v_stop_2202_, v_b_2203_, v___y_2205_);
return v___x_2209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___boxed(lean_object* v_as_2210_, lean_object* v_i_2211_, lean_object* v_stop_2212_, lean_object* v_b_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
size_t v_i_boxed_2219_; size_t v_stop_boxed_2220_; lean_object* v_res_2221_; 
v_i_boxed_2219_ = lean_unbox_usize(v_i_2211_);
lean_dec(v_i_2211_);
v_stop_boxed_2220_ = lean_unbox_usize(v_stop_2212_);
lean_dec(v_stop_2212_);
v_res_2221_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5(v_as_2210_, v_i_boxed_2219_, v_stop_boxed_2220_, v_b_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
lean_dec_ref(v_as_2210_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1(lean_object* v_00_u03b2_2222_, lean_object* v_x_2223_, lean_object* v_x_2224_, lean_object* v_x_2225_){
_start:
{
lean_object* v___x_2226_; 
v___x_2226_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(v_x_2223_, v_x_2224_, v_x_2225_);
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_2227_, lean_object* v_x_2228_, size_t v_x_2229_, size_t v_x_2230_, lean_object* v_x_2231_, lean_object* v_x_2232_){
_start:
{
lean_object* v___x_2233_; 
v___x_2233_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_2228_, v_x_2229_, v_x_2230_, v_x_2231_, v_x_2232_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2234_, lean_object* v_x_2235_, lean_object* v_x_2236_, lean_object* v_x_2237_, lean_object* v_x_2238_, lean_object* v_x_2239_){
_start:
{
size_t v_x_7741__boxed_2240_; size_t v_x_7742__boxed_2241_; lean_object* v_res_2242_; 
v_x_7741__boxed_2240_ = lean_unbox_usize(v_x_2236_);
lean_dec(v_x_2236_);
v_x_7742__boxed_2241_ = lean_unbox_usize(v_x_2237_);
lean_dec(v_x_2237_);
v_res_2242_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3(v_00_u03b2_2234_, v_x_2235_, v_x_7741__boxed_2240_, v_x_7742__boxed_2241_, v_x_2238_, v_x_2239_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_2243_, lean_object* v_n_2244_, lean_object* v_k_2245_, lean_object* v_v_2246_){
_start:
{
lean_object* v___x_2247_; 
v___x_2247_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(v_n_2244_, v_k_2245_, v_v_2246_);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9(lean_object* v_00_u03b2_2248_, size_t v_depth_2249_, lean_object* v_keys_2250_, lean_object* v_vals_2251_, lean_object* v_heq_2252_, lean_object* v_i_2253_, lean_object* v_entries_2254_){
_start:
{
lean_object* v___x_2255_; 
v___x_2255_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_depth_2249_, v_keys_2250_, v_vals_2251_, v_i_2253_, v_entries_2254_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___boxed(lean_object* v_00_u03b2_2256_, lean_object* v_depth_2257_, lean_object* v_keys_2258_, lean_object* v_vals_2259_, lean_object* v_heq_2260_, lean_object* v_i_2261_, lean_object* v_entries_2262_){
_start:
{
size_t v_depth_boxed_2263_; lean_object* v_res_2264_; 
v_depth_boxed_2263_ = lean_unbox_usize(v_depth_2257_);
lean_dec(v_depth_2257_);
v_res_2264_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9(v_00_u03b2_2256_, v_depth_boxed_2263_, v_keys_2258_, v_vals_2259_, v_heq_2260_, v_i_2261_, v_entries_2262_);
lean_dec_ref(v_vals_2259_);
lean_dec_ref(v_keys_2258_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9(lean_object* v_00_u03b2_2265_, lean_object* v_x_2266_, lean_object* v_x_2267_, lean_object* v_x_2268_, lean_object* v_x_2269_){
_start:
{
lean_object* v___x_2270_; 
v___x_2270_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(v_x_2266_, v_x_2267_, v_x_2268_, v_x_2269_);
return v___x_2270_;
}
}
static lean_object* _init_l_Lean_MVarId_applyConst___closed__1(void){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2272_ = ((lean_object*)(l_Lean_MVarId_applyConst___closed__0));
v___x_2273_ = l_Lean_stringToMessageData(v___x_2272_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyConst(lean_object* v_mvar_2274_, lean_object* v_c_2275_, lean_object* v_cfg_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_){
_start:
{
lean_object* v___x_2282_; 
lean_inc(v_c_2275_);
v___x_2282_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_c_2275_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_);
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v_a_2283_; lean_object* v___x_2284_; uint8_t v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
lean_inc(v_a_2283_);
lean_dec_ref_known(v___x_2282_, 1);
v___x_2284_ = lean_obj_once(&l_Lean_MVarId_applyConst___closed__1, &l_Lean_MVarId_applyConst___closed__1_once, _init_l_Lean_MVarId_applyConst___closed__1);
v___x_2285_ = 0;
v___x_2286_ = l_Lean_MessageData_ofConstName(v_c_2275_, v___x_2285_);
v___x_2287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2284_);
lean_ctor_set(v___x_2287_, 1, v___x_2286_);
v___x_2288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2287_);
lean_ctor_set(v___x_2288_, 1, v___x_2284_);
v___x_2289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2288_);
v___x_2290_ = l_Lean_MVarId_apply(v_mvar_2274_, v_a_2283_, v_cfg_2276_, v___x_2289_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_);
return v___x_2290_;
}
else
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2298_; 
lean_dec_ref(v_cfg_2276_);
lean_dec(v_c_2275_);
lean_dec(v_mvar_2274_);
v_a_2291_ = lean_ctor_get(v___x_2282_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2293_ = v___x_2282_;
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v___x_2282_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2291_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyConst___boxed(lean_object* v_mvar_2299_, lean_object* v_c_2300_, lean_object* v_cfg_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_){
_start:
{
lean_object* v_res_2307_; 
v_res_2307_ = l_Lean_MVarId_applyConst(v_mvar_2299_, v_c_2300_, v_cfg_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_);
lean_dec(v_a_2305_);
lean_dec_ref(v_a_2304_);
lean_dec(v_a_2303_);
lean_dec_ref(v_a_2302_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(lean_object* v_msgData_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_){
_start:
{
lean_object* v___x_2314_; lean_object* v_env_2315_; uint8_t v___x_2316_; lean_object* v_env_2317_; lean_object* v___x_2318_; lean_object* v_toCold_2319_; lean_object* v_mctx_2320_; lean_object* v_lctx_2321_; lean_object* v_options_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2314_ = lean_st_ref_get(v___y_2312_);
v_env_2315_ = lean_ctor_get(v___x_2314_, 0);
lean_inc_ref(v_env_2315_);
lean_dec(v___x_2314_);
v___x_2316_ = 0;
v_env_2317_ = l_Lean_Environment_setRecordingDeps(v_env_2315_, v___x_2316_);
v___x_2318_ = lean_st_ref_get(v___y_2310_);
v_toCold_2319_ = lean_ctor_get(v___y_2311_, 0);
v_mctx_2320_ = lean_ctor_get(v___x_2318_, 0);
lean_inc_ref(v_mctx_2320_);
lean_dec(v___x_2318_);
v_lctx_2321_ = lean_ctor_get(v___y_2309_, 2);
v_options_2322_ = lean_ctor_get(v_toCold_2319_, 2);
lean_inc_ref(v_options_2322_);
lean_inc_ref(v_lctx_2321_);
v___x_2323_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2323_, 0, v_env_2317_);
lean_ctor_set(v___x_2323_, 1, v_mctx_2320_);
lean_ctor_set(v___x_2323_, 2, v_lctx_2321_);
lean_ctor_set(v___x_2323_, 3, v_options_2322_);
v___x_2324_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2324_, 0, v___x_2323_);
lean_ctor_set(v___x_2324_, 1, v_msgData_2308_);
v___x_2325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2324_);
return v___x_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1___boxed(lean_object* v_msgData_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_){
_start:
{
lean_object* v_res_2332_; 
v_res_2332_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(v_msgData_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(lean_object* v_msg_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v_ref_2339_; lean_object* v___x_2340_; lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2349_; 
v_ref_2339_ = lean_ctor_get(v___y_2336_, 2);
v___x_2340_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(v_msg_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2343_ = v___x_2340_;
v_isShared_2344_ = v_isSharedCheck_2349_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2340_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2349_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2345_; lean_object* v___x_2347_; 
lean_inc(v_ref_2339_);
v___x_2345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2345_, 0, v_ref_2339_);
lean_ctor_set(v___x_2345_, 1, v_a_2341_);
if (v_isShared_2344_ == 0)
{
lean_ctor_set_tag(v___x_2343_, 1);
lean_ctor_set(v___x_2343_, 0, v___x_2345_);
v___x_2347_ = v___x_2343_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2345_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg___boxed(lean_object* v_msg_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_){
_start:
{
lean_object* v_res_2356_; 
v_res_2356_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v_msg_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_);
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2353_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(size_t v_sz_2357_, size_t v_i_2358_, lean_object* v_bs_2359_){
_start:
{
uint8_t v___x_2360_; 
v___x_2360_ = lean_usize_dec_lt(v_i_2358_, v_sz_2357_);
if (v___x_2360_ == 0)
{
return v_bs_2359_;
}
else
{
lean_object* v_v_2361_; lean_object* v___x_2362_; lean_object* v_bs_x27_2363_; lean_object* v___x_2364_; size_t v___x_2365_; size_t v___x_2366_; lean_object* v___x_2367_; 
v_v_2361_ = lean_array_uget(v_bs_2359_, v_i_2358_);
v___x_2362_ = lean_unsigned_to_nat(0u);
v_bs_x27_2363_ = lean_array_uset(v_bs_2359_, v_i_2358_, v___x_2362_);
v___x_2364_ = l_Lean_Expr_mvarId_x21(v_v_2361_);
lean_dec(v_v_2361_);
v___x_2365_ = ((size_t)1ULL);
v___x_2366_ = lean_usize_add(v_i_2358_, v___x_2365_);
v___x_2367_ = lean_array_uset(v_bs_x27_2363_, v_i_2358_, v___x_2364_);
v_i_2358_ = v___x_2366_;
v_bs_2359_ = v___x_2367_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0___boxed(lean_object* v_sz_2369_, lean_object* v_i_2370_, lean_object* v_bs_2371_){
_start:
{
size_t v_sz_boxed_2372_; size_t v_i_boxed_2373_; lean_object* v_res_2374_; 
v_sz_boxed_2372_ = lean_unbox_usize(v_sz_2369_);
lean_dec(v_sz_2369_);
v_i_boxed_2373_ = lean_unbox_usize(v_i_2370_);
lean_dec(v_i_2370_);
v_res_2374_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(v_sz_boxed_2372_, v_i_boxed_2373_, v_bs_2371_);
return v_res_2374_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2376_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__0));
v___x_2377_ = l_Lean_stringToMessageData(v___x_2376_);
return v___x_2377_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2379_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__2));
v___x_2380_ = l_Lean_stringToMessageData(v___x_2379_);
return v___x_2380_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2382_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__4));
v___x_2383_ = l_Lean_stringToMessageData(v___x_2382_);
return v___x_2383_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2385_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__6));
v___x_2386_ = l_Lean_stringToMessageData(v___x_2385_);
return v___x_2386_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__9(void){
_start:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2388_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__8));
v___x_2389_ = l_Lean_stringToMessageData(v___x_2388_);
return v___x_2389_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__11(void){
_start:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2391_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__10));
v___x_2392_ = l_Lean_stringToMessageData(v___x_2391_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___lam__0(lean_object* v_mvarId_2393_, lean_object* v___x_2394_, lean_object* v_e_2395_, lean_object* v_n_2396_, uint8_t v_useApproxDefEq_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_){
_start:
{
lean_object* v___x_2403_; 
lean_inc(v_mvarId_2393_);
v___x_2403_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2393_, v___x_2394_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_object* v___x_2404_; 
lean_dec_ref_known(v___x_2403_, 1);
lean_inc(v_mvarId_2393_);
v___x_2404_ = l_Lean_MVarId_getType(v_mvarId_2393_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_object* v_a_2405_; lean_object* v___x_2406_; 
v_a_2405_ = lean_ctor_get(v___x_2404_, 0);
lean_inc(v_a_2405_);
lean_dec_ref_known(v___x_2404_, 1);
lean_inc(v___y_2401_);
lean_inc_ref(v___y_2400_);
lean_inc(v___y_2399_);
lean_inc_ref(v___y_2398_);
lean_inc_ref(v_e_2395_);
v___x_2406_ = lean_infer_type(v_e_2395_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v_a_2407_; uint8_t v___x_2408_; lean_object* v___x_2409_; 
v_a_2407_ = lean_ctor_get(v___x_2406_, 0);
lean_inc(v_a_2407_);
lean_dec_ref_known(v___x_2406_, 1);
v___x_2408_ = 0;
lean_inc(v_n_2396_);
v___x_2409_ = l_Lean_Meta_forallMetaBoundedTelescope(v_a_2407_, v_n_2396_, v___x_2408_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_object* v_a_2410_; lean_object* v_fst_2411_; lean_object* v_snd_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2502_; 
v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
lean_inc(v_a_2410_);
lean_dec_ref_known(v___x_2409_, 1);
v_fst_2411_ = lean_ctor_get(v_a_2410_, 0);
v_snd_2412_ = lean_ctor_get(v_a_2410_, 1);
v_isSharedCheck_2502_ = !lean_is_exclusive(v_a_2410_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2414_ = v_a_2410_;
v_isShared_2415_ = v_isSharedCheck_2502_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_snd_2412_);
lean_inc(v_fst_2411_);
lean_dec(v_a_2410_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2502_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___y_2417_; lean_object* v_snd_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2500_; 
v_snd_2432_ = lean_ctor_get(v_snd_2412_, 1);
v_isSharedCheck_2500_ = !lean_is_exclusive(v_snd_2412_);
if (v_isSharedCheck_2500_ == 0)
{
lean_object* v_unused_2501_; 
v_unused_2501_ = lean_ctor_get(v_snd_2412_, 0);
lean_dec(v_unused_2501_);
v___x_2434_ = v_snd_2412_;
v_isShared_2435_ = v_isSharedCheck_2500_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_snd_2432_);
lean_dec(v_snd_2412_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2500_;
goto v_resetjp_2433_;
}
v___jp_2416_:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2430_; 
lean_inc(v_fst_2411_);
v___x_2418_ = l_Lean_Expr_beta(v_e_2395_, v_fst_2411_);
v___x_2419_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2393_, v___x_2418_, v___y_2417_);
lean_dec(v___y_2417_);
v_isSharedCheck_2430_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2430_ == 0)
{
lean_object* v_unused_2431_; 
v_unused_2431_ = lean_ctor_get(v___x_2419_, 0);
lean_dec(v_unused_2431_);
v___x_2421_ = v___x_2419_;
v_isShared_2422_ = v_isSharedCheck_2430_;
goto v_resetjp_2420_;
}
else
{
lean_dec(v___x_2419_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2430_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
size_t v_sz_2423_; size_t v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2428_; 
v_sz_2423_ = lean_array_size(v_fst_2411_);
v___x_2424_ = ((size_t)0ULL);
v___x_2425_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(v_sz_2423_, v___x_2424_, v_fst_2411_);
v___x_2426_ = lean_array_to_list(v___x_2425_);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 0, v___x_2426_);
v___x_2428_ = v___x_2421_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v___x_2426_);
v___x_2428_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
return v___x_2428_;
}
}
}
v_resetjp_2433_:
{
lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___x_2480_; uint8_t v___x_2481_; 
v___x_2480_ = lean_array_get_size(v_fst_2411_);
v___x_2481_ = lean_nat_dec_eq(v___x_2480_, v_n_2396_);
if (v___x_2481_ == 0)
{
lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v_a_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2499_; 
lean_del_object(v___x_2434_);
lean_del_object(v___x_2414_);
lean_dec(v_fst_2411_);
lean_dec(v_a_2405_);
lean_dec_ref(v_e_2395_);
lean_dec(v_mvarId_2393_);
v___x_2482_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__9, &l_Lean_MVarId_applyN___lam__0___closed__9_once, _init_l_Lean_MVarId_applyN___lam__0___closed__9);
v___x_2483_ = l_Nat_reprFast(v_n_2396_);
v___x_2484_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2484_, 0, v___x_2483_);
v___x_2485_ = l_Lean_MessageData_ofFormat(v___x_2484_);
v___x_2486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2482_);
lean_ctor_set(v___x_2486_, 1, v___x_2485_);
v___x_2487_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__11, &l_Lean_MVarId_applyN___lam__0___closed__11_once, _init_l_Lean_MVarId_applyN___lam__0___closed__11);
v___x_2488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2486_);
lean_ctor_set(v___x_2488_, 1, v___x_2487_);
v___x_2489_ = l_Lean_indentExpr(v_snd_2432_);
v___x_2490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2490_, 0, v___x_2488_);
lean_ctor_set(v___x_2490_, 1, v___x_2489_);
v___x_2491_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_2490_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
v_a_2492_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2494_ = v___x_2491_;
v_isShared_2495_ = v_isSharedCheck_2499_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_a_2492_);
lean_dec(v___x_2491_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2499_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v___x_2497_; 
if (v_isShared_2495_ == 0)
{
v___x_2497_ = v___x_2494_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v_a_2492_);
v___x_2497_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
return v___x_2497_;
}
}
}
else
{
v___y_2437_ = v___y_2398_;
v___y_2438_ = v___y_2399_;
v___y_2439_ = v___y_2400_;
v___y_2440_ = v___y_2401_;
goto v___jp_2436_;
}
v___jp_2436_:
{
lean_object* v___x_2441_; 
lean_inc(v_a_2405_);
lean_inc(v_snd_2432_);
v___x_2441_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_useApproxDefEq_2397_, v_snd_2432_, v_a_2405_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_);
if (lean_obj_tag(v___x_2441_) == 0)
{
lean_object* v_a_2442_; uint8_t v___x_2443_; 
v_a_2442_ = lean_ctor_get(v___x_2441_, 0);
lean_inc(v_a_2442_);
lean_dec_ref_known(v___x_2441_, 1);
v___x_2443_ = lean_unbox(v_a_2442_);
lean_dec(v_a_2442_);
if (v___x_2443_ == 0)
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2447_; 
lean_dec(v_fst_2411_);
lean_dec_ref(v_e_2395_);
lean_dec(v_mvarId_2393_);
v___x_2444_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__1, &l_Lean_MVarId_applyN___lam__0___closed__1_once, _init_l_Lean_MVarId_applyN___lam__0___closed__1);
v___x_2445_ = l_Lean_indentExpr(v_a_2405_);
if (v_isShared_2435_ == 0)
{
lean_ctor_set_tag(v___x_2434_, 7);
lean_ctor_set(v___x_2434_, 1, v___x_2445_);
lean_ctor_set(v___x_2434_, 0, v___x_2444_);
v___x_2447_ = v___x_2434_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v___x_2444_);
lean_ctor_set(v_reuseFailAlloc_2471_, 1, v___x_2445_);
v___x_2447_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
lean_object* v___x_2448_; lean_object* v___x_2450_; 
v___x_2448_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__3, &l_Lean_MVarId_applyN___lam__0___closed__3_once, _init_l_Lean_MVarId_applyN___lam__0___closed__3);
if (v_isShared_2415_ == 0)
{
lean_ctor_set_tag(v___x_2414_, 7);
lean_ctor_set(v___x_2414_, 1, v___x_2448_);
lean_ctor_set(v___x_2414_, 0, v___x_2447_);
v___x_2450_ = v___x_2414_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v___x_2447_);
lean_ctor_set(v_reuseFailAlloc_2470_, 1, v___x_2448_);
v___x_2450_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
v___x_2451_ = l_Lean_indentExpr(v_snd_2432_);
v___x_2452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2450_);
lean_ctor_set(v___x_2452_, 1, v___x_2451_);
v___x_2453_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__5, &l_Lean_MVarId_applyN___lam__0___closed__5_once, _init_l_Lean_MVarId_applyN___lam__0___closed__5);
v___x_2454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2454_, 0, v___x_2452_);
lean_ctor_set(v___x_2454_, 1, v___x_2453_);
v___x_2455_ = l_Nat_reprFast(v_n_2396_);
v___x_2456_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2455_);
v___x_2457_ = l_Lean_MessageData_ofFormat(v___x_2456_);
v___x_2458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2454_);
lean_ctor_set(v___x_2458_, 1, v___x_2457_);
v___x_2459_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__7, &l_Lean_MVarId_applyN___lam__0___closed__7_once, _init_l_Lean_MVarId_applyN___lam__0___closed__7);
v___x_2460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2458_);
lean_ctor_set(v___x_2460_, 1, v___x_2459_);
v___x_2461_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_2460_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
v_a_2462_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2461_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2461_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2467_; 
if (v_isShared_2465_ == 0)
{
v___x_2467_ = v___x_2464_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2462_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
}
}
else
{
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec_ref(v___y_2437_);
lean_del_object(v___x_2434_);
lean_dec(v_snd_2432_);
lean_del_object(v___x_2414_);
lean_dec(v_a_2405_);
lean_dec(v_n_2396_);
v___y_2417_ = v___y_2438_;
goto v___jp_2416_;
}
}
else
{
lean_object* v_a_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2479_; 
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_del_object(v___x_2434_);
lean_dec(v_snd_2432_);
lean_del_object(v___x_2414_);
lean_dec(v_fst_2411_);
lean_dec(v_a_2405_);
lean_dec(v_n_2396_);
lean_dec_ref(v_e_2395_);
lean_dec(v_mvarId_2393_);
v_a_2472_ = lean_ctor_get(v___x_2441_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2441_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2474_ = v___x_2441_;
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_a_2472_);
lean_dec(v___x_2441_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2477_; 
if (v_isShared_2475_ == 0)
{
v___x_2477_ = v___x_2474_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_a_2472_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2510_; 
lean_dec(v_a_2405_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v_n_2396_);
lean_dec_ref(v_e_2395_);
lean_dec(v_mvarId_2393_);
v_a_2503_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2505_ = v___x_2409_;
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_a_2503_);
lean_dec(v___x_2409_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2508_; 
if (v_isShared_2506_ == 0)
{
v___x_2508_ = v___x_2505_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_a_2503_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
}
}
else
{
lean_object* v_a_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2518_; 
lean_dec(v_a_2405_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v_n_2396_);
lean_dec_ref(v_e_2395_);
lean_dec(v_mvarId_2393_);
v_a_2511_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2518_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2518_ == 0)
{
v___x_2513_ = v___x_2406_;
v_isShared_2514_ = v_isSharedCheck_2518_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_a_2511_);
lean_dec(v___x_2406_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2518_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v___x_2516_; 
if (v_isShared_2514_ == 0)
{
v___x_2516_ = v___x_2513_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_a_2511_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
return v___x_2516_;
}
}
}
}
else
{
lean_object* v_a_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2526_; 
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v_n_2396_);
lean_dec_ref(v_e_2395_);
lean_dec(v_mvarId_2393_);
v_a_2519_ = lean_ctor_get(v___x_2404_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2521_ = v___x_2404_;
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_a_2519_);
lean_dec(v___x_2404_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2524_; 
if (v_isShared_2522_ == 0)
{
v___x_2524_ = v___x_2521_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_a_2519_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
}
}
else
{
lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2534_; 
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v_n_2396_);
lean_dec_ref(v_e_2395_);
lean_dec(v_mvarId_2393_);
v_a_2527_ = lean_ctor_get(v___x_2403_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2529_ = v___x_2403_;
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_a_2527_);
lean_dec(v___x_2403_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2532_; 
if (v_isShared_2530_ == 0)
{
v___x_2532_ = v___x_2529_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_a_2527_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___lam__0___boxed(lean_object* v_mvarId_2535_, lean_object* v___x_2536_, lean_object* v_e_2537_, lean_object* v_n_2538_, lean_object* v_useApproxDefEq_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_){
_start:
{
uint8_t v_useApproxDefEq_boxed_2545_; lean_object* v_res_2546_; 
v_useApproxDefEq_boxed_2545_ = lean_unbox(v_useApproxDefEq_2539_);
v_res_2546_ = l_Lean_MVarId_applyN___lam__0(v_mvarId_2535_, v___x_2536_, v_e_2537_, v_n_2538_, v_useApproxDefEq_boxed_2545_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN(lean_object* v_mvarId_2547_, lean_object* v_e_2548_, lean_object* v_n_2549_, uint8_t v_useApproxDefEq_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_){
_start:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___f_2558_; lean_object* v___x_2559_; 
v___x_2556_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7));
v___x_2557_ = lean_box(v_useApproxDefEq_2550_);
lean_inc(v_mvarId_2547_);
v___f_2558_ = lean_alloc_closure((void*)(l_Lean_MVarId_applyN___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2558_, 0, v_mvarId_2547_);
lean_closure_set(v___f_2558_, 1, v___x_2556_);
lean_closure_set(v___f_2558_, 2, v_e_2548_);
lean_closure_set(v___f_2558_, 3, v_n_2549_);
lean_closure_set(v___f_2558_, 4, v___x_2557_);
v___x_2559_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2547_, v___f_2558_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_);
return v___x_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___boxed(lean_object* v_mvarId_2560_, lean_object* v_e_2561_, lean_object* v_n_2562_, lean_object* v_useApproxDefEq_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_){
_start:
{
uint8_t v_useApproxDefEq_boxed_2569_; lean_object* v_res_2570_; 
v_useApproxDefEq_boxed_2569_ = lean_unbox(v_useApproxDefEq_2563_);
v_res_2570_ = l_Lean_MVarId_applyN(v_mvarId_2560_, v_e_2561_, v_n_2562_, v_useApproxDefEq_boxed_2569_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_);
lean_dec(v_a_2567_);
lean_dec_ref(v_a_2566_);
lean_dec(v_a_2565_);
lean_dec_ref(v_a_2564_);
return v_res_2570_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1(lean_object* v_00_u03b1_2571_, lean_object* v_msg_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
lean_object* v___x_2578_; 
v___x_2578_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v_msg_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
return v___x_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___boxed(lean_object* v_00_u03b1_2579_, lean_object* v_msg_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_){
_start:
{
lean_object* v_res_2586_; 
v_res_2586_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1(v_00_u03b1_2579_, v_msg_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_);
lean_dec(v___y_2584_);
lean_dec_ref(v___y_2583_);
lean_dec(v___y_2582_);
lean_dec_ref(v___y_2581_);
return v_res_2586_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6(void){
_start:
{
lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2597_ = lean_box(0);
v___x_2598_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__5));
v___x_2599_ = l_Lean_mkConst(v___x_2598_, v___x_2597_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(lean_object* v_tag_2600_, lean_object* v_type_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_){
_start:
{
lean_object* v___x_2608_; 
lean_inc(v_a_2606_);
lean_inc_ref(v_a_2605_);
lean_inc(v_a_2604_);
lean_inc_ref(v_a_2603_);
v___x_2608_ = lean_whnf(v_type_2601_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_);
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v_a_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; uint8_t v___x_2612_; 
v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
lean_inc(v_a_2609_);
lean_dec_ref_known(v___x_2608_, 1);
v___x_2610_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1));
v___x_2611_ = lean_unsigned_to_nat(2u);
v___x_2612_ = l_Lean_Expr_isAppOfArity(v_a_2609_, v___x_2610_, v___x_2611_);
if (v___x_2612_ == 0)
{
lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2613_ = lean_st_ref_get(v_a_2602_);
v___x_2614_ = lean_array_get_size(v___x_2613_);
lean_dec(v___x_2613_);
v___x_2615_ = lean_unsigned_to_nat(1u);
v___x_2616_ = lean_nat_add(v___x_2614_, v___x_2615_);
v___x_2617_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__3));
v___x_2618_ = lean_name_append_index_after(v___x_2617_, v___x_2616_);
v___x_2619_ = l_Lean_Name_append(v_tag_2600_, v___x_2618_);
v___x_2620_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2609_, v___x_2619_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_);
if (lean_obj_tag(v___x_2620_) == 0)
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2632_; 
v_a_2621_ = lean_ctor_get(v___x_2620_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2623_ = v___x_2620_;
v_isShared_2624_ = v_isSharedCheck_2632_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2620_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2632_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2630_; 
v___x_2625_ = lean_st_ref_take(v_a_2602_);
v___x_2626_ = l_Lean_Expr_mvarId_x21(v_a_2621_);
v___x_2627_ = lean_array_push(v___x_2625_, v___x_2626_);
v___x_2628_ = lean_st_ref_put(v_a_2602_, v___x_2627_);
if (v_isShared_2624_ == 0)
{
v___x_2630_ = v___x_2623_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2621_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
else
{
return v___x_2620_;
}
}
else
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2633_ = l_Lean_Expr_appFn_x21(v_a_2609_);
v___x_2634_ = l_Lean_Expr_appArg_x21(v___x_2633_);
lean_dec_ref(v___x_2633_);
v___x_2635_ = l_Lean_Expr_appArg_x21(v_a_2609_);
lean_dec(v_a_2609_);
lean_inc_ref(v___x_2634_);
lean_inc(v_tag_2600_);
v___x_2636_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2600_, v___x_2634_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_);
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v_a_2637_; lean_object* v___x_2638_; 
v_a_2637_ = lean_ctor_get(v___x_2636_, 0);
lean_inc(v_a_2637_);
lean_dec_ref_known(v___x_2636_, 1);
lean_inc_ref(v___x_2635_);
v___x_2638_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2600_, v___x_2635_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_);
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2648_; 
v_a_2639_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2641_ = v___x_2638_;
v_isShared_2642_ = v_isSharedCheck_2648_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2638_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2648_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2646_; 
v___x_2643_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6, &l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6);
v___x_2644_ = l_Lean_mkApp4(v___x_2643_, v___x_2634_, v___x_2635_, v_a_2637_, v_a_2639_);
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 0, v___x_2644_);
v___x_2646_ = v___x_2641_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v___x_2644_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
else
{
lean_dec(v_a_2637_);
lean_dec_ref(v___x_2635_);
lean_dec_ref(v___x_2634_);
return v___x_2638_;
}
}
else
{
lean_dec_ref(v___x_2635_);
lean_dec_ref(v___x_2634_);
lean_dec(v_tag_2600_);
return v___x_2636_;
}
}
}
else
{
lean_dec(v_tag_2600_);
return v___x_2608_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___boxed(lean_object* v_tag_2649_, lean_object* v_type_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_){
_start:
{
lean_object* v_res_2657_; 
v_res_2657_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2649_, v_type_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_);
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2654_);
lean_dec(v_a_2653_);
lean_dec_ref(v_a_2652_);
lean_dec(v_a_2651_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___lam__0(lean_object* v_mvarId_2658_, lean_object* v___x_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_){
_start:
{
lean_object* v___x_2665_; 
lean_inc(v_mvarId_2658_);
v___x_2665_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2658_, v___x_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v___x_2666_; 
lean_dec_ref_known(v___x_2665_, 1);
lean_inc(v_mvarId_2658_);
v___x_2666_ = l_Lean_MVarId_getType_x27(v_mvarId_2658_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2712_; 
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2669_ = v___x_2666_;
v_isShared_2670_ = v_isSharedCheck_2712_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2666_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2712_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; uint8_t v___x_2673_; 
v___x_2671_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1));
v___x_2672_ = lean_unsigned_to_nat(2u);
v___x_2673_ = l_Lean_Expr_isAppOfArity(v_a_2667_, v___x_2671_, v___x_2672_);
if (v___x_2673_ == 0)
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2677_; 
lean_dec(v_a_2667_);
v___x_2674_ = lean_box(0);
v___x_2675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2675_, 0, v_mvarId_2658_);
lean_ctor_set(v___x_2675_, 1, v___x_2674_);
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 0, v___x_2675_);
v___x_2677_ = v___x_2669_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v___x_2675_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
else
{
lean_object* v___x_2679_; 
lean_del_object(v___x_2669_);
lean_inc(v_mvarId_2658_);
v___x_2679_ = l_Lean_MVarId_getTag(v_mvarId_2658_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v_a_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; 
v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
lean_inc(v_a_2680_);
lean_dec_ref_known(v___x_2679_, 1);
v___x_2681_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__0));
v___x_2682_ = lean_st_mk_ref(v___x_2681_);
v___x_2683_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_a_2680_, v_a_2667_, v___x_2682_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_);
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_object* v_a_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2694_; 
v_a_2684_ = lean_ctor_get(v___x_2683_, 0);
lean_inc(v_a_2684_);
lean_dec_ref_known(v___x_2683_, 1);
v___x_2685_ = lean_st_ref_get(v___x_2682_);
lean_dec(v___x_2682_);
v___x_2686_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2658_, v_a_2684_, v___y_2661_);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2694_ == 0)
{
lean_object* v_unused_2695_; 
v_unused_2695_ = lean_ctor_get(v___x_2686_, 0);
lean_dec(v_unused_2695_);
v___x_2688_ = v___x_2686_;
v_isShared_2689_ = v_isSharedCheck_2694_;
goto v_resetjp_2687_;
}
else
{
lean_dec(v___x_2686_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2694_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2690_; lean_object* v___x_2692_; 
v___x_2690_ = lean_array_to_list(v___x_2685_);
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 0, v___x_2690_);
v___x_2692_ = v___x_2688_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v___x_2690_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
}
else
{
lean_object* v_a_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2703_; 
lean_dec(v___x_2682_);
lean_dec(v_mvarId_2658_);
v_a_2696_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2698_ = v___x_2683_;
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_a_2696_);
lean_dec(v___x_2683_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2701_; 
if (v_isShared_2699_ == 0)
{
v___x_2701_ = v___x_2698_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_a_2696_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
}
else
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2711_; 
lean_dec(v_a_2667_);
lean_dec(v_mvarId_2658_);
v_a_2704_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2706_ = v___x_2679_;
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2679_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2709_; 
if (v_isShared_2707_ == 0)
{
v___x_2709_ = v___x_2706_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_a_2704_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
}
}
else
{
lean_object* v_a_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2720_; 
lean_dec(v_mvarId_2658_);
v_a_2713_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2715_ = v___x_2666_;
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_a_2713_);
lean_dec(v___x_2666_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2718_; 
if (v_isShared_2716_ == 0)
{
v___x_2718_ = v___x_2715_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_a_2713_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
}
else
{
lean_object* v_a_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2728_; 
lean_dec(v_mvarId_2658_);
v_a_2721_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2723_ = v___x_2665_;
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_a_2721_);
lean_dec(v___x_2665_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2726_; 
if (v_isShared_2724_ == 0)
{
v___x_2726_ = v___x_2723_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_a_2721_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
return v___x_2726_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___lam__0___boxed(lean_object* v_mvarId_2729_, lean_object* v___x_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l_Lean_MVarId_splitAndCore___lam__0(v_mvarId_2729_, v___x_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore(lean_object* v_mvarId_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_){
_start:
{
lean_object* v___x_2746_; lean_object* v___f_2747_; lean_object* v___x_2748_; 
v___x_2746_ = ((lean_object*)(l_Lean_MVarId_splitAndCore___closed__1));
lean_inc(v_mvarId_2740_);
v___f_2747_ = lean_alloc_closure((void*)(l_Lean_MVarId_splitAndCore___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2747_, 0, v_mvarId_2740_);
lean_closure_set(v___f_2747_, 1, v___x_2746_);
v___x_2748_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2740_, v___f_2747_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_);
return v___x_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___boxed(lean_object* v_mvarId_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l_Lean_MVarId_splitAndCore(v_mvarId_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_);
lean_dec(v_a_2753_);
lean_dec_ref(v_a_2752_);
lean_dec(v_a_2751_);
lean_dec_ref(v_a_2750_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAnd(lean_object* v_mvarId_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_){
_start:
{
lean_object* v___x_2762_; 
v___x_2762_ = l_Lean_MVarId_splitAndCore(v_mvarId_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAnd___boxed(lean_object* v_mvarId_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_){
_start:
{
lean_object* v_res_2769_; 
v_res_2769_ = l_Lean_MVarId_splitAnd(v_mvarId_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_);
lean_dec(v_a_2767_);
lean_dec_ref(v_a_2766_);
lean_dec(v_a_2765_);
lean_dec_ref(v_a_2764_);
return v_res_2769_;
}
}
static lean_object* _init_l_Lean_MVarId_exfalso___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; 
v___x_2773_ = lean_box(0);
v___x_2774_ = ((lean_object*)(l_Lean_MVarId_exfalso___lam__0___closed__1));
v___x_2775_ = l_Lean_mkConst(v___x_2774_, v___x_2773_);
return v___x_2775_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___lam__0(lean_object* v_mvarId_2780_, lean_object* v___x_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_){
_start:
{
lean_object* v___x_2787_; 
lean_inc(v_mvarId_2780_);
v___x_2787_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2780_, v___x_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_object* v___x_2788_; 
lean_dec_ref_known(v___x_2787_, 1);
lean_inc(v_mvarId_2780_);
v___x_2788_ = l_Lean_MVarId_getType(v_mvarId_2780_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; lean_object* v___x_2790_; lean_object* v_a_2791_; lean_object* v___x_2792_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
lean_inc(v_a_2789_);
lean_dec_ref_known(v___x_2788_, 1);
v___x_2790_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_a_2789_, v___y_2783_);
v_a_2791_ = lean_ctor_get(v___x_2790_, 0);
lean_inc_n(v_a_2791_, 2);
lean_dec_ref(v___x_2790_);
v___x_2792_ = l_Lean_Meta_getLevel(v_a_2791_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_);
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_object* v_a_2793_; lean_object* v___x_2794_; 
v_a_2793_ = lean_ctor_get(v___x_2792_, 0);
lean_inc(v_a_2793_);
lean_dec_ref_known(v___x_2792_, 1);
lean_inc(v_mvarId_2780_);
v___x_2794_ = l_Lean_MVarId_getTag(v_mvarId_2780_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v_a_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; 
v_a_2795_ = lean_ctor_get(v___x_2794_, 0);
lean_inc(v_a_2795_);
lean_dec_ref_known(v___x_2794_, 1);
v___x_2796_ = lean_box(0);
v___x_2797_ = lean_obj_once(&l_Lean_MVarId_exfalso___lam__0___closed__2, &l_Lean_MVarId_exfalso___lam__0___closed__2_once, _init_l_Lean_MVarId_exfalso___lam__0___closed__2);
v___x_2798_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2797_, v_a_2795_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_);
if (lean_obj_tag(v___x_2798_) == 0)
{
lean_object* v_a_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2812_; 
v_a_2799_ = lean_ctor_get(v___x_2798_, 0);
lean_inc_n(v_a_2799_, 2);
lean_dec_ref_known(v___x_2798_, 1);
v___x_2800_ = ((lean_object*)(l_Lean_MVarId_exfalso___lam__0___closed__4));
v___x_2801_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2801_, 0, v_a_2793_);
lean_ctor_set(v___x_2801_, 1, v___x_2796_);
v___x_2802_ = l_Lean_mkConst(v___x_2800_, v___x_2801_);
v___x_2803_ = l_Lean_mkAppB(v___x_2802_, v_a_2791_, v_a_2799_);
v___x_2804_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2780_, v___x_2803_, v___y_2783_);
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2812_ == 0)
{
lean_object* v_unused_2813_; 
v_unused_2813_ = lean_ctor_get(v___x_2804_, 0);
lean_dec(v_unused_2813_);
v___x_2806_ = v___x_2804_;
v_isShared_2807_ = v_isSharedCheck_2812_;
goto v_resetjp_2805_;
}
else
{
lean_dec(v___x_2804_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2812_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2808_; lean_object* v___x_2810_; 
v___x_2808_ = l_Lean_Expr_mvarId_x21(v_a_2799_);
lean_dec(v_a_2799_);
if (v_isShared_2807_ == 0)
{
lean_ctor_set(v___x_2806_, 0, v___x_2808_);
v___x_2810_ = v___x_2806_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v___x_2808_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
}
else
{
lean_object* v_a_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2821_; 
lean_dec(v_a_2793_);
lean_dec(v_a_2791_);
lean_dec(v_mvarId_2780_);
v_a_2814_ = lean_ctor_get(v___x_2798_, 0);
v_isSharedCheck_2821_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2821_ == 0)
{
v___x_2816_ = v___x_2798_;
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_a_2814_);
lean_dec(v___x_2798_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
lean_object* v___x_2819_; 
if (v_isShared_2817_ == 0)
{
v___x_2819_ = v___x_2816_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v_a_2814_);
v___x_2819_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
return v___x_2819_;
}
}
}
}
else
{
lean_object* v_a_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2829_; 
lean_dec(v_a_2793_);
lean_dec(v_a_2791_);
lean_dec(v_mvarId_2780_);
v_a_2822_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2824_ = v___x_2794_;
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_a_2822_);
lean_dec(v___x_2794_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2827_; 
if (v_isShared_2825_ == 0)
{
v___x_2827_ = v___x_2824_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_a_2822_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
}
else
{
lean_object* v_a_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2837_; 
lean_dec(v_a_2791_);
lean_dec(v_mvarId_2780_);
v_a_2830_ = lean_ctor_get(v___x_2792_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2832_ = v___x_2792_;
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_a_2830_);
lean_dec(v___x_2792_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v___x_2835_; 
if (v_isShared_2833_ == 0)
{
v___x_2835_ = v___x_2832_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_a_2830_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
}
}
}
}
else
{
lean_object* v_a_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2845_; 
lean_dec(v_mvarId_2780_);
v_a_2838_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2840_ = v___x_2788_;
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_a_2838_);
lean_dec(v___x_2788_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2843_; 
if (v_isShared_2841_ == 0)
{
v___x_2843_ = v___x_2840_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_a_2838_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
}
else
{
lean_object* v_a_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2853_; 
lean_dec(v_mvarId_2780_);
v_a_2846_ = lean_ctor_get(v___x_2787_, 0);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2848_ = v___x_2787_;
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_a_2846_);
lean_dec(v___x_2787_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2851_; 
if (v_isShared_2849_ == 0)
{
v___x_2851_ = v___x_2848_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_a_2846_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___lam__0___boxed(lean_object* v_mvarId_2854_, lean_object* v___x_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_){
_start:
{
lean_object* v_res_2861_; 
v_res_2861_ = l_Lean_MVarId_exfalso___lam__0(v_mvarId_2854_, v___x_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
lean_dec(v___y_2859_);
lean_dec_ref(v___y_2858_);
lean_dec(v___y_2857_);
lean_dec_ref(v___y_2856_);
return v_res_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso(lean_object* v_mvarId_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_){
_start:
{
lean_object* v___x_2871_; lean_object* v___f_2872_; lean_object* v___x_2873_; 
v___x_2871_ = ((lean_object*)(l_Lean_MVarId_exfalso___closed__1));
lean_inc(v_mvarId_2865_);
v___f_2872_ = lean_alloc_closure((void*)(l_Lean_MVarId_exfalso___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2872_, 0, v_mvarId_2865_);
lean_closure_set(v___f_2872_, 1, v___x_2871_);
v___x_2873_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2865_, v___f_2872_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_);
return v___x_2873_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___boxed(lean_object* v_mvarId_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_){
_start:
{
lean_object* v_res_2880_; 
v_res_2880_ = l_Lean_MVarId_exfalso(v_mvarId_2874_, v_a_2875_, v_a_2876_, v_a_2877_, v_a_2878_);
lean_dec(v_a_2878_);
lean_dec_ref(v_a_2877_);
lean_dec(v_a_2876_);
lean_dec_ref(v_a_2875_);
return v_res_2880_;
}
}
static lean_object* _init_l_Lean_MVarId_nthConstructor___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2884_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__1));
v___x_2885_ = l_Lean_MessageData_ofFormat(v___x_2884_);
return v___x_2885_;
}
}
static lean_object* _init_l_Lean_MVarId_nthConstructor___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2886_ = lean_obj_once(&l_Lean_MVarId_nthConstructor___lam__0___closed__2, &l_Lean_MVarId_nthConstructor___lam__0___closed__2_once, _init_l_Lean_MVarId_nthConstructor___lam__0___closed__2);
v___x_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2886_);
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___lam__0(lean_object* v_name_2892_, lean_object* v_goal_2893_, lean_object* v_idx_2894_, lean_object* v_expected_x3f_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_){
_start:
{
lean_object* v___x_2904_; 
lean_inc(v_name_2892_);
lean_inc(v_goal_2893_);
v___x_2904_ = l_Lean_MVarId_checkNotAssigned(v_goal_2893_, v_name_2892_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_);
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_object* v___x_2905_; 
lean_dec_ref_known(v___x_2904_, 1);
lean_inc(v_goal_2893_);
v___x_2905_ = l_Lean_MVarId_getType_x27(v_goal_2893_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v_a_2906_; lean_object* v___x_2907_; 
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
lean_inc(v_a_2906_);
lean_dec_ref_known(v___x_2905_, 1);
v___x_2907_ = l_Lean_Expr_getAppFn(v_a_2906_);
lean_dec(v_a_2906_);
if (lean_obj_tag(v___x_2907_) == 4)
{
lean_object* v_declName_2908_; lean_object* v_us_2909_; lean_object* v___x_2910_; lean_object* v_env_2911_; uint8_t v___x_2912_; lean_object* v___x_2913_; 
v_declName_2908_ = lean_ctor_get(v___x_2907_, 0);
lean_inc(v_declName_2908_);
v_us_2909_ = lean_ctor_get(v___x_2907_, 1);
lean_inc(v_us_2909_);
lean_dec_ref_known(v___x_2907_, 2);
v___x_2910_ = lean_st_ref_get(v___y_2899_);
v_env_2911_ = lean_ctor_get(v___x_2910_, 0);
lean_inc_ref(v_env_2911_);
lean_dec(v___x_2910_);
v___x_2912_ = 0;
v___x_2913_ = l_Lean_Environment_find_x3f(v_env_2911_, v_declName_2908_, v___x_2912_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_dec(v_us_2909_);
lean_dec(v_expected_x3f_2895_);
lean_dec(v_idx_2894_);
goto v___jp_2901_;
}
else
{
lean_object* v_val_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2984_; 
v_val_2914_ = lean_ctor_get(v___x_2913_, 0);
v_isSharedCheck_2984_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2916_ = v___x_2913_;
v_isShared_2917_ = v_isSharedCheck_2984_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_val_2914_);
lean_dec(v___x_2913_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2984_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
if (lean_obj_tag(v_val_2914_) == 5)
{
lean_object* v_val_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2983_; 
v_val_2918_ = lean_ctor_get(v_val_2914_, 0);
v_isSharedCheck_2983_ = !lean_is_exclusive(v_val_2914_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2920_ = v_val_2914_;
v_isShared_2921_ = v_isSharedCheck_2983_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_val_2918_);
lean_dec(v_val_2914_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2983_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; 
if (lean_obj_tag(v_expected_x3f_2895_) == 1)
{
lean_object* v_val_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2982_; 
v_val_2953_ = lean_ctor_get(v_expected_x3f_2895_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v_expected_x3f_2895_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2955_ = v_expected_x3f_2895_;
v_isShared_2956_ = v_isSharedCheck_2982_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_val_2953_);
lean_dec(v_expected_x3f_2895_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2982_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v_ctors_2957_; lean_object* v___x_2958_; uint8_t v___x_2959_; 
v_ctors_2957_ = lean_ctor_get(v_val_2918_, 4);
v___x_2958_ = l_List_lengthTR___redArg(v_ctors_2957_);
v___x_2959_ = lean_nat_dec_eq(v___x_2958_, v_val_2953_);
lean_dec(v___x_2958_);
if (v___x_2959_ == 0)
{
uint8_t v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2971_; 
v___x_2960_ = 1;
lean_inc(v_name_2892_);
v___x_2961_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2892_, v___x_2960_);
v___x_2962_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__7));
v___x_2963_ = lean_string_append(v___x_2961_, v___x_2962_);
v___x_2964_ = l_Nat_reprFast(v_val_2953_);
v___x_2965_ = lean_string_append(v___x_2963_, v___x_2964_);
lean_dec_ref(v___x_2964_);
v___x_2966_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__6));
v___x_2967_ = lean_string_append(v___x_2965_, v___x_2966_);
v___x_2968_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2967_);
v___x_2969_ = l_Lean_MessageData_ofFormat(v___x_2968_);
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 0, v___x_2969_);
v___x_2971_ = v___x_2955_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v___x_2969_);
v___x_2971_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
lean_object* v___x_2972_; 
lean_inc(v_goal_2893_);
lean_inc(v_name_2892_);
v___x_2972_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2892_, v_goal_2893_, v___x_2971_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_);
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_dec_ref_known(v___x_2972_, 1);
v___y_2923_ = v___y_2896_;
v___y_2924_ = v___y_2897_;
v___y_2925_ = v___y_2898_;
v___y_2926_ = v___y_2899_;
goto v___jp_2922_;
}
else
{
lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2980_; 
lean_del_object(v___x_2920_);
lean_dec_ref(v_val_2918_);
lean_del_object(v___x_2916_);
lean_dec(v_us_2909_);
lean_dec(v_idx_2894_);
lean_dec(v_goal_2893_);
lean_dec(v_name_2892_);
v_a_2973_ = lean_ctor_get(v___x_2972_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2975_ = v___x_2972_;
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v___x_2972_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2978_; 
if (v_isShared_2976_ == 0)
{
v___x_2978_ = v___x_2975_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_a_2973_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
}
}
else
{
lean_del_object(v___x_2955_);
lean_dec(v_val_2953_);
v___y_2923_ = v___y_2896_;
v___y_2924_ = v___y_2897_;
v___y_2925_ = v___y_2898_;
v___y_2926_ = v___y_2899_;
goto v___jp_2922_;
}
}
}
else
{
lean_dec(v_expected_x3f_2895_);
v___y_2923_ = v___y_2896_;
v___y_2924_ = v___y_2897_;
v___y_2925_ = v___y_2898_;
v___y_2926_ = v___y_2899_;
goto v___jp_2922_;
}
v___jp_2922_:
{
lean_object* v_ctors_2927_; lean_object* v___x_2928_; uint8_t v___x_2929_; 
v_ctors_2927_ = lean_ctor_get(v_val_2918_, 4);
lean_inc(v_ctors_2927_);
lean_dec_ref(v_val_2918_);
v___x_2928_ = l_List_lengthTR___redArg(v_ctors_2927_);
v___x_2929_ = lean_nat_dec_lt(v_idx_2894_, v___x_2928_);
if (v___x_2929_ == 0)
{
lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2940_; 
lean_dec(v_ctors_2927_);
lean_dec(v_us_2909_);
v___x_2930_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__4));
v___x_2931_ = l_Nat_reprFast(v_idx_2894_);
v___x_2932_ = lean_string_append(v___x_2930_, v___x_2931_);
lean_dec_ref(v___x_2931_);
v___x_2933_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__5));
v___x_2934_ = lean_string_append(v___x_2932_, v___x_2933_);
v___x_2935_ = l_Nat_reprFast(v___x_2928_);
v___x_2936_ = lean_string_append(v___x_2934_, v___x_2935_);
lean_dec_ref(v___x_2935_);
v___x_2937_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__6));
v___x_2938_ = lean_string_append(v___x_2936_, v___x_2937_);
if (v_isShared_2921_ == 0)
{
lean_ctor_set_tag(v___x_2920_, 3);
lean_ctor_set(v___x_2920_, 0, v___x_2938_);
v___x_2940_ = v___x_2920_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v___x_2938_);
v___x_2940_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
lean_object* v___x_2941_; lean_object* v___x_2943_; 
v___x_2941_ = l_Lean_MessageData_ofFormat(v___x_2940_);
if (v_isShared_2917_ == 0)
{
lean_ctor_set(v___x_2916_, 0, v___x_2941_);
v___x_2943_ = v___x_2916_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v___x_2941_);
v___x_2943_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
lean_object* v___x_2944_; 
v___x_2944_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2892_, v_goal_2893_, v___x_2943_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
return v___x_2944_;
}
}
}
else
{
lean_object* v___x_2947_; lean_object* v___x_2948_; uint8_t v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
lean_dec(v___x_2928_);
lean_del_object(v___x_2920_);
lean_del_object(v___x_2916_);
lean_dec(v_name_2892_);
v___x_2947_ = l_List_get___redArg(v_ctors_2927_, v_idx_2894_);
lean_dec(v_ctors_2927_);
v___x_2948_ = l_Lean_mkConst(v___x_2947_, v_us_2909_);
v___x_2949_ = 0;
v___x_2950_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_2950_, 0, v___x_2949_);
lean_ctor_set_uint8(v___x_2950_, 1, v___x_2929_);
lean_ctor_set_uint8(v___x_2950_, 2, v___x_2912_);
lean_ctor_set_uint8(v___x_2950_, 3, v___x_2929_);
v___x_2951_ = lean_box(0);
v___x_2952_ = l_Lean_MVarId_apply(v_goal_2893_, v___x_2948_, v___x_2950_, v___x_2951_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
return v___x_2952_;
}
}
}
}
else
{
lean_del_object(v___x_2916_);
lean_dec(v_val_2914_);
lean_dec(v_us_2909_);
lean_dec(v_expected_x3f_2895_);
lean_dec(v_idx_2894_);
goto v___jp_2901_;
}
}
}
}
else
{
lean_dec_ref(v___x_2907_);
lean_dec(v_expected_x3f_2895_);
lean_dec(v_idx_2894_);
goto v___jp_2901_;
}
}
else
{
lean_object* v_a_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_2992_; 
lean_dec(v_expected_x3f_2895_);
lean_dec(v_idx_2894_);
lean_dec(v_goal_2893_);
lean_dec(v_name_2892_);
v_a_2985_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_2992_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_2992_ == 0)
{
v___x_2987_ = v___x_2905_;
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_a_2985_);
lean_dec(v___x_2905_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v___x_2990_; 
if (v_isShared_2988_ == 0)
{
v___x_2990_ = v___x_2987_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_a_2985_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
}
}
}
}
else
{
lean_object* v_a_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3000_; 
lean_dec(v_expected_x3f_2895_);
lean_dec(v_idx_2894_);
lean_dec(v_goal_2893_);
lean_dec(v_name_2892_);
v_a_2993_ = lean_ctor_get(v___x_2904_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2995_ = v___x_2904_;
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_a_2993_);
lean_dec(v___x_2904_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2998_; 
if (v_isShared_2996_ == 0)
{
v___x_2998_ = v___x_2995_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_a_2993_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
}
v___jp_2901_:
{
lean_object* v___x_2902_; lean_object* v___x_2903_; 
v___x_2902_ = lean_obj_once(&l_Lean_MVarId_nthConstructor___lam__0___closed__3, &l_Lean_MVarId_nthConstructor___lam__0___closed__3_once, _init_l_Lean_MVarId_nthConstructor___lam__0___closed__3);
v___x_2903_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2892_, v_goal_2893_, v___x_2902_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_);
return v___x_2903_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___lam__0___boxed(lean_object* v_name_3001_, lean_object* v_goal_3002_, lean_object* v_idx_3003_, lean_object* v_expected_x3f_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_){
_start:
{
lean_object* v_res_3010_; 
v_res_3010_ = l_Lean_MVarId_nthConstructor___lam__0(v_name_3001_, v_goal_3002_, v_idx_3003_, v_expected_x3f_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec_ref(v___y_3005_);
return v_res_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor(lean_object* v_name_3011_, lean_object* v_idx_3012_, lean_object* v_expected_x3f_3013_, lean_object* v_goal_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_){
_start:
{
lean_object* v___f_3020_; lean_object* v___x_3021_; 
lean_inc(v_goal_3014_);
v___f_3020_ = lean_alloc_closure((void*)(l_Lean_MVarId_nthConstructor___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3020_, 0, v_name_3011_);
lean_closure_set(v___f_3020_, 1, v_goal_3014_);
lean_closure_set(v___f_3020_, 2, v_idx_3012_);
lean_closure_set(v___f_3020_, 3, v_expected_x3f_3013_);
v___x_3021_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_goal_3014_, v___f_3020_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
return v___x_3021_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___boxed(lean_object* v_name_3022_, lean_object* v_idx_3023_, lean_object* v_expected_x3f_3024_, lean_object* v_goal_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_){
_start:
{
lean_object* v_res_3031_; 
v_res_3031_ = l_Lean_MVarId_nthConstructor(v_name_3022_, v_idx_3023_, v_expected_x3f_3024_, v_goal_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_);
lean_dec(v_a_3029_);
lean_dec_ref(v_a_3028_);
lean_dec(v_a_3027_);
lean_dec_ref(v_a_3026_);
return v_res_3031_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(lean_object* v_x_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_){
_start:
{
lean_object* v___x_3038_; 
v___x_3038_ = l_Lean_Meta_saveState___redArg(v___y_3034_, v___y_3036_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v_a_3039_; lean_object* v___x_3040_; 
v_a_3039_ = lean_ctor_get(v___x_3038_, 0);
lean_inc(v_a_3039_);
lean_dec_ref_known(v___x_3038_, 1);
lean_inc(v___y_3036_);
lean_inc_ref(v___y_3035_);
lean_inc(v___y_3034_);
lean_inc_ref(v___y_3033_);
v___x_3040_ = lean_apply_5(v_x_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, lean_box(0));
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_object* v_a_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3049_; 
lean_dec(v_a_3039_);
v_a_3041_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3043_ = v___x_3040_;
v_isShared_3044_ = v_isSharedCheck_3049_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_a_3041_);
lean_dec(v___x_3040_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3049_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v___x_3045_; lean_object* v___x_3047_; 
v___x_3045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3045_, 0, v_a_3041_);
if (v_isShared_3044_ == 0)
{
lean_ctor_set(v___x_3043_, 0, v___x_3045_);
v___x_3047_ = v___x_3043_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v___x_3045_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
else
{
lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3080_; 
v_a_3050_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3052_ = v___x_3040_;
v_isShared_3053_ = v_isSharedCheck_3080_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v___x_3040_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3080_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
uint8_t v___x_3054_; 
v___x_3054_ = l_Lean_Exception_isInterrupt(v_a_3050_);
if (v___x_3054_ == 0)
{
uint8_t v___x_3055_; 
lean_inc(v_a_3050_);
v___x_3055_ = l_Lean_Exception_isRuntime(v_a_3050_);
if (v___x_3055_ == 0)
{
lean_object* v___x_3056_; 
lean_del_object(v___x_3052_);
lean_dec(v_a_3050_);
v___x_3056_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3039_, v___y_3034_, v___y_3036_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3064_; 
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3064_ == 0)
{
lean_object* v_unused_3065_; 
v_unused_3065_ = lean_ctor_get(v___x_3056_, 0);
lean_dec(v_unused_3065_);
v___x_3058_ = v___x_3056_;
v_isShared_3059_ = v_isSharedCheck_3064_;
goto v_resetjp_3057_;
}
else
{
lean_dec(v___x_3056_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3064_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3060_; lean_object* v___x_3062_; 
v___x_3060_ = lean_box(0);
if (v_isShared_3059_ == 0)
{
lean_ctor_set(v___x_3058_, 0, v___x_3060_);
v___x_3062_ = v___x_3058_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v___x_3060_);
v___x_3062_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
return v___x_3062_;
}
}
}
else
{
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3073_; 
v_a_3066_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3068_ = v___x_3056_;
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___x_3056_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3071_; 
if (v_isShared_3069_ == 0)
{
v___x_3071_ = v___x_3068_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_a_3066_);
v___x_3071_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
return v___x_3071_;
}
}
}
}
else
{
lean_object* v___x_3075_; 
lean_dec(v_a_3039_);
if (v_isShared_3053_ == 0)
{
v___x_3075_ = v___x_3052_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_a_3050_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
}
else
{
lean_object* v___x_3078_; 
lean_dec(v_a_3039_);
if (v_isShared_3053_ == 0)
{
v___x_3078_ = v___x_3052_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_a_3050_);
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
lean_object* v_a_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3088_; 
lean_dec_ref(v_x_3032_);
v_a_3081_ = lean_ctor_get(v___x_3038_, 0);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3083_ = v___x_3038_;
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_a_3081_);
lean_dec(v___x_3038_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3086_; 
if (v_isShared_3084_ == 0)
{
v___x_3086_ = v___x_3083_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_a_3081_);
v___x_3086_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
return v___x_3086_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg___boxed(lean_object* v_x_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v_x_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_);
lean_dec(v___y_3093_);
lean_dec_ref(v___y_3092_);
lean_dec(v___y_3091_);
lean_dec_ref(v___y_3090_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0(lean_object* v_00_u03b1_3096_, lean_object* v_x_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_){
_start:
{
lean_object* v___x_3103_; 
v___x_3103_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v_x_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_);
return v___x_3103_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___boxed(lean_object* v_00_u03b1_3104_, lean_object* v_x_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_){
_start:
{
lean_object* v_res_3111_; 
v_res_3111_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0(v_00_u03b1_3104_, v_x_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec(v___y_3107_);
lean_dec_ref(v___y_3106_);
return v_res_3111_;
}
}
static lean_object* _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3113_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___lam__0___closed__0));
v___x_3114_ = l_Lean_stringToMessageData(v___x_3113_);
return v___x_3114_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___lam__0(lean_object* v_mvarId_3115_, lean_object* v___x_3116_, lean_object* v___x_3117_, lean_object* v___x_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_){
_start:
{
lean_object* v___x_3127_; 
v___x_3127_ = l_Lean_MVarId_apply(v_mvarId_3115_, v___x_3116_, v___x_3117_, v___x_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_);
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3137_; 
v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3130_ = v___x_3127_;
v_isShared_3131_ = v_isSharedCheck_3137_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_3127_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3137_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
if (lean_obj_tag(v_a_3128_) == 1)
{
lean_object* v_tail_3132_; 
v_tail_3132_ = lean_ctor_get(v_a_3128_, 1);
if (lean_obj_tag(v_tail_3132_) == 0)
{
lean_object* v_head_3133_; lean_object* v___x_3135_; 
v_head_3133_ = lean_ctor_get(v_a_3128_, 0);
lean_inc(v_head_3133_);
lean_dec_ref_known(v_a_3128_, 2);
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 0, v_head_3133_);
v___x_3135_ = v___x_3130_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_head_3133_);
v___x_3135_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
return v___x_3135_;
}
}
else
{
lean_dec_ref_known(v_a_3128_, 2);
lean_del_object(v___x_3130_);
goto v___jp_3124_;
}
}
else
{
lean_del_object(v___x_3130_);
lean_dec(v_a_3128_);
goto v___jp_3124_;
}
}
}
else
{
lean_object* v_a_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3145_; 
v_a_3138_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3140_ = v___x_3127_;
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_a_3138_);
lean_dec(v___x_3127_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3143_; 
if (v_isShared_3141_ == 0)
{
v___x_3143_ = v___x_3140_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_a_3138_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
}
v___jp_3124_:
{
lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3125_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3126_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3125_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_);
return v___x_3126_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___lam__0___boxed(lean_object* v_mvarId_3146_, lean_object* v___x_3147_, lean_object* v___x_3148_, lean_object* v___x_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_){
_start:
{
lean_object* v_res_3155_; 
v_res_3155_ = l_Lean_MVarId_iffOfEq___lam__0(v_mvarId_3146_, v___x_3147_, v___x_3148_, v___x_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
return v_res_3155_;
}
}
static lean_object* _init_l_Lean_MVarId_iffOfEq___closed__2(void){
_start:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; 
v___x_3159_ = lean_box(0);
v___x_3160_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___closed__1));
v___x_3161_ = l_Lean_mkConst(v___x_3160_, v___x_3159_);
return v___x_3161_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq(lean_object* v_mvarId_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_){
_start:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___f_3175_; lean_object* v___x_3176_; 
v___x_3172_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___closed__2, &l_Lean_MVarId_iffOfEq___closed__2_once, _init_l_Lean_MVarId_iffOfEq___closed__2);
v___x_3173_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___closed__3));
v___x_3174_ = lean_box(0);
lean_inc(v_mvarId_3166_);
v___f_3175_ = lean_alloc_closure((void*)(l_Lean_MVarId_iffOfEq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3175_, 0, v_mvarId_3166_);
lean_closure_set(v___f_3175_, 1, v___x_3172_);
lean_closure_set(v___f_3175_, 2, v___x_3173_);
lean_closure_set(v___f_3175_, 3, v___x_3174_);
v___x_3176_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3175_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_);
if (lean_obj_tag(v___x_3176_) == 0)
{
lean_object* v_a_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3188_; 
v_a_3177_ = lean_ctor_get(v___x_3176_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_3176_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3179_ = v___x_3176_;
v_isShared_3180_ = v_isSharedCheck_3188_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_a_3177_);
lean_dec(v___x_3176_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3188_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
if (lean_obj_tag(v_a_3177_) == 0)
{
lean_object* v___x_3182_; 
if (v_isShared_3180_ == 0)
{
lean_ctor_set(v___x_3179_, 0, v_mvarId_3166_);
v___x_3182_ = v___x_3179_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_mvarId_3166_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
}
}
else
{
lean_object* v_val_3184_; lean_object* v___x_3186_; 
lean_dec(v_mvarId_3166_);
v_val_3184_ = lean_ctor_get(v_a_3177_, 0);
lean_inc(v_val_3184_);
lean_dec_ref_known(v_a_3177_, 1);
if (v_isShared_3180_ == 0)
{
lean_ctor_set(v___x_3179_, 0, v_val_3184_);
v___x_3186_ = v___x_3179_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_val_3184_);
v___x_3186_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
return v___x_3186_;
}
}
}
}
else
{
lean_object* v_a_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3196_; 
lean_dec(v_mvarId_3166_);
v_a_3189_ = lean_ctor_get(v___x_3176_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_3176_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3191_ = v___x_3176_;
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_a_3189_);
lean_dec(v___x_3176_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3194_; 
if (v_isShared_3192_ == 0)
{
v___x_3194_ = v___x_3191_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_a_3189_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___boxed(lean_object* v_mvarId_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_){
_start:
{
lean_object* v_res_3203_; 
v_res_3203_ = l_Lean_MVarId_iffOfEq(v_mvarId_3197_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_);
lean_dec(v_a_3201_);
lean_dec_ref(v_a_3200_);
lean_dec(v_a_3199_);
lean_dec_ref(v_a_3198_);
return v_res_3203_;
}
}
static lean_object* _init_l_Lean_MVarId_propext___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___x_3207_ = lean_box(0);
v___x_3208_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__1));
v___x_3209_ = l_Lean_mkConst(v___x_3208_, v___x_3207_);
return v___x_3209_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___lam__0(lean_object* v_mvarId_3213_, uint8_t v___x_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_){
_start:
{
lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; uint8_t v___y_3228_; lean_object* v___y_3254_; lean_object* v___x_3292_; uint8_t v_transparency_3293_; uint8_t v___x_3294_; 
v___x_3292_ = l_Lean_Meta_Context_config(v___y_3215_);
v_transparency_3293_ = lean_ctor_get_uint8(v___x_3292_, 9);
lean_dec_ref(v___x_3292_);
v___x_3294_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3293_, v___x_3214_);
if (v___x_3294_ == 0)
{
lean_object* v_keyedConfig_3295_; uint8_t v_trackZetaDelta_3296_; lean_object* v_zetaDeltaSet_3297_; lean_object* v_lctx_3298_; lean_object* v_localInstances_3299_; lean_object* v_defEqCtx_x3f_3300_; lean_object* v_synthPendingDepth_3301_; lean_object* v_customCanUnfoldPredicate_x3f_3302_; uint8_t v_univApprox_3303_; uint8_t v_inTypeClassResolution_3304_; uint8_t v_cacheInferType_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; 
v_keyedConfig_3295_ = lean_ctor_get(v___y_3215_, 0);
v_trackZetaDelta_3296_ = lean_ctor_get_uint8(v___y_3215_, sizeof(void*)*7);
v_zetaDeltaSet_3297_ = lean_ctor_get(v___y_3215_, 1);
v_lctx_3298_ = lean_ctor_get(v___y_3215_, 2);
v_localInstances_3299_ = lean_ctor_get(v___y_3215_, 3);
v_defEqCtx_x3f_3300_ = lean_ctor_get(v___y_3215_, 4);
v_synthPendingDepth_3301_ = lean_ctor_get(v___y_3215_, 5);
v_customCanUnfoldPredicate_x3f_3302_ = lean_ctor_get(v___y_3215_, 6);
v_univApprox_3303_ = lean_ctor_get_uint8(v___y_3215_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3304_ = lean_ctor_get_uint8(v___y_3215_, sizeof(void*)*7 + 2);
v_cacheInferType_3305_ = lean_ctor_get_uint8(v___y_3215_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3295_);
v___x_3306_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3214_, v_keyedConfig_3295_);
lean_inc(v_customCanUnfoldPredicate_x3f_3302_);
lean_inc(v_synthPendingDepth_3301_);
lean_inc(v_defEqCtx_x3f_3300_);
lean_inc_ref(v_localInstances_3299_);
lean_inc_ref(v_lctx_3298_);
lean_inc(v_zetaDeltaSet_3297_);
v___x_3307_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3307_, 0, v___x_3306_);
lean_ctor_set(v___x_3307_, 1, v_zetaDeltaSet_3297_);
lean_ctor_set(v___x_3307_, 2, v_lctx_3298_);
lean_ctor_set(v___x_3307_, 3, v_localInstances_3299_);
lean_ctor_set(v___x_3307_, 4, v_defEqCtx_x3f_3300_);
lean_ctor_set(v___x_3307_, 5, v_synthPendingDepth_3301_);
lean_ctor_set(v___x_3307_, 6, v_customCanUnfoldPredicate_x3f_3302_);
lean_ctor_set_uint8(v___x_3307_, sizeof(void*)*7, v_trackZetaDelta_3296_);
lean_ctor_set_uint8(v___x_3307_, sizeof(void*)*7 + 1, v_univApprox_3303_);
lean_ctor_set_uint8(v___x_3307_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3304_);
lean_ctor_set_uint8(v___x_3307_, sizeof(void*)*7 + 3, v_cacheInferType_3305_);
lean_inc(v_mvarId_3213_);
v___x_3308_ = l_Lean_MVarId_getType_x27(v_mvarId_3213_, v___x_3307_, v___y_3216_, v___y_3217_, v___y_3218_);
lean_dec_ref_known(v___x_3307_, 7);
v___y_3254_ = v___x_3308_;
goto v___jp_3253_;
}
else
{
lean_object* v___x_3309_; 
lean_inc(v_mvarId_3213_);
v___x_3309_ = l_Lean_MVarId_getType_x27(v_mvarId_3213_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
v___y_3254_ = v___x_3309_;
goto v___jp_3253_;
}
v___jp_3220_:
{
lean_object* v___x_3225_; lean_object* v___x_3226_; 
v___x_3225_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3226_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3225_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_);
lean_dec_ref(v___y_3221_);
return v___x_3226_;
}
v___jp_3227_:
{
lean_object* v___x_3229_; uint8_t v___x_3230_; uint8_t v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3229_ = lean_obj_once(&l_Lean_MVarId_propext___lam__0___closed__2, &l_Lean_MVarId_propext___lam__0___closed__2_once, _init_l_Lean_MVarId_propext___lam__0___closed__2);
v___x_3230_ = 0;
v___x_3231_ = 0;
v___x_3232_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3232_, 0, v___x_3230_);
lean_ctor_set_uint8(v___x_3232_, 1, v___y_3228_);
lean_ctor_set_uint8(v___x_3232_, 2, v___x_3231_);
lean_ctor_set_uint8(v___x_3232_, 3, v___y_3228_);
v___x_3233_ = lean_box(0);
v___x_3234_ = l_Lean_MVarId_apply(v_mvarId_3213_, v___x_3229_, v___x_3232_, v___x_3233_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
if (lean_obj_tag(v___x_3234_) == 0)
{
lean_object* v_a_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3244_; 
v_a_3235_ = lean_ctor_get(v___x_3234_, 0);
v_isSharedCheck_3244_ = !lean_is_exclusive(v___x_3234_);
if (v_isSharedCheck_3244_ == 0)
{
v___x_3237_ = v___x_3234_;
v_isShared_3238_ = v_isSharedCheck_3244_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_a_3235_);
lean_dec(v___x_3234_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3244_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
if (lean_obj_tag(v_a_3235_) == 1)
{
lean_object* v_tail_3239_; 
v_tail_3239_ = lean_ctor_get(v_a_3235_, 1);
if (lean_obj_tag(v_tail_3239_) == 0)
{
lean_object* v_head_3240_; lean_object* v___x_3242_; 
lean_dec_ref(v___y_3215_);
v_head_3240_ = lean_ctor_get(v_a_3235_, 0);
lean_inc(v_head_3240_);
lean_dec_ref_known(v_a_3235_, 2);
if (v_isShared_3238_ == 0)
{
lean_ctor_set(v___x_3237_, 0, v_head_3240_);
v___x_3242_ = v___x_3237_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v_head_3240_);
v___x_3242_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
return v___x_3242_;
}
}
else
{
lean_dec_ref_known(v_a_3235_, 2);
lean_del_object(v___x_3237_);
v___y_3221_ = v___y_3215_;
v___y_3222_ = v___y_3216_;
v___y_3223_ = v___y_3217_;
v___y_3224_ = v___y_3218_;
goto v___jp_3220_;
}
}
else
{
lean_del_object(v___x_3237_);
lean_dec(v_a_3235_);
v___y_3221_ = v___y_3215_;
v___y_3222_ = v___y_3216_;
v___y_3223_ = v___y_3217_;
v___y_3224_ = v___y_3218_;
goto v___jp_3220_;
}
}
}
else
{
lean_object* v_a_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3252_; 
lean_dec_ref(v___y_3215_);
v_a_3245_ = lean_ctor_get(v___x_3234_, 0);
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3234_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3247_ = v___x_3234_;
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_a_3245_);
lean_dec(v___x_3234_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v___x_3250_; 
if (v_isShared_3248_ == 0)
{
v___x_3250_ = v___x_3247_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_a_3245_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
}
v___jp_3253_:
{
if (lean_obj_tag(v___y_3254_) == 0)
{
lean_object* v_a_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; uint8_t v___x_3258_; 
v_a_3255_ = lean_ctor_get(v___y_3254_, 0);
lean_inc(v_a_3255_);
lean_dec_ref_known(v___y_3254_, 1);
v___x_3256_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__4));
v___x_3257_ = lean_unsigned_to_nat(3u);
v___x_3258_ = l_Lean_Expr_isAppOfArity(v_a_3255_, v___x_3256_, v___x_3257_);
if (v___x_3258_ == 0)
{
lean_object* v___x_3259_; lean_object* v___x_3260_; 
lean_dec(v_a_3255_);
lean_dec(v_mvarId_3213_);
v___x_3259_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3260_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3259_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
lean_dec_ref(v___y_3215_);
return v___x_3260_;
}
else
{
lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; 
v___x_3261_ = l_Lean_Expr_appFn_x21(v_a_3255_);
lean_dec(v_a_3255_);
v___x_3262_ = l_Lean_Expr_appArg_x21(v___x_3261_);
lean_dec_ref(v___x_3261_);
v___x_3263_ = l_Lean_Meta_isProp(v___x_3262_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
if (lean_obj_tag(v___x_3263_) == 0)
{
lean_object* v_a_3264_; uint8_t v___x_3265_; 
v_a_3264_ = lean_ctor_get(v___x_3263_, 0);
lean_inc(v_a_3264_);
lean_dec_ref_known(v___x_3263_, 1);
v___x_3265_ = lean_unbox(v_a_3264_);
lean_dec(v_a_3264_);
if (v___x_3265_ == 0)
{
lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v_a_3268_; lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3275_; 
lean_dec(v_mvarId_3213_);
v___x_3266_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3267_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3266_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
lean_dec_ref(v___y_3215_);
v_a_3268_ = lean_ctor_get(v___x_3267_, 0);
v_isSharedCheck_3275_ = !lean_is_exclusive(v___x_3267_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3270_ = v___x_3267_;
v_isShared_3271_ = v_isSharedCheck_3275_;
goto v_resetjp_3269_;
}
else
{
lean_inc(v_a_3268_);
lean_dec(v___x_3267_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3275_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
lean_object* v___x_3273_; 
if (v_isShared_3271_ == 0)
{
v___x_3273_ = v___x_3270_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v_a_3268_);
v___x_3273_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
return v___x_3273_;
}
}
}
else
{
v___y_3228_ = v___x_3258_;
goto v___jp_3227_;
}
}
else
{
lean_object* v_a_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3283_; 
lean_dec_ref(v___y_3215_);
lean_dec(v_mvarId_3213_);
v_a_3276_ = lean_ctor_get(v___x_3263_, 0);
v_isSharedCheck_3283_ = !lean_is_exclusive(v___x_3263_);
if (v_isSharedCheck_3283_ == 0)
{
v___x_3278_ = v___x_3263_;
v_isShared_3279_ = v_isSharedCheck_3283_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_a_3276_);
lean_dec(v___x_3263_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3283_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v___x_3281_; 
if (v_isShared_3279_ == 0)
{
v___x_3281_ = v___x_3278_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v_a_3276_);
v___x_3281_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
return v___x_3281_;
}
}
}
}
}
else
{
lean_object* v_a_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3291_; 
lean_dec_ref(v___y_3215_);
lean_dec(v_mvarId_3213_);
v_a_3284_ = lean_ctor_get(v___y_3254_, 0);
v_isSharedCheck_3291_ = !lean_is_exclusive(v___y_3254_);
if (v_isSharedCheck_3291_ == 0)
{
v___x_3286_ = v___y_3254_;
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_a_3284_);
lean_dec(v___y_3254_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v___x_3289_; 
if (v_isShared_3287_ == 0)
{
v___x_3289_ = v___x_3286_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v_a_3284_);
v___x_3289_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
return v___x_3289_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___lam__0___boxed(lean_object* v_mvarId_3310_, lean_object* v___x_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_){
_start:
{
uint8_t v___x_2525__boxed_3317_; lean_object* v_res_3318_; 
v___x_2525__boxed_3317_ = lean_unbox(v___x_3311_);
v_res_3318_ = l_Lean_MVarId_propext___lam__0(v_mvarId_3310_, v___x_2525__boxed_3317_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_);
lean_dec(v___y_3315_);
lean_dec_ref(v___y_3314_);
lean_dec(v___y_3313_);
return v_res_3318_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext(lean_object* v_mvarId_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_){
_start:
{
uint8_t v___x_3325_; lean_object* v___x_3326_; lean_object* v___f_3327_; lean_object* v___x_3328_; 
v___x_3325_ = 2;
v___x_3326_ = lean_box(v___x_3325_);
lean_inc(v_mvarId_3319_);
v___f_3327_ = lean_alloc_closure((void*)(l_Lean_MVarId_propext___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3327_, 0, v_mvarId_3319_);
lean_closure_set(v___f_3327_, 1, v___x_3326_);
v___x_3328_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3327_, v_a_3320_, v_a_3321_, v_a_3322_, v_a_3323_);
if (lean_obj_tag(v___x_3328_) == 0)
{
lean_object* v_a_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3340_; 
v_a_3329_ = lean_ctor_get(v___x_3328_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v___x_3328_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3331_ = v___x_3328_;
v_isShared_3332_ = v_isSharedCheck_3340_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_a_3329_);
lean_dec(v___x_3328_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3340_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
if (lean_obj_tag(v_a_3329_) == 0)
{
lean_object* v___x_3334_; 
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 0, v_mvarId_3319_);
v___x_3334_ = v___x_3331_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v_mvarId_3319_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
return v___x_3334_;
}
}
else
{
lean_object* v_val_3336_; lean_object* v___x_3338_; 
lean_dec(v_mvarId_3319_);
v_val_3336_ = lean_ctor_get(v_a_3329_, 0);
lean_inc(v_val_3336_);
lean_dec_ref_known(v_a_3329_, 1);
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 0, v_val_3336_);
v___x_3338_ = v___x_3331_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v_val_3336_);
v___x_3338_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
return v___x_3338_;
}
}
}
}
else
{
lean_object* v_a_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3348_; 
lean_dec(v_mvarId_3319_);
v_a_3341_ = lean_ctor_get(v___x_3328_, 0);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_3328_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3343_ = v___x_3328_;
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_a_3341_);
lean_dec(v___x_3328_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
lean_object* v___x_3346_; 
if (v_isShared_3344_ == 0)
{
v___x_3346_ = v___x_3343_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v_a_3341_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___boxed(lean_object* v_mvarId_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_){
_start:
{
lean_object* v_res_3355_; 
v_res_3355_ = l_Lean_MVarId_propext(v_mvarId_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_);
lean_dec(v_a_3353_);
lean_dec_ref(v_a_3352_);
lean_dec(v_a_3351_);
lean_dec_ref(v_a_3350_);
return v_res_3355_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0(lean_object* v_mvarId_3362_, lean_object* v___x_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_){
_start:
{
lean_object* v___y_3370_; lean_object* v___x_3414_; 
lean_inc(v_mvarId_3362_);
v___x_3414_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3362_, v___x_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_);
if (lean_obj_tag(v___x_3414_) == 0)
{
lean_object* v___x_3415_; uint8_t v_transparency_3416_; uint8_t v___x_3417_; uint8_t v___x_3418_; 
lean_dec_ref_known(v___x_3414_, 1);
v___x_3415_ = l_Lean_Meta_Context_config(v___y_3364_);
v_transparency_3416_ = lean_ctor_get_uint8(v___x_3415_, 9);
lean_dec_ref(v___x_3415_);
v___x_3417_ = 2;
v___x_3418_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3416_, v___x_3417_);
if (v___x_3418_ == 0)
{
lean_object* v_keyedConfig_3419_; uint8_t v_trackZetaDelta_3420_; lean_object* v_zetaDeltaSet_3421_; lean_object* v_lctx_3422_; lean_object* v_localInstances_3423_; lean_object* v_defEqCtx_x3f_3424_; lean_object* v_synthPendingDepth_3425_; lean_object* v_customCanUnfoldPredicate_x3f_3426_; uint8_t v_univApprox_3427_; uint8_t v_inTypeClassResolution_3428_; uint8_t v_cacheInferType_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; 
v_keyedConfig_3419_ = lean_ctor_get(v___y_3364_, 0);
v_trackZetaDelta_3420_ = lean_ctor_get_uint8(v___y_3364_, sizeof(void*)*7);
v_zetaDeltaSet_3421_ = lean_ctor_get(v___y_3364_, 1);
v_lctx_3422_ = lean_ctor_get(v___y_3364_, 2);
v_localInstances_3423_ = lean_ctor_get(v___y_3364_, 3);
v_defEqCtx_x3f_3424_ = lean_ctor_get(v___y_3364_, 4);
v_synthPendingDepth_3425_ = lean_ctor_get(v___y_3364_, 5);
v_customCanUnfoldPredicate_x3f_3426_ = lean_ctor_get(v___y_3364_, 6);
v_univApprox_3427_ = lean_ctor_get_uint8(v___y_3364_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3428_ = lean_ctor_get_uint8(v___y_3364_, sizeof(void*)*7 + 2);
v_cacheInferType_3429_ = lean_ctor_get_uint8(v___y_3364_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3419_);
v___x_3430_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3417_, v_keyedConfig_3419_);
lean_inc(v_customCanUnfoldPredicate_x3f_3426_);
lean_inc(v_synthPendingDepth_3425_);
lean_inc(v_defEqCtx_x3f_3424_);
lean_inc_ref(v_localInstances_3423_);
lean_inc_ref(v_lctx_3422_);
lean_inc(v_zetaDeltaSet_3421_);
v___x_3431_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3431_, 0, v___x_3430_);
lean_ctor_set(v___x_3431_, 1, v_zetaDeltaSet_3421_);
lean_ctor_set(v___x_3431_, 2, v_lctx_3422_);
lean_ctor_set(v___x_3431_, 3, v_localInstances_3423_);
lean_ctor_set(v___x_3431_, 4, v_defEqCtx_x3f_3424_);
lean_ctor_set(v___x_3431_, 5, v_synthPendingDepth_3425_);
lean_ctor_set(v___x_3431_, 6, v_customCanUnfoldPredicate_x3f_3426_);
lean_ctor_set_uint8(v___x_3431_, sizeof(void*)*7, v_trackZetaDelta_3420_);
lean_ctor_set_uint8(v___x_3431_, sizeof(void*)*7 + 1, v_univApprox_3427_);
lean_ctor_set_uint8(v___x_3431_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3428_);
lean_ctor_set_uint8(v___x_3431_, sizeof(void*)*7 + 3, v_cacheInferType_3429_);
lean_inc(v_mvarId_3362_);
v___x_3432_ = l_Lean_MVarId_getType_x27(v_mvarId_3362_, v___x_3431_, v___y_3365_, v___y_3366_, v___y_3367_);
lean_dec_ref_known(v___x_3431_, 7);
v___y_3370_ = v___x_3432_;
goto v___jp_3369_;
}
else
{
lean_object* v___x_3433_; 
lean_inc(v_mvarId_3362_);
v___x_3433_ = l_Lean_MVarId_getType_x27(v_mvarId_3362_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_);
v___y_3370_ = v___x_3433_;
goto v___jp_3369_;
}
}
else
{
lean_object* v_a_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3441_; 
lean_dec_ref(v___y_3364_);
lean_dec(v_mvarId_3362_);
v_a_3434_ = lean_ctor_get(v___x_3414_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v___x_3414_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3436_ = v___x_3414_;
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v___x_3414_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3439_; 
if (v_isShared_3437_ == 0)
{
v___x_3439_ = v___x_3436_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_a_3434_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
}
v___jp_3369_:
{
if (lean_obj_tag(v___y_3370_) == 0)
{
lean_object* v_a_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; uint8_t v___x_3374_; 
v_a_3371_ = lean_ctor_get(v___y_3370_, 0);
lean_inc(v_a_3371_);
lean_dec_ref_known(v___y_3370_, 1);
v___x_3372_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__1));
v___x_3373_ = lean_unsigned_to_nat(4u);
v___x_3374_ = l_Lean_Expr_isAppOfArity(v_a_3371_, v___x_3372_, v___x_3373_);
if (v___x_3374_ == 0)
{
lean_object* v___x_3375_; lean_object* v___x_3376_; 
lean_dec(v_a_3371_);
lean_dec(v_mvarId_3362_);
v___x_3375_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3376_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3375_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_);
lean_dec_ref(v___y_3364_);
return v___x_3376_;
}
else
{
lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; 
v___x_3377_ = l_Lean_Expr_appFn_x21(v_a_3371_);
v___x_3378_ = l_Lean_Expr_appFn_x21(v___x_3377_);
lean_dec_ref(v___x_3377_);
v___x_3379_ = l_Lean_Expr_appArg_x21(v___x_3378_);
lean_dec_ref(v___x_3378_);
v___x_3380_ = l_Lean_Expr_appArg_x21(v_a_3371_);
lean_dec(v_a_3371_);
v___x_3381_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__3));
v___x_3382_ = lean_unsigned_to_nat(2u);
v___x_3383_ = lean_mk_empty_array_with_capacity(v___x_3382_);
v___x_3384_ = lean_array_push(v___x_3383_, v___x_3379_);
v___x_3385_ = lean_array_push(v___x_3384_, v___x_3380_);
v___x_3386_ = l_Lean_Meta_mkAppM(v___x_3381_, v___x_3385_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_);
lean_dec_ref(v___y_3364_);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v_a_3387_; lean_object* v___x_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3396_; 
v_a_3387_ = lean_ctor_get(v___x_3386_, 0);
lean_inc(v_a_3387_);
lean_dec_ref_known(v___x_3386_, 1);
v___x_3388_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_3362_, v_a_3387_, v___y_3365_);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3396_ == 0)
{
lean_object* v_unused_3397_; 
v_unused_3397_ = lean_ctor_get(v___x_3388_, 0);
lean_dec(v_unused_3397_);
v___x_3390_ = v___x_3388_;
v_isShared_3391_ = v_isSharedCheck_3396_;
goto v_resetjp_3389_;
}
else
{
lean_dec(v___x_3388_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3396_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v___x_3392_; lean_object* v___x_3394_; 
v___x_3392_ = lean_box(v___x_3374_);
if (v_isShared_3391_ == 0)
{
lean_ctor_set(v___x_3390_, 0, v___x_3392_);
v___x_3394_ = v___x_3390_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v___x_3392_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
else
{
lean_object* v_a_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3405_; 
lean_dec(v_mvarId_3362_);
v_a_3398_ = lean_ctor_get(v___x_3386_, 0);
v_isSharedCheck_3405_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3400_ = v___x_3386_;
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_a_3398_);
lean_dec(v___x_3386_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v___x_3403_; 
if (v_isShared_3401_ == 0)
{
v___x_3403_ = v___x_3400_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_a_3398_);
v___x_3403_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
return v___x_3403_;
}
}
}
}
}
else
{
lean_object* v_a_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3413_; 
lean_dec_ref(v___y_3364_);
lean_dec(v_mvarId_3362_);
v_a_3406_ = lean_ctor_get(v___y_3370_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___y_3370_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3408_ = v___y_3370_;
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_a_3406_);
lean_dec(v___y_3370_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v___x_3411_; 
if (v_isShared_3409_ == 0)
{
v___x_3411_ = v___x_3408_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_a_3406_);
v___x_3411_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
return v___x_3411_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0___boxed(lean_object* v_mvarId_3442_, lean_object* v___x_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_){
_start:
{
lean_object* v_res_3449_; 
v_res_3449_ = l_Lean_MVarId_proofIrrelHeq___lam__0(v_mvarId_3442_, v___x_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_);
lean_dec(v___y_3447_);
lean_dec_ref(v___y_3446_);
lean_dec(v___y_3445_);
return v_res_3449_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__1(lean_object* v___f_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_){
_start:
{
lean_object* v___x_3456_; 
v___x_3456_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v_a_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3470_; 
v_a_3457_ = lean_ctor_get(v___x_3456_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3459_ = v___x_3456_;
v_isShared_3460_ = v_isSharedCheck_3470_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_a_3457_);
lean_dec(v___x_3456_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3470_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
if (lean_obj_tag(v_a_3457_) == 0)
{
uint8_t v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3464_; 
v___x_3461_ = 0;
v___x_3462_ = lean_box(v___x_3461_);
if (v_isShared_3460_ == 0)
{
lean_ctor_set(v___x_3459_, 0, v___x_3462_);
v___x_3464_ = v___x_3459_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v___x_3462_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
return v___x_3464_;
}
}
else
{
lean_object* v_val_3466_; lean_object* v___x_3468_; 
v_val_3466_ = lean_ctor_get(v_a_3457_, 0);
lean_inc(v_val_3466_);
lean_dec_ref_known(v_a_3457_, 1);
if (v_isShared_3460_ == 0)
{
lean_ctor_set(v___x_3459_, 0, v_val_3466_);
v___x_3468_ = v___x_3459_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_val_3466_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
return v___x_3468_;
}
}
}
}
else
{
lean_object* v_a_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3478_; 
v_a_3471_ = lean_ctor_get(v___x_3456_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3473_ = v___x_3456_;
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_a_3471_);
lean_dec(v___x_3456_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3476_; 
if (v_isShared_3474_ == 0)
{
v___x_3476_ = v___x_3473_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_a_3471_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
return v___x_3476_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__1___boxed(lean_object* v___f_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_){
_start:
{
lean_object* v_res_3485_; 
v_res_3485_ = l_Lean_MVarId_proofIrrelHeq___lam__1(v___f_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
return v_res_3485_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq(lean_object* v_mvarId_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_){
_start:
{
lean_object* v___x_3495_; lean_object* v___f_3496_; lean_object* v___f_3497_; lean_object* v___x_3498_; 
v___x_3495_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___closed__1));
lean_inc(v_mvarId_3489_);
v___f_3496_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3496_, 0, v_mvarId_3489_);
lean_closure_set(v___f_3496_, 1, v___x_3495_);
v___f_3497_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__1___boxed), 6, 1);
lean_closure_set(v___f_3497_, 0, v___f_3496_);
v___x_3498_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_3489_, v___f_3497_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_);
return v___x_3498_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___boxed(lean_object* v_mvarId_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_){
_start:
{
lean_object* v_res_3505_; 
v_res_3505_ = l_Lean_MVarId_proofIrrelHeq(v_mvarId_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_);
lean_dec(v_a_3503_);
lean_dec_ref(v_a_3502_);
lean_dec(v_a_3501_);
lean_dec_ref(v_a_3500_);
return v_res_3505_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___lam__0(lean_object* v_mvarId_3510_, lean_object* v___x_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_){
_start:
{
lean_object* v___y_3518_; lean_object* v___x_3561_; 
lean_inc(v_mvarId_3510_);
v___x_3561_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3510_, v___x_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_);
if (lean_obj_tag(v___x_3561_) == 0)
{
lean_object* v___x_3562_; uint8_t v_transparency_3563_; uint8_t v___x_3564_; uint8_t v___x_3565_; 
lean_dec_ref_known(v___x_3561_, 1);
v___x_3562_ = l_Lean_Meta_Context_config(v___y_3512_);
v_transparency_3563_ = lean_ctor_get_uint8(v___x_3562_, 9);
lean_dec_ref(v___x_3562_);
v___x_3564_ = 2;
v___x_3565_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3563_, v___x_3564_);
if (v___x_3565_ == 0)
{
lean_object* v_keyedConfig_3566_; uint8_t v_trackZetaDelta_3567_; lean_object* v_zetaDeltaSet_3568_; lean_object* v_lctx_3569_; lean_object* v_localInstances_3570_; lean_object* v_defEqCtx_x3f_3571_; lean_object* v_synthPendingDepth_3572_; lean_object* v_customCanUnfoldPredicate_x3f_3573_; uint8_t v_univApprox_3574_; uint8_t v_inTypeClassResolution_3575_; uint8_t v_cacheInferType_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; 
v_keyedConfig_3566_ = lean_ctor_get(v___y_3512_, 0);
v_trackZetaDelta_3567_ = lean_ctor_get_uint8(v___y_3512_, sizeof(void*)*7);
v_zetaDeltaSet_3568_ = lean_ctor_get(v___y_3512_, 1);
v_lctx_3569_ = lean_ctor_get(v___y_3512_, 2);
v_localInstances_3570_ = lean_ctor_get(v___y_3512_, 3);
v_defEqCtx_x3f_3571_ = lean_ctor_get(v___y_3512_, 4);
v_synthPendingDepth_3572_ = lean_ctor_get(v___y_3512_, 5);
v_customCanUnfoldPredicate_x3f_3573_ = lean_ctor_get(v___y_3512_, 6);
v_univApprox_3574_ = lean_ctor_get_uint8(v___y_3512_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3575_ = lean_ctor_get_uint8(v___y_3512_, sizeof(void*)*7 + 2);
v_cacheInferType_3576_ = lean_ctor_get_uint8(v___y_3512_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3566_);
v___x_3577_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3564_, v_keyedConfig_3566_);
lean_inc(v_customCanUnfoldPredicate_x3f_3573_);
lean_inc(v_synthPendingDepth_3572_);
lean_inc(v_defEqCtx_x3f_3571_);
lean_inc_ref(v_localInstances_3570_);
lean_inc_ref(v_lctx_3569_);
lean_inc(v_zetaDeltaSet_3568_);
v___x_3578_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3578_, 0, v___x_3577_);
lean_ctor_set(v___x_3578_, 1, v_zetaDeltaSet_3568_);
lean_ctor_set(v___x_3578_, 2, v_lctx_3569_);
lean_ctor_set(v___x_3578_, 3, v_localInstances_3570_);
lean_ctor_set(v___x_3578_, 4, v_defEqCtx_x3f_3571_);
lean_ctor_set(v___x_3578_, 5, v_synthPendingDepth_3572_);
lean_ctor_set(v___x_3578_, 6, v_customCanUnfoldPredicate_x3f_3573_);
lean_ctor_set_uint8(v___x_3578_, sizeof(void*)*7, v_trackZetaDelta_3567_);
lean_ctor_set_uint8(v___x_3578_, sizeof(void*)*7 + 1, v_univApprox_3574_);
lean_ctor_set_uint8(v___x_3578_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3575_);
lean_ctor_set_uint8(v___x_3578_, sizeof(void*)*7 + 3, v_cacheInferType_3576_);
lean_inc(v_mvarId_3510_);
v___x_3579_ = l_Lean_MVarId_getType_x27(v_mvarId_3510_, v___x_3578_, v___y_3513_, v___y_3514_, v___y_3515_);
lean_dec_ref_known(v___x_3578_, 7);
v___y_3518_ = v___x_3579_;
goto v___jp_3517_;
}
else
{
lean_object* v___x_3580_; 
lean_inc(v_mvarId_3510_);
v___x_3580_ = l_Lean_MVarId_getType_x27(v_mvarId_3510_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_);
v___y_3518_ = v___x_3580_;
goto v___jp_3517_;
}
}
else
{
lean_object* v_a_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3588_; 
lean_dec_ref(v___y_3512_);
lean_dec(v_mvarId_3510_);
v_a_3581_ = lean_ctor_get(v___x_3561_, 0);
v_isSharedCheck_3588_ = !lean_is_exclusive(v___x_3561_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3583_ = v___x_3561_;
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_a_3581_);
lean_dec(v___x_3561_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v___x_3586_; 
if (v_isShared_3584_ == 0)
{
v___x_3586_ = v___x_3583_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v_a_3581_);
v___x_3586_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
return v___x_3586_;
}
}
}
v___jp_3517_:
{
if (lean_obj_tag(v___y_3518_) == 0)
{
lean_object* v_a_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; uint8_t v___x_3522_; 
v_a_3519_ = lean_ctor_get(v___y_3518_, 0);
lean_inc(v_a_3519_);
lean_dec_ref_known(v___y_3518_, 1);
v___x_3520_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__4));
v___x_3521_ = lean_unsigned_to_nat(3u);
v___x_3522_ = l_Lean_Expr_isAppOfArity(v_a_3519_, v___x_3520_, v___x_3521_);
if (v___x_3522_ == 0)
{
lean_object* v___x_3523_; lean_object* v___x_3524_; 
lean_dec(v_a_3519_);
lean_dec(v_mvarId_3510_);
v___x_3523_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3524_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3523_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_);
lean_dec_ref(v___y_3512_);
return v___x_3524_;
}
else
{
lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; 
v___x_3525_ = l_Lean_Expr_appFn_x21(v_a_3519_);
v___x_3526_ = l_Lean_Expr_appArg_x21(v___x_3525_);
lean_dec_ref(v___x_3525_);
v___x_3527_ = l_Lean_Expr_appArg_x21(v_a_3519_);
lean_dec(v_a_3519_);
v___x_3528_ = ((lean_object*)(l_Lean_MVarId_subsingletonElim___lam__0___closed__1));
v___x_3529_ = lean_unsigned_to_nat(2u);
v___x_3530_ = lean_mk_empty_array_with_capacity(v___x_3529_);
v___x_3531_ = lean_array_push(v___x_3530_, v___x_3526_);
v___x_3532_ = lean_array_push(v___x_3531_, v___x_3527_);
v___x_3533_ = l_Lean_Meta_mkAppM(v___x_3528_, v___x_3532_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_);
lean_dec_ref(v___y_3512_);
if (lean_obj_tag(v___x_3533_) == 0)
{
lean_object* v_a_3534_; lean_object* v___x_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3543_; 
v_a_3534_ = lean_ctor_get(v___x_3533_, 0);
lean_inc(v_a_3534_);
lean_dec_ref_known(v___x_3533_, 1);
v___x_3535_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_3510_, v_a_3534_, v___y_3513_);
v_isSharedCheck_3543_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3543_ == 0)
{
lean_object* v_unused_3544_; 
v_unused_3544_ = lean_ctor_get(v___x_3535_, 0);
lean_dec(v_unused_3544_);
v___x_3537_ = v___x_3535_;
v_isShared_3538_ = v_isSharedCheck_3543_;
goto v_resetjp_3536_;
}
else
{
lean_dec(v___x_3535_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3543_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3539_; lean_object* v___x_3541_; 
v___x_3539_ = lean_box(v___x_3522_);
if (v_isShared_3538_ == 0)
{
lean_ctor_set(v___x_3537_, 0, v___x_3539_);
v___x_3541_ = v___x_3537_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v___x_3539_);
v___x_3541_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
return v___x_3541_;
}
}
}
else
{
lean_object* v_a_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3552_; 
lean_dec(v_mvarId_3510_);
v_a_3545_ = lean_ctor_get(v___x_3533_, 0);
v_isSharedCheck_3552_ = !lean_is_exclusive(v___x_3533_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3547_ = v___x_3533_;
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_a_3545_);
lean_dec(v___x_3533_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3550_; 
if (v_isShared_3548_ == 0)
{
v___x_3550_ = v___x_3547_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_a_3545_);
v___x_3550_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
return v___x_3550_;
}
}
}
}
}
else
{
lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3560_; 
lean_dec_ref(v___y_3512_);
lean_dec(v_mvarId_3510_);
v_a_3553_ = lean_ctor_get(v___y_3518_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___y_3518_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3555_ = v___y_3518_;
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_dec(v___y_3518_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3558_; 
if (v_isShared_3556_ == 0)
{
v___x_3558_ = v___x_3555_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_a_3553_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___lam__0___boxed(lean_object* v_mvarId_3589_, lean_object* v___x_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_){
_start:
{
lean_object* v_res_3596_; 
v_res_3596_ = l_Lean_MVarId_subsingletonElim___lam__0(v_mvarId_3589_, v___x_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_);
lean_dec(v___y_3594_);
lean_dec_ref(v___y_3593_);
lean_dec(v___y_3592_);
return v_res_3596_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim(lean_object* v_mvarId_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_){
_start:
{
lean_object* v___x_3606_; lean_object* v___f_3607_; lean_object* v___f_3608_; lean_object* v___x_3609_; 
v___x_3606_ = ((lean_object*)(l_Lean_MVarId_subsingletonElim___closed__1));
lean_inc(v_mvarId_3600_);
v___f_3607_ = lean_alloc_closure((void*)(l_Lean_MVarId_subsingletonElim___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3607_, 0, v_mvarId_3600_);
lean_closure_set(v___f_3607_, 1, v___x_3606_);
v___f_3608_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__1___boxed), 6, 1);
lean_closure_set(v___f_3608_, 0, v___f_3607_);
v___x_3609_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_3600_, v___f_3608_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_);
return v___x_3609_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___boxed(lean_object* v_mvarId_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_){
_start:
{
lean_object* v_res_3616_; 
v_res_3616_ = l_Lean_MVarId_subsingletonElim(v_mvarId_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_);
lean_dec(v_a_3614_);
lean_dec_ref(v_a_3613_);
lean_dec(v_a_3612_);
lean_dec_ref(v_a_3611_);
return v_res_3616_;
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
