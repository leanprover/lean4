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
lean_ctor_set(v___x_239_, 0, v___y_242_);
v___x_246_ = v___x_239_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___y_242_);
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
lean_ctor_set(v___x_254_, 1, v___y_243_);
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
v___y_242_ = v___x_267_;
v___y_243_ = v_a_262_;
v___y_244_ = v___x_268_;
goto v___jp_241_;
}
else
{
lean_object* v_val_269_; 
v_val_269_ = lean_ctor_get(v_term_x3f_207_, 0);
lean_inc(v_val_269_);
lean_dec_ref_known(v_term_x3f_207_, 1);
v___y_242_ = v___x_267_;
v___y_243_ = v_a_262_;
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
lean_object* v___x_374_; uint8_t v_constApprox_375_; uint8_t v_isDefEqStuckEx_376_; uint8_t v_unificationHints_377_; uint8_t v_proofIrrelevance_378_; uint8_t v_assignSyntheticOpaque_379_; uint8_t v_offsetCnstrs_380_; uint8_t v_transparency_381_; uint8_t v_etaStruct_382_; uint8_t v_univApprox_383_; uint8_t v_iota_384_; uint8_t v_beta_385_; uint8_t v_proj_386_; uint8_t v_zeta_387_; uint8_t v_zetaDelta_388_; uint8_t v_zetaUnused_389_; uint8_t v_zetaHave_390_; uint8_t v_canUnfoldPredicateConfig_391_; uint8_t v_stringLitToCtor_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_413_; 
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
v_stringLitToCtor_392_ = lean_ctor_get_uint8(v___x_374_, 20);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_413_ == 0)
{
v___x_394_ = v___x_374_;
v_isShared_395_ = v_isSharedCheck_413_;
goto v_resetjp_393_;
}
else
{
lean_dec(v___x_374_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_413_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 0, 21);
lean_ctor_set_uint8(v_reuseFailAlloc_412_, 3, v_constApprox_375_);
lean_ctor_set_uint8(v_reuseFailAlloc_412_, 4, v_isDefEqStuckEx_376_);
lean_ctor_set_uint8(v_reuseFailAlloc_412_, 5, v_unificationHints_377_);
lean_ctor_set_uint8(v_reuseFailAlloc_412_, 6, v_proofIrrelevance_378_);
lean_ctor_set_uint8(v_reuseFailAlloc_412_, 7, v_assignSyntheticOpaque_379_);
lean_ctor_set_uint8(v_reuseFailAlloc_412_, 8, v_offsetCnstrs_380_);
lean_ctor_set_uint8(v_reuseFailAlloc_412_, 9, v_transparency_381_);
lean_ctor_set_uint8(v_reuseFailAlloc_412_, 10, v_etaStruct_382_);
lean_ctor_set_uint8(v_reuseFailAlloc_412_, 11, v_univApprox_383_);
lean_ctor_set_uint8(v_reuseFailAlloc_412_, 12, v_iota_384_);
lean_ctor_set_uint8(v_reuseFailAlloc_412_, 13, v_beta_385_);
lean_ctor_set_uint8(v_reuseFailAlloc_412_, 14, v_proj_386_);
lean_ctor_set_uint8(v_reuseFailAlloc_412_, 15, v_zeta_387_);
lean_ctor_set_uint8(v_reuseFailAlloc_412_, 16, v_zetaDelta_388_);
lean_ctor_set_uint8(v_reuseFailAlloc_412_, 17, v_zetaUnused_389_);
lean_ctor_set_uint8(v_reuseFailAlloc_412_, 18, v_zetaHave_390_);
lean_ctor_set_uint8(v_reuseFailAlloc_412_, 19, v_canUnfoldPredicateConfig_391_);
lean_ctor_set_uint8(v_reuseFailAlloc_412_, 20, v_stringLitToCtor_392_);
v___x_397_ = v_reuseFailAlloc_412_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
uint8_t v_trackZetaDelta_398_; lean_object* v_zetaDeltaSet_399_; lean_object* v_lctx_400_; lean_object* v_localInstances_401_; lean_object* v_defEqCtx_x3f_402_; lean_object* v_synthPendingDepth_403_; lean_object* v_customCanUnfoldPredicate_x3f_404_; uint8_t v_univApprox_405_; uint8_t v_inTypeClassResolution_406_; uint8_t v_cacheInferType_407_; uint64_t v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
lean_ctor_set_uint8(v___x_397_, 0, v_approx_314_);
lean_ctor_set_uint8(v___x_397_, 1, v_approx_314_);
lean_ctor_set_uint8(v___x_397_, 2, v_approx_314_);
v_trackZetaDelta_398_ = lean_ctor_get_uint8(v_a_315_, sizeof(void*)*7);
v_zetaDeltaSet_399_ = lean_ctor_get(v_a_315_, 1);
v_lctx_400_ = lean_ctor_get(v_a_315_, 2);
v_localInstances_401_ = lean_ctor_get(v_a_315_, 3);
v_defEqCtx_x3f_402_ = lean_ctor_get(v_a_315_, 4);
v_synthPendingDepth_403_ = lean_ctor_get(v_a_315_, 5);
v_customCanUnfoldPredicate_x3f_404_ = lean_ctor_get(v_a_315_, 6);
v_univApprox_405_ = lean_ctor_get_uint8(v_a_315_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_406_ = lean_ctor_get_uint8(v_a_315_, sizeof(void*)*7 + 2);
v_cacheInferType_407_ = lean_ctor_get_uint8(v_a_315_, sizeof(void*)*7 + 3);
v___x_408_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_397_);
v___x_409_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_409_, 0, v___x_397_);
lean_ctor_set_uint64(v___x_409_, sizeof(void*)*1, v___x_408_);
lean_inc(v_customCanUnfoldPredicate_x3f_404_);
lean_inc(v_synthPendingDepth_403_);
lean_inc(v_defEqCtx_x3f_402_);
lean_inc_ref(v_localInstances_401_);
lean_inc_ref(v_lctx_400_);
lean_inc(v_zetaDeltaSet_399_);
v___x_410_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_410_, 0, v___x_409_);
lean_ctor_set(v___x_410_, 1, v_zetaDeltaSet_399_);
lean_ctor_set(v___x_410_, 2, v_lctx_400_);
lean_ctor_set(v___x_410_, 3, v_localInstances_401_);
lean_ctor_set(v___x_410_, 4, v_defEqCtx_x3f_402_);
lean_ctor_set(v___x_410_, 5, v_synthPendingDepth_403_);
lean_ctor_set(v___x_410_, 6, v_customCanUnfoldPredicate_x3f_404_);
lean_ctor_set_uint8(v___x_410_, sizeof(void*)*7, v_trackZetaDelta_398_);
lean_ctor_set_uint8(v___x_410_, sizeof(void*)*7 + 1, v_univApprox_405_);
lean_ctor_set_uint8(v___x_410_, sizeof(void*)*7 + 2, v_inTypeClassResolution_406_);
lean_ctor_set_uint8(v___x_410_, sizeof(void*)*7 + 3, v_cacheInferType_407_);
v___x_411_ = l_Lean_Meta_Context_config(v___x_410_);
lean_dec_ref_known(v___x_410_, 7);
v_config_366_ = v___x_411_;
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
lean_closure_set(v___f_329_, 0, v___y_322_);
lean_closure_set(v___f_329_, 1, v___y_321_);
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
lean_inc(v___y_324_);
v___x_336_ = l_Lean_Meta_throwTacticEx___redArg(v___y_324_, v_mvarId_309_, v___x_335_, v___y_323_, v___y_326_, v___y_327_, v___y_325_);
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
v___y_321_ = v___y_360_;
v___y_322_ = v___y_358_;
v___y_323_ = v___y_354_;
v___y_324_ = v___y_359_;
v___y_325_ = v___y_355_;
v___y_326_ = v___y_356_;
v___y_327_ = v___y_357_;
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
v___y_338_ = v___y_360_;
v___y_339_ = v___y_358_;
v___y_340_ = v___y_354_;
v___y_341_ = v___x_362_;
v___y_342_ = v___y_359_;
v___y_343_ = v___y_355_;
v___y_344_ = v___y_356_;
v___y_345_ = v___y_357_;
v___y_346_ = v___x_363_;
goto v___jp_337_;
}
else
{
lean_object* v_val_364_; 
v_val_364_ = lean_ctor_get(v_term_x3f_313_, 0);
lean_inc(v_val_364_);
v___y_338_ = v___y_360_;
v___y_339_ = v___y_358_;
v___y_340_ = v___y_354_;
v___y_341_ = v___x_362_;
v___y_342_ = v___y_359_;
v___y_343_ = v___y_355_;
v___y_344_ = v___y_356_;
v___y_345_ = v___y_357_;
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
v___y_354_ = v___y_367_;
v___y_355_ = v___y_370_;
v___y_356_ = v___y_368_;
v___y_357_ = v___y_369_;
v___y_358_ = v_config_366_;
v___y_359_ = v___x_371_;
v___y_360_ = v_eType_310_;
goto v___jp_353_;
}
else
{
lean_object* v_val_372_; 
v_val_372_ = lean_ctor_get(v_conclusionType_x3f_311_, 0);
lean_inc(v_val_372_);
v___y_354_ = v___y_367_;
v___y_355_ = v___y_370_;
v___y_356_ = v___y_368_;
v___y_357_ = v___y_369_;
v___y_358_ = v_config_366_;
v___y_359_ = v___x_371_;
v___y_360_ = v_val_372_;
goto v___jp_353_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___boxed(lean_object* v_mvarId_414_, lean_object* v_eType_415_, lean_object* v_conclusionType_x3f_416_, lean_object* v_targetType_417_, lean_object* v_term_x3f_418_, lean_object* v_approx_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
uint8_t v_approx_boxed_425_; lean_object* v_res_426_; 
v_approx_boxed_425_ = lean_unbox(v_approx_419_);
v_res_426_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_414_, v_eType_415_, v_conclusionType_x3f_416_, v_targetType_417_, v_term_x3f_418_, v_approx_boxed_425_, v_a_420_, v_a_421_, v_a_422_, v_a_423_);
lean_dec(v_a_423_);
lean_dec_ref(v_a_422_);
lean_dec(v_a_421_);
lean_dec_ref(v_a_420_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError(lean_object* v_00_u03b1_427_, lean_object* v_mvarId_428_, lean_object* v_eType_429_, lean_object* v_conclusionType_x3f_430_, lean_object* v_targetType_431_, lean_object* v_term_x3f_432_, uint8_t v_approx_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_428_, v_eType_429_, v_conclusionType_x3f_430_, v_targetType_431_, v_term_x3f_432_, v_approx_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___boxed(lean_object* v_00_u03b1_440_, lean_object* v_mvarId_441_, lean_object* v_eType_442_, lean_object* v_conclusionType_x3f_443_, lean_object* v_targetType_444_, lean_object* v_term_x3f_445_, lean_object* v_approx_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_){
_start:
{
uint8_t v_approx_boxed_452_; lean_object* v_res_453_; 
v_approx_boxed_452_ = lean_unbox(v_approx_446_);
v_res_453_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError(v_00_u03b1_440_, v_mvarId_441_, v_eType_442_, v_conclusionType_x3f_443_, v_targetType_444_, v_term_x3f_445_, v_approx_boxed_452_, v_a_447_, v_a_448_, v_a_449_, v_a_450_);
lean_dec(v_a_450_);
lean_dec_ref(v_a_449_);
lean_dec(v_a_448_);
lean_dec_ref(v_a_447_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(lean_object* v_a_454_, lean_object* v_snd_455_, lean_object* v_fst_456_, lean_object* v_____r_457_, uint8_t v_progressAfterEx_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_464_, 0, v_a_454_);
v___x_465_ = lean_box(v_progressAfterEx_458_);
v___x_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
lean_ctor_set(v___x_466_, 1, v_snd_455_);
v___x_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_467_, 0, v_fst_456_);
lean_ctor_set(v___x_467_, 1, v___x_466_);
v___x_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_464_);
lean_ctor_set(v___x_468_, 1, v___x_467_);
v___x_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0___boxed(lean_object* v_a_470_, lean_object* v_snd_471_, lean_object* v_fst_472_, lean_object* v_____r_473_, lean_object* v_progressAfterEx_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
uint8_t v_progressAfterEx_boxed_480_; lean_object* v_res_481_; 
v_progressAfterEx_boxed_480_ = lean_unbox(v_progressAfterEx_474_);
v_res_481_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(v_a_470_, v_snd_471_, v_fst_472_, v_____r_473_, v_progressAfterEx_boxed_480_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
return v_res_481_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__1));
v___x_486_ = l_Lean_MessageData_ofFormat(v___x_485_);
return v___x_486_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2);
v___x_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0(uint8_t v_allowSynthFailures_489_, lean_object* v_tacticName_490_, lean_object* v_mvarId_491_, lean_object* v_as_492_, size_t v_sz_493_, size_t v_i_494_, lean_object* v_b_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
lean_object* v_a_502_; lean_object* v_fst_507_; lean_object* v_fst_508_; lean_object* v_snd_509_; uint8_t v___x_512_; 
v___x_512_ = lean_usize_dec_lt(v_i_494_, v_sz_493_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; 
lean_dec(v_mvarId_491_);
lean_dec(v_tacticName_490_);
v___x_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_513_, 0, v_b_495_);
return v___x_513_;
}
else
{
lean_object* v_snd_514_; lean_object* v_fst_515_; lean_object* v_fst_516_; lean_object* v_snd_517_; lean_object* v_a_518_; lean_object* v_a_520_; lean_object* v___y_528_; lean_object* v___x_589_; 
v_snd_514_ = lean_ctor_get(v_b_495_, 1);
lean_inc(v_snd_514_);
v_fst_515_ = lean_ctor_get(v_b_495_, 0);
lean_inc(v_fst_515_);
lean_dec_ref(v_b_495_);
v_fst_516_ = lean_ctor_get(v_snd_514_, 0);
lean_inc(v_fst_516_);
v_snd_517_ = lean_ctor_get(v_snd_514_, 1);
lean_inc(v_snd_517_);
lean_dec(v_snd_514_);
v_a_518_ = lean_array_uget_borrowed(v_as_492_, v_i_494_);
lean_inc(v___y_499_);
lean_inc_ref(v___y_498_);
lean_inc(v___y_497_);
lean_inc_ref(v___y_496_);
lean_inc(v_a_518_);
v___x_589_ = lean_infer_type(v_a_518_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v_a_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v_a_590_ = lean_ctor_get(v___x_589_, 0);
lean_inc(v_a_590_);
lean_dec_ref_known(v___x_589_, 1);
v___x_591_ = lean_box(0);
v___x_592_ = l_Lean_Meta_synthInstance(v_a_590_, v___x_591_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; lean_object* v___x_594_; lean_object* v___x_595_; uint8_t v___x_596_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_a_593_);
lean_dec_ref_known(v___x_592_, 1);
v___x_594_ = lean_array_get_size(v_snd_517_);
v___x_595_ = lean_unsigned_to_nat(0u);
v___x_596_ = lean_nat_dec_eq(v___x_594_, v___x_595_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = lean_box(0);
lean_inc(v_snd_517_);
v___x_598_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(v_a_593_, v_snd_517_, v_fst_515_, v___x_597_, v___x_512_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
v___y_528_ = v___x_598_;
goto v___jp_527_;
}
else
{
lean_object* v___x_599_; uint8_t v___x_600_; lean_object* v___x_601_; 
v___x_599_ = lean_box(0);
v___x_600_ = lean_unbox(v_fst_516_);
lean_inc(v_snd_517_);
v___x_601_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(v_a_593_, v_snd_517_, v_fst_515_, v___x_599_, v___x_600_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
v___y_528_ = v___x_601_;
goto v___jp_527_;
}
}
else
{
lean_object* v_a_602_; 
lean_dec(v_fst_515_);
v_a_602_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_a_602_);
lean_dec_ref_known(v___x_592_, 1);
v_a_520_ = v_a_602_;
goto v___jp_519_;
}
}
else
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
lean_dec(v_snd_517_);
lean_dec(v_fst_516_);
lean_dec(v_fst_515_);
lean_dec(v_mvarId_491_);
lean_dec(v_tacticName_490_);
v_a_603_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v___x_589_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_589_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_603_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
v___jp_519_:
{
uint8_t v___x_521_; 
v___x_521_ = l_Lean_Exception_isInterrupt(v_a_520_);
if (v___x_521_ == 0)
{
uint8_t v___x_522_; 
lean_inc_ref(v_a_520_);
v___x_522_ = l_Lean_Exception_isRuntime(v_a_520_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_523_, 0, v_a_520_);
lean_inc(v_a_518_);
v___x_524_ = lean_array_push(v_snd_517_, v_a_518_);
v_fst_507_ = v___x_523_;
v_fst_508_ = v_fst_516_;
v_snd_509_ = v___x_524_;
goto v___jp_506_;
}
else
{
lean_object* v___x_525_; 
lean_dec(v_snd_517_);
lean_dec(v_fst_516_);
lean_dec(v_mvarId_491_);
lean_dec(v_tacticName_490_);
v___x_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_525_, 0, v_a_520_);
return v___x_525_;
}
}
else
{
lean_object* v___x_526_; 
lean_dec(v_snd_517_);
lean_dec(v_fst_516_);
lean_dec(v_mvarId_491_);
lean_dec(v_tacticName_490_);
v___x_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_526_, 0, v_a_520_);
return v___x_526_;
}
}
v___jp_527_:
{
if (lean_obj_tag(v___y_528_) == 0)
{
lean_object* v_a_529_; lean_object* v_snd_530_; lean_object* v_snd_531_; lean_object* v_fst_532_; 
lean_dec(v_snd_517_);
lean_dec(v_fst_516_);
v_a_529_ = lean_ctor_get(v___y_528_, 0);
lean_inc(v_a_529_);
lean_dec_ref_known(v___y_528_, 1);
v_snd_530_ = lean_ctor_get(v_a_529_, 1);
lean_inc(v_snd_530_);
v_snd_531_ = lean_ctor_get(v_snd_530_, 1);
lean_inc(v_snd_531_);
v_fst_532_ = lean_ctor_get(v_a_529_, 0);
lean_inc(v_fst_532_);
lean_dec(v_a_529_);
if (lean_obj_tag(v_fst_532_) == 1)
{
lean_object* v_fst_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_583_; 
v_fst_533_ = lean_ctor_get(v_snd_530_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v_snd_530_);
if (v_isSharedCheck_583_ == 0)
{
lean_object* v_unused_584_; 
v_unused_584_ = lean_ctor_get(v_snd_530_, 1);
lean_dec(v_unused_584_);
v___x_535_ = v_snd_530_;
v_isShared_536_ = v_isSharedCheck_583_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_fst_533_);
lean_dec(v_snd_530_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_583_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v_fst_537_; lean_object* v_snd_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_582_; 
v_fst_537_ = lean_ctor_get(v_snd_531_, 0);
v_snd_538_ = lean_ctor_get(v_snd_531_, 1);
v_isSharedCheck_582_ = !lean_is_exclusive(v_snd_531_);
if (v_isSharedCheck_582_ == 0)
{
v___x_540_ = v_snd_531_;
v_isShared_541_ = v_isSharedCheck_582_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_snd_538_);
lean_inc(v_fst_537_);
lean_dec(v_snd_531_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_582_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v_val_542_; lean_object* v___x_543_; 
v_val_542_ = lean_ctor_get(v_fst_532_, 0);
lean_inc(v_val_542_);
lean_dec_ref_known(v_fst_532_, 1);
lean_inc(v_a_518_);
v___x_543_ = l_Lean_Meta_isExprDefEq(v_a_518_, v_val_542_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v_a_544_; uint8_t v___x_545_; 
v_a_544_ = lean_ctor_get(v___x_543_, 0);
lean_inc(v_a_544_);
lean_dec_ref_known(v___x_543_, 1);
v___x_545_ = lean_unbox(v_a_544_);
lean_dec(v_a_544_);
if (v___x_545_ == 0)
{
if (v_allowSynthFailures_489_ == 0)
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3);
lean_inc(v_mvarId_491_);
lean_inc(v_tacticName_490_);
v___x_547_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_490_, v_mvarId_491_, v___x_546_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
if (lean_obj_tag(v___x_547_) == 0)
{
lean_object* v___x_549_; 
lean_dec_ref_known(v___x_547_, 1);
if (v_isShared_541_ == 0)
{
v___x_549_ = v___x_540_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_fst_537_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_snd_538_);
v___x_549_ = v_reuseFailAlloc_553_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_object* v___x_551_; 
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 1, v___x_549_);
v___x_551_ = v___x_535_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_fst_533_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v___x_549_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
v_a_502_ = v___x_551_;
goto v___jp_501_;
}
}
}
else
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
lean_del_object(v___x_540_);
lean_dec(v_snd_538_);
lean_dec(v_fst_537_);
lean_del_object(v___x_535_);
lean_dec(v_fst_533_);
lean_dec(v_mvarId_491_);
lean_dec(v_tacticName_490_);
v_a_554_ = lean_ctor_get(v___x_547_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_561_ == 0)
{
v___x_556_ = v___x_547_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_547_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_a_554_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
else
{
lean_object* v___x_563_; 
if (v_isShared_541_ == 0)
{
v___x_563_ = v___x_540_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_fst_537_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v_snd_538_);
v___x_563_ = v_reuseFailAlloc_567_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
lean_object* v___x_565_; 
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 1, v___x_563_);
v___x_565_ = v___x_535_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_fst_533_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v___x_563_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
v_a_502_ = v___x_565_;
goto v___jp_501_;
}
}
}
}
else
{
lean_object* v___x_569_; 
if (v_isShared_541_ == 0)
{
v___x_569_ = v___x_540_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_fst_537_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v_snd_538_);
v___x_569_ = v_reuseFailAlloc_573_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
lean_object* v___x_571_; 
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 1, v___x_569_);
v___x_571_ = v___x_535_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_fst_533_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v___x_569_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
v_a_502_ = v___x_571_;
goto v___jp_501_;
}
}
}
}
else
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_581_; 
lean_del_object(v___x_540_);
lean_dec(v_snd_538_);
lean_dec(v_fst_537_);
lean_del_object(v___x_535_);
lean_dec(v_fst_533_);
lean_dec(v_mvarId_491_);
lean_dec(v_tacticName_490_);
v_a_574_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_581_ == 0)
{
v___x_576_ = v___x_543_;
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___x_543_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_579_; 
if (v_isShared_577_ == 0)
{
v___x_579_ = v___x_576_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_a_574_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
}
}
}
else
{
lean_object* v_fst_585_; lean_object* v_fst_586_; lean_object* v_snd_587_; 
lean_dec(v_fst_532_);
v_fst_585_ = lean_ctor_get(v_snd_530_, 0);
lean_inc(v_fst_585_);
lean_dec(v_snd_530_);
v_fst_586_ = lean_ctor_get(v_snd_531_, 0);
lean_inc(v_fst_586_);
v_snd_587_ = lean_ctor_get(v_snd_531_, 1);
lean_inc(v_snd_587_);
lean_dec(v_snd_531_);
v_fst_507_ = v_fst_585_;
v_fst_508_ = v_fst_586_;
v_snd_509_ = v_snd_587_;
goto v___jp_506_;
}
}
else
{
lean_object* v_a_588_; 
v_a_588_ = lean_ctor_get(v___y_528_, 0);
lean_inc(v_a_588_);
lean_dec_ref_known(v___y_528_, 1);
v_a_520_ = v_a_588_;
goto v___jp_519_;
}
}
}
v___jp_501_:
{
size_t v___x_503_; size_t v___x_504_; 
v___x_503_ = ((size_t)1ULL);
v___x_504_ = lean_usize_add(v_i_494_, v___x_503_);
v_i_494_ = v___x_504_;
v_b_495_ = v_a_502_;
goto _start;
}
v___jp_506_:
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_510_, 0, v_fst_508_);
lean_ctor_set(v___x_510_, 1, v_snd_509_);
v___x_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_511_, 0, v_fst_507_);
lean_ctor_set(v___x_511_, 1, v___x_510_);
v_a_502_ = v___x_511_;
goto v___jp_501_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___boxed(lean_object* v_allowSynthFailures_611_, lean_object* v_tacticName_612_, lean_object* v_mvarId_613_, lean_object* v_as_614_, lean_object* v_sz_615_, lean_object* v_i_616_, lean_object* v_b_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
uint8_t v_allowSynthFailures_boxed_623_; size_t v_sz_boxed_624_; size_t v_i_boxed_625_; lean_object* v_res_626_; 
v_allowSynthFailures_boxed_623_ = lean_unbox(v_allowSynthFailures_611_);
v_sz_boxed_624_ = lean_unbox_usize(v_sz_615_);
lean_dec(v_sz_615_);
v_i_boxed_625_ = lean_unbox_usize(v_i_616_);
lean_dec(v_i_616_);
v_res_626_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0(v_allowSynthFailures_boxed_623_, v_tacticName_612_, v_mvarId_613_, v_as_614_, v_sz_boxed_624_, v_i_boxed_625_, v_b_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec_ref(v_as_614_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(lean_object* v_tacticName_636_, lean_object* v_mvarId_637_, uint8_t v_allowSynthFailures_638_, lean_object* v_mvars_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_){
_start:
{
lean_object* v_postponed_645_; lean_object* v___x_646_; size_t v_sz_647_; size_t v___x_648_; lean_object* v___x_649_; 
v_postponed_645_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0));
v___x_646_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__2));
v_sz_647_ = lean_array_size(v_mvars_639_);
v___x_648_ = ((size_t)0ULL);
v___x_649_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0(v_allowSynthFailures_638_, v_tacticName_636_, v_mvarId_637_, v_mvars_639_, v_sz_647_, v___x_648_, v___x_646_, v_a_640_, v_a_641_, v_a_642_, v_a_643_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_672_; 
v_a_650_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_672_ == 0)
{
v___x_652_ = v___x_649_;
v_isShared_653_ = v_isSharedCheck_672_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_649_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_672_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v_fst_654_; 
v_fst_654_ = lean_ctor_get(v_a_650_, 0);
lean_inc(v_fst_654_);
if (lean_obj_tag(v_fst_654_) == 1)
{
lean_object* v_snd_655_; lean_object* v_fst_656_; uint8_t v___x_657_; 
v_snd_655_ = lean_ctor_get(v_a_650_, 1);
lean_inc(v_snd_655_);
lean_dec(v_a_650_);
v_fst_656_ = lean_ctor_get(v_snd_655_, 0);
v___x_657_ = lean_unbox(v_fst_656_);
if (v___x_657_ == 0)
{
lean_dec(v_snd_655_);
if (v_allowSynthFailures_638_ == 0)
{
lean_object* v_val_658_; lean_object* v___x_660_; 
v_val_658_ = lean_ctor_get(v_fst_654_, 0);
lean_inc(v_val_658_);
lean_dec_ref_known(v_fst_654_, 1);
if (v_isShared_653_ == 0)
{
lean_ctor_set_tag(v___x_652_, 1);
lean_ctor_set(v___x_652_, 0, v_val_658_);
v___x_660_ = v___x_652_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_val_658_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
else
{
lean_object* v___x_663_; 
lean_dec_ref_known(v_fst_654_, 1);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 0, v_postponed_645_);
v___x_663_ = v___x_652_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_postponed_645_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
else
{
lean_object* v_snd_665_; lean_object* v___x_667_; 
lean_dec_ref_known(v_fst_654_, 1);
v_snd_665_ = lean_ctor_get(v_snd_655_, 1);
lean_inc(v_snd_665_);
lean_dec(v_snd_655_);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 0, v_snd_665_);
v___x_667_ = v___x_652_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_snd_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
else
{
lean_object* v___x_670_; 
lean_dec(v_fst_654_);
lean_dec(v_a_650_);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 0, v_postponed_645_);
v___x_670_ = v___x_652_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_postponed_645_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
else
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_680_; 
v_a_673_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_680_ == 0)
{
v___x_675_ = v___x_649_;
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_649_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_678_; 
if (v_isShared_676_ == 0)
{
v___x_678_ = v___x_675_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_a_673_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___boxed(lean_object* v_tacticName_681_, lean_object* v_mvarId_682_, lean_object* v_allowSynthFailures_683_, lean_object* v_mvars_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_){
_start:
{
uint8_t v_allowSynthFailures_boxed_690_; lean_object* v_res_691_; 
v_allowSynthFailures_boxed_690_ = lean_unbox(v_allowSynthFailures_683_);
v_res_691_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(v_tacticName_681_, v_mvarId_682_, v_allowSynthFailures_boxed_690_, v_mvars_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
lean_dec(v_a_686_);
lean_dec_ref(v_a_685_);
lean_dec_ref(v_mvars_684_);
return v_res_691_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_keys_692_, lean_object* v_i_693_, lean_object* v_k_694_){
_start:
{
lean_object* v___x_695_; uint8_t v___x_696_; 
v___x_695_ = lean_array_get_size(v_keys_692_);
v___x_696_ = lean_nat_dec_lt(v_i_693_, v___x_695_);
if (v___x_696_ == 0)
{
lean_dec(v_i_693_);
return v___x_696_;
}
else
{
lean_object* v_k_x27_697_; uint8_t v___x_698_; 
v_k_x27_697_ = lean_array_fget_borrowed(v_keys_692_, v_i_693_);
v___x_698_ = l_Lean_instBEqMVarId_beq(v_k_694_, v_k_x27_697_);
if (v___x_698_ == 0)
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = lean_unsigned_to_nat(1u);
v___x_700_ = lean_nat_add(v_i_693_, v___x_699_);
lean_dec(v_i_693_);
v_i_693_ = v___x_700_;
goto _start;
}
else
{
lean_dec(v_i_693_);
return v___x_696_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_keys_702_, lean_object* v_i_703_, lean_object* v_k_704_){
_start:
{
uint8_t v_res_705_; lean_object* v_r_706_; 
v_res_705_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_702_, v_i_703_, v_k_704_);
lean_dec(v_k_704_);
lean_dec_ref(v_keys_702_);
v_r_706_ = lean_box(v_res_705_);
return v_r_706_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(lean_object* v_x_707_, size_t v_x_708_, lean_object* v_x_709_){
_start:
{
if (lean_obj_tag(v_x_707_) == 0)
{
lean_object* v_es_710_; lean_object* v___x_711_; size_t v___x_712_; size_t v___x_713_; lean_object* v_j_714_; lean_object* v___x_715_; 
v_es_710_ = lean_ctor_get(v_x_707_, 0);
v___x_711_ = lean_box(2);
v___x_712_ = ((size_t)31ULL);
v___x_713_ = lean_usize_land(v_x_708_, v___x_712_);
v_j_714_ = lean_usize_to_nat(v___x_713_);
v___x_715_ = lean_array_get_borrowed(v___x_711_, v_es_710_, v_j_714_);
lean_dec(v_j_714_);
switch(lean_obj_tag(v___x_715_))
{
case 0:
{
lean_object* v_key_716_; uint8_t v___x_717_; 
v_key_716_ = lean_ctor_get(v___x_715_, 0);
v___x_717_ = l_Lean_instBEqMVarId_beq(v_x_709_, v_key_716_);
return v___x_717_;
}
case 1:
{
lean_object* v_node_718_; size_t v___x_719_; size_t v___x_720_; 
v_node_718_ = lean_ctor_get(v___x_715_, 0);
v___x_719_ = ((size_t)5ULL);
v___x_720_ = lean_usize_shift_right(v_x_708_, v___x_719_);
v_x_707_ = v_node_718_;
v_x_708_ = v___x_720_;
goto _start;
}
default: 
{
uint8_t v___x_722_; 
v___x_722_ = 0;
return v___x_722_;
}
}
}
else
{
lean_object* v_ks_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
v_ks_723_ = lean_ctor_get(v_x_707_, 0);
v___x_724_ = lean_unsigned_to_nat(0u);
v___x_725_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_ks_723_, v___x_724_, v_x_709_);
return v___x_725_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_726_, lean_object* v_x_727_, lean_object* v_x_728_){
_start:
{
size_t v_x_2813__boxed_729_; uint8_t v_res_730_; lean_object* v_r_731_; 
v_x_2813__boxed_729_ = lean_unbox_usize(v_x_727_);
lean_dec(v_x_727_);
v_res_730_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_726_, v_x_2813__boxed_729_, v_x_728_);
lean_dec(v_x_728_);
lean_dec_ref(v_x_726_);
v_r_731_ = lean_box(v_res_730_);
return v_r_731_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(lean_object* v_x_732_, lean_object* v_x_733_){
_start:
{
uint64_t v___x_734_; size_t v___x_735_; uint8_t v___x_736_; 
v___x_734_ = l_Lean_instHashableMVarId_hash(v_x_733_);
v___x_735_ = lean_uint64_to_usize(v___x_734_);
v___x_736_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_732_, v___x_735_, v_x_733_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg___boxed(lean_object* v_x_737_, lean_object* v_x_738_){
_start:
{
uint8_t v_res_739_; lean_object* v_r_740_; 
v_res_739_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_x_737_, v_x_738_);
lean_dec(v_x_738_);
lean_dec_ref(v_x_737_);
v_r_740_ = lean_box(v_res_739_);
return v_r_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(lean_object* v_mvarId_741_, lean_object* v___y_742_){
_start:
{
lean_object* v___x_744_; lean_object* v_mctx_745_; lean_object* v_eAssignment_746_; uint8_t v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_744_ = lean_st_ref_get(v___y_742_);
v_mctx_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc_ref(v_mctx_745_);
lean_dec(v___x_744_);
v_eAssignment_746_ = lean_ctor_get(v_mctx_745_, 8);
lean_inc_ref(v_eAssignment_746_);
lean_dec_ref(v_mctx_745_);
v___x_747_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_eAssignment_746_, v_mvarId_741_);
lean_dec_ref(v_eAssignment_746_);
v___x_748_ = lean_box(v___x_747_);
v___x_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg___boxed(lean_object* v_mvarId_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v_mvarId_750_, v___y_751_);
lean_dec(v___y_751_);
lean_dec(v_mvarId_750_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(uint8_t v_synthAssignedInstances_754_, lean_object* v_as_755_, size_t v_sz_756_, size_t v_i_757_, lean_object* v_b_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v_a_765_; uint8_t v___x_769_; 
v___x_769_ = lean_usize_dec_lt(v_i_757_, v_sz_756_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; 
v___x_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_770_, 0, v_b_758_);
return v___x_770_;
}
else
{
lean_object* v_snd_771_; lean_object* v_fst_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_821_; 
v_snd_771_ = lean_ctor_get(v_b_758_, 1);
v_fst_772_ = lean_ctor_get(v_b_758_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v_b_758_);
if (v_isSharedCheck_821_ == 0)
{
v___x_774_ = v_b_758_;
v_isShared_775_ = v_isSharedCheck_821_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_snd_771_);
lean_inc(v_fst_772_);
lean_dec(v_b_758_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_821_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v_array_776_; lean_object* v_start_777_; lean_object* v_stop_778_; uint8_t v___x_779_; 
v_array_776_ = lean_ctor_get(v_snd_771_, 0);
v_start_777_ = lean_ctor_get(v_snd_771_, 1);
v_stop_778_ = lean_ctor_get(v_snd_771_, 2);
v___x_779_ = lean_nat_dec_lt(v_start_777_, v_stop_778_);
if (v___x_779_ == 0)
{
lean_object* v___x_781_; 
if (v_isShared_775_ == 0)
{
v___x_781_ = v___x_774_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_fst_772_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v_snd_771_);
v___x_781_ = v_reuseFailAlloc_783_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_782_; 
v___x_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
return v___x_782_;
}
}
else
{
lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_817_; 
lean_inc(v_stop_778_);
lean_inc(v_start_777_);
lean_inc_ref(v_array_776_);
v_isSharedCheck_817_ = !lean_is_exclusive(v_snd_771_);
if (v_isSharedCheck_817_ == 0)
{
lean_object* v_unused_818_; lean_object* v_unused_819_; lean_object* v_unused_820_; 
v_unused_818_ = lean_ctor_get(v_snd_771_, 2);
lean_dec(v_unused_818_);
v_unused_819_ = lean_ctor_get(v_snd_771_, 1);
lean_dec(v_unused_819_);
v_unused_820_ = lean_ctor_get(v_snd_771_, 0);
lean_dec(v_unused_820_);
v___x_785_ = v_snd_771_;
v_isShared_786_ = v_isSharedCheck_817_;
goto v_resetjp_784_;
}
else
{
lean_dec(v_snd_771_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_817_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_791_; 
v___x_787_ = lean_array_fget(v_array_776_, v_start_777_);
v___x_788_ = lean_unsigned_to_nat(1u);
v___x_789_ = lean_nat_add(v_start_777_, v___x_788_);
lean_dec(v_start_777_);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 1, v___x_789_);
v___x_791_ = v___x_785_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_array_776_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v___x_789_);
lean_ctor_set(v_reuseFailAlloc_816_, 2, v_stop_778_);
v___x_791_ = v_reuseFailAlloc_816_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
uint8_t v___x_792_; uint8_t v___x_793_; 
v___x_792_ = lean_unbox(v___x_787_);
lean_dec(v___x_787_);
v___x_793_ = l_Lean_BinderInfo_isInstImplicit(v___x_792_);
if (v___x_793_ == 0)
{
lean_object* v___x_795_; 
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 1, v___x_791_);
v___x_795_ = v___x_774_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_fst_772_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v___x_791_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
v_a_765_ = v___x_795_;
goto v___jp_764_;
}
}
else
{
lean_object* v_a_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v_a_797_ = lean_array_uget_borrowed(v_as_755_, v_i_757_);
v___x_798_ = l_Lean_Expr_mvarId_x21(v_a_797_);
v___x_799_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_798_, v___y_760_);
lean_dec(v___x_798_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_a_800_);
lean_dec_ref_known(v___x_799_, 1);
if (v_synthAssignedInstances_754_ == 0)
{
uint8_t v___x_806_; 
v___x_806_ = lean_unbox(v_a_800_);
lean_dec(v_a_800_);
if (v___x_806_ == 0)
{
goto v___jp_801_;
}
else
{
lean_object* v___x_807_; 
lean_del_object(v___x_774_);
v___x_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_807_, 0, v_fst_772_);
lean_ctor_set(v___x_807_, 1, v___x_791_);
v_a_765_ = v___x_807_;
goto v___jp_764_;
}
}
else
{
lean_dec(v_a_800_);
goto v___jp_801_;
}
v___jp_801_:
{
lean_object* v___x_802_; lean_object* v___x_804_; 
lean_inc(v_a_797_);
v___x_802_ = lean_array_push(v_fst_772_, v_a_797_);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 1, v___x_791_);
lean_ctor_set(v___x_774_, 0, v___x_802_);
v___x_804_ = v___x_774_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v___x_791_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
v_a_765_ = v___x_804_;
goto v___jp_764_;
}
}
}
else
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
lean_dec_ref(v___x_791_);
lean_del_object(v___x_774_);
lean_dec(v_fst_772_);
v_a_808_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_815_ == 0)
{
v___x_810_ = v___x_799_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_799_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_808_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
}
}
}
}
}
v___jp_764_:
{
size_t v___x_766_; size_t v___x_767_; 
v___x_766_ = ((size_t)1ULL);
v___x_767_ = lean_usize_add(v_i_757_, v___x_766_);
v_i_757_ = v___x_767_;
v_b_758_ = v_a_765_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1___boxed(lean_object* v_synthAssignedInstances_822_, lean_object* v_as_823_, lean_object* v_sz_824_, lean_object* v_i_825_, lean_object* v_b_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
uint8_t v_synthAssignedInstances_boxed_832_; size_t v_sz_boxed_833_; size_t v_i_boxed_834_; lean_object* v_res_835_; 
v_synthAssignedInstances_boxed_832_ = lean_unbox(v_synthAssignedInstances_822_);
v_sz_boxed_833_ = lean_unbox_usize(v_sz_824_);
lean_dec(v_sz_824_);
v_i_boxed_834_ = lean_unbox_usize(v_i_825_);
lean_dec(v_i_825_);
v_res_835_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(v_synthAssignedInstances_boxed_832_, v_as_823_, v_sz_boxed_833_, v_i_boxed_834_, v_b_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec_ref(v_as_823_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(lean_object* v_tacticName_836_, lean_object* v_mvarId_837_, uint8_t v_allowSynthFailures_838_, lean_object* v_a_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; uint8_t v___x_847_; 
v___x_845_ = lean_array_get_size(v_a_839_);
v___x_846_ = lean_unsigned_to_nat(0u);
v___x_847_ = lean_nat_dec_eq(v___x_845_, v___x_846_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; 
lean_inc(v_mvarId_837_);
lean_inc(v_tacticName_836_);
v___x_848_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(v_tacticName_836_, v_mvarId_837_, v_allowSynthFailures_838_, v_a_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
lean_dec_ref(v_a_839_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_a_849_);
lean_dec_ref_known(v___x_848_, 1);
v_a_839_ = v_a_849_;
goto _start;
}
else
{
lean_dec(v_mvarId_837_);
lean_dec(v_tacticName_836_);
return v___x_848_;
}
}
else
{
lean_object* v___x_851_; 
lean_dec(v_mvarId_837_);
lean_dec(v_tacticName_836_);
v___x_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_851_, 0, v_a_839_);
return v___x_851_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg___boxed(lean_object* v_tacticName_852_, lean_object* v_mvarId_853_, lean_object* v_allowSynthFailures_854_, lean_object* v_a_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
uint8_t v_allowSynthFailures_boxed_861_; lean_object* v_res_862_; 
v_allowSynthFailures_boxed_861_ = lean_unbox(v_allowSynthFailures_854_);
v_res_862_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(v_tacticName_852_, v_mvarId_853_, v_allowSynthFailures_boxed_861_, v_a_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances(lean_object* v_tacticName_863_, lean_object* v_mvarId_864_, lean_object* v_mvarsNew_865_, lean_object* v_binderInfos_866_, uint8_t v_synthAssignedInstances_867_, uint8_t v_allowSynthFailures_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_){
_start:
{
lean_object* v___x_874_; lean_object* v_todo_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; size_t v_sz_879_; size_t v___x_880_; lean_object* v___x_881_; 
v___x_874_ = lean_unsigned_to_nat(0u);
v_todo_875_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0));
v___x_876_ = lean_array_get_size(v_binderInfos_866_);
v___x_877_ = l_Array_toSubarray___redArg(v_binderInfos_866_, v___x_874_, v___x_876_);
v___x_878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_878_, 0, v_todo_875_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
v_sz_879_ = lean_array_size(v_mvarsNew_865_);
v___x_880_ = ((size_t)0ULL);
v___x_881_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(v_synthAssignedInstances_867_, v_mvarsNew_865_, v_sz_879_, v___x_880_, v___x_878_, v_a_869_, v_a_870_, v_a_871_, v_a_872_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; lean_object* v_fst_883_; lean_object* v___x_884_; 
v_a_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_a_882_);
lean_dec_ref_known(v___x_881_, 1);
v_fst_883_ = lean_ctor_get(v_a_882_, 0);
lean_inc(v_fst_883_);
lean_dec(v_a_882_);
v___x_884_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(v_tacticName_863_, v_mvarId_864_, v_allowSynthFailures_868_, v_fst_883_, v_a_869_, v_a_870_, v_a_871_, v_a_872_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_892_; 
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_892_ == 0)
{
lean_object* v_unused_893_; 
v_unused_893_ = lean_ctor_get(v___x_884_, 0);
lean_dec(v_unused_893_);
v___x_886_ = v___x_884_;
v_isShared_887_ = v_isSharedCheck_892_;
goto v_resetjp_885_;
}
else
{
lean_dec(v___x_884_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_892_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_888_; lean_object* v___x_890_; 
v___x_888_ = lean_box(0);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 0, v___x_888_);
v___x_890_ = v___x_886_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_888_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
else
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
v_a_894_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_901_ == 0)
{
v___x_896_ = v___x_884_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_884_);
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
else
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
lean_dec(v_mvarId_864_);
lean_dec(v_tacticName_863_);
v_a_902_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_881_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_881_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances___boxed(lean_object* v_tacticName_910_, lean_object* v_mvarId_911_, lean_object* v_mvarsNew_912_, lean_object* v_binderInfos_913_, lean_object* v_synthAssignedInstances_914_, lean_object* v_allowSynthFailures_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_){
_start:
{
uint8_t v_synthAssignedInstances_boxed_921_; uint8_t v_allowSynthFailures_boxed_922_; lean_object* v_res_923_; 
v_synthAssignedInstances_boxed_921_ = lean_unbox(v_synthAssignedInstances_914_);
v_allowSynthFailures_boxed_922_ = lean_unbox(v_allowSynthFailures_915_);
v_res_923_ = l_Lean_Meta_synthAppInstances(v_tacticName_910_, v_mvarId_911_, v_mvarsNew_912_, v_binderInfos_913_, v_synthAssignedInstances_boxed_921_, v_allowSynthFailures_boxed_922_, v_a_916_, v_a_917_, v_a_918_, v_a_919_);
lean_dec(v_a_919_);
lean_dec_ref(v_a_918_);
lean_dec(v_a_917_);
lean_dec_ref(v_a_916_);
lean_dec_ref(v_mvarsNew_912_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0(lean_object* v_mvarId_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v_mvarId_924_, v___y_926_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___boxed(lean_object* v_mvarId_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0(v_mvarId_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v_mvarId_931_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2(lean_object* v_tacticName_938_, lean_object* v_mvarId_939_, uint8_t v_allowSynthFailures_940_, lean_object* v_inst_941_, lean_object* v_a_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(v_tacticName_938_, v_mvarId_939_, v_allowSynthFailures_940_, v_a_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___boxed(lean_object* v_tacticName_949_, lean_object* v_mvarId_950_, lean_object* v_allowSynthFailures_951_, lean_object* v_inst_952_, lean_object* v_a_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
uint8_t v_allowSynthFailures_boxed_959_; lean_object* v_res_960_; 
v_allowSynthFailures_boxed_959_ = lean_unbox(v_allowSynthFailures_951_);
v_res_960_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2(v_tacticName_949_, v_mvarId_950_, v_allowSynthFailures_boxed_959_, v_inst_952_, v_a_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
return v_res_960_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0(lean_object* v_00_u03b2_961_, lean_object* v_x_962_, lean_object* v_x_963_){
_start:
{
uint8_t v___x_964_; 
v___x_964_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_x_962_, v_x_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___boxed(lean_object* v_00_u03b2_965_, lean_object* v_x_966_, lean_object* v_x_967_){
_start:
{
uint8_t v_res_968_; lean_object* v_r_969_; 
v_res_968_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0(v_00_u03b2_965_, v_x_966_, v_x_967_);
lean_dec(v_x_967_);
lean_dec_ref(v_x_966_);
v_r_969_ = lean_box(v_res_968_);
return v_r_969_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_970_, lean_object* v_x_971_, size_t v_x_972_, lean_object* v_x_973_){
_start:
{
uint8_t v___x_974_; 
v___x_974_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_971_, v_x_972_, v_x_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_975_, lean_object* v_x_976_, lean_object* v_x_977_, lean_object* v_x_978_){
_start:
{
size_t v_x_3145__boxed_979_; uint8_t v_res_980_; lean_object* v_r_981_; 
v_x_3145__boxed_979_ = lean_unbox_usize(v_x_977_);
lean_dec(v_x_977_);
v_res_980_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1(v_00_u03b2_975_, v_x_976_, v_x_3145__boxed_979_, v_x_978_);
lean_dec(v_x_978_);
lean_dec_ref(v_x_976_);
v_r_981_ = lean_box(v_res_980_);
return v_r_981_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_982_, lean_object* v_keys_983_, lean_object* v_vals_984_, lean_object* v_heq_985_, lean_object* v_i_986_, lean_object* v_k_987_){
_start:
{
uint8_t v___x_988_; 
v___x_988_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_983_, v_i_986_, v_k_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_989_, lean_object* v_keys_990_, lean_object* v_vals_991_, lean_object* v_heq_992_, lean_object* v_i_993_, lean_object* v_k_994_){
_start:
{
uint8_t v_res_995_; lean_object* v_r_996_; 
v_res_995_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_989_, v_keys_990_, v_vals_991_, v_heq_992_, v_i_993_, v_k_994_);
lean_dec(v_k_994_);
lean_dec_ref(v_vals_991_);
lean_dec_ref(v_keys_990_);
v_r_996_ = lean_box(v_res_995_);
return v_r_996_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(lean_object* v_newMVars_997_, lean_object* v_binderInfos_998_, lean_object* v_a_999_, lean_object* v_n_1000_, lean_object* v_i_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v_zero_1007_; uint8_t v_isZero_1008_; 
v_zero_1007_ = lean_unsigned_to_nat(0u);
v_isZero_1008_ = lean_nat_dec_eq(v_i_1001_, v_zero_1007_);
if (v_isZero_1008_ == 1)
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
lean_dec(v_i_1001_);
lean_dec(v_a_999_);
v___x_1009_ = lean_box(0);
v___x_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
return v___x_1010_;
}
else
{
uint8_t v___x_1011_; lean_object* v_one_1012_; lean_object* v_n_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v_a_1019_; uint8_t v___x_1020_; 
v___x_1011_ = 0;
v_one_1012_ = lean_unsigned_to_nat(1u);
v_n_1013_ = lean_nat_sub(v_i_1001_, v_one_1012_);
lean_dec(v_i_1001_);
v___x_1014_ = lean_nat_sub(v_n_1000_, v_n_1013_);
v___x_1015_ = lean_nat_sub(v___x_1014_, v_one_1012_);
lean_dec(v___x_1014_);
v___x_1016_ = lean_array_fget_borrowed(v_newMVars_997_, v___x_1015_);
v___x_1017_ = l_Lean_Expr_mvarId_x21(v___x_1016_);
v___x_1018_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_1017_, v___y_1003_);
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_a_1019_);
lean_dec_ref(v___x_1018_);
v___x_1020_ = lean_unbox(v_a_1019_);
lean_dec(v_a_1019_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; lean_object* v___x_1022_; uint8_t v___x_1023_; uint8_t v___x_1024_; 
v___x_1021_ = lean_box(v___x_1011_);
v___x_1022_ = lean_array_get(v___x_1021_, v_binderInfos_998_, v___x_1015_);
lean_dec(v___x_1015_);
lean_dec(v___x_1021_);
v___x_1023_ = lean_unbox(v___x_1022_);
lean_dec(v___x_1022_);
v___x_1024_ = l_Lean_BinderInfo_isInstImplicit(v___x_1023_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1025_; 
lean_inc(v___x_1017_);
v___x_1025_ = l_Lean_MVarId_getTag(v___x_1017_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_a_1026_);
lean_dec_ref_known(v___x_1025_, 1);
lean_inc(v_a_999_);
v___x_1027_ = l_Lean_Meta_appendTag(v_a_999_, v_a_1026_);
lean_dec(v_a_1026_);
v___x_1028_ = l_Lean_MVarId_setTag___redArg(v___x_1017_, v___x_1027_, v___y_1003_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_dec_ref_known(v___x_1028_, 1);
v_i_1001_ = v_n_1013_;
goto _start;
}
else
{
lean_dec(v_n_1013_);
lean_dec(v_a_999_);
return v___x_1028_;
}
}
else
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1037_; 
lean_dec(v___x_1017_);
lean_dec(v_n_1013_);
lean_dec(v_a_999_);
v_a_1030_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1032_ = v___x_1025_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_1025_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1030_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
else
{
lean_dec(v___x_1017_);
v_i_1001_ = v_n_1013_;
goto _start;
}
}
else
{
lean_dec(v___x_1017_);
lean_dec(v___x_1015_);
v_i_1001_ = v_n_1013_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg___boxed(lean_object* v_newMVars_1040_, lean_object* v_binderInfos_1041_, lean_object* v_a_1042_, lean_object* v_n_1043_, lean_object* v_i_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_1040_, v_binderInfos_1041_, v_a_1042_, v_n_1043_, v_i_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
lean_dec(v_n_1043_);
lean_dec_ref(v_binderInfos_1041_);
lean_dec_ref(v_newMVars_1040_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendParentTag(lean_object* v_mvarId_1051_, lean_object* v_newMVars_1052_, lean_object* v_binderInfos_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = l_Lean_instInhabitedExpr;
v___x_1060_ = l_Lean_MVarId_getTag(v_mvarId_1051_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1078_; 
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1063_ = v___x_1060_;
v_isShared_1064_ = v_isSharedCheck_1078_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1060_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1078_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; uint8_t v___x_1067_; 
v___x_1065_ = lean_array_get_size(v_newMVars_1052_);
v___x_1066_ = lean_unsigned_to_nat(1u);
v___x_1067_ = lean_nat_dec_eq(v___x_1065_, v___x_1066_);
if (v___x_1067_ == 0)
{
uint8_t v___x_1068_; 
v___x_1068_ = l_Lean_Name_isAnonymous(v_a_1061_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; 
lean_del_object(v___x_1063_);
v___x_1069_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_1052_, v_binderInfos_1053_, v_a_1061_, v___x_1065_, v___x_1065_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_);
return v___x_1069_;
}
else
{
lean_object* v___x_1070_; lean_object* v___x_1072_; 
lean_dec(v_a_1061_);
v___x_1070_ = lean_box(0);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 0, v___x_1070_);
v___x_1072_ = v___x_1063_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1070_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
else
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
lean_del_object(v___x_1063_);
v___x_1074_ = lean_unsigned_to_nat(0u);
v___x_1075_ = lean_array_get_borrowed(v___x_1059_, v_newMVars_1052_, v___x_1074_);
v___x_1076_ = l_Lean_Expr_mvarId_x21(v___x_1075_);
v___x_1077_ = l_Lean_MVarId_setTag___redArg(v___x_1076_, v_a_1061_, v_a_1055_);
return v___x_1077_;
}
}
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
v_a_1079_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_1060_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1060_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendParentTag___boxed(lean_object* v_mvarId_1087_, lean_object* v_newMVars_1088_, lean_object* v_binderInfos_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Lean_Meta_appendParentTag(v_mvarId_1087_, v_newMVars_1088_, v_binderInfos_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_);
lean_dec(v_a_1093_);
lean_dec_ref(v_a_1092_);
lean_dec(v_a_1091_);
lean_dec_ref(v_a_1090_);
lean_dec_ref(v_binderInfos_1089_);
lean_dec_ref(v_newMVars_1088_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0(lean_object* v_newMVars_1096_, lean_object* v_binderInfos_1097_, lean_object* v_a_1098_, lean_object* v_n_1099_, lean_object* v_i_1100_, lean_object* v_a_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v___x_1107_; 
v___x_1107_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_1096_, v_binderInfos_1097_, v_a_1098_, v_n_1099_, v_i_1100_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___boxed(lean_object* v_newMVars_1108_, lean_object* v_binderInfos_1109_, lean_object* v_a_1110_, lean_object* v_n_1111_, lean_object* v_i_1112_, lean_object* v_a_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0(v_newMVars_1108_, v_binderInfos_1109_, v_a_1110_, v_n_1111_, v_i_1112_, v_a_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v_n_1111_);
lean_dec_ref(v_binderInfos_1109_);
lean_dec_ref(v_newMVars_1108_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_postprocessAppMVars(lean_object* v_tacticName_1120_, lean_object* v_mvarId_1121_, lean_object* v_newMVars_1122_, lean_object* v_binderInfos_1123_, uint8_t v_synthAssignedInstances_1124_, uint8_t v_allowSynthFailures_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_){
_start:
{
lean_object* v___x_1131_; 
v___x_1131_ = l_Lean_Meta_synthAppInstances(v_tacticName_1120_, v_mvarId_1121_, v_newMVars_1122_, v_binderInfos_1123_, v_synthAssignedInstances_1124_, v_allowSynthFailures_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_postprocessAppMVars___boxed(lean_object* v_tacticName_1132_, lean_object* v_mvarId_1133_, lean_object* v_newMVars_1134_, lean_object* v_binderInfos_1135_, lean_object* v_synthAssignedInstances_1136_, lean_object* v_allowSynthFailures_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_){
_start:
{
uint8_t v_synthAssignedInstances_boxed_1143_; uint8_t v_allowSynthFailures_boxed_1144_; lean_object* v_res_1145_; 
v_synthAssignedInstances_boxed_1143_ = lean_unbox(v_synthAssignedInstances_1136_);
v_allowSynthFailures_boxed_1144_ = lean_unbox(v_allowSynthFailures_1137_);
v_res_1145_ = l_Lean_Meta_postprocessAppMVars(v_tacticName_1132_, v_mvarId_1133_, v_newMVars_1134_, v_binderInfos_1135_, v_synthAssignedInstances_boxed_1143_, v_allowSynthFailures_boxed_1144_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_);
lean_dec(v_a_1141_);
lean_dec_ref(v_a_1140_);
lean_dec(v_a_1139_);
lean_dec_ref(v_a_1138_);
lean_dec_ref(v_newMVars_1134_);
return v_res_1145_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0(lean_object* v_mvar_1146_, lean_object* v_mvarId_1147_){
_start:
{
lean_object* v___x_1148_; uint8_t v___x_1149_; 
v___x_1148_ = l_Lean_Expr_mvarId_x21(v_mvar_1146_);
v___x_1149_ = l_Lean_instBEqMVarId_beq(v_mvarId_1147_, v___x_1148_);
lean_dec(v___x_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0___boxed(lean_object* v_mvar_1150_, lean_object* v_mvarId_1151_){
_start:
{
uint8_t v_res_1152_; lean_object* v_r_1153_; 
v_res_1152_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0(v_mvar_1150_, v_mvarId_1151_);
lean_dec(v_mvarId_1151_);
lean_dec_ref(v_mvar_1150_);
v_r_1153_ = lean_box(v_res_1152_);
return v_r_1153_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(lean_object* v_mvar_1154_, lean_object* v_as_1155_, size_t v_i_1156_, size_t v_stop_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
uint8_t v___x_1167_; 
v___x_1167_ = lean_usize_dec_eq(v_i_1156_, v_stop_1157_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; uint8_t v___x_1169_; 
v___x_1168_ = lean_array_uget_borrowed(v_as_1155_, v_i_1156_);
v___x_1169_ = lean_expr_eqv(v_mvar_1154_, v___x_1168_);
if (v___x_1169_ == 0)
{
lean_object* v___f_1170_; uint8_t v___x_1171_; lean_object* v___x_1172_; 
lean_inc_ref(v_mvar_1154_);
v___f_1170_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1170_, 0, v_mvar_1154_);
v___x_1171_ = 1;
lean_inc(v___y_1161_);
lean_inc_ref(v___y_1160_);
lean_inc(v___y_1159_);
lean_inc_ref(v___y_1158_);
lean_inc(v___x_1168_);
v___x_1172_ = lean_infer_type(v___x_1168_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1183_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1175_ = v___x_1172_;
v_isShared_1176_ = v_isSharedCheck_1183_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1172_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1183_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = lean_box(0);
v___x_1178_ = l_Lean_FindMVar_main(v___f_1170_, v_a_1173_, v___x_1177_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_del_object(v___x_1175_);
goto v___jp_1163_;
}
else
{
lean_object* v___x_1179_; lean_object* v___x_1181_; 
lean_dec_ref_known(v___x_1178_, 1);
lean_dec_ref(v_mvar_1154_);
v___x_1179_ = lean_box(v___x_1171_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 0, v___x_1179_);
v___x_1181_ = v___x_1175_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1179_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
else
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1191_; 
lean_dec_ref(v___f_1170_);
lean_dec_ref(v_mvar_1154_);
v_a_1184_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1186_ = v___x_1172_;
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1172_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1189_; 
if (v_isShared_1187_ == 0)
{
v___x_1189_ = v___x_1186_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1184_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
else
{
goto v___jp_1163_;
}
}
else
{
uint8_t v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
lean_dec_ref(v_mvar_1154_);
v___x_1192_ = 0;
v___x_1193_ = lean_box(v___x_1192_);
v___x_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
return v___x_1194_;
}
v___jp_1163_:
{
size_t v___x_1164_; size_t v___x_1165_; 
v___x_1164_ = ((size_t)1ULL);
v___x_1165_ = lean_usize_add(v_i_1156_, v___x_1164_);
v_i_1156_ = v___x_1165_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___boxed(lean_object* v_mvar_1195_, lean_object* v_as_1196_, lean_object* v_i_1197_, lean_object* v_stop_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
size_t v_i_boxed_1204_; size_t v_stop_boxed_1205_; lean_object* v_res_1206_; 
v_i_boxed_1204_ = lean_unbox_usize(v_i_1197_);
lean_dec(v_i_1197_);
v_stop_boxed_1205_ = lean_unbox_usize(v_stop_1198_);
lean_dec(v_stop_1198_);
v_res_1206_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(v_mvar_1195_, v_as_1196_, v_i_boxed_1204_, v_stop_boxed_1205_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec_ref(v_as_1196_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(lean_object* v_mvar_1207_, lean_object* v_otherMVars_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; uint8_t v___x_1216_; 
v___x_1214_ = lean_unsigned_to_nat(0u);
v___x_1215_ = lean_array_get_size(v_otherMVars_1208_);
v___x_1216_ = lean_nat_dec_lt(v___x_1214_, v___x_1215_);
if (v___x_1216_ == 0)
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
lean_dec_ref(v_mvar_1207_);
v___x_1217_ = lean_box(v___x_1216_);
v___x_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
return v___x_1218_;
}
else
{
if (v___x_1216_ == 0)
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
lean_dec_ref(v_mvar_1207_);
v___x_1219_ = lean_box(v___x_1216_);
v___x_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
return v___x_1220_;
}
else
{
size_t v___x_1221_; size_t v___x_1222_; lean_object* v___x_1223_; 
v___x_1221_ = ((size_t)0ULL);
v___x_1222_ = lean_usize_of_nat(v___x_1215_);
v___x_1223_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(v_mvar_1207_, v_otherMVars_1208_, v___x_1221_, v___x_1222_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_);
return v___x_1223_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___boxed(lean_object* v_mvar_1224_, lean_object* v_otherMVars_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(v_mvar_1224_, v_otherMVars_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec_ref(v_otherMVars_1225_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(lean_object* v_mvars_1232_, lean_object* v_as_1233_, size_t v_i_1234_, size_t v_stop_1235_, lean_object* v_b_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v_a_1243_; uint8_t v___x_1247_; 
v___x_1247_ = lean_usize_dec_eq(v_i_1234_, v_stop_1235_);
if (v___x_1247_ == 0)
{
lean_object* v_fst_1248_; lean_object* v_snd_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1274_; 
v_fst_1248_ = lean_ctor_get(v_b_1236_, 0);
v_snd_1249_ = lean_ctor_get(v_b_1236_, 1);
v_isSharedCheck_1274_ = !lean_is_exclusive(v_b_1236_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1251_ = v_b_1236_;
v_isShared_1252_ = v_isSharedCheck_1274_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_snd_1249_);
lean_inc(v_fst_1248_);
lean_dec(v_b_1236_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1274_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1253_; lean_object* v_currMVarId_1254_; lean_object* v___x_1255_; 
v___x_1253_ = lean_array_uget_borrowed(v_as_1233_, v_i_1234_);
v_currMVarId_1254_ = l_Lean_Expr_mvarId_x21(v___x_1253_);
lean_inc(v___x_1253_);
v___x_1255_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(v___x_1253_, v_mvars_1232_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v_a_1256_; uint8_t v___x_1257_; 
v_a_1256_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_a_1256_);
lean_dec_ref_known(v___x_1255_, 1);
v___x_1257_ = lean_unbox(v_a_1256_);
lean_dec(v_a_1256_);
if (v___x_1257_ == 0)
{
lean_object* v___x_1258_; lean_object* v___x_1260_; 
v___x_1258_ = lean_array_push(v_fst_1248_, v_currMVarId_1254_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 0, v___x_1258_);
v___x_1260_ = v___x_1251_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1258_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v_snd_1249_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
v_a_1243_ = v___x_1260_;
goto v___jp_1242_;
}
}
else
{
lean_object* v___x_1262_; lean_object* v___x_1264_; 
v___x_1262_ = lean_array_push(v_snd_1249_, v_currMVarId_1254_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 1, v___x_1262_);
v___x_1264_ = v___x_1251_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_fst_1248_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v___x_1262_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
v_a_1243_ = v___x_1264_;
goto v___jp_1242_;
}
}
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec(v_currMVarId_1254_);
lean_del_object(v___x_1251_);
lean_dec(v_snd_1249_);
lean_dec(v_fst_1248_);
v_a_1266_ = lean_ctor_get(v___x_1255_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1255_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1255_);
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
else
{
lean_object* v___x_1275_; 
v___x_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1275_, 0, v_b_1236_);
return v___x_1275_;
}
v___jp_1242_:
{
size_t v___x_1244_; size_t v___x_1245_; 
v___x_1244_ = ((size_t)1ULL);
v___x_1245_ = lean_usize_add(v_i_1234_, v___x_1244_);
v_i_1234_ = v___x_1245_;
v_b_1236_ = v_a_1243_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0___boxed(lean_object* v_mvars_1276_, lean_object* v_as_1277_, lean_object* v_i_1278_, lean_object* v_stop_1279_, lean_object* v_b_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
size_t v_i_boxed_1286_; size_t v_stop_boxed_1287_; lean_object* v_res_1288_; 
v_i_boxed_1286_ = lean_unbox_usize(v_i_1278_);
lean_dec(v_i_1278_);
v_stop_boxed_1287_ = lean_unbox_usize(v_stop_1279_);
lean_dec(v_stop_1279_);
v_res_1288_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_1276_, v_as_1277_, v_i_boxed_1286_, v_stop_boxed_1287_, v_b_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec_ref(v_as_1277_);
lean_dec_ref(v_mvars_1276_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(lean_object* v_mvars_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; uint8_t v___x_1302_; 
v___x_1299_ = lean_unsigned_to_nat(0u);
v___x_1300_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1));
v___x_1301_ = lean_array_get_size(v_mvars_1293_);
v___x_1302_ = lean_nat_dec_lt(v___x_1299_, v___x_1301_);
if (v___x_1302_ == 0)
{
lean_object* v___x_1303_; 
v___x_1303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1300_);
return v___x_1303_;
}
else
{
size_t v___x_1304_; size_t v___x_1305_; lean_object* v___x_1306_; 
v___x_1304_ = ((size_t)0ULL);
v___x_1305_ = lean_usize_of_nat(v___x_1301_);
v___x_1306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_1293_, v_mvars_1293_, v___x_1304_, v___x_1305_, v___x_1300_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_);
return v___x_1306_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___boxed(lean_object* v_mvars_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
lean_dec(v_a_1311_);
lean_dec_ref(v_a_1310_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec_ref(v_mvars_1307_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals_spec__0(lean_object* v_a_1314_, lean_object* v_a_1315_){
_start:
{
if (lean_obj_tag(v_a_1314_) == 0)
{
lean_object* v___x_1316_; 
v___x_1316_ = l_List_reverse___redArg(v_a_1315_);
return v___x_1316_;
}
else
{
lean_object* v_head_1317_; lean_object* v_tail_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1327_; 
v_head_1317_ = lean_ctor_get(v_a_1314_, 0);
v_tail_1318_ = lean_ctor_get(v_a_1314_, 1);
v_isSharedCheck_1327_ = !lean_is_exclusive(v_a_1314_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1320_ = v_a_1314_;
v_isShared_1321_ = v_isSharedCheck_1327_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_tail_1318_);
lean_inc(v_head_1317_);
lean_dec(v_a_1314_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1327_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1322_; lean_object* v___x_1324_; 
v___x_1322_ = l_Lean_Expr_mvarId_x21(v_head_1317_);
lean_dec(v_head_1317_);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 1, v_a_1315_);
lean_ctor_set(v___x_1320_, 0, v___x_1322_);
v___x_1324_ = v___x_1320_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v___x_1322_);
lean_ctor_set(v_reuseFailAlloc_1326_, 1, v_a_1315_);
v___x_1324_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
v_a_1314_ = v_tail_1318_;
v_a_1315_ = v___x_1324_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(lean_object* v_mvars_1328_, uint8_t v_x_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_){
_start:
{
switch(v_x_1329_)
{
case 0:
{
lean_object* v___x_1335_; 
v___x_1335_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1328_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_);
lean_dec_ref(v_mvars_1328_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1348_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1338_ = v___x_1335_;
v_isShared_1339_ = v_isSharedCheck_1348_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1335_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1348_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v_fst_1340_; lean_object* v_snd_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1346_; 
v_fst_1340_ = lean_ctor_get(v_a_1336_, 0);
lean_inc(v_fst_1340_);
v_snd_1341_ = lean_ctor_get(v_a_1336_, 1);
lean_inc(v_snd_1341_);
lean_dec(v_a_1336_);
v___x_1342_ = lean_array_to_list(v_fst_1340_);
v___x_1343_ = lean_array_to_list(v_snd_1341_);
v___x_1344_ = l_List_appendTR___redArg(v___x_1342_, v___x_1343_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 0, v___x_1344_);
v___x_1346_ = v___x_1338_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1344_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
else
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
v_a_1349_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1351_ = v___x_1335_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1335_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
case 1:
{
lean_object* v___x_1357_; 
v___x_1357_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1328_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_);
lean_dec_ref(v_mvars_1328_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1367_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1360_ = v___x_1357_;
v_isShared_1361_ = v_isSharedCheck_1367_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1357_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1367_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v_fst_1362_; lean_object* v___x_1363_; lean_object* v___x_1365_; 
v_fst_1362_ = lean_ctor_get(v_a_1358_, 0);
lean_inc(v_fst_1362_);
lean_dec(v_a_1358_);
v___x_1363_ = lean_array_to_list(v_fst_1362_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 0, v___x_1363_);
v___x_1365_ = v___x_1360_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1363_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
v_a_1368_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1357_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1357_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
default: 
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1376_ = lean_array_to_list(v_mvars_1328_);
v___x_1377_ = lean_box(0);
v___x_1378_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals_spec__0(v___x_1376_, v___x_1377_);
v___x_1379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1378_);
return v___x_1379_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals___boxed(lean_object* v_mvars_1380_, lean_object* v_x_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_){
_start:
{
uint8_t v_x_731__boxed_1387_; lean_object* v_res_1388_; 
v_x_731__boxed_1387_ = lean_unbox(v_x_1381_);
v_res_1388_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(v_mvars_1380_, v_x_731__boxed_1387_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_);
lean_dec(v_a_1385_);
lean_dec_ref(v_a_1384_);
lean_dec(v_a_1383_);
lean_dec_ref(v_a_1382_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(uint8_t v_approx_1389_, lean_object* v_a_1390_, lean_object* v_b_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_){
_start:
{
if (v_approx_1389_ == 0)
{
lean_object* v___x_1397_; 
v___x_1397_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1390_, v_b_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
return v___x_1397_;
}
else
{
lean_object* v___x_1398_; uint8_t v_constApprox_1399_; uint8_t v_isDefEqStuckEx_1400_; uint8_t v_unificationHints_1401_; uint8_t v_proofIrrelevance_1402_; uint8_t v_assignSyntheticOpaque_1403_; uint8_t v_offsetCnstrs_1404_; uint8_t v_transparency_1405_; uint8_t v_etaStruct_1406_; uint8_t v_univApprox_1407_; uint8_t v_iota_1408_; uint8_t v_beta_1409_; uint8_t v_proj_1410_; uint8_t v_zeta_1411_; uint8_t v_zetaDelta_1412_; uint8_t v_zetaUnused_1413_; uint8_t v_zetaHave_1414_; uint8_t v_canUnfoldPredicateConfig_1415_; uint8_t v_stringLitToCtor_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1437_; 
v___x_1398_ = l_Lean_Meta_Context_config(v_a_1392_);
v_constApprox_1399_ = lean_ctor_get_uint8(v___x_1398_, 3);
v_isDefEqStuckEx_1400_ = lean_ctor_get_uint8(v___x_1398_, 4);
v_unificationHints_1401_ = lean_ctor_get_uint8(v___x_1398_, 5);
v_proofIrrelevance_1402_ = lean_ctor_get_uint8(v___x_1398_, 6);
v_assignSyntheticOpaque_1403_ = lean_ctor_get_uint8(v___x_1398_, 7);
v_offsetCnstrs_1404_ = lean_ctor_get_uint8(v___x_1398_, 8);
v_transparency_1405_ = lean_ctor_get_uint8(v___x_1398_, 9);
v_etaStruct_1406_ = lean_ctor_get_uint8(v___x_1398_, 10);
v_univApprox_1407_ = lean_ctor_get_uint8(v___x_1398_, 11);
v_iota_1408_ = lean_ctor_get_uint8(v___x_1398_, 12);
v_beta_1409_ = lean_ctor_get_uint8(v___x_1398_, 13);
v_proj_1410_ = lean_ctor_get_uint8(v___x_1398_, 14);
v_zeta_1411_ = lean_ctor_get_uint8(v___x_1398_, 15);
v_zetaDelta_1412_ = lean_ctor_get_uint8(v___x_1398_, 16);
v_zetaUnused_1413_ = lean_ctor_get_uint8(v___x_1398_, 17);
v_zetaHave_1414_ = lean_ctor_get_uint8(v___x_1398_, 18);
v_canUnfoldPredicateConfig_1415_ = lean_ctor_get_uint8(v___x_1398_, 19);
v_stringLitToCtor_1416_ = lean_ctor_get_uint8(v___x_1398_, 20);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1418_ = v___x_1398_;
v_isShared_1419_ = v_isSharedCheck_1437_;
goto v_resetjp_1417_;
}
else
{
lean_dec(v___x_1398_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1437_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 0, 21);
lean_ctor_set_uint8(v_reuseFailAlloc_1436_, 3, v_constApprox_1399_);
lean_ctor_set_uint8(v_reuseFailAlloc_1436_, 4, v_isDefEqStuckEx_1400_);
lean_ctor_set_uint8(v_reuseFailAlloc_1436_, 5, v_unificationHints_1401_);
lean_ctor_set_uint8(v_reuseFailAlloc_1436_, 6, v_proofIrrelevance_1402_);
lean_ctor_set_uint8(v_reuseFailAlloc_1436_, 7, v_assignSyntheticOpaque_1403_);
lean_ctor_set_uint8(v_reuseFailAlloc_1436_, 8, v_offsetCnstrs_1404_);
lean_ctor_set_uint8(v_reuseFailAlloc_1436_, 9, v_transparency_1405_);
lean_ctor_set_uint8(v_reuseFailAlloc_1436_, 10, v_etaStruct_1406_);
lean_ctor_set_uint8(v_reuseFailAlloc_1436_, 11, v_univApprox_1407_);
lean_ctor_set_uint8(v_reuseFailAlloc_1436_, 12, v_iota_1408_);
lean_ctor_set_uint8(v_reuseFailAlloc_1436_, 13, v_beta_1409_);
lean_ctor_set_uint8(v_reuseFailAlloc_1436_, 14, v_proj_1410_);
lean_ctor_set_uint8(v_reuseFailAlloc_1436_, 15, v_zeta_1411_);
lean_ctor_set_uint8(v_reuseFailAlloc_1436_, 16, v_zetaDelta_1412_);
lean_ctor_set_uint8(v_reuseFailAlloc_1436_, 17, v_zetaUnused_1413_);
lean_ctor_set_uint8(v_reuseFailAlloc_1436_, 18, v_zetaHave_1414_);
lean_ctor_set_uint8(v_reuseFailAlloc_1436_, 19, v_canUnfoldPredicateConfig_1415_);
lean_ctor_set_uint8(v_reuseFailAlloc_1436_, 20, v_stringLitToCtor_1416_);
v___x_1421_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
uint8_t v_trackZetaDelta_1422_; lean_object* v_zetaDeltaSet_1423_; lean_object* v_lctx_1424_; lean_object* v_localInstances_1425_; lean_object* v_defEqCtx_x3f_1426_; lean_object* v_synthPendingDepth_1427_; lean_object* v_customCanUnfoldPredicate_x3f_1428_; uint8_t v_univApprox_1429_; uint8_t v_inTypeClassResolution_1430_; uint8_t v_cacheInferType_1431_; uint64_t v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
lean_ctor_set_uint8(v___x_1421_, 0, v_approx_1389_);
lean_ctor_set_uint8(v___x_1421_, 1, v_approx_1389_);
lean_ctor_set_uint8(v___x_1421_, 2, v_approx_1389_);
v_trackZetaDelta_1422_ = lean_ctor_get_uint8(v_a_1392_, sizeof(void*)*7);
v_zetaDeltaSet_1423_ = lean_ctor_get(v_a_1392_, 1);
v_lctx_1424_ = lean_ctor_get(v_a_1392_, 2);
v_localInstances_1425_ = lean_ctor_get(v_a_1392_, 3);
v_defEqCtx_x3f_1426_ = lean_ctor_get(v_a_1392_, 4);
v_synthPendingDepth_1427_ = lean_ctor_get(v_a_1392_, 5);
v_customCanUnfoldPredicate_x3f_1428_ = lean_ctor_get(v_a_1392_, 6);
v_univApprox_1429_ = lean_ctor_get_uint8(v_a_1392_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1430_ = lean_ctor_get_uint8(v_a_1392_, sizeof(void*)*7 + 2);
v_cacheInferType_1431_ = lean_ctor_get_uint8(v_a_1392_, sizeof(void*)*7 + 3);
v___x_1432_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1421_);
v___x_1433_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1433_, 0, v___x_1421_);
lean_ctor_set_uint64(v___x_1433_, sizeof(void*)*1, v___x_1432_);
lean_inc(v_customCanUnfoldPredicate_x3f_1428_);
lean_inc(v_synthPendingDepth_1427_);
lean_inc(v_defEqCtx_x3f_1426_);
lean_inc_ref(v_localInstances_1425_);
lean_inc_ref(v_lctx_1424_);
lean_inc(v_zetaDeltaSet_1423_);
v___x_1434_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1434_, 0, v___x_1433_);
lean_ctor_set(v___x_1434_, 1, v_zetaDeltaSet_1423_);
lean_ctor_set(v___x_1434_, 2, v_lctx_1424_);
lean_ctor_set(v___x_1434_, 3, v_localInstances_1425_);
lean_ctor_set(v___x_1434_, 4, v_defEqCtx_x3f_1426_);
lean_ctor_set(v___x_1434_, 5, v_synthPendingDepth_1427_);
lean_ctor_set(v___x_1434_, 6, v_customCanUnfoldPredicate_x3f_1428_);
lean_ctor_set_uint8(v___x_1434_, sizeof(void*)*7, v_trackZetaDelta_1422_);
lean_ctor_set_uint8(v___x_1434_, sizeof(void*)*7 + 1, v_univApprox_1429_);
lean_ctor_set_uint8(v___x_1434_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1430_);
lean_ctor_set_uint8(v___x_1434_, sizeof(void*)*7 + 3, v_cacheInferType_1431_);
v___x_1435_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1390_, v_b_1391_, v___x_1434_, v_a_1393_, v_a_1394_, v_a_1395_);
lean_dec_ref_known(v___x_1434_, 7);
return v___x_1435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply___boxed(lean_object* v_approx_1438_, lean_object* v_a_1439_, lean_object* v_b_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_){
_start:
{
uint8_t v_approx_boxed_1446_; lean_object* v_res_1447_; 
v_approx_boxed_1446_ = lean_unbox(v_approx_1438_);
v_res_1447_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_approx_boxed_1446_, v_a_1439_, v_b_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_);
lean_dec(v_a_1444_);
lean_dec_ref(v_a_1443_);
lean_dec(v_a_1442_);
lean_dec_ref(v_a_1441_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(lean_object* v_mvarId_1448_, lean_object* v_cfg_1449_, lean_object* v_term_x3f_1450_, lean_object* v_targetType_1451_, lean_object* v_eType_1452_, lean_object* v_rangeNumArgs_1453_, lean_object* v_i_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_){
_start:
{
lean_object* v_conclusionType_x3f_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v_lower_1468_; lean_object* v_upper_1469_; uint8_t v___x_1470_; 
v_lower_1468_ = lean_ctor_get(v_rangeNumArgs_1453_, 0);
v_upper_1469_ = lean_ctor_get(v_rangeNumArgs_1453_, 1);
v___x_1470_ = lean_nat_dec_lt(v_i_1454_, v_upper_1469_);
if (v___x_1470_ == 0)
{
lean_object* v___x_1471_; uint8_t v___x_1472_; 
lean_dec(v_i_1454_);
v___x_1471_ = lean_unsigned_to_nat(0u);
v___x_1472_ = lean_nat_dec_eq(v_lower_1468_, v___x_1471_);
if (v___x_1472_ == 0)
{
lean_object* v___x_1473_; uint8_t v___x_1474_; lean_object* v___x_1475_; 
lean_inc(v_lower_1468_);
v___x_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1473_, 0, v_lower_1468_);
v___x_1474_ = 0;
lean_inc_ref(v_eType_1452_);
v___x_1475_ = l_Lean_Meta_forallMetaTelescopeReducing(v_eType_1452_, v___x_1473_, v___x_1474_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v_snd_1477_; lean_object* v_snd_1478_; lean_object* v___x_1479_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1476_);
lean_dec_ref_known(v___x_1475_, 1);
v_snd_1477_ = lean_ctor_get(v_a_1476_, 1);
lean_inc(v_snd_1477_);
lean_dec(v_a_1476_);
v_snd_1478_ = lean_ctor_get(v_snd_1477_, 1);
lean_inc(v_snd_1478_);
lean_dec(v_snd_1477_);
v___x_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1479_, 0, v_snd_1478_);
v_conclusionType_x3f_1461_ = v___x_1479_;
v___y_1462_ = v_a_1455_;
v___y_1463_ = v_a_1456_;
v___y_1464_ = v_a_1457_;
v___y_1465_ = v_a_1458_;
goto v___jp_1460_;
}
else
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
lean_dec_ref(v_eType_1452_);
lean_dec_ref(v_targetType_1451_);
lean_dec(v_term_x3f_1450_);
lean_dec(v_mvarId_1448_);
v_a_1480_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1475_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1475_);
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
else
{
lean_object* v___x_1488_; 
v___x_1488_ = lean_box(0);
v_conclusionType_x3f_1461_ = v___x_1488_;
v___y_1462_ = v_a_1455_;
v___y_1463_ = v_a_1456_;
v___y_1464_ = v_a_1457_;
v___y_1465_ = v_a_1458_;
goto v___jp_1460_;
}
}
else
{
lean_object* v___x_1489_; 
v___x_1489_ = l_Lean_Meta_saveState___redArg(v_a_1456_, v_a_1458_);
if (lean_obj_tag(v___x_1489_) == 0)
{
lean_object* v_a_1490_; lean_object* v___x_1491_; uint8_t v___x_1492_; lean_object* v___x_1493_; 
v_a_1490_ = lean_ctor_get(v___x_1489_, 0);
lean_inc(v_a_1490_);
lean_dec_ref_known(v___x_1489_, 1);
lean_inc(v_i_1454_);
v___x_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1491_, 0, v_i_1454_);
v___x_1492_ = 0;
lean_inc_ref(v_eType_1452_);
v___x_1493_ = l_Lean_Meta_forallMetaTelescopeReducing(v_eType_1452_, v___x_1491_, v___x_1492_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v_a_1494_; lean_object* v_snd_1495_; lean_object* v_fst_1496_; lean_object* v_fst_1497_; lean_object* v_snd_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1536_; 
v_a_1494_ = lean_ctor_get(v___x_1493_, 0);
lean_inc(v_a_1494_);
lean_dec_ref_known(v___x_1493_, 1);
v_snd_1495_ = lean_ctor_get(v_a_1494_, 1);
lean_inc(v_snd_1495_);
v_fst_1496_ = lean_ctor_get(v_a_1494_, 0);
lean_inc(v_fst_1496_);
lean_dec(v_a_1494_);
v_fst_1497_ = lean_ctor_get(v_snd_1495_, 0);
v_snd_1498_ = lean_ctor_get(v_snd_1495_, 1);
v_isSharedCheck_1536_ = !lean_is_exclusive(v_snd_1495_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1500_ = v_snd_1495_;
v_isShared_1501_ = v_isSharedCheck_1536_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_snd_1498_);
lean_inc(v_fst_1497_);
lean_dec(v_snd_1495_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1536_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
uint8_t v_approx_1502_; lean_object* v___x_1503_; 
v_approx_1502_ = lean_ctor_get_uint8(v_cfg_1449_, 3);
lean_inc_ref(v_targetType_1451_);
v___x_1503_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_approx_1502_, v_snd_1498_, v_targetType_1451_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1527_; 
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1506_ = v___x_1503_;
v_isShared_1507_ = v_isSharedCheck_1527_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1503_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1527_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
uint8_t v___x_1508_; 
v___x_1508_ = lean_unbox(v_a_1504_);
lean_dec(v_a_1504_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1509_; 
lean_del_object(v___x_1506_);
lean_del_object(v___x_1500_);
lean_dec(v_fst_1497_);
lean_dec(v_fst_1496_);
v___x_1509_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1490_, v_a_1456_, v_a_1458_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
lean_dec_ref_known(v___x_1509_, 1);
v___x_1510_ = lean_unsigned_to_nat(1u);
v___x_1511_ = lean_nat_add(v_i_1454_, v___x_1510_);
lean_dec(v_i_1454_);
v_i_1454_ = v___x_1511_;
goto _start;
}
else
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
lean_dec(v_i_1454_);
lean_dec_ref(v_eType_1452_);
lean_dec_ref(v_targetType_1451_);
lean_dec(v_term_x3f_1450_);
lean_dec(v_mvarId_1448_);
v_a_1513_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1515_ = v___x_1509_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1509_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1513_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
else
{
lean_object* v___x_1522_; 
lean_dec(v_a_1490_);
lean_dec(v_i_1454_);
lean_dec_ref(v_eType_1452_);
lean_dec_ref(v_targetType_1451_);
lean_dec(v_term_x3f_1450_);
lean_dec(v_mvarId_1448_);
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 1, v_fst_1497_);
lean_ctor_set(v___x_1500_, 0, v_fst_1496_);
v___x_1522_ = v___x_1500_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_fst_1496_);
lean_ctor_set(v_reuseFailAlloc_1526_, 1, v_fst_1497_);
v___x_1522_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
lean_object* v___x_1524_; 
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 0, v___x_1522_);
v___x_1524_ = v___x_1506_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1522_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
}
else
{
lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1535_; 
lean_del_object(v___x_1500_);
lean_dec(v_fst_1497_);
lean_dec(v_fst_1496_);
lean_dec(v_a_1490_);
lean_dec(v_i_1454_);
lean_dec_ref(v_eType_1452_);
lean_dec_ref(v_targetType_1451_);
lean_dec(v_term_x3f_1450_);
lean_dec(v_mvarId_1448_);
v_a_1528_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1530_ = v___x_1503_;
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1503_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1533_; 
if (v_isShared_1531_ == 0)
{
v___x_1533_ = v___x_1530_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_a_1528_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
}
}
else
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1544_; 
lean_dec(v_a_1490_);
lean_dec(v_i_1454_);
lean_dec_ref(v_eType_1452_);
lean_dec_ref(v_targetType_1451_);
lean_dec(v_term_x3f_1450_);
lean_dec(v_mvarId_1448_);
v_a_1537_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1539_ = v___x_1493_;
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1493_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1542_; 
if (v_isShared_1540_ == 0)
{
v___x_1542_ = v___x_1539_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_a_1537_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
else
{
lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1552_; 
lean_dec(v_i_1454_);
lean_dec_ref(v_eType_1452_);
lean_dec_ref(v_targetType_1451_);
lean_dec(v_term_x3f_1450_);
lean_dec(v_mvarId_1448_);
v_a_1545_ = lean_ctor_get(v___x_1489_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1489_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1547_ = v___x_1489_;
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1489_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1550_; 
if (v_isShared_1548_ == 0)
{
v___x_1550_ = v___x_1547_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_a_1545_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
}
v___jp_1460_:
{
uint8_t v_approx_1466_; lean_object* v___x_1467_; 
v_approx_1466_ = lean_ctor_get_uint8(v_cfg_1449_, 3);
v___x_1467_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_1448_, v_eType_1452_, v_conclusionType_x3f_1461_, v_targetType_1451_, v_term_x3f_1450_, v_approx_1466_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
return v___x_1467_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go___boxed(lean_object* v_mvarId_1553_, lean_object* v_cfg_1554_, lean_object* v_term_x3f_1555_, lean_object* v_targetType_1556_, lean_object* v_eType_1557_, lean_object* v_rangeNumArgs_1558_, lean_object* v_i_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(v_mvarId_1553_, v_cfg_1554_, v_term_x3f_1555_, v_targetType_1556_, v_eType_1557_, v_rangeNumArgs_1558_, v_i_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_);
lean_dec(v_a_1563_);
lean_dec_ref(v_a_1562_);
lean_dec(v_a_1561_);
lean_dec_ref(v_a_1560_);
lean_dec_ref(v_rangeNumArgs_1558_);
lean_dec_ref(v_cfg_1554_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go_match__1_splitter___redArg(lean_object* v_x_1566_, lean_object* v_h__1_1567_){
_start:
{
lean_object* v_snd_1568_; lean_object* v_fst_1569_; lean_object* v_fst_1570_; lean_object* v_snd_1571_; lean_object* v___x_1572_; 
v_snd_1568_ = lean_ctor_get(v_x_1566_, 1);
lean_inc(v_snd_1568_);
v_fst_1569_ = lean_ctor_get(v_x_1566_, 0);
lean_inc(v_fst_1569_);
lean_dec_ref(v_x_1566_);
v_fst_1570_ = lean_ctor_get(v_snd_1568_, 0);
lean_inc(v_fst_1570_);
v_snd_1571_ = lean_ctor_get(v_snd_1568_, 1);
lean_inc(v_snd_1571_);
lean_dec(v_snd_1568_);
v___x_1572_ = lean_apply_3(v_h__1_1567_, v_fst_1569_, v_fst_1570_, v_snd_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go_match__1_splitter(lean_object* v_motive_1573_, lean_object* v_x_1574_, lean_object* v_h__1_1575_){
_start:
{
lean_object* v_snd_1576_; lean_object* v_fst_1577_; lean_object* v_fst_1578_; lean_object* v_snd_1579_; lean_object* v___x_1580_; 
v_snd_1576_ = lean_ctor_get(v_x_1574_, 1);
lean_inc(v_snd_1576_);
v_fst_1577_ = lean_ctor_get(v_x_1574_, 0);
lean_inc(v_fst_1577_);
lean_dec_ref(v_x_1574_);
v_fst_1578_ = lean_ctor_get(v_snd_1576_, 0);
lean_inc(v_fst_1578_);
v_snd_1579_ = lean_ctor_get(v_snd_1576_, 1);
lean_inc(v_snd_1579_);
lean_dec(v_snd_1576_);
v___x_1580_ = lean_apply_3(v_h__1_1575_, v_fst_1577_, v_fst_1578_, v_snd_1579_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(lean_object* v_e_1581_, lean_object* v___y_1582_){
_start:
{
uint8_t v___x_1584_; 
v___x_1584_ = l_Lean_Expr_hasMVar(v_e_1581_);
if (v___x_1584_ == 0)
{
lean_object* v___x_1585_; 
v___x_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1585_, 0, v_e_1581_);
return v___x_1585_;
}
else
{
lean_object* v___x_1586_; lean_object* v_mctx_1587_; lean_object* v___x_1588_; lean_object* v_fst_1589_; lean_object* v_snd_1590_; lean_object* v___x_1591_; lean_object* v_cache_1592_; lean_object* v_zetaDeltaFVarIds_1593_; lean_object* v_postponed_1594_; lean_object* v_diag_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1604_; 
v___x_1586_ = lean_st_ref_get(v___y_1582_);
v_mctx_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc_ref(v_mctx_1587_);
lean_dec(v___x_1586_);
v___x_1588_ = l_Lean_instantiateMVarsCore(v_mctx_1587_, v_e_1581_);
v_fst_1589_ = lean_ctor_get(v___x_1588_, 0);
lean_inc(v_fst_1589_);
v_snd_1590_ = lean_ctor_get(v___x_1588_, 1);
lean_inc(v_snd_1590_);
lean_dec_ref(v___x_1588_);
v___x_1591_ = lean_st_ref_take(v___y_1582_);
v_cache_1592_ = lean_ctor_get(v___x_1591_, 1);
v_zetaDeltaFVarIds_1593_ = lean_ctor_get(v___x_1591_, 2);
v_postponed_1594_ = lean_ctor_get(v___x_1591_, 3);
v_diag_1595_ = lean_ctor_get(v___x_1591_, 4);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1604_ == 0)
{
lean_object* v_unused_1605_; 
v_unused_1605_ = lean_ctor_get(v___x_1591_, 0);
lean_dec(v_unused_1605_);
v___x_1597_ = v___x_1591_;
v_isShared_1598_ = v_isSharedCheck_1604_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_diag_1595_);
lean_inc(v_postponed_1594_);
lean_inc(v_zetaDeltaFVarIds_1593_);
lean_inc(v_cache_1592_);
lean_dec(v___x_1591_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1604_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 0, v_snd_1590_);
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_snd_1590_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v_cache_1592_);
lean_ctor_set(v_reuseFailAlloc_1603_, 2, v_zetaDeltaFVarIds_1593_);
lean_ctor_set(v_reuseFailAlloc_1603_, 3, v_postponed_1594_);
lean_ctor_set(v_reuseFailAlloc_1603_, 4, v_diag_1595_);
v___x_1600_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1601_ = lean_st_ref_put(v___y_1582_, v___x_1600_);
v___x_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1602_, 0, v_fst_1589_);
return v___x_1602_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg___boxed(lean_object* v_e_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_1606_, v___y_1607_);
lean_dec(v___y_1607_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0(lean_object* v_e_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v___x_1616_; 
v___x_1616_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_1610_, v___y_1612_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___boxed(lean_object* v_e_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0(v_e_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(lean_object* v_mvarId_1624_, lean_object* v_x_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1624_, v_x_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1631_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1631_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
else
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1647_; 
v_a_1640_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1642_ = v___x_1631_;
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1631_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1645_; 
if (v_isShared_1643_ == 0)
{
v___x_1645_ = v___x_1642_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_a_1640_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg___boxed(lean_object* v_mvarId_1648_, lean_object* v_x_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_1648_, v_x_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6(lean_object* v_00_u03b1_1656_, lean_object* v_mvarId_1657_, lean_object* v_x_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_1657_, v_x_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___boxed(lean_object* v_00_u03b1_1665_, lean_object* v_mvarId_1666_, lean_object* v_x_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6(v_00_u03b1_1665_, v_mvarId_1666_, v_x_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(lean_object* v_as_1674_, size_t v_i_1675_, size_t v_stop_1676_, lean_object* v_b_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v_a_1681_; uint8_t v___x_1685_; 
v___x_1685_ = lean_usize_dec_eq(v_i_1675_, v_stop_1676_);
if (v___x_1685_ == 0)
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1686_ = lean_array_uget_borrowed(v_as_1674_, v_i_1675_);
v___x_1687_ = l_Lean_Expr_mvarId_x21(v___x_1686_);
v___x_1688_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_1687_, v___y_1678_);
lean_dec(v___x_1687_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_object* v_a_1689_; uint8_t v___x_1690_; 
v_a_1689_ = lean_ctor_get(v___x_1688_, 0);
lean_inc(v_a_1689_);
lean_dec_ref_known(v___x_1688_, 1);
v___x_1690_ = lean_unbox(v_a_1689_);
lean_dec(v_a_1689_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; 
lean_inc(v___x_1686_);
v___x_1691_ = lean_array_push(v_b_1677_, v___x_1686_);
v_a_1681_ = v___x_1691_;
goto v___jp_1680_;
}
else
{
v_a_1681_ = v_b_1677_;
goto v___jp_1680_;
}
}
else
{
lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1699_; 
lean_dec_ref(v_b_1677_);
v_a_1692_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1694_ = v___x_1688_;
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v___x_1688_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1697_; 
if (v_isShared_1695_ == 0)
{
v___x_1697_ = v___x_1694_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_a_1692_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
}
else
{
lean_object* v___x_1700_; 
v___x_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1700_, 0, v_b_1677_);
return v___x_1700_;
}
v___jp_1680_:
{
size_t v___x_1682_; size_t v___x_1683_; 
v___x_1682_ = ((size_t)1ULL);
v___x_1683_ = lean_usize_add(v_i_1675_, v___x_1682_);
v_i_1675_ = v___x_1683_;
v_b_1677_ = v_a_1681_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg___boxed(lean_object* v_as_1701_, lean_object* v_i_1702_, lean_object* v_stop_1703_, lean_object* v_b_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
size_t v_i_boxed_1707_; size_t v_stop_boxed_1708_; lean_object* v_res_1709_; 
v_i_boxed_1707_ = lean_unbox_usize(v_i_1702_);
lean_dec(v_i_1702_);
v_stop_boxed_1708_ = lean_unbox_usize(v_stop_1703_);
lean_dec(v_stop_1703_);
v_res_1709_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_as_1701_, v_i_boxed_1707_, v_stop_boxed_1708_, v_b_1704_, v___y_1705_);
lean_dec(v___y_1705_);
lean_dec_ref(v_as_1701_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_apply_spec__3(lean_object* v_as_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
if (lean_obj_tag(v_as_1710_) == 0)
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1716_ = lean_box(0);
v___x_1717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1716_);
return v___x_1717_;
}
else
{
lean_object* v_head_1718_; lean_object* v_tail_1719_; lean_object* v___x_1720_; 
v_head_1718_ = lean_ctor_get(v_as_1710_, 0);
lean_inc(v_head_1718_);
v_tail_1719_ = lean_ctor_get(v_as_1710_, 1);
lean_inc(v_tail_1719_);
lean_dec_ref_known(v_as_1710_, 2);
v___x_1720_ = l_Lean_MVarId_headBetaType(v_head_1718_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_dec_ref_known(v___x_1720_, 1);
v_as_1710_ = v_tail_1719_;
goto _start;
}
else
{
lean_dec(v_tail_1719_);
return v___x_1720_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_apply_spec__3___boxed(lean_object* v_as_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l_List_forM___at___00Lean_MVarId_apply_spec__3(v_as_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(lean_object* v_x_1729_, lean_object* v_x_1730_, lean_object* v_x_1731_, lean_object* v_x_1732_){
_start:
{
lean_object* v_ks_1733_; lean_object* v_vs_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1758_; 
v_ks_1733_ = lean_ctor_get(v_x_1729_, 0);
v_vs_1734_ = lean_ctor_get(v_x_1729_, 1);
v_isSharedCheck_1758_ = !lean_is_exclusive(v_x_1729_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1736_ = v_x_1729_;
v_isShared_1737_ = v_isSharedCheck_1758_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_vs_1734_);
lean_inc(v_ks_1733_);
lean_dec(v_x_1729_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1758_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1738_; uint8_t v___x_1739_; 
v___x_1738_ = lean_array_get_size(v_ks_1733_);
v___x_1739_ = lean_nat_dec_lt(v_x_1730_, v___x_1738_);
if (v___x_1739_ == 0)
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1743_; 
lean_dec(v_x_1730_);
v___x_1740_ = lean_array_push(v_ks_1733_, v_x_1731_);
v___x_1741_ = lean_array_push(v_vs_1734_, v_x_1732_);
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 1, v___x_1741_);
lean_ctor_set(v___x_1736_, 0, v___x_1740_);
v___x_1743_ = v___x_1736_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1740_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v___x_1741_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
else
{
lean_object* v_k_x27_1745_; uint8_t v___x_1746_; 
v_k_x27_1745_ = lean_array_fget_borrowed(v_ks_1733_, v_x_1730_);
v___x_1746_ = l_Lean_instBEqMVarId_beq(v_x_1731_, v_k_x27_1745_);
if (v___x_1746_ == 0)
{
lean_object* v___x_1748_; 
if (v_isShared_1737_ == 0)
{
v___x_1748_ = v___x_1736_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_ks_1733_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v_vs_1734_);
v___x_1748_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1749_ = lean_unsigned_to_nat(1u);
v___x_1750_ = lean_nat_add(v_x_1730_, v___x_1749_);
lean_dec(v_x_1730_);
v_x_1729_ = v___x_1748_;
v_x_1730_ = v___x_1750_;
goto _start;
}
}
else
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1756_; 
v___x_1753_ = lean_array_fset(v_ks_1733_, v_x_1730_, v_x_1731_);
v___x_1754_ = lean_array_fset(v_vs_1734_, v_x_1730_, v_x_1732_);
lean_dec(v_x_1730_);
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 1, v___x_1754_);
lean_ctor_set(v___x_1736_, 0, v___x_1753_);
v___x_1756_ = v___x_1736_;
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(lean_object* v_n_1759_, lean_object* v_k_1760_, lean_object* v_v_1761_){
_start:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1762_ = lean_unsigned_to_nat(0u);
v___x_1763_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(v_n_1759_, v___x_1762_, v_k_1760_, v_v_1761_);
return v___x_1763_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1764_; 
v___x_1764_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(lean_object* v_x_1765_, size_t v_x_1766_, size_t v_x_1767_, lean_object* v_x_1768_, lean_object* v_x_1769_){
_start:
{
if (lean_obj_tag(v_x_1765_) == 0)
{
lean_object* v_es_1770_; size_t v___x_1771_; size_t v___x_1772_; lean_object* v_j_1773_; lean_object* v___x_1774_; uint8_t v___x_1775_; 
v_es_1770_ = lean_ctor_get(v_x_1765_, 0);
v___x_1771_ = ((size_t)31ULL);
v___x_1772_ = lean_usize_land(v_x_1766_, v___x_1771_);
v_j_1773_ = lean_usize_to_nat(v___x_1772_);
v___x_1774_ = lean_array_get_size(v_es_1770_);
v___x_1775_ = lean_nat_dec_lt(v_j_1773_, v___x_1774_);
if (v___x_1775_ == 0)
{
lean_dec(v_j_1773_);
lean_dec(v_x_1769_);
lean_dec(v_x_1768_);
return v_x_1765_;
}
else
{
lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1814_; 
lean_inc_ref(v_es_1770_);
v_isSharedCheck_1814_ = !lean_is_exclusive(v_x_1765_);
if (v_isSharedCheck_1814_ == 0)
{
lean_object* v_unused_1815_; 
v_unused_1815_ = lean_ctor_get(v_x_1765_, 0);
lean_dec(v_unused_1815_);
v___x_1777_ = v_x_1765_;
v_isShared_1778_ = v_isSharedCheck_1814_;
goto v_resetjp_1776_;
}
else
{
lean_dec(v_x_1765_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1814_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v_v_1779_; lean_object* v___x_1780_; lean_object* v_xs_x27_1781_; lean_object* v___y_1783_; 
v_v_1779_ = lean_array_fget(v_es_1770_, v_j_1773_);
v___x_1780_ = lean_box(0);
v_xs_x27_1781_ = lean_array_fset(v_es_1770_, v_j_1773_, v___x_1780_);
switch(lean_obj_tag(v_v_1779_))
{
case 0:
{
lean_object* v_key_1788_; lean_object* v_val_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1799_; 
v_key_1788_ = lean_ctor_get(v_v_1779_, 0);
v_val_1789_ = lean_ctor_get(v_v_1779_, 1);
v_isSharedCheck_1799_ = !lean_is_exclusive(v_v_1779_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1791_ = v_v_1779_;
v_isShared_1792_ = v_isSharedCheck_1799_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_val_1789_);
lean_inc(v_key_1788_);
lean_dec(v_v_1779_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1799_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
uint8_t v___x_1793_; 
v___x_1793_ = l_Lean_instBEqMVarId_beq(v_x_1768_, v_key_1788_);
if (v___x_1793_ == 0)
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
lean_del_object(v___x_1791_);
v___x_1794_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1788_, v_val_1789_, v_x_1768_, v_x_1769_);
v___x_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1794_);
v___y_1783_ = v___x_1795_;
goto v___jp_1782_;
}
else
{
lean_object* v___x_1797_; 
lean_dec(v_val_1789_);
lean_dec(v_key_1788_);
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 1, v_x_1769_);
lean_ctor_set(v___x_1791_, 0, v_x_1768_);
v___x_1797_ = v___x_1791_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_x_1768_);
lean_ctor_set(v_reuseFailAlloc_1798_, 1, v_x_1769_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
v___y_1783_ = v___x_1797_;
goto v___jp_1782_;
}
}
}
}
case 1:
{
lean_object* v_node_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1812_; 
v_node_1800_ = lean_ctor_get(v_v_1779_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v_v_1779_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1802_ = v_v_1779_;
v_isShared_1803_ = v_isSharedCheck_1812_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_node_1800_);
lean_dec(v_v_1779_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1812_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
size_t v___x_1804_; size_t v___x_1805_; size_t v___x_1806_; size_t v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1810_; 
v___x_1804_ = ((size_t)5ULL);
v___x_1805_ = lean_usize_shift_right(v_x_1766_, v___x_1804_);
v___x_1806_ = ((size_t)1ULL);
v___x_1807_ = lean_usize_add(v_x_1767_, v___x_1806_);
v___x_1808_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_node_1800_, v___x_1805_, v___x_1807_, v_x_1768_, v_x_1769_);
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 0, v___x_1808_);
v___x_1810_ = v___x_1802_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v___x_1808_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
v___y_1783_ = v___x_1810_;
goto v___jp_1782_;
}
}
}
default: 
{
lean_object* v___x_1813_; 
v___x_1813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1813_, 0, v_x_1768_);
lean_ctor_set(v___x_1813_, 1, v_x_1769_);
v___y_1783_ = v___x_1813_;
goto v___jp_1782_;
}
}
v___jp_1782_:
{
lean_object* v___x_1784_; lean_object* v___x_1786_; 
v___x_1784_ = lean_array_fset(v_xs_x27_1781_, v_j_1773_, v___y_1783_);
lean_dec(v_j_1773_);
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 0, v___x_1784_);
v___x_1786_ = v___x_1777_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1784_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
}
else
{
lean_object* v_ks_1816_; lean_object* v_vs_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1835_; 
v_ks_1816_ = lean_ctor_get(v_x_1765_, 0);
v_vs_1817_ = lean_ctor_get(v_x_1765_, 1);
v_isSharedCheck_1835_ = !lean_is_exclusive(v_x_1765_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1819_ = v_x_1765_;
v_isShared_1820_ = v_isSharedCheck_1835_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_vs_1817_);
lean_inc(v_ks_1816_);
lean_dec(v_x_1765_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1835_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1822_; 
if (v_isShared_1820_ == 0)
{
v___x_1822_ = v___x_1819_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_ks_1816_);
lean_ctor_set(v_reuseFailAlloc_1834_, 1, v_vs_1817_);
v___x_1822_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
lean_object* v_newNode_1823_; size_t v___x_1824_; uint8_t v___x_1825_; 
v_newNode_1823_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(v___x_1822_, v_x_1768_, v_x_1769_);
v___x_1824_ = ((size_t)7ULL);
v___x_1825_ = lean_usize_dec_le(v___x_1824_, v_x_1767_);
if (v___x_1825_ == 0)
{
lean_object* v___x_1826_; lean_object* v___x_1827_; uint8_t v___x_1828_; 
v___x_1826_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1823_);
v___x_1827_ = lean_unsigned_to_nat(4u);
v___x_1828_ = lean_nat_dec_lt(v___x_1826_, v___x_1827_);
lean_dec(v___x_1826_);
if (v___x_1828_ == 0)
{
lean_object* v_ks_1829_; lean_object* v_vs_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
v_ks_1829_ = lean_ctor_get(v_newNode_1823_, 0);
lean_inc_ref(v_ks_1829_);
v_vs_1830_ = lean_ctor_get(v_newNode_1823_, 1);
lean_inc_ref(v_vs_1830_);
lean_dec_ref(v_newNode_1823_);
v___x_1831_ = lean_unsigned_to_nat(0u);
v___x_1832_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_1833_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_x_1767_, v_ks_1829_, v_vs_1830_, v___x_1831_, v___x_1832_);
lean_dec_ref(v_vs_1830_);
lean_dec_ref(v_ks_1829_);
return v___x_1833_;
}
else
{
return v_newNode_1823_;
}
}
else
{
return v_newNode_1823_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(size_t v_depth_1836_, lean_object* v_keys_1837_, lean_object* v_vals_1838_, lean_object* v_i_1839_, lean_object* v_entries_1840_){
_start:
{
lean_object* v___x_1841_; uint8_t v___x_1842_; 
v___x_1841_ = lean_array_get_size(v_keys_1837_);
v___x_1842_ = lean_nat_dec_lt(v_i_1839_, v___x_1841_);
if (v___x_1842_ == 0)
{
lean_dec(v_i_1839_);
return v_entries_1840_;
}
else
{
lean_object* v_k_1843_; lean_object* v_v_1844_; uint64_t v___x_1845_; size_t v_h_1846_; size_t v___x_1847_; lean_object* v___x_1848_; size_t v___x_1849_; size_t v___x_1850_; size_t v___x_1851_; size_t v_h_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v_k_1843_ = lean_array_fget_borrowed(v_keys_1837_, v_i_1839_);
v_v_1844_ = lean_array_fget_borrowed(v_vals_1838_, v_i_1839_);
v___x_1845_ = l_Lean_instHashableMVarId_hash(v_k_1843_);
v_h_1846_ = lean_uint64_to_usize(v___x_1845_);
v___x_1847_ = ((size_t)5ULL);
v___x_1848_ = lean_unsigned_to_nat(1u);
v___x_1849_ = ((size_t)1ULL);
v___x_1850_ = lean_usize_sub(v_depth_1836_, v___x_1849_);
v___x_1851_ = lean_usize_mul(v___x_1847_, v___x_1850_);
v_h_1852_ = lean_usize_shift_right(v_h_1846_, v___x_1851_);
v___x_1853_ = lean_nat_add(v_i_1839_, v___x_1848_);
lean_dec(v_i_1839_);
lean_inc(v_v_1844_);
lean_inc(v_k_1843_);
v___x_1854_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_entries_1840_, v_h_1852_, v_depth_1836_, v_k_1843_, v_v_1844_);
v_i_1839_ = v___x_1853_;
v_entries_1840_ = v___x_1854_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg___boxed(lean_object* v_depth_1856_, lean_object* v_keys_1857_, lean_object* v_vals_1858_, lean_object* v_i_1859_, lean_object* v_entries_1860_){
_start:
{
size_t v_depth_boxed_1861_; lean_object* v_res_1862_; 
v_depth_boxed_1861_ = lean_unbox_usize(v_depth_1856_);
lean_dec(v_depth_1856_);
v_res_1862_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_depth_boxed_1861_, v_keys_1857_, v_vals_1858_, v_i_1859_, v_entries_1860_);
lean_dec_ref(v_vals_1858_);
lean_dec_ref(v_keys_1857_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_1863_, lean_object* v_x_1864_, lean_object* v_x_1865_, lean_object* v_x_1866_, lean_object* v_x_1867_){
_start:
{
size_t v_x_7048__boxed_1868_; size_t v_x_7049__boxed_1869_; lean_object* v_res_1870_; 
v_x_7048__boxed_1868_ = lean_unbox_usize(v_x_1864_);
lean_dec(v_x_1864_);
v_x_7049__boxed_1869_ = lean_unbox_usize(v_x_1865_);
lean_dec(v_x_1865_);
v_res_1870_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_1863_, v_x_7048__boxed_1868_, v_x_7049__boxed_1869_, v_x_1866_, v_x_1867_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(lean_object* v_x_1871_, lean_object* v_x_1872_, lean_object* v_x_1873_){
_start:
{
uint64_t v___x_1874_; size_t v___x_1875_; size_t v___x_1876_; lean_object* v___x_1877_; 
v___x_1874_ = l_Lean_instHashableMVarId_hash(v_x_1872_);
v___x_1875_ = lean_uint64_to_usize(v___x_1874_);
v___x_1876_ = ((size_t)1ULL);
v___x_1877_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_1871_, v___x_1875_, v___x_1876_, v_x_1872_, v_x_1873_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(lean_object* v_mvarId_1878_, lean_object* v_val_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v___x_1882_; lean_object* v_mctx_1883_; lean_object* v_cache_1884_; lean_object* v_zetaDeltaFVarIds_1885_; lean_object* v_postponed_1886_; lean_object* v_diag_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1916_; 
v___x_1882_ = lean_st_ref_take(v___y_1880_);
v_mctx_1883_ = lean_ctor_get(v___x_1882_, 0);
v_cache_1884_ = lean_ctor_get(v___x_1882_, 1);
v_zetaDeltaFVarIds_1885_ = lean_ctor_get(v___x_1882_, 2);
v_postponed_1886_ = lean_ctor_get(v___x_1882_, 3);
v_diag_1887_ = lean_ctor_get(v___x_1882_, 4);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1889_ = v___x_1882_;
v_isShared_1890_ = v_isSharedCheck_1916_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_diag_1887_);
lean_inc(v_postponed_1886_);
lean_inc(v_zetaDeltaFVarIds_1885_);
lean_inc(v_cache_1884_);
lean_inc(v_mctx_1883_);
lean_dec(v___x_1882_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1916_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v_depth_1891_; lean_object* v_levelAssignDepth_1892_; lean_object* v_lmvarCounter_1893_; lean_object* v_mvarCounter_1894_; lean_object* v_lDecls_1895_; lean_object* v_decls_1896_; lean_object* v_userNames_1897_; lean_object* v_lAssignment_1898_; lean_object* v_eAssignment_1899_; lean_object* v_dAssignment_1900_; lean_object* v_instanceTypedMVars_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1915_; 
v_depth_1891_ = lean_ctor_get(v_mctx_1883_, 0);
v_levelAssignDepth_1892_ = lean_ctor_get(v_mctx_1883_, 1);
v_lmvarCounter_1893_ = lean_ctor_get(v_mctx_1883_, 2);
v_mvarCounter_1894_ = lean_ctor_get(v_mctx_1883_, 3);
v_lDecls_1895_ = lean_ctor_get(v_mctx_1883_, 4);
v_decls_1896_ = lean_ctor_get(v_mctx_1883_, 5);
v_userNames_1897_ = lean_ctor_get(v_mctx_1883_, 6);
v_lAssignment_1898_ = lean_ctor_get(v_mctx_1883_, 7);
v_eAssignment_1899_ = lean_ctor_get(v_mctx_1883_, 8);
v_dAssignment_1900_ = lean_ctor_get(v_mctx_1883_, 9);
v_instanceTypedMVars_1901_ = lean_ctor_get(v_mctx_1883_, 10);
v_isSharedCheck_1915_ = !lean_is_exclusive(v_mctx_1883_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1903_ = v_mctx_1883_;
v_isShared_1904_ = v_isSharedCheck_1915_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_instanceTypedMVars_1901_);
lean_inc(v_dAssignment_1900_);
lean_inc(v_eAssignment_1899_);
lean_inc(v_lAssignment_1898_);
lean_inc(v_userNames_1897_);
lean_inc(v_decls_1896_);
lean_inc(v_lDecls_1895_);
lean_inc(v_mvarCounter_1894_);
lean_inc(v_lmvarCounter_1893_);
lean_inc(v_levelAssignDepth_1892_);
lean_inc(v_depth_1891_);
lean_dec(v_mctx_1883_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1915_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1908_; 
v___x_1905_ = lean_box(0);
v___x_1906_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(v_eAssignment_1899_, v_mvarId_1878_, v_val_1879_);
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 8, v___x_1906_);
v___x_1908_ = v___x_1903_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_depth_1891_);
lean_ctor_set(v_reuseFailAlloc_1914_, 1, v_levelAssignDepth_1892_);
lean_ctor_set(v_reuseFailAlloc_1914_, 2, v_lmvarCounter_1893_);
lean_ctor_set(v_reuseFailAlloc_1914_, 3, v_mvarCounter_1894_);
lean_ctor_set(v_reuseFailAlloc_1914_, 4, v_lDecls_1895_);
lean_ctor_set(v_reuseFailAlloc_1914_, 5, v_decls_1896_);
lean_ctor_set(v_reuseFailAlloc_1914_, 6, v_userNames_1897_);
lean_ctor_set(v_reuseFailAlloc_1914_, 7, v_lAssignment_1898_);
lean_ctor_set(v_reuseFailAlloc_1914_, 8, v___x_1906_);
lean_ctor_set(v_reuseFailAlloc_1914_, 9, v_dAssignment_1900_);
lean_ctor_set(v_reuseFailAlloc_1914_, 10, v_instanceTypedMVars_1901_);
v___x_1908_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
lean_object* v___x_1910_; 
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 0, v___x_1908_);
v___x_1910_ = v___x_1889_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v___x_1908_);
lean_ctor_set(v_reuseFailAlloc_1913_, 1, v_cache_1884_);
lean_ctor_set(v_reuseFailAlloc_1913_, 2, v_zetaDeltaFVarIds_1885_);
lean_ctor_set(v_reuseFailAlloc_1913_, 3, v_postponed_1886_);
lean_ctor_set(v_reuseFailAlloc_1913_, 4, v_diag_1887_);
v___x_1910_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1911_ = lean_st_ref_put(v___y_1880_, v___x_1910_);
v___x_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1905_);
return v___x_1912_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg___boxed(lean_object* v_mvarId_1917_, lean_object* v_val_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_1917_, v_val_1918_, v___y_1919_);
lean_dec(v___y_1919_);
return v_res_1921_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_MVarId_apply_spec__2(lean_object* v_a_1922_, lean_object* v_x_1923_){
_start:
{
if (lean_obj_tag(v_x_1923_) == 0)
{
uint8_t v___x_1924_; 
v___x_1924_ = 0;
return v___x_1924_;
}
else
{
lean_object* v_head_1925_; lean_object* v_tail_1926_; uint8_t v___x_1927_; 
v_head_1925_ = lean_ctor_get(v_x_1923_, 0);
v_tail_1926_ = lean_ctor_get(v_x_1923_, 1);
v___x_1927_ = l_Lean_instBEqMVarId_beq(v_a_1922_, v_head_1925_);
if (v___x_1927_ == 0)
{
v_x_1923_ = v_tail_1926_;
goto _start;
}
else
{
return v___x_1927_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_MVarId_apply_spec__2___boxed(lean_object* v_a_1929_, lean_object* v_x_1930_){
_start:
{
uint8_t v_res_1931_; lean_object* v_r_1932_; 
v_res_1931_ = l_List_elem___at___00Lean_MVarId_apply_spec__2(v_a_1929_, v_x_1930_);
lean_dec(v_x_1930_);
lean_dec(v_a_1929_);
v_r_1932_ = lean_box(v_res_1931_);
return v_r_1932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(lean_object* v_a_1933_, lean_object* v_as_1934_, size_t v_i_1935_, size_t v_stop_1936_, lean_object* v_b_1937_){
_start:
{
lean_object* v___y_1939_; uint8_t v___x_1943_; 
v___x_1943_ = lean_usize_dec_eq(v_i_1935_, v_stop_1936_);
if (v___x_1943_ == 0)
{
lean_object* v___x_1944_; uint8_t v___x_1945_; 
v___x_1944_ = lean_array_uget_borrowed(v_as_1934_, v_i_1935_);
v___x_1945_ = l_List_elem___at___00Lean_MVarId_apply_spec__2(v___x_1944_, v_a_1933_);
if (v___x_1945_ == 0)
{
lean_object* v___x_1946_; 
lean_inc(v___x_1944_);
v___x_1946_ = lean_array_push(v_b_1937_, v___x_1944_);
v___y_1939_ = v___x_1946_;
goto v___jp_1938_;
}
else
{
v___y_1939_ = v_b_1937_;
goto v___jp_1938_;
}
}
else
{
return v_b_1937_;
}
v___jp_1938_:
{
size_t v___x_1940_; size_t v___x_1941_; 
v___x_1940_ = ((size_t)1ULL);
v___x_1941_ = lean_usize_add(v_i_1935_, v___x_1940_);
v_i_1935_ = v___x_1941_;
v_b_1937_ = v___y_1939_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4___boxed(lean_object* v_a_1947_, lean_object* v_as_1948_, lean_object* v_i_1949_, lean_object* v_stop_1950_, lean_object* v_b_1951_){
_start:
{
size_t v_i_boxed_1952_; size_t v_stop_boxed_1953_; lean_object* v_res_1954_; 
v_i_boxed_1952_ = lean_unbox_usize(v_i_1949_);
lean_dec(v_i_1949_);
v_stop_boxed_1953_ = lean_unbox_usize(v_stop_1950_);
lean_dec(v_stop_1950_);
v_res_1954_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_1947_, v_as_1948_, v_i_boxed_1952_, v_stop_boxed_1953_, v_b_1951_);
lean_dec_ref(v_as_1948_);
lean_dec(v_a_1947_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lam__0(lean_object* v_mvarId_1955_, lean_object* v___x_1956_, lean_object* v_e_1957_, lean_object* v_cfg_1958_, lean_object* v_term_x3f_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1968_; lean_object* v___y_1969_; lean_object* v___y_1970_; lean_object* v___y_1971_; lean_object* v___y_1992_; uint8_t v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v_a_2000_; lean_object* v___x_2028_; 
lean_inc(v___x_1956_);
lean_inc(v_mvarId_1955_);
v___x_2028_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1955_, v___x_1956_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
if (lean_obj_tag(v___x_2028_) == 0)
{
lean_object* v___x_2029_; 
lean_dec_ref_known(v___x_2028_, 1);
lean_inc(v_mvarId_1955_);
v___x_2029_ = l_Lean_MVarId_getType(v_mvarId_1955_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v_a_2030_; lean_object* v___x_2031_; 
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
lean_inc(v_a_2030_);
lean_dec_ref_known(v___x_2029_, 1);
lean_inc(v___y_1963_);
lean_inc_ref(v___y_1962_);
lean_inc(v___y_1961_);
lean_inc_ref(v___y_1960_);
lean_inc_ref(v_e_1957_);
v___x_2031_ = lean_infer_type(v_e_1957_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v_a_2032_; lean_object* v_rangeNumArgs_2034_; lean_object* v_lower_2035_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v___x_2084_; 
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
lean_inc_n(v_a_2032_, 2);
lean_dec_ref_known(v___x_2031_, 1);
v___x_2084_ = l_Lean_Meta_getExpectedNumArgsAux(v_a_2032_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v_a_2085_; lean_object* v_snd_2086_; uint8_t v___x_2087_; 
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
lean_inc(v_a_2085_);
lean_dec_ref_known(v___x_2084_, 1);
v_snd_2086_ = lean_ctor_get(v_a_2085_, 1);
v___x_2087_ = lean_unbox(v_snd_2086_);
if (v___x_2087_ == 0)
{
lean_object* v_fst_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2108_; 
v_fst_2088_ = lean_ctor_get(v_a_2085_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v_a_2085_);
if (v_isSharedCheck_2108_ == 0)
{
lean_object* v_unused_2109_; 
v_unused_2109_ = lean_ctor_get(v_a_2085_, 1);
lean_dec(v_unused_2109_);
v___x_2090_ = v_a_2085_;
v_isShared_2091_ = v_isSharedCheck_2108_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_fst_2088_);
lean_dec(v_a_2085_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2108_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2092_; 
lean_inc(v_a_2030_);
v___x_2092_ = l_Lean_Meta_getExpectedNumArgs(v_a_2030_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v_a_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2098_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
lean_inc(v_a_2093_);
lean_dec_ref_known(v___x_2092_, 1);
v___x_2094_ = lean_nat_sub(v_fst_2088_, v_a_2093_);
lean_dec(v_a_2093_);
v___x_2095_ = lean_unsigned_to_nat(1u);
v___x_2096_ = lean_nat_add(v_fst_2088_, v___x_2095_);
lean_dec(v_fst_2088_);
lean_inc(v___x_2094_);
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 1, v___x_2096_);
lean_ctor_set(v___x_2090_, 0, v___x_2094_);
v___x_2098_ = v___x_2090_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v___x_2094_);
lean_ctor_set(v_reuseFailAlloc_2099_, 1, v___x_2096_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
v_rangeNumArgs_2034_ = v___x_2098_;
v_lower_2035_ = v___x_2094_;
v___y_2036_ = v___y_1960_;
v___y_2037_ = v___y_1961_;
v___y_2038_ = v___y_1962_;
v___y_2039_ = v___y_1963_;
goto v___jp_2033_;
}
}
else
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2107_; 
lean_del_object(v___x_2090_);
lean_dec(v_fst_2088_);
lean_dec(v_a_2032_);
lean_dec(v_a_2030_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v_term_x3f_1959_);
lean_dec_ref(v_e_1957_);
lean_dec(v___x_1956_);
lean_dec(v_mvarId_1955_);
v_a_2100_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2102_ = v___x_2092_;
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2092_);
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
}
else
{
lean_object* v_fst_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2119_; 
v_fst_2110_ = lean_ctor_get(v_a_2085_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v_a_2085_);
if (v_isSharedCheck_2119_ == 0)
{
lean_object* v_unused_2120_; 
v_unused_2120_ = lean_ctor_get(v_a_2085_, 1);
lean_dec(v_unused_2120_);
v___x_2112_ = v_a_2085_;
v_isShared_2113_ = v_isSharedCheck_2119_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_fst_2110_);
lean_dec(v_a_2085_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2119_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2117_; 
v___x_2114_ = lean_unsigned_to_nat(1u);
v___x_2115_ = lean_nat_add(v_fst_2110_, v___x_2114_);
lean_inc(v_fst_2110_);
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 1, v___x_2115_);
v___x_2117_ = v___x_2112_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_fst_2110_);
lean_ctor_set(v_reuseFailAlloc_2118_, 1, v___x_2115_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
v_rangeNumArgs_2034_ = v___x_2117_;
v_lower_2035_ = v_fst_2110_;
v___y_2036_ = v___y_1960_;
v___y_2037_ = v___y_1961_;
v___y_2038_ = v___y_1962_;
v___y_2039_ = v___y_1963_;
goto v___jp_2033_;
}
}
}
}
else
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2128_; 
lean_dec(v_a_2032_);
lean_dec(v_a_2030_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v_term_x3f_1959_);
lean_dec_ref(v_e_1957_);
lean_dec(v___x_1956_);
lean_dec(v_mvarId_1955_);
v_a_2121_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2123_ = v___x_2084_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2084_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2124_ == 0)
{
v___x_2126_ = v___x_2123_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2121_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
v___jp_2033_:
{
lean_object* v___x_2040_; 
lean_inc(v_mvarId_1955_);
v___x_2040_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(v_mvarId_1955_, v_cfg_1958_, v_term_x3f_1959_, v_a_2030_, v_a_2032_, v_rangeNumArgs_2034_, v_lower_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
lean_dec_ref(v_rangeNumArgs_2034_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_a_2041_; lean_object* v_fst_2042_; lean_object* v_snd_2043_; uint8_t v_newGoals_2044_; uint8_t v_synthAssignedInstances_2045_; uint8_t v_allowSynthFailures_2046_; lean_object* v___x_2047_; 
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
lean_inc(v_a_2041_);
lean_dec_ref_known(v___x_2040_, 1);
v_fst_2042_ = lean_ctor_get(v_a_2041_, 0);
lean_inc(v_fst_2042_);
v_snd_2043_ = lean_ctor_get(v_a_2041_, 1);
lean_inc_n(v_snd_2043_, 2);
lean_dec(v_a_2041_);
v_newGoals_2044_ = lean_ctor_get_uint8(v_cfg_1958_, 0);
v_synthAssignedInstances_2045_ = lean_ctor_get_uint8(v_cfg_1958_, 1);
v_allowSynthFailures_2046_ = lean_ctor_get_uint8(v_cfg_1958_, 2);
lean_inc(v_mvarId_1955_);
v___x_2047_ = l_Lean_Meta_synthAppInstances(v___x_1956_, v_mvarId_1955_, v_fst_2042_, v_snd_2043_, v_synthAssignedInstances_2045_, v_allowSynthFailures_2046_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v___x_2048_; lean_object* v_a_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; uint8_t v___x_2055_; 
lean_dec_ref_known(v___x_2047_, 1);
v___x_2048_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_1957_, v___y_2037_);
v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
lean_inc_n(v_a_2049_, 2);
lean_dec_ref(v___x_2048_);
v___x_2050_ = l_Lean_mkAppN(v_a_2049_, v_fst_2042_);
lean_inc(v_mvarId_1955_);
v___x_2051_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_1955_, v___x_2050_, v___y_2037_);
lean_dec_ref(v___x_2051_);
v___x_2052_ = lean_unsigned_to_nat(0u);
v___x_2053_ = lean_array_get_size(v_fst_2042_);
v___x_2054_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0));
v___x_2055_ = lean_nat_dec_lt(v___x_2052_, v___x_2053_);
if (v___x_2055_ == 0)
{
lean_dec(v_fst_2042_);
v___y_1992_ = v___y_2037_;
v___y_1993_ = v_newGoals_2044_;
v___y_1994_ = v___y_2039_;
v___y_1995_ = v_a_2049_;
v___y_1996_ = v___y_2038_;
v___y_1997_ = v___x_2052_;
v___y_1998_ = v_snd_2043_;
v___y_1999_ = v___y_2036_;
v_a_2000_ = v___x_2054_;
goto v___jp_1991_;
}
else
{
size_t v___x_2056_; size_t v___x_2057_; lean_object* v___x_2058_; 
v___x_2056_ = ((size_t)0ULL);
v___x_2057_ = lean_usize_of_nat(v___x_2053_);
v___x_2058_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_fst_2042_, v___x_2056_, v___x_2057_, v___x_2054_, v___y_2037_);
lean_dec(v_fst_2042_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2059_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_a_2059_);
lean_dec_ref_known(v___x_2058_, 1);
v___y_1992_ = v___y_2037_;
v___y_1993_ = v_newGoals_2044_;
v___y_1994_ = v___y_2039_;
v___y_1995_ = v_a_2049_;
v___y_1996_ = v___y_2038_;
v___y_1997_ = v___x_2052_;
v___y_1998_ = v_snd_2043_;
v___y_1999_ = v___y_2036_;
v_a_2000_ = v_a_2059_;
goto v___jp_1991_;
}
else
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
lean_dec(v_a_2049_);
lean_dec(v_snd_2043_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec(v_mvarId_1955_);
v_a_2060_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_2058_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2058_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2063_ == 0)
{
v___x_2065_ = v___x_2062_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2060_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
}
}
else
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
lean_dec(v_snd_2043_);
lean_dec(v_fst_2042_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec_ref(v_e_1957_);
lean_dec(v_mvarId_1955_);
v_a_2068_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_2047_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2047_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_a_2068_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
else
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec_ref(v_e_1957_);
lean_dec(v___x_1956_);
lean_dec(v_mvarId_1955_);
v_a_2076_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2078_ = v___x_2040_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2040_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_a_2076_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
}
}
else
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2136_; 
lean_dec(v_a_2030_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v_term_x3f_1959_);
lean_dec_ref(v_e_1957_);
lean_dec(v___x_1956_);
lean_dec(v_mvarId_1955_);
v_a_2129_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2131_ = v___x_2031_;
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2031_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2134_; 
if (v_isShared_2132_ == 0)
{
v___x_2134_ = v___x_2131_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_a_2129_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v_term_x3f_1959_);
lean_dec_ref(v_e_1957_);
lean_dec(v___x_1956_);
lean_dec(v_mvarId_1955_);
v_a_2137_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2029_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2029_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2137_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
else
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2152_; 
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v_term_x3f_1959_);
lean_dec_ref(v_e_1957_);
lean_dec(v___x_1956_);
lean_dec(v_mvarId_1955_);
v_a_2145_ = lean_ctor_get(v___x_2028_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2147_ = v___x_2028_;
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2028_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2150_; 
if (v_isShared_2148_ == 0)
{
v___x_2150_ = v___x_2147_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_a_2145_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
v___jp_1965_:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1972_ = lean_array_to_list(v___y_1971_);
v___x_1973_ = l_List_appendTR___redArg(v___y_1968_, v___x_1972_);
lean_inc(v___x_1973_);
v___x_1974_ = l_List_forM___at___00Lean_MVarId_apply_spec__3(v___x_1973_, v___y_1970_, v___y_1966_, v___y_1969_, v___y_1967_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1969_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1970_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1981_; 
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_1981_ == 0)
{
lean_object* v_unused_1982_; 
v_unused_1982_ = lean_ctor_get(v___x_1974_, 0);
lean_dec(v_unused_1982_);
v___x_1976_ = v___x_1974_;
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
else
{
lean_dec(v___x_1974_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 0, v___x_1973_);
v___x_1979_ = v___x_1976_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v___x_1973_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
else
{
lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1990_; 
lean_dec(v___x_1973_);
v_a_1983_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1985_ = v___x_1974_;
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v___x_1974_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1988_; 
if (v_isShared_1986_ == 0)
{
v___x_1988_ = v___x_1985_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_a_1983_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
}
v___jp_1991_:
{
lean_object* v___x_2001_; 
v___x_2001_ = l_Lean_Meta_appendParentTag(v_mvarId_1955_, v_a_2000_, v___y_1998_, v___y_1999_, v___y_1992_, v___y_1996_, v___y_1994_);
lean_dec_ref(v___y_1998_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v___x_2002_; 
lean_dec_ref_known(v___x_2001_, 1);
v___x_2002_ = l_Lean_Meta_getMVarsNoDelayed(v___y_1995_, v___y_1999_, v___y_1992_, v___y_1996_, v___y_1994_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2003_; lean_object* v___x_2004_; 
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_a_2003_);
lean_dec_ref_known(v___x_2002_, 1);
v___x_2004_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(v_a_2000_, v___y_1993_, v___y_1999_, v___y_1992_, v___y_1996_, v___y_1994_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_a_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; uint8_t v___x_2008_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_a_2005_);
lean_dec_ref_known(v___x_2004_, 1);
v___x_2006_ = lean_array_get_size(v_a_2003_);
v___x_2007_ = lean_mk_empty_array_with_capacity(v___y_1997_);
v___x_2008_ = lean_nat_dec_lt(v___y_1997_, v___x_2006_);
if (v___x_2008_ == 0)
{
lean_dec(v_a_2003_);
v___y_1966_ = v___y_1992_;
v___y_1967_ = v___y_1994_;
v___y_1968_ = v_a_2005_;
v___y_1969_ = v___y_1996_;
v___y_1970_ = v___y_1999_;
v___y_1971_ = v___x_2007_;
goto v___jp_1965_;
}
else
{
size_t v___x_2009_; size_t v___x_2010_; lean_object* v___x_2011_; 
v___x_2009_ = ((size_t)0ULL);
v___x_2010_ = lean_usize_of_nat(v___x_2006_);
v___x_2011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_2005_, v_a_2003_, v___x_2009_, v___x_2010_, v___x_2007_);
lean_dec(v_a_2003_);
v___y_1966_ = v___y_1992_;
v___y_1967_ = v___y_1994_;
v___y_1968_ = v_a_2005_;
v___y_1969_ = v___y_1996_;
v___y_1970_ = v___y_1999_;
v___y_1971_ = v___x_2011_;
goto v___jp_1965_;
}
}
else
{
lean_dec(v_a_2003_);
lean_dec_ref(v___y_1999_);
lean_dec_ref(v___y_1996_);
lean_dec(v___y_1994_);
lean_dec(v___y_1992_);
return v___x_2004_;
}
}
else
{
lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2019_; 
lean_dec_ref(v_a_2000_);
lean_dec_ref(v___y_1999_);
lean_dec_ref(v___y_1996_);
lean_dec(v___y_1994_);
lean_dec(v___y_1992_);
v_a_2012_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2014_ = v___x_2002_;
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_2002_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
if (v_isShared_2015_ == 0)
{
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_a_2012_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
}
else
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
lean_dec_ref(v_a_2000_);
lean_dec_ref(v___y_1999_);
lean_dec_ref(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec(v___y_1992_);
v_a_2020_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2022_ = v___x_2001_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_2001_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_a_2020_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lam__0___boxed(lean_object* v_mvarId_2153_, lean_object* v___x_2154_, lean_object* v_e_2155_, lean_object* v_cfg_2156_, lean_object* v_term_x3f_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v_res_2163_; 
v_res_2163_ = l_Lean_MVarId_apply___lam__0(v_mvarId_2153_, v___x_2154_, v_e_2155_, v_cfg_2156_, v_term_x3f_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_);
lean_dec_ref(v_cfg_2156_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply(lean_object* v_mvarId_2164_, lean_object* v_e_2165_, lean_object* v_cfg_2166_, lean_object* v_term_x3f_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_){
_start:
{
lean_object* v___x_2173_; lean_object* v___f_2174_; lean_object* v___x_2175_; 
v___x_2173_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7));
lean_inc(v_mvarId_2164_);
v___f_2174_ = lean_alloc_closure((void*)(l_Lean_MVarId_apply___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2174_, 0, v_mvarId_2164_);
lean_closure_set(v___f_2174_, 1, v___x_2173_);
lean_closure_set(v___f_2174_, 2, v_e_2165_);
lean_closure_set(v___f_2174_, 3, v_cfg_2166_);
lean_closure_set(v___f_2174_, 4, v_term_x3f_2167_);
v___x_2175_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2164_, v___f_2174_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___boxed(lean_object* v_mvarId_2176_, lean_object* v_e_2177_, lean_object* v_cfg_2178_, lean_object* v_term_x3f_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l_Lean_MVarId_apply(v_mvarId_2176_, v_e_2177_, v_cfg_2178_, v_term_x3f_2179_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_);
lean_dec(v_a_2183_);
lean_dec_ref(v_a_2182_);
lean_dec(v_a_2181_);
lean_dec_ref(v_a_2180_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1(lean_object* v_mvarId_2186_, lean_object* v_val_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v___x_2193_; 
v___x_2193_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2186_, v_val_2187_, v___y_2189_);
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___boxed(lean_object* v_mvarId_2194_, lean_object* v_val_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1(v_mvarId_2194_, v_val_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5(lean_object* v_as_2202_, size_t v_i_2203_, size_t v_stop_2204_, lean_object* v_b_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
lean_object* v___x_2211_; 
v___x_2211_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_as_2202_, v_i_2203_, v_stop_2204_, v_b_2205_, v___y_2207_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___boxed(lean_object* v_as_2212_, lean_object* v_i_2213_, lean_object* v_stop_2214_, lean_object* v_b_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
size_t v_i_boxed_2221_; size_t v_stop_boxed_2222_; lean_object* v_res_2223_; 
v_i_boxed_2221_ = lean_unbox_usize(v_i_2213_);
lean_dec(v_i_2213_);
v_stop_boxed_2222_ = lean_unbox_usize(v_stop_2214_);
lean_dec(v_stop_2214_);
v_res_2223_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5(v_as_2212_, v_i_boxed_2221_, v_stop_boxed_2222_, v_b_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec_ref(v_as_2212_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1(lean_object* v_00_u03b2_2224_, lean_object* v_x_2225_, lean_object* v_x_2226_, lean_object* v_x_2227_){
_start:
{
lean_object* v___x_2228_; 
v___x_2228_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(v_x_2225_, v_x_2226_, v_x_2227_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_2229_, lean_object* v_x_2230_, size_t v_x_2231_, size_t v_x_2232_, lean_object* v_x_2233_, lean_object* v_x_2234_){
_start:
{
lean_object* v___x_2235_; 
v___x_2235_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_2230_, v_x_2231_, v_x_2232_, v_x_2233_, v_x_2234_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2236_, lean_object* v_x_2237_, lean_object* v_x_2238_, lean_object* v_x_2239_, lean_object* v_x_2240_, lean_object* v_x_2241_){
_start:
{
size_t v_x_7741__boxed_2242_; size_t v_x_7742__boxed_2243_; lean_object* v_res_2244_; 
v_x_7741__boxed_2242_ = lean_unbox_usize(v_x_2238_);
lean_dec(v_x_2238_);
v_x_7742__boxed_2243_ = lean_unbox_usize(v_x_2239_);
lean_dec(v_x_2239_);
v_res_2244_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3(v_00_u03b2_2236_, v_x_2237_, v_x_7741__boxed_2242_, v_x_7742__boxed_2243_, v_x_2240_, v_x_2241_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_2245_, lean_object* v_n_2246_, lean_object* v_k_2247_, lean_object* v_v_2248_){
_start:
{
lean_object* v___x_2249_; 
v___x_2249_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(v_n_2246_, v_k_2247_, v_v_2248_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9(lean_object* v_00_u03b2_2250_, size_t v_depth_2251_, lean_object* v_keys_2252_, lean_object* v_vals_2253_, lean_object* v_heq_2254_, lean_object* v_i_2255_, lean_object* v_entries_2256_){
_start:
{
lean_object* v___x_2257_; 
v___x_2257_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_depth_2251_, v_keys_2252_, v_vals_2253_, v_i_2255_, v_entries_2256_);
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___boxed(lean_object* v_00_u03b2_2258_, lean_object* v_depth_2259_, lean_object* v_keys_2260_, lean_object* v_vals_2261_, lean_object* v_heq_2262_, lean_object* v_i_2263_, lean_object* v_entries_2264_){
_start:
{
size_t v_depth_boxed_2265_; lean_object* v_res_2266_; 
v_depth_boxed_2265_ = lean_unbox_usize(v_depth_2259_);
lean_dec(v_depth_2259_);
v_res_2266_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9(v_00_u03b2_2258_, v_depth_boxed_2265_, v_keys_2260_, v_vals_2261_, v_heq_2262_, v_i_2263_, v_entries_2264_);
lean_dec_ref(v_vals_2261_);
lean_dec_ref(v_keys_2260_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9(lean_object* v_00_u03b2_2267_, lean_object* v_x_2268_, lean_object* v_x_2269_, lean_object* v_x_2270_, lean_object* v_x_2271_){
_start:
{
lean_object* v___x_2272_; 
v___x_2272_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(v_x_2268_, v_x_2269_, v_x_2270_, v_x_2271_);
return v___x_2272_;
}
}
static lean_object* _init_l_Lean_MVarId_applyConst___closed__1(void){
_start:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2274_ = ((lean_object*)(l_Lean_MVarId_applyConst___closed__0));
v___x_2275_ = l_Lean_stringToMessageData(v___x_2274_);
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyConst(lean_object* v_mvar_2276_, lean_object* v_c_2277_, lean_object* v_cfg_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_){
_start:
{
lean_object* v___x_2284_; 
lean_inc(v_c_2277_);
v___x_2284_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_c_2277_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v_a_2285_; lean_object* v___x_2286_; uint8_t v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_a_2285_);
lean_dec_ref_known(v___x_2284_, 1);
v___x_2286_ = lean_obj_once(&l_Lean_MVarId_applyConst___closed__1, &l_Lean_MVarId_applyConst___closed__1_once, _init_l_Lean_MVarId_applyConst___closed__1);
v___x_2287_ = 0;
v___x_2288_ = l_Lean_MessageData_ofConstName(v_c_2277_, v___x_2287_);
v___x_2289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2286_);
lean_ctor_set(v___x_2289_, 1, v___x_2288_);
v___x_2290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2289_);
lean_ctor_set(v___x_2290_, 1, v___x_2286_);
v___x_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2290_);
v___x_2292_ = l_Lean_MVarId_apply(v_mvar_2276_, v_a_2285_, v_cfg_2278_, v___x_2291_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_);
return v___x_2292_;
}
else
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2300_; 
lean_dec_ref(v_cfg_2278_);
lean_dec(v_c_2277_);
lean_dec(v_mvar_2276_);
v_a_2293_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2295_ = v___x_2284_;
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2284_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2298_; 
if (v_isShared_2296_ == 0)
{
v___x_2298_ = v___x_2295_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_a_2293_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyConst___boxed(lean_object* v_mvar_2301_, lean_object* v_c_2302_, lean_object* v_cfg_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l_Lean_MVarId_applyConst(v_mvar_2301_, v_c_2302_, v_cfg_2303_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_);
lean_dec(v_a_2307_);
lean_dec_ref(v_a_2306_);
lean_dec(v_a_2305_);
lean_dec_ref(v_a_2304_);
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(lean_object* v_msgData_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v___x_2316_; lean_object* v_env_2317_; uint8_t v___x_2318_; lean_object* v_env_2319_; lean_object* v___x_2320_; lean_object* v_toCold_2321_; lean_object* v_mctx_2322_; lean_object* v_lctx_2323_; lean_object* v_options_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2316_ = lean_st_ref_get(v___y_2314_);
v_env_2317_ = lean_ctor_get(v___x_2316_, 0);
lean_inc_ref(v_env_2317_);
lean_dec(v___x_2316_);
v___x_2318_ = 0;
v_env_2319_ = l_Lean_Environment_setRecordingDeps(v_env_2317_, v___x_2318_);
v___x_2320_ = lean_st_ref_get(v___y_2312_);
v_toCold_2321_ = lean_ctor_get(v___y_2313_, 0);
v_mctx_2322_ = lean_ctor_get(v___x_2320_, 0);
lean_inc_ref(v_mctx_2322_);
lean_dec(v___x_2320_);
v_lctx_2323_ = lean_ctor_get(v___y_2311_, 2);
v_options_2324_ = lean_ctor_get(v_toCold_2321_, 2);
lean_inc_ref(v_options_2324_);
lean_inc_ref(v_lctx_2323_);
v___x_2325_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2325_, 0, v_env_2319_);
lean_ctor_set(v___x_2325_, 1, v_mctx_2322_);
lean_ctor_set(v___x_2325_, 2, v_lctx_2323_);
lean_ctor_set(v___x_2325_, 3, v_options_2324_);
v___x_2326_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2325_);
lean_ctor_set(v___x_2326_, 1, v_msgData_2310_);
v___x_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
return v___x_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1___boxed(lean_object* v_msgData_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(v_msgData_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(lean_object* v_msg_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_){
_start:
{
lean_object* v_ref_2341_; lean_object* v___x_2342_; lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2351_; 
v_ref_2341_ = lean_ctor_get(v___y_2338_, 2);
v___x_2342_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(v_msg_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_);
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2345_ = v___x_2342_;
v_isShared_2346_ = v_isSharedCheck_2351_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2342_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2351_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2347_; lean_object* v___x_2349_; 
lean_inc(v_ref_2341_);
v___x_2347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2347_, 0, v_ref_2341_);
lean_ctor_set(v___x_2347_, 1, v_a_2343_);
if (v_isShared_2346_ == 0)
{
lean_ctor_set_tag(v___x_2345_, 1);
lean_ctor_set(v___x_2345_, 0, v___x_2347_);
v___x_2349_ = v___x_2345_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v___x_2347_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg___boxed(lean_object* v_msg_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
lean_object* v_res_2358_; 
v_res_2358_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v_msg_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2353_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(size_t v_sz_2359_, size_t v_i_2360_, lean_object* v_bs_2361_){
_start:
{
uint8_t v___x_2362_; 
v___x_2362_ = lean_usize_dec_lt(v_i_2360_, v_sz_2359_);
if (v___x_2362_ == 0)
{
return v_bs_2361_;
}
else
{
lean_object* v_v_2363_; lean_object* v___x_2364_; lean_object* v_bs_x27_2365_; lean_object* v___x_2366_; size_t v___x_2367_; size_t v___x_2368_; lean_object* v___x_2369_; 
v_v_2363_ = lean_array_uget(v_bs_2361_, v_i_2360_);
v___x_2364_ = lean_unsigned_to_nat(0u);
v_bs_x27_2365_ = lean_array_uset(v_bs_2361_, v_i_2360_, v___x_2364_);
v___x_2366_ = l_Lean_Expr_mvarId_x21(v_v_2363_);
lean_dec(v_v_2363_);
v___x_2367_ = ((size_t)1ULL);
v___x_2368_ = lean_usize_add(v_i_2360_, v___x_2367_);
v___x_2369_ = lean_array_uset(v_bs_x27_2365_, v_i_2360_, v___x_2366_);
v_i_2360_ = v___x_2368_;
v_bs_2361_ = v___x_2369_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0___boxed(lean_object* v_sz_2371_, lean_object* v_i_2372_, lean_object* v_bs_2373_){
_start:
{
size_t v_sz_boxed_2374_; size_t v_i_boxed_2375_; lean_object* v_res_2376_; 
v_sz_boxed_2374_ = lean_unbox_usize(v_sz_2371_);
lean_dec(v_sz_2371_);
v_i_boxed_2375_ = lean_unbox_usize(v_i_2372_);
lean_dec(v_i_2372_);
v_res_2376_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(v_sz_boxed_2374_, v_i_boxed_2375_, v_bs_2373_);
return v_res_2376_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2378_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__0));
v___x_2379_ = l_Lean_stringToMessageData(v___x_2378_);
return v___x_2379_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2381_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__2));
v___x_2382_ = l_Lean_stringToMessageData(v___x_2381_);
return v___x_2382_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2384_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__4));
v___x_2385_ = l_Lean_stringToMessageData(v___x_2384_);
return v___x_2385_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2387_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__6));
v___x_2388_ = l_Lean_stringToMessageData(v___x_2387_);
return v___x_2388_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__9(void){
_start:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2390_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__8));
v___x_2391_ = l_Lean_stringToMessageData(v___x_2390_);
return v___x_2391_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__11(void){
_start:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2393_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__10));
v___x_2394_ = l_Lean_stringToMessageData(v___x_2393_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___lam__0(lean_object* v_mvarId_2395_, lean_object* v___x_2396_, lean_object* v_e_2397_, lean_object* v_n_2398_, uint8_t v_useApproxDefEq_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v___x_2405_; 
lean_inc(v_mvarId_2395_);
v___x_2405_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2395_, v___x_2396_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v___x_2406_; 
lean_dec_ref_known(v___x_2405_, 1);
lean_inc(v_mvarId_2395_);
v___x_2406_ = l_Lean_MVarId_getType(v_mvarId_2395_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v_a_2407_; lean_object* v___x_2408_; 
v_a_2407_ = lean_ctor_get(v___x_2406_, 0);
lean_inc(v_a_2407_);
lean_dec_ref_known(v___x_2406_, 1);
lean_inc(v___y_2403_);
lean_inc_ref(v___y_2402_);
lean_inc(v___y_2401_);
lean_inc_ref(v___y_2400_);
lean_inc_ref(v_e_2397_);
v___x_2408_ = lean_infer_type(v_e_2397_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_object* v_a_2409_; uint8_t v___x_2410_; lean_object* v___x_2411_; 
v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
lean_inc(v_a_2409_);
lean_dec_ref_known(v___x_2408_, 1);
v___x_2410_ = 0;
lean_inc(v_n_2398_);
v___x_2411_ = l_Lean_Meta_forallMetaBoundedTelescope(v_a_2409_, v_n_2398_, v___x_2410_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v_a_2412_; lean_object* v_fst_2413_; lean_object* v_snd_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2504_; 
v_a_2412_ = lean_ctor_get(v___x_2411_, 0);
lean_inc(v_a_2412_);
lean_dec_ref_known(v___x_2411_, 1);
v_fst_2413_ = lean_ctor_get(v_a_2412_, 0);
v_snd_2414_ = lean_ctor_get(v_a_2412_, 1);
v_isSharedCheck_2504_ = !lean_is_exclusive(v_a_2412_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2416_ = v_a_2412_;
v_isShared_2417_ = v_isSharedCheck_2504_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_snd_2414_);
lean_inc(v_fst_2413_);
lean_dec(v_a_2412_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2504_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___y_2419_; lean_object* v_snd_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2502_; 
v_snd_2434_ = lean_ctor_get(v_snd_2414_, 1);
v_isSharedCheck_2502_ = !lean_is_exclusive(v_snd_2414_);
if (v_isSharedCheck_2502_ == 0)
{
lean_object* v_unused_2503_; 
v_unused_2503_ = lean_ctor_get(v_snd_2414_, 0);
lean_dec(v_unused_2503_);
v___x_2436_ = v_snd_2414_;
v_isShared_2437_ = v_isSharedCheck_2502_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_snd_2434_);
lean_dec(v_snd_2414_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2502_;
goto v_resetjp_2435_;
}
v___jp_2418_:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2432_; 
lean_inc(v_fst_2413_);
v___x_2420_ = l_Lean_Expr_beta(v_e_2397_, v_fst_2413_);
v___x_2421_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2395_, v___x_2420_, v___y_2419_);
lean_dec(v___y_2419_);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2432_ == 0)
{
lean_object* v_unused_2433_; 
v_unused_2433_ = lean_ctor_get(v___x_2421_, 0);
lean_dec(v_unused_2433_);
v___x_2423_ = v___x_2421_;
v_isShared_2424_ = v_isSharedCheck_2432_;
goto v_resetjp_2422_;
}
else
{
lean_dec(v___x_2421_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2432_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
size_t v_sz_2425_; size_t v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2430_; 
v_sz_2425_ = lean_array_size(v_fst_2413_);
v___x_2426_ = ((size_t)0ULL);
v___x_2427_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(v_sz_2425_, v___x_2426_, v_fst_2413_);
v___x_2428_ = lean_array_to_list(v___x_2427_);
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 0, v___x_2428_);
v___x_2430_ = v___x_2423_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2428_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
v_resetjp_2435_:
{
lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___x_2482_; uint8_t v___x_2483_; 
v___x_2482_ = lean_array_get_size(v_fst_2413_);
v___x_2483_ = lean_nat_dec_eq(v___x_2482_, v_n_2398_);
if (v___x_2483_ == 0)
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v_a_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2501_; 
lean_del_object(v___x_2436_);
lean_del_object(v___x_2416_);
lean_dec(v_fst_2413_);
lean_dec(v_a_2407_);
lean_dec_ref(v_e_2397_);
lean_dec(v_mvarId_2395_);
v___x_2484_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__9, &l_Lean_MVarId_applyN___lam__0___closed__9_once, _init_l_Lean_MVarId_applyN___lam__0___closed__9);
v___x_2485_ = l_Nat_reprFast(v_n_2398_);
v___x_2486_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2485_);
v___x_2487_ = l_Lean_MessageData_ofFormat(v___x_2486_);
v___x_2488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2484_);
lean_ctor_set(v___x_2488_, 1, v___x_2487_);
v___x_2489_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__11, &l_Lean_MVarId_applyN___lam__0___closed__11_once, _init_l_Lean_MVarId_applyN___lam__0___closed__11);
v___x_2490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2490_, 0, v___x_2488_);
lean_ctor_set(v___x_2490_, 1, v___x_2489_);
v___x_2491_ = l_Lean_indentExpr(v_snd_2434_);
v___x_2492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2490_);
lean_ctor_set(v___x_2492_, 1, v___x_2491_);
v___x_2493_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_2492_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
v_a_2494_ = lean_ctor_get(v___x_2493_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2496_ = v___x_2493_;
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_a_2494_);
lean_dec(v___x_2493_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2499_; 
if (v_isShared_2497_ == 0)
{
v___x_2499_ = v___x_2496_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_a_2494_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
}
else
{
v___y_2439_ = v___y_2400_;
v___y_2440_ = v___y_2401_;
v___y_2441_ = v___y_2402_;
v___y_2442_ = v___y_2403_;
goto v___jp_2438_;
}
v___jp_2438_:
{
lean_object* v___x_2443_; 
lean_inc(v_a_2407_);
lean_inc(v_snd_2434_);
v___x_2443_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_useApproxDefEq_2399_, v_snd_2434_, v_a_2407_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; uint8_t v___x_2445_; 
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
lean_inc(v_a_2444_);
lean_dec_ref_known(v___x_2443_, 1);
v___x_2445_ = lean_unbox(v_a_2444_);
lean_dec(v_a_2444_);
if (v___x_2445_ == 0)
{
lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2449_; 
lean_dec(v_fst_2413_);
lean_dec_ref(v_e_2397_);
lean_dec(v_mvarId_2395_);
v___x_2446_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__1, &l_Lean_MVarId_applyN___lam__0___closed__1_once, _init_l_Lean_MVarId_applyN___lam__0___closed__1);
v___x_2447_ = l_Lean_indentExpr(v_a_2407_);
if (v_isShared_2437_ == 0)
{
lean_ctor_set_tag(v___x_2436_, 7);
lean_ctor_set(v___x_2436_, 1, v___x_2447_);
lean_ctor_set(v___x_2436_, 0, v___x_2446_);
v___x_2449_ = v___x_2436_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v___x_2446_);
lean_ctor_set(v_reuseFailAlloc_2473_, 1, v___x_2447_);
v___x_2449_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
lean_object* v___x_2450_; lean_object* v___x_2452_; 
v___x_2450_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__3, &l_Lean_MVarId_applyN___lam__0___closed__3_once, _init_l_Lean_MVarId_applyN___lam__0___closed__3);
if (v_isShared_2417_ == 0)
{
lean_ctor_set_tag(v___x_2416_, 7);
lean_ctor_set(v___x_2416_, 1, v___x_2450_);
lean_ctor_set(v___x_2416_, 0, v___x_2449_);
v___x_2452_ = v___x_2416_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v___x_2449_);
lean_ctor_set(v_reuseFailAlloc_2472_, 1, v___x_2450_);
v___x_2452_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2471_; 
v___x_2453_ = l_Lean_indentExpr(v_snd_2434_);
v___x_2454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2454_, 0, v___x_2452_);
lean_ctor_set(v___x_2454_, 1, v___x_2453_);
v___x_2455_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__5, &l_Lean_MVarId_applyN___lam__0___closed__5_once, _init_l_Lean_MVarId_applyN___lam__0___closed__5);
v___x_2456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2454_);
lean_ctor_set(v___x_2456_, 1, v___x_2455_);
v___x_2457_ = l_Nat_reprFast(v_n_2398_);
v___x_2458_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2457_);
v___x_2459_ = l_Lean_MessageData_ofFormat(v___x_2458_);
v___x_2460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2456_);
lean_ctor_set(v___x_2460_, 1, v___x_2459_);
v___x_2461_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__7, &l_Lean_MVarId_applyN___lam__0___closed__7_once, _init_l_Lean_MVarId_applyN___lam__0___closed__7);
v___x_2462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2460_);
lean_ctor_set(v___x_2462_, 1, v___x_2461_);
v___x_2463_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_2462_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2466_ = v___x_2463_;
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2463_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2469_; 
if (v_isShared_2467_ == 0)
{
v___x_2469_ = v___x_2466_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2464_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
}
}
else
{
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec_ref(v___y_2439_);
lean_del_object(v___x_2436_);
lean_dec(v_snd_2434_);
lean_del_object(v___x_2416_);
lean_dec(v_a_2407_);
lean_dec(v_n_2398_);
v___y_2419_ = v___y_2440_;
goto v___jp_2418_;
}
}
else
{
lean_object* v_a_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2481_; 
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_del_object(v___x_2436_);
lean_dec(v_snd_2434_);
lean_del_object(v___x_2416_);
lean_dec(v_fst_2413_);
lean_dec(v_a_2407_);
lean_dec(v_n_2398_);
lean_dec_ref(v_e_2397_);
lean_dec(v_mvarId_2395_);
v_a_2474_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2476_ = v___x_2443_;
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_a_2474_);
lean_dec(v___x_2443_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2479_; 
if (v_isShared_2477_ == 0)
{
v___x_2479_ = v___x_2476_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_a_2474_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2512_; 
lean_dec(v_a_2407_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v_n_2398_);
lean_dec_ref(v_e_2397_);
lean_dec(v_mvarId_2395_);
v_a_2505_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2507_ = v___x_2411_;
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2411_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2510_; 
if (v_isShared_2508_ == 0)
{
v___x_2510_ = v___x_2507_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_a_2505_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
else
{
lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2520_; 
lean_dec(v_a_2407_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v_n_2398_);
lean_dec_ref(v_e_2397_);
lean_dec(v_mvarId_2395_);
v_a_2513_ = lean_ctor_get(v___x_2408_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2515_ = v___x_2408_;
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v___x_2408_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2518_; 
if (v_isShared_2516_ == 0)
{
v___x_2518_ = v___x_2515_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_a_2513_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
}
else
{
lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2528_; 
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v_n_2398_);
lean_dec_ref(v_e_2397_);
lean_dec(v_mvarId_2395_);
v_a_2521_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2523_ = v___x_2406_;
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v___x_2406_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2526_; 
if (v_isShared_2524_ == 0)
{
v___x_2526_ = v___x_2523_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_a_2521_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
}
}
else
{
lean_object* v_a_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2536_; 
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v_n_2398_);
lean_dec_ref(v_e_2397_);
lean_dec(v_mvarId_2395_);
v_a_2529_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2531_ = v___x_2405_;
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_a_2529_);
lean_dec(v___x_2405_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___x_2534_; 
if (v_isShared_2532_ == 0)
{
v___x_2534_ = v___x_2531_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_a_2529_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___lam__0___boxed(lean_object* v_mvarId_2537_, lean_object* v___x_2538_, lean_object* v_e_2539_, lean_object* v_n_2540_, lean_object* v_useApproxDefEq_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_){
_start:
{
uint8_t v_useApproxDefEq_boxed_2547_; lean_object* v_res_2548_; 
v_useApproxDefEq_boxed_2547_ = lean_unbox(v_useApproxDefEq_2541_);
v_res_2548_ = l_Lean_MVarId_applyN___lam__0(v_mvarId_2537_, v___x_2538_, v_e_2539_, v_n_2540_, v_useApproxDefEq_boxed_2547_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_);
return v_res_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN(lean_object* v_mvarId_2549_, lean_object* v_e_2550_, lean_object* v_n_2551_, uint8_t v_useApproxDefEq_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_){
_start:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___f_2560_; lean_object* v___x_2561_; 
v___x_2558_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7));
v___x_2559_ = lean_box(v_useApproxDefEq_2552_);
lean_inc(v_mvarId_2549_);
v___f_2560_ = lean_alloc_closure((void*)(l_Lean_MVarId_applyN___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2560_, 0, v_mvarId_2549_);
lean_closure_set(v___f_2560_, 1, v___x_2558_);
lean_closure_set(v___f_2560_, 2, v_e_2550_);
lean_closure_set(v___f_2560_, 3, v_n_2551_);
lean_closure_set(v___f_2560_, 4, v___x_2559_);
v___x_2561_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2549_, v___f_2560_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_);
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___boxed(lean_object* v_mvarId_2562_, lean_object* v_e_2563_, lean_object* v_n_2564_, lean_object* v_useApproxDefEq_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_){
_start:
{
uint8_t v_useApproxDefEq_boxed_2571_; lean_object* v_res_2572_; 
v_useApproxDefEq_boxed_2571_ = lean_unbox(v_useApproxDefEq_2565_);
v_res_2572_ = l_Lean_MVarId_applyN(v_mvarId_2562_, v_e_2563_, v_n_2564_, v_useApproxDefEq_boxed_2571_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_);
lean_dec(v_a_2569_);
lean_dec_ref(v_a_2568_);
lean_dec(v_a_2567_);
lean_dec_ref(v_a_2566_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1(lean_object* v_00_u03b1_2573_, lean_object* v_msg_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_){
_start:
{
lean_object* v___x_2580_; 
v___x_2580_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v_msg_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___boxed(lean_object* v_00_u03b1_2581_, lean_object* v_msg_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_){
_start:
{
lean_object* v_res_2588_; 
v_res_2588_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1(v_00_u03b1_2581_, v_msg_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_);
lean_dec(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec(v___y_2584_);
lean_dec_ref(v___y_2583_);
return v_res_2588_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6(void){
_start:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2599_ = lean_box(0);
v___x_2600_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__5));
v___x_2601_ = l_Lean_mkConst(v___x_2600_, v___x_2599_);
return v___x_2601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(lean_object* v_tag_2602_, lean_object* v_type_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_){
_start:
{
lean_object* v___x_2610_; 
lean_inc(v_a_2608_);
lean_inc_ref(v_a_2607_);
lean_inc(v_a_2606_);
lean_inc_ref(v_a_2605_);
v___x_2610_ = lean_whnf(v_type_2603_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; uint8_t v___x_2614_; 
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
lean_inc(v_a_2611_);
lean_dec_ref_known(v___x_2610_, 1);
v___x_2612_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1));
v___x_2613_ = lean_unsigned_to_nat(2u);
v___x_2614_ = l_Lean_Expr_isAppOfArity(v_a_2611_, v___x_2612_, v___x_2613_);
if (v___x_2614_ == 0)
{
lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2615_ = lean_st_ref_get(v_a_2604_);
v___x_2616_ = lean_array_get_size(v___x_2615_);
lean_dec(v___x_2615_);
v___x_2617_ = lean_unsigned_to_nat(1u);
v___x_2618_ = lean_nat_add(v___x_2616_, v___x_2617_);
v___x_2619_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__3));
v___x_2620_ = lean_name_append_index_after(v___x_2619_, v___x_2618_);
v___x_2621_ = l_Lean_Name_append(v_tag_2602_, v___x_2620_);
v___x_2622_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2611_, v___x_2621_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_);
if (lean_obj_tag(v___x_2622_) == 0)
{
lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2634_; 
v_a_2623_ = lean_ctor_get(v___x_2622_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2625_ = v___x_2622_;
v_isShared_2626_ = v_isSharedCheck_2634_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v___x_2622_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2634_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2632_; 
v___x_2627_ = lean_st_ref_take(v_a_2604_);
v___x_2628_ = l_Lean_Expr_mvarId_x21(v_a_2623_);
v___x_2629_ = lean_array_push(v___x_2627_, v___x_2628_);
v___x_2630_ = lean_st_ref_put(v_a_2604_, v___x_2629_);
if (v_isShared_2626_ == 0)
{
v___x_2632_ = v___x_2625_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2623_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
}
else
{
return v___x_2622_;
}
}
else
{
lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; 
v___x_2635_ = l_Lean_Expr_appFn_x21(v_a_2611_);
v___x_2636_ = l_Lean_Expr_appArg_x21(v___x_2635_);
lean_dec_ref(v___x_2635_);
v___x_2637_ = l_Lean_Expr_appArg_x21(v_a_2611_);
lean_dec(v_a_2611_);
lean_inc_ref(v___x_2636_);
lean_inc(v_tag_2602_);
v___x_2638_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2602_, v___x_2636_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_);
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_object* v_a_2639_; lean_object* v___x_2640_; 
v_a_2639_ = lean_ctor_get(v___x_2638_, 0);
lean_inc(v_a_2639_);
lean_dec_ref_known(v___x_2638_, 1);
lean_inc_ref(v___x_2637_);
v___x_2640_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2602_, v___x_2637_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2650_; 
v_a_2641_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2643_ = v___x_2640_;
v_isShared_2644_ = v_isSharedCheck_2650_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___x_2640_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2650_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2648_; 
v___x_2645_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6, &l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6);
v___x_2646_ = l_Lean_mkApp4(v___x_2645_, v___x_2636_, v___x_2637_, v_a_2639_, v_a_2641_);
if (v_isShared_2644_ == 0)
{
lean_ctor_set(v___x_2643_, 0, v___x_2646_);
v___x_2648_ = v___x_2643_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v___x_2646_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
else
{
lean_dec(v_a_2639_);
lean_dec_ref(v___x_2637_);
lean_dec_ref(v___x_2636_);
return v___x_2640_;
}
}
else
{
lean_dec_ref(v___x_2637_);
lean_dec_ref(v___x_2636_);
lean_dec(v_tag_2602_);
return v___x_2638_;
}
}
}
else
{
lean_dec(v_tag_2602_);
return v___x_2610_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___boxed(lean_object* v_tag_2651_, lean_object* v_type_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2651_, v_type_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_);
lean_dec(v_a_2657_);
lean_dec_ref(v_a_2656_);
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2654_);
lean_dec(v_a_2653_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___lam__0(lean_object* v_mvarId_2660_, lean_object* v___x_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
lean_object* v___x_2667_; 
lean_inc(v_mvarId_2660_);
v___x_2667_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2660_, v___x_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v___x_2668_; 
lean_dec_ref_known(v___x_2667_, 1);
lean_inc(v_mvarId_2660_);
v___x_2668_ = l_Lean_MVarId_getType_x27(v_mvarId_2660_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_object* v_a_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2714_; 
v_a_2669_ = lean_ctor_get(v___x_2668_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2671_ = v___x_2668_;
v_isShared_2672_ = v_isSharedCheck_2714_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_a_2669_);
lean_dec(v___x_2668_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2714_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2673_; lean_object* v___x_2674_; uint8_t v___x_2675_; 
v___x_2673_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1));
v___x_2674_ = lean_unsigned_to_nat(2u);
v___x_2675_ = l_Lean_Expr_isAppOfArity(v_a_2669_, v___x_2673_, v___x_2674_);
if (v___x_2675_ == 0)
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2679_; 
lean_dec(v_a_2669_);
v___x_2676_ = lean_box(0);
v___x_2677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2677_, 0, v_mvarId_2660_);
lean_ctor_set(v___x_2677_, 1, v___x_2676_);
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 0, v___x_2677_);
v___x_2679_ = v___x_2671_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v___x_2677_);
v___x_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
return v___x_2679_;
}
}
else
{
lean_object* v___x_2681_; 
lean_del_object(v___x_2671_);
lean_inc(v_mvarId_2660_);
v___x_2681_ = l_Lean_MVarId_getTag(v_mvarId_2660_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
if (lean_obj_tag(v___x_2681_) == 0)
{
lean_object* v_a_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v_a_2682_ = lean_ctor_get(v___x_2681_, 0);
lean_inc(v_a_2682_);
lean_dec_ref_known(v___x_2681_, 1);
v___x_2683_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__0));
v___x_2684_ = lean_st_mk_ref(v___x_2683_);
v___x_2685_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_a_2682_, v_a_2669_, v___x_2684_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v_a_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2696_; 
v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
lean_inc(v_a_2686_);
lean_dec_ref_known(v___x_2685_, 1);
v___x_2687_ = lean_st_ref_get(v___x_2684_);
lean_dec(v___x_2684_);
v___x_2688_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2660_, v_a_2686_, v___y_2663_);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2696_ == 0)
{
lean_object* v_unused_2697_; 
v_unused_2697_ = lean_ctor_get(v___x_2688_, 0);
lean_dec(v_unused_2697_);
v___x_2690_ = v___x_2688_;
v_isShared_2691_ = v_isSharedCheck_2696_;
goto v_resetjp_2689_;
}
else
{
lean_dec(v___x_2688_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2696_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2692_; lean_object* v___x_2694_; 
v___x_2692_ = lean_array_to_list(v___x_2687_);
if (v_isShared_2691_ == 0)
{
lean_ctor_set(v___x_2690_, 0, v___x_2692_);
v___x_2694_ = v___x_2690_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2692_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
else
{
lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2705_; 
lean_dec(v___x_2684_);
lean_dec(v_mvarId_2660_);
v_a_2698_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2700_ = v___x_2685_;
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2685_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2703_; 
if (v_isShared_2701_ == 0)
{
v___x_2703_ = v___x_2700_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_a_2698_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
}
}
else
{
lean_object* v_a_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2713_; 
lean_dec(v_a_2669_);
lean_dec(v_mvarId_2660_);
v_a_2706_ = lean_ctor_get(v___x_2681_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2681_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2708_ = v___x_2681_;
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_dec(v___x_2681_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2711_; 
if (v_isShared_2709_ == 0)
{
v___x_2711_ = v___x_2708_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_a_2706_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
return v___x_2711_;
}
}
}
}
}
}
else
{
lean_object* v_a_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2722_; 
lean_dec(v_mvarId_2660_);
v_a_2715_ = lean_ctor_get(v___x_2668_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2717_ = v___x_2668_;
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_a_2715_);
lean_dec(v___x_2668_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2720_; 
if (v_isShared_2718_ == 0)
{
v___x_2720_ = v___x_2717_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_a_2715_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
return v___x_2720_;
}
}
}
}
else
{
lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2730_; 
lean_dec(v_mvarId_2660_);
v_a_2723_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2725_ = v___x_2667_;
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2667_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2728_; 
if (v_isShared_2726_ == 0)
{
v___x_2728_ = v___x_2725_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_a_2723_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___lam__0___boxed(lean_object* v_mvarId_2731_, lean_object* v___x_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
lean_object* v_res_2738_; 
v_res_2738_ = l_Lean_MVarId_splitAndCore___lam__0(v_mvarId_2731_, v___x_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
lean_dec(v___y_2736_);
lean_dec_ref(v___y_2735_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore(lean_object* v_mvarId_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_){
_start:
{
lean_object* v___x_2748_; lean_object* v___f_2749_; lean_object* v___x_2750_; 
v___x_2748_ = ((lean_object*)(l_Lean_MVarId_splitAndCore___closed__1));
lean_inc(v_mvarId_2742_);
v___f_2749_ = lean_alloc_closure((void*)(l_Lean_MVarId_splitAndCore___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2749_, 0, v_mvarId_2742_);
lean_closure_set(v___f_2749_, 1, v___x_2748_);
v___x_2750_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2742_, v___f_2749_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___boxed(lean_object* v_mvarId_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_){
_start:
{
lean_object* v_res_2757_; 
v_res_2757_ = l_Lean_MVarId_splitAndCore(v_mvarId_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_);
lean_dec(v_a_2755_);
lean_dec_ref(v_a_2754_);
lean_dec(v_a_2753_);
lean_dec_ref(v_a_2752_);
return v_res_2757_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAnd(lean_object* v_mvarId_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_){
_start:
{
lean_object* v___x_2764_; 
v___x_2764_ = l_Lean_MVarId_splitAndCore(v_mvarId_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
return v___x_2764_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAnd___boxed(lean_object* v_mvarId_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_){
_start:
{
lean_object* v_res_2771_; 
v_res_2771_ = l_Lean_MVarId_splitAnd(v_mvarId_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_);
lean_dec(v_a_2769_);
lean_dec_ref(v_a_2768_);
lean_dec(v_a_2767_);
lean_dec_ref(v_a_2766_);
return v_res_2771_;
}
}
static lean_object* _init_l_Lean_MVarId_exfalso___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; 
v___x_2775_ = lean_box(0);
v___x_2776_ = ((lean_object*)(l_Lean_MVarId_exfalso___lam__0___closed__1));
v___x_2777_ = l_Lean_mkConst(v___x_2776_, v___x_2775_);
return v___x_2777_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___lam__0(lean_object* v_mvarId_2782_, lean_object* v___x_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_){
_start:
{
lean_object* v___x_2789_; 
lean_inc(v_mvarId_2782_);
v___x_2789_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2782_, v___x_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v___x_2790_; 
lean_dec_ref_known(v___x_2789_, 1);
lean_inc(v_mvarId_2782_);
v___x_2790_ = l_Lean_MVarId_getType(v_mvarId_2782_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_);
if (lean_obj_tag(v___x_2790_) == 0)
{
lean_object* v_a_2791_; lean_object* v___x_2792_; lean_object* v_a_2793_; lean_object* v___x_2794_; 
v_a_2791_ = lean_ctor_get(v___x_2790_, 0);
lean_inc(v_a_2791_);
lean_dec_ref_known(v___x_2790_, 1);
v___x_2792_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_a_2791_, v___y_2785_);
v_a_2793_ = lean_ctor_get(v___x_2792_, 0);
lean_inc_n(v_a_2793_, 2);
lean_dec_ref(v___x_2792_);
v___x_2794_ = l_Lean_Meta_getLevel(v_a_2793_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v_a_2795_; lean_object* v___x_2796_; 
v_a_2795_ = lean_ctor_get(v___x_2794_, 0);
lean_inc(v_a_2795_);
lean_dec_ref_known(v___x_2794_, 1);
lean_inc(v_mvarId_2782_);
v___x_2796_ = l_Lean_MVarId_getTag(v_mvarId_2782_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_);
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_object* v_a_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; 
v_a_2797_ = lean_ctor_get(v___x_2796_, 0);
lean_inc(v_a_2797_);
lean_dec_ref_known(v___x_2796_, 1);
v___x_2798_ = lean_box(0);
v___x_2799_ = lean_obj_once(&l_Lean_MVarId_exfalso___lam__0___closed__2, &l_Lean_MVarId_exfalso___lam__0___closed__2_once, _init_l_Lean_MVarId_exfalso___lam__0___closed__2);
v___x_2800_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2799_, v_a_2797_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_);
if (lean_obj_tag(v___x_2800_) == 0)
{
lean_object* v_a_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2814_; 
v_a_2801_ = lean_ctor_get(v___x_2800_, 0);
lean_inc_n(v_a_2801_, 2);
lean_dec_ref_known(v___x_2800_, 1);
v___x_2802_ = ((lean_object*)(l_Lean_MVarId_exfalso___lam__0___closed__4));
v___x_2803_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2803_, 0, v_a_2795_);
lean_ctor_set(v___x_2803_, 1, v___x_2798_);
v___x_2804_ = l_Lean_mkConst(v___x_2802_, v___x_2803_);
v___x_2805_ = l_Lean_mkAppB(v___x_2804_, v_a_2793_, v_a_2801_);
v___x_2806_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2782_, v___x_2805_, v___y_2785_);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2814_ == 0)
{
lean_object* v_unused_2815_; 
v_unused_2815_ = lean_ctor_get(v___x_2806_, 0);
lean_dec(v_unused_2815_);
v___x_2808_ = v___x_2806_;
v_isShared_2809_ = v_isSharedCheck_2814_;
goto v_resetjp_2807_;
}
else
{
lean_dec(v___x_2806_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2814_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2810_; lean_object* v___x_2812_; 
v___x_2810_ = l_Lean_Expr_mvarId_x21(v_a_2801_);
lean_dec(v_a_2801_);
if (v_isShared_2809_ == 0)
{
lean_ctor_set(v___x_2808_, 0, v___x_2810_);
v___x_2812_ = v___x_2808_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v___x_2810_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
}
else
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2823_; 
lean_dec(v_a_2795_);
lean_dec(v_a_2793_);
lean_dec(v_mvarId_2782_);
v_a_2816_ = lean_ctor_get(v___x_2800_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2818_ = v___x_2800_;
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2800_);
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
else
{
lean_object* v_a_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2831_; 
lean_dec(v_a_2795_);
lean_dec(v_a_2793_);
lean_dec(v_mvarId_2782_);
v_a_2824_ = lean_ctor_get(v___x_2796_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2826_ = v___x_2796_;
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_a_2824_);
lean_dec(v___x_2796_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v___x_2829_; 
if (v_isShared_2827_ == 0)
{
v___x_2829_ = v___x_2826_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_a_2824_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
return v___x_2829_;
}
}
}
}
else
{
lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2839_; 
lean_dec(v_a_2793_);
lean_dec(v_mvarId_2782_);
v_a_2832_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2834_ = v___x_2794_;
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___x_2794_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2837_; 
if (v_isShared_2835_ == 0)
{
v___x_2837_ = v___x_2834_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_a_2832_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
return v___x_2837_;
}
}
}
}
else
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2847_; 
lean_dec(v_mvarId_2782_);
v_a_2840_ = lean_ctor_get(v___x_2790_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2842_ = v___x_2790_;
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2790_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2845_; 
if (v_isShared_2843_ == 0)
{
v___x_2845_ = v___x_2842_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_a_2840_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
}
else
{
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2855_; 
lean_dec(v_mvarId_2782_);
v_a_2848_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2850_ = v___x_2789_;
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2789_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___lam__0___boxed(lean_object* v_mvarId_2856_, lean_object* v___x_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_){
_start:
{
lean_object* v_res_2863_; 
v_res_2863_ = l_Lean_MVarId_exfalso___lam__0(v_mvarId_2856_, v___x_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_);
lean_dec(v___y_2861_);
lean_dec_ref(v___y_2860_);
lean_dec(v___y_2859_);
lean_dec_ref(v___y_2858_);
return v_res_2863_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso(lean_object* v_mvarId_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_){
_start:
{
lean_object* v___x_2873_; lean_object* v___f_2874_; lean_object* v___x_2875_; 
v___x_2873_ = ((lean_object*)(l_Lean_MVarId_exfalso___closed__1));
lean_inc(v_mvarId_2867_);
v___f_2874_ = lean_alloc_closure((void*)(l_Lean_MVarId_exfalso___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2874_, 0, v_mvarId_2867_);
lean_closure_set(v___f_2874_, 1, v___x_2873_);
v___x_2875_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2867_, v___f_2874_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___boxed(lean_object* v_mvarId_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l_Lean_MVarId_exfalso(v_mvarId_2876_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_);
lean_dec(v_a_2880_);
lean_dec_ref(v_a_2879_);
lean_dec(v_a_2878_);
lean_dec_ref(v_a_2877_);
return v_res_2882_;
}
}
static lean_object* _init_l_Lean_MVarId_nthConstructor___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2886_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__1));
v___x_2887_ = l_Lean_MessageData_ofFormat(v___x_2886_);
return v___x_2887_;
}
}
static lean_object* _init_l_Lean_MVarId_nthConstructor___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2888_; lean_object* v___x_2889_; 
v___x_2888_ = lean_obj_once(&l_Lean_MVarId_nthConstructor___lam__0___closed__2, &l_Lean_MVarId_nthConstructor___lam__0___closed__2_once, _init_l_Lean_MVarId_nthConstructor___lam__0___closed__2);
v___x_2889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2888_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___lam__0(lean_object* v_name_2894_, lean_object* v_goal_2895_, lean_object* v_idx_2896_, lean_object* v_expected_x3f_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_){
_start:
{
lean_object* v___x_2906_; 
lean_inc(v_name_2894_);
lean_inc(v_goal_2895_);
v___x_2906_ = l_Lean_MVarId_checkNotAssigned(v_goal_2895_, v_name_2894_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2906_) == 0)
{
lean_object* v___x_2907_; 
lean_dec_ref_known(v___x_2906_, 1);
lean_inc(v_goal_2895_);
v___x_2907_ = l_Lean_MVarId_getType_x27(v_goal_2895_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_object* v_a_2908_; lean_object* v___x_2909_; 
v_a_2908_ = lean_ctor_get(v___x_2907_, 0);
lean_inc(v_a_2908_);
lean_dec_ref_known(v___x_2907_, 1);
v___x_2909_ = l_Lean_Expr_getAppFn(v_a_2908_);
lean_dec(v_a_2908_);
if (lean_obj_tag(v___x_2909_) == 4)
{
lean_object* v_declName_2910_; lean_object* v_us_2911_; lean_object* v___x_2912_; lean_object* v_env_2913_; uint8_t v___x_2914_; lean_object* v___x_2915_; 
v_declName_2910_ = lean_ctor_get(v___x_2909_, 0);
lean_inc(v_declName_2910_);
v_us_2911_ = lean_ctor_get(v___x_2909_, 1);
lean_inc(v_us_2911_);
lean_dec_ref_known(v___x_2909_, 2);
v___x_2912_ = lean_st_ref_get(v___y_2901_);
v_env_2913_ = lean_ctor_get(v___x_2912_, 0);
lean_inc_ref(v_env_2913_);
lean_dec(v___x_2912_);
v___x_2914_ = 0;
v___x_2915_ = l_Lean_Environment_find_x3f(v_env_2913_, v_declName_2910_, v___x_2914_);
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_dec(v_us_2911_);
lean_dec(v_expected_x3f_2897_);
lean_dec(v_idx_2896_);
goto v___jp_2903_;
}
else
{
lean_object* v_val_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2986_; 
v_val_2916_ = lean_ctor_get(v___x_2915_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2918_ = v___x_2915_;
v_isShared_2919_ = v_isSharedCheck_2986_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_val_2916_);
lean_dec(v___x_2915_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2986_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
if (lean_obj_tag(v_val_2916_) == 5)
{
lean_object* v_val_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2985_; 
v_val_2920_ = lean_ctor_get(v_val_2916_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v_val_2916_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2922_ = v_val_2916_;
v_isShared_2923_ = v_isSharedCheck_2985_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_val_2920_);
lean_dec(v_val_2916_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2985_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; 
if (lean_obj_tag(v_expected_x3f_2897_) == 1)
{
lean_object* v_val_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2984_; 
v_val_2955_ = lean_ctor_get(v_expected_x3f_2897_, 0);
v_isSharedCheck_2984_ = !lean_is_exclusive(v_expected_x3f_2897_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2957_ = v_expected_x3f_2897_;
v_isShared_2958_ = v_isSharedCheck_2984_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_val_2955_);
lean_dec(v_expected_x3f_2897_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2984_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v_ctors_2959_; lean_object* v___x_2960_; uint8_t v___x_2961_; 
v_ctors_2959_ = lean_ctor_get(v_val_2920_, 4);
v___x_2960_ = l_List_lengthTR___redArg(v_ctors_2959_);
v___x_2961_ = lean_nat_dec_eq(v___x_2960_, v_val_2955_);
lean_dec(v___x_2960_);
if (v___x_2961_ == 0)
{
uint8_t v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2973_; 
v___x_2962_ = 1;
lean_inc(v_name_2894_);
v___x_2963_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2894_, v___x_2962_);
v___x_2964_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__7));
v___x_2965_ = lean_string_append(v___x_2963_, v___x_2964_);
v___x_2966_ = l_Nat_reprFast(v_val_2955_);
v___x_2967_ = lean_string_append(v___x_2965_, v___x_2966_);
lean_dec_ref(v___x_2966_);
v___x_2968_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__6));
v___x_2969_ = lean_string_append(v___x_2967_, v___x_2968_);
v___x_2970_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2970_, 0, v___x_2969_);
v___x_2971_ = l_Lean_MessageData_ofFormat(v___x_2970_);
if (v_isShared_2958_ == 0)
{
lean_ctor_set(v___x_2957_, 0, v___x_2971_);
v___x_2973_ = v___x_2957_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v___x_2971_);
v___x_2973_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
lean_object* v___x_2974_; 
lean_inc(v_goal_2895_);
lean_inc(v_name_2894_);
v___x_2974_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2894_, v_goal_2895_, v___x_2973_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2974_) == 0)
{
lean_dec_ref_known(v___x_2974_, 1);
v___y_2925_ = v___y_2898_;
v___y_2926_ = v___y_2899_;
v___y_2927_ = v___y_2900_;
v___y_2928_ = v___y_2901_;
goto v___jp_2924_;
}
else
{
lean_object* v_a_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2982_; 
lean_del_object(v___x_2922_);
lean_dec_ref(v_val_2920_);
lean_del_object(v___x_2918_);
lean_dec(v_us_2911_);
lean_dec(v_idx_2896_);
lean_dec(v_goal_2895_);
lean_dec(v_name_2894_);
v_a_2975_ = lean_ctor_get(v___x_2974_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2977_ = v___x_2974_;
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_a_2975_);
lean_dec(v___x_2974_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2980_; 
if (v_isShared_2978_ == 0)
{
v___x_2980_ = v___x_2977_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_a_2975_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
}
}
else
{
lean_del_object(v___x_2957_);
lean_dec(v_val_2955_);
v___y_2925_ = v___y_2898_;
v___y_2926_ = v___y_2899_;
v___y_2927_ = v___y_2900_;
v___y_2928_ = v___y_2901_;
goto v___jp_2924_;
}
}
}
else
{
lean_dec(v_expected_x3f_2897_);
v___y_2925_ = v___y_2898_;
v___y_2926_ = v___y_2899_;
v___y_2927_ = v___y_2900_;
v___y_2928_ = v___y_2901_;
goto v___jp_2924_;
}
v___jp_2924_:
{
lean_object* v_ctors_2929_; lean_object* v___x_2930_; uint8_t v___x_2931_; 
v_ctors_2929_ = lean_ctor_get(v_val_2920_, 4);
lean_inc(v_ctors_2929_);
lean_dec_ref(v_val_2920_);
v___x_2930_ = l_List_lengthTR___redArg(v_ctors_2929_);
v___x_2931_ = lean_nat_dec_lt(v_idx_2896_, v___x_2930_);
if (v___x_2931_ == 0)
{
lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2942_; 
lean_dec(v_ctors_2929_);
lean_dec(v_us_2911_);
v___x_2932_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__4));
v___x_2933_ = l_Nat_reprFast(v_idx_2896_);
v___x_2934_ = lean_string_append(v___x_2932_, v___x_2933_);
lean_dec_ref(v___x_2933_);
v___x_2935_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__5));
v___x_2936_ = lean_string_append(v___x_2934_, v___x_2935_);
v___x_2937_ = l_Nat_reprFast(v___x_2930_);
v___x_2938_ = lean_string_append(v___x_2936_, v___x_2937_);
lean_dec_ref(v___x_2937_);
v___x_2939_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__6));
v___x_2940_ = lean_string_append(v___x_2938_, v___x_2939_);
if (v_isShared_2923_ == 0)
{
lean_ctor_set_tag(v___x_2922_, 3);
lean_ctor_set(v___x_2922_, 0, v___x_2940_);
v___x_2942_ = v___x_2922_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v___x_2940_);
v___x_2942_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
lean_object* v___x_2943_; lean_object* v___x_2945_; 
v___x_2943_ = l_Lean_MessageData_ofFormat(v___x_2942_);
if (v_isShared_2919_ == 0)
{
lean_ctor_set(v___x_2918_, 0, v___x_2943_);
v___x_2945_ = v___x_2918_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v___x_2943_);
v___x_2945_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
lean_object* v___x_2946_; 
v___x_2946_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2894_, v_goal_2895_, v___x_2945_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
return v___x_2946_;
}
}
}
else
{
lean_object* v___x_2949_; lean_object* v___x_2950_; uint8_t v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; 
lean_dec(v___x_2930_);
lean_del_object(v___x_2922_);
lean_del_object(v___x_2918_);
lean_dec(v_name_2894_);
v___x_2949_ = l_List_get___redArg(v_ctors_2929_, v_idx_2896_);
lean_dec(v_ctors_2929_);
v___x_2950_ = l_Lean_mkConst(v___x_2949_, v_us_2911_);
v___x_2951_ = 0;
v___x_2952_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_2952_, 0, v___x_2951_);
lean_ctor_set_uint8(v___x_2952_, 1, v___x_2931_);
lean_ctor_set_uint8(v___x_2952_, 2, v___x_2914_);
lean_ctor_set_uint8(v___x_2952_, 3, v___x_2931_);
v___x_2953_ = lean_box(0);
v___x_2954_ = l_Lean_MVarId_apply(v_goal_2895_, v___x_2950_, v___x_2952_, v___x_2953_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
return v___x_2954_;
}
}
}
}
else
{
lean_del_object(v___x_2918_);
lean_dec(v_val_2916_);
lean_dec(v_us_2911_);
lean_dec(v_expected_x3f_2897_);
lean_dec(v_idx_2896_);
goto v___jp_2903_;
}
}
}
}
else
{
lean_dec_ref(v___x_2909_);
lean_dec(v_expected_x3f_2897_);
lean_dec(v_idx_2896_);
goto v___jp_2903_;
}
}
else
{
lean_object* v_a_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_2994_; 
lean_dec(v_expected_x3f_2897_);
lean_dec(v_idx_2896_);
lean_dec(v_goal_2895_);
lean_dec(v_name_2894_);
v_a_2987_ = lean_ctor_get(v___x_2907_, 0);
v_isSharedCheck_2994_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2989_ = v___x_2907_;
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_a_2987_);
lean_dec(v___x_2907_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2992_; 
if (v_isShared_2990_ == 0)
{
v___x_2992_ = v___x_2989_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_a_2987_);
v___x_2992_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
return v___x_2992_;
}
}
}
}
else
{
lean_object* v_a_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3002_; 
lean_dec(v_expected_x3f_2897_);
lean_dec(v_idx_2896_);
lean_dec(v_goal_2895_);
lean_dec(v_name_2894_);
v_a_2995_ = lean_ctor_get(v___x_2906_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2906_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2997_ = v___x_2906_;
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_a_2995_);
lean_dec(v___x_2906_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_3000_; 
if (v_isShared_2998_ == 0)
{
v___x_3000_ = v___x_2997_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_a_2995_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
v___jp_2903_:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; 
v___x_2904_ = lean_obj_once(&l_Lean_MVarId_nthConstructor___lam__0___closed__3, &l_Lean_MVarId_nthConstructor___lam__0___closed__3_once, _init_l_Lean_MVarId_nthConstructor___lam__0___closed__3);
v___x_2905_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2894_, v_goal_2895_, v___x_2904_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
return v___x_2905_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___lam__0___boxed(lean_object* v_name_3003_, lean_object* v_goal_3004_, lean_object* v_idx_3005_, lean_object* v_expected_x3f_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_){
_start:
{
lean_object* v_res_3012_; 
v_res_3012_ = l_Lean_MVarId_nthConstructor___lam__0(v_name_3003_, v_goal_3004_, v_idx_3005_, v_expected_x3f_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3009_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
return v_res_3012_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor(lean_object* v_name_3013_, lean_object* v_idx_3014_, lean_object* v_expected_x3f_3015_, lean_object* v_goal_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_){
_start:
{
lean_object* v___f_3022_; lean_object* v___x_3023_; 
lean_inc(v_goal_3016_);
v___f_3022_ = lean_alloc_closure((void*)(l_Lean_MVarId_nthConstructor___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3022_, 0, v_name_3013_);
lean_closure_set(v___f_3022_, 1, v_goal_3016_);
lean_closure_set(v___f_3022_, 2, v_idx_3014_);
lean_closure_set(v___f_3022_, 3, v_expected_x3f_3015_);
v___x_3023_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_goal_3016_, v___f_3022_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_);
return v___x_3023_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___boxed(lean_object* v_name_3024_, lean_object* v_idx_3025_, lean_object* v_expected_x3f_3026_, lean_object* v_goal_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_){
_start:
{
lean_object* v_res_3033_; 
v_res_3033_ = l_Lean_MVarId_nthConstructor(v_name_3024_, v_idx_3025_, v_expected_x3f_3026_, v_goal_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_);
lean_dec(v_a_3031_);
lean_dec_ref(v_a_3030_);
lean_dec(v_a_3029_);
lean_dec_ref(v_a_3028_);
return v_res_3033_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(lean_object* v_x_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_){
_start:
{
lean_object* v___x_3040_; 
v___x_3040_ = l_Lean_Meta_saveState___redArg(v___y_3036_, v___y_3038_);
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_object* v_a_3041_; lean_object* v___x_3042_; 
v_a_3041_ = lean_ctor_get(v___x_3040_, 0);
lean_inc(v_a_3041_);
lean_dec_ref_known(v___x_3040_, 1);
lean_inc(v___y_3038_);
lean_inc_ref(v___y_3037_);
lean_inc(v___y_3036_);
lean_inc_ref(v___y_3035_);
v___x_3042_ = lean_apply_5(v_x_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, lean_box(0));
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3051_; 
lean_dec(v_a_3041_);
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3045_ = v___x_3042_;
v_isShared_3046_ = v_isSharedCheck_3051_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_3042_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3051_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3047_; lean_object* v___x_3049_; 
v___x_3047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3047_, 0, v_a_3043_);
if (v_isShared_3046_ == 0)
{
lean_ctor_set(v___x_3045_, 0, v___x_3047_);
v___x_3049_ = v___x_3045_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v___x_3047_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
else
{
lean_object* v_a_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3082_; 
v_a_3052_ = lean_ctor_get(v___x_3042_, 0);
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3054_ = v___x_3042_;
v_isShared_3055_ = v_isSharedCheck_3082_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_a_3052_);
lean_dec(v___x_3042_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3082_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
uint8_t v___x_3056_; 
v___x_3056_ = l_Lean_Exception_isInterrupt(v_a_3052_);
if (v___x_3056_ == 0)
{
uint8_t v___x_3057_; 
lean_inc(v_a_3052_);
v___x_3057_ = l_Lean_Exception_isRuntime(v_a_3052_);
if (v___x_3057_ == 0)
{
lean_object* v___x_3058_; 
lean_del_object(v___x_3054_);
lean_dec(v_a_3052_);
v___x_3058_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3041_, v___y_3036_, v___y_3038_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3066_; 
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3066_ == 0)
{
lean_object* v_unused_3067_; 
v_unused_3067_ = lean_ctor_get(v___x_3058_, 0);
lean_dec(v_unused_3067_);
v___x_3060_ = v___x_3058_;
v_isShared_3061_ = v_isSharedCheck_3066_;
goto v_resetjp_3059_;
}
else
{
lean_dec(v___x_3058_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3066_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3062_; lean_object* v___x_3064_; 
v___x_3062_ = lean_box(0);
if (v_isShared_3061_ == 0)
{
lean_ctor_set(v___x_3060_, 0, v___x_3062_);
v___x_3064_ = v___x_3060_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v___x_3062_);
v___x_3064_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
return v___x_3064_;
}
}
}
else
{
lean_object* v_a_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3075_; 
v_a_3068_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3070_ = v___x_3058_;
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_a_3068_);
lean_dec(v___x_3058_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3073_; 
if (v_isShared_3071_ == 0)
{
v___x_3073_ = v___x_3070_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_a_3068_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
}
else
{
lean_object* v___x_3077_; 
lean_dec(v_a_3041_);
if (v_isShared_3055_ == 0)
{
v___x_3077_ = v___x_3054_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v_a_3052_);
v___x_3077_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
return v___x_3077_;
}
}
}
else
{
lean_object* v___x_3080_; 
lean_dec(v_a_3041_);
if (v_isShared_3055_ == 0)
{
v___x_3080_ = v___x_3054_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_a_3052_);
v___x_3080_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
return v___x_3080_;
}
}
}
}
}
else
{
lean_object* v_a_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3090_; 
lean_dec_ref(v_x_3034_);
v_a_3083_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3085_ = v___x_3040_;
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_a_3083_);
lean_dec(v___x_3040_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3088_; 
if (v_isShared_3086_ == 0)
{
v___x_3088_ = v___x_3085_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_a_3083_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg___boxed(lean_object* v_x_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_){
_start:
{
lean_object* v_res_3097_; 
v_res_3097_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v_x_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_);
lean_dec(v___y_3095_);
lean_dec_ref(v___y_3094_);
lean_dec(v___y_3093_);
lean_dec_ref(v___y_3092_);
return v_res_3097_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0(lean_object* v_00_u03b1_3098_, lean_object* v_x_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_){
_start:
{
lean_object* v___x_3105_; 
v___x_3105_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v_x_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_);
return v___x_3105_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___boxed(lean_object* v_00_u03b1_3106_, lean_object* v_x_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_){
_start:
{
lean_object* v_res_3113_; 
v_res_3113_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0(v_00_u03b1_3106_, v_x_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
return v_res_3113_;
}
}
static lean_object* _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3115_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___lam__0___closed__0));
v___x_3116_ = l_Lean_stringToMessageData(v___x_3115_);
return v___x_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___lam__0(lean_object* v_mvarId_3117_, lean_object* v___x_3118_, lean_object* v___x_3119_, lean_object* v___x_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_){
_start:
{
lean_object* v___x_3129_; 
v___x_3129_ = l_Lean_MVarId_apply(v_mvarId_3117_, v___x_3118_, v___x_3119_, v___x_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_);
if (lean_obj_tag(v___x_3129_) == 0)
{
lean_object* v_a_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3139_; 
v_a_3130_ = lean_ctor_get(v___x_3129_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3129_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3132_ = v___x_3129_;
v_isShared_3133_ = v_isSharedCheck_3139_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_a_3130_);
lean_dec(v___x_3129_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3139_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
if (lean_obj_tag(v_a_3130_) == 1)
{
lean_object* v_tail_3134_; 
v_tail_3134_ = lean_ctor_get(v_a_3130_, 1);
if (lean_obj_tag(v_tail_3134_) == 0)
{
lean_object* v_head_3135_; lean_object* v___x_3137_; 
v_head_3135_ = lean_ctor_get(v_a_3130_, 0);
lean_inc(v_head_3135_);
lean_dec_ref_known(v_a_3130_, 2);
if (v_isShared_3133_ == 0)
{
lean_ctor_set(v___x_3132_, 0, v_head_3135_);
v___x_3137_ = v___x_3132_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_head_3135_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
return v___x_3137_;
}
}
else
{
lean_dec_ref_known(v_a_3130_, 2);
lean_del_object(v___x_3132_);
goto v___jp_3126_;
}
}
else
{
lean_del_object(v___x_3132_);
lean_dec(v_a_3130_);
goto v___jp_3126_;
}
}
}
else
{
lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3147_; 
v_a_3140_ = lean_ctor_get(v___x_3129_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3129_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3142_ = v___x_3129_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_3129_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3145_; 
if (v_isShared_3143_ == 0)
{
v___x_3145_ = v___x_3142_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_a_3140_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
v___jp_3126_:
{
lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3127_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3128_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3127_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_);
return v___x_3128_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___lam__0___boxed(lean_object* v_mvarId_3148_, lean_object* v___x_3149_, lean_object* v___x_3150_, lean_object* v___x_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_){
_start:
{
lean_object* v_res_3157_; 
v_res_3157_ = l_Lean_MVarId_iffOfEq___lam__0(v_mvarId_3148_, v___x_3149_, v___x_3150_, v___x_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
return v_res_3157_;
}
}
static lean_object* _init_l_Lean_MVarId_iffOfEq___closed__2(void){
_start:
{
lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3161_ = lean_box(0);
v___x_3162_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___closed__1));
v___x_3163_ = l_Lean_mkConst(v___x_3162_, v___x_3161_);
return v___x_3163_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq(lean_object* v_mvarId_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_){
_start:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___f_3177_; lean_object* v___x_3178_; 
v___x_3174_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___closed__2, &l_Lean_MVarId_iffOfEq___closed__2_once, _init_l_Lean_MVarId_iffOfEq___closed__2);
v___x_3175_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___closed__3));
v___x_3176_ = lean_box(0);
lean_inc(v_mvarId_3168_);
v___f_3177_ = lean_alloc_closure((void*)(l_Lean_MVarId_iffOfEq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3177_, 0, v_mvarId_3168_);
lean_closure_set(v___f_3177_, 1, v___x_3174_);
lean_closure_set(v___f_3177_, 2, v___x_3175_);
lean_closure_set(v___f_3177_, 3, v___x_3176_);
v___x_3178_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3177_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_);
if (lean_obj_tag(v___x_3178_) == 0)
{
lean_object* v_a_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3190_; 
v_a_3179_ = lean_ctor_get(v___x_3178_, 0);
v_isSharedCheck_3190_ = !lean_is_exclusive(v___x_3178_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3181_ = v___x_3178_;
v_isShared_3182_ = v_isSharedCheck_3190_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_a_3179_);
lean_dec(v___x_3178_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3190_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
if (lean_obj_tag(v_a_3179_) == 0)
{
lean_object* v___x_3184_; 
if (v_isShared_3182_ == 0)
{
lean_ctor_set(v___x_3181_, 0, v_mvarId_3168_);
v___x_3184_ = v___x_3181_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_mvarId_3168_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
}
}
else
{
lean_object* v_val_3186_; lean_object* v___x_3188_; 
lean_dec(v_mvarId_3168_);
v_val_3186_ = lean_ctor_get(v_a_3179_, 0);
lean_inc(v_val_3186_);
lean_dec_ref_known(v_a_3179_, 1);
if (v_isShared_3182_ == 0)
{
lean_ctor_set(v___x_3181_, 0, v_val_3186_);
v___x_3188_ = v___x_3181_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_val_3186_);
v___x_3188_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
return v___x_3188_;
}
}
}
}
else
{
lean_object* v_a_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3198_; 
lean_dec(v_mvarId_3168_);
v_a_3191_ = lean_ctor_get(v___x_3178_, 0);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3178_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3193_ = v___x_3178_;
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_a_3191_);
lean_dec(v___x_3178_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3196_; 
if (v_isShared_3194_ == 0)
{
v___x_3196_ = v___x_3193_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_a_3191_);
v___x_3196_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
return v___x_3196_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___boxed(lean_object* v_mvarId_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_){
_start:
{
lean_object* v_res_3205_; 
v_res_3205_ = l_Lean_MVarId_iffOfEq(v_mvarId_3199_, v_a_3200_, v_a_3201_, v_a_3202_, v_a_3203_);
lean_dec(v_a_3203_);
lean_dec_ref(v_a_3202_);
lean_dec(v_a_3201_);
lean_dec_ref(v_a_3200_);
return v_res_3205_;
}
}
static lean_object* _init_l_Lean_MVarId_propext___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; 
v___x_3209_ = lean_box(0);
v___x_3210_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__1));
v___x_3211_ = l_Lean_mkConst(v___x_3210_, v___x_3209_);
return v___x_3211_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___lam__0(lean_object* v_mvarId_3215_, uint8_t v___x_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_){
_start:
{
lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; uint8_t v___y_3230_; lean_object* v___y_3256_; lean_object* v___x_3294_; uint8_t v_transparency_3295_; uint8_t v___x_3296_; 
v___x_3294_ = l_Lean_Meta_Context_config(v___y_3217_);
v_transparency_3295_ = lean_ctor_get_uint8(v___x_3294_, 9);
lean_dec_ref(v___x_3294_);
v___x_3296_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3295_, v___x_3216_);
if (v___x_3296_ == 0)
{
lean_object* v_keyedConfig_3297_; uint8_t v_trackZetaDelta_3298_; lean_object* v_zetaDeltaSet_3299_; lean_object* v_lctx_3300_; lean_object* v_localInstances_3301_; lean_object* v_defEqCtx_x3f_3302_; lean_object* v_synthPendingDepth_3303_; lean_object* v_customCanUnfoldPredicate_x3f_3304_; uint8_t v_univApprox_3305_; uint8_t v_inTypeClassResolution_3306_; uint8_t v_cacheInferType_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; 
v_keyedConfig_3297_ = lean_ctor_get(v___y_3217_, 0);
v_trackZetaDelta_3298_ = lean_ctor_get_uint8(v___y_3217_, sizeof(void*)*7);
v_zetaDeltaSet_3299_ = lean_ctor_get(v___y_3217_, 1);
v_lctx_3300_ = lean_ctor_get(v___y_3217_, 2);
v_localInstances_3301_ = lean_ctor_get(v___y_3217_, 3);
v_defEqCtx_x3f_3302_ = lean_ctor_get(v___y_3217_, 4);
v_synthPendingDepth_3303_ = lean_ctor_get(v___y_3217_, 5);
v_customCanUnfoldPredicate_x3f_3304_ = lean_ctor_get(v___y_3217_, 6);
v_univApprox_3305_ = lean_ctor_get_uint8(v___y_3217_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3306_ = lean_ctor_get_uint8(v___y_3217_, sizeof(void*)*7 + 2);
v_cacheInferType_3307_ = lean_ctor_get_uint8(v___y_3217_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3297_);
v___x_3308_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3216_, v_keyedConfig_3297_);
lean_inc(v_customCanUnfoldPredicate_x3f_3304_);
lean_inc(v_synthPendingDepth_3303_);
lean_inc(v_defEqCtx_x3f_3302_);
lean_inc_ref(v_localInstances_3301_);
lean_inc_ref(v_lctx_3300_);
lean_inc(v_zetaDeltaSet_3299_);
v___x_3309_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3309_, 0, v___x_3308_);
lean_ctor_set(v___x_3309_, 1, v_zetaDeltaSet_3299_);
lean_ctor_set(v___x_3309_, 2, v_lctx_3300_);
lean_ctor_set(v___x_3309_, 3, v_localInstances_3301_);
lean_ctor_set(v___x_3309_, 4, v_defEqCtx_x3f_3302_);
lean_ctor_set(v___x_3309_, 5, v_synthPendingDepth_3303_);
lean_ctor_set(v___x_3309_, 6, v_customCanUnfoldPredicate_x3f_3304_);
lean_ctor_set_uint8(v___x_3309_, sizeof(void*)*7, v_trackZetaDelta_3298_);
lean_ctor_set_uint8(v___x_3309_, sizeof(void*)*7 + 1, v_univApprox_3305_);
lean_ctor_set_uint8(v___x_3309_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3306_);
lean_ctor_set_uint8(v___x_3309_, sizeof(void*)*7 + 3, v_cacheInferType_3307_);
lean_inc(v_mvarId_3215_);
v___x_3310_ = l_Lean_MVarId_getType_x27(v_mvarId_3215_, v___x_3309_, v___y_3218_, v___y_3219_, v___y_3220_);
lean_dec_ref_known(v___x_3309_, 7);
v___y_3256_ = v___x_3310_;
goto v___jp_3255_;
}
else
{
lean_object* v___x_3311_; 
lean_inc(v_mvarId_3215_);
v___x_3311_ = l_Lean_MVarId_getType_x27(v_mvarId_3215_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_);
v___y_3256_ = v___x_3311_;
goto v___jp_3255_;
}
v___jp_3222_:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3227_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3228_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3227_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
lean_dec_ref(v___y_3223_);
return v___x_3228_;
}
v___jp_3229_:
{
lean_object* v___x_3231_; uint8_t v___x_3232_; uint8_t v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3231_ = lean_obj_once(&l_Lean_MVarId_propext___lam__0___closed__2, &l_Lean_MVarId_propext___lam__0___closed__2_once, _init_l_Lean_MVarId_propext___lam__0___closed__2);
v___x_3232_ = 0;
v___x_3233_ = 0;
v___x_3234_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3234_, 0, v___x_3232_);
lean_ctor_set_uint8(v___x_3234_, 1, v___y_3230_);
lean_ctor_set_uint8(v___x_3234_, 2, v___x_3233_);
lean_ctor_set_uint8(v___x_3234_, 3, v___y_3230_);
v___x_3235_ = lean_box(0);
v___x_3236_ = l_Lean_MVarId_apply(v_mvarId_3215_, v___x_3231_, v___x_3234_, v___x_3235_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_);
if (lean_obj_tag(v___x_3236_) == 0)
{
lean_object* v_a_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3246_; 
v_a_3237_ = lean_ctor_get(v___x_3236_, 0);
v_isSharedCheck_3246_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3246_ == 0)
{
v___x_3239_ = v___x_3236_;
v_isShared_3240_ = v_isSharedCheck_3246_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_a_3237_);
lean_dec(v___x_3236_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3246_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
if (lean_obj_tag(v_a_3237_) == 1)
{
lean_object* v_tail_3241_; 
v_tail_3241_ = lean_ctor_get(v_a_3237_, 1);
if (lean_obj_tag(v_tail_3241_) == 0)
{
lean_object* v_head_3242_; lean_object* v___x_3244_; 
lean_dec_ref(v___y_3217_);
v_head_3242_ = lean_ctor_get(v_a_3237_, 0);
lean_inc(v_head_3242_);
lean_dec_ref_known(v_a_3237_, 2);
if (v_isShared_3240_ == 0)
{
lean_ctor_set(v___x_3239_, 0, v_head_3242_);
v___x_3244_ = v___x_3239_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v_head_3242_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
else
{
lean_dec_ref_known(v_a_3237_, 2);
lean_del_object(v___x_3239_);
v___y_3223_ = v___y_3217_;
v___y_3224_ = v___y_3218_;
v___y_3225_ = v___y_3219_;
v___y_3226_ = v___y_3220_;
goto v___jp_3222_;
}
}
else
{
lean_del_object(v___x_3239_);
lean_dec(v_a_3237_);
v___y_3223_ = v___y_3217_;
v___y_3224_ = v___y_3218_;
v___y_3225_ = v___y_3219_;
v___y_3226_ = v___y_3220_;
goto v___jp_3222_;
}
}
}
else
{
lean_object* v_a_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3254_; 
lean_dec_ref(v___y_3217_);
v_a_3247_ = lean_ctor_get(v___x_3236_, 0);
v_isSharedCheck_3254_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3254_ == 0)
{
v___x_3249_ = v___x_3236_;
v_isShared_3250_ = v_isSharedCheck_3254_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_a_3247_);
lean_dec(v___x_3236_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3254_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3252_; 
if (v_isShared_3250_ == 0)
{
v___x_3252_ = v___x_3249_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_a_3247_);
v___x_3252_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
return v___x_3252_;
}
}
}
}
v___jp_3255_:
{
if (lean_obj_tag(v___y_3256_) == 0)
{
lean_object* v_a_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; uint8_t v___x_3260_; 
v_a_3257_ = lean_ctor_get(v___y_3256_, 0);
lean_inc(v_a_3257_);
lean_dec_ref_known(v___y_3256_, 1);
v___x_3258_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__4));
v___x_3259_ = lean_unsigned_to_nat(3u);
v___x_3260_ = l_Lean_Expr_isAppOfArity(v_a_3257_, v___x_3258_, v___x_3259_);
if (v___x_3260_ == 0)
{
lean_object* v___x_3261_; lean_object* v___x_3262_; 
lean_dec(v_a_3257_);
lean_dec(v_mvarId_3215_);
v___x_3261_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3262_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3261_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_);
lean_dec_ref(v___y_3217_);
return v___x_3262_;
}
else
{
lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; 
v___x_3263_ = l_Lean_Expr_appFn_x21(v_a_3257_);
lean_dec(v_a_3257_);
v___x_3264_ = l_Lean_Expr_appArg_x21(v___x_3263_);
lean_dec_ref(v___x_3263_);
v___x_3265_ = l_Lean_Meta_isProp(v___x_3264_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_);
if (lean_obj_tag(v___x_3265_) == 0)
{
lean_object* v_a_3266_; uint8_t v___x_3267_; 
v_a_3266_ = lean_ctor_get(v___x_3265_, 0);
lean_inc(v_a_3266_);
lean_dec_ref_known(v___x_3265_, 1);
v___x_3267_ = lean_unbox(v_a_3266_);
lean_dec(v_a_3266_);
if (v___x_3267_ == 0)
{
lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v_a_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3277_; 
lean_dec(v_mvarId_3215_);
v___x_3268_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3269_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3268_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_);
lean_dec_ref(v___y_3217_);
v_a_3270_ = lean_ctor_get(v___x_3269_, 0);
v_isSharedCheck_3277_ = !lean_is_exclusive(v___x_3269_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3272_ = v___x_3269_;
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_a_3270_);
lean_dec(v___x_3269_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v___x_3275_; 
if (v_isShared_3273_ == 0)
{
v___x_3275_ = v___x_3272_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_a_3270_);
v___x_3275_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
return v___x_3275_;
}
}
}
else
{
v___y_3230_ = v___x_3260_;
goto v___jp_3229_;
}
}
else
{
lean_object* v_a_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3285_; 
lean_dec_ref(v___y_3217_);
lean_dec(v_mvarId_3215_);
v_a_3278_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3285_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3285_ == 0)
{
v___x_3280_ = v___x_3265_;
v_isShared_3281_ = v_isSharedCheck_3285_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_a_3278_);
lean_dec(v___x_3265_);
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
}
else
{
lean_object* v_a_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3293_; 
lean_dec_ref(v___y_3217_);
lean_dec(v_mvarId_3215_);
v_a_3286_ = lean_ctor_get(v___y_3256_, 0);
v_isSharedCheck_3293_ = !lean_is_exclusive(v___y_3256_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3288_ = v___y_3256_;
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_a_3286_);
lean_dec(v___y_3256_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v___x_3291_; 
if (v_isShared_3289_ == 0)
{
v___x_3291_ = v___x_3288_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v_a_3286_);
v___x_3291_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
return v___x_3291_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___lam__0___boxed(lean_object* v_mvarId_3312_, lean_object* v___x_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_){
_start:
{
uint8_t v___x_2525__boxed_3319_; lean_object* v_res_3320_; 
v___x_2525__boxed_3319_ = lean_unbox(v___x_3313_);
v_res_3320_ = l_Lean_MVarId_propext___lam__0(v_mvarId_3312_, v___x_2525__boxed_3319_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_);
lean_dec(v___y_3317_);
lean_dec_ref(v___y_3316_);
lean_dec(v___y_3315_);
return v_res_3320_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext(lean_object* v_mvarId_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_){
_start:
{
uint8_t v___x_3327_; lean_object* v___x_3328_; lean_object* v___f_3329_; lean_object* v___x_3330_; 
v___x_3327_ = 2;
v___x_3328_ = lean_box(v___x_3327_);
lean_inc(v_mvarId_3321_);
v___f_3329_ = lean_alloc_closure((void*)(l_Lean_MVarId_propext___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3329_, 0, v_mvarId_3321_);
lean_closure_set(v___f_3329_, 1, v___x_3328_);
v___x_3330_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3329_, v_a_3322_, v_a_3323_, v_a_3324_, v_a_3325_);
if (lean_obj_tag(v___x_3330_) == 0)
{
lean_object* v_a_3331_; lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3342_; 
v_a_3331_ = lean_ctor_get(v___x_3330_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3330_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3333_ = v___x_3330_;
v_isShared_3334_ = v_isSharedCheck_3342_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_a_3331_);
lean_dec(v___x_3330_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3342_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
if (lean_obj_tag(v_a_3331_) == 0)
{
lean_object* v___x_3336_; 
if (v_isShared_3334_ == 0)
{
lean_ctor_set(v___x_3333_, 0, v_mvarId_3321_);
v___x_3336_ = v___x_3333_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v_mvarId_3321_);
v___x_3336_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
return v___x_3336_;
}
}
else
{
lean_object* v_val_3338_; lean_object* v___x_3340_; 
lean_dec(v_mvarId_3321_);
v_val_3338_ = lean_ctor_get(v_a_3331_, 0);
lean_inc(v_val_3338_);
lean_dec_ref_known(v_a_3331_, 1);
if (v_isShared_3334_ == 0)
{
lean_ctor_set(v___x_3333_, 0, v_val_3338_);
v___x_3340_ = v___x_3333_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_val_3338_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
return v___x_3340_;
}
}
}
}
else
{
lean_object* v_a_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3350_; 
lean_dec(v_mvarId_3321_);
v_a_3343_ = lean_ctor_get(v___x_3330_, 0);
v_isSharedCheck_3350_ = !lean_is_exclusive(v___x_3330_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3345_ = v___x_3330_;
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_a_3343_);
lean_dec(v___x_3330_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3348_; 
if (v_isShared_3346_ == 0)
{
v___x_3348_ = v___x_3345_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_a_3343_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___boxed(lean_object* v_mvarId_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_){
_start:
{
lean_object* v_res_3357_; 
v_res_3357_ = l_Lean_MVarId_propext(v_mvarId_3351_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_);
lean_dec(v_a_3355_);
lean_dec_ref(v_a_3354_);
lean_dec(v_a_3353_);
lean_dec_ref(v_a_3352_);
return v_res_3357_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0(lean_object* v_mvarId_3364_, lean_object* v___x_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_){
_start:
{
lean_object* v___y_3372_; lean_object* v___x_3416_; 
lean_inc(v_mvarId_3364_);
v___x_3416_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3364_, v___x_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_);
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v___x_3417_; uint8_t v_transparency_3418_; uint8_t v___x_3419_; uint8_t v___x_3420_; 
lean_dec_ref_known(v___x_3416_, 1);
v___x_3417_ = l_Lean_Meta_Context_config(v___y_3366_);
v_transparency_3418_ = lean_ctor_get_uint8(v___x_3417_, 9);
lean_dec_ref(v___x_3417_);
v___x_3419_ = 2;
v___x_3420_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3418_, v___x_3419_);
if (v___x_3420_ == 0)
{
lean_object* v_keyedConfig_3421_; uint8_t v_trackZetaDelta_3422_; lean_object* v_zetaDeltaSet_3423_; lean_object* v_lctx_3424_; lean_object* v_localInstances_3425_; lean_object* v_defEqCtx_x3f_3426_; lean_object* v_synthPendingDepth_3427_; lean_object* v_customCanUnfoldPredicate_x3f_3428_; uint8_t v_univApprox_3429_; uint8_t v_inTypeClassResolution_3430_; uint8_t v_cacheInferType_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; 
v_keyedConfig_3421_ = lean_ctor_get(v___y_3366_, 0);
v_trackZetaDelta_3422_ = lean_ctor_get_uint8(v___y_3366_, sizeof(void*)*7);
v_zetaDeltaSet_3423_ = lean_ctor_get(v___y_3366_, 1);
v_lctx_3424_ = lean_ctor_get(v___y_3366_, 2);
v_localInstances_3425_ = lean_ctor_get(v___y_3366_, 3);
v_defEqCtx_x3f_3426_ = lean_ctor_get(v___y_3366_, 4);
v_synthPendingDepth_3427_ = lean_ctor_get(v___y_3366_, 5);
v_customCanUnfoldPredicate_x3f_3428_ = lean_ctor_get(v___y_3366_, 6);
v_univApprox_3429_ = lean_ctor_get_uint8(v___y_3366_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3430_ = lean_ctor_get_uint8(v___y_3366_, sizeof(void*)*7 + 2);
v_cacheInferType_3431_ = lean_ctor_get_uint8(v___y_3366_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3421_);
v___x_3432_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3419_, v_keyedConfig_3421_);
lean_inc(v_customCanUnfoldPredicate_x3f_3428_);
lean_inc(v_synthPendingDepth_3427_);
lean_inc(v_defEqCtx_x3f_3426_);
lean_inc_ref(v_localInstances_3425_);
lean_inc_ref(v_lctx_3424_);
lean_inc(v_zetaDeltaSet_3423_);
v___x_3433_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3433_, 0, v___x_3432_);
lean_ctor_set(v___x_3433_, 1, v_zetaDeltaSet_3423_);
lean_ctor_set(v___x_3433_, 2, v_lctx_3424_);
lean_ctor_set(v___x_3433_, 3, v_localInstances_3425_);
lean_ctor_set(v___x_3433_, 4, v_defEqCtx_x3f_3426_);
lean_ctor_set(v___x_3433_, 5, v_synthPendingDepth_3427_);
lean_ctor_set(v___x_3433_, 6, v_customCanUnfoldPredicate_x3f_3428_);
lean_ctor_set_uint8(v___x_3433_, sizeof(void*)*7, v_trackZetaDelta_3422_);
lean_ctor_set_uint8(v___x_3433_, sizeof(void*)*7 + 1, v_univApprox_3429_);
lean_ctor_set_uint8(v___x_3433_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3430_);
lean_ctor_set_uint8(v___x_3433_, sizeof(void*)*7 + 3, v_cacheInferType_3431_);
lean_inc(v_mvarId_3364_);
v___x_3434_ = l_Lean_MVarId_getType_x27(v_mvarId_3364_, v___x_3433_, v___y_3367_, v___y_3368_, v___y_3369_);
lean_dec_ref_known(v___x_3433_, 7);
v___y_3372_ = v___x_3434_;
goto v___jp_3371_;
}
else
{
lean_object* v___x_3435_; 
lean_inc(v_mvarId_3364_);
v___x_3435_ = l_Lean_MVarId_getType_x27(v_mvarId_3364_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_);
v___y_3372_ = v___x_3435_;
goto v___jp_3371_;
}
}
else
{
lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3443_; 
lean_dec_ref(v___y_3366_);
lean_dec(v_mvarId_3364_);
v_a_3436_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3438_ = v___x_3416_;
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_dec(v___x_3416_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3441_; 
if (v_isShared_3439_ == 0)
{
v___x_3441_ = v___x_3438_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_a_3436_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
return v___x_3441_;
}
}
}
v___jp_3371_:
{
if (lean_obj_tag(v___y_3372_) == 0)
{
lean_object* v_a_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; uint8_t v___x_3376_; 
v_a_3373_ = lean_ctor_get(v___y_3372_, 0);
lean_inc(v_a_3373_);
lean_dec_ref_known(v___y_3372_, 1);
v___x_3374_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__1));
v___x_3375_ = lean_unsigned_to_nat(4u);
v___x_3376_ = l_Lean_Expr_isAppOfArity(v_a_3373_, v___x_3374_, v___x_3375_);
if (v___x_3376_ == 0)
{
lean_object* v___x_3377_; lean_object* v___x_3378_; 
lean_dec(v_a_3373_);
lean_dec(v_mvarId_3364_);
v___x_3377_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3378_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3377_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_);
lean_dec_ref(v___y_3366_);
return v___x_3378_;
}
else
{
lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___x_3379_ = l_Lean_Expr_appFn_x21(v_a_3373_);
v___x_3380_ = l_Lean_Expr_appFn_x21(v___x_3379_);
lean_dec_ref(v___x_3379_);
v___x_3381_ = l_Lean_Expr_appArg_x21(v___x_3380_);
lean_dec_ref(v___x_3380_);
v___x_3382_ = l_Lean_Expr_appArg_x21(v_a_3373_);
lean_dec(v_a_3373_);
v___x_3383_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__3));
v___x_3384_ = lean_unsigned_to_nat(2u);
v___x_3385_ = lean_mk_empty_array_with_capacity(v___x_3384_);
v___x_3386_ = lean_array_push(v___x_3385_, v___x_3381_);
v___x_3387_ = lean_array_push(v___x_3386_, v___x_3382_);
v___x_3388_ = l_Lean_Meta_mkAppM(v___x_3383_, v___x_3387_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_);
lean_dec_ref(v___y_3366_);
if (lean_obj_tag(v___x_3388_) == 0)
{
lean_object* v_a_3389_; lean_object* v___x_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3398_; 
v_a_3389_ = lean_ctor_get(v___x_3388_, 0);
lean_inc(v_a_3389_);
lean_dec_ref_known(v___x_3388_, 1);
v___x_3390_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_3364_, v_a_3389_, v___y_3367_);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3390_);
if (v_isSharedCheck_3398_ == 0)
{
lean_object* v_unused_3399_; 
v_unused_3399_ = lean_ctor_get(v___x_3390_, 0);
lean_dec(v_unused_3399_);
v___x_3392_ = v___x_3390_;
v_isShared_3393_ = v_isSharedCheck_3398_;
goto v_resetjp_3391_;
}
else
{
lean_dec(v___x_3390_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3398_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v___x_3394_; lean_object* v___x_3396_; 
v___x_3394_ = lean_box(v___x_3376_);
if (v_isShared_3393_ == 0)
{
lean_ctor_set(v___x_3392_, 0, v___x_3394_);
v___x_3396_ = v___x_3392_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v___x_3394_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
}
}
}
else
{
lean_object* v_a_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3407_; 
lean_dec(v_mvarId_3364_);
v_a_3400_ = lean_ctor_get(v___x_3388_, 0);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3402_ = v___x_3388_;
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_a_3400_);
lean_dec(v___x_3388_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3405_; 
if (v_isShared_3403_ == 0)
{
v___x_3405_ = v___x_3402_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_a_3400_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
}
}
else
{
lean_object* v_a_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3415_; 
lean_dec_ref(v___y_3366_);
lean_dec(v_mvarId_3364_);
v_a_3408_ = lean_ctor_get(v___y_3372_, 0);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___y_3372_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3410_ = v___y_3372_;
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_a_3408_);
lean_dec(v___y_3372_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3413_; 
if (v_isShared_3411_ == 0)
{
v___x_3413_ = v___x_3410_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_a_3408_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
return v___x_3413_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0___boxed(lean_object* v_mvarId_3444_, lean_object* v___x_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_){
_start:
{
lean_object* v_res_3451_; 
v_res_3451_ = l_Lean_MVarId_proofIrrelHeq___lam__0(v_mvarId_3444_, v___x_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_);
lean_dec(v___y_3449_);
lean_dec_ref(v___y_3448_);
lean_dec(v___y_3447_);
return v_res_3451_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__1(lean_object* v___f_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_){
_start:
{
lean_object* v___x_3458_; 
v___x_3458_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
if (lean_obj_tag(v___x_3458_) == 0)
{
lean_object* v_a_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3472_; 
v_a_3459_ = lean_ctor_get(v___x_3458_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3461_ = v___x_3458_;
v_isShared_3462_ = v_isSharedCheck_3472_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_a_3459_);
lean_dec(v___x_3458_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3472_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
if (lean_obj_tag(v_a_3459_) == 0)
{
uint8_t v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3466_; 
v___x_3463_ = 0;
v___x_3464_ = lean_box(v___x_3463_);
if (v_isShared_3462_ == 0)
{
lean_ctor_set(v___x_3461_, 0, v___x_3464_);
v___x_3466_ = v___x_3461_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v___x_3464_);
v___x_3466_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
return v___x_3466_;
}
}
else
{
lean_object* v_val_3468_; lean_object* v___x_3470_; 
v_val_3468_ = lean_ctor_get(v_a_3459_, 0);
lean_inc(v_val_3468_);
lean_dec_ref_known(v_a_3459_, 1);
if (v_isShared_3462_ == 0)
{
lean_ctor_set(v___x_3461_, 0, v_val_3468_);
v___x_3470_ = v___x_3461_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_val_3468_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
}
}
}
}
else
{
lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3480_; 
v_a_3473_ = lean_ctor_get(v___x_3458_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3475_ = v___x_3458_;
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3458_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3478_; 
if (v_isShared_3476_ == 0)
{
v___x_3478_ = v___x_3475_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3473_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__1___boxed(lean_object* v___f_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_){
_start:
{
lean_object* v_res_3487_; 
v_res_3487_ = l_Lean_MVarId_proofIrrelHeq___lam__1(v___f_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
return v_res_3487_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq(lean_object* v_mvarId_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_){
_start:
{
lean_object* v___x_3497_; lean_object* v___f_3498_; lean_object* v___f_3499_; lean_object* v___x_3500_; 
v___x_3497_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___closed__1));
lean_inc(v_mvarId_3491_);
v___f_3498_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3498_, 0, v_mvarId_3491_);
lean_closure_set(v___f_3498_, 1, v___x_3497_);
v___f_3499_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__1___boxed), 6, 1);
lean_closure_set(v___f_3499_, 0, v___f_3498_);
v___x_3500_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_3491_, v___f_3499_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_);
return v___x_3500_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___boxed(lean_object* v_mvarId_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_){
_start:
{
lean_object* v_res_3507_; 
v_res_3507_ = l_Lean_MVarId_proofIrrelHeq(v_mvarId_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_);
lean_dec(v_a_3505_);
lean_dec_ref(v_a_3504_);
lean_dec(v_a_3503_);
lean_dec_ref(v_a_3502_);
return v_res_3507_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___lam__0(lean_object* v_mvarId_3512_, lean_object* v___x_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_){
_start:
{
lean_object* v___y_3520_; lean_object* v___x_3563_; 
lean_inc(v_mvarId_3512_);
v___x_3563_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3512_, v___x_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_);
if (lean_obj_tag(v___x_3563_) == 0)
{
lean_object* v___x_3564_; uint8_t v_transparency_3565_; uint8_t v___x_3566_; uint8_t v___x_3567_; 
lean_dec_ref_known(v___x_3563_, 1);
v___x_3564_ = l_Lean_Meta_Context_config(v___y_3514_);
v_transparency_3565_ = lean_ctor_get_uint8(v___x_3564_, 9);
lean_dec_ref(v___x_3564_);
v___x_3566_ = 2;
v___x_3567_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3565_, v___x_3566_);
if (v___x_3567_ == 0)
{
lean_object* v_keyedConfig_3568_; uint8_t v_trackZetaDelta_3569_; lean_object* v_zetaDeltaSet_3570_; lean_object* v_lctx_3571_; lean_object* v_localInstances_3572_; lean_object* v_defEqCtx_x3f_3573_; lean_object* v_synthPendingDepth_3574_; lean_object* v_customCanUnfoldPredicate_x3f_3575_; uint8_t v_univApprox_3576_; uint8_t v_inTypeClassResolution_3577_; uint8_t v_cacheInferType_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; 
v_keyedConfig_3568_ = lean_ctor_get(v___y_3514_, 0);
v_trackZetaDelta_3569_ = lean_ctor_get_uint8(v___y_3514_, sizeof(void*)*7);
v_zetaDeltaSet_3570_ = lean_ctor_get(v___y_3514_, 1);
v_lctx_3571_ = lean_ctor_get(v___y_3514_, 2);
v_localInstances_3572_ = lean_ctor_get(v___y_3514_, 3);
v_defEqCtx_x3f_3573_ = lean_ctor_get(v___y_3514_, 4);
v_synthPendingDepth_3574_ = lean_ctor_get(v___y_3514_, 5);
v_customCanUnfoldPredicate_x3f_3575_ = lean_ctor_get(v___y_3514_, 6);
v_univApprox_3576_ = lean_ctor_get_uint8(v___y_3514_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3577_ = lean_ctor_get_uint8(v___y_3514_, sizeof(void*)*7 + 2);
v_cacheInferType_3578_ = lean_ctor_get_uint8(v___y_3514_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3568_);
v___x_3579_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3566_, v_keyedConfig_3568_);
lean_inc(v_customCanUnfoldPredicate_x3f_3575_);
lean_inc(v_synthPendingDepth_3574_);
lean_inc(v_defEqCtx_x3f_3573_);
lean_inc_ref(v_localInstances_3572_);
lean_inc_ref(v_lctx_3571_);
lean_inc(v_zetaDeltaSet_3570_);
v___x_3580_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3580_, 0, v___x_3579_);
lean_ctor_set(v___x_3580_, 1, v_zetaDeltaSet_3570_);
lean_ctor_set(v___x_3580_, 2, v_lctx_3571_);
lean_ctor_set(v___x_3580_, 3, v_localInstances_3572_);
lean_ctor_set(v___x_3580_, 4, v_defEqCtx_x3f_3573_);
lean_ctor_set(v___x_3580_, 5, v_synthPendingDepth_3574_);
lean_ctor_set(v___x_3580_, 6, v_customCanUnfoldPredicate_x3f_3575_);
lean_ctor_set_uint8(v___x_3580_, sizeof(void*)*7, v_trackZetaDelta_3569_);
lean_ctor_set_uint8(v___x_3580_, sizeof(void*)*7 + 1, v_univApprox_3576_);
lean_ctor_set_uint8(v___x_3580_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3577_);
lean_ctor_set_uint8(v___x_3580_, sizeof(void*)*7 + 3, v_cacheInferType_3578_);
lean_inc(v_mvarId_3512_);
v___x_3581_ = l_Lean_MVarId_getType_x27(v_mvarId_3512_, v___x_3580_, v___y_3515_, v___y_3516_, v___y_3517_);
lean_dec_ref_known(v___x_3580_, 7);
v___y_3520_ = v___x_3581_;
goto v___jp_3519_;
}
else
{
lean_object* v___x_3582_; 
lean_inc(v_mvarId_3512_);
v___x_3582_ = l_Lean_MVarId_getType_x27(v_mvarId_3512_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_);
v___y_3520_ = v___x_3582_;
goto v___jp_3519_;
}
}
else
{
lean_object* v_a_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3590_; 
lean_dec_ref(v___y_3514_);
lean_dec(v_mvarId_3512_);
v_a_3583_ = lean_ctor_get(v___x_3563_, 0);
v_isSharedCheck_3590_ = !lean_is_exclusive(v___x_3563_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3585_ = v___x_3563_;
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_a_3583_);
lean_dec(v___x_3563_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3588_; 
if (v_isShared_3586_ == 0)
{
v___x_3588_ = v___x_3585_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v_a_3583_);
v___x_3588_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
return v___x_3588_;
}
}
}
v___jp_3519_:
{
if (lean_obj_tag(v___y_3520_) == 0)
{
lean_object* v_a_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; uint8_t v___x_3524_; 
v_a_3521_ = lean_ctor_get(v___y_3520_, 0);
lean_inc(v_a_3521_);
lean_dec_ref_known(v___y_3520_, 1);
v___x_3522_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__4));
v___x_3523_ = lean_unsigned_to_nat(3u);
v___x_3524_ = l_Lean_Expr_isAppOfArity(v_a_3521_, v___x_3522_, v___x_3523_);
if (v___x_3524_ == 0)
{
lean_object* v___x_3525_; lean_object* v___x_3526_; 
lean_dec(v_a_3521_);
lean_dec(v_mvarId_3512_);
v___x_3525_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3526_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3525_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_);
lean_dec_ref(v___y_3514_);
return v___x_3526_;
}
else
{
lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; 
v___x_3527_ = l_Lean_Expr_appFn_x21(v_a_3521_);
v___x_3528_ = l_Lean_Expr_appArg_x21(v___x_3527_);
lean_dec_ref(v___x_3527_);
v___x_3529_ = l_Lean_Expr_appArg_x21(v_a_3521_);
lean_dec(v_a_3521_);
v___x_3530_ = ((lean_object*)(l_Lean_MVarId_subsingletonElim___lam__0___closed__1));
v___x_3531_ = lean_unsigned_to_nat(2u);
v___x_3532_ = lean_mk_empty_array_with_capacity(v___x_3531_);
v___x_3533_ = lean_array_push(v___x_3532_, v___x_3528_);
v___x_3534_ = lean_array_push(v___x_3533_, v___x_3529_);
v___x_3535_ = l_Lean_Meta_mkAppM(v___x_3530_, v___x_3534_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_);
lean_dec_ref(v___y_3514_);
if (lean_obj_tag(v___x_3535_) == 0)
{
lean_object* v_a_3536_; lean_object* v___x_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3545_; 
v_a_3536_ = lean_ctor_get(v___x_3535_, 0);
lean_inc(v_a_3536_);
lean_dec_ref_known(v___x_3535_, 1);
v___x_3537_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_3512_, v_a_3536_, v___y_3515_);
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3537_);
if (v_isSharedCheck_3545_ == 0)
{
lean_object* v_unused_3546_; 
v_unused_3546_ = lean_ctor_get(v___x_3537_, 0);
lean_dec(v_unused_3546_);
v___x_3539_ = v___x_3537_;
v_isShared_3540_ = v_isSharedCheck_3545_;
goto v_resetjp_3538_;
}
else
{
lean_dec(v___x_3537_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3545_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3541_; lean_object* v___x_3543_; 
v___x_3541_ = lean_box(v___x_3524_);
if (v_isShared_3540_ == 0)
{
lean_ctor_set(v___x_3539_, 0, v___x_3541_);
v___x_3543_ = v___x_3539_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v___x_3541_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
return v___x_3543_;
}
}
}
else
{
lean_object* v_a_3547_; lean_object* v___x_3549_; uint8_t v_isShared_3550_; uint8_t v_isSharedCheck_3554_; 
lean_dec(v_mvarId_3512_);
v_a_3547_ = lean_ctor_get(v___x_3535_, 0);
v_isSharedCheck_3554_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3549_ = v___x_3535_;
v_isShared_3550_ = v_isSharedCheck_3554_;
goto v_resetjp_3548_;
}
else
{
lean_inc(v_a_3547_);
lean_dec(v___x_3535_);
v___x_3549_ = lean_box(0);
v_isShared_3550_ = v_isSharedCheck_3554_;
goto v_resetjp_3548_;
}
v_resetjp_3548_:
{
lean_object* v___x_3552_; 
if (v_isShared_3550_ == 0)
{
v___x_3552_ = v___x_3549_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v_a_3547_);
v___x_3552_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
return v___x_3552_;
}
}
}
}
}
else
{
lean_object* v_a_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3562_; 
lean_dec_ref(v___y_3514_);
lean_dec(v_mvarId_3512_);
v_a_3555_ = lean_ctor_get(v___y_3520_, 0);
v_isSharedCheck_3562_ = !lean_is_exclusive(v___y_3520_);
if (v_isSharedCheck_3562_ == 0)
{
v___x_3557_ = v___y_3520_;
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_a_3555_);
lean_dec(v___y_3520_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v___x_3560_; 
if (v_isShared_3558_ == 0)
{
v___x_3560_ = v___x_3557_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_a_3555_);
v___x_3560_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
return v___x_3560_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___lam__0___boxed(lean_object* v_mvarId_3591_, lean_object* v___x_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_){
_start:
{
lean_object* v_res_3598_; 
v_res_3598_ = l_Lean_MVarId_subsingletonElim___lam__0(v_mvarId_3591_, v___x_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_);
lean_dec(v___y_3596_);
lean_dec_ref(v___y_3595_);
lean_dec(v___y_3594_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim(lean_object* v_mvarId_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_){
_start:
{
lean_object* v___x_3608_; lean_object* v___f_3609_; lean_object* v___f_3610_; lean_object* v___x_3611_; 
v___x_3608_ = ((lean_object*)(l_Lean_MVarId_subsingletonElim___closed__1));
lean_inc(v_mvarId_3602_);
v___f_3609_ = lean_alloc_closure((void*)(l_Lean_MVarId_subsingletonElim___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3609_, 0, v_mvarId_3602_);
lean_closure_set(v___f_3609_, 1, v___x_3608_);
v___f_3610_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__1___boxed), 6, 1);
lean_closure_set(v___f_3610_, 0, v___f_3609_);
v___x_3611_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_3602_, v___f_3610_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_);
return v___x_3611_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___boxed(lean_object* v_mvarId_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_){
_start:
{
lean_object* v_res_3618_; 
v_res_3618_ = l_Lean_MVarId_subsingletonElim(v_mvarId_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_);
lean_dec(v_a_3616_);
lean_dec_ref(v_a_3615_);
lean_dec(v_a_3614_);
lean_dec_ref(v_a_3613_);
return v_res_3618_;
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
